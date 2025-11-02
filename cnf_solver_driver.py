#!/usr/bin/env python3
"""
cnf_solver_driver.py
Integrates with your C++ DPLL solver (solver.exe). Generates CNF for
monoalphabetic substitution mapping (cipher letters -> plain A-Z), optionally
tries word-hypotheses, calls solver.exe via stdin, parses SAT result,
builds mapping and decrypts ciphertext, and scores outputs.

Usage:
    python cnf_solver_driver.py --cipher "QEB NRFZH YOLTK CLU GRJMP LSBO QEB IXWV ALD"
"""

import argparse
import subprocess
import itertools
import string
import sys
import math
import time
import os
from math import log
from collections import Counter, defaultdict

# ------------------ Configuration ------------------
solver_path = r'.\solver.exe'   # path to your compiled solver executable
# For Linux/macOS or if solver named differently, change above.
# Example: solver_path = './solver' or './solver.bin'

# Wordlist path (optional). If you have a big wordlist, point here.
wordlist_file = None  # e.g., 'wordlist.txt' or None to use internal small list

# Limits for hypothesis search
MAX_CANDIDATES_PER_TOKEN = 8   # per token (short word), top-K matched words
MAX_COMBINATION_SIZE = 2       # try single hypotheses and pairs (increase slowly)
MAX_TOTAL_TRIES = 100          # safety cap for how many solver runs we'll attempt
SOLVER_TIMEOUT = 12.0          # seconds - per solver run (avoid hanging)

# ------------------ Small builtin wordlist (useful for English constraints) --------------
BUILTIN_WORDS = [
    # common short words and some common longer ones for pattern matching
    "A","I","AN","IN","ON","IS","IT","AS","AT","BE","BY","TO","OF","THE","AND","FOR","YOU","NOT","THAT",
    "THIS","WITH","HAVE","THEY","WILL","FROM","THEM","YOUR","WHAT","WHEN","WHERE","WHO","HOW","HE","SHE",
    "WE","OUR","ARE","DO","CAN","BUT","OR","IF","THEN","HER","HIS","ALL","ANY","SO","NO","YES","MY","ME",
    "QUICK","BROWN","FOX","JUMPS","OVER","LAZY","DOG","HELLO","WORLD","TEST","SAMPLE","THERE","THEIR",
    "THEY","THEM","THESE","THOSE","AND","THUS","TIME","YEAR","PEOPLE","FIRST","SECOND","THIRD"
]

# English letter bigram log probabilities (normalized)
# Source: Google Books / word frequency studies (log10 probabilities)
BIGRAM_LOG = defaultdict(lambda: -5.0, {
    'TH': -1.2, 'HE': -1.3, 'IN': -1.5, 'ER': -1.6, 'AN': -1.7, 'RE': -1.7,
    'ON': -1.7, 'AT': -1.8, 'EN': -1.8, 'ND': -1.8, 'TI': -1.9, 'ES': -1.9,
    'OR': -1.9, 'TE': -1.9, 'OF': -2.0, 'ED': -2.0, 'IS': -2.0, 'IT': -2.0,
    'AL': -2.1, 'AR': -2.1, 'ST': -2.1, 'TO': -2.1, 'NT': -2.2,
})

# ------------------ Utilities ------------------
ALPHABET = list(string.ascii_uppercase)  # plaintext alphabet A..Z

# Paths you can set (absolute or relative)
WORD_FREQ_PATH = "word_freq.txt"   # expected: "word <count>" per line
TRIGRAM_PATH = "trigram_counts.txt"  # expected: "TRI count" per line, e.g. THE 12345

# Safety defaults / small fallback models (kept small for offline use)
FALLBACK_WORD_FREQ = {
    "THE": 23135851162, "OF": 13151942776, "AND": 12997637966, "TO": 12136980858,
    "A": 9081174698, "IN": 8469404971, "FOR": 5933321709, "IS": 4705743816,
    "ON": 3750423199, "YOU": 3162674656, "HELLO": 100000, "WORLD": 90000
}
FALLBACK_TRIGRAM_COUNTS = {
    "THE": 10000000, "AND": 5000000, "ING": 3000000, "ENT": 2000000, "ION": 1800000,
    "HER": 1600000, "FOR": 1500000, "THA": 1400000, "NTH": 1300000, "INT": 1200000
}

# Globals that will be populated
_word_freq = None           # dict word -> int count
_trigram_logprob = None     # dict trigram -> log-probability
_total_trigram_count = 0

def normalize_ciphertext(s):
    # uppercase, keep letters and spaces and punctuation (we keep tokens)
    return "".join(ch.upper() if ch.isalpha() else ch for ch in s)

def unique_letters_in_text(s):
    return sorted({ch for ch in s if ch.isalpha()})

def token_pattern(word):
    # produce pattern like ABCA for word "NOON" -> 0 1 2 2? but we want letter-equality pattern
    # We'll produce pattern with numbers: first new letter gets next number
    mapping = {}
    pat = []
    next_id = 0
    for ch in word:
        if ch not in mapping:
            mapping[ch] = next_id
            next_id += 1
        pat.append(mapping[ch])
    return tuple(pat)

def word_matches_pattern(cipher_word, candidate):
    # both uppercase; require same length and pattern shape
    if len(cipher_word) != len(candidate):
        return False
    return token_pattern(cipher_word) == token_pattern(candidate)

def load_wordlist(limit_len=12):
    words = []
    if wordlist_file:
        try:
            with open(wordlist_file, 'r', encoding='utf8') as f:
                for line in f:
                    w = line.strip().upper()
                    if w and all(ch.isalpha() for ch in w) and len(w) <= limit_len:
                        words.append(w)
        except Exception as e:
            print("Failed to load wordlist from", wordlist_file, ":", e)
    # fallback to builtin few words
    words.extend([w for w in BUILTIN_WORDS if all(ch.isalpha() for ch in w)])
    # dedupe & uppercase
    words = sorted(set(w.upper() for w in words))
    return words

# ------------------ CNF builder ------------------
def var_id(cipher_index, plain_index, N_plain):
    # 1-based DIMACS variable numbering
    return 1 + cipher_index * N_plain + plain_index

def build_bijection_clauses(cipher_letters):
    """
    Returns (num_vars, clauses_list)
    - cipher_letters: list of distinct cipher letters (ordered)
    - clauses_list: each clause is a list of integers ending without 0;
        writer will append trailing 0 when creating DIMACS.
    """
    M = len(cipher_letters)
    N = len(ALPHABET)
    clauses = []

    # Each cipher letter maps to at least one plaintext letter
    for i in range(M):
        clause = [var_id(i, p, N) for p in range(N)]
        clauses.append(clause)

    # Each cipher letter maps to at most one plaintext letter (pairwise)
    for i in range(M):
        for p, q in itertools.combinations(range(N), 2):
            clauses.append([-var_id(i, p, N), -var_id(i, q, N)])

    # Each plaintext letter is mapped by at most one cipher letter
    for p in range(N):
        for i, j in itertools.combinations(range(M), 2):
            clauses.append([-var_id(i, p, N), -var_id(j, p, N)])

    num_vars = M * N
    return num_vars, clauses

def build_hypothesis_clauses(hypotheses, cipher_letter_index_map):
    """
    hypotheses: list of tuples (token_pos, cipher_token, candidate_plain_word)
    token_pos is the index within tokens list (not used for var generation beyond identity)
    cipher_letter_index_map: dict mapping cipher letter -> cipher index (0..M-1)
    Returns:
      - list of hyp_vars (var index for each hypothesis)
      - clauses list for implications (¬H ∨ X_c_p)
    """
    hyp_clauses = []
    hyp_vars = []
    # Hypothesis var numbering will start after base num_vars; caller should offset when writing file
    for hyp in hypotheses:
        token_pos, cipher_token, candidate = hyp
        # For each position in token, add (¬H ∨ X_c_p)
        # We'll not assign var ids here: this function only returns clause templates with placeholders.
        hyp_clauses.append((cipher_token, candidate))  # store pair; actual clause creation deferred with offset
    return hyp_clauses

# ------------------ DIMACS writer ------------------
def dimacs_from_clauses(num_vars, clauses):
    # clauses: list of lists of ints, where each int is DIMACS var (positive) or negative literal
    out_lines = []
    out_lines.append(f"p cnf {num_vars} {len(clauses)}")
    for cl in clauses:
        out_lines.append(" ".join(str(l) for l in cl) + " 0")
    return "\n".join(out_lines) + "\n"

# ------------------ Solver invocation & parser ------------------
def run_solver_with_cnf_text(cnf_text, timeout=SOLVER_TIMEOUT):
    """
    Pipes cnf_text to solver_path stdin, returns (status, lits_list or None, raw_stdout, raw_stderr, runtime)
    status: 'SAT' or 'UNSAT' or 'ERROR' or 'TIMEOUT'
    lits_list: list of int (assignment literals terminated by 0 not included) if SAT else None
    """
    try:
        start = time.time()
        # Use subprocess.run with input as bytes; capture stdout/stderr
        proc = subprocess.run([solver_path], input=cnf_text.encode('utf8'), stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
        runtime = time.time() - start
        stdout = proc.stdout.decode('utf8', errors='ignore').strip().splitlines()
        stderr = proc.stderr.decode('utf8', errors='ignore').strip()
        if not stdout:
            return 'ERROR', None, stdout, stderr, runtime
        first = stdout[0].strip().upper()
        if first.startswith('SAT'):
            # find assignment line after the first line that contains trailing 0
            assign_line = None
            for line in stdout[1:]:
                line = line.strip()
                if not line:
                    continue
                parts = line.split()
                # assignment line usually ends with "0"
                if parts and parts[-1] == '0':
                    assign_line = line
                    break
            if assign_line is None:
                # maybe solver prints assignment on same line or in other format; try to collect all ints
                collected = []
                for line in stdout[1:]:
                    for tok in line.split():
                        try:
                            collected.append(int(tok))
                        except:
                            pass
                # find until 0
                if 0 in collected:
                    idx = collected.index(0)
                    lits = collected[:idx]
                    return 'SAT', lits, stdout, stderr, runtime
                return 'SAT', None, stdout, stderr, runtime
            lits = [int(x) for x in assign_line.split() if x != '0']
            return 'SAT', lits, stdout, stderr, runtime
        elif first.startswith('UNSAT'):
            return 'UNSAT', None, stdout, stderr, runtime
        else:
            # sometimes solver prints extra info; try to detect SAT/UNSAT anywhere
            joined = "\n".join(stdout).upper()
            if 'SAT' in joined:
                # parse assignment similarly
                all_ints = []
                for line in stdout:
                    for tok in line.split():
                        try:
                            all_ints.append(int(tok))
                        except:
                            pass
                if 0 in all_ints:
                    idx = all_ints.index(0)
                    lits = all_ints[:idx]
                    return 'SAT', lits, stdout, stderr, runtime
                return 'SAT', None, stdout, stderr, runtime
            if 'UNSAT' in joined:
                return 'UNSAT', None, stdout, stderr, runtime
            return 'ERROR', None, stdout, stderr, runtime
    except subprocess.TimeoutExpired:
        return 'TIMEOUT', None, None, None, timeout
    except FileNotFoundError as e:
        print("ERROR: solver executable not found at:", solver_path, file=sys.stderr)
        raise e

# ------------------ Mapping & decryption ------------------
def mapping_from_assignment(lits, cipher_letters):
    """
    Convert solver literal list to mapping: cipher letter -> plaintext letter
    lits: list of ints like [1, -2, 3, ...] from solver assignment line
    cipher_letters: list ordered
    """
    if lits is None:
        return {}
    N = len(ALPHABET)
    M = len(cipher_letters)
    mapping = {}
    for lit in lits:
        if lit == 0:
            continue
        if lit > 0:
            v = lit - 1
            cidx = v // N
            pidx = v % N
            if 0 <= cidx < M:
                mapping[cipher_letters[cidx]] = ALPHABET[pidx]
    return mapping

def decrypt_with_mapping(ciphertext, mapping):
    out = []
    for ch in ciphertext:
        if ch.isalpha():
            out.append(mapping.get(ch, '?'))
        else:
            out.append(ch)
    return "".join(out)


def load_word_frequency(path=WORD_FREQ_PATH):
    """Load a word -> frequency dictionary from path. Falls back to builtin small table."""
    global _word_freq
    _word_freq = {}
    if path and os.path.isfile(path):
        try:
            with open(path, 'r', encoding='utf8') as f:
                for line in f:
                    parts = line.strip().split()
                    if not parts: continue
                    word = parts[0].upper()
                    # last token expected to be integer frequency
                    try:
                        count = int(parts[-1])
                    except:
                        # sometimes format is "word\tfreq", ignore malformed lines
                        continue
                    _word_freq[word] = _word_freq.get(word, 0) + count
            if not _word_freq:
                raise RuntimeError("Loaded word frequency file but no words parsed.")
            print(f"[lang] Loaded {len(_word_freq)} words from {path}")
            return
        except Exception as e:
            print("[lang] Failed to load word frequency:", e)
    # fallback
    print("[lang] Word frequency file not found or failed to load; using fallback small table.")
    _word_freq = {k: int(v) for k, v in FALLBACK_WORD_FREQ.items()}

def load_trigram_model(path=TRIGRAM_PATH, smoothing=1.0):
    """
    Load trigram counts and convert to log-probabilities with additive smoothing.
    Returns trigram_logprob dict and sets global total count.
    """
    global _trigram_logprob, _total_trigram_count
    trig_counts = {}
    total = 0
    if path and os.path.isfile(path):
        try:
            with open(path, 'r', encoding='utf8') as f:
                for line in f:
                    parts = line.strip().split()
                    if len(parts) < 2: continue
                    tri = parts[0].upper()
                    if len(tri) != 3 or not tri.isalpha():
                        continue
                    try:
                        c = int(parts[1])
                    except:
                        continue
                    trig_counts[tri] = trig_counts.get(tri, 0) + c
                    total += c
            if not trig_counts:
                raise RuntimeError("No trigram counts parsed.")
            print(f"[lang] Loaded {len(trig_counts)} trigrams from {path} (total count {total})")
        except Exception as e:
            print("[lang] Failed to load trigram file:", e)
            trig_counts = FALLBACK_TRIGRAM_COUNTS.copy()
            total = sum(trig_counts.values())
            print("[lang] Using fallback trigram counts.")
    else:
        trig_counts = FALLBACK_TRIGRAM_COUNTS.copy()
        total = sum(trig_counts.values())
        print("[lang] Trigram file not found; using fallback trigram counts.")

    # convert to log-probabilities with additive smoothing
    vocab_size = 26**3  # number of possible trigrams
    _trigram_logprob = {}
    denom = total + smoothing * vocab_size
    for tri, cnt in trig_counts.items():
        prob = (cnt + smoothing) / denom
        _trigram_logprob[tri] = log(prob)  # natural log
    # For unseen trigrams, give a small default log-probability
    _trigram_logprob['_DEFAULT_'] = log(smoothing / denom)
    _total_trigram_count = total

def ensure_language_models():
    """Load models on demand (idempotent)."""
    global _word_freq, _trigram_logprob
    if _word_freq is None:
        load_word_frequency()
    if _trigram_logprob is None:
        load_trigram_model()

def trigram_score(text):
    """
    Return average trigram log-probability (natural log normalized by number of trigrams).
    Non-letter characters are removed. Short texts return low score.
    """
    ensure_language_models()
    s = ''.join(ch for ch in text.upper() if ch.isalpha())
    if len(s) < 3:
        return float(_trigram_logprob.get('_DEFAULT_', -10.0))
    total = 0.0
    count = 0
    for i in range(len(s) - 2):
        tri = s[i:i+3]
        total += _trigram_logprob.get(tri, _trigram_logprob.get('_DEFAULT_', -10.0))
        count += 1
    return total / max(1, count)  # average log-prob

def word_frequency_score(tokens):
    """
    tokens: list of uppercase tokens (words).
    Returns average log-frequency of tokens that are present, and a ratio of matched words.
    """
    ensure_language_models()
    if not tokens:
        return -100.0, 0.0
    matched_count = 0
    total_log = 0.0
    for t in tokens:
        t_u = t.upper()
        if t_u in _word_freq:
            matched_count += 1
            # use log(count) to compress range
            total_log += log(_word_freq[t_u] + 1)
        else:
            # small penalty for unknown words (use log 1 = 0)
            total_log += 0.0
    avg_log = total_log / len(tokens)
    ratio = matched_count / len(tokens)
    return avg_log, ratio

# New score function combining word freq + trigram
def score_plaintext(plaintext, wordset):
    """
    Improved scoring:
      - word match fraction (ratio)
      - word frequency average (log scale)
      - trigram average log-prob (normalized)
      - penalty for '?'
    Returns a single float; higher is better.
    """
    ensure_language_models()

    # Normalize tokens (uppercase)
    tokens = [t for t in "".join(ch if ch.isalpha() or ch == ' ' else ' ' for ch in plaintext).split()]
    if not tokens:
        return -1e9

    # Word match fraction (s1)
    hits = sum(1 for t in tokens if t.upper() in _word_freq or t.upper() in wordset)
    s1 = hits / len(tokens)

    # Word frequency average (s2: avg log-frequency)
    avg_logfreq, match_ratio = word_frequency_score([t.upper() for t in tokens])

    # Trigram score (s3: avg log-prob)
    s3 = trigram_score(plaintext)  # typically negative log-likelihood; higher (less negative) is better

    # Penalty for unknown chars and too many single-letter words
    qmarks = plaintext.count('?')
    penalty_q = -0.02 * qmarks

    short_word_penalty = 0.0
    single_letter_words = sum(1 for t in tokens if len(t) == 1 and t.upper() not in ('A', 'I'))
    short_word_penalty -= 0.1 * single_letter_words

    # Combine: weights tuned experimentally (you can tweak)
    # We convert avg_logfreq and s3 into comparable scales:
    # avg_logfreq can be between ~0..~26 (log of large counts), so normalize by a typical constant
    avg_logfreq_norm = avg_logfreq / 10.0  # heuristic scaling
    s3_norm = (s3 + 10.0)  # shift trigram log-prob up (because s3 is negative); +10 is heuristic

    score = (10.0 * s1) + (4.0 * avg_logfreq_norm) + (3.5 * s3_norm) + penalty_q + short_word_penalty

    # final safety clamp to avoid NaNs
    if score != score:  # NaN check
        return -1e9
    return float(score)
    
# ------------------ Hypothesis generator ------------------
def build_token_candidates(cipher_tokens, wordlist, top_k=MAX_CANDIDATES_PER_TOKEN):
    """
    For each token of length 1..4 in the ciphertext, find candidate English words
    with same pattern shape from wordlist. Return dict token->list(candidates)
    """
    token_candidates = {}
    for idx, tk in enumerate(cipher_tokens):
        t = tk.strip()
        if len(t) == 0:
            continue
        if not all(ch.isalpha() for ch in t):
            continue
        if len(t) > 12:
            continue
        # Consider only tokens length up to 6 or 4 (configurable)
        if len(t) <= 6:
            # find matching candidate words by same pattern
            candidates = []
            for w in wordlist:
                if len(w) != len(t):
                    continue
                if word_matches_pattern(t, w):
                    candidates.append(w)
            # For 1-letter words, keep A and I priority
            if len(t) == 1:
                if 'A' in candidates: candidates.remove('A'); candidates.insert(0, 'A')
                if 'I' in candidates and 'I' not in candidates[:2]: candidates.insert(0, 'I')
            token_candidates[(idx, t)] = candidates[:top_k]
    return token_candidates

# ------------------ Main orchestration ------------------
def generate_cnf_text(cipher_letters, hypotheses_active, hypotheses_defs):
    """
    Build full CNF text given:
      - cipher_letters: ordered list
      - hypotheses_active: list of hypothesis indices to activate (ints indexing hypotheses_defs)
      - hypotheses_defs: list of (token_pos, cipher_token, candidate_word)
    Returns:
      - DIMACS CNF text (string)
    """
    base_num_vars, base_clauses = build_bijection_clauses(cipher_letters)
    clauses = [list(cl) for cl in base_clauses]  # copy

    # Hypothesis definitions: for each hyp we will create an H var (index = base_num_vars + hyp_index + 1)
    hyp_var_start = base_num_vars + 1
    # For each hypothesis, create clauses (¬H ∨ X_c_p) for each letter position
    M = len(cipher_letters)
    N = len(ALPHABET)
    # mapping from cipher letter to its cipher_index
    cipher_idx_map = {c: i for i, c in enumerate(cipher_letters)}

    for hyp_idx, hyp in enumerate(hypotheses_defs):
        token_pos, cipher_token, candidate = hyp
        H_var = hyp_var_start + hyp_idx
        # For each letter position in the token, derive cipher letter and required plaintext letter
        for pos, plain_ch in enumerate(candidate):
            cch = cipher_token[pos]
            if cch not in cipher_idx_map:
                # if cipher letter not in list (shouldn't happen) skip
                continue
            cidx = cipher_idx_map[cch]
            pidx = ALPHABET.index(plain_ch)
            x_var = var_id(cidx, pidx, N)
            # clause (¬H ∨ X)
            clauses.append([-H_var, x_var])
        # If the hypothesis is to be activated now, add unit clause (H)
        if hyp_idx in hypotheses_active:
            clauses.append([H_var])

    total_vars = base_num_vars + len(hypotheses_defs)
    cnf_text = dimacs_from_clauses(total_vars, clauses)
    return cnf_text

def iterate_and_solve(ciphertext, solver_path_local, max_tries=MAX_TOTAL_TRIES):
    # normalize
    normalized = normalize_ciphertext(ciphertext)
    cipher_letters = unique_letters_in_text(normalized)
    print("Cipher letters used:", "".join(cipher_letters))
    if not cipher_letters:
        print("No letters found in ciphertext.")
        return

    # tokens
    tokens = [tk for tk in "".join(ch if ch.isalpha() or ch==' ' else ' ' for ch in normalized).split()]
    print("Tokens:", tokens[:40])

    # load wordlist
    wordlist = load_wordlist(limit_len=12)
    wordset = set(wordlist)

    # build token candidates for short tokens
    token_candidates = build_token_candidates(tokens, wordlist, top_k=MAX_CANDIDATES_PER_TOKEN)
    # convert token_candidates keys to a flat list of hypothesis defs: (token_pos, cipher_token, candidate)
    hypotheses_defs = []
    hyp_info = []  # keep track of mapping to token for debugging
    for (idx, token) in token_candidates:
        ctoken = token
        cand_list = token_candidates[(idx, token)]
        for cand in cand_list:
            hypotheses_defs.append((idx, ctoken, cand))
            hyp_info.append((idx, ctoken, cand))
    print(f"Found {len(hypotheses_defs)} hypotheses (short token candidates).")

    best = {'score': -1e9, 'plaintext': None, 'mapping': None, 'hypothesis_combo': None, 'solver_output': None}

    # Try with NO hypothesis (baseline): this will give some mapping but usually gibberish
    tries = 0
    def attempt_and_score(active_hyp_indices):
        nonlocal tries, best
        tries += 1
        if tries > max_tries:
            return False  # stop
        cnf_text = generate_cnf_text(cipher_letters, active_hyp_indices, hypotheses_defs)
        status, lits, stdout_lines, stderr, runtime = run_solver_with_cnf_text(cnf_text, timeout=SOLVER_TIMEOUT)
        print(f"Attempt {tries}: hyp={active_hyp_indices} -> solver={status} (time {runtime:.2f}s)")
        if status == 'SAT':
            mapping = mapping_from_assignment(lits, cipher_letters)
            plain = decrypt_with_mapping(normalized, mapping)
            sc = score_plaintext(plain, wordset)
            print(f"  Score={sc:.4f} Decrypted (start): {plain[:80]}...")
            if sc > best['score']:
                best.update({'score': sc, 'plaintext': plain, 'mapping': mapping.copy(),
                             'hypothesis_combo': [hypotheses_defs[i] for i in active_hyp_indices],
                             'solver_output': stdout_lines})
            # if score is very good, we can quit early
            if sc > 8.0:
                print("High score reached, stopping early.")
                return True
        elif status == 'TIMEOUT':
            print("  Solver timed out; skipping.")
        elif status == 'ERROR':
            print("  Solver error; check solver output.")
        return False

    # 1) Try baseline (no hypotheses)
    print("\n=== Trying baseline (no hypotheses) ===")
    stop = attempt_and_score([])
    if stop:
        return best

    # 2) Try single hypotheses first, then pairs up to MAX_COMBINATION_SIZE
    total_hyps = len(hypotheses_defs)
    if total_hyps == 0:
        print("No short-token hypotheses found; you'll need to supply a dictionary or run with longer tokens.")
        return best

    # limit candidate set to reasonable top ones by heuristic (e.g., frequency of cipher token)
    # sort hypotheses by frequency of their cipher token occurrence (prefer hypotheses for frequent tokens)
    freq = Counter([hypotheses_defs[i][1] for i in range(len(hypotheses_defs))])
    hyp_indices_sorted = sorted(range(total_hyps), key=lambda i: (-freq[hypotheses_defs[i][1]], i))
    # cap overall considered hypotheses for combinatorics
    MAX_HYPS_TO_CONSIDER = min(30, len(hyp_indices_sorted))
    hyp_indices_sorted = hyp_indices_sorted[:MAX_HYPS_TO_CONSIDER]
    print(f"Considering top {len(hyp_indices_sorted)} hypotheses for combinations (capped).")

    # try singletons
    for i in hyp_indices_sorted:
        if attempt_and_score([i]):
            return best

    # try combinations size 2 .. MAX_COMBINATION_SIZE
    for r in range(2, MAX_COMBINATION_SIZE + 1):
        print(f"\n=== Trying hypothesis combinations of size {r} ===")
        combos = itertools.combinations(hyp_indices_sorted, r)
        for combo in combos:
            if attempt_and_score(list(combo)):
                return best
            if tries >= max_tries:
                print("Reached max tries limit.")
                return best

    print("Search finished (or limit reached).")
    return best

# ------------------ CLI ------------------
def main():
    parser = argparse.ArgumentParser(description="CNF generator + SAT runner for monoalphabetic substitution decryption")
    parser.add_argument("--cipher", type=str, default=None, help="Ciphertext string (in quotes)")
    parser.add_argument("--cipher-file", type=str, default=None, help="Path to file containing ciphertext")
    parser.add_argument("--solver", type=str, default=None, help="Path to solver executable (overrides config)")
    args = parser.parse_args()

    global solver_path
    if args.solver:
        solver_path = args.solver

    if args.cipher_file:
        with open(args.cipher_file, 'r', encoding='utf8') as f:
            ciphertext = f.read().strip()
    elif args.cipher:
        ciphertext = args.cipher
    else:
        print("Enter ciphertext (single line). Press Ctrl-D (Unix) or Ctrl-Z+Enter (Windows) to finish:")
        ciphertext = sys.stdin.read().strip()

    if not ciphertext:
        print("No ciphertext provided.")
        return

    print("Using solver:", solver_path)
    result = iterate_and_solve(ciphertext, solver_path_local=solver_path)
    print("\n======== BEST RESULT ========")
    if result['plaintext'] is None:
        print("No satisfying decryption found.")
    else:
        print("Score:", result['score'])
        print("Plaintext (first 500 chars):")
        print(result['plaintext'][:1000])
        print("Mapping (cipher -> plain):")
        for k, v in sorted(result['mapping'].items()):
            print(f"  {k} -> {v}")
        print("Hypotheses used:")
        print(result['hypothesis_combo'])
        print("Solver output (first lines):")
        if result['solver_output']:
            print("\n".join(result['solver_output'][:8]))

if __name__ == '__main__':
    main()
