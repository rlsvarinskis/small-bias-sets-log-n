"""Deterministic small-bias sets in Z_n ("prime fractions with a searched inner set").

    S = { c * q^{-1} mod n :  q prime, Q/2 < q <= Q, q does not divide n,  c in C }

C is a multiset of s integers in [1, N), chosen by a deterministic greedy search
(method of conditional expectations with an exponential potential) so that
|avg_{c in C} e(c*beta)| is small for every real beta with ||beta|| >= delta.

Every set comes with a certificate: an upper bound on
    bias(S) = max_{l != 0 mod n} | (1/|S|) sum_{k in S} e(l*k/n) |
that follows from Lemma 2 (few bad primes) and a fine-grid evaluation of C
(see proof.md).  No randomness is used anywhere.
"""
import math
import numpy as np


# ---------------------------------------------------------------- primes

def primes_in(lo, hi, n=None):
    """Primes q with lo < q <= hi (and q not dividing n, if n is given)."""
    sieve = np.ones(hi + 1, bool)
    sieve[:2] = False
    for p in range(2, math.isqrt(hi) + 1):
        if sieve[p]:
            sieve[p * p::p] = False
    return [q for q in range(lo + 1, hi + 1) if sieve[q] and (n is None or n % q)]


def _is_prime(m):
    if m < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small:
        if m % p == 0:
            return m == p
    d, r = m - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in small:                     # deterministic for m < 3.3e24
        x = pow(a, d, m)
        if x in (1, m - 1):
            continue
        for _ in range(r - 1):
            x = x * x % m
            if x == m - 1:
                break
        else:
            return False
    return True


def _smooth_prime(at_least):
    """Smallest prime M = k*2^a + 1 >= at_least with small odd k (so M-1 is FFT-friendly)."""
    cands = sorted(k << a | 1 for a in range(1, 40) for k in range(1, 64, 2)
                   if at_least <= (k << a | 1) <= 4 * at_least)
    return next(M for M in cands if _is_prime(M))


def _primitive_root(p):
    m, fs, f = p - 1, set(), 2
    while f * f <= m:
        while m % f == 0:
            fs.add(f)
            m //= f
        f += 1
    if m > 1:
        fs.add(m)
    return next(g for g in range(2, p) if all(pow(g, (p - 1) // f, p) != 1 for f in fs))


def _powers(g, p, block=4096):
    """pw[a] = g^a mod p for a in [0, p-1)."""
    L = p - 1
    pw = np.empty(L, np.int64)
    x = 1
    for a in range(min(block, L)):
        pw[a] = x
        x = x * g % p
    gb = pow(g, block, p)
    for start in range(block, L, block):
        end = min(start + block, L)
        pw[start:end] = pw[start - block:end - block] * gb % p
    return pw


# ---------------------------------------------------------------- inner set

def greedy_inner(N, s, delta, grid_factor=4, dirs=4, t=None):
    """Deterministically pick c_1..c_s in [1, N) keeping avg e(c*beta) small for ||beta|| >= delta.

    Greedy minimisation of  Phi = sum_{beta in grid} sum_u exp(t * sum_i cos(2 pi c_i beta + 2 pi u/dirs)).
    The grid is beta = j/M (M prime); for all N candidates at once the potential is a
    cross-correlation over the multiplicative group of Z_M, so each step costs a few FFTs.
    """
    M = _smooth_prime(grid_factor * N)
    L = M - 1
    pw = _powers(_primitive_root(M), M)
    lg = np.empty(M, np.int64)
    lg[pw] = np.arange(L)
    allowed = np.minimum(pw, M - pw) >= max(1, math.floor(delta * M))
    if t is None:
        t = math.sqrt(2 * math.log(dirs * allowed.sum()) / s)
    thetas = 2 * np.pi * np.arange(dirs) / dirs
    angle = 2 * np.pi * pw / M
    F_hat = [np.fft.rfft(np.exp(t * np.cos(angle + th))) for th in thetas]
    log_w = np.zeros((dirs, L))
    cand_c = np.arange(1, N)
    cand_b = lg[cand_c]
    C = []
    for _ in range(s):
        top = log_w[:, allowed].max()
        phi = np.zeros(cand_c.size)
        for u in range(dirs):
            w = np.where(allowed, np.exp(log_w[u] - top), 0.0)
            corr = np.fft.irfft(np.conj(np.fft.rfft(w)) * F_hat[u], n=L)
            phi += corr[cand_b]          # corr[b] = sum_a w[a] F[a+b]  ->  candidate c = g^b
        c = int(cand_c[np.argmin(phi)])
        C.append(c)
        new = 2 * np.pi * (c * pw % M) / M
        for u, th in enumerate(thetas):
            log_w[u] += t * np.cos(new + th)
    return np.array(C, dtype=np.int64)


def inner_profile(C, fine_factor=128):
    """Certified profile of C: sup_{||beta|| >= delta} |avg e(c beta)| for any delta (via inner_sup)."""
    C = np.asarray(C, dtype=np.int64)
    Mf = 1 << math.ceil(math.log2(fine_factor * (int(C.max()) + 1)))
    spec = np.abs(np.fft.rfft(np.bincount(C, minlength=Mf).astype(np.float64))) / C.size
    suffix_max = np.maximum.accumulate(spec[::-1])[::-1]       # max over k' >= k
    lipschitz = math.pi * float(C.mean()) / Mf                # |d/dbeta| <= 2 pi mean(C), half a cell
    return suffix_max, Mf, lipschitz


def inner_sup(profile, delta):
    suffix_max, Mf, lipschitz = profile
    k = min(math.floor(delta * Mf), suffix_max.size - 1)
    return min(1.0, float(suffix_max[k]) + lipschitz)


# ---------------------------------------------------------------- outer bound and certificate

def bad_count(n, Q, x):
    """Lemma 2: for every l != 0 mod n, #{q in P : ||l q^{-1}/n|| < x} <= J * K."""
    J = 2 * math.ceil(x * Q + 0.5) - 1                          # integers j with |j| < xQ + 1/2
    log_bound = math.log(x) + math.log(n) + math.log(Q)        # |l + jn| < x n Q
    K = max(0, math.ceil(log_bound / math.log(Q / 2)) - 1)     # primes > Q/2 dividing it
    return J * K


def certify(n, Q, num_primes, profile, max_k=64):
    """Upper bound on bias(S): min over delta_k = (k - 1/2)/Q of  F + (1 - F) * sup_{>= delta_k} |C^|."""
    best = 1.0
    for k in range(1, max_k + 1):
        delta = (k - 0.5) / Q
        if delta > 0.5:
            break
        F = min(1.0, bad_count(n, Q, delta) / num_primes)
        best = min(best, F + (1 - F) * inner_sup(profile, delta))
    return best


# ---------------------------------------------------------------- the set itself

def build_set(n, Q, C):
    """The multiset S as Python ints (works for any n, including n far beyond 2^64)."""
    return [int(c) * pow(q, -1, n) % n for q in primes_in(Q // 2, Q, n) for c in C]


def measured_bias(S, n):
    """Exact bias by FFT (only feasible for n up to ~2^25)."""
    h = np.bincount(np.asarray(S, dtype=np.int64) % n, minlength=n).astype(np.float64)
    spec = np.abs(np.fft.rfft(h)) / h.sum()
    return float(spec[1:].max())
