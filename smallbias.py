"""Deterministic small-bias sets in Z_n: the construction of proof.md (formalised in lean/).

    S = { c * q^{-1} mod n :  q in P,  c in C }

    P = the k smallest primes q > R that do not divide n,   Q = max P
    C = greedy inner list: c_1, c_2, ... in [0, N), each the least minimiser of an exponential
        potential over D directions and a grid of frequencies (Lemma 3)

Two entry points:

* formal_parameters(n, eps) -- the exact parameters of the theorem and the proved size |S| = k*s.
  The theorem's inner search (N = 300Q/eps candidates, grid M = 1000N/eps) is polynomial but far
  too large to run, so this only computes sizes.

* build(n, eps) -- a practical variant that is actually run: the same outer set P, a smaller inner
  search (N = 16Q, coarse grid, FFT-accelerated), and a certificate.  The certificate is a rigorous
  upper bound on bias(S) for the set produced (Lemmas 1-2 for all thresholds at once, plus an exact
  fine-grid evaluation of the inner list).  The inner list is grown until the certificate is <= eps.

    bias(S) = max_{l != 0 mod n} | (1/|S|) sum_{k in S} e(l*k/n) |,   e(x) = exp(2 pi i x).

No randomness is used anywhere.
"""
import math
import numpy as np


# ---------------------------------------------------------------- primes and integer helpers

def _sieve(limit):
    s = np.ones(limit + 1, bool)
    s[:2] = False
    for p in range(2, math.isqrt(limit) + 1):
        if s[p]:
            s[p * p::p] = False
    return s


def smallest_primes_above(R, k, n):
    """The k smallest primes q > R that do not divide n (the outer set P)."""
    hi = max(2 * R, R + 256)
    while True:
        s = _sieve(hi)
        found = [q for q in range(R + 1, hi + 1) if s[q] and n % q]
        if len(found) >= k:
            return found[:k]
        hi *= 2


def nat_log(b, x):
    """Largest K with b**K <= x (Lean's Nat.log b x)."""
    K, p = 0, b
    while p <= x:
        K, p = K + 1, p * b
    return K


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


# ---------------------------------------------------------------- the theorem's parameters

def formal_parameters(n, eps):
    """Parameters of the theorem (proof.md, lean/Smallbias/Main.lean) and the proved size k*s.

    Up to floating-point rounding in the ceilings, these are exactly Rpar, numPrimes, primes, Pmax,
    Npar, Mpar, spar of the Lean development (here k = |P| and Q = P_max); |S| = k*s is
    `main_size_exact`.
    """
    R = math.ceil(4 * math.log(n) / eps) + 16
    K = nat_log(R + 1, n // 2)
    k = math.floor(3 * K / eps) + 1
    P = smallest_primes_above(R, k, n)
    Q = P[-1]
    assert Q <= R * R                               # Lemma 4
    N = math.ceil(300 * Q / eps)
    M = math.ceil(1000 * N / eps)
    t = 5 * eps / 8
    s = math.ceil(2 * math.log(16 * (M + 1)) / t ** 2)
    return dict(R=R, K=K, k=k, P=P, Q=Q, N=N, M=M, D=16, t=t, s=s, size=k * s,
                closed_form=235 * (math.log(n) + 2) / eps ** 3)


# ---------------------------------------------------------------- inner list: greedy search

class GreedyInner:
    """Deterministic greedy inner list (Lemma 3), resumable.

    Grid beta = j/M (M prime) restricted to delta/2 <= ||beta||, directions u < D.  Step: append
    the least c in [0, N) minimising
        Phi = sum_{beta in grid} sum_{u < D} exp(t * sum_{c in C} cos(2 pi (c beta - u/D))).
    For all N candidates at once the potential is a cross-correlation over the multiplicative group
    of Z_M, so one step costs 2D FFTs of length M - 1.
    """

    def __init__(self, N, delta, t, dirs=8, grid_factor=4):
        self.N = N
        M = _smooth_prime(grid_factor * N)
        self.M, L = M, M - 1
        self.pw = _powers(_primitive_root(M), M)
        lg = np.empty(M, np.int64)
        lg[self.pw] = np.arange(L)
        self.allowed = np.minimum(self.pw, M - self.pw) >= max(1, math.floor(delta / 2 * M))
        self.t, self.L = t, L
        self.shifts = 2 * np.pi * np.arange(dirs) / dirs
        angle = 2 * np.pi * self.pw / M
        self.F_hat = [np.fft.rfft(np.exp(t * np.cos(angle - sh))) for sh in self.shifts]
        self.log_w = np.zeros((dirs, L))
        self.c0_factor = np.exp(t * np.cos(-self.shifts))      # candidate c = 0
        self.cand_b = lg[np.arange(1, N)]
        self.C = []

    def extend(self, steps):
        M, pw, t = self.M, self.pw, self.t
        for _ in range(steps):
            top = self.log_w[:, self.allowed].max()
            phi = np.zeros(self.N)
            for u in range(len(self.shifts)):
                w = np.where(self.allowed, np.exp(self.log_w[u] - top), 0.0)
                corr = np.fft.irfft(np.conj(np.fft.rfft(w)) * self.F_hat[u], n=self.L)
                phi[1:] += corr[self.cand_b]          # corr[b] = sum_a w[a] F[a+b], c = g^b
                phi[0] += w.sum() * self.c0_factor[u]
            c = int(np.argmin(phi))                   # least minimiser
            self.C.append(c)
            new = 2 * np.pi * (c * pw % M) / M
            for u, sh in enumerate(self.shifts):
                self.log_w[u] += t * np.cos(new - sh)
        return self.C


# ---------------------------------------------------------------- certificate

def inner_profile(C, fine_factor=128):
    """Exact |avg_c e(c beta)| on a fine grid, as a suffix maximum, plus the Lipschitz slack."""
    C = np.asarray(C, dtype=np.int64)
    Mf = 1 << math.ceil(math.log2(fine_factor * (int(C.max()) + 1)))
    spec = np.abs(np.fft.rfft(np.bincount(C, minlength=Mf).astype(np.float64))) / C.size
    suffix_max = np.maximum.accumulate(spec[::-1])[::-1]       # max over k' >= k
    lipschitz = math.pi * float(C.mean()) / Mf                # |d/dbeta| <= 2 pi mean(C)
    return suffix_max, Mf, lipschitz


def _sup_from(profile, x):
    """Upper bound on sup_{x <= ||beta|| <= 1/2} |C^(beta)|."""
    suffix_max, Mf, lipschitz = profile
    k = min(math.floor(x * Mf), suffix_max.size - 1)
    return min(1.0, float(suffix_max[k]) + lipschitz)


def bad_fraction(n, R, Q, num_primes, x):
    """Lemma 2 at threshold x: the fraction of q in P with ||l q^{-1} / n|| < x is at most
    J*K / |P|, J = #{j : |j| < xQ + 1/2}, K = max number of primes > R dividing a nonzero
    integer of absolute value < x n Q.  (Floating-point K is rounded up, so the bound is safe.)"""
    if x <= 0:
        return 0.0
    J = 2 * math.ceil(x * Q + 0.5) - 1
    v = (math.log(x) + math.log(n) + math.log(Q)) / math.log(R + 1)
    K = max(0, math.floor(v + 1e-9))
    return min(1.0, J * K / num_primes)


def certify(n, R, Q, num_primes, profile, geometric_points=4000):
    """Rigorous upper bound on bias(S), combining Lemmas 1-3 over all thresholds.

    For each l != 0 put X_q = ||l q^{-1} / n|| and G(x) = sup_{||beta|| >= x} |C^(beta)|
    (nonincreasing).  Lemma 1 gives |S^(l)| <= E_q G(X_q), and Abel summation over any grid
    0 = x_0 < ... < x_m = 1/2 gives
        E_q G(X_q) <= G(x_m) + sum_i (G(x_i) - G(x_{i+1})) * P[X < x_{i+1}],
    where P[X < x] <= bad_fraction(x) by Lemma 2.  Grid points below 1/Mf contribute nothing.
    """
    _, Mf, _ = profile
    lo = 1.0 / Mf
    xs = set(np.geomspace(lo, 0.5, geometric_points).tolist())
    xs.update((j - 0.5) / Q for j in range(1, int(Q / 2) + 2) if lo <= (j - 0.5) / Q <= 0.5)
    log_base = math.log(R + 1)
    m = 1
    while True:                                      # where K jumps: x n Q = (R+1)^m
        lx = m * log_base - math.log(n) - math.log(Q)
        if lx > math.log(0.5):
            break
        if lx >= math.log(lo):
            xs.add(math.exp(lx))
        m += 1
    xs = [0.0] + sorted(xs) + [0.5]
    G = [1.0] + [_sup_from(profile, x) for x in xs[1:]]
    bound = G[-1]
    for i in range(len(xs) - 1):
        drop = G[i] - G[i + 1]
        if drop > 0:
            bound += drop * bad_fraction(n, R, Q, num_primes, xs[i + 1])
    return min(1.0, bound)


# ---------------------------------------------------------------- the practical construction

def build(n, eps, R=None, a=3.0, kappa=16, dirs=8, grid_factor=4, t=None, s_max=1 << 15):
    """Deterministic set with certificate <= eps (or the best found up to s_max).

    Outer set as in the theorem: R (default ceil(4 ln n / eps) + 16), k = floor(a K/eps) + 1
    primes.  Inner list from GreedyInner with N = kappa Q; its length s is the smallest found
    (doubling, then binary search over prefixes) whose certificate is <= eps.
    """
    if R is None:
        R = math.ceil(4 * math.log(n) / eps) + 16
    K = nat_log(R + 1, n // 2)
    k = math.floor(a * K / eps) + 1
    P = smallest_primes_above(R, k, n)
    Q = P[-1]
    greedy = GreedyInner(kappa * Q, 1 / (2 * Q), t if t is not None else 0.6 * eps,
                         dirs, grid_factor)
    cert_of = lambda s: certify(n, R, Q, k, inner_profile(greedy.C[:s]))
    lo, hi = 0, 32
    while True:
        greedy.extend(hi - len(greedy.C))
        if cert_of(hi) <= eps or hi >= s_max:
            break
        lo, hi = hi, 2 * hi
    while hi - lo > max(1, hi // 64):                # binary search for a short certified prefix
        mid = (lo + hi) // 2
        if cert_of(mid) <= eps:
            hi = mid
        else:
            lo = mid
    s = hi
    return dict(n=n, eps=eps, R=R, K=K, k=k, P=P, Q=Q, N=kappa * Q, C=greedy.C[:s], s=s,
                size=k * s, certificate=cert_of(s))


def build_set(n, P, C):
    """The multiset S as Python ints (works for any n, including n far beyond 2^64)."""
    return [int(c) * pow(q, -1, n) % n for q in P for c in C]


def measured_bias(S, n):
    """Exact bias by FFT (only feasible for n up to ~2^25)."""
    h = np.bincount(np.asarray(S, dtype=np.int64) % n, minlength=n).astype(np.float64)
    spec = np.abs(np.fft.rfft(h)) / h.sum()
    return float(spec[1:].max())
