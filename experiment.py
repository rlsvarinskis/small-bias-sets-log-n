"""How does the certified set size grow with n?  (sparse searched inner set vs. dense run)

For each n = 2^r we find the smallest |S| whose *certificate* is <= eps, over a grid of
parameters, for two inner sets:
  sparse: C = greedy_inner(N = 16 Q, s)         (this construction)
  dense : C = {0, 1, ..., L-1}                   (the earlier version)
For r <= 24 the chosen sparse sets are also checked against the exact bias (FFT).
"""
import math, time
import numpy as np
import smallbias as sb

Q_LIST = [64, 96, 128, 192, 256, 384, 512, 768, 1024, 1536, 2048, 3072, 4096]
S_LIST = [32, 48, 64, 96, 128, 192, 256, 384, 512, 768]
L_LIST = sorted({int(round(2 ** (e / 2))) for e in range(8, 37)})        # 16 .. 2^18
R_LIST = [16, 24, 32, 48, 64, 96, 128, 192, 256, 384, 512, 768, 1024]
EPS_LIST = [0.3, 0.2]
KMAX = 64
deltas = lambda Q: [(k - 0.5) / Q for k in range(1, KMAX + 1) if (k - 0.5) / Q <= 0.5]


def sups(profile, Q):
    return [sb.inner_sup(profile, d) for d in deltas(Q)]


def certify_from_sups(n, Q, num_primes, sup_list):
    best = 1.0
    for d, g in zip(deltas(Q), sup_list):
        F = min(1.0, sb.bad_count(n, Q, d) / num_primes)
        best = min(best, F + (1 - F) * g)
    return best


t0 = time.time()
num_primes = {Q: len(sb.primes_in(Q // 2, Q)) for Q in Q_LIST}
sparse, inner_sets = {}, {}                       # (Q, s) -> sup list
for Q in Q_LIST:
    C = sb.greedy_inner(16 * Q, max(S_LIST), 1 / (2 * Q))
    inner_sets[Q] = C
    for s in S_LIST:
        sparse[Q, s] = sups(sb.inner_profile(C[:s]), Q)
    print(f"[{time.time() - t0:6.0f}s] inner sets for Q={Q} done", flush=True)
dense = {}
for L in L_LIST:
    prof = sb.inner_profile(np.arange(L))
    for Q in Q_LIST:
        dense[Q, L] = sups(prof, Q)
print(f"[{time.time() - t0:6.0f}s] dense profiles done\n", flush=True)

for eps in EPS_LIST:
    print(f"=== certified bias <= {eps} ===")
    print(f"{'r':>5} | {'sparse m':>9} {'m/r':>6} {'(Q, s)':>12} | {'dense m':>9} {'m/r':>7} {'(Q, L)':>14}")
    for r in R_LIST:
        n = 1 << r
        best_s = min(((num_primes[Q] * s, Q, s) for (Q, s), g in sparse.items()
                      if certify_from_sups(n, Q, num_primes[Q], g) <= eps), default=None)
        best_d = min(((num_primes[Q] * L, Q, L) for (Q, L), g in dense.items()
                      if certify_from_sups(n, Q, num_primes[Q], g) <= eps), default=None)
        fs = f"{best_s[0]:>9} {best_s[0] / r:>6.0f} {str(best_s[1:]):>12}" if best_s else f"{'-':>9} {'':>6} {'':>12}"
        fd = f"{best_d[0]:>9} {best_d[0] / r:>7.0f} {str(best_d[1:]):>14}" if best_d else f"{'(none in grid)':>32}"
        print(f"{r:>5} | {fs} | {fd}")
        if best_s and r <= 24:
            S = sb.build_set(n, best_s[1], inner_sets[best_s[1]][:best_s[2]])
            print(f"{'':>5}   exact bias of that sparse set: {sb.measured_bias(S, n):.3f}")
    print()

print("=== smallest sparse set with EXACT bias <= 0.2 (n small enough to check by FFT) ===")
for r in (16, 20, 24):
    n = 1 << r
    found = None
    for m, Q, s in sorted((num_primes[Q] * s, Q, s) for Q in Q_LIST if Q <= 1024 for s in S_LIST):
        b = sb.measured_bias(sb.build_set(n, Q, inner_sets[Q][:s]), n)
        if b <= 0.2:
            found = (m, Q, s, b)
            break
    print(f"r={r}: m={found[0]} (Q={found[1]}, s={found[2]}, exact bias {found[3]:.3f}), m/r = {found[0] / r:.0f}")
print(f"\n[{time.time() - t0:.0f}s total]")
