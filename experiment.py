"""Set sizes for the construction of proof.md, for n = 2^r.

1. Proved sizes: the theorem's exact formula |S| = k*s (no search is run).
2. Certified sets: smallbias.build, a practical variant that is actually run, with a rigorous
   certificate (an upper bound on the bias of the set produced) <= eps.
3. Exact bias: for r <= 24 the bias of the certified sets is computed exactly by FFT, and the
   smallest sets with exact bias <= 0.2 are found.
"""
import math, time
import smallbias as sb

R_LIST = [16, 24, 32, 64, 128, 256, 512, 1024]
EPS_LIST = [0.3, 0.2, 0.1]
t_start = time.time()

print("=== 1. Proved sizes (theorem, exact formula |S| = k*s) ===")
print(f"{'r':>5} {'eps':>4} | {'k':>5} {'s':>6} {'|S|':>11} {'|S|/r':>8} | {'closed form':>11}")
for r in R_LIST:
    for eps in EPS_LIST:
        f = sb.formal_parameters(1 << r, eps)
        print(f"{r:>5} {eps:>4} | {f['k']:>5} {f['s']:>6} {f['size']:>11,} {f['size'] / r:>8,.0f} | "
              f"{f['closed_form']:>11.3g}")
print()

print("=== 2. Certified sets (smallbias.build: certificate <= eps) ===")
print(f"{'r':>5} {'eps':>4} | {'k':>4} {'Q':>6} {'s':>5} {'|S|':>8} {'|S|/r':>6} {'cert':>6} "
      f"{'exact':>6} {'time':>5}")
built = {}
for r in (16, 24, 32, 48, 64, 96, 128, 192, 256):
    for eps in (0.3, 0.2):
        n, t0 = 1 << r, time.time()
        res = sb.build(n, eps)
        built[r, eps] = res
        exact = ""
        if r <= 24:
            exact = f"{sb.measured_bias(sb.build_set(n, res['P'], res['C']), n):.3f}"
        print(f"{r:>5} {eps:>4} | {res['k']:>4} {res['Q']:>6} {res['s']:>5} {res['size']:>8,} "
              f"{res['size'] / r:>6.0f} {res['certificate']:>6.3f} {exact:>6} "
              f"{time.time() - t0:>4.0f}s", flush=True)
print()

print("=== 3. Smallest sets with EXACT bias <= 0.2 (n small enough to check by FFT) ===")
for r in (16, 20, 24):
    n = 1 << r
    best = None
    for a in (0.5, 1.0, 2.0, 3.0):
        R = math.ceil(4 * math.log(n) / 0.2) + 16
        k = math.floor(a * sb.nat_log(R + 1, n // 2) / 0.2) + 1
        P = sb.smallest_primes_above(R, k, n)
        Q = P[-1]
        g = sb.GreedyInner(16 * Q, 1 / (2 * Q), 0.12)
        g.extend(256)
        lo, hi = 0, 256
        if sb.measured_bias(sb.build_set(n, P, g.C[:hi]), n) > 0.2:
            continue
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if sb.measured_bias(sb.build_set(n, P, g.C[:mid]), n) <= 0.2:
                hi = mid
            else:
                lo = mid
        if best is None or k * hi < best[0]:
            best = (k * hi, a, k, hi)
    if best is None:
        print(f"r={r}: no prefix of 256 inner elements reached exact bias 0.2")
    else:
        print(f"r={r}: |S|={best[0]} (a={best[1]}, k={best[2]} primes, s={best[3]}), "
              f"|S|/r = {best[0] / r:.0f}", flush=True)
print(f"\n[{time.time() - t_start:.0f}s total]")
