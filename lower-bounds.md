# Lower bounds: how small can the error be?

**Setup.** Take a list of integers k₁, …, k_m mod n (repeats allowed). Define

  T(ℓ) = Σⱼ e(ℓ·kⱼ/n),  Ŝ(ℓ) = T(ℓ)/m,  bias = max_{ℓ ≠ 0 (mod n)} |Ŝ(ℓ)|,

where e(x) = e^{2πix} and ‖x‖ is the distance from x to the nearest integer.

This file proves three limits on the bias that hold for **every** choice of coefficients.

| number of coefficients m | error is always at least | reason |
|---|---|---|
| fewer than log₂(n)/3 | 0.707 | §2, pigeonhole |
| log₂ n | about 0.3 (0.387 at n = 2¹⁰, decreasing towards ≈ 0.30) | §3, counting solutions |
| any m much smaller than n | about 1/√m | §1, energy |
| m = n (all residues once) | 0, which is achievable | §1 |

For comparison, the construction in `proof.md` reaches error 0.2 with about 30·log₂ n coefficients in practice.

---

## 1. Energy bound

**Theorem 1.** For every list of m coefficients,

  bias ≥ √( (n − m) / (m(n − 1)) ).

When m is much smaller than n, this is about 1/√m. When m = n, it is 0.

*Proof.* Expand the square and swap the sums:

  Σ_{ℓ=0}^{n−1} |T(ℓ)|² = Σ_{j, j'} Σ_ℓ e(ℓ(kⱼ − k_{j'})/n).

The inner sum is n when kⱼ ≡ k_{j'} (mod n) and 0 otherwise. So the total is n times the number of pairs (j, j') with equal coefficients. The m pairs with j = j' already give

  Σ_ℓ |T(ℓ)|² ≥ n·m.

The term ℓ = 0 equals m². The remaining n − 1 terms therefore sum to at least nm − m², so the largest of them is at least their average, (nm − m²)/(n − 1). Dividing by m² gives the claim. ∎

**Intuition.** The total "energy" over all n frequencies is at least n/m. Frequency 0 always takes exactly 1, and the other n − 1 frequencies share the rest. So at least one of them gets about 1/m, and its average arrow has length at least about 1/√m.

**Example: n = 4, m = 4.** The bound is √0 = 0, and S = {0, 1, 2, 3} reaches it:
- l = 1: 1 + i − 1 − i = 0
- l = 2: 1 − 1 + 1 − 1 = 0
- l = 3: 1 − i − 1 + i = 0

In general, all of ℤₙ has error 0. The bound only matters when m is much smaller than n, which is the case of interest (m ≈ C·log n).

---

## 2. Pigeonhole: fewer than log₂(n)/3 coefficients

**Theorem 2.** Let B ≥ 2 be an integer with B^m < n. Then there is an ℓ ∈ {1, …, n − 1} with

  ‖ℓ·kⱼ/n‖ < 1/B  for every j.

Consequently, if B ≥ 5, then bias > cos(2π/B).

*Proof.*
1. **Points.** For each a ∈ {0, …, n − 1}, take the point

  v_a = ( frac(a·k₁/n), …, frac(a·k_m/n) )  in the cube [0, 1)^m.

2. **Boxes.** Cut the cube into B^m boxes of side 1/B. There are n > B^m points, so two of them, v_a and v_b with a < b, land in the same box.
3. **The frequency.** Let ℓ = b − a, which lies in {1, …, n − 1}. For each j, the coordinates of v_a and v_b differ by less than 1/B. That difference also differs from ℓ·kⱼ/n by an integer. Hence ‖ℓ·kⱼ/n‖ < 1/B.
4. **The bias.** Each term e(ℓ·kⱼ/n) has real part cos(2π·‖ℓ·kⱼ/n‖) > cos(2π/B), because cos is decreasing on [0, π]. Averaging over j gives Re Ŝ(ℓ) > cos(2π/B), and bias ≥ |Ŝ(ℓ)| ≥ Re Ŝ(ℓ). ∎

**Consequences.** Use B^m < n ⟺ m < log₂(n)/log₂(B):

| if m < | then bias > |
|---|---|
| log₂(n)/3 (B = 8) | cos(π/4) ≈ 0.707 |
| log₂(n)/2.585 (B = 6) | cos(π/3) = 0.5 |
| log₂(n)/2.322 (B = 5) | cos(2π/5) ≈ 0.309 |

**Picture.** At this ℓ, every arrow e(ℓ·kⱼ/n) points within 1/B of a turn from "straight right". Nothing cancels, so the average arrow is long.

**Why it stops before log₂ n.** The argument needs more points (n) than boxes (B^m), and B must be at least 5 for cos(2π/B) to be positive. So it only works for m < log₅ n ≈ log₂(n)/2.32. At m = log₂ n it says nothing, which is why §3 needs a different argument.

This is also why simple choices such as kⱼ = 2ʲ fail: for small ℓ, most of the arrows ℓ·2ʲ/n are close to 0.

---

## 3. Counting solutions: exactly log₂ n coefficients

**Theorem 3.** For every 1 ≤ p ≤ m,

  bias^{2p} ≥ ( n·(m)_p·p! / m^{2p} − 1 ) / (n − 1),

where (m)_p = m(m − 1)⋯(m − p + 1).

*Proof.*
1. **Expand.** Write |T(ℓ)|^{2p} = T(ℓ)^p · conj(T(ℓ))^p and expand both powers. With k_J = k_{J₁} + ⋯ + k_{J_p}:

  Σ_ℓ |T(ℓ)|^{2p} = Σ_{J, J' ∈ {1..m}^p} Σ_ℓ e(ℓ(k_J − k_{J'})/n).

2. **Count.** The inner sum is n when k_J ≡ k_{J'} (mod n) and 0 otherwise. A pair satisfies this whenever J has distinct entries and J' is a rearrangement of J, because then k_J = k_{J'}. There are (m)_p·p! such pairs, so

  Σ_ℓ |T(ℓ)|^{2p} ≥ n·(m)_p·p!.

3. **Conclude.** Remove the ℓ = 0 term, which is m^{2p}. The largest of the other n − 1 terms is at least their average. Divide by m^{2p}. ∎

For p = 1 this is Theorem 1.

**Intuition.** Look at all sums of p coefficients. Reordering the same p coefficients always gives the same sum, so the list of sums has many forced coincidences. No set can avoid them, and coincidences mean energy at nonzero frequencies, just as in §1. Higher moments simply make that energy easier to detect.

**At m = log₂ n.** Take n = 2^m and choose the best p:

| log₂ n = m | 10 | 16 | 24 | 32 | 64 | 128 | 256 |
|---|---|---|---|---|---|---|---|
| bias is at least | 0.387 | 0.365 | 0.346 | 0.340 | 0.324 | 0.315 | 0.309 |
| best p | 3 | 5 | 7 | 10 | 19 | 38 | 75 |

**Limit as n → ∞.** With p ≈ c·m and Stirling's formula, the bound tends to

  max_c  e^{−1} · √c · (1 − c)^{−(1−c)/(2c)},

over the c with ln 2 − 2c + c·ln c − (1 − c)·ln(1 − c) > 0. The maximum is attained near c ≈ 0.28 and gives about 0.30.

So **log₂ n coefficients never give error below about 0.3**, for any n.

**Check.** For n = 1024 and m = 10, a local search over random sets found best error 0.614, consistent with the bound 0.387.

---

## 4. What this means

- **Exactly log₂ n coefficients can't give small error.** Every choice has error at least about 0.3, and the pigeonhole argument shows the error exceeds 0.7 once m drops below log₂(n)/3.
- **Small error needs C·log n coefficients with C growing as ε shrinks.** The energy bound alone forces m ≥ about 1/ε². The strongest known lower bound, which is not proved here, is m = Ω(log n / (ε²·log(1/ε))). It comes from Alon's rank argument for nearly orthogonal vectors.
- **The construction is within a constant of the limit for fixed ε.** It uses about 30·log₂ n coefficients for error 0.2, against the unavoidable C·log n.
