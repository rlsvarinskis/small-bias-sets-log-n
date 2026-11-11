# Small-bias sets in ℤₙ of size O(log n / ε³)

## Summary in plain language

**Goal.** Deterministically choose integers k₁, …, k_m in [0, n) such that at every time ℓ = 1, …, n−1

  |Ŝ(ℓ)| = |(1/m) · Σⱼ e^{2πi·kⱼ·ℓ/n}| ≤ ε,

using as few coefficients m as possible. Think of each kⱼ as a clock hand that turns kⱼ/n of a turn per tick: Ŝ(ℓ) is the average of the hands at time ℓ, and we want the hands spread around the dial at every time. At time 0 the average is automatically 1.

**Construction.**
1. Take the |P| smallest primes above R = ⌈4·ln n/ε⌉ + 16 that do not divide n, where |P| ≈ 3·log_R(n)/ε. Call this set of primes P and its largest element P_max.
2. Choose a short list of small whole numbers, the multipliers c₁, …, c_s, by a greedy search. Each step adds the multiplier that keeps all the running totals most balanced. No randomness is involved.
3. The coefficients are all products c·q⁻¹ mod n, one for each chosen prime q and each multiplier c. Here q⁻¹ is the u with q·u ≡ 1 (mod n). The products for one prime q form the group S_q, so m = |P|·s.

**Error.** At most ε at every time ℓ ≠ 0. At most ε/3 comes from the few bad groups, whose prime divides ℓ, and at most 2ε/3 from all the other groups.

**Count.** The count grows like log n/ε³. For error 0.2:

| guarantee | n = 2²⁴ | n = 2⁶⁴ |
|---|---|---|
| proved for every n, exact formula m = \|P\|·s | 98,859 | 302,302 |
| proved for every n, closed form 235·(ln n + 2)/ε³ | 5.5·10⁵ | 1.4·10⁶ |
| proved by computer for one specific set (certificate) | 5,704 | 19,838 |
| measured exactly | 434 | – |

The proved bound is about 15–17× above the computer certificate and about 230× above the measured size, because two steps of the proof are worst-case (see Remark 3).

**Limits** (proved in `lower-bounds.md`).
- Fewer than log₂(n)/3 coefficients always give error above 0.707.
- Exactly log₂ n coefficients always give error at least about 0.3.
- m coefficients give error at least √((n − m)/(m(n − 1))), which is about 1/√m when m is much smaller than n.

The slideshow `tutorial.html` explains the same proof step by step, with the same notation.

---

## Notation

- **Hands.** e(x) = e^{2πix} is a hand of length 1 that has turned x full turns counter-clockwise from pointing right. ‖x‖ is the distance from x to the nearest integer: how far e(x) is from pointing right, in turns.
- **Averages at a time.** For a multiset S ⊆ ℤₙ and a time ℓ, Ŝ(ℓ) = (1/|S|) Σ_{k∈S} e(ℓk/n) is the average of S's hands at time ℓ, and bias(S) = max_{ℓ ≢ 0 (mod n)} |Ŝ(ℓ)|. The hat always means "average at time ℓ".
- **Signed numbers.** For q coprime to n, q⁻¹ is the inverse of q mod n. For a residue y mod n, y* is its representative in (−n/2, n/2]; for n = 2ʳ this is the two's-complement reading.
- **Groups.** For a list C of s multipliers and a prime q ∤ n, the group of q is the multiset S_q = { c·q⁻¹ mod n : c ∈ C }, and Ŝ_q(ℓ) is its average at time ℓ.
- **Base hand.** The base hand of group q is the hand q⁻¹ (multiplier 1). At time ℓ it points at ℓ·q⁻¹/n turns (reducing ℓ·q⁻¹ mod n only removes whole turns). Hand c of the group turns exactly c times as fast, so it points at e(c·ℓ·q⁻¹/n).
- **Group average at a base angle.** For a real angle a, the hands at c·a for c ∈ C average to (1/s) Σ_{c∈C} e(c·a). It depends only on a mod 1, and the average at −a is the complex conjugate of the average at a.

## Theorem

Let n ≥ 2 and 0 < ε ≤ 1. The construction below is fully determined, runs in time poly(log n, 1/ε), and outputs a multiset S ⊆ ℤₙ with

  bias(S) ≤ ε,  |S| = |P|·s ≤ 235 · (ln n + 2) / ε³.

## Construction

| symbol | value | role |
|---|---|---|
| R | ⌈4·ln n/ε⌉ + 16 | primes are taken above R |
| K | ⌊log_{R+1}(n/2)⌋ | maximum number of bad groups at one time (Lemma 2) |
| \|P\| | ⌊3K/ε⌋ + 1 | number of primes, one group each |
| P | the \|P\| smallest primes in (R, R²] not dividing n | the primes (Lemma 4 shows there are enough) |
| P_max | max P | largest prime used |
| δ | 1/(2P_max) | width of the excused zone around "pointing right" |
| N, M | ⌈300·P_max/ε⌉, ⌈1000N/ε⌉ | size of the candidate pool {0, …, N−1}; resolution of the grid of base angles |
| D, t | 16, 5ε/8 | number of compass directions; sharpness of the exponential |
| s | ⌈2·ln(16(M+1))/t²⌉ | number of multipliers |

- **Multipliers.** C is the greedy list of Lemma 3 with these parameters.
- **Output.** S is the union of the groups: S = { c·q⁻¹ mod n : q ∈ P, c ∈ C }, as a multiset.
- **Credit.** The outer layer (inverses of many primes, with Lemma 2 counting the bad ones) is the method of Ajtai, Iwaniec, Komlós, Pintz and Szemerédi [AIKPS90]. Remark 4 compares the two constructions.

## Lemma 1 (the hands split into groups)

For every time ℓ,

  Ŝ(ℓ) = (1/|P|) Σ_{q∈P} Ŝ_q(ℓ),  and  Ŝ_q(ℓ) = (1/s) Σ_{c∈C} e(c·ℓ·q⁻¹/n).

*Proof.* All |P| groups have the same size s, so the average over S is the average of the group averages. Hand c of group q is c·q⁻¹ mod n. At time ℓ it has turned ℓ·(c·q⁻¹ mod n)/n turns, and reducing mod n changes this only by an integer number of turns. So it points at e(c·ℓ·q⁻¹/n), and averaging over c gives the second formula. ∎

## Lemma 2 (few bad groups)

Let ℓ ≢ 0 (mod n), and suppose every prime in P is greater than R and at most P_max. Call q ∈ P **bad** at time ℓ if its base hand is in the excused zone: ‖ℓ·q⁻¹/n‖ < δ = 1/(2P_max).

**(a)** If q is bad at time ℓ, then q divides ℓ*.

**(b)** At most ⌊log_{R+1}(n/2)⌋ = K primes of P are bad at time ℓ.

*Proof.*
- (a) Let d = (ℓ·q⁻¹)*, the signed value of ℓ·q⁻¹ mod n. Then ‖ℓ·q⁻¹/n‖ = |d|/n, so bad means |d| < n/(2P_max). Multiplying by q gives ℓ* ≡ q·d (mod n), and |q·d| < n/2 because q ≤ P_max. Both ℓ* and q·d lie in (−n/2, n/2] and agree mod n, so ℓ* = q·d.
- (b) The bad primes are distinct primes greater than R, and all of them divide the nonzero integer ℓ*. So their product divides ℓ*, and (R+1)^{#bad} ≤ |ℓ*| ≤ n/2. ∎

This plays the role of "a nonzero polynomial of degree < r has fewer than r roots" in Reed–Solomon codes. The same count, for a prime modulus, is the core of [AIKPS90]; see [BDFKK11, Lemma 12].

## Lemma 3 (greedy multipliers)

**Setup.** Let D ≥ 3, t > 0, δ > 0 and Mδ ≥ 2.
- **Grid of base angles:** Γ = { j/M : j ∈ {0, …, M}, δ/2 ≤ j/M ≤ ½ }.
- **Checks and reaches:** the compass directions are ω_u = e(−u/D) for u = 0, …, D−1. A check is a pair (a, u) with a ∈ Γ, and the reach of multiplier c in that check is X_{a,u}(c) = Re(ω_u·e(c·a)) ∈ [−1, 1]: how far hand c reaches in direction u when the base hand points at a.
- **Potential:** for a partial list cs, the running total of check (a, u) is Σ_{c∈cs} X_{a,u}(c), and

  Φ(cs) = Σ_{a∈Γ} Σ_u exp( t · Σ_{c∈cs} X_{a,u}(c) ).

- **Greedy step:** append the least c ∈ {0, …, N−1} that minimises Φ(cs + c). Repeat s times. The result is the multiplier list C.

**Claim.** For every real base angle a with δ ≤ ‖a‖ ≤ ½:

  |(1/s) Σ_{c∈C} e(c·a)| ≤ B / cos(π/D) + 2πN/M,  where B = ln(D(M+1))/(ts) + t/2 + sinh(t)/(t·N·δ).

*Proof.*
1. **Small means.** For a ∈ [δ/2, ½], |e(a) − 1| = 2 sin(πa) ≥ 4a. So the geometric sum gives |E_{c<N} e(c·a)| ≤ 1/(2Na) ≤ 1/(Nδ). Hence for every check, the reach X_{a,u} has mean at most 1/(Nδ) in absolute value over the pool.
2. **One step.** For X ∈ [−1, 1], convexity of exp gives e^{tX} ≤ cosh t + X·sinh t. If X has mean μ, then E e^{tX} ≤ cosh t + |μ| sinh t ≤ exp(t²/2 + |μ| sinh t), using cosh t ≤ e^{t²/2} and 1 + y ≤ eʸ. The minimiser does at least as well as the average candidate, so each step multiplies Φ by at most exp(t²/2 + sinh(t)/(Nδ)).
3. **Final potential.** Φ starts at D·|Γ| ≤ D(M+1), so after s steps Φ ≤ D(M+1)·exp(s·(t²/2 + sinh(t)/(Nδ))).
4. **Every check passes.** Each term of the final Φ is at most Φ. Taking logs and dividing by t·s, the average reach Re(ω_u·(1/s)Σ_{c∈C} e(c·a)) is at most B, for every a ∈ Γ and every u.
5. **From reaches to lengths.** For any complex z, rounding the argument of z to the nearest multiple of 2π/D gives a u with Re(ω_u·z) ≥ |z|·cos(π/D). Hence |(1/s)Σ_{c∈C} e(c·a)| ≤ B/cos(π/D) for every a ∈ Γ.
6. **Off the grid.** For δ ≤ a ≤ ½, the grid angle a′ = ⌊aM⌋/M lies in Γ, because Mδ ≥ 2, and |a − a′| ≤ 1/M. Since every c is below N, the group average changes by at most 2πN·|a − a′| ≤ 2πN/M. For other a with δ ≤ ‖a‖ ≤ ½, use that the average depends only on a mod 1 and that the average at −a is the complex conjugate of the average at a. ∎

## Lemma 4 (enough primes)

For R ≥ 16, the interval (R, R²] contains at least R − 1 − ⌊log_{R+1} n⌋ primes that do not divide n.

*Proof.*
- 2^R ≥ R⁴ for R ≥ 16, by induction, since (R+1)⁴ ≤ 2R⁴. So R·ln 2 ≥ 4·ln R.
- Chebyshev's bound then gives π(R²) ≥ R²·ln 2/ln(R²) = R²·ln 2/(2·ln R) ≥ 2R.
- At most R + 1 of these primes are ≤ R.
- At most ⌊log_{R+1} n⌋ primes above R divide n, because their product divides n.

So at least 2R − (R + 1) − ⌊log_{R+1} n⌋ remain. ∎

## Proof of the theorem

**Enough primes.** Let L = ⌊log_{R+1} n⌋. Since R + 1 ≥ 17, L ≤ ln n/ln 17 < ln n/2.77. Also K ≤ L, so |P| = ⌊3K/ε⌋ + 1 ≤ 3L/ε + 1. Since R ≥ 4·ln n/ε + 16, we get R − 1 − L ≥ |P|, and Lemma 4 gives at least that many candidates. Hence P exists, every q ∈ P satisfies R < q ≤ P_max ≤ R², and P_max ≥ 17.

**Bias.** Fix a time ℓ ≢ 0. By Lemma 1, |Ŝ(ℓ)| ≤ (1/|P|) Σ_q |Ŝ_q(ℓ)|.
- By Lemma 2, at most K groups are bad, and each has |Ŝ_q(ℓ)| ≤ 1. Since |P| > 3K/ε, they contribute at most K/|P| < ε/3.
- Every other group has its base hand at δ ≤ ‖ℓ·q⁻¹/n‖ ≤ ½. By Lemma 1, Ŝ_q(ℓ) is the group average at base angle a = ℓ·q⁻¹/n, so Lemma 3 bounds |Ŝ_q(ℓ)|. With our parameters that bound is at most 2ε/3:
  - ln(16(M+1))/(ts) ≤ t/2 by the choice of s, so the first two terms of B total at most t = 5ε/8.
  - sinh(t)/(tNδ) = (2P_max/N)·sinh(t)/t ≤ (ε/150)·(3/2) = ε/100, using sinh t ≤ 1.5t for t ≤ 1.
  - cos(π/16) ≥ 1 − (π/16)²/2 ≥ 49/50, and 2πN/M ≤ 2πε/1000 < 0.0064ε.
  - So the bound is at most (0.635ε)/(0.98) + 0.0064ε < 0.655ε < 2ε/3.
- Also Mδ = M/(2P_max) ≥ 300·1000/(2ε²) ≥ 2, as Lemma 3 requires.

So |Ŝ(ℓ)| < ε/3 + 2ε/3 = ε.

**Size.** |S| = |P|·s exactly. For the closed form:
- |P| ≤ 3·ln n/(ε·ln R) + 1.
- Using P_max ≤ R², 1/ε ≤ R and R ≥ 16, we get 16(M+1) ≤ R¹⁰, hence s ≤ 52·ln R/ε².
- So |P|·s ≤ 52·(3·ln n/ε + ln R)/ε².
- Finally ln R ≤ R/e ≤ (4·ln n/ε + 17)/2.7, which gives |S| ≤ 235·(ln n + 2)/ε³.

**Running time.**
- The candidate primes lie below R² = O((log n/ε)²).
- The greedy search takes s steps, each trying N candidates against D·|Γ| checks, which is poly(log n/ε).
- Each coefficient costs one modular inverse and one multiplication mod n.

So the total is poly(log n, 1/ε). ∎

## Formal verification

Everything above is machine-checked in Lean 4 + Mathlib; see `lean/` and `lean/README.md`. The file structure follows this document:

| file | content |
|---|---|
| `Core.lean` | Lemma 1, Lemma 2 |
| `Greedy.lean` | Lemma 3 for general D, including the direction-rounding argument of step 5 |
| `Main.lean` | Lemma 4, parameters, the theorem |

- **Theorems:** `main_bias`, `main_size_exact` (|S| = |P|·s) and `main_size` (the closed form).
- **Final statement:** `explicitList_spec`, written only in terms of `Complex.exp`, lists and `Real.log`.
- **Axioms:** `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`, and Lean reports no warnings; Lake only notes that the files are not written as Mathlib modules.
- **Not formalized:** the running time. The definition is `noncomputable` because it compares real numbers, but it determines the set uniquely.

The Lean names follow this document's notation:

| this document | Lean |
|---|---|
| e(x) | `e x` |
| Ŝ(ℓ), the average of S at time ℓ | `avgAt T k ℓ` |
| S, the union of the groups S_q | `hand C` on `P ×ˢ univ`: the map (q, i) ↦ C_i·q⁻¹ |
| ℓ·q⁻¹/n, as a signed angle | `angle (ℓ * (q : ZMod n)⁻¹)`, where `angle y = y.valMinAbs / n` |
| group average at base angle a, (1/s) Σ_{c∈C} e(c·a) | `groupAvg C a` |
| Lemma 1 | `avgAt_hand` |
| Lemma 2 (a), (b) | `dvd_of_angle_small`, `card_bad_le` |
| ω_u, compass direction u | `dir D u` |
| reach X_{a,u}(c), with a = j/M | `reach D M j u c` |
| Φ, the greedy multipliers | `Φ`, `greedyList D N M δ t s` |
| Lemma 3 | `greedy_mult_bound` |
| Lemma 4 | `card_candidates_ge` |
| R, \|P\|, P, P_max, N, M, s, C | `Rpar`, `numPrimes`, `primes`, `Pmax`, `Npar`, `Mpar`, `spar`, `multList` |

## Numerical check

These numbers come from `experiment.py` (`smallbias.py`); the full output is in `results.txt`.
- **Same primes, smaller search.** The code uses the theorem's R, K and primes, with |P| = ⌊3K/ε⌋ + 1. Only the search for multipliers is smaller: a pool of N = 16·P_max candidates, a grid of a prime M ≈ 4N base angles (FFT-accelerated), 8 directions and t = 0.6ε. The theorem's search is not practical. For n = 2⁶⁴ and ε = 0.2 it would have N ≈ 2.3·10⁶ and M ≈ 1.2·10¹⁰, which needs about 2·10¹⁶ operations even with the FFT, and 1.5 TB of memory.
- **"Certified" means a computed bound.** The certificate is a proof-level upper bound on the bias of the specific set the code outputs. It is computed from Lemma 1, Lemma 2 at every threshold, and an exact fine-grid evaluation of the group average with a Lipschitz correction. Let W(y) be the largest length of the group average (1/s)Σ_{c∈C} e(c·a) over base angles with ‖a‖ ≥ y. The thresholds y₀ < y₁ < … < y_m are combined by Abel summation: E_q W(‖ℓ·q⁻¹/n‖) ≤ W(y_m) + Σᵢ (W(yᵢ) − W(yᵢ₊₁))·Pr_q[‖ℓ·q⁻¹/n‖ < yᵢ₊₁]. The code keeps the shortest prefix of the greedy list whose certificate is ≤ ε.
- **Deterministic.** Every run outputs the same set, and building one takes 2–115 s on this machine.

| r = log₂ n | 16 | 24 | 32 | 48 | 64 | 96 | 128 | 192 | 256 |
|---|---|---|---|---|---|---|---|---|---|
| certified bias ≤ 0.3: \|S\|/r | 64 | 62 | 72 | 85 | 80 | 89 | 101 | 108 | 104 |
| certified bias ≤ 0.2: \|S\|/r | 154 | 238 | 253 | 244 | 310 | 306 | 332 | 326 | 336 |

**Exact bias,** checked by FFT where n is small enough:
- The certified sets for r = 16 and 24 have exact bias 0.09–0.15, about half of their certificates.
- The smallest sets found with exact bias ≤ 0.2 have |S| = 272, 525 and 434 for r = 16, 20 and 24. That is about 20 · log₂ n. They come from prefixes of the same greedy list, with |P| = ⌊a·K/ε⌋ + 1 for a ∈ {0.5, 1, 2, 3}.

**The formal construction's own sizes,** from the exact formula m = |P|·s:

| | n = 2²⁴ | n = 2⁶⁴ | n = 2²⁵⁶ |
|---|---|---|---|
| ε = 0.2 | 98,859 | 302,302 | 1,106,316 |
| ε = 0.1 | 842,959 | 2,163,679 | 8,599,831 |

## Remarks

1. **Code analogy.** The primes act as an outer code, and Lemma 2 is its distance bound. The greedy multipliers are an inner code, found by search because the inner problem has size only poly(log n/ε). This mirrors the classical concatenation that gives ε-biased sets of size O(r/ε³) in 𝔽₂^r.

2. **Size versus time.** Taking primes above a larger R needs fewer groups, so the set gets smaller, but the multipliers then range up to about R/ε, so the search gets slower. With a single prime q > n/2, no group is ever bad, and the set q⁻¹·C has size O(log n/ε²). But that search runs over all of ℤₙ, which takes time polynomial in n. This direct search is how Khadieva and Ziatdinov [KZ22] choose the coefficients of quantum fingerprinting automata over ℤ_p, using the pessimistic estimators of Wigderson and Xiao [WX08]. Their potential reduces, up to a constant term, to Σ_{j≠0} exp(t·Σᵢ cos(2π·kᵢ·j/p)): the Φ of Lemma 3 with one check per time j and a single direction. The primes exist only to make the construction fast.

3. **What is still loose.** The proved size is about 230× above what is measured. Two worst-case steps cause this:
   - the multipliers' guarantee is a union bound over every check (grid angle, direction);
   - every bad group is charged the full 1, although its hands are often already spread out.

   The computer certificate recovers part of the gap by checking the actual set.

4. **Prior work.** The outer layer and Lemma 2 are not new. They are the method of Ajtai, Iwaniec, Komlós, Pintz and Szemerédi [AIKPS90], as presented by Bourgain, Dilworth, Ford, Konyagin and Kutzarova [BDFKK11, §7]. In the notation here, their basic step [BDFKK11, Lemma 12] takes a prime modulus n and the multiset

   { r + c·q⁻¹ mod n : 1 ≤ r ≤ R′, q a prime in (P_max/2, P_max], c ∈ C_q },

   where each C_q is a list of integers in (−q/2, q/2) whose average is small at every nonzero multiple of 1/q. A prime is bad at time ℓ only if it divides ℓ, and few large primes divide one number. The differences:
   - **Inner lists.** There, each prime needs its own list C_q, built by applying the same step again. Consecutive multipliers give size about log² n/(ε² log log n) [BDFKK11, Cor. 5]. Two levels give about log n·log log n/ε⁴ [BDFKK11, Thm. 2]. Iterating all the way gives size log n·(log* n)^{O(log* n)} with bias O(1/log* n) [AIKPS90]. Here one list C serves every prime and covers every real base angle in [δ, ½]. The greedy search finds it in time poly(log n/ε), which removes the iterated logarithms.
   - **Base angle.** For prime n they use the identity ℓ·(q⁻¹ mod n)/n ≡ −ℓ·(n⁻¹ mod q)/q + ℓ/(qn) (mod 1). So the base hand sits at a multiple of 1/q plus a drift ℓ/(qn), and the shifts r handle the drift. Here nothing is reduced mod q: Lemma 3 covers all real angles directly.
   - **Modulus.** [AIKPS90] and [BDFKK11] assume n is prime; Razborov, Szemerédi and Wigderson [RSW93] treat composite moduli separately. Lemma 2(a) here works for every n through signed representatives.

   What may be new is only the combination: one searched inner list instead of recursion, giving O(log n/ε³) deterministically in time poly(log n/ε) for every n. The step is natural, so it may already be known; I have not found it written down. The Lean proof settles correctness, not novelty.

5. **Next step.** Using S with constant ε as the starting set for the Ta-Shma [TS17] / Jalan–Moshkovitz [JM21] amplification should give O(log n/ε^{2+o(1)}). That amplification sums elements mod n along expander walks.

## References

- [AIKPS90] M. Ajtai, H. Iwaniec, J. Komlós, J. Pintz, E. Szemerédi. Construction of a thin set with small Fourier coefficients. *Bull. London Math. Soc.* 22 (1990), 583–590.
- [BDFKK11] J. Bourgain, S. J. Dilworth, K. Ford, S. Konyagin, D. Kutzarova. Explicit constructions of RIP matrices and related problems. *Duke Math. J.* 159 (2011), 145–185. arXiv:1008.4535.
- [KZ22] A. Khadieva, M. Ziatdinov. Deterministic construction of QFAs based on the quantum fingerprinting technique. arXiv:2212.14442 (2022); *Lobachevskii J. Math.* 44 (2023), 713–723.
- [WX08] A. Wigderson, D. Xiao. Derandomizing the Ahlswede–Winter matrix-valued Chernoff bound using pessimistic estimators, and applications. *Theory of Computing* 4 (2008), 53–76.
- [RSW93] A. Razborov, E. Szemerédi, A. Wigderson. Constructing small sets that are uniform in arithmetic progressions. *Combin. Probab. Comput.* 2 (1993), 513–518.
- [TS17] A. Ta-Shma. Explicit, almost optimal, epsilon-balanced codes. *STOC 2017*.
- [JM21] A. Jalan, D. Moshkovitz. Near-optimal Cayley expanders for abelian groups. *FSTTCS 2021*. arXiv:2105.01149.
