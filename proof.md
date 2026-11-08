# Small-bias sets in ℤₙ of size O(log n / ε³)

## Summary in plain language

**Goal.** Deterministically choose integers k₁, …, k_m in [0, n) such that for every l = 1, …, n−1

  |(1/m) · Σⱼ e^{2πi·kⱼ·l/n}| ≤ ε,

using as few coefficients m as possible. For l = 0 the average is automatically 1.

**Construction.**
1. Take the k smallest primes above R = ⌈4·ln n/ε⌉ + 16 that do not divide n, where k ≈ 3·log_R(n)/ε.
2. Choose a short list of small numbers c₁, …, c_s by a greedy search. Each step adds the number that keeps all the test sums most balanced. No randomness is involved.
3. The coefficients are all products c·q⁻¹ mod n, one for each chosen prime q and each c in the list. Here q⁻¹ is the u with q·u ≡ 1 (mod n). So m = k·s.

**Error.** At most ε for every l ≠ 0. At most ε/3 comes from the few primes that divide the frequency, and at most 2ε/3 from the inner list.

**Count.** The count grows like log n/ε³. For error 0.2:

| guarantee | n = 2²⁴ | n = 2⁶⁴ |
|---|---|---|
| proved for every n, exact formula m = k·s | 98,859 | 302,302 |
| proved for every n, closed form 235·(ln n + 2)/ε³ | 5.5·10⁵ | 1.4·10⁶ |
| proved by computer for one specific set (certificate) | 5,704 | 19,838 |
| measured exactly | 434 | – |

The proved bound is about 15–17× above the computer certificate and about 230× above the measured size, because two steps of the proof are worst-case (see Remark 3).

**Limits** (proved in `lower-bounds.md`).
- Fewer than log₂(n)/3 coefficients always give error above 0.707.
- Exactly log₂ n coefficients always give error at least about 0.3.
- m coefficients give error at least √((n − m)/(m(n − 1))), which is about 1/√m when m is much smaller than n.

---

## Notation

- e(x) = e^{2πix}, and ‖x‖ = distance from x to the nearest integer.
- For a multiset S ⊆ ℤₙ: Ŝ(ℓ) = (1/|S|) Σ_{k∈S} e(ℓk/n), and bias(S) = max_{ℓ ≢ 0 (mod n)} |Ŝ(ℓ)|.
- For a list C of integers and real β: Ĉ(β) = (1/|C|) Σ_{c∈C} e(cβ).
- For q coprime to n, q̄ = q⁻¹ mod n.

## Theorem

Let n ≥ 2 and 0 < ε ≤ 1. The construction below is fully determined, runs in time poly(log n, 1/ε), and outputs a multiset S ⊆ ℤₙ with

  bias(S) ≤ ε,  |S| = k·s ≤ 235 · (ln n + 2) / ε³.

## Construction

| symbol | value | role |
|---|---|---|
| R | ⌈4·ln n/ε⌉ + 16 | primes are taken above R |
| K | ⌊log_{R+1}(n/2)⌋ | maximum number of bad primes (Lemma 2) |
| k | ⌊3K/ε⌋ + 1 | number of primes |
| P | the k smallest primes in (R, R²] not dividing n | outer set (Lemma 4 shows there are enough) |
| Q | max P | largest prime used |
| δ | 1/(2Q) | threshold for "tiny" steps |
| N, M | ⌈300Q/ε⌉, ⌈1000N/ε⌉ | range of inner numbers; grid resolution |
| D, t | 16, 5ε/8 | number of directions; potential parameter |
| s | ⌈2·ln(16(M+1))/t²⌉ | length of the inner list |

- **Inner list.** C is the greedy list of Lemma 3 with these parameters.
- **Output.** S = { c·q̄ mod n : q ∈ P, c ∈ C }.

## Lemma 1 (product structure)

For every ℓ, Ŝ(ℓ) = (1/|P|) Σ_{q∈P} Ĉ(β_q), where β_q = ℓq̄/n.

*Proof.* Replacing c·q̄ by c·q̄ mod n changes ℓ·c·q̄/n by an integer, so e(ℓ·(c q̄ mod n)/n) = e(c·β_q). Averaging over c gives Ĉ(β_q), and averaging over q gives the claim. ∎

## Lemma 2 (few bad primes)

Let ℓ ≢ 0 (mod n), and let ℓ* be its representative in (−n/2, n/2]. Suppose every prime in P is greater than R and at most Q.

**(a)** If ‖β_q‖ < 1/(2Q), then q divides ℓ*.

**(b)** At most ⌊log_{R+1}(n/2)⌋ = K primes of P are bad, meaning ‖β_q‖ < δ.

*Proof.*
- (a) ℓq̄ ≡ t (mod n) for some integer t with |t| < n/(2Q). Multiplying by q gives ℓ* ≡ tq (mod n). Both ℓ* and tq lie in (−n/2, n/2], so ℓ* = tq.
- (b) The bad primes are distinct primes greater than R, and all of them divide the nonzero integer ℓ*. So their product divides ℓ*, and (R+1)^{#bad} ≤ |ℓ*| ≤ n/2. ∎

This plays the role of "a nonzero polynomial of degree < r has fewer than r roots" in Reed–Solomon codes.

## Lemma 3 (greedy inner list)

**Setup.** Let D ≥ 3, t > 0, δ > 0 and Mδ ≥ 2.
- Grid: Γ = { k/M : k ∈ {0, …, M}, δ/2 ≤ k/M ≤ ½ }.
- Directions: ω_u = e(−u/D) for u = 0, …, D−1, and X_{γ,u}(c) = Re(ω_u·e(cγ)) ∈ [−1, 1].
- Potential of a partial list cs:

  Φ(cs) = Σ_{γ∈Γ} Σ_u exp( t · Σ_{c∈cs} X_{γ,u}(c) ).

- Greedy step: append the least c ∈ {0, …, N−1} that minimises Φ(cs + c). Repeat s times.

**Claim.** For every β with δ ≤ |β| ≤ ½:

  |Ĉ(β)| ≤ A / cos(π/D) + 2πN/M,  where A = ln(D(M+1))/(ts) + t/2 + sinh(t)/(t·N·δ).

*Proof.*
1. **Small means.** For γ ∈ [δ/2, ½], |e(γ) − 1| = 2 sin(πγ) ≥ 4γ. So the geometric sum gives |E_{c<N} e(cγ)| ≤ 1/(2Nγ) ≤ 1/(Nδ). Hence every X_{γ,u} has mean at most 1/(Nδ) in absolute value.
2. **One step.** For X ∈ [−1, 1], convexity of exp gives e^{tX} ≤ cosh t + X·sinh t. If X has mean μ, then E e^{tX} ≤ cosh t + |μ| sinh t ≤ exp(t²/2 + |μ| sinh t), using cosh t ≤ e^{t²/2} and 1 + y ≤ eʸ. The minimiser does at least as well as the average, so each step multiplies Φ by at most exp(t²/2 + sinh(t)/(Nδ)).
3. **Final potential.** Φ starts at D·|Γ| ≤ D(M+1), so after s steps Φ ≤ D(M+1)·exp(s·(t²/2 + sinh(t)/(Nδ))).
4. **Balanced in every direction.** Each term of the final Φ is at most Φ. Taking logs, Re(ω_u·Ĉ(γ)) ≤ A for every γ ∈ Γ and every u.
5. **From directions to lengths.** For any complex z, rounding the argument of z to the nearest multiple of 2π/D gives a u with Re(ω_u·z) ≥ |z|·cos(π/D). Hence |Ĉ(γ)| ≤ A/cos(π/D).
6. **Off the grid.** For δ ≤ β ≤ ½, the grid point γ = ⌊βM⌋/M lies in Γ, because Mδ ≥ 2. It satisfies |β − γ| ≤ 1/M. Since every c is below N, |dĈ/dβ| ≤ 2πN. For negative β, use that Ĉ(−β) is the complex conjugate of Ĉ(β). ∎

## Lemma 4 (enough primes)

For R ≥ 16, the interval (R, R²] contains at least R − 1 − ⌊log_{R+1} n⌋ primes that do not divide n.

*Proof.*
- 2^R ≥ R⁴ for R ≥ 16, by induction, since (R+1)⁴ ≤ 2R⁴. So R·ln 2 ≥ 4·ln R.
- Chebyshev's bound then gives π(R²) ≥ R²·ln 2/ln(R²) = R²·ln 2/(2·ln R) ≥ 2R.
- At most R + 1 of these primes are ≤ R.
- At most ⌊log_{R+1} n⌋ primes above R divide n, because their product divides n.

So at least 2R − (R + 1) − ⌊log_{R+1} n⌋ remain. ∎

## Proof of the theorem

**Enough primes.** Let L = ⌊log_{R+1} n⌋. Since R + 1 ≥ 17, L ≤ ln n/ln 17 < ln n/2.77. Also K ≤ L, so k ≤ 3L/ε + 1. Since R ≥ 4·ln n/ε + 16, we get R − 1 − L ≥ k, and Lemma 4 gives at least k candidates. Hence |P| = k, every q ∈ P satisfies R < q ≤ Q ≤ R², and Q ≥ 17.

**Bias.** Fix ℓ ≢ 0. By Lemma 1, |Ŝ(ℓ)| ≤ (1/k) Σ_q |Ĉ(β_q)|.
- By Lemma 2, at most K primes are bad, and each contributes at most 1. Since k > 3K/ε, these contribute at most K/k < ε/3.
- Every other prime has δ ≤ ‖β_q‖ ≤ ½, so it contributes at most the bound of Lemma 3. With our parameters that bound is at most 2ε/3:
  - ln(16(M+1))/(ts) ≤ t/2 by the choice of s, so the first two terms of A total at most t = 5ε/8.
  - sinh(t)/(tNδ) = (2Q/N)·sinh(t)/t ≤ (ε/150)·(3/2) = ε/100, using sinh t ≤ 1.5t for t ≤ 1.
  - cos(π/16) ≥ 1 − (π/16)²/2 ≥ 49/50, and 2πN/M ≤ 2πε/1000 < 0.0064ε.
  - So the bound is at most (0.635ε)/(0.98) + 0.0064ε < 0.655ε < 2ε/3.
- Also Mδ = M/(2Q) ≥ 300·1000/(2ε²) ≥ 2, as Lemma 3 requires.

So |Ŝ(ℓ)| < ε/3 + 2ε/3 = ε.

**Size.** |S| = k·s exactly. For the closed form:
- k ≤ 3·ln n/(ε·ln R) + 1.
- Using Q ≤ R², 1/ε ≤ R and R ≥ 16, we get 16(M+1) ≤ R¹⁰, hence s ≤ 52·ln R/ε².
- So k·s ≤ 52·(3·ln n/ε + ln R)/ε².
- Finally ln R ≤ R/e ≤ (4·ln n/ε + 17)/2.7, which gives |S| ≤ 235·(ln n + 2)/ε³.

**Running time.**
- The candidate primes lie below R² = O((log n/ε)²).
- The greedy search takes s steps, each trying N candidates against D·|Γ| terms, which is poly(log n/ε).
- Each coefficient costs one modular inverse and one multiplication mod n.

So the total is poly(log n, 1/ε). ∎

## Formal verification

Everything above is machine-checked in Lean 4 + Mathlib; see `lean/` and `lean/README.md`. The file structure follows this document:

| file | content |
|---|---|
| `Core.lean` | Lemma 1, Lemma 2 |
| `Greedy.lean` | Lemma 3 for general D, including the direction-rounding argument of step 5 |
| `Main.lean` | Lemma 4, parameters, the theorem |

- **Theorems:** `main_bias`, `main_size_exact` (|S| = k·s) and `main_size` (the closed form).
- **Final statement:** `explicitList_spec`, written only in terms of `Complex.exp`, lists and `Real.log`.
- **Axioms:** `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`, and the build has no warnings.
- **Not formalized:** the running time. The definition is `noncomputable` because it compares real numbers, but it determines the set uniquely.

## Numerical check

These numbers come from `experiment.py` (`smallbias.py`); the full output is in `results.txt`.
- **Same outer structure, smaller search.** The code uses the theorem's R, K and primes, with k = ⌊3K/ε⌋ + 1. Only the inner search is smaller: N = 16Q candidates, a grid of a prime M ≈ 4N points (FFT-accelerated), 8 directions and t = 0.6ε. The theorem's search is not practical. For n = 2⁶⁴ and ε = 0.2 it would have N ≈ 2.3·10⁶ and M ≈ 1.2·10¹⁰, which needs about 2·10¹⁶ operations even with the FFT, and 1.5 TB of memory.
- **"Certified" means a computed bound.** The certificate is a proof-level upper bound on the bias of the specific set the code outputs. It is computed from Lemma 1, Lemma 2 at every threshold, and an exact fine-grid evaluation of Ĉ with a Lipschitz correction. The thresholds are combined by Abel summation: E_q G(X_q) ≤ G(x_m) + Σᵢ (G(xᵢ) − G(xᵢ₊₁))·Pr[X < xᵢ₊₁], with G(x) = sup over ‖β‖ ≥ x of |Ĉ(β)|. The code keeps the shortest prefix of the greedy list whose certificate is ≤ ε.
- **Deterministic.** Every run outputs the same set, and building one takes 2–115 s on this machine.

| r = log₂ n | 16 | 24 | 32 | 48 | 64 | 96 | 128 | 192 | 256 |
|---|---|---|---|---|---|---|---|---|---|
| certified bias ≤ 0.3: \|S\|/r | 64 | 62 | 72 | 85 | 80 | 89 | 101 | 108 | 104 |
| certified bias ≤ 0.2: \|S\|/r | 154 | 238 | 253 | 244 | 310 | 306 | 332 | 326 | 336 |

**Exact bias,** checked by FFT where n is small enough:
- The certified sets for r = 16 and 24 have exact bias 0.09–0.15, about half of their certificates.
- The smallest sets found with exact bias ≤ 0.2 have |S| = 272, 525 and 434 for r = 16, 20 and 24. That is about 20 · log₂ n. They come from prefixes of the same greedy list, with k from a ∈ {0.5, 1, 2, 3}.

**The formal construction's own sizes,** from the exact formula m = k·s:

| | n = 2²⁴ | n = 2⁶⁴ | n = 2²⁵⁶ |
|---|---|---|---|
| ε = 0.2 | 98,859 | 302,302 | 1,106,316 |
| ε = 0.1 | 842,959 | 2,163,679 | 8,599,831 |

## Remarks

1. **Code analogy.** The primes act as an outer code, and Lemma 2 is its distance bound. The greedy list is an inner code, found by search because the inner problem has size only poly(log n/ε). This mirrors the classical concatenation that gives ε-biased sets of size O(r/ε³) in 𝔽₂^r.

2. **Size versus time.** Taking primes above a larger R needs fewer primes, so the set gets smaller, but the inner search runs over numbers up to about R/ε, so it gets slower. With a single prime q > n/2, no prime is ever bad, and the set q⁻¹·C has size O(log n/ε²). But that search runs over all of ℤₙ, which takes time polynomial in n. The primes exist only to make the construction fast.

3. **What is still loose.** The proved size is about 230× above what is measured. Two worst-case steps cause this:
   - the inner list's guarantee is a union bound over every grid frequency;
   - every bad prime is charged the full 1.

   The computer certificate recovers part of the gap by checking the actual set.

4. **Literature.** I have not found this construction in the literature. Published explicit constructions for cyclic groups that I know of have size polylog(n)/ε² or log n·ε^{−O(log* n)}. The Lean proof settles correctness, so the open question is novelty.

5. **Next step.** Using S with constant ε as the starting set for the Ta-Shma / Jalan–Moshkovitz amplification should give O(log n/ε^{2+o(1)}). That amplification sums elements mod n along expander walks.
