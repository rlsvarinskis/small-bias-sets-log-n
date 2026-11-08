# Small-bias sets in ℤₙ of size O(log n / ε³)

## Summary in plain language

**Goal.** Deterministically choose integers k₁, …, k_m in [0, n) such that for every l = 1, …, n−1

  |(1/m) · Σⱼ e^{2πi·kⱼ·l/n}| ≤ ε,

using as few coefficients m as possible. For l = 0 the average is automatically 1.

**Construction.**
1. Pick a cutoff Q, proportional to (log n)/ε.
2. Take the primes q in (√Q, Q] that do not divide n.
3. Choose a short list of small numbers c₁, …, c_s by a greedy search. Each step adds the number that keeps all the test sums most balanced. No randomness is involved.
4. The coefficients are all products k = c · q⁻¹ mod n, one for each prime q and each c in the list. Here q⁻¹ is the u with q·u ≡ 1 (mod n), so k is "c divided by q" in mod-n arithmetic. The count is m = (number of primes) × s.

**Error.** At most ε for every l ≠ 0.

**Count.** The count grows like log n / ε³: doubling the digits of n roughly doubles m, and halving ε multiplies m by about 8. The constant depends on the strength of the guarantee:

| guarantee | count for error ≤ 0.2 | example |
|---|---|---|
| proved for every n (this document, checked in Lean) | ≤ 1625·(20·ln n/ε + 32769)/ε² | n = 2⁶⁴: ≈ 1.5·10⁹ |
| proved by computer for one specific set (certificate) | ≈ 600–800 · log₂ n | n = 2⁶⁴: 38,400 |
| measured exactly (feasible up to n = 2²⁴) | ≈ 30 · log₂ n | n = 2²⁴: 736, error 0.176 |

The general bound is loose. Its "+32769" term only keeps the proof simple, and it dominates for every realistic n.

**Limits.**
- No set of about log₂ n elements can have small error: a pigeonhole argument always finds an l that aligns all the terms.
- No set of m elements has error below about 1/√m.
- Random sets need about log n/ε², so this construction loses a factor of about 1/ε against random.

---

## Notation

- e(x) = e^{2πix}, and ‖x‖ = distance from x to the nearest integer.
- For a multiset S ⊆ ℤₙ: Ŝ(ℓ) = (1/|S|) Σ_{k∈S} e(ℓk/n), and bias(S) = max_{ℓ ≢ 0 (mod n)} |Ŝ(ℓ)|.
- For a multiset C of integers and real β: Ĉ(β) = (1/|C|) Σ_{c∈C} e(cβ).
- For q coprime to n, q̄ denotes q⁻¹ mod n.

## Theorem

Let n ≥ 2 and 0 < ε ≤ 1. With the construction below, bias(S) ≤ ε and

  |S| ≤ 1625 · (20·ln n/ε + 32769) / ε² = O(log n / ε³).

The construction is fully determined, and it runs in time poly(log n, 1/ε).

## Construction

| symbol | value | role |
|---|---|---|
| Q | ⌈20·ln n/ε⌉ + 32768 | prime cutoff |
| r | ⌊√Q⌋ | lower end of the prime range |
| P | primes q with r < q ≤ Q and q ∤ n | outer set |
| δ | 1/(2Q) | threshold for "tiny" steps |
| N | ⌈48Q/ε⌉ | inner numbers are taken from {0, …, N−1} |
| M | ⌈51N/ε⌉ | grid resolution |
| t | ε/8 | potential parameter |
| s | ⌈128·ln(4(M+1))/ε²⌉ | length of the inner list |

- **Inner list.** C = (c₁, …, c_s) is produced by the greedy search of Lemma 3.
- **Output.** S = { c·q̄ mod n : q ∈ P, c ∈ C }, so |S| = |P|·s.

## Lemma 1 (product structure)

For every ℓ, Ŝ(ℓ) = (1/|P|) Σ_{q∈P} Ĉ(β_q), where β_q = ℓq̄/n.

*Proof.* Replacing c·q̄ by c·q̄ mod n changes ℓ·c·q̄/n by an integer, so e(ℓ·(c q̄ mod n)/n) = e(c·β_q). Averaging over c gives Ĉ(β_q), and averaging over q gives the claim. ∎

## Lemma 2 (few bad primes)

Let ℓ ≢ 0 (mod n), and let ℓ* be its representative in (−n/2, n/2].

**(a)** If q ≤ Q and ‖β_q‖ < 1/(2Q), then q divides ℓ*.

**(b)** Consequently at most K = ⌊log_{r+1}(n/2)⌋ primes of P have ‖β_q‖ < δ.

*Proof.*
- (a) ℓq̄ ≡ t (mod n) for some integer t with |t| < n/(2Q). Multiplying by q gives ℓ* ≡ tq (mod n). Both ℓ* and tq lie in (−n/2, n/2], since |tq| < n/2. So ℓ* = tq, and q divides ℓ*.
- (b) The bad primes are distinct primes greater than r, and all of them divide the nonzero integer ℓ*. Their product therefore divides ℓ*, so (r+1)^{#bad} ≤ |ℓ*| ≤ n/2. ∎

This plays the role of "a nonzero polynomial of degree < r has fewer than r roots" in Reed–Solomon codes.

## Lemma 3 (greedy inner list)

**Setup.**
- Grid: Γ = { k/M : k ∈ {0, …, M}, δ/2 ≤ k/M ≤ ½ }.
- Directions: d ∈ {Re, −Re, Im, −Im}, and X_{γ,d}(c) = d(e(cγ)) ∈ [−1, 1].
- Potential of a partial list cs:

  Φ(cs) = Σ_{γ∈Γ} Σ_d exp( t · Σ_{c∈cs} X_{γ,d}(c) ).

- Greedy step: append the least c ∈ {0, …, N−1} that minimises Φ(cs + c). Repeat s times.

**Claim.** The resulting list C satisfies, for every β with δ ≤ |β| ≤ ½:

  |Ĉ(β)| ≤ η := √2 · ( ln(4(M+1))/(ts) + t/2 + (2Q/N)·(sinh t)/t ) + 2πN/M.

*Proof.*
1. **Small means.** For γ ∈ [δ/2, ½], |e(γ) − 1| = 2 sin(πγ) ≥ 4γ. So the geometric sum gives |E_{c<N} e(cγ)| ≤ 1/(2Nγ) ≤ 1/(Nδ) = 2Q/N.
2. **One step.** For X ∈ [−1, 1], convexity of exp gives e^{tX} ≤ cosh t + X sinh t. If X has mean μ over c < N, then E e^{tX} ≤ cosh t + |μ| sinh t ≤ exp(t²/2 + |μ| sinh t), using cosh t ≤ e^{t²/2} and 1 + y ≤ eʸ. The minimiser does at least as well as the average, so each step multiplies Φ by at most e^D, where D = t²/2 + (2Q/N) sinh t.
3. **Final potential.** Φ starts at 4|Γ| ≤ 4(M+1), so after s steps Φ ≤ 4(M+1)·e^{sD}.
4. **Balanced on the grid.** Each term of the final Φ is at most Φ. Taking logs, every direction sum is at most (ln(4(M+1)) + sD)/t. So |Re Ĉ(γ)| and |Im Ĉ(γ)| are at most A = (ln(4(M+1)) + sD)/(ts), and |Ĉ(γ)| ≤ √2·A.
5. **Off the grid.** For δ ≤ β ≤ ½, the grid point γ = ⌊βM⌋/M lies in Γ, because Mδ ≥ 2. It satisfies |β − γ| ≤ 1/M. Since every c is below N, |dĈ/dβ| ≤ 2πN, so |Ĉ(β)| ≤ √2·A + 2πN/M.
6. **Negative β.** Ĉ(−β) is the complex conjugate of Ĉ(β), so it has the same absolute value. ∎

## Proof of the theorem

**Inner error.** With the parameters above, η ≤ ε/2:
- ln(4(M+1))/(ts) ≤ ε/16, by the choice of s.
- t/2 = ε/16.
- (2Q/N)·(sinh t)/t ≤ (ε/24)·(3/2) = ε/16, using sinh t ≤ 1.5t for t ≤ 1.
- 2πN/M ≤ 2π·ε/51 < 0.124·ε.
- With √2 < 1.415: η ≤ 1.415·(3ε/16) + 0.124ε < 0.39·ε.
- Also Mδ = M/(2Q) ≥ 51·48/(2ε²) ≥ 2, as Lemma 3 requires.

**Prime count.** We show |P| ≥ 1 and K ≤ (ε/2)·|P|.
- Chebyshev's bound gives π(Q) ≥ Q·ln 2/ln Q.
- Write L = ⌊log_{r+1} n⌋. At most L primes in (r, Q] divide n, so |P| ≥ π(Q) − (r+1) − L.
- Since Q < (r+1)², we have ln(r+1) ≥ ½·ln Q, so K ≤ L ≤ 2·ln n/ln Q. Also ln n ≤ εQ/20.
- It therefore suffices that |P| ≥ 1 + 2L/ε. After multiplying out, this reduces to (√Q + 2)·ln Q ≤ (ln 2 − 0.3)·Q.
- That holds for Q ≥ 13⁴, which follows from ln Q ≤ 4·Q^{1/4}. Our Q is at least 32768 > 13⁴.

**Bias.** Fix ℓ ≢ 0. By Lemma 1, |Ŝ(ℓ)| ≤ (1/|P|) Σ_q |Ĉ(β_q)|.
- By Lemma 2, at most K primes have ‖β_q‖ < δ, and for those |Ĉ(β_q)| ≤ 1.
- Every other prime has δ ≤ ‖β_q‖ ≤ ½, so |Ĉ(β_q)| ≤ η ≤ ε/2 by Lemma 3.

So |Ŝ(ℓ)| ≤ K/|P| + ε/2 ≤ ε.

**Size.**
- |P| ≤ π(Q) ≤ 2·ln 4·Q/ln Q + √Q (Chebyshev upper bound).
- Using 1/ε ≤ Q and Q ≥ 32768, we get 4(M+1) ≤ Q⁴, hence s ≤ 513·ln Q/ε².
- Multiplying, and using √Q·ln Q ≤ 0.393·Q: |S| ≤ 513·(2·1.3863 + 0.393)·Q/ε² ≤ 1625·Q/ε².
- Finally, Q ≤ 20·ln n/ε + 32769.

**Running time.**
- Sieving primes up to Q: poly(log n/ε).
- The greedy search: s steps × N candidates × 4|Γ| terms, which is poly(log n/ε).
- Each coefficient: one modular inverse and one multiplication mod n.

So the total is poly(log n, 1/ε). ∎

## Formal verification

The theorem is machine-checked in Lean 4 + Mathlib; see `lean/` and `lean/README.md`.
- **Final statement:** `SmallBias.explicitList_spec`, written only in terms of `Complex.exp`, lists and `Real.log`.
- **Axioms:** `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`.
- **Not formalized:** the running time. The Lean definition is `noncomputable` because it compares real numbers, but it determines the set uniquely.

## Numerical check

These numbers come from `experiment.py`; the full output is in `results.txt`.
- **A different variant.** The code uses an earlier variant of the construction: primes in (Q/2, Q], N = 16Q, and a greedy search with 4 directions accelerated by FFTs. Lemmas 1–3 apply unchanged to this variant, with m = Q/2.
- **"Certified" means a computed bound.** It is a proof-level upper bound on the bias of the specific set the code outputs. It comes from Lemma 2 for general thresholds x, of the form "at most (2⌈xQ + ½⌉ − 1)·(⌈log_{Q/2}(xnQ)⌉ − 1) bad primes", combined with an exact fine-grid evaluation of Ĉ.

Each entry below is the smallest certified set found on a parameter grid with Q ≤ 4096 and s ≤ 768. The dense rows use the inner run C = {0, …, L−1} instead of the greedy list.

| r = log₂ n | 16 | 24 | 32 | 64 | 128 | 256 | 512 |
|---|---|---|---|---|---|---|---|
| certified bias ≤ 0.3, greedy inner list: \|S\|/r | 144 | 236 | 225 | 236 | 255 | 255 | 255 |
| certified bias ≤ 0.3, dense run: \|S\|/r | 407 | 555 | 736 | 1376 | 2670 | 4384 | 8160 |
| certified bias ≤ 0.2, greedy inner list: \|S\|/r | 456 | 491 | 688 | 600 | 788 | 765 | – |
| certified bias ≤ 0.2, dense run: \|S\|/r | 1664 | 2775 | 2986 | 5340 | 9684 | 17830 | 92320 |

A dash means the grid would need Q > 4096.

- **Greedy inner list:** |S|/log₂ n stays roughly flat, consistent with O(log n).
- **Dense run:** the ratio grows about 20-fold, consistent with O(log² n).

**Exact bias,** checked by FFT where n is small enough:
- The certified sets for r = 16 (target 0.3) and r = 24 (target 0.2) have exact bias 0.212 and 0.096.
- The smallest sets in the grid with exact bias ≤ 0.2 have |S| = 416, 608, 736 for r = 16, 20, 24. That's about 26–31 · log₂ n.

## Remarks

1. **Code analogy.** The primes act as an outer code, and Lemma 2 is its distance bound. The greedy inner list is an inner code, found by search because the inner problem is small: N = O(log n/ε²). This mirrors the classical concatenation that gives ε-biased sets of size O(r/ε³) in 𝔽₂^r. Replacing the greedy list by the dense run {0, …, L−1} is the analogue of using the Hadamard inner code, and it costs a factor of log n.

2. **Literature.** I have not found this construction in the literature. Published explicit constructions for cyclic groups that I know of have size polylog(n)/ε² or log n·ε^{−O(log* n)}. The Lean proof covers correctness, so the open question is novelty, not validity.

3. **Next step.** Using S with constant ε as the starting set for the Ta-Shma / Jalan–Moshkovitz amplification should give O(log n/ε^{2+o(1)}). That amplification sums elements mod n along expander walks. I have not checked whether their theorem accepts an arbitrary starting set.
