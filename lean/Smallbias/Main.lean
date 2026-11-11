import Smallbias.Greedy
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Finset.Sort

/-!
# The construction, Lemma 4, and the main theorem

For `n ≥ 2` and `0 < ε ≤ 1` (Lean name of each parameter in brackets):
* `R = ⌈4 log n / ε⌉ + 16` (`Rpar`), `K = ⌊log_{R+1}(n/2)⌋`, `|P| = ⌊3K/ε⌋ + 1` (`numPrimes`);
* `P` = the `|P|` smallest primes in `(R, R²]` that do not divide `n` (`primes`), and
  `P_max = max P` (`Pmax`);
* the multipliers `C = greedyList 16 N M δ t s` (`multList`) with `δ = 1/(2 P_max)`,
  `N = ⌈300 P_max/ε⌉` (`Npar`), `M = ⌈1000N/ε⌉` (`Mpar`), `t = 5ε/8`,
  `s = ⌈2 log(16(M+1)) / t²⌉` (`spar`);
* `S = { c · q⁻¹ mod n : q ∈ P, c ∈ C }`, so `|S| = |P| · s`.

`main_bias`: at every time `ℓ ≠ 0`, `‖Ŝ(ℓ)‖ ≤ ε` (at most `ε/3` from the bad groups and `2ε/3` from
the others). `main_size_exact`: `|S| = |P| · s`.  `main_size`: `|S| ≤ 235 (log n + 2) / ε³`.
`explicitList_spec`: the statement for a plain list of integers, using only `Complex.exp`.
-/

open Finset

namespace SmallBias

/-! ### Parameters and the construction -/

noncomputable def Rpar (n : ℕ) (ε : ℝ) : ℕ := ⌈4 * Real.log n / ε⌉₊ + 16
noncomputable def numPrimes (n : ℕ) (ε : ℝ) : ℕ :=
  ⌊3 * (Nat.log (Rpar n ε + 1) (n / 2) : ℝ) / ε⌋₊ + 1

/-- Candidate primes: `q ∈ (R, R²]`, prime, not dividing `n`. -/
def candidates (n R : ℕ) : Finset ℕ := (Ioc R (R ^ 2)).filter fun q => q.Prime ∧ q.Coprime n

/-- `P`: the `|P|` smallest candidates. -/
noncomputable def primes (n : ℕ) (ε : ℝ) : Finset ℕ :=
  (((candidates n (Rpar n ε)).sort (· ≤ ·)).take (numPrimes n ε)).toFinset

noncomputable def Pmax (n : ℕ) (ε : ℝ) : ℕ := (primes n ε).sup id
noncomputable def Npar (Pmax : ℕ) (ε : ℝ) : ℕ := ⌈300 * Pmax / ε⌉₊
noncomputable def Mpar (N : ℕ) (ε : ℝ) : ℕ := ⌈1000 * N / ε⌉₊
noncomputable def spar (M : ℕ) (ε : ℝ) : ℕ := ⌈2 * Real.log (16 * (M + 1)) / (5 * ε / 8) ^ 2⌉₊

/-- The multipliers `C` (newest choice first). -/
noncomputable def multList (n : ℕ) (ε : ℝ) : List ℕ :=
  greedyList 16 (Npar (Pmax n ε) ε) (Mpar (Npar (Pmax n ε) ε) ε) (1 / (2 * (Pmax n ε : ℝ)))
    (5 * ε / 8) (spar (Mpar (Npar (Pmax n ε) ε) ε) ε)

/-- Index set of `S`. -/
noncomputable def indexSet (n : ℕ) (ε : ℝ) : Finset (ℕ × Fin (multList n ε).length) :=
  primes n ε ×ˢ univ

/-- The hands of `S`: `(q, i) ↦ c_i · q⁻¹`. -/
noncomputable def element (n : ℕ) (ε : ℝ) : ℕ × Fin (multList n ε).length → ZMod n :=
  hand (ofList (multList n ε))

/-! ### Elementary facts -/

lemma sinh_le_three_halves {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : Real.sinh t ≤ 3 / 2 * t := by
  have hconv := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ 1) (by linarith : 0 ≤ 1 - t) h0
    (by ring : 1 - t + t = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.exp_zero] at hconv
  have he := Real.exp_one_lt_d9
  have hneg := Real.add_one_le_exp (-t)
  rw [Real.sinh_eq]
  nlinarith

lemma pow_four_le_two_pow {R : ℕ} (h : 16 ≤ R) : R ^ 4 ≤ 2 ^ R := by
  induction R, h using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      have h1 : 16 * m ^ 3 ≤ m ^ 4 := by
        calc 16 * m ^ 3 ≤ m * m ^ 3 := Nat.mul_le_mul_right _ hm
          _ = m ^ 4 := by ring
      have h2 : 16 * m ^ 2 ≤ m ^ 3 := by
        calc 16 * m ^ 2 ≤ m * m ^ 2 := Nat.mul_le_mul_right _ hm
          _ = m ^ 3 := by ring
      have h3 : 16 * m ≤ m ^ 2 := by
        calc 16 * m ≤ m * m := Nat.mul_le_mul_right _ hm
          _ = m ^ 2 := by ring
      have h4 : (m + 1) ^ 4 ≤ 2 * m ^ 4 := by nlinarith
      calc (m + 1) ^ 4 ≤ 2 * m ^ 4 := h4
        _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (m + 1) := by ring

lemma four_log_le {R : ℕ} (h : 16 ≤ R) : 4 * Real.log R ≤ R * Real.log 2 := by
  have h1 : (R : ℝ) ^ 4 ≤ (2 : ℝ) ^ R := by exact_mod_cast pow_four_le_two_pow h
  have hR : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have := Real.log_le_log (by positivity) h1
  rw [Real.log_pow, Real.log_pow] at this
  push_cast at this
  linarith

lemma log_le_div_exp_one {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx (Real.exp_pos 1))
  rw [Real.log_div hx.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  linarith

lemma log_sixteen : Real.log (16 : ℝ) = 4 * Real.log 2 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring

/-- `L · log (R+1) ≤ log n` where `L = ⌊log_{R+1} n⌋`. -/
lemma log_count_le {n R : ℕ} (hn : n ≠ 0) :
    (Nat.log (R + 1) n : ℝ) * Real.log (R + 1) ≤ Real.log n := by
  have hp : (R + 1) ^ Nat.log (R + 1) n ≤ n := Nat.pow_log_le_self (R + 1) hn
  have : Real.log (((R + 1) ^ Nat.log (R + 1) n : ℕ) : ℝ) ≤ Real.log n :=
    Real.log_le_log (by positivity) (by exact_mod_cast hp)
  push_cast at this
  rwa [Real.log_pow] at this

/-! ### Lemma 4: enough candidate primes -/

/-- At most `⌊log_{r+1} n⌋` primes larger than `r` divide `n`. -/
lemma card_dvd_primes_le {n : ℕ} (hn : n ≠ 0) {r : ℕ} (hr : 1 ≤ r) (X : ℕ) :
    ((Ioc r X).filter fun q => q.Prime ∧ q ∣ n).card ≤ Nat.log (r + 1) n := by
  set D := (Ioc r X).filter fun q => q.Prime ∧ q ∣ n
  have hprod : ∏ q ∈ D, q ∣ n := by
    apply Finset.prod_primes_dvd
    · intro q hq; exact Nat.prime_iff.mp (mem_filter.mp hq).2.1
    · intro q hq; exact (mem_filter.mp hq).2.2
  have hpow : (r + 1) ^ D.card ≤ n := by
    rw [← Finset.prod_const]
    refine (Finset.prod_le_prod fun q hq => ?_).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hprod)
    exact (mem_Ioc.mp (mem_filter.mp hq).1).1
  exact (Nat.le_log_iff_pow_le (by omega) hn).mpr hpow

/-- There are at least `R - 1 - ⌊log_{R+1} n⌋` candidates (Chebyshev: `π(R²) ≥ 2R`). -/
lemma card_candidates_ge {n R : ℕ} (hn : n ≠ 0) (hR : 16 ≤ R) :
    (R : ℝ) - 1 - Nat.log (R + 1) n ≤ (candidates n R).card := by
  set D := (Ioc R (R ^ 2)).filter fun q => q.Prime ∧ q ∣ n
  have hsub : Nat.primesLE (R ^ 2) ⊆ range (R + 1) ∪ (candidates n R ∪ D) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
    have hpQ : p ≤ R ^ 2 := Nat.le_of_mem_primesLE hp
    simp only [mem_union, mem_range, candidates, mem_filter, mem_Ioc, D]
    by_cases hpr : p ≤ R
    · left; omega
    · right
      push Not at hpr
      by_cases hc : p.Coprime n
      · left; exact ⟨⟨hpr, hpQ⟩, hpp, hc⟩
      · right; exact ⟨⟨hpr, hpQ⟩, hpp, (Nat.Prime.dvd_iff_not_coprime hpp).mpr hc⟩
  have hcard : (Nat.primesLE (R ^ 2)).card ≤
      (range (R + 1)).card + ((candidates n R).card + D.card) :=
    (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left (card_union_le _ _) _))
  rw [Nat.primesLE_card_eq_primeCounting, card_range] at hcard
  have hD : D.card ≤ Nat.log (R + 1) n := card_dvd_primes_le hn (by omega) (R ^ 2)
  have hpi := Chebyshev.pi_ge_of_four_le (n := R ^ 2) (by nlinarith)
  push_cast at hpi
  have hRR : (16 : ℝ) ≤ R := by exact_mod_cast hR
  have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
  have h4 := four_log_le hR
  have hpi2 : 2 * (R : ℝ) ≤ Nat.primeCounting (R ^ 2) := by
    refine le_trans ?_ hpi
    rw [Real.log_pow, le_div_iff₀ (by push_cast; positivity)]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ R)]
  have h1 : (Nat.primeCounting (R ^ 2) : ℝ) ≤ (R + 1) + ((candidates n R).card + D.card) := by
    exact_mod_cast hcard
  have hD' : (D.card : ℝ) ≤ Nat.log (R + 1) n := by exact_mod_cast hD
  linarith

lemma Rpar_ge (n : ℕ) (ε : ℝ) : 16 ≤ Rpar n ε := Nat.le_add_left _ _

lemma Rpar_lo (n : ℕ) (ε : ℝ) : 4 * Real.log n / ε + 16 ≤ Rpar n ε := by
  have := Nat.le_ceil (4 * Real.log n / ε)
  unfold Rpar; push_cast; linarith

lemma Rpar_hi {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) :
    (Rpar n ε : ℝ) ≤ 4 * Real.log n / ε + 17 := by
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have := Nat.ceil_lt_add_one (div_nonneg (by linarith : 0 ≤ 4 * Real.log n) hε0.le)
  unfold Rpar; push_cast; linarith

/-- `|P| ≤ 3 log n / (ε log R) + 1`. -/
lemma numPrimes_le {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) :
    (numPrimes n ε : ℝ) ≤ 3 * Real.log n / (ε * Real.log (Rpar n ε)) + 1 := by
  have hR16 : (16 : ℝ) ≤ Rpar n ε := by exact_mod_cast Rpar_ge n ε
  have hlogR : 0 < Real.log (Rpar n ε) := Real.log_pos (by linarith)
  have hfl := Nat.floor_le (div_nonneg (by positivity :
    (0 : ℝ) ≤ 3 * (Nat.log (Rpar n ε + 1) (n / 2) : ℝ)) hε0.le)
  have hKL : (Nat.log (Rpar n ε + 1) (n / 2) : ℝ) ≤ Nat.log (Rpar n ε + 1) n := by
    exact_mod_cast Nat.log_mono_right (Nat.div_le_self n 2)
  have hL := log_count_le (n := n) (R := Rpar n ε) (by omega)
  have hlogR1 : Real.log (Rpar n ε) ≤ Real.log ((Rpar n ε : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hK0 : (0 : ℝ) ≤ Nat.log (Rpar n ε + 1) (n / 2) := by positivity
  have hKb : (Nat.log (Rpar n ε + 1) (n / 2) : ℝ) * Real.log (Rpar n ε) ≤ Real.log n := by
    have hlog0 : 0 ≤ Real.log ((Rpar n ε : ℝ) + 1) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hlogR1 hK0, mul_le_mul_of_nonneg_right hKL hlog0]
  have h3 : 3 * (Nat.log (Rpar n ε + 1) (n / 2) : ℝ) / ε ≤
      3 * Real.log n / (ε * Real.log (Rpar n ε)) := by
    rw [div_le_div_iff₀ hε0 (by positivity)]
    nlinarith
  unfold numPrimes
  push_cast
  linarith

/-- **Lemma 4**: there are at least `|P|` candidates. -/
lemma numPrimes_le_card {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    numPrimes n ε ≤ (candidates n (Rpar n ε)).card := by
  have hn0 : n ≠ 0 := by omega
  have hR16 := Rpar_ge n ε
  have hcand := card_candidates_ge hn0 hR16
  set L := Nat.log (Rpar n ε + 1) n with hLdef
  have hfl := Nat.floor_le (div_nonneg (by positivity :
    (0 : ℝ) ≤ 3 * (Nat.log (Rpar n ε + 1) (n / 2) : ℝ)) hε0.le)
  have hKL : (Nat.log (Rpar n ε + 1) (n / 2) : ℝ) ≤ L := by
    exact_mod_cast Nat.log_mono_right (Nat.div_le_self n 2)
  have hnumP : (numPrimes n ε : ℝ) ≤ 3 * L / ε + 1 := by
    have : 3 * (Nat.log (Rpar n ε + 1) (n / 2) : ℝ) / ε ≤ 3 * L / ε := by gcongr
    unfold numPrimes; push_cast; linarith
  have hRR : (16 : ℝ) ≤ Rpar n ε := by exact_mod_cast hR16
  have hl2 := Real.log_two_gt_d9
  have hlog16 : 2.77 ≤ Real.log ((Rpar n ε : ℝ) + 1) := by
    have : Real.log (16 : ℝ) ≤ Real.log ((Rpar n ε : ℝ) + 1) :=
      Real.log_le_log (by norm_num) (by linarith)
    rw [log_sixteen] at this
    linarith
  have hL := log_count_le (n := n) (R := Rpar n ε) hn0
  have hL0 : (0 : ℝ) ≤ L := by positivity
  have hL277 : (L : ℝ) * 2.77 ≤ Real.log n := by
    nlinarith [mul_le_mul_of_nonneg_left hlog16 hL0]
  have hRlo := Rpar_lo n ε
  -- with x = L/ε and y = log n / ε: L ≤ x, 2.77 x ≤ y, R ≥ 4y + 16
  have hx : (L : ℝ) ≤ L / ε := by rw [le_div_iff₀ hε0]; nlinarith
  have hxy : (L : ℝ) / ε * 2.77 ≤ Real.log n / ε := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hε0]; linarith
  have hy0 : 0 ≤ Real.log n / ε := by
    have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    positivity
  have e1 : 3 * (L : ℝ) / ε = 3 * (L / ε) := by ring
  have e2 : 4 * Real.log n / ε = 4 * (Real.log n / ε) := by ring
  have hfinal : (numPrimes n ε : ℝ) ≤ (candidates n (Rpar n ε)).card := by
    have hx0 : 0 ≤ (L : ℝ) / ε := by positivity
    linarith
  exact_mod_cast hfinal

/-! ### The primes `P` -/

lemma primes_card {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (primes n ε).card = numPrimes n ε := by
  unfold primes
  have hnd : ((candidates n (Rpar n ε)).sort (· ≤ ·)).Nodup := Finset.sort_nodup ..
  rw [List.toFinset_card_of_nodup (hnd.sublist (List.take_sublist _ _)), List.length_take,
    Finset.length_sort]
  exact Nat.min_eq_left (numPrimes_le_card hn hε0 hε1)

lemma mem_candidates_of_mem_primes {n : ℕ} {ε : ℝ} {q : ℕ} (hq : q ∈ primes n ε) :
    q ∈ candidates n (Rpar n ε) := by
  unfold primes at hq
  rw [List.mem_toFinset] at hq
  exact (Finset.mem_sort _).mp (List.mem_of_mem_take hq)

lemma le_Pmax {n : ℕ} {ε : ℝ} {q : ℕ} (hq : q ∈ primes n ε) : q ≤ Pmax n ε :=
  Finset.le_sup (f := id) hq

lemma Pmax_le_sq (n : ℕ) (ε : ℝ) : Pmax n ε ≤ Rpar n ε ^ 2 :=
  Finset.sup_le fun q hq => by
    have := mem_candidates_of_mem_primes hq
    simp only [candidates, mem_filter, mem_Ioc] at this
    exact this.1.2

lemma primes_nonempty {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (primes n ε).Nonempty := by
  rw [← card_pos, primes_card hn hε0 hε1]; unfold numPrimes; omega

lemma Pmax_ge {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) : 17 ≤ Pmax n ε := by
  obtain ⟨q, hq⟩ := primes_nonempty hn hε0 hε1
  have h := mem_candidates_of_mem_primes hq
  simp only [candidates, mem_filter, mem_Ioc] at h
  have h16 := Rpar_ge n ε
  have := le_Pmax hq
  omega

/-! ### The multipliers -/

lemma mult_bound_le (Pmax : ℕ) (hPm : 1 ≤ Pmax) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (Real.log (16 * ((Mpar (Npar Pmax ε) ε : ℝ) + 1)) + spar (Mpar (Npar Pmax ε) ε) ε *
        ((5 * ε / 8) ^ 2 / 2 +
          1 / (Npar Pmax ε * (1 / (2 * (Pmax : ℝ)))) * Real.sinh (5 * ε / 8))) /
        (5 * ε / 8 * spar (Mpar (Npar Pmax ε) ε) ε) / Real.cos (Real.pi / 16) +
      2 * Real.pi * Npar Pmax ε / Mpar (Npar Pmax ε) ε ≤ 2 * ε / 3 := by
  have hPmR : (1 : ℝ) ≤ Pmax := by exact_mod_cast hPm
  have hN : 300 * (Pmax : ℝ) / ε ≤ Npar Pmax ε := Nat.le_ceil _
  have hM : 1000 * (Npar Pmax ε : ℝ) / ε ≤ Mpar (Npar Pmax ε) ε := Nat.le_ceil _
  have hs : 2 * Real.log (16 * ((Mpar (Npar Pmax ε) ε : ℝ) + 1)) / (5 * ε / 8) ^ 2 ≤
      spar (Mpar (Npar Pmax ε) ε) ε := Nat.le_ceil _
  generalize spar (Mpar (Npar Pmax ε) ε) ε = s at *
  generalize Mpar (Npar Pmax ε) ε = M at *
  generalize Npar Pmax ε = N at *
  set t := 5 * ε / 8 with ht
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (by positivity) hM
  have hlog : 0 < Real.log (16 * ((M : ℝ) + 1)) := Real.log_pos (by linarith)
  have htpos : 0 < t := by positivity
  have hspos : (0 : ℝ) < s := lt_of_lt_of_le (by positivity) hs
  have ht1 : t ≤ 1 := by rw [ht]; linarith
  have hsplit : (Real.log (16 * ((M : ℝ) + 1)) + s * (t ^ 2 / 2 +
      1 / (N * (1 / (2 * (Pmax : ℝ)))) * Real.sinh t)) / (t * s) =
      Real.log (16 * ((M : ℝ) + 1)) / (t * s) + t / 2 + 2 * Pmax / N * (Real.sinh t / t) := by
    field_simp
    ring
  have h1 : Real.log (16 * ((M : ℝ) + 1)) / (t * s) ≤ t / 2 := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hs
    nlinarith
  have hsinh0 : 0 ≤ Real.sinh t / t := div_nonneg (Real.sinh_nonneg_iff.mpr htpos.le) htpos.le
  have hsinh : Real.sinh t / t ≤ 3 / 2 := by
    rw [div_le_iff₀ htpos]; exact sinh_le_three_halves htpos.le ht1
  have h3 : 2 * (Pmax : ℝ) / N * (Real.sinh t / t) ≤ ε / 100 := by
    have hPmN : 2 * (Pmax : ℝ) / N ≤ ε / 150 := by
      rw [div_le_iff₀ hNpos]
      rw [div_le_iff₀ hε0] at hN
      nlinarith
    calc 2 * (Pmax : ℝ) / N * (Real.sinh t / t) ≤ ε / 150 * (3 / 2) := by gcongr
      _ = ε / 100 := by ring
  have hpi : Real.pi < 63 / 20 := by have := Real.pi_lt_d2; norm_num at this; linarith
  have hcos : (49 / 50 : ℝ) ≤ Real.cos (Real.pi / 16) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := Real.pi / 16)
    have hpi0 := Real.pi_pos
    nlinarith
  have h4 : 2 * Real.pi * N / M ≤ 2 * (63 / 20) * ε / 1000 := by
    rw [div_le_iff₀ hMpos]
    rw [div_le_iff₀ hε0] at hM
    nlinarith
  rw [hsplit]
  have hA : Real.log (16 * ((M : ℝ) + 1)) / (t * s) + t / 2 + 2 * Pmax / N * (Real.sinh t / t) ≤
      5 * ε / 8 + ε / 100 := by
    linarith
  calc (Real.log (16 * ((M : ℝ) + 1)) / (t * s) + t / 2 + 2 * Pmax / N * (Real.sinh t / t)) /
        Real.cos (Real.pi / 16) + 2 * Real.pi * N / M
      ≤ (5 * ε / 8 + ε / 100) / (49 / 50) + 2 * (63 / 20) * ε / 1000 := by
        gcongr
    _ ≤ 2 * ε / 3 := by linarith

/-- For a given `P_max`, the multipliers keep every group average at most `2ε/3` whenever the base
hand is at `1/(2 P_max) ≤ |a| ≤ 1/2`. -/
lemma mult_good (Pmax : ℕ) (hPm : 1 ≤ Pmax) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (a : ℝ)
    (ha1 : 1 / (2 * (Pmax : ℝ)) ≤ |a|) (ha2 : |a| ≤ 1 / 2) :
    ‖groupAvg (ofList (greedyList 16 (Npar Pmax ε) (Mpar (Npar Pmax ε) ε) (1 / (2 * (Pmax : ℝ)))
      (5 * ε / 8) (spar (Mpar (Npar Pmax ε) ε) ε))) a‖ ≤ 2 * ε / 3 := by
  have hPmR : (1 : ℝ) ≤ Pmax := by exact_mod_cast hPm
  have hNb : 300 * (Pmax : ℝ) / ε ≤ Npar Pmax ε := Nat.le_ceil _
  have hMb : 1000 * (Npar Pmax ε : ℝ) / ε ≤ Mpar (Npar Pmax ε) ε := Nat.le_ceil _
  have hsb : 2 * Real.log (16 * ((Mpar (Npar Pmax ε) ε : ℝ) + 1)) / (5 * ε / 8) ^ 2 ≤
      spar (Mpar (Npar Pmax ε) ε) ε := Nat.le_ceil _
  have hNR : (0 : ℝ) < Npar Pmax ε := lt_of_lt_of_le (by positivity) hNb
  have hMR : (0 : ℝ) < Mpar (Npar Pmax ε) ε := lt_of_lt_of_le (by positivity) hMb
  have hlog : 0 < Real.log (16 * ((Mpar (Npar Pmax ε) ε : ℝ) + 1)) := Real.log_pos (by linarith)
  have hsR : (0 : ℝ) < spar (Mpar (Npar Pmax ε) ε) ε := lt_of_lt_of_le (by positivity) hsb
  have hN : 0 < Npar Pmax ε := by exact_mod_cast hNR
  have hM : 0 < Mpar (Npar Pmax ε) ε := by exact_mod_cast hMR
  have hs : 0 < spar (Mpar (Npar Pmax ε) ε) ε := by exact_mod_cast hsR
  have hMδ : 2 ≤ (Mpar (Npar Pmax ε) ε : ℝ) * (1 / (2 * (Pmax : ℝ))) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ hε0] at hMb hNb
    nlinarith
  have h := greedy_mult_bound 16 (Npar Pmax ε) (Mpar (Npar Pmax ε) ε) (1 / (2 * (Pmax : ℝ)))
    (5 * ε / 8)
    (by norm_num) hN hM (by positivity) hMδ (by positivity) _ hs a ha1 ha2
  simp only [Nat.cast_ofNat] at h
  exact h.trans (mult_bound_le Pmax hPm hε0 hε1)

/-! ### Main theorems -/

/-- **Main theorem (bias).** At every time `ℓ ≠ 0`, `‖Ŝ(ℓ)‖ ≤ ε`. -/
theorem main_bias (n : ℕ) [NeZero n] (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (ℓ : ZMod n) (hℓ : ℓ ≠ 0) : ‖avgAt (indexSet n ε) (element n ε) ℓ‖ ≤ ε := by
  have hcard := primes_card hn hε0 hε1
  have hPm := Pmax_ge hn hε0 hε1
  have hR16 := Rpar_ge n ε
  have hP : ∀ q ∈ primes n ε, q.Prime ∧ Rpar n ε < q ∧ q ≤ Pmax n ε ∧ q.Coprime n := by
    intro q hq
    have h := mem_candidates_of_mem_primes hq
    simp only [candidates, mem_filter, mem_Ioc] at h
    exact ⟨h.2.1, h.1.1, le_Pmax hq, h.2.2⟩
  have hcore := core_bias_bound (n := n) (R := Rpar n ε) (Pmax := Pmax n ε) (by omega)
    (primes n ε) hP (primes_nonempty hn hε0 hε1) (ofList (multList n ε))
    (η := 2 * ε / 3) (by positivity)
    (fun a h1 h2 => mult_good (Pmax n ε) (by omega) hε0 hε1 a h1 h2) ℓ hℓ
  have hnumP : 3 * (Nat.log (Rpar n ε + 1) (n / 2) : ℝ) / ε < numPrimes n ε := by
    unfold numPrimes; push_cast; exact Nat.lt_floor_add_one _
  have hnumPpos : (0 : ℝ) < numPrimes n ε := by unfold numPrimes; positivity
  have hdiv : (Nat.log (Rpar n ε + 1) (n / 2) : ℝ) / (primes n ε).card ≤ ε / 3 := by
    rw [hcard, div_le_iff₀ hnumPpos]
    rw [div_lt_iff₀ hε0] at hnumP
    linarith
  calc ‖avgAt (indexSet n ε) (element n ε) ℓ‖
      = ‖avgAt (primes n ε ×ˢ univ) (hand (ofList (multList n ε))) ℓ‖ := rfl
    _ ≤ (Nat.log (Rpar n ε + 1) (n / 2) : ℝ) / (primes n ε).card + 2 * ε / 3 := hcore
    _ ≤ ε := by linarith

/-- **Main theorem (size, exact).** `|S| = |P| · s`. -/
theorem main_size_exact (n : ℕ) (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (indexSet n ε).card = numPrimes n ε * spar (Mpar (Npar (Pmax n ε) ε) ε) ε := by
  rw [indexSet, card_product, card_univ, Fintype.card_fin, multList, greedyList_length,
    primes_card hn hε0 hε1]

/-- The arithmetic behind the size bound, with all parameters as plain variables. -/
lemma size_arith {n numP s M N Pmax R : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hPm17 : 17 ≤ Pmax) (hPmR2 : Pmax ≤ R ^ 2) (hR16 : 16 ≤ R)
    (hRlo : 4 * Real.log n / ε + 16 ≤ R) (hRhi : (R : ℝ) ≤ 4 * Real.log n / ε + 17)
    (hnumP : (numP : ℝ) ≤ 3 * Real.log n / (ε * Real.log R) + 1)
    (hNle : (N : ℝ) ≤ 300 * Pmax / ε + 1) (hMle : (M : ℝ) ≤ 1000 * N / ε + 1)
    (hsle : (s : ℝ) ≤ 2 * Real.log (16 * ((M : ℝ) + 1)) / (5 * ε / 8) ^ 2 + 1) :
    (numP : ℝ) * s ≤ 235 * (Real.log n + 2) / ε ^ 3 := by
  have hl2 := Real.log_two_gt_d9
  have hlogn2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlogn0 : 0 ≤ Real.log n := by linarith
  have hRR : (16 : ℝ) ≤ R := by exact_mod_cast hR16
  have hlogR16 : 4 * Real.log 2 ≤ Real.log R := by
    rw [← log_sixteen]; exact Real.log_le_log (by norm_num) hRR
  have hlogRpos : 0 < Real.log R := by linarith
  have hPmR' : (Pmax : ℝ) ≤ (R : ℝ) ^ 2 := by exact_mod_cast hPmR2
  have hPm17' : (17 : ℝ) ≤ Pmax := by exact_mod_cast hPm17
  have hε2 : 0 < ε ^ 2 := by positivity
  have hε21 : ε ^ 2 ≤ 1 := pow_le_one₀ hε0.le hε1
  have hinvε : 1 / ε ≤ R := by
    have : 1 / ε ≤ 4 * Real.log n / ε := by
      rw [div_le_div_iff_of_pos_right hε0]; linarith
    linarith
  -- M + 1 ≤ 301002 Pmax/ε²
  have hPme : 1 ≤ (Pmax : ℝ) / ε ^ 2 := by rw [le_div_iff₀ hε2]; linarith
  have hPme' : 1 / ε ≤ (Pmax : ℝ) / ε ^ 2 := by
    rw [div_le_div_iff₀ hε0 hε2, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hε1 hε0.le, mul_le_mul_of_nonneg_right hPm17' hε0.le]
  have hN' : 1000 * (N : ℝ) / ε ≤ 1000 * (300 * Pmax / ε + 1) / ε := by gcongr
  have e1 : 1000 * (300 * (Pmax : ℝ) / ε + 1) / ε = 300000 * (Pmax / ε ^ 2) + 1000 * (1 / ε) := by
    field_simp; ring
  have hM1 : (M : ℝ) + 1 ≤ 301002 * ((Pmax : ℝ) / ε ^ 2) := by linarith
  -- Pmax/ε² ≤ R⁴, hence 16(M+1) ≤ R¹⁰
  have hu : (Pmax : ℝ) / ε ^ 2 ≤ (R : ℝ) ^ 4 := by
    have h1 : 1 / ε ^ 2 ≤ (R : ℝ) ^ 2 := by
      rw [show 1 / ε ^ 2 = (1 / ε) ^ 2 by ring]
      gcongr
    calc (Pmax : ℝ) / ε ^ 2 = (Pmax : ℝ) * (1 / ε ^ 2) := by ring
      _ ≤ (R : ℝ) ^ 2 * (R : ℝ) ^ 2 := by gcongr
      _ = (R : ℝ) ^ 4 := by ring
  have hR4 : (0 : ℝ) ≤ (R : ℝ) ^ 4 := by positivity
  have hR6 : (2 : ℝ) ^ 23 ≤ (R : ℝ) ^ 6 := by
    calc (2 : ℝ) ^ 23 ≤ (16 : ℝ) ^ 6 := by norm_num
      _ ≤ (R : ℝ) ^ 6 := by gcongr
  have h16M : 16 * ((M : ℝ) + 1) ≤ (R : ℝ) ^ 10 := by
    calc 16 * ((M : ℝ) + 1) ≤ 4816032 * (R : ℝ) ^ 4 := by linarith
      _ ≤ (2 : ℝ) ^ 23 * (R : ℝ) ^ 4 := by
          have : (4816032 : ℝ) ≤ 2 ^ 23 := by norm_num
          exact mul_le_mul_of_nonneg_right this hR4
      _ ≤ (R : ℝ) ^ 6 * (R : ℝ) ^ 4 := by gcongr
      _ = (R : ℝ) ^ 10 := by ring
  have hlogM : Real.log (16 * ((M : ℝ) + 1)) ≤ 10 * Real.log R := by
    have := Real.log_le_log (by positivity) h16M
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  -- s ≤ 52 log R / ε²
  have hs' : (s : ℝ) ≤ 52 * Real.log R / ε ^ 2 := by
    have e2 : 2 * Real.log (16 * ((M : ℝ) + 1)) / (5 * ε / 8) ^ 2 =
        128 / 25 * (Real.log (16 * ((M : ℝ) + 1)) / ε ^ 2) := by
      field_simp; ring
    have h2 : Real.log (16 * ((M : ℝ) + 1)) / ε ^ 2 ≤ 10 * (Real.log R / ε ^ 2) := by
      rw [← mul_div_assoc]; gcongr
    have h3 : 1 ≤ 4 / 5 * (Real.log R / ε ^ 2) := by
      have : Real.log R ≤ Real.log R / ε ^ 2 := by
        rw [le_div_iff₀ hε2]
        nlinarith [mul_le_mul_of_nonneg_left hε21 hlogRpos.le]
      linarith
    calc (s : ℝ) ≤ 2 * Real.log (16 * ((M : ℝ) + 1)) / (5 * ε / 8) ^ 2 + 1 := hsle
      _ = 128 / 25 * (Real.log (16 * ((M : ℝ) + 1)) / ε ^ 2) + 1 := by rw [e2]
      _ ≤ 128 / 25 * (10 * (Real.log R / ε ^ 2)) + 4 / 5 * (Real.log R / ε ^ 2) := by
          linarith
      _ = 52 * Real.log R / ε ^ 2 := by ring
  -- numP s ≤ 52 (3 log n / ε + log R) / ε²
  have hnumP' : (numP : ℝ) ≤ (3 * Real.log n / ε + Real.log R) / Real.log R := by
    calc (numP : ℝ) ≤ 3 * Real.log n / (ε * Real.log R) + 1 := hnumP
      _ = (3 * Real.log n / ε + Real.log R) / Real.log R := by field_simp
  have hnumPs : (numP : ℝ) * s ≤ 52 * (3 * Real.log n / ε + Real.log R) / ε ^ 2 := by
    have hb0 : 0 ≤ (3 * Real.log n / ε + Real.log R) / Real.log R := by positivity
    calc (numP : ℝ) * s ≤ ((3 * Real.log n / ε + Real.log R) / Real.log R) *
          (52 * Real.log R / ε ^ 2) := by
          gcongr
      _ = 52 * (3 * Real.log n / ε + Real.log R) / ε ^ 2 := by field_simp
  -- log R ≤ R / e ≤ (4 log n / ε + 17) / (27/10)
  have he' : (27 / 10 : ℝ) ≤ Real.exp 1 := by
    have he := Real.exp_one_gt_d9
    norm_num at he ⊢; linarith
  have hlogR : Real.log R ≤ (4 * Real.log n / ε + 17) / (27 / 10) := by
    calc Real.log R ≤ (R : ℝ) / Real.exp 1 := log_le_div_exp_one (by linarith)
      _ ≤ (R : ℝ) / (27 / 10) := by gcongr
      _ ≤ (4 * Real.log n / ε + 17) / (27 / 10) := by gcongr
  calc (numP : ℝ) * s ≤ 52 * (3 * Real.log n / ε + Real.log R) / ε ^ 2 := hnumPs
    _ ≤ 52 * (3 * Real.log n / ε + (4 * Real.log n / ε + 17) / (27 / 10)) / ε ^ 2 := by
        gcongr
    _ = (52 * (3 + 40 / 27) * Real.log n + 52 * 170 / 27 * ε) / ε ^ 3 := by
        field_simp; ring
    _ ≤ 235 * (Real.log n + 2) / ε ^ 3 := by
        rw [div_le_div_iff_of_pos_right (by positivity)]
        linarith

/-- **Main theorem (size).** `|S| ≤ 235 (log n + 2) / ε³`. -/
theorem main_size (n : ℕ) (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ((indexSet n ε).card : ℝ) ≤ 235 * (Real.log n + 2) / ε ^ 3 := by
  rw [main_size_exact n hn hε0 hε1]
  push_cast
  apply size_arith hn hε0 hε1 (Pmax_ge hn hε0 hε1) (Pmax_le_sq n ε) (Rpar_ge n ε) (Rpar_lo n ε)
    (Rpar_hi hn hε0) (numPrimes_le hn hε0) (Nat.ceil_lt_add_one (by positivity)).le
    (Nat.ceil_lt_add_one (by positivity)).le
  refine (Nat.ceil_lt_add_one ?_).le
  have : 0 ≤ Real.log (16 * ((Mpar (Npar (Pmax n ε) ε) ε : ℝ) + 1)) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ Mpar (Npar (Pmax n ε) ε) ε := by positivity
    linarith)
  positivity

/-! ### The theorem in plain terms -/

/-- The explicit list of integers `k ∈ [0, n)` (with multiplicity). -/
noncomputable def explicitList (n : ℕ) (ε : ℝ) : List ℕ :=
  (indexSet n ε).toList.map fun a => (element n ε a).val

/-- **Small-bias sets in `ℤ/nℤ`, stated without auxiliary definitions.** For `n ≥ 2` and
`0 < ε ≤ 1`, the explicitly constructed list `ks = explicitList n ε` consists of integers in
`[0, n)`, has length at most `235 (log n + 2) / ε³`, and for every `0 < l < n` the average of
`exp(2πi k l / n)` over `k ∈ ks` has absolute value at most `ε`. -/
theorem explicitList_spec (n : ℕ) (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ k ∈ explicitList n ε, k < n) ∧
    ((explicitList n ε).length : ℝ) ≤ 235 * (Real.log n + 2) / ε ^ 3 ∧
    ∀ l : ℕ, 0 < l → l < n →
      ‖((explicitList n ε).length : ℂ)⁻¹ *
        ((explicitList n ε).map fun k : ℕ =>
          Complex.exp (2 * Real.pi * Complex.I * k * l / n)).sum‖ ≤ ε := by
  have : NeZero n := ⟨by omega⟩
  have hlen : (explicitList n ε).length = (indexSet n ε).card := by
    simp [explicitList, Finset.length_toList]
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    simp only [explicitList, List.mem_map] at hk
    obtain ⟨a, _, rfl⟩ := hk
    exact ZMod.val_lt _
  · rw [hlen]; exact main_size n hn hε0 hε1
  · intro l hl0 hln
    have hℓ : (l : ZMod n) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => absurd (Nat.le_of_dvd hl0 h) (by omega)
    have hmain := main_bias n hn hε0 hε1 (l : ZMod n) hℓ
    have hterm : ∀ x : ZMod n, Complex.exp (2 * Real.pi * Complex.I * (x.val : ℕ) * l / n) =
        e (angle ((l : ZMod n) * x)) := by
      intro x
      have h := e_div_eq_of_cast_eq (n := n) (a := (x.val * l : ℕ))
        (b := ((l : ZMod n) * x).valMinAbs)
        (by push_cast; rw [ZMod.natCast_zmod_val]; ring)
      unfold angle
      rw [← h]
      unfold e
      congr 1
      push_cast
      ring
    have hsum : ((explicitList n ε).map fun k : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * k * l / n)).sum =
        ∑ a ∈ indexSet n ε, e (angle ((l : ZMod n) * element n ε a)) := by
      rw [explicitList, List.map_map, ← Finset.sum_map_toList]
      congr 1
      apply List.map_congr_left
      intro a _
      simp only [Function.comp_apply]
      exact hterm _
    rw [hsum, hlen]
    exact hmain

end SmallBias
