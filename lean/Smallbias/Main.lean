import Smallbias.Greedy
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The construction and the main theorem

Parameters (for `n ≥ 2`, `0 < ε ≤ 1`):
* `Q = ⌈20 log n / ε⌉ + 2^15 = ⌈20 log n / ε⌉ + 32768`, `r = ⌊√Q⌋`, primes `P = {q ∈ (r, Q] prime, coprime to n}`;
* inner set: `greedyList N M δ t s` with `δ = 1/(2Q)`, `N = ⌈48Q/ε⌉`, `M = ⌈51N/ε⌉`, `t = ε/8`,
  `s = ⌈128 log(4(M+1)) / ε²⌉`;
* `S = { c · q⁻¹ mod n : q ∈ P, c ∈ inner set }`.

`main_bias`: every nontrivial normalised character sum of `S` has norm `≤ ε`.
`main_size`: `|S| ≤ 1625 · (20 log n / ε + 32769) / ε²`, i.e. `O(log n / ε³)`.
-/

open Finset

namespace SmallBias

/-! ### Parameters -/

noncomputable def Qpar (n : ℕ) (ε : ℝ) : ℕ := ⌈20 * Real.log n / ε⌉₊ + 32768
noncomputable def Npar (Q : ℕ) (ε : ℝ) : ℕ := ⌈48 * Q / ε⌉₊
noncomputable def Mpar (N : ℕ) (ε : ℝ) : ℕ := ⌈51 * N / ε⌉₊
noncomputable def spar (M : ℕ) (ε : ℝ) : ℕ := ⌈128 * Real.log (4 * (M + 1)) / ε ^ 2⌉₊

/-- The primes `q ∈ (⌊√Q⌋, Q]` coprime to `n`. -/
def primeSet (n Q : ℕ) : Finset ℕ := (Ioc (Nat.sqrt Q) Q).filter fun q => q.Prime ∧ q.Coprime n

/-- The inner set (a list, newest choice first). -/
noncomputable def innerList (n : ℕ) (ε : ℝ) : List ℕ :=
  greedyList (Npar (Qpar n ε) ε) (Mpar (Npar (Qpar n ε) ε) ε) (1 / (2 * (Qpar n ε : ℝ))) (ε / 8)
    (spar (Mpar (Npar (Qpar n ε) ε) ε) ε)

/-- Index set of `S`. -/
noncomputable def indexSet (n : ℕ) (ε : ℝ) : Finset (ℕ × Fin (innerList n ε).length) :=
  primeSet n (Qpar n ε) ×ˢ univ

/-- The elements of `S`: `(q, i) ↦ c_i · q⁻¹`. -/
noncomputable def element (n : ℕ) (ε : ℝ) : ℕ × Fin (innerList n ε).length → ZMod n :=
  fracSet (listInner (innerList n ε))

/-! ### Real-number facts -/

lemma sinh_le_three_halves {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : Real.sinh t ≤ 3 / 2 * t := by
  have hconv := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ 1) (by linarith : 0 ≤ 1 - t) h0
    (by ring : 1 - t + t = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.exp_zero] at hconv
  have he := Real.exp_one_lt_d9
  have hneg := Real.add_one_le_exp (-t)
  rw [Real.sinh_eq]
  nlinarith

/-- `(√Q + 2) log Q ≤ 0.393 Q` for `Q ≥ 13⁴`. -/
lemma sqrt_add_two_mul_log_le {Q : ℝ} (hQ : 28561 ≤ Q) : (√Q + 2) * Real.log Q ≤ 0.393 * Q := by
  have hQ0 : 0 ≤ Q := by linarith
  set w := √(√Q) with hw
  have hsq : √Q = w ^ 2 := by rw [hw, Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hQw : Q = w ^ 4 := by
    rw [show w ^ 4 = (w ^ 2) ^ 2 by ring, ← hsq, Real.sq_sqrt hQ0]
  have hw0 : 0 < w := by
    rw [hw]; apply Real.sqrt_pos.mpr; apply Real.sqrt_pos.mpr; linarith
  have hw13 : 13 ≤ w := by
    by_contra h
    push Not at h
    have : w ^ 4 < 13 ^ 4 := by gcongr
    linarith
  have hlog : Real.log Q ≤ 4 * w := by
    rw [hQw, Real.log_pow]
    have := Real.log_le_sub_one_of_pos hw0
    push_cast
    linarith
  rw [hsq, hQw]
  have h1 : (w ^ 2 + 2) * Real.log (w ^ 4) ≤ (w ^ 2 + 2) * (4 * w) := by
    rw [← hQw]; gcongr
  nlinarith [h1, mul_pos hw0 hw0]

/-! ### The primes -/

lemma card_dvd_primes_le {n : ℕ} (hn : n ≠ 0) {r : ℕ} (hr : 1 ≤ r) (Q : ℕ) :
    ((Ioc r Q).filter fun q => q.Prime ∧ q ∣ n).card ≤ Nat.log (r + 1) n := by
  set D := (Ioc r Q).filter fun q => q.Prime ∧ q ∣ n
  have hprod : ∏ q ∈ D, q ∣ n := by
    apply Finset.prod_primes_dvd
    · intro q hq; exact Nat.prime_iff.mp (mem_filter.mp hq).2.1
    · intro q hq; exact (mem_filter.mp hq).2.2
  have hpow : (r + 1) ^ D.card ≤ n := by
    rw [← Finset.prod_const]
    refine (Finset.prod_le_prod fun q hq => ?_).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hprod)
    exact (mem_Ioc.mp (mem_filter.mp hq).1).1
  exact (Nat.le_log_iff_pow_le (by omega) hn).mpr hpow

lemma primeSet_card_ge {n : ℕ} (hn : n ≠ 0) {Q : ℕ} (hr : 1 ≤ Nat.sqrt Q) :
    (Nat.primeCounting Q : ℝ) ≤ (primeSet n Q).card + (Nat.sqrt Q + 1) + Nat.log (Nat.sqrt Q + 1) n := by
  set r := Nat.sqrt Q
  set D := (Ioc r Q).filter fun q => q.Prime ∧ q ∣ n
  have hsub : Nat.primesLE Q ⊆ range (r + 1) ∪ (primeSet n Q ∪ D) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
    have hpQ : p ≤ Q := Nat.le_of_mem_primesLE hp
    simp only [mem_union, mem_range, primeSet, mem_filter, mem_Ioc, D]
    by_cases hpr : p ≤ r
    · left; omega
    · right
      push Not at hpr
      by_cases hc : p.Coprime n
      · left; exact ⟨⟨hpr, hpQ⟩, hpp, hc⟩
      · right; exact ⟨⟨hpr, hpQ⟩, hpp, (Nat.Prime.dvd_iff_not_coprime hpp).mpr hc⟩
  have hcard : (Nat.primesLE Q).card ≤ (range (r + 1)).card + ((primeSet n Q).card + D.card) :=
    (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left (card_union_le _ _) _))
  rw [Nat.primesLE_card_eq_primeCounting, card_range] at hcard
  have hD : D.card ≤ Nat.log (r + 1) n := card_dvd_primes_le hn hr Q
  have : (Nat.primeCounting Q) ≤ (primeSet n Q).card + (r + 1) + Nat.log (r + 1) n := by omega
  exact_mod_cast this

/-- The key prime-counting estimate: `|P| ≥ 1` and `K ≤ (ε/2)|P|`. -/
lemma primeSet_good (n : ℕ) (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (primeSet n (Qpar n ε)).Nonempty ∧
      (Nat.log (Nat.sqrt (Qpar n ε) + 1) (n / 2) : ℝ) ≤ ε / 2 * (primeSet n (Qpar n ε)).card := by
  have hn0 : n ≠ 0 := by omega
  have hQ0 : 32768 ≤ Qpar n ε := Nat.le_add_left _ _
  have hQ1 : 20 * Real.log n / ε ≤ (Qpar n ε : ℝ) := by
    have := Nat.le_ceil (20 * Real.log n / ε)
    unfold Qpar; push_cast; linarith
  generalize Qpar n ε = Q at *
  have hQR : (32768 : ℝ) ≤ Q := by exact_mod_cast hQ0
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hr_sq : Nat.sqrt Q * Nat.sqrt Q ≤ Q := Nat.sqrt_le Q
  have hQ_lt : Q < (Nat.sqrt Q + 1) * (Nat.sqrt Q + 1) := Nat.lt_succ_sqrt Q
  have hr1' : 1 ≤ Nat.sqrt Q := Nat.le_sqrt.mpr (by omega)
  have hcount := primeSet_card_ge hn0 (Q := Q) hr1'
  generalize Nat.sqrt Q = r at *
  set L := Nat.log (r + 1) n with hLdef
  -- log n ≤ ε Q / 20
  have hlogQ : Real.log n ≤ ε * Q / 20 := by
    rw [div_le_iff₀ hε0] at hQ1; linarith
  -- r and Q
  have hrR : (r : ℝ) ≤ √(Q : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have : ((r * r : ℕ) : ℝ) ≤ Q := by exact_mod_cast hr_sq
    push_cast at this; nlinarith
  have hr1 : 2 ≤ r + 1 := by omega
  have hQpos : (0 : ℝ) < Q := by linarith
  have hlogQpos : 0 < Real.log Q := Real.log_pos (by linarith)
  -- log(r+1) ≥ log Q / 2
  have hlogr : Real.log Q / 2 ≤ Real.log (r + 1) := by
    have h : (Q : ℝ) < (r + 1) ^ 2 := by
      have : ((Q : ℕ) : ℝ) < ((r + 1) * (r + 1) : ℕ) := by exact_mod_cast hQ_lt
      push_cast at this; nlinarith
    have := Real.log_lt_log hQpos h
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hlogr_pos : 0 < Real.log (r + 1) := by linarith
  -- L ≤ log n / log (r+1) ≤ 2 log n / log Q
  have hL : (L : ℝ) * Real.log (r + 1) ≤ Real.log n := by
    have hp : (r + 1) ^ L ≤ n := Nat.pow_log_le_self (r + 1) hn0
    have : Real.log (((r + 1) ^ L : ℕ) : ℝ) ≤ Real.log n :=
      Real.log_le_log (by positivity) (by exact_mod_cast hp)
    push_cast at this
    rwa [Real.log_pow] at this
  have hL2 : (L : ℝ) * Real.log Q ≤ 2 * Real.log n := by nlinarith
  -- π Q ≥ Q log 2 / log Q
  have hpi : (Q : ℝ) * Real.log 2 / Real.log Q ≤ Nat.primeCounting Q :=
    Chebyshev.pi_ge_of_four_le (by omega)
  -- main inequality
  have hkey := sqrt_add_two_mul_log_le (by linarith : (28561 : ℝ) ≤ Q)
  have hl2 := Real.log_two_gt_d9
  set p := ((primeSet n Q).card : ℝ) with hpdef
  -- p ≥ 1 + 2L/ε, multiplied out by ε log Q
  have hmain : ε * Real.log Q * (1 + 2 * L / ε) ≤ ε * Real.log Q * p := by
    have e1 : ε * Real.log Q * (1 + 2 * L / ε) = ε * Real.log Q + 2 * (L * Real.log Q) := by
      field_simp
    rw [e1]
    -- from hcount: p ≥ π Q - (r+1) - L
    have hp : (Nat.primeCounting Q : ℝ) - (r + 1) - L ≤ p := by
      linarith
    have hpi' : (Q : ℝ) * Real.log 2 ≤ Nat.primeCounting Q * Real.log Q := by
      rwa [div_le_iff₀ hlogQpos] at hpi
    nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ ε * Real.log Q),
      mul_le_mul_of_nonneg_left hrR hlogQpos.le]
  have hp1 : 1 + 2 * L / ε ≤ p := le_of_mul_le_mul_left hmain (by positivity)
  have hL0 : (0 : ℝ) ≤ 2 * L / ε := by positivity
  refine ⟨?_, ?_⟩
  · rw [← card_pos]
    have h0 : (0 : ℝ) < ((primeSet n Q).card : ℝ) := by rw [← hpdef]; linarith
    exact_mod_cast h0
  · have hK : Nat.log (r + 1) (n / 2) ≤ L := Nat.log_mono_right (Nat.div_le_self n 2)
    have hK' : (Nat.log (r + 1) (n / 2) : ℝ) ≤ L := by exact_mod_cast hK
    have : (L : ℝ) ≤ ε / 2 * p := by
      have h := hp1
      rw [← sub_le_iff_le_add', show (2 : ℝ) * L / ε = L / (ε / 2) by ring] at *
      have h2 : L / (ε / 2) ≤ p := by linarith
      rwa [div_le_iff₀ (by positivity), mul_comm] at h2
    linarith

/-! ### The inner-set error -/

lemma eta_le (Q : ℕ) (hQ : 1 ≤ Q) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    √2 * ((Real.log (4 * (Mpar (Npar Q ε) ε + 1)) + spar (Mpar (Npar Q ε) ε) ε *
        ((ε / 8) ^ 2 / 2 + 1 / (Npar Q ε * (1 / (2 * (Q : ℝ)))) * Real.sinh (ε / 8))) /
        (ε / 8 * spar (Mpar (Npar Q ε) ε) ε)) +
      2 * Real.pi * Npar Q ε / Mpar (Npar Q ε) ε ≤ ε / 2 := by
  set N := Npar Q ε
  set M := Mpar N ε
  set s := spar M ε
  set t := ε / 8 with ht
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hN : 48 * (Q : ℝ) / ε ≤ N := Nat.le_ceil _
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hM : 51 * (N : ℝ) / ε ≤ M := Nat.le_ceil _
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (by positivity) hM
  have hlogM : 0 < Real.log (4 * (M + 1)) := Real.log_pos (by linarith)
  have hs : 128 * Real.log (4 * (M + 1)) / ε ^ 2 ≤ s := Nat.le_ceil _
  have hspos : (0 : ℝ) < s := lt_of_lt_of_le (by positivity) hs
  have htpos : 0 < t := by positivity
  -- three pieces
  have hsplit : (Real.log (4 * (M + 1)) + s * (t ^ 2 / 2 + 1 / (N * (1 / (2 * (Q : ℝ)))) *
      Real.sinh t)) / (t * s) =
      Real.log (4 * (M + 1)) / (t * s) + t / 2 + 2 * Q / N * (Real.sinh t / t) := by
    field_simp
    ring
  have h1 : Real.log (4 * (M + 1)) / (t * s) ≤ ε / 16 := by
    rw [div_le_iff₀ (by positivity), ht]
    rw [div_le_iff₀ (by positivity)] at hs
    nlinarith
  have hsinh : Real.sinh t / t ≤ 3 / 2 := by
    rw [div_le_iff₀ htpos]
    exact sinh_le_three_halves htpos.le (by rw [ht]; linarith)
  have h3 : 2 * (Q : ℝ) / N * (Real.sinh t / t) ≤ ε / 16 := by
    have hQN : 2 * (Q : ℝ) / N ≤ ε / 24 := by
      rw [div_le_iff₀ hNpos]
      rw [div_le_iff₀ hε0] at hN
      nlinarith
    calc 2 * (Q : ℝ) / N * (Real.sinh t / t) ≤ ε / 24 * (3 / 2) := by
          gcongr
      _ = ε / 16 := by ring
  have h4 : 2 * Real.pi * N / M ≤ 2 * 3.15 * ε / 51 := by
    rw [div_le_iff₀ hMpos]
    rw [div_le_iff₀ hε0] at hM
    have := Real.pi_lt_d2
    nlinarith
  have hsqrt2 : √2 ≤ 1.415 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  rw [hsplit]
  have hsum : Real.log (4 * (M + 1)) / (t * s) + t / 2 + 2 * Q / N * (Real.sinh t / t) ≤
      3 * ε / 16 := by
    rw [ht] at h1 h3 ⊢; linarith
  have hsum0 : 0 ≤ Real.log (4 * (M + 1)) / (t * s) + t / 2 + 2 * Q / N * (Real.sinh t / t) := by
    have : 0 ≤ Real.sinh t / t := div_nonneg (Real.sinh_nonneg_iff.mpr htpos.le) htpos.le
    positivity
  calc √2 * (Real.log (4 * (M + 1)) / (t * s) + t / 2 + 2 * Q / N * (Real.sinh t / t)) +
        2 * Real.pi * N / M ≤ 1.415 * (3 * ε / 16) + 2 * 3.15 * ε / 51 := by
        gcongr
    _ ≤ ε / 2 := by nlinarith

/-! ### Main theorems -/

/-- The inner set chosen for a given `Q` is `ε/2`-balanced on `1/(2Q) ≤ |β| ≤ 1/2`. -/
lemma inner_good (Q : ℕ) (hQ : 1 ≤ Q) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (β : ℝ)
    (hβ1 : 1 / (2 * (Q : ℝ)) ≤ |β|) (hβ2 : |β| ≤ 1 / 2) :
    ‖innerSum (listInner (greedyList (Npar Q ε) (Mpar (Npar Q ε) ε) (1 / (2 * (Q : ℝ))) (ε / 8)
      (spar (Mpar (Npar Q ε) ε) ε))) β‖ ≤ ε / 2 := by
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hNb : 48 * (Q : ℝ) / ε ≤ Npar Q ε := Nat.le_ceil _
  have hMb : 51 * (Npar Q ε : ℝ) / ε ≤ Mpar (Npar Q ε) ε := Nat.le_ceil _
  have hsb : 128 * Real.log (4 * ((Mpar (Npar Q ε) ε : ℝ) + 1)) / ε ^ 2 ≤
      spar (Mpar (Npar Q ε) ε) ε := Nat.le_ceil _
  have hNR : (0 : ℝ) < Npar Q ε := lt_of_lt_of_le (by positivity) hNb
  have hMR : (0 : ℝ) < Mpar (Npar Q ε) ε := lt_of_lt_of_le (by positivity) hMb
  have hlog : 0 < Real.log (4 * ((Mpar (Npar Q ε) ε : ℝ) + 1)) := Real.log_pos (by linarith)
  have hsR : (0 : ℝ) < spar (Mpar (Npar Q ε) ε) ε := lt_of_lt_of_le (by positivity) hsb
  have hN : 0 < Npar Q ε := by exact_mod_cast hNR
  have hM : 0 < Mpar (Npar Q ε) ε := by exact_mod_cast hMR
  have hs : 0 < spar (Mpar (Npar Q ε) ε) ε := by exact_mod_cast hsR
  have hMδ : 2 ≤ (Mpar (Npar Q ε) ε : ℝ) * (1 / (2 * (Q : ℝ))) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ hε0] at hMb hNb
    nlinarith
  exact (greedy_inner_bound (Npar Q ε) (Mpar (Npar Q ε) ε) (1 / (2 * (Q : ℝ))) (ε / 8) hN hM
    (by positivity) hMδ (by positivity) _ hs β hβ1 hβ2).trans (eta_le Q hQ hε0 hε1)

/-- **Main theorem (bias).** -/
theorem main_bias (n : ℕ) [NeZero n] (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (ℓ : ZMod n) (hℓ : ℓ ≠ 0) : ‖expSum (indexSet n ε) (element n ε) ℓ‖ ≤ ε := by
  obtain ⟨hPne, hK⟩ := primeSet_good n hn hε0 hε1
  have hQ0 : 32768 ≤ Qpar n ε := Nat.le_add_left _ _
  have hr : 1 ≤ Nat.sqrt (Qpar n ε) := Nat.le_sqrt.mpr (by omega)
  have hP : ∀ q ∈ primeSet n (Qpar n ε),
      q.Prime ∧ Nat.sqrt (Qpar n ε) < q ∧ q ≤ Qpar n ε ∧ q.Coprime n := by
    intro q hq
    simp only [primeSet, mem_filter, mem_Ioc] at hq
    exact ⟨hq.2.1, hq.1.1, hq.1.2, hq.2.2⟩
  have hcore := core_bias_bound (n := n) (m := Nat.sqrt (Qpar n ε)) (Q := Qpar n ε) hr
    (primeSet n (Qpar n ε)) hP hPne (listInner (innerList n ε)) (η := ε / 2) (by positivity)
    (fun β h1 h2 => inner_good (Qpar n ε) (by omega) hε0 hε1 β h1 h2) ℓ hℓ
  have hPc : (0 : ℝ) < (primeSet n (Qpar n ε)).card := by exact_mod_cast hPne.card_pos
  have hdiv : (Nat.log (Nat.sqrt (Qpar n ε) + 1) (n / 2) : ℝ) / (primeSet n (Qpar n ε)).card ≤
      ε / 2 := by
    rw [div_le_iff₀ hPc]; linarith
  calc ‖expSum (indexSet n ε) (element n ε) ℓ‖
      = ‖expSum (primeSet n (Qpar n ε) ×ˢ univ) (fracSet (listInner (innerList n ε))) ℓ‖ := rfl
    _ ≤ _ := hcore
    _ ≤ ε := by linarith

/-- **Main theorem (size).** `|S| ≤ 1625 · (20 log n / ε + 32769) / ε²`. -/
theorem main_size (n : ℕ) (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ((indexSet n ε).card : ℝ) ≤ 1625 * (20 * Real.log n / ε + 32769) / ε ^ 2 := by
  have hQ0 : 32768 ≤ Qpar n ε := Nat.le_add_left _ _
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hQup : (Qpar n ε : ℝ) ≤ 20 * Real.log n / ε + 32769 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 20 * Real.log n / ε by positivity)
    unfold Qpar; push_cast; linarith
  have hQlo : 20 * Real.log n / ε ≤ (Qpar n ε : ℝ) := by
    have := Nat.le_ceil (20 * Real.log n / ε)
    unfold Qpar; push_cast; linarith
  have hcardS : (indexSet n ε).card =
      (primeSet n (Qpar n ε)).card * spar (Mpar (Npar (Qpar n ε) ε) ε) ε := by
    rw [indexSet, card_product, card_univ, Fintype.card_fin, innerList, greedyList_length]
  rw [hcardS]
  generalize Qpar n ε = Q at *
  have hQR : (32768 : ℝ) ≤ Q := by exact_mod_cast hQ0
  have hQpos : (0 : ℝ) < Q := by linarith
  have hinvε : 1 / ε ≤ Q := by
    have : 1 / ε ≤ 20 * Real.log n / ε := by
      rw [div_le_div_iff_of_pos_right hε0]; linarith
    linarith
  have hNle : (Npar Q ε : ℝ) ≤ 48 * Q / ε + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hMle : (Mpar (Npar Q ε) ε : ℝ) ≤ 51 * (Npar Q ε) / ε + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hsle : (spar (Mpar (Npar Q ε) ε) ε : ℝ) ≤
      128 * Real.log (4 * ((Mpar (Npar Q ε) ε : ℝ) + 1)) / ε ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (by
      have : 0 ≤ Real.log (4 * ((Mpar (Npar Q ε) ε : ℝ) + 1)) := Real.log_nonneg (by
        have : (0 : ℝ) ≤ Mpar (Npar Q ε) ε := by positivity
        linarith)
      positivity)).le
  generalize spar (Mpar (Npar Q ε) ε) ε = s at *
  generalize Mpar (Npar Q ε) ε = M at *
  generalize Npar Q ε = N at *
  -- |P| ≤ π Q ≤ 2 log 4 · Q / log Q + √Q
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hP : ((primeSet n Q).card : ℝ) ≤ 2 * Real.log 4 * Q / Real.log Q + √(Q : ℝ) := by
    have hsub : primeSet n Q ⊆ Nat.primesLE Q := by
      intro q hq
      simp only [primeSet, mem_filter, mem_Ioc] at hq
      exact Nat.mem_primesLE.mpr ⟨hq.1.2, hq.2.1⟩
    have h1 : ((primeSet n Q).card : ℝ) ≤ Nat.primeCounting Q := by
      have := card_le_card hsub
      rw [Nat.primesLE_card_eq_primeCounting] at this
      exact_mod_cast this
    have h2 := Chebyshev.pi_le_log4_mul_div (x := (Q : ℝ)) (by linarith)
    rw [Nat.floor_natCast, Real.log_sqrt hQpos.le] at h2
    calc ((primeSet n Q).card : ℝ) ≤ Nat.primeCounting Q := h1
      _ ≤ Real.log 4 * Q / (Real.log Q / 2) + √(Q : ℝ) := h2
      _ = 2 * Real.log 4 * Q / Real.log Q + √(Q : ℝ) := by field_simp
  -- s ≤ 513 log Q / ε²
  have hs : (s : ℝ) ≤ 513 * Real.log Q / ε ^ 2 := by
    have hεQ : 1 ≤ ε * Q := by rwa [div_le_iff₀ hε0, mul_comm] at hinvε
    have hM4 : 4 * ((M : ℝ) + 1) ≤ (Q : ℝ) ^ 4 := by
      have hNQ : (N : ℝ) ≤ 49 * Q / ε := by
        have : (1 : ℝ) ≤ Q / ε := by rw [le_div_iff₀ hε0]; nlinarith
        calc (N : ℝ) ≤ 48 * Q / ε + 1 := hNle
          _ ≤ 48 * Q / ε + Q / ε := by linarith
          _ = 49 * Q / ε := by ring
      have hMQ : (M : ℝ) + 1 ≤ 2501 * Q / ε ^ 2 := by
        have hq1 : (1 : ℝ) ≤ Q / ε ^ 2 := by
          rw [le_div_iff₀ (by positivity)]; nlinarith
        calc (M : ℝ) + 1 ≤ 51 * N / ε + 2 := by linarith
          _ ≤ 51 * (49 * Q / ε) / ε + 2 := by gcongr
          _ = 2499 * (Q / ε ^ 2) + 2 := by ring
          _ ≤ 2501 * (Q / ε ^ 2) := by linarith
          _ = 2501 * Q / ε ^ 2 := by ring
      have hεinv2 : 1 / ε ^ 2 ≤ (Q : ℝ) ^ 2 := by
        rw [one_div, ← inv_pow]
        gcongr
        rw [inv_eq_one_div]; exact hinvε
      calc 4 * ((M : ℝ) + 1) ≤ 4 * (2501 * Q / ε ^ 2) := by gcongr
        _ = 10004 * Q * (1 / ε ^ 2) := by ring
        _ ≤ 10004 * Q * Q ^ 2 := by gcongr
        _ ≤ Q * Q * Q ^ 2 := by gcongr; nlinarith
        _ = (Q : ℝ) ^ 4 := by ring
    have hlogM : Real.log (4 * ((M : ℝ) + 1)) ≤ 4 * Real.log Q := by
      have := Real.log_le_log (by positivity) hM4
      rwa [Real.log_pow] at this
    have hone : (1 : ℝ) ≤ Real.log Q / ε ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : 10 ≤ Real.log Q := by
        have h := Real.log_le_log (by norm_num) hQR
        have h' : Real.log (32768 : ℝ) = 15 * Real.log 2 := by
          rw [show (32768 : ℝ) = 2 ^ 15 by norm_num, Real.log_pow]; push_cast; ring
        linarith
      nlinarith
    calc (s : ℝ) ≤ 128 * Real.log (4 * ((M : ℝ) + 1)) / ε ^ 2 + 1 := hsle
      _ ≤ 128 * (4 * Real.log Q) / ε ^ 2 + Real.log Q / ε ^ 2 := by gcongr
      _ = 513 * Real.log Q / ε ^ 2 := by ring
  -- combine
  have hkey := sqrt_add_two_mul_log_le (by linarith : (28561 : ℝ) ≤ Q)
  have hlog4 : Real.log 4 < 1.3863 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  push_cast
  have hsQ : √(Q : ℝ) * Real.log Q ≤ 0.393 * Q := by nlinarith
  calc ((primeSet n Q).card : ℝ) * s
      ≤ (2 * Real.log 4 * Q / Real.log Q + √(Q : ℝ)) * (513 * Real.log Q / ε ^ 2) := by
        gcongr
    _ = 513 * (2 * Real.log 4 * Q + √(Q : ℝ) * Real.log Q) / ε ^ 2 := by
        field_simp
    _ ≤ 513 * (2 * 1.3863 * Q + 0.393 * Q) / ε ^ 2 := by gcongr
    _ = 513 * (2 * 1.3863 + 0.393) * Q / ε ^ 2 := by ring
    _ ≤ 1625 * Q / ε ^ 2 := by
        gcongr
        norm_num
    _ ≤ 1625 * (20 * Real.log n / ε + 32769) / ε ^ 2 := by gcongr

end SmallBias

/-! ### The theorem in plain terms -/

namespace SmallBias

/-- The explicit list of integers `k ∈ [0, n)` (with multiplicity). -/
noncomputable def explicitList (n : ℕ) (ε : ℝ) : List ℕ :=
  (indexSet n ε).toList.map fun a => (element n ε a).val

/-- **Small-bias sets in `ℤ/nℤ`, stated without any auxiliary definitions.** For `n ≥ 2` and
`0 < ε ≤ 1`, the explicitly constructed list `ks = explicitList n ε` consists of integers in
`[0, n)`, has length at most `1625 (20 log n / ε + 32769) / ε²`, and for every `0 < l < n`
the average of `exp(2πi k l / n)` over `k ∈ ks` has absolute value at most `ε`. -/
theorem explicitList_spec (n : ℕ) (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ k ∈ explicitList n ε, k < n) ∧
    ((explicitList n ε).length : ℝ) ≤ 1625 * (20 * Real.log n / ε + 32769) / ε ^ 2 ∧
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
        e (θ ((l : ZMod n) * x)) := by
      intro x
      have h := e_div_eq_of_cast_eq (n := n) (a := (x.val * l : ℕ)) (b := ((l : ZMod n) * x).valMinAbs)
        (by push_cast; rw [ZMod.natCast_zmod_val]; ring)
      unfold θ
      rw [← h]
      unfold e
      congr 1
      push_cast
      ring
    have hsum : ((explicitList n ε).map fun k : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * k * l / n)).sum =
        ∑ a ∈ indexSet n ε, e (θ ((l : ZMod n) * element n ε a)) := by
      rw [explicitList, List.map_map, ← Finset.sum_map_toList]
      congr 1
      apply List.map_congr_left
      intro a _
      simp only [Function.comp_apply]
      exact hterm _
    rw [hsum, hlen]
    exact hmain

end SmallBias
