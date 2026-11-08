import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.BigOperators.Associated

/-!
# Small-bias sets in `ZMod n`: the core bias bound

`S = { c_i * q⁻¹ : q ∈ P, i < s }` where `P` is a set of primes in `(m, Q]` coprime to `n`.

* `e x = exp(2πix)`, `θ y = y.valMinAbs / n ∈ [-1/2, 1/2]`.
* `expSum T k ℓ = |T|⁻¹ ∑_{a ∈ T} e(θ(ℓ * k a))`, the normalised character sum of the
  multiset `k(T)`.
* `innerSum C β = s⁻¹ ∑_i e(C_i β)`.

Main result `core_bias_bound`: if the inner set is `η`-balanced on `1/(2Q) ≤ |β| ≤ 1/2`, then every
nontrivial character sum of `S` has norm at most `Nat.log (m+1) (n/2) / |P| + η`.
-/

open Finset

namespace SmallBias

/-- `e x = exp (2 π i x)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma e_intCast (k : ℤ) : e k = 1 := by
  unfold e
  rw [show (2 * Real.pi * Complex.I * ((k : ℝ) : ℂ)) = k * (2 * Real.pi * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

lemma e_add_intCast (x : ℝ) (k : ℤ) : e (x + k) = e x := by
  rw [e_add, e_intCast, mul_one]

lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  rw [show (2 * Real.pi * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

variable {n : ℕ}

/-- The centred angle of `y : ZMod n`, in `[-1/2, 1/2]`. -/
noncomputable def θ (y : ZMod n) : ℝ := (y.valMinAbs : ℝ) / n

/-- Two integers that agree mod `n` give the same point `e (a / n)`. -/
lemma e_div_eq_of_cast_eq [NeZero n] {a b : ℤ} (h : (a : ZMod n) = (b : ZMod n)) :
    e ((a : ℝ) / n) = e ((b : ℝ) / n) := by
  have hdvd : (n : ℤ) ∣ a - b := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h, sub_self]
  obtain ⟨k, hk⟩ := hdvd
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have : (a : ℝ) / n = (b : ℝ) / n + k := by
    have hk' : (a : ℝ) = b + n * k := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hk
      push_cast at this
      linarith
    rw [hk']
    field_simp
  rw [this, e_add_intCast]

lemma e_θ_natCast_mul [NeZero n] (c : ℕ) (y : ZMod n) :
    e (θ ((c : ZMod n) * y)) = e (c * θ y) := by
  unfold θ
  rw [show (c : ℝ) * ((y.valMinAbs : ℝ) / n) = (((c : ℤ) * y.valMinAbs : ℤ) : ℝ) / n by
    push_cast; ring]
  apply e_div_eq_of_cast_eq
  push_cast
  simp

lemma abs_valMinAbs_mul_two_le [NeZero n] (y : ZMod n) : |(y.valMinAbs : ℝ)| * 2 ≤ n := by
  have h := ZMod.natAbs_valMinAbs_le y
  have h2 : y.valMinAbs.natAbs * 2 ≤ n := by omega
  have : |(y.valMinAbs : ℝ)| = (y.valMinAbs.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; rfl
  rw [this]
  exact_mod_cast h2

lemma abs_θ_le_half [NeZero n] (y : ZMod n) : |θ y| ≤ 1 / 2 := by
  unfold θ
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  rw [abs_div, abs_of_pos hn, div_le_iff₀ hn]
  linarith [abs_valMinAbs_mul_two_le y]

/-- Normalised character sum of the multiset `{k a : a ∈ T}` at frequency `ℓ`. -/
noncomputable def expSum {α : Type*} (T : Finset α) (k : α → ZMod n) (ℓ : ZMod n) : ℂ :=
  (T.card : ℂ)⁻¹ * ∑ a ∈ T, e (θ (ℓ * k a))

/-- Normalised exponential sum of the inner set `C` at the real frequency `β`. -/
noncomputable def innerSum {s : ℕ} (C : Fin s → ℕ) (β : ℝ) : ℂ :=
  (s : ℂ)⁻¹ * ∑ i, e (C i * β)

lemma norm_innerSum_le_one {s : ℕ} (C : Fin s → ℕ) (β : ℝ) : ‖innerSum C β‖ ≤ 1 := by
  unfold innerSum
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; simp
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have : ‖∑ i, e (C i * β)‖ ≤ s := by
    calc ‖∑ i, e (C i * β)‖ ≤ ∑ i : Fin s, ‖e (C i * β)‖ := norm_sum_le _ _
      _ = s := by simp [norm_e]
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  rw [inv_mul_le_iff₀ hs', mul_one]
  exact this

/-- The set `S`: index `(q, i) ↦ C_i * q⁻¹`. -/
noncomputable def fracSet {s : ℕ} (C : Fin s → ℕ) : ℕ × Fin s → ZMod n :=
  fun a => (C a.2 : ZMod n) * (a.1 : ZMod n)⁻¹

/-- **Lemma 1** (product structure). -/
lemma expSum_fracSet [NeZero n] {s : ℕ} (P : Finset ℕ) (C : Fin s → ℕ) (ℓ : ZMod n) :
    expSum (P ×ˢ (univ : Finset (Fin s))) (fracSet C) ℓ =
      (P.card : ℂ)⁻¹ * ∑ q ∈ P, innerSum C (θ (ℓ * (q : ZMod n)⁻¹)) := by
  unfold expSum innerSum fracSet
  rw [card_product, card_univ, Fintype.card_fin, sum_product, mul_sum, mul_sum]
  push_cast
  rw [mul_inv]
  refine sum_congr rfl fun q _ => ?_
  rw [mul_assoc]
  congr 2
  refine sum_congr rfl fun i _ => ?_
  rw [← e_θ_natCast_mul]
  congr 2
  ring

/-- **Lemma 2** (a bad prime divides `ℓ`): if `q ≤ Q` and the step `θ(ℓ q⁻¹)` is shorter than
`1/(2Q)`, then `q` divides the centred representative of `ℓ`. -/
lemma dvd_of_θ_small [NeZero n] {Q q : ℕ} (hq : q ≤ Q) (hcop : q.Coprime n) (ℓ : ZMod n)
    (hsmall : |θ (ℓ * (q : ZMod n)⁻¹)| < 1 / (2 * Q)) : (q : ℤ) ∣ ℓ.valMinAbs := by
  set y := ℓ * (q : ZMod n)⁻¹ with hy
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hm : (0 : ℝ) < Q := by
    rcases Nat.eq_zero_or_pos Q with h | h
    · subst h
      simp only [Nat.cast_zero, mul_zero, div_zero] at hsmall
      exact absurd hsmall (not_lt.mpr (abs_nonneg _))
    · exact_mod_cast h
  -- y * q = ℓ
  have hyq : y * (q : ZMod n) = ℓ := by
    rw [hy, mul_assoc, mul_comm ((q : ZMod n)⁻¹), ZMod.coe_mul_inv_eq_one q hcop, mul_one]
  -- |y.valMinAbs| * 4m < n
  have h1 : |(y.valMinAbs : ℝ)| * (2 * Q) < n := by
    unfold θ at hsmall
    rw [abs_div, abs_of_pos hn, div_lt_div_iff₀ hn (by positivity), one_mul] at hsmall
    linarith
  -- the integer y.valMinAbs * q - ℓ.valMinAbs is divisible by n and smaller than n
  have hdvd : (n : ℤ) ∣ y.valMinAbs * q - ℓ.valMinAbs := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [hyq]
  have hlt : |((y.valMinAbs * q - ℓ.valMinAbs : ℤ) : ℝ)| < n := by
    push_cast
    have hqR : (q : ℝ) ≤ Q := by exact_mod_cast hq
    have ha : |(y.valMinAbs : ℝ) * q| * 2 < n := by
      rw [abs_mul, Nat.abs_cast]
      nlinarith [abs_nonneg (y.valMinAbs : ℝ)]
    have hb := abs_valMinAbs_mul_two_le ℓ
    calc |(y.valMinAbs : ℝ) * q - ℓ.valMinAbs|
        ≤ |(y.valMinAbs : ℝ) * q| + |(ℓ.valMinAbs : ℝ)| := abs_sub _ _
      _ < n := by linarith
  have hzero : y.valMinAbs * q - ℓ.valMinAbs = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd hdvd
    have : |((y.valMinAbs * q - ℓ.valMinAbs : ℤ) : ℝ)| =
        ((|y.valMinAbs * q - ℓ.valMinAbs| : ℤ) : ℝ) := by
      push_cast; rfl
    rw [this] at hlt
    exact_mod_cast hlt
  exact ⟨y.valMinAbs, by linarith⟩

/-- **Lemma 2** (counting): at most `Nat.log (m+1) (n/2)` primes larger than `m` divide `ℓ`. -/
lemma card_bad_le [NeZero n] {m : ℕ} (hm : 1 ≤ m) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime ∧ m < q) (ℓ : ZMod n) (hℓ : ℓ ≠ 0) :
    (P.filter fun q : ℕ => (q : ℤ) ∣ ℓ.valMinAbs).card ≤ Nat.log (m + 1) (n / 2) := by
  set B := P.filter fun q : ℕ => (q : ℤ) ∣ ℓ.valMinAbs
  set z := ℓ.valMinAbs.natAbs with hz
  have hz0 : z ≠ 0 := by
    rw [hz, Int.natAbs_ne_zero, Ne, ZMod.valMinAbs_eq_zero]
    exact hℓ
  have hzle : z ≤ n / 2 := ZMod.natAbs_valMinAbs_le ℓ
  -- product of the bad primes divides z
  have hprod : ∏ q ∈ B, q ∣ z := by
    apply Finset.prod_primes_dvd
    · intro q hq
      exact (Nat.prime_iff.mp (hP q (mem_filter.mp hq).1).1)
    · intro q hq
      have := (mem_filter.mp hq).2
      rw [hz]
      exact Int.natCast_dvd.mp this
  have hprod_le : ∏ q ∈ B, q ≤ z := Nat.le_of_dvd (Nat.pos_of_ne_zero hz0) hprod
  have hpow : (m + 1) ^ B.card ≤ ∏ q ∈ B, q := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun q hq => (hP q (mem_filter.mp hq).1).2)
  have hfinal : (m + 1) ^ B.card ≤ n / 2 := hpow.trans (hprod_le.trans hzle)
  have hn2 : n / 2 ≠ 0 := by omega
  exact (Nat.le_log_iff_pow_le (by omega) hn2).mpr hfinal

/-- **Core theorem.** -/
theorem core_bias_bound [NeZero n] {m Q s : ℕ} (hm : 1 ≤ m) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime ∧ m < q ∧ q ≤ Q ∧ q.Coprime n) (hPne : P.Nonempty)
    (C : Fin s → ℕ) {η : ℝ} (hη : 0 ≤ η)
    (hinner : ∀ β : ℝ, 1 / (2 * Q) ≤ |β| → |β| ≤ 1 / 2 → ‖innerSum C β‖ ≤ η)
    (ℓ : ZMod n) (hℓ : ℓ ≠ 0) :
    ‖expSum (P ×ˢ (univ : Finset (Fin s))) (fracSet C) ℓ‖ ≤
      (Nat.log (m + 1) (n / 2) : ℝ) / P.card + η := by
  rw [expSum_fracSet]
  have hPc : (0 : ℝ) < P.card := by exact_mod_cast hPne.card_pos
  -- pointwise bound
  have hpt : ∀ q ∈ P, ‖innerSum C (θ (ℓ * (q : ZMod n)⁻¹))‖ ≤
      (if (q : ℤ) ∣ ℓ.valMinAbs then 1 else 0) + η := by
    intro q hq
    by_cases hd : (q : ℤ) ∣ ℓ.valMinAbs
    · simp only [hd, ↓reduceIte]
      linarith [norm_innerSum_le_one C (θ (ℓ * (q : ZMod n)⁻¹))]
    · simp only [hd, ↓reduceIte, zero_add]
      apply hinner _ _ (abs_θ_le_half _)
      by_contra hlt
      exact hd (dvd_of_θ_small (hP q hq).2.2.1 (hP q hq).2.2.2 ℓ (not_le.mp hlt))
  have hsum : ∑ q ∈ P, ‖innerSum C (θ (ℓ * (q : ZMod n)⁻¹))‖ ≤
      (P.filter fun q : ℕ => (q : ℤ) ∣ ℓ.valMinAbs).card + P.card * η := by
    calc ∑ q ∈ P, ‖innerSum C (θ (ℓ * (q : ZMod n)⁻¹))‖
        ≤ ∑ q ∈ P, ((if (q : ℤ) ∣ ℓ.valMinAbs then 1 else 0) + η) := sum_le_sum hpt
      _ = (P.filter fun q : ℕ => (q : ℤ) ∣ ℓ.valMinAbs).card + P.card * η := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← sum_filter, sum_const, nsmul_eq_mul,
          mul_one]
  have hbad := card_bad_le hm P (fun q hq => ⟨(hP q hq).1, (hP q hq).2.1⟩) ℓ hℓ
  calc ‖(P.card : ℂ)⁻¹ * ∑ q ∈ P, innerSum C (θ (ℓ * (q : ZMod n)⁻¹))‖
      ≤ (P.card : ℝ)⁻¹ * ∑ q ∈ P, ‖innerSum C (θ (ℓ * (q : ZMod n)⁻¹))‖ := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
        gcongr
        exact norm_sum_le _ _
    _ ≤ (P.card : ℝ)⁻¹ * ((P.filter fun q : ℕ => (q : ℤ) ∣ ℓ.valMinAbs).card + P.card * η) := by
        gcongr
    _ ≤ (Nat.log (m + 1) (n / 2) : ℝ) / P.card + η := by
        rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hPc.ne', one_mul, inv_mul_eq_div]
        gcongr

end SmallBias
