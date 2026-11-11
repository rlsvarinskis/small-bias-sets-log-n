import Smallbias.Core
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-!
# The greedy multipliers (Lemma 3)

`greedyList D N M δ t s` picks the multipliers `c₁, …, c_s ∈ [0, N)` one at a time. A **check** is a
pair (grid angle `j/M`, compass direction `u < D`). The **reach** of hand `c` for that check is
`reach j u c = Re (dir D u · e(c · j/M))`, where `dir D u = e(-u/D)`. Each check keeps a running
total of the reaches of the hands chosen so far, its **danger** is `exp (t · total)`, and the
potential `Φ` is the sum of all dangers:
`Φ(cs) = ∑_{j ∈ grid} ∑_{u < D} exp (t · ∑_{c ∈ cs} reach j u c)`.
Each step adds the least `c < N` that makes `Φ` smallest.

`greedy_mult_bound` (Lemma 3): for `D ≥ 3` and every base angle `δ ≤ |a| ≤ 1/2`,
`‖groupAvg C a‖ ≤ (log (D(M+1)) + s (t²/2 + sinh t /(Nδ))) / (t s) / cos(π/D) + 2πN/M`.
-/

open Finset

namespace SmallBias

/-! ### Elementary inequalities -/

/-- Convexity of `exp`: for `x ∈ [-1,1]`, `exp (t x) ≤ cosh t + x sinh t`. -/
lemma exp_mul_le_cosh_add (t : ℝ) {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    Real.exp (t * x) ≤ Real.cosh t + x * Real.sinh t := by
  have ha : 0 ≤ (1 - x) / 2 := by linarith
  have hb : 0 ≤ (1 + x) / 2 := by linarith
  have hab : (1 - x) / 2 + (1 + x) / 2 = 1 := by ring
  have h := convexOn_exp.2 (Set.mem_univ (-t)) (Set.mem_univ t) ha hb hab
  simp only [smul_eq_mul] at h
  rw [Real.cosh_eq, Real.sinh_eq]
  calc Real.exp (t * x) = Real.exp ((1 - x) / 2 * -t + (1 + x) / 2 * t) := by congr 1; ring
    _ ≤ (1 - x) / 2 * Real.exp (-t) + (1 + x) / 2 * Real.exp t := h
    _ = (Real.exp t + Real.exp (-t)) / 2 + x * ((Real.exp t - Real.exp (-t)) / 2) := by ring

/-- Hoeffding-type bound for an average of values in `[-1,1]` with small mean. -/
lemma avg_exp_le {N : ℕ} (hN : 0 < N) (f : ℕ → ℝ) (hf : ∀ c, -1 ≤ f c ∧ f c ≤ 1)
    {t μ : ℝ} (ht : 0 ≤ t) (hμ : |(N : ℝ)⁻¹ * ∑ c ∈ range N, f c| ≤ μ) :
    (N : ℝ)⁻¹ * ∑ c ∈ range N, Real.exp (t * f c) ≤ Real.exp (t ^ 2 / 2 + μ * Real.sinh t) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set m := (N : ℝ)⁻¹ * ∑ c ∈ range N, f c with hm
  have h1 : (N : ℝ)⁻¹ * ∑ c ∈ range N, Real.exp (t * f c) ≤ Real.cosh t + m * Real.sinh t := by
    calc (N : ℝ)⁻¹ * ∑ c ∈ range N, Real.exp (t * f c)
        ≤ (N : ℝ)⁻¹ * ∑ c ∈ range N, (Real.cosh t + f c * Real.sinh t) := by
          gcongr with c hc
          exact exp_mul_le_cosh_add t (hf c).1 (hf c).2
      _ = Real.cosh t + m * Real.sinh t := by
          rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_mul, hm, mul_add,
            ← mul_assoc, inv_mul_cancel₀ hNR.ne', one_mul, mul_assoc]
  have hsinh : 0 ≤ Real.sinh t := Real.sinh_nonneg_iff.mpr ht
  have h2 : m * Real.sinh t ≤ μ * Real.sinh t :=
    mul_le_mul_of_nonneg_right ((le_abs_self m).trans hμ) hsinh
  have h3 : Real.cosh t ≤ Real.exp (t ^ 2 / 2) := Real.cosh_le_exp_half_sq t
  have h4 : 0 ≤ μ * Real.sinh t := mul_nonneg ((abs_nonneg _).trans hμ) hsinh
  have h5 : 1 ≤ Real.exp (t ^ 2 / 2) := Real.one_le_exp (by positivity)
  calc _ ≤ Real.cosh t + m * Real.sinh t := h1
    _ ≤ Real.exp (t ^ 2 / 2) * (1 + μ * Real.sinh t) := by nlinarith
    _ ≤ Real.exp (t ^ 2 / 2) * Real.exp (μ * Real.sinh t) := by
        gcongr
        linarith [Real.add_one_le_exp (μ * Real.sinh t)]
    _ = Real.exp (t ^ 2 / 2 + μ * Real.sinh t) := (Real.exp_add _ _).symm

lemma e_natCast_mul (c : ℕ) (γ : ℝ) : e (c * γ) = e γ ^ c := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma e_eq_exp_I_mul (x : ℝ) : e x = Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) := by
  unfold e
  congr 1
  push_cast
  ring

/-- `‖e γ - 1‖ ≥ 4γ` for `0 ≤ γ ≤ 1/2`. -/
lemma four_mul_le_norm_e_sub_one {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1 / 2) : 4 * γ ≤ ‖e γ - 1‖ := by
  rw [e_eq_exp_I_mul, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hs : 2 / Real.pi * (Real.pi * γ) ≤ Real.sin (Real.pi * γ) :=
    Real.mul_le_sin (by positivity) (by nlinarith [Real.pi_pos])
  have hpi : 2 / Real.pi * (Real.pi * γ) = 2 * γ := by field_simp
  rw [show 2 * Real.pi * γ / 2 = Real.pi * γ by ring, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_two]
  have : 2 * γ ≤ |Real.sin (Real.pi * γ)| := by
    rw [← hpi]; exact hs.trans (le_abs_self _)
  linarith

/-- The mean of `e(cγ)` over `c < N` is small away from `γ = 0`. -/
lemma norm_sum_e_le (N : ℕ) {γ : ℝ} (h0 : 0 < γ) (h1 : γ ≤ 1 / 2) :
    ‖∑ c ∈ range N, e (c * γ)‖ ≤ 1 / (2 * γ) := by
  have hlow := four_mul_le_norm_e_sub_one h0.le h1
  have hpos : 0 < ‖e γ - 1‖ := by linarith
  have hne : e γ ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hpos; exact lt_irrefl _ hpos
  simp_rw [e_natCast_mul]
  rw [geom_sum_eq hne, norm_div]
  have hnum : ‖e γ ^ N - 1‖ ≤ 2 := by
    calc ‖e γ ^ N - 1‖ ≤ ‖e γ ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_e, one_pow, norm_one]; norm_num
  rw [div_le_div_iff₀ hpos (by positivity)]
  nlinarith

/-- Lipschitz bound for `e`. -/
lemma norm_e_sub_e_le (x y : ℝ) : ‖e x - e y‖ ≤ 2 * Real.pi * |x - y| := by
  have h : e x - e y = e y * (e (x - y) - 1) := by
    rw [mul_sub, ← e_add, mul_one]; congr 2; ring
  rw [h, norm_mul, norm_e, one_mul, e_eq_exp_I_mul]
  calc ‖Complex.exp (Complex.I * ((2 * Real.pi * (x - y) : ℝ) : ℂ)) - 1‖
      ≤ ‖(2 * Real.pi * (x - y) : ℝ)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * |x - y| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

lemma e_neg (x : ℝ) : e (-x) = (starRingEnd ℂ) (e x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast
  ring

/-! ### Compass directions -/

/-- Real part of a rotated complex number. -/
lemma re_e_mul (a : ℝ) (z : ℂ) :
    (e a * z).re = ‖z‖ * Real.cos (2 * Real.pi * a + Complex.arg z) := by
  have he : e a = Complex.exp (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I) := by
    unfold e; congr 1; push_cast; ring
  rw [Complex.mul_re, he, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Real.cos_add, ← Complex.norm_mul_cos_arg z, ← Complex.norm_mul_sin_arg z]
  ring

/-- Compass direction `u`: `dir D u = e(-u/D)`, so `Re (dir D u · z)` is the reach of `z` in
direction `u`. -/
noncomputable def dir (D u : ℕ) : ℂ := e (-(u : ℝ) / D)

/-- Every arrow is within angle `π/D` of one of the `D` directions, so its reach there is at least
`cos(π/D)` times its length. -/
lemma exists_dir_ge (z : ℂ) {D : ℕ} (hD : 0 < D) :
    ∃ u < D, ‖z‖ * Real.cos (Real.pi / D) ≤ (dir D u * z).re := by
  set θ := Complex.arg z
  set j : ℤ := round (θ * D / (2 * Real.pi))
  have hDz : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hnn : 0 ≤ j % D := Int.emod_nonneg _ hDz
  have hlt : j % D < D := Int.emod_lt_of_pos _ (by exact_mod_cast hD)
  refine ⟨(j % D).toNat, by omega, ?_⟩
  have hu : (((j % D).toNat : ℕ) : ℝ) = j - D * ((j / D : ℤ) : ℝ) := by
    have h1 : (((j % D).toNat : ℕ) : ℤ) = j - D * (j / D) := by
      rw [Int.toNat_of_nonneg hnn, Int.emod_def]
    have h2 := congrArg (fun x : ℤ => (x : ℝ)) h1
    push_cast at h2
    exact h2
  rw [dir, re_e_mul]
  have hangle : 2 * Real.pi * (-(((j % D).toNat : ℕ) : ℝ) / D) + θ =
      (θ - 2 * Real.pi * j / D) + ((j / D : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hu]; field_simp; ring
  rw [hangle, Real.cos_add_int_mul_two_pi]
  have hbound : |θ - 2 * Real.pi * j / D| ≤ Real.pi / D := by
    have h : θ - 2 * Real.pi * j / D = 2 * Real.pi / D * (θ * D / (2 * Real.pi) - j) := by
      field_simp
    rw [h, abs_mul, abs_of_pos (by positivity)]
    calc 2 * Real.pi / D * |θ * D / (2 * Real.pi) - j| ≤ 2 * Real.pi / D * (1 / 2) := by
          gcongr; exact abs_sub_round _
      _ = Real.pi / D := by ring
  have hcos : Real.cos (Real.pi / D) ≤ Real.cos (θ - 2 * Real.pi * j / D) := by
    rw [← Real.cos_abs (θ - 2 * Real.pi * j / D)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
      (div_le_self Real.pi_pos.le (by exact_mod_cast hD)) hbound
  exact mul_le_mul_of_nonneg_left hcos (norm_nonneg _)

/-! ### A list of multipliers -/

lemma sum_fin_get {a : Type*} [AddCommMonoid a] (f : ℕ → a) (L : List ℕ) :
    ∑ i : Fin L.length, f (L.get i) = (L.map f).sum := by
  rw [← List.sum_ofFn]
  conv_rhs => rw [← List.ofFn_get L]
  rw [List.map_ofFn]
  rfl

lemma norm_list_sum_map_le (L : List ℕ) (f : ℕ → ℂ) :
    ‖(L.map f).sum‖ ≤ (L.map fun c => ‖f c‖).sum := by
  induction L with
  | nil => simp
  | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (norm_add_le _ _).trans (by gcongr)

lemma list_sum_map_sub (L : List ℕ) (f g : ℕ → ℂ) :
    (L.map f).sum - (L.map g).sum = (L.map fun c => f c - g c).sum := by
  induction L with
  | nil => simp
  | cons c cs ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring

lemma re_mul_list_sum (a : ℂ) (L : List ℕ) (f : ℕ → ℂ) :
    (a * (L.map f).sum).re = (L.map fun c => (a * f c).re).sum := by
  induction L with
  | nil => simp
  | cons c cs ih => simp only [List.map_cons, List.sum_cons, mul_add, Complex.add_re, ih]

/-- The multipliers given by a list, indexed by position. -/
noncomputable def ofList (L : List ℕ) : Fin L.length → ℕ := fun i => L.get i

lemma groupAvg_ofList (L : List ℕ) (a : ℝ) :
    groupAvg (ofList L) a = (L.length : ℂ)⁻¹ * (L.map fun c : ℕ => e (c * a)).sum := by
  unfold groupAvg ofList
  rw [sum_fin_get (fun c : ℕ => e (c * a)) L]

lemma norm_groupAvg_neg (L : List ℕ) (a : ℝ) :
    ‖groupAvg (ofList L) (-a)‖ = ‖groupAvg (ofList L) a‖ := by
  rw [groupAvg_ofList, groupAvg_ofList]
  have : (L.map fun c : ℕ => e (c * -a)).sum =
      (starRingEnd ℂ) (L.map fun c : ℕ => e (c * a)).sum := by
    rw [map_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c _
    simp only [Function.comp_apply, ← e_neg]
    congr 1; ring
  rw [this, norm_mul, norm_mul, Complex.norm_conj]

/-! ### Grid, potential, greedy search -/

variable (D N M : ℕ) (δ t : ℝ)

/-- The grid of base angles: indices `j` with `δ/2 ≤ j/M ≤ 1/2`. -/
noncomputable def grid : Finset ℕ :=
  (range (M + 1)).filter fun j => δ / 2 ≤ (j : ℝ) / M ∧ (j : ℝ) / M ≤ 1 / 2

/-- The reach of hand `c` for the check (grid angle `j/M`, direction `u`):
`reach j u c = Re (e(-u/D) · e(c · j/M))`. -/
noncomputable def reach (j u c : ℕ) : ℝ := (dir D u * e (c * ((j : ℝ) / M))).re

/-- The potential: the sum over all checks of the danger `exp (t · running total)`. -/
noncomputable def Φ (cs : List ℕ) : ℝ :=
  ∑ j ∈ grid M δ, ∑ u ∈ range D, Real.exp (t * (cs.map (reach D M j u)).sum)

open Classical in
/-- One greedy step: the least minimiser of the potential among `c < N`. -/
noncomputable def greedyStep (cs : List ℕ) : ℕ :=
  if h : ∃ c, c < N ∧ ∀ c' < N, Φ D M δ t (c :: cs) ≤ Φ D M δ t (c' :: cs) then Nat.find h else 0

/-- The greedy multipliers (newest choice first). -/
noncomputable def greedyList : ℕ → List ℕ
  | 0 => []
  | i + 1 => greedyStep D N M δ t (greedyList i) :: greedyList i

lemma greedyList_length (s : ℕ) : (greedyList D N M δ t s).length = s := by
  induction s with
  | zero => rfl
  | succ i ih => simp [greedyList, ih]

lemma greedyStep_spec (hN : 0 < N) (cs : List ℕ) :
    greedyStep D N M δ t cs < N ∧
      ∀ c' < N, Φ D M δ t (greedyStep D N M δ t cs :: cs) ≤ Φ D M δ t (c' :: cs) := by
  have hex : ∃ c, c < N ∧ ∀ c' < N, Φ D M δ t (c :: cs) ≤ Φ D M δ t (c' :: cs) := by
    obtain ⟨c, hc, hmin⟩ := (range N).exists_min_image (fun c => Φ D M δ t (c :: cs))
      (nonempty_range_iff.mpr hN.ne')
    exact ⟨c, mem_range.mp hc, fun c' hc' => hmin c' (mem_range.mpr hc')⟩
  unfold greedyStep
  split_ifs
  exact Nat.find_spec hex

lemma greedyList_lt (hN : 0 < N) (s : ℕ) : ∀ c ∈ greedyList D N M δ t s, c < N := by
  induction s with
  | zero => simp [greedyList]
  | succ i ih =>
      intro c hc
      simp only [greedyList, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact (greedyStep_spec D N M δ t hN _).1
      · exact ih c hc

lemma reach_mem (j u c : ℕ) : -1 ≤ reach D M j u c ∧ reach D M j u c ≤ 1 := by
  have h := Complex.abs_re_le_norm (dir D u * e (c * ((j : ℝ) / M)))
  rw [norm_mul, dir, norm_e, norm_e, one_mul] at h
  exact abs_le.mp h

/-- Over the pool `c < N`, the average reach for every check is at most `1/(Nδ)`. -/
lemma abs_mean_reach_le (hN : 0 < N) (hδ : 0 < δ) {j : ℕ} (hj : j ∈ grid M δ) (u : ℕ) :
    |(N : ℝ)⁻¹ * ∑ c ∈ range N, reach D M j u c| ≤ 1 / (N * δ) := by
  have hj' := (mem_filter.mp hj).2
  have hγ0 : 0 < (j : ℝ) / M := by linarith [hj'.1]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : ∑ c ∈ range N, reach D M j u c =
      (dir D u * ∑ c ∈ range N, e (c * ((j : ℝ) / M))).re := by
    rw [mul_sum, Complex.re_sum]; rfl
  rw [hsum, abs_mul, abs_inv, Nat.abs_cast]
  calc (N : ℝ)⁻¹ * |(dir D u * ∑ c ∈ range N, e (c * ((j : ℝ) / M))).re|
      ≤ (N : ℝ)⁻¹ * (1 / (2 * ((j : ℝ) / M))) := by
        gcongr
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, dir, norm_e, one_mul]
        exact norm_sum_e_le N hγ0 hj'.2
    _ ≤ (N : ℝ)⁻¹ * (1 / δ) := by
        gcongr
        linarith [hj'.1]
    _ = 1 / (N * δ) := by field_simp

/-- One greedy step multiplies the potential by at most `exp (t²/2 + sinh t /(Nδ))`. -/
lemma Φ_step (hN : 0 < N) (hδ : 0 < δ) (ht : 0 ≤ t) (cs : List ℕ) :
    Φ D M δ t (greedyStep D N M δ t cs :: cs) ≤
      Φ D M δ t cs * Real.exp (t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set E := t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t
  have hmin : Φ D M δ t (greedyStep D N M δ t cs :: cs) ≤
      (N : ℝ)⁻¹ * ∑ c ∈ range N, Φ D M δ t (c :: cs) := by
    rw [le_inv_mul_iff₀ hNR]
    have := (greedyStep_spec D N M δ t hN cs).2
    calc (N : ℝ) * Φ D M δ t (greedyStep D N M δ t cs :: cs)
        = ∑ _c ∈ range N, Φ D M δ t (greedyStep D N M δ t cs :: cs) := by
          rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ ∑ c ∈ range N, Φ D M δ t (c :: cs) :=
          sum_le_sum fun c hc => this c (mem_range.mp hc)
  have hexp : ∀ c, Φ D M δ t (c :: cs) = ∑ j ∈ grid M δ, ∑ u ∈ range D,
      Real.exp (t * (cs.map (reach D M j u)).sum) * Real.exp (t * reach D M j u c) := by
    intro c
    unfold Φ
    refine sum_congr rfl fun j _ => sum_congr rfl fun u _ => ?_
    rw [← Real.exp_add]
    congr 1
    simp only [List.map_cons, List.sum_cons]
    ring
  have havg : (N : ℝ)⁻¹ * ∑ c ∈ range N, Φ D M δ t (c :: cs) ≤ Φ D M δ t cs * Real.exp E := by
    simp_rw [hexp]
    rw [sum_comm, mul_sum]
    unfold Φ
    rw [sum_mul]
    refine sum_le_sum fun j hj => ?_
    rw [sum_comm, mul_sum, sum_mul]
    refine sum_le_sum fun u _ => ?_
    rw [← mul_sum, ← mul_assoc, mul_comm (N : ℝ)⁻¹, mul_assoc]
    gcongr
    exact avg_exp_le hN (reach D M j u) (reach_mem D M j u) ht
      (abs_mean_reach_le D N M δ hN hδ hj u)
  exact hmin.trans havg

lemma Φ_nil : Φ D M δ t [] = D * (grid M δ).card := by
  simp [Φ, mul_comm]

lemma Φ_greedy_le (hN : 0 < N) (hδ : 0 < δ) (ht : 0 ≤ t) (s : ℕ) :
    Φ D M δ t (greedyList D N M δ t s) ≤
      D * (grid M δ).card * Real.exp (s * (t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t)) := by
  induction s with
  | zero => simp [greedyList, Φ_nil]
  | succ i ih =>
      calc Φ D M δ t (greedyList D N M δ t (i + 1))
          ≤ Φ D M δ t (greedyList D N M δ t i) *
              Real.exp (t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t) := Φ_step D N M δ t hN hδ ht _
        _ ≤ D * (grid M δ).card * Real.exp (i * (t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t)) *
              Real.exp (t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t) := by gcongr
        _ = _ := by rw [mul_assoc, ← Real.exp_add]; push_cast; ring_nf

/-- On the grid, every check's running total is small. -/
lemma total_le_on_grid (hD : 0 < D) (hN : 0 < N) (hδ : 0 < δ) (ht : 0 < t) (s : ℕ)
    {j : ℕ} (hj : j ∈ grid M δ) {u : ℕ} (hu : u < D) :
    ((greedyList D N M δ t s).map (reach D M j u)).sum ≤
      (Real.log (D * (M + 1)) + s * (t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t)) / t := by
  set L := greedyList D N M δ t s
  set E := t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t
  have hsingle : Real.exp (t * (L.map (reach D M j u)).sum) ≤ Φ D M δ t L := by
    unfold Φ
    calc Real.exp (t * (L.map (reach D M j u)).sum)
        ≤ ∑ u' ∈ range D, Real.exp (t * (L.map (reach D M j u')).sum) :=
          single_le_sum (f := fun u' => Real.exp (t * (L.map (reach D M j u')).sum))
            (fun _ _ => (Real.exp_pos _).le) (mem_range.mpr hu)
      _ ≤ ∑ j' ∈ grid M δ, ∑ u' ∈ range D, Real.exp (t * (L.map (reach D M j' u')).sum) :=
          single_le_sum
            (f := fun j' => ∑ u' ∈ range D, Real.exp (t * (L.map (reach D M j' u')).sum))
            (fun _ _ => sum_nonneg fun _ _ => (Real.exp_pos _).le) hj
  have hcard : ((grid M δ).card : ℝ) ≤ M + 1 := by
    have := card_filter_le (range (M + 1)) fun j => δ / 2 ≤ (j : ℝ) / M ∧ (j : ℝ) / M ≤ 1 / 2
    rw [card_range] at this
    exact_mod_cast this
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hbound := (hsingle.trans (Φ_greedy_le D N M δ t hN hδ ht.le s)).trans
    (by gcongr : (D : ℝ) * ((grid M δ).card : ℝ) * Real.exp (s * E) ≤
      D * (M + 1) * Real.exp (s * E))
  have hlog := Real.log_le_log (Real.exp_pos _) hbound
  rw [Real.log_exp, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at hlog
  rw [le_div_iff₀ ht]
  linarith

/-- **Lemma 3** (greedy multipliers): the group average is small at every base angle
`δ ≤ |a| ≤ 1/2`. -/
theorem greedy_mult_bound (hD : 3 ≤ D) (hN : 0 < N) (hM : 0 < M) (hδ : 0 < δ)
    (hMδ : 2 ≤ M * δ) (ht : 0 < t) (s : ℕ) (hs : 0 < s) (a : ℝ) (ha1 : δ ≤ |a|)
    (ha2 : |a| ≤ 1 / 2) :
    ‖groupAvg (ofList (greedyList D N M δ t s)) a‖ ≤
      (Real.log (D * (M + 1)) + s * (t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t)) / (t * s) /
        Real.cos (Real.pi / D) + 2 * Real.pi * N / M := by
  set L := greedyList D N M δ t s with hL
  set A := (Real.log (D * (M + 1)) + s * (t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t)) / (t * s)
  have hlen : L.length = s := greedyList_length D N M δ t s
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hD0 : 0 < D := by omega
  have hcos : 0 < Real.cos (Real.pi / D) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have hDR' : (0 : ℝ) < D := by exact_mod_cast hD0
      have : 0 < Real.pi / D := div_pos Real.pi_pos hDR'
      linarith [Real.pi_pos]
    · rw [div_lt_iff₀ (by exact_mod_cast hD0)]
      have : (3 : ℝ) ≤ D := by exact_mod_cast hD
      nlinarith [Real.pi_pos]
  -- reduce to a ≥ 0
  wlog ha0 : 0 ≤ a generalizing a
  · have h := this (-a) (by rwa [abs_neg]) (by rwa [abs_neg]) (by linarith)
    rwa [norm_groupAvg_neg] at h
  rw [abs_of_nonneg ha0] at ha1 ha2
  -- nearest grid point below a
  set j := ⌊a * M⌋₊ with hj
  have hjle : (j : ℝ) ≤ a * M := Nat.floor_le (by positivity)
  have hjlt : a * M < j + 1 := Nat.lt_floor_add_one _
  have hγ1 : (j : ℝ) / M ≤ 1 / 2 := by rw [div_le_iff₀ hMR]; nlinarith
  have hγ0 : δ / 2 ≤ (j : ℝ) / M := by
    rw [le_div_iff₀ hMR]; nlinarith
  have hjgrid : j ∈ grid M δ := by
    refine mem_filter.mpr ⟨mem_range.mpr ?_, hγ0, hγ1⟩
    have : (j : ℝ) < M + 1 := by nlinarith
    exact_mod_cast this
  have hdist : |a - (j : ℝ) / M| ≤ 1 / M := by
    have hj1 : (j : ℝ) / M ≤ a := by rw [div_le_iff₀ hMR]; linarith
    have hj2 : a < (j : ℝ) / M + 1 / M := by rw [← add_div, lt_div_iff₀ hMR]; linarith
    have hM1 : 0 < 1 / (M : ℝ) := by positivity
    rw [abs_le]
    constructor <;> linarith
  -- on the grid: every reach is at most A, hence the length is at most A / cos(π/D)
  have hrot : ∀ u < D, (dir D u * groupAvg (ofList L) ((j : ℝ) / M)).re ≤ A := by
    intro u hu
    rw [groupAvg_ofList, hlen, mul_left_comm,
      show ((s : ℂ)⁻¹) = (((s : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
      re_mul_list_sum]
    have h := total_le_on_grid D N M δ t hD0 hN hδ ht s hjgrid hu
    unfold reach at h
    rw [← hL] at h
    rw [inv_mul_le_iff₀ hsR, show (s : ℝ) * A =
      (Real.log (D * (M + 1)) + s * (t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t)) / t by
        simp only [A]; field_simp]
    exact h
  have hnorm_grid : ‖groupAvg (ofList L) ((j : ℝ) / M)‖ ≤ A / Real.cos (Real.pi / D) := by
    obtain ⟨u, hu, hge⟩ := exists_dir_ge (groupAvg (ofList L) ((j : ℝ) / M)) hD0
    rw [le_div_iff₀ hcos]
    exact hge.trans (hrot u hu)
  -- Lipschitz step
  have hlip : ‖groupAvg (ofList L) a - groupAvg (ofList L) ((j : ℝ) / M)‖ ≤
      2 * Real.pi * N / M := by
    rw [groupAvg_ofList, groupAvg_ofList, ← mul_sub, list_sum_map_sub, hlen, norm_mul,
      norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hsR]
    have hterm : ∀ c ∈ L, ‖e (c * a) - e (c * ((j : ℝ) / M))‖ ≤ 2 * Real.pi * N / M := by
      intro c hc
      have hcN : (c : ℝ) ≤ N := by exact_mod_cast (greedyList_lt D N M δ t hN s c hc).le
      calc ‖e (c * a) - e (c * ((j : ℝ) / M))‖ ≤ 2 * Real.pi * |c * a - c * ((j : ℝ) / M)| :=
            norm_e_sub_e_le _ _
        _ = 2 * Real.pi * c * |a - (j : ℝ) / M| := by
            rw [← mul_sub, abs_mul, Nat.abs_cast]; ring
        _ ≤ 2 * Real.pi * N * (1 / M) := by gcongr
        _ = 2 * Real.pi * N / M := by ring
    calc ‖(L.map fun c : ℕ => e (c * a) - e (c * ((j : ℝ) / M))).sum‖
        ≤ (L.map fun c : ℕ => ‖e (c * a) - e (c * ((j : ℝ) / M))‖).sum :=
          norm_list_sum_map_le L _
      _ ≤ (L.map fun _ => 2 * Real.pi * N / M).sum := List.sum_le_sum fun c hc => hterm c hc
      _ = s * (2 * Real.pi * N / M) := by
          rw [List.map_const', List.sum_replicate, hlen, nsmul_eq_mul]
  calc ‖groupAvg (ofList L) a‖
      ≤ ‖groupAvg (ofList L) ((j : ℝ) / M)‖ +
          ‖groupAvg (ofList L) a - groupAvg (ofList L) ((j : ℝ) / M)‖ := by
        have := norm_add_le (groupAvg (ofList L) ((j : ℝ) / M))
          (groupAvg (ofList L) a - groupAvg (ofList L) ((j : ℝ) / M))
        rwa [add_sub_cancel] at this
    _ ≤ A / Real.cos (Real.pi / D) + 2 * Real.pi * N / M := add_le_add hnorm_grid hlip

end SmallBias
