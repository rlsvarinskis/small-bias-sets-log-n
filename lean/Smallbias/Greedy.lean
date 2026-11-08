import Smallbias.Core
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-!
# The inner set: a deterministic greedy search (Lemma 3)

`greedyList N M δ t s` picks `c₁, …, c_s ∈ [0, N)` one at a time, each minimising the potential
`Φ(cs) = ∑_{k ∈ grid} ∑_{d < 4} exp (t · ∑_{c ∈ cs} dir_d (e (c · k/M)))` (least index on ties).
`greedy_inner_bound`: the resulting inner set satisfies, for all `δ ≤ |β| ≤ 1/2`,
`‖innerSum C β‖ ≤ √2 · (log (4(M+1)) + s (t²/2 + sinh t /(Nδ))) / (t s) + 2πN/M`.
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

/-! ### Lists as inner sets -/

lemma sum_fin_get {β : Type*} [AddCommMonoid β] (f : ℕ → β) (L : List ℕ) :
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

/-- The inner set given by a list. -/
noncomputable def listInner (L : List ℕ) : Fin L.length → ℕ := fun i => L.get i

lemma innerSum_listInner (L : List ℕ) (β : ℝ) :
    innerSum (listInner L) β = (L.length : ℂ)⁻¹ * (L.map fun c : ℕ => e (c * β)).sum := by
  unfold innerSum listInner
  rw [sum_fin_get (fun c : ℕ => e (c * β)) L]

lemma norm_innerSum_neg (L : List ℕ) (β : ℝ) :
    ‖innerSum (listInner L) (-β)‖ = ‖innerSum (listInner L) β‖ := by
  rw [innerSum_listInner, innerSum_listInner]
  have : (L.map fun c : ℕ => e (c * -β)).sum = (starRingEnd ℂ) (L.map fun c : ℕ => e (c * β)).sum := by
    rw [map_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c _
    simp only [Function.comp_apply, ← e_neg]
    congr 1; ring
  rw [this, norm_mul, norm_mul, Complex.norm_conj]

/-! ### Directions, grid, potential -/

/-- The four directions `Re, -Re, Im, -Im`. -/
def dir : Fin 4 → ℂ → ℝ
  | 0, z => z.re
  | 1, z => -z.re
  | 2, z => z.im
  | 3, z => -z.im

lemma abs_dir_le (d : Fin 4) (z : ℂ) : |dir d z| ≤ ‖z‖ := by
  fin_cases d <;> simp [dir, Complex.abs_re_le_norm, Complex.abs_im_le_norm]

lemma dir_sum (d : Fin 4) (S : Finset ℕ) (f : ℕ → ℂ) :
    dir d (∑ c ∈ S, f c) = ∑ c ∈ S, dir d (f c) := by
  fin_cases d <;> simp [dir, Complex.re_sum, Complex.im_sum]

lemma dir_list_sum (d : Fin 4) (L : List ℕ) (f : ℕ → ℂ) :
    dir d (L.map f).sum = (L.map fun c => dir d (f c)).sum := by
  induction L with
  | nil => fin_cases d <;> simp [dir]
  | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      fin_cases d <;> simp [dir] <;> ring

lemma dir_real_mul (d : Fin 4) (r : ℝ) (z : ℂ) : dir d ((r : ℂ) * z) = r * dir d z := by
  fin_cases d <;> simp [dir]

variable (N M : ℕ) (δ t : ℝ)

/-- Grid indices `k` with `δ/2 ≤ k/M ≤ 1/2`. -/
noncomputable def grid : Finset ℕ :=
  (range (M + 1)).filter fun k => δ / 2 ≤ (k : ℝ) / M ∧ (k : ℝ) / M ≤ 1 / 2

/-- `X k d c = dir_d (e (c · k/M))`. -/
noncomputable def X (k : ℕ) (d : Fin 4) (c : ℕ) : ℝ := dir d (e (c * ((k : ℝ) / M)))

/-- The potential of a partial choice `cs`. -/
noncomputable def Φ (cs : List ℕ) : ℝ :=
  ∑ k ∈ grid M δ, ∑ d : Fin 4, Real.exp (t * (cs.map (X M k d)).sum)

open Classical in
/-- One greedy step: the least minimiser of the potential among `c < N`. -/
noncomputable def greedyStep (cs : List ℕ) : ℕ :=
  if h : ∃ c, c < N ∧ ∀ c' < N, Φ M δ t (c :: cs) ≤ Φ M δ t (c' :: cs) then Nat.find h else 0

/-- The greedy inner set (newest choice first). -/
noncomputable def greedyList : ℕ → List ℕ
  | 0 => []
  | i + 1 => greedyStep N M δ t (greedyList i) :: greedyList i

lemma greedyList_length (s : ℕ) : (greedyList N M δ t s).length = s := by
  induction s with
  | zero => rfl
  | succ i ih => simp [greedyList, ih]

lemma greedyStep_spec (hN : 0 < N) (cs : List ℕ) :
    greedyStep N M δ t cs < N ∧
      ∀ c' < N, Φ M δ t (greedyStep N M δ t cs :: cs) ≤ Φ M δ t (c' :: cs) := by
  have hex : ∃ c, c < N ∧ ∀ c' < N, Φ M δ t (c :: cs) ≤ Φ M δ t (c' :: cs) := by
    obtain ⟨c, hc, hmin⟩ := (range N).exists_min_image (fun c => Φ M δ t (c :: cs))
      (nonempty_range_iff.mpr hN.ne')
    exact ⟨c, mem_range.mp hc, fun c' hc' => hmin c' (mem_range.mpr hc')⟩
  unfold greedyStep
  split_ifs
  exact Nat.find_spec hex

lemma greedyList_lt (hN : 0 < N) (s : ℕ) : ∀ c ∈ greedyList N M δ t s, c < N := by
  induction s with
  | zero => simp [greedyList]
  | succ i ih =>
      intro c hc
      simp only [greedyList, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact (greedyStep_spec N M δ t hN _).1
      · exact ih c hc

lemma X_mem (k : ℕ) (d : Fin 4) (c : ℕ) : -1 ≤ X M k d c ∧ X M k d c ≤ 1 := by
  have h := abs_dir_le d (e (c * ((k : ℝ) / M)))
  rw [norm_e] at h
  exact abs_le.mp h

/-- Mean bound for every grid direction. -/
lemma abs_mean_X_le (hN : 0 < N) (hδ : 0 < δ) {k : ℕ} (hk : k ∈ grid M δ)
    (d : Fin 4) : |(N : ℝ)⁻¹ * ∑ c ∈ range N, X M k d c| ≤ 1 / (N * δ) := by
  have hk' := (mem_filter.mp hk).2
  have hγ0 : 0 < (k : ℝ) / M := by linarith [hk'.1]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  unfold X
  rw [← dir_sum, abs_mul, abs_inv, Nat.abs_cast]
  calc (N : ℝ)⁻¹ * |dir d (∑ c ∈ range N, e (c * ((k : ℝ) / M)))|
      ≤ (N : ℝ)⁻¹ * (1 / (2 * ((k : ℝ) / M))) := by
        gcongr
        exact (abs_dir_le _ _).trans (norm_sum_e_le N hγ0 hk'.2)
    _ ≤ (N : ℝ)⁻¹ * (1 / δ) := by
        gcongr
        linarith [hk'.1]
    _ = 1 / (N * δ) := by field_simp

/-- One greedy step multiplies the potential by at most `exp D`. -/
lemma Φ_step (hN : 0 < N) (hδ : 0 < δ) (ht : 0 ≤ t) (cs : List ℕ) :
    Φ M δ t (greedyStep N M δ t cs :: cs) ≤
      Φ M δ t cs * Real.exp (t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set D := t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t
  -- minimum ≤ average
  have hmin : Φ M δ t (greedyStep N M δ t cs :: cs) ≤
      (N : ℝ)⁻¹ * ∑ c ∈ range N, Φ M δ t (c :: cs) := by
    rw [le_inv_mul_iff₀ hNR]
    have := (greedyStep_spec N M δ t hN cs).2
    calc (N : ℝ) * Φ M δ t (greedyStep N M δ t cs :: cs)
        = ∑ _c ∈ range N, Φ M δ t (greedyStep N M δ t cs :: cs) := by
          rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ ∑ c ∈ range N, Φ M δ t (c :: cs) :=
          sum_le_sum fun c hc => this c (mem_range.mp hc)
  -- expand the average
  have hexp : ∀ c, Φ M δ t (c :: cs) = ∑ k ∈ grid M δ, ∑ d : Fin 4,
      Real.exp (t * (cs.map (X M k d)).sum) * Real.exp (t * X M k d c) := by
    intro c
    unfold Φ
    refine sum_congr rfl fun k _ => sum_congr rfl fun d _ => ?_
    rw [← Real.exp_add]
    congr 1
    simp only [List.map_cons, List.sum_cons]
    ring
  have havg : (N : ℝ)⁻¹ * ∑ c ∈ range N, Φ M δ t (c :: cs) ≤ Φ M δ t cs * Real.exp D := by
    simp_rw [hexp]
    rw [sum_comm, mul_sum]
    unfold Φ
    rw [sum_mul]
    refine sum_le_sum fun k hk => ?_
    rw [sum_comm, mul_sum, sum_mul]
    refine sum_le_sum fun d _ => ?_
    rw [← mul_sum, ← mul_assoc, mul_comm (N : ℝ)⁻¹, mul_assoc]
    gcongr
    exact avg_exp_le hN (X M k d) (X_mem M k d) ht (abs_mean_X_le N M δ hN hδ hk d)
  exact hmin.trans havg

lemma Φ_nil : Φ M δ t [] = 4 * (grid M δ).card := by
  simp [Φ, mul_comm]

lemma Φ_greedy_le (hN : 0 < N) (hδ : 0 < δ) (ht : 0 ≤ t) (s : ℕ) :
    Φ M δ t (greedyList N M δ t s) ≤
      4 * (grid M δ).card * Real.exp (s * (t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t)) := by
  induction s with
  | zero => simp [greedyList, Φ_nil]
  | succ i ih =>
      calc Φ M δ t (greedyList N M δ t (i + 1))
          ≤ Φ M δ t (greedyList N M δ t i) *
              Real.exp (t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t) := Φ_step N M δ t hN hδ ht _
        _ ≤ 4 * (grid M δ).card * Real.exp (i * (t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t)) *
              Real.exp (t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t) := by gcongr
        _ = _ := by rw [mul_assoc, ← Real.exp_add]; push_cast; ring_nf

/-- On the grid, every direction of the inner sum is small. -/
lemma dir_sum_le_on_grid (hN : 0 < N) (hδ : 0 < δ) (ht : 0 < t) (s : ℕ)
    {k : ℕ} (hk : k ∈ grid M δ) (d : Fin 4) :
    ((greedyList N M δ t s).map (X M k d)).sum ≤
      (Real.log (4 * (M + 1)) + s * (t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t)) / t := by
  set L := greedyList N M δ t s
  set D := t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t
  have hsingle : Real.exp (t * (L.map (X M k d)).sum) ≤ Φ M δ t L := by
    unfold Φ
    calc Real.exp (t * (L.map (X M k d)).sum)
        ≤ ∑ d' : Fin 4, Real.exp (t * (L.map (X M k d')).sum) :=
          single_le_sum (f := fun d' => Real.exp (t * (L.map (X M k d')).sum))
            (fun _ _ => (Real.exp_pos _).le) (mem_univ d)
      _ ≤ ∑ k' ∈ grid M δ, ∑ d' : Fin 4, Real.exp (t * (L.map (X M k' d')).sum) :=
          single_le_sum (f := fun k' => ∑ d' : Fin 4, Real.exp (t * (L.map (X M k' d')).sum))
            (fun _ _ => sum_nonneg fun _ _ => (Real.exp_pos _).le) hk
  have hcard : ((grid M δ).card : ℝ) ≤ M + 1 := by
    have := card_filter_le (range (M + 1)) fun k => δ / 2 ≤ (k : ℝ) / M ∧ (k : ℝ) / M ≤ 1 / 2
    rw [card_range] at this
    exact_mod_cast this
  have hbound := (hsingle.trans (Φ_greedy_le N M δ t hN hδ ht.le s)).trans
    (by gcongr : 4 * ((grid M δ).card : ℝ) * Real.exp (s * D) ≤ 4 * (M + 1) * Real.exp (s * D))
  have hlog := Real.log_le_log (Real.exp_pos _) hbound
  rw [Real.log_exp, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at hlog
  rw [le_div_iff₀ ht]
  linarith

/-- **Lemma 3** (the greedy inner set is balanced on `δ ≤ |β| ≤ 1/2`). -/
theorem greedy_inner_bound (hN : 0 < N) (hM : 0 < M) (hδ : 0 < δ) (hMδ : 2 ≤ M * δ) (ht : 0 < t)
    (s : ℕ) (hs : 0 < s) (β : ℝ) (hβ1 : δ ≤ |β|) (hβ2 : |β| ≤ 1 / 2) :
    ‖innerSum (listInner (greedyList N M δ t s)) β‖ ≤
      √2 * ((Real.log (4 * (M + 1)) + s * (t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t)) / (t * s)) +
        2 * Real.pi * N / M := by
  set L := greedyList N M δ t s with hL
  set A := (Real.log (4 * (M + 1)) + s * (t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t)) / (t * s)
  have hlen : L.length = s := greedyList_length N M δ t s
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  -- reduce to β ≥ 0
  wlog hβ0 : 0 ≤ β generalizing β
  · have h := this (-β) (by rwa [abs_neg]) (by rwa [abs_neg]) (by linarith)
    rwa [norm_innerSum_neg] at h
  rw [abs_of_nonneg hβ0] at hβ1 hβ2
  -- nearest grid point below β
  set k := ⌊β * M⌋₊ with hk
  have hkle : (k : ℝ) ≤ β * M := Nat.floor_le (by positivity)
  have hklt : β * M < k + 1 := Nat.lt_floor_add_one _
  have hγ1 : (k : ℝ) / M ≤ 1 / 2 := by rw [div_le_iff₀ hMR]; nlinarith
  have hγ0 : δ / 2 ≤ (k : ℝ) / M := by
    rw [le_div_iff₀ hMR]; nlinarith
  have hkgrid : k ∈ grid M δ := by
    refine mem_filter.mpr ⟨mem_range.mpr ?_, hγ0, hγ1⟩
    have : (k : ℝ) < M + 1 := by nlinarith
    exact_mod_cast this
  have hdist : |β - (k : ℝ) / M| ≤ 1 / M := by
    have hk1 : (k : ℝ) / M ≤ β := by rw [div_le_iff₀ hMR]; linarith
    have hk2 : β < (k : ℝ) / M + 1 / M := by rw [← add_div, lt_div_iff₀ hMR]; linarith
    have hM1 : 0 < 1 / (M : ℝ) := by positivity
    rw [abs_le]
    constructor <;> linarith
  -- grid bound: |Re|, |Im| ≤ A
  have hgrid : ∀ d : Fin 4, dir d (innerSum (listInner L) ((k : ℝ) / M)) ≤ A := by
    intro d
    rw [innerSum_listInner, hlen,
      show ((s : ℂ)⁻¹) = (((s : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, dir_real_mul, dir_list_sum]
    have h := dir_sum_le_on_grid N M δ t hN hδ ht s hkgrid d
    unfold X at h
    rw [← hL] at h
    rw [inv_mul_le_iff₀ hsR, show (s : ℝ) * A =
      (Real.log (4 * (M + 1)) + s * (t ^ 2 / 2 + 1 / (N * δ) * Real.sinh t)) / t by
        simp only [A]; field_simp]
    exact h
  have hnorm_grid : ‖innerSum (listInner L) ((k : ℝ) / M)‖ ≤ √2 * A := by
    refine (Complex.norm_le_sqrt_two_mul_max _).trans ?_
    gcongr
    refine max_le (abs_le.mpr ⟨?_, ?_⟩) (abs_le.mpr ⟨?_, ?_⟩)
    · have := hgrid 1; simp only [dir] at this; linarith
    · exact hgrid 0
    · have := hgrid 3; simp only [dir] at this; linarith
    · exact hgrid 2
  -- Lipschitz step
  have hlip : ‖innerSum (listInner L) β - innerSum (listInner L) ((k : ℝ) / M)‖ ≤
      2 * Real.pi * N / M := by
    rw [innerSum_listInner, innerSum_listInner, ← mul_sub, list_sum_map_sub, hlen, norm_mul,
      norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hsR]
    have hterm : ∀ c ∈ L, ‖e (c * β) - e (c * ((k : ℝ) / M))‖ ≤ 2 * Real.pi * N / M := by
      intro c hc
      have hcN : (c : ℝ) ≤ N := by exact_mod_cast (greedyList_lt N M δ t hN s c hc).le
      calc ‖e (c * β) - e (c * ((k : ℝ) / M))‖ ≤ 2 * Real.pi * |c * β - c * ((k : ℝ) / M)| :=
            norm_e_sub_e_le _ _
        _ = 2 * Real.pi * c * |β - (k : ℝ) / M| := by
            rw [← mul_sub, abs_mul, Nat.abs_cast]; ring
        _ ≤ 2 * Real.pi * N * (1 / M) := by gcongr
        _ = 2 * Real.pi * N / M := by ring
    calc ‖(L.map fun c : ℕ => e (c * β) - e (c * ((k : ℝ) / M))).sum‖
        ≤ (L.map fun c : ℕ => ‖e (c * β) - e (c * ((k : ℝ) / M))‖).sum := by
          exact norm_list_sum_map_le L _
      _ ≤ (L.map fun _ => 2 * Real.pi * N / M).sum := List.sum_le_sum fun c hc => hterm c hc
      _ = s * (2 * Real.pi * N / M) := by
          rw [List.map_const', List.sum_replicate, hlen, nsmul_eq_mul]
  calc ‖innerSum (listInner L) β‖
      ≤ ‖innerSum (listInner L) ((k : ℝ) / M)‖ +
          ‖innerSum (listInner L) β - innerSum (listInner L) ((k : ℝ) / M)‖ := by
        have := norm_add_le (innerSum (listInner L) ((k : ℝ) / M))
          (innerSum (listInner L) β - innerSum (listInner L) ((k : ℝ) / M))
        rwa [add_sub_cancel] at this
    _ ≤ √2 * A + 2 * Real.pi * N / M := add_le_add hnorm_grid hlip

end SmallBias
