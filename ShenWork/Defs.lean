/-
  ShenWork/Defs.lean

  Core definitions for:
    Shen, "Existence, uniqueness, stability, and monotonicity of traveling waves
    for repulsion/attraction chemotaxis models with logistic type source"
    (arXiv:2605.04401)

  System (CM):
    u_t = u_xx − χ(uᵐ v_x)_x + u(1 − uᵅ),   x ∈ ℝ
    0   = v_xx − v + uᵞ,                        x ∈ ℝ
  where m, α, γ ≥ 1 and χ ∈ ℝ.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Order.Filter.Basic

open Filter Topology MeasureTheory

noncomputable section

/-! ## Parameters of the chemotaxis system -/

/-- Parameters for the parabolic-elliptic chemotaxis system (CM). -/
structure CMParams where
  m : ℝ
  α : ℝ
  γ : ℝ
  χ : ℝ
  hm : 1 ≤ m
  hα : 1 ≤ α
  hγ : 1 ≤ γ

/-! ## Function spaces -/

/-- A function is bounded: ∃ M, ∀ x, |f x| ≤ M. -/
def IsBddFun (f : ℝ → ℝ) : Prop := ∃ M : ℝ, ∀ x, |f x| ≤ M

/-- C^b_unif(ℝ): uniformly continuous and bounded functions ℝ → ℝ. -/
def IsCUnifBdd (f : ℝ → ℝ) : Prop := Continuous f ∧ IsBddFun f

/-! ## Classical solutions -/

/-- A pair (u, v) is a classical solution of (CM) on (0, T). -/
structure IsClassicalSolution (p : CMParams) (T : ℝ) (u v : ℝ → ℝ → ℝ) : Prop where
  hT : 0 < T
  u_smooth : ∀ t x, 0 < t → t < T →
    DifferentiableAt ℝ (u · x) t ∧ DifferentiableAt ℝ (u t) x
  v_smooth : ∀ t x, 0 < t → t < T → DifferentiableAt ℝ (v t) x
  pde_u : ∀ t x, 0 < t → t < T →
    deriv (u · x) t =
      iteratedDeriv 2 (u t) x
      - p.χ * deriv (fun y => (u t y) ^ p.m * deriv (v t) y) x
      + u t x * (1 - (u t x) ^ p.α)
  pde_v : ∀ t x, 0 < t → t < T →
    iteratedDeriv 2 (v t) x - v t x + (u t x) ^ p.γ = 0

def IsGlobalClassicalSolution (p : CMParams) (u v : ℝ → ℝ → ℝ) : Prop :=
  ∀ T > 0, IsClassicalSolution p T u v

theorem IsClassicalSolution.shift_space
    {p : CMParams} {T : ℝ} {u v : ℝ → ℝ → ℝ}
    (h : IsClassicalSolution p T u v) (a : ℝ) :
    IsClassicalSolution p T
      (fun t x => u t (x + a)) (fun t x => v t (x + a)) := by
  refine
    { hT := h.hT
      u_smooth := ?_
      v_smooth := ?_
      pde_u := ?_
      pde_v := ?_ }
  · intro t x ht0 htT
    exact
      ⟨(h.u_smooth t (x + a) ht0 htT).1,
        (h.u_smooth t (x + a) ht0 htT).2.comp x
          (differentiableAt_id.add (differentiableAt_const a))⟩
  · intro t x ht0 htT
    exact
      (h.v_smooth t (x + a) ht0 htT).comp x
        (differentiableAt_id.add (differentiableAt_const a))
  · intro t x ht0 htT
    have hU2 := congr_fun (iteratedDeriv_comp_add_const 2 (u t) a) x
    have hV1 : ∀ y,
        deriv (fun z => v t (z + a)) y = deriv (v t) (y + a) := by
      intro y
      exact deriv_comp_add_const (v t) a y
    have hChem :
        deriv
          (fun y => (u t (y + a)) ^ p.m *
            deriv (fun z => v t (z + a)) y) x =
        deriv (fun ξ => (u t ξ) ^ p.m * deriv (v t) ξ) (x + a) := by
      have hfun :
          (fun y => (u t (y + a)) ^ p.m *
            deriv (fun z => v t (z + a)) y) =
          (fun y => (u t (y + a)) ^ p.m * deriv (v t) (y + a)) := by
        ext y
        rw [hV1 y]
      rw [hfun]
      have := congr_fun
        (iteratedDeriv_comp_add_const 1
          (fun ξ => (u t ξ) ^ p.m * deriv (v t) ξ) a) x
      simpa [iteratedDeriv_one] using this
    rw [hU2, hChem]
    exact h.pde_u t (x + a) ht0 htT
  · intro t x ht0 htT
    have hV2 := congr_fun (iteratedDeriv_comp_add_const 2 (v t) a) x
    rw [hV2]
    exact h.pde_v t (x + a) ht0 htT

theorem IsGlobalClassicalSolution.shift_space
    {p : CMParams} {u v : ℝ → ℝ → ℝ}
    (h : IsGlobalClassicalSolution p u v) (a : ℝ) :
    IsGlobalClassicalSolution p
      (fun t x => u t (x + a)) (fun t x => v t (x + a)) := by
  intro T hT
  exact (h T hT).shift_space a

def IsPositiveClassicalSolution (p : CMParams) (T : ℝ) (u v : ℝ → ℝ → ℝ) : Prop :=
  IsClassicalSolution p T u v ∧ ∀ t x, 0 ≤ t → t < T → 0 < u t x

def IsBoundedGlobal (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ M : ℝ, ∀ t x, 0 ≤ t → |u t x| ≤ M

theorem IsPositiveClassicalSolution.shift_space
    {p : CMParams} {T : ℝ} {u v : ℝ → ℝ → ℝ}
    (h : IsPositiveClassicalSolution p T u v) (a : ℝ) :
    IsPositiveClassicalSolution p T
      (fun t x => u t (x + a)) (fun t x => v t (x + a)) := by
  exact ⟨h.1.shift_space a, fun t x ht0 htT => h.2 t (x + a) ht0 htT⟩

theorem IsBoundedGlobal.shift_space
    {u : ℝ → ℝ → ℝ} (h : IsBoundedGlobal u) (a : ℝ) :
    IsBoundedGlobal (fun t x => u t (x + a)) := by
  rcases h with ⟨M, hM⟩
  exact ⟨M, fun t x ht => hM t (x + a) ht⟩

/-! ## Traveling wave solutions -/

/-- A traveling wave solution of (CM) connecting (1,1) and (0,0) with speed c. -/
structure IsTravelingWave (p : CMParams) (c : ℝ) (U V : ℝ → ℝ) : Prop where
  hc : 0 < c
  U_pos : ∀ x, 0 < U x
  ode_U : ∀ x,
    iteratedDeriv 2 U x + c * deriv U x
    - p.χ * deriv (fun y => (U y) ^ p.m * deriv V y) x
    + U x * (1 - (U x) ^ p.α) = 0
  ode_V : ∀ x, iteratedDeriv 2 V x - V x + (U x) ^ p.γ = 0
  lim_neg_inf : Tendsto U atBot (𝓝 1) ∧ Tendsto V atBot (𝓝 1)
  lim_pos_inf : Tendsto U atTop (𝓝 0) ∧ Tendsto V atTop (𝓝 0)

def IsMonotoneTravelingWave (p : CMParams) (c : ℝ) (U V : ℝ → ℝ) : Prop :=
  IsTravelingWave p c U V ∧ (∀ x, deriv U x ≤ 0) ∧ (∀ x, deriv V x ≤ 0)

theorem IsTravelingWave.shift (p : CMParams) {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V) (a : ℝ) :
    IsTravelingWave p c (fun x => U (x + a)) (fun x => V (x + a)) := by
  refine
    { hc := hTW.hc
      U_pos := fun x => hTW.U_pos (x + a)
      ode_U := ?_
      ode_V := ?_
      lim_neg_inf := ?_
      lim_pos_inf := ?_ }
  · intro x
    have hU2 := congr_fun (iteratedDeriv_comp_add_const 2 U a) x
    have hU1 := deriv_comp_add_const U a x
    have hV1 : ∀ y,
        deriv (fun z => V (z + a)) y = deriv V (y + a) := by
      intro y
      exact deriv_comp_add_const V a y
    have hChem :
        deriv
          (fun y => (U (y + a)) ^ p.m *
            deriv (fun z => V (z + a)) y) x =
        deriv (fun ξ => (U ξ) ^ p.m * deriv V ξ) (x + a) := by
      have hfun :
          (fun y => (U (y + a)) ^ p.m *
            deriv (fun z => V (z + a)) y) =
          (fun y => (U (y + a)) ^ p.m * deriv V (y + a)) := by
        ext y
        rw [hV1 y]
      rw [hfun]
      have := congr_fun
        (iteratedDeriv_comp_add_const 1
          (fun ξ => (U ξ) ^ p.m * deriv V ξ) a) x
      simpa [iteratedDeriv_one] using this
    rw [hU2, hU1, hChem]
    exact hTW.ode_U (x + a)
  · intro x
    have hV2 := congr_fun (iteratedDeriv_comp_add_const 2 V a) x
    rw [hV2]
    exact hTW.ode_V (x + a)
  · exact
      ⟨hTW.lim_neg_inf.1.comp
          (tendsto_atBot_add_const_right atBot a tendsto_id),
        hTW.lim_neg_inf.2.comp
          (tendsto_atBot_add_const_right atBot a tendsto_id)⟩
  · exact
      ⟨hTW.lim_pos_inf.1.comp
          (tendsto_atTop_add_const_right atTop a tendsto_id),
        hTW.lim_pos_inf.2.comp
          (tendsto_atTop_add_const_right atTop a tendsto_id)⟩

theorem IsMonotoneTravelingWave.shift (p : CMParams) {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsMonotoneTravelingWave p c U V) (a : ℝ) :
    IsMonotoneTravelingWave p c (fun x => U (x + a)) (fun x => V (x + a)) := by
  refine ⟨hTW.1.shift p a, ?_, ?_⟩
  · intro x
    rw [deriv_comp_add_const]
    exact hTW.2.1 (x + a)
  · intro x
    rw [deriv_comp_add_const]
    exact hTW.2.2 (x + a)

lemma exp_bound_shift_right {k a : ℝ} (hk : 0 ≤ k) (ha : 0 ≤ a)
    {U : ℝ → ℝ} (hbound : ∀ x, U x < Real.exp (-k * x)) :
    ∀ x, U (x + a) < Real.exp (-k * x) := by
  intro x
  have hshift := hbound (x + a)
  have hle_exp : Real.exp (-k * (x + a)) ≤ Real.exp (-k * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hk ha]
  exact hshift.trans_le hle_exp

/-! ## Wave speed bounds -/

/-- c*_{χ,m,γ} from Theorem 1.1(1), eq (1.13). -/
def cStarLower (p : CMParams) : ℝ :=
  max (1 / p.m + p.m)
    (1 / Real.sqrt (p.m * p.γ * |p.χ| + p.γ ^ 2 * |p.χ| + p.γ ^ 2) +
     Real.sqrt (p.m * p.γ * |p.χ| + p.γ ^ 2 * |p.χ| + p.γ ^ 2))

/-- χ*(m, α, γ) from Theorem 1.1(2), eq (1.17). -/
def chiStar (p : CMParams) : ℝ :=
  min 1 ((2 * p.m + 2 * p.γ) / (p.m ^ 2 + p.m + 2 * p.γ))

/-- κ = (c − √(c² − 4)) / 2, the exponential decay rate. -/
def kappa (c : ℝ) : ℝ := (c - Real.sqrt (c ^ 2 - 4)) / 2

lemma cStarLower_ge_two (p : CMParams) :
    2 ≤ cStarLower p := by
  have hm_pos : 0 < p.m := lt_of_lt_of_le one_pos p.hm
  have htwo_le_m_inv_add_m : 2 ≤ 1 / p.m + p.m := by
    have hsq : 0 ≤ (p.m - 1) ^ 2 := sq_nonneg (p.m - 1)
    field_simp [ne_of_gt hm_pos]
    nlinarith
  exact le_trans htwo_le_m_inv_add_m (le_max_left _ _)

lemma kappa_pos_of_two_lt {c : ℝ} (hc : 2 < c) :
    0 < kappa c := by
  simp only [kappa]
  have hrad_pos : 0 < c ^ 2 - 4 := by nlinarith
  have hsqrt_lt : Real.sqrt (c ^ 2 - 4) < c := by
    have hsq : (Real.sqrt (c ^ 2 - 4)) ^ 2 = c ^ 2 - 4 :=
      Real.sq_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg (c ^ 2 - 4)]
  linarith

lemma cStarLower_pos (p : CMParams) :
    0 < cStarLower p :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (cStarLower_ge_two p)

lemma two_lt_of_cStarLower_lt {p : CMParams} {c : ℝ}
    (hc : cStarLower p < c) :
    2 < c :=
  lt_of_le_of_lt (cStarLower_ge_two p) hc

lemma kappa_lt_one_of_two_lt {c : ℝ} (hc : 2 < c) :
    kappa c < 1 := by
  simp only [kappa]
  have hsq_lt : (c - 2) ^ 2 < c ^ 2 - 4 := by nlinarith
  have hsqrt_gt : c - 2 < Real.sqrt (c ^ 2 - 4) :=
    Real.lt_sqrt_of_sq_lt hsq_lt
  linarith

lemma kappa_quadratic_eq_zero {c : ℝ} (hc : 2 ≤ c) :
    kappa c ^ 2 - c * kappa c + 1 = 0 := by
  unfold kappa
  have hrad_nonneg : 0 ≤ c ^ 2 - 4 := by nlinarith
  have hsq : (Real.sqrt (c ^ 2 - 4)) ^ 2 = c ^ 2 - 4 :=
    Real.sq_sqrt hrad_nonneg
  nlinarith

lemma kappa_add_inv_eq_of_two_lt {c : ℝ} (hc : 2 < c) :
    kappa c + (kappa c)⁻¹ = c := by
  have hk_pos : 0 < kappa c := kappa_pos_of_two_lt hc
  have hquad : kappa c ^ 2 - c * kappa c + 1 = 0 :=
    kappa_quadratic_eq_zero hc.le
  field_simp [ne_of_gt hk_pos]
  nlinarith

lemma inv_kappa_eq_of_two_lt {c : ℝ} (hc : 2 < c) :
    (kappa c)⁻¹ = c - kappa c := by
  have h := kappa_add_inv_eq_of_two_lt hc
  linarith

lemma two_lt_of_pos_lt_one_kappa_speed {κ c : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ < 1) (hc : c = κ + κ⁻¹) :
    2 < c := by
  rw [hc]
  have hκ_ne : κ ≠ 0 := ne_of_gt hκ0
  have hsq_pos : 0 < (κ - 1) ^ 2 := sq_pos_of_ne_zero (by linarith)
  have hidentity : κ + κ⁻¹ - 2 = (κ - 1) ^ 2 / κ := by
    field_simp [hκ_ne]
    ring
  have hpos : 0 < κ + κ⁻¹ - 2 := by
    rw [hidentity]
    exact div_pos hsq_pos hκ0
  linarith

lemma kappa_eq_of_pos_lt_one_kappa_speed {κ c : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ < 1) (hc : c = κ + κ⁻¹) :
    kappa c = κ := by
  have hκ_ne : κ ≠ 0 := ne_of_gt hκ0
  have hinv_gt : κ < κ⁻¹ := by
    have hinv_gt_one : 1 < κ⁻¹ := (one_lt_inv₀ hκ0).2 hκ1
    linarith
  have hsqrt :
      Real.sqrt ((κ + κ⁻¹) ^ 2 - 4) = κ⁻¹ - κ := by
    rw [← Real.sqrt_sq (sub_nonneg.mpr hinv_gt.le)]
    congr 1
    field_simp [hκ_ne]
    ring
  rw [kappa, hc, hsqrt]
  field_simp [hκ_ne]
  ring

lemma kappa_mem_Ioo_zero_one_of_two_lt {c : ℝ} (hc : 2 < c) :
    kappa c ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨kappa_pos_of_two_lt hc, kappa_lt_one_of_two_lt hc⟩

lemma kappa_pos_of_cStarLower_lt {p : CMParams} {c : ℝ}
    (hc : cStarLower p < c) :
    0 < kappa c :=
  kappa_pos_of_two_lt (two_lt_of_cStarLower_lt hc)

lemma kappa_lt_one_of_cStarLower_lt {p : CMParams} {c : ℝ}
    (hc : cStarLower p < c) :
    kappa c < 1 :=
  kappa_lt_one_of_two_lt (two_lt_of_cStarLower_lt hc)

lemma kappa_add_inv_eq_of_cStarLower_lt {p : CMParams} {c : ℝ}
    (hc : cStarLower p < c) :
    kappa c + (kappa c)⁻¹ = c :=
  kappa_add_inv_eq_of_two_lt (two_lt_of_cStarLower_lt hc)

lemma kappa_mul_c_eq {c : ℝ} (hc : 2 ≤ c) :
    kappa c * c = kappa c ^ 2 + 1 := by
  have hquad := kappa_quadratic_eq_zero hc
  nlinarith

lemma one_sub_kappa_sq_pos {c : ℝ} (hc : 2 < c) :
    0 < 1 - kappa c ^ 2 := by
  have hk := kappa_pos_of_two_lt hc
  have hk1 := kappa_lt_one_of_two_lt hc
  nlinarith [sq_nonneg (1 - kappa c), sq_abs (kappa c)]

lemma one_sub_kappa_sq_eq {c : ℝ} (hc : 2 ≤ c) :
    1 - kappa c ^ 2 = c * kappa c - 2 * kappa c ^ 2 := by
  have hquad := kappa_quadratic_eq_zero hc
  nlinarith

lemma kappa_nonneg_of_two_le {c : ℝ} (hc : 2 ≤ c) :
    0 ≤ kappa c := by
  rcases lt_or_eq_of_le hc with h | h
  · exact (kappa_pos_of_two_lt h).le
  · subst h; simp [kappa]; norm_num

lemma kappa_le_one_of_two_le {c : ℝ} (hc : 2 ≤ c) :
    kappa c ≤ 1 := by
  rcases lt_or_eq_of_le hc with h | h
  · exact (kappa_lt_one_of_two_lt h).le
  · subst h; simp [kappa]; norm_num

lemma sqrt_discriminant_eq {c : ℝ} (hc : 2 ≤ c) :
    Real.sqrt (c ^ 2 - 4) = (kappa c)⁻¹ - kappa c := by
  have hk_pos : 0 < kappa c := by
    rcases lt_or_eq_of_le hc with h | h
    · exact kappa_pos_of_two_lt h
    · subst h; simp [kappa]; norm_num
  have hquad := kappa_quadratic_eq_zero hc
  have hrad_nonneg : 0 ≤ c ^ 2 - 4 := by nlinarith
  have hk_le_one := kappa_le_one_of_two_le hc
  have hinv_sub_pos : 0 ≤ (kappa c)⁻¹ - kappa c := by
    rw [sub_nonneg]
    calc kappa c ≤ 1 := hk_le_one
      _ ≤ (kappa c)⁻¹ := one_le_inv_iff₀.mpr ⟨hk_pos, hk_le_one⟩
  rw [← Real.sqrt_sq hinv_sub_pos]
  congr 1
  field_simp [ne_of_gt hk_pos]
  nlinarith

lemma kappa_strictAntiOn :
    StrictAntiOn kappa (Set.Ioi 2) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hka := kappa_pos_of_two_lt ha
  have hkb := kappa_pos_of_two_lt (lt_trans ha hab)
  have hka1 := kappa_lt_one_of_two_lt ha
  have hkb1 := kappa_lt_one_of_two_lt (lt_trans ha hab)
  have hqa := kappa_quadratic_eq_zero ha.le
  have hqb := kappa_quadratic_eq_zero (le_of_lt (lt_trans ha hab))
  by_contra hle
  push_neg at hle
  rcases lt_or_eq_of_le hle with hlt | heq
  · have h1 : kappa a ^ 2 - a * kappa a + 1 = 0 := hqa
    have h2 : kappa b ^ 2 - b * kappa b + 1 = 0 := hqb
    have hab' : a < b := hab
    have hkab : kappa a < kappa b := hlt
    nlinarith [sq_nonneg (kappa b - kappa a),
      mul_pos (sub_pos.mpr hab') (sub_pos.mpr hkab)]
  · rw [heq] at hqa
    have h2 := hqb
    have hab' : a < b := hab
    nlinarith

lemma kappa_sq_lt_one {c : ℝ} (hc : 2 < c) :
    kappa c ^ 2 < 1 := by
  have hk1 := kappa_lt_one_of_two_lt hc
  have hk0 := kappa_pos_of_two_lt hc
  nlinarith [sq_abs (kappa c)]

lemma kappa_sq_le_one {c : ℝ} (hc : 2 ≤ c) :
    kappa c ^ 2 ≤ 1 := by
  rcases lt_or_eq_of_le hc with h | h
  · exact (kappa_sq_lt_one h).le
  · subst h; simp [kappa]; norm_num

lemma one_div_one_sub_kappa_sq_pos {c : ℝ} (hc : 2 < c) :
    0 < 1 / (1 - kappa c ^ 2) :=
  div_pos one_pos (one_sub_kappa_sq_pos hc)

lemma gamma_kappa_lt_one_of_gamma_le_one {c : ℝ} {γ : ℝ}
    (hc : 2 < c) (hγ : γ ≤ 1) :
    γ * kappa c < 1 := by
  calc γ * kappa c ≤ 1 * kappa c :=
        mul_le_mul_of_nonneg_right hγ (kappa_pos_of_two_lt hc).le
    _ = kappa c := one_mul _
    _ < 1 := kappa_lt_one_of_two_lt hc

lemma gamma_sq_kappa_sq_lt_one {c : ℝ} {γ : ℝ}
    (hc : 2 < c) (hγ : 0 < γ) (hγκ : γ * kappa c < 1) :
    γ ^ 2 * kappa c ^ 2 < 1 := by
  have hgk := mul_pos hγ (kappa_pos_of_two_lt hc)
  nlinarith [sq_nonneg (γ * kappa c - 1)]

lemma one_sub_gamma_sq_kappa_sq_pos {c : ℝ} {γ : ℝ}
    (hc : 2 < c) (hγ : 0 < γ) (hγκ : γ * kappa c < 1) :
    0 < 1 - γ ^ 2 * kappa c ^ 2 := by
  linarith [gamma_sq_kappa_sq_lt_one hc hγ hγκ]

lemma kappa_continuous : Continuous kappa := by
  unfold kappa
  exact ((continuous_id.sub
    (Real.continuous_sqrt.comp
      (continuous_id.pow 2 |>.sub continuous_const))).div_const 2)

lemma chiStar_pos (p : CMParams) :
    0 < chiStar p := by
  unfold chiStar
  apply lt_min
  · norm_num
  · apply div_pos
    · nlinarith [p.hm, p.hγ]
    · nlinarith [sq_nonneg p.m, p.hm, p.hγ]

lemma chiStar_le_one (p : CMParams) :
    chiStar p ≤ 1 := by
  unfold chiStar
  exact min_le_left _ _

lemma chiStar_le_ratio (p : CMParams) :
    chiStar p ≤ (2 * p.m + 2 * p.γ) / (p.m ^ 2 + p.m + 2 * p.γ) := by
  unfold chiStar
  exact min_le_right _ _

/-! ## The elliptic Green's function Ψ -/

/-- Ψ(x; u, l, μ) = (μ / (2√l)) ∫ e^{-√l |x-y|} u(y) dy -/
def Psi (u : ℝ → ℝ) (l mu : ℝ) (x : ℝ) : ℝ :=
  mu / (2 * Real.sqrt l) * ∫ y : ℝ, Real.exp (-Real.sqrt l * |x - y|) * u y

private lemma kernel_exp_neg_one_integrable (x : ℝ) :
    MeasureTheory.Integrable (fun y : ℝ => Real.exp (-1 * |x - y|)) := by
  let f : ℝ → ℝ := fun y => Real.exp (-1 * |x - y|)
  have hleft_eq : Set.EqOn (fun y : ℝ => Real.exp (-x) * Real.exp (1 * y)) f (Set.Iic x) := by
    intro y hy
    have hyx : y ≤ x := by simpa using hy
    simp only [f]; rw [abs_of_nonneg (sub_nonneg.mpr hyx), ← Real.exp_add]; congr 1; ring
  have hright_eq : Set.EqOn (fun y : ℝ => Real.exp x * Real.exp ((-1) * y)) f (Set.Ioi x) := by
    intro y hy
    have hxy : x < y := by simpa using hy
    simp only [f]; rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hxy)), ← Real.exp_add]; congr 1; ring
  have hleft : MeasureTheory.IntegrableOn f (Set.Iic x) := by
    have h1 : MeasureTheory.IntegrableOn (fun y => Real.exp (1 * y)) (Set.Iic x) :=
      integrableOn_exp_mul_Iic (by norm_num : (0:ℝ) < 1) x
    have h2 : MeasureTheory.IntegrableOn (fun y => Real.exp (-x) * Real.exp (1 * y)) (Set.Iic x) :=
      MeasureTheory.Integrable.const_mul h1 (Real.exp (-x))
    exact h2.congr_fun hleft_eq measurableSet_Iic
  have hright : MeasureTheory.IntegrableOn f (Set.Ioi x) := by
    have h1 : MeasureTheory.IntegrableOn (fun y => Real.exp ((-1) * y)) (Set.Ioi x) :=
      integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ) < 0) x
    have h2 : MeasureTheory.IntegrableOn (fun y => Real.exp x * Real.exp ((-1) * y)) (Set.Ioi x) :=
      MeasureTheory.Integrable.const_mul h1 (Real.exp x)
    exact h2.congr_fun hright_eq measurableSet_Ioi
  have hcover : Set.Iic x ∪ Set.Ioi x = (Set.univ : Set ℝ) := by
    ext y; by_cases hy : y ≤ x <;> simp [hy, lt_of_not_ge]
  rw [← MeasureTheory.integrableOn_univ, ← hcover]
  exact hleft.union hright

lemma kernel_exp_neg_mul_abs_integrable {a : ℝ} (ha : 0 < a) (x : ℝ) :
    MeasureTheory.Integrable (fun y : ℝ => Real.exp (-a * |x - y|)) := by
  let f : ℝ → ℝ := fun y => Real.exp (-a * |x - y|)
  have hleft_eq :
      Set.EqOn (fun y : ℝ => Real.exp (-a * x) * Real.exp (a * y))
        f (Set.Iic x) := by
    intro y hy
    have hyx : y ≤ x := by simpa using hy
    simp only [f]
    rw [abs_of_nonneg (sub_nonneg.mpr hyx), ← Real.exp_add]
    congr 1
    ring
  have hright_eq :
      Set.EqOn (fun y : ℝ => Real.exp (a * x) * Real.exp ((-a) * y))
        f (Set.Ioi x) := by
    intro y hy
    have hxy : x < y := by simpa using hy
    simp only [f]
    rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hxy)), ← Real.exp_add]
    congr 1
    ring
  have hleft : MeasureTheory.IntegrableOn f (Set.Iic x) := by
    have h1 :
        MeasureTheory.IntegrableOn
          (fun y : ℝ => Real.exp (a * y)) (Set.Iic x) :=
      integrableOn_exp_mul_Iic ha x
    have h2 :
        MeasureTheory.IntegrableOn
          (fun y : ℝ => Real.exp (-a * x) * Real.exp (a * y)) (Set.Iic x) :=
      MeasureTheory.Integrable.const_mul h1 (Real.exp (-a * x))
    exact h2.congr_fun hleft_eq measurableSet_Iic
  have hright : MeasureTheory.IntegrableOn f (Set.Ioi x) := by
    have h1 :
        MeasureTheory.IntegrableOn
          (fun y : ℝ => Real.exp ((-a) * y)) (Set.Ioi x) :=
      integrableOn_exp_mul_Ioi (by linarith : -a < (0 : ℝ)) x
    have h2 :
        MeasureTheory.IntegrableOn
          (fun y : ℝ => Real.exp (a * x) * Real.exp ((-a) * y)) (Set.Ioi x) :=
      MeasureTheory.Integrable.const_mul h1 (Real.exp (a * x))
    exact h2.congr_fun hright_eq measurableSet_Ioi
  have hcover : Set.Iic x ∪ Set.Ioi x = (Set.univ : Set ℝ) := by
    ext y
    by_cases hy : y ≤ x <;> simp [hy, lt_of_not_ge]
  rw [← MeasureTheory.integrableOn_univ, ← hcover]
  exact hleft.union hright

lemma integral_exp_neg_mul_abs_sub {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∫ y : ℝ, Real.exp (-a * |x - y|)) = 2 / a := by
  let f : ℝ → ℝ := fun y => Real.exp (-a * |x - y|)
  have hfi : MeasureTheory.Integrable f :=
    kernel_exp_neg_mul_abs_integrable ha x
  have hsplit := MeasureTheory.integral_add_compl (s := Set.Iic x) measurableSet_Iic hfi
  simp only [Set.compl_Iic] at hsplit
  have hleft_val :
      ∫ y in Set.Iic x, f y = 1 / a := by
    have hleft_eq :
        Set.EqOn (fun y : ℝ => Real.exp (-a * x) * Real.exp (a * y))
          f (Set.Iic x) := by
      intro y hy
      have hyx : y ≤ x := by simpa using hy
      simp only [f]
      rw [abs_of_nonneg (sub_nonneg.mpr hyx), ← Real.exp_add]
      congr 1
      ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Iic hleft_eq.symm]
    calc
      ∫ y in Set.Iic x, Real.exp (-a * x) * Real.exp (a * y)
          = Real.exp (-a * x) * ∫ y in Set.Iic x, Real.exp (a * y) := by
            change _ = Real.exp (-a * x) * ∫ y, _ ∂(MeasureTheory.volume.restrict _)
            exact MeasureTheory.integral_const_mul _ _
      _ = Real.exp (-a * x) * (Real.exp (a * x) / a) := by
            rw [integral_exp_mul_Iic ha x]
      _ = 1 / a := by
            field_simp [ne_of_gt ha]
            rw [← Real.exp_add]
            have hzero : -(a * x) + a * x = 0 := by ring
            rw [hzero, Real.exp_zero]
  have hright_val :
      ∫ y in Set.Ioi x, f y = 1 / a := by
    have hright_eq :
        Set.EqOn (fun y : ℝ => Real.exp (a * x) * Real.exp ((-a) * y))
          f (Set.Ioi x) := by
      intro y hy
      have hxy : x < y := by simpa using hy
      simp only [f]
      rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hxy)), ← Real.exp_add]
      congr 1
      ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hright_eq.symm]
    calc
      ∫ y in Set.Ioi x, Real.exp (a * x) * Real.exp ((-a) * y)
          = Real.exp (a * x) * ∫ y in Set.Ioi x, Real.exp ((-a) * y) := by
            change _ = Real.exp (a * x) * ∫ y, _ ∂(MeasureTheory.volume.restrict _)
            exact MeasureTheory.integral_const_mul _ _
      _ = Real.exp (a * x) * (-Real.exp ((-a) * x) / (-a)) := by
            rw [integral_exp_mul_Ioi (by linarith : -a < (0 : ℝ)) x]
      _ = 1 / a := by
            field_simp [ne_of_gt ha]
            rw [← Real.exp_add]
            have hzero : a * x + -(a * x) = 0 := by ring
            rw [hzero, Real.exp_zero]
  calc
    ∫ y : ℝ, f y = (∫ y in Set.Iic x, f y) + (∫ y in Set.Ioi x, f y) :=
      hsplit.symm
    _ = 2 / a := by
      rw [hleft_val, hright_val]
      ring

lemma kernel_mul_bounded_integrable_of_pos
    {u : ℝ → ℝ} {a M : ℝ} (ha : 0 < a) (_hM : 0 ≤ M)
    (hu : ∀ y, |u y| ≤ M) (x : ℝ)
    (hu_meas : AEStronglyMeasurable u MeasureTheory.volume) :
    MeasureTheory.Integrable (fun y => Real.exp (-a * |x - y|) * u y) :=
  (kernel_exp_neg_mul_abs_integrable ha x).mul_bdd hu_meas
    (Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hu y)

lemma psi_kernel_mul_bounded_integrable
    {u : ℝ → ℝ} {l M : ℝ} (hl : 0 < l) (hM : 0 ≤ M)
    (hu : ∀ y, |u y| ≤ M) (x : ℝ)
    (hu_meas : AEStronglyMeasurable u MeasureTheory.volume) :
    MeasureTheory.Integrable
      (fun y => Real.exp (-Real.sqrt l * |x - y|) * u y) :=
  kernel_mul_bounded_integrable_of_pos (Real.sqrt_pos.mpr hl) hM hu x hu_meas

lemma kernel_mul_const_integrable (M : ℝ) (x : ℝ) :
    MeasureTheory.Integrable (fun y => Real.exp (-1 * |x - y|) * M) :=
  (kernel_exp_neg_one_integrable x).mul_const M

lemma kernel_mul_exp_integrable (k : ℝ) (hk : 0 < k) (hk1 : k < 1) (x : ℝ) :
    MeasureTheory.Integrable (fun y => Real.exp (-1 * |x - y|) * Real.exp (-k * y)) := by
  let f : ℝ → ℝ := fun y => Real.exp (-1 * |x - y|) * Real.exp (-k * y)
  have hleft_eq : Set.EqOn (fun y : ℝ => Real.exp (-x) * Real.exp ((1 - k) * y)) f (Set.Iic x) := by
    intro y hy
    have hyx : y ≤ x := by simpa using hy
    simp only [f]; rw [abs_of_nonneg (sub_nonneg.mpr hyx), ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hright_eq : Set.EqOn (fun y : ℝ => Real.exp x * Real.exp (-(1 + k) * y)) f (Set.Ioi x) := by
    intro y hy
    have hxy : x < y := by simpa using hy
    simp only [f]; rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hxy)), ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hleft : MeasureTheory.IntegrableOn f (Set.Iic x) := by
    have h1 := integrableOn_exp_mul_Iic (by linarith : (0:ℝ) < 1 - k) x
    have h2 := h1.const_mul (Real.exp (-x))
    exact MeasureTheory.IntegrableOn.congr_fun h2 hleft_eq measurableSet_Iic
  have hright : MeasureTheory.IntegrableOn f (Set.Ioi x) := by
    have h1 := integrableOn_exp_mul_Ioi (by linarith : -(1 + k) < (0:ℝ)) x
    have h2 := h1.const_mul (Real.exp x)
    exact MeasureTheory.IntegrableOn.congr_fun h2 hright_eq measurableSet_Ioi
  have hcover : Set.Iic x ∪ Set.Ioi x = (Set.univ : Set ℝ) := by
    ext y; by_cases hy : y ≤ x <;> simp [hy, lt_of_not_ge]
  rw [← MeasureTheory.integrableOn_univ, ← hcover]
  exact hleft.union hright

lemma kernel_mul_exp_integrable_of_lt
    {a k : ℝ} (hk : 0 < k) (hka : k < a) (x : ℝ) :
    MeasureTheory.Integrable
      (fun y => Real.exp (-a * |x - y|) * Real.exp (-k * y)) := by
  have ha : 0 < a := lt_trans hk hka
  let f : ℝ → ℝ := fun y => Real.exp (-a * |x - y|) * Real.exp (-k * y)
  have hleft_eq :
      Set.EqOn (fun y : ℝ => Real.exp (-a * x) * Real.exp ((a - k) * y))
        f (Set.Iic x) := by
    intro y hy
    have hyx : y ≤ x := by simpa using hy
    simp only [f]
    rw [abs_of_nonneg (sub_nonneg.mpr hyx), ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hright_eq :
      Set.EqOn (fun y : ℝ => Real.exp (a * x) * Real.exp (-(a + k) * y))
        f (Set.Ioi x) := by
    intro y hy
    have hxy : x < y := by simpa using hy
    simp only [f]
    rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hxy)), ← Real.exp_add,
      ← Real.exp_add]
    congr 1
    ring
  have hleft : MeasureTheory.IntegrableOn f (Set.Iic x) := by
    have h1 :=
      integrableOn_exp_mul_Iic (by linarith : (0 : ℝ) < a - k) x
    have h2 := h1.const_mul (Real.exp (-a * x))
    exact MeasureTheory.IntegrableOn.congr_fun h2 hleft_eq measurableSet_Iic
  have hright : MeasureTheory.IntegrableOn f (Set.Ioi x) := by
    have h1 :=
      integrableOn_exp_mul_Ioi (by linarith : -(a + k) < (0 : ℝ)) x
    have h2 := h1.const_mul (Real.exp (a * x))
    exact MeasureTheory.IntegrableOn.congr_fun h2 hright_eq measurableSet_Ioi
  have hcover : Set.Iic x ∪ Set.Ioi x = (Set.univ : Set ℝ) := by
    ext y
    by_cases hy : y ≤ x <;> simp [hy, lt_of_not_ge]
  rw [← MeasureTheory.integrableOn_univ, ← hcover]
  exact hleft.union hright

lemma kernel_mul_bounded_integrable (u : ℝ → ℝ) (M : ℝ) (_hM : 0 ≤ M)
    (hu : ∀ y, |u y| ≤ M) (x : ℝ)
    (hu_meas : AEStronglyMeasurable u MeasureTheory.volume) :
    MeasureTheory.Integrable (fun y => Real.exp (-1 * |x - y|) * u y) :=
  (kernel_exp_neg_one_integrable x).mul_bdd hu_meas
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hu y)

theorem Psi_nonneg {u : ℝ → ℝ} {l mu : ℝ} (_hl : 0 < l) (hmu : 0 < mu)
    (hu : ∀ x, 0 ≤ u x) (x : ℝ) : 0 ≤ Psi u l mu x := by
  unfold Psi
  apply mul_nonneg
  · exact div_nonneg (le_of_lt hmu) (mul_nonneg (by norm_num) (Real.sqrt_nonneg l))
  · exact MeasureTheory.integral_nonneg (fun y => mul_nonneg (Real.exp_nonneg _) (hu y))

theorem Psi_mono {u v : ℝ → ℝ} {l mu : ℝ} (hl : 0 < l) (hmu : 0 < mu)
    (huv : ∀ x, u x ≤ v x) (x : ℝ)
    (hiu : MeasureTheory.Integrable (fun y => Real.exp (-Real.sqrt l * |x - y|) * u y))
    (hiv : MeasureTheory.Integrable (fun y => Real.exp (-Real.sqrt l * |x - y|) * v y)) :
    Psi u l mu x ≤ Psi v l mu x := by
  unfold Psi
  apply mul_le_mul_of_nonneg_left
  · exact MeasureTheory.integral_mono hiu hiv (fun y =>
      mul_le_mul_of_nonneg_left (huv y) (Real.exp_nonneg _))
  · exact div_nonneg (le_of_lt hmu) (mul_nonneg (by norm_num) (Real.sqrt_nonneg l))

theorem Psi_zero (l mu : ℝ) (x : ℝ) :
    Psi (fun _ => (0 : ℝ)) l mu x = 0 := by
  simp [Psi]

theorem Psi_sub_le {u v : ℝ → ℝ} {l mu : ℝ}
    (hl : 0 < l) (hmu : 0 < mu)
    (huv : ∀ x, u x ≤ v x)
    (hu_cont : Continuous u) (hv_cont : Continuous v)
    (hu_bdd : IsBddFun u) (hv_bdd : IsBddFun v) (x : ℝ) :
    Psi u l mu x ≤ Psi v l mu x := by
  rcases hu_bdd with ⟨Mu, hMu⟩
  rcases hv_bdd with ⟨Mv, hMv⟩
  have hMu_nn : 0 ≤ Mu := le_trans (abs_nonneg _) (hMu 0)
  have hMv_nn : 0 ≤ Mv := le_trans (abs_nonneg _) (hMv 0)
  exact Psi_mono hl hmu huv x
    (psi_kernel_mul_bounded_integrable hl hMu_nn hMu x
      hu_cont.aestronglyMeasurable)
    (psi_kernel_mul_bounded_integrable hl hMv_nn hMv x
      hv_cont.aestronglyMeasurable)

theorem Psi_kernel_splitting {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (_hu_nonneg : ∀ y, 0 ≤ u y) (x : ℝ) :
    Psi u 1 1 x =
      1 / 2 * (Real.exp (-1 * x) *
          (∫ y in Set.Iic x, Real.exp (1 * y) * u y) +
        Real.exp (1 * x) *
          (∫ y in Set.Ioi x, Real.exp (-1 * y) * u y)) := by
  let A : ℝ :=
    Real.exp (-1 * x) * (∫ y in Set.Iic x, Real.exp (1 * y) * u y)
  let B : ℝ :=
    Real.exp (1 * x) * (∫ y in Set.Ioi x, Real.exp (-1 * y) * u y)
  obtain ⟨M, hMbound⟩ := hu.2
  have hM_nonneg : 0 ≤ M := by
    exact le_trans (abs_nonneg (u 0)) (hMbound 0)
  have hiu :
      Integrable
        (fun y : ℝ => Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y) := by
    exact psi_kernel_mul_bounded_integrable (by norm_num : (0 : ℝ) < 1)
      hM_nonneg hMbound x hu.1.aestronglyMeasurable
  have hkernel_split :
      (∫ y : ℝ, Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y) = A + B := by
    have hsplit :=
      MeasureTheory.integral_add_compl (s := Set.Iic x) measurableSet_Iic hiu
    simp only [Set.compl_Iic] at hsplit
    have hleft :
        ∫ y in Set.Iic x, Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y = A := by
      have hleft_eq :
          Set.EqOn
            (fun y : ℝ => Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y)
            (fun y : ℝ => Real.exp (-1 * x) * (Real.exp (1 * y) * u y))
            (Set.Iic x) := by
        intro y hy
        have hyx : y ≤ x := by simpa using hy
        change
          Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y =
            Real.exp (-1 * x) * (Real.exp (1 * y) * u y)
        rw [Real.sqrt_one, abs_of_nonneg (sub_nonneg.mpr hyx)]
        rw [show -1 * (x - y) = -1 * x + 1 * y by ring, Real.exp_add]
        ring
      calc
        ∫ y in Set.Iic x, Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y
            = ∫ y in Set.Iic x,
                Real.exp (-1 * x) * (Real.exp (1 * y) * u y) := by
              exact MeasureTheory.setIntegral_congr_fun measurableSet_Iic hleft_eq
        _ = Real.exp (-1 * x) * ∫ y in Set.Iic x, Real.exp (1 * y) * u y := by
              exact MeasureTheory.integral_const_mul _ _
        _ = A := by rfl
    have hright :
        ∫ y in Set.Ioi x, Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y = B := by
      have hright_eq :
          Set.EqOn
            (fun y : ℝ => Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y)
            (fun y : ℝ => Real.exp (1 * x) * (Real.exp (-1 * y) * u y))
            (Set.Ioi x) := by
        intro y hy
        have hxy : x < y := by simpa using hy
        change
          Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y =
            Real.exp (1 * x) * (Real.exp (-1 * y) * u y)
        rw [Real.sqrt_one, abs_of_nonpos (sub_nonpos.mpr (le_of_lt hxy))]
        rw [show -1 * -(x - y) = 1 * x + -1 * y by ring, Real.exp_add]
        ring
      calc
        ∫ y in Set.Ioi x, Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y
            = ∫ y in Set.Ioi x,
                Real.exp (1 * x) * (Real.exp (-1 * y) * u y) := by
              exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hright_eq
        _ = Real.exp (1 * x) * ∫ y in Set.Ioi x, Real.exp (-1 * y) * u y := by
              exact MeasureTheory.integral_const_mul _ _
        _ = B := by rfl
    calc
      ∫ y : ℝ, Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y
          = (∫ y in Set.Iic x, Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y) +
              (∫ y in Set.Ioi x, Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) * u y) :=
            hsplit.symm
      _ = A + B := by rw [hleft, hright]
  unfold Psi
  rw [hkernel_split]
  dsimp only [A, B]
  simp only [Real.sqrt_one]
  ring

private lemma integral_exp_neg_abs : ∫ x : ℝ, Real.exp (-|x|) = 2 := by
  have h := @integral_comp_abs (fun t => Real.exp (-t))
  simp only [Function.comp] at h
  linarith [integral_exp_neg_Ioi_zero]

private lemma integral_exp_neg_abs_sub (x : ℝ) :
    ∫ y : ℝ, Real.exp (-|x - y|) = 2 := by
  have h : (fun y : ℝ => Real.exp (-|x - y|)) = (fun y => Real.exp (-|y + (-x)|)) := by
    ext y; congr 2; rw [abs_sub_comm]; ring_nf
  rw [h, integral_add_right_eq_self (fun z => Real.exp (-|z|)) (-x), integral_exp_neg_abs]

theorem Psi_const {c : ℝ} (_hc : 0 ≤ c) (x : ℝ) :
    Psi (fun _ : ℝ => c) 1 1 x = c := by
  simp only [Psi, Real.sqrt_one, mul_one]
  rw [show (fun y : ℝ => Real.exp (-1 * |x - y|) * c) =
    (fun y => c * Real.exp (-|x - y|)) from by ext y; ring]
  rw [MeasureTheory.integral_const_mul, integral_exp_neg_abs_sub x]
  ring

theorem Psi_const_general {c l mu : ℝ} (hl : 0 < l) (x : ℝ) :
    Psi (fun _ : ℝ => c) l mu x = (mu / l) * c := by
  have hsqrt_pos : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  simp only [Psi]
  rw [show (fun y : ℝ => Real.exp (-Real.sqrt l * |x - y|) * c) =
    (fun y => c * Real.exp (-Real.sqrt l * |x - y|)) from by ext y; ring]
  rw [MeasureTheory.integral_const_mul,
    integral_exp_neg_mul_abs_sub hsqrt_pos x]
  have hsqrt_sq : Real.sqrt l * Real.sqrt l = l := by
    rw [← sq]
    exact Real.sq_sqrt hl.le
  calc
    mu / (2 * Real.sqrt l) * (c * (2 / Real.sqrt l))
        = (mu / (Real.sqrt l * Real.sqrt l)) * c := by
          field_simp [ne_of_gt hsqrt_pos]
    _ = (mu / l) * c := by
          rw [hsqrt_sq]

theorem Psi_smul {u : ℝ → ℝ} {l mu a : ℝ} (x : ℝ) :
    Psi (fun y => a * u y) l mu x = a * Psi u l mu x := by
  unfold Psi
  rw [show (fun y : ℝ => Real.exp (-Real.sqrt l * |x - y|) * (a * u y)) =
    (fun y => a * (Real.exp (-Real.sqrt l * |x - y|) * u y)) from by ext y; ring]
  rw [MeasureTheory.integral_const_mul]
  ring

theorem Psi_neg {u : ℝ → ℝ} {l mu : ℝ} (x : ℝ) :
    Psi (fun y => -u y) l mu x = -Psi u l mu x := by
  have h := Psi_smul (u := u) (l := l) (mu := mu) (a := -1) x
  simp only [neg_one_mul] at h
  exact h

theorem Psi_add {u v : ℝ → ℝ} {l mu : ℝ} (x : ℝ)
    (hiu : MeasureTheory.Integrable
      (fun y => Real.exp (-Real.sqrt l * |x - y|) * u y))
    (hiv : MeasureTheory.Integrable
      (fun y => Real.exp (-Real.sqrt l * |x - y|) * v y)) :
    Psi (fun y => u y + v y) l mu x = Psi u l mu x + Psi v l mu x := by
  unfold Psi
  rw [show (fun y : ℝ => Real.exp (-Real.sqrt l * |x - y|) * (u y + v y)) =
    (fun y => Real.exp (-Real.sqrt l * |x - y|) * u y +
      Real.exp (-Real.sqrt l * |x - y|) * v y) from by ext y; ring]
  rw [MeasureTheory.integral_add hiu hiv]
  ring

theorem Psi_sub {u v : ℝ → ℝ} {l mu : ℝ} (x : ℝ)
    (hiu : MeasureTheory.Integrable
      (fun y => Real.exp (-Real.sqrt l * |x - y|) * u y))
    (hiv : MeasureTheory.Integrable
      (fun y => Real.exp (-Real.sqrt l * |x - y|) * v y)) :
    Psi (fun y => u y - v y) l mu x = Psi u l mu x - Psi v l mu x := by
  unfold Psi
  rw [show (fun y : ℝ => Real.exp (-Real.sqrt l * |x - y|) * (u y - v y)) =
    (fun y => Real.exp (-Real.sqrt l * |x - y|) * u y -
      Real.exp (-Real.sqrt l * |x - y|) * v y) from by ext y; ring]
  rw [MeasureTheory.integral_sub hiu hiv]
  ring

theorem Psi_mu_smul {u : ℝ → ℝ} {l mu₁ mu₂ : ℝ}
    (hl : 0 < l) (x : ℝ) :
    Psi u l (mu₁ * mu₂) x = mu₁ * Psi u l mu₂ x := by
  unfold Psi
  have hsqrt_ne : (2 * Real.sqrt l) ≠ 0 := by
    positivity
  field_simp [hsqrt_ne]

theorem Psi_le_const_general_of_le {u : ℝ → ℝ} {l mu M : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hM : 0 ≤ M)
    (huM : ∀ y, u y ≤ M) (x : ℝ)
    (hiu : MeasureTheory.Integrable
      (fun y => Real.exp (-Real.sqrt l * |x - y|) * u y)) :
    Psi u l mu x ≤ (mu / l) * M := by
  have hconst_int :
      MeasureTheory.Integrable
        (fun y =>
          Real.exp (-Real.sqrt l * |x - y|) *
            (fun _ : ℝ => M) y) := by
    exact psi_kernel_mul_bounded_integrable hl hM
      (fun _ => by simp [abs_of_nonneg hM])
      x aestronglyMeasurable_const
  calc
    Psi u l mu x ≤ Psi (fun _ : ℝ => M) l mu x :=
      Psi_mono hl hmu huM x hiu hconst_int
    _ = (mu / l) * M := Psi_const_general hl x

theorem Psi_le_const_general_of_nonneg_le {u : ℝ → ℝ} {l mu M : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hM : 0 ≤ M)
    (hu_cont : Continuous u)
    (hu_nonneg : ∀ y, 0 ≤ u y)
    (huM : ∀ y, u y ≤ M) (x : ℝ) :
    Psi u l mu x ≤ (mu / l) * M := by
  have hiu :
      MeasureTheory.Integrable
        (fun y => Real.exp (-Real.sqrt l * |x - y|) * u y) := by
    exact psi_kernel_mul_bounded_integrable hl hM
      (fun y => by
        rw [abs_of_nonneg (hu_nonneg y)]
        exact huM y)
      x hu_cont.aestronglyMeasurable
  exact Psi_le_const_general_of_le hl hmu hM huM x hiu

private lemma exp_kernel_left_eq (x y k : ℝ) (hy : y ≤ x) :
    Real.exp (-|x - y|) * Real.exp (-k * y) = Real.exp (-x) * Real.exp ((1 - k) * y) := by
  rw [abs_of_nonneg (sub_nonneg.mpr hy), ← Real.exp_add, ← Real.exp_add]; congr 1; ring

private lemma exp_kernel_right_eq (x y k : ℝ) (hy : x < y) :
    Real.exp (-|x - y|) * Real.exp (-k * y) = Real.exp x * Real.exp (-(1 + k) * y) := by
  rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hy)), ← Real.exp_add, ← Real.exp_add]; congr 1; ring

private lemma integral_exp_kernel_exp {k : ℝ} (hk : 0 < k) (hk1 : k < 1) (x : ℝ) :
    (∫ y : ℝ, Real.exp (-|x - y|) * Real.exp (-k * y)) =
      2 * (1 / (1 - k ^ 2) * Real.exp (-k * x)) := by
  have hkpos : 0 < 1 - k := by linarith
  have hkneg : -(1 + k) < 0 := by linarith
  have hk1p_pos : 0 < 1 + k := by linarith
  -- Integrability
  have hfi : MeasureTheory.Integrable (fun y => Real.exp (-|x - y|) * Real.exp (-k * y)) := by
    have h := kernel_mul_exp_integrable k hk hk1 x
    rwa [show (fun y => Real.exp (-1 * |x - y|) * Real.exp (-k * y)) =
      (fun y => Real.exp (-|x - y|) * Real.exp (-k * y)) from by
        ext y; norm_num] at h
  -- Split
  have hsplit := MeasureTheory.integral_add_compl (s := Set.Iic x) measurableSet_Iic hfi
  simp only [Set.compl_Iic] at hsplit
  -- Left value
  have hleft_val : ∫ y in Set.Iic x, Real.exp (-|x - y|) * Real.exp (-k * y) =
      Real.exp (-k * x) / (1 - k) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Iic (fun y hy => exp_kernel_left_eq x y k hy)]
    calc ∫ y in Set.Iic x, Real.exp (-x) * Real.exp ((1 - k) * y)
        = Real.exp (-x) * ∫ y in Set.Iic x, Real.exp ((1 - k) * y) := by
          change _ = Real.exp (-x) * ∫ y, _ ∂(MeasureTheory.volume.restrict _)
          exact MeasureTheory.integral_const_mul _ _
      _ = Real.exp (-x) * (Real.exp ((1 - k) * x) / (1 - k)) := by rw [integral_exp_mul_Iic hkpos x]
      _ = Real.exp (-k * x) / (1 - k) := by
          rw [show Real.exp (-x) * (Real.exp ((1 - k) * x) / (1 - k)) =
            (Real.exp (-x) * Real.exp ((1 - k) * x)) / (1 - k) from by ring,
            ← Real.exp_add]; congr 1; ring
  -- Right value
  have hright_val : ∫ y in Set.Ioi x, Real.exp (-|x - y|) * Real.exp (-k * y) =
      Real.exp (-k * x) / (1 + k) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => exp_kernel_right_eq x y k hy)]
    calc ∫ y in Set.Ioi x, Real.exp x * Real.exp (-(1 + k) * y)
        = Real.exp x * ∫ y in Set.Ioi x, Real.exp (-(1 + k) * y) := by
          change _ = Real.exp x * ∫ y, _ ∂(MeasureTheory.volume.restrict _)
          exact MeasureTheory.integral_const_mul _ _
      _ = Real.exp x * (-Real.exp (-(1 + k) * x) / (-(1 + k))) := by rw [integral_exp_mul_Ioi hkneg x]
      _ = Real.exp (-k * x) / (1 + k) := by
          have hne : (1 : ℝ) + k ≠ 0 := by linarith
          field_simp [hne]
          rw [← Real.exp_add]; congr 1; ring
  -- Combine
  calc ∫ y, Real.exp (-|x - y|) * Real.exp (-k * y)
      = (∫ y in Set.Iic x, _) + (∫ y in Set.Ioi x, _) := hsplit.symm
    _ = Real.exp (-k * x) / (1 - k) + Real.exp (-k * x) / (1 + k) := by rw [hleft_val, hright_val]
    _ = 2 * (1 / (1 - k ^ 2) * Real.exp (-k * x)) := by
        have h1 : (1 : ℝ) - k ≠ 0 := by linarith
        have h2 : (1 : ℝ) + k ≠ 0 := by linarith
        have hden : (1 : ℝ) - k ^ 2 ≠ 0 := by nlinarith [mul_pos hkpos hk1p_pos]
        field_simp [h1, h2, hden]; ring

private lemma integral_exp_kernel_exp_general
    {a k : ℝ} (hk : 0 < k) (hka : k < a) (x : ℝ) :
    (∫ y : ℝ, Real.exp (-a * |x - y|) * Real.exp (-k * y)) =
      (2 * a / (a ^ 2 - k ^ 2)) * Real.exp (-k * x) := by
  have ha : 0 < a := lt_trans hk hka
  have hleft_pos : 0 < a - k := by linarith
  have hright_neg : -(a + k) < 0 := by linarith
  have hright_pos : 0 < a + k := by linarith
  have hfi :
      MeasureTheory.Integrable
        (fun y => Real.exp (-a * |x - y|) * Real.exp (-k * y)) :=
    kernel_mul_exp_integrable_of_lt hk hka x
  have hsplit := MeasureTheory.integral_add_compl (s := Set.Iic x) measurableSet_Iic hfi
  simp only [Set.compl_Iic] at hsplit
  have hleft_val :
      ∫ y in Set.Iic x, Real.exp (-a * |x - y|) * Real.exp (-k * y) =
        Real.exp (-k * x) / (a - k) := by
    have hleft_eq :
        Set.EqOn
          (fun y : ℝ => Real.exp (-a * x) * Real.exp ((a - k) * y))
          (fun y => Real.exp (-a * |x - y|) * Real.exp (-k * y))
          (Set.Iic x) := by
      intro y hy
      have hyx : y ≤ x := by simpa using hy
      change
        Real.exp (-a * x) * Real.exp ((a - k) * y) =
          Real.exp (-a * |x - y|) * Real.exp (-k * y)
      rw [abs_of_nonneg (sub_nonneg.mpr hyx), ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Iic hleft_eq.symm]
    calc
      ∫ y in Set.Iic x, Real.exp (-a * x) * Real.exp ((a - k) * y)
          = Real.exp (-a * x) * ∫ y in Set.Iic x, Real.exp ((a - k) * y) := by
            change _ = Real.exp (-a * x) * ∫ y, _ ∂(MeasureTheory.volume.restrict _)
            exact MeasureTheory.integral_const_mul _ _
      _ = Real.exp (-a * x) * (Real.exp ((a - k) * x) / (a - k)) := by
            rw [integral_exp_mul_Iic hleft_pos x]
      _ = Real.exp (-k * x) / (a - k) := by
            rw [show Real.exp (-a * x) * (Real.exp ((a - k) * x) / (a - k)) =
              (Real.exp (-a * x) * Real.exp ((a - k) * x)) / (a - k) from by ring,
              ← Real.exp_add]
            congr 1
            ring
  have hright_val :
      ∫ y in Set.Ioi x, Real.exp (-a * |x - y|) * Real.exp (-k * y) =
        Real.exp (-k * x) / (a + k) := by
    have hright_eq :
        Set.EqOn
          (fun y : ℝ => Real.exp (a * x) * Real.exp (-(a + k) * y))
          (fun y => Real.exp (-a * |x - y|) * Real.exp (-k * y))
          (Set.Ioi x) := by
      intro y hy
      have hxy : x < y := by simpa using hy
      change
        Real.exp (a * x) * Real.exp (-(a + k) * y) =
          Real.exp (-a * |x - y|) * Real.exp (-k * y)
      rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hxy)), ← Real.exp_add,
        ← Real.exp_add]
      congr 1
      ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hright_eq.symm]
    calc
      ∫ y in Set.Ioi x, Real.exp (a * x) * Real.exp (-(a + k) * y)
          = Real.exp (a * x) * ∫ y in Set.Ioi x, Real.exp (-(a + k) * y) := by
            change _ = Real.exp (a * x) * ∫ y, _ ∂(MeasureTheory.volume.restrict _)
            exact MeasureTheory.integral_const_mul _ _
      _ = Real.exp (a * x) * (-Real.exp (-(a + k) * x) / (-(a + k))) := by
            rw [integral_exp_mul_Ioi hright_neg x]
      _ = Real.exp (-k * x) / (a + k) := by
            have hne : a + k ≠ 0 := by linarith
            field_simp [hne]
            rw [← Real.exp_add]
            congr 1
            ring
  calc
    ∫ y, Real.exp (-a * |x - y|) * Real.exp (-k * y)
        = (∫ y in Set.Iic x, _) + (∫ y in Set.Ioi x, _) := hsplit.symm
    _ = Real.exp (-k * x) / (a - k) + Real.exp (-k * x) / (a + k) := by
          rw [hleft_val, hright_val]
    _ = (2 * a / (a ^ 2 - k ^ 2)) * Real.exp (-k * x) := by
          have h1 : a - k ≠ 0 := by linarith
          have h2 : a + k ≠ 0 := by linarith
          have hden : a ^ 2 - k ^ 2 ≠ 0 := by
            nlinarith [mul_pos hleft_pos hright_pos]
          field_simp [h1, h2, hden]
          ring

theorem Psi_exp {k : ℝ} (hk : 0 < k) (hk1 : k < 1) (x : ℝ) :
    Psi (fun y : ℝ => Real.exp (-k * y)) 1 1 x =
      1 / (1 - k ^ 2) * Real.exp (-k * x) := by
  simp only [Psi, Real.sqrt_one, mul_one]
  rw [show (fun y : ℝ => Real.exp (-1 * |x - y|) * Real.exp (-k * y)) =
    (fun y => Real.exp (-|x - y|) * Real.exp (-k * y)) from by ext y; ring_nf]
  rw [integral_exp_kernel_exp hk hk1 x]
  ring

theorem Psi_exp_general {l mu k : ℝ}
    (hl : 0 < l) (hk : 0 < k) (hklt : k < Real.sqrt l) (x : ℝ) :
    Psi (fun y : ℝ => Real.exp (-k * y)) l mu x =
      mu / (l - k ^ 2) * Real.exp (-k * x) := by
  have hsqrt_pos : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  have hsqrt_sq : Real.sqrt l * Real.sqrt l = l := by
    rw [← sq]
    exact Real.sq_sqrt hl.le
  simp only [Psi]
  rw [integral_exp_kernel_exp_general hk hklt x]
  calc
    mu / (2 * Real.sqrt l) *
        ((2 * Real.sqrt l / (Real.sqrt l ^ 2 - k ^ 2)) * Real.exp (-k * x))
        = mu / (Real.sqrt l ^ 2 - k ^ 2) * Real.exp (-k * x) := by
          field_simp [ne_of_gt hsqrt_pos]
    _ = mu / (l - k ^ 2) * Real.exp (-k * x) := by
          rw [show Real.sqrt l ^ 2 = l from Real.sq_sqrt hl.le]

lemma resolvent_exp_denom_pos
    {l k : ℝ} (hl : 0 < l) (hk_nonneg : 0 ≤ k) (hklt : k < Real.sqrt l) :
    0 < l - k ^ 2 := by
  have hprod : 0 < (Real.sqrt l - k) * (Real.sqrt l + k) := by
    exact mul_pos (sub_pos.mpr hklt) (by positivity)
  have hsqrt_sq : Real.sqrt l * Real.sqrt l = l := by
    rw [← sq]
    exact Real.sq_sqrt hl.le
  nlinarith

lemma resolvent_exp_coeff_pos
    {l mu k : ℝ} (hl : 0 < l) (hmu : 0 < mu)
    (hk_nonneg : 0 ≤ k) (hklt : k < Real.sqrt l) :
    0 < mu / (l - k ^ 2) := by
  exact div_pos hmu (resolvent_exp_denom_pos hl hk_nonneg hklt)

theorem Psi_le_exp_general_of_le {u : ℝ → ℝ} {l mu k : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hk : 0 < k) (hklt : k < Real.sqrt l)
    (huexp : ∀ y, u y ≤ Real.exp (-k * y)) (x : ℝ)
    (hiu : MeasureTheory.Integrable
      (fun y => Real.exp (-Real.sqrt l * |x - y|) * u y)) :
    Psi u l mu x ≤ mu / (l - k ^ 2) * Real.exp (-k * x) := by
  have hexp_int :
      MeasureTheory.Integrable
        (fun y =>
          Real.exp (-Real.sqrt l * |x - y|) *
            (fun y : ℝ => Real.exp (-k * y)) y) := by
    exact kernel_mul_exp_integrable_of_lt hk hklt x
  calc
    Psi u l mu x ≤ Psi (fun y : ℝ => Real.exp (-k * y)) l mu x :=
      Psi_mono hl hmu huexp x hiu hexp_int
    _ = mu / (l - k ^ 2) * Real.exp (-k * x) :=
      Psi_exp_general hl hk hklt x

theorem Psi_le_min_const_exp_general_of_le
    {u : ℝ → ℝ} {l mu M k : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hM : 0 ≤ M)
    (hk : 0 < k) (hklt : k < Real.sqrt l)
    (huM : ∀ y, u y ≤ M)
    (huexp : ∀ y, u y ≤ Real.exp (-k * y)) (x : ℝ)
    (hiu : MeasureTheory.Integrable
      (fun y => Real.exp (-Real.sqrt l * |x - y|) * u y)) :
    Psi u l mu x ≤
      min ((mu / l) * M) (mu / (l - k ^ 2) * Real.exp (-k * x)) := by
  exact le_min
    (Psi_le_const_general_of_le hl hmu hM huM x hiu)
    (Psi_le_exp_general_of_le hl hmu hk hklt huexp x hiu)

theorem Psi_le_min_const_exp_general_of_nonneg_le
    {u : ℝ → ℝ} {l mu M k : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hM : 0 ≤ M)
    (hk : 0 < k) (hklt : k < Real.sqrt l)
    (hu_cont : Continuous u)
    (hu_nonneg : ∀ y, 0 ≤ u y)
    (huM : ∀ y, u y ≤ M)
    (huexp : ∀ y, u y ≤ Real.exp (-k * y)) (x : ℝ) :
    Psi u l mu x ≤
      min ((mu / l) * M) (mu / (l - k ^ 2) * Real.exp (-k * x)) := by
  have hiu :
      MeasureTheory.Integrable
        (fun y => Real.exp (-Real.sqrt l * |x - y|) * u y) := by
    exact psi_kernel_mul_bounded_integrable hl hM
      (fun y => by
        rw [abs_of_nonneg (hu_nonneg y)]
        exact huM y)
      x hu_cont.aestronglyMeasurable
  exact Psi_le_min_const_exp_general_of_le hl hmu hM hk hklt huM huexp x hiu

theorem Psi_le_const_of_le {u : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (huM : ∀ y, u y ≤ M) (x : ℝ)
    (hiu : MeasureTheory.Integrable
      (fun y => Real.exp (-Real.sqrt 1 * |x - y|) * u y)) :
    Psi u 1 1 x ≤ M := by
  have hconst_int :
      MeasureTheory.Integrable
        (fun y => Real.exp (-Real.sqrt 1 * |x - y|) * (fun _ : ℝ => M) y) := by
    simpa [Real.sqrt_one] using kernel_mul_const_integrable M x
  calc
    Psi u 1 1 x ≤ Psi (fun _ : ℝ => M) 1 1 x :=
      Psi_mono one_pos one_pos huM x hiu hconst_int
    _ = M := Psi_const hM x

theorem Psi_le_exp_of_le {u : ℝ → ℝ} {k : ℝ}
    (hk : 0 < k) (hk1 : k < 1)
    (huexp : ∀ y, u y ≤ Real.exp (-k * y)) (x : ℝ)
    (hiu : MeasureTheory.Integrable
      (fun y => Real.exp (-Real.sqrt 1 * |x - y|) * u y)) :
    Psi u 1 1 x ≤ 1 / (1 - k ^ 2) * Real.exp (-k * x) := by
  have hexp_int :
      MeasureTheory.Integrable
        (fun y =>
          Real.exp (-Real.sqrt 1 * |x - y|) *
            (fun y : ℝ => Real.exp (-k * y)) y) := by
    simpa [Real.sqrt_one] using kernel_mul_exp_integrable k hk hk1 x
  calc
    Psi u 1 1 x ≤ Psi (fun y : ℝ => Real.exp (-k * y)) 1 1 x :=
      Psi_mono one_pos one_pos huexp x hiu hexp_int
    _ = 1 / (1 - k ^ 2) * Real.exp (-k * x) := Psi_exp hk hk1 x

theorem Psi_le_min_const_exp_of_le {u : ℝ → ℝ} {M k : ℝ}
    (hM : 0 ≤ M) (hk : 0 < k) (hk1 : k < 1)
    (huM : ∀ y, u y ≤ M)
    (huexp : ∀ y, u y ≤ Real.exp (-k * y)) (x : ℝ)
    (hiu : MeasureTheory.Integrable
      (fun y => Real.exp (-Real.sqrt 1 * |x - y|) * u y)) :
    Psi u 1 1 x ≤ min M (1 / (1 - k ^ 2) * Real.exp (-k * x)) := by
  exact le_min
    (Psi_le_const_of_le hM huM x hiu)
    (Psi_le_exp_of_le hk hk1 huexp x hiu)

theorem Psi_le_min_const_exp_of_nonneg_le {u : ℝ → ℝ} {M k : ℝ}
    (hM : 0 ≤ M) (hk : 0 < k) (hk1 : k < 1)
    (hu_cont : Continuous u)
    (hu_nonneg : ∀ y, 0 ≤ u y)
    (huM : ∀ y, u y ≤ M)
    (huexp : ∀ y, u y ≤ Real.exp (-k * y)) (x : ℝ) :
    Psi u 1 1 x ≤ min M (1 / (1 - k ^ 2) * Real.exp (-k * x)) := by
  have hiu_raw :
      MeasureTheory.Integrable (fun y => Real.exp (-1 * |x - y|) * u y) :=
    kernel_mul_bounded_integrable u M hM
      (fun y => by
        rw [abs_of_nonneg (hu_nonneg y)]
        exact huM y)
      x hu_cont.aestronglyMeasurable
  have hiu :
      MeasureTheory.Integrable
        (fun y => Real.exp (-Real.sqrt 1 * |x - y|) * u y) := by
    simpa [Real.sqrt_one] using hiu_raw
  exact Psi_le_min_const_exp_of_le hM hk hk1 huM huexp x hiu

/-- HasDerivAt for exp(-|x'-y|) at x'=x when y < x. -/
lemma hasDerivAt_kernel_left {x y : ℝ} (hy : y < x) :
    HasDerivAt (fun x' => Real.exp (-|x' - y|)) (-Real.exp (-(x - y))) x := by
  have hev : (fun x' => Real.exp (-|x' - y|)) =ᶠ[𝓝 x]
      (fun x' => Real.exp (-(x' - y))) := by
    filter_upwards [Ioi_mem_nhds hy] with x' hx'
    show Real.exp (-|x' - y|) = Real.exp (-(x' - y))
    congr 1; rw [abs_of_pos (sub_pos.mpr hx')]
  exact hev.hasDerivAt_iff.mpr
    ((((hasDerivAt_id x).sub_const y).neg.exp).congr_deriv (by simp [neg_sub]))

/-- HasDerivAt for exp(-|x'-y|) at x'=x when y > x. -/
lemma hasDerivAt_kernel_right {x y : ℝ} (hy : x < y) :
    HasDerivAt (fun x' => Real.exp (-|x' - y|)) (Real.exp (-(y - x))) x := by
  have hev : (fun x' => Real.exp (-|x' - y|)) =ᶠ[𝓝 x]
      (fun x' => Real.exp (x' - y)) := by
    filter_upwards [Iio_mem_nhds hy] with x' hx'
    show Real.exp (-|x' - y|) = Real.exp (x' - y)
    rw [show -|x' - y| = x' - y from by
      rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hx'))]; ring]
  exact hev.hasDerivAt_iff.mpr
    (((hasDerivAt_id x).sub_const y).exp.congr_deriv (by simp [neg_sub]))

-- Psi_deriv_abs_le moved to PDE/LeibnizRule.lean as Psi_deriv_abs_le'

/-- c**_{χ,m,α,γ} from Theorem 1.2. -/
def cStarStar (p : CMParams) : ℝ :=
  1 + |p.χ| ^ (1/6 : ℝ) + 1 / (1 + |p.χ| ^ (1/6 : ℝ))

lemma cStarStar_ge_two (p : CMParams) :
    2 ≤ cStarStar p := by
  unfold cStarStar
  set a : ℝ := |p.χ| ^ (1 / 6 : ℝ)
  have ha : 0 ≤ a := by positivity
  have hpos : 0 < 1 + a := by linarith
  have hmul : 2 * (1 + a) ≤ (1 + a + 1 / (1 + a)) * (1 + a) := by
    field_simp [ne_of_gt hpos]
    nlinarith [sq_nonneg a]
  exact le_of_mul_le_mul_right hmul hpos

lemma two_lt_of_cStarStar_lt {p : CMParams} {c : ℝ}
    (hc : cStarStar p < c) :
    2 < c :=
  lt_of_le_of_lt (cStarStar_ge_two p) hc

lemma kappa_pos_of_cStarStar_lt {p : CMParams} {c : ℝ}
    (hc : cStarStar p < c) :
    0 < kappa c :=
  kappa_pos_of_two_lt (two_lt_of_cStarStar_lt hc)

theorem IsTravelingWave.shift_right_with_exp_bound (p : CMParams)
    {c a : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hc : cStarStar p < c)
    (ha : 0 ≤ a)
    (hbound : ∀ x, U x < Real.exp (-kappa c * x)) :
    IsTravelingWave p c (fun x => U (x + a)) (fun x => V (x + a)) ∧
      ∀ x, U (x + a) < Real.exp (-kappa c * x) := by
  exact
    ⟨hTW.shift p a,
      exp_bound_shift_right (kappa_pos_of_cStarStar_lt hc).le ha hbound⟩

theorem IsMonotoneTravelingWave.shift_right_with_exp_bound (p : CMParams)
    {c a : ℝ} {U V : ℝ → ℝ}
    (hTW : IsMonotoneTravelingWave p c U V)
    (hc : cStarStar p < c)
    (ha : 0 ≤ a)
    (hbound : ∀ x, U x < Real.exp (-kappa c * x)) :
    IsMonotoneTravelingWave p c (fun x => U (x + a)) (fun x => V (x + a)) ∧
      ∀ x, U (x + a) < Real.exp (-kappa c * x) := by
  exact
    ⟨hTW.shift p a,
      exp_bound_shift_right (kappa_pos_of_cStarStar_lt hc).le ha hbound⟩

/-! ## Explicit solutions for special cases -/

/-- The constant solution u ≡ 1, v ≡ 1 is a global classical solution for ANY χ. -/
theorem constant_solution_is_global (p : CMParams) :
    IsGlobalClassicalSolution p (fun _ _ => 1) (fun _ _ => 1) := by
  intro T hT
  exact {
    hT := hT
    u_smooth := fun t x _ _ => ⟨differentiableAt_const 1, differentiableAt_const 1⟩
    v_smooth := fun t x _ _ => differentiableAt_const 1
    pde_u := fun t x _ _ => by
      simp only [Function.comp_apply, deriv_const,
        show iteratedDeriv 2 (fun _ : ℝ => (1:ℝ)) x = 0 from by
          rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]; simp [deriv_const],
        Real.one_rpow, sub_self, mul_zero, zero_add, zero_sub, neg_zero]
    pde_v := fun t x _ _ => by
      rw [show iteratedDeriv 2 (fun _ : ℝ => (1:ℝ)) x = 0 from by
        rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
        simp [deriv_const]]
      simp [Real.one_rpow]
  }

/-! ## Honest projection lemmas

The paper-level global existence, stabilization, traveling-wave existence,
stability, and uniqueness theorems are not stated here as Lean theorems yet.
This section keeps only facts that follow directly from the current definitions.
-/

theorem IsTravelingWave.to_movingFrame_global_classical_solution_of_differentiable
    (p : CMParams)
    {c : ℝ} {U V : ℝ → ℝ} (hTW : IsTravelingWave p c U V)
    (hU_diff : Differentiable ℝ U) (hV_diff : Differentiable ℝ V) :
    IsGlobalClassicalSolution p
      (fun t x => U (x - c * t)) (fun t x => V (x - c * t)) := by
  intro T hT
  exact {
    hT := hT
    u_smooth := fun t x _ _ => ⟨
      (hU_diff _).comp _ ((differentiableAt_const x).sub
        ((differentiableAt_const c).mul differentiableAt_id)),
      (hU_diff _).comp _ (differentiableAt_id.sub (differentiableAt_const _))⟩
    v_smooth := fun t x _ _ =>
      (hV_diff _).comp _ (differentiableAt_id.sub (differentiableAt_const _))
    pde_u := fun t x _ _ => by
      -- Time derivative via chain rule.
      have hinner : HasDerivAt (fun t' => x - c * t') (-c) t := by
        have := (hasDerivAt_const t x).sub ((hasDerivAt_id t).const_mul c)
        simpa using this
      have htime :
          deriv (fun t' => U (x - c * t')) t = deriv U (x - c * t) * (-c) :=
        ((hU_diff _).hasDerivAt.comp t hinner).deriv
      -- Spatial translations.
      have hU2 := congr_fun (iteratedDeriv_comp_sub_const 2 U (c * t)) x
      have hV1 : ∀ y, deriv (fun z => V (z - c * t)) y = deriv V (y - c * t) := by
        intro y
        have := congr_fun (iteratedDeriv_comp_sub_const 1 V (c * t)) y
        simpa [iteratedDeriv_one] using this
      have hChem :
          deriv (fun y => U (y - c * t) ^ p.m *
            deriv (fun z => V (z - c * t)) y) x =
          deriv (fun ξ => U ξ ^ p.m * deriv V ξ) (x - c * t) := by
        have hfun :
            (fun y => U (y - c * t) ^ p.m *
              deriv (fun z => V (z - c * t)) y) =
            (fun y => U (y - c * t) ^ p.m * deriv V (y - c * t)) := by
          ext y
          rw [hV1 y]
        rw [hfun]
        have := congr_fun (iteratedDeriv_comp_sub_const 1
          (fun ξ => U ξ ^ p.m * deriv V ξ) (c * t)) x
        simpa [iteratedDeriv_one] using this
      rw [htime, hU2, hChem]
      linarith [hTW.ode_U (x - c * t)]
    pde_v := fun t x _ _ => by
      have h := congr_fun (iteratedDeriv_comp_sub_const 2 V (c * t)) x
      rw [h]
      exact hTW.ode_V (x - c * t)
  }

/-- A `C²` wave is, in particular, differentiable; this is the historical
interface retained for existing callers.  The classical-solution structure
itself only asks for the first derivatives used above. -/
theorem IsTravelingWave.to_movingFrame_global_classical_solution (p : CMParams)
    {c : ℝ} {U V : ℝ → ℝ} (hTW : IsTravelingWave p c U V)
    (hU_diff : ContDiff ℝ 2 U) (hV_diff : ContDiff ℝ 2 V) :
    IsGlobalClassicalSolution p
      (fun t x => U (x - c * t)) (fun t x => V (x - c * t)) :=
  hTW.to_movingFrame_global_classical_solution_of_differentiable p
    (hU_diff.differentiable two_ne_zero)
    (hV_diff.differentiable two_ne_zero)

theorem IsTravelingWave.to_global_classical_solution (p : CMParams)
    {c : ℝ} {U V : ℝ → ℝ} (hTW : IsTravelingWave p c U V)
    (hU_diff : ContDiff ℝ 2 U) (hV_diff : ContDiff ℝ 2 V)
    : ∃ u v : ℝ → ℝ → ℝ, IsGlobalClassicalSolution p u v :=
  ⟨fun t x => U (x - c * t), fun t x => V (x - c * t),
    hTW.to_movingFrame_global_classical_solution p hU_diff hV_diff⟩

end
