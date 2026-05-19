/-
  Statement layer for Shen,
  "Existence, uniqueness, stability, and monotonicity of traveling waves for
  repulsion/attraction chemotaxis models with logistic type source".

  The declarations below formalize the paper-level targets as propositions.
  They are not proofs of the paper theorems.
-/
import ShenWork.PDE.LeibnizRule
import Mathlib.Analysis.Convex.Basic

open Filter Topology MeasureTheory

namespace ShenWork.Paper1

noncomputable section

def NonnegativeInitialDatum (u₀ : ℝ → ℝ) : Prop :=
  IsCUnifBdd u₀ ∧ ∀ x, 0 ≤ u₀ x

def UniformlyPositive (u₀ : ℝ → ℝ) : Prop :=
  ∃ δ > 0, ∀ x, δ ≤ u₀ x

def StrictlyPositiveAtLeft (u₀ : ℝ → ℝ) : Prop :=
  ∃ δ > 0, ∀ᶠ x in atBot, δ ≤ u₀ x

theorem UniformlyPositive.pos
    {u₀ : ℝ → ℝ} (h : UniformlyPositive u₀) :
    ∀ x, 0 < u₀ x := by
  rcases h with ⟨δ, hδ, hδle⟩
  intro x
  exact lt_of_lt_of_le hδ (hδle x)

theorem UniformlyPositive.strictlyPositiveAtLeft
    {u₀ : ℝ → ℝ} (h : UniformlyPositive u₀) :
    StrictlyPositiveAtLeft u₀ := by
  rcases h with ⟨δ, hδ, hδle⟩
  exact ⟨δ, hδ, Eventually.of_forall hδle⟩

theorem UniformlyPositive.shift
    {u₀ : ℝ → ℝ} (h : UniformlyPositive u₀) (a : ℝ) :
    UniformlyPositive (fun x => u₀ (x + a)) := by
  rcases h with ⟨δ, hδ, hδle⟩
  exact ⟨δ, hδ, fun x => hδle (x + a)⟩

theorem StrictlyPositiveAtLeft.eventually_pos
    {u₀ : ℝ → ℝ} (h : StrictlyPositiveAtLeft u₀) :
    ∀ᶠ x in atBot, 0 < u₀ x := by
  rcases h with ⟨δ, hδ, hδle⟩
  filter_upwards [hδle] with x hx
  exact lt_of_lt_of_le hδ hx

theorem StrictlyPositiveAtLeft.shift
    {u₀ : ℝ → ℝ} (h : StrictlyPositiveAtLeft u₀) (a : ℝ) :
    StrictlyPositiveAtLeft (fun x => u₀ (x + a)) := by
  rcases h with ⟨δ, hδ, hδle⟩
  refine ⟨δ, hδ, ?_⟩
  exact
    (tendsto_atBot_add_const_right atBot a tendsto_id).eventually hδle

def HasInitialDatum (u : ℝ → ℝ → ℝ) (u₀ : ℝ → ℝ) : Prop :=
  ∀ x, u 0 x = u₀ x

def IsGlobalCauchySolutionFrom
    (p : CMParams) (u₀ : ℝ → ℝ) (u v : ℝ → ℝ → ℝ) : Prop :=
  IsGlobalClassicalSolution p u v ∧
    HasInitialDatum u u₀ ∧
    ∀ t x, 0 ≤ t → 0 < u t x

def UniformEventuallyBounded (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ M, ∀ᶠ t in atTop, ∀ x, |u t x| ≤ M

def UniformLimsupLe (u : ℝ → ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ t in atTop, ∀ x, u t x ≤ L + ε

def UniformConvergesToConstant (u : ℝ → ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ T, ∀ t x, T ≤ t → |u t x - a| < ε

theorem UniformEventuallyBounded.shift_space
    {u : ℝ → ℝ → ℝ} (h : UniformEventuallyBounded u) (a : ℝ) :
    UniformEventuallyBounded (fun t x => u t (x + a)) := by
  rcases h with ⟨M, hM⟩
  exact ⟨M, hM.mono fun _t ht x => ht (x + a)⟩

theorem UniformLimsupLe.shift_space
    {u : ℝ → ℝ → ℝ} {L : ℝ} (h : UniformLimsupLe u L) (a : ℝ) :
    UniformLimsupLe (fun t x => u t (x + a)) L := by
  intro ε hε
  exact (h ε hε).mono fun _t ht x => ht (x + a)

theorem UniformConvergesToConstant.shift_space
    {u : ℝ → ℝ → ℝ} {b : ℝ} (h : UniformConvergesToConstant u b) (a : ℝ) :
    UniformConvergesToConstant (fun t x => u t (x + a)) b := by
  intro ε hε
  rcases h ε hε with ⟨T, hT⟩
  exact ⟨T, fun t x ht => hT t (x + a) ht⟩

theorem UniformConvergesToConstant.uniformLimsupLe
    {u : ℝ → ℝ → ℝ} {a : ℝ} (h : UniformConvergesToConstant u a) :
    UniformLimsupLe u a := by
  intro ε hε
  rcases h ε hε with ⟨T, hT⟩
  refine eventually_atTop.2 ⟨T, ?_⟩
  intro t ht x
  have hlt : u t x - a < ε :=
    lt_of_le_of_lt (le_abs_self (u t x - a)) (hT t x ht)
  linarith

theorem UniformConvergesToConstant.uniformEventuallyBounded
    {u : ℝ → ℝ → ℝ} {a : ℝ} (h : UniformConvergesToConstant u a) :
    UniformEventuallyBounded u := by
  rcases h 1 (by norm_num) with ⟨T, hT⟩
  refine ⟨|a| + 1, eventually_atTop.2 ⟨T, ?_⟩⟩
  intro t ht x
  have hdist : |u t x - a| < 1 := hT t x ht
  have htri : |u t x| ≤ |u t x - a| + |a| := by
    calc
      |u t x| = |(u t x - a) + a| := by ring_nf
      _ ≤ |u t x - a| + |a| := abs_add_le _ _
  linarith

def HasWaveRightTailAsymptotic (c κ₁ : ℝ) (U : ℝ → ℝ) : Prop :=
  Tendsto
    (fun x => Real.exp ((κ₁ - kappa c) * x) *
      (U x / Real.exp (-(kappa c) * x) - 1))
    atTop (𝓝 0)

theorem HasWaveRightTailAsymptotic.ratio_tendsto_one
    {c κ₁ : ℝ} {U : ℝ → ℝ}
    (h : HasWaveRightTailAsymptotic c κ₁ U) (hκ₁ : kappa c < κ₁) :
    Tendsto (fun x => U x / Real.exp (-(kappa c) * x)) atTop (𝓝 1) := by
  have hcoef : 0 < κ₁ - kappa c := sub_pos.mpr hκ₁
  have hexp_atTop :
      Tendsto (fun x : ℝ => Real.exp ((κ₁ - kappa c) * x)) atTop atTop := by
    have hmul : Tendsto (fun x : ℝ => (κ₁ - kappa c) * x) atTop atTop :=
      (Filter.tendsto_id.atTop_mul_const hcoef).congr
        (fun x => mul_comm x (κ₁ - kappa c))
    exact Real.tendsto_exp_atTop.comp hmul
  have hinv :
      Tendsto (fun x : ℝ => (Real.exp ((κ₁ - kappa c) * x))⁻¹)
        atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hexp_atTop
  have hminus :
      Tendsto
        (fun x => U x / Real.exp (-(kappa c) * x) - 1)
        atTop (𝓝 0) := by
    have hprod := h.mul hinv
    convert hprod using 1
    · ext x
      field_simp [Real.exp_ne_zero]
    · simp
  simpa [sub_eq_add_neg] using hminus.add_const 1

theorem HasWaveRightTailAsymptotic.tendsto_atTop_zero
    {c κ₁ : ℝ} {U : ℝ → ℝ}
    (h : HasWaveRightTailAsymptotic c κ₁ U)
    (hk : 0 < kappa c) (hκ₁ : kappa c < κ₁) :
    Tendsto U atTop (𝓝 0) := by
  have hratio := h.ratio_tendsto_one hκ₁
  have hmul : Tendsto (fun x : ℝ => kappa c * x) atTop atTop :=
    (Filter.tendsto_id.atTop_mul_const hk).congr
      (fun x => mul_comm x (kappa c))
  have hexp : Tendsto (fun x : ℝ => Real.exp (-(kappa c * x))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp hmul)
  have hprod := hratio.mul hexp
  convert hprod using 1
  · ext x
    field_simp [Real.exp_ne_zero]
  · simp

def positiveSensitivityExtendedThreshold (p : CMParams) : ℝ :=
  (2 * p.m + 2 * p.γ) / (p.m ^ 2 + p.m + 2 * p.γ)

theorem positiveSensitivityExtendedThreshold_pos (p : CMParams) :
    0 < positiveSensitivityExtendedThreshold p := by
  unfold positiveSensitivityExtendedThreshold
  have hnum : 0 < 2 * p.m + 2 * p.γ := by
    nlinarith [p.hm, p.hγ]
  have hden : 0 < p.m ^ 2 + p.m + 2 * p.γ := by
    nlinarith [p.hm, p.hγ, sq_nonneg p.m]
  exact div_pos hnum hden

/-- A weaker traveling-wave target used in Paper1 Remark 1.3(2) and
Remark 4.3(2): the right end converges to `(0,0)`, while the left end is only
bounded away from zero and may be oscillatory. -/
structure IsRightVanishingTravelingWave
    (p : CMParams) (c : ℝ) (U V : ℝ → ℝ) : Prop where
  hc : 0 < c
  U_pos : ∀ x, 0 < U x
  ode_U : ∀ x,
    iteratedDeriv 2 U x + c * deriv U x
    - p.χ * deriv (fun y => (U y) ^ p.m * deriv V y) x
    + U x * (1 - (U x) ^ p.α) = 0
  ode_V : ∀ x, iteratedDeriv 2 V x - V x + (U x) ^ p.γ = 0
  lim_pos_inf : Tendsto U atTop (𝓝 0) ∧ Tendsto V atTop (𝓝 0)
  positive_at_left : StrictlyPositiveAtLeft U

theorem IsTravelingWave.to_rightVanishingTravelingWave
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (h : IsTravelingWave p c U V) :
    IsRightVanishingTravelingWave p c U V :=
  { hc := h.hc
    U_pos := h.U_pos
    ode_U := h.ode_U
    ode_V := h.ode_V
    lim_pos_inf := h.lim_pos_inf
    positive_at_left := by
      refine ⟨1 / 2, by norm_num, ?_⟩
      have hnhds : Set.Ioi (1 / 2 : ℝ) ∈ 𝓝 (1 : ℝ) :=
        Ioi_mem_nhds (by norm_num)
      filter_upwards [h.lim_neg_inf.1 hnhds] with x hx
      exact le_of_lt hx }

theorem IsRightVanishingTravelingWave.shift
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsRightVanishingTravelingWave p c U V) (a : ℝ) :
    IsRightVanishingTravelingWave p c
      (fun x => U (x + a)) (fun x => V (x + a)) := by
  refine
    { hc := hTW.hc
      U_pos := fun x => hTW.U_pos (x + a)
      ode_U := ?_
      ode_V := ?_
      lim_pos_inf := ?_
      positive_at_left := hTW.positive_at_left.shift a }
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
      ⟨hTW.lim_pos_inf.1.comp
          (tendsto_atTop_add_const_right atTop a tendsto_id),
        hTW.lim_pos_inf.2.comp
          (tendsto_atTop_add_const_right atTop a tendsto_id)⟩

theorem IsRightVanishingTravelingWave.to_movingFrame_global_classical_solution
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsRightVanishingTravelingWave p c U V)
    (hU_diff : ContDiff ℝ 2 U) (hV_diff : ContDiff ℝ 2 V) :
    IsGlobalClassicalSolution p
      (fun t x => U (x - c * t)) (fun t x => V (x - c * t)) := by
  have hU_d : Differentiable ℝ U := hU_diff.differentiable two_ne_zero
  have hV_d : Differentiable ℝ V := hV_diff.differentiable two_ne_zero
  intro T hT
  exact {
    hT := hT
    u_smooth := fun t x _ _ => ⟨
      (hU_d _).comp _ ((differentiableAt_const x).sub
        ((differentiableAt_const c).mul differentiableAt_id)),
      (hU_d _).comp _ (differentiableAt_id.sub (differentiableAt_const _))⟩
    v_smooth := fun t x _ _ =>
      (hV_d _).comp _ (differentiableAt_id.sub (differentiableAt_const _))
    pde_u := fun t x _ _ => by
      have hinner : HasDerivAt (fun t' => x - c * t') (-c) t := by
        have := (hasDerivAt_const t x).sub ((hasDerivAt_id t).const_mul c)
        simpa using this
      have htime :
          deriv (fun t' => U (x - c * t')) t = deriv U (x - c * t) * (-c) :=
        ((hU_d _).hasDerivAt.comp t hinner).deriv
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

theorem IsRightVanishingTravelingWave.to_global_classical_solution
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsRightVanishingTravelingWave p c U V)
    (hU_diff : ContDiff ℝ 2 U) (hV_diff : ContDiff ℝ 2 V) :
    ∃ u v : ℝ → ℝ → ℝ, IsGlobalClassicalSolution p u v :=
  ⟨fun t x => U (x - c * t), fun t x => V (x - c * t),
    hTW.to_movingFrame_global_classical_solution hU_diff hV_diff⟩

theorem IsRightVanishingTravelingWave.strictlyPositiveAtLeft
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsRightVanishingTravelingWave p c U V) :
    StrictlyPositiveAtLeft U :=
  hTW.positive_at_left

theorem IsRightVanishingTravelingWave.eventually_pos_atLeft
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsRightVanishingTravelingWave p c U V) :
    ∀ᶠ x in atBot, 0 < U x :=
  hTW.positive_at_left.eventually_pos

theorem IsRightVanishingTravelingWave.nonnegativeInitialDatum
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsRightVanishingTravelingWave p c U V) (hU : IsCUnifBdd U) :
    NonnegativeInitialDatum U :=
  ⟨hU, fun x => (hTW.U_pos x).le⟩

theorem IsRightVanishingTravelingWave.to_globalCauchySolutionFrom
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsRightVanishingTravelingWave p c U V)
    (hU_diff : ContDiff ℝ 2 U) (hV_diff : ContDiff ℝ 2 V) :
    IsGlobalCauchySolutionFrom p U
      (fun t x => U (x - c * t)) (fun t x => V (x - c * t)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hTW.to_movingFrame_global_classical_solution hU_diff hV_diff
  · intro x
    simp
  · intro t x _ht
    exact hTW.U_pos (x - c * t)

def ShenUpperBoundNegative (c : ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ x, 0 < U x ∧ U x < max 1 (Real.exp (-(kappa c) * x))

theorem ShenUpperBoundNegative.pos
    {c : ℝ} {U : ℝ → ℝ} (h : ShenUpperBoundNegative c U) (x : ℝ) :
    0 < U x :=
  (h x).1

theorem ShenUpperBoundNegative.lt_max
    {c : ℝ} {U : ℝ → ℝ} (h : ShenUpperBoundNegative c U) (x : ℝ) :
    U x < max 1 (Real.exp (-(kappa c) * x)) :=
  (h x).2

theorem ShenUpperBoundNegative.shift_right
    {c a : ℝ} {U : ℝ → ℝ}
    (h : ShenUpperBoundNegative c U) (hk : 0 ≤ kappa c) (ha : 0 ≤ a) :
    ShenUpperBoundNegative c (fun x => U (x + a)) := by
  intro x
  refine ⟨h.pos (x + a), ?_⟩
  have hle_exp :
      Real.exp (-(kappa c) * (x + a)) ≤ Real.exp (-(kappa c) * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hk ha]
  have hle_max :
      max 1 (Real.exp (-(kappa c) * (x + a))) ≤
      max 1 (Real.exp (-(kappa c) * x)) := by
    exact max_le (le_max_left _ _) (hle_exp.trans (le_max_right _ _))
  exact (h.lt_max (x + a)).trans_le hle_max

theorem ShenUpperBoundNegative.shift_right_of_cStarLower_lt
    {p : CMParams} {c a : ℝ} {U : ℝ → ℝ}
    (h : ShenUpperBoundNegative c U) (hc : cStarLower p < c) (ha : 0 ≤ a) :
    ShenUpperBoundNegative c (fun x => U (x + a)) :=
  h.shift_right (kappa_pos_of_cStarLower_lt hc).le ha

theorem ShenUpperBoundNegative.nonneg
    {c : ℝ} {U : ℝ → ℝ} (h : ShenUpperBoundNegative c U) (x : ℝ) :
    0 ≤ U x :=
  (h.pos x).le

def ShenUpperBoundPositive (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ x, 0 < U x ∧
    U x < min ((1 / (1 - p.χ)) ^ (1 / p.α)) (Real.exp (-(kappa c) * x))

theorem ShenUpperBoundPositive.pos
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : ShenUpperBoundPositive p c U) (x : ℝ) :
    0 < U x :=
  (h x).1

theorem ShenUpperBoundPositive.nonneg
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : ShenUpperBoundPositive p c U) (x : ℝ) :
    0 ≤ U x :=
  (h.pos x).le

theorem ShenUpperBoundPositive.lt_constant
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : ShenUpperBoundPositive p c U) (x : ℝ) :
    U x < (1 / (1 - p.χ)) ^ (1 / p.α) :=
  lt_of_lt_of_le (h x).2 (min_le_left _ _)

theorem ShenUpperBoundPositive.le_constant
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : ShenUpperBoundPositive p c U) (x : ℝ) :
    U x ≤ (1 / (1 - p.χ)) ^ (1 / p.α) :=
  (h.lt_constant x).le

theorem ShenUpperBoundPositive.lt_exp
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : ShenUpperBoundPositive p c U) (x : ℝ) :
    U x < Real.exp (-(kappa c) * x) :=
  lt_of_lt_of_le (h x).2 (min_le_right _ _)

theorem ShenUpperBoundPositive.le_exp
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : ShenUpperBoundPositive p c U) (x : ℝ) :
    U x ≤ Real.exp (-(kappa c) * x) :=
  (h.lt_exp x).le

theorem ShenUpperBoundPositive.shift_right
    {p : CMParams} {c a : ℝ} {U : ℝ → ℝ}
    (h : ShenUpperBoundPositive p c U) (hk : 0 ≤ kappa c) (ha : 0 ≤ a) :
    ShenUpperBoundPositive p c (fun x => U (x + a)) := by
  intro x
  refine ⟨h.pos (x + a), ?_⟩
  apply lt_min
  · exact h.lt_constant (x + a)
  · have hle_exp :
        Real.exp (-(kappa c) * (x + a)) ≤ Real.exp (-(kappa c) * x) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hk ha]
    exact (h.lt_exp (x + a)).trans_le hle_exp

theorem ShenUpperBoundPositive.shift_right_of_two_lt
    {p : CMParams} {c a : ℝ} {U : ℝ → ℝ}
    (h : ShenUpperBoundPositive p c U) (hc : 2 < c) (ha : 0 ≤ a) :
    ShenUpperBoundPositive p c (fun x => U (x + a)) :=
  h.shift_right (kappa_pos_of_two_lt hc).le ha

def WeightedL2InitialCloseness (η : ℝ) (u₀ U : ℝ → ℝ) : Prop :=
  Integrable (fun x : ℝ => Real.exp (2 * η * x) * |u₀ x - U x| ^ 2)

def WeightedL2MovingFrameConvergence
    (η c : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) : Prop :=
  Tendsto
    (fun t : ℝ =>
      ∫ x : ℝ, Real.exp (2 * η * x) * |u t x - U (x - c * t)| ^ 2)
    atTop (𝓝 0)

def UniformMovingFrameConvergence
    (c : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ T, ∀ t x, T ≤ t → |u t x - U (x - c * t)| < ε

theorem IsRightVanishingTravelingWave.weightedL2MovingFrameConvergence_self
    {p : CMParams} {c η : ℝ} {U V : ℝ → ℝ}
    (_hTW : IsRightVanishingTravelingWave p c U V) :
    WeightedL2MovingFrameConvergence η c (fun t x => U (x - c * t)) U := by
  simp [WeightedL2MovingFrameConvergence]

theorem IsRightVanishingTravelingWave.uniformMovingFrameConvergence_self
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (_hTW : IsRightVanishingTravelingWave p c U V) :
    UniformMovingFrameConvergence c (fun t x => U (x - c * t)) U := by
  intro ε hε
  exact ⟨0, fun _t _x _ht => by simpa using hε⟩

theorem UniformMovingFrameConvergence.profile_eq_of_movingFrame
    {c : ℝ} {U W : ℝ → ℝ}
    (h : UniformMovingFrameConvergence c (fun t x => W (x - c * t)) U) :
    ∀ x, W x = U x := by
  intro y
  by_contra hne
  have hdist_pos : 0 < |W y - U y| :=
    abs_pos.mpr (sub_ne_zero.mpr hne)
  rcases h (|W y - U y| / 2) (by positivity) with ⟨T, hT⟩
  let t : ℝ := T
  let x : ℝ := y + c * T
  have hx : x - c * t = y := by
    dsimp [x, t]
    ring
  have hlt := hT t x le_rfl
  simp [t, x, hx] at hlt
  linarith [abs_nonneg (W y - U y)]

theorem WeightedL2InitialCloseness.refl
    (η : ℝ) (U : ℝ → ℝ) :
    WeightedL2InitialCloseness η U U := by
  simp [WeightedL2InitialCloseness]

theorem WeightedL2InitialCloseness.symm
    {η : ℝ} {u₀ U : ℝ → ℝ}
    (h : WeightedL2InitialCloseness η u₀ U) :
    WeightedL2InitialCloseness η U u₀ := by
  unfold WeightedL2InitialCloseness at h ⊢
  convert h using 1
  ext x
  rw [abs_sub_comm]

theorem IsGlobalCauchySolutionFrom.classical
    {p : CMParams} {u₀ : ℝ → ℝ} {u v : ℝ → ℝ → ℝ}
    (h : IsGlobalCauchySolutionFrom p u₀ u v) :
    IsGlobalClassicalSolution p u v :=
  h.1

theorem IsGlobalCauchySolutionFrom.initial
    {p : CMParams} {u₀ : ℝ → ℝ} {u v : ℝ → ℝ → ℝ}
    (h : IsGlobalCauchySolutionFrom p u₀ u v) :
    HasInitialDatum u u₀ :=
  h.2.1

theorem IsGlobalCauchySolutionFrom.pos
    {p : CMParams} {u₀ : ℝ → ℝ} {u v : ℝ → ℝ → ℝ}
    (h : IsGlobalCauchySolutionFrom p u₀ u v) :
    ∀ t x, 0 ≤ t → 0 < u t x :=
  h.2.2

theorem IsGlobalCauchySolutionFrom.initial_pos
    {p : CMParams} {u₀ : ℝ → ℝ} {u v : ℝ → ℝ → ℝ}
    (h : IsGlobalCauchySolutionFrom p u₀ u v) (x : ℝ) :
    0 < u₀ x := by
  rw [← h.initial x]
  exact h.pos 0 x le_rfl

theorem IsGlobalCauchySolutionFrom.shift_space
    {p : CMParams} {u₀ : ℝ → ℝ} {u v : ℝ → ℝ → ℝ}
    (h : IsGlobalCauchySolutionFrom p u₀ u v) (a : ℝ) :
    IsGlobalCauchySolutionFrom p (fun x => u₀ (x + a))
      (fun t x => u t (x + a)) (fun t x => v t (x + a)) := by
  refine ⟨_root_.IsGlobalClassicalSolution.shift_space h.classical a, ?_, ?_⟩
  · intro x
    exact h.initial (x + a)
  · intro t x ht
    exact h.pos t (x + a) ht

theorem IsTravelingWave.strictlyPositiveAtLeft
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V) :
    StrictlyPositiveAtLeft U := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  have hnhds : Set.Ioi (1 / 2 : ℝ) ∈ 𝓝 (1 : ℝ) :=
    Ioi_mem_nhds (by norm_num)
  filter_upwards [hTW.lim_neg_inf.1 hnhds] with x hx
  exact le_of_lt hx

theorem IsTravelingWave.nonnegativeInitialDatum
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V) (hU : IsCUnifBdd U) :
    NonnegativeInitialDatum U :=
  ⟨hU, fun x => (hTW.U_pos x).le⟩

theorem IsTravelingWave.to_globalCauchySolutionFrom
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hU_diff : ContDiff ℝ 2 U) (hV_diff : ContDiff ℝ 2 V) :
    IsGlobalCauchySolutionFrom p U
      (fun t x => U (x - c * t)) (fun t x => V (x - c * t)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact _root_.IsTravelingWave.to_movingFrame_global_classical_solution
      p hTW hU_diff hV_diff
  · intro x
    simp
  · intro t x _ht
    exact hTW.U_pos (x - c * t)

theorem IsTravelingWave.weightedL2MovingFrameConvergence_self
    {p : CMParams} {c η : ℝ} {U V : ℝ → ℝ}
    (_hTW : IsTravelingWave p c U V) :
    WeightedL2MovingFrameConvergence η c (fun t x => U (x - c * t)) U := by
  simp [WeightedL2MovingFrameConvergence]

theorem IsTravelingWave.uniformMovingFrameConvergence_self
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (_hTW : IsTravelingWave p c U V) :
    UniformMovingFrameConvergence c (fun t x => U (x - c * t)) U := by
  intro ε hε
  exact ⟨0, fun _t _x _ht => by simpa using hε⟩

structure HeatSemigroupEstimateData where
  lpNorm : ℝ → (ℝ → ℝ) → ℝ
  lqNorm : ℝ → (ℝ → ℝ) → ℝ
  linftyNorm : (ℝ → ℝ) → ℝ
  gradientNorm : ℝ → (ℝ → ℝ) → ℝ
  semigroup : ℝ → (ℝ → ℝ) → ℝ → ℝ
  divergenceSemigroup : ℝ → (ℝ → ℝ) → ℝ → ℝ

def Lemma_2_1 (S : HeatSemigroupEstimateData) : Prop :=
  ∀ p q : ℝ, 1 < p → p ≤ q →
    (∃ Cpq > 0, ∀ t > 0, ∀ u : ℝ → ℝ,
      S.lqNorm q (S.semigroup t u) ≤
        Cpq * t ^ (-(1 / 2 : ℝ) * (1 / p - 1 / q)) *
          Real.exp (-t) * S.lpNorm p u) ∧
    (∃ Cpq > 0, ∀ t > 0, ∀ u : ℝ → ℝ,
      S.gradientNorm q (S.semigroup t u) ≤
        Cpq * t ^ (-(1 / 2 : ℝ) - (1 / 2 : ℝ) * (1 / p - 1 / q)) *
          Real.exp (-t) * S.lpNorm p u) ∧
    (∃ Cp > 0, ∀ t > 0, ∀ u : ℝ → ℝ,
      S.linftyNorm (S.divergenceSemigroup t u) ≤
        Cp * t ^ (-(1 / 2 : ℝ) - (1 / (2 * p))) *
          Real.exp (-t) * S.lpNorm p u)

theorem Lemma_2_1.semigroup_lp_lq
    {S : HeatSemigroupEstimateData}
    (h : Lemma_2_1 S)
    {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) :
    ∃ Cpq > 0, ∀ t > 0, ∀ u : ℝ → ℝ,
      S.lqNorm q (S.semigroup t u) ≤
        Cpq * t ^ (-(1 / 2 : ℝ) * (1 / p - 1 / q)) *
          Real.exp (-t) * S.lpNorm p u :=
  (h p q hp hpq).1

theorem Lemma_2_1.gradient_lp_lq
    {S : HeatSemigroupEstimateData}
    (h : Lemma_2_1 S)
    {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) :
    ∃ Cpq > 0, ∀ t > 0, ∀ u : ℝ → ℝ,
      S.gradientNorm q (S.semigroup t u) ≤
        Cpq * t ^ (-(1 / 2 : ℝ) - (1 / 2 : ℝ) * (1 / p - 1 / q)) *
          Real.exp (-t) * S.lpNorm p u :=
  (h p q hp hpq).2.1

theorem Lemma_2_1.divergence_linf
    {S : HeatSemigroupEstimateData}
    (h : Lemma_2_1 S)
    {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) :
    ∃ Cp > 0, ∀ t > 0, ∀ u : ℝ → ℝ,
      S.linftyNorm (S.divergenceSemigroup t u) ≤
        Cp * t ^ (-(1 / 2 : ℝ) - (1 / (2 * p))) *
          Real.exp (-t) * S.lpNorm p u :=
  (h p q hp hpq).2.2

def PsiDerivativeFormula (u : ℝ → ℝ) (l mu : ℝ) : Prop :=
  ∀ x,
    deriv (fun z => Psi u l mu z) x =
      (-(mu / 2) * Real.exp (-Real.sqrt l * x) *
          (∫ y in Set.Iic x, Real.exp (Real.sqrt l * y) * u y))
        + ((mu / 2) * Real.exp (Real.sqrt l * x) *
          (∫ y in Set.Ioi x, Real.exp (-Real.sqrt l * y) * u y))

def Lemma_2_2 : Prop :=
  ∀ u : ℝ → ℝ, ∀ l mu : ℝ, 0 < l → 0 < mu → IsCUnifBdd u →
    (∀ x,
      Psi u l mu x =
        mu / (2 * Real.sqrt l) *
          ∫ y : ℝ, Real.exp (-Real.sqrt l * |x - y|) * u y) ∧
    PsiDerivativeFormula u l mu

theorem Lemma_2_2.kernel_formula
    (h : Lemma_2_2)
    {u : ℝ → ℝ} {l mu : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hu : IsCUnifBdd u) :
    ∀ x,
      Psi u l mu x =
        mu / (2 * Real.sqrt l) *
          ∫ y : ℝ, Real.exp (-Real.sqrt l * |x - y|) * u y :=
  (h u l mu hl hmu hu).1

theorem Lemma_2_2.derivative_formula
    (h : Lemma_2_2)
    {u : ℝ → ℝ} {l mu : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hu : IsCUnifBdd u) :
    PsiDerivativeFormula u l mu :=
  (h u l mu hl hmu hu).2

theorem Psi_kernel_integrable_of_isCUnifBdd
    {u : ℝ → ℝ} {l : ℝ}
    (hl : 0 < l) (hu : IsCUnifBdd u) (x : ℝ) :
    Integrable
      (fun y : ℝ => Real.exp (-Real.sqrt l * |x - y|) * u y) := by
  rcases hu.2 with ⟨M, hM⟩
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (u 0)) (hM 0)
  exact _root_.psi_kernel_mul_bounded_integrable hl hM_nonneg hM x
    hu.1.aestronglyMeasurable

theorem Lemma_2_2_kernel_formula_proved :
    ∀ u : ℝ → ℝ, ∀ l mu : ℝ, 0 < l → 0 < mu → IsCUnifBdd u →
      ∀ x,
        Psi u l mu x =
          mu / (2 * Real.sqrt l) *
            ∫ y : ℝ, Real.exp (-Real.sqrt l * |x - y|) * u y := by
  intro u l mu _hl _hmu _hu x
  rfl

theorem Lemma_2_2_derivative_formula_proved :
    ∀ u : ℝ → ℝ, ∀ l mu : ℝ, 0 < l → 0 < mu → IsCUnifBdd u →
      PsiDerivativeFormula u l mu := by
  intro u l mu hl hmu hu
  exact Psi_derivative_formula_general hl hmu hu

theorem Lemma_2_2_proved : Lemma_2_2 := by
  intro u l mu hl hmu hu
  exact
    ⟨Lemma_2_2_kernel_formula_proved u l mu hl hmu hu,
      Lemma_2_2_derivative_formula_proved u l mu hl hmu hu⟩

def Lemma_2_3 : Prop :=
  ∀ u : ℝ → ℝ, ∀ l mu : ℝ, 0 < l → 0 < mu → IsCUnifBdd u →
    (∀ x, 0 ≤ u x) →
      ∀ x, |deriv (fun z => Psi u l mu z) x| ≤ Real.sqrt l * Psi u l mu x

theorem Lemma_2_3.derivative_bound
    (h : Lemma_2_3)
    {u : ℝ → ℝ} {l mu : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hu : IsCUnifBdd u)
    (hu_nonneg : ∀ x, 0 ≤ u x) :
    ∀ x, |deriv (fun z => Psi u l mu z) x| ≤ Real.sqrt l * Psi u l mu x :=
  h u l mu hl hmu hu hu_nonneg

theorem Lemma_2_3_proved : Lemma_2_3 := by
  intro u l mu hl hmu hu hu_nonneg x
  exact Psi_deriv_abs_le_general hl hmu hu hu_nonneg x

theorem Lemma_2_3_of_Lemma_2_2 (h22 : Lemma_2_2) : Lemma_2_3 := by
  intro u l mu hl hmu hu hu_nonneg x
  let a : ℝ := Real.sqrt l
  have ha : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.mpr hl
  let A : ℝ :=
    Real.exp (-a * x) * ∫ y in Set.Iic x, Real.exp (a * y) * u y
  let B : ℝ :=
    Real.exp (a * x) * ∫ y in Set.Ioi x, Real.exp (-a * y) * u y
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (Real.exp_nonneg _)
      (MeasureTheory.integral_nonneg
        (fun y => mul_nonneg (Real.exp_nonneg _) (hu_nonneg y)))
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (Real.exp_nonneg _)
      (MeasureTheory.integral_nonneg
        (fun y => mul_nonneg (Real.exp_nonneg _) (hu_nonneg y)))
  have hder :
      deriv (fun z => Psi u l mu z) x =
        -(mu / 2) * A + (mu / 2) * B := by
    have h := (h22.derivative_formula hl hmu hu) x
    simpa [A, B, a, mul_assoc, mul_left_comm, mul_comm] using h
  have habs :
      |deriv (fun z => Psi u l mu z) x| ≤ (mu / 2) * (A + B) := by
    rw [hder]
    have hmu2_nonneg : 0 ≤ mu / 2 := by positivity
    have htermA : |-(mu / 2) * A| = (mu / 2) * A := by
      rw [show -(mu / 2) * A = -((mu / 2) * A) by ring]
      rw [abs_neg, abs_of_nonneg (mul_nonneg hmu2_nonneg hA_nonneg)]
    have htermB : |(mu / 2) * B| = (mu / 2) * B := by
      rw [abs_of_nonneg (mul_nonneg hmu2_nonneg hB_nonneg)]
    calc
      |-(mu / 2) * A + (mu / 2) * B|
          ≤ |-(mu / 2) * A| + |(mu / 2) * B| := abs_add_le _ _
      _ = (mu / 2) * A + (mu / 2) * B := by
            rw [htermA, htermB]
      _ = (mu / 2) * (A + B) := by ring
  have hiu :
      Integrable
        (fun y : ℝ => Real.exp (-a * |x - y|) * u y) := by
    dsimp [a]
    simpa using Psi_kernel_integrable_of_isCUnifBdd hl hu x
  have hkernel_split :
      (∫ y : ℝ, Real.exp (-a * |x - y|) * u y) = A + B := by
    have hsplit :=
      MeasureTheory.integral_add_compl (s := Set.Iic x) measurableSet_Iic hiu
    simp only [Set.compl_Iic] at hsplit
    have hleft :
        ∫ y in Set.Iic x, Real.exp (-a * |x - y|) * u y = A := by
      have hleft_eq :
          Set.EqOn
            (fun y : ℝ => Real.exp (-a * |x - y|) * u y)
            (fun y : ℝ => Real.exp (-a * x) * (Real.exp (a * y) * u y))
            (Set.Iic x) := by
        intro y hy
        have hyx : y ≤ x := by simpa using hy
        change
          Real.exp (-a * |x - y|) * u y =
            Real.exp (-a * x) * (Real.exp (a * y) * u y)
        rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
        rw [show -a * (x - y) = -a * x + a * y by ring, Real.exp_add]
        ring_nf
      calc
        ∫ y in Set.Iic x, Real.exp (-a * |x - y|) * u y
            = ∫ y in Set.Iic x,
                Real.exp (-a * x) * (Real.exp (a * y) * u y) := by
              exact MeasureTheory.setIntegral_congr_fun measurableSet_Iic hleft_eq
        _ = Real.exp (-a * x) * ∫ y in Set.Iic x, Real.exp (a * y) * u y := by
              exact MeasureTheory.integral_const_mul _ _
        _ = A := by rfl
    have hright :
        ∫ y in Set.Ioi x, Real.exp (-a * |x - y|) * u y = B := by
      have hright_eq :
          Set.EqOn
            (fun y : ℝ => Real.exp (-a * |x - y|) * u y)
            (fun y : ℝ => Real.exp (a * x) * (Real.exp (-a * y) * u y))
            (Set.Ioi x) := by
        intro y hy
        have hxy : x < y := by simpa using hy
        change
          Real.exp (-a * |x - y|) * u y =
            Real.exp (a * x) * (Real.exp (-a * y) * u y)
        rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hxy))]
        rw [show -a * -(x - y) = a * x + -a * y by ring, Real.exp_add]
        ring_nf
      calc
        ∫ y in Set.Ioi x, Real.exp (-a * |x - y|) * u y
            = ∫ y in Set.Ioi x,
                Real.exp (a * x) * (Real.exp (-a * y) * u y) := by
              exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hright_eq
        _ = Real.exp (a * x) * ∫ y in Set.Ioi x, Real.exp (-a * y) * u y := by
              exact MeasureTheory.integral_const_mul _ _
        _ = B := by rfl
    calc
      ∫ y : ℝ, Real.exp (-a * |x - y|) * u y
          = (∫ y in Set.Iic x, Real.exp (-a * |x - y|) * u y) +
              (∫ y in Set.Ioi x, Real.exp (-a * |x - y|) * u y) := hsplit.symm
      _ = A + B := by rw [hleft, hright]
  have hpsi :
      Real.sqrt l * Psi u l mu x = (mu / 2) * (A + B) := by
    dsimp [a] at hkernel_split
    unfold Psi
    rw [hkernel_split]
    have hsqrt_pos : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
    field_simp [ne_of_gt hsqrt_pos]
  exact le_trans habs (le_of_eq hpsi.symm)

def Lemma_2_3_unit : Prop :=
  ∀ u : ℝ → ℝ, IsCUnifBdd u →
    (∀ x, 0 ≤ u x) →
      ∀ x, |deriv (Psi u 1 1) x| ≤ Psi u 1 1 x

theorem Lemma_2_3_unit_proved : Lemma_2_3_unit := by
  intro u hu hu_nonneg x
  rcases hu.2 with ⟨M, hM⟩
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (u 0)) (hM 0)
  have hint_raw :
      Integrable (fun y => Real.exp (-1 * |x - y|) * u y) :=
    kernel_mul_bounded_integrable u M hM_nonneg hM x hu.1.aestronglyMeasurable
  have hint :
      Integrable (fun y => Real.exp (-|x - y|) * u y) := by
    simpa using hint_raw
  exact Psi_deriv_abs_le' hu_nonneg x hint hu.1.aestronglyMeasurable

theorem Psi_one_mu_eq (u : ℝ → ℝ) (mu x : ℝ) :
    Psi u 1 mu x = mu * Psi u 1 1 x := by
  simp [Psi]
  ring

theorem Lemma_2_3_unit_mu_proved :
    ∀ u : ℝ → ℝ, ∀ mu : ℝ, 0 < mu → IsCUnifBdd u →
      (∀ x, 0 ≤ u x) →
        ∀ x, |deriv (Psi u 1 mu) x| ≤ Psi u 1 mu x := by
  intro u mu hmu hu hu_nonneg x
  have hderiv :
      deriv (Psi u 1 mu) x = mu * deriv (Psi u 1 1) x := by
    rw [show Psi u 1 mu = fun z => mu * Psi u 1 1 z from by
      ext z
      exact Psi_one_mu_eq u mu z]
    rw [deriv_const_mul_field]
  rw [hderiv, Psi_one_mu_eq u mu x]
  rw [abs_mul, abs_of_pos hmu]
  exact mul_le_mul_of_nonneg_left
    (Lemma_2_3_unit_proved u hu hu_nonneg x) hmu.le

def Lemma_2_4 : Prop :=
  ∀ M k : ℝ, 1 ≤ M → 0 < k → k < 1 →
    ∀ u : ℝ → ℝ, IsCUnifBdd u →
      (∀ x, 0 ≤ u x) →
      (∀ x, u x ≤ min M (Real.exp (-k * x))) →
        ∀ x, Psi u 1 1 x ≤ min M (1 / (1 - k ^ 2) * Real.exp (-k * x))

theorem Lemma_2_4_proved : Lemma_2_4 := by
  intro M k hM hk hk1 u hu hu_nonneg hu_bound x
  have hM_nonneg : 0 ≤ M := le_trans zero_le_one hM
  have huM : ∀ y, u y ≤ M := by
    intro y
    exact le_trans (hu_bound y) (min_le_left _ _)
  have huexp : ∀ y, u y ≤ Real.exp (-k * y) := by
    intro y
    exact le_trans (hu_bound y) (min_le_right _ _)
  exact
    Psi_le_min_const_exp_of_nonneg_le hM_nonneg hk hk1
      hu.1 hu_nonneg huM huexp x

structure ExponentialWeight where
  weight : ℝ → ℝ
  smooth : ContDiff ℝ 2 weight
  pos : ∀ x, 0 < weight x
  decay : ∃ k > 0, ∀ x, weight x ≤ Real.exp (-k * |x|)
  deriv_abs_le : ∃ k > 0, ∀ x, |deriv weight x| ≤ k * weight x
  second_deriv_abs_le : ∃ k > 0, ∀ x, |iteratedDeriv 2 weight x| ≤ k * weight x

def Lemma_2_5 : Prop :=
  ∀ pExp gamma l mu : ℝ, 1 < pExp → 0 < gamma → 0 < l → 0 < mu →
    ∃ C > 0, ∀ u : ℝ → ℝ, ∀ psi : ExponentialWeight,
      Integrable (fun x => (u x) ^ (gamma * pExp) * psi.weight x) →
        Integrable
          (fun x =>
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
              psi.weight x) ∧
        ∫ x : ℝ,
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
              psi.weight x
          ≤ C * ∫ x : ℝ, (u x) ^ (gamma * pExp) * psi.weight x

theorem Lemma_2_5.weighted_resolvent_gradient
    (h : Lemma_2_5)
    {pExp gamma l mu : ℝ}
    (hpExp : 1 < pExp) (hgamma : 0 < gamma) (hl : 0 < l) (hmu : 0 < mu) :
    ∃ C > 0, ∀ u : ℝ → ℝ, ∀ psi : ExponentialWeight,
      Integrable (fun x => (u x) ^ (gamma * pExp) * psi.weight x) →
        Integrable
          (fun x =>
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
              psi.weight x) ∧
        ∫ x : ℝ,
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
              psi.weight x
          ≤ C * ∫ x : ℝ, (u x) ^ (gamma * pExp) * psi.weight x :=
  h pExp gamma l mu hpExp hgamma hl hmu

theorem Lemma_2_5.weighted_resolvent_gradient_unit
    (h : Lemma_2_5) (p : CMParams) {pExp : ℝ} (hpExp : 1 < pExp) :
    ∃ C > 0, ∀ u : ℝ → ℝ, ∀ psi : ExponentialWeight,
      Integrable (fun x => (u x) ^ (p.γ * pExp) * psi.weight x) →
        Integrable
          (fun x =>
            |deriv (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^ pExp *
              psi.weight x) ∧
        ∫ x : ℝ,
            |deriv (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^ pExp *
              psi.weight x
          ≤ C * ∫ x : ℝ, (u x) ^ (p.γ * pExp) * psi.weight x :=
  h.weighted_resolvent_gradient hpExp
    (lt_of_lt_of_le one_pos p.hγ) one_pos one_pos

theorem Lemma_2_5.weighted_resolvent_gradient_unit_L2
    (h : Lemma_2_5) (p : CMParams) :
    ∃ C > 0, ∀ u : ℝ → ℝ, ∀ psi : ExponentialWeight,
      Integrable (fun x => (u x) ^ (p.γ * (2 : ℝ)) * psi.weight x) →
        Integrable
          (fun x =>
            |deriv (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^ (2 : ℝ) *
              psi.weight x) ∧
        ∫ x : ℝ,
            |deriv (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^ (2 : ℝ) *
              psi.weight x
          ≤ C * ∫ x : ℝ, (u x) ^ (p.γ * (2 : ℝ)) * psi.weight x :=
  h.weighted_resolvent_gradient_unit p (by norm_num : (1 : ℝ) < 2)

def frozenElliptic (p : CMParams) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun x => Psi (fun y => (u y) ^ p.γ) 1 1 x

theorem frozenElliptic_nonneg
    (p : CMParams) {u : ℝ → ℝ} (hu : ∀ x, 0 ≤ u x) (x : ℝ) :
    0 ≤ frozenElliptic p u x := by
  unfold frozenElliptic
  exact Psi_nonneg one_pos one_pos
    (fun y => Real.rpow_nonneg (hu y) p.γ) x

theorem frozenElliptic_le_of_rpow_le
    (p : CMParams) {u : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M)
    (hu_cont : Continuous u)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_rpow_le : ∀ x, (u x) ^ p.γ ≤ M) (x : ℝ) :
    frozenElliptic p u x ≤ M := by
  unfold frozenElliptic
  have hle := Psi_le_const_general_of_nonneg_le one_pos one_pos hM
    (hu_cont.rpow_const (fun _ => Or.inr (by linarith [p.hγ] : 0 ≤ p.γ)))
    (fun y => Real.rpow_nonneg (hu_nonneg y) p.γ)
    hu_rpow_le x
  simp [div_one] at hle
  exact hle

theorem frozenElliptic_le_one_of_le_one
    (p : CMParams) {u : ℝ → ℝ}
    (hu_cont : Continuous u)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le : ∀ x, u x ≤ 1) (x : ℝ) :
    frozenElliptic p u x ≤ 1 := by
  apply frozenElliptic_le_of_rpow_le p (by norm_num) hu_cont hu_nonneg
  intro y
  exact Real.rpow_le_one (hu_nonneg y) (hu_le y)
    (by linarith [p.hγ] : 0 ≤ p.γ)

theorem rpow_cunif_bdd_of_nonneg
    (p : CMParams) {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x) :
    IsCUnifBdd (fun y => (u y) ^ p.γ) := by
  rcases hu.2 with ⟨M, hM⟩
  have hγ_nonneg : 0 ≤ p.γ := by linarith [p.hγ]
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (u 0)) (hM 0)
  refine ⟨?_, ⟨M ^ p.γ, ?_⟩⟩
  · exact hu.1.rpow_const (fun y => Or.inr hγ_nonneg)
  · intro y
    rw [abs_of_nonneg (Real.rpow_nonneg (hu_nonneg y) p.γ)]
    exact Real.rpow_le_rpow (hu_nonneg y)
      (by simpa [abs_of_nonneg (hu_nonneg y)] using hM y) hγ_nonneg

theorem frozenElliptic_ode
    (p : CMParams) {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x) (x : ℝ) :
    iteratedDeriv 2 (frozenElliptic p u) x -
        frozenElliptic p u x + (u x) ^ p.γ = 0 := by
  unfold frozenElliptic
  simpa using
    (Psi_elliptic_ode (u := fun y => (u y) ^ p.γ) (l := 1) (mu := 1)
      one_pos one_pos (rpow_cunif_bdd_of_nonneg p hu hu_nonneg)
      (fun y => Real.rpow_nonneg (hu_nonneg y) p.γ) x)

theorem frozenElliptic_iteratedDeriv_two_eq
    (p : CMParams) {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x) (x : ℝ) :
    iteratedDeriv 2 (frozenElliptic p u) x =
        frozenElliptic p u x - (u x) ^ p.γ := by
  have h := frozenElliptic_ode p hu hu_nonneg x
  linarith

theorem frozenElliptic_deriv_deriv_eq
    (p : CMParams) {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x) (x : ℝ) :
    deriv (deriv (frozenElliptic p u)) x =
        frozenElliptic p u x - (u x) ^ p.γ := by
  simpa [iteratedDeriv_succ, iteratedDeriv_zero] using
    frozenElliptic_iteratedDeriv_two_eq p hu hu_nonneg x

theorem frozenElliptic_deriv_abs_le
    (p : CMParams) {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x) (x : ℝ) :
    |deriv (frozenElliptic p u) x| ≤ frozenElliptic p u x := by
  unfold frozenElliptic
  simpa using
    (Psi_deriv_abs_le_general
      (u := fun y => (u y) ^ p.γ) (l := 1) (mu := 1)
      one_pos one_pos (rpow_cunif_bdd_of_nonneg p hu hu_nonneg)
      (fun y => Real.rpow_nonneg (hu_nonneg y) p.γ) x)

def frozenWaveOperator (p : CMParams) (c : ℝ) (u W : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    iteratedDeriv 2 W x + c * deriv W x
      - p.χ *
        deriv (fun y => (W y) ^ p.m * deriv (frozenElliptic p u) y) x
      + W x * (1 - (W x) ^ p.α)

def paperWaveOperator (p : CMParams) (c : ℝ) (u W : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    let V := frozenElliptic p u
    iteratedDeriv 2 W x + c * deriv W x
      - p.χ * p.m * (W x) ^ (p.m - 1) * deriv V x * deriv W x
      + W x * (1 - p.χ * (W x) ^ (p.m - 1) * V x
        - ((W x) ^ p.α - p.χ * (W x) ^ (p.m + p.γ - 1)))

theorem paperWaveOperator_const_eq
    (p : CMParams) {c M : ℝ} {u : ℝ → ℝ}
    (_hu : IsCUnifBdd u) (_hu_nonneg : ∀ x, 0 ≤ u x) (x : ℝ) :
    paperWaveOperator p c u (fun _ => M) x =
      M * (1 - p.χ * M ^ (p.m - 1) * frozenElliptic p u x
        - (M ^ p.α - p.χ * M ^ (p.m + p.γ - 1))) := by
  unfold paperWaveOperator
  simp only [iteratedDeriv_const, deriv_const, show (2 : ℕ) ≠ 0 from by norm_num,
    ite_false, mul_zero, zero_add, add_zero, sub_zero]

/-- Stationary profile obtained after the frozen auxiliary fixed-point step.
This is the exact bridge object needed before producing an `IsTravelingWave`.
The hard analytic work is to prove these fields for the Schauder fixed point. -/
structure FrozenStationaryWaveProfile
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop where
  hc : 0 < c
  U_pos : ∀ x, 0 < U x
  stationary_eq : ∀ x, frozenWaveOperator p c U U x = 0
  elliptic_eq :
    ∀ x,
      iteratedDeriv 2 (frozenElliptic p U) x -
          frozenElliptic p U x + (U x) ^ p.γ = 0
  lim_neg_inf :
    Tendsto U atBot (𝓝 1) ∧ Tendsto (frozenElliptic p U) atBot (𝓝 1)
  lim_pos_inf :
    Tendsto U atTop (𝓝 0) ∧ Tendsto (frozenElliptic p U) atTop (𝓝 0)

theorem frozenElliptic_tendsto_atTop_of_U_tendsto
    (p : CMParams) {U : ℝ → ℝ}
    (hU : IsCUnifBdd U) (hU_nonneg : ∀ x, 0 ≤ U x)
    (hU_lim : Tendsto U atTop (𝓝 0)) :
    Tendsto (frozenElliptic p U) atTop (𝓝 0) := by
  have hγ_pos : 0 < p.γ := by linarith [p.hγ]
  let f : ℝ → ℝ := fun y => (U y) ^ p.γ
  have hf_lim : Tendsto (fun x => (U x) ^ p.γ) atTop (𝓝 0) := by
    have h0γ : (0 : ℝ) ^ p.γ = 0 := Real.zero_rpow (ne_of_gt hγ_pos)
    rw [← h0γ]
    exact hU_lim.rpow_const (Or.inr hγ_pos.le)
  have hf_lim' : Tendsto f atTop (𝓝 0) := by
    simpa [f] using hf_lim
  have hf_cunif : IsCUnifBdd f := by
    simpa [f] using rpow_cunif_bdd_of_nonneg p hU hU_nonneg
  rcases hU.2 with ⟨M, hM⟩
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (U 0)) (hM 0)
  let B : ℝ := M ^ p.γ
  have hB_nonneg : 0 ≤ B := Real.rpow_nonneg hM_nonneg p.γ
  have hf_bound : ∀ y, f y ≤ B := by
    intro y
    dsimp [f, B]
    exact Real.rpow_le_rpow (hU_nonneg y)
      (le_trans (le_abs_self (U y)) (hM y)) hγ_pos.le
  let F : ℝ → ℝ → ℝ := fun x z => (1 / 2 : ℝ) * (Real.exp (-|z|) * f (x + z))
  let bound : ℝ → ℝ := fun z => (1 / 2 : ℝ) * (Real.exp (-|z|) * B)
  have hbound_int : Integrable bound := by
    have hk0 :
        Integrable (fun z : ℝ => Real.exp (-1 * |0 - z|)) :=
      _root_.kernel_exp_neg_mul_abs_integrable (by norm_num : (0 : ℝ) < 1) 0
    have hk : Integrable (fun z : ℝ => Real.exp (-|z|)) := by
      convert hk0 using 1
      ext z
      rw [zero_sub, abs_neg]
      ring_nf
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using
      hk.const_mul ((1 / 2 : ℝ) * B)
  have hF_meas :
      ∀ᶠ x in atTop, AEStronglyMeasurable (F x) volume := by
    refine Eventually.of_forall ?_
    intro x
    have hcont_kernel : Continuous fun z : ℝ => Real.exp (-|z|) :=
      Real.continuous_exp.comp continuous_abs.neg
    have hcont_shift : Continuous fun z : ℝ => f (x + z) :=
      hf_cunif.1.comp (continuous_const.add continuous_id)
    exact (continuous_const.mul (hcont_kernel.mul hcont_shift)).aestronglyMeasurable
  have h_bound :
      ∀ᶠ x in atTop, ∀ᵐ z ∂volume, ‖F x z‖ ≤ bound z := by
    refine Eventually.of_forall ?_
    intro x
    refine Eventually.of_forall ?_
    intro z
    have hf_nonneg : 0 ≤ f (x + z) := by
      dsimp [f]
      exact Real.rpow_nonneg (hU_nonneg (x + z)) p.γ
    have hprod_nonneg : 0 ≤ Real.exp (-|z|) * f (x + z) :=
      mul_nonneg (Real.exp_nonneg _) hf_nonneg
    have hprod_le :
        Real.exp (-|z|) * f (x + z) ≤ Real.exp (-|z|) * B :=
      mul_le_mul_of_nonneg_left (hf_bound (x + z)) (Real.exp_nonneg _)
    dsimp [F, bound]
    rw [abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hprod_nonneg)]
    exact mul_le_mul_of_nonneg_left hprod_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h_lim :
      ∀ᵐ z ∂volume, Tendsto (fun x => F x z) atTop (𝓝 0) := by
    refine Eventually.of_forall ?_
    intro z
    have hshift : Tendsto (fun x : ℝ => x + z) atTop atTop :=
      tendsto_atTop_add_const_right atTop z tendsto_id
    have hf_shift : Tendsto (fun x : ℝ => f (x + z)) atTop (𝓝 0) :=
      hf_lim'.comp hshift
    have hconst :
        Tendsto (fun _x : ℝ => (1 / 2 : ℝ) * Real.exp (-|z|)) atTop
          (𝓝 ((1 / 2 : ℝ) * Real.exp (-|z|))) :=
      tendsto_const_nhds
    simpa [F, mul_assoc] using hconst.mul hf_shift
  have hInt_tendsto :
      Tendsto (fun x => ∫ z, F x z) atTop (𝓝 0) := by
    have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := atTop) (F := F) (f := fun _z : ℝ => (0 : ℝ))
      bound hF_meas h_bound hbound_int h_lim
    simpa using h
  have hrepr : ∀ x, frozenElliptic p U x = ∫ z, F x z := by
    intro x
    have hchange :
        (∫ y : ℝ, Real.exp (-1 * |x - y|) * f y) =
          ∫ z : ℝ, Real.exp (-|z|) * f (x + z) := by
      let g : ℝ → ℝ := fun y => Real.exp (-1 * |x - y|) * f y
      have htrans := integral_add_right_eq_self (μ := (volume : Measure ℝ)) g x
      calc
        (∫ y : ℝ, Real.exp (-1 * |x - y|) * f y) = ∫ y : ℝ, g y := rfl
        _ = ∫ z : ℝ, g (z + x) := htrans.symm
        _ = ∫ z : ℝ, Real.exp (-|z|) * f (x + z) := by
          apply integral_congr_ae
          refine Eventually.of_forall ?_
          intro z
          dsimp [g]
          rw [show x - (z + x) = -z by ring, abs_neg]
          ring_nf
    unfold frozenElliptic Psi
    simp only [Real.sqrt_one, mul_one]
    rw [hchange]
    dsimp [F]
    change (1 / 2 : ℝ) * (∫ z : ℝ, Real.exp (-|z|) * f (x + z)) =
      ∫ z : ℝ, (1 / 2 : ℝ) * (Real.exp (-|z|) * f (x + z))
    rw [MeasureTheory.integral_const_mul]
  exact hInt_tendsto.congr' (Eventually.of_forall fun x => (hrepr x).symm)

theorem frozenElliptic_const_eq (p : CMParams) {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    frozenElliptic p (fun _ => c) x = c ^ p.γ := by
  unfold frozenElliptic
  simp only
  exact Psi_const (Real.rpow_nonneg hc p.γ) x

theorem frozenElliptic_one_eq (p : CMParams) (x : ℝ) :
    frozenElliptic p (fun _ => (1 : ℝ)) x = 1 := by
  rw [frozenElliptic_const_eq p (by norm_num) x, Real.one_rpow]

theorem frozenWaveOperator_one_eq_zero (p : CMParams) (c x : ℝ) :
    frozenWaveOperator p c (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) x = 0 := by
  unfold frozenWaveOperator
  simp only [iteratedDeriv_const, deriv_const, show (2 : ℕ) ≠ 0 from by norm_num,
    ite_false, mul_zero, zero_add, add_zero, sub_zero]
  have hV_eq : frozenElliptic p (fun _ => (1 : ℝ)) x = 1 :=
    frozenElliptic_one_eq p x
  have hV'_eq : deriv (frozenElliptic p (fun _ => (1 : ℝ))) x = 0 := by
    have hV_const : (fun z => frozenElliptic p (fun _ => (1 : ℝ)) z) = fun _ => (1 : ℝ) := by
      ext z; exact frozenElliptic_one_eq p z
    rw [show deriv (frozenElliptic p (fun _ => (1 : ℝ))) x =
        deriv (fun _ => (1 : ℝ)) x from congr_arg (fun f => deriv f x) hV_const]
    exact deriv_const x 1
  have h1m : (1 : ℝ) ^ p.m = 1 := Real.one_rpow p.m
  have h1α : (1 : ℝ) ^ p.α = 1 := Real.one_rpow p.α
  have hprod : (fun y => (1 : ℝ) ^ p.m * deriv (frozenElliptic p (fun _ => (1 : ℝ))) y) =
      fun y => deriv (frozenElliptic p (fun _ => (1 : ℝ))) y := by
    ext y; rw [h1m, one_mul]
  have hV'_const :
      (fun y => deriv (frozenElliptic p (fun _ => (1 : ℝ))) y) =
        fun _ => (0 : ℝ) := by
    ext y
    have hV_const : (fun z => frozenElliptic p (fun _ => (1 : ℝ)) z) = fun _ => (1 : ℝ) := by
      ext z; exact frozenElliptic_one_eq p z
    rw [show deriv (frozenElliptic p (fun _ => (1 : ℝ))) y =
        deriv (fun _ => (1 : ℝ)) y from congr_arg (fun f => deriv f y) hV_const]
    exact deriv_const y 1
  rw [hprod, hV'_const, deriv_const, h1α]
  ring

theorem frozenElliptic_tendsto_atBot_of_U_tendsto
    (p : CMParams) {U : ℝ → ℝ}
    (hU : IsCUnifBdd U) (hU_nonneg : ∀ x, 0 ≤ U x)
    (hU_lim : Tendsto U atBot (𝓝 1)) :
    Tendsto (frozenElliptic p U) atBot (𝓝 1) := by
  let f : ℝ → ℝ := fun y => (U y) ^ p.γ
  have hf_lim : Tendsto (fun x => (U x) ^ p.γ) atBot (𝓝 1) := by
    have h1γ : (1 : ℝ) ^ p.γ = 1 := Real.one_rpow p.γ
    rw [← h1γ]
    exact hU_lim.rpow_const (Or.inl one_ne_zero)
  have hf_lim' : Tendsto f atBot (𝓝 1) := by
    simpa [f] using hf_lim
  have hf_cunif : IsCUnifBdd f := by
    simpa [f] using rpow_cunif_bdd_of_nonneg p hU hU_nonneg
  rcases hU.2 with ⟨M, hM⟩
  have hγ_pos : 0 < p.γ := by linarith [p.hγ]
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (U 0)) (hM 0)
  let B : ℝ := M ^ p.γ
  have hf_bound : ∀ y, f y ≤ B := by
    intro y
    dsimp [f, B]
    exact Real.rpow_le_rpow (hU_nonneg y)
      (le_trans (le_abs_self (U y)) (hM y)) hγ_pos.le
  let F : ℝ → ℝ → ℝ := fun x z => (1 / 2 : ℝ) * (Real.exp (-|z|) * f (x + z))
  let G : ℝ → ℝ := fun z => (1 / 2 : ℝ) * (Real.exp (-|z|) * (1 : ℝ))
  let bound : ℝ → ℝ := fun z => (1 / 2 : ℝ) * (Real.exp (-|z|) * B)
  have hbound_int : Integrable bound := by
    have hk0 :
        Integrable (fun z : ℝ => Real.exp (-1 * |0 - z|)) :=
      _root_.kernel_exp_neg_mul_abs_integrable (by norm_num : (0 : ℝ) < 1) 0
    have hk : Integrable (fun z : ℝ => Real.exp (-|z|)) := by
      convert hk0 using 1
      ext z
      rw [zero_sub, abs_neg]
      ring_nf
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using
      hk.const_mul ((1 / 2 : ℝ) * B)
  have hF_meas :
      ∀ᶠ x in atBot, AEStronglyMeasurable (F x) volume := by
    refine Eventually.of_forall ?_
    intro x
    have hcont_kernel : Continuous fun z : ℝ => Real.exp (-|z|) :=
      Real.continuous_exp.comp continuous_abs.neg
    have hcont_shift : Continuous fun z : ℝ => f (x + z) :=
      hf_cunif.1.comp (continuous_const.add continuous_id)
    exact (continuous_const.mul (hcont_kernel.mul hcont_shift)).aestronglyMeasurable
  have h_bound :
      ∀ᶠ x in atBot, ∀ᵐ z ∂volume, ‖F x z‖ ≤ bound z := by
    refine Eventually.of_forall ?_
    intro x
    refine Eventually.of_forall ?_
    intro z
    have hf_nonneg : 0 ≤ f (x + z) := by
      dsimp [f]
      exact Real.rpow_nonneg (hU_nonneg (x + z)) p.γ
    have hprod_nonneg : 0 ≤ Real.exp (-|z|) * f (x + z) :=
      mul_nonneg (Real.exp_nonneg _) hf_nonneg
    have hprod_le :
        Real.exp (-|z|) * f (x + z) ≤ Real.exp (-|z|) * B :=
      mul_le_mul_of_nonneg_left (hf_bound (x + z)) (Real.exp_nonneg _)
    dsimp [F, bound]
    rw [abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hprod_nonneg)]
    exact mul_le_mul_of_nonneg_left hprod_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h_lim :
      ∀ᵐ z ∂volume, Tendsto (fun x => F x z) atBot (𝓝 (G z)) := by
    refine Eventually.of_forall ?_
    intro z
    have hshift : Tendsto (fun x : ℝ => x + z) atBot atBot :=
      tendsto_atBot_add_const_right atBot z tendsto_id
    have hf_shift : Tendsto (fun x : ℝ => f (x + z)) atBot (𝓝 1) :=
      hf_lim'.comp hshift
    have hconst :
        Tendsto (fun _x : ℝ => (1 / 2 : ℝ) * Real.exp (-|z|)) atBot
          (𝓝 ((1 / 2 : ℝ) * Real.exp (-|z|))) :=
      tendsto_const_nhds
    simpa [F, G, mul_assoc] using hconst.mul hf_shift
  have hInt_tendsto :
      Tendsto (fun x => ∫ z, F x z) atBot (𝓝 (∫ z, G z)) := by
    exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := atBot) (F := F) (f := G)
      bound hF_meas h_bound hbound_int h_lim
  have hrepr : ∀ x, frozenElliptic p U x = ∫ z, F x z := by
    intro x
    have hchange :
        (∫ y : ℝ, Real.exp (-1 * |x - y|) * f y) =
          ∫ z : ℝ, Real.exp (-|z|) * f (x + z) := by
      let g : ℝ → ℝ := fun y => Real.exp (-1 * |x - y|) * f y
      have htrans := integral_add_right_eq_self (μ := (volume : Measure ℝ)) g x
      calc
        (∫ y : ℝ, Real.exp (-1 * |x - y|) * f y) = ∫ y : ℝ, g y := rfl
        _ = ∫ z : ℝ, g (z + x) := htrans.symm
        _ = ∫ z : ℝ, Real.exp (-|z|) * f (x + z) := by
          apply integral_congr_ae
          refine Eventually.of_forall ?_
          intro z
          dsimp [g]
          rw [show x - (z + x) = -z by ring, abs_neg]
          ring_nf
    unfold frozenElliptic Psi
    simp only [Real.sqrt_one, mul_one]
    rw [hchange]
    dsimp [F]
    change (1 / 2 : ℝ) * (∫ z : ℝ, Real.exp (-|z|) * f (x + z)) =
      ∫ z : ℝ, (1 / 2 : ℝ) * (Real.exp (-|z|) * f (x + z))
    rw [MeasureTheory.integral_const_mul]
  have hG_integral : (∫ z, G z) = 1 := by
    have hpsi := Psi_const (c := (1 : ℝ)) (by norm_num) 0
    unfold Psi at hpsi
    simp only [Real.sqrt_one, mul_one] at hpsi
    have hkernel :
        (∫ y : ℝ, Real.exp (-1 * |0 - y|) * (1 : ℝ)) =
          ∫ z : ℝ, Real.exp (-|z|) * (1 : ℝ) := by
      apply integral_congr_ae
      refine Eventually.of_forall ?_
      intro z
      simp only [sub_zero, mul_one, neg_one_mul, zero_sub, abs_neg]
    dsimp [G]
    rw [MeasureTheory.integral_const_mul]
    rw [← hkernel]
    simpa using hpsi
  rw [← hG_integral]
  exact hInt_tendsto.congr' (Eventually.of_forall fun x => (hrepr x).symm)

theorem FrozenStationaryWaveProfile.mk_from_stationary
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hc : 0 < c)
    (hU_pos : ∀ x, 0 < U x)
    (hU_bdd : IsCUnifBdd U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hlim_neg : Tendsto U atBot (𝓝 1) ∧ Tendsto (frozenElliptic p U) atBot (𝓝 1))
    (hlim_pos : Tendsto U atTop (𝓝 0) ∧ Tendsto (frozenElliptic p U) atTop (𝓝 0)) :
    FrozenStationaryWaveProfile p c U :=
  { hc
    U_pos := hU_pos
    stationary_eq := hstat
    elliptic_eq := frozenElliptic_ode p hU_bdd (fun x => (hU_pos x).le)
    lim_neg_inf := hlim_neg
    lim_pos_inf := hlim_pos }

theorem paperWaveOperator_eq_frozenWaveOperator_at_fixed_point
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ}
    (hU : IsCUnifBdd U) (hU_nonneg : ∀ x, 0 ≤ U x)
    (hU_diff : DifferentiableAt ℝ U x)
    (hV_diff : DifferentiableAt ℝ (deriv (frozenElliptic p U)) x)
    (hU_rpow_diff : DifferentiableAt ℝ (fun y => (U y) ^ p.m) x)
    (x : ℝ) :
    paperWaveOperator p c U U x = frozenWaveOperator p c U U x := by
  unfold paperWaveOperator frozenWaveOperator
  simp only
  -- The product rule expansion:
  -- deriv(U^m · V') = m U^{m-1} U' V' + U^m V''
  -- V'' = V - U^γ (by frozenElliptic_ode)
  -- Substituting gives the paper form.
  sorry

theorem FrozenStationaryWaveProfile.mk_auto_limits
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hc : 0 < c)
    (hU_pos : ∀ x, 0 < U x)
    (hU_bdd : IsCUnifBdd U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hU_lim_neg : Tendsto U atBot (𝓝 1))
    (hU_lim_pos : Tendsto U atTop (𝓝 0)) :
    FrozenStationaryWaveProfile p c U :=
  FrozenStationaryWaveProfile.mk_from_stationary hc hU_pos hU_bdd hstat
    ⟨hU_lim_neg, frozenElliptic_tendsto_atBot_of_U_tendsto p hU_bdd
      (fun x => (hU_pos x).le) hU_lim_neg⟩
    ⟨hU_lim_pos, frozenElliptic_tendsto_atTop_of_U_tendsto p hU_bdd
      (fun x => (hU_pos x).le) hU_lim_pos⟩

theorem FrozenStationaryWaveProfile.to_travelingWave
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : FrozenStationaryWaveProfile p c U) :
    IsTravelingWave p c U (frozenElliptic p U) := by
  refine
    { hc := h.hc
      U_pos := h.U_pos
      ode_U := ?_
      ode_V := h.elliptic_eq
      lim_neg_inf := h.lim_neg_inf
      lim_pos_inf := h.lim_pos_inf }
  intro x
  simpa [frozenWaveOperator] using h.stationary_eq x

theorem FrozenStationaryWaveProfile.to_monotoneTravelingWave
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : FrozenStationaryWaveProfile p c U)
    (hUmono : ∀ x, deriv U x ≤ 0)
    (hVmono : ∀ x, deriv (frozenElliptic p U) x ≤ 0) :
    IsMonotoneTravelingWave p c U (frozenElliptic p U) :=
  ⟨h.to_travelingWave, hUmono, hVmono⟩

def IsFrozenSuperSolution (p : CMParams) (c : ℝ) (u W : ℝ → ℝ) : Prop :=
  ∀ x, frozenWaveOperator p c u W x ≤ 0

def IsFrozenSubSolutionOn (p : CMParams) (c : ℝ) (u W : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, 0 ≤ frozenWaveOperator p c u W x

def IsPaperFrozenSuperSolution (p : CMParams) (c : ℝ) (u W : ℝ → ℝ) : Prop :=
  ∀ x, paperWaveOperator p c u W x ≤ 0

def IsPaperFrozenSubSolutionOn (p : CMParams) (c : ℝ) (u W : ℝ → ℝ) (s : Set ℝ) :
    Prop :=
  ∀ x ∈ s, 0 ≤ paperWaveOperator p c u W x

def expDecay (κ : ℝ) : ℝ → ℝ :=
  fun x => Real.exp (-(κ * x))

theorem expDecay_pos (κ x : ℝ) :
    0 < expDecay κ x := by
  exact Real.exp_pos _

theorem expDecay_antitone {κ : ℝ} (hκ : 0 ≤ κ) :
    Antitone (expDecay κ) := by
  intro x y hxy
  unfold expDecay
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hxy hκ]

theorem expDecay_tendsto_atTop {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (expDecay κ) atTop (𝓝 0) := by
  have hmul : Tendsto (fun x : ℝ => κ * x) atTop atTop :=
    (Filter.tendsto_id.atTop_mul_const hκ).congr (fun x => mul_comm x κ)
  have hneg : Tendsto (fun x : ℝ => -(κ * x)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hmul
  simpa [expDecay] using Real.tendsto_exp_atBot.comp hneg

theorem expDecay_tendsto_atBot {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (expDecay κ) atBot atTop := by
  have hmul : Tendsto (fun x : ℝ => κ * x) atBot atBot :=
    (Filter.tendsto_id.atBot_mul_const hκ).congr (fun x => mul_comm x κ)
  have hneg : Tendsto (fun x : ℝ => -(κ * x)) atBot atTop :=
    tendsto_neg_atBot_atTop.comp hmul
  simpa [expDecay] using Real.tendsto_exp_atTop.comp hneg

theorem expDecay_hasDerivAt (κ x : ℝ) :
    HasDerivAt (expDecay κ) (-κ * expDecay κ x) x := by
  have hlin : HasDerivAt (fun y : ℝ => -κ * y) (-κ) x :=
    by simpa using (hasDerivAt_id x).const_mul (-κ)
  change
    HasDerivAt (fun y : ℝ => Real.exp (-(κ * y)))
      (-κ * Real.exp (-(κ * x))) x
  simpa [expDecay, mul_comm, mul_left_comm, mul_assoc] using hlin.exp

theorem expDecay_deriv (κ x : ℝ) :
    deriv (expDecay κ) x = -κ * expDecay κ x :=
  (expDecay_hasDerivAt κ x).deriv

theorem expDecay_iteratedDeriv_two (κ x : ℝ) :
    iteratedDeriv 2 (expDecay κ) x = κ ^ 2 * expDecay κ x := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  change deriv (deriv (expDecay κ)) x = κ ^ 2 * expDecay κ x
  have hderiv :
      deriv (expDecay κ) = fun y => -κ * expDecay κ y := by
    ext y
    exact expDecay_deriv κ y
  rw [hderiv]
  have h :=
    ((expDecay_hasDerivAt κ x).const_mul (-κ)).deriv
  simpa [pow_two, mul_assoc] using h

theorem expDecay_linear_part_eq
    (κ c x : ℝ) :
    iteratedDeriv 2 (expDecay κ) x + c * deriv (expDecay κ) x +
        expDecay κ x =
      (κ ^ 2 - c * κ + 1) * expDecay κ x := by
  rw [expDecay_iteratedDeriv_two, expDecay_deriv]
  ring

theorem expDecay_linear_part_kappa_eq_zero
    {c : ℝ} (hc : 2 ≤ c) (x : ℝ) :
    iteratedDeriv 2 (expDecay (kappa c)) x +
        c * deriv (expDecay (kappa c)) x +
        expDecay (kappa c) x = 0 := by
  rw [expDecay_linear_part_eq]
  rw [kappa_quadratic_eq_zero hc]
  ring

theorem expDecay_logistic_wave_eq
    (p : CMParams) (κ c x : ℝ) :
    iteratedDeriv 2 (expDecay κ) x + c * deriv (expDecay κ) x +
        expDecay κ x * (1 - (expDecay κ x) ^ p.α) =
      (κ ^ 2 - c * κ + 1) * expDecay κ x -
        expDecay κ x * (expDecay κ x) ^ p.α := by
  rw [expDecay_iteratedDeriv_two, expDecay_deriv]
  ring

theorem expDecay_logistic_wave_at_kappa
    {c : ℝ} (hc : 2 ≤ c) (p : CMParams) (x : ℝ) :
    iteratedDeriv 2 (expDecay (kappa c)) x +
        c * deriv (expDecay (kappa c)) x +
        expDecay (kappa c) x * (1 - (expDecay (kappa c) x) ^ p.α) =
      -expDecay (kappa c) x * (expDecay (kappa c) x) ^ p.α := by
  rw [expDecay_logistic_wave_eq]
  rw [kappa_quadratic_eq_zero hc]
  ring

theorem expDecay_logistic_wave_nonpos_at_kappa
    {c : ℝ} (hc : 2 ≤ c) (p : CMParams) (x : ℝ) :
    iteratedDeriv 2 (expDecay (kappa c)) x +
        c * deriv (expDecay (kappa c)) x +
        expDecay (kappa c) x * (1 - (expDecay (kappa c) x) ^ p.α) ≤ 0 := by
  rw [expDecay_logistic_wave_at_kappa hc p x]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (expDecay_pos (kappa c) x).le)
    (Real.rpow_nonneg (expDecay_pos (kappa c) x).le _)

theorem expDecay_linear_part_eq_of_kappa_speed
    {κ c x : ℝ} (hκ : κ ≠ 0) (hc : c = κ + κ⁻¹) :
    iteratedDeriv 2 (expDecay κ) x + c * deriv (expDecay κ) x +
        expDecay κ x = 0 := by
  rw [expDecay_linear_part_eq, hc]
  have hzero : κ ^ 2 - (κ + κ⁻¹) * κ + 1 = 0 := by
    field_simp [hκ]
    ring
  rw [hzero]
  ring

theorem expDecay_logistic_wave_nonpos_of_kappa_speed
    {κ c : ℝ} (hκ : κ ≠ 0) (hc : c = κ + κ⁻¹)
    (p : CMParams) (x : ℝ) :
    iteratedDeriv 2 (expDecay κ) x + c * deriv (expDecay κ) x +
        expDecay κ x * (1 - (expDecay κ x) ^ p.α) ≤ 0 := by
  rw [expDecay_logistic_wave_eq, hc]
  have hzero : κ ^ 2 - (κ + κ⁻¹) * κ + 1 = 0 := by
    field_simp [hκ]
    ring
  rw [hzero]
  ring_nf
  exact neg_nonpos.mpr
    (mul_nonneg (expDecay_pos κ x).le
      (Real.rpow_nonneg (expDecay_pos κ x).le _))

theorem constant_logistic_nonpos
    (p : CMParams) {M : ℝ} (hM : 1 ≤ M) :
    M * (1 - M ^ p.α) ≤ 0 := by
  have hM_pos : 0 < M := by linarith
  exact mul_nonpos_of_nonneg_of_nonpos hM_pos.le
    (sub_nonpos.mpr (Real.one_le_rpow hM (by linarith [p.hα])))

theorem constant_logistic_neg
    (p : CMParams) {M : ℝ} (hM : 1 < M) :
    M * (1 - M ^ p.α) < 0 := by
  have hM_pos : 0 < M := by linarith
  exact mul_neg_of_pos_of_neg hM_pos
    (sub_neg.mpr (Real.one_lt_rpow hM (by linarith [p.hα])))

theorem expDecay_logistic_wave_neg_at_kappa
    {c : ℝ} (hc : 2 < c) (p : CMParams) (x : ℝ) :
    iteratedDeriv 2 (expDecay (kappa c)) x +
        c * deriv (expDecay (kappa c)) x +
        expDecay (kappa c) x * (1 - (expDecay (kappa c) x) ^ p.α) < 0 := by
  rw [expDecay_logistic_wave_at_kappa hc.le p x]
  have hpos := expDecay_pos (kappa c) x
  nlinarith [Real.rpow_pos_of_pos hpos p.α]

def upperBarrier (κ M : ℝ) : ℝ → ℝ :=
  fun x => min M (Real.exp (-κ * x))

theorem upperBarrier_le_M (κ M x : ℝ) :
    upperBarrier κ M x ≤ M :=
  min_le_left _ _

theorem upperBarrier_le_exp (κ M x : ℝ) :
    upperBarrier κ M x ≤ Real.exp (-κ * x) :=
  min_le_right _ _

theorem upperBarrier_mono_M {κ M₁ M₂ : ℝ} (hM : M₁ ≤ M₂) (x : ℝ) :
    upperBarrier κ M₁ x ≤ upperBarrier κ M₂ x :=
  min_le_min hM le_rfl

theorem upperBarrier_eq_M_of_le_exp {κ M x : ℝ}
    (h : M ≤ Real.exp (-κ * x)) :
    upperBarrier κ M x = M := by
  exact min_eq_left h

theorem upperBarrier_eq_exp_of_exp_le {κ M x : ℝ}
    (h : Real.exp (-κ * x) ≤ M) :
    upperBarrier κ M x = Real.exp (-κ * x) := by
  exact min_eq_right h

theorem upperBarrier_eventuallyEq_const_of_lt {κ M x : ℝ}
    (h : M < Real.exp (-κ * x)) :
    upperBarrier κ M =ᶠ[𝓝 x] fun _ : ℝ => M := by
  have hcont : Continuous fun z : ℝ => Real.exp (-κ * z) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hopen : IsOpen {z : ℝ | M < Real.exp (-κ * z)} :=
    isOpen_lt continuous_const hcont
  filter_upwards [hopen.mem_nhds h] with z hz
  exact upperBarrier_eq_M_of_le_exp (le_of_lt hz)

theorem upperBarrier_eventuallyEq_exp_of_lt {κ M x : ℝ}
    (h : Real.exp (-κ * x) < M) :
    upperBarrier κ M =ᶠ[𝓝 x] expDecay κ := by
  have hcont : Continuous fun z : ℝ => Real.exp (-κ * z) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hopen : IsOpen {z : ℝ | Real.exp (-κ * z) < M} :=
    isOpen_lt hcont continuous_const
  filter_upwards [hopen.mem_nhds h] with z hz
  simpa [expDecay] using upperBarrier_eq_exp_of_exp_le (le_of_lt hz)

theorem upperBarrier_deriv_eq_zero_of_const_lt {κ M x : ℝ}
    (h : M < Real.exp (-κ * x)) :
    deriv (upperBarrier κ M) x = 0 := by
  rw [Filter.EventuallyEq.deriv_eq (upperBarrier_eventuallyEq_const_of_lt h)]
  exact deriv_const x M

theorem upperBarrier_deriv_eq_exp_of_lt {κ M x : ℝ}
    (h : Real.exp (-κ * x) < M) :
    deriv (upperBarrier κ M) x = -κ * expDecay κ x := by
  rw [Filter.EventuallyEq.deriv_eq (upperBarrier_eventuallyEq_exp_of_lt h)]
  exact expDecay_deriv κ x

theorem upperBarrier_iteratedDeriv_two_eq_zero_of_const_lt {κ M x : ℝ}
    (h : M < Real.exp (-κ * x)) :
    iteratedDeriv 2 (upperBarrier κ M) x = 0 := by
  have hderiv :
      deriv (upperBarrier κ M) =ᶠ[𝓝 x] deriv (fun _ : ℝ => M) :=
    (upperBarrier_eventuallyEq_const_of_lt h).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [Filter.EventuallyEq.deriv_eq hderiv]
  simp [deriv_const]

theorem upperBarrier_iteratedDeriv_two_eq_exp_of_lt {κ M x : ℝ}
    (h : Real.exp (-κ * x) < M) :
    iteratedDeriv 2 (upperBarrier κ M) x = κ ^ 2 * expDecay κ x := by
  have hderiv :
      deriv (upperBarrier κ M) =ᶠ[𝓝 x] deriv (expDecay κ) :=
    (upperBarrier_eventuallyEq_exp_of_lt h).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [Filter.EventuallyEq.deriv_eq hderiv]
  simpa [iteratedDeriv_succ, iteratedDeriv_zero] using
    expDecay_iteratedDeriv_two κ x

theorem frozenWaveOperator_upperBarrier_const_region_eq
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x)
    {x : ℝ} (hx : M < Real.exp (-κ * x)) :
    frozenWaveOperator p c u (upperBarrier κ M) x =
      -p.χ * (M ^ p.m *
        (frozenElliptic p u x - (u x) ^ p.γ)) +
        M * (1 - M ^ p.α) := by
  have hW : upperBarrier κ M =ᶠ[𝓝 x] fun _ : ℝ => M :=
    upperBarrier_eventuallyEq_const_of_lt hx
  have hWpow :
      (fun y => (upperBarrier κ M y) ^ p.m *
          deriv (frozenElliptic p u) y) =ᶠ[𝓝 x]
        fun y => M ^ p.m * deriv (frozenElliptic p u) y := by
    filter_upwards [hW] with y hy
    rw [hy]
  have hchem :
      deriv
          (fun y => (upperBarrier κ M y) ^ p.m *
            deriv (frozenElliptic p u) y) x =
        M ^ p.m * (frozenElliptic p u x - (u x) ^ p.γ) := by
    rw [Filter.EventuallyEq.deriv_eq hWpow]
    rw [deriv_const_mul_field]
    rw [frozenElliptic_deriv_deriv_eq p hu hu_nonneg x]
  have hW_x : upperBarrier κ M x = M :=
    upperBarrier_eq_M_of_le_exp (le_of_lt hx)
  unfold frozenWaveOperator
  rw [upperBarrier_iteratedDeriv_two_eq_zero_of_const_lt hx,
    upperBarrier_deriv_eq_zero_of_const_lt hx, hchem, hW_x]
  ring

theorem upperBarrier_nonneg {κ M : ℝ} (hM : 0 ≤ M) (x : ℝ) :
    0 ≤ upperBarrier κ M x :=
  le_min hM (Real.exp_pos _).le

theorem upperBarrier_pos {κ M : ℝ} (hM : 0 < M) (x : ℝ) :
    0 < upperBarrier κ M x :=
  lt_min hM (Real.exp_pos _)

theorem upperBarrier_continuous (κ M : ℝ) :
    Continuous (upperBarrier κ M) := by
  unfold upperBarrier
  exact continuous_const.min
    (Real.continuous_exp.comp (continuous_const.mul continuous_id))

theorem upperBarrier_isBddFun {κ M : ℝ} (hM : 0 ≤ M) :
    IsBddFun (upperBarrier κ M) := by
  refine ⟨M, ?_⟩
  intro x
  rw [abs_of_nonneg (upperBarrier_nonneg hM x)]
  exact upperBarrier_le_M κ M x

theorem upperBarrier_cunif_bdd {κ M : ℝ} (hM : 0 ≤ M) :
    IsCUnifBdd (upperBarrier κ M) :=
  ⟨upperBarrier_continuous κ M, upperBarrier_isBddFun hM⟩

theorem upperBarrier_rpow_le_M
    {κ M a : ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a) (x : ℝ) :
    (upperBarrier κ M x) ^ a ≤ M ^ a :=
  Real.rpow_le_rpow (upperBarrier_nonneg hM x) (upperBarrier_le_M κ M x) ha

theorem upperBarrier_rpow_le_exp
    {κ M a : ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a) (x : ℝ) :
    (upperBarrier κ M x) ^ a ≤ (Real.exp (-κ * x)) ^ a :=
  Real.rpow_le_rpow (upperBarrier_nonneg hM x) (upperBarrier_le_exp κ M x) ha

theorem upperBarrier_rpow_le_exp_mul
    {κ M a : ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a) (x : ℝ) :
    (upperBarrier κ M x) ^ a ≤ Real.exp (-κ * a * x) := by
  calc
    (upperBarrier κ M x) ^ a ≤ (Real.exp (-κ * x)) ^ a :=
      upperBarrier_rpow_le_exp hM ha x
    _ = Real.exp (-κ * a * x) := by
      rw [← Real.exp_mul]
      congr 1
      ring

theorem upperBarrier_antitone {κ M : ℝ} (hκ : 0 ≤ κ) :
    Antitone (upperBarrier κ M) := by
  intro x₁ x₂ hx
  unfold upperBarrier
  exact min_le_min le_rfl
    (Real.exp_le_exp.mpr (by nlinarith))

def lowerBarrierRaw (κ κtilde D : ℝ) : ℝ → ℝ :=
  fun x => Real.exp (-κ * x) - D * Real.exp (-κtilde * x)

theorem lowerBarrierRaw_continuous (κ κtilde D : ℝ) :
    Continuous (lowerBarrierRaw κ κtilde D) := by
  have hlinκ : Continuous (fun x : ℝ => (-κ) * x) :=
    continuous_const.mul continuous_id
  have hlinκtilde : Continuous (fun x : ℝ => (-κtilde) * x) :=
    continuous_const.mul continuous_id
  have hκ : Continuous (fun x : ℝ => Real.exp ((-κ) * x)) :=
    Real.continuous_exp.comp hlinκ
  have hκtilde : Continuous (fun x : ℝ => Real.exp ((-κtilde) * x)) :=
    Real.continuous_exp.comp hlinκtilde
  have hD : Continuous (fun _ : ℝ => D) := continuous_const
  change Continuous
    (fun x : ℝ => Real.exp ((-κ) * x) - D * Real.exp ((-κtilde) * x))
  exact hκ.sub (hD.mul hκtilde)

theorem lowerBarrierRaw_hasDerivAt (κ κtilde D x : ℝ) :
    HasDerivAt (lowerBarrierRaw κ κtilde D)
      (-κ * Real.exp (-κ * x) + D * κtilde * Real.exp (-κtilde * x)) x := by
  unfold lowerBarrierRaw
  have hκ :
      HasDerivAt
        (fun y : ℝ => Real.exp (-κ * y))
        (-κ * Real.exp (-κ * x)) x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).const_mul κ).neg.exp)
  have hκtilde :
      HasDerivAt
        (fun y : ℝ => D * Real.exp (-κtilde * y))
        (D * (-κtilde * Real.exp (-κtilde * x))) x := by
    have hbase :
        HasDerivAt
          (fun y : ℝ => Real.exp (-κtilde * y))
          (-κtilde * Real.exp (-κtilde * x)) x := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id x).const_mul κtilde).neg.exp)
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase.const_mul D
  simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hκ.sub hκtilde

theorem lowerBarrierRaw_deriv (κ κtilde D x : ℝ) :
    deriv (lowerBarrierRaw κ κtilde D) x =
      -κ * Real.exp (-κ * x) + D * κtilde * Real.exp (-κtilde * x) := by
  exact (lowerBarrierRaw_hasDerivAt κ κtilde D x).deriv

theorem lowerBarrierRaw_second_deriv (κ κtilde D x : ℝ) :
    iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x =
      κ ^ 2 * Real.exp (-κ * x) - D * κtilde ^ 2 * Real.exp (-κtilde * x) := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  have hder_fun :
      deriv (lowerBarrierRaw κ κtilde D) =
        fun y : ℝ =>
          -κ * Real.exp (-κ * y) + D * κtilde * Real.exp (-κtilde * y) := by
    funext y
    exact lowerBarrierRaw_deriv κ κtilde D y
  rw [hder_fun]
  have hκbase :
      HasDerivAt
        (fun y : ℝ => Real.exp (-κ * y))
        (-κ * Real.exp (-κ * x)) x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).const_mul κ).neg.exp)
  have hκ :
      HasDerivAt
        (fun y : ℝ => -κ * Real.exp (-κ * y))
        (κ ^ 2 * Real.exp (-κ * x)) x := by
    convert hκbase.const_mul (-κ) using 1
    ring
  have hκtilde_base :
      HasDerivAt
        (fun y : ℝ => Real.exp (-κtilde * y))
        (-κtilde * Real.exp (-κtilde * x)) x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).const_mul κtilde).neg.exp)
  have hκtilde :
      HasDerivAt
        (fun y : ℝ => D * κtilde * Real.exp (-κtilde * y))
        (-(D * κtilde ^ 2 * Real.exp (-κtilde * x))) x := by
    convert hκtilde_base.const_mul (D * κtilde) using 1
    ring
  have hder := hκ.add hκtilde
  simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hder.deriv

theorem lowerBarrierRaw_linear_part_eq
    (κ κtilde D c x : ℝ) :
    iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x +
        c * deriv (lowerBarrierRaw κ κtilde D) x +
        lowerBarrierRaw κ κtilde D x =
      (κ ^ 2 - c * κ + 1) * Real.exp (-κ * x) -
        D * (κtilde ^ 2 - c * κtilde + 1) *
          Real.exp (-κtilde * x) := by
  rw [lowerBarrierRaw_second_deriv, lowerBarrierRaw_deriv]
  unfold lowerBarrierRaw
  ring

theorem lowerBarrierRaw_linear_part_eq_of_kappa_speed
    {κ κtilde D c x : ℝ} (hκ : κ ≠ 0) (hc : c = κ + κ⁻¹) :
    iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x +
        c * deriv (lowerBarrierRaw κ κtilde D) x +
        lowerBarrierRaw κ κtilde D x =
      -D * (κtilde ^ 2 - c * κtilde + 1) *
        Real.exp (-κtilde * x) := by
  rw [lowerBarrierRaw_linear_part_eq, hc]
  have hzero : κ ^ 2 - (κ + κ⁻¹) * κ + 1 = 0 := by
    field_simp [hκ]
    ring
  rw [hzero]
  ring

theorem lowerBarrierRaw_speed_coefficient_neg
    {κ κtilde c : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ < 1) (hgap : κ < κtilde)
    (hκtilde1 : κtilde ≤ 1) (hc : c = κ + κ⁻¹) :
    κtilde ^ 2 - c * κtilde + 1 < 0 := by
  have hinv_gt_one : 1 < κ⁻¹ := (one_lt_inv₀ hκ0).2 hκ1
  have hleft : 0 < κtilde - κ := sub_pos.mpr hgap
  have hright : κtilde - κ⁻¹ < 0 := sub_neg.mpr (lt_of_le_of_lt hκtilde1 hinv_gt_one)
  have hfactor :
      κtilde ^ 2 - c * κtilde + 1 =
        (κtilde - κ) * (κtilde - κ⁻¹) := by
    rw [hc]
    field_simp [ne_of_gt hκ0]
    ring
  rw [hfactor]
  exact mul_neg_of_pos_of_neg hleft hright

theorem lowerBarrierRaw_speed_denominator_pos
    {κ κtilde c : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ < 1) (hgap : κ < κtilde)
    (hκtilde1 : κtilde ≤ 1) (hc : c = κ + κ⁻¹) :
    0 < c * κtilde - κtilde ^ 2 - 1 := by
  have h :=
    lowerBarrierRaw_speed_coefficient_neg hκ0 hκ1 hgap hκtilde1 hc
  nlinarith

theorem lowerBarrierRaw_linear_part_pos_of_kappa_speed
    {κ κtilde D c x : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ < 1) (hgap : κ < κtilde)
    (hκtilde1 : κtilde ≤ 1) (hD : 0 < D) (hc : c = κ + κ⁻¹) :
    0 <
      iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x +
        c * deriv (lowerBarrierRaw κ κtilde D) x +
        lowerBarrierRaw κ κtilde D x := by
  rw [lowerBarrierRaw_linear_part_eq_of_kappa_speed (ne_of_gt hκ0) hc]
  apply mul_pos
  · exact mul_pos_of_neg_of_neg (neg_lt_zero.mpr hD)
      (lowerBarrierRaw_speed_coefficient_neg hκ0 hκ1 hgap hκtilde1 hc)
  · exact Real.exp_pos _

theorem lowerBarrierRaw_linear_part_pos_of_speed_gt_two
    {κtilde D c x : ℝ}
    (hc : 2 < c) (hgap : kappa c < κtilde)
    (hκtilde1 : κtilde ≤ 1) (hD : 0 < D) :
    0 <
      iteratedDeriv 2 (lowerBarrierRaw (kappa c) κtilde D) x +
        c * deriv (lowerBarrierRaw (kappa c) κtilde D) x +
        lowerBarrierRaw (kappa c) κtilde D x := by
  exact
    lowerBarrierRaw_linear_part_pos_of_kappa_speed
      (kappa_pos_of_two_lt hc)
      (kappa_lt_one_of_two_lt hc)
      hgap hκtilde1 hD
      (kappa_add_inv_eq_of_two_lt hc).symm

theorem lowerBarrierRaw_linear_part_pos_of_cStarLower_lt
    {p : CMParams} {κtilde D c x : ℝ}
    (hc : cStarLower p < c) (hgap : kappa c < κtilde)
    (hκtilde1 : κtilde ≤ 1) (hD : 0 < D) :
    0 <
      iteratedDeriv 2 (lowerBarrierRaw (kappa c) κtilde D) x +
        c * deriv (lowerBarrierRaw (kappa c) κtilde D) x +
        lowerBarrierRaw (kappa c) κtilde D x :=
  lowerBarrierRaw_linear_part_pos_of_speed_gt_two
    (two_lt_of_cStarLower_lt hc) hgap hκtilde1 hD

def lowerBarrierXMinus (κ κtilde D : ℝ) : ℝ :=
  Real.log D / (κtilde - κ)

theorem lowerBarrierRaw_eq_exp_mul (κ κtilde D x : ℝ) :
    lowerBarrierRaw κ κtilde D x =
      Real.exp (-κ * x) * (1 - D * Real.exp (-(κtilde - κ) * x)) := by
  unfold lowerBarrierRaw
  have hexp :
      Real.exp (-κtilde * x) =
        Real.exp (-κ * x) * Real.exp (-(κtilde - κ) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

theorem lowerBarrierRaw_le_exp {κ κtilde D x : ℝ} (hD : 0 ≤ D) :
    lowerBarrierRaw κ κtilde D x ≤ Real.exp (-κ * x) := by
  unfold lowerBarrierRaw
  have hnonneg : 0 ≤ D * Real.exp (-κtilde * x) :=
    mul_nonneg hD (Real.exp_pos _).le
  linarith

theorem lowerBarrierRaw_nonneg_of_xminus_le
    {κ κtilde D x : ℝ} (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hx : lowerBarrierXMinus κ κtilde D ≤ x) :
    0 ≤ lowerBarrierRaw κ κtilde D x := by
  rw [lowerBarrierRaw_eq_exp_mul]
  apply mul_nonneg (Real.exp_pos _).le
  have hlog_le : Real.log D ≤ (κtilde - κ) * x := by
    rw [lowerBarrierXMinus] at hx
    simpa [mul_comm] using (div_le_iff₀ hgap).mp hx
  have hexp_le :
      Real.exp (Real.log D + (-(κtilde - κ) * x)) ≤ Real.exp 0 :=
    Real.exp_le_exp.mpr (by linarith)
  have hDexp_le : D * Real.exp (-(κtilde - κ) * x) ≤ 1 := by
    simpa [Real.exp_add, Real.exp_log hD] using hexp_le
  linarith

theorem lowerBarrierRaw_pos_of_xminus_lt
    {κ κtilde D x : ℝ} (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hx : lowerBarrierXMinus κ κtilde D < x) :
    0 < lowerBarrierRaw κ κtilde D x := by
  rw [lowerBarrierRaw_eq_exp_mul]
  apply mul_pos (Real.exp_pos _)
  have hlog_lt : Real.log D < (κtilde - κ) * x := by
    rw [lowerBarrierXMinus] at hx
    simpa [mul_comm] using (div_lt_iff₀ hgap).mp hx
  have hexp_lt :
      Real.exp (Real.log D + (-(κtilde - κ) * x)) < Real.exp 0 :=
    Real.exp_lt_exp.mpr (by linarith)
  have hDexp_lt : D * Real.exp (-(κtilde - κ) * x) < 1 := by
    simpa [Real.exp_add, Real.exp_log hD] using hexp_lt
  linarith

theorem lowerBarrierRaw_eq_zero_at_xminus
    {κ κtilde D : ℝ} (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    lowerBarrierRaw κ κtilde D (lowerBarrierXMinus κ κtilde D) = 0 := by
  rw [lowerBarrierRaw_eq_exp_mul]
  have hx :
      (κtilde - κ) * lowerBarrierXMinus κ κtilde D = Real.log D := by
    unfold lowerBarrierXMinus
    field_simp [ne_of_gt hgap]
  have hDexp :
      D * Real.exp (-(κtilde - κ) * lowerBarrierXMinus κ κtilde D) = 1 := by
    have hexp :
        Real.exp
          (Real.log D + (-(κtilde - κ) * lowerBarrierXMinus κ κtilde D)) =
          Real.exp 0 := by
      congr 1
      linarith
    simpa [Real.exp_add, Real.exp_log hD] using hexp
  rw [hDexp]
  ring

def lowerBarrierXPlus (κ κtilde D : ℝ) : ℝ :=
  Real.log (κtilde * D / κ) / (κtilde - κ)

theorem lowerBarrierXPlus_of_exp_choice
    {κ κtilde x : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) :
    lowerBarrierXPlus κ κtilde
        (κ / κtilde * Real.exp ((κtilde - κ) * x)) = x := by
  have hκtilde : 0 < κtilde := by linarith
  unfold lowerBarrierXPlus
  have harg :
      κtilde * (κ / κtilde * Real.exp ((κtilde - κ) * x)) / κ =
        Real.exp ((κtilde - κ) * x) := by
    field_simp [ne_of_gt hκ, ne_of_gt hκtilde]
  rw [harg, Real.log_exp]
  field_simp [ne_of_gt hgap]

theorem lowerBarrierXPlus_mono_D
    {κ κtilde D₁ D₂ : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD₁ : 0 < D₁) (hDle : D₁ ≤ D₂) :
    lowerBarrierXPlus κ κtilde D₁ ≤ lowerBarrierXPlus κ κtilde D₂ := by
  have hκtilde : 0 < κtilde := by linarith
  have harg₁ : 0 < κtilde * D₁ / κ := by positivity
  have hmul : κtilde * D₁ ≤ κtilde * D₂ :=
    mul_le_mul_of_nonneg_left hDle hκtilde.le
  have hargle : κtilde * D₁ / κ ≤ κtilde * D₂ / κ :=
    div_le_div_of_nonneg_right hmul hκ.le
  unfold lowerBarrierXPlus
  exact div_le_div_of_nonneg_right (Real.log_le_log harg₁ hargle) hgap.le

theorem lowerBarrierExpXPlus_antitone_D
    {κ κtilde D₁ D₂ : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD₁ : 0 < D₁) (hDle : D₁ ≤ D₂) :
    Real.exp (-κ * lowerBarrierXPlus κ κtilde D₂) ≤
      Real.exp (-κ * lowerBarrierXPlus κ κtilde D₁) := by
  apply Real.exp_le_exp.mpr
  have hx :=
    lowerBarrierXPlus_mono_D hκ hgap hD₁ hDle
  nlinarith [mul_nonneg hκ.le (sub_nonneg.mpr hx)]

theorem exists_D_gt_with_exp_xplus_le
    {κ κtilde M B : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hM : 0 < M) :
    ∃ D > B, Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ M := by
  have hκtilde : 0 < κtilde := by linarith
  let x₀ : ℝ := max 0 (-(Real.log M) / κ)
  let Dneed : ℝ := κ / κtilde * Real.exp ((κtilde - κ) * x₀)
  let D : ℝ := max (B + 1) Dneed
  have hDneed_pos : 0 < Dneed := by
    dsimp [Dneed]
    positivity
  have hB_D : B < D := by
    have h : B < B + 1 := by linarith
    exact lt_of_lt_of_le h (le_max_left _ _)
  have hDneed_le_D : Dneed ≤ D := le_max_right _ _
  have hx₀_bound : Real.exp (-κ * x₀) ≤ M := by
    have hx₀_ge : -(Real.log M) / κ ≤ x₀ := le_max_right _ _
    have hmul : -κ * x₀ ≤ Real.log M := by
      rw [neg_mul]
      have hmul' := mul_le_mul_of_nonneg_left hx₀_ge hκ.le
      rw [mul_div_cancel₀ _ (ne_of_gt hκ)] at hmul'
      linarith
    calc
      Real.exp (-κ * x₀) ≤ Real.exp (Real.log M) :=
        Real.exp_le_exp.mpr hmul
      _ = M := Real.exp_log hM
  refine ⟨D, hB_D, ?_⟩
  calc
    Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤
        Real.exp (-κ * lowerBarrierXPlus κ κtilde Dneed) :=
      lowerBarrierExpXPlus_antitone_D hκ hgap hDneed_pos hDneed_le_D
    _ = Real.exp (-κ * x₀) := by
      rw [lowerBarrierXPlus_of_exp_choice hκ hgap]
    _ ≤ M := hx₀_bound

theorem lowerBarrierXMinus_lt_xplus
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    lowerBarrierXMinus κ κtilde D < lowerBarrierXPlus κ κtilde D := by
  have harg_pos : 0 < κtilde * D / κ := by
    have hκtilde_pos : 0 < κtilde := by linarith
    positivity
  have hD_lt_arg : D < κtilde * D / κ := by
    rw [lt_div_iff₀ hκ]
    nlinarith
  unfold lowerBarrierXMinus lowerBarrierXPlus
  rw [div_lt_div_iff_of_pos_right hgap]
  exact Real.log_lt_log hD hD_lt_arg

theorem lowerBarrierRaw_deriv_eq_zero_at_xplus
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    deriv (lowerBarrierRaw κ κtilde D) (lowerBarrierXPlus κ κtilde D) = 0 := by
  have hκtilde_pos : 0 < κtilde := by linarith
  have harg_pos : 0 < κtilde * D / κ := by positivity
  have hx :
      (κtilde - κ) * lowerBarrierXPlus κ κtilde D =
        Real.log (κtilde * D / κ) := by
    unfold lowerBarrierXPlus
    field_simp [ne_of_gt hgap]
  have hargexp :
      (κtilde * D / κ) *
        Real.exp (-(κtilde - κ) * lowerBarrierXPlus κ κtilde D) = 1 := by
    have hexp :
        Real.exp
          (Real.log (κtilde * D / κ) +
            (-(κtilde - κ) * lowerBarrierXPlus κ κtilde D)) =
          Real.exp 0 := by
      congr 1
      linarith
    simpa [Real.exp_add, Real.exp_log harg_pos] using hexp
  have hcrit :
      D * κtilde *
        Real.exp (-(κtilde - κ) * lowerBarrierXPlus κ κtilde D) = κ := by
    have hκ_ne : κ ≠ 0 := ne_of_gt hκ
    field_simp [hκ_ne] at hargexp
    convert hargexp using 1
    ring_nf
  rw [lowerBarrierRaw_deriv]
  have hexp :
      Real.exp (-κtilde * lowerBarrierXPlus κ κtilde D) =
        Real.exp (-κ * lowerBarrierXPlus κ κtilde D) *
          Real.exp (-(κtilde - κ) * lowerBarrierXPlus κ κtilde D) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  nlinarith [Real.exp_pos (-κ * lowerBarrierXPlus κ κtilde D)]

theorem lowerBarrierRaw_deriv_nonpos_of_xplus_le
    {κ κtilde D x : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hx : lowerBarrierXPlus κ κtilde D ≤ x) :
    deriv (lowerBarrierRaw κ κtilde D) x ≤ 0 := by
  have hκtilde_pos : 0 < κtilde := by linarith
  have harg_pos : 0 < κtilde * D / κ := by positivity
  have hlog_le : Real.log (κtilde * D / κ) ≤ (κtilde - κ) * x := by
    rw [lowerBarrierXPlus] at hx
    simpa [mul_comm] using (div_le_iff₀ hgap).mp hx
  have hexp_le :
      Real.exp (Real.log (κtilde * D / κ) + (-(κtilde - κ) * x)) ≤
        Real.exp 0 :=
    Real.exp_le_exp.mpr (by linarith)
  have hcrit_le :
      D * κtilde * Real.exp (-(κtilde - κ) * x) ≤ κ := by
    have hle :
        (κtilde * D / κ) * Real.exp (-(κtilde - κ) * x) ≤ 1 := by
      simpa [Real.exp_add, Real.exp_log harg_pos] using hexp_le
    have hκ_nonneg : 0 ≤ κ := hκ.le
    have hmul := mul_le_mul_of_nonneg_right hle hκ_nonneg
    have hκ_ne : κ ≠ 0 := ne_of_gt hκ
    field_simp [hκ_ne] at hmul
    convert hmul using 1
    ring_nf
  rw [lowerBarrierRaw_deriv]
  have hexp :
      Real.exp (-κtilde * x) =
        Real.exp (-κ * x) * Real.exp (-(κtilde - κ) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  nlinarith [Real.exp_pos (-κ * x)]

theorem lowerBarrierRaw_antitoneOn_Ici_xplus
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    AntitoneOn (lowerBarrierRaw κ κtilde D)
      (Set.Ici (lowerBarrierXPlus κ κtilde D)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici _)
    (lowerBarrierRaw_continuous κ κtilde D).continuousOn ?_ ?_
  · intro x _hx
    exact (lowerBarrierRaw_hasDerivAt κ κtilde D x).differentiableAt.differentiableWithinAt
  · intro x hx
    exact lowerBarrierRaw_deriv_nonpos_of_xplus_le hκ hgap hD
      (by
        have hx' : lowerBarrierXPlus κ κtilde D < x := by
          simpa using hx
        exact hx'.le)

theorem lowerBarrierRaw_deriv_nonneg_of_le_xplus
    {κ κtilde D x : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hx : x ≤ lowerBarrierXPlus κ κtilde D) :
    0 ≤ deriv (lowerBarrierRaw κ κtilde D) x := by
  have hκtilde_pos : 0 < κtilde := by linarith
  have harg_pos : 0 < κtilde * D / κ := by positivity
  have hlog_ge : Real.log (κtilde * D / κ) ≥ (κtilde - κ) * x := by
    rw [lowerBarrierXPlus] at hx
    simpa [mul_comm] using (le_div_iff₀ hgap).mp hx
  have hexp_ge :
      Real.exp 0 ≤
        Real.exp (Real.log (κtilde * D / κ) + (-(κtilde - κ) * x)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hcrit_ge :
      κ ≤ D * κtilde * Real.exp (-(κtilde - κ) * x) := by
    have hle :
        1 ≤ (κtilde * D / κ) * Real.exp (-(κtilde - κ) * x) := by
      simpa [Real.exp_add, Real.exp_log harg_pos] using hexp_ge
    have hκ_nonneg : 0 ≤ κ := hκ.le
    have hmul := mul_le_mul_of_nonneg_right hle hκ_nonneg
    have hκ_ne : κ ≠ 0 := ne_of_gt hκ
    field_simp [hκ_ne] at hmul
    convert hmul using 1
    ring_nf
  rw [lowerBarrierRaw_deriv]
  have hexp :
      Real.exp (-κtilde * x) =
        Real.exp (-κ * x) * Real.exp (-(κtilde - κ) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  nlinarith [Real.exp_pos (-κ * x)]

theorem lowerBarrierRaw_pos_at_xplus
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    0 < lowerBarrierRaw κ κtilde D (lowerBarrierXPlus κ κtilde D) :=
  lowerBarrierRaw_pos_of_xminus_lt hgap hD
    (lowerBarrierXMinus_lt_xplus hκ hgap hD)

def lowerBarrierPlateau (κ κtilde D : ℝ) : ℝ → ℝ :=
  fun x =>
    if x ≤ lowerBarrierXPlus κ κtilde D then
      lowerBarrierRaw κ κtilde D (lowerBarrierXPlus κ κtilde D)
    else
      lowerBarrierRaw κ κtilde D x

theorem lowerBarrierPlateau_eq_const_of_le
    {κ κtilde D x : ℝ} (hx : x ≤ lowerBarrierXPlus κ κtilde D) :
    lowerBarrierPlateau κ κtilde D x =
      lowerBarrierRaw κ κtilde D (lowerBarrierXPlus κ κtilde D) := by
  simp [lowerBarrierPlateau, hx]

theorem lowerBarrierPlateau_eq_raw_of_xplus_lt
    {κ κtilde D x : ℝ} (hx : lowerBarrierXPlus κ κtilde D < x) :
    lowerBarrierPlateau κ κtilde D x = lowerBarrierRaw κ κtilde D x := by
  simp [lowerBarrierPlateau, not_le.mpr hx]

theorem lowerBarrierPlateau_continuous (κ κtilde D : ℝ) :
    Continuous (lowerBarrierPlateau κ κtilde D) := by
  unfold lowerBarrierPlateau
  exact continuous_if_le continuous_id continuous_const
    continuous_const.continuousOn
    (lowerBarrierRaw_continuous κ κtilde D).continuousOn
    (fun x hx => by rw [hx])

theorem lowerBarrierPlateau_pos
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (x : ℝ) :
    0 < lowerBarrierPlateau κ κtilde D x := by
  by_cases hx : x ≤ lowerBarrierXPlus κ κtilde D
  · rw [lowerBarrierPlateau_eq_const_of_le hx]
    exact lowerBarrierRaw_pos_at_xplus hκ hgap hD
  · have hxlt : lowerBarrierXPlus κ κtilde D < x := lt_of_not_ge hx
    rw [lowerBarrierPlateau_eq_raw_of_xplus_lt hxlt]
    exact lowerBarrierRaw_pos_of_xminus_lt hgap hD
      (lt_trans (lowerBarrierXMinus_lt_xplus hκ hgap hD) hxlt)

theorem lowerBarrierPlateau_le_exp
    {κ κtilde D : ℝ} (hκ : 0 ≤ κ) (hD : 0 ≤ D) (x : ℝ) :
    lowerBarrierPlateau κ κtilde D x ≤ Real.exp (-κ * x) := by
  by_cases hx : x ≤ lowerBarrierXPlus κ κtilde D
  · rw [lowerBarrierPlateau_eq_const_of_le hx]
    have hraw_le :
        lowerBarrierRaw κ κtilde D (lowerBarrierXPlus κ κtilde D) ≤
          Real.exp (-κ * lowerBarrierXPlus κ κtilde D) :=
      lowerBarrierRaw_le_exp hD
    have hexp_le :
        Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ Real.exp (-κ * x) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hκ (sub_nonneg.mpr hx)]
    exact le_trans hraw_le hexp_le
  · have hxlt : lowerBarrierXPlus κ κtilde D < x := lt_of_not_ge hx
    rw [lowerBarrierPlateau_eq_raw_of_xplus_lt hxlt]
    exact lowerBarrierRaw_le_exp hD

theorem lowerBarrierPlateau_le_exp_xplus
    {κ κtilde D : ℝ} (hκ : 0 ≤ κ) (hD : 0 ≤ D) (x : ℝ) :
    lowerBarrierPlateau κ κtilde D x ≤
      Real.exp (-κ * lowerBarrierXPlus κ κtilde D) := by
  by_cases hx : x ≤ lowerBarrierXPlus κ κtilde D
  · rw [lowerBarrierPlateau_eq_const_of_le hx]
    exact lowerBarrierRaw_le_exp hD
  · have hxlt : lowerBarrierXPlus κ κtilde D < x := lt_of_not_ge hx
    calc
      lowerBarrierPlateau κ κtilde D x ≤ Real.exp (-κ * x) :=
        lowerBarrierPlateau_le_exp hκ hD x
      _ ≤ Real.exp (-κ * lowerBarrierXPlus κ κtilde D) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hκ (sub_nonneg.mpr hxlt.le)]

theorem lowerBarrierPlateau_rpow_le_exp
    {κ κtilde D a : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D) (ha : 0 ≤ a) (x : ℝ) :
    (lowerBarrierPlateau κ κtilde D x) ^ a ≤
      (Real.exp (-κ * x)) ^ a :=
  Real.rpow_le_rpow
    (lowerBarrierPlateau_pos hκ hgap hD x).le
    (lowerBarrierPlateau_le_exp hκ.le hD.le x) ha

theorem lowerBarrierPlateau_rpow_le_exp_mul
    {κ κtilde D a : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D) (ha : 0 ≤ a) (x : ℝ) :
    (lowerBarrierPlateau κ κtilde D x) ^ a ≤ Real.exp (-κ * a * x) := by
  calc
    (lowerBarrierPlateau κ κtilde D x) ^ a ≤
        (Real.exp (-κ * x)) ^ a :=
      lowerBarrierPlateau_rpow_le_exp hκ hgap hD ha x
    _ = Real.exp (-κ * a * x) := by
      rw [← Real.exp_mul]
      congr 1
      ring

theorem lowerBarrierPlateau_rpow_le_exp_xplus
    {κ κtilde D a : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D) (ha : 0 ≤ a) (x : ℝ) :
    (lowerBarrierPlateau κ κtilde D x) ^ a ≤
      (Real.exp (-κ * lowerBarrierXPlus κ κtilde D)) ^ a :=
  Real.rpow_le_rpow
    (lowerBarrierPlateau_pos hκ hgap hD x).le
    (lowerBarrierPlateau_le_exp_xplus hκ.le hD.le x) ha

theorem lowerBarrierPlateau_rpow_le_exp_xplus_mul
    {κ κtilde D a : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D) (ha : 0 ≤ a) (x : ℝ) :
    (lowerBarrierPlateau κ κtilde D x) ^ a ≤
      Real.exp (-κ * a * lowerBarrierXPlus κ κtilde D) := by
  calc
    (lowerBarrierPlateau κ κtilde D x) ^ a ≤
        (Real.exp (-κ * lowerBarrierXPlus κ κtilde D)) ^ a :=
      lowerBarrierPlateau_rpow_le_exp_xplus hκ hgap hD ha x
    _ = Real.exp (-κ * a * lowerBarrierXPlus κ κtilde D) := by
      rw [← Real.exp_mul]
      congr 1
      ring

theorem lowerBarrierPlateau_isBddFun
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    IsBddFun (lowerBarrierPlateau κ κtilde D) := by
  refine ⟨Real.exp (-κ * lowerBarrierXPlus κ κtilde D), ?_⟩
  intro x
  rw [abs_of_nonneg (lowerBarrierPlateau_pos hκ hgap hD x).le]
  exact lowerBarrierPlateau_le_exp_xplus hκ.le hD.le x

theorem lowerBarrierPlateau_cunif_bdd
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    IsCUnifBdd (lowerBarrierPlateau κ κtilde D) :=
  ⟨lowerBarrierPlateau_continuous κ κtilde D,
    lowerBarrierPlateau_isBddFun hκ hgap hD⟩

theorem lowerBarrierPlateau_antitone
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    Antitone (lowerBarrierPlateau κ κtilde D) := by
  intro x y hxy
  by_cases hy : y ≤ lowerBarrierXPlus κ κtilde D
  · have hx : x ≤ lowerBarrierXPlus κ κtilde D := le_trans hxy hy
    rw [lowerBarrierPlateau_eq_const_of_le hx,
      lowerBarrierPlateau_eq_const_of_le hy]
  · have hylt : lowerBarrierXPlus κ κtilde D < y := lt_of_not_ge hy
    by_cases hx : x ≤ lowerBarrierXPlus κ κtilde D
    · rw [lowerBarrierPlateau_eq_const_of_le hx,
        lowerBarrierPlateau_eq_raw_of_xplus_lt hylt]
      exact lowerBarrierRaw_antitoneOn_Ici_xplus hκ hgap hD
        (le_rfl : lowerBarrierXPlus κ κtilde D ≤ lowerBarrierXPlus κ κtilde D)
        hylt.le hylt.le
    · have hxlt : lowerBarrierXPlus κ κtilde D < x := lt_of_not_ge hx
      rw [lowerBarrierPlateau_eq_raw_of_xplus_lt hxlt,
        lowerBarrierPlateau_eq_raw_of_xplus_lt hylt]
      exact lowerBarrierRaw_antitoneOn_Ici_xplus hκ hgap hD
        hxlt.le hylt.le hxy

def InWaveTrapSet (κ M : ℝ) (u : ℝ → ℝ) : Prop :=
  IsCUnifBdd u ∧ ∀ x, 0 ≤ u x ∧ u x ≤ upperBarrier κ M x

def NonincreasingProfile (u : ℝ → ℝ) : Prop :=
  Antitone u

def InMonotoneWaveTrapSet (κ M : ℝ) (u : ℝ → ℝ) : Prop :=
  InWaveTrapSet κ M u ∧ NonincreasingProfile u

def WaveTrapSet (κ M : ℝ) : Set (ℝ → ℝ) :=
  {u | InWaveTrapSet κ M u}

def MonotoneWaveTrapSet (κ M : ℝ) : Set (ℝ → ℝ) :=
  {u | InMonotoneWaveTrapSet κ M u}

theorem IsBddFun.convex_combo
    {u v : ℝ → ℝ} {θ : ℝ}
    (_hθ0 : 0 ≤ θ) (_hθ1 : θ ≤ 1)
    (hu : IsBddFun u) (hv : IsBddFun v) :
    IsBddFun (fun x => θ * u x + (1 - θ) * v x) := by
  rcases hu with ⟨Mu, hu⟩
  rcases hv with ⟨Mv, hv⟩
  refine ⟨|θ| * Mu + |1 - θ| * Mv, ?_⟩
  intro x
  calc
    |θ * u x + (1 - θ) * v x| ≤
        |θ * u x| + |(1 - θ) * v x| := abs_add_le _ _
    _ = |θ| * |u x| + |1 - θ| * |v x| := by rw [abs_mul, abs_mul]
    _ ≤ |θ| * Mu + |1 - θ| * Mv := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hu x) (abs_nonneg θ))
        (mul_le_mul_of_nonneg_left (hv x) (abs_nonneg (1 - θ)))

theorem IsCUnifBdd.convex_combo
    {u v : ℝ → ℝ} {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hu : IsCUnifBdd u) (hv : IsCUnifBdd v) :
    IsCUnifBdd (fun x => θ * u x + (1 - θ) * v x) := by
  constructor
  · exact (continuous_const.mul hu.1).add (continuous_const.mul hv.1)
  · exact IsBddFun.convex_combo hθ0 hθ1 hu.2 hv.2

theorem IsBddFun.zero :
    IsBddFun (fun _ : ℝ => (0 : ℝ)) := by
  exact ⟨0, by simp⟩

theorem IsBddFun.shift
    {u : ℝ → ℝ} (hu : IsBddFun u) (a : ℝ) :
    IsBddFun (fun x => u (x + a)) := by
  rcases hu with ⟨M, hM⟩
  exact ⟨M, fun x => hM (x + a)⟩

theorem IsCUnifBdd.zero :
    IsCUnifBdd (fun _ : ℝ => (0 : ℝ)) := by
  exact ⟨continuous_const, IsBddFun.zero⟩

theorem IsCUnifBdd.shift
    {u : ℝ → ℝ} (hu : IsCUnifBdd u) (a : ℝ) :
    IsCUnifBdd (fun x => u (x + a)) := by
  constructor
  · exact hu.1.comp (continuous_id.add continuous_const)
  · exact IsBddFun.shift hu.2 a

theorem ContDiff.two_shift
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (a : ℝ) :
    ContDiff ℝ 2 (fun x => u (x + a)) := by
  exact hu.comp (contDiff_id.add contDiff_const)

theorem NonnegativeInitialDatum.shift
    {u₀ : ℝ → ℝ} (h : NonnegativeInitialDatum u₀) (a : ℝ) :
    NonnegativeInitialDatum (fun x => u₀ (x + a)) :=
  ⟨IsCUnifBdd.shift h.1 a, fun x => h.2 (x + a)⟩

theorem InWaveTrapSet.cunif_bdd {κ M : ℝ} {u : ℝ → ℝ}
    (h : InWaveTrapSet κ M u) :
    IsCUnifBdd u :=
  h.1

theorem InWaveTrapSet.nonneg {κ M : ℝ} {u : ℝ → ℝ}
    (h : InWaveTrapSet κ M u) (x : ℝ) :
    0 ≤ u x :=
  (h.2 x).1

theorem InWaveTrapSet.le_upperBarrier {κ M : ℝ} {u : ℝ → ℝ}
    (h : InWaveTrapSet κ M u) (x : ℝ) :
    u x ≤ upperBarrier κ M x :=
  (h.2 x).2

theorem InWaveTrapSet.le_M {κ M : ℝ} {u : ℝ → ℝ}
    (h : InWaveTrapSet κ M u) (x : ℝ) :
    u x ≤ M :=
  le_trans (h.le_upperBarrier x) (min_le_left _ _)

theorem InWaveTrapSet.le_exp {κ M : ℝ} {u : ℝ → ℝ}
    (h : InWaveTrapSet κ M u) (x : ℝ) :
    u x ≤ Real.exp (-κ * x) :=
  le_trans (h.le_upperBarrier x) (min_le_right _ _)

theorem InWaveTrapSet.le_one_of_M_le_one {κ M : ℝ} {u : ℝ → ℝ}
    (h : InWaveTrapSet κ M u) (hM : M ≤ 1) (x : ℝ) :
    u x ≤ 1 :=
  le_trans (h.le_M x) hM

theorem InWaveTrapSet.rpow_le_M
    {κ M : ℝ} {u : ℝ → ℝ} {a : ℝ}
    (h : InWaveTrapSet κ M u) (ha : 0 ≤ a) (x : ℝ) :
    (u x) ^ a ≤ M ^ a :=
  Real.rpow_le_rpow (h.nonneg x) (h.le_M x) ha

theorem InWaveTrapSet.rpow_le_exp
    {κ M : ℝ} {u : ℝ → ℝ} {a : ℝ}
    (h : InWaveTrapSet κ M u) (ha : 0 ≤ a) (x : ℝ) :
    (u x) ^ a ≤ (Real.exp (-κ * x)) ^ a :=
  Real.rpow_le_rpow (h.nonneg x) (h.le_exp x) ha

theorem InWaveTrapSet.rpow_le_exp_mul
    {κ M : ℝ} {u : ℝ → ℝ} {a : ℝ}
    (h : InWaveTrapSet κ M u) (ha : 0 ≤ a) (x : ℝ) :
    (u x) ^ a ≤ Real.exp (-κ * a * x) := by
  calc
    (u x) ^ a ≤ (Real.exp (-κ * x)) ^ a := h.rpow_le_exp ha x
    _ = Real.exp (-κ * a * x) := by
      rw [← Real.exp_mul]
      congr 1
      ring

theorem frozenElliptic_le_M_of_inWaveTrapSet
    (p : CMParams) {κ M : ℝ} {u : ℝ → ℝ}
    (hM : 0 < M) (hM1 : M ≤ 1)
    (hu : InWaveTrapSet κ M u) (x : ℝ) :
    frozenElliptic p u x ≤ M := by
  apply frozenElliptic_le_of_rpow_le p hM.le hu.cunif_bdd.1 hu.nonneg
  intro y
  calc (u y) ^ p.γ ≤ M ^ p.γ :=
        Real.rpow_le_rpow (hu.nonneg y) (hu.le_M y)
          (by linarith [p.hγ])
    _ ≤ M ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hM hM1 p.hγ
    _ = M := Real.rpow_one M

theorem frozenElliptic_le_M_of_inMonotoneWaveTrapSet
    (p : CMParams) {κ M : ℝ} {u : ℝ → ℝ}
    (hM : 0 < M) (hM1 : M ≤ 1)
    (hu : InMonotoneWaveTrapSet κ M u) (x : ℝ) :
    frozenElliptic p u x ≤ M :=
  frozenElliptic_le_M_of_inWaveTrapSet p hM hM1 hu.1 x

theorem paperWaveOperator_const_nonpos_neg
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    (_hκ : 0 < κ) (hM : 1 ≤ M)
    (hu : InWaveTrapSet κ M u) (x : ℝ) :
    paperWaveOperator p c u (fun _ => M) x ≤ 0 := by
  rw [paperWaveOperator_const_eq p hu.cunif_bdd hu.nonneg x]
  have hM_pos : 0 < M := by linarith
  have hV_le : frozenElliptic p u x ≤ M ^ p.γ :=
    frozenElliptic_le_of_rpow_le p
      (Real.rpow_nonneg hM_pos.le p.γ) hu.cunif_bdd.1 hu.nonneg
      (fun y => hu.rpow_le_M (by linarith [p.hγ]) y) x
  have hchem : -p.χ * M ^ (p.m - 1) * frozenElliptic p u x ≤
      -p.χ * M ^ (p.m + p.γ - 1) := by
    have h1 : 0 ≤ -p.χ := by linarith
    have h2 : 0 ≤ M ^ (p.m - 1) := Real.rpow_nonneg hM_pos.le _
    have h3 : M ^ (p.m - 1) * frozenElliptic p u x ≤
        M ^ (p.m - 1) * M ^ p.γ :=
      mul_le_mul_of_nonneg_left hV_le h2
    have h4 : M ^ (p.m - 1) * M ^ p.γ = M ^ (p.m + p.γ - 1) := by
      rw [← Real.rpow_add hM_pos]
      congr 1; ring
    calc -p.χ * M ^ (p.m - 1) * frozenElliptic p u x
          = -p.χ * (M ^ (p.m - 1) * frozenElliptic p u x) := by ring
      _ ≤ -p.χ * (M ^ (p.m - 1) * M ^ p.γ) :=
            mul_le_mul_of_nonneg_left h3 h1
      _ = -p.χ * M ^ (p.m + p.γ - 1) := by rw [h4]
  have hα_le : M ^ p.α ≤ M ^ (p.m + p.γ - 1) :=
    Real.rpow_le_rpow_of_exponent_le hM hα
  have hlogistic : M ^ p.α ≥ 1 :=
    Real.one_le_rpow hM (by linarith [p.hα])
  apply mul_nonpos_of_nonneg_of_nonpos hM_pos.le
  nlinarith

theorem one_le_one_sub_chi_mul_M_rpow_alpha
    (p : CMParams) {M : ℝ} (hχ : p.χ < 1)
    (hM : 0 ≤ M)
    (hMchi : (1 / (1 - p.χ)) ^ (1 / p.α) ≤ M) :
    1 ≤ (1 - p.χ) * M ^ p.α := by
  have hden_pos : 0 < 1 - p.χ := by linarith
  have hbase_pos : 0 < 1 / (1 - p.χ) := div_pos one_pos hden_pos
  have hα_pos : 0 < p.α := lt_of_lt_of_le one_pos p.hα
  have hpow_le :
      (1 / (1 - p.χ)) ≤ M ^ p.α := by
    calc
      1 / (1 - p.χ)
          = ((1 / (1 - p.χ)) ^ (1 / p.α)) ^ p.α := by
              rw [← Real.rpow_mul hbase_pos.le]
              have hα_ne : p.α ≠ 0 := ne_of_gt hα_pos
              have hmul_exp : (1 / p.α) * p.α = 1 := by
                field_simp [hα_ne]
              rw [hmul_exp, Real.rpow_one]
      _ ≤ M ^ p.α :=
          Real.rpow_le_rpow
            (Real.rpow_nonneg hbase_pos.le _) hMchi
            (le_of_lt hα_pos)
  have hmul := mul_le_mul_of_nonneg_left hpow_le hden_pos.le
  have hleft : (1 - p.χ) * (1 / (1 - p.χ)) = 1 := by
    field_simp [ne_of_gt hden_pos]
  nlinarith

theorem paperWaveOperator_const_nonpos_pos
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hχ_nonneg : 0 ≤ p.χ) (hχ : p.χ < chiStar p)
    (hα : p.α = p.m + p.γ - 1)
    (hM : 1 ≤ M)
    (hMchi : (1 / (1 - p.χ)) ^ (1 / p.α) ≤ M)
    (hu : InWaveTrapSet κ M u) (x : ℝ) :
    paperWaveOperator p c u (fun _ => M) x ≤ 0 := by
  rw [paperWaveOperator_const_eq p hu.cunif_bdd hu.nonneg x]
  have hM_nonneg : 0 ≤ M := le_trans zero_le_one hM
  have hχ_lt_one : p.χ < 1 := lt_of_lt_of_le hχ (chiStar_le_one p)
  have hmain :
      1 ≤ (1 - p.χ) * M ^ p.α :=
    one_le_one_sub_chi_mul_M_rpow_alpha p hχ_lt_one hM_nonneg hMchi
  have hV_nonneg : 0 ≤ frozenElliptic p u x :=
    frozenElliptic_nonneg p hu.nonneg x
  have hpow_nonneg : 0 ≤ M ^ (p.m - 1) :=
    Real.rpow_nonneg hM_nonneg (p.m - 1)
  have hVterm :
      -p.χ * M ^ (p.m - 1) * frozenElliptic p u x ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hχ_nonneg) hpow_nonneg)
      hV_nonneg
  have hpow_eq : M ^ (p.m + p.γ - 1) = M ^ p.α := by
    rw [hα]
  have hinside :
      1 - p.χ * M ^ (p.m - 1) * frozenElliptic p u x -
          (M ^ p.α - p.χ * M ^ (p.m + p.γ - 1)) ≤ 0 := by
    rw [hpow_eq]
    nlinarith
  exact mul_nonpos_of_nonneg_of_nonpos hM_nonneg hinside

theorem paperWaveOperator_upperBarrier_const_region_eq
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    {x : ℝ} (hx : M < Real.exp (-κ * x)) :
    paperWaveOperator p c u (upperBarrier κ M) x =
      M * (1 - p.χ * M ^ (p.m - 1) * frozenElliptic p u x
        - (M ^ p.α - p.χ * M ^ (p.m + p.γ - 1))) := by
  unfold paperWaveOperator
  rw [upperBarrier_iteratedDeriv_two_eq_zero_of_const_lt hx,
    upperBarrier_deriv_eq_zero_of_const_lt hx,
    upperBarrier_eq_M_of_le_exp (le_of_lt hx)]
  ring

theorem paperWaveOperator_upperBarrier_const_region_nonpos_neg
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hκ : 0 < κ) (hM : 1 ≤ M)
    (hu : InWaveTrapSet κ M u) {x : ℝ}
    (hx : M < Real.exp (-κ * x)) :
    paperWaveOperator p c u (upperBarrier κ M) x ≤ 0 := by
  have hconst := paperWaveOperator_const_nonpos_neg
    p (c := c) hχ hα hκ hM hu x
  rw [paperWaveOperator_const_eq p hu.cunif_bdd hu.nonneg x] at hconst
  rw [paperWaveOperator_upperBarrier_const_region_eq p hx]
  exact hconst

theorem paperWaveOperator_upperBarrier_const_region_nonpos_pos
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hχ_nonneg : 0 ≤ p.χ) (hχ : p.χ < chiStar p)
    (hα : p.α = p.m + p.γ - 1)
    (hM : 1 ≤ M)
    (hMchi : (1 / (1 - p.χ)) ^ (1 / p.α) ≤ M)
    (hu : InWaveTrapSet κ M u) {x : ℝ}
    (hx : M < Real.exp (-κ * x)) :
    paperWaveOperator p c u (upperBarrier κ M) x ≤ 0 := by
  have hconst := paperWaveOperator_const_nonpos_pos
    p (c := c) hχ_nonneg hχ hα hM hMchi hu x
  rw [paperWaveOperator_const_eq p hu.cunif_bdd hu.nonneg x] at hconst
  rw [paperWaveOperator_upperBarrier_const_region_eq p hx]
  exact hconst

theorem paperWaveOperator_upperBarrier_exp_region_eq_of_kappa_speed
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hκ : κ ≠ 0) (hc : c = κ + κ⁻¹)
    {x : ℝ} (hx : Real.exp (-κ * x) < M) :
    paperWaveOperator p c u (upperBarrier κ M) x =
      -expDecay κ x * (expDecay κ x) ^ p.α
        - p.χ * p.m * (expDecay κ x) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x * (-κ * expDecay κ x)
        + expDecay κ x *
          (-p.χ * (expDecay κ x) ^ (p.m - 1) *
            frozenElliptic p u x
          + p.χ * (expDecay κ x) ^ (p.m + p.γ - 1)) := by
  unfold paperWaveOperator
  rw [upperBarrier_iteratedDeriv_two_eq_exp_of_lt hx,
    upperBarrier_deriv_eq_exp_of_lt hx,
    upperBarrier_eq_exp_of_exp_le (le_of_lt hx)]
  simp only [expDecay]
  have hexp : Real.exp (-κ * x) = Real.exp (-(κ * x)) := by
    congr 1
    ring
  rw [hexp]
  have hlin :
      κ ^ 2 * Real.exp (-(κ * x)) + c * (-κ * Real.exp (-(κ * x))) +
          Real.exp (-(κ * x)) = 0 := by
    have h := expDecay_linear_part_eq_of_kappa_speed
      (κ := κ) (c := c) (x := x) hκ hc
    simpa [expDecay, expDecay_iteratedDeriv_two, expDecay_deriv] using h
  nlinarith

theorem paperWaveOperator_upperBarrier_exp_region_nonpos_of_dominance
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hκ : κ ≠ 0) (hc : c = κ + κ⁻¹)
    {x : ℝ} (hx : Real.exp (-κ * x) < M)
    (hdom :
      - p.χ * p.m * (expDecay κ x) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x * (-κ * expDecay κ x)
        + expDecay κ x *
          (-p.χ * (expDecay κ x) ^ (p.m - 1) *
            frozenElliptic p u x
          + p.χ * (expDecay κ x) ^ (p.m + p.γ - 1)) ≤
        expDecay κ x * (expDecay κ x) ^ p.α) :
    paperWaveOperator p c u (upperBarrier κ M) x ≤ 0 := by
  rw [paperWaveOperator_upperBarrier_exp_region_eq_of_kappa_speed p hκ hc hx]
  nlinarith

theorem InWaveTrapSet.zero {κ M : ℝ} (hM : 0 ≤ M) :
    InWaveTrapSet κ M (fun _ : ℝ => (0 : ℝ)) := by
  refine ⟨IsCUnifBdd.zero, ?_⟩
  intro x
  exact ⟨le_rfl, upperBarrier_nonneg hM x⟩

theorem upperBarrier_mem_InWaveTrapSet {κ M : ℝ} (hM : 0 ≤ M) :
    InWaveTrapSet κ M (upperBarrier κ M) := by
  refine ⟨upperBarrier_cunif_bdd hM, ?_⟩
  intro x
  exact ⟨upperBarrier_nonneg hM x, le_rfl⟩

theorem lowerBarrierPlateau_mem_InWaveTrapSet_exp_xplus
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    InWaveTrapSet κ
      (Real.exp (-κ * lowerBarrierXPlus κ κtilde D))
      (lowerBarrierPlateau κ κtilde D) := by
  refine ⟨lowerBarrierPlateau_cunif_bdd hκ hgap hD, ?_⟩
  intro x
  refine ⟨(lowerBarrierPlateau_pos hκ hgap hD x).le, ?_⟩
  exact le_min
    (lowerBarrierPlateau_le_exp_xplus hκ.le hD.le x)
    (lowerBarrierPlateau_le_exp hκ.le hD.le x)

theorem InWaveTrapSet.convex_combo
    {κ M : ℝ} {u v : ℝ → ℝ} {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hu : InWaveTrapSet κ M u) (hv : InWaveTrapSet κ M v) :
    InWaveTrapSet κ M (fun x => θ * u x + (1 - θ) * v x) := by
  refine ⟨IsCUnifBdd.convex_combo hθ0 hθ1 hu.cunif_bdd hv.cunif_bdd, ?_⟩
  intro x
  constructor
  · exact add_nonneg
      (mul_nonneg hθ0 (hu.nonneg x))
      (mul_nonneg (sub_nonneg.mpr hθ1) (hv.nonneg x))
  · calc
      θ * u x + (1 - θ) * v x ≤
          θ * upperBarrier κ M x + (1 - θ) * upperBarrier κ M x :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hu.le_upperBarrier x) hθ0)
          (mul_le_mul_of_nonneg_left (hv.le_upperBarrier x) (sub_nonneg.mpr hθ1))
      _ = upperBarrier κ M x := by ring

theorem InWaveTrapSet.mono_M
    {κ M₁ M₂ : ℝ} {u : ℝ → ℝ}
    (hM : M₁ ≤ M₂) (h : InWaveTrapSet κ M₁ u) :
    InWaveTrapSet κ M₂ u := by
  refine ⟨h.cunif_bdd, ?_⟩
  intro x
  exact
    ⟨h.nonneg x,
      le_trans (h.le_upperBarrier x) (upperBarrier_mono_M hM x)⟩

theorem lowerBarrierPlateau_mem_InWaveTrapSet_of_exp_xplus_le
    {κ κtilde D M : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D)
    (hM : Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ M) :
    InWaveTrapSet κ M (lowerBarrierPlateau κ κtilde D) :=
  InWaveTrapSet.mono_M hM
    (lowerBarrierPlateau_mem_InWaveTrapSet_exp_xplus hκ hgap hD)

theorem lowerBarrierPlateau_mem_InMonotoneWaveTrapSet_exp_xplus
    {κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D) :
    InMonotoneWaveTrapSet κ
      (Real.exp (-κ * lowerBarrierXPlus κ κtilde D))
      (lowerBarrierPlateau κ κtilde D) :=
  ⟨lowerBarrierPlateau_mem_InWaveTrapSet_exp_xplus hκ hgap hD,
    lowerBarrierPlateau_antitone hκ hgap hD⟩

theorem lowerBarrierPlateau_mem_InMonotoneWaveTrapSet_of_exp_xplus_le
    {κ κtilde D M : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D)
    (hM : Real.exp (-κ * lowerBarrierXPlus κ κtilde D) ≤ M) :
    InMonotoneWaveTrapSet κ M (lowerBarrierPlateau κ κtilde D) :=
  ⟨lowerBarrierPlateau_mem_InWaveTrapSet_of_exp_xplus_le hκ hgap hD hM,
    lowerBarrierPlateau_antitone hκ hgap hD⟩

theorem exists_D_gt_lowerBarrierPlateau_mem_InWaveTrapSet
    {κ κtilde M B : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hM : 0 < M) (hB : 0 ≤ B) :
    ∃ D > B, InWaveTrapSet κ M (lowerBarrierPlateau κ κtilde D) := by
  rcases exists_D_gt_with_exp_xplus_le (κ := κ) (κtilde := κtilde)
      (M := M) (B := B) hκ hgap hM with
    ⟨D, hBD, hheight⟩
  have hD : 0 < D := lt_of_le_of_lt hB hBD
  exact
    ⟨D, hBD,
      lowerBarrierPlateau_mem_InWaveTrapSet_of_exp_xplus_le
        hκ hgap hD hheight⟩

theorem exists_D_gt_lowerBarrierPlateau_mem_InMonotoneWaveTrapSet
    {κ κtilde M B : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hM : 0 < M) (hB : 0 ≤ B) :
    ∃ D > B, InMonotoneWaveTrapSet κ M (lowerBarrierPlateau κ κtilde D) := by
  rcases exists_D_gt_with_exp_xplus_le (κ := κ) (κtilde := κtilde)
      (M := M) (B := B) hκ hgap hM with
    ⟨D, hBD, hheight⟩
  have hD : 0 < D := lt_of_le_of_lt hB hBD
  exact
    ⟨D, hBD,
      lowerBarrierPlateau_mem_InMonotoneWaveTrapSet_of_exp_xplus_le
        hκ hgap hD hheight⟩

theorem WaveTrapSet_subset_of_M_le
    {κ M₁ M₂ : ℝ} (hM : M₁ ≤ M₂) :
    WaveTrapSet κ M₁ ⊆ WaveTrapSet κ M₂ := by
  intro u hu
  exact InWaveTrapSet.mono_M hM hu

theorem InWaveTrapSet.set_nonempty {κ M : ℝ} (hM : 0 ≤ M) :
    ({u : ℝ → ℝ | InWaveTrapSet κ M u}).Nonempty :=
  ⟨fun _ => 0, InWaveTrapSet.zero hM⟩

theorem WaveTrapSet_nonempty {κ M : ℝ} (hM : 0 ≤ M) :
    (WaveTrapSet κ M).Nonempty :=
  InWaveTrapSet.set_nonempty hM

theorem InWaveTrapSet.set_convex (κ M : ℝ) :
    Convex ℝ {u : ℝ → ℝ | InWaveTrapSet κ M u} := by
  rw [convex_iff_add_mem]
  intro u hu v hv a b ha hb hab
  have ha_le_one : a ≤ 1 := by nlinarith
  have hb_eq : b = 1 - a := by linarith
  convert InWaveTrapSet.convex_combo ha ha_le_one hu hv using 1
  ext x
  simp [hb_eq, smul_eq_mul]

theorem WaveTrapSet_convex (κ M : ℝ) :
    Convex ℝ (WaveTrapSet κ M) :=
  InWaveTrapSet.set_convex κ M

theorem InMonotoneWaveTrapSet.trap
    {κ M : ℝ} {u : ℝ → ℝ}
    (h : InMonotoneWaveTrapSet κ M u) :
    InWaveTrapSet κ M u :=
  h.1

theorem InMonotoneWaveTrapSet.antitone
    {κ M : ℝ} {u : ℝ → ℝ}
    (h : InMonotoneWaveTrapSet κ M u) :
    Antitone u :=
  h.2

theorem InMonotoneWaveTrapSet.deriv_nonpos
    {κ M : ℝ} {u : ℝ → ℝ}
    (h : InMonotoneWaveTrapSet κ M u) (x : ℝ) :
    deriv u x ≤ 0 :=
  h.antitone.deriv_nonpos

theorem InMonotoneWaveTrapSet.nonneg
    {κ M : ℝ} {u : ℝ → ℝ}
    (h : InMonotoneWaveTrapSet κ M u) (x : ℝ) :
    0 ≤ u x :=
  h.trap.nonneg x

theorem InMonotoneWaveTrapSet.le_upperBarrier
    {κ M : ℝ} {u : ℝ → ℝ}
    (h : InMonotoneWaveTrapSet κ M u) (x : ℝ) :
    u x ≤ upperBarrier κ M x :=
  h.trap.le_upperBarrier x

theorem InMonotoneWaveTrapSet.le_M
    {κ M : ℝ} {u : ℝ → ℝ}
    (h : InMonotoneWaveTrapSet κ M u) (x : ℝ) :
    u x ≤ M :=
  h.trap.le_M x

theorem InMonotoneWaveTrapSet.le_exp
    {κ M : ℝ} {u : ℝ → ℝ}
    (h : InMonotoneWaveTrapSet κ M u) (x : ℝ) :
    u x ≤ Real.exp (-κ * x) :=
  h.trap.le_exp x

theorem InMonotoneWaveTrapSet.le_one_of_M_le_one
    {κ M : ℝ} {u : ℝ → ℝ}
    (h : InMonotoneWaveTrapSet κ M u) (hM : M ≤ 1) (x : ℝ) :
    u x ≤ 1 :=
  h.trap.le_one_of_M_le_one hM x

theorem InMonotoneWaveTrapSet.rpow_le_M
    {κ M : ℝ} {u : ℝ → ℝ} {a : ℝ}
    (h : InMonotoneWaveTrapSet κ M u) (ha : 0 ≤ a) (x : ℝ) :
    (u x) ^ a ≤ M ^ a :=
  h.trap.rpow_le_M ha x

theorem InMonotoneWaveTrapSet.rpow_le_exp
    {κ M : ℝ} {u : ℝ → ℝ} {a : ℝ}
    (h : InMonotoneWaveTrapSet κ M u) (ha : 0 ≤ a) (x : ℝ) :
    (u x) ^ a ≤ (Real.exp (-κ * x)) ^ a :=
  h.trap.rpow_le_exp ha x

theorem InMonotoneWaveTrapSet.rpow_le_exp_mul
    {κ M : ℝ} {u : ℝ → ℝ} {a : ℝ}
    (h : InMonotoneWaveTrapSet κ M u) (ha : 0 ≤ a) (x : ℝ) :
    (u x) ^ a ≤ Real.exp (-κ * a * x) :=
  h.trap.rpow_le_exp_mul ha x

theorem InMonotoneWaveTrapSet.zero {κ M : ℝ} (hM : 0 ≤ M) :
    InMonotoneWaveTrapSet κ M (fun _ : ℝ => (0 : ℝ)) := by
  exact ⟨InWaveTrapSet.zero hM, antitone_const⟩

theorem upperBarrier_mem_InMonotoneWaveTrapSet
    {κ M : ℝ} (hκ : 0 ≤ κ) (hM : 0 ≤ M) :
    InMonotoneWaveTrapSet κ M (upperBarrier κ M) := by
  exact ⟨upperBarrier_mem_InWaveTrapSet hM, upperBarrier_antitone hκ⟩

theorem InMonotoneWaveTrapSet.convex_combo
    {κ M : ℝ} {u v : ℝ → ℝ} {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hv : InMonotoneWaveTrapSet κ M v) :
    InMonotoneWaveTrapSet κ M
      (fun x => θ * u x + (1 - θ) * v x) := by
  refine
    ⟨InWaveTrapSet.convex_combo hθ0 hθ1 hu.trap hv.trap, ?_⟩
  intro x y hxy
  exact add_le_add
    (mul_le_mul_of_nonneg_left (hu.antitone hxy) hθ0)
    (mul_le_mul_of_nonneg_left (hv.antitone hxy) (sub_nonneg.mpr hθ1))

theorem InMonotoneWaveTrapSet.mono_M
    {κ M₁ M₂ : ℝ} {u : ℝ → ℝ}
    (hM : M₁ ≤ M₂) (h : InMonotoneWaveTrapSet κ M₁ u) :
    InMonotoneWaveTrapSet κ M₂ u :=
  ⟨InWaveTrapSet.mono_M hM h.trap, h.antitone⟩

theorem MonotoneWaveTrapSet_subset_of_M_le
    {κ M₁ M₂ : ℝ} (hM : M₁ ≤ M₂) :
    MonotoneWaveTrapSet κ M₁ ⊆ MonotoneWaveTrapSet κ M₂ := by
  intro u hu
  exact InMonotoneWaveTrapSet.mono_M hM hu

theorem InMonotoneWaveTrapSet.set_nonempty {κ M : ℝ} (hM : 0 ≤ M) :
    ({u : ℝ → ℝ | InMonotoneWaveTrapSet κ M u}).Nonempty :=
  ⟨fun _ => 0, InMonotoneWaveTrapSet.zero hM⟩

theorem MonotoneWaveTrapSet_nonempty {κ M : ℝ} (hM : 0 ≤ M) :
    (MonotoneWaveTrapSet κ M).Nonempty :=
  InMonotoneWaveTrapSet.set_nonempty hM

theorem InMonotoneWaveTrapSet.set_convex (κ M : ℝ) :
    Convex ℝ {u : ℝ → ℝ | InMonotoneWaveTrapSet κ M u} := by
  rw [convex_iff_add_mem]
  intro u hu v hv a b ha hb hab
  have ha_le_one : a ≤ 1 := by nlinarith
  have hb_eq : b = 1 - a := by linarith
  convert InMonotoneWaveTrapSet.convex_combo ha ha_le_one hu hv using 1
  ext x
  simp [hb_eq, smul_eq_mul]

theorem MonotoneWaveTrapSet_convex (κ M : ℝ) :
    Convex ℝ (MonotoneWaveTrapSet κ M) :=
  InMonotoneWaveTrapSet.set_convex κ M

/-- Local-uniform convergence on compact intervals of the line.  This is the
topology used in the Schauder step of the traveling-wave construction. -/
def LocallyUniformConverges
    (fs : ℕ → ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ R > 0, ∀ ε > 0,
    ∀ᶠ n in atTop, ∀ x : ℝ, x ∈ Set.Icc (-R) R → |fs n x - f x| < ε

theorem LocallyUniformConverges.tendsto_at
    {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (h : LocallyUniformConverges fs f) (x : ℝ) :
    Tendsto (fun n : ℕ => fs n x) atTop (𝓝 (f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let R : ℝ := |x| + 1
  have hR : 0 < R := by
    dsimp [R]
    nlinarith [abs_nonneg x]
  have hxR : x ∈ Set.Icc (-R) R := by
    have hxabs : |x| ≤ R := by
      dsimp [R]
      nlinarith [abs_nonneg x]
    exact abs_le.mp hxabs
  rcases (eventually_atTop.1 (h R hR ε hε)) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  simpa [Real.dist_eq] using hN n hn x hxR

theorem LocallyUniformConverges.unique
    {fs : ℕ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hf : LocallyUniformConverges fs f)
    (hg : LocallyUniformConverges fs g) :
    f = g := by
  funext x
  exact tendsto_nhds_unique (hf.tendsto_at x) (hg.tendsto_at x)

theorem LocallyUniformConverges.comp_strictMono
    {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {subseq : ℕ → ℕ}
    (h : LocallyUniformConverges fs f) (hsubseq : StrictMono subseq) :
    LocallyUniformConverges (fun n => fs (subseq n)) f := by
  intro R hR ε hε
  exact hsubseq.tendsto_atTop.eventually (h R hR ε hε)

theorem LocallyUniformConverges.congr
    {fs gs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hfg : ∀ᶠ n in atTop, fs n = gs n)
    (h : LocallyUniformConverges fs f) :
    LocallyUniformConverges gs f := by
  intro R hR ε hε
  filter_upwards [hfg, h R hR ε hε] with n hn hconv
  simpa [← hn] using hconv

theorem LocallyUniformConverges.le_of_forall_le
    {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {b x : ℝ}
    (h : LocallyUniformConverges fs f)
    (hle : ∀ n, fs n x ≤ b) :
    f x ≤ b :=
  le_of_tendsto' (h.tendsto_at x) hle

theorem LocallyUniformConverges.nonneg_of_forall_nonneg
    {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {x : ℝ}
    (h : LocallyUniformConverges fs f)
    (hnonneg : ∀ n, 0 ≤ fs n x) :
    0 ≤ f x :=
  le_of_tendsto_of_tendsto' tendsto_const_nhds (h.tendsto_at x) hnonneg

theorem LocallyUniformConverges.antitone_of_forall_antitone
    {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (h : LocallyUniformConverges fs f)
    (hanti : ∀ n, Antitone (fs n)) :
    Antitone f := by
  intro x y hxy
  exact le_of_tendsto_of_tendsto'
    (h.tendsto_at y) (h.tendsto_at x) (fun n => hanti n hxy)

theorem LocallyUniformConverges.nonneg_of_inWaveTrapSet
    {κ M : ℝ} {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (h : LocallyUniformConverges fs f)
    (htrap : ∀ n, InWaveTrapSet κ M (fs n)) :
    ∀ x, 0 ≤ f x :=
  fun x => h.nonneg_of_forall_nonneg (fun n => (htrap n).nonneg x)

theorem LocallyUniformConverges.le_upperBarrier_of_inWaveTrapSet
    {κ M : ℝ} {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (h : LocallyUniformConverges fs f)
    (htrap : ∀ n, InWaveTrapSet κ M (fs n)) :
    ∀ x, f x ≤ upperBarrier κ M x :=
  fun x => h.le_of_forall_le (fun n => (htrap n).le_upperBarrier x)

theorem LocallyUniformConverges.le_M_of_inWaveTrapSet
    {κ M : ℝ} {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (h : LocallyUniformConverges fs f)
    (htrap : ∀ n, InWaveTrapSet κ M (fs n)) :
    ∀ x, f x ≤ M :=
  fun x => h.le_of_forall_le (fun n => (htrap n).le_M x)

theorem LocallyUniformConverges.le_exp_of_inWaveTrapSet
    {κ M : ℝ} {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (h : LocallyUniformConverges fs f)
    (htrap : ∀ n, InWaveTrapSet κ M (fs n)) :
    ∀ x, f x ≤ Real.exp (-κ * x) :=
  fun x => h.le_of_forall_le (fun n => (htrap n).le_exp x)

theorem LocallyUniformConverges.antitone_of_inMonotoneWaveTrapSet
    {κ M : ℝ} {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (h : LocallyUniformConverges fs f)
    (htrap : ∀ n, InMonotoneWaveTrapSet κ M (fs n)) :
    Antitone f :=
  h.antitone_of_forall_antitone (fun n => (htrap n).antitone)

/-- Sequential continuity of a wave map in the local-uniform topology, restricted
to a trapping set. -/
def LocalUniformContinuousOn
    (trap : (ℝ → ℝ) → Prop) (Tmap : (ℝ → ℝ) → ℝ → ℝ) : Prop :=
  ∀ (seq : ℕ → ℝ → ℝ) (u : ℝ → ℝ),
    (∀ n, trap (seq n)) →
      trap u →
        LocallyUniformConverges seq u →
          LocallyUniformConverges (fun n => Tmap (seq n)) (Tmap u)

theorem LocalUniformContinuousOn.fixed_of_approx_fixed
    {trap : (ℝ → ℝ) → Prop} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hcont : LocalUniformContinuousOn trap Tmap)
    {seq : ℕ → ℝ → ℝ} {u : ℝ → ℝ}
    (hseq : ∀ n, trap (seq n)) (hu : trap u)
    (hconv : LocallyUniformConverges seq u)
    (hfix : ∀ n, Tmap (seq n) = seq n) :
    Tmap u = u := by
  have himage : LocallyUniformConverges (fun n => Tmap (seq n)) (Tmap u) :=
    hcont seq u hseq hu hconv
  have hsame : LocallyUniformConverges (fun n => Tmap (seq n)) u := by
    intro R hR ε hε
    filter_upwards [hconv R hR ε hε] with n hn
    simpa [hfix n] using hn
  exact himage.unique hsame

theorem LocalUniformContinuousOn.fixed_of_common_limit
    {trap : (ℝ → ℝ) → Prop} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hcont : LocalUniformContinuousOn trap Tmap)
    {seq : ℕ → ℝ → ℝ} {u : ℝ → ℝ}
    (hseq : ∀ n, trap (seq n)) (hu : trap u)
    (hconv : LocallyUniformConverges seq u)
    (himage : LocallyUniformConverges (fun n => Tmap (seq n)) u) :
    Tmap u = u := by
  have hT :
      LocallyUniformConverges (fun n => Tmap (seq n)) (Tmap u) :=
    hcont seq u hseq hu hconv
  exact hT.unique himage

theorem LocalUniformContinuousOn.fixed_of_subseq_fixed_limit
    {trap : (ℝ → ℝ) → Prop} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hcont : LocalUniformContinuousOn trap Tmap)
    {seq : ℕ → ℝ → ℝ} {u : ℝ → ℝ} {subseq : ℕ → ℕ}
    (_hsubseq : StrictMono subseq)
    (hseq : ∀ n, trap (seq n)) (hu : trap u)
    (hconv : LocallyUniformConverges (fun n => seq (subseq n)) u)
    (hfix : ∀ n, Tmap (seq n) = seq n) :
    Tmap u = u := by
  exact hcont.fixed_of_approx_fixed
    (seq := fun n => seq (subseq n)) (u := u)
    (fun n => hseq (subseq n)) hu hconv
    (fun n => hfix (subseq n))

theorem LocalUniformContinuousOn.comp_strictMono
    {trap : (ℝ → ℝ) → Prop} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hcont : LocalUniformContinuousOn trap Tmap)
    {seq : ℕ → ℝ → ℝ} {u : ℝ → ℝ} {subseq : ℕ → ℕ}
    (_hsubseq : StrictMono subseq)
    (hseq : ∀ n, trap (seq n)) (hu : trap u)
    (hconv : LocallyUniformConverges (fun n => seq (subseq n)) u) :
    LocallyUniformConverges
      (fun n => Tmap (seq (subseq n))) (Tmap u) :=
  hcont (fun n => seq (subseq n)) u (fun n => hseq (subseq n)) hu hconv

/-- Sequential compactness of the range of a wave map in the local-uniform
topology, restricted to a trapping set. -/
def LocalUniformSequentiallyCompactRange
    (trap : (ℝ → ℝ) → Prop) (Tmap : (ℝ → ℝ) → ℝ → ℝ) : Prop :=
  ∀ seq : ℕ → ℝ → ℝ,
    (∀ n, trap (seq n)) →
      ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
        ∃ U : ℝ → ℝ,
          trap U ∧
            LocallyUniformConverges (fun n => Tmap (seq (subseq n))) U

theorem LocalUniformSequentiallyCompactRange.exists_fixed_subseq_limit
    {trap : (ℝ → ℝ) → Prop} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap)
    (hcont : LocalUniformContinuousOn trap Tmap)
    {seq : ℕ → ℝ → ℝ}
    (hseq : ∀ n, trap (seq n))
    (hfix : ∀ n, Tmap (seq n) = seq n) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ∃ U : ℝ → ℝ,
        trap U ∧
          LocallyUniformConverges (fun n => seq (subseq n)) U ∧
          Tmap U = U := by
  rcases hcompact seq hseq with ⟨subseq, hsubseq, U, hU, hconv_image⟩
  have hconv_seq :
      LocallyUniformConverges (fun n => seq (subseq n)) U := by
    intro R hR ε hε
    filter_upwards [hconv_image R hR ε hε] with n hn
    simpa [hfix (subseq n)] using hn
  exact
    ⟨subseq, hsubseq, U, hU, hconv_seq,
      hcont.fixed_of_subseq_fixed_limit hsubseq hseq hU hconv_seq hfix⟩

/-- The frozen auxiliary parabolic equation used in Section 4.2/4.3.
The frozen profile supplies the elliptic response; the orbit starts from the
upper barrier. -/
def FrozenAuxiliarySolutionFrom
    (p : CMParams) (c : ℝ) (frozen initial : ℝ → ℝ)
    (z : ℝ → ℝ → ℝ) : Prop :=
  (∀ x, z 0 x = initial x) ∧
    ∀ t x, 0 < t →
      deriv (fun τ : ℝ => z τ x) t =
        frozenWaveOperator p c frozen (z t) x

theorem FrozenAuxiliarySolutionFrom.initial_eq
    {p : CMParams} {c : ℝ} {frozen initial : ℝ → ℝ}
    {z : ℝ → ℝ → ℝ}
    (h : FrozenAuxiliarySolutionFrom p c frozen initial z) (x : ℝ) :
    z 0 x = initial x :=
  h.1 x

theorem FrozenAuxiliarySolutionFrom.evolution_eq
    {p : CMParams} {c : ℝ} {frozen initial : ℝ → ℝ}
    {z : ℝ → ℝ → ℝ}
    (h : FrozenAuxiliarySolutionFrom p c frozen initial z)
    {t x : ℝ} (ht : 0 < t) :
    deriv (fun τ : ℝ => z τ x) t =
      frozenWaveOperator p c frozen (z t) x :=
  h.2 t x ht

/-- Output of the auxiliary parabolic construction: the orbit stays in the
chosen trapping set, is monotone in time pointwise, and converges locally
pointwise to the profile `U`. -/
def FrozenAuxiliaryLimitOutput
    (p : CMParams) (c κ M : ℝ) (trap : (ℝ → ℝ) → Prop)
    (frozen U : ℝ → ℝ) : Prop :=
  ∃ z : ℝ → ℝ → ℝ,
    FrozenAuxiliarySolutionFrom p c frozen (upperBarrier κ M) z ∧
      (∀ t, 0 ≤ t → trap (z t)) ∧
      (∀ x, Antitone (fun t => z t x)) ∧
      ∀ x, Tendsto (fun t : ℝ => z t x) atTop (𝓝 (U x))

theorem FrozenAuxiliaryLimitOutput.exists_orbit
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    {frozen U : ℝ → ℝ}
    (h : FrozenAuxiliaryLimitOutput p c κ M trap frozen U) :
    ∃ z : ℝ → ℝ → ℝ,
      FrozenAuxiliarySolutionFrom p c frozen (upperBarrier κ M) z ∧
        (∀ t, 0 ≤ t → trap (z t)) ∧
        (∀ x, Antitone (fun t => z t x)) ∧
        ∀ x, Tendsto (fun t : ℝ => z t x) atTop (𝓝 (U x)) :=
  h

theorem FrozenAuxiliaryLimitOutput.solution_from
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    {frozen U : ℝ → ℝ}
    (h : FrozenAuxiliaryLimitOutput p c κ M trap frozen U) :
    ∃ z : ℝ → ℝ → ℝ,
      FrozenAuxiliarySolutionFrom p c frozen (upperBarrier κ M) z := by
  rcases h with ⟨z, hz, _htrap, _hanti, _htendsto⟩
  exact ⟨z, hz⟩

theorem FrozenAuxiliaryLimitOutput.exists_trapped_antitone_orbit
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    {frozen U : ℝ → ℝ}
    (h : FrozenAuxiliaryLimitOutput p c κ M trap frozen U) :
    ∃ z : ℝ → ℝ → ℝ,
      (∀ t, 0 ≤ t → trap (z t)) ∧
        (∀ x, Antitone (fun t => z t x)) ∧
        ∀ x, Tendsto (fun t : ℝ => z t x) atTop (𝓝 (U x)) := by
  rcases h with ⟨z, _hz, htrap, hanti, htendsto⟩
  exact ⟨z, htrap, hanti, htendsto⟩

theorem FrozenAuxiliaryLimitOutput.le_initial_upperBarrier
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    {frozen U : ℝ → ℝ}
    (h : FrozenAuxiliaryLimitOutput p c κ M trap frozen U) (x : ℝ) :
    U x ≤ upperBarrier κ M x := by
  rcases h with ⟨z, hz, _htrap, hanti, htendsto⟩
  have heventually :
      ∀ᶠ t in atTop, z t x ≤ upperBarrier κ M x := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hle : z t x ≤ z 0 x := hanti x ht
    simpa [FrozenAuxiliarySolutionFrom.initial_eq hz x] using hle
  exact le_of_tendsto (htendsto x) heventually

theorem FrozenAuxiliaryLimitOutput.nonneg_of_inWaveTrapSet
    {p : CMParams} {c κ M : ℝ} {frozen U : ℝ → ℝ}
    (h :
      FrozenAuxiliaryLimitOutput p c κ M
        (fun u => InWaveTrapSet κ M u) frozen U)
    (x : ℝ) :
    0 ≤ U x := by
  rcases h with ⟨z, _hz, htrap, _hanti, htendsto⟩
  have heventually :
      (fun _ : ℝ => (0 : ℝ)) ≤ᶠ[atTop] fun t : ℝ => z t x := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (htrap t ht).nonneg x
  exact le_of_tendsto_of_tendsto tendsto_const_nhds (htendsto x) heventually

theorem FrozenAuxiliaryLimitOutput.le_M_of_inWaveTrapSet
    {p : CMParams} {c κ M : ℝ} {frozen U : ℝ → ℝ}
    (h :
      FrozenAuxiliaryLimitOutput p c κ M
        (fun u => InWaveTrapSet κ M u) frozen U)
    (x : ℝ) :
    U x ≤ M := by
  rcases h with ⟨z, _hz, htrap, _hanti, htendsto⟩
  have heventually : ∀ᶠ t in atTop, z t x ≤ M := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (htrap t ht).le_M x
  exact le_of_tendsto (htendsto x) heventually

theorem FrozenAuxiliaryLimitOutput.le_exp_of_inWaveTrapSet
    {p : CMParams} {c κ M : ℝ} {frozen U : ℝ → ℝ}
    (h :
      FrozenAuxiliaryLimitOutput p c κ M
        (fun u => InWaveTrapSet κ M u) frozen U)
    (x : ℝ) :
    U x ≤ Real.exp (-κ * x) := by
  rcases h with ⟨z, _hz, htrap, _hanti, htendsto⟩
  have heventually :
      ∀ᶠ t in atTop, z t x ≤ Real.exp (-κ * x) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (htrap t ht).le_exp x
  exact le_of_tendsto (htendsto x) heventually

theorem FrozenAuxiliaryLimitOutput.antitone_of_inMonotoneWaveTrapSet
    {p : CMParams} {c κ M : ℝ} {frozen U : ℝ → ℝ}
    (h :
      FrozenAuxiliaryLimitOutput p c κ M
        (fun u => InMonotoneWaveTrapSet κ M u) frozen U) :
    Antitone U := by
  rcases h with ⟨z, _hz, htrap, _hanti, htendsto⟩
  intro x y hxy
  have heventually : (fun t : ℝ => z t y) ≤ᶠ[atTop] fun t : ℝ => z t x := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (htrap t ht).antitone hxy
  exact le_of_tendsto_of_tendsto (htendsto y) (htendsto x) heventually

/-- Data constructed before applying Schauder in the Section 4 wave proof:
a self-map on the trapping set, the auxiliary parabolic limit output for each
frozen profile, sequential local-uniform continuity, and sequential compactness
of the image range.  This deliberately does not include a fixed point. -/
def FrozenWaveMapSchauderData
    (p : CMParams) (c κ M : ℝ) (trap : (ℝ → ℝ) → Prop)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ) : Prop :=
  (∀ u, trap u → trap (Tmap u)) ∧
    (∀ u, trap u → FrozenAuxiliaryLimitOutput p c κ M trap u (Tmap u)) ∧
    LocalUniformContinuousOn trap Tmap ∧
    LocalUniformSequentiallyCompactRange trap Tmap

theorem FrozenWaveMapSchauderData.self_mem
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (h : FrozenWaveMapSchauderData p c κ M trap Tmap)
    {u : ℝ → ℝ} (hu : trap u) :
    trap (Tmap u) :=
  h.1 u hu

theorem FrozenWaveMapSchauderData.limit_output
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (h : FrozenWaveMapSchauderData p c κ M trap Tmap)
    {u : ℝ → ℝ} (hu : trap u) :
    FrozenAuxiliaryLimitOutput p c κ M trap u (Tmap u) :=
  h.2.1 u hu

theorem FrozenWaveMapSchauderData.continuousOn
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (h : FrozenWaveMapSchauderData p c κ M trap Tmap) :
    LocalUniformContinuousOn trap Tmap :=
  h.2.2.1

theorem FrozenWaveMapSchauderData.compactRange
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (h : FrozenWaveMapSchauderData p c κ M trap Tmap) :
    LocalUniformSequentiallyCompactRange trap Tmap :=
  h.2.2.2

/-- Abstract fixed-point principle needed after constructing a continuous compact
self-map in the local-uniform topology.  The analytic/topological proof of this
principle is deliberately separated from the paper-specific wave map data. -/
def LocalUniformSchauderFixedPointPrinciple
    (trap : (ℝ → ℝ) → Prop) : Prop :=
  ∀ Tmap : (ℝ → ℝ) → ℝ → ℝ,
    (∀ u, trap u → trap (Tmap u)) →
      LocalUniformContinuousOn trap Tmap →
        LocalUniformSequentiallyCompactRange trap Tmap →
          ∃ U : ℝ → ℝ, trap U ∧ Tmap U = U

theorem FrozenWaveMapSchauderData.exists_fixed_of_principle
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hprinciple : LocalUniformSchauderFixedPointPrinciple trap)
    (h : FrozenWaveMapSchauderData p c κ M trap Tmap) :
    ∃ U : ℝ → ℝ, trap U ∧ Tmap U = U :=
  hprinciple Tmap h.1 h.continuousOn h.compactRange

theorem FrozenWaveMapSchauderData.exists_fixed_limit_of_principle
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hprinciple : LocalUniformSchauderFixedPointPrinciple trap)
    (h : FrozenWaveMapSchauderData p c κ M trap Tmap) :
    ∃ U : ℝ → ℝ,
      trap U ∧ FrozenAuxiliaryLimitOutput p c κ M trap U U := by
  rcases h.exists_fixed_of_principle hprinciple with ⟨U, hU, hfix⟩
  refine ⟨U, hU, ?_⟩
  have hlimit := h.limit_output hU
  rwa [hfix] at hlimit

/-- The Schauder-map statement target from the proof of Theorem 1.1: construct
a local-uniformly compact and continuous limit map on a trapping set, then get a
fixed point. -/
def FrozenWaveMapConstruction
    (p : CMParams) (c κ M : ℝ) (trap : (ℝ → ℝ) → Prop) : Prop :=
  ∃ Tmap : (ℝ → ℝ) → ℝ → ℝ,
    (∀ u, trap u → trap (Tmap u)) ∧
      (∀ u, trap u → FrozenAuxiliaryLimitOutput p c κ M trap u (Tmap u)) ∧
      LocalUniformContinuousOn trap Tmap ∧
      LocalUniformSequentiallyCompactRange trap Tmap ∧
      ∃ U : ℝ → ℝ, trap U ∧ Tmap U = U

theorem FrozenWaveMapSchauderData.to_construction
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hprinciple : LocalUniformSchauderFixedPointPrinciple trap)
    (h : FrozenWaveMapSchauderData p c κ M trap Tmap) :
    FrozenWaveMapConstruction p c κ M trap :=
  ⟨Tmap, h.1, h.2.1, h.continuousOn, h.compactRange,
    h.exists_fixed_of_principle hprinciple⟩

theorem FrozenWaveMapConstruction.of_schauderData
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    (hprinciple : LocalUniformSchauderFixedPointPrinciple trap)
    (hdata :
      ∃ Tmap : (ℝ → ℝ) → ℝ → ℝ,
        FrozenWaveMapSchauderData p c κ M trap Tmap) :
    FrozenWaveMapConstruction p c κ M trap := by
  rcases hdata with ⟨Tmap, h⟩
  exact h.to_construction hprinciple

theorem FrozenWaveMapConstruction.exists_map
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    (h : FrozenWaveMapConstruction p c κ M trap) :
    ∃ Tmap : (ℝ → ℝ) → ℝ → ℝ,
      (∀ u, trap u → trap (Tmap u)) ∧
        (∀ u, trap u → FrozenAuxiliaryLimitOutput p c κ M trap u (Tmap u)) ∧
        LocalUniformContinuousOn trap Tmap ∧
        LocalUniformSequentiallyCompactRange trap Tmap ∧
        ∃ U : ℝ → ℝ, trap U ∧ Tmap U = U :=
  h

theorem FrozenWaveMapConstruction.exists_schauderData
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    (h : FrozenWaveMapConstruction p c κ M trap) :
    ∃ Tmap : (ℝ → ℝ) → ℝ → ℝ,
      FrozenWaveMapSchauderData p c κ M trap Tmap ∧
        ∃ U : ℝ → ℝ, trap U ∧ Tmap U = U := by
  rcases h with ⟨Tmap, hmap, hlimit, hcont, hcompact, hfixed⟩
  exact ⟨Tmap, ⟨hmap, hlimit, hcont, hcompact⟩, hfixed⟩

theorem FrozenWaveMapConstruction.exists_map_self
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    (h : FrozenWaveMapConstruction p c κ M trap) :
    ∃ Tmap : (ℝ → ℝ) → ℝ → ℝ,
      (∀ u, trap u → trap (Tmap u)) ∧
        ∀ u, trap u →
          FrozenAuxiliaryLimitOutput p c κ M trap u (Tmap u) := by
  rcases h with ⟨Tmap, hmap, hlimit, _hcont, _hcompact, _hfixed⟩
  exact ⟨Tmap, hmap, hlimit⟩

theorem FrozenWaveMapConstruction.exists_continuous_compact_map
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    (h : FrozenWaveMapConstruction p c κ M trap) :
    ∃ Tmap : (ℝ → ℝ) → ℝ → ℝ,
      LocalUniformContinuousOn trap Tmap ∧
        LocalUniformSequentiallyCompactRange trap Tmap ∧
        ∃ U : ℝ → ℝ, trap U ∧ Tmap U = U := by
  rcases h with ⟨Tmap, _hmap, _hlimit, hcont, hcompact, hfixed⟩
  exact ⟨Tmap, hcont, hcompact, hfixed⟩

theorem FrozenWaveMapConstruction.exists_fixed_limit
    {p : CMParams} {c κ M : ℝ} {trap : (ℝ → ℝ) → Prop}
    (h : FrozenWaveMapConstruction p c κ M trap) :
    ∃ U : ℝ → ℝ,
      trap U ∧ FrozenAuxiliaryLimitOutput p c κ M trap U U := by
  rcases h with ⟨Tmap, _hmap, hlimit, _hcont, _hcompact, U, hU, hfix⟩
  refine ⟨U, hU, ?_⟩
  have hUlimit := hlimit U hU
  rwa [hfix] at hUlimit

theorem FrozenWaveMapConstruction.exists_fixed_inWaveTrapSet_with_bounds
    {p : CMParams} {c κ M : ℝ}
    (h : FrozenWaveMapConstruction p c κ M (fun u => InWaveTrapSet κ M u)) :
    ∃ U : ℝ → ℝ,
      InWaveTrapSet κ M U ∧
        FrozenAuxiliaryLimitOutput p c κ M
          (fun u => InWaveTrapSet κ M u) U U ∧
        (∀ x, 0 ≤ U x) ∧
        (∀ x, U x ≤ M) ∧
        ∀ x, U x ≤ Real.exp (-κ * x) := by
  rcases h.exists_fixed_limit with ⟨U, hU, hlimit⟩
  exact ⟨U, hU, hlimit, hU.nonneg, hU.le_M, hU.le_exp⟩

theorem FrozenWaveMapConstruction.exists_fixed_inMonotoneWaveTrapSet_with_bounds
    {p : CMParams} {c κ M : ℝ}
    (h :
      FrozenWaveMapConstruction p c κ M
        (fun u => InMonotoneWaveTrapSet κ M u)) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U ∧
        FrozenAuxiliaryLimitOutput p c κ M
          (fun u => InMonotoneWaveTrapSet κ M u) U U ∧
        Antitone U ∧
        (∀ x, 0 ≤ U x) ∧
        (∀ x, U x ≤ M) ∧
        ∀ x, U x ≤ Real.exp (-κ * x) := by
  rcases h.exists_fixed_limit with ⟨U, hU, hlimit⟩
  exact
    ⟨U, hU, hlimit, hU.antitone, hU.nonneg, hU.le_M, hU.le_exp⟩

def subsolutionK (M κ κtilde m gamma : ℝ) : ℝ :=
  let prefactor := m * (κtilde + κ) + 1
  if gamma * κ = 1 then
    prefactor * (M ^ gamma + 3 / 4)
  else if gamma * κ < 1 then
    prefactor * (1 / (1 - gamma ^ 2 * κ ^ 2))
  else
    prefactor *
      (M ^ gamma * (κ ^ 2 * gamma ^ 2 - 1 + gamma * κ) /
        (κ ^ 2 * gamma ^ 2 - 1))

def subsolutionDThreshold
    (χ M κ κtilde m gamma c : ℝ) : ℝ :=
  (1 + |χ| * subsolutionK M κ κtilde m gamma) /
    (c * κtilde - κtilde ^ 2 - 1)

def constantSubsolutionThreshold (χ κ κtilde D : ℝ) : ℝ :=
  min (1 / (1 + |χ|))
    ((κ / (κtilde * D)) ^ (κ / (κtilde - κ)) *
      (1 - κ / κtilde))

/-- The simplified `K_{κ,m,γ}` from Paper1 Remark 4.1, obtained from
`K_{M,κ,κ̃,m,γ}` when `κ̃ = 2κ` and `γκ < 1`. -/
def remark41K (κ m gamma : ℝ) : ℝ :=
  (3 * m * κ + 1) / (1 - gamma ^ 2 * κ ^ 2)

/-- The simplified upper bound `D_{κ,χ,m,γ}` from Paper1 Remark 4.1. -/
def remark41DUpperBound (χ κ m gamma : ℝ) : ℝ :=
  2 * (1 - gamma ^ 2 * κ ^ 2 + |χ| * (3 * m * κ + 1)) /
    (1 - gamma ^ 2 * κ ^ 2)

/-- The lower bound for the small constant subsolution threshold recorded in
Paper1 Remark 4.1.  The paper writes `|χ|σ`; this definition represents that
product as `|χ| * σ`. -/
def remark41ConstantSubsolutionLowerBound
    (χ m gamma sigma : ℝ) : ℝ :=
  (1 + gamma) * |χ| * sigma /
    (8 * (1 + |χ| + 2 * m * |χ|) * (gamma + |χ| * sigma))

theorem subsolutionK_eq_remark41K_of_double_kappa
    {M κ m gamma : ℝ} (hγκ : gamma * κ < 1) :
    subsolutionK M κ (2 * κ) m gamma = remark41K κ m gamma := by
  unfold subsolutionK remark41K
  have hne : ¬ gamma * κ = 1 := ne_of_lt hγκ
  rw [if_neg hne, if_pos hγκ]
  ring

theorem lowerBarrierRaw_speed_denominator_double_kappa_eq
    {κ : ℝ} (hκ : κ ≠ 0) :
    (κ + κ⁻¹) * (2 * κ) - (2 * κ) ^ 2 - 1 = 1 - 2 * κ ^ 2 := by
  field_simp [hκ]
  ring

theorem lowerBarrierRaw_speed_denominator_double_kappa_pos
    {κ : ℝ} (hκ_pos : 0 < κ) (hκ_half : κ < 1 / 2) :
    0 < (κ + κ⁻¹) * (2 * κ) - (2 * κ) ^ 2 - 1 := by
  rw [lowerBarrierRaw_speed_denominator_double_kappa_eq (ne_of_gt hκ_pos)]
  nlinarith

theorem subsolutionDThreshold_double_kappa_le_remark41DUpperBound
    {χ M κ m gamma : ℝ}
    (hκ_pos : 0 < κ) (hκ_half : κ < 1 / 2)
    (hm_pos : 0 < m) (hgamma_pos : 0 < gamma)
    (hγκ : gamma * κ < 1) :
    subsolutionDThreshold χ M κ (2 * κ) m gamma (κ + κ⁻¹) ≤
      remark41DUpperBound χ κ m gamma := by
  have hK : subsolutionK M κ (2 * κ) m gamma = remark41K κ m gamma :=
    subsolutionK_eq_remark41K_of_double_kappa hγκ
  have hden :
      (κ + κ⁻¹) * (2 * κ) - (2 * κ) ^ 2 - 1 = 1 - 2 * κ ^ 2 :=
    lowerBarrierRaw_speed_denominator_double_kappa_eq (ne_of_gt hκ_pos)
  have hgamma_kappa_pos : 0 < gamma * κ := mul_pos hgamma_pos hκ_pos
  have hG_pos : 0 < 1 - gamma ^ 2 * κ ^ 2 := by
    nlinarith
  have hH_pos : 0 < 1 - 2 * κ ^ 2 := by
    nlinarith
  have hA_nonneg : 0 ≤ 3 * m * κ + 1 := by
    nlinarith [mul_pos hm_pos hκ_pos]
  have hN_nonneg :
      0 ≤ 1 - gamma ^ 2 * κ ^ 2 + |χ| * (3 * m * κ + 1) :=
    add_nonneg hG_pos.le (mul_nonneg (abs_nonneg χ) hA_nonneg)
  unfold subsolutionDThreshold remark41DUpperBound
  rw [hK, hden]
  unfold remark41K
  by_contra hnot
  push Not at hnot
  have hG_pos' : 0 < 1 - κ ^ 2 * gamma ^ 2 := by
    nlinarith
  have hH_pos' : 0 < 1 - κ ^ 2 * 2 := by
    nlinarith
  field_simp [hG_pos'.ne', hH_pos'.ne'] at hnot
  nlinarith

theorem subsolutionK_pos
    {M κ κtilde m gamma : ℝ} (hM : 0 < M) (hκ : 0 < κ)
    (hgap : 0 < κtilde - κ) (hm : 0 < m) (hgamma : 0 < gamma) :
    0 < subsolutionK M κ κtilde m gamma := by
  have hκtilde : 0 < κtilde := by linarith
  have hprefactor : 0 < m * (κtilde + κ) + 1 := by
    nlinarith [mul_pos hm (by linarith : 0 < κtilde + κ)]
  unfold subsolutionK
  by_cases heq : gamma * κ = 1
  · rw [if_pos heq]
    exact mul_pos hprefactor
      (add_pos (Real.rpow_pos_of_pos hM _) (by norm_num))
  · rw [if_neg heq]
    by_cases hlt : gamma * κ < 1
    · rw [if_pos hlt]
      apply mul_pos hprefactor
      apply div_pos one_pos
      nlinarith [mul_pos hgamma hκ]
    · rw [if_neg hlt]
      have hgt : 1 < gamma * κ := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      apply mul_pos hprefactor
      apply div_pos
      · apply mul_pos (Real.rpow_pos_of_pos hM _)
        nlinarith
      · nlinarith

theorem subsolutionDThreshold_pos
    {χ M κ κtilde m gamma c : ℝ}
    (hM : 0 < M) (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hm : 0 < m) (hgamma : 0 < gamma)
    (hden : 0 < c * κtilde - κtilde ^ 2 - 1) :
    0 < subsolutionDThreshold χ M κ κtilde m gamma c := by
  unfold subsolutionDThreshold
  apply div_pos
  · exact add_pos_of_pos_of_nonneg one_pos
      (mul_nonneg (abs_nonneg χ)
        (subsolutionK_pos hM hκ hgap hm hgamma).le)
  · exact hden

theorem subsolutionDThreshold_pos_of_kappa_speed
    {χ M κ κtilde m gamma c : ℝ}
    (hM : 0 < M) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hgap : κ < κtilde) (hκtilde1 : κtilde ≤ 1)
    (hm : 0 < m) (hgamma : 0 < gamma) (hc : c = κ + κ⁻¹) :
    0 < subsolutionDThreshold χ M κ κtilde m gamma c :=
  subsolutionDThreshold_pos hM hκ0 (sub_pos.mpr hgap) hm hgamma
    (lowerBarrierRaw_speed_denominator_pos hκ0 hκ1 hgap hκtilde1 hc)

theorem subsolutionDThreshold_pos_of_speed_gt_two
    {χ M κtilde m gamma c : ℝ}
    (hM : 0 < M) (hc : 2 < c) (hgap : kappa c < κtilde)
    (hκtilde1 : κtilde ≤ 1) (hm : 0 < m) (hgamma : 0 < gamma) :
    0 < subsolutionDThreshold χ M (kappa c) κtilde m gamma c :=
  subsolutionDThreshold_pos_of_kappa_speed hM
    (kappa_pos_of_two_lt hc)
    (kappa_lt_one_of_two_lt hc)
    hgap hκtilde1 hm hgamma
    (kappa_add_inv_eq_of_two_lt hc).symm

theorem subsolutionDThreshold_pos_of_cStarLower_lt
    {p : CMParams} {M κtilde c : ℝ}
    (hM : 0 < M) (hc : cStarLower p < c)
    (hgap : kappa c < κtilde) (hκtilde1 : κtilde ≤ 1) :
    0 < subsolutionDThreshold p.χ M (kappa c) κtilde p.m p.γ c :=
  subsolutionDThreshold_pos_of_speed_gt_two hM
    (two_lt_of_cStarLower_lt hc) hgap hκtilde1
    (lt_of_lt_of_le one_pos p.hm)
    (lt_of_lt_of_le one_pos p.hγ)

theorem constantSubsolutionThreshold_pos
    {χ κ κtilde D : ℝ} (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D) :
    0 < constantSubsolutionThreshold χ κ κtilde D := by
  have hκtilde : 0 < κtilde := by linarith
  unfold constantSubsolutionThreshold
  apply lt_min
  · exact div_pos one_pos (by positivity)
  · apply mul_pos
    · apply Real.rpow_pos_of_pos
      exact div_pos hκ (mul_pos hκtilde hD)
    · rw [sub_pos]
      exact (div_lt_one hκtilde).mpr (by linarith)

theorem exists_D_gt_subsolutionDThreshold_lowerBarrierPlateau_mem_InWaveTrapSet
    {χ M κ κtilde m gamma c : ℝ}
    (hM : 0 < M) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hgap : κ < κtilde) (hκtilde1 : κtilde ≤ 1)
    (hm : 0 < m) (hgamma : 0 < gamma) (hc : c = κ + κ⁻¹) :
    ∃ D > subsolutionDThreshold χ M κ κtilde m gamma c,
      InWaveTrapSet κ M (lowerBarrierPlateau κ κtilde D) := by
  exact
    exists_D_gt_lowerBarrierPlateau_mem_InWaveTrapSet
      hκ0 (sub_pos.mpr hgap) hM
      (subsolutionDThreshold_pos_of_kappa_speed hM hκ0 hκ1 hgap
        hκtilde1 hm hgamma hc).le

theorem exists_D_gt_subsolutionDThreshold_lowerBarrierPlateau_mem_InMonotoneWaveTrapSet
    {χ M κ κtilde m gamma c : ℝ}
    (hM : 0 < M) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hgap : κ < κtilde) (hκtilde1 : κtilde ≤ 1)
    (hm : 0 < m) (hgamma : 0 < gamma) (hc : c = κ + κ⁻¹) :
    ∃ D > subsolutionDThreshold χ M κ κtilde m gamma c,
      InMonotoneWaveTrapSet κ M (lowerBarrierPlateau κ κtilde D) := by
  exact
    exists_D_gt_lowerBarrierPlateau_mem_InMonotoneWaveTrapSet
      hκ0 (sub_pos.mpr hgap) hM
      (subsolutionDThreshold_pos_of_kappa_speed hM hκ0 hκ1 hgap
        hκtilde1 hm hgamma hc).le

theorem
    exists_D_gt_subsolutionDThreshold_lowerBarrierPlateau_mem_InMonotoneWaveTrapSet_of_cStarLower_lt
    {p : CMParams} {M κtilde c : ℝ}
    (hM : 0 < M) (hc : cStarLower p < c)
    (hgap : kappa c < κtilde) (hκtilde1 : κtilde ≤ 1) :
    ∃ D > subsolutionDThreshold p.χ M (kappa c) κtilde p.m p.γ c,
      InMonotoneWaveTrapSet (kappa c) M
        (lowerBarrierPlateau (kappa c) κtilde D) := by
  exact
    exists_D_gt_subsolutionDThreshold_lowerBarrierPlateau_mem_InMonotoneWaveTrapSet
      hM (kappa_pos_of_cStarLower_lt hc) (kappa_lt_one_of_cStarLower_lt hc)
      hgap hκtilde1
      (lt_of_lt_of_le one_pos p.hm)
      (lt_of_lt_of_le one_pos p.hγ)
      (kappa_add_inv_eq_of_cStarLower_lt hc).symm

theorem D_pos_of_subsolutionDThreshold_lt_of_kappa_speed
    {χ M κ κtilde m gamma c D : ℝ}
    (hM : 0 < M) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hgap : κ < κtilde) (hκtilde1 : κtilde ≤ 1)
    (hm : 0 < m) (hgamma : 0 < gamma) (hc : c = κ + κ⁻¹)
    (hD : subsolutionDThreshold χ M κ κtilde m gamma c < D) :
    0 < D :=
  lt_trans
    (subsolutionDThreshold_pos_of_kappa_speed hM hκ0 hκ1 hgap
      hκtilde1 hm hgamma hc)
    hD

theorem D_pos_of_subsolutionDThreshold_lt_of_cStarLower_lt
    {p : CMParams} {M κtilde c D : ℝ}
    (hM : 0 < M) (hc : cStarLower p < c)
    (hgap : kappa c < κtilde) (hκtilde1 : κtilde ≤ 1)
    (hD : subsolutionDThreshold p.χ M (kappa c) κtilde p.m p.γ c < D) :
    0 < D :=
  D_pos_of_subsolutionDThreshold_lt_of_kappa_speed
    hM (kappa_pos_of_cStarLower_lt hc) (kappa_lt_one_of_cStarLower_lt hc)
    hgap hκtilde1
    (lt_of_lt_of_le one_pos p.hm)
    (lt_of_lt_of_le one_pos p.hγ)
    (kappa_add_inv_eq_of_cStarLower_lt hc).symm
    hD

theorem exists_d_pos_le_constantSubsolutionThreshold
    {χ κ κtilde D : ℝ}
    (hκ : 0 < κ) (hgap : κ < κtilde) (hD : 0 < D) :
    ∃ d : ℝ, 0 < d ∧ d ≤ constantSubsolutionThreshold χ κ κtilde D := by
  let d := constantSubsolutionThreshold χ κ κtilde D / 2
  have hthr : 0 < constantSubsolutionThreshold χ κ κtilde D :=
    constantSubsolutionThreshold_pos hκ (sub_pos.mpr hgap) hD
  refine ⟨d, ?_, ?_⟩
  · dsimp [d]
    linarith
  · dsimp [d]
    linarith

theorem
    exists_d_pos_le_constantSubsolutionThreshold_of_subsolutionDThreshold_lt
    {χ M κ κtilde m gamma c D : ℝ}
    (hM : 0 < M) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hgap : κ < κtilde) (hκtilde1 : κtilde ≤ 1)
    (hm : 0 < m) (hgamma : 0 < gamma) (hc : c = κ + κ⁻¹)
    (hD : subsolutionDThreshold χ M κ κtilde m gamma c < D) :
    ∃ d : ℝ, 0 < d ∧ d ≤ constantSubsolutionThreshold χ κ κtilde D :=
  exists_d_pos_le_constantSubsolutionThreshold hκ0 hgap
    (D_pos_of_subsolutionDThreshold_lt_of_kappa_speed hM hκ0 hκ1 hgap
      hκtilde1 hm hgamma hc hD)

theorem
    exists_d_pos_le_constantSubsolutionThreshold_of_cStarLower_lt
    {p : CMParams} {M κtilde c D : ℝ}
    (hM : 0 < M) (hc : cStarLower p < c)
    (hgap : kappa c < κtilde) (hκtilde1 : κtilde ≤ 1)
    (hD : subsolutionDThreshold p.χ M (kappa c) κtilde p.m p.γ c < D) :
    ∃ d : ℝ, 0 < d ∧
      d ≤ constantSubsolutionThreshold p.χ (kappa c) κtilde D :=
  exists_d_pos_le_constantSubsolutionThreshold_of_subsolutionDThreshold_lt
    hM (kappa_pos_of_cStarLower_lt hc) (kappa_lt_one_of_cStarLower_lt hc)
    hgap hκtilde1
    (lt_of_lt_of_le one_pos p.hm)
    (lt_of_lt_of_le one_pos p.hγ)
    (kappa_add_inv_eq_of_cStarLower_lt hc).symm
    hD

theorem kappaTilde_pos_of_kappa_lt
    {κ κtilde : ℝ} (hκ : 0 < κ) (hgap : κ < κtilde) :
    0 < κtilde := by
  linarith

theorem kappaTilde_le_one_plus_alpha_mul_kappa_of_subsolution_range
    {alpha m κ κtilde : ℝ}
    (hrange :
      κtilde ≤ min ((1 + alpha) * κ) (min (m * κ + 1 / 2) 1)) :
    κtilde ≤ (1 + alpha) * κ :=
  le_trans hrange (min_le_left _ _)

theorem kappaTilde_le_m_mul_kappa_add_half_of_subsolution_range
    {alpha m κ κtilde : ℝ}
    (hrange :
      κtilde ≤ min ((1 + alpha) * κ) (min (m * κ + 1 / 2) 1)) :
    κtilde ≤ m * κ + 1 / 2 :=
  le_trans hrange (le_trans (min_le_right _ _) (min_le_left _ _))

theorem kappaTilde_le_one_of_subsolution_range
    {alpha m κ κtilde : ℝ}
    (hrange :
      κtilde ≤ min ((1 + alpha) * κ) (min (m * κ + 1 / 2) 1)) :
    κtilde ≤ 1 :=
  le_trans hrange (le_trans (min_le_right _ _) (min_le_right _ _))

theorem kappaTilde_lt_one_of_lt_subsolution_range
    {alpha m κ κtilde : ℝ}
    (hrange :
      κtilde < min ((1 + alpha) * κ) (min (m * κ + 1 / 2) 1)) :
    κtilde < 1 :=
  lt_of_lt_of_le hrange (le_trans (min_le_right _ _) (min_le_right _ _))

def Lemma_4_1 : Prop :=
  (∀ p : CMParams, p.χ ≤ 0 → p.α ≤ p.m + p.γ - 1 →
    ∀ κ M c : ℝ, 0 < κ → κ < 1 → 1 ≤ M → c = κ + κ⁻¹ →
      ∀ u : ℝ → ℝ, InWaveTrapSet κ M u →
        IsFrozenSuperSolution p c u (upperBarrier κ M)) ∧
  (∀ p : CMParams, 0 ≤ p.χ → p.χ < chiStar p →
    p.α = p.m + p.γ - 1 →
    ∀ κ M c : ℝ, 0 < κ → κ < 1 → 1 ≤ M →
      (1 / (1 - p.χ)) ^ (1 / p.α) ≤ M → c = κ + κ⁻¹ →
      ∀ u : ℝ → ℝ, InWaveTrapSet κ M u →
        IsFrozenSuperSolution p c u (upperBarrier κ M))

theorem frozenWaveOperator_const_eq
    (p : CMParams) {c M : ℝ} {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x) (x : ℝ) :
    frozenWaveOperator p c u (fun _ => M) x =
      -p.χ * (M ^ p.m *
        (frozenElliptic p u x - (u x) ^ p.γ)) +
        M * (1 - M ^ p.α) := by
  unfold frozenWaveOperator
  simp only [iteratedDeriv_const, deriv_const, mul_zero, add_zero, zero_add,
    show (2 : ℕ) ≠ 0 from by norm_num, ite_false]
  have hconst_deriv :
      deriv (fun y => (fun _ => M) y ^ p.m *
        deriv (frozenElliptic p u) y) x =
      M ^ p.m * (frozenElliptic p u x - (u x) ^ p.γ) := by
    have hW : (fun y => (fun _ : ℝ => M) y ^ p.m *
        deriv (frozenElliptic p u) y) =
      (fun y => M ^ p.m * deriv (frozenElliptic p u) y) := by
      ext y; simp
    rw [hW, deriv_const_mul_field,
      frozenElliptic_deriv_deriv_eq p hu hu_nonneg x]
  rw [hconst_deriv]
  ring

theorem frozenWaveOperator_exp_eq
    (p : CMParams) {c κ : ℝ} {u : ℝ → ℝ}
    (hc : 2 ≤ c) (hκ : κ = kappa c)
    (_hu : IsCUnifBdd u) (_hu_nonneg : ∀ x, 0 ≤ u x) (x : ℝ) :
    frozenWaveOperator p c u (expDecay κ) x =
      -(expDecay κ x) * (expDecay κ x) ^ p.α
      - p.χ * deriv (fun y => (expDecay κ y) ^ p.m *
          deriv (frozenElliptic p u) y) x := by
  unfold frozenWaveOperator
  have hW2 := expDecay_iteratedDeriv_two κ x
  have hW1 := expDecay_deriv κ x
  have hquad : κ ^ 2 - c * κ + 1 = 0 := by
    rw [hκ]; exact kappa_quadratic_eq_zero hc
  rw [hW2, hW1]
  have h : κ ^ 2 * expDecay κ x + c * (-κ * expDecay κ x) +
      expDecay κ x = 0 := by
    have := expDecay_linear_part_eq κ c x
    rw [hW2, hW1, hquad, zero_mul] at this
    linarith
  nlinarith [expDecay_pos κ x, Real.rpow_nonneg (expDecay_pos κ x).le p.α]

theorem constant_subsolution_frozenWaveOperator_nonneg_of_chem_nonneg
    (p : CMParams) {κ κtilde D d c M : ℝ} {u : ℝ → ℝ}
    (hd_pos : 0 < d)
    (hd_le : d ≤ constantSubsolutionThreshold p.χ κ κtilde D)
    (hu : InWaveTrapSet κ M u)
    (hchem :
      ∀ x, 0 ≤
        -p.χ * (d ^ p.m *
          (frozenElliptic p u x - (u x) ^ p.γ))) :
    IsFrozenSubSolutionOn p c u (fun _ => d) Set.univ := by
  intro x _hx
  rw [frozenWaveOperator_const_eq p hu.cunif_bdd hu.nonneg x]
  apply add_nonneg
  · exact hchem x
  · have hd_nonneg : 0 ≤ d := hd_pos.le
    have hd_le_inv : d ≤ 1 / (1 + |p.χ|) := by
      exact le_trans hd_le (min_le_left _ _)
    have hinv_le_one : 1 / (1 + |p.χ|) ≤ (1 : ℝ) := by
      have hden_ge : 1 ≤ 1 + |p.χ| := by
        exact le_add_of_nonneg_right (abs_nonneg p.χ)
      simpa [one_div] using inv_le_one_of_one_le₀ hden_ge
    have hd_le_one : d ≤ 1 := le_trans hd_le_inv hinv_le_one
    exact mul_nonneg hd_nonneg
      (sub_nonneg.mpr
        (Real.rpow_le_one hd_nonneg hd_le_one
          (by linarith [p.hα] : 0 ≤ p.α)))

theorem paperWaveOperator_const_subsolution_nonneg_of_chi_nonpos
    (p : CMParams) {c κ κtilde D d : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ ≤ 0) (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x)
    (hd_pos : 0 < d)
    (hd_le : d ≤ constantSubsolutionThreshold p.χ κ κtilde D)
    (x : ℝ) :
    0 ≤ paperWaveOperator p c u (fun _ => d) x := by
  rw [paperWaveOperator_const_eq p hu hu_nonneg x]
  apply mul_nonneg hd_pos.le
  have hd_nonneg : 0 ≤ d := hd_pos.le
  have hd_le_inv : d ≤ 1 / (1 + |p.χ|) := by
    exact le_trans hd_le (min_le_left _ _)
  have hden_pos : 0 < 1 + |p.χ| := by positivity
  have hsmall : (1 + |p.χ|) * d ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hd_le_inv hden_pos.le
    have hleft : (1 + |p.χ|) * (1 / (1 + |p.χ|)) = 1 := by
      field_simp [ne_of_gt hden_pos]
    nlinarith
  have hd_le_one : d ≤ 1 := by
    nlinarith [abs_nonneg p.χ, hsmall]
  have hd_alpha_le :
      d ^ p.α ≤ d := by
    calc d ^ p.α ≤ d ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hd_pos hd_le_one p.hα
      _ = d := Real.rpow_one d
  have hmg_ge_one : 1 ≤ p.m + p.γ - 1 := by
    linarith [p.hm, p.hγ]
  have hd_mg_le :
      d ^ (p.m + p.γ - 1) ≤ d := by
    calc d ^ (p.m + p.γ - 1) ≤ d ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hd_pos hd_le_one hmg_ge_one
      _ = d := Real.rpow_one d
  have hcore_abs :
      0 ≤ 1 - d ^ p.α - |p.χ| * d ^ (p.m + p.γ - 1) := by
    have hchem_small :
        |p.χ| * d ^ (p.m + p.γ - 1) ≤ |p.χ| * d :=
      mul_le_mul_of_nonneg_left hd_mg_le (abs_nonneg p.χ)
    nlinarith
  have hχ_abs : -p.χ = |p.χ| := by
    rw [abs_of_nonpos hχ]
  have hcore :
      0 ≤ 1 - d ^ p.α - (-p.χ) * d ^ (p.m + p.γ - 1) := by
    simpa [hχ_abs] using hcore_abs
  have hV_nonneg : 0 ≤ frozenElliptic p u x :=
    frozenElliptic_nonneg p hu_nonneg x
  have hdm_nonneg : 0 ≤ d ^ (p.m - 1) :=
    Real.rpow_nonneg hd_nonneg _
  have hVterm :
      0 ≤ -p.χ * d ^ (p.m - 1) * frozenElliptic p u x := by
    exact mul_nonneg
      (mul_nonneg (neg_nonneg.mpr hχ) hdm_nonneg)
      hV_nonneg
  nlinarith

theorem constant_subsolution_paperWaveOperator_nonneg_of_chi_nonpos
    (p : CMParams) {κ κtilde D d c M : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ ≤ 0)
    (hd_pos : 0 < d)
    (hd_le : d ≤ constantSubsolutionThreshold p.χ κ κtilde D)
    (hu : InWaveTrapSet κ M u) :
    IsPaperFrozenSubSolutionOn p c u (fun _ => d) Set.univ := by
  intro x _hx
  exact paperWaveOperator_const_subsolution_nonneg_of_chi_nonpos
    p hχ hu.cunif_bdd hu.nonneg hd_pos hd_le x

theorem paperWaveOperator_const_subsolution_nonneg_of_chi_nonneg
    (p : CMParams) {c κ κtilde D d : ℝ} {u : ℝ → ℝ}
    (hχ_nonneg : 0 ≤ p.χ) (hχ : p.χ < chiStar p)
    (hα : p.α = p.m + p.γ - 1)
    (hd_pos : 0 < d)
    (hd_le : d ≤ constantSubsolutionThreshold p.χ κ κtilde D)
    (hu : InWaveTrapSet κ 1 u)
    (x : ℝ) :
    0 ≤ paperWaveOperator p c u (fun _ => d) x := by
  rw [paperWaveOperator_const_eq p hu.cunif_bdd hu.nonneg x]
  apply mul_nonneg hd_pos.le
  have hd_nonneg : 0 ≤ d := hd_pos.le
  have hd_le_inv : d ≤ 1 / (1 + |p.χ|) := by
    exact le_trans hd_le (min_le_left _ _)
  have hden_pos : 0 < 1 + |p.χ| := by positivity
  have hinv_le_one : 1 / (1 + |p.χ|) ≤ (1 : ℝ) := by
    have hden_ge : 1 ≤ 1 + |p.χ| :=
      le_add_of_nonneg_right (abs_nonneg p.χ)
    simpa [one_div] using inv_le_one_of_one_le₀ hden_ge
  have hd_le_one : d ≤ 1 := le_trans hd_le_inv hinv_le_one
  have hχ_le_one : p.χ ≤ 1 :=
    le_trans (le_of_lt hχ) (chiStar_le_one p)
  have hV_le_one : frozenElliptic p u x ≤ 1 := by
    simpa using
      (frozenElliptic_le_M_of_inWaveTrapSet p one_pos le_rfl hu x)
  have hq_nonneg : 0 ≤ d ^ (p.m - 1) :=
    Real.rpow_nonneg hd_nonneg _
  have hq_le_one : d ^ (p.m - 1) ≤ 1 :=
    Real.rpow_le_one hd_nonneg hd_le_one (by linarith [p.hm])
  have hr_nonneg : 0 ≤ d ^ p.γ :=
    Real.rpow_nonneg hd_nonneg _
  have hr_le_one : d ^ p.γ ≤ 1 :=
    Real.rpow_le_one hd_nonneg hd_le_one (by linarith [p.hγ])
  have hpow_mγ :
      d ^ (p.m + p.γ - 1) = d ^ (p.m - 1) * d ^ p.γ := by
    rw [← Real.rpow_add hd_pos]
    congr 1
    ring
  have hcore_model :
      0 ≤ 1 - d ^ (p.m + p.γ - 1) -
          p.χ * d ^ (p.m - 1) + p.χ * d ^ (p.m + p.γ - 1) := by
    rw [hpow_mγ]
    have hpart1 : 0 ≤ 1 - d ^ (p.m - 1) :=
      sub_nonneg.mpr hq_le_one
    have hpart2 :
        0 ≤ (1 - p.χ) * d ^ (p.m - 1) * (1 - d ^ p.γ) :=
      mul_nonneg
        (mul_nonneg (sub_nonneg.mpr hχ_le_one) hq_nonneg)
        (sub_nonneg.mpr hr_le_one)
    have hdecomp :
        1 - d ^ (p.m - 1) * d ^ p.γ -
            p.χ * d ^ (p.m - 1) +
            p.χ * (d ^ (p.m - 1) * d ^ p.γ) =
          (1 - d ^ (p.m - 1)) +
            (1 - p.χ) * d ^ (p.m - 1) * (1 - d ^ p.γ) := by
      ring
    rw [hdecomp]
    exact add_nonneg hpart1 hpart2
  have hVterm_le :
      p.χ * d ^ (p.m - 1) * frozenElliptic p u x ≤
        p.χ * d ^ (p.m - 1) * 1 := by
    exact mul_le_mul_of_nonneg_left hV_le_one
      (mul_nonneg hχ_nonneg hq_nonneg)
  rw [hα]
  nlinarith

theorem constant_subsolution_paperWaveOperator_nonneg_of_chi_nonneg
    (p : CMParams) {κ κtilde D d c : ℝ} {u : ℝ → ℝ}
    (hχ_nonneg : 0 ≤ p.χ) (hχ : p.χ < chiStar p)
    (hα : p.α = p.m + p.γ - 1)
    (hd_pos : 0 < d)
    (hd_le : d ≤ constantSubsolutionThreshold p.χ κ κtilde D)
    (hu : InWaveTrapSet κ 1 u) :
    IsPaperFrozenSubSolutionOn p c u (fun _ => d) Set.univ := by
  intro x _hx
  exact paperWaveOperator_const_subsolution_nonneg_of_chi_nonneg
    p hχ_nonneg hχ hα hd_pos hd_le hu x

theorem expDecay_rpow_eq (κ m x : ℝ) :
    (expDecay κ x) ^ m = expDecay (m * κ) x := by
  unfold expDecay
  rw [← Real.exp_mul]
  congr 1; ring

theorem expDecay_rpow_hasDerivAt (κ m x : ℝ) :
    HasDerivAt (fun y => (expDecay κ y) ^ m)
      (-(m * κ) * (expDecay κ x) ^ m) x := by
  have : (fun y => (expDecay κ y) ^ m) = expDecay (m * κ) := by
    ext y; exact expDecay_rpow_eq κ m y
  rw [this, expDecay_rpow_eq κ m x]
  exact expDecay_hasDerivAt (m * κ) x

theorem expDecay_rpow_deriv (κ m x : ℝ) :
    deriv (fun y => (expDecay κ y) ^ m) x = -(m * κ) * (expDecay κ x) ^ m :=
  (expDecay_rpow_hasDerivAt κ m x).deriv

theorem paperWaveOperator_exp_eq_of_kappa_speed
    (p : CMParams) {c κ : ℝ} {u : ℝ → ℝ}
    (hκ : κ ≠ 0) (hc : c = κ + κ⁻¹) (x : ℝ) :
    paperWaveOperator p c u (expDecay κ) x =
      -expDecay κ x * (expDecay κ x) ^ p.α
        - p.χ * p.m * (expDecay κ x) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x * (-κ * expDecay κ x)
        + expDecay κ x *
          (-p.χ * (expDecay κ x) ^ (p.m - 1) *
            frozenElliptic p u x
          + p.χ * (expDecay κ x) ^ (p.m + p.γ - 1)) := by
  unfold paperWaveOperator
  rw [expDecay_iteratedDeriv_two, expDecay_deriv]
  have hlin :
      κ ^ 2 * expDecay κ x + c * (-κ * expDecay κ x) +
          expDecay κ x = 0 := by
    have h := expDecay_linear_part_eq_of_kappa_speed
      (κ := κ) (c := c) (x := x) hκ hc
    rw [expDecay_iteratedDeriv_two, expDecay_deriv] at h
    exact h
  nlinarith

theorem paperWaveOperator_exp_nonpos_of_kappa_speed_of_dominance
    (p : CMParams) {c κ : ℝ} {u : ℝ → ℝ}
    (hκ : κ ≠ 0) (hc : c = κ + κ⁻¹) (x : ℝ)
    (hdom :
      - p.χ * p.m * (expDecay κ x) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x * (-κ * expDecay κ x)
        + expDecay κ x *
          (-p.χ * (expDecay κ x) ^ (p.m - 1) *
            frozenElliptic p u x
          + p.χ * (expDecay κ x) ^ (p.m + p.γ - 1)) ≤
        expDecay κ x * (expDecay κ x) ^ p.α) :
    paperWaveOperator p c u (expDecay κ) x ≤ 0 := by
  rw [paperWaveOperator_exp_eq_of_kappa_speed p hκ hc x]
  nlinarith

theorem chemotaxis_product_rule_exp
    (p : CMParams) {κ : ℝ} {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x) (x : ℝ)
    (hV_diff : DifferentiableAt ℝ (deriv (frozenElliptic p u)) x) :
    deriv (fun y => (expDecay κ y) ^ p.m *
        deriv (frozenElliptic p u) y) x =
      (expDecay κ x) ^ p.m *
        (-(p.m * κ) * deriv (frozenElliptic p u) x +
          frozenElliptic p u x - (u x) ^ p.γ) := by
  have hexp_deriv := expDecay_rpow_hasDerivAt κ p.m x
  have hV_deriv : HasDerivAt (deriv (frozenElliptic p u))
      (frozenElliptic p u x - (u x) ^ p.γ) x := by
    rw [← frozenElliptic_deriv_deriv_eq p hu hu_nonneg x]
    exact hV_diff.hasDerivAt
  have hprod := hexp_deriv.mul hV_deriv
  have hfun_eq :
      (fun y => (expDecay κ y) ^ p.m * deriv (frozenElliptic p u) y) =
      (fun y => (expDecay κ y) ^ p.m) * deriv (frozenElliptic p u) := by
    ext y; simp [Pi.mul_apply]
  rw [hfun_eq, hprod.deriv]
  ring

theorem frozenWaveOperator_exp_full_eq
    (p : CMParams) {c κ : ℝ} {u : ℝ → ℝ}
    (hc : 2 ≤ c) (hκ : κ = kappa c)
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x) (x : ℝ)
    (hV_diff : DifferentiableAt ℝ (deriv (frozenElliptic p u)) x) :
    frozenWaveOperator p c u (expDecay κ) x =
      -(expDecay κ x) * (expDecay κ x) ^ p.α
      - p.χ * (expDecay κ x) ^ p.m *
        (-(p.m * κ) * deriv (frozenElliptic p u) x +
          frozenElliptic p u x - (u x) ^ p.γ) := by
  rw [frozenWaveOperator_exp_eq p hc hκ hu hu_nonneg x,
    chemotaxis_product_rule_exp p hu hu_nonneg x hV_diff]
  ring

theorem frozenWaveOperator_exp_nonpos_of_chi_nonpos_of_dominance
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hc : 2 ≤ c) (hκ_eq : κ = kappa c) (hκ_nonneg : 0 ≤ κ)
    (hχ : p.χ ≤ 0) (hu : InWaveTrapSet κ M u) (x : ℝ)
    (hV_diff : DifferentiableAt ℝ (deriv (frozenElliptic p u)) x)
    (hdom :
      -p.χ * (expDecay κ x) ^ p.m *
          ((p.m * κ + 1) * frozenElliptic p u x - (u x) ^ p.γ) ≤
        expDecay κ x * (expDecay κ x) ^ p.α) :
    frozenWaveOperator p c u (expDecay κ) x ≤ 0 := by
  have hVx_abs := frozenElliptic_deriv_abs_le p hu.cunif_bdd hu.nonneg x
  have hnegVx_le :
      -deriv (frozenElliptic p u) x ≤ frozenElliptic p u x :=
    le_trans (neg_le_abs _) hVx_abs
  have hmk_nonneg : 0 ≤ p.m * κ :=
    mul_nonneg (le_trans zero_le_one p.hm) hκ_nonneg
  have hterm :
      -(p.m * κ) * deriv (frozenElliptic p u) x ≤
        (p.m * κ) * frozenElliptic p u x := by
    calc
      -(p.m * κ) * deriv (frozenElliptic p u) x =
          (p.m * κ) * (-deriv (frozenElliptic p u) x) := by ring
      _ ≤ (p.m * κ) * frozenElliptic p u x :=
          mul_le_mul_of_nonneg_left hnegVx_le hmk_nonneg
  have hbracket :
      -(p.m * κ) * deriv (frozenElliptic p u) x +
          frozenElliptic p u x - (u x) ^ p.γ ≤
        (p.m * κ + 1) * frozenElliptic p u x - (u x) ^ p.γ := by
    nlinarith [hterm]
  have hcoef_nonneg :
      0 ≤ -p.χ * (expDecay κ x) ^ p.m :=
    mul_nonneg (neg_nonneg.mpr hχ)
      (Real.rpow_nonneg (expDecay_pos κ x).le p.m)
  have hchem_le :
      -p.χ * (expDecay κ x) ^ p.m *
          (-(p.m * κ) * deriv (frozenElliptic p u) x +
            frozenElliptic p u x - (u x) ^ p.γ) ≤
        -p.χ * (expDecay κ x) ^ p.m *
          ((p.m * κ + 1) * frozenElliptic p u x - (u x) ^ p.γ) :=
    mul_le_mul_of_nonneg_left hbracket hcoef_nonneg
  rw [frozenWaveOperator_exp_full_eq p hc hκ_eq hu.cunif_bdd hu.nonneg x hV_diff]
  linarith

theorem setIntegral_Iic_exp_le_of_rpow_le
    {κ : ℝ} {u : ℝ → ℝ} {γ : ℝ}
    (_hκ : 0 < κ) (_hγ : 0 < γ) (hγκ : γ * κ < 1)
    (hu_exp : ∀ y, (u y) ^ γ ≤ Real.exp (-(γ * κ) * y))
    (x : ℝ)
    (hint : IntegrableOn (fun y => Real.exp (1 * y) * (u y) ^ γ) (Set.Iic x)) :
    ∫ y in Set.Iic x, Real.exp (1 * y) * (u y) ^ γ ≤
      Real.exp ((1 - γ * κ) * x) / (1 - γ * κ) := by
  have h1mgk : 0 < 1 - γ * κ := by linarith
  have hint_exp : IntegrableOn
      (fun y => Real.exp ((1 - γ * κ) * y)) (Set.Iic x) :=
    integrableOn_exp_mul_Iic h1mgk x
  calc ∫ y in Set.Iic x, Real.exp (1 * y) * (u y) ^ γ
      ≤ ∫ y in Set.Iic x, Real.exp ((1 - γ * κ) * y) := by
        apply MeasureTheory.setIntegral_mono hint hint_exp
        intro y
        calc Real.exp (1 * y) * (u y) ^ γ
            ≤ Real.exp (1 * y) * Real.exp (-(γ * κ) * y) :=
              mul_le_mul_of_nonneg_left (hu_exp y) (Real.exp_nonneg _)
          _ = Real.exp ((1 - γ * κ) * y) := by
              rw [← Real.exp_add]; congr 1; ring
    _ = Real.exp ((1 - γ * κ) * x) / (1 - γ * κ) :=
        integral_exp_mul_Iic h1mgk x

theorem setIntegral_Ioi_exp_le_of_rpow_le
    {κ : ℝ} {u : ℝ → ℝ} {γ : ℝ}
    (_hκ : 0 < κ) (_hγ : 0 < γ) (hγκ : γ * κ < 1)
    (hu_exp : ∀ y, (u y) ^ γ ≤ Real.exp (-(γ * κ) * y))
    (x : ℝ)
    (hint : IntegrableOn (fun y => Real.exp (-1 * y) * (u y) ^ γ) (Set.Ioi x)) :
    ∫ y in Set.Ioi x, Real.exp (-1 * y) * (u y) ^ γ ≤
      Real.exp (-(1 + γ * κ) * x) / (1 + γ * κ) := by
  have h1pgk : 0 < 1 + γ * κ := by positivity
  have hneg : -(1 + γ * κ) < 0 := by linarith
  have hint_exp : IntegrableOn
      (fun y => Real.exp (-(1 + γ * κ) * y)) (Set.Ioi x) :=
    integrableOn_exp_mul_Ioi hneg x
  calc ∫ y in Set.Ioi x, Real.exp (-1 * y) * (u y) ^ γ
      ≤ ∫ y in Set.Ioi x, Real.exp (-(1 + γ * κ) * y) := by
        apply MeasureTheory.setIntegral_mono hint hint_exp
        intro y
        calc Real.exp (-1 * y) * (u y) ^ γ
            ≤ Real.exp (-1 * y) * Real.exp (-(γ * κ) * y) :=
              mul_le_mul_of_nonneg_left (hu_exp y) (Real.exp_nonneg _)
          _ = Real.exp (-(1 + γ * κ) * y) := by
              rw [← Real.exp_add]; congr 1; ring
    _ = -Real.exp (-(1 + γ * κ) * x) / (-(1 + γ * κ)) :=
        integral_exp_mul_Ioi hneg x
    _ = Real.exp (-(1 + γ * κ) * x) / (1 + γ * κ) := by
        field_simp

theorem chemotaxis_resolvent_bound
    (p : CMParams) {κ M : ℝ} {u : ℝ → ℝ}
    (hκ : 0 < κ) (hγκ : p.γ * κ < 1) (hmκ : κ * p.m ≤ 1)
    (_hM : 1 ≤ M) (hu : InWaveTrapSet κ M u) (x : ℝ) :
    -κ * p.m * deriv (frozenElliptic p u) x +
        frozenElliptic p u x ≤
      (1 + p.m * p.γ * κ ^ 2) / (1 - p.γ ^ 2 * κ ^ 2) *
        Real.exp (-(p.γ * κ) * x) := by
  have hγ_pos : 0 < p.γ := by linarith [p.hγ]
  have hγκ_pos : 0 < p.γ * κ := mul_pos hγ_pos hκ
  have hf := fun y => (hu.nonneg y)
  have hf_rpow : ∀ y, 0 ≤ (u y) ^ p.γ := fun y => Real.rpow_nonneg (hf y) p.γ
  have hu_bdd := hu.cunif_bdd
  have hu_rpow := rpow_cunif_bdd_of_nonneg p hu_bdd hf
  have hVx := Psi_derivative_formula_general (l := 1) (mu := 1) one_pos one_pos hu_rpow x
  have hu_rpow_le_exp : ∀ y, (u y) ^ p.γ ≤ Real.exp (-(p.γ * κ) * y) := by
    intro y
    calc (u y) ^ p.γ ≤ (Real.exp (-κ * y)) ^ p.γ :=
          Real.rpow_le_rpow (hf y) (hu.le_exp y) (by linarith)
      _ = Real.exp (-(p.γ * κ) * y) := by rw [← Real.exp_mul]; congr 1; ring
  have hgk : p.γ * κ < 1 := hγκ
  have h1mgk : 0 < 1 - p.γ * κ := by linarith
  have h1pgk : 0 < 1 + p.γ * κ := by positivity
  have hmk_pos : 0 ≤ p.m * κ := mul_nonneg (by linarith [p.hm]) hκ.le
  have hmk1 : 0 < κ * p.m + 1 := by linarith [mul_pos hκ (by linarith [p.hm] : 0 < p.m)]
  -- Write V'(x) from Psi_derivative_formula_general (with √1=1, μ=1):
  -- V'(x) = -(1/2)·exp(-x)·L(x) + (1/2)·exp(x)·R(x)
  -- V(x) = (1/2)·[exp(-x)·L(x) + exp(x)·R(x)]  (kernel splitting)
  -- -κm·V' + V = (1/2)(κm+1)·exp(-x)·L + (1/2)(1-κm)·exp(x)·R
  -- Use L ≤ exp((1-γκ)x)/(1-γκ), R ≤ exp(-(1+γκ)x)/(1+γκ)
  -- Second term ≤ 0 when mκ ≥ 1, and contributes positively when mκ < 1.
  -- In both cases: total ≤ (1+mγκ²)/(1-γ²κ²) · exp(-γκx).
  set L := ∫ y in Set.Iic x, Real.exp (1 * y) * (u y) ^ p.γ
  set R := ∫ y in Set.Ioi x, Real.exp (-1 * y) * (u y) ^ p.γ
  have hL_int : IntegrableOn (fun y => Real.exp (1 * y) * (u y) ^ p.γ)
      (Set.Iic x) := by
    have hdom : IntegrableOn
        (fun y => Real.exp ((1 - p.γ * κ) * y)) (Set.Iic x) :=
      integrableOn_exp_mul_Iic h1mgk x
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        hu_rpow.1).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      rw [abs_of_nonneg
        (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg (hf y) p.γ))]
      calc Real.exp (1 * y) * (u y) ^ p.γ
          ≤ Real.exp (1 * y) * Real.exp (-(p.γ * κ) * y) :=
            mul_le_mul_of_nonneg_left (hu_rpow_le_exp y) (Real.exp_nonneg _)
        _ = Real.exp ((1 - p.γ * κ) * y) := by
            rw [← Real.exp_add]
            congr 1
            ring
  have hR_int : IntegrableOn (fun y => Real.exp (-1 * y) * (u y) ^ p.γ)
      (Set.Ioi x) := by
    have hdom : IntegrableOn
        (fun y => Real.exp (-(1 + p.γ * κ) * y)) (Set.Ioi x) :=
      integrableOn_exp_mul_Ioi (by linarith : -(1 + p.γ * κ) < (0 : ℝ)) x
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        hu_rpow.1).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      rw [abs_of_nonneg
        (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg (hf y) p.γ))]
      calc Real.exp (-1 * y) * (u y) ^ p.γ
          ≤ Real.exp (-1 * y) * Real.exp (-(p.γ * κ) * y) :=
            mul_le_mul_of_nonneg_left (hu_rpow_le_exp y) (Real.exp_nonneg _)
        _ = Real.exp (-(1 + p.γ * κ) * y) := by
            rw [← Real.exp_add]
            congr 1
            ring
  have hL_bound := setIntegral_Iic_exp_le_of_rpow_le hκ hγ_pos hγκ
    hu_rpow_le_exp x hL_int
  have hR_bound := setIntegral_Ioi_exp_le_of_rpow_le hκ hγ_pos hγκ
    hu_rpow_le_exp x hR_int
  -- V'(x) from Psi_derivative_formula_general:
  -- V'(x) = -(1/2)·exp(-x)·L + (1/2)·exp(x)·R
  simp only [Real.sqrt_one] at hVx
  have hV' : deriv (frozenElliptic p u) x =
      -(1 / 2) * Real.exp (-1 * x) * L + (1 / 2) * Real.exp (1 * x) * R := by
    have : (fun z => frozenElliptic p u z) =
        (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) := rfl
    rw [show deriv (frozenElliptic p u) x =
        deriv (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x from
      congr_arg (fun f => deriv f x) this, hVx]
  -- V(x) = (1/2)·(exp(-x)·L + exp(x)·R) from kernel splitting
  have hV : frozenElliptic p u x =
      1 / 2 * (Real.exp (-1 * x) * L + Real.exp (1 * x) * R) := by
    exact Psi_kernel_splitting hu_rpow (fun y => hf_rpow y) x
  -- Combine: -κm·V' + V = (1/2)(κm+1)·exp(-x)·L + (1/2)(1-κm)·exp(x)·R
  have hcomb :
      -κ * p.m * deriv (frozenElliptic p u) x + frozenElliptic p u x =
        1 / 2 * (κ * p.m + 1) * (Real.exp (-1 * x) * L) +
          1 / 2 * (1 - κ * p.m) * (Real.exp (1 * x) * R) := by
    rw [hV', hV]; ring
  rw [hcomb]
  -- Apply bounds and coefficient algebra
  have hcoeff :
      (κ * p.m + 1) * (1 + p.γ * κ) + (1 - κ * p.m) * (1 - p.γ * κ) =
        2 * (1 + p.m * p.γ * κ ^ 2) := by ring
  have hden : (1 - p.γ * κ) * (1 + p.γ * κ) = 1 - p.γ ^ 2 * κ ^ 2 := by ring
  have hden_pos : 0 < 1 - p.γ ^ 2 * κ ^ 2 := by nlinarith [sq_nonneg (p.γ * κ - 1)]
  have hexp_combine_L :
      Real.exp (-1 * x) * (Real.exp ((1 - p.γ * κ) * x) / (1 - p.γ * κ)) =
        Real.exp (-(p.γ * κ) * x) / (1 - p.γ * κ) := by
    field_simp [ne_of_gt h1mgk]
    rw [← Real.exp_add]; congr 1; ring
  have hexp_combine_R :
      Real.exp (1 * x) * (Real.exp (-(1 + p.γ * κ) * x) / (1 + p.γ * κ)) =
        Real.exp (-(p.γ * κ) * x) / (1 + p.γ * κ) := by
    field_simp [ne_of_gt h1pgk]
    rw [← Real.exp_add]; congr 1; ring
  -- The LHS after rewriting equals:
  -- (1/2)(κm+1)·exp(-x)·L + (1/2)(1-κm)·exp(x)·R
  -- Bound L and R, simplify exp products, combine coefficients.
  have hL_nonneg : 0 ≤ L := by
    apply MeasureTheory.setIntegral_nonneg measurableSet_Iic
    intro y _; exact mul_nonneg (Real.exp_nonneg _) (hf_rpow y)
  have hR_nonneg : 0 ≤ R := by
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro y _; exact mul_nonneg (Real.exp_nonneg _) (hf_rpow y)
  have hexp_nonneg : 0 ≤ Real.exp (-(p.γ * κ) * x) := Real.exp_nonneg _
  -- First term bound
  have hterm1 :
      1 / 2 * (κ * p.m + 1) * (Real.exp (-1 * x) * L) ≤
        1 / 2 * (κ * p.m + 1) / (1 - p.γ * κ) * Real.exp (-(p.γ * κ) * x) := by
    have h1 : 0 ≤ 1 / 2 * (κ * p.m + 1) := by positivity
    calc 1 / 2 * (κ * p.m + 1) * (Real.exp (-1 * x) * L)
        ≤ 1 / 2 * (κ * p.m + 1) *
            (Real.exp (-1 * x) * (Real.exp ((1 - p.γ * κ) * x) / (1 - p.γ * κ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hL_bound (Real.exp_nonneg _)) h1
      _ = 1 / 2 * (κ * p.m + 1) *
            (Real.exp (-(p.γ * κ) * x) / (1 - p.γ * κ)) := by
          rw [hexp_combine_L]
      _ = _ := by ring
  -- Second term bound
  have hterm2_bound :
      Real.exp (1 * x) * R ≤ Real.exp (-(p.γ * κ) * x) / (1 + p.γ * κ) := by
    calc Real.exp (1 * x) * R
        ≤ Real.exp (1 * x) * (Real.exp (-(1 + p.γ * κ) * x) / (1 + p.γ * κ)) :=
          mul_le_mul_of_nonneg_left hR_bound (Real.exp_nonneg _)
      _ = _ := hexp_combine_R
  -- Both terms contribute positively (using hmκ : κ * p.m ≤ 1)
  have h2 : (0 : ℝ) ≤ 1 / 2 * (1 - κ * p.m) := by linarith
  have hterm2 :
      1 / 2 * (1 - κ * p.m) * (Real.exp (1 * x) * R) ≤
        1 / 2 * (1 - κ * p.m) / (1 + p.γ * κ) *
          Real.exp (-(p.γ * κ) * x) := by
    calc 1 / 2 * (1 - κ * p.m) * (Real.exp (1 * x) * R)
        ≤ 1 / 2 * (1 - κ * p.m) *
            (Real.exp (-(p.γ * κ) * x) / (1 + p.γ * κ)) :=
          mul_le_mul_of_nonneg_left hterm2_bound h2
      _ = _ := by ring
  have htotal := add_le_add hterm1 hterm2
  -- Show the bound sum = target
  suffices hbound_eq :
      1 / 2 * (κ * p.m + 1) / (1 - p.γ * κ) * Real.exp (-(p.γ * κ) * x) +
        1 / 2 * (1 - κ * p.m) / (1 + p.γ * κ) * Real.exp (-(p.γ * κ) * x) =
        (1 + p.m * p.γ * κ ^ 2) / (1 - p.γ ^ 2 * κ ^ 2) *
          Real.exp (-(p.γ * κ) * x) by
    linarith
  -- Factor out exp(-γκx), use coefficient identity
  have hfact : ∀ a b : ℝ,
      a * Real.exp (-(p.γ * κ) * x) + b * Real.exp (-(p.γ * κ) * x) =
        (a + b) * Real.exp (-(p.γ * κ) * x) := by intros; ring
  rw [hfact]
  congr 1
  rw [← hden]
  rw [div_add_div _ _ (ne_of_gt h1mgk) (ne_of_gt h1pgk)]
  congr 1
  nlinarith [hcoeff]

theorem paperWaveOperator_exp_region_hdom_of_resolvent_bound
    (p : CMParams) {κ M : ℝ} {u : ℝ → ℝ}
    (hκ : 0 < κ) (hγκ : p.γ * κ < 1) (hmκ : κ * p.m ≤ 1)
    (hχ : p.χ ≤ 0) (hM : 1 ≤ M) (hu : InWaveTrapSet κ M u) (x : ℝ)
    (hgap :
      -p.χ * (expDecay κ x) ^ p.m *
          (((1 + p.m * p.γ * κ ^ 2) / (1 - p.γ ^ 2 * κ ^ 2)) *
            (expDecay κ x) ^ p.γ - (expDecay κ x) ^ p.γ) ≤
        expDecay κ x * (expDecay κ x) ^ p.α) :
    - p.χ * p.m * (expDecay κ x) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x * (-κ * expDecay κ x)
        + expDecay κ x *
          (-p.χ * (expDecay κ x) ^ (p.m - 1) *
            frozenElliptic p u x
          + p.χ * (expDecay κ x) ^ (p.m + p.γ - 1)) ≤
        expDecay κ x * (expDecay κ x) ^ p.α := by
  let E := expDecay κ x
  let V := frozenElliptic p u x
  let Vx := deriv (frozenElliptic p u) x
  let C := (1 + p.m * p.γ * κ ^ 2) / (1 - p.γ ^ 2 * κ ^ 2)
  have hE_pos : 0 < E := by
    dsimp [E]
    exact expDecay_pos κ x
  have hE_nonneg : 0 ≤ E := hE_pos.le
  have hEgamma :
      Real.exp (-(p.γ * κ) * x) = E ^ p.γ := by
    dsimp [E]
    rw [expDecay_rpow_eq κ p.γ x]
    unfold expDecay
    congr 1
    ring
  have hres :
      -(κ * p.m) * Vx + V ≤ C * E ^ p.γ := by
    dsimp [V, Vx, C]
    have h := chemotaxis_resolvent_bound p hκ hγκ hmκ hM hu x
    rw [hEgamma] at h
    convert h using 1 <;> ring
  have hbracket :
      -(κ * p.m) * Vx + V - E ^ p.γ ≤ C * E ^ p.γ - E ^ p.γ := by
    linarith
  have hcoef_nonneg : 0 ≤ -p.χ * E ^ p.m := by
    exact mul_nonneg (neg_nonneg.mpr hχ)
      (Real.rpow_nonneg hE_nonneg p.m)
  have hchem_le :
      -p.χ * E ^ p.m * (-(κ * p.m) * Vx + V - E ^ p.γ) ≤
        -p.χ * E ^ p.m * (C * E ^ p.γ - E ^ p.γ) :=
    mul_le_mul_of_nonneg_left hbracket hcoef_nonneg
  have hpow_m : E ^ (p.m - 1) * E = E ^ p.m := by
    calc
      E ^ (p.m - 1) * E = E ^ (p.m - 1) * E ^ (1 : ℝ) := by
        rw [Real.rpow_one E]
      _ = E ^ ((p.m - 1) + 1) := by
        rw [Real.rpow_add hE_pos]
      _ = E ^ p.m := by
        congr 1
        ring
  have hpow_mγ : E * E ^ (p.m + p.γ - 1) = E ^ p.m * E ^ p.γ := by
    calc
      E * E ^ (p.m + p.γ - 1) =
          E ^ (1 : ℝ) * E ^ (p.m + p.γ - 1) := by
        rw [Real.rpow_one E]
      _ = E ^ (1 + (p.m + p.γ - 1)) := by
        rw [Real.rpow_add hE_pos]
      _ = E ^ (p.m + p.γ) := by
        congr 1
        ring
      _ = E ^ p.m * E ^ p.γ := by
        rw [← Real.rpow_add hE_pos]
  have hrewrite :
      - p.χ * p.m * E ^ (p.m - 1) * Vx * (-κ * E)
        + E * (-p.χ * E ^ (p.m - 1) * V + p.χ * E ^ (p.m + p.γ - 1)) =
      -p.χ * E ^ p.m * (-(κ * p.m) * Vx + V - E ^ p.γ) := by
    calc
      - p.χ * p.m * E ^ (p.m - 1) * Vx * (-κ * E)
          + E * (-p.χ * E ^ (p.m - 1) * V + p.χ * E ^ (p.m + p.γ - 1))
          =
        - p.χ * p.m * (E ^ (p.m - 1) * E) * Vx * (-κ)
          + (-p.χ * (E ^ (p.m - 1) * E) * V
            + p.χ * (E * E ^ (p.m + p.γ - 1))) := by
            ring
      _ = -p.χ * p.m * E ^ p.m * Vx * (-κ)
          + (-p.χ * E ^ p.m * V + p.χ * (E ^ p.m * E ^ p.γ)) := by
            rw [hpow_m, hpow_mγ]
      _ = -p.χ * E ^ p.m * (-(κ * p.m) * Vx + V - E ^ p.γ) := by
            ring
  dsimp [E, V, Vx, C] at hrewrite hchem_le hgap
  rw [hrewrite]
  exact le_trans hchem_le hgap

theorem paperWaveOperator_exp_nonpos_of_chi_nonpos
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hγκ : p.γ * κ < 1) (hmκ : κ * p.m ≤ 1)
    (hM : 1 ≤ M)
    (hMbound : |p.χ| * (1 + p.m * p.γ * κ ^ 2) /
        (1 - p.γ ^ 2 * κ ^ 2) *
        M ^ (p.m + p.γ - p.α - 1) ≤
        1 + |p.χ| * M ^ (p.m + p.γ - p.α - 1))
    (hu : InWaveTrapSet κ M u)
    {x : ℝ} (hx : Real.exp (-κ * x) < M)
    (hc : c = κ + κ⁻¹) :
    paperWaveOperator p c u (upperBarrier κ M) x ≤ 0 := by
  apply paperWaveOperator_upperBarrier_exp_region_nonpos_of_dominance p
    (ne_of_gt hκ) hc hx
  -- Use the bridge theorem
  apply paperWaveOperator_exp_region_hdom_of_resolvent_bound p hκ hγκ hmκ hχ hM hu x
  -- hgap: paper equation (4.6)
  -- Goal: -χ · E^m · ((C-1)·E^γ) ≤ E · E^α
  -- i.e., |χ|·(C-1)·E^{m+γ} ≤ E^{α+1}
  set E := expDecay κ x
  set C := (1 + p.m * p.γ * κ ^ 2) / (1 - p.γ ^ 2 * κ ^ 2)
  set δ := p.m + p.γ - p.α - 1
  have hE_pos : 0 < E := expDecay_pos κ x
  have hE_lt_M : E < M := by simpa [E, expDecay] using hx
  have hα_le : p.α ≤ p.m + p.γ - 1 := hα
  -- Factor E^{m+γ} = E^{α+1} · E^{m+γ-α-1}
  have hexp_split :
      E ^ p.m * E ^ p.γ = E ^ (p.α + 1) * E ^ (p.m + p.γ - p.α - 1) := by
    rw [← Real.rpow_add hE_pos, ← Real.rpow_add hE_pos]
    congr 1; ring
  -- E^{m+γ-α-1} ≤ M^{m+γ-α-1} since E < M and exponent ≥ 0
  have hexp_le : 0 ≤ p.m + p.γ - p.α - 1 := by linarith
  have hE_rpow_le :
      E ^ (p.m + p.γ - p.α - 1) ≤ M ^ (p.m + p.γ - p.α - 1) :=
    Real.rpow_le_rpow hE_pos.le hE_lt_M.le hexp_le
  -- E · E^α = E^{α+1}
  have hE_pow :
      E * E ^ p.α = E ^ (p.α + 1) := by
    have : E = E ^ (1 : ℝ) := (Real.rpow_one E).symm
    nth_rw 1 [this]
    rw [← Real.rpow_add hE_pos]; congr 1; ring
  have hγ_pos : 0 < p.γ := by linarith [p.hγ]
  have hγκ_pos : 0 < p.γ * κ := mul_pos hγ_pos hκ
  have hden_pos : 0 < 1 - p.γ ^ 2 * κ ^ 2 := by
    have hsq : (p.γ * κ) ^ 2 < 1 := by
      rw [sq_lt_one_iff_abs_lt_one]
      rw [abs_of_pos hγκ_pos]
      exact hγκ
    nlinarith
  have hC_ge_one : 1 ≤ C := by
    dsimp [C]
    rw [le_div_iff₀ hden_pos]
    have hm_nonneg : 0 ≤ p.m := by linarith [p.hm]
    have hγ_nonneg : 0 ≤ p.γ := by linarith [p.hγ]
    have hk2_nonneg : 0 ≤ κ ^ 2 := sq_nonneg κ
    have hterm1 : 0 ≤ p.m * p.γ * κ ^ 2 :=
      mul_nonneg (mul_nonneg hm_nonneg hγ_nonneg) hk2_nonneg
    have hterm2 : 0 ≤ p.γ ^ 2 * κ ^ 2 :=
      mul_nonneg (sq_nonneg p.γ) hk2_nonneg
    nlinarith
  have hcoef_nonneg : 0 ≤ |p.χ| * (C - 1) := by
    exact mul_nonneg (abs_nonneg p.χ) (sub_nonneg.mpr hC_ge_one)
  have hMboundC :
      |p.χ| * C * M ^ δ ≤ 1 + |p.χ| * M ^ δ := by
    have heq :
        |p.χ| * C * M ^ δ =
          |p.χ| * (1 + p.m * p.γ * κ ^ 2) /
            (1 - p.γ ^ 2 * κ ^ 2) * M ^ δ := by
      dsimp [C]
      ring
    rw [heq]
    exact hMbound
  have hcoef_M : |p.χ| * (C - 1) * M ^ δ ≤ 1 := by
    nlinarith
  have hE_rpow_le_delta : E ^ δ ≤ M ^ δ := by
    simpa [δ] using hE_rpow_le
  have hcoef_E : |p.χ| * (C - 1) * E ^ δ ≤ 1 := by
    exact le_trans
      (mul_le_mul_of_nonneg_left hE_rpow_le_delta hcoef_nonneg) hcoef_M
  have hminus_chi : -p.χ = |p.χ| := by
    rw [abs_of_nonpos hχ]
  have hright_nonneg : 0 ≤ E * E ^ p.α := by
    exact mul_nonneg hE_pos.le (Real.rpow_nonneg hE_pos.le p.α)
  calc
    -p.χ * E ^ p.m * (C * E ^ p.γ - E ^ p.γ)
        = (|p.χ| * (C - 1) * E ^ δ) * (E * E ^ p.α) := by
          rw [hminus_chi, hE_pow]
          calc
            |p.χ| * E ^ p.m * (C * E ^ p.γ - E ^ p.γ)
                = |p.χ| * (C - 1) * (E ^ p.m * E ^ p.γ) := by ring
            _ = |p.χ| * (C - 1) *
                  (E ^ (p.α + 1) * E ^ (p.m + p.γ - p.α - 1)) := by
                rw [hexp_split]
            _ = |p.χ| * (C - 1) * (E ^ (p.α + 1) * E ^ δ) := by
                simp [δ]
            _ = (|p.χ| * (C - 1) * E ^ δ) * E ^ (p.α + 1) := by ring
    _ ≤ 1 * (E * E ^ p.α) :=
        mul_le_mul_of_nonneg_right hcoef_E hright_nonneg
    _ = E * E ^ p.α := by ring

theorem Lemma_4_1_neg_holds_away_from_interface
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hγκ : p.γ * κ < 1) (hmκ : κ * p.m ≤ 1)
    (hM : 1 ≤ M)
    (hMbound : |p.χ| * (1 + p.m * p.γ * κ ^ 2) /
        (1 - p.γ ^ 2 * κ ^ 2) *
        M ^ (p.m + p.γ - p.α - 1) ≤
        1 + |p.χ| * M ^ (p.m + p.γ - p.α - 1))
    (hu : InWaveTrapSet κ M u)
    (hc : c = κ + κ⁻¹) :
    ∀ x, Real.exp (-κ * x) ≠ M →
      paperWaveOperator p c u (upperBarrier κ M) x ≤ 0 := by
  intro x hneq
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  ·
    exact paperWaveOperator_exp_nonpos_of_chi_nonpos p hχ hα hκ hκ1 hγκ hmκ
      hM hMbound hu hlt hc
  ·
    exact paperWaveOperator_upperBarrier_const_region_nonpos_neg p hχ hα hκ hM hu hgt

theorem paperWaveOperator_exp_nonpos_of_chi_nonpos_one_of_speed_bound
    (p : CMParams) {c κ : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hmκ : κ * p.m ≤ 1)
    (hspeed :
      (p.m * p.γ * |p.χ| + p.γ ^ 2 * |p.χ| + p.γ ^ 2) * κ ^ 2 < 1)
    (hu : InWaveTrapSet κ 1 u)
    {x : ℝ} (hx : Real.exp (-κ * x) < 1)
    (hc : c = κ + κ⁻¹) :
    paperWaveOperator p c u (upperBarrier κ 1) x ≤ 0 := by
  have hγ_pos : 0 < p.γ := by linarith [p.hγ]
  have hγκ_pos : 0 < p.γ * κ := mul_pos hγ_pos hκ
  have hγsqκsq_lt :
      p.γ ^ 2 * κ ^ 2 < 1 := by
    have hA_ge :
        p.γ ^ 2 ≤
          p.m * p.γ * |p.χ| + p.γ ^ 2 * |p.χ| + p.γ ^ 2 := by
      have hm_nonneg : 0 ≤ p.m := by linarith [p.hm]
      have hγ_nonneg : 0 ≤ p.γ := by linarith [p.hγ]
      have hχ_abs : 0 ≤ |p.χ| := abs_nonneg p.χ
      have hterm1 : 0 ≤ p.m * p.γ * |p.χ| :=
        mul_nonneg (mul_nonneg hm_nonneg hγ_nonneg) hχ_abs
      have hterm2 : 0 ≤ p.γ ^ 2 * |p.χ| :=
        mul_nonneg (sq_nonneg p.γ) hχ_abs
      nlinarith
    have hk2_nonneg : 0 ≤ κ ^ 2 := sq_nonneg κ
    have hmul_le :
        p.γ ^ 2 * κ ^ 2 ≤
          (p.m * p.γ * |p.χ| + p.γ ^ 2 * |p.χ| + p.γ ^ 2) * κ ^ 2 :=
      mul_le_mul_of_nonneg_right hA_ge hk2_nonneg
    exact lt_of_le_of_lt hmul_le hspeed
  have hγκ : p.γ * κ < 1 := by
    have hsquare : (p.γ * κ) ^ 2 < 1 := by
      nlinarith
    rw [sq_lt_one_iff_abs_lt_one] at hsquare
    rwa [abs_of_pos hγκ_pos] at hsquare
  have hden_pos : 0 < 1 - p.γ ^ 2 * κ ^ 2 := by
    linarith
  have hMbound :
      |p.χ| * (1 + p.m * p.γ * κ ^ 2) /
          (1 - p.γ ^ 2 * κ ^ 2) *
          (1 : ℝ) ^ (p.m + p.γ - p.α - 1) ≤
        1 + |p.χ| * (1 : ℝ) ^ (p.m + p.γ - p.α - 1) := by
    simp only [Real.one_rpow, mul_one]
    rw [div_le_iff₀ hden_pos]
    nlinarith [le_of_lt hspeed]
  exact paperWaveOperator_exp_nonpos_of_chi_nonpos p hχ hα hκ hκ1 hγκ hmκ
    le_rfl hMbound hu hx hc

def Lemma_4_2 : Prop :=
  ∀ p : CMParams, ∀ κ κtilde M c : ℝ,
    0 < κ → κ < 1 →
      κ < κtilde →
      κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1) →
      1 ≤ M → c = κ + κ⁻¹ →
        ∀ D : ℝ,
          subsolutionDThreshold p.χ M κ κtilde p.m p.γ c < D →
            ∀ u : ℝ → ℝ, InWaveTrapSet κ M u →
              IsFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
                (Set.Ioi (lowerBarrierXMinus κ κtilde D)) ∧
              ∀ d : ℝ, 0 < d → d ≤ constantSubsolutionThreshold p.χ κ κtilde D →
                IsFrozenSubSolutionOn p c u (fun _ => d) Set.univ

theorem Lemma_4_1.negative_superSolution
    (h : Lemma_4_1) {p : CMParams} (hχ : p.χ ≤ 0)
    (hα : p.α ≤ p.m + p.γ - 1)
    {κ M c : ℝ} (hκ_pos : 0 < κ) (hκ_lt_one : κ < 1)
    (hM : 1 ≤ M) (hc : c = κ + κ⁻¹)
    {u : ℝ → ℝ} (hu : InWaveTrapSet κ M u) :
    IsFrozenSuperSolution p c u (upperBarrier κ M) :=
  h.1 p hχ hα κ M c hκ_pos hκ_lt_one hM hc u hu

theorem Lemma_4_1.positive_superSolution
    (h : Lemma_4_1) {p : CMParams} (hχ_nonneg : 0 ≤ p.χ)
    (hχ : p.χ < chiStar p) (hα : p.α = p.m + p.γ - 1)
    {κ M c : ℝ} (hκ_pos : 0 < κ) (hκ_lt_one : κ < 1)
    (hM : 1 ≤ M)
    (hMchi : (1 / (1 - p.χ)) ^ (1 / p.α) ≤ M)
    (hc : c = κ + κ⁻¹)
    {u : ℝ → ℝ} (hu : InWaveTrapSet κ M u) :
    IsFrozenSuperSolution p c u (upperBarrier κ M) :=
  h.2 p hχ_nonneg hχ hα κ M c hκ_pos hκ_lt_one hM hMchi hc u hu

theorem Lemma_4_2.subsolutions
    (h : Lemma_4_2) {p : CMParams} {κ κtilde M c D : ℝ}
    (hκ_pos : 0 < κ) (hκ_lt_one : κ < 1) (hκ_gap : κ < κtilde)
    (hrange :
      κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1))
    (hM : 1 ≤ M) (hc : c = κ + κ⁻¹)
    (hD : subsolutionDThreshold p.χ M κ κtilde p.m p.γ c < D)
    {u : ℝ → ℝ} (hu : InWaveTrapSet κ M u) :
    IsFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
        (Set.Ioi (lowerBarrierXMinus κ κtilde D)) ∧
      ∀ d : ℝ, 0 < d → d ≤ constantSubsolutionThreshold p.χ κ κtilde D →
        IsFrozenSubSolutionOn p c u (fun _ => d) Set.univ :=
  h p κ κtilde M c hκ_pos hκ_lt_one hκ_gap hrange hM hc D hD u hu

/-- The finite-time upper barrier from Paper1 Remark 4.2:
`\tilde U^+_{κ,M}(x) = min {M, M exp(-κx)}`. -/
def scaledUpperBarrier (κ M : ℝ) : ℝ → ℝ :=
  fun x => min M (M * Real.exp (-κ * x))

theorem scaledUpperBarrier_le_M (κ M x : ℝ) :
    scaledUpperBarrier κ M x ≤ M :=
  min_le_left _ _

theorem scaledUpperBarrier_le_scaled_exp (κ M x : ℝ) :
    scaledUpperBarrier κ M x ≤ M * Real.exp (-κ * x) :=
  min_le_right _ _

theorem scaledUpperBarrier_nonneg {κ M : ℝ} (hM : 0 ≤ M) (x : ℝ) :
    0 ≤ scaledUpperBarrier κ M x :=
  le_min hM (mul_nonneg hM (Real.exp_pos _).le)

theorem scaledUpperBarrier_pos {κ M : ℝ} (hM : 0 < M) (x : ℝ) :
    0 < scaledUpperBarrier κ M x :=
  lt_min hM (mul_pos hM (Real.exp_pos _))

theorem scaledUpperBarrier_continuous (κ M : ℝ) :
    Continuous (scaledUpperBarrier κ M) := by
  unfold scaledUpperBarrier
  exact continuous_const.min
    (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)))

theorem scaledUpperBarrier_isBddFun {κ M : ℝ} (hM : 0 ≤ M) :
    IsBddFun (scaledUpperBarrier κ M) := by
  refine ⟨M, ?_⟩
  intro x
  rw [abs_of_nonneg (scaledUpperBarrier_nonneg hM x)]
  exact scaledUpperBarrier_le_M κ M x

theorem scaledUpperBarrier_cunif_bdd {κ M : ℝ} (hM : 0 ≤ M) :
    IsCUnifBdd (scaledUpperBarrier κ M) :=
  ⟨scaledUpperBarrier_continuous κ M, scaledUpperBarrier_isBddFun hM⟩

/-- The finite-time trapping set `\tilde E_{κ,M,T}` from Paper1 Remark 4.2. -/
def InTimeWaveTrapSet
    (κ M T : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
    IsCUnifBdd (u t) ∧
      ∀ x : ℝ, 0 ≤ u t x ∧ u t x ≤ scaledUpperBarrier κ M x

theorem InTimeWaveTrapSet.slice_cunif
    {κ M T : ℝ} {u : ℝ → ℝ → ℝ}
    (h : InTimeWaveTrapSet κ M T u)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IsCUnifBdd (u t) :=
  (h t ht).1

theorem InTimeWaveTrapSet.nonneg
    {κ M T : ℝ} {u : ℝ → ℝ → ℝ}
    (h : InTimeWaveTrapSet κ M T u)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (x : ℝ) :
    0 ≤ u t x :=
  ((h t ht).2 x).1

theorem InTimeWaveTrapSet.le_scaledUpperBarrier
    {κ M T : ℝ} {u : ℝ → ℝ → ℝ}
    (h : InTimeWaveTrapSet κ M T u)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (x : ℝ) :
    u t x ≤ scaledUpperBarrier κ M x :=
  ((h t ht).2 x).2

theorem scaledUpperBarrier_one_eq_upperBarrier (κ : ℝ) :
    scaledUpperBarrier κ 1 = upperBarrier κ 1 := by
  ext x
  simp [scaledUpperBarrier, upperBarrier]

theorem InTimeWaveTrapSet.slice_inWaveTrapSet_one
    {κ T : ℝ} {u : ℝ → ℝ → ℝ}
    (h : InTimeWaveTrapSet κ 1 T u)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    InWaveTrapSet κ 1 (u t) := by
  refine ⟨h.slice_cunif ht, ?_⟩
  intro x
  refine ⟨h.nonneg ht x, ?_⟩
  simpa [scaledUpperBarrier_one_eq_upperBarrier κ] using
    h.le_scaledUpperBarrier ht x

/-- Paper1 Remark 4.2: the lower and constant subsolution construction also
works for finite-time frozen coefficient paths in `\tilde E_{κ,M,T}`. -/
def Remark_4_2 : Prop :=
  ∀ p : CMParams, ∀ κ κtilde M c T : ℝ,
    0 < κ → κ < 1 →
      κ < κtilde →
      κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1) →
      1 ≤ M → 0 < T → c = κ + κ⁻¹ →
        ∃ D0 : ℝ, ∀ D : ℝ, D0 < D →
          ∀ u : ℝ → ℝ → ℝ, InTimeWaveTrapSet κ M T u →
            (∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
              IsFrozenSubSolutionOn p c (u t) (lowerBarrierRaw κ κtilde D)
                (Set.Ioi (lowerBarrierXMinus κ κtilde D))) ∧
            ∀ d : ℝ, 0 < d →
              d ≤ constantSubsolutionThreshold p.χ κ κtilde D →
                ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
                  IsFrozenSubSolutionOn p c (u t) (fun _ => d) Set.univ

theorem Remark_4_2.exists_time_slice_subsolutions
    (h : Remark_4_2) {p : CMParams} {κ κtilde M c T : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hgap : κ < κtilde)
    (hrange : κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1))
    (hM : 1 ≤ M) (hT : 0 < T) (hc : c = κ + κ⁻¹) :
    ∃ D0 : ℝ, ∀ D : ℝ, D0 < D →
      ∀ u : ℝ → ℝ → ℝ, InTimeWaveTrapSet κ M T u →
        (∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
          IsFrozenSubSolutionOn p c (u t) (lowerBarrierRaw κ κtilde D)
            (Set.Ioi (lowerBarrierXMinus κ κtilde D))) ∧
        ∀ d : ℝ, 0 < d →
          d ≤ constantSubsolutionThreshold p.χ κ κtilde D →
            ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
              IsFrozenSubSolutionOn p c (u t) (fun _ => d) Set.univ :=
  h p κ κtilde M c T hκ0 hκ1 hgap hrange hM hT hc

def MChi (p : CMParams) : ℝ :=
  if p.χ ≤ 0 then 1 else (1 / (1 - p.χ)) ^ (1 / p.α)

theorem MChi_eq_one_of_chi_nonpos (p : CMParams) (hχ : p.χ ≤ 0) :
    MChi p = 1 := by
  simp [MChi, hχ]

theorem MChi_eq_rpow_of_chi_pos (p : CMParams) (hχ : 0 < p.χ) :
    MChi p = (1 / (1 - p.χ)) ^ (1 / p.α) := by
  simp [MChi, not_le.mpr hχ]

theorem MChi_eq_rpow_of_chi_nonneg_lt_one
    (p : CMParams) (hχ_nonneg : 0 ≤ p.χ) (_hχ_lt : p.χ < 1) :
    MChi p = (1 / (1 - p.χ)) ^ (1 / p.α) := by
  by_cases hχ_zero : p.χ = 0
  · have hχ_nonpos : p.χ ≤ 0 := by linarith
    simp [MChi_eq_one_of_chi_nonpos p hχ_nonpos, hχ_zero]
  · exact
      MChi_eq_rpow_of_chi_pos p
        (lt_of_le_of_ne hχ_nonneg (Ne.symm hχ_zero))

theorem MChi_pos_of_chi_lt_one (p : CMParams) (hχ : p.χ < 1) :
    0 < MChi p := by
  by_cases hχ_nonpos : p.χ ≤ 0
  · simp [MChi, hχ_nonpos]
  · have hχ_pos : 0 < p.χ := lt_of_not_ge hχ_nonpos
    have hden_pos : 0 < 1 - p.χ := by linarith
    rw [MChi_eq_rpow_of_chi_pos p hχ_pos]
    exact Real.rpow_pos_of_pos (div_pos one_pos hden_pos) _

theorem one_le_MChi_of_chi_nonneg_lt_one
    (p : CMParams) (hχ_nonneg : 0 ≤ p.χ) (hχ_lt : p.χ < 1) :
    1 ≤ MChi p := by
  by_cases hχ_zero : p.χ = 0
  · have hχ_nonpos : p.χ ≤ 0 := by linarith
    simp [MChi_eq_one_of_chi_nonpos p hχ_nonpos]
  · have hχ_pos : 0 < p.χ := lt_of_le_of_ne hχ_nonneg (Ne.symm hχ_zero)
    have hden_pos : 0 < 1 - p.χ := by linarith
    have hbase : 1 ≤ 1 / (1 - p.χ) := by
      rw [le_div_iff₀ hden_pos]
      linarith
    have hα_pos : 0 < p.α := lt_of_lt_of_le one_pos p.hα
    have hexp_nonneg : 0 ≤ 1 / p.α := by positivity
    rw [MChi_eq_rpow_of_chi_pos p hχ_pos]
    exact Real.one_le_rpow hbase hexp_nonneg

theorem MChi_pos_of_chi_lt_chiStar (p : CMParams) (hχ : p.χ < chiStar p) :
    0 < MChi p :=
  MChi_pos_of_chi_lt_one p (lt_of_lt_of_le hχ (chiStar_le_one p))

theorem MChi_nonneg_of_chi_lt_one (p : CMParams) (hχ : p.χ < 1) :
    0 ≤ MChi p :=
  (MChi_pos_of_chi_lt_one p hχ).le

theorem MChi_rpow_pos_of_chi_lt_one (p : CMParams) (hχ : p.χ < 1) (a : ℝ) :
    0 < (MChi p) ^ a :=
  Real.rpow_pos_of_pos (MChi_pos_of_chi_lt_one p hχ) a

theorem MChi_gamma_pos_of_chi_lt_one (p : CMParams) (hχ : p.χ < 1) :
    0 < (MChi p) ^ p.γ :=
  MChi_rpow_pos_of_chi_lt_one p hχ p.γ

/-- Section 4.2 fixed-point construction for negative sensitivity, before the
final conversion of the fixed point into a traveling wave. -/
def NegativeSensitivityWaveFixedPointConstruction
    (p : CMParams) (c κ₁ κtilde D : ℝ) : Prop :=
  p.χ < 0 ∧
    p.α ≤ p.m + p.γ - 1 ∧
    cStarLower p < c ∧
    kappa c < κ₁ ∧
    κ₁ < κtilde ∧
    κtilde ≤
      min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) ∧
    subsolutionDThreshold p.χ 1 (kappa c) κtilde p.m p.γ c < D ∧
    FrozenWaveMapConstruction p c (kappa c) 1
      (fun u => InMonotoneWaveTrapSet (kappa c) 1 u)

/-- Section 4.3 fixed-point construction for positive sensitivity, before the
final conversion of the fixed point into a traveling wave. -/
def PositiveSensitivityWaveFixedPointConstruction
    (p : CMParams) (c κ₁ κtilde D : ℝ) : Prop :=
  0 ≤ p.χ ∧
    p.χ < min (1 / 2 : ℝ) (chiStar p) ∧
    p.α = p.m + p.γ - 1 ∧
    2 < c ∧
    kappa c < κ₁ ∧
    κ₁ < κtilde ∧
    κtilde ≤
      min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) ∧
    subsolutionDThreshold p.χ (MChi p) (kappa c) κtilde p.m p.γ c < D ∧
    FrozenWaveMapConstruction p c (kappa c) (MChi p)
      (fun u => InWaveTrapSet (kappa c) (MChi p) u)

theorem NegativeSensitivityWaveFixedPointConstruction.chi_neg
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    p.χ < 0 :=
  h.1

theorem NegativeSensitivityWaveFixedPointConstruction.alpha_le
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    p.α ≤ p.m + p.γ - 1 :=
  h.2.1

theorem NegativeSensitivityWaveFixedPointConstruction.cStarLower_lt
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    cStarLower p < c :=
  h.2.2.1

theorem NegativeSensitivityWaveFixedPointConstruction.two_lt_c
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    2 < c :=
  two_lt_of_cStarLower_lt h.cStarLower_lt

theorem NegativeSensitivityWaveFixedPointConstruction.c_pos
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    0 < c :=
  lt_trans (by norm_num : (0 : ℝ) < 2) h.two_lt_c

theorem NegativeSensitivityWaveFixedPointConstruction.kappa_lt_kappaOne
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    kappa c < κ₁ :=
  h.2.2.2.1

theorem NegativeSensitivityWaveFixedPointConstruction.kappaOne_lt_kappaTilde
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    κ₁ < κtilde :=
  h.2.2.2.2.1

theorem NegativeSensitivityWaveFixedPointConstruction.kappaTilde_range
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    κtilde ≤
      min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) :=
  h.2.2.2.2.2.1

theorem NegativeSensitivityWaveFixedPointConstruction.D_gt_threshold
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    subsolutionDThreshold p.χ 1 (kappa c) κtilde p.m p.γ c < D :=
  h.2.2.2.2.2.2.1

theorem NegativeSensitivityWaveFixedPointConstruction.map_construction
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    FrozenWaveMapConstruction p c (kappa c) 1
      (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) :=
  h.2.2.2.2.2.2.2

theorem NegativeSensitivityWaveFixedPointConstruction.kappa_pos
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    0 < kappa c :=
  kappa_pos_of_cStarLower_lt h.cStarLower_lt

theorem NegativeSensitivityWaveFixedPointConstruction.kappa_lt_one
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    kappa c < 1 :=
  kappa_lt_one_of_cStarLower_lt h.cStarLower_lt

theorem NegativeSensitivityWaveFixedPointConstruction.kappa_add_inv_eq
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    kappa c + (kappa c)⁻¹ = c :=
  kappa_add_inv_eq_of_cStarLower_lt h.cStarLower_lt

theorem NegativeSensitivityWaveFixedPointConstruction.kappa_lt_kappaTilde
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    kappa c < κtilde :=
  lt_trans h.kappa_lt_kappaOne h.kappaOne_lt_kappaTilde

theorem NegativeSensitivityWaveFixedPointConstruction.kappaTilde_pos
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    0 < κtilde :=
  kappaTilde_pos_of_kappa_lt h.kappa_pos h.kappa_lt_kappaTilde

theorem NegativeSensitivityWaveFixedPointConstruction.kappaTilde_le_one
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    κtilde ≤ 1 :=
  kappaTilde_le_one_of_subsolution_range h.kappaTilde_range

theorem NegativeSensitivityWaveFixedPointConstruction.kappaTilde_le_one_plus_alpha_mul_kappa
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    κtilde ≤ (1 + p.α) * kappa c :=
  kappaTilde_le_one_plus_alpha_mul_kappa_of_subsolution_range
    h.kappaTilde_range

theorem NegativeSensitivityWaveFixedPointConstruction.kappaTilde_le_m_mul_kappa_add_half
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    κtilde ≤ p.m * kappa c + 1 / 2 :=
  kappaTilde_le_m_mul_kappa_add_half_of_subsolution_range
    h.kappaTilde_range

theorem NegativeSensitivityWaveFixedPointConstruction.D_pos
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    0 < D :=
  D_pos_of_subsolutionDThreshold_lt_of_cStarLower_lt
    one_pos h.cStarLower_lt h.kappa_lt_kappaTilde h.kappaTilde_le_one
    h.D_gt_threshold

theorem NegativeSensitivityWaveFixedPointConstruction.exists_constant_subsolution
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    ∃ d : ℝ, 0 < d ∧
      d ≤ constantSubsolutionThreshold p.χ (kappa c) κtilde D :=
  exists_d_pos_le_constantSubsolutionThreshold_of_cStarLower_lt
    one_pos h.cStarLower_lt h.kappa_lt_kappaTilde h.kappaTilde_le_one
    h.D_gt_threshold

theorem NegativeSensitivityWaveFixedPointConstruction.MChi_eq_one
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    MChi p = 1 :=
  MChi_eq_one_of_chi_nonpos p (le_of_lt h.chi_neg)

theorem Lemma_4_1.negative_superSolution_of_fixedPointConstruction
    (hL : Lemma_4_1) {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D)
    {u : ℝ → ℝ} (hu : InMonotoneWaveTrapSet (kappa c) 1 u) :
    IsFrozenSuperSolution p c u (upperBarrier (kappa c) 1) :=
  hL.negative_superSolution (le_of_lt h.chi_neg) h.alpha_le
    h.kappa_pos h.kappa_lt_one le_rfl h.kappa_add_inv_eq.symm hu.trap

theorem Lemma_4_2.subsolutions_of_negative_fixedPointConstruction
    (hL : Lemma_4_2) {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D)
    {u : ℝ → ℝ} (hu : InMonotoneWaveTrapSet (kappa c) 1 u) :
    IsFrozenSubSolutionOn p c u (lowerBarrierRaw (kappa c) κtilde D)
        (Set.Ioi (lowerBarrierXMinus (kappa c) κtilde D)) ∧
      ∀ d : ℝ,
        0 < d →
          d ≤ constantSubsolutionThreshold p.χ (kappa c) κtilde D →
            IsFrozenSubSolutionOn p c u (fun _ => d) Set.univ :=
  hL.subsolutions h.kappa_pos h.kappa_lt_one h.kappa_lt_kappaTilde
    h.kappaTilde_range le_rfl h.kappa_add_inv_eq.symm
    h.D_gt_threshold hu.trap

theorem PositiveSensitivityWaveFixedPointConstruction.chi_nonneg
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    0 ≤ p.χ :=
  h.1

theorem PositiveSensitivityWaveFixedPointConstruction.chi_lt_min
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    p.χ < min (1 / 2 : ℝ) (chiStar p) :=
  h.2.1

theorem PositiveSensitivityWaveFixedPointConstruction.chi_lt_chiStar
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    p.χ < chiStar p :=
  lt_of_lt_of_le h.chi_lt_min (min_le_right _ _)

theorem PositiveSensitivityWaveFixedPointConstruction.alpha_eq
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    p.α = p.m + p.γ - 1 :=
  h.2.2.1

theorem PositiveSensitivityWaveFixedPointConstruction.two_lt_c
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    2 < c :=
  h.2.2.2.1

theorem PositiveSensitivityWaveFixedPointConstruction.c_pos
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    0 < c :=
  lt_trans (by norm_num : (0 : ℝ) < 2) h.two_lt_c

theorem PositiveSensitivityWaveFixedPointConstruction.kappa_lt_kappaOne
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    kappa c < κ₁ :=
  h.2.2.2.2.1

theorem PositiveSensitivityWaveFixedPointConstruction.kappaOne_lt_kappaTilde
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    κ₁ < κtilde :=
  h.2.2.2.2.2.1

theorem PositiveSensitivityWaveFixedPointConstruction.kappaTilde_range
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    κtilde ≤
      min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) :=
  h.2.2.2.2.2.2.1

theorem PositiveSensitivityWaveFixedPointConstruction.D_gt_threshold
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    subsolutionDThreshold p.χ (MChi p) (kappa c) κtilde p.m p.γ c < D :=
  h.2.2.2.2.2.2.2.1

theorem PositiveSensitivityWaveFixedPointConstruction.map_construction
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    FrozenWaveMapConstruction p c (kappa c) (MChi p)
      (fun u => InWaveTrapSet (kappa c) (MChi p) u) :=
  h.2.2.2.2.2.2.2.2

theorem PositiveSensitivityWaveFixedPointConstruction.kappa_pos
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    0 < kappa c :=
  kappa_pos_of_two_lt h.two_lt_c

theorem PositiveSensitivityWaveFixedPointConstruction.kappa_lt_one
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    kappa c < 1 :=
  kappa_lt_one_of_two_lt h.two_lt_c

theorem PositiveSensitivityWaveFixedPointConstruction.kappa_add_inv_eq
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    kappa c + (kappa c)⁻¹ = c :=
  kappa_add_inv_eq_of_two_lt h.two_lt_c

theorem PositiveSensitivityWaveFixedPointConstruction.kappa_lt_kappaTilde
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    kappa c < κtilde :=
  lt_trans h.kappa_lt_kappaOne h.kappaOne_lt_kappaTilde

theorem PositiveSensitivityWaveFixedPointConstruction.kappaTilde_pos
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    0 < κtilde :=
  kappaTilde_pos_of_kappa_lt h.kappa_pos h.kappa_lt_kappaTilde

theorem PositiveSensitivityWaveFixedPointConstruction.kappaTilde_le_one
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    κtilde ≤ 1 :=
  kappaTilde_le_one_of_subsolution_range h.kappaTilde_range

theorem PositiveSensitivityWaveFixedPointConstruction.kappaTilde_le_one_plus_alpha_mul_kappa
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    κtilde ≤ (1 + p.α) * kappa c :=
  kappaTilde_le_one_plus_alpha_mul_kappa_of_subsolution_range
    h.kappaTilde_range

theorem PositiveSensitivityWaveFixedPointConstruction.kappaTilde_le_m_mul_kappa_add_half
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    κtilde ≤ p.m * kappa c + 1 / 2 :=
  kappaTilde_le_m_mul_kappa_add_half_of_subsolution_range
    h.kappaTilde_range

theorem PositiveSensitivityWaveFixedPointConstruction.MChi_pos
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    0 < MChi p :=
  MChi_pos_of_chi_lt_chiStar p h.chi_lt_chiStar

theorem PositiveSensitivityWaveFixedPointConstruction.D_pos
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    0 < D :=
  D_pos_of_subsolutionDThreshold_lt_of_kappa_speed h.MChi_pos
    h.kappa_pos h.kappa_lt_one h.kappa_lt_kappaTilde h.kappaTilde_le_one
    (lt_of_lt_of_le one_pos p.hm)
    (lt_of_lt_of_le one_pos p.hγ)
    (kappa_add_inv_eq_of_two_lt h.two_lt_c).symm
    h.D_gt_threshold

theorem PositiveSensitivityWaveFixedPointConstruction.exists_constant_subsolution
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    ∃ d : ℝ, 0 < d ∧
      d ≤ constantSubsolutionThreshold p.χ (kappa c) κtilde D :=
  exists_d_pos_le_constantSubsolutionThreshold h.kappa_pos
    h.kappa_lt_kappaTilde h.D_pos

theorem PositiveSensitivityWaveFixedPointConstruction.one_le_MChi
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    1 ≤ MChi p :=
  one_le_MChi_of_chi_nonneg_lt_one p h.chi_nonneg
    (lt_of_lt_of_le h.chi_lt_chiStar (chiStar_le_one p))

theorem Lemma_4_1.positive_superSolution_of_fixedPointConstruction
    (hL : Lemma_4_1) {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D)
    {u : ℝ → ℝ} (hu : InWaveTrapSet (kappa c) (MChi p) u) :
    IsFrozenSuperSolution p c u (upperBarrier (kappa c) (MChi p)) := by
  have hχ_lt_one : p.χ < 1 :=
    lt_of_lt_of_le h.chi_lt_chiStar (chiStar_le_one p)
  have hMchi :
      (1 / (1 - p.χ)) ^ (1 / p.α) ≤ MChi p :=
    le_of_eq (MChi_eq_rpow_of_chi_nonneg_lt_one p h.chi_nonneg hχ_lt_one).symm
  exact hL.positive_superSolution h.chi_nonneg h.chi_lt_chiStar h.alpha_eq
    h.kappa_pos h.kappa_lt_one h.one_le_MChi hMchi
    h.kappa_add_inv_eq.symm hu

theorem Lemma_4_2.subsolutions_of_positive_fixedPointConstruction
    (hL : Lemma_4_2) {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D)
    {u : ℝ → ℝ} (hu : InWaveTrapSet (kappa c) (MChi p) u) :
    IsFrozenSubSolutionOn p c u (lowerBarrierRaw (kappa c) κtilde D)
        (Set.Ioi (lowerBarrierXMinus (kappa c) κtilde D)) ∧
      ∀ d : ℝ,
        0 < d →
          d ≤ constantSubsolutionThreshold p.χ (kappa c) κtilde D →
            IsFrozenSubSolutionOn p c u (fun _ => d) Set.univ :=
  hL.subsolutions h.kappa_pos h.kappa_lt_one h.kappa_lt_kappaTilde
    h.kappaTilde_range h.one_le_MChi h.kappa_add_inv_eq.symm
    h.D_gt_threshold hu

theorem NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet (kappa c) 1 U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) 1
          (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U := by
  exact FrozenWaveMapConstruction.exists_fixed_limit h.map_construction

theorem NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_bounds
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet (kappa c) 1 U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) 1
          (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U ∧
        Antitone U ∧
        (∀ x, 0 ≤ U x) ∧
        (∀ x, U x ≤ 1) ∧
        ∀ x, U x ≤ Real.exp (-(kappa c) * x) := by
  exact h.map_construction.exists_fixed_inMonotoneWaveTrapSet_with_bounds

theorem NegativeSensitivityWaveFixedPointConstruction.exists_limit_map
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    ∃ Tmap : (ℝ → ℝ) → ℝ → ℝ,
      (∀ u, InMonotoneWaveTrapSet (kappa c) 1 u →
        InMonotoneWaveTrapSet (kappa c) 1 (Tmap u)) ∧
        ∀ u, InMonotoneWaveTrapSet (kappa c) 1 u →
          FrozenAuxiliaryLimitOutput p c (kappa c) 1
            (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) u (Tmap u) :=
  h.map_construction.exists_map_self

theorem PositiveSensitivityWaveFixedPointConstruction.exists_fixed_limit
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    ∃ U : ℝ → ℝ,
      InWaveTrapSet (kappa c) (MChi p) U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) (MChi p)
          (fun u => InWaveTrapSet (kappa c) (MChi p) u) U U := by
  exact FrozenWaveMapConstruction.exists_fixed_limit h.map_construction

theorem PositiveSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_bounds
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    ∃ U : ℝ → ℝ,
      InWaveTrapSet (kappa c) (MChi p) U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) (MChi p)
          (fun u => InWaveTrapSet (kappa c) (MChi p) u) U U ∧
        (∀ x, 0 ≤ U x) ∧
        (∀ x, U x ≤ MChi p) ∧
        ∀ x, U x ≤ Real.exp (-(kappa c) * x) := by
  exact h.map_construction.exists_fixed_inWaveTrapSet_with_bounds

theorem PositiveSensitivityWaveFixedPointConstruction.exists_limit_map
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    ∃ Tmap : (ℝ → ℝ) → ℝ → ℝ,
      (∀ u, InWaveTrapSet (kappa c) (MChi p) u →
        InWaveTrapSet (kappa c) (MChi p) (Tmap u)) ∧
        ∀ u, InWaveTrapSet (kappa c) (MChi p) u →
          FrozenAuxiliaryLimitOutput p c (kappa c) (MChi p)
            (fun u => InWaveTrapSet (kappa c) (MChi p) u) u (Tmap u) :=
  h.map_construction.exists_map_self

theorem one_le_MChi_of_chi_nonneg_lt_chiStar
    (p : CMParams) (hχ_nonneg : 0 ≤ p.χ) (hχ : p.χ < chiStar p) :
    1 ≤ MChi p :=
  one_le_MChi_of_chi_nonneg_lt_one p hχ_nonneg
    (lt_of_lt_of_le hχ (chiStar_le_one p))

def HasWaveUpperTailBound (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ x, 0 < U x ∧ U x ≤ min (MChi p) (Real.exp (-(kappa c) * x))

def HasStrictWaveUpperTailBound (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ x, 0 < U x ∧ U x < min (MChi p) (Real.exp (-(kappa c) * x))

theorem InWaveTrapSet.hasWaveUpperTailBound_of_pos
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (htrap : InWaveTrapSet (kappa c) (MChi p) U)
    (hpos : ∀ x, 0 < U x) :
    HasWaveUpperTailBound p c U := by
  intro x
  exact ⟨hpos x, by simpa [upperBarrier] using htrap.le_upperBarrier x⟩

theorem InMonotoneWaveTrapSet.hasWaveUpperTailBound_of_pos
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hpos : ∀ x, 0 < U x) :
    HasWaveUpperTailBound p c U :=
  htrap.trap.hasWaveUpperTailBound_of_pos hpos

theorem FrozenStationaryWaveProfile.hasWaveUpperTailBound_of_inWaveTrapSet
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hprofile : FrozenStationaryWaveProfile p c U)
    (htrap : InWaveTrapSet (kappa c) (MChi p) U) :
    HasWaveUpperTailBound p c U :=
  htrap.hasWaveUpperTailBound_of_pos hprofile.U_pos

theorem FrozenStationaryWaveProfile.hasWaveUpperTailBound_of_inMonotoneWaveTrapSet
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hprofile : FrozenStationaryWaveProfile p c U)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U) :
    HasWaveUpperTailBound p c U :=
  htrap.hasWaveUpperTailBound_of_pos hprofile.U_pos

theorem HasStrictWaveUpperTailBound.hasWaveUpperTailBound
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasStrictWaveUpperTailBound p c U) :
    HasWaveUpperTailBound p c U := by
  intro x
  exact ⟨(h x).1, (h x).2.le⟩

theorem HasStrictWaveUpperTailBound.pos
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasStrictWaveUpperTailBound p c U) (x : ℝ) :
    0 < U x :=
  (h x).1

theorem HasStrictWaveUpperTailBound.lt_MChi
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasStrictWaveUpperTailBound p c U) (x : ℝ) :
    U x < MChi p :=
  lt_of_lt_of_le (h x).2 (min_le_left _ _)

theorem HasStrictWaveUpperTailBound.lt_exp
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasStrictWaveUpperTailBound p c U) (x : ℝ) :
    U x < Real.exp (-(kappa c) * x) :=
  lt_of_lt_of_le (h x).2 (min_le_right _ _)

theorem HasWaveUpperTailBound.pos {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (x : ℝ) :
    0 < U x :=
  (h x).1

theorem HasWaveUpperTailBound.le_MChi {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (x : ℝ) :
    U x ≤ MChi p :=
  le_trans (h x).2 (min_le_left _ _)

theorem HasWaveUpperTailBound.le_exp {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (x : ℝ) :
    U x ≤ Real.exp (-(kappa c) * x) :=
  le_trans (h x).2 (min_le_right _ _)

theorem HasStrictWaveUpperTailBound.shift_right
    {p : CMParams} {c a : ℝ} {U : ℝ → ℝ}
    (h : HasStrictWaveUpperTailBound p c U)
    (hk : 0 ≤ kappa c) (ha : 0 ≤ a) :
    HasStrictWaveUpperTailBound p c (fun x => U (x + a)) := by
  intro x
  refine ⟨h.pos (x + a), ?_⟩
  apply lt_min
  · exact h.lt_MChi (x + a)
  · have hle_exp :
        Real.exp (-(kappa c) * (x + a)) ≤ Real.exp (-(kappa c) * x) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hk ha]
    exact (h.lt_exp (x + a)).trans_le hle_exp

theorem HasStrictWaveUpperTailBound.shift_right_of_two_lt
    {p : CMParams} {c a : ℝ} {U : ℝ → ℝ}
    (h : HasStrictWaveUpperTailBound p c U) (hc : 2 < c) (ha : 0 ≤ a) :
    HasStrictWaveUpperTailBound p c (fun x => U (x + a)) :=
  h.shift_right (kappa_pos_of_two_lt hc).le ha

theorem HasWaveUpperTailBound.shift_right
    {p : CMParams} {c a : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U)
    (hk : 0 ≤ kappa c) (ha : 0 ≤ a) :
    HasWaveUpperTailBound p c (fun x => U (x + a)) := by
  intro x
  refine ⟨h.pos (x + a), ?_⟩
  apply le_min
  · exact h.le_MChi (x + a)
  · have hle_exp :
        Real.exp (-(kappa c) * (x + a)) ≤ Real.exp (-(kappa c) * x) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hk ha]
    exact (h.le_exp (x + a)).trans hle_exp

theorem HasWaveUpperTailBound.shift_right_of_two_lt
    {p : CMParams} {c a : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (hc : 2 < c) (ha : 0 ≤ a) :
    HasWaveUpperTailBound p c (fun x => U (x + a)) :=
  h.shift_right (kappa_pos_of_two_lt hc).le ha

theorem HasWaveUpperTailBound.inWaveTrapSet
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (hU : IsCUnifBdd U) :
    InWaveTrapSet (kappa c) (MChi p) U := by
  refine ⟨hU, ?_⟩
  intro x
  exact ⟨(h.pos x).le, by simpa [upperBarrier] using (h x).2⟩

theorem HasWaveUpperTailBound.inMonotoneWaveTrapSet
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (hU : IsCUnifBdd U)
    (hmono : NonincreasingProfile U) :
    InMonotoneWaveTrapSet (kappa c) (MChi p) U :=
  ⟨h.inWaveTrapSet hU, hmono⟩

theorem HasWaveUpperTailBound.rpow_le_MChi
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ} {a : ℝ}
    (h : HasWaveUpperTailBound p c U) (ha : 0 ≤ a) (x : ℝ) :
    (U x) ^ a ≤ (MChi p) ^ a :=
  Real.rpow_le_rpow (h.pos x).le (h.le_MChi x) ha

theorem HasWaveUpperTailBound.rpow_le_exp
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ} {a : ℝ}
    (h : HasWaveUpperTailBound p c U) (ha : 0 ≤ a) (x : ℝ) :
    (U x) ^ a ≤ (Real.exp (-(kappa c) * x)) ^ a :=
  Real.rpow_le_rpow (h.pos x).le (h.le_exp x) ha

theorem HasWaveUpperTailBound.rpow_le_exp_mul
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ} {a : ℝ}
    (h : HasWaveUpperTailBound p c U) (ha : 0 ≤ a) (x : ℝ) :
    (U x) ^ a ≤ Real.exp (-(kappa c) * a * x) := by
  calc
    (U x) ^ a ≤ (Real.exp (-(kappa c) * x)) ^ a := h.rpow_le_exp ha x
    _ = Real.exp (-(kappa c) * a * x) := by
      rw [← Real.exp_mul]
      congr 1
      ring

theorem HasWaveUpperTailBound.rpow_le_MChi_gamma
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (x : ℝ) :
    (U x) ^ p.γ ≤ (MChi p) ^ p.γ :=
  h.rpow_le_MChi (le_trans zero_le_one p.hγ) x

theorem HasWaveUpperTailBound.rpow_le_exp_gamma
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (x : ℝ) :
    (U x) ^ p.γ ≤ (Real.exp (-(kappa c) * x)) ^ p.γ :=
  h.rpow_le_exp (le_trans zero_le_one p.hγ) x

theorem HasWaveUpperTailBound.rpow_abs_le_MChi_gamma
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (x : ℝ) :
    |(U x) ^ p.γ| ≤ (MChi p) ^ p.γ := by
  rw [abs_of_nonneg (Real.rpow_nonneg (h.pos x).le _)]
  exact h.rpow_le_MChi_gamma x

theorem ShenUpperBoundPositive.hasStrictWaveUpperTailBound
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : ShenUpperBoundPositive p c U)
    (hχ_nonneg : 0 ≤ p.χ) (hχ_lt : p.χ < 1) :
    HasStrictWaveUpperTailBound p c U := by
  intro x
  refine ⟨(h x).1, ?_⟩
  rw [MChi_eq_rpow_of_chi_nonneg_lt_one p hχ_nonneg hχ_lt]
  exact (h x).2

theorem ShenUpperBoundPositive.hasWaveUpperTailBound
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hχ_nonneg : 0 ≤ p.χ) (hχ_lt : p.χ < 1)
    (h : ShenUpperBoundPositive p c U) :
    HasWaveUpperTailBound p c U :=
  (h.hasStrictWaveUpperTailBound hχ_nonneg hχ_lt).hasWaveUpperTailBound

theorem ShenUpperBoundPositive.inWaveTrapSet
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hχ_nonneg : 0 ≤ p.χ) (hχ_lt : p.χ < 1)
    (h : ShenUpperBoundPositive p c U) (hU : IsCUnifBdd U) :
    InWaveTrapSet (kappa c) (MChi p) U :=
  (ShenUpperBoundPositive.hasWaveUpperTailBound hχ_nonneg hχ_lt h).inWaveTrapSet hU

/-- The admissible extra right-tail decay rate in Paper1 Remark 4.3:
`0 < η < min {ακ, (m-1)κ+1/2, 1-κ}`. -/
def Remark43TailRateBound (p : CMParams) (c eta : ℝ) : Prop :=
  0 < eta ∧
    eta <
      min (p.α * kappa c)
        (min ((p.m - 1) * kappa c + 1 / 2) (1 - kappa c))

/-- The pointwise right-tail normalization recorded in Paper1 Remark 4.3. -/
def HasRemark43TailAsymptotic
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ eta : ℝ, Remark43TailRateBound p c eta →
    Tendsto
      (fun x => Real.exp (eta * x) *
        (U x / Real.exp (-(kappa c) * x) - 1))
      atTop (𝓝 0)

/-- Paper1 Remark 4.3: the construction gives the sharper right-tail
normalization, and two waves with that normalization are close in the weighted
space used by the stability theorem. -/
def Remark_4_3 : Prop :=
  ∀ p : CMParams, ∀ c : ℝ, 0 < kappa c →
    ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
      IsTravelingWave p c U₁ V₁ →
      IsTravelingWave p c U₂ V₂ →
      HasWaveUpperTailBound p c U₁ →
      HasWaveUpperTailBound p c U₂ →
      HasRemark43TailAsymptotic p c U₁ →
      HasRemark43TailAsymptotic p c U₂ →
      ∀ eta : ℝ, Remark43TailRateBound p c eta →
        WeightedL2InitialCloseness (eta + kappa c) U₂ U₁

/-- Paper1 Remark 1.3(2), repeated in Remark 4.3(2): in the extended
positive-sensitivity range, the construction yields a wave whose right end is
`(0,0)` and whose left end stays uniformly positive, without claiming
convergence to `(1,1)`. -/
def Remark_1_3_2 : Prop :=
  ∀ p : CMParams,
    p.α = p.m + p.γ - 1 →
    (1 / 2 : ℝ) < positiveSensitivityExtendedThreshold p →
    (1 / 2 : ℝ) ≤ p.χ →
    p.χ < min (positiveSensitivityExtendedThreshold p) 1 →
      ∀ c : ℝ, 2 < c →
        ∃ U V : ℝ → ℝ, IsRightVanishingTravelingWave p c U V

/-- Paper1 Remark 4.3(2) invokes the same extended positive-sensitivity
right-vanishing wave conclusion as Remark 1.3(2). -/
def Remark_4_3_part2 : Prop := Remark_1_3_2

theorem Remark_1_3_2.rightVanishingWave
    (h : Remark_1_3_2) {p : CMParams}
    (halpha : p.α = p.m + p.γ - 1)
    (hthreshold : (1 / 2 : ℝ) < positiveSensitivityExtendedThreshold p)
    (hχ_half : (1 / 2 : ℝ) ≤ p.χ)
    (hχ_small : p.χ < min (positiveSensitivityExtendedThreshold p) 1)
    {c : ℝ} (hc : 2 < c) :
    ∃ U V : ℝ → ℝ, IsRightVanishingTravelingWave p c U V :=
  h p halpha hthreshold hχ_half hχ_small c hc

theorem Remark_4_3_part2.rightVanishingWave
    (h : Remark_4_3_part2) {p : CMParams}
    (halpha : p.α = p.m + p.γ - 1)
    (hthreshold : (1 / 2 : ℝ) < positiveSensitivityExtendedThreshold p)
    (hχ_half : (1 / 2 : ℝ) ≤ p.χ)
    (hχ_small : p.χ < min (positiveSensitivityExtendedThreshold p) 1)
    {c : ℝ} (hc : 2 < c) :
    ∃ U V : ℝ → ℝ, IsRightVanishingTravelingWave p c U V :=
  Remark_1_3_2.rightVanishingWave h halpha hthreshold hχ_half hχ_small hc

theorem Remark43TailRateBound.pos
    {p : CMParams} {c eta : ℝ} (h : Remark43TailRateBound p c eta) :
    0 < eta :=
  h.1

theorem Remark43TailRateBound.lt_alpha_kappa
    {p : CMParams} {c eta : ℝ} (h : Remark43TailRateBound p c eta) :
    eta < p.α * kappa c :=
  lt_of_lt_of_le h.2 (min_le_left _ _)

theorem Remark43TailRateBound.lt_m_kappa_add_half
    {p : CMParams} {c eta : ℝ} (h : Remark43TailRateBound p c eta) :
    eta < (p.m - 1) * kappa c + 1 / 2 :=
  lt_of_lt_of_le h.2 (le_trans (min_le_right _ _) (min_le_left _ _))

theorem Remark43TailRateBound.lt_one_sub_kappa
    {p : CMParams} {c eta : ℝ} (h : Remark43TailRateBound p c eta) :
    eta < 1 - kappa c :=
  lt_of_lt_of_le h.2 (le_trans (min_le_right _ _) (min_le_right _ _))

theorem Remark43TailRateBound.weight_pos
    {p : CMParams} {c eta : ℝ} (h : Remark43TailRateBound p c eta)
    (hkappa : 0 < kappa c) :
    0 < eta + kappa c := by
  linarith [h.pos, hkappa]

theorem Remark43TailRateBound.of_kappaOne_range
    {p : CMParams} {c κ₁ : ℝ}
    (hκ₁ : kappa c < κ₁)
    (hrange :
      κ₁ <
        min ((1 + p.α) * kappa c)
          (min (p.m * kappa c + 1 / 2) 1)) :
    Remark43TailRateBound p c (κ₁ - kappa c) := by
  refine ⟨by linarith, ?_⟩
  have hα :
      κ₁ < (1 + p.α) * kappa c :=
    lt_of_lt_of_le hrange (min_le_left _ _)
  have hm :
      κ₁ < p.m * kappa c + 1 / 2 :=
    lt_of_lt_of_le hrange
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have hone : κ₁ < 1 :=
    lt_of_lt_of_le hrange
      (le_trans (min_le_right _ _) (min_le_right _ _))
  apply lt_min
  · nlinarith
  · apply lt_min
    · nlinarith
    · linarith

theorem exists_kappaOne_in_tail_range
    {p : CMParams} {c : ℝ}
    (hkappa_pos : 0 < kappa c) (hkappa_lt_one : kappa c < 1) :
    ∃ κ₁ : ℝ,
      kappa c < κ₁ ∧ κ₁ < 1 ∧
        κ₁ <
          min ((1 + p.α) * kappa c)
            (min (p.m * kappa c + 1 / 2) 1) := by
  let etaMax : ℝ :=
    min (p.α * kappa c)
      (min ((p.m - 1) * kappa c + 1 / 2) (1 - kappa c))
  have hAlpha_pos : 0 < p.α * kappa c :=
    mul_pos (lt_of_lt_of_le one_pos p.hα) hkappa_pos
  have hmterm_nonneg : 0 ≤ (p.m - 1) * kappa c :=
    mul_nonneg (sub_nonneg.mpr p.hm) hkappa_pos.le
  have hm_pos : 0 < (p.m - 1) * kappa c + 1 / 2 := by
    linarith
  have hone_pos : 0 < 1 - kappa c := by
    linarith
  have hetaMax_pos : 0 < etaMax := by
    dsimp [etaMax]
    exact lt_min hAlpha_pos (lt_min hm_pos hone_pos)
  let eta : ℝ := etaMax / 2
  let κ₁ : ℝ := kappa c + eta
  have heta_pos : 0 < eta := by
    dsimp [eta]
    linarith
  have hκ₁_gt : kappa c < κ₁ := by
    dsimp [κ₁]
    linarith
  have hκ₁_lt_one : κ₁ < 1 := by
    have hetaMax_le : etaMax ≤ 1 - kappa c := by
      dsimp [etaMax]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    dsimp [κ₁, eta]
    nlinarith
  have hκ₁_range :
      κ₁ <
        min ((1 + p.α) * kappa c)
          (min (p.m * kappa c + 1 / 2) 1) := by
    have hle_alpha : etaMax ≤ p.α * kappa c := by
      dsimp [etaMax]
      exact min_le_left _ _
    have hle_m : etaMax ≤ (p.m - 1) * kappa c + 1 / 2 := by
      dsimp [etaMax]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    apply lt_min
    · dsimp [κ₁, eta]
      nlinarith
    · apply lt_min
      · dsimp [κ₁, eta]
        nlinarith
      · exact hκ₁_lt_one
  exact ⟨κ₁, hκ₁_gt, hκ₁_lt_one, hκ₁_range⟩

theorem exists_remark43TailRateBound
    {p : CMParams} {c : ℝ}
    (hkappa_pos : 0 < kappa c) (hkappa_lt_one : kappa c < 1) :
    ∃ eta : ℝ, 0 < eta ∧ Remark43TailRateBound p c eta := by
  rcases exists_kappaOne_in_tail_range
      (p := p) (c := c) hkappa_pos hkappa_lt_one with
    ⟨κ₁, hκ₁_gt, _hκ₁_lt_one, hκ₁_range⟩
  exact
    ⟨κ₁ - kappa c, by linarith,
      Remark43TailRateBound.of_kappaOne_range hκ₁_gt hκ₁_range⟩

theorem exists_waveRightTailAsymptotic_of_forall_kappaOne_range
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (htail :
      ∀ κ₁, kappa c < κ₁ →
        κ₁ <
          min ((1 + p.α) * kappa c)
            (min (p.m * kappa c + 1 / 2) 1) →
        HasWaveRightTailAsymptotic c κ₁ U)
    (hkappa_pos : 0 < kappa c) (hkappa_lt_one : kappa c < 1) :
    ∃ κ₁ : ℝ,
      kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U := by
  rcases exists_kappaOne_in_tail_range
      (p := p) (c := c) hkappa_pos hkappa_lt_one with
    ⟨κ₁, hκ₁_gt, hκ₁_lt_one, hκ₁_range⟩
  exact ⟨κ₁, hκ₁_gt, hκ₁_lt_one, htail κ₁ hκ₁_gt hκ₁_range⟩

theorem exists_common_waveRightTailAsymptotic_of_forall_kappaOne_range
    {p : CMParams} {c : ℝ} {U₁ U₂ : ℝ → ℝ}
    (htail₁ :
      ∀ κ₁, kappa c < κ₁ →
        κ₁ <
          min ((1 + p.α) * kappa c)
            (min (p.m * kappa c + 1 / 2) 1) →
        HasWaveRightTailAsymptotic c κ₁ U₁)
    (htail₂ :
      ∀ κ₁, kappa c < κ₁ →
        κ₁ <
          min ((1 + p.α) * kappa c)
            (min (p.m * kappa c + 1 / 2) 1) →
        HasWaveRightTailAsymptotic c κ₁ U₂)
    (hkappa_pos : 0 < kappa c) (hkappa_lt_one : kappa c < 1) :
    ∃ κ₁ : ℝ,
      kappa c < κ₁ ∧ κ₁ < 1 ∧
        HasWaveRightTailAsymptotic c κ₁ U₁ ∧
        HasWaveRightTailAsymptotic c κ₁ U₂ := by
  rcases exists_kappaOne_in_tail_range
      (p := p) (c := c) hkappa_pos hkappa_lt_one with
    ⟨κ₁, hκ₁_gt, hκ₁_lt_one, hκ₁_range⟩
  exact
    ⟨κ₁, hκ₁_gt, hκ₁_lt_one,
      htail₁ κ₁ hκ₁_gt hκ₁_range,
      htail₂ κ₁ hκ₁_gt hκ₁_range⟩

theorem HasRemark43TailAsymptotic.at_rate
    {p : CMParams} {c eta : ℝ} {U : ℝ → ℝ}
    (h : HasRemark43TailAsymptotic p c U)
    (heta : Remark43TailRateBound p c eta) :
    Tendsto
      (fun x => Real.exp (eta * x) *
        (U x / Real.exp (-(kappa c) * x) - 1))
      atTop (𝓝 0) :=
  h eta heta

theorem HasRemark43TailAsymptotic.hasWaveRightTailAsymptotic
    {p : CMParams} {c κ₁ : ℝ} {U : ℝ → ℝ}
    (h : HasRemark43TailAsymptotic p c U)
    (hκ₁ : kappa c < κ₁)
    (hrange :
      κ₁ <
        min ((1 + p.α) * kappa c)
          (min (p.m * kappa c + 1 / 2) 1)) :
    HasWaveRightTailAsymptotic c κ₁ U :=
  h.at_rate (Remark43TailRateBound.of_kappaOne_range hκ₁ hrange)

theorem HasRemark43TailAsymptotic.exists_waveRightTailAsymptotic
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasRemark43TailAsymptotic p c U)
    (hkappa_pos : 0 < kappa c) (hkappa_lt_one : kappa c < 1) :
    ∃ κ₁ : ℝ,
      kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U := by
  let etaMax : ℝ :=
    min (p.α * kappa c)
      (min ((p.m - 1) * kappa c + 1 / 2) (1 - kappa c))
  have hAlpha_pos : 0 < p.α * kappa c :=
    mul_pos (lt_of_lt_of_le one_pos p.hα) hkappa_pos
  have hmterm_nonneg : 0 ≤ (p.m - 1) * kappa c :=
    mul_nonneg (sub_nonneg.mpr p.hm) hkappa_pos.le
  have hm_pos : 0 < (p.m - 1) * kappa c + 1 / 2 := by
    linarith
  have hone_pos : 0 < 1 - kappa c := by
    linarith
  have hetaMax_pos : 0 < etaMax := by
    dsimp [etaMax]
    exact lt_min hAlpha_pos (lt_min hm_pos hone_pos)
  let eta : ℝ := etaMax / 2
  let κ₁ : ℝ := kappa c + eta
  have heta_pos : 0 < eta := by
    dsimp [eta]
    linarith
  have hκ₁_gt : kappa c < κ₁ := by
    dsimp [κ₁]
    linarith
  have hκ₁_lt_one : κ₁ < 1 := by
    have hetaMax_le : etaMax ≤ 1 - kappa c := by
      dsimp [etaMax]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    dsimp [κ₁, eta]
    nlinarith
  have hκ₁_range :
      κ₁ <
        min ((1 + p.α) * kappa c)
          (min (p.m * kappa c + 1 / 2) 1) := by
    have hle_alpha : etaMax ≤ p.α * kappa c := by
      dsimp [etaMax]
      exact min_le_left _ _
    have hle_m : etaMax ≤ (p.m - 1) * kappa c + 1 / 2 := by
      dsimp [etaMax]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    apply lt_min
    · dsimp [κ₁, eta]
      nlinarith
    · apply lt_min
      · dsimp [κ₁, eta]
        nlinarith
      · exact hκ₁_lt_one
  exact
    ⟨κ₁, hκ₁_gt, hκ₁_lt_one,
      h.hasWaveRightTailAsymptotic hκ₁_gt hκ₁_range⟩

theorem HasRemark43TailAsymptotic.exists_common_waveRightTailAsymptotic
    {p : CMParams} {c : ℝ} {U₁ U₂ : ℝ → ℝ}
    (h₁ : HasRemark43TailAsymptotic p c U₁)
    (h₂ : HasRemark43TailAsymptotic p c U₂)
    (hkappa_pos : 0 < kappa c) (hkappa_lt_one : kappa c < 1) :
    ∃ κ₁ : ℝ,
      kappa c < κ₁ ∧ κ₁ < 1 ∧
        HasWaveRightTailAsymptotic c κ₁ U₁ ∧
        HasWaveRightTailAsymptotic c κ₁ U₂ := by
  let etaMax : ℝ :=
    min (p.α * kappa c)
      (min ((p.m - 1) * kappa c + 1 / 2) (1 - kappa c))
  have hAlpha_pos : 0 < p.α * kappa c :=
    mul_pos (lt_of_lt_of_le one_pos p.hα) hkappa_pos
  have hmterm_nonneg : 0 ≤ (p.m - 1) * kappa c :=
    mul_nonneg (sub_nonneg.mpr p.hm) hkappa_pos.le
  have hm_pos : 0 < (p.m - 1) * kappa c + 1 / 2 := by
    linarith
  have hone_pos : 0 < 1 - kappa c := by
    linarith
  have hetaMax_pos : 0 < etaMax := by
    dsimp [etaMax]
    exact lt_min hAlpha_pos (lt_min hm_pos hone_pos)
  let eta : ℝ := etaMax / 2
  let κ₁ : ℝ := kappa c + eta
  have heta_pos : 0 < eta := by
    dsimp [eta]
    linarith
  have hκ₁_gt : kappa c < κ₁ := by
    dsimp [κ₁]
    linarith
  have hκ₁_lt_one : κ₁ < 1 := by
    have hetaMax_le : etaMax ≤ 1 - kappa c := by
      dsimp [etaMax]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    dsimp [κ₁, eta]
    nlinarith
  have hκ₁_range :
      κ₁ <
        min ((1 + p.α) * kappa c)
          (min (p.m * kappa c + 1 / 2) 1) := by
    have hle_alpha : etaMax ≤ p.α * kappa c := by
      dsimp [etaMax]
      exact min_le_left _ _
    have hle_m : etaMax ≤ (p.m - 1) * kappa c + 1 / 2 := by
      dsimp [etaMax]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    apply lt_min
    · dsimp [κ₁, eta]
      nlinarith
    · apply lt_min
      · dsimp [κ₁, eta]
        nlinarith
      · exact hκ₁_lt_one
  exact
    ⟨κ₁, hκ₁_gt, hκ₁_lt_one,
      h₁.hasWaveRightTailAsymptotic hκ₁_gt hκ₁_range,
      h₂.hasWaveRightTailAsymptotic hκ₁_gt hκ₁_range⟩

theorem Remark_4_3.weighted_initial_closeness
    (h : Remark_4_3) {p : CMParams} {c eta : ℝ}
    (hkappa : 0 < kappa c) (heta : Remark43TailRateBound p c eta)
    {U₁ V₁ U₂ V₂ : ℝ → ℝ}
    (hTW₁ : IsTravelingWave p c U₁ V₁)
    (hTW₂ : IsTravelingWave p c U₂ V₂)
    (hbound₁ : HasWaveUpperTailBound p c U₁)
    (hbound₂ : HasWaveUpperTailBound p c U₂)
    (htail₁ : HasRemark43TailAsymptotic p c U₁)
    (htail₂ : HasRemark43TailAsymptotic p c U₂) :
    WeightedL2InitialCloseness (eta + kappa c) U₂ U₁ :=
  h p c hkappa U₁ V₁ U₂ V₂ hTW₁ hTW₂
    hbound₁ hbound₂ htail₁ htail₂ eta heta

theorem Remark_4_3.exists_weighted_initial_closeness
    (h : Remark_4_3) {p : CMParams} {c : ℝ}
    (hkappa_pos : 0 < kappa c) (hkappa_lt_one : kappa c < 1)
    {U₁ V₁ U₂ V₂ : ℝ → ℝ}
    (hTW₁ : IsTravelingWave p c U₁ V₁)
    (hTW₂ : IsTravelingWave p c U₂ V₂)
    (hbound₁ : HasWaveUpperTailBound p c U₁)
    (hbound₂ : HasWaveUpperTailBound p c U₂)
    (htail₁ : HasRemark43TailAsymptotic p c U₁)
    (htail₂ : HasRemark43TailAsymptotic p c U₂) :
    ∃ eta : ℝ, 0 < eta ∧
      Remark43TailRateBound p c eta ∧
        WeightedL2InitialCloseness (eta + kappa c) U₂ U₁ := by
  rcases exists_remark43TailRateBound
      (p := p) (c := c) hkappa_pos hkappa_lt_one with
    ⟨eta, heta_pos, heta⟩
  exact
    ⟨eta, heta_pos, heta,
      h.weighted_initial_closeness hkappa_pos heta
        hTW₁ hTW₂ hbound₁ hbound₂ htail₁ htail₂⟩

def WaveDerivativeTendsZero (U : ℝ → ℝ) : Prop :=
  Tendsto (fun x => deriv U x) atBot (𝓝 0) ∧
    Tendsto (fun x => deriv U x) atTop (𝓝 0)

def Lemma_5_1 : Prop :=
  ∀ p : CMParams, ∀ c : ℝ, 2 < c →
    ∀ U V : ℝ → ℝ,
      IsTravelingWave p c U V →
      HasWaveUpperTailBound p c U →
        (∀ x, |V x| ≤ (MChi p) ^ p.γ ∧ |deriv V x| ≤ (MChi p) ^ p.γ) ∧
        (p.γ + p.γ⁻¹ < c →
          ∀ x,
            |V x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x)) ∧
            |deriv V x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x))) ∧
        WaveDerivativeTendsZero U ∧
        (c > p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) →
          ∃ B > 0, ∀ x, |deriv U x| ≤ B) ∧
        (c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
          ∃ B1 B2, ∀ x,
            |deriv U x| ≤
              B1 * Real.exp (-(kappa c) * x) +
                B2 * Real.exp (-(kappa c) * p.γ * x))

theorem Lemma_5_1.signal_bound
    (h : Lemma_5_1) {p : CMParams} {c : ℝ} (hc : 2 < c)
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U) :
    ∀ x, |V x| ≤ (MChi p) ^ p.γ ∧ |deriv V x| ≤ (MChi p) ^ p.γ :=
  (h p c hc U V hTW hbound).1

theorem Lemma_5_1.exponential_signal_bound
    (h : Lemma_5_1) {p : CMParams} {c : ℝ} (hc : 2 < c)
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hspeed : p.γ + p.γ⁻¹ < c) :
    ∀ x,
      |V x| ≤
        min ((MChi p) ^ p.γ)
          ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
            Real.exp (-(kappa c) * p.γ * x)) ∧
      |deriv V x| ≤
        min ((MChi p) ^ p.γ)
          ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
            Real.exp (-(kappa c) * p.γ * x)) :=
  (h p c hc U V hTW hbound).2.1 hspeed

theorem Lemma_5_1.wave_derivative_tends_zero
    (h : Lemma_5_1) {p : CMParams} {c : ℝ} (hc : 2 < c)
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U) :
    WaveDerivativeTendsZero U :=
  (h p c hc U V hTW hbound).2.2.1

theorem Lemma_5_1.wave_derivative_bounded
    (h : Lemma_5_1) {p : CMParams} {c : ℝ} (hc : 2 < c)
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hspeed : c > p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) :
    ∃ B > 0, ∀ x, |deriv U x| ≤ B :=
  (h p c hc U V hTW hbound).2.2.2.1 hspeed

theorem Lemma_5_1.wave_derivative_exp_bound
    (h : Lemma_5_1) {p : CMParams} {c : ℝ} (hc : 2 < c)
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hspeed :
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1))) :
    ∃ B1 B2, ∀ x,
      |deriv U x| ≤
        B1 * Real.exp (-(kappa c) * x) +
          B2 * Real.exp (-(kappa c) * p.γ * x) :=
  (h p c hc U V hTW hbound).2.2.2.2 hspeed

/-- The explicit log-derivative bound from Paper1 Lemma 5.2. -/
def logDerivativeBoundFormula (p : CMParams) (c : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (c + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) +
      Real.sqrt
        ((c + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1)) ^ 2 +
          4 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
          4 * (MChi p) ^ p.α))

/-- Paper1 Lemma 5.2 with the explicit constant displayed in the paper. -/
def Lemma_5_2_explicit : Prop :=
  ∀ p : CMParams, ∀ c : ℝ,
    c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
          ∀ x, deriv U x / U x ≤ logDerivativeBoundFormula p c

theorem Lemma_5_2_explicit.log_derivative_bound
    (h : Lemma_5_2_explicit) {p : CMParams} {c : ℝ}
    (hspeed :
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U) :
    ∀ x, deriv U x / U x ≤ logDerivativeBoundFormula p c :=
  h p c hspeed U V hTW hbound

def Lemma_5_2 : Prop :=
  ∀ p : CMParams, ∀ c : ℝ,
    c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
          ∃ B > 0, ∀ x, deriv U x / U x ≤ B

theorem Lemma_5_2_explicit.to_Lemma_5_2
    (h : Lemma_5_2_explicit) : Lemma_5_2 := by
  intro p c hspeed U V hTW hbound
  refine ⟨max (logDerivativeBoundFormula p c) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · intro x
    exact le_trans
      (h.log_derivative_bound hspeed hTW hbound x)
      (le_max_left _ _)

theorem Lemma_5_2.log_derivative_bound
    (h : Lemma_5_2) {p : CMParams} {c : ℝ}
    (hspeed :
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U) :
    ∃ B > 0, ∀ x, deriv U x / U x ≤ B :=
  h p c hspeed U V hTW hbound

/-- The constant `M'_{\chi,m,\alpha,\gamma}` from Paper1 Remark 5.1. -/
def remark51MPrime (p : CMParams) : ℝ :=
  |p.χ| * (MChi p) ^ (p.m + p.γ) + (MChi p) ^ (1 + p.α)

/-- The constant `M''_{\chi,m,\alpha,\gamma,\sigma}` from Paper1 Remark 5.1.
The paper writes `|χ|2σ`; here it is represented as `|χ|^2 * σ`. -/
def remark51MDoublePrime (p : CMParams) (sigma : ℝ) : ℝ :=
  2 *
    (1 + 2 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) + (MChi p) ^ p.α) *
      (|p.χ| ^ 2 * sigma +
        |p.χ| * p.m * (MChi p) ^ (p.m - 1) *
          (|p.χ| * (MChi p) ^ (p.m + p.γ) +
            (MChi p) ^ (p.α + 1)) *
          (p.γ + |p.χ| * sigma))

/-- The stronger speed hypothesis used in Paper1 Remarks 5.1 and 5.2. -/
def remark5SpeedCondition (p : CMParams) (c sigma : ℝ) : Prop :=
  c >
    max
      (p.γ + |p.χ| * sigma + (p.γ + |p.χ|) / sigma)
      (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
        |p.χ| * sigma)

theorem remark5SpeedCondition.gt_first
    {p : CMParams} {c sigma : ℝ}
    (h : remark5SpeedCondition p c sigma) :
    p.γ + |p.χ| * sigma + (p.γ + |p.χ|) / sigma < c :=
  lt_of_le_of_lt (le_max_left _ _) h

theorem remark5SpeedCondition.gt_second
    {p : CMParams} {c sigma : ℝ}
    (h : remark5SpeedCondition p c sigma) :
    p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
        |p.χ| * sigma < c :=
  lt_of_le_of_lt (le_max_right _ _) h

theorem remark5SpeedCondition.gt_waveDerivativeSpeed
    {p : CMParams} {c sigma : ℝ}
    (h : remark5SpeedCondition p c sigma) (hsigma : 0 ≤ sigma) :
    p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) < c := by
  have hnonneg : 0 ≤ |p.χ| * sigma :=
    mul_nonneg (abs_nonneg p.χ) hsigma
  exact lt_of_le_of_lt (by linarith) h.gt_second

/-- Paper1 Remark 5.1: under the stronger `sigma` speed condition, the
stationary profile derivative has a global `1/(|χ|σ)` bound and a right-tail
exponential `1/(|χ|^2 σ)` bound. -/
def Remark_5_1 : Prop :=
  ∀ p : CMParams, ∀ c sigma : ℝ,
    0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
          (∀ x : ℝ,
            |deriv U x| ≤ remark51MPrime p / (|p.χ| * sigma)) ∧
          ∀ x : ℝ, 0 ≤ x →
            |deriv U x| ≤
              remark51MDoublePrime p sigma / (|p.χ| ^ 2 * sigma) *
                Real.exp (-(kappa c) * x)

theorem Remark_5_1.derivative_bound
    (h : Remark_5_1) {p : CMParams} {c sigma : ℝ}
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hspeed : remark5SpeedCondition p c sigma)
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U) :
    ∀ x : ℝ, |deriv U x| ≤ remark51MPrime p / (|p.χ| * sigma) :=
  (h p c sigma hsigma hχ hspeed U V hTW hbound).1

theorem Remark_5_1.derivative_exp_bound
    (h : Remark_5_1) {p : CMParams} {c sigma : ℝ}
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hspeed : remark5SpeedCondition p c sigma)
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U) :
    ∀ x : ℝ, 0 ≤ x →
      |deriv U x| ≤
        remark51MDoublePrime p sigma / (|p.χ| ^ 2 * sigma) *
          Real.exp (-(kappa c) * x) :=
  (h p c sigma hsigma hχ hspeed U V hTW hbound).2

/-- The piecewise constant `M'''_{\chi,m,\alpha,\gamma,\sigma}` from
Paper1 Remark 5.2.  The branch at `c ≤ 5/2` comes from Lemma 5.2; the branch at
`5/2 < c` comes from Remark 4.1 and Remark 5.1. -/
def remark52MTriplePrime (p : CMParams) (c sigma : ℝ) : ℝ :=
  if c ≤ (5 / 2 : ℝ) then
    |p.χ| ^ 2 * sigma / 2 *
      (5 / 2 + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) +
        Real.sqrt
          ((5 / 2 + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1)) ^ 2 +
            4 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
            4 * (MChi p) ^ p.α))
  else
    max
      (8 * (1 + |p.χ| + 2 * p.m * |p.χ|) *
        (p.γ + |p.χ| * sigma) / (1 + p.γ) * remark51MPrime p)
      (2 * remark51MDoublePrime p sigma)

theorem remark52MTriplePrime_eq_of_le
    {p : CMParams} {c sigma : ℝ} (hc : c ≤ (5 / 2 : ℝ)) :
    remark52MTriplePrime p c sigma =
      |p.χ| ^ 2 * sigma / 2 *
        (5 / 2 + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) +
          Real.sqrt
            ((5 / 2 + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1)) ^ 2 +
              4 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
              4 * (MChi p) ^ p.α)) := by
  simp [remark52MTriplePrime, hc]

theorem remark52MTriplePrime_eq_of_gt
    {p : CMParams} {c sigma : ℝ} (hc : (5 / 2 : ℝ) < c) :
    remark52MTriplePrime p c sigma =
      max
        (8 * (1 + |p.χ| + 2 * p.m * |p.χ|) *
          (p.γ + |p.χ| * sigma) / (1 + p.γ) * remark51MPrime p)
        (2 * remark51MDoublePrime p sigma) := by
  simp [remark52MTriplePrime, not_le.mpr hc]

theorem remark52MTriplePrime.first_branch_le_of_gt
    {p : CMParams} {c sigma : ℝ} (hc : (5 / 2 : ℝ) < c) :
    8 * (1 + |p.χ| + 2 * p.m * |p.χ|) *
        (p.γ + |p.χ| * sigma) / (1 + p.γ) * remark51MPrime p ≤
      remark52MTriplePrime p c sigma := by
  rw [remark52MTriplePrime_eq_of_gt hc]
  exact le_max_left _ _

theorem remark52MTriplePrime.doublePrime_branch_le_of_gt
    {p : CMParams} {c sigma : ℝ} (hc : (5 / 2 : ℝ) < c) :
    2 * remark51MDoublePrime p sigma ≤ remark52MTriplePrime p c sigma := by
  rw [remark52MTriplePrime_eq_of_gt hc]
  exact le_max_right _ _

theorem remark5Denominator_pos
    {p : CMParams} {sigma : ℝ} (hsigma : 0 < sigma) (hχ : p.χ ≠ 0) :
    0 < |p.χ| ^ 2 * sigma := by
  exact mul_pos (pow_pos (abs_pos.mpr hχ) 2) hsigma

/-- Paper1 Remark 5.2: the `sigma` speed condition gives the displayed
`U'/U` bound with the piecewise constant `M'''`. -/
def Remark_5_2 : Prop :=
  ∀ p : CMParams, ∀ c sigma : ℝ,
    0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
          ∀ x : ℝ,
            deriv U x / U x ≤
              remark52MTriplePrime p c sigma / (|p.χ| ^ 2 * sigma)

theorem Remark_5_2.log_derivative_bound
    (h : Remark_5_2) {p : CMParams} {c sigma : ℝ}
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hspeed : remark5SpeedCondition p c sigma)
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U) :
    ∀ x : ℝ,
      deriv U x / U x ≤
        remark52MTriplePrime p c sigma / (|p.χ| ^ 2 * sigma) :=
  h p c sigma hsigma hχ hspeed U V hTW hbound

def Lemma_5_3 : Prop :=
  ∀ gamma M eta : ℝ,
    1 ≤ gamma → 1 ≤ M → 0 < eta → eta < 1 →
      ∀ u1 u2 : ℝ → ℝ,
        IsCUnifBdd u1 → IsCUnifBdd u2 →
        (∀ x, 0 ≤ u1 x ∧ u1 x ≤ M) →
        (∀ x, 0 ≤ u2 x ∧ u2 x ≤ M) →
        Integrable
          (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2) →
          let v := Psi (fun x => u2 x ^ gamma - u1 x ^ gamma) 1 1
          let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
          let V := fun x => Real.exp (eta * x) * v x
          (∫ x : ℝ, |V x| ^ 2 ≤
              gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta) ^ 2 *
                ∫ x : ℝ, |U x| ^ 2) ∧
            (∫ x : ℝ, |deriv V x| ^ 2 ≤
              gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta ^ 2) *
                ∫ x : ℝ, |U x| ^ 2)

theorem Lemma_5_3.weighted_elliptic_perturbation
    (h : Lemma_5_3)
    {gamma M eta : ℝ}
    (hgamma : 1 ≤ gamma) (hM : 1 ≤ M) (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hu1_bound : ∀ x, 0 ≤ u1 x ∧ u1 x ≤ M)
    (hu2_bound : ∀ x, 0 ≤ u2 x ∧ u2 x ≤ M)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2)) :
    let v := Psi (fun x => u2 x ^ gamma - u1 x ^ gamma) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  h gamma M eta hgamma hM heta_pos heta_one
    u1 u2 hu1 hu2 hu1_bound hu2_bound hclose

theorem Lemma_5_3.weighted_elliptic_perturbation_CM
    (h : Lemma_5_3) (p : CMParams) {eta : ℝ}
    (hM : 1 ≤ MChi p) (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hu1_bound : ∀ x, 0 ≤ u1 x ∧ u1 x ≤ MChi p)
    (hu2_bound : ∀ x, 0 ≤ u2 x ∧ u2 x ≤ MChi p)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2)) :
    let v := Psi (fun x => u2 x ^ p.γ - u1 x ^ p.γ) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  h.weighted_elliptic_perturbation p.hγ hM heta_pos heta_one
    hu1 hu2 hu1_bound hu2_bound hclose

theorem Lemma_5_3.weighted_elliptic_perturbation_of_tail_bounds
    (h : Lemma_5_3) {p : CMParams} {c eta : ℝ}
    (hM : 1 ≤ MChi p) (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hbound1 : HasWaveUpperTailBound p c u1)
    (hbound2 : HasWaveUpperTailBound p c u2)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2)) :
    let v := Psi (fun x => u2 x ^ p.γ - u1 x ^ p.γ) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  h.weighted_elliptic_perturbation_CM p hM heta_pos heta_one
    hu1 hu2
    (fun x => ⟨(hbound1.pos x).le, hbound1.le_MChi x⟩)
    (fun x => ⟨(hbound2.pos x).le, hbound2.le_MChi x⟩)
    hclose

/-- Paper1 Proposition 1.1: global existence and boundedness of Cauchy solutions. -/
def Proposition_1_1 : Prop :=
  (∀ p : CMParams, p.χ ≤ 0 →
    ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ →
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p u₀ u v ∧
        (∀ M, (∀ x, u₀ x ≤ M) →
          ∀ t x, 0 ≤ t → u t x ≤ max 1 M) ∧
        UniformLimsupLe u 1) ∧
  (∀ p : CMParams,
    (0 < p.χ ∧ p.α > p.m + p.γ - 1) ∨
      (0 < p.χ ∧
        p.χ < min
          ((p.m + p.γ - 1) / (2 * p.m - 1))
          ((p.m + p.γ - 1) / (p.γ - 1)) ∧
        p.α = p.m + p.γ - 1) →
    ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ →
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p u₀ u v ∧
        UniformEventuallyBounded u ∧
        (0 < p.χ → p.χ < 1 → UniformLimsupLe u ((1 / (1 - p.χ)) ^ (1 / p.α))))

theorem Proposition_1_1.negative_solution
    (h : Proposition_1_1) {p : CMParams}
    (hχ : p.χ ≤ 0) {u₀ : ℝ → ℝ}
    (hu₀ : NonnegativeInitialDatum u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p u₀ u v ∧
      (∀ M, (∀ x, u₀ x ≤ M) →
        ∀ t x, 0 ≤ t → u t x ≤ max 1 M) ∧
      UniformLimsupLe u 1 :=
  h.1 p hχ u₀ hu₀

theorem Proposition_1_1.positive_solution
    (h : Proposition_1_1) {p : CMParams}
    (hparam :
      (0 < p.χ ∧ p.α > p.m + p.γ - 1) ∨
        (0 < p.χ ∧
          p.χ < min
            ((p.m + p.γ - 1) / (2 * p.m - 1))
            ((p.m + p.γ - 1) / (p.γ - 1)) ∧
          p.α = p.m + p.γ - 1))
    {u₀ : ℝ → ℝ} (hu₀ : NonnegativeInitialDatum u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p u₀ u v ∧
      UniformEventuallyBounded u ∧
      (0 < p.χ → p.χ < 1 → UniformLimsupLe u ((1 / (1 - p.χ)) ^ (1 / p.α))) :=
  h.2 p hparam u₀ hu₀

/-- Paper1 Proposition 1.2: stability of the positive constant solution. -/
def Proposition_1_2 : Prop :=
  (∀ p : CMParams, p.χ ≤ 0 →
    ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ → UniformlyPositive u₀ →
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p u₀ u v ∧
        UniformConvergesToConstant u 1) ∧
  (∀ p : CMParams, 0 < p.χ → p.χ < (1 / 2 : ℝ) →
    p.m + p.γ - 1 ≤ p.α →
    ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ → UniformlyPositive u₀ →
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p u₀ u v ∧
        UniformConvergesToConstant u 1)

theorem Proposition_1_2.negative_stability
    (h : Proposition_1_2) {p : CMParams}
    (hχ : p.χ ≤ 0) {u₀ : ℝ → ℝ}
    (hu₀_nonneg : NonnegativeInitialDatum u₀)
    (hu₀_pos : UniformlyPositive u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p u₀ u v ∧
      UniformConvergesToConstant u 1 :=
  h.1 p hχ u₀ hu₀_nonneg hu₀_pos

theorem Proposition_1_2.negative_stability_with_long_time_bounds
    (h : Proposition_1_2) {p : CMParams}
    (hχ : p.χ ≤ 0) {u₀ : ℝ → ℝ}
    (hu₀_nonneg : NonnegativeInitialDatum u₀)
    (hu₀_pos : UniformlyPositive u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p u₀ u v ∧
      UniformConvergesToConstant u 1 ∧
      UniformEventuallyBounded u ∧
      UniformLimsupLe u 1 := by
  rcases h.negative_stability hχ hu₀_nonneg hu₀_pos with ⟨u, v, hsol, hconv⟩
  exact ⟨u, v, hsol, hconv, hconv.uniformEventuallyBounded, hconv.uniformLimsupLe⟩

theorem Proposition_1_2.positive_stability
    (h : Proposition_1_2) {p : CMParams}
    (hχ_pos : 0 < p.χ) (hχ_small : p.χ < (1 / 2 : ℝ))
    (halpha : p.m + p.γ - 1 ≤ p.α)
    {u₀ : ℝ → ℝ}
    (hu₀_nonneg : NonnegativeInitialDatum u₀)
    (hu₀_pos : UniformlyPositive u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p u₀ u v ∧
      UniformConvergesToConstant u 1 :=
  h.2 p hχ_pos hχ_small halpha u₀ hu₀_nonneg hu₀_pos

theorem Proposition_1_2.positive_stability_with_long_time_bounds
    (h : Proposition_1_2) {p : CMParams}
    (hχ_pos : 0 < p.χ) (hχ_small : p.χ < (1 / 2 : ℝ))
    (halpha : p.m + p.γ - 1 ≤ p.α)
    {u₀ : ℝ → ℝ}
    (hu₀_nonneg : NonnegativeInitialDatum u₀)
    (hu₀_pos : UniformlyPositive u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p u₀ u v ∧
      UniformConvergesToConstant u 1 ∧
      UniformEventuallyBounded u ∧
      UniformLimsupLe u 1 := by
  rcases h.positive_stability hχ_pos hχ_small halpha hu₀_nonneg hu₀_pos with
    ⟨u, v, hsol, hconv⟩
  exact ⟨u, v, hsol, hconv, hconv.uniformEventuallyBounded, hconv.uniformLimsupLe⟩

/-- Paper1 Theorem 1.1: existence of traveling waves. -/
def Theorem_1_1 : Prop :=
  (∀ p : CMParams, p.α ≤ p.m + p.γ - 1 → p.χ ≤ 0 →
    ∀ c : ℝ, cStarLower p < c →
      ∃ U V : ℝ → ℝ,
        IsMonotoneTravelingWave p c U V ∧
        ShenUpperBoundNegative c U ∧
        ∀ κ₁, kappa c < κ₁ →
          κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) →
          HasWaveRightTailAsymptotic c κ₁ U) ∧
  (∀ p : CMParams, p.α = p.m + p.γ - 1 →
    0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
    ∀ c : ℝ, 2 < c →
      ∃ U V : ℝ → ℝ,
        IsTravelingWave p c U V ∧
        ShenUpperBoundPositive p c U ∧
        ∀ κ₁, kappa c < κ₁ →
          κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) →
          HasWaveRightTailAsymptotic c κ₁ U)

theorem Theorem_1_1.negative_wave
    (h : Theorem_1_1) {p : CMParams}
    (halpha : p.α ≤ p.m + p.γ - 1) (hχ : p.χ ≤ 0)
    {c : ℝ} (hc : cStarLower p < c) :
    ∃ U V : ℝ → ℝ,
      IsMonotoneTravelingWave p c U V ∧
      ShenUpperBoundNegative c U ∧
      ∀ κ₁, kappa c < κ₁ →
        κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) →
        HasWaveRightTailAsymptotic c κ₁ U :=
  h.1 p halpha hχ c hc

theorem Theorem_1_1.positive_wave
    (h : Theorem_1_1) {p : CMParams}
    (halpha : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ) (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    {c : ℝ} (hc : 2 < c) :
    ∃ U V : ℝ → ℝ,
      IsTravelingWave p c U V ∧
      ShenUpperBoundPositive p c U ∧
      ∀ κ₁, kappa c < κ₁ →
        κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) →
        HasWaveRightTailAsymptotic c κ₁ U :=
  h.2 p halpha hχ_nonneg hχ_small c hc

theorem Theorem_1_1.positive_rightVanishingWave
    (h : Theorem_1_1) {p : CMParams}
    (halpha : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ) (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    {c : ℝ} (hc : 2 < c) :
    ∃ U V : ℝ → ℝ, IsRightVanishingTravelingWave p c U V := by
  rcases h.positive_wave halpha hχ_nonneg hχ_small hc with
    ⟨U, V, hTW, _hupper, _htail⟩
  exact ⟨U, V, IsTravelingWave.to_rightVanishingTravelingWave hTW⟩

theorem Theorem_1_1.positive_wave_with_strict_tail_bound
    (h : Theorem_1_1) {p : CMParams}
    (halpha : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ) (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    {c : ℝ} (hc : 2 < c) :
    ∃ U V : ℝ → ℝ,
      IsTravelingWave p c U V ∧
      HasStrictWaveUpperTailBound p c U ∧
      ∀ κ₁, kappa c < κ₁ →
        κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) →
        HasWaveRightTailAsymptotic c κ₁ U := by
  rcases h.positive_wave halpha hχ_nonneg hχ_small hc with
    ⟨U, V, hTW, hupper, htail⟩
  have hχ_lt_one : p.χ < 1 := by
    have hχ_lt_half : p.χ < (1 / 2 : ℝ) :=
      lt_of_lt_of_le hχ_small (min_le_left _ _)
    linarith
  exact
    ⟨U, V, hTW,
      ShenUpperBoundPositive.hasStrictWaveUpperTailBound hupper hχ_nonneg hχ_lt_one,
      htail⟩

theorem Theorem_1_1.negative_wave_with_tail_witness
    (h : Theorem_1_1) {p : CMParams}
    (halpha : p.α ≤ p.m + p.γ - 1) (hχ : p.χ ≤ 0)
    {c : ℝ} (hc : cStarLower p < c) :
    ∃ U V : ℝ → ℝ,
      IsMonotoneTravelingWave p c U V ∧
      ShenUpperBoundNegative c U ∧
      ∃ κ₁ : ℝ,
        kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U := by
  rcases h.negative_wave halpha hχ hc with ⟨U, V, hTW, hupper, htail⟩
  exact
    ⟨U, V, hTW, hupper,
      exists_waveRightTailAsymptotic_of_forall_kappaOne_range
        htail (kappa_pos_of_cStarLower_lt hc) (kappa_lt_one_of_cStarLower_lt hc)⟩

theorem Theorem_1_1.positive_wave_with_stability_tail_data
    (h : Theorem_1_1) {p : CMParams}
    (halpha : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ) (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    {c : ℝ} (hc : 2 < c) :
    ∃ U V : ℝ → ℝ,
      IsTravelingWave p c U V ∧
      HasStrictWaveUpperTailBound p c U ∧
      ∃ κ₁ : ℝ,
        kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U := by
  rcases h.positive_wave_with_strict_tail_bound
      halpha hχ_nonneg hχ_small hc with
    ⟨U, V, hTW, hbound, htail⟩
  exact
    ⟨U, V, hTW, hbound,
      exists_waveRightTailAsymptotic_of_forall_kappaOne_range
        htail (kappa_pos_of_two_lt hc) (kappa_lt_one_of_two_lt hc)⟩

theorem Theorem_1_1.negative_wave_with_ratio_limit
    (h : Theorem_1_1) {p : CMParams}
    (halpha : p.α ≤ p.m + p.γ - 1) (hχ : p.χ ≤ 0)
    {c : ℝ} (hc : cStarLower p < c) :
    ∃ U V : ℝ → ℝ,
      IsMonotoneTravelingWave p c U V ∧
      ShenUpperBoundNegative c U ∧
      Tendsto (fun x => U x / Real.exp (-(kappa c) * x)) atTop (𝓝 1) := by
  rcases h.negative_wave_with_tail_witness halpha hχ hc with
    ⟨U, V, hTW, hupper, κ₁, hκ₁_gt, _hκ₁_lt, htail⟩
  exact ⟨U, V, hTW, hupper, htail.ratio_tendsto_one hκ₁_gt⟩

theorem Theorem_1_1.positive_wave_with_ratio_limit
    (h : Theorem_1_1) {p : CMParams}
    (halpha : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ) (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    {c : ℝ} (hc : 2 < c) :
    ∃ U V : ℝ → ℝ,
      IsTravelingWave p c U V ∧
      HasStrictWaveUpperTailBound p c U ∧
      Tendsto (fun x => U x / Real.exp (-(kappa c) * x)) atTop (𝓝 1) := by
  rcases h.positive_wave_with_stability_tail_data
      halpha hχ_nonneg hχ_small hc with
    ⟨U, V, hTW, hbound, κ₁, hκ₁_gt, _hκ₁_lt, htail⟩
  exact ⟨U, V, hTW, hbound, htail.ratio_tendsto_one hκ₁_gt⟩

theorem Theorem_1_1.of_frozenStationaryProfile_branches
    (hneg :
      ∀ p : CMParams, p.α ≤ p.m + p.γ - 1 → p.χ ≤ 0 →
        ∀ c : ℝ, cStarLower p < c →
          ∃ U : ℝ → ℝ,
            FrozenStationaryWaveProfile p c U ∧
              (∀ x, deriv U x ≤ 0) ∧
              (∀ x, deriv (frozenElliptic p U) x ≤ 0) ∧
              ShenUpperBoundNegative c U ∧
              ∀ κ₁, kappa c < κ₁ →
                κ₁ <
                  min ((1 + p.α) * kappa c)
                    (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U)
    (hpos :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∃ U : ℝ → ℝ,
            FrozenStationaryWaveProfile p c U ∧
              ShenUpperBoundPositive p c U ∧
              ∀ κ₁, kappa c < κ₁ →
                κ₁ <
                  min ((1 + p.α) * kappa c)
                    (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U) :
    Theorem_1_1 := by
  constructor
  · intro p halpha hχ c hc
    rcases hneg p halpha hχ c hc with
      ⟨U, hprofile, hUmono, hVmono, hupper, htail⟩
    exact
      ⟨U, frozenElliptic p U,
        hprofile.to_monotoneTravelingWave hUmono hVmono, hupper, htail⟩
  · intro p halpha hχ_nonneg hχ_small c hc
    rcases hpos p halpha hχ_nonneg hχ_small c hc with
      ⟨U, hprofile, hupper, htail⟩
    exact
      ⟨U, frozenElliptic p U,
        hprofile.to_travelingWave, hupper, htail⟩

theorem Theorem_1_1.of_frozenStationaryProfile_trap_branches
    (hneg :
      ∀ p : CMParams, p.α ≤ p.m + p.γ - 1 → p.χ ≤ 0 →
        ∀ c : ℝ, cStarLower p < c →
          ∃ U : ℝ → ℝ,
            InMonotoneWaveTrapSet (kappa c) 1 U ∧
              FrozenStationaryWaveProfile p c U ∧
              (∀ x, deriv (frozenElliptic p U) x ≤ 0) ∧
              ShenUpperBoundNegative c U ∧
              ∀ κ₁, kappa c < κ₁ →
                κ₁ <
                  min ((1 + p.α) * kappa c)
                    (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U)
    (hpos :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∃ U : ℝ → ℝ,
            FrozenStationaryWaveProfile p c U ∧
              ShenUpperBoundPositive p c U ∧
              ∀ κ₁, kappa c < κ₁ →
                κ₁ <
                  min ((1 + p.α) * kappa c)
                    (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U) :
    Theorem_1_1 := by
  refine Theorem_1_1.of_frozenStationaryProfile_branches ?_ hpos
  intro p halpha hχ c hc
  rcases hneg p halpha hχ c hc with
    ⟨U, htrap, hprofile, hVmono, hupper, htail⟩
  exact
    ⟨U, hprofile, htrap.deriv_nonpos, hVmono, hupper, htail⟩

def StableWaveParameterRegime (p : CMParams) : Prop :=
  (p.χ < 0 ∧ p.α ≤ p.m + p.γ - 1) ∨
    (0 ≤ p.χ ∧ p.χ < chiStar p ∧ p.α = p.m + p.γ - 1)

theorem StableWaveParameterRegime.of_negative
    {p : CMParams} (hχ : p.χ < 0) (halpha : p.α ≤ p.m + p.γ - 1) :
    StableWaveParameterRegime p :=
  Or.inl ⟨hχ, halpha⟩

theorem StableWaveParameterRegime.of_positive
    {p : CMParams}
    (hχ_nonneg : 0 ≤ p.χ) (hχ_small : p.χ < chiStar p)
    (halpha : p.α = p.m + p.γ - 1) :
    StableWaveParameterRegime p :=
  Or.inr ⟨hχ_nonneg, hχ_small, halpha⟩

theorem StableWaveParameterRegime.alpha_le
    {p : CMParams} (h : StableWaveParameterRegime p) :
    p.α ≤ p.m + p.γ - 1 := by
  rcases h with hneg | hpos
  · exact hneg.2
  · exact le_of_eq hpos.2.2

theorem StableWaveParameterRegime.positive_branch_of_chi_nonneg
    {p : CMParams} (h : StableWaveParameterRegime p) (hχ_nonneg : 0 ≤ p.χ) :
    p.χ < chiStar p ∧ p.α = p.m + p.γ - 1 := by
  rcases h with hneg | hpos
  · linarith
  · exact ⟨hpos.2.1, hpos.2.2⟩

theorem StableWaveParameterRegime.MChi_eq_one_of_chi_neg
    {p : CMParams} (_h : StableWaveParameterRegime p) (hχ : p.χ < 0) :
    MChi p = 1 :=
  MChi_eq_one_of_chi_nonpos p (le_of_lt hχ)

def stabilitySpeedBaseline (p : CMParams) : ℝ :=
  1 + |p.χ| ^ (1 / 6 : ℝ) + (1 + |p.χ| ^ (1 / 6 : ℝ))⁻¹

/-- The paper's `c**_{χ,m,α,γ} - γ - γ⁻¹ = O(|χ|^{1/6})`
as `χ → 0`, represented by an explicit big-O bound for a threshold family. -/
def StabilitySpeedThresholdFamilyAsymptotic
    (p : CMParams) (cStarStar : ℝ → ℝ) : Prop :=
  ∃ A > 0, ∃ δ > 0, ∀ χ : ℝ, |χ| < δ →
    |cStarStar χ - (p.γ + p.γ⁻¹)| ≤ A * |χ| ^ (1 / 6 : ℝ)

lemma StabilitySpeedThresholdFamilyAsymptotic.bound
    {p : CMParams} {cStarStar : ℝ → ℝ}
    (h : StabilitySpeedThresholdFamilyAsymptotic p cStarStar) :
    ∃ A > 0, ∃ δ > 0, ∀ χ : ℝ, |χ| < δ →
      |cStarStar χ - (p.γ + p.γ⁻¹)| ≤ A * |χ| ^ (1 / 6 : ℝ) :=
  h

theorem stabilitySpeedBaseline_pos (p : CMParams) :
    0 < stabilitySpeedBaseline p := by
  unfold stabilitySpeedBaseline
  have hpow_nonneg : 0 ≤ |p.χ| ^ (1 / 6 : ℝ) :=
    Real.rpow_nonneg (abs_nonneg p.χ) _
  have hden_pos : 0 < 1 + |p.χ| ^ (1 / 6 : ℝ) := by
    linarith
  positivity

theorem one_lt_stabilitySpeedBaseline (p : CMParams) :
    1 < stabilitySpeedBaseline p := by
  unfold stabilitySpeedBaseline
  have hpow_nonneg : 0 ≤ |p.χ| ^ (1 / 6 : ℝ) :=
    Real.rpow_nonneg (abs_nonneg p.χ) _
  have hden_pos : 0 < 1 + |p.χ| ^ (1 / 6 : ℝ) := by
    linarith
  have hinv_pos : 0 < (1 + |p.χ| ^ (1 / 6 : ℝ))⁻¹ :=
    inv_pos.mpr hden_pos
  linarith

theorem stabilitySpeedBaseline_eq_cStarStar (p : CMParams) :
    stabilitySpeedBaseline p = cStarStar p := by
  simp [stabilitySpeedBaseline, cStarStar, one_div]

theorem two_le_stabilitySpeedBaseline (p : CMParams) :
    2 ≤ stabilitySpeedBaseline p := by
  rw [stabilitySpeedBaseline_eq_cStarStar]
  exact cStarStar_ge_two p

theorem two_lt_of_stabilitySpeedBaseline_lt
    {p : CMParams} {threshold : ℝ → ℝ} {c : ℝ}
    (hlower : stabilitySpeedBaseline p < threshold p.χ)
    (hc : threshold p.χ < c) :
    2 < c :=
  lt_of_le_of_lt (two_le_stabilitySpeedBaseline p) (lt_trans hlower hc)

theorem kappa_pos_of_stabilitySpeedBaseline_lt
    {p : CMParams} {threshold : ℝ → ℝ} {c : ℝ}
    (hlower : stabilitySpeedBaseline p < threshold p.χ)
    (hc : threshold p.χ < c) :
    0 < kappa c :=
  kappa_pos_of_two_lt (two_lt_of_stabilitySpeedBaseline_lt hlower hc)

theorem kappa_lt_one_of_stabilitySpeedBaseline_lt
    {p : CMParams} {threshold : ℝ → ℝ} {c : ℝ}
    (hlower : stabilitySpeedBaseline p < threshold p.χ)
    (hc : threshold p.χ < c) :
    kappa c < 1 :=
  kappa_lt_one_of_two_lt (two_lt_of_stabilitySpeedBaseline_lt hlower hc)

theorem eta_pos_of_stability_weight_hypotheses
    {p : CMParams} {threshold : ℝ → ℝ} {c eta : ℝ}
    (hlower : stabilitySpeedBaseline p < threshold p.χ)
    (hc : threshold p.χ < c) (hketa : kappa c < eta) :
    0 < eta :=
  lt_trans (kappa_pos_of_stabilitySpeedBaseline_lt hlower hc) hketa

theorem eta_lt_one_of_stability_weight_upper_bound
    (p : CMParams) {eta : ℝ}
    (heta : eta < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ))) :
    eta < 1 := by
  have hpow_nonneg : 0 ≤ |p.χ| ^ (1 / 6 : ℝ) :=
    Real.rpow_nonneg (abs_nonneg p.χ) _
  have hden_one : 1 ≤ 1 + |p.χ| ^ (1 / 6 : ℝ) := by
    linarith
  have hbound :
      1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) ≤ (1 : ℝ) := by
    simpa [one_div] using inv_le_one_of_one_le₀ hden_one
  exact lt_of_lt_of_le heta hbound

theorem eta_mem_Ioo_zero_one_of_stability_weight_hypotheses
    {p : CMParams} {threshold : ℝ → ℝ} {c eta : ℝ}
    (hlower : stabilitySpeedBaseline p < threshold p.χ)
    (hc : threshold p.χ < c) (hketa : kappa c < eta)
    (heta_upper : eta < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ))) :
    eta ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨eta_pos_of_stability_weight_hypotheses hlower hc hketa,
    eta_lt_one_of_stability_weight_upper_bound p heta_upper⟩

theorem StableWaveParameterRegime.chi_lt_one
    {p : CMParams} (h : StableWaveParameterRegime p) :
    p.χ < 1 := by
  rcases h with h | h
  · linarith [h.1]
  · exact lt_of_lt_of_le h.2.1 (chiStar_le_one p)

theorem StableWaveParameterRegime.MChi_pos
    {p : CMParams} (h : StableWaveParameterRegime p) :
    0 < MChi p :=
  MChi_pos_of_chi_lt_one p h.chi_lt_one

theorem StableWaveParameterRegime.MChi_nonneg
    {p : CMParams} (h : StableWaveParameterRegime p) :
    0 ≤ MChi p :=
  h.MChi_pos.le

theorem StableWaveParameterRegime.one_le_MChi
    {p : CMParams} (h : StableWaveParameterRegime p) :
    1 ≤ MChi p := by
  rcases h with hneg | hpos
  · simp [MChi_eq_one_of_chi_nonpos p (le_of_lt hneg.1)]
  · exact one_le_MChi_of_chi_nonneg_lt_chiStar p hpos.1 hpos.2.1

theorem Lemma_5_3.weighted_elliptic_perturbation_of_stable_tail_bounds
    (h : Lemma_5_3) {p : CMParams} {c eta : ℝ}
    (hregime : StableWaveParameterRegime p)
    (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hbound1 : HasWaveUpperTailBound p c u1)
    (hbound2 : HasWaveUpperTailBound p c u2)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2)) :
    let v := Psi (fun x => u2 x ^ p.γ - u1 x ^ p.γ) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  h.weighted_elliptic_perturbation_of_tail_bounds
    hregime.one_le_MChi heta_pos heta_one hu1 hu2 hbound1 hbound2 hclose

theorem Lemma_5_3.weighted_elliptic_perturbation_of_stable_strict_tail_bounds
    (h : Lemma_5_3) {p : CMParams} {c eta : ℝ}
    (hregime : StableWaveParameterRegime p)
    (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hbound1 : HasStrictWaveUpperTailBound p c u1)
    (hbound2 : HasStrictWaveUpperTailBound p c u2)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2)) :
    let v := Psi (fun x => u2 x ^ p.γ - u1 x ^ p.γ) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  h.weighted_elliptic_perturbation_of_stable_tail_bounds hregime
    heta_pos heta_one hu1 hu2
    hbound1.hasWaveUpperTailBound hbound2.hasWaveUpperTailBound hclose

theorem Lemma_5_3.weighted_elliptic_perturbation_of_stability_hypotheses
    (h : Lemma_5_3) {p : CMParams} {threshold : ℝ → ℝ} {c eta : ℝ}
    (hregime : StableWaveParameterRegime p)
    (hlower : stabilitySpeedBaseline p < threshold p.χ)
    (hc : threshold p.χ < c) (hketa : kappa c < eta)
    (heta_upper : eta < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)))
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hbound1 : HasStrictWaveUpperTailBound p c u1)
    (hbound2 : HasStrictWaveUpperTailBound p c u2)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2)) :
    let v := Psi (fun x => u2 x ^ p.γ - u1 x ^ p.γ) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  h.weighted_elliptic_perturbation_of_stable_strict_tail_bounds hregime
    (eta_pos_of_stability_weight_hypotheses hlower hc hketa)
    (eta_lt_one_of_stability_weight_upper_bound p heta_upper)
    hu1 hu2 hbound1 hbound2 hclose

/-- Paper1 Theorem 1.2: weighted stability of traveling waves. -/
def Theorem_1_2 : Prop :=
  ∀ p : CMParams, StableWaveParameterRegime p →
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η → η < 1 / (1 + |p.χ| ^ (1 / 6)) →
          ∀ u₀ : ℝ → ℝ,
            NonnegativeInitialDatum u₀ →
            StrictlyPositiveAtLeft u₀ →
            WeightedL2InitialCloseness η u₀ U →
            ∃ u v : ℝ → ℝ → ℝ,
              IsGlobalCauchySolutionFrom p u₀ u v ∧
              WeightedL2MovingFrameConvergence η c u U ∧
              UniformMovingFrameConvergence c u U

theorem Theorem_1_2.threshold_family
    (h : Theorem_1_2) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
        stabilitySpeedBaseline p < cStarStar p.χ := by
  rcases h p hp with ⟨cStarStar, hasymp, hlower, _hconcl⟩
  exact ⟨cStarStar, hasymp, hlower⟩

theorem Theorem_1_2.stability_package
    (h : Theorem_1_2) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η → η < 1 / (1 + |p.χ| ^ (1 / 6)) →
          ∀ u₀ : ℝ → ℝ,
            NonnegativeInitialDatum u₀ →
            StrictlyPositiveAtLeft u₀ →
            WeightedL2InitialCloseness η u₀ U →
            ∃ u v : ℝ → ℝ → ℝ,
              IsGlobalCauchySolutionFrom p u₀ u v ∧
              WeightedL2MovingFrameConvergence η c u U ∧
              UniformMovingFrameConvergence c u U :=
  h p hp

theorem Theorem_1_2.stability_package_of_remark43_tail
    (h : Theorem_1_2) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        HasRemark43TailAsymptotic p c U →
        ∀ η : ℝ, kappa c < η → η < 1 / (1 + |p.χ| ^ (1 / 6)) →
          ∀ u₀ : ℝ → ℝ,
            NonnegativeInitialDatum u₀ →
            StrictlyPositiveAtLeft u₀ →
            WeightedL2InitialCloseness η u₀ U →
            ∃ u v : ℝ → ℝ → ℝ,
              IsGlobalCauchySolutionFrom p u₀ u v ∧
              WeightedL2MovingFrameConvergence η c u U ∧
              UniformMovingFrameConvergence c u U := by
  rcases h.stability_package hp with ⟨cStarStar, hasymp, hlower, hstable⟩
  refine ⟨cStarStar, hasymp, hlower, ?_⟩
  intro c hc U V hTW hbound htail η hketa heta u₀ hu₀ hleft hclose
  have hkappa_pos : 0 < kappa c :=
    kappa_pos_of_stabilitySpeedBaseline_lt hlower hc
  have hkappa_lt_one : kappa c < 1 :=
    kappa_lt_one_of_stabilitySpeedBaseline_lt hlower hc
  exact hstable c hc U V hTW hbound
    (htail.exists_waveRightTailAsymptotic hkappa_pos hkappa_lt_one)
    η hketa heta u₀ hu₀ hleft hclose

theorem Theorem_1_2.stability_from_wave_initial_package
    (h : Theorem_1_2) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        IsCUnifBdd U →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η → η < 1 / (1 + |p.χ| ^ (1 / 6)) →
          ∃ u v : ℝ → ℝ → ℝ,
            IsGlobalCauchySolutionFrom p U u v ∧
            WeightedL2MovingFrameConvergence η c u U ∧
            UniformMovingFrameConvergence c u U := by
  rcases h.stability_package hp with ⟨cStarStar, hasymp, hlower, hstable⟩
  refine ⟨cStarStar, hasymp, hlower, ?_⟩
  intro c hc U V hTW hU hbound htail η hketa heta
  exact hstable c hc U V hTW hbound htail η hketa heta U
    (IsTravelingWave.nonnegativeInitialDatum hTW hU)
    (IsTravelingWave.strictlyPositiveAtLeft hTW)
    (WeightedL2InitialCloseness.refl η U)

theorem Theorem_1_2.stability_from_wave_initial_package_of_remark43_tail
    (h : Theorem_1_2) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        IsCUnifBdd U →
        HasStrictWaveUpperTailBound p c U →
        HasRemark43TailAsymptotic p c U →
        ∀ η : ℝ, kappa c < η → η < 1 / (1 + |p.χ| ^ (1 / 6)) →
          ∃ u v : ℝ → ℝ → ℝ,
            IsGlobalCauchySolutionFrom p U u v ∧
            WeightedL2MovingFrameConvergence η c u U ∧
            UniformMovingFrameConvergence c u U := by
  rcases h.stability_package_of_remark43_tail hp with
    ⟨cStarStar, hasymp, hlower, hstable⟩
  refine ⟨cStarStar, hasymp, hlower, ?_⟩
  intro c hc U V hTW hU hbound htail η hketa heta
  exact hstable c hc U V hTW hbound htail η hketa heta U
    (IsTravelingWave.nonnegativeInitialDatum hTW hU)
    (IsTravelingWave.strictlyPositiveAtLeft hTW)
    (WeightedL2InitialCloseness.refl η U)

theorem Theorem_1_2.stability_from_second_wave_initial_package
    (h : Theorem_1_2) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        IsCUnifBdd U₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U₁) →
        ∀ η : ℝ, kappa c < η → η < 1 / (1 + |p.χ| ^ (1 / 6)) →
          WeightedL2InitialCloseness η U₂ U₁ →
          ∃ u v : ℝ → ℝ → ℝ,
            IsGlobalCauchySolutionFrom p U₂ u v ∧
            WeightedL2MovingFrameConvergence η c u U₁ ∧
            UniformMovingFrameConvergence c u U₁ := by
  rcases h.stability_package hp with ⟨cStarStar, hasymp, hlower, hstable⟩
  refine ⟨cStarStar, hasymp, hlower, ?_⟩
  intro c hc U₁ V₁ U₂ V₂ hTW₁ hTW₂ hU₂ hbound₁ htail₁ η hketa heta hclose
  exact hstable c hc U₁ V₁ hTW₁ hbound₁ htail₁ η hketa heta U₂
    (IsTravelingWave.nonnegativeInitialDatum hTW₂ hU₂)
    (IsTravelingWave.strictlyPositiveAtLeft hTW₂)
    hclose

theorem Theorem_1_2.stability_from_second_wave_initial_package_of_remark43_tail
    (h : Theorem_1_2) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        IsCUnifBdd U₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasRemark43TailAsymptotic p c U₁ →
        ∀ η : ℝ, kappa c < η → η < 1 / (1 + |p.χ| ^ (1 / 6)) →
          WeightedL2InitialCloseness η U₂ U₁ →
          ∃ u v : ℝ → ℝ → ℝ,
            IsGlobalCauchySolutionFrom p U₂ u v ∧
            WeightedL2MovingFrameConvergence η c u U₁ ∧
            UniformMovingFrameConvergence c u U₁ := by
  rcases h.stability_package_of_remark43_tail hp with
    ⟨cStarStar, hasymp, hlower, hstable⟩
  refine ⟨cStarStar, hasymp, hlower, ?_⟩
  intro c hc U₁ V₁ U₂ V₂ hTW₁ hTW₂ hU₂ hbound₁ htail₁ η hketa heta hclose
  exact hstable c hc U₁ V₁ hTW₁ hbound₁ htail₁ η hketa heta U₂
    (IsTravelingWave.nonnegativeInitialDatum hTW₂ hU₂)
    (IsTravelingWave.strictlyPositiveAtLeft hTW₂)
    hclose

theorem Theorem_1_2.positive_existing_wave_stability_package
    (hstability : Theorem_1_2) (hexistence : Theorem_1_1)
    {p : CMParams}
    (halpha : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p)) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
        ∃ U V : ℝ → ℝ,
          IsTravelingWave p c U V ∧
          HasStrictWaveUpperTailBound p c U ∧
          (∀ η : ℝ, kappa c < η →
            η < 1 / (1 + |p.χ| ^ (1 / 6)) →
            ∀ u₀ : ℝ → ℝ,
              NonnegativeInitialDatum u₀ →
              StrictlyPositiveAtLeft u₀ →
              WeightedL2InitialCloseness η u₀ U →
              ∃ u v : ℝ → ℝ → ℝ,
                IsGlobalCauchySolutionFrom p u₀ u v ∧
                WeightedL2MovingFrameConvergence η c u U ∧
                UniformMovingFrameConvergence c u U) := by
  have hp : StableWaveParameterRegime p :=
    StableWaveParameterRegime.of_positive hχ_nonneg
      (lt_of_lt_of_le hχ_small (min_le_right _ _)) halpha
  rcases hstability.stability_package hp with
    ⟨cStarStar, hasymp, hlower, hstable⟩
  refine ⟨cStarStar, hasymp, hlower, ?_⟩
  intro c hc
  have hc2 : 2 < c :=
    two_lt_of_stabilitySpeedBaseline_lt hlower hc
  rcases hexistence.positive_wave_with_stability_tail_data
      halpha hχ_nonneg hχ_small hc2 with
    ⟨U, V, hTW, hbound, htail⟩
  exact ⟨U, V, hTW, hbound, hstable c hc U V hTW hbound htail⟩

theorem Theorem_1_2.positive_existing_wave_stability_package_with_ratio_limit
    (hstability : Theorem_1_2) (hexistence : Theorem_1_1)
    {p : CMParams}
    (halpha : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p)) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
        ∃ U V : ℝ → ℝ,
          IsTravelingWave p c U V ∧
          HasStrictWaveUpperTailBound p c U ∧
          Tendsto (fun x => U x / Real.exp (-(kappa c) * x)) atTop (𝓝 1) ∧
          (∀ η : ℝ, kappa c < η →
            η < 1 / (1 + |p.χ| ^ (1 / 6)) →
            ∀ u₀ : ℝ → ℝ,
              NonnegativeInitialDatum u₀ →
              StrictlyPositiveAtLeft u₀ →
              WeightedL2InitialCloseness η u₀ U →
              ∃ u v : ℝ → ℝ → ℝ,
                IsGlobalCauchySolutionFrom p u₀ u v ∧
                WeightedL2MovingFrameConvergence η c u U ∧
                UniformMovingFrameConvergence c u U) := by
  have hp : StableWaveParameterRegime p :=
    StableWaveParameterRegime.of_positive hχ_nonneg
      (lt_of_lt_of_le hχ_small (min_le_right _ _)) halpha
  rcases hstability.stability_package hp with
    ⟨cStarStar, hasymp, hlower, hstable⟩
  refine ⟨cStarStar, hasymp, hlower, ?_⟩
  intro c hc
  have hc2 : 2 < c :=
    two_lt_of_stabilitySpeedBaseline_lt hlower hc
  rcases hexistence.positive_wave_with_stability_tail_data
      halpha hχ_nonneg hχ_small hc2 with
    ⟨U, V, hTW, hbound, κ₁, hκ₁_gt, _hκ₁_lt, htail⟩
  exact
    ⟨U, V, hTW, hbound, htail.ratio_tendsto_one hκ₁_gt,
      hstable c hc U V hTW hbound
        ⟨κ₁, hκ₁_gt, _hκ₁_lt, htail⟩⟩

/-- Paper1 Theorem 1.3: uniqueness of traveling waves with the prescribed right tail. -/
def Theorem_1_3 : Prop :=
  ∀ p : CMParams, StableWaveParameterRegime p →
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasStrictWaveUpperTailBound p c U₂ →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧
          HasWaveRightTailAsymptotic c κ₁ U₁ ∧
          HasWaveRightTailAsymptotic c κ₁ U₂) →
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x)

theorem Theorem_1_3.threshold_family
    (h : Theorem_1_3) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
        stabilitySpeedBaseline p < cStarStar p.χ := by
  rcases h p hp with ⟨cStarStar, hasymp, hlower, _hconcl⟩
  exact ⟨cStarStar, hasymp, hlower⟩

theorem Theorem_1_3.uniqueness_package
    (h : Theorem_1_3) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasStrictWaveUpperTailBound p c U₂ →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧
          HasWaveRightTailAsymptotic c κ₁ U₁ ∧
          HasWaveRightTailAsymptotic c κ₁ U₂) →
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) :=
  h p hp

theorem Theorem_1_3.uniqueness_package_of_remark43_tail
    (h : Theorem_1_3) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasStrictWaveUpperTailBound p c U₂ →
        HasRemark43TailAsymptotic p c U₁ →
        HasRemark43TailAsymptotic p c U₂ →
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) := by
  rcases h.uniqueness_package hp with ⟨cStarStar, hasymp, hlower, huniq⟩
  refine ⟨cStarStar, hasymp, hlower, ?_⟩
  intro c hc U₁ V₁ U₂ V₂ hTW₁ hTW₂ hbound₁ hbound₂ htail₁ htail₂
  have hkappa_pos : 0 < kappa c :=
    kappa_pos_of_stabilitySpeedBaseline_lt hlower hc
  have hkappa_lt_one : kappa c < 1 :=
    kappa_lt_one_of_stabilitySpeedBaseline_lt hlower hc
  exact huniq c hc U₁ V₁ U₂ V₂ hTW₁ hTW₂ hbound₁ hbound₂
    (htail₁.exists_common_waveRightTailAsymptotic htail₂ hkappa_pos hkappa_lt_one)

theorem Theorem_1_3.uniqueness_package_of_forall_kappaOne_range_tail
    (h : Theorem_1_3) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasStrictWaveUpperTailBound p c U₂ →
        (∀ κ₁, kappa c < κ₁ →
          κ₁ <
            min ((1 + p.α) * kappa c)
              (min (p.m * kappa c + 1 / 2) 1) →
          HasWaveRightTailAsymptotic c κ₁ U₁) →
        (∀ κ₁, kappa c < κ₁ →
          κ₁ <
            min ((1 + p.α) * kappa c)
              (min (p.m * kappa c + 1 / 2) 1) →
          HasWaveRightTailAsymptotic c κ₁ U₂) →
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) := by
  rcases h.uniqueness_package hp with ⟨cStarStar, hasymp, hlower, huniq⟩
  refine ⟨cStarStar, hasymp, hlower, ?_⟩
  intro c hc U₁ V₁ U₂ V₂ hTW₁ hTW₂ hbound₁ hbound₂ htail₁ htail₂
  have hkappa_pos : 0 < kappa c :=
    kappa_pos_of_stabilitySpeedBaseline_lt hlower hc
  have hkappa_lt_one : kappa c < 1 :=
    kappa_lt_one_of_stabilitySpeedBaseline_lt hlower hc
  exact huniq c hc U₁ V₁ U₂ V₂ hTW₁ hTW₂ hbound₁ hbound₂
    (exists_common_waveRightTailAsymptotic_of_forall_kappaOne_range
      htail₁ htail₂ hkappa_pos hkappa_lt_one)

theorem Theorem_1_3.uniqueness_at_admissible_threshold
    {p : CMParams} {cStarStar : ℝ → ℝ}
    (hthreshold :
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasStrictWaveUpperTailBound p c U₂ →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧
          HasWaveRightTailAsymptotic c κ₁ U₁ ∧
          HasWaveRightTailAsymptotic c κ₁ U₂) →
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x))
    {c : ℝ} (hc : cStarStar p.χ < c)
    {U₁ V₁ U₂ V₂ : ℝ → ℝ}
    (hTW₁ : IsTravelingWave p c U₁ V₁)
    (hTW₂ : IsTravelingWave p c U₂ V₂)
    (hbound₁ : HasStrictWaveUpperTailBound p c U₁)
    (hbound₂ : HasStrictWaveUpperTailBound p c U₂)
    (htail :
      ∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧
        HasWaveRightTailAsymptotic c κ₁ U₁ ∧
        HasWaveRightTailAsymptotic c κ₁ U₂) :
    (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) :=
  hthreshold.2.2 c hc U₁ V₁ U₂ V₂
    hTW₁ hTW₂ hbound₁ hbound₂ htail

theorem Theorem_1_3.uniqueness_at_admissible_threshold_of_remark43_tail
    {p : CMParams} {cStarStar : ℝ → ℝ}
    (hthreshold :
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasStrictWaveUpperTailBound p c U₂ →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧
          HasWaveRightTailAsymptotic c κ₁ U₁ ∧
          HasWaveRightTailAsymptotic c κ₁ U₂) →
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x))
    {c : ℝ} (hc : cStarStar p.χ < c)
    {U₁ V₁ U₂ V₂ : ℝ → ℝ}
    (hTW₁ : IsTravelingWave p c U₁ V₁)
    (hTW₂ : IsTravelingWave p c U₂ V₂)
    (hbound₁ : HasStrictWaveUpperTailBound p c U₁)
    (hbound₂ : HasStrictWaveUpperTailBound p c U₂)
    (htail₁ : HasRemark43TailAsymptotic p c U₁)
    (htail₂ : HasRemark43TailAsymptotic p c U₂) :
    (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) := by
  have hkappa_pos : 0 < kappa c :=
    kappa_pos_of_stabilitySpeedBaseline_lt hthreshold.2.1 hc
  have hkappa_lt_one : kappa c < 1 :=
    kappa_lt_one_of_stabilitySpeedBaseline_lt hthreshold.2.1 hc
  exact Theorem_1_3.uniqueness_at_admissible_threshold
    hthreshold hc hTW₁ hTW₂ hbound₁ hbound₂
    (htail₁.exists_common_waveRightTailAsymptotic htail₂ hkappa_pos hkappa_lt_one)

theorem Theorem_1_3.uniqueness_at_admissible_threshold_of_forall_kappaOne_range_tail
    {p : CMParams} {cStarStar : ℝ → ℝ}
    (hthreshold :
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasStrictWaveUpperTailBound p c U₂ →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧
          HasWaveRightTailAsymptotic c κ₁ U₁ ∧
          HasWaveRightTailAsymptotic c κ₁ U₂) →
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x))
    {c : ℝ} (hc : cStarStar p.χ < c)
    {U₁ V₁ U₂ V₂ : ℝ → ℝ}
    (hTW₁ : IsTravelingWave p c U₁ V₁)
    (hTW₂ : IsTravelingWave p c U₂ V₂)
    (hbound₁ : HasStrictWaveUpperTailBound p c U₁)
    (hbound₂ : HasStrictWaveUpperTailBound p c U₂)
    (htail₁ :
      ∀ κ₁, kappa c < κ₁ →
        κ₁ <
          min ((1 + p.α) * kappa c)
            (min (p.m * kappa c + 1 / 2) 1) →
        HasWaveRightTailAsymptotic c κ₁ U₁)
    (htail₂ :
      ∀ κ₁, kappa c < κ₁ →
        κ₁ <
          min ((1 + p.α) * kappa c)
            (min (p.m * kappa c + 1 / 2) 1) →
        HasWaveRightTailAsymptotic c κ₁ U₂) :
    (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) := by
  have hkappa_pos : 0 < kappa c :=
    kappa_pos_of_stabilitySpeedBaseline_lt hthreshold.2.1 hc
  have hkappa_lt_one : kappa c < 1 :=
    kappa_lt_one_of_stabilitySpeedBaseline_lt hthreshold.2.1 hc
  exact Theorem_1_3.uniqueness_at_admissible_threshold
    hthreshold hc hTW₁ hTW₂ hbound₁ hbound₂
    (exists_common_waveRightTailAsymptotic_of_forall_kappaOne_range
      htail₁ htail₂ hkappa_pos hkappa_lt_one)

theorem Theorem_1_3.exists_threshold_with_uniqueness_at_speed
    (h : Theorem_1_3) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasStrictWaveUpperTailBound p c U₂ →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧
          HasWaveRightTailAsymptotic c κ₁ U₁ ∧
          HasWaveRightTailAsymptotic c κ₁ U₂) →
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) :=
  h.uniqueness_package hp

theorem Theorem_1_3.exists_threshold_with_uniqueness_at_speed_of_remark43_tail
    (h : Theorem_1_3) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasStrictWaveUpperTailBound p c U₂ →
        HasRemark43TailAsymptotic p c U₁ →
        HasRemark43TailAsymptotic p c U₂ →
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) :=
  h.uniqueness_package_of_remark43_tail hp

theorem Theorem_1_3.exists_threshold_with_uniqueness_at_speed_of_forall_kappaOne_range_tail
    (h : Theorem_1_3) {p : CMParams} (hp : StableWaveParameterRegime p) :
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasStrictWaveUpperTailBound p c U₂ →
        (∀ κ₁, kappa c < κ₁ →
          κ₁ <
            min ((1 + p.α) * kappa c)
              (min (p.m * kappa c + 1 / 2) 1) →
          HasWaveRightTailAsymptotic c κ₁ U₁) →
        (∀ κ₁, kappa c < κ₁ →
          κ₁ <
            min ((1 + p.α) * kappa c)
              (min (p.m * kappa c + 1 / 2) 1) →
          HasWaveRightTailAsymptotic c κ₁ U₂) →
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) :=
  h.uniqueness_package_of_forall_kappaOne_range_tail hp

end

end ShenWork.Paper1
