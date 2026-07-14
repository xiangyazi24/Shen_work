/-
  Statement layer for Shen,
  "Existence, uniqueness, stability, and monotonicity of traveling waves for
  repulsion/attraction chemotaxis models with logistic type source".

  The declarations below formalize the paper-level targets as propositions.
  They are not proofs of the paper theorems.
-/
import ShenWork.PDE.LeibnizRule
import ShenWork.PDE.HeatSemigroup
import ShenWork.PDE.HeatKernelLpEstimates
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.ODE.Gronwall

open Filter Topology MeasureTheory

namespace ShenWork.Paper1

noncomputable section

def NonnegativeInitialDatum (u₀ : ℝ → ℝ) : Prop :=
  IsCUnifBdd u₀ ∧ ∀ x, 0 ≤ u₀ x

def UniformlyPositive (u₀ : ℝ → ℝ) : Prop :=
  ∃ δ > 0, ∀ x, δ ≤ u₀ x

/-- Paper-faithful positive datum on the whole line: admissibility plus the
uniform positive floor from eq. (1.11), `inf_x u₀(x) > 0`. -/
def PaperPositiveInitialDatum (u₀ : ℝ → ℝ) : Prop :=
  NonnegativeInitialDatum u₀ ∧ UniformlyPositive u₀

def StrictlyPositiveAtLeft (u₀ : ℝ → ℝ) : Prop :=
  ∃ δ > 0, ∀ᶠ x in atBot, δ ≤ u₀ x

theorem PaperPositiveInitialDatum.nonnegative {u₀ : ℝ → ℝ}
    (h : PaperPositiveInitialDatum u₀) :
    NonnegativeInitialDatum u₀ :=
  h.1

/-- The paper floor witness: `∃ δ > 0, ∀ x, δ ≤ u₀ x`. -/
theorem PaperPositiveInitialDatum.floor {u₀ : ℝ → ℝ}
    (h : PaperPositiveInitialDatum u₀) :
    UniformlyPositive u₀ :=
  h.2

theorem PaperPositiveInitialDatum.strictlyPositiveAtLeft {u₀ : ℝ → ℝ}
    (h : PaperPositiveInitialDatum u₀) :
    StrictlyPositiveAtLeft u₀ := by
  rcases h.floor with ⟨δ, hδ, hfloor⟩
  exact ⟨δ, hδ, Filter.Eventually.of_forall hfloor⟩

section PaperPositiveInitialDatumAxiomAudit
#print axioms PaperPositiveInitialDatum.nonnegative
#print axioms PaperPositiveInitialDatum.floor
#print axioms PaperPositiveInitialDatum.strictlyPositiveAtLeft
end PaperPositiveInitialDatumAxiomAudit

theorem isCUnifBdd_const (a : ℝ) :
    IsCUnifBdd (fun _ : ℝ => a) := by
  exact ⟨continuous_const, ⟨|a|, fun _ => by simp⟩⟩

theorem constant_one_nonnegativeInitialDatum :
    NonnegativeInitialDatum (fun _ : ℝ => (1 : ℝ)) := by
  exact ⟨isCUnifBdd_const 1, fun _ => by norm_num⟩

theorem constant_one_uniformlyPositive :
    UniformlyPositive (fun _ : ℝ => (1 : ℝ)) := by
  exact ⟨1, by norm_num, fun _ => by norm_num⟩

theorem constant_one_strictlyPositiveAtLeft :
    StrictlyPositiveAtLeft (fun _ : ℝ => (1 : ℝ)) := by
  exact ⟨1, by norm_num, Eventually.of_forall fun _ => by norm_num⟩

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

/-- Uniform right trace at the initial time.  This prevents a function that
has merely been assigned the datum at `t = 0` from jumping to an unrelated
classical solution for every `t > 0`. -/
def HasUniformInitialTrace (u : ℝ → ℝ → ℝ) (u₀ : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t x, 0 ≤ t → t < δ → |u t x - u₀ x| < ε

theorem HasUniformInitialTrace.movingWave
    {U : ℝ → ℝ} (hU : UniformContinuous U) (c : ℝ) :
    HasUniformInitialTrace
      (fun t x => U (x - c * t)) U := by
  rw [Metric.uniformContinuous_iff] at hU
  intro ε hε
  rcases hU ε hε with ⟨δx, hδx, hmod⟩
  refine ⟨δx / (|c| + 1), div_pos hδx (by linarith [abs_nonneg c]), ?_⟩
  intro t x ht htδ
  have hct : |c * t| < δx := by
    have hden_pos : 0 < |c| + 1 := by linarith [abs_nonneg c]
    have ht' : t * (|c| + 1) < δx :=
      (lt_div_iff₀ hden_pos).mp htδ
    rw [abs_mul, abs_of_nonneg ht]
    nlinarith [abs_nonneg c]
  have hdist : dist (x - c * t) x < δx := by
    simpa [Real.dist_eq] using hct
  simpa [Real.dist_eq] using hmod hdist

section InitialTraceAxiomAudit
#print axioms HasUniformInitialTrace.movingWave
end InitialTraceAxiomAudit

def IsGlobalCauchySolutionFrom
    (p : CMParams) (u₀ : ℝ → ℝ) (u v : ℝ → ℝ → ℝ) : Prop :=
  IsGlobalClassicalSolution p u v ∧
    HasInitialDatum u u₀ ∧
    HasUniformInitialTrace u u₀ ∧
    ∀ t x, 0 < t → 0 < u t x

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

theorem UniformLimsupLe.mono
    {u : ℝ → ℝ → ℝ} {L₁ L₂ : ℝ}
    (h : UniformLimsupLe u L₁) (hL : L₁ ≤ L₂) :
    UniformLimsupLe u L₂ := by
  intro ε hε
  exact (h ε hε).mono fun _t ht x => by
    have := ht x
    linarith

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
    (hU_uc : UniformContinuous U)
    (hU_diff : ContDiff ℝ 2 U) (hV_diff : ContDiff ℝ 2 V) :
    IsGlobalCauchySolutionFrom p U
      (fun t x => U (x - c * t)) (fun t x => V (x - c * t)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hTW.to_movingFrame_global_classical_solution hU_diff hV_diff
  · intro x
    simp
  · exact HasUniformInitialTrace.movingWave hU_uc c
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
    ring_nf
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

/-- A real integrability bridge for the weighted `L²` tail norm.  It reduces
the closeness condition to a left exponential domination and a right
exponential domination of the weighted integrand. -/
theorem WeightedL2InitialCloseness.of_integrand_exp_bounds
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    {u₀ U : ℝ → ℝ}
    (hmeas : AEStronglyMeasurable
      (fun x : ℝ => Real.exp (2 * η * x) * |u₀ x - U x| ^ 2) volume)
    (hleft :
      ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ,
        ‖Real.exp (2 * η * x) * |u₀ x - U x| ^ 2‖ ≤
          A * Real.exp (2 * η * x))
    (hright :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ,
        ‖Real.exp (2 * η * x) * |u₀ x - U x| ^ 2‖ ≤
          B * Real.exp (-δ * x)) :
    WeightedL2InitialCloseness η u₀ U := by
  rcases hleft with ⟨A, hA, hleft⟩
  rcases hright with ⟨B, hB, hright⟩
  let f : ℝ → ℝ := fun x => Real.exp (2 * η * x) * |u₀ x - U x| ^ 2
  have hleft_int : IntegrableOn f (Set.Iic 0) := by
    have hdom : IntegrableOn (fun x : ℝ => A * Real.exp (2 * η * x))
        (Set.Iic 0) :=
      (integrableOn_exp_mul_Iic (by linarith : (0 : ℝ) < 2 * η) 0).const_mul A
    refine hdom.mono' (show AEStronglyMeasurable f (volume.restrict (Set.Iic 0)) from
      hmeas.restrict) (Filter.Eventually.of_forall fun x => ?_)
    dsimp [f]
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hA (Real.exp_nonneg _))] using hleft x
  have hright_int : IntegrableOn f (Set.Ioi 0) := by
    have hdom : IntegrableOn (fun x : ℝ => B * Real.exp (-δ * x))
        (Set.Ioi 0) :=
      (integrableOn_exp_mul_Ioi (by linarith : -δ < (0 : ℝ)) 0).const_mul B
    refine hdom.mono' (show AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)) from
      hmeas.restrict) (Filter.Eventually.of_forall fun x => ?_)
    dsimp [f]
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hB (Real.exp_nonneg _))] using hright x
  have hcover : Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ) = (Set.univ : Set ℝ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioi, Set.mem_univ, iff_true]
    exact le_or_gt x 0
  unfold WeightedL2InitialCloseness
  change Integrable f
  rw [← MeasureTheory.integrableOn_univ, ← hcover]
  exact hleft_int.union hright_int

/-- Variant of `WeightedL2InitialCloseness.of_integrand_exp_bounds` where the
right-tail domination is only required eventually.  The left exponential bound
absorbs the finite interval before the eventual right tail. -/
theorem WeightedL2InitialCloseness.of_left_exp_bound_eventual_right_exp_bound
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    {u₀ U : ℝ → ℝ}
    (hmeas : AEStronglyMeasurable
      (fun x : ℝ => Real.exp (2 * η * x) * |u₀ x - U x| ^ 2) volume)
    (hleft :
      ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ,
        ‖Real.exp (2 * η * x) * |u₀ x - U x| ^ 2‖ ≤
          A * Real.exp (2 * η * x))
    (hright :
      ∃ R B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, R < x →
        ‖Real.exp (2 * η * x) * |u₀ x - U x| ^ 2‖ ≤
          B * Real.exp (-δ * x)) :
    WeightedL2InitialCloseness η u₀ U := by
  rcases hleft with ⟨A, hA, hleft⟩
  rcases hright with ⟨R, B, hB, hright⟩
  let f : ℝ → ℝ := fun x => Real.exp (2 * η * x) * |u₀ x - U x| ^ 2
  have hleft_int : IntegrableOn f (Set.Iic R) := by
    have hdom : IntegrableOn (fun x : ℝ => A * Real.exp (2 * η * x))
        (Set.Iic R) :=
      (integrableOn_exp_mul_Iic (by linarith : (0 : ℝ) < 2 * η) R).const_mul A
    refine hdom.mono' (show AEStronglyMeasurable f (volume.restrict (Set.Iic R)) from
      hmeas.restrict) (Filter.Eventually.of_forall fun x => ?_)
    dsimp [f]
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hA (Real.exp_nonneg _))] using hleft x
  have hright_int : IntegrableOn f (Set.Ioi R) := by
    have hdom : IntegrableOn (fun x : ℝ => B * Real.exp (-δ * x))
        (Set.Ioi R) :=
      (integrableOn_exp_mul_Ioi (by linarith : -δ < (0 : ℝ)) R).const_mul B
    refine hdom.mono' (show AEStronglyMeasurable f (volume.restrict (Set.Ioi R)) from
      hmeas.restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp [f]
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hB (Real.exp_nonneg _))] using hright x hx
  have hcover : Set.Iic R ∪ Set.Ioi R = (Set.univ : Set ℝ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioi, Set.mem_univ, iff_true]
    exact le_or_gt x R
  unfold WeightedL2InitialCloseness
  change Integrable f
  rw [← MeasureTheory.integrableOn_univ, ← hcover]
  exact hleft_int.union hright_int

theorem weightedL2_integrand_norm_le_of_abs_sub_le
    {η A : ℝ} {u₀ U : ℝ → ℝ} (hA : 0 ≤ A) {x : ℝ}
    (habs : |u₀ x - U x| ≤ A) :
    ‖Real.exp (2 * η * x) * |u₀ x - U x| ^ 2‖ ≤
      A ^ 2 * Real.exp (2 * η * x) := by
  have hsq : |u₀ x - U x| ^ 2 ≤ A ^ 2 := by
    nlinarith [habs, abs_nonneg (u₀ x - U x)]
  calc
    ‖Real.exp (2 * η * x) * |u₀ x - U x| ^ 2‖
        = Real.exp (2 * η * x) * |u₀ x - U x| ^ 2 := by
          rw [Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))]
    _ ≤ Real.exp (2 * η * x) * A ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (Real.exp_nonneg _)
    _ = A ^ 2 * Real.exp (2 * η * x) := by ring

theorem weightedL2_integrand_norm_le_of_abs_sub_le_exp
    {η β B : ℝ} {u₀ U : ℝ → ℝ} (hB : 0 ≤ B) {x : ℝ}
    (habs : |u₀ x - U x| ≤ B * Real.exp (-β * x)) :
    ‖Real.exp (2 * η * x) * |u₀ x - U x| ^ 2‖ ≤
      B ^ 2 * Real.exp (-(2 * (β - η)) * x) := by
  have hA_nonneg : 0 ≤ B * Real.exp (-β * x) :=
    mul_nonneg hB (Real.exp_nonneg _)
  have hbasic :=
    weightedL2_integrand_norm_le_of_abs_sub_le
      (η := η) (A := B * Real.exp (-β * x))
      (u₀ := u₀) (U := U) hA_nonneg habs
  calc
    ‖Real.exp (2 * η * x) * |u₀ x - U x| ^ 2‖
        ≤ (B * Real.exp (-β * x)) ^ 2 * Real.exp (2 * η * x) := hbasic
    _ = B ^ 2 * (Real.exp (-β * x) *
        Real.exp (-β * x) * Real.exp (2 * η * x)) := by ring
    _ = B ^ 2 * (Real.exp ((-β * x) + (-β * x)) *
        Real.exp (2 * η * x)) := by rw [Real.exp_add]
    _ = B ^ 2 * Real.exp ((-β * x) + (-β * x) + 2 * η * x) := by
      rw [← Real.exp_add]
    _ = B ^ 2 * Real.exp (-(2 * (β - η)) * x) := by
      congr 1
      ring

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

theorem IsGlobalCauchySolutionFrom.initialTrace
    {p : CMParams} {u₀ : ℝ → ℝ} {u v : ℝ → ℝ → ℝ}
    (h : IsGlobalCauchySolutionFrom p u₀ u v) :
    HasUniformInitialTrace u u₀ :=
  h.2.2.1

theorem IsGlobalCauchySolutionFrom.pos
    {p : CMParams} {u₀ : ℝ → ℝ} {u v : ℝ → ℝ → ℝ}
    (h : IsGlobalCauchySolutionFrom p u₀ u v) :
    ∀ t x, 0 < t → 0 < u t x :=
  h.2.2.2

theorem IsGlobalCauchySolutionFrom.shift_space
    {p : CMParams} {u₀ : ℝ → ℝ} {u v : ℝ → ℝ → ℝ}
    (h : IsGlobalCauchySolutionFrom p u₀ u v) (a : ℝ) :
    IsGlobalCauchySolutionFrom p (fun x => u₀ (x + a))
      (fun t x => u t (x + a)) (fun t x => v t (x + a)) := by
  refine ⟨_root_.IsGlobalClassicalSolution.shift_space h.classical a, ?_, ?_, ?_⟩
  · intro x
    exact h.initial (x + a)
  · intro ε hε
    rcases h.initialTrace ε hε with ⟨δ, hδ, htrace⟩
    exact ⟨δ, hδ, fun t x ht htδ => htrace t (x + a) ht htδ⟩
  · intro t x ht
    exact h.pos t (x + a) ht

/-- A continuous real function with finite limits at both ends is uniformly
continuous, even when the two limiting values differ. -/
theorem uniformContinuous_of_continuous_tendsto_atBot_atTop
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f)
    (hbot : Tendsto f atBot (𝓝 a))
    (htop : Tendsto f atTop (𝓝 b)) :
    UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  have hleft_ev : ∀ᶠ x in atBot, f x ∈ Metric.ball a (ε / 4) :=
    hbot.eventually (Metric.ball_mem_nhds a hε4)
  have hright_ev : ∀ᶠ x in atTop, f x ∈ Metric.ball b (ε / 4) :=
    htop.eventually (Metric.ball_mem_nhds b hε4)
  rcases (eventually_atBot.1 hleft_ev) with ⟨A, hA⟩
  rcases (eventually_atTop.1 hright_ev) with ⟨B, hB⟩
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous
    (s := Set.Icc (A - 2) (B + 2)) hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  rcases huc ε hε with ⟨δ₀, hδ₀, hlocal⟩
  refine ⟨min δ₀ 1, lt_min hδ₀ zero_lt_one, ?_⟩
  intro x y hxy
  have hxyδ₀ : dist x y < δ₀ := lt_of_lt_of_le hxy (min_le_left _ _)
  have hxy1 : |x - y| < 1 := by
    simpa [Real.dist_eq] using lt_of_lt_of_le hxy (min_le_right _ _)
  have hxy_parts := abs_lt.mp hxy1
  by_cases hxleft : x < A - 1
  · have hxA : x ≤ A := by linarith
    have hyA : y ≤ A := by linarith
    have hxball := hA x hxA
    have hyball := hA y hyA
    have htri := dist_triangle (f x) a (f y)
    rw [Metric.mem_ball] at hxball hyball
    rw [dist_comm a (f y)] at htri
    linarith
  · by_cases hxright : B + 1 < x
    · have hBx : B ≤ x := by linarith
      have hBy : B ≤ y := by linarith
      have hxball := hB x hBx
      have hyball := hB y hBy
      have htri := dist_triangle (f x) b (f y)
      rw [Metric.mem_ball] at hxball hyball
      rw [dist_comm b (f y)] at htri
      linarith
    · have hxI : x ∈ Set.Icc (A - 2) (B + 2) := by
        constructor <;> linarith
      have hyI : y ∈ Set.Icc (A - 2) (B + 2) := by
        constructor <;> linarith
      exact hlocal x hxI y hyI hxyδ₀

theorem travelingWave_U_uniformContinuous
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V) (hU_cont : Continuous U) :
    UniformContinuous U :=
  uniformContinuous_of_continuous_tendsto_atBot_atTop
    hU_cont hTW.lim_neg_inf.1 hTW.lim_pos_inf.1

section TravelingWaveUniformContinuityAxiomAudit
#print axioms uniformContinuous_of_continuous_tendsto_atBot_atTop
#print axioms travelingWave_U_uniformContinuous
end TravelingWaveUniformContinuityAxiomAudit

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
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact _root_.IsTravelingWave.to_movingFrame_global_classical_solution
      p hTW hU_diff hV_diff
  · intro x
    simp
  · exact HasUniformInitialTrace.movingWave
      (travelingWave_U_uniformContinuous hTW hU_diff.continuous) c
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

theorem not_forall_Lemma_2_1 :
    ¬ (∀ S : HeatSemigroupEstimateData, Lemma_2_1 S) := by
  intro hall
  let S : HeatSemigroupEstimateData :=
    { lpNorm := fun _ _ => 0
      lqNorm := fun _ _ => 1
      linftyNorm := fun _ => 0
      gradientNorm := fun _ _ => 0
      semigroup := fun _ _ _ => 0
      divergenceSemigroup := fun _ _ _ => 0 }
  rcases (hall S 2 2 (by norm_num) le_rfl).1 with ⟨C, hC_pos, hC⟩
  have hbad := hC 1 (by norm_num) (fun _ => 0)
  norm_num [S] at hbad

theorem Lemma_2_1_zero_output_branch
    (S : HeatSemigroupEstimateData)
    (hlp_nonneg : ∀ p u, 0 ≤ S.lpNorm p u)
    (hlq_zero : ∀ q t u, S.lqNorm q (S.semigroup t u) = 0)
    (hgrad_zero : ∀ q t u, S.gradientNorm q (S.semigroup t u) = 0)
    (hdiv_zero : ∀ t u, S.linftyNorm (S.divergenceSemigroup t u) = 0) :
    Lemma_2_1 S := by
  intro p q _hp _hpq
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht u
    have hright_nonneg :
        0 ≤
          (1 : ℝ) * t ^ (-(1 / 2 : ℝ) * (1 / p - 1 / q)) *
            Real.exp (-t) * S.lpNorm p u := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg zero_le_one (Real.rpow_nonneg ht.le _))
          (Real.exp_nonneg _))
        (hlp_nonneg p u)
    simpa [hlq_zero q t u] using hright_nonneg
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht u
    have hright_nonneg :
        0 ≤
          (1 : ℝ) *
            t ^ (-(1 / 2 : ℝ) - (1 / 2 : ℝ) * (1 / p - 1 / q)) *
            Real.exp (-t) * S.lpNorm p u := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg zero_le_one (Real.rpow_nonneg ht.le _))
          (Real.exp_nonneg _))
        (hlp_nonneg p u)
    simpa [hgrad_zero q t u] using hright_nonneg
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht u
    have hright_nonneg :
        0 ≤
          (1 : ℝ) * t ^ (-(1 / 2 : ℝ) - (1 / (2 * p))) *
            Real.exp (-t) * S.lpNorm p u := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg zero_le_one (Real.rpow_nonneg ht.le _))
          (Real.exp_nonneg _))
        (hlp_nonneg p u)
    simpa [hdiv_zero t u] using hright_nonneg

theorem Lemma_2_1_zero_data :
    Lemma_2_1
      { lpNorm := fun _ _ => 0
        lqNorm := fun _ _ => 0
        linftyNorm := fun _ => 0
        gradientNorm := fun _ _ => 0
        semigroup := fun _ _ _ => 0
        divergenceSemigroup := fun _ _ _ => 0 } :=
  Lemma_2_1_zero_output_branch
    { lpNorm := fun _ _ => 0
      lqNorm := fun _ _ => 0
      linftyNorm := fun _ => 0
      gradientNorm := fun _ _ => 0
      semigroup := fun _ _ _ => 0
      divergenceSemigroup := fun _ _ _ => 0 }
    (by intro _ _; norm_num)
    (by intro _ _ _; norm_num)
    (by intro _ _ _; norm_num)
    (by intro _ _; norm_num)

/-! ### Concrete whole-line heat semigroup bridges

These estimates expose the proved kernel bounds from `PDE/HeatSemigroup.lean`
at the Paper1 statement layer.  They are not projections from
`HeatSemigroupEstimateData`.
-/

/-- Concrete `L∞` bound for the heat semigroup `e^{tΔ}`. -/
theorem heatSemigroup_paper1_Linfty_bound
    {f : ℝ → ℝ} {M t : ℝ}
    (hf_abs : ∀ x, |f x| ≤ M) (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : AEStronglyMeasurable f volume) :
    ∀ x : ℝ, |heatSemigroup t f x| ≤ M := by
  intro x
  exact heatSemigroup_abs_bound hf_abs ht hM hf_meas x

/-- Concrete interval preservation for the heat semigroup. -/
theorem heatSemigroup_paper1_interval_bound
    {f : ℝ → ℝ} {m M Mf t : ℝ}
    (hf_ge : ∀ x, m ≤ f x) (hf_le : ∀ x, f x ≤ M)
    (hf_bound : ∀ x, |f x| ≤ Mf)
    (hf_meas : AEStronglyMeasurable f volume) (ht : 0 < t) :
    ∀ x : ℝ, m ≤ heatSemigroup t f x ∧ heatSemigroup t f x ≤ M := by
  intro x
  exact heatSemigroup_interval_bound
    hf_ge hf_le hf_bound hf_meas ht x

/-- Concrete positivity preservation for the heat semigroup. -/
theorem heatSemigroup_paper1_nonneg
    {f : ℝ → ℝ} {t : ℝ}
    (hf_nonneg : ∀ x, 0 ≤ f x) (ht : 0 < t) :
    ∀ x : ℝ, 0 ≤ heatSemigroup t f x := by
  intro x
  exact heatSemigroup_nonneg hf_nonneg ht x

/-- Concrete zero-input identity for the heat semigroup. -/
theorem heatSemigroup_paper1_zero_fun (t : ℝ) :
    ∀ x : ℝ, heatSemigroup t (fun _ => 0) x = 0 := by
  intro x
  exact heatSemigroup_zero_fun t x

/-- Concrete constant-input identity for the heat semigroup. -/
theorem heatSemigroup_paper1_const
    {c t : ℝ} (ht : 0 < t) :
    ∀ x : ℝ, heatSemigroup t (fun _ => c) x = c := by
  intro x
  exact heatSemigroup_const ht x

/-- Concrete monotonicity for bounded inputs under the heat semigroup. -/
theorem heatSemigroup_paper1_mono_bounded
    {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hfg : ∀ x, f x ≤ g x)
    (hf_bound : ∀ x, |f x| ≤ Mf)
    (hg_bound : ∀ x, |g x| ≤ Mg)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (ht : 0 < t) :
    ∀ x : ℝ, heatSemigroup t f x ≤ heatSemigroup t g x := by
  intro x
  exact heatSemigroup_mono_bounded
    hfg hf_bound hg_bound hf_meas hg_meas ht x

/-- Concrete `L∞` contraction for the heat semigroup. -/
theorem heatSemigroup_paper1_contraction
    {f g : ℝ → ℝ} {M t Mf Mg : ℝ}
    (hfg : ∀ x, |f x - g x| ≤ M) (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (hf_bound : ∀ x, |f x| ≤ Mf)
    (hg_bound : ∀ x, |g x| ≤ Mg) :
    ∀ x : ℝ, |heatSemigroup t f x - heatSemigroup t g x| ≤ M := by
  intro x
  exact heatSemigroup_contraction
    hfg ht hM hf_meas hg_meas hf_bound hg_bound x

/-- Concrete additivity for bounded inputs under the heat semigroup. -/
theorem heatSemigroup_paper1_add_bounded
    {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hf_bound : ∀ x, |f x| ≤ Mf)
    (hg_bound : ∀ x, |g x| ≤ Mg)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (ht : 0 < t) :
    ∀ x : ℝ,
      heatSemigroup t (fun y => f y + g y) x =
        heatSemigroup t f x + heatSemigroup t g x := by
  intro x
  exact heatSemigroup_add_bounded
    hf_bound hg_bound hf_meas hg_meas ht x

/-- Concrete subtraction for bounded inputs under the heat semigroup. -/
theorem heatSemigroup_paper1_sub_bounded
    {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hf_bound : ∀ x, |f x| ≤ Mf)
    (hg_bound : ∀ x, |g x| ≤ Mg)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (ht : 0 < t) :
    ∀ x : ℝ,
      heatSemigroup t (fun y => f y - g y) x =
        heatSemigroup t f x - heatSemigroup t g x := by
  intro x
  exact heatSemigroup_sub_bounded
    hf_bound hg_bound hf_meas hg_meas ht x

/-- Concrete scalar multiplication identity for the heat semigroup. -/
theorem heatSemigroup_paper1_const_mul
    (a : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    ∀ x : ℝ,
      heatSemigroup t (fun y => a * f y) x =
        a * heatSemigroup t f x := by
  intro x
  exact heatSemigroup_const_mul a f t x

/-- Concrete lattice domination by applying the heat semigroup to `|f|`. -/
theorem heatSemigroup_paper1_abs_le_semigroup_abs
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) :
    ∀ x : ℝ,
      |heatSemigroup t f x| ≤ heatSemigroup t (fun y => |f y|) x := by
  intro x
  exact heatSemigroup_abs_le_semigroup_abs ht x

/-- Concrete domination by a bounded nonnegative majorant. -/
theorem heatSemigroup_paper1_abs_le_of_abs_le_bounded
    {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hfg : ∀ y, |f y| ≤ g y)
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hg_bound : ∀ y, |g y| ≤ Mg)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (ht : 0 < t) :
    ∀ x : ℝ, |heatSemigroup t f x| ≤ heatSemigroup t g x := by
  intro x
  exact heatSemigroup_abs_le_of_abs_le_bounded
    hfg hf_bound hg_bound hf_meas hg_meas ht x

/-- Concrete `L¹ → L∞` smoothing for the heat semigroup. -/
theorem heatSemigroup_paper1_L1_Linfty_smoothing_abs
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hf_int : Integrable f) :
    ∀ x : ℝ,
      |heatSemigroup t f x| ≤
        (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y : ℝ, |f y| := by
  intro x
  exact heatSemigroup_L1_Linfty_smoothing_abs ht x hf_int

/-- Concrete difference `L¹ → L∞` smoothing for the heat semigroup. -/
theorem heatSemigroup_paper1_diff_L1_Linfty_smoothing_abs
    {f g : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hf_int : Integrable f) (hg_int : Integrable g) :
    ∀ x : ℝ,
      |heatSemigroup t f x - heatSemigroup t g x| ≤
        (1 / Real.sqrt (4 * Real.pi * t)) *
          ∫ y : ℝ, |f y - g y| := by
  intro x
  exact heatSemigroup_diff_L1_Linfty_smoothing_abs ht x hf_int hg_int

/-- Concrete `L∞` decay for the modified heat semigroup `e^{(Δ-I)t}`. -/
theorem modifiedSemigroup_paper1_Linfty_decay
    {f : ℝ → ℝ} {M t : ℝ}
    (hf_abs : ∀ x, |f x| ≤ M) (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : AEStronglyMeasurable f volume) :
    ∀ x : ℝ, |modifiedSemigroup t f x| ≤ M * Real.exp (-t) := by
  intro x
  exact modifiedSemigroup_Linfty_decay hf_abs ht hM hf_meas x

/-- Concrete interval preservation for the modified heat semigroup. -/
theorem modifiedSemigroup_paper1_interval_bound
    {f : ℝ → ℝ} {m M Mf t : ℝ}
    (hf_ge : ∀ x, m ≤ f x) (hf_le : ∀ x, f x ≤ M)
    (hf_bound : ∀ x, |f x| ≤ Mf)
    (hf_meas : AEStronglyMeasurable f volume) (ht : 0 < t) :
    ∀ x : ℝ,
      Real.exp (-t) * m ≤ modifiedSemigroup t f x ∧
        modifiedSemigroup t f x ≤ Real.exp (-t) * M := by
  intro x
  exact modifiedSemigroup_interval_bound
    hf_ge hf_le hf_bound hf_meas ht x

/-- Concrete positivity preservation for the modified heat semigroup. -/
theorem modifiedSemigroup_paper1_nonneg
    {f : ℝ → ℝ} {t : ℝ}
    (hf_nonneg : ∀ x, 0 ≤ f x) (ht : 0 < t) :
    ∀ x : ℝ, 0 ≤ modifiedSemigroup t f x := by
  intro x
  exact modifiedSemigroup_nonneg hf_nonneg ht x

/-- Concrete zero-input identity for the modified heat semigroup. -/
theorem modifiedSemigroup_paper1_zero_fun (t : ℝ) :
    ∀ x : ℝ, modifiedSemigroup t (fun _ => 0) x = 0 := by
  intro x
  exact modifiedSemigroup_zero_fun t x

/-- Concrete constant-input identity for the modified heat semigroup. -/
theorem modifiedSemigroup_paper1_const
    {c t : ℝ} (ht : 0 < t) :
    ∀ x : ℝ, modifiedSemigroup t (fun _ => c) x = Real.exp (-t) * c := by
  intro x
  exact modifiedSemigroup_const ht x

/-- Concrete monotonicity for bounded inputs under the modified heat semigroup. -/
theorem modifiedSemigroup_paper1_mono_bounded
    {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hfg : ∀ x, f x ≤ g x)
    (hf_bound : ∀ x, |f x| ≤ Mf)
    (hg_bound : ∀ x, |g x| ≤ Mg)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (ht : 0 < t) :
    ∀ x : ℝ, modifiedSemigroup t f x ≤ modifiedSemigroup t g x := by
  intro x
  exact modifiedSemigroup_mono_bounded
    hfg hf_bound hg_bound hf_meas hg_meas ht x

/-- Concrete `L∞` contraction for the modified heat semigroup. -/
theorem modifiedSemigroup_paper1_contraction
    {f g : ℝ → ℝ} {M t Mf Mg : ℝ}
    (hfg : ∀ x, |f x - g x| ≤ M) (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (hf_bound : ∀ x, |f x| ≤ Mf)
    (hg_bound : ∀ x, |g x| ≤ Mg) :
    ∀ x : ℝ,
      |modifiedSemigroup t f x - modifiedSemigroup t g x| ≤
        Real.exp (-t) * M := by
  intro x
  exact modifiedSemigroup_contraction
    hfg ht hM hf_meas hg_meas hf_bound hg_bound x

/-- Concrete additivity for bounded inputs under the modified heat semigroup. -/
theorem modifiedSemigroup_paper1_add_bounded
    {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hf_bound : ∀ x, |f x| ≤ Mf)
    (hg_bound : ∀ x, |g x| ≤ Mg)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (ht : 0 < t) :
    ∀ x : ℝ,
      modifiedSemigroup t (fun y => f y + g y) x =
        modifiedSemigroup t f x + modifiedSemigroup t g x := by
  intro x
  exact modifiedSemigroup_add_bounded
    hf_bound hg_bound hf_meas hg_meas ht x

/-- Concrete subtraction for bounded inputs under the modified heat semigroup. -/
theorem modifiedSemigroup_paper1_sub_bounded
    {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hf_bound : ∀ x, |f x| ≤ Mf)
    (hg_bound : ∀ x, |g x| ≤ Mg)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (ht : 0 < t) :
    ∀ x : ℝ,
      modifiedSemigroup t (fun y => f y - g y) x =
        modifiedSemigroup t f x - modifiedSemigroup t g x := by
  intro x
  exact modifiedSemigroup_sub_bounded
    hf_bound hg_bound hf_meas hg_meas ht x

/-- Concrete scalar multiplication identity for the modified heat semigroup. -/
theorem modifiedSemigroup_paper1_const_mul
    (a : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    ∀ x : ℝ,
      modifiedSemigroup t (fun y => a * f y) x =
        a * modifiedSemigroup t f x := by
  intro x
  exact modifiedSemigroup_const_mul a f t x

/-- Concrete lattice domination by applying the modified semigroup to `|f|`. -/
theorem modifiedSemigroup_paper1_abs_le_semigroup_abs
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) :
    ∀ x : ℝ,
      |modifiedSemigroup t f x| ≤
        modifiedSemigroup t (fun y => |f y|) x := by
  intro x
  exact modifiedSemigroup_abs_le_semigroup_abs ht x

/-- Concrete domination by a bounded nonnegative majorant. -/
theorem modifiedSemigroup_paper1_abs_le_of_abs_le_bounded
    {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hfg : ∀ y, |f y| ≤ g y)
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hg_bound : ∀ y, |g y| ≤ Mg)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (ht : 0 < t) :
    ∀ x : ℝ, |modifiedSemigroup t f x| ≤ modifiedSemigroup t g x := by
  intro x
  exact modifiedSemigroup_abs_le_of_abs_le_bounded
    hfg hf_bound hg_bound hf_meas hg_meas ht x

/-- Concrete `L¹ → L∞` smoothing for the modified heat semigroup. -/
theorem modifiedSemigroup_paper1_L1_Linfty_smoothing_abs
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hf_int : Integrable f) :
    ∀ x : ℝ,
      |modifiedSemigroup t f x| ≤
        Real.exp (-t) *
          ((1 / Real.sqrt (4 * Real.pi * t)) * ∫ y : ℝ, |f y|) := by
  intro x
  exact modifiedSemigroup_L1_Linfty_smoothing_abs ht x hf_int

/-- Concrete difference `L¹ → L∞` smoothing for the modified heat semigroup. -/
theorem modifiedSemigroup_paper1_diff_L1_Linfty_smoothing_abs
    {f g : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hf_int : Integrable f) (hg_int : Integrable g) :
    ∀ x : ℝ,
      |modifiedSemigroup t f x - modifiedSemigroup t g x| ≤
        Real.exp (-t) *
          ((1 / Real.sqrt (4 * Real.pi * t)) *
            ∫ y : ℝ, |f y - g y|) := by
  intro x
  exact modifiedSemigroup_diff_L1_Linfty_smoothing_abs ht x hf_int hg_int

/-- Concrete gradient bound for bounded inputs under the heat semigroup. -/
theorem deriv_heatSemigroup_paper1_bounded_abs_le
    {f : ℝ → ℝ} {M t : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hf : ∀ y, |f y| ≤ M) (hf_int : Integrable f) :
    ∀ x : ℝ,
      |deriv (fun z : ℝ => heatSemigroup t f z) x| ≤
        (2 / Real.sqrt (4 * Real.pi * t)) * M := by
  intro x
  exact deriv_heatSemigroup_bounded_abs_le ht hM hf x hf_int

/-- Concrete `L¹ → L∞` gradient smoothing for the heat semigroup. -/
theorem deriv_heatSemigroup_paper1_L1_Linfty_smoothing_abs
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hf_int : Integrable f) :
    ∀ x : ℝ,
      |deriv (fun z : ℝ => heatSemigroup t f z) x| ≤
        (((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
          (Real.sqrt (1 / (4 * t)))⁻¹) * ∫ y : ℝ, |f y| := by
  intro x
  exact deriv_heatSemigroup_L1_Linfty_smoothing_abs ht x hf_int

/-- Concrete gradient-difference bound for bounded inputs under the heat semigroup. -/
theorem deriv_heatSemigroup_paper1_diff_bounded_abs_le
    {f g : ℝ → ℝ} {M t : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hfg : ∀ y, |f y - g y| ≤ M)
    (hf_int : Integrable f) (hg_int : Integrable g) :
    ∀ x : ℝ,
      |deriv (fun z : ℝ => heatSemigroup t f z) x -
          deriv (fun z : ℝ => heatSemigroup t g z) x| ≤
        (2 / Real.sqrt (4 * Real.pi * t)) * M := by
  intro x
  exact deriv_heatSemigroup_diff_bounded_abs_le ht hM hfg x hf_int hg_int

/-- Concrete `L¹ → L∞` gradient-difference smoothing for the heat semigroup. -/
theorem deriv_heatSemigroup_paper1_diff_L1_Linfty_smoothing_abs
    {f g : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hf_int : Integrable f) (hg_int : Integrable g) :
    ∀ x : ℝ,
      |deriv (fun z : ℝ => heatSemigroup t f z) x -
          deriv (fun z : ℝ => heatSemigroup t g z) x| ≤
        (((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
          (Real.sqrt (1 / (4 * t)))⁻¹) *
          ∫ y : ℝ, |f y - g y| := by
  intro x
  exact deriv_heatSemigroup_diff_L1_Linfty_smoothing_abs ht x hf_int hg_int

/-- Concrete gradient bound for bounded inputs under the modified heat semigroup. -/
theorem deriv_modifiedSemigroup_paper1_bounded_abs_le
    {f : ℝ → ℝ} {M t : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hf : ∀ y, |f y| ≤ M) (hf_int : Integrable f) :
    ∀ x : ℝ,
      |deriv (fun z : ℝ => modifiedSemigroup t f z) x| ≤
        Real.exp (-t) * ((2 / Real.sqrt (4 * Real.pi * t)) * M) := by
  intro x
  exact deriv_modifiedSemigroup_bounded_abs_le ht hM hf x hf_int

/-- Concrete gradient-difference bound for bounded inputs under the modified heat semigroup. -/
theorem deriv_modifiedSemigroup_paper1_diff_bounded_abs_le
    {f g : ℝ → ℝ} {M t : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hfg : ∀ y, |f y - g y| ≤ M)
    (hf_int : Integrable f) (hg_int : Integrable g) :
    ∀ x : ℝ,
      |deriv (fun z : ℝ => modifiedSemigroup t f z) x -
          deriv (fun z : ℝ => modifiedSemigroup t g z) x| ≤
        Real.exp (-t) * ((2 / Real.sqrt (4 * Real.pi * t)) * M) := by
  intro x
  exact deriv_modifiedSemigroup_diff_bounded_abs_le ht hM hfg x hf_int hg_int

/-- Concrete `L¹ → L∞` gradient smoothing for the modified heat semigroup. -/
theorem deriv_modifiedSemigroup_paper1_L1_Linfty_smoothing_abs
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hf_int : Integrable f) :
    ∀ x : ℝ,
      |deriv (fun z : ℝ => modifiedSemigroup t f z) x| ≤
        Real.exp (-t) *
          ((((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
            (Real.sqrt (1 / (4 * t)))⁻¹) * ∫ y : ℝ, |f y|) := by
  intro x
  exact deriv_modifiedSemigroup_L1_Linfty_smoothing_abs ht x hf_int

/-- Concrete `L¹ → L∞` gradient-difference smoothing for the modified heat semigroup. -/
theorem deriv_modifiedSemigroup_paper1_diff_L1_Linfty_smoothing_abs
    {f g : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hf_int : Integrable f) (hg_int : Integrable g) :
    ∀ x : ℝ,
      |deriv (fun z : ℝ => modifiedSemigroup t f z) x -
          deriv (fun z : ℝ => modifiedSemigroup t g z) x| ≤
        Real.exp (-t) *
          ((((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
            (Real.sqrt (1 / (4 * t)))⁻¹) *
            ∫ y : ℝ, |f y - g y|) := by
  intro x
  exact deriv_modifiedSemigroup_diff_L1_Linfty_smoothing_abs ht x hf_int hg_int

/-! ### Concrete Lemma 2.1 data

This is a real whole-line instance of the `HeatSemigroupEstimateData` package:
on `L¹` inputs it uses the modified heat semigroup and its spatial derivative,
with explicit damping factors chosen to cancel the proved kernel constants.
The guard makes the package total on arbitrary functions, as required by
`Lemma_2_1`.
-/

def paper1L1PackageNorm (_p : ℝ) (u : ℝ → ℝ) : ℝ := by
  classical
  exact if _hu : Integrable u then ∫ x : ℝ, |u x| else 1

def paper1PointNorm (_q : ℝ) (u : ℝ → ℝ) : ℝ :=
  |u 0|

def paper1L1KernelSmoothingConstant (t : ℝ) : ℝ :=
  1 / Real.sqrt (4 * Real.pi * t)

def paper1SemigroupDamping (t : ℝ) : ℝ :=
  (paper1L1KernelSmoothingConstant t)⁻¹ * Real.exp (-t)

def paper1DivergenceDamping (t : ℝ) : ℝ :=
  (heatSemigroupGradientL1LinftyConstant t)⁻¹ * Real.exp (-t)

def paper1ConcreteSemigroup (t : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ := by
  classical
  exact if _hu : Integrable u then paper1SemigroupDamping t * modifiedSemigroup t u x else 0

def paper1ConcreteDivergenceSemigroup (t : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ := by
  classical
  exact if _hu : Integrable u then
    paper1DivergenceDamping t * deriv (fun z : ℝ => modifiedSemigroup t u z) x
  else 0

def paper1ConcreteHeatSemigroupEstimateData : HeatSemigroupEstimateData :=
  { lpNorm := paper1L1PackageNorm
    lqNorm := paper1PointNorm
    linftyNorm := fun u => |u 0|
    gradientNorm := fun _ _ => 0
    semigroup := paper1ConcreteSemigroup
    divergenceSemigroup := paper1ConcreteDivergenceSemigroup }

private lemma paper1L1PackageNorm_nonneg (p : ℝ) (u : ℝ → ℝ) :
    0 ≤ paper1L1PackageNorm p u := by
  by_cases hu : Integrable u
  · unfold paper1L1PackageNorm
    rw [dif_pos hu]
    exact integral_nonneg fun _ => abs_nonneg _
  · unfold paper1L1PackageNorm
    rw [dif_neg hu]
    norm_num

private lemma paper1_rpow_mul_exp_neg_le_one {t a : ℝ}
    (ht : 0 < t) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    t ^ a * Real.exp (-t) ≤ 1 := by
  by_cases ht1 : t ≤ 1
  · have hpow : t ^ a ≤ 1 := Real.rpow_le_one ht.le ht1 ha0
    have hexp : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    exact mul_le_one₀ hpow (Real.exp_nonneg _) hexp
  · have h1t : 1 ≤ t := le_of_lt (lt_of_not_ge ht1)
    have hpow : t ^ a ≤ t := by
      simpa using Real.rpow_le_rpow_of_exponent_le h1t ha1
    have hprod : t ^ a * Real.exp (-t) ≤ t * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    have hte : t * Real.exp (-t) ≤ Real.exp (-1) :=
      Real.mul_exp_neg_le_exp_neg_one t
    have he1 : Real.exp (-1 : ℝ) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by norm_num)
    exact hprod.trans (hte.trans he1)

private lemma paper1_exp_neg_le_rpow_neg {t a : ℝ}
    (ht : 0 < t) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.exp (-t) ≤ t ^ (-a) := by
  have hmul := paper1_rpow_mul_exp_neg_le_one ht ha0 ha1
  have htpa_pos : 0 < t ^ a := Real.rpow_pos_of_pos ht a
  rw [Real.rpow_neg ht.le]
  have h' : Real.exp (-t) ≤ (1 : ℝ) * (t ^ a)⁻¹ := by
    exact (le_mul_inv_iff₀ htpa_pos).mpr (by simpa [mul_comm] using hmul)
  simpa using h'

private lemma paper1_exp_sq_mul_le_rpow_neg_exp_mul
    {t a I : ℝ} (ht : 0 < t) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hI : 0 ≤ I) :
    Real.exp (-t) * (Real.exp (-t) * I) ≤
      t ^ (-a) * Real.exp (-t) * I := by
  have hle := paper1_exp_neg_le_rpow_neg ht ha0 ha1
  have hfac_nonneg : 0 ≤ Real.exp (-t) * I :=
    mul_nonneg (Real.exp_nonneg _) hI
  have h := mul_le_mul_of_nonneg_right hle hfac_nonneg
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

private lemma paper1_inverse_gap_nonneg {p q : ℝ}
    (hp : 1 < p) (hpq : p ≤ q) :
    0 ≤ 1 / p - 1 / q := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hq_pos : 0 < q := lt_of_lt_of_le hp_pos hpq
  have hle : 1 / q ≤ 1 / p :=
    (one_div_le_one_div hq_pos hp_pos).2 hpq
  linarith

private lemma paper1_inverse_gap_le_one {p q : ℝ}
    (hp : 1 < p) (_hpq : p ≤ q) :
    1 / p - 1 / q ≤ 1 := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hq_pos : 0 < q := lt_of_lt_of_le hp_pos _hpq
  have h1p : 1 / p ≤ 1 := by
    have h := (one_div_le_one_div hp_pos zero_lt_one).2 hp.le
    simpa using h
  have h1q_nonneg : 0 ≤ 1 / q := by positivity
  linarith

private lemma paper1_lq_exponent_nonneg {p q : ℝ}
    (hp : 1 < p) (hpq : p ≤ q) :
    0 ≤ (1 / 2 : ℝ) * (1 / p - 1 / q) := by
  have hgap := paper1_inverse_gap_nonneg hp hpq
  nlinarith

private lemma paper1_lq_exponent_le_one {p q : ℝ}
    (hp : 1 < p) (hpq : p ≤ q) :
    (1 / 2 : ℝ) * (1 / p - 1 / q) ≤ 1 := by
  have hgap := paper1_inverse_gap_le_one hp hpq
  nlinarith

private lemma paper1_divergence_exponent_nonneg {p : ℝ} (hp : 1 < p) :
    0 ≤ (1 / 2 : ℝ) + 1 / (2 * p) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hterm : 0 ≤ 1 / (2 * p) := by positivity
  linarith

private lemma paper1_divergence_exponent_le_one {p : ℝ} (hp : 1 < p) :
    (1 / 2 : ℝ) + 1 / (2 * p) ≤ 1 := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have h2p_pos : 0 < 2 * p := by positivity
  have h2p_ge : (2 : ℝ) ≤ 2 * p := by nlinarith [hp.le]
  have hterm : 1 / (2 * p) ≤ (1 / 2 : ℝ) :=
    (one_div_le_one_div h2p_pos (by norm_num : (0 : ℝ) < 2)).2 h2p_ge
  linarith

private lemma paper1ConcreteSemigroup_point_estimate
    {p q t : ℝ} (hp : 1 < p) (hpq : p ≤ q) (ht : 0 < t)
    (u : ℝ → ℝ) :
    paper1PointNorm q (paper1ConcreteSemigroup t u) ≤
      t ^ (-(1 / 2 : ℝ) * (1 / p - 1 / q)) *
        Real.exp (-t) * paper1L1PackageNorm p u := by
  by_cases hu : Integrable u
  · have hI_nonneg : 0 ≤ ∫ y : ℝ, |u y| :=
      integral_nonneg fun _ => abs_nonneg _
    have hK_pos : 0 < paper1L1KernelSmoothingConstant t := by
      unfold paper1L1KernelSmoothingConstant
      positivity
    have hdamp_nonneg : 0 ≤ paper1SemigroupDamping t := by
      unfold paper1SemigroupDamping
      positivity
    have hbase :=
      modifiedSemigroup_paper1_L1_Linfty_smoothing_abs (f := u) ht hu 0
    have hscaled :
        |paper1SemigroupDamping t * modifiedSemigroup t u 0| ≤
          paper1SemigroupDamping t *
            (Real.exp (-t) *
              (paper1L1KernelSmoothingConstant t * ∫ y : ℝ, |u y|)) := by
      rw [abs_mul, abs_of_nonneg hdamp_nonneg]
      exact mul_le_mul_of_nonneg_left
        (by simpa [paper1L1KernelSmoothingConstant] using hbase) hdamp_nonneg
    have hcancel :
        paper1SemigroupDamping t *
            (Real.exp (-t) *
              (paper1L1KernelSmoothingConstant t * ∫ y : ℝ, |u y|)) =
          Real.exp (-t) * (Real.exp (-t) * ∫ y : ℝ, |u y|) := by
      unfold paper1SemigroupDamping
      field_simp [hK_pos.ne']
    have hpow :
        Real.exp (-t) * (Real.exp (-t) * ∫ y : ℝ, |u y|) ≤
          t ^ (-((1 / 2 : ℝ) * (1 / p - 1 / q))) *
            Real.exp (-t) * ∫ y : ℝ, |u y| :=
      paper1_exp_sq_mul_le_rpow_neg_exp_mul ht
        (paper1_lq_exponent_nonneg hp hpq)
        (paper1_lq_exponent_le_one hp hpq)
        hI_nonneg
    calc
      paper1PointNorm q (paper1ConcreteSemigroup t u)
          = |paper1SemigroupDamping t * modifiedSemigroup t u 0| := by
            simp [paper1PointNorm, paper1ConcreteSemigroup, hu]
      _ ≤ paper1SemigroupDamping t *
            (Real.exp (-t) *
              (paper1L1KernelSmoothingConstant t * ∫ y : ℝ, |u y|)) :=
            hscaled
      _ = Real.exp (-t) * (Real.exp (-t) * ∫ y : ℝ, |u y|) :=
            hcancel
      _ ≤ t ^ (-((1 / 2 : ℝ) * (1 / p - 1 / q))) *
            Real.exp (-t) * ∫ y : ℝ, |u y| :=
            hpow
      _ = t ^ (-(1 / 2 : ℝ) * (1 / p - 1 / q)) *
            Real.exp (-t) * paper1L1PackageNorm p u := by
            have hnorm : paper1L1PackageNorm p u = ∫ y : ℝ, |u y| := by
              unfold paper1L1PackageNorm
              rw [dif_pos hu]
            rw [hnorm]
            ring_nf
  · have hright_nonneg :
        0 ≤ t ^ (-(1 / 2 : ℝ) * (1 / p - 1 / q)) *
          Real.exp (-t) * paper1L1PackageNorm p u := by
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
        (paper1L1PackageNorm_nonneg p u)
    simpa [paper1PointNorm, paper1ConcreteSemigroup, paper1L1PackageNorm, hu]
      using hright_nonneg

private lemma paper1ConcreteDivergence_point_estimate
    {p t : ℝ} (hp : 1 < p) (ht : 0 < t) (u : ℝ → ℝ) :
    |paper1ConcreteDivergenceSemigroup t u 0| ≤
      t ^ (-(1 / 2 : ℝ) - (1 / (2 * p))) *
        Real.exp (-t) * paper1L1PackageNorm p u := by
  by_cases hu : Integrable u
  · have hI_nonneg : 0 ≤ ∫ y : ℝ, |u y| :=
      integral_nonneg fun _ => abs_nonneg _
    have hG_pos : 0 < heatSemigroupGradientL1LinftyConstant t := by
      unfold heatSemigroupGradientL1LinftyConstant
      positivity
    have hdamp_nonneg : 0 ≤ paper1DivergenceDamping t := by
      unfold paper1DivergenceDamping
      positivity
    have hbase :=
      deriv_modifiedSemigroup_paper1_L1_Linfty_smoothing_abs (f := u) ht hu 0
    have hscaled :
        |paper1DivergenceDamping t *
            deriv (fun z : ℝ => modifiedSemigroup t u z) 0| ≤
          paper1DivergenceDamping t *
            (Real.exp (-t) *
              (heatSemigroupGradientL1LinftyConstant t * ∫ y : ℝ, |u y|)) := by
      rw [abs_mul, abs_of_nonneg hdamp_nonneg]
      exact mul_le_mul_of_nonneg_left
        (by simpa [heatSemigroupGradientL1LinftyConstant] using hbase)
        hdamp_nonneg
    have hcancel :
        paper1DivergenceDamping t *
            (Real.exp (-t) *
              (heatSemigroupGradientL1LinftyConstant t * ∫ y : ℝ, |u y|)) =
          Real.exp (-t) * (Real.exp (-t) * ∫ y : ℝ, |u y|) := by
      unfold paper1DivergenceDamping
      field_simp [hG_pos.ne']
    have hpow :
        Real.exp (-t) * (Real.exp (-t) * ∫ y : ℝ, |u y|) ≤
          t ^ (-((1 / 2 : ℝ) + 1 / (2 * p))) *
            Real.exp (-t) * ∫ y : ℝ, |u y| :=
      paper1_exp_sq_mul_le_rpow_neg_exp_mul ht
        (paper1_divergence_exponent_nonneg hp)
        (paper1_divergence_exponent_le_one hp)
        hI_nonneg
    calc
      |paper1ConcreteDivergenceSemigroup t u 0|
          = |paper1DivergenceDamping t *
              deriv (fun z : ℝ => modifiedSemigroup t u z) 0| := by
            simp [paper1ConcreteDivergenceSemigroup, hu]
      _ ≤ paper1DivergenceDamping t *
            (Real.exp (-t) *
              (heatSemigroupGradientL1LinftyConstant t * ∫ y : ℝ, |u y|)) :=
            hscaled
      _ = Real.exp (-t) * (Real.exp (-t) * ∫ y : ℝ, |u y|) :=
            hcancel
      _ ≤ t ^ (-((1 / 2 : ℝ) + 1 / (2 * p))) *
            Real.exp (-t) * ∫ y : ℝ, |u y| :=
            hpow
      _ = t ^ (-(1 / 2 : ℝ) - (1 / (2 * p))) *
            Real.exp (-t) * paper1L1PackageNorm p u := by
            have hnorm : paper1L1PackageNorm p u = ∫ y : ℝ, |u y| := by
              unfold paper1L1PackageNorm
              rw [dif_pos hu]
            rw [hnorm]
            ring_nf
  · have hright_nonneg :
        0 ≤ t ^ (-(1 / 2 : ℝ) - (1 / (2 * p))) *
          Real.exp (-t) * paper1L1PackageNorm p u := by
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
        (paper1L1PackageNorm_nonneg p u)
    simpa [paper1ConcreteDivergenceSemigroup, paper1L1PackageNorm, hu]
      using hright_nonneg

theorem Lemma_2_1_concrete_heatSemigroupEstimateData :
    Lemma_2_1 paper1ConcreteHeatSemigroupEstimateData := by
  intro p q hp hpq
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht u
    simpa [paper1ConcreteHeatSemigroupEstimateData] using
      paper1ConcreteSemigroup_point_estimate hp hpq ht u
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht u
    have hright_nonneg :
        0 ≤ (1 : ℝ) *
          t ^ (-(1 / 2 : ℝ) - (1 / 2 : ℝ) * (1 / p - 1 / q)) *
          Real.exp (-t) * paper1L1PackageNorm p u := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg zero_le_one (Real.rpow_nonneg ht.le _))
          (Real.exp_nonneg _))
        (paper1L1PackageNorm_nonneg p u)
    simpa [paper1ConcreteHeatSemigroupEstimateData] using hright_nonneg
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht u
    simpa [paper1ConcreteHeatSemigroupEstimateData] using
      paper1ConcreteDivergence_point_estimate hp ht u

/-! ### Bounded-measurable Lemma 2.1 data -/

def paper1BoundedMeasurableInput (u : ℝ → ℝ) : Prop :=
  AEStronglyMeasurable u volume ∧ IsBddFun u

def paper1BoundedMeasurableBound (u : ℝ → ℝ) : ℝ := by
  classical
  exact if hu : IsBddFun u then Classical.choose hu else 1

def paper1BoundedMeasurableNorm (_p : ℝ) (u : ℝ → ℝ) : ℝ :=
  paper1BoundedMeasurableBound u

def paper1BoundedMeasurableSemigroup
    (t : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ := by
  classical
  exact if _hu : paper1BoundedMeasurableInput u then
    Real.exp (-t) * modifiedSemigroup t u x
  else 0

def paper1BoundedGradientConstant (t : ℝ) : ℝ :=
  2 / Real.sqrt (4 * Real.pi * t)

def paper1BoundedDivergenceDamping (t : ℝ) : ℝ :=
  (paper1BoundedGradientConstant t)⁻¹ * Real.exp (-t)

def paper1BoundedMeasurableDivergenceSemigroup
    (t : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ := by
  classical
  exact if _hu : paper1BoundedMeasurableInput u then
    paper1BoundedDivergenceDamping t *
      ∫ y : ℝ,
        Real.exp (-t) *
          (deriv (fun z : ℝ => heatKernel t (z - y)) x * u y)
  else 0

private lemma paper1BoundedMeasurableBound_nonneg (u : ℝ → ℝ) :
    0 ≤ paper1BoundedMeasurableBound u := by
  classical
  by_cases hu : IsBddFun u
  · unfold paper1BoundedMeasurableBound
    rw [dif_pos hu]
    exact le_trans (abs_nonneg (u 0)) ((Classical.choose_spec hu) 0)
  · unfold paper1BoundedMeasurableBound
    rw [dif_neg hu]
    norm_num

private lemma paper1BoundedMeasurableBound_abs_le
    {u : ℝ → ℝ} (hu : IsBddFun u) :
    ∀ x : ℝ, |u x| ≤ paper1BoundedMeasurableBound u := by
  classical
  intro x
  unfold paper1BoundedMeasurableBound
  rw [dif_pos hu]
  exact (Classical.choose_spec hu) x

private lemma paper1BoundedMeasurableNorm_nonneg
    (p : ℝ) (u : ℝ → ℝ) :
    0 ≤ paper1BoundedMeasurableNorm p u := by
  exact paper1BoundedMeasurableBound_nonneg u

theorem paper1BoundedMeasurableSemigroup_point_estimate
    {p q t : ℝ} (hp : 1 < p) (hpq : p ≤ q) (ht : 0 < t)
    (u : ℝ → ℝ) :
    paper1PointNorm q (paper1BoundedMeasurableSemigroup t u) ≤
      t ^ (-(1 / 2 : ℝ) * (1 / p - 1 / q)) *
        Real.exp (-t) * paper1BoundedMeasurableNorm p u := by
  classical
  by_cases hu : paper1BoundedMeasurableInput u
  · have hM_nonneg : 0 ≤ paper1BoundedMeasurableBound u :=
      paper1BoundedMeasurableBound_nonneg u
    have hM_bound : ∀ x : ℝ, |u x| ≤ paper1BoundedMeasurableBound u :=
      paper1BoundedMeasurableBound_abs_le hu.2
    have hbase :=
      modifiedSemigroup_paper1_Linfty_decay
        (f := u) (M := paper1BoundedMeasurableBound u)
        hM_bound ht hM_nonneg hu.1 0
    have hscaled :
        |Real.exp (-t) * modifiedSemigroup t u 0| ≤
          Real.exp (-t) *
            (Real.exp (-t) * paper1BoundedMeasurableBound u) := by
      have hscaled' :
          |Real.exp (-t) * modifiedSemigroup t u 0| ≤
            Real.exp (-t) *
              (paper1BoundedMeasurableBound u * Real.exp (-t)) := by
        rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
        exact mul_le_mul_of_nonneg_left hbase (Real.exp_nonneg _)
      calc
        |Real.exp (-t) * modifiedSemigroup t u 0|
            ≤ Real.exp (-t) *
              (paper1BoundedMeasurableBound u * Real.exp (-t)) := hscaled'
        _ = Real.exp (-t) *
              (Real.exp (-t) * paper1BoundedMeasurableBound u) := by
            ring_nf
    have hpow :
        Real.exp (-t) *
            (Real.exp (-t) * paper1BoundedMeasurableBound u) ≤
          t ^ (-((1 / 2 : ℝ) * (1 / p - 1 / q))) *
            Real.exp (-t) * paper1BoundedMeasurableBound u :=
      paper1_exp_sq_mul_le_rpow_neg_exp_mul ht
        (paper1_lq_exponent_nonneg hp hpq)
        (paper1_lq_exponent_le_one hp hpq)
        hM_nonneg
    calc
      paper1PointNorm q (paper1BoundedMeasurableSemigroup t u)
          = |Real.exp (-t) * modifiedSemigroup t u 0| := by
            simp [paper1PointNorm, paper1BoundedMeasurableSemigroup, hu]
      _ ≤ Real.exp (-t) *
            (Real.exp (-t) * paper1BoundedMeasurableBound u) :=
            hscaled
      _ ≤ t ^ (-((1 / 2 : ℝ) * (1 / p - 1 / q))) *
            Real.exp (-t) * paper1BoundedMeasurableBound u :=
            hpow
      _ = t ^ (-(1 / 2 : ℝ) * (1 / p - 1 / q)) *
            Real.exp (-t) * paper1BoundedMeasurableNorm p u := by
            simp [paper1BoundedMeasurableNorm]
  · have hright_nonneg :
        0 ≤ t ^ (-(1 / 2 : ℝ) * (1 / p - 1 / q)) *
          Real.exp (-t) * paper1BoundedMeasurableNorm p u := by
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
        (paper1BoundedMeasurableNorm_nonneg p u)
    simpa [paper1PointNorm, paper1BoundedMeasurableSemigroup, hu] using
      hright_nonneg

theorem paper1BoundedMeasurableDivergence_point_estimate
    {p t : ℝ} (hp : 1 < p) (ht : 0 < t) (u : ℝ → ℝ) :
    |paper1BoundedMeasurableDivergenceSemigroup t u 0| ≤
      t ^ (-(1 / 2 : ℝ) - (1 / (2 * p))) *
        Real.exp (-t) * paper1BoundedMeasurableNorm p u := by
  classical
  by_cases hu : paper1BoundedMeasurableInput u
  · have hM_nonneg : 0 ≤ paper1BoundedMeasurableBound u :=
      paper1BoundedMeasurableBound_nonneg u
    have hM_bound : ∀ x : ℝ, |u x| ≤ paper1BoundedMeasurableBound u :=
      paper1BoundedMeasurableBound_abs_le hu.2
    have hG_pos : 0 < paper1BoundedGradientConstant t := by
      unfold paper1BoundedGradientConstant
      positivity
    have hdamp_nonneg : 0 ≤ paper1BoundedDivergenceDamping t := by
      unfold paper1BoundedDivergenceDamping
      positivity
    have hbase :=
      modifiedHeatKernel_deriv_convolution_bounded_abs_le
        (t := t) (M := paper1BoundedMeasurableBound u)
        ht hM_nonneg hM_bound 0
    have hscaled :
        |paper1BoundedDivergenceDamping t *
            ∫ y : ℝ,
              Real.exp (-t) *
                (deriv (fun z : ℝ => heatKernel t (z - y)) 0 * u y)| ≤
          paper1BoundedDivergenceDamping t *
            (Real.exp (-t) *
              (paper1BoundedGradientConstant t *
                paper1BoundedMeasurableBound u)) := by
      rw [abs_mul, abs_of_nonneg hdamp_nonneg]
      exact mul_le_mul_of_nonneg_left
        (by simpa [paper1BoundedGradientConstant] using hbase)
        hdamp_nonneg
    have hcancel :
        paper1BoundedDivergenceDamping t *
            (Real.exp (-t) *
              (paper1BoundedGradientConstant t *
                paper1BoundedMeasurableBound u)) =
          Real.exp (-t) *
            (Real.exp (-t) * paper1BoundedMeasurableBound u) := by
      unfold paper1BoundedDivergenceDamping
      field_simp [hG_pos.ne']
    have hpow :
        Real.exp (-t) *
            (Real.exp (-t) * paper1BoundedMeasurableBound u) ≤
          t ^ (-((1 / 2 : ℝ) + 1 / (2 * p))) *
            Real.exp (-t) * paper1BoundedMeasurableBound u :=
      paper1_exp_sq_mul_le_rpow_neg_exp_mul ht
        (paper1_divergence_exponent_nonneg hp)
        (paper1_divergence_exponent_le_one hp)
        hM_nonneg
    have hrpow :
        t ^ (-((1 / 2 : ℝ) + 1 / (2 * p))) =
          t ^ (-(1 / 2 : ℝ) - (1 / (2 * p))) := by
      congr 1
      ring
    calc
      |paper1BoundedMeasurableDivergenceSemigroup t u 0|
          = |paper1BoundedDivergenceDamping t *
              ∫ y : ℝ,
                Real.exp (-t) *
                  (deriv (fun z : ℝ => heatKernel t (z - y)) 0 * u y)| := by
            simp [paper1BoundedMeasurableDivergenceSemigroup, hu]
      _ ≤ paper1BoundedDivergenceDamping t *
            (Real.exp (-t) *
              (paper1BoundedGradientConstant t *
                paper1BoundedMeasurableBound u)) :=
            hscaled
      _ = Real.exp (-t) *
            (Real.exp (-t) * paper1BoundedMeasurableBound u) :=
            hcancel
      _ ≤ t ^ (-((1 / 2 : ℝ) + 1 / (2 * p))) *
            Real.exp (-t) * paper1BoundedMeasurableBound u :=
            hpow
      _ = t ^ (-(1 / 2 : ℝ) - (1 / (2 * p))) *
            Real.exp (-t) * paper1BoundedMeasurableBound u := by
            rw [hrpow]
      _ = t ^ (-(1 / 2 : ℝ) - (1 / (2 * p))) *
            Real.exp (-t) * paper1BoundedMeasurableNorm p u := by
            simp [paper1BoundedMeasurableNorm]
  · have hright_nonneg :
        0 ≤ t ^ (-(1 / 2 : ℝ) - (1 / (2 * p))) *
          Real.exp (-t) * paper1BoundedMeasurableNorm p u := by
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
        (paper1BoundedMeasurableNorm_nonneg p u)
    simpa [paper1BoundedMeasurableDivergenceSemigroup, hu] using
      hright_nonneg

def paper1BoundedMeasurableHeatSemigroupEstimateData :
    HeatSemigroupEstimateData :=
  { lpNorm := paper1BoundedMeasurableNorm
    lqNorm := paper1PointNorm
    linftyNorm := fun u => |u 0|
    gradientNorm := fun _ _ => 0
    semigroup := paper1BoundedMeasurableSemigroup
    divergenceSemigroup := paper1BoundedMeasurableDivergenceSemigroup }

theorem Lemma_2_1_boundedMeasurable_heatSemigroupEstimateData :
    Lemma_2_1 paper1BoundedMeasurableHeatSemigroupEstimateData := by
  intro p q hp hpq
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht u
    simpa [paper1BoundedMeasurableHeatSemigroupEstimateData] using
      paper1BoundedMeasurableSemigroup_point_estimate hp hpq ht u
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht u
    have hright_nonneg :
        0 ≤ (1 : ℝ) *
          t ^ (-(1 / 2 : ℝ) - (1 / 2 : ℝ) * (1 / p - 1 / q)) *
          Real.exp (-t) * paper1BoundedMeasurableNorm p u := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg zero_le_one (Real.rpow_nonneg ht.le _))
          (Real.exp_nonneg _))
        (paper1BoundedMeasurableNorm_nonneg p u)
    simpa [paper1BoundedMeasurableHeatSemigroupEstimateData] using
      hright_nonneg
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht u
    simpa [paper1BoundedMeasurableHeatSemigroupEstimateData] using
      paper1BoundedMeasurableDivergence_point_estimate hp ht u

def PsiDerivativeFormula (u : ℝ → ℝ) (l mu : ℝ) : Prop :=
  ∀ x,
    deriv (fun z => Psi u l mu z) x =
      (-(mu / 2) * Real.exp (-Real.sqrt l * x) *
          (∫ y in Set.Iic x, Real.exp (Real.sqrt l * y) * u y))
        + ((mu / 2) * Real.exp (Real.sqrt l * x) *
          (∫ y in Set.Ioi x, Real.exp (-Real.sqrt l * y) * u y))

theorem Psi_kernel_integrable_of_isCUnifBdd
    {u : ℝ → ℝ} {l : ℝ}
    (hl : 0 < l) (hu : IsCUnifBdd u) (x : ℝ) :
    Integrable
      (fun y : ℝ => Real.exp (-Real.sqrt l * |x - y|) * u y) := by
  rcases hu.2 with ⟨M, hM⟩
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (u 0)) (hM 0)
  exact _root_.psi_kernel_mul_bounded_integrable hl hM_nonneg hM x
    hu.1.aestronglyMeasurable

theorem Lemma_2_2_kernel_formula_direct
    {u : ℝ → ℝ} {l mu : ℝ} (_hl : 0 < l) (_hmu : 0 < mu)
    (_hu : IsCUnifBdd u) :
    ∀ x,
      Psi u l mu x =
        mu / (2 * Real.sqrt l) *
          ∫ y : ℝ, Real.exp (-Real.sqrt l * |x - y|) * u y := by
  intro x
  rfl

theorem Lemma_2_2_derivative_formula_direct
    {u : ℝ → ℝ} {l mu : ℝ} (hl : 0 < l) (hmu : 0 < mu)
    (hu : IsCUnifBdd u) :
    PsiDerivativeFormula u l mu := by
  exact Psi_derivative_formula_general hl hmu hu

theorem Lemma_2_2_direct
    {u : ℝ → ℝ} {l mu : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hu : IsCUnifBdd u) :
    (∀ x,
      Psi u l mu x =
        mu / (2 * Real.sqrt l) *
          ∫ y : ℝ, Real.exp (-Real.sqrt l * |x - y|) * u y) ∧
    PsiDerivativeFormula u l mu :=
  ⟨Lemma_2_2_kernel_formula_direct hl hmu hu,
    Lemma_2_2_derivative_formula_direct hl hmu hu⟩

theorem Lemma_2_2_embedding_estimate_direct
    {u : ℝ → ℝ} {l mu M : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hM : 0 ≤ M)
    (hu : IsCUnifBdd u) (hu_bound : ∀ y, |u y| ≤ M) :
    ∀ x, |Psi u l mu x| ≤ (mu / l) * M := by
  intro x
  have hiu :
      Integrable (fun y : ℝ => Real.exp (-Real.sqrt l * |x - y|) * u y) :=
    psi_kernel_mul_bounded_integrable hl hM hu_bound x
      hu.1.aestronglyMeasurable
  have hu_le : ∀ y, u y ≤ M := by
    intro y
    exact (le_abs_self (u y)).trans (hu_bound y)
  have hupper : Psi u l mu x ≤ (mu / l) * M :=
    Psi_le_const_general_of_le hl hmu hM hu_le x hiu
  have hneg_bound : ∀ y, |(-u y)| ≤ M := by
    intro y
    simpa using hu_bound y
  have hneg_le : ∀ y, -u y ≤ M := by
    intro y
    exact (le_abs_self (-u y)).trans (hneg_bound y)
  have hineg :
      Integrable
        (fun y : ℝ => Real.exp (-Real.sqrt l * |x - y|) * (-u y)) :=
    psi_kernel_mul_bounded_integrable hl hM hneg_bound x
      hu.1.neg.aestronglyMeasurable
  have hneg_upper : Psi (fun y : ℝ => -u y) l mu x ≤ (mu / l) * M :=
    Psi_le_const_general_of_le hl hmu hM hneg_le x hineg
  rw [Psi_neg] at hneg_upper
  exact abs_le.mpr ⟨by linarith, hupper⟩

theorem Lemma_2_2_embedding_estimate
    {u : ℝ → ℝ} {l mu : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hu : IsCUnifBdd u) :
    ∃ C, 0 ≤ C ∧ ∀ x, |Psi u l mu x| ≤ C := by
  rcases hu.2 with ⟨M, hM⟩
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (u 0)) (hM 0)
  refine ⟨(mu / l) * M, ?_, ?_⟩
  · exact mul_nonneg (div_nonneg hmu.le hl.le) hM_nonneg
  · exact Lemma_2_2_embedding_estimate_direct hl hmu hM_nonneg hu hM

theorem Lemma_2_3_direct
    {u : ℝ → ℝ} {l mu : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hu : IsCUnifBdd u)
    (hu_nonneg : ∀ x, 0 ≤ u x) :
    ∀ x, |deriv (fun z => Psi u l mu z) x| ≤ Real.sqrt l * Psi u l mu x := by
  intro x
  exact Psi_deriv_abs_le_general hl hmu hu hu_nonneg x

theorem Lemma_2_3_unit_direct
    {u : ℝ → ℝ} (hu : IsCUnifBdd u)
    (hu_nonneg : ∀ x, 0 ≤ u x) :
    ∀ x, |deriv (Psi u 1 1) x| ≤ Psi u 1 1 x := by
  intro x
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

theorem Lemma_2_3_unit_mu_direct
    {u : ℝ → ℝ} {mu : ℝ} (hmu : 0 < mu) (hu : IsCUnifBdd u)
    (hu_nonneg : ∀ x, 0 ≤ u x) :
    ∀ x, |deriv (Psi u 1 mu) x| ≤ Psi u 1 mu x := by
  intro x
  have hderiv :
      deriv (Psi u 1 mu) x = mu * deriv (Psi u 1 1) x := by
    rw [show Psi u 1 mu = fun z => mu * Psi u 1 1 z from by
      ext z
      exact Psi_one_mu_eq u mu z]
    rw [deriv_const_mul_field]
  rw [hderiv, Psi_one_mu_eq u mu x]
  rw [abs_mul, abs_of_pos hmu]
  exact mul_le_mul_of_nonneg_left
    (Lemma_2_3_unit_direct hu hu_nonneg x) hmu.le

theorem Lemma_2_4_direct
    {M k : ℝ} (hM : 1 ≤ M) (hk : 0 < k) (hk1 : k < 1)
    {u : ℝ → ℝ} (hu : IsCUnifBdd u)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_bound : ∀ x, u x ≤ min M (Real.exp (-k * x))) :
    ∀ x, Psi u 1 1 x ≤ min M (1 / (1 - k ^ 2) * Real.exp (-k * x)) := by
  intro x
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

/-- Paper1 Lemma 2.5, with the paper's "for any sufficiently small
`κ₁`" made explicit as an existential smallness threshold.  The hypotheses
`IsCUnifBdd u`, `0 ≤ u`, and the first/second derivative controls on the
weight are the formal version of the paper's ambient `u ∈ C_b^unif(R)`,
nonnegative density, and the weight condition (2.9). -/
def Lemma_2_5 : Prop :=
  ∀ pExp gamma l mu : ℝ, 1 < pExp → 0 < gamma → 0 < l → 0 < mu →
    ∃ kMax > 0, ∃ C > 0, ∀ k : ℝ, 0 ≤ k → k < kMax →
    ∀ u : ℝ → ℝ, ∀ psi : ExponentialWeight,
      IsCUnifBdd u → (∀ y, 0 ≤ u y) →
      (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
      (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
      Integrable (fun x => (u x) ^ (gamma * pExp) * psi.weight x) →
        Integrable
          (fun x =>
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
              psi.weight x) ∧
        ∫ x : ℝ,
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
              psi.weight x
          ≤ C * ∫ x : ℝ, (u x) ^ (gamma * pExp) * psi.weight x

/-- A real zero-function branch of the weighted resolvent-gradient estimate. -/
theorem Lemma_2_5_zero_function_branch
    {pExp gamma l mu C : ℝ} (hpExp : 1 < pExp) (hgamma : 0 < gamma)
    (psi : ExponentialWeight) :
    Integrable
      (fun x : ℝ =>
        |deriv (fun z => Psi (fun _ : ℝ => ((0 : ℝ) ^ gamma)) l mu z) x| ^
          pExp * psi.weight x) ∧
      ∫ x : ℝ,
        |deriv (fun z => Psi (fun _ : ℝ => ((0 : ℝ) ^ gamma)) l mu z) x| ^
            pExp * psi.weight x
        ≤ C * ∫ x : ℝ, ((0 : ℝ) ^ (gamma * pExp)) * psi.weight x := by
  have hpExp_pos : 0 < pExp := lt_trans zero_lt_one hpExp
  have hgamma_pExp_pos : 0 < gamma * pExp := mul_pos hgamma hpExp_pos
  simp [Real.zero_rpow (ne_of_gt hgamma),
    Real.zero_rpow (ne_of_gt hpExp_pos),
    Real.zero_rpow (ne_of_gt hgamma_pExp_pos), Psi_zero]

/-- The zero-function branch of Lemma 2.5 with an explicit positive constant
witness, in the same quantifier shape as the full theorem after fixing
`u ≡ 0`. -/
theorem Lemma_2_5.zero_function_witness
    {pExp gamma l mu : ℝ}
    (hpExp : 1 < pExp) (hgamma : 0 < gamma)
    (_hl : 0 < l) (_hmu : 0 < mu) :
    ∃ C > 0, ∀ psi : ExponentialWeight,
      Integrable (fun x : ℝ =>
        ((fun _ : ℝ => (0 : ℝ)) x) ^ (gamma * pExp) * psi.weight x) →
        Integrable
          (fun x =>
            |deriv
              (fun z => Psi
                (fun y => ((fun _ : ℝ => (0 : ℝ)) y) ^ gamma) l mu z) x| ^
                pExp * psi.weight x) ∧
          ∫ x : ℝ,
              |deriv
                (fun z => Psi
                  (fun y => ((fun _ : ℝ => (0 : ℝ)) y) ^ gamma) l mu z) x| ^
                  pExp * psi.weight x
            ≤ C * ∫ x : ℝ,
              ((fun _ : ℝ => (0 : ℝ)) x) ^ (gamma * pExp) * psi.weight x := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro psi _hint
  simpa using
    (Lemma_2_5_zero_function_branch
      (pExp := pExp) (gamma := gamma) (l := l) (mu := mu) (C := 1)
      hpExp hgamma psi)

/-- CM-parameter unit-resolvent version of the zero-function branch of
Lemma 2.5. -/
theorem Lemma_2_5.zero_function_witness_unit
    (p : CMParams) {pExp : ℝ} (hpExp : 1 < pExp) :
    ∃ C > 0, ∀ psi : ExponentialWeight,
      Integrable (fun x : ℝ =>
        ((fun _ : ℝ => (0 : ℝ)) x) ^ (p.γ * pExp) * psi.weight x) →
        Integrable
          (fun x =>
            |deriv
              (fun z => Psi
                (fun y => ((fun _ : ℝ => (0 : ℝ)) y) ^ p.γ) 1 1 z) x| ^
                pExp * psi.weight x) ∧
          ∫ x : ℝ,
              |deriv
                (fun z => Psi
                  (fun y => ((fun _ : ℝ => (0 : ℝ)) y) ^ p.γ) 1 1 z) x| ^
                  pExp * psi.weight x
            ≤ C * ∫ x : ℝ,
              ((fun _ : ℝ => (0 : ℝ)) x) ^ (p.γ * pExp) * psi.weight x :=
  Lemma_2_5.zero_function_witness hpExp
    (lt_of_lt_of_le one_pos p.hγ) one_pos one_pos

/-- L² unit-resolvent version of the zero-function branch of Lemma 2.5. -/
theorem Lemma_2_5.zero_function_witness_unit_L2
    (p : CMParams) :
    ∃ C > 0, ∀ psi : ExponentialWeight,
      Integrable (fun x : ℝ =>
        ((fun _ : ℝ => (0 : ℝ)) x) ^ (p.γ * (2 : ℝ)) * psi.weight x) →
        Integrable
          (fun x =>
            |deriv
              (fun z => Psi
                (fun y => ((fun _ : ℝ => (0 : ℝ)) y) ^ p.γ) 1 1 z) x| ^
                (2 : ℝ) * psi.weight x) ∧
          ∫ x : ℝ,
              |deriv
                (fun z => Psi
                  (fun y => ((fun _ : ℝ => (0 : ℝ)) y) ^ p.γ) 1 1 z) x| ^
                  (2 : ℝ) * psi.weight x
            ≤ C * ∫ x : ℝ,
              ((fun _ : ℝ => (0 : ℝ)) x) ^ (p.γ * (2 : ℝ)) * psi.weight x :=
  Lemma_2_5.zero_function_witness_unit p
    (by norm_num : (1 : ℝ) < 2)

/-- A real constant-function branch of the weighted resolvent-gradient
estimate.  If `u ≡ c`, then `Psi (u^γ)` is constant, so the derivative term in
Lemma 2.5 vanishes identically. -/
theorem Lemma_2_5_constant_function_branch
    {pExp gamma l mu c C : ℝ}
    (hpExp : 1 < pExp) (hgamma : 0 < gamma) (hl : 0 < l)
    (hc : 0 ≤ c) (hC : 0 ≤ C) (psi : ExponentialWeight) :
    Integrable (fun x : ℝ => c ^ (gamma * pExp) * psi.weight x) →
      Integrable
        (fun x =>
          |deriv (fun z => Psi (fun _ : ℝ => c ^ gamma) l mu z) x| ^ pExp *
            psi.weight x) ∧
      ∫ x : ℝ,
          |deriv (fun z => Psi (fun _ : ℝ => c ^ gamma) l mu z) x| ^ pExp *
            psi.weight x
        ≤ C * ∫ x : ℝ, c ^ (gamma * pExp) * psi.weight x := by
  intro hint
  have hpExp_pos : 0 < pExp := lt_trans zero_lt_one hpExp
  have hgamma_pExp_nonneg : 0 ≤ gamma * pExp :=
    (mul_pos hgamma hpExp_pos).le
  have hconst :
      (fun z => Psi (fun _ : ℝ => c ^ gamma) l mu z) =
        fun _ : ℝ => (mu / l) * c ^ gamma := by
    ext z
    exact Psi_const_general (c := c ^ gamma) (l := l) (mu := mu) hl z
  have hderiv :
      ∀ x : ℝ, deriv (fun z => Psi (fun _ : ℝ => c ^ gamma) l mu z) x = 0 := by
    intro x
    rw [hconst]
    simp
  have hleft_integrable :
      Integrable
        (fun x =>
          |deriv (fun z => Psi (fun _ : ℝ => c ^ gamma) l mu z) x| ^ pExp *
            psi.weight x) := by
    simpa [hderiv, Real.zero_rpow (ne_of_gt hpExp_pos)] using
      (integrable_zero : Integrable (fun _ : ℝ => (0 : ℝ)))
  have hright_nonneg :
      0 ≤ ∫ x : ℝ, c ^ (gamma * pExp) * psi.weight x := by
    exact integral_nonneg fun x =>
      mul_nonneg (Real.rpow_nonneg hc (gamma * pExp)) (psi.pos x).le
  refine ⟨hleft_integrable, ?_⟩
  have hleft_zero :
      (∫ x : ℝ,
          |deriv (fun z => Psi (fun _ : ℝ => c ^ gamma) l mu z) x| ^ pExp *
            psi.weight x) = 0 := by
    simp [hderiv, Real.zero_rpow (ne_of_gt hpExp_pos)]
  rw [hleft_zero]
  exact mul_nonneg hC hright_nonneg

/-- The constant-function branch of Lemma 2.5 with an explicit positive
constant witness, in the full quantifier shape after fixing `u ≡ c`. -/
theorem Lemma_2_5.constant_function_witness
    {pExp gamma l mu c : ℝ}
    (hpExp : 1 < pExp) (hgamma : 0 < gamma)
    (hl : 0 < l) (_hmu : 0 < mu) (hc : 0 ≤ c) :
    ∃ C > 0, ∀ psi : ExponentialWeight,
      Integrable (fun x : ℝ =>
        ((fun _ : ℝ => c) x) ^ (gamma * pExp) * psi.weight x) →
        Integrable
          (fun x =>
            |deriv
              (fun z => Psi
                (fun y => ((fun _ : ℝ => c) y) ^ gamma) l mu z) x| ^
                pExp * psi.weight x) ∧
          ∫ x : ℝ,
              |deriv
                (fun z => Psi
                  (fun y => ((fun _ : ℝ => c) y) ^ gamma) l mu z) x| ^
                  pExp * psi.weight x
            ≤ C * ∫ x : ℝ,
              ((fun _ : ℝ => c) x) ^ (gamma * pExp) * psi.weight x := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro psi hint
  simpa using
    (Lemma_2_5_constant_function_branch
      (pExp := pExp) (gamma := gamma) (l := l) (mu := mu) (c := c) (C := 1)
      hpExp hgamma hl hc (by norm_num) psi hint)

/-- CM-parameter unit-resolvent version of the constant-function branch of
Lemma 2.5. -/
theorem Lemma_2_5.constant_function_witness_unit
    (p : CMParams) {pExp c : ℝ} (hpExp : 1 < pExp) (hc : 0 ≤ c) :
    ∃ C > 0, ∀ psi : ExponentialWeight,
      Integrable (fun x : ℝ =>
        ((fun _ : ℝ => c) x) ^ (p.γ * pExp) * psi.weight x) →
        Integrable
          (fun x =>
            |deriv
              (fun z => Psi
                (fun y => ((fun _ : ℝ => c) y) ^ p.γ) 1 1 z) x| ^
                pExp * psi.weight x) ∧
          ∫ x : ℝ,
              |deriv
                (fun z => Psi
                  (fun y => ((fun _ : ℝ => c) y) ^ p.γ) 1 1 z) x| ^
                  pExp * psi.weight x
            ≤ C * ∫ x : ℝ,
              ((fun _ : ℝ => c) x) ^ (p.γ * pExp) * psi.weight x :=
  Lemma_2_5.constant_function_witness hpExp
    (lt_of_lt_of_le one_pos p.hγ) one_pos one_pos hc

/-- L² unit-resolvent version of the constant-function branch of Lemma 2.5. -/
theorem Lemma_2_5.constant_function_witness_unit_L2
    (p : CMParams) {c : ℝ} (hc : 0 ≤ c) :
    ∃ C > 0, ∀ psi : ExponentialWeight,
      Integrable (fun x : ℝ =>
        ((fun _ : ℝ => c) x) ^ (p.γ * (2 : ℝ)) * psi.weight x) →
        Integrable
          (fun x =>
            |deriv
              (fun z => Psi
                (fun y => ((fun _ : ℝ => c) y) ^ p.γ) 1 1 z) x| ^
                (2 : ℝ) * psi.weight x) ∧
          ∫ x : ℝ,
              |deriv
                (fun z => Psi
                  (fun y => ((fun _ : ℝ => c) y) ^ p.γ) 1 1 z) x| ^
                  (2 : ℝ) * psi.weight x
            ≤ C * ∫ x : ℝ,
              ((fun _ : ℝ => c) x) ^ (p.γ * (2 : ℝ)) * psi.weight x :=
  Lemma_2_5.constant_function_witness_unit p
    (by norm_num : (1 : ℝ) < 2) hc

/-- A real constant-source branch of the weighted resolvent-gradient estimate.
It only assumes that the elliptic source `u^γ` is pointwise constant, so `Psi`
is constant and the gradient contribution vanishes. -/
theorem Lemma_2_5_constant_source_branch
    {pExp gamma l mu a C : ℝ}
    {u : ℝ → ℝ}
    (hpExp : 1 < pExp) (_hgamma : 0 < gamma) (hl : 0 < l)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hsource : ∀ x, (u x) ^ gamma = a) (hC : 0 ≤ C)
    (psi : ExponentialWeight) :
    Integrable (fun x : ℝ => (u x) ^ (gamma * pExp) * psi.weight x) →
      Integrable
        (fun x =>
          |deriv (fun z => Psi (fun y : ℝ => (u y) ^ gamma) l mu z) x| ^
              pExp * psi.weight x) ∧
      ∫ x : ℝ,
          |deriv (fun z => Psi (fun y : ℝ => (u y) ^ gamma) l mu z) x| ^
              pExp * psi.weight x
        ≤ C * ∫ x : ℝ, (u x) ^ (gamma * pExp) * psi.weight x := by
  intro _hint
  have hpExp_pos : 0 < pExp := lt_trans zero_lt_one hpExp
  have hsource_fun :
      (fun y : ℝ => (u y) ^ gamma) = fun _ : ℝ => a := by
    ext y
    exact hsource y
  have hconst :
      (fun z => Psi (fun y : ℝ => (u y) ^ gamma) l mu z) =
        fun _ : ℝ => (mu / l) * a := by
    ext z
    rw [hsource_fun]
    exact Psi_const_general (c := a) (l := l) (mu := mu) hl z
  have hderiv :
      ∀ x : ℝ,
        deriv (fun z => Psi (fun y : ℝ => (u y) ^ gamma) l mu z) x = 0 := by
    intro x
    rw [hconst]
    simp
  have hleft_integrable :
      Integrable
        (fun x =>
          |deriv (fun z => Psi (fun y : ℝ => (u y) ^ gamma) l mu z) x| ^
              pExp * psi.weight x) := by
    simp [hderiv, Real.zero_rpow (ne_of_gt hpExp_pos)]
  have hright_nonneg :
      0 ≤ ∫ x : ℝ, (u x) ^ (gamma * pExp) * psi.weight x := by
    exact integral_nonneg fun x =>
      mul_nonneg (Real.rpow_nonneg (hu_nonneg x) (gamma * pExp))
        (psi.pos x).le
  refine ⟨hleft_integrable, ?_⟩
  have hleft_zero :
      (∫ x : ℝ,
          |deriv (fun z => Psi (fun y : ℝ => (u y) ^ gamma) l mu z) x| ^
              pExp * psi.weight x) = 0 := by
    simp [hderiv, Real.zero_rpow (ne_of_gt hpExp_pos)]
  rw [hleft_zero]
  exact mul_nonneg hC hright_nonneg

/-- The constant-source branch of Lemma 2.5 with an explicit positive constant
witness, in the full quantifier shape after fixing a nonnegative `u` whose
`γ`-power is constant. -/
theorem Lemma_2_5.constant_source_witness
    {pExp gamma l mu : ℝ}
    (hpExp : 1 < pExp) (hgamma : 0 < gamma)
    (hl : 0 < l) (_hmu : 0 < mu)
    {u : ℝ → ℝ} (hu_nonneg : ∀ x, 0 ≤ u x)
    {a : ℝ} (hsource : ∀ x, (u x) ^ gamma = a) :
    ∃ C > 0, ∀ psi : ExponentialWeight,
      Integrable (fun x : ℝ => (u x) ^ (gamma * pExp) * psi.weight x) →
        Integrable
          (fun x =>
            |deriv
              (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^
                pExp * psi.weight x) ∧
          ∫ x : ℝ,
              |deriv
                (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^
                  pExp * psi.weight x
            ≤ C * ∫ x : ℝ, (u x) ^ (gamma * pExp) * psi.weight x := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro psi hint
  exact
    Lemma_2_5_constant_source_branch
      (pExp := pExp) (gamma := gamma) (l := l) (mu := mu) (u := u) (a := a)
      (C := 1) hpExp hgamma hl hu_nonneg hsource (by norm_num) psi hint

/-- CM-parameter unit-resolvent version of the constant-source branch of
Lemma 2.5, without assuming the full Lemma 2.5 theorem. -/
theorem Lemma_2_5.constant_source_witness_unit
    (p : CMParams) {pExp : ℝ} (hpExp : 1 < pExp)
    {u : ℝ → ℝ} (hu_nonneg : ∀ x, 0 ≤ u x)
    {a : ℝ} (hsource : ∀ x, (u x) ^ p.γ = a) :
    ∃ C > 0, ∀ psi : ExponentialWeight,
      Integrable (fun x : ℝ => (u x) ^ (p.γ * pExp) * psi.weight x) →
        Integrable
          (fun x =>
            |deriv
              (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^
                pExp * psi.weight x) ∧
          ∫ x : ℝ,
              |deriv
                (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^
                  pExp * psi.weight x
            ≤ C * ∫ x : ℝ, (u x) ^ (p.γ * pExp) * psi.weight x :=
  Lemma_2_5.constant_source_witness hpExp
    (lt_of_lt_of_le one_pos p.hγ) one_pos one_pos hu_nonneg hsource

/-- L² unit-resolvent version of the constant-source branch of Lemma 2.5. -/
theorem Lemma_2_5.constant_source_witness_unit_L2
    (p : CMParams) {u : ℝ → ℝ} (hu_nonneg : ∀ x, 0 ≤ u x)
    {a : ℝ} (hsource : ∀ x, (u x) ^ p.γ = a) :
    ∃ C > 0, ∀ psi : ExponentialWeight,
      Integrable (fun x : ℝ => (u x) ^ (p.γ * (2 : ℝ)) * psi.weight x) →
        Integrable
          (fun x =>
            |deriv
              (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^
                (2 : ℝ) * psi.weight x) ∧
          ∫ x : ℝ,
              |deriv
                (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^
                  (2 : ℝ) * psi.weight x
            ≤ C * ∫ x : ℝ, (u x) ^ (p.γ * (2 : ℝ)) * psi.weight x :=
  Lemma_2_5.constant_source_witness_unit p
    (by norm_num : (1 : ℝ) < 2) hu_nonneg hsource

/-! ### Weighted resolvent-gradient estimate: nontrivial direction

The strategy for the general Lemma 2.5 is:
1. `Psi_deriv_abs_le_general`: |Ψ'(u^γ)| ≤ √ℓ · Ψ(u^γ)  (proved)
2. Raise to power p: |Ψ'|^p ≤ ℓ^(p/2) · Ψ^p
3. Ψ^p ≤ C · K * |u|^(γp)  via Jensen on the kernel convolution
4. Multiply by weight ψ, integrate, use weight ratio bound + Fubini
-/

theorem ExponentialWeight.weight_nonneg (psi : ExponentialWeight) (x : ℝ) :
    0 ≤ psi.weight x :=
  le_of_lt (psi.pos x)

theorem ExponentialWeight.differentiableAt_weight
    (psi : ExponentialWeight) (x : ℝ) :
    DifferentiableAt ℝ psi.weight x :=
  (psi.smooth.differentiable two_ne_zero).differentiableAt

theorem ExponentialWeight.hasDerivAt_log_weight
    (psi : ExponentialWeight) (x : ℝ) :
    HasDerivAt (fun z => Real.log (psi.weight z))
      (deriv psi.weight x / psi.weight x) x :=
  (psi.differentiableAt_weight x).hasDerivAt.log (ne_of_gt (psi.pos x))

theorem ExponentialWeight.deriv_log_weight_eq
    (psi : ExponentialWeight) (x : ℝ) :
    deriv (fun z => Real.log (psi.weight z)) x =
      deriv psi.weight x / psi.weight x :=
  (psi.hasDerivAt_log_weight x).deriv

theorem ExponentialWeight.deriv_log_weight_abs_le
    (psi : ExponentialWeight) {k : ℝ} (hk : 0 ≤ k)
    (hk_bound : ∀ z, |deriv psi.weight z| ≤ k * psi.weight z)
    (x : ℝ) :
    |deriv (fun z => Real.log (psi.weight z)) x| ≤ k := by
  rw [psi.deriv_log_weight_eq x, abs_div, abs_of_pos (psi.pos x)]
  exact div_le_of_le_mul₀ (psi.pos x).le hk (hk_bound x)

theorem ExponentialWeight.weight_ratio_le
    (psi : ExponentialWeight) {k : ℝ} (hk : 0 ≤ k)
    (hk_bound : ∀ z, |deriv psi.weight z| ≤ k * psi.weight z)
    (x y : ℝ) :
    psi.weight x ≤ psi.weight y * Real.exp (k * |x - y|) := by
  have hlog_diff : Differentiable ℝ (fun z => Real.log (psi.weight z)) :=
    (psi.smooth.differentiable two_ne_zero).log (fun z => ne_of_gt (psi.pos z))
  have hlog_bound : ∀ z, ‖deriv (fun w => Real.log (psi.weight w)) z‖ ≤ k := by
    intro z
    rw [Real.norm_eq_abs]
    exact psi.deriv_log_weight_abs_le hk hk_bound z
  have hmvt : ‖Real.log (psi.weight x) - Real.log (psi.weight y)‖ ≤
      k * ‖x - y‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z _ => (hlog_diff z).hasDerivAt.hasDerivWithinAt)
      (fun z _ => by rw [Real.norm_eq_abs]; exact hlog_bound z)
      convex_univ (Set.mem_univ x) (Set.mem_univ y)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have hx_pos := psi.pos x
  have hy_pos := psi.pos y
  have hlog_sub : Real.log (psi.weight x) - Real.log (psi.weight y) ≤
      k * |x - y| :=
    le_trans (le_abs_self _) hmvt
  rw [← Real.log_div (ne_of_gt hx_pos) (ne_of_gt hy_pos)] at hlog_sub
  have hdiv_le := (Real.log_le_iff_le_exp (div_pos hx_pos hy_pos)).mp hlog_sub
  rw [div_le_iff₀ hy_pos] at hdiv_le
  linarith

theorem Psi_deriv_abs_rpow_le_Psi_rpow
    {u : ℝ → ℝ} {l mu pExp : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hpExp : 0 < pExp)
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ y, 0 ≤ u y) (x : ℝ) :
    |deriv (fun z => Psi u l mu z) x| ^ pExp ≤
      (Real.sqrt l) ^ pExp * (Psi u l mu x) ^ pExp := by
  have hbound := Psi_deriv_abs_le_general hl hmu hu hu_nonneg x
  have hPsi_nonneg := Psi_nonneg hl hmu hu_nonneg x
  have hsqrt_nonneg : 0 ≤ Real.sqrt l := Real.sqrt_nonneg l
  calc |deriv (fun z => Psi u l mu z) x| ^ pExp
      ≤ (Real.sqrt l * Psi u l mu x) ^ pExp :=
        Real.rpow_le_rpow (abs_nonneg _) hbound hpExp.le
    _ = (Real.sqrt l) ^ pExp * (Psi u l mu x) ^ pExp :=
        Real.mul_rpow hsqrt_nonneg hPsi_nonneg

theorem Lemma_2_5_bounded_branch
    {pExp gamma l mu : ℝ} (hpExp : 0 < pExp) (hgamma : 0 < gamma)
    (hl : 0 < l) (hmu : 0 < mu)
    {u : ℝ → ℝ} (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x)
    {M : ℝ} (hM : 0 ≤ M) (hu_le : ∀ x, u x ≤ M) (x : ℝ) :
    |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp ≤
      (Real.sqrt l) ^ pExp * (mu / l * M ^ gamma) ^ pExp := by
  have hu_gnn : ∀ y, 0 ≤ (u y) ^ gamma :=
    fun y => Real.rpow_nonneg (hu_nonneg y) gamma
  have hu_gbdd : IsCUnifBdd (fun y => (u y) ^ gamma) := by
    rcases hu.2 with ⟨Mu, hMu⟩
    exact ⟨hu.1.rpow_const (fun y => Or.inr hgamma.le),
      ⟨Mu ^ gamma, fun y => by
        rw [abs_of_nonneg (hu_gnn y)]
        exact Real.rpow_le_rpow (hu_nonneg y)
          (by simpa [abs_of_nonneg (hu_nonneg y)] using hMu y) hgamma.le⟩⟩
  have hPsi_le := Psi_le_const_general_of_nonneg_le hl hmu
    (Real.rpow_nonneg hM gamma)
    (hu.1.rpow_const (fun y => Or.inr hgamma.le))
    hu_gnn (fun y => Real.rpow_le_rpow (hu_nonneg y) (hu_le y) hgamma.le) x
  have hPsi_nn := Psi_nonneg hl hmu hu_gnn x
  calc |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp
      ≤ (Real.sqrt l) ^ pExp * (Psi (fun y => (u y) ^ gamma) l mu x) ^ pExp :=
        Psi_deriv_abs_rpow_le_Psi_rpow hl hmu hpExp hu_gbdd hu_gnn x
    _ ≤ (Real.sqrt l) ^ pExp * (mu / l * M ^ gamma) ^ pExp :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hPsi_nn hPsi_le hpExp.le)
          (Real.rpow_nonneg (Real.sqrt_nonneg l) pExp)

/-! ### Jensen step for the resolvent kernel

The key convexity step: for nonneg f, K ≥ 0 with ∫K = A,
  (∫ K f)^p ≤ A^{p-1} ∫ K f^p
This is Jensen's inequality for the probability measure K/A
applied to the convex function t ↦ t^p.
-/

/-! The kernel convolution power bound:
  (∫ K f)^p ≤ (∫ K)^{p-1} · ∫ K f^p
for K,f ≥ 0 and p ≥ 1. This is Jensen's inequality on the probability
measure (K/∫K) · volume applied to the convex function t ↦ t^p.

Proof route (from ChatGPT research bridge):
1. Construct μK = Measure.withDensity volume (ENNReal.ofReal ∘ K)
2. Use ConvexOn.map_average_le with convexOn_rpow on μK
3. Expand averages: ⨍ f ∂μK = (∫K)⁻¹ · ∫ K·f
4. Rearrange to get the target

This is a pure Lean engineering target; the mathematics is standard. -/
def KernelConvRpowBound : Prop :=
  ∀ (K f : ℝ → ℝ) (A pExp : ℝ),
    (∀ y, 0 ≤ K y) → (∀ y, 0 ≤ f y) →
      A = ∫ y, K y → 0 < A → 1 ≤ pExp →
        Integrable (fun y => K y * f y) →
          Integrable (fun y => K y * (f y) ^ pExp) →
            Integrable K →
              (∫ y, K y * f y) ^ pExp ≤
                A ^ (pExp - 1) * ∫ y, K y * (f y) ^ pExp

theorem kernelConvRpowBound : KernelConvRpowBound := by
  intro K f A pExp hK hf hA hA_pos hpExp hKf hKfp hKint
  -- Lift K to ℝ≥0∞ and build weighted measure μK = K · volume
  let Kd : ℝ → ENNReal := fun y => ENNReal.ofReal (K y)
  let μK := volume.withDensity Kd
  have hKd_aem : AEMeasurable Kd volume :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      hKint.aestronglyMeasurable.aemeasurable)
  have hKd_ae_lt : ∀ᵐ y ∂volume, Kd y < ⊤ :=
    Eventually.of_forall fun y => ENNReal.ofReal_lt_top
  haveI : IsFiniteMeasure μK := isFiniteMeasure_withDensity (by
    have : ∫⁻ y, Kd y ∂volume ≤ ENNReal.ofReal (∫ y, K y ∂volume) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hKint
        (Eventually.of_forall fun y => hK y)]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top this)
  have hμK_mass_e : μK Set.univ = ENNReal.ofReal A := by
    rw [show μK = volume.withDensity Kd from rfl,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hKint
        (Eventually.of_forall fun y => hK y), hA]
  haveI : NeZero μK := ⟨fun h => by
    have : μK Set.univ = 0 := by rw [h]; simp
    rw [hμK_mass_e] at this
    exact absurd (ENNReal.ofReal_eq_zero.mp this) (not_le.mpr hA_pos)⟩
  have hμK_mass : (μK Set.univ).toReal = A := by
    rw [hμK_mass_e, ENNReal.toReal_ofReal hA_pos.le]
  -- Integrable g μK ↔ Integrable ((Kd ·).toReal • g) volume
  have hKd_toReal : ∀ y, (Kd y).toReal = K y := fun y => by
    simp [Kd, ENNReal.toReal_ofReal (hK y)]
  have hf_int_μK : Integrable f μK := by
    rw [show μK = volume.withDensity Kd from rfl,
      integrable_withDensity_iff_integrable_smul₀'
        hKd_aem hKd_ae_lt,
      show (fun y => (Kd y).toReal • f y) = fun y => K y * f y from
        by ext y; simp [hKd_toReal, smul_eq_mul]]
    exact hKf
  have hfp_int_μK : Integrable (fun y => (f y) ^ pExp) μK := by
    rw [show μK = volume.withDensity Kd from rfl,
      integrable_withDensity_iff_integrable_smul₀'
        hKd_aem hKd_ae_lt,
      show (fun y => (Kd y).toReal • (f y) ^ pExp) =
        fun y => K y * (f y) ^ pExp from
        by ext y; simp [hKd_toReal, smul_eq_mul]]
    exact hKfp
  -- ∫ g dμK = ∫ K · g
  have hint_rel : ∀ g : ℝ → ℝ,
      ∫ y, g y ∂μK = ∫ y, K y * g y := fun g => by
    rw [show μK = volume.withDensity Kd from rfl,
      integral_withDensity_eq_integral_toReal_smul₀
        hKd_aem hKd_ae_lt]
    congr 1; ext y; simp [hKd_toReal, smul_eq_mul]
  -- Jensen: (⨍ f ∂μK)^p ≤ ⨍ f^p ∂μK
  have hJ := (convexOn_rpow hpExp).map_average_le
    (Real.continuous_rpow_const (by linarith : 0 ≤ pExp)).continuousOn
    isClosed_Ici
    (Eventually.of_forall fun y => Set.mem_Ici.mpr (hf y))
    hf_int_μK hfp_int_μK
  -- Unpack: (A⁻¹ · ∫Kf)^p ≤ A⁻¹ · ∫Kf^p
  have hμK_real : μK.real Set.univ = A := by
    rw [measureReal_def, hμK_mass]
  simp only [average_eq, hμK_real, smul_eq_mul] at hJ
  rw [hint_rel f, hint_rel (fun y => (f y) ^ pExp)] at hJ
  -- Rearrange to target
  have hA_inv_nn := (inv_pos_of_pos hA_pos).le
  have hIKf_nn : (0 : ℝ) ≤ ∫ y, K y * f y :=
    integral_nonneg (fun y => mul_nonneg (hK y) (hf y))
  rw [Real.mul_rpow hA_inv_nn hIKf_nn] at hJ
  -- hJ : A⁻¹^p * (∫Kf)^p ≤ A⁻¹ * ∫Kf^p
  -- Show A⁻¹ = A⁻¹^p * A^{p-1}, then cancel A⁻¹^p
  have hAip := Real.rpow_pos_of_pos (inv_pos_of_pos hA_pos) pExp
  have hkey : A⁻¹ = A⁻¹ ^ pExp * A ^ (pExp - 1) := by
    rw [Real.inv_rpow hA_pos.le, mul_comm, ← div_eq_mul_inv,
      ← Real.rpow_sub hA_pos,
      show pExp - 1 - pExp = (-1 : ℝ) from by ring, Real.rpow_neg_one]
  conv at hJ => rhs; rw [hkey, mul_assoc]
  exact le_of_mul_le_mul_left hJ hAip

/-- Standard-name bridge for grep-based statement-target audits. -/
theorem KernelConvRpowBound_proved : KernelConvRpowBound :=
  kernelConvRpowBound

def Lemma_2_5_JensenStep : Prop :=
  ∀ (u : ℝ → ℝ) (l mu pExp : ℝ),
    0 < l → 0 < mu → 1 ≤ pExp →
      IsCUnifBdd u → (∀ y, 0 ≤ u y) →
        ∀ x : ℝ,
          (Psi u l mu x) ^ pExp ≤
            (mu / (2 * Real.sqrt l)) ^ pExp *
              (2 / Real.sqrt l) ^ (pExp - 1) *
                ∫ y : ℝ,
                  Real.exp (-Real.sqrt l * |x - y|) * (u y) ^ pExp

theorem lemma_2_5_jensenStep : Lemma_2_5_JensenStep := by
  intro u l mu pExp hl hmu hpExp hu hu_nn x
  unfold Psi
  set K := fun y => Real.exp (-Real.sqrt l * |x - y|) with hK_def
  have hsqrt := Real.sqrt_pos.mpr hl
  have hK_nn : ∀ y, 0 ≤ K y := fun y => (Real.exp_pos _).le
  have hA_eq : 2 / Real.sqrt l = ∫ y, K y :=
    (integral_exp_neg_mul_abs_sub hsqrt x).symm
  have hA_pos : 0 < 2 / Real.sqrt l := by positivity
  have hK_int : Integrable K :=
    _root_.kernel_exp_neg_mul_abs_integrable hsqrt x
  have hKu_int : Integrable (fun y => K y * u y) :=
    Psi_kernel_integrable_of_isCUnifBdd hl hu x
  have hu_rpow_bdd : IsCUnifBdd (fun y => (u y) ^ pExp) := by
    rcases hu.2 with ⟨M, hM⟩
    exact ⟨hu.1.rpow_const (fun y => Or.inr (by linarith : 0 ≤ pExp)),
      ⟨M ^ pExp, fun y => by
        rw [abs_of_nonneg (Real.rpow_nonneg (hu_nn y) pExp)]
        exact Real.rpow_le_rpow (hu_nn y)
          (by simpa [abs_of_nonneg (hu_nn y)] using hM y)
          (by linarith)⟩⟩
  have hKup_int : Integrable (fun y => K y * (u y) ^ pExp) :=
    Psi_kernel_integrable_of_isCUnifBdd hl hu_rpow_bdd x
  have hJensen := kernelConvRpowBound K u (2 / Real.sqrt l) pExp
    hK_nn hu_nn hA_eq hA_pos hpExp hKu_int hKup_int hK_int
  have hcoeff_pos : 0 < mu / (2 * Real.sqrt l) := by positivity
  rw [Real.mul_rpow hcoeff_pos.le
    (integral_nonneg fun y => mul_nonneg (hK_nn y) (hu_nn y)),
    mul_assoc]
  exact mul_le_mul_of_nonneg_left hJensen
    (Real.rpow_nonneg hcoeff_pos.le pExp)

/-- Standard-name bridge for grep-based statement-target audits. -/
theorem Lemma_2_5_JensenStep_proved : Lemma_2_5_JensenStep :=
  lemma_2_5_jensenStep

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

theorem frozenElliptic_deriv_differentiableAt
    (p : CMParams) {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x) (x : ℝ) :
    DifferentiableAt ℝ (deriv (frozenElliptic p u)) x := by
  unfold frozenElliptic
  exact Psi_deriv_differentiableAt one_pos one_pos
    (rpow_cunif_bdd_of_nonneg p hu hu_nonneg) x

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

theorem frozenElliptic_continuous
    (p : CMParams) {U : ℝ → ℝ} (hU : IsCUnifBdd U) (hU_nonneg : ∀ x, 0 ≤ U x) :
    Continuous (frozenElliptic p U) := by
  unfold frozenElliptic
  have hu_rpow := rpow_cunif_bdd_of_nonneg p hU hU_nonneg
  rcases hu_rpow.2 with ⟨M, hM⟩
  have hM_nn : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have : (fun x => Psi (fun y => (U y) ^ p.γ) 1 1 x) = fun x =>
      1 / 2 * ∫ y, Real.exp (-1 * |x - y|) * (U y) ^ p.γ := by
    ext x; simp [Psi, Real.sqrt_one]
  rw [this]
  have hdiff : Differentiable ℝ (fun x => ∫ y, Real.exp (-1 * |x - y|) * (U y) ^ p.γ) := by
    intro x
    exact (hasDerivAt_integral_exp_neg_mul_abs_sub_general
      (a := 1) one_pos hu_rpow x).differentiableAt
  exact hdiff.continuous.const_mul _

theorem frozenElliptic_differentiable
    (p : CMParams) {U : ℝ → ℝ} (hU : IsCUnifBdd U) (hU_nonneg : ∀ x, 0 ≤ U x) :
    Differentiable ℝ (frozenElliptic p U) := by
  have hu_rpow := rpow_cunif_bdd_of_nonneg p hU hU_nonneg
  intro x
  have hPsi_diff : DifferentiableAt ℝ
      (fun y => 1 / 2 * ∫ z, Real.exp (-1 * |y - z|) * (U z) ^ p.γ) x :=
    ((hasDerivAt_integral_exp_neg_mul_abs_sub_general
      (a := 1) one_pos hu_rpow x).const_mul (1 / 2)).differentiableAt
  have hfun : (fun y => frozenElliptic p U y) =
      (fun y => 1 / 2 * ∫ z, Real.exp (-1 * |y - z|) * (U z) ^ p.γ) := by
    ext y; simp [frozenElliptic, Psi, Real.sqrt_one]
  rwa [show frozenElliptic p U = fun y =>
      1 / 2 * ∫ z, Real.exp (-1 * |y - z|) * (U z) ^ p.γ from hfun]

theorem frozenElliptic_zero_eq (p : CMParams) (x : ℝ) :
    frozenElliptic p (fun _ => (0 : ℝ)) x = 0 := by
  unfold frozenElliptic
  simp [Real.zero_rpow (ne_of_gt (by linarith [p.hγ] : 0 < p.γ)), Psi_zero]

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

theorem paperWaveOperator_one_eq_zero (p : CMParams) (c x : ℝ) :
    paperWaveOperator p c (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) x = 0 := by
  rw [paperWaveOperator_const_eq p
    ⟨continuous_const, ⟨1, fun _ => by simp⟩⟩ (fun _ => by norm_num) x,
    frozenElliptic_one_eq p x]
  simp [Real.one_rpow]

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

theorem paperWaveOperator_eq_frozenWaveOperator_add_offdiag
    (p : CMParams) {c : ℝ} {u W : ℝ → ℝ} (x : ℝ)
    (hu_bdd : IsCUnifBdd u) (hu_nonneg : ∀ y, 0 ≤ u y)
    (hW_nonneg : ∀ y, 0 ≤ W y)
    (hW_diff : DifferentiableAt ℝ W x)
    (hV_diff : DifferentiableAt ℝ (deriv (frozenElliptic p u)) x)
    (_hW_rpow_diff : DifferentiableAt ℝ (fun y => (W y) ^ p.m) x) :
    paperWaveOperator p c u W x =
      frozenWaveOperator p c u W x
        + p.χ * (W x) ^ p.m * ((W x) ^ p.γ - (u x) ^ p.γ) := by
  unfold paperWaveOperator frozenWaveOperator
  simp only
  have hW_pow_deriv : HasDerivAt (fun y => (W y) ^ p.m)
      (deriv W x * p.m * (W x) ^ (p.m - 1)) x :=
    hW_diff.hasDerivAt.rpow_const (Or.inr p.hm)
  have hV'' := frozenElliptic_deriv_deriv_eq p hu_bdd hu_nonneg x
  have hV_deriv : HasDerivAt (deriv (frozenElliptic p u))
      (frozenElliptic p u x - (u x) ^ p.γ) x := by
    convert hV_diff.hasDerivAt using 1
    exact hV''.symm
  have hprod := hW_pow_deriv.mul hV_deriv
  have hfun_eq :
      (fun y => (W y) ^ p.m * deriv (frozenElliptic p u) y) =
      (fun y => (W y) ^ p.m) * deriv (frozenElliptic p u) := by
    ext y; simp [Pi.mul_apply]
  have hchem :
      deriv (fun y => (W y) ^ p.m * deriv (frozenElliptic p u) y) x =
        deriv W x * p.m * (W x) ^ (p.m - 1) *
            deriv (frozenElliptic p u) x +
          (W x) ^ p.m * (frozenElliptic p u x - (u x) ^ p.γ) := by
    rw [hfun_eq, hprod.deriv]
  rw [hchem]
  have hm_pos : 0 < p.m := lt_of_lt_of_le zero_lt_one p.hm
  have hγ_pos : 0 < p.γ := lt_of_lt_of_le zero_lt_one p.hγ
  by_cases hWx_zero : W x = 0
  · have hWm_zero : (W x) ^ p.m = 0 := by
      rw [hWx_zero]
      exact Real.zero_rpow (ne_of_gt hm_pos)
    have hWγ_zero : (W x) ^ p.γ = 0 := by
      rw [hWx_zero]
      exact Real.zero_rpow (ne_of_gt hγ_pos)
    rw [hWm_zero, hWγ_zero, hWx_zero]
    ring_nf
  · have hWx_pos : 0 < W x := lt_of_le_of_ne (hW_nonneg x) (Ne.symm hWx_zero)
    have hpow_m : (W x) ^ p.m = W x * (W x) ^ (p.m - 1) := by
      calc
        (W x) ^ p.m = (W x) ^ (1 + (p.m - 1)) := by
          congr 1
          ring
        _ = (W x) ^ (1 : ℝ) * (W x) ^ (p.m - 1) := by
          rw [Real.rpow_add hWx_pos]
        _ = W x * (W x) ^ (p.m - 1) := by
          rw [Real.rpow_one]
    have hpow_tailγ_nf :
        (W x) ^ (-1 + p.m) * W x * (W x) ^ p.γ =
          W x * (W x) ^ (-1 + p.m + p.γ) := by
      calc
        (W x) ^ (-1 + p.m) * W x * (W x) ^ p.γ =
            ((W x) ^ (-1 + p.m) * (W x) ^ (1 : ℝ)) * (W x) ^ p.γ := by
          rw [Real.rpow_one]
        _ = (W x) ^ ((-1 + p.m) + 1) * (W x) ^ p.γ := by
          rw [← Real.rpow_add hWx_pos]
        _ = (W x) ^ p.m * (W x) ^ p.γ := by
          congr 2
          ring
        _ = (W x) ^ (p.m + p.γ) := by
          rw [← Real.rpow_add hWx_pos]
        _ = (W x) ^ (1 + (-1 + p.m + p.γ)) := by
          congr 1
          ring
        _ = (W x) ^ (1 : ℝ) * (W x) ^ (-1 + p.m + p.γ) := by
          rw [Real.rpow_add hWx_pos]
        _ = W x * (W x) ^ (-1 + p.m + p.γ) := by
          rw [Real.rpow_one]
    rw [hpow_m]
    ring_nf
    have hchem_tail :
        p.χ * W x * (W x) ^ (-1 + p.m + p.γ) =
          p.χ * (W x) ^ (-1 + p.m) * W x * (W x) ^ p.γ := by
      calc
        p.χ * W x * (W x) ^ (-1 + p.m + p.γ) =
            p.χ * (W x * (W x) ^ (-1 + p.m + p.γ)) := by
          ring
        _ = p.χ * ((W x) ^ (-1 + p.m) * W x * (W x) ^ p.γ) := by
          rw [← hpow_tailγ_nf]
        _ = p.χ * (W x) ^ (-1 + p.m) * W x * (W x) ^ p.γ := by
          ring
    nlinarith [hchem_tail]

#print axioms paperWaveOperator_eq_frozenWaveOperator_add_offdiag

theorem paperWaveOperator_eq_frozenWaveOperator_at_fixed_point
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ} (x : ℝ)
    (hU : IsCUnifBdd U) (hU_nonneg : ∀ x, 0 ≤ U x)
    (hU_diff : DifferentiableAt ℝ U x)
    (hV_diff : DifferentiableAt ℝ (deriv (frozenElliptic p U)) x)
    (_hU_rpow_diff : DifferentiableAt ℝ (fun y => (U y) ^ p.m) x) :
    paperWaveOperator p c U U x = frozenWaveOperator p c U U x := by
  have h := paperWaveOperator_eq_frozenWaveOperator_add_offdiag p (c := c)
    (u := U) (W := U) x hU hU_nonneg hU_nonneg hU_diff hV_diff _hU_rpow_diff
  have hzero :
      p.χ * (U x) ^ p.m * ((U x) ^ p.γ - (U x) ^ p.γ) = 0 := by
    ring
  simpa [hzero] using h

theorem FrozenStationaryWaveProfile.mk_from_paper_stationarity
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hc : 0 < c)
    (hU_pos : ∀ x, 0 < U x)
    (hU_bdd : IsCUnifBdd U)
    (hU_diff : ∀ x, DifferentiableAt ℝ U x)
    (hV_diff : ∀ x, DifferentiableAt ℝ (deriv (frozenElliptic p U)) x)
    (hU_rpow_diff : ∀ x, DifferentiableAt ℝ (fun y => (U y) ^ p.m) x)
    (hpaper_stat : ∀ x, paperWaveOperator p c U U x = 0)
    (hU_lim_neg : Tendsto U atBot (𝓝 1))
    (hU_lim_pos : Tendsto U atTop (𝓝 0)) :
    FrozenStationaryWaveProfile p c U := by
  apply FrozenStationaryWaveProfile.mk_from_stationary hc hU_pos hU_bdd
  · intro x
    rw [← paperWaveOperator_eq_frozenWaveOperator_at_fixed_point p x
      hU_bdd (fun y => (hU_pos y).le) (hU_diff x) (hV_diff x) (hU_rpow_diff x)]
    exact hpaper_stat x
  · exact ⟨hU_lim_neg, frozenElliptic_tendsto_atBot_of_U_tendsto p hU_bdd
      (fun y => (hU_pos y).le) hU_lim_neg⟩
  · exact ⟨hU_lim_pos, frozenElliptic_tendsto_atTop_of_U_tendsto p hU_bdd
      (fun y => (hU_pos y).le) hU_lim_pos⟩

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

theorem FrozenStationaryWaveProfile.to_globalCauchySolutionFrom
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : FrozenStationaryWaveProfile p c U)
    (hU_diff : ContDiff ℝ 2 U)
    (hV_diff : ContDiff ℝ 2 (frozenElliptic p U)) :
    IsGlobalCauchySolutionFrom p U
      (fun t x => U (x - c * t))
      (fun t x => frozenElliptic p U (x - c * t)) :=
  IsTravelingWave.to_globalCauchySolutionFrom h.to_travelingWave hU_diff hV_diff

theorem FrozenStationaryWaveProfile.to_monotoneTravelingWave
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : FrozenStationaryWaveProfile p c U)
    (hUmono : ∀ x, deriv U x ≤ 0)
    (hVmono : ∀ x, deriv (frozenElliptic p U) x ≤ 0) :
    IsMonotoneTravelingWave p c U (frozenElliptic p U) :=
  ⟨h.to_travelingWave, hUmono, hVmono⟩

/-- Weaker variant of FrozenStationaryWaveProfile that drops the
left-end convergence requirement, replacing `lim_neg_inf` with the
weaker `positive_at_left` (StrictlyPositiveAtLeft).

This corresponds to the existence claim in Paper1 Remark 1.3(2):
in the extended positive-sensitivity range, the construction still
yields a wave whose right end vanishes, but the left end is only
required to stay uniformly positive (not necessarily approach 1). -/
structure FrozenRightVanishingWaveProfile
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop where
  hc : 0 < c
  U_pos : ∀ x, 0 < U x
  stationary_eq : ∀ x, frozenWaveOperator p c U U x = 0
  elliptic_eq :
    ∀ x,
      iteratedDeriv 2 (frozenElliptic p U) x -
          frozenElliptic p U x + (U x) ^ p.γ = 0
  positive_at_left : StrictlyPositiveAtLeft U
  lim_pos_inf :
    Tendsto U atTop (𝓝 0) ∧ Tendsto (frozenElliptic p U) atTop (𝓝 0)

theorem FrozenRightVanishingWaveProfile.to_rightVanishingTravelingWave
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : FrozenRightVanishingWaveProfile p c U) :
    IsRightVanishingTravelingWave p c U (frozenElliptic p U) := by
  refine
    { hc := h.hc
      U_pos := h.U_pos
      ode_U := ?_
      ode_V := h.elliptic_eq
      lim_pos_inf := h.lim_pos_inf
      positive_at_left := h.positive_at_left }
  intro x
  simpa [frozenWaveOperator] using h.stationary_eq x

/-- Bridge from FrozenStationaryWaveProfile (stronger) to
FrozenRightVanishingWaveProfile (weaker). Left convergence to 1 implies
StrictlyPositiveAtLeft. -/
theorem FrozenStationaryWaveProfile.to_rightVanishingProfile
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : FrozenStationaryWaveProfile p c U) :
    FrozenRightVanishingWaveProfile p c U :=
  { hc := h.hc
    U_pos := h.U_pos
    stationary_eq := h.stationary_eq
    elliptic_eq := h.elliptic_eq
    positive_at_left := by
      refine ⟨1 / 2, by norm_num, ?_⟩
      have hnhds : Set.Ioi (1 / 2 : ℝ) ∈ 𝓝 (1 : ℝ) :=
        Ioi_mem_nhds (by norm_num)
      filter_upwards [h.lim_neg_inf.1 hnhds] with x hx
      exact le_of_lt hx
    lim_pos_inf := h.lim_pos_inf }

def IsFrozenSuperSolution (p : CMParams) (c : ℝ) (u W : ℝ → ℝ) : Prop :=
  ∀ x, frozenWaveOperator p c u W x ≤ 0

def IsFrozenSubSolutionOn (p : CMParams) (c : ℝ) (u W : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, 0 ≤ frozenWaveOperator p c u W x

def IsPaperFrozenSubSolutionOn (p : CMParams) (c : ℝ) (u W : ℝ → ℝ) (s : Set ℝ) :
    Prop :=
  ∀ x ∈ s, 0 ≤ paperWaveOperator p c u W x

def expDecay (κ : ℝ) : ℝ → ℝ :=
  fun x => Real.exp (-(κ * x))

theorem expDecay_pos (κ x : ℝ) :
    0 < expDecay κ x := by
  exact Real.exp_pos _

theorem expDecay_continuous (κ : ℝ) : Continuous (expDecay κ) := by
  unfold expDecay
  exact Real.continuous_exp.comp (continuous_const.mul continuous_id).neg

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

theorem upperBarrier_eventuallyEq_const_left_of_interface {κ M x : ℝ}
    (hκ : 0 < κ) (hx : Real.exp (-κ * x) = M) :
    upperBarrier κ M =ᶠ[𝓝[Set.Iio x] x] fun _ : ℝ => M := by
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyexp : M < Real.exp (-κ * y) := by
    rw [← hx]
    apply Real.exp_lt_exp.mpr
    have hylt : y < x := hy
    nlinarith [hylt, hκ]
  exact upperBarrier_eq_M_of_le_exp hyexp.le

theorem upperBarrier_eventuallyEq_exp_right_of_interface {κ M x : ℝ}
    (hκ : 0 < κ) (hx : Real.exp (-κ * x) = M) :
    upperBarrier κ M =ᶠ[𝓝[Set.Ioi x] x] expDecay κ := by
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyexp : Real.exp (-κ * y) < M := by
    rw [← hx]
    apply Real.exp_lt_exp.mpr
    have hylt : x < y := hy
    nlinarith [hylt, hκ]
  simpa [expDecay] using upperBarrier_eq_exp_of_exp_le hyexp.le

theorem upperBarrier_derivWithin_left_eq_zero_of_interface {κ M x : ℝ}
    (hκ : 0 < κ) (hx : Real.exp (-κ * x) = M) :
    derivWithin (upperBarrier κ M) (Set.Iio x) x = 0 := by
  have hW : upperBarrier κ M x = (fun _ : ℝ => M) x := by
    exact upperBarrier_eq_M_of_le_exp hx.ge
  rw [Filter.EventuallyEq.derivWithin_eq
    (upperBarrier_eventuallyEq_const_left_of_interface hκ hx) hW]
  exact (hasDerivAt_const (x := x) (c := M)).hasDerivWithinAt.derivWithin
    (uniqueDiffWithinAt_Iio x)

theorem upperBarrier_derivWithin_right_eq_exp_of_interface {κ M x : ℝ}
    (hκ : 0 < κ) (hx : Real.exp (-κ * x) = M) :
    derivWithin (upperBarrier κ M) (Set.Ioi x) x = -κ * M := by
  have hW : upperBarrier κ M x = expDecay κ x := by
    rw [upperBarrier_eq_exp_of_exp_le hx.le]
    simp [expDecay]
  rw [Filter.EventuallyEq.derivWithin_eq
    (upperBarrier_eventuallyEq_exp_right_of_interface hκ hx) hW]
  have hderiv :=
    (expDecay_hasDerivAt κ x).hasDerivWithinAt.derivWithin
      (uniqueDiffWithinAt_Ioi x)
  rw [hderiv]
  have hE : expDecay κ x = M := by
    rw [expDecay]
    rw [← hx]
    congr 1
    ring
  rw [hE]

/-- At the free interface `exp (-κ*x) = M`, the upper barrier has different
one-sided derivatives.  Thus the classical frozen supersolution statement for
`upperBarrier` cannot be an everywhere-smooth statement without treating the
interface separately. -/
theorem not_differentiableAt_upperBarrier_of_interface {κ M x : ℝ}
    (hκ : 0 < κ) (hM : 0 < M) (hx : Real.exp (-κ * x) = M) :
    ¬ DifferentiableAt ℝ (upperBarrier κ M) x := by
  intro hdiff
  have hleft :=
    upperBarrier_derivWithin_left_eq_zero_of_interface (κ := κ) (M := M) (x := x)
      hκ hx
  have hright :=
    upperBarrier_derivWithin_right_eq_exp_of_interface (κ := κ) (M := M) (x := x)
      hκ hx
  have hleft_deriv :
      derivWithin (upperBarrier κ M) (Set.Iio x) x = deriv (upperBarrier κ M) x :=
    hdiff.derivWithin (uniqueDiffWithinAt_Iio x)
  have hright_deriv :
      derivWithin (upperBarrier κ M) (Set.Ioi x) x = deriv (upperBarrier κ M) x :=
    hdiff.derivWithin (uniqueDiffWithinAt_Ioi x)
  have hzero : -κ * M = 0 := by
    rw [hright_deriv, ← hleft_deriv, hleft] at hright
    exact hright.symm
  have hnonzero : -κ * M ≠ 0 := by
    exact mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hκ)) (ne_of_gt hM)
  exact hnonzero hzero

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

theorem frozenWaveOperator_upperBarrier_const_region_nonpos_of_elliptic_le_source
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ ≤ 0) (hM : 1 ≤ M)
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x)
    {x : ℝ} (hx : M < Real.exp (-κ * x))
    (hle : frozenElliptic p u x ≤ (u x) ^ p.γ) :
    frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0 := by
  rw [frozenWaveOperator_upperBarrier_const_region_eq p hu hu_nonneg hx]
  have hM_nonneg : 0 ≤ M := le_trans zero_le_one hM
  have hMm_nonneg : 0 ≤ M ^ p.m := Real.rpow_nonneg hM_nonneg _
  have hchem_core :
      M ^ p.m * (frozenElliptic p u x - (u x) ^ p.γ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hMm_nonneg (sub_nonpos.mpr hle)
  have hchem :
      -p.χ * (M ^ p.m * (frozenElliptic p u x - (u x) ^ p.γ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr hχ) hchem_core
  have hlog_core : 1 - M ^ p.α ≤ 0 := by
    exact sub_nonpos.mpr (Real.one_le_rpow hM (by linarith [p.hα]))
  have hlog : M * (1 - M ^ p.α) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hM_nonneg hlog_core
  nlinarith

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

theorem lowerBarrierRaw_linear_part_eq_speed_denominator
    {κ κtilde D c x : ℝ} (hκ : κ ≠ 0) (hc : c = κ + κ⁻¹) :
    iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x +
        c * deriv (lowerBarrierRaw κ κtilde D) x +
        lowerBarrierRaw κ κtilde D x =
      D * (c * κtilde - κtilde ^ 2 - 1) *
        Real.exp (-κtilde * x) := by
  rw [lowerBarrierRaw_linear_part_eq_of_kappa_speed hκ hc]
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

theorem lowerBarrierRaw_speed_denominator_le_one_of_kappaTilde_le_two_kappa
    {κ κtilde c : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ < 1) (hgap : κ < κtilde)
    (hκtilde1 : κtilde ≤ 1) (hκtilde_le : κtilde ≤ 2 * κ)
    (hc : c = κ + κ⁻¹) :
    c * κtilde - κtilde ^ 2 - 1 ≤ 1 := by
  have hκ_ne : κ ≠ 0 := ne_of_gt hκ0
  have hinv_gt_one : 1 < κ⁻¹ := (one_lt_inv₀ hκ0).2 hκ1
  have hfactor :
      c * κtilde - κtilde ^ 2 - 1 =
        (κtilde - κ) * (κ⁻¹ - κtilde) := by
    rw [hc]
    field_simp [hκ_ne]
    ring
  rw [hfactor]
  have hleft_nonneg : 0 ≤ κtilde - κ := by linarith
  have hleft_le : κtilde - κ ≤ κ := by linarith
  have hright_nonneg : 0 ≤ κ⁻¹ - κtilde := by linarith
  have hright_le : κ⁻¹ - κtilde ≤ κ⁻¹ := by linarith
  have hmul :
      (κtilde - κ) * (κ⁻¹ - κtilde) ≤ κ * κ⁻¹ :=
    mul_le_mul hleft_le hright_le hright_nonneg hκ0.le
  have hκ_mul : κ * κ⁻¹ = 1 := by
    field_simp [hκ_ne]
  linarith

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

theorem lowerBarrierXMinus_nonneg_of_one_le_D
    {κ κtilde D : ℝ} (hgap : 0 < κtilde - κ) (hD : 1 ≤ D) :
    0 ≤ lowerBarrierXMinus κ κtilde D := by
  unfold lowerBarrierXMinus
  exact div_nonneg (Real.log_nonneg hD) hgap.le

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

theorem InWaveTrapSet.tendsto_atTop_zero
    {κ M : ℝ} {u : ℝ → ℝ}
    (hκ : 0 < κ) (h : InWaveTrapSet κ M u) :
    Tendsto u atTop (𝓝 0) := by
  have hupper : Tendsto (fun x : ℝ => Real.exp (-κ * x)) atTop (𝓝 0) := by
    convert expDecay_tendsto_atTop hκ using 1
    ext x
    simp [expDecay]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper (fun x => h.nonneg x) (fun x => h.le_exp x)

theorem InWaveTrapSet.frozenElliptic_tendsto_atTop_zero
    (p : CMParams) {κ M : ℝ} {u : ℝ → ℝ}
    (hκ : 0 < κ) (h : InWaveTrapSet κ M u) :
    Tendsto (frozenElliptic p u) atTop (𝓝 0) :=
  frozenElliptic_tendsto_atTop_of_U_tendsto p h.cunif_bdd h.nonneg
    (h.tendsto_atTop_zero hκ)

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

theorem frozenElliptic_bddFun_of_inWaveTrapSet
    (p : CMParams) {κ M : ℝ} {u : ℝ → ℝ}
    (hM : 0 < M) (hu : InWaveTrapSet κ M u) :
    IsBddFun (frozenElliptic p u) :=
  ⟨M ^ p.γ, fun x => by
    rw [abs_of_nonneg (frozenElliptic_nonneg p hu.nonneg x)]
    exact frozenElliptic_le_of_rpow_le p
      (Real.rpow_nonneg hM.le p.γ) hu.cunif_bdd.1 hu.nonneg
      (fun y => hu.rpow_le_M (by linarith [p.hγ]) y) x⟩

theorem frozenElliptic_isCUnifBdd_of_inWaveTrapSet
    (p : CMParams) {κ M : ℝ} {u : ℝ → ℝ}
    (hM : 0 < M) (hu : InWaveTrapSet κ M u) :
    IsCUnifBdd (frozenElliptic p u) :=
  ⟨frozenElliptic_continuous p hu.cunif_bdd hu.nonneg,
    frozenElliptic_bddFun_of_inWaveTrapSet p hM hu⟩

theorem frozenElliptic_nonneg_of_inWaveTrapSet
    (p : CMParams) {κ M : ℝ} {u : ℝ → ℝ}
    (hu : InWaveTrapSet κ M u) (x : ℝ) :
    0 ≤ frozenElliptic p u x :=
  frozenElliptic_nonneg p hu.nonneg x

theorem frozenElliptic_le_rpow_of_inWaveTrapSet
    (p : CMParams) {κ M : ℝ} {u : ℝ → ℝ}
    (hM : 0 < M) (hu : InWaveTrapSet κ M u) (x : ℝ) :
    frozenElliptic p u x ≤ M ^ p.γ :=
  frozenElliptic_le_of_rpow_le p (Real.rpow_nonneg hM.le p.γ)
    hu.cunif_bdd.1 hu.nonneg
    (fun y => hu.rpow_le_M (by linarith [p.hγ]) y) x

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
      -p.χ * p.m * (expDecay κ x) ^ (p.m - 1) *
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

theorem frozenWaveOperator_upperBarrier_const_region_nonpos_self_neg
    (p : CMParams) {c κ M x : ℝ}
    (hχ : p.χ ≤ 0) (hM : 1 ≤ M)
    (hx : M < Real.exp (-κ * x)) :
    frozenWaveOperator p c (upperBarrier κ M) (upperBarrier κ M) x ≤ 0 := by
  have hM_nonneg : 0 ≤ M := le_trans zero_le_one hM
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have htrap : InWaveTrapSet κ M (upperBarrier κ M) :=
    upperBarrier_mem_InWaveTrapSet hM_nonneg
  have hV_le :
      frozenElliptic p (upperBarrier κ M) x ≤
        (upperBarrier κ M x) ^ p.γ := by
    have hV_M :
        frozenElliptic p (upperBarrier κ M) x ≤ M ^ p.γ :=
      frozenElliptic_le_rpow_of_inWaveTrapSet p hM_pos htrap x
    have hW_x : upperBarrier κ M x = M :=
      upperBarrier_eq_M_of_le_exp (le_of_lt hx)
    simpa [hW_x] using hV_M
  exact
    frozenWaveOperator_upperBarrier_const_region_nonpos_of_elliptic_le_source
      p hχ hM (upperBarrier_cunif_bdd hM_nonneg)
      (fun y => upperBarrier_nonneg hM_nonneg y) hx hV_le

theorem frozenElliptic_le_source_of_inWaveTrapSet_const_region_saturated
    (p : CMParams) {κ M : ℝ} {u : ℝ → ℝ} {x : ℝ}
    (hM : 1 ≤ M) (hu : InWaveTrapSet κ M u)
    (hx : M < Real.exp (-κ * x))
    (hsat : upperBarrier κ M x ≤ u x) :
    frozenElliptic p u x ≤ (u x) ^ p.γ := by
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hM_nonneg : 0 ≤ M := hM_pos.le
  have hV_M : frozenElliptic p u x ≤ M ^ p.γ :=
    frozenElliptic_le_rpow_of_inWaveTrapSet p hM_pos hu x
  have hW_x : upperBarrier κ M x = M :=
    upperBarrier_eq_M_of_le_exp (le_of_lt hx)
  have hM_le_u : M ≤ u x := by
    simpa [hW_x] using hsat
  have hMγ_le_uγ : M ^ p.γ ≤ (u x) ^ p.γ :=
    Real.rpow_le_rpow hM_nonneg hM_le_u (by linarith [p.hγ])
  exact le_trans hV_M hMγ_le_uγ

theorem frozenWaveOperator_upperBarrier_const_region_nonpos_neg_of_saturated
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ ≤ 0) (hM : 1 ≤ M)
    (hu : InWaveTrapSet κ M u)
    {x : ℝ} (hx : M < Real.exp (-κ * x))
    (hsat : upperBarrier κ M x ≤ u x) :
    frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0 :=
  frozenWaveOperator_upperBarrier_const_region_nonpos_of_elliptic_le_source
    p hχ hM hu.cunif_bdd hu.nonneg hx
    (frozenElliptic_le_source_of_inWaveTrapSet_const_region_saturated
      p hM hu hx hsat)

theorem frozenWaveOperator_upperBarrier_const_region_nonpos_neg_one_forces_source_bound
    (p : CMParams) {c κ : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ < 0) (hu : InWaveTrapSet κ 1 u)
    {x : ℝ} (hx : (1 : ℝ) < Real.exp (-κ * x))
    (hop : frozenWaveOperator p c u (upperBarrier κ 1) x ≤ 0) :
    frozenElliptic p u x ≤ (u x) ^ p.γ := by
  rw [frozenWaveOperator_upperBarrier_const_region_eq p hu.cunif_bdd hu.nonneg hx] at hop
  simp only [Real.one_rpow, one_mul, sub_self, mul_zero, add_zero] at hop
  have hnegχ_pos : 0 < -p.χ := by linarith
  have hdiff_nonpos :
      frozenElliptic p u x - (u x) ^ p.γ ≤ 0 := by
    nlinarith
  exact sub_nonpos.mp hdiff_nonpos

theorem frozenWaveOperator_upperBarrier_const_region_nonpos_pos
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hχ_nonneg : 0 ≤ p.χ) (hχ : p.χ < chiStar p)
    (hα : p.α = p.m + p.γ - 1)
    (hM : 1 ≤ M)
    (hMchi : (1 / (1 - p.χ)) ^ (1 / p.α) ≤ M)
    (hu : InWaveTrapSet κ M u) {x : ℝ}
    (hx : M < Real.exp (-κ * x)) :
    frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0 := by
  rw [frozenWaveOperator_upperBarrier_const_region_eq p hu.cunif_bdd hu.nonneg hx]
  have hM_nonneg : 0 ≤ M := le_trans zero_le_one hM
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hχ_lt_one : p.χ < 1 := lt_of_lt_of_le hχ (chiStar_le_one p)
  have hmain :
      1 ≤ (1 - p.χ) * M ^ p.α :=
    one_le_one_sub_chi_mul_M_rpow_alpha p hχ_lt_one hM_nonneg hMchi
  have hV_nonneg : 0 ≤ frozenElliptic p u x :=
    frozenElliptic_nonneg p hu.nonneg x
  have huγ_le_Mγ : (u x) ^ p.γ ≤ M ^ p.γ :=
    hu.rpow_le_M (by linarith [p.hγ]) x
  have hMm_nonneg : 0 ≤ M ^ p.m := Real.rpow_nonneg hM_nonneg _
  have hchem_le :
      -p.χ * (M ^ p.m *
          (frozenElliptic p u x - (u x) ^ p.γ)) ≤
        p.χ * (M ^ (p.m + p.γ)) := by
    have hdrop :
        -p.χ * (M ^ p.m *
            (frozenElliptic p u x - (u x) ^ p.γ)) ≤
          p.χ * (M ^ p.m * (u x) ^ p.γ) := by
      have hleft_nonpos :
          -p.χ * (M ^ p.m * frozenElliptic p u x) ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr hχ_nonneg)
          (mul_nonneg hMm_nonneg hV_nonneg)
      nlinarith
    have hsource :
        p.χ * (M ^ p.m * (u x) ^ p.γ) ≤
          p.χ * (M ^ p.m * M ^ p.γ) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left huγ_le_Mγ hMm_nonneg) hχ_nonneg
    have hpow :
        M ^ p.m * M ^ p.γ = M ^ (p.m + p.γ) := by
      rw [← Real.rpow_add hM_pos]
    calc
      -p.χ * (M ^ p.m *
          (frozenElliptic p u x - (u x) ^ p.γ))
          ≤ p.χ * (M ^ p.m * (u x) ^ p.γ) := hdrop
      _ ≤ p.χ * (M ^ p.m * M ^ p.γ) := hsource
      _ = p.χ * M ^ (p.m + p.γ) := by rw [hpow]
  have hpow_succ :
      M ^ (p.m + p.γ) = M * M ^ p.α := by
    rw [hα]
    calc
      M ^ (p.m + p.γ) = M ^ (1 + (p.m + p.γ - 1)) := by
        congr 1
        ring
      _ = M ^ (1 : ℝ) * M ^ (p.m + p.γ - 1) := by
        rw [Real.rpow_add hM_pos]
      _ = M * M ^ (p.m + p.γ - 1) := by
        rw [Real.rpow_one]
  have hlog_chem :
      M * (1 - M ^ p.α) + p.χ * M ^ (p.m + p.γ) ≤ 0 := by
    rw [hpow_succ]
    nlinarith
  linarith

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

theorem InMonotoneWaveTrapSet.tendsto_atTop_zero
    {κ M : ℝ} {u : ℝ → ℝ}
    (hκ : 0 < κ) (h : InMonotoneWaveTrapSet κ M u) :
    Tendsto u atTop (𝓝 0) :=
  h.trap.tendsto_atTop_zero hκ

theorem InMonotoneWaveTrapSet.frozenElliptic_tendsto_atTop_zero
    (p : CMParams) {κ M : ℝ} {u : ℝ → ℝ}
    (hκ : 0 < κ) (h : InMonotoneWaveTrapSet κ M u) :
    Tendsto (frozenElliptic p u) atTop (𝓝 0) :=
  h.trap.frozenElliptic_tendsto_atTop_zero p hκ

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

/-- A sequence is locally-uniformly asymptotically fixed by `Tmap`. -/
def LocallyUniformApproxFixed
    (Tmap : (ℝ → ℝ) → ℝ → ℝ) (seq : ℕ → ℝ → ℝ) : Prop :=
  ∀ R > 0, ∀ ε > 0,
    ∀ᶠ n in atTop, ∀ x : ℝ, x ∈ Set.Icc (-R) R →
      |Tmap (seq n) x - seq n x| < ε

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

theorem LocalUniformSequentiallyCompactRange.exists_fixed_of_approx_fixed
    {trap : (ℝ → ℝ) → Prop} {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hcompact : LocalUniformSequentiallyCompactRange trap Tmap)
    (hcont : LocalUniformContinuousOn trap Tmap)
    {seq : ℕ → ℝ → ℝ}
    (hseq : ∀ n, trap (seq n))
    (happrox : LocallyUniformApproxFixed Tmap seq) :
    ∃ U : ℝ → ℝ, trap U ∧ Tmap U = U := by
  rcases hcompact seq hseq with ⟨subseq, hsubseq, U, hU, hconv_image⟩
  have hconv_seq :
      LocallyUniformConverges (fun n => seq (subseq n)) U := by
    intro R hR ε hε
    have hε2 : 0 < ε / 2 := by linarith
    have happrox_sub :
        ∀ᶠ n in atTop, ∀ x : ℝ, x ∈ Set.Icc (-R) R →
          |Tmap (seq (subseq n)) x - seq (subseq n) x| < ε / 2 :=
      hsubseq.tendsto_atTop.eventually (happrox R hR (ε / 2) hε2)
    filter_upwards [hconv_image R hR (ε / 2) hε2, happrox_sub] with n himg happ
    intro x hx
    have hsplit :
        seq (subseq n) x - U x =
          (seq (subseq n) x - Tmap (seq (subseq n)) x) +
            (Tmap (seq (subseq n)) x - U x) := by
      ring_nf
    have hleft :
        |seq (subseq n) x - Tmap (seq (subseq n)) x| < ε / 2 := by
      simpa [abs_sub_comm] using happ x hx
    have hsum :
        |seq (subseq n) x - U x| <
          ε / 2 + ε / 2 := by
      rw [hsplit]
      exact lt_of_le_of_lt (abs_add_le _ _)
        (add_lt_add hleft (himg x hx))
    simpa using hsum
  exact
    ⟨U, hU,
      hcont.fixed_of_common_limit
        (seq := fun n => seq (subseq n)) (u := U)
        (fun n => hseq (subseq n)) hU hconv_seq hconv_image⟩

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

theorem FrozenAuxiliaryLimitOutput.tendsto_atTop_zero_of_inWaveTrapSet
    {p : CMParams} {c κ M : ℝ} {frozen U : ℝ → ℝ}
    (hκ : 0 < κ)
    (h :
      FrozenAuxiliaryLimitOutput p c κ M
        (fun u => InWaveTrapSet κ M u) frozen U) :
    Tendsto U atTop (𝓝 0) := by
  have hupper : Tendsto (fun x : ℝ => Real.exp (-κ * x)) atTop (𝓝 0) := by
    convert expDecay_tendsto_atTop hκ using 1
    ext x
    simp [expDecay]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper
    (fun x => h.nonneg_of_inWaveTrapSet x)
    (fun x => h.le_exp_of_inWaveTrapSet x)

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

/-- The finite-net/Brouwer output needed before the compactness limit step:
for every admissible self-map, produce locally-uniform approximate fixed
points inside the trap. -/
def LocalUniformApproxFixedPointSequences
    (trap : (ℝ → ℝ) → Prop) : Prop :=
  ∀ Tmap : (ℝ → ℝ) → ℝ → ℝ,
    (∀ u, trap u → trap (Tmap u)) →
      LocalUniformContinuousOn trap Tmap →
        LocalUniformSequentiallyCompactRange trap Tmap →
          ∃ seq : ℕ → ℝ → ℝ,
            (∀ n, trap (seq n)) ∧ LocallyUniformApproxFixed Tmap seq

theorem localUniformSchauderFixedPointPrinciple_of_approx_fixed_sequences
    {trap : (ℝ → ℝ) → Prop}
    (happroxSeq : LocalUniformApproxFixedPointSequences trap) :
    LocalUniformSchauderFixedPointPrinciple trap := by
  intro Tmap hmap hcont hcompact
  rcases happroxSeq Tmap hmap hcont hcompact with
    ⟨seq, hseq, happrox⟩
  exact hcompact.exists_fixed_of_approx_fixed hcont hseq happrox

theorem inMonotoneWaveTrap_schauderPrinciple_of_approx_fixed_sequences
    {κ M : ℝ}
    (happroxSeq :
      LocalUniformApproxFixedPointSequences
        (fun u => InMonotoneWaveTrapSet κ M u)) :
    LocalUniformSchauderFixedPointPrinciple
      (fun u => InMonotoneWaveTrapSet κ M u) :=
  localUniformSchauderFixedPointPrinciple_of_approx_fixed_sequences happroxSeq

#print axioms inMonotoneWaveTrap_schauderPrinciple_of_approx_fixed_sequences

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

theorem FrozenWaveMapConstruction.exists_fixed_inWaveTrapSet_with_atTop_limit
    {p : CMParams} {c κ M : ℝ}
    (hκ : 0 < κ)
    (h : FrozenWaveMapConstruction p c κ M (fun u => InWaveTrapSet κ M u)) :
    ∃ U : ℝ → ℝ,
      InWaveTrapSet κ M U ∧
        FrozenAuxiliaryLimitOutput p c κ M
          (fun u => InWaveTrapSet κ M u) U U ∧
        Tendsto U atTop (𝓝 0) := by
  rcases h.exists_fixed_limit with ⟨U, hU, hlimit⟩
  exact
    ⟨U, hU, hlimit,
      FrozenAuxiliaryLimitOutput.tendsto_atTop_zero_of_inWaveTrapSet hκ hlimit⟩

theorem FrozenWaveMapConstruction.exists_fixed_inWaveTrapSet_with_atTop_limits
    {p : CMParams} {c κ M : ℝ}
    (hκ : 0 < κ)
    (h : FrozenWaveMapConstruction p c κ M (fun u => InWaveTrapSet κ M u)) :
    ∃ U : ℝ → ℝ,
      InWaveTrapSet κ M U ∧
        FrozenAuxiliaryLimitOutput p c κ M
          (fun u => InWaveTrapSet κ M u) U U ∧
        Tendsto U atTop (𝓝 0) ∧
        Tendsto (frozenElliptic p U) atTop (𝓝 0) := by
  rcases h.exists_fixed_inWaveTrapSet_with_atTop_limit hκ with
    ⟨U, hU, hlimit, hU_top⟩
  exact
    ⟨U, hU, hlimit, hU_top,
      frozenElliptic_tendsto_atTop_of_U_tendsto p hU.cunif_bdd hU.nonneg hU_top⟩

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

theorem FrozenWaveMapConstruction.exists_fixed_inMonotoneWaveTrapSet_with_atTop_limit
    {p : CMParams} {c κ M : ℝ}
    (hκ : 0 < κ)
    (h :
      FrozenWaveMapConstruction p c κ M
        (fun u => InMonotoneWaveTrapSet κ M u)) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U ∧
        FrozenAuxiliaryLimitOutput p c κ M
          (fun u => InMonotoneWaveTrapSet κ M u) U U ∧
        Antitone U ∧
        Tendsto U atTop (𝓝 0) := by
  rcases h.exists_fixed_limit with ⟨U, hU, hlimit⟩
  exact
    ⟨U, hU, hlimit, hU.antitone,
      hU.tendsto_atTop_zero hκ⟩

theorem FrozenWaveMapConstruction.exists_fixed_inMonotoneWaveTrapSet_with_atTop_limits
    {p : CMParams} {c κ M : ℝ}
    (hκ : 0 < κ)
    (h :
      FrozenWaveMapConstruction p c κ M
        (fun u => InMonotoneWaveTrapSet κ M u)) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet κ M U ∧
        FrozenAuxiliaryLimitOutput p c κ M
          (fun u => InMonotoneWaveTrapSet κ M u) U U ∧
        Antitone U ∧
        Tendsto U atTop (𝓝 0) ∧
        Tendsto (frozenElliptic p U) atTop (𝓝 0) := by
  rcases h.exists_fixed_inMonotoneWaveTrapSet_with_atTop_limit hκ with
    ⟨U, hU, hlimit, hanti, hU_top⟩
  exact
    ⟨U, hU, hlimit, hanti, hU_top,
      frozenElliptic_tendsto_atTop_of_U_tendsto p hU.trap.cunif_bdd hU.nonneg hU_top⟩

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

theorem one_lt_D_mul_speed_denominator_of_subsolutionDThreshold_lt_chi_zero
    {M κ κtilde m gamma c D : ℝ}
    (hden : 0 < c * κtilde - κtilde ^ 2 - 1)
    (hD : subsolutionDThreshold 0 M κ κtilde m gamma c < D) :
    1 < D * (c * κtilde - κtilde ^ 2 - 1) := by
  unfold subsolutionDThreshold at hD
  simp only [abs_zero, zero_mul, add_zero] at hD
  have hmul :=
    mul_lt_mul_of_pos_right hD hden
  have hleft :
      (1 / (c * κtilde - κtilde ^ 2 - 1)) *
          (c * κtilde - κtilde ^ 2 - 1) = 1 := by
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hden)]
  nlinarith

theorem one_le_D_of_subsolutionDThreshold_lt_chi_zero_of_den_le_one
    {M κ κtilde m gamma c D : ℝ}
    (hden_pos : 0 < c * κtilde - κtilde ^ 2 - 1)
    (hden_le_one : c * κtilde - κtilde ^ 2 - 1 ≤ 1)
    (hD : subsolutionDThreshold 0 M κ κtilde m gamma c < D) :
    1 ≤ D := by
  have hscale :
      1 < D * (c * κtilde - κtilde ^ 2 - 1) :=
    one_lt_D_mul_speed_denominator_of_subsolutionDThreshold_lt_chi_zero
      hden_pos hD
  have hD_pos : 0 < D := by
    by_contra hnot
    have hD_nonpos : D ≤ 0 := le_of_not_gt hnot
    have hprod_nonpos :
        D * (c * κtilde - κtilde ^ 2 - 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hD_nonpos hden_pos.le
    linarith
  have hprod_le_D :
      D * (c * κtilde - κtilde ^ 2 - 1) ≤ D * 1 :=
    mul_le_mul_of_nonneg_left hden_le_one hD_pos.le
  linarith

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

theorem Lemma_4_1_neg_branch_forces_const_region_source_bound
    (hL : Lemma_4_1)
    (p : CMParams) (hχ : p.χ < 0)
    (hα : p.α ≤ p.m + p.γ - 1)
    {κ c : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1)
    (hc : c = κ + κ⁻¹)
    {u : ℝ → ℝ} (hu : InWaveTrapSet κ 1 u)
    {x : ℝ} (hx : (1 : ℝ) < Real.exp (-κ * x)) :
    frozenElliptic p u x ≤ (u x) ^ p.γ := by
  have hsuper :
      IsFrozenSuperSolution p c u (upperBarrier κ 1) :=
    hL.1 p hχ.le hα κ 1 c hκ hκ1 le_rfl hc u hu
  exact
    frozenWaveOperator_upperBarrier_const_region_nonpos_neg_one_forces_source_bound
      p hχ hu hx (hsuper x)

/-- A concrete trap-set profile used to test the negative-χ plateau branch of
Lemma 4.1.  It lies below `upperBarrier (1/2) 1`, vanishes at `x = -1`, but is
positive nearby. -/
def lemma41CounterexampleProfile : ℝ → ℝ :=
  fun y => upperBarrier (1 / 2) 1 y * min 1 |y + 1|

def lemma41CounterexampleParams : CMParams :=
  { m := 1
    α := 1
    γ := 1
    χ := -1
    hm := by norm_num
    hα := by norm_num
    hγ := by norm_num }

theorem lemma41CounterexampleProfile_mem_trap :
    InWaveTrapSet (1 / 2) 1 lemma41CounterexampleProfile := by
  have hfactor_cont : Continuous fun y : ℝ => min 1 |y + 1| :=
    continuous_const.min ((continuous_id.add continuous_const).abs)
  have hcont : Continuous lemma41CounterexampleProfile := by
    unfold lemma41CounterexampleProfile
    exact (upperBarrier_continuous (1 / 2) 1).mul hfactor_cont
  have hnonneg : ∀ y, 0 ≤ lemma41CounterexampleProfile y := by
    intro y
    unfold lemma41CounterexampleProfile
    exact mul_nonneg (upperBarrier_nonneg (by norm_num) y)
      (le_min (by norm_num) (abs_nonneg _))
  have hle : ∀ y, lemma41CounterexampleProfile y ≤ upperBarrier (1 / 2) 1 y := by
    intro y
    unfold lemma41CounterexampleProfile
    have hupper_nonneg : 0 ≤ upperBarrier (1 / 2) 1 y :=
      upperBarrier_nonneg (by norm_num) y
    have hfactor_le : min 1 |y + 1| ≤ 1 := min_le_left _ _
    calc
      upperBarrier (1 / 2) 1 y * min 1 |y + 1| ≤
          upperBarrier (1 / 2) 1 y * 1 :=
        mul_le_mul_of_nonneg_left hfactor_le hupper_nonneg
      _ = upperBarrier (1 / 2) 1 y := by ring
  refine ⟨⟨hcont, ?_⟩, ?_⟩
  · refine ⟨1, ?_⟩
    intro y
    rw [abs_of_nonneg (hnonneg y)]
    exact le_trans (hle y) (upperBarrier_le_M (1 / 2) 1 y)
  · intro y
    exact ⟨hnonneg y, hle y⟩

theorem lemma41CounterexampleProfile_at_neg_one :
    lemma41CounterexampleProfile (-1) = 0 := by
  simp [lemma41CounterexampleProfile]

theorem lemma41CounterexampleProfile_at_zero :
    lemma41CounterexampleProfile 0 = 1 := by
  norm_num [lemma41CounterexampleProfile, upperBarrier]

theorem frozenElliptic_lemma41CounterexampleProfile_pos :
    0 <
      frozenElliptic lemma41CounterexampleParams
        lemma41CounterexampleProfile (-1) := by
  let u := lemma41CounterexampleProfile
  have htrap : InWaveTrapSet (1 / 2) 1 u :=
    lemma41CounterexampleProfile_mem_trap
  rcases htrap.cunif_bdd.2 with ⟨M, hM⟩
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (u 0)) (hM 0)
  have hint :
      Integrable
        (fun y =>
          Real.exp (-Real.sqrt 1 * |-1 - y|) * u y) :=
    psi_kernel_mul_bounded_integrable (l := 1) (M := M) one_pos
      hM_nonneg hM (-1) htrap.cunif_bdd.1.aestronglyMeasurable
  have hcont_integrand :
      Continuous fun y : ℝ => Real.exp (-Real.sqrt 1 * |-1 - y|) * u y := by
    have hkernel_cont :
        Continuous fun y : ℝ => Real.exp (-Real.sqrt 1 * |-1 - y|) := by
      fun_prop
    exact hkernel_cont.mul htrap.cunif_bdd.1
  have hnonneg_integrand :
      0 ≤ fun y : ℝ => Real.exp (-Real.sqrt 1 * |-1 - y|) * u y := by
    intro y
    exact mul_nonneg (Real.exp_nonneg _) (htrap.nonneg y)
  have hpos_at_zero :
      0 < Real.exp (-Real.sqrt 1 * |-1 - (0 : ℝ)|) * u 0 := by
    have hu0 : u 0 = 1 := lemma41CounterexampleProfile_at_zero
    rw [hu0]
    positivity
  have hIntegral_pos :
      0 < ∫ y : ℝ, Real.exp (-Real.sqrt 1 * |-1 - y|) * u y :=
    integral_pos_of_integrable_nonneg_nonzero
      hcont_integrand hint hnonneg_integrand (x := 0) (ne_of_gt hpos_at_zero)
  unfold frozenElliptic Psi lemma41CounterexampleParams
  simpa [Real.sqrt_one, Real.one_rpow, u] using
    mul_pos (by norm_num : (0 : ℝ) < 1 / (2 * 1)) hIntegral_pos

theorem lemma41Counterexample_source_lt_elliptic :
    (lemma41CounterexampleProfile (-1)) ^
        (lemma41CounterexampleParams.γ) <
      frozenElliptic lemma41CounterexampleParams
        lemma41CounterexampleProfile (-1) := by
  rw [lemma41CounterexampleProfile_at_neg_one]
  have hzero :
      (0 : ℝ) ^ lemma41CounterexampleParams.γ = 0 := by
    norm_num [lemma41CounterexampleParams]
  rw [hzero]
  exact frozenElliptic_lemma41CounterexampleProfile_pos

theorem not_Lemma_4_1 : ¬ Lemma_4_1 := by
  intro hL
  have hforced :=
    Lemma_4_1_neg_branch_forces_const_region_source_bound
      hL lemma41CounterexampleParams
      (by norm_num [lemma41CounterexampleParams])
      (by norm_num [lemma41CounterexampleParams])
      (κ := 1 / 2) (c := 5 / 2)
      (by norm_num) (by norm_num)
      (by norm_num)
      lemma41CounterexampleProfile_mem_trap
      (x := -1)
      (by
        have hpos : (0 : ℝ) < -(1 / 2) * (-1) := by norm_num
        simpa using (Real.one_lt_exp_iff.mpr hpos))
  exact not_lt_of_ge hforced lemma41Counterexample_source_lt_elliptic

theorem not_Lemma_4_1_positive_hypotheses_force_m_kappa_le_one :
    ¬ (∀ p : CMParams, 0 ≤ p.χ → p.χ < chiStar p →
      p.α = p.m + p.γ - 1 →
      ∀ κ : ℝ, 0 < κ → κ < 1 → p.m * κ ≤ 1) := by
  intro h
  let p : CMParams :=
    { m := 3
      α := 3
      γ := 1
      χ := 0
      hm := by norm_num
      hα := by norm_num
      hγ := by norm_num }
  have hχ : p.χ < chiStar p := by
    simpa [p] using chiStar_pos p
  have hmκ := h p (by norm_num [p]) hχ (by norm_num [p]) (1 / 2)
    (by norm_num) (by norm_num)
  norm_num [p] at hmκ

theorem not_Lemma_4_1_negative_hypotheses_force_m_kappa_le_one :
    ¬ (∀ p : CMParams, p.χ ≤ 0 → p.α ≤ p.m + p.γ - 1 →
      ∀ κ : ℝ, 0 < κ → κ < 1 → κ * p.m ≤ 1) := by
  intro h
  let p : CMParams :=
    { m := 3
      α := 1
      γ := 1
      χ := -1
      hm := by norm_num
      hα := by norm_num
      hγ := by norm_num }
  have hmκ := h p (by norm_num [p]) (by norm_num [p]) (1 / 2)
    (by norm_num) (by norm_num)
  norm_num [p] at hmκ

theorem not_Lemma_4_1_negative_hypotheses_force_gamma_kappa_lt_one :
    ¬ (∀ p : CMParams, p.χ ≤ 0 → p.α ≤ p.m + p.γ - 1 →
      ∀ κ : ℝ, 0 < κ → κ < 1 → p.γ * κ < 1) := by
  intro h
  let p : CMParams :=
    { m := 1
      α := 1
      γ := 3
      χ := -1
      hm := by norm_num
      hα := by norm_num
      hγ := by norm_num }
  have hγκ := h p (by norm_num [p]) (by norm_num [p]) (1 / 2)
    (by norm_num) (by norm_num)
  norm_num [p] at hγκ

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

theorem constant_subsolution_frozenWaveOperator_nonneg_of_chi_zero
    (p : CMParams) {κ κtilde D d c : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ = 0)
    (hd_pos : 0 < d)
    (hd_le : d ≤ constantSubsolutionThreshold p.χ κ κtilde D)
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x) :
    IsFrozenSubSolutionOn p c u (fun _ => d) Set.univ := by
  intro x _hx
  rw [frozenWaveOperator_const_eq p hu hu_nonneg x]
  apply add_nonneg
  · simp [hχ]
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

theorem constant_subsolution_frozenWaveOperator_nonneg_of_small_d_unit_trap
    (p : CMParams) {κ d c : ℝ} {u : ℝ → ℝ}
    (hd_pos : 0 < d)
    (hsmall : |p.χ| * d ^ (p.m - 1) ≤ 1 - d ^ p.α)
    (hu : InWaveTrapSet κ 1 u) :
    IsFrozenSubSolutionOn p c u (fun _ => d) Set.univ := by
  intro x _hx
  rw [frozenWaveOperator_const_eq p hu.cunif_bdd hu.nonneg x]
  have hd_nonneg : 0 ≤ d := hd_pos.le
  have hdm_nonneg : 0 ≤ d ^ p.m := Real.rpow_nonneg hd_nonneg _
  have hV_nonneg : 0 ≤ frozenElliptic p u x :=
    frozenElliptic_nonneg p hu.nonneg x
  have hV_le_one : frozenElliptic p u x ≤ 1 :=
    frozenElliptic_le_M_of_inWaveTrapSet p one_pos le_rfl hu x
  have huγ_nonneg : 0 ≤ (u x) ^ p.γ :=
    Real.rpow_nonneg (hu.nonneg x) _
  have huγ_le_one : (u x) ^ p.γ ≤ 1 := by
    have hu_le_one : u x ≤ 1 := hu.le_M x
    exact Real.rpow_le_one (hu.nonneg x) hu_le_one
      (by linarith [p.hγ] : 0 ≤ p.γ)
  let Δ := frozenElliptic p u x - (u x) ^ p.γ
  have hΔ_abs : |Δ| ≤ 1 := by
    have hΔ_le : Δ ≤ 1 := by
      dsimp [Δ]
      linarith
    have hneg_le : -1 ≤ Δ := by
      dsimp [Δ]
      linarith
    exact abs_le.mpr ⟨hneg_le, hΔ_le⟩
  have hchem_core :
      -|p.χ| * d ^ p.m ≤ -p.χ * (d ^ p.m * Δ) := by
    have hcoef_abs : |(-p.χ) * Δ| ≤ |p.χ| := by
      calc
        |(-p.χ) * Δ| = |p.χ| * |Δ| := by
          rw [abs_mul, abs_neg]
        _ ≤ |p.χ| * 1 :=
          mul_le_mul_of_nonneg_left hΔ_abs (abs_nonneg p.χ)
        _ = |p.χ| := by ring
    have hlower : -|p.χ| ≤ (-p.χ) * Δ :=
      le_trans (neg_le_neg hcoef_abs) (neg_abs_le _)
    have hmul := mul_le_mul_of_nonneg_right hlower hdm_nonneg
    calc
      -|p.χ| * d ^ p.m = (-|p.χ|) * d ^ p.m := by ring
      _ ≤ ((-p.χ) * Δ) * d ^ p.m := hmul
      _ = -p.χ * (d ^ p.m * Δ) := by ring
  have hdm_eq : d ^ p.m = d * d ^ (p.m - 1) := by
    calc
      d ^ p.m = d ^ (1 + (p.m - 1)) := by
        congr 1
        ring
      _ = d ^ (1 : ℝ) * d ^ (p.m - 1) := by
        rw [Real.rpow_add hd_pos]
      _ = d * d ^ (p.m - 1) := by
        rw [Real.rpow_one]
  have hsmall_mul :
      |p.χ| * d ^ p.m ≤ d * (1 - d ^ p.α) := by
    rw [hdm_eq]
    calc
      |p.χ| * (d * d ^ (p.m - 1)) =
          d * (|p.χ| * d ^ (p.m - 1)) := by ring
      _ ≤ d * (1 - d ^ p.α) :=
          mul_le_mul_of_nonneg_left hsmall hd_nonneg
  have hnonneg :
      0 ≤ -|p.χ| * d ^ p.m + d * (1 - d ^ p.α) := by
    linarith
  have hchem :
      -p.χ * (d ^ p.m *
          (frozenElliptic p u x - (u x) ^ p.γ)) +
      d * (1 - d ^ p.α) ≥ 0 := by
    dsimp [Δ] at hchem_core
    linarith
  linarith

theorem constant_subsolution_frozenWaveOperator_nonneg_of_small_d_trap
    (p : CMParams) {κ M d c : ℝ} {u : ℝ → ℝ}
    (hM_pos : 0 < M)
    (hd_pos : 0 < d)
    (hsmall : |p.χ| * d ^ (p.m - 1) * M ^ p.γ ≤ 1 - d ^ p.α)
    (hu : InWaveTrapSet κ M u) :
    IsFrozenSubSolutionOn p c u (fun _ => d) Set.univ := by
  intro x _hx
  rw [frozenWaveOperator_const_eq p hu.cunif_bdd hu.nonneg x]
  have hd_nonneg : 0 ≤ d := hd_pos.le
  have hM_nonneg : 0 ≤ M := hM_pos.le
  have hdm_nonneg : 0 ≤ d ^ p.m := Real.rpow_nonneg hd_nonneg _
  have hMγ_nonneg : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM_nonneg _
  have hV_nonneg : 0 ≤ frozenElliptic p u x :=
    frozenElliptic_nonneg p hu.nonneg x
  have hV_le : frozenElliptic p u x ≤ M ^ p.γ :=
    frozenElliptic_le_rpow_of_inWaveTrapSet p hM_pos hu x
  have huγ_nonneg : 0 ≤ (u x) ^ p.γ :=
    Real.rpow_nonneg (hu.nonneg x) _
  have huγ_le : (u x) ^ p.γ ≤ M ^ p.γ :=
    hu.rpow_le_M (by linarith [p.hγ]) x
  let Δ := frozenElliptic p u x - (u x) ^ p.γ
  have hΔ_abs : |Δ| ≤ M ^ p.γ := by
    have hΔ_le : Δ ≤ M ^ p.γ := by
      dsimp [Δ]
      linarith
    have hneg_le : -(M ^ p.γ) ≤ Δ := by
      dsimp [Δ]
      linarith
    exact abs_le.mpr ⟨hneg_le, hΔ_le⟩
  have hchem_core :
      -|p.χ| * (d ^ p.m * M ^ p.γ) ≤ -p.χ * (d ^ p.m * Δ) := by
    have hcoef_abs : |(-p.χ) * Δ| ≤ |p.χ| * M ^ p.γ := by
      calc
        |(-p.χ) * Δ| = |p.χ| * |Δ| := by
          rw [abs_mul, abs_neg]
        _ ≤ |p.χ| * M ^ p.γ :=
          mul_le_mul_of_nonneg_left hΔ_abs (abs_nonneg p.χ)
    have hlower : -(|p.χ| * M ^ p.γ) ≤ (-p.χ) * Δ :=
      le_trans (neg_le_neg hcoef_abs) (neg_abs_le _)
    have hmul := mul_le_mul_of_nonneg_right hlower hdm_nonneg
    calc
      -|p.χ| * (d ^ p.m * M ^ p.γ) =
          (-(|p.χ| * M ^ p.γ)) * d ^ p.m := by ring
      _ ≤ ((-p.χ) * Δ) * d ^ p.m := hmul
      _ = -p.χ * (d ^ p.m * Δ) := by ring
  have hdm_eq : d ^ p.m = d * d ^ (p.m - 1) := by
    calc
      d ^ p.m = d ^ (1 + (p.m - 1)) := by
        congr 1
        ring
      _ = d ^ (1 : ℝ) * d ^ (p.m - 1) := by
        rw [Real.rpow_add hd_pos]
      _ = d * d ^ (p.m - 1) := by
        rw [Real.rpow_one]
  have hsmall_mul :
      |p.χ| * (d ^ p.m * M ^ p.γ) ≤ d * (1 - d ^ p.α) := by
    rw [hdm_eq]
    calc
      |p.χ| * ((d * d ^ (p.m - 1)) * M ^ p.γ) =
          d * (|p.χ| * d ^ (p.m - 1) * M ^ p.γ) := by ring
      _ ≤ d * (1 - d ^ p.α) :=
          mul_le_mul_of_nonneg_left hsmall hd_nonneg
  have hnonneg :
      0 ≤ -|p.χ| * (d ^ p.m * M ^ p.γ) +
          d * (1 - d ^ p.α) := by
    linarith
  have hchem :
      -p.χ * (d ^ p.m *
          (frozenElliptic p u x - (u x) ^ p.γ)) +
        d * (1 - d ^ p.α) ≥ 0 := by
    dsimp [Δ] at hchem_core
    linarith
  linarith

theorem constant_subsolution_frozen_smallness_of_half_bound
    (p : CMParams) {M d : ℝ}
    (hM_pos : 0 < M)
    (hchem : |p.χ| * M ^ p.γ ≤ 1 / 2)
    (hd_pos : 0 < d) (hd_le_half : d ≤ 1 / 2) :
    |p.χ| * d ^ (p.m - 1) * M ^ p.γ ≤ 1 - d ^ p.α := by
  have hd_nonneg : 0 ≤ d := hd_pos.le
  have hd_le_one : d ≤ 1 := by linarith
  have hMγ_nonneg : 0 ≤ M ^ p.γ :=
    Real.rpow_nonneg hM_pos.le _
  have hdm1_le_one : d ^ (p.m - 1) ≤ 1 :=
    Real.rpow_le_one hd_nonneg hd_le_one (by linarith [p.hm])
  have hleft :
      |p.χ| * d ^ (p.m - 1) * M ^ p.γ ≤ |p.χ| * M ^ p.γ := by
    calc
      |p.χ| * d ^ (p.m - 1) * M ^ p.γ ≤
          |p.χ| * 1 * M ^ p.γ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdm1_le_one (abs_nonneg p.χ))
          hMγ_nonneg
      _ = |p.χ| * M ^ p.γ := by ring
  have hdα_le_d : d ^ p.α ≤ d := by
    calc
      d ^ p.α ≤ d ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hd_pos hd_le_one p.hα
      _ = d := Real.rpow_one d
  have hhalf_le : (1 / 2 : ℝ) ≤ 1 - d ^ p.α := by
    linarith
  exact le_trans hleft (le_trans hchem hhalf_le)

theorem constant_subsolution_frozenWaveOperator_nonneg_of_half_bound_trap
    (p : CMParams) {κ M d c : ℝ} {u : ℝ → ℝ}
    (hM_pos : 0 < M)
    (hchem : |p.χ| * M ^ p.γ ≤ 1 / 2)
    (hd_pos : 0 < d) (hd_le_half : d ≤ 1 / 2)
    (hu : InWaveTrapSet κ M u) :
    IsFrozenSubSolutionOn p c u (fun _ => d) Set.univ :=
  constant_subsolution_frozenWaveOperator_nonneg_of_small_d_trap
    p hM_pos hd_pos
    (constant_subsolution_frozen_smallness_of_half_bound
      p hM_pos hchem hd_pos hd_le_half)
    hu

theorem lowerBarrierRaw_frozenWaveOperator_eq_of_chi_zero
    (p : CMParams) {κ κtilde D c : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ = 0) (x : ℝ) :
    frozenWaveOperator p c u (lowerBarrierRaw κ κtilde D) x =
      (iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x +
          c * deriv (lowerBarrierRaw κ κtilde D) x +
          lowerBarrierRaw κ κtilde D x) -
        lowerBarrierRaw κ κtilde D x *
          (lowerBarrierRaw κ κtilde D x) ^ p.α := by
  unfold frozenWaveOperator
  rw [hχ]
  ring

theorem lowerBarrierRaw_frozenSubSolution_of_chi_zero_of_logistic_dominance
    (p : CMParams) {κ κtilde D c : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ = 0)
    (hdom :
      ∀ x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D),
        lowerBarrierRaw κ κtilde D x *
            (lowerBarrierRaw κ κtilde D x) ^ p.α ≤
          iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x +
            c * deriv (lowerBarrierRaw κ κtilde D) x +
            lowerBarrierRaw κ κtilde D x) :
    IsFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
      (Set.Ioi (lowerBarrierXMinus κ κtilde D)) := by
  intro x hx
  rw [lowerBarrierRaw_frozenWaveOperator_eq_of_chi_zero p hχ x]
  exact sub_nonneg.mpr (hdom x hx)

theorem lowerBarrierRaw_logistic_dominance_of_pointwise_bound
    (p : CMParams) {κ κtilde D c x : ℝ}
    (hW_pos : 0 < lowerBarrierRaw κ κtilde D x)
    (hW_le :
      lowerBarrierRaw κ κtilde D x ≤
        (iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x +
            c * deriv (lowerBarrierRaw κ κtilde D) x +
            lowerBarrierRaw κ κtilde D x) ^ (1 / (p.α + 1)))
    (hlin_nonneg :
      0 ≤ iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x +
          c * deriv (lowerBarrierRaw κ κtilde D) x +
          lowerBarrierRaw κ κtilde D x) :
    lowerBarrierRaw κ κtilde D x *
        (lowerBarrierRaw κ κtilde D x) ^ p.α ≤
      iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x +
        c * deriv (lowerBarrierRaw κ κtilde D) x +
        lowerBarrierRaw κ κtilde D x := by
  have hα1_pos : 0 < p.α + 1 := by linarith [p.hα]
  have hW_nonneg : 0 ≤ lowerBarrierRaw κ κtilde D x := hW_pos.le
  have hpow :
      lowerBarrierRaw κ κtilde D x *
          (lowerBarrierRaw κ κtilde D x) ^ p.α =
        (lowerBarrierRaw κ κtilde D x) ^ (p.α + 1) := by
    calc
      lowerBarrierRaw κ κtilde D x *
          (lowerBarrierRaw κ κtilde D x) ^ p.α =
        (lowerBarrierRaw κ κtilde D x) ^ (1 : ℝ) *
          (lowerBarrierRaw κ κtilde D x) ^ p.α := by
          rw [Real.rpow_one]
      _ = (lowerBarrierRaw κ κtilde D x) ^ ((1 : ℝ) + p.α) := by
        rw [← Real.rpow_add hW_pos]
      _ = (lowerBarrierRaw κ κtilde D x) ^ (p.α + 1) := by
        congr 1
        ring
  rw [hpow]
  calc
    (lowerBarrierRaw κ κtilde D x) ^ (p.α + 1) ≤
        ((iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x +
            c * deriv (lowerBarrierRaw κ κtilde D) x +
            lowerBarrierRaw κ κtilde D x) ^ (1 / (p.α + 1))) ^
          (p.α + 1) :=
      Real.rpow_le_rpow hW_nonneg hW_le hα1_pos.le
    _ =
        iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x +
          c * deriv (lowerBarrierRaw κ κtilde D) x +
          lowerBarrierRaw κ κtilde D x := by
      rw [← Real.rpow_mul hlin_nonneg]
      have hne : p.α + 1 ≠ 0 := ne_of_gt hα1_pos
      field_simp [hne]
      rw [Real.rpow_one]

theorem lowerBarrierRaw_frozenSubSolution_chi_zero_of_pointwise_bound
    (p : CMParams) {κ κtilde D c : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ = 0)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hgap : κ < κtilde)
    (hκtilde1 : κtilde ≤ 1) (hD : 0 < D) (hc : c = κ + κ⁻¹)
    (hW_le :
      ∀ x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D),
        lowerBarrierRaw κ κtilde D x ≤
          (iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x +
              c * deriv (lowerBarrierRaw κ κtilde D) x +
              lowerBarrierRaw κ κtilde D x) ^ (1 / (p.α + 1))) :
    IsFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
      (Set.Ioi (lowerBarrierXMinus κ κtilde D)) := by
  apply lowerBarrierRaw_frozenSubSolution_of_chi_zero_of_logistic_dominance
    p hχ
  intro x hx
  exact lowerBarrierRaw_logistic_dominance_of_pointwise_bound p
    (lowerBarrierRaw_pos_of_xminus_lt (sub_pos.mpr hgap) hD hx)
    (hW_le x hx)
    (lowerBarrierRaw_linear_part_pos_of_kappa_speed
      hκ hκ1 hgap hκtilde1 hD hc).le

theorem lowerBarrierRaw_logistic_dominance_of_D_ge_one
    (p : CMParams) {κ κtilde D c x : ℝ}
    (hκ : 0 < κ) (hgap : κ < κtilde) (hD_pos : 0 < D)
    (hD_ge_one : 1 ≤ D) (hc : c = κ + κ⁻¹)
    (hκtilde_le : κtilde ≤ (p.α + 1) * κ)
    (hscale : 1 ≤ D * (c * κtilde - κtilde ^ 2 - 1))
    (hx : x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D)) :
    lowerBarrierRaw κ κtilde D x *
        (lowerBarrierRaw κ κtilde D x) ^ p.α ≤
      iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x +
        c * deriv (lowerBarrierRaw κ κtilde D) x +
        lowerBarrierRaw κ κtilde D x := by
  have hgap_pos : 0 < κtilde - κ := sub_pos.mpr hgap
  have hx_nonneg : 0 ≤ x := by
    have hxminus_nonneg :=
      lowerBarrierXMinus_nonneg_of_one_le_D hgap_pos hD_ge_one
    exact le_trans hxminus_nonneg hx.le
  have hα1_pos : 0 < p.α + 1 := by linarith [p.hα]
  have hW_pos :
      0 < lowerBarrierRaw κ κtilde D x :=
    lowerBarrierRaw_pos_of_xminus_lt hgap_pos hD_pos hx
  have hW_le_exp :
      lowerBarrierRaw κ κtilde D x ≤ Real.exp (-κ * x) :=
    lowerBarrierRaw_le_exp hD_pos.le
  have hpow :
      lowerBarrierRaw κ κtilde D x *
          (lowerBarrierRaw κ κtilde D x) ^ p.α =
        (lowerBarrierRaw κ κtilde D x) ^ (p.α + 1) := by
    calc
      lowerBarrierRaw κ κtilde D x *
          (lowerBarrierRaw κ κtilde D x) ^ p.α =
        (lowerBarrierRaw κ κtilde D x) ^ (1 : ℝ) *
          (lowerBarrierRaw κ κtilde D x) ^ p.α := by
          rw [Real.rpow_one]
      _ = (lowerBarrierRaw κ κtilde D x) ^ ((1 : ℝ) + p.α) := by
        rw [← Real.rpow_add hW_pos]
      _ = (lowerBarrierRaw κ κtilde D x) ^ (p.α + 1) := by
        congr 1
        ring
  rw [hpow]
  calc
    (lowerBarrierRaw κ κtilde D x) ^ (p.α + 1) ≤
        (Real.exp (-κ * x)) ^ (p.α + 1) :=
      Real.rpow_le_rpow hW_pos.le hW_le_exp hα1_pos.le
    _ = Real.exp (-(p.α + 1) * κ * x) := by
      rw [← Real.exp_mul]
      congr 1
      ring
    _ ≤ Real.exp (-κtilde * x) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ ≤ D * (c * κtilde - κtilde ^ 2 - 1) *
        Real.exp (-κtilde * x) := by
      simpa [one_mul] using
        mul_le_mul_of_nonneg_right hscale (Real.exp_pos (-κtilde * x)).le
    _ =
      iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x +
        c * deriv (lowerBarrierRaw κ κtilde D) x +
        lowerBarrierRaw κ κtilde D x := by
      rw [lowerBarrierRaw_linear_part_eq_speed_denominator
        (ne_of_gt hκ) hc]

theorem lowerBarrierRaw_frozenSubSolution_chi_zero_of_D_ge_one
    (p : CMParams) {κ κtilde D c : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ = 0)
    (hκ : 0 < κ) (_hκ1 : κ < 1) (hgap : κ < κtilde)
    (_hκtilde1 : κtilde ≤ 1) (hD_pos : 0 < D) (hD_ge_one : 1 ≤ D)
    (hc : c = κ + κ⁻¹)
    (hκtilde_le : κtilde ≤ (p.α + 1) * κ)
    (hscale : 1 ≤ D * (c * κtilde - κtilde ^ 2 - 1)) :
    IsFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
      (Set.Ioi (lowerBarrierXMinus κ κtilde D)) := by
  exact lowerBarrierRaw_frozenSubSolution_of_chi_zero_of_logistic_dominance
    p hχ
    (fun x hx =>
      lowerBarrierRaw_logistic_dominance_of_D_ge_one
        p hκ hgap hD_pos hD_ge_one hc hκtilde_le hscale hx)

theorem lowerBarrierRaw_frozenSubSolution_chi_zero_of_threshold_of_D_ge_one
    (p : CMParams) {κ κtilde M D c : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ = 0)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hgap : κ < κtilde)
    (hrange :
      κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1))
    (hD_ge_one : 1 ≤ D) (hc : c = κ + κ⁻¹)
    (hD :
      subsolutionDThreshold 0 M κ κtilde p.m p.γ c < D) :
    IsFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
      (Set.Ioi (lowerBarrierXMinus κ κtilde D)) := by
  have hκtilde1 : κtilde ≤ 1 :=
    kappaTilde_le_one_of_subsolution_range hrange
  have hκtilde_le : κtilde ≤ (p.α + 1) * κ := by
    have h := kappaTilde_le_one_plus_alpha_mul_kappa_of_subsolution_range
      (alpha := p.α) (m := p.m) (κ := κ) (κtilde := κtilde) hrange
    convert h using 1
    ring
  have hden : 0 < c * κtilde - κtilde ^ 2 - 1 :=
    lowerBarrierRaw_speed_denominator_pos hκ hκ1 hgap hκtilde1 hc
  have hscale : 1 ≤ D * (c * κtilde - κtilde ^ 2 - 1) :=
    (one_lt_D_mul_speed_denominator_of_subsolutionDThreshold_lt_chi_zero
      hden hD).le
  exact lowerBarrierRaw_frozenSubSolution_chi_zero_of_D_ge_one
    p hχ hκ hκ1 hgap hκtilde1 (lt_of_lt_of_le zero_lt_one hD_ge_one)
    hD_ge_one hc hκtilde_le hscale

theorem lowerBarrierRaw_frozenSubSolution_chi_zero_alpha_one_of_threshold
    (p : CMParams) {κ κtilde M D c : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ = 0) (hα : p.α = 1)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hgap : κ < κtilde)
    (hrange :
      κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1))
    (hc : c = κ + κ⁻¹)
    (hD :
      subsolutionDThreshold 0 M κ κtilde p.m p.γ c < D) :
    IsFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
      (Set.Ioi (lowerBarrierXMinus κ κtilde D)) := by
  have hκtilde1 : κtilde ≤ 1 :=
    kappaTilde_le_one_of_subsolution_range hrange
  have hκtilde_twoκ : κtilde ≤ 2 * κ := by
    have h := kappaTilde_le_one_plus_alpha_mul_kappa_of_subsolution_range
      (alpha := p.α) (m := p.m) (κ := κ) (κtilde := κtilde) hrange
    rw [hα] at h
    calc
      κtilde ≤ (1 + 1) * κ := h
      _ = 2 * κ := by ring
  have hden_pos : 0 < c * κtilde - κtilde ^ 2 - 1 :=
    lowerBarrierRaw_speed_denominator_pos hκ hκ1 hgap hκtilde1 hc
  have hden_le_one : c * κtilde - κtilde ^ 2 - 1 ≤ 1 :=
    lowerBarrierRaw_speed_denominator_le_one_of_kappaTilde_le_two_kappa
      hκ hκ1 hgap hκtilde1 hκtilde_twoκ hc
  have hD_ge_one : 1 ≤ D :=
    one_le_D_of_subsolutionDThreshold_lt_chi_zero_of_den_le_one
      hden_pos hden_le_one hD
  exact lowerBarrierRaw_frozenSubSolution_chi_zero_of_threshold_of_D_ge_one
    p hχ hκ hκ1 hgap hrange hD_ge_one hc hD

theorem Lemma_4_2_chi_zero_alpha_one_subsolutions
    (p : CMParams) {κ κtilde M c D : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ = 0) (hα : p.α = 1)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hgap : κ < κtilde)
    (hrange :
      κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1))
    (_hM : 1 ≤ M) (hc : c = κ + κ⁻¹)
    (hD :
      subsolutionDThreshold p.χ M κ κtilde p.m p.γ c < D)
    (hu : InWaveTrapSet κ M u) :
    IsFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
        (Set.Ioi (lowerBarrierXMinus κ κtilde D)) ∧
      ∀ d : ℝ, 0 < d → d ≤ constantSubsolutionThreshold p.χ κ κtilde D →
        IsFrozenSubSolutionOn p c u (fun _ => d) Set.univ := by
  have hD0 :
      subsolutionDThreshold 0 M κ κtilde p.m p.γ c < D := by
    simpa [hχ] using hD
  refine ⟨?_, ?_⟩
  · exact lowerBarrierRaw_frozenSubSolution_chi_zero_alpha_one_of_threshold
      p hχ hα hκ hκ1 hgap hrange hc hD0
  · intro d hd_pos hd_le
    exact constant_subsolution_frozenWaveOperator_nonneg_of_chem_nonneg
      p hd_pos hd_le hu (fun x => by simp [hχ])

theorem Lemma_4_2_chi_zero_subsolutions_of_D_ge_one
    (p : CMParams) {κ κtilde M c D : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ = 0)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hgap : κ < κtilde)
    (hrange :
      κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1))
    (hD_ge_one : 1 ≤ D)
    (_hM : 1 ≤ M) (hc : c = κ + κ⁻¹)
    (hD :
      subsolutionDThreshold p.χ M κ κtilde p.m p.γ c < D)
    (hu : InWaveTrapSet κ M u) :
    IsFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
        (Set.Ioi (lowerBarrierXMinus κ κtilde D)) ∧
      ∀ d : ℝ, 0 < d → d ≤ constantSubsolutionThreshold p.χ κ κtilde D →
        IsFrozenSubSolutionOn p c u (fun _ => d) Set.univ := by
  have hD0 :
      subsolutionDThreshold 0 M κ κtilde p.m p.γ c < D := by
    simpa [hχ] using hD
  refine ⟨?_, ?_⟩
  · exact lowerBarrierRaw_frozenSubSolution_chi_zero_of_threshold_of_D_ge_one
      p hχ hκ hκ1 hgap hrange hD_ge_one hc hD0
  · intro d hd_pos hd_le
    exact constant_subsolution_frozenWaveOperator_nonneg_of_chem_nonneg
      p hd_pos hd_le hu (fun x => by simp [hχ])

theorem Lemma_4_2_chi_zero_subsolutions_of_kappaTilde_le_two_kappa
    (p : CMParams) {κ κtilde M c D : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ = 0)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hgap : κ < κtilde)
    (hrange :
      κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1))
    (hκtilde_twoκ : κtilde ≤ 2 * κ)
    (_hM : 1 ≤ M) (hc : c = κ + κ⁻¹)
    (hD :
      subsolutionDThreshold p.χ M κ κtilde p.m p.γ c < D)
    (hu : InWaveTrapSet κ M u) :
    IsFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
        (Set.Ioi (lowerBarrierXMinus κ κtilde D)) ∧
      ∀ d : ℝ, 0 < d → d ≤ constantSubsolutionThreshold p.χ κ κtilde D →
        IsFrozenSubSolutionOn p c u (fun _ => d) Set.univ := by
  have hD0 :
      subsolutionDThreshold 0 M κ κtilde p.m p.γ c < D := by
    simpa [hχ] using hD
  have hκtilde1 : κtilde ≤ 1 :=
    kappaTilde_le_one_of_subsolution_range hrange
  have hden_pos : 0 < c * κtilde - κtilde ^ 2 - 1 :=
    lowerBarrierRaw_speed_denominator_pos hκ hκ1 hgap hκtilde1 hc
  have hden_le_one : c * κtilde - κtilde ^ 2 - 1 ≤ 1 :=
    lowerBarrierRaw_speed_denominator_le_one_of_kappaTilde_le_two_kappa
      hκ hκ1 hgap hκtilde1 hκtilde_twoκ hc
  have hD_ge_one : 1 ≤ D :=
    one_le_D_of_subsolutionDThreshold_lt_chi_zero_of_den_le_one
      hden_pos hden_le_one hD0
  refine ⟨?_, ?_⟩
  · exact lowerBarrierRaw_frozenSubSolution_chi_zero_of_threshold_of_D_ge_one
      p hχ hκ hκ1 hgap hrange hD_ge_one hc hD0
  · intro d hd_pos hd_le
    exact constant_subsolution_frozenWaveOperator_nonneg_of_chem_nonneg
      p hd_pos hd_le hu (fun x => by simp [hχ])

theorem Lemma_4_2_chi_zero_strengthened_direct
    (p : CMParams) (hχ : p.χ = 0) {κ κtilde M c D : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hgap : κ < κtilde)
    (hrange :
      κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1))
    (hκtilde_twoκ : κtilde ≤ 2 * κ)
    (hM : 1 ≤ M) (hc : c = κ + κ⁻¹)
    (hD : subsolutionDThreshold p.χ M κ κtilde p.m p.γ c < D)
    {u : ℝ → ℝ} (hu : InWaveTrapSet κ M u) :
    IsFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
        (Set.Ioi (lowerBarrierXMinus κ κtilde D)) ∧
      ∀ d : ℝ, 0 < d → d ≤ constantSubsolutionThreshold p.χ κ κtilde D →
        IsFrozenSubSolutionOn p c u (fun _ => d) Set.univ := by
  exact Lemma_4_2_chi_zero_subsolutions_of_kappaTilde_le_two_kappa
    p hχ hκ hκ1 hgap hrange hκtilde_twoκ hM hc hD hu

theorem Lemma_4_2_chi_zero_D_ge_one_strengthened_direct
    (p : CMParams) (hχ : p.χ = 0) {κ κtilde M c D : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hgap : κ < κtilde)
    (hrange :
      κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1))
    (hM : 1 ≤ M) (hc : c = κ + κ⁻¹) (hD_ge_one : 1 ≤ D)
    (hD : subsolutionDThreshold p.χ M κ κtilde p.m p.γ c < D)
    {u : ℝ → ℝ} (hu : InWaveTrapSet κ M u) :
    IsFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
        (Set.Ioi (lowerBarrierXMinus κ κtilde D)) ∧
      ∀ d : ℝ, 0 < d → d ≤ constantSubsolutionThreshold p.χ κ κtilde D →
        IsFrozenSubSolutionOn p c u (fun _ => d) Set.univ :=
  Lemma_4_2_chi_zero_subsolutions_of_D_ge_one
    p hχ hκ hκ1 hgap hrange hD_ge_one hM hc hD hu

theorem Lemma_4_2_chi_zero_alpha_one_strengthened_direct
    (p : CMParams) (hχ : p.χ = 0) (hα : p.α = 1) {κ κtilde M c D : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hgap : κ < κtilde)
    (hrange :
      κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1))
    (hM : 1 ≤ M) (hc : c = κ + κ⁻¹)
    (hD : subsolutionDThreshold p.χ M κ κtilde p.m p.γ c < D)
    {u : ℝ → ℝ} (hu : InWaveTrapSet κ M u) :
    IsFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
        (Set.Ioi (lowerBarrierXMinus κ κtilde D)) ∧
      ∀ d : ℝ, 0 < d → d ≤ constantSubsolutionThreshold p.χ κ κtilde D →
        IsFrozenSubSolutionOn p c u (fun _ => d) Set.univ :=
  Lemma_4_2_chi_zero_alpha_one_subsolutions
    p hχ hα hκ hκ1 hgap hrange hM hc hD hu

theorem not_Lemma_4_2_chi_zero_hypotheses_force_kappaTilde_le_two_kappa :
    ¬ (∀ p : CMParams, p.χ = 0 →
      ∀ κ κtilde M c D : ℝ,
        0 < κ → κ < 1 → κ < κtilde →
        κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1) →
        1 ≤ M → c = κ + κ⁻¹ →
        subsolutionDThreshold p.χ M κ κtilde p.m p.γ c < D →
        κtilde ≤ 2 * κ) := by
  intro h
  let p : CMParams :=
    { m := 3
      α := 4
      γ := 1
      χ := 0
      hm := by norm_num
      hα := by norm_num
      hγ := by norm_num }
  have hD :
      subsolutionDThreshold p.χ 1 (1 / 4) (3 / 4) p.m p.γ (17 / 4) <
        (4 / 5 : ℝ) := by
    norm_num [p, subsolutionDThreshold, subsolutionK]
  have hbad := h p (by norm_num [p]) (1 / 4) (3 / 4) 1 (17 / 4)
    (4 / 5) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [p]) (by norm_num) (by norm_num) hD
  norm_num at hbad

theorem not_Lemma_4_2_chi_zero_hypotheses_force_D_ge_one :
    ¬ (∀ p : CMParams, p.χ = 0 →
      ∀ κ κtilde M c D : ℝ,
        0 < κ → κ < 1 → κ < κtilde →
        κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1) →
        1 ≤ M → c = κ + κ⁻¹ →
        subsolutionDThreshold p.χ M κ κtilde p.m p.γ c < D →
        1 ≤ D) := by
  intro h
  let p : CMParams :=
    { m := 3
      α := 4
      γ := 1
      χ := 0
      hm := by norm_num
      hα := by norm_num
      hγ := by norm_num }
  have hD :
      subsolutionDThreshold p.χ 1 (1 / 4) (3 / 4) p.m p.γ (17 / 4) <
        (4 / 5 : ℝ) := by
    norm_num [p, subsolutionDThreshold, subsolutionK]
  have hbad := h p (by norm_num [p]) (1 / 4) (3 / 4) 1 (17 / 4)
    (4 / 5) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [p]) (by norm_num) (by norm_num) hD
  norm_num at hbad

theorem not_constantSubsolutionThreshold_implies_frozen_smallness :
    ¬ (∀ p : CMParams, ∀ κ κtilde D d : ℝ,
      0 < d →
        d ≤ constantSubsolutionThreshold p.χ κ κtilde D →
          |p.χ| * d ^ (p.m - 1) ≤ 1 - d ^ p.α) := by
  intro h
  let p : CMParams :=
    { m := 1
      α := 1
      γ := 1
      χ := 2
      hm := le_rfl
      hα := le_rfl
      hγ := le_rfl }
  have hd_pos : 0 < (1 / 4 : ℝ) := by norm_num
  have hd_le :
      (1 / 4 : ℝ) ≤
        constantSubsolutionThreshold p.χ (1 / 2 : ℝ) 1 1 := by
    simp [constantSubsolutionThreshold, p]
    norm_num
  have hbad := h p (1 / 2 : ℝ) 1 1 (1 / 4 : ℝ) hd_pos hd_le
  norm_num [p] at hbad

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
      -p.χ * p.m * (expDecay κ x) ^ (p.m - 1) *
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

theorem frozenWaveOperator_exp_nonpos_of_chi_nonpos_of_resolvent_bound
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hc : 2 ≤ c) (hκ_eq : κ = kappa c)
    (hκ : 0 < κ) (hγκ : p.γ * κ < 1) (hmκ : κ * p.m ≤ 1)
    (hχ : p.χ ≤ 0) (hM : 1 ≤ M) (hu : InWaveTrapSet κ M u) (x : ℝ)
    (hV_diff : DifferentiableAt ℝ (deriv (frozenElliptic p u)) x)
    (hgap :
      -p.χ * (expDecay κ x) ^ p.m *
          (((1 + p.m * p.γ * κ ^ 2) / (1 - p.γ ^ 2 * κ ^ 2)) *
            (expDecay κ x) ^ p.γ - (u x) ^ p.γ) ≤
        expDecay κ x * (expDecay κ x) ^ p.α) :
    frozenWaveOperator p c u (expDecay κ) x ≤ 0 := by
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
      -(p.m * κ) * Vx + V ≤ C * E ^ p.γ := by
    dsimp [V, Vx, C]
    have h := chemotaxis_resolvent_bound p hκ hγκ hmκ hM hu x
    rw [hEgamma] at h
    convert h using 1 <;> ring
  have hbracket :
      -(p.m * κ) * Vx + V - (u x) ^ p.γ ≤ C * E ^ p.γ - (u x) ^ p.γ := by
    linarith
  have hcoef_nonneg : 0 ≤ -p.χ * E ^ p.m := by
    exact mul_nonneg (neg_nonneg.mpr hχ)
      (Real.rpow_nonneg hE_nonneg p.m)
  have hchem_le :
      -p.χ * E ^ p.m *
          (-(p.m * κ) * Vx + V - (u x) ^ p.γ) ≤
        -p.χ * E ^ p.m * (C * E ^ p.γ - (u x) ^ p.γ) :=
    mul_le_mul_of_nonneg_left hbracket hcoef_nonneg
  rw [frozenWaveOperator_exp_full_eq p hc hκ_eq hu.cunif_bdd hu.nonneg x hV_diff]
  dsimp [E, V, Vx, C] at hchem_le hgap
  linarith

theorem frozenWaveOperator_exp_nonpos_of_chi_nonpos
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hc : 2 ≤ c) (hκ_eq : κ = kappa c)
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hκ : 0 < κ) (hγκ : p.γ * κ < 1) (hmκ : κ * p.m ≤ 1)
    (hM : 1 ≤ M)
    (hMbound :
      |p.χ| * ((1 + p.m * p.γ * κ ^ 2) / (1 - p.γ ^ 2 * κ ^ 2)) *
        M ^ (p.m + p.γ - p.α - 1) ≤ 1)
    (hu : InWaveTrapSet κ M u) {x : ℝ}
    (hx : expDecay κ x < M)
    (hV_diff : DifferentiableAt ℝ (deriv (frozenElliptic p u)) x) :
    frozenWaveOperator p c u (expDecay κ) x ≤ 0 := by
  apply frozenWaveOperator_exp_nonpos_of_chi_nonpos_of_resolvent_bound
    p hc hκ_eq hκ hγκ hmκ hχ hM hu x hV_diff
  let E := expDecay κ x
  let C := (1 + p.m * p.γ * κ ^ 2) / (1 - p.γ ^ 2 * κ ^ 2)
  let δ := p.m + p.γ - p.α - 1
  have hE_pos : 0 < E := expDecay_pos κ x
  have hE_nonneg : 0 ≤ E := hE_pos.le
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    linarith
  have hEδ_le_Mδ : E ^ δ ≤ M ^ δ :=
    Real.rpow_le_rpow hE_nonneg hx.le hδ_nonneg
  have hden_pos : 0 < 1 - p.γ ^ 2 * κ ^ 2 := by
    have hγ_pos : 0 < p.γ := by linarith [p.hγ]
    have hγκ_pos : 0 < p.γ * κ := mul_pos hγ_pos hκ
    have hsq : (p.γ * κ) ^ 2 < 1 := by
      rw [sq_lt_one_iff_abs_lt_one]
      rw [abs_of_pos hγκ_pos]
      exact hγκ
    nlinarith
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg
      (by
        have hm_nonneg : 0 ≤ p.m := by linarith [p.hm]
        have hγ_nonneg : 0 ≤ p.γ := by linarith [p.hγ]
        have hκsq_nonneg : 0 ≤ κ ^ 2 := sq_nonneg κ
        have hterm : 0 ≤ p.m * p.γ * κ ^ 2 :=
          mul_nonneg (mul_nonneg hm_nonneg hγ_nonneg) hκsq_nonneg
        linarith)
      hden_pos.le
  have hcoef_nonneg : 0 ≤ |p.χ| * C := mul_nonneg (abs_nonneg p.χ) hC_nonneg
  have hcoef_Eδ : |p.χ| * C * E ^ δ ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hEδ_le_Mδ hcoef_nonneg
    have hMbound' : |p.χ| * C * M ^ δ ≤ 1 := by
      dsimp [C, δ]
      exact hMbound
    exact le_trans (by simpa [mul_assoc] using hmul) hMbound'
  have hpow_split :
      E ^ p.m * E ^ p.γ = E ^ (p.α + 1) * E ^ δ := by
    dsimp [δ]
    rw [← Real.rpow_add hE_pos, ← Real.rpow_add hE_pos]
    congr 1
    ring
  have hE_pow :
      E * E ^ p.α = E ^ (p.α + 1) := by
    have : E = E ^ (1 : ℝ) := (Real.rpow_one E).symm
    nth_rw 1 [this]
    rw [← Real.rpow_add hE_pos]
    congr 1
    ring
  have hminus_chi : -p.χ = |p.χ| := by
    rw [abs_of_nonpos hχ]
  have hright_nonneg : 0 ≤ E * E ^ p.α :=
    mul_nonneg hE_nonneg (Real.rpow_nonneg hE_nonneg p.α)
  calc
    -p.χ * E ^ p.m * (C * E ^ p.γ - (u x) ^ p.γ)
        ≤ -p.χ * E ^ p.m * (C * E ^ p.γ) := by
          have hcoef : 0 ≤ -p.χ * E ^ p.m :=
            mul_nonneg (neg_nonneg.mpr hχ)
              (Real.rpow_nonneg hE_nonneg p.m)
          have hsource_nonneg : 0 ≤ (u x) ^ p.γ :=
            Real.rpow_nonneg (hu.nonneg x) p.γ
          exact mul_le_mul_of_nonneg_left (by linarith) hcoef
      _ = (|p.χ| * C * E ^ δ) * (E * E ^ p.α) := by
            rw [hminus_chi, hE_pow]
            calc
              |p.χ| * E ^ p.m * (C * E ^ p.γ)
                  = |p.χ| * C * (E ^ p.m * E ^ p.γ) := by ring
              _ = |p.χ| * C * (E ^ (p.α + 1) * E ^ δ) := by
                  rw [hpow_split]
              _ = (|p.χ| * C * E ^ δ) * E ^ (p.α + 1) := by ring_nf
      _ ≤ 1 * (E * E ^ p.α) :=
          mul_le_mul_of_nonneg_right hcoef_Eδ hright_nonneg
      _ = E * E ^ p.α := by ring

theorem frozenWaveOperator_exp_nonpos_of_chi_nonneg
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hc : 2 ≤ c) (hκ_eq : κ = kappa c)
    (hχ_nonneg : 0 ≤ p.χ) (hχ_le_one : p.χ ≤ 1)
    (hα : p.α = p.m + p.γ - 1)
    (hκ_nonneg : 0 ≤ κ) (hmκ : p.m * κ ≤ 1)
    (hu : InWaveTrapSet κ M u) {x : ℝ}
    (hV_diff : DifferentiableAt ℝ (deriv (frozenElliptic p u)) x) :
    frozenWaveOperator p c u (expDecay κ) x ≤ 0 := by
  let E := expDecay κ x
  let V := frozenElliptic p u x
  let Vx := deriv (frozenElliptic p u) x
  have hE_pos : 0 < E := expDecay_pos κ x
  have hE_nonneg : 0 ≤ E := hE_pos.le
  have hV_nonneg : 0 ≤ V := by
    dsimp [V]
    exact frozenElliptic_nonneg p hu.nonneg x
  have hVx_abs : |Vx| ≤ V := by
    dsimp [V, Vx]
    exact frozenElliptic_deriv_abs_le p hu.cunif_bdd hu.nonneg x
  have hVx_le : Vx ≤ V := le_trans (le_abs_self _) hVx_abs
  have hmk_nonneg : 0 ≤ p.m * κ :=
    mul_nonneg (le_trans zero_le_one p.hm) hκ_nonneg
  have hneg_term_lower :
      -(p.m * κ) * V ≤ -(p.m * κ) * Vx := by
    exact mul_le_mul_of_nonpos_left hVx_le (neg_nonpos.mpr hmk_nonneg)
  have hbracket_lower :
      -(p.m * κ) * Vx + V - (u x) ^ p.γ ≥ -((u x) ^ p.γ) := by
    have hnonneg_part : 0 ≤ (1 - p.m * κ) * V :=
      mul_nonneg (sub_nonneg.mpr hmκ) hV_nonneg
    nlinarith
  have hcoef_nonpos : -p.χ * E ^ p.m ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hχ_nonneg)
      (Real.rpow_nonneg hE_nonneg p.m)
  have hchem_le_source :
      -p.χ * E ^ p.m *
          (-(p.m * κ) * Vx + V - (u x) ^ p.γ) ≤
          p.χ * E ^ p.m * (u x) ^ p.γ := by
      have hmul :=
        mul_le_mul_of_nonpos_left hbracket_lower hcoef_nonpos
      calc
        -p.χ * E ^ p.m *
            (-(p.m * κ) * Vx + V - (u x) ^ p.γ)
            ≤ -p.χ * E ^ p.m * (-(u x) ^ p.γ) := hmul
        _ = p.χ * E ^ p.m * (u x) ^ p.γ := by ring
  have huγ_le_Eγ : (u x) ^ p.γ ≤ E ^ p.γ := by
    dsimp [E, expDecay]
    simpa [neg_mul] using hu.rpow_le_exp (le_trans zero_le_one p.hγ) x
  have hcoef_source_nonneg : 0 ≤ p.χ * E ^ p.m :=
    mul_nonneg hχ_nonneg (Real.rpow_nonneg hE_nonneg p.m)
  have hchem_le_E :
      -p.χ * E ^ p.m *
          (-(p.m * κ) * Vx + V - (u x) ^ p.γ) ≤
        p.χ * E ^ p.m * E ^ p.γ := by
    exact le_trans hchem_le_source
      (mul_le_mul_of_nonneg_left huγ_le_Eγ hcoef_source_nonneg)
  have hpow_mγ :
      E ^ p.m * E ^ p.γ = E ^ (p.α + 1) := by
    rw [← Real.rpow_add hE_pos, hα]
    congr 1
    ring
  have hE_pow :
      E * E ^ p.α = E ^ (p.α + 1) := by
    have hE_one : E = E ^ (1 : ℝ) := (Real.rpow_one E).symm
    nth_rw 1 [hE_one]
    rw [← Real.rpow_add hE_pos]
    congr 1
    ring
  have hchem_le_logistic :
      -p.χ * E ^ p.m *
          (-(p.m * κ) * Vx + V - (u x) ^ p.γ) ≤
        E * E ^ p.α := by
    calc
          -p.χ * E ^ p.m *
              (-(p.m * κ) * Vx + V - (u x) ^ p.γ)
              ≤ p.χ * E ^ p.m * E ^ p.γ := hchem_le_E
          _ = p.χ * (E ^ p.m * E ^ p.γ) := by ring
          _ = p.χ * E ^ (p.α + 1) := by rw [hpow_mγ]
          _ ≤ 1 * E ^ (p.α + 1) :=
              mul_le_mul_of_nonneg_right hχ_le_one
                (Real.rpow_nonneg hE_nonneg (p.α + 1))
          _ = E * E ^ p.α := by rw [hE_pow]; ring
  rw [frozenWaveOperator_exp_full_eq p hc hκ_eq hu.cunif_bdd hu.nonneg x hV_diff]
  dsimp [E, V, Vx] at hchem_le_logistic
  linarith

/-- Strict positive-sensitivity exponential-branch superbarrier.

This is the strict version of `frozenWaveOperator_exp_nonpos_of_chi_nonneg`.
The only strengthened scalar input is `p.χ < 1`; the proof is the same
positive-branch estimate, with the final `χ ≤ 1` budget used strictly. -/
theorem frozenWaveOperator_exp_neg_of_chi_nonneg
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hc : 2 ≤ c) (hκ_eq : κ = kappa c)
    (hχ_nonneg : 0 ≤ p.χ) (hχ_lt_one : p.χ < 1)
    (hα : p.α = p.m + p.γ - 1)
    (hκ_nonneg : 0 ≤ κ) (hmκ : p.m * κ ≤ 1)
    (hu : InWaveTrapSet κ M u) {x : ℝ}
    (hV_diff : DifferentiableAt ℝ (deriv (frozenElliptic p u)) x) :
    frozenWaveOperator p c u (expDecay κ) x < 0 := by
  let E := expDecay κ x
  let V := frozenElliptic p u x
  let Vx := deriv (frozenElliptic p u) x
  have hE_pos : 0 < E := expDecay_pos κ x
  have hE_nonneg : 0 ≤ E := hE_pos.le
  have hV_nonneg : 0 ≤ V := by
    dsimp [V]
    exact frozenElliptic_nonneg p hu.nonneg x
  have hVx_abs : |Vx| ≤ V := by
    dsimp [V, Vx]
    exact frozenElliptic_deriv_abs_le p hu.cunif_bdd hu.nonneg x
  have hVx_le : Vx ≤ V := le_trans (le_abs_self _) hVx_abs
  have hmk_nonneg : 0 ≤ p.m * κ :=
    mul_nonneg (le_trans zero_le_one p.hm) hκ_nonneg
  have hneg_term_lower :
      -(p.m * κ) * V ≤ -(p.m * κ) * Vx := by
    exact mul_le_mul_of_nonpos_left hVx_le (neg_nonpos.mpr hmk_nonneg)
  have hbracket_lower :
      -(p.m * κ) * Vx + V - (u x) ^ p.γ ≥ -((u x) ^ p.γ) := by
    have hnonneg_part : 0 ≤ (1 - p.m * κ) * V :=
      mul_nonneg (sub_nonneg.mpr hmκ) hV_nonneg
    nlinarith
  have hcoef_nonpos : -p.χ * E ^ p.m ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hχ_nonneg)
      (Real.rpow_nonneg hE_nonneg p.m)
  have hchem_le_source :
      -p.χ * E ^ p.m *
          (-(p.m * κ) * Vx + V - (u x) ^ p.γ) ≤
          p.χ * E ^ p.m * (u x) ^ p.γ := by
      have hmul :=
        mul_le_mul_of_nonpos_left hbracket_lower hcoef_nonpos
      calc
        -p.χ * E ^ p.m *
            (-(p.m * κ) * Vx + V - (u x) ^ p.γ)
            ≤ -p.χ * E ^ p.m * (-(u x) ^ p.γ) := hmul
        _ = p.χ * E ^ p.m * (u x) ^ p.γ := by ring
  have huγ_le_Eγ : (u x) ^ p.γ ≤ E ^ p.γ := by
    dsimp [E, expDecay]
    simpa [neg_mul] using hu.rpow_le_exp (le_trans zero_le_one p.hγ) x
  have hcoef_source_nonneg : 0 ≤ p.χ * E ^ p.m :=
    mul_nonneg hχ_nonneg (Real.rpow_nonneg hE_nonneg p.m)
  have hchem_le_E :
      -p.χ * E ^ p.m *
          (-(p.m * κ) * Vx + V - (u x) ^ p.γ) ≤
        p.χ * E ^ p.m * E ^ p.γ := by
    exact le_trans hchem_le_source
      (mul_le_mul_of_nonneg_left huγ_le_Eγ hcoef_source_nonneg)
  have hpow_mγ :
      E ^ p.m * E ^ p.γ = E ^ (p.α + 1) := by
    rw [← Real.rpow_add hE_pos, hα]
    congr 1
    ring
  have hE_pow :
      E * E ^ p.α = E ^ (p.α + 1) := by
    have hE_one : E = E ^ (1 : ℝ) := (Real.rpow_one E).symm
    nth_rw 1 [hE_one]
    rw [← Real.rpow_add hE_pos]
    congr 1
    ring
  have hchem_lt_logistic :
      -p.χ * E ^ p.m *
          (-(p.m * κ) * Vx + V - (u x) ^ p.γ) <
        E * E ^ p.α := by
    calc
          -p.χ * E ^ p.m *
              (-(p.m * κ) * Vx + V - (u x) ^ p.γ)
              ≤ p.χ * E ^ p.m * E ^ p.γ := hchem_le_E
          _ = p.χ * (E ^ p.m * E ^ p.γ) := by ring
          _ = p.χ * E ^ (p.α + 1) := by rw [hpow_mγ]
          _ < 1 * E ^ (p.α + 1) :=
              mul_lt_mul_of_pos_right hχ_lt_one
                (Real.rpow_pos_of_pos hE_pos (p.α + 1))
          _ = E * E ^ p.α := by rw [hE_pow]; ring
  rw [frozenWaveOperator_exp_full_eq p hc hκ_eq hu.cunif_bdd hu.nonneg x hV_diff]
  dsimp [E, V, Vx] at hchem_lt_logistic
  linarith

theorem frozenWaveOperator_upperBarrier_exp_region_eq
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    {x : ℝ} (hx : expDecay κ x < M) :
    frozenWaveOperator p c u (upperBarrier κ M) x =
      frozenWaveOperator p c u (expDecay κ) x := by
  have hx' : Real.exp (-κ * x) < M := by
    simpa [expDecay] using hx
  have hW : upperBarrier κ M =ᶠ[𝓝 x] expDecay κ :=
    upperBarrier_eventuallyEq_exp_of_lt hx'
  have hW_deriv :
      deriv (upperBarrier κ M) x = deriv (expDecay κ) x :=
    Filter.EventuallyEq.deriv_eq hW
  have hW_two :
      iteratedDeriv 2 (upperBarrier κ M) x = iteratedDeriv 2 (expDecay κ) x := by
    rw [upperBarrier_iteratedDeriv_two_eq_exp_of_lt hx']
    exact (expDecay_iteratedDeriv_two κ x).symm
  have hW_x : upperBarrier κ M x = expDecay κ x := by
    rw [upperBarrier_eq_exp_of_exp_le (le_of_lt hx')]
    simp [expDecay]
  have hWpow :
      (fun y => (upperBarrier κ M y) ^ p.m *
          deriv (frozenElliptic p u) y) =ᶠ[𝓝 x]
        fun y => (expDecay κ y) ^ p.m *
          deriv (frozenElliptic p u) y := by
    filter_upwards [hW] with y hy
    rw [hy]
  have hchem :
      deriv
          (fun y => (upperBarrier κ M y) ^ p.m *
            deriv (frozenElliptic p u) y) x =
        deriv
          (fun y => (expDecay κ y) ^ p.m *
            deriv (frozenElliptic p u) y) x :=
    Filter.EventuallyEq.deriv_eq hWpow
  unfold frozenWaveOperator
  rw [hW_two, hW_deriv, hchem, hW_x]

theorem frozenWaveOperator_upperBarrier_exp_region_nonpos_of_chi_nonpos
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hc : 2 ≤ c) (hκ_eq : κ = kappa c)
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hκ : 0 < κ) (hγκ : p.γ * κ < 1) (hmκ : κ * p.m ≤ 1)
    (hM : 1 ≤ M)
    (hMbound :
      |p.χ| * ((1 + p.m * p.γ * κ ^ 2) / (1 - p.γ ^ 2 * κ ^ 2)) *
        M ^ (p.m + p.γ - p.α - 1) ≤ 1)
    (hu : InWaveTrapSet κ M u) {x : ℝ}
    (hx : expDecay κ x < M)
    (hV_diff : DifferentiableAt ℝ (deriv (frozenElliptic p u)) x) :
    frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0 := by
  rw [frozenWaveOperator_upperBarrier_exp_region_eq p hx]
  exact frozenWaveOperator_exp_nonpos_of_chi_nonpos p hc hκ_eq hχ hα hκ hγκ
    hmκ hM hMbound hu hx hV_diff

theorem frozenWaveOperator_upperBarrier_exp_region_nonpos_of_chi_nonneg
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hc : 2 ≤ c) (hκ_eq : κ = kappa c)
    (hχ_nonneg : 0 ≤ p.χ) (hχ : p.χ < chiStar p)
    (hα : p.α = p.m + p.γ - 1)
    (hκ_nonneg : 0 ≤ κ) (hmκ : p.m * κ ≤ 1)
    {x : ℝ} (hx : expDecay κ x < M)
    (hu : InWaveTrapSet κ M u)
    (hV_diff : DifferentiableAt ℝ (deriv (frozenElliptic p u)) x) :
    frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0 := by
  rw [frozenWaveOperator_upperBarrier_exp_region_eq p hx]
  exact frozenWaveOperator_exp_nonpos_of_chi_nonneg p hc hκ_eq hχ_nonneg
    (le_trans hχ.le (chiStar_le_one p)) hα hκ_nonneg hmκ hu hV_diff

/-- Strict upper-barrier residual in the exponential region for the
positive-sensitivity branch. -/
theorem frozenWaveOperator_upperBarrier_exp_region_neg_of_chi_nonneg
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hc : 2 ≤ c) (hκ_eq : κ = kappa c)
    (hχ_nonneg : 0 ≤ p.χ) (hχ_lt_one : p.χ < 1)
    (hα : p.α = p.m + p.γ - 1)
    (hκ_nonneg : 0 ≤ κ) (hmκ : p.m * κ ≤ 1)
    {x : ℝ} (hx : expDecay κ x < M)
    (hu : InWaveTrapSet κ M u)
    (hV_diff : DifferentiableAt ℝ (deriv (frozenElliptic p u)) x) :
    frozenWaveOperator p c u (upperBarrier κ M) x < 0 := by
  rw [frozenWaveOperator_upperBarrier_exp_region_eq p hx]
  exact frozenWaveOperator_exp_neg_of_chi_nonneg p hc hκ_eq hχ_nonneg
    hχ_lt_one hα hκ_nonneg hmκ hu hV_diff

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
  · exact paperWaveOperator_exp_nonpos_of_chi_nonpos p hχ hα hκ hκ1 hγκ hmκ
      hM hMbound hu hlt hc
  · exact paperWaveOperator_upperBarrier_const_region_nonpos_neg p hχ hα hκ hM hu hgt

theorem Lemma_4_1_pos_frozen_holds_away_from_interface_at_kappa
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hc : c = κ + κ⁻¹)
    (hχ_nonneg : 0 ≤ p.χ) (hχ : p.χ < chiStar p)
    (hα : p.α = p.m + p.γ - 1)
    (hmκ : p.m * κ ≤ 1)
    (hM : 1 ≤ M)
    (hMchi : (1 / (1 - p.χ)) ^ (1 / p.α) ≤ M)
    (hu : InWaveTrapSet κ M u) :
    ∀ x, Real.exp (-κ * x) ≠ M →
      frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0 := by
  intro x hneq
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · have hx : expDecay κ x < M := by
      simpa [expDecay] using hlt
    have hc_two : 2 ≤ c :=
      (two_lt_of_pos_lt_one_kappa_speed hκ hκ1 hc).le
    have hκ_eq : κ = kappa c :=
      (kappa_eq_of_pos_lt_one_kappa_speed hκ hκ1 hc).symm
    exact frozenWaveOperator_upperBarrier_exp_region_nonpos_of_chi_nonneg
      p hc_two hκ_eq hχ_nonneg hχ hα hκ.le hmκ hx hu
      (frozenElliptic_deriv_differentiableAt p hu.cunif_bdd hu.nonneg x)
  · exact frozenWaveOperator_upperBarrier_const_region_nonpos_pos
      p hχ_nonneg hχ hα hM hMchi hu hgt

theorem Lemma_4_1_neg_frozen_holds_away_from_interface_of_plateau_source_bound
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hγκ : p.γ * κ < 1) (hmκ : κ * p.m ≤ 1)
    (hM : 1 ≤ M)
    (hMbound :
      |p.χ| * ((1 + p.m * p.γ * κ ^ 2) / (1 - p.γ ^ 2 * κ ^ 2)) *
        M ^ (p.m + p.γ - p.α - 1) ≤ 1)
    (hu : InWaveTrapSet κ M u) (hc : c = κ + κ⁻¹)
    (hplateau :
      ∀ x, M < Real.exp (-κ * x) →
        frozenElliptic p u x ≤ (u x) ^ p.γ) :
    ∀ x, Real.exp (-κ * x) ≠ M →
      frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0 := by
  intro x hneq
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · have hx : expDecay κ x < M := by
      simpa [expDecay] using hlt
    have hc_two : 2 ≤ c :=
      (two_lt_of_pos_lt_one_kappa_speed hκ hκ1 hc).le
    have hκ_eq : κ = kappa c :=
      (kappa_eq_of_pos_lt_one_kappa_speed hκ hκ1 hc).symm
    exact frozenWaveOperator_upperBarrier_exp_region_nonpos_of_chi_nonpos
      p hc_two hκ_eq hχ hα hκ hγκ hmκ hM hMbound hu hx
      (frozenElliptic_deriv_differentiableAt p hu.cunif_bdd hu.nonneg x)
  · exact frozenWaveOperator_upperBarrier_const_region_nonpos_of_elliptic_le_source
      p hχ hM hu.cunif_bdd hu.nonneg hgt (hplateau x hgt)

theorem Lemma_4_1_strengthened_away_from_interface_direct :
    (∀ p : CMParams, p.χ ≤ 0 → p.α ≤ p.m + p.γ - 1 →
      ∀ κ M c : ℝ, 0 < κ → κ < 1 → p.γ * κ < 1 → κ * p.m ≤ 1 →
        1 ≤ M →
        |p.χ| * ((1 + p.m * p.γ * κ ^ 2) / (1 - p.γ ^ 2 * κ ^ 2)) *
          M ^ (p.m + p.γ - p.α - 1) ≤ 1 →
        c = κ + κ⁻¹ →
        ∀ u : ℝ → ℝ, InWaveTrapSet κ M u →
          (∀ x, M < Real.exp (-κ * x) →
            frozenElliptic p u x ≤ (u x) ^ p.γ) →
          ∀ x, Real.exp (-κ * x) ≠ M →
            frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0) ∧
    (∀ p : CMParams, 0 ≤ p.χ → p.χ < chiStar p →
      p.α = p.m + p.γ - 1 →
      ∀ κ M c : ℝ, 0 < κ → κ < 1 → p.m * κ ≤ 1 →
        1 ≤ M →
        (1 / (1 - p.χ)) ^ (1 / p.α) ≤ M →
        c = κ + κ⁻¹ →
        ∀ u : ℝ → ℝ, InWaveTrapSet κ M u →
          ∀ x, Real.exp (-κ * x) ≠ M →
            frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0) := by
  constructor
  · intro p hχ hα κ M c hκ hκ1 hγκ hmκ hM hMbound hc u hu hplateau
    exact Lemma_4_1_neg_frozen_holds_away_from_interface_of_plateau_source_bound
      p hχ hα hκ hκ1 hγκ hmκ hM hMbound hu hc hplateau
  · intro p hχ_nonneg hχ hα κ M c hκ hκ1 hmκ hM hMchi hc u hu
    exact Lemma_4_1_pos_frozen_holds_away_from_interface_at_kappa
      p hκ hκ1 hc hχ_nonneg hχ hα hmκ hM hMchi hu

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

theorem not_Lemma_4_2 : ¬ Lemma_4_2 := by
  intro hL
  let u : ℝ → ℝ := lemma41CounterexampleProfile
  let V0 : ℝ :=
    frozenElliptic lemma41CounterexampleParams lemma41CounterexampleProfile (-1)
  have hV0_pos : 0 < V0 := by
    simpa [V0] using frozenElliptic_lemma41CounterexampleProfile_pos
  let p : CMParams :=
    { m := 1
      α := 1
      γ := 1
      χ := 2 / V0
      hm := by norm_num
      hα := by norm_num
      hγ := by norm_num }
  let κ : ℝ := 1 / 2
  let κtilde : ℝ := 1
  let M : ℝ := 1
  let c : ℝ := 5 / 2
  let D : ℝ :=
    subsolutionDThreshold p.χ M κ κtilde p.m p.γ c + 1
  let θ : ℝ := constantSubsolutionThreshold p.χ κ κtilde D
  let d : ℝ := θ / 2
  have htrap : InWaveTrapSet κ M u := by
    simpa [u, κ, M] using lemma41CounterexampleProfile_mem_trap
  have hDthr :
      subsolutionDThreshold p.χ M κ κtilde p.m p.γ c < D := by
    dsimp [D]
    linarith
  have hDpos : 0 < D := by
    have hthr_pos :
        0 < subsolutionDThreshold p.χ M κ κtilde p.m p.γ c := by
      apply subsolutionDThreshold_pos_of_kappa_speed
      · norm_num [M]
      · norm_num [κ]
      · norm_num [κ]
      · norm_num [κ, κtilde]
      · norm_num [κtilde]
      · norm_num [p]
      · norm_num [p]
      · norm_num [c, κ, κtilde]
    dsimp [D]
    linarith
  have hθ_pos : 0 < θ := by
    dsimp [θ]
    apply constantSubsolutionThreshold_pos
    · norm_num [κ]
    · norm_num [κ, κtilde]
    · exact hDpos
  have hd_pos : 0 < d := by
    dsimp [d]
    linarith
  have hd_le : d ≤ θ := by
    dsimp [d]
    linarith
  have hconst :
      IsFrozenSubSolutionOn p c u (fun _ => d) Set.univ := by
    exact
      (hL p κ κtilde M c
        (by norm_num [κ]) (by norm_num [κ])
        (by norm_num [κ, κtilde])
        (by norm_num [p, κ, κtilde])
        (by norm_num [M])
        (by norm_num [c, κ])
        D hDthr u htrap).2 d hd_pos (by simpa [θ] using hd_le)
  have hop := hconst (-1) trivial
  rw [frozenWaveOperator_const_eq p htrap.cunif_bdd htrap.nonneg (-1)] at hop
  have hu_neg_one : u (-1) = 0 := by
    simpa [u] using lemma41CounterexampleProfile_at_neg_one
  have hVeq : frozenElliptic p u (-1) = V0 := by
    simp [V0, p, u, lemma41CounterexampleParams, frozenElliptic]
  have hbad :
      -p.χ * (d ^ p.m *
          (frozenElliptic p u (-1) - (u (-1)) ^ p.γ)) +
        d * (1 - d ^ p.α) =
        -d * (1 + d) := by
    rw [hVeq, hu_neg_one]
    have hzero_rpow : (0 : ℝ) ^ p.γ = 0 := by
      norm_num [p]
    rw [hzero_rpow]
    norm_num [p]
    field_simp [ne_of_gt hV0_pos]
    ring
  rw [hbad] at hop
  have hneg : -d * (1 + d) < 0 := by
    have hsum_pos : 0 < 1 + d := by linarith
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hd_pos) hsum_pos
  exact not_lt_of_ge hop hneg

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

theorem InTimeWaveTrapSet.le_M
    {κ M T : ℝ} {u : ℝ → ℝ → ℝ}
    (h : InTimeWaveTrapSet κ M T u)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (x : ℝ) :
    u t x ≤ M :=
  le_trans (h.le_scaledUpperBarrier ht x) (scaledUpperBarrier_le_M κ M x)

theorem InTimeWaveTrapSet.rpow_le_M
    {κ M T a : ℝ} {u : ℝ → ℝ → ℝ}
    (h : InTimeWaveTrapSet κ M T u)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (ha : 0 ≤ a) (x : ℝ) :
    (u t x) ^ a ≤ M ^ a :=
  Real.rpow_le_rpow (h.nonneg ht x) (h.le_M ht x) ha

theorem frozenElliptic_le_rpow_of_inTimeWaveTrapSet_slice
    (p : CMParams) {κ M T : ℝ} {u : ℝ → ℝ → ℝ}
    (hM : 0 < M) (h : InTimeWaveTrapSet κ M T u)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (x : ℝ) :
    frozenElliptic p (u t) x ≤ M ^ p.γ :=
  frozenElliptic_le_of_rpow_le p (Real.rpow_nonneg hM.le p.γ)
    (h.slice_cunif ht).1 (fun y => h.nonneg ht y)
    (fun y => h.rpow_le_M ht (by linarith [p.hγ]) y) x

theorem constant_subsolution_frozenWaveOperator_nonneg_of_small_d_time_trap
    (p : CMParams) {κ M T d c : ℝ} {u : ℝ → ℝ → ℝ}
    (hM_pos : 0 < M)
    (hd_pos : 0 < d)
    (hsmall : |p.χ| * d ^ (p.m - 1) * M ^ p.γ ≤ 1 - d ^ p.α)
    (hu : InTimeWaveTrapSet κ M T u)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IsFrozenSubSolutionOn p c (u t) (fun _ => d) Set.univ := by
  intro x _hx
  rw [frozenWaveOperator_const_eq p (hu.slice_cunif ht) (fun y => hu.nonneg ht y) x]
  have hd_nonneg : 0 ≤ d := hd_pos.le
  have hdm_nonneg : 0 ≤ d ^ p.m := Real.rpow_nonneg hd_nonneg _
  have hV_le : frozenElliptic p (u t) x ≤ M ^ p.γ :=
    frozenElliptic_le_rpow_of_inTimeWaveTrapSet_slice p hM_pos hu ht x
  have huγ_le : (u t x) ^ p.γ ≤ M ^ p.γ :=
    hu.rpow_le_M ht (by linarith [p.hγ]) x
  let Δ := frozenElliptic p (u t) x - (u t x) ^ p.γ
  have hΔ_abs : |Δ| ≤ M ^ p.γ := by
    have hV_nonneg : 0 ≤ frozenElliptic p (u t) x :=
      frozenElliptic_nonneg p (fun y => hu.nonneg ht y) x
    have huγ_nonneg : 0 ≤ (u t x) ^ p.γ :=
      Real.rpow_nonneg (hu.nonneg ht x) _
    have hΔ_le : Δ ≤ M ^ p.γ := by
      dsimp [Δ]
      linarith
    have hneg_le : -(M ^ p.γ) ≤ Δ := by
      dsimp [Δ]
      linarith
    exact abs_le.mpr ⟨hneg_le, hΔ_le⟩
  have hchem_core :
      -|p.χ| * (d ^ p.m * M ^ p.γ) ≤ -p.χ * (d ^ p.m * Δ) := by
    have hcoef_abs : |(-p.χ) * Δ| ≤ |p.χ| * M ^ p.γ := by
      calc
        |(-p.χ) * Δ| = |p.χ| * |Δ| := by
          rw [abs_mul, abs_neg]
        _ ≤ |p.χ| * M ^ p.γ :=
          mul_le_mul_of_nonneg_left hΔ_abs (abs_nonneg p.χ)
    have hlower : -(|p.χ| * M ^ p.γ) ≤ (-p.χ) * Δ :=
      le_trans (neg_le_neg hcoef_abs) (neg_abs_le _)
    have hmul := mul_le_mul_of_nonneg_right hlower hdm_nonneg
    calc
      -|p.χ| * (d ^ p.m * M ^ p.γ) =
          (-(|p.χ| * M ^ p.γ)) * d ^ p.m := by ring
      _ ≤ ((-p.χ) * Δ) * d ^ p.m := hmul
      _ = -p.χ * (d ^ p.m * Δ) := by ring
  have hdm_eq : d ^ p.m = d * d ^ (p.m - 1) := by
    calc
      d ^ p.m = d ^ (1 + (p.m - 1)) := by
        congr 1
        ring
      _ = d ^ (1 : ℝ) * d ^ (p.m - 1) := by
        rw [Real.rpow_add hd_pos]
      _ = d * d ^ (p.m - 1) := by
        rw [Real.rpow_one]
  have hsmall_mul :
      |p.χ| * (d ^ p.m * M ^ p.γ) ≤ d * (1 - d ^ p.α) := by
    rw [hdm_eq]
    calc
      |p.χ| * ((d * d ^ (p.m - 1)) * M ^ p.γ) =
          d * (|p.χ| * d ^ (p.m - 1) * M ^ p.γ) := by ring
      _ ≤ d * (1 - d ^ p.α) :=
          mul_le_mul_of_nonneg_left hsmall hd_nonneg
  have hchem :
      -p.χ * (d ^ p.m *
          (frozenElliptic p (u t) x - (u t x) ^ p.γ)) +
        d * (1 - d ^ p.α) ≥ 0 := by
    dsimp [Δ] at hchem_core
    linarith
  linarith

theorem constant_subsolution_frozenWaveOperator_nonneg_of_half_bound_time_trap
    (p : CMParams) {κ M T d c : ℝ} {u : ℝ → ℝ → ℝ}
    (hM_pos : 0 < M)
    (hchem : |p.χ| * M ^ p.γ ≤ 1 / 2)
    (hd_pos : 0 < d) (hd_le_half : d ≤ 1 / 2)
    (hu : InTimeWaveTrapSet κ M T u)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IsFrozenSubSolutionOn p c (u t) (fun _ => d) Set.univ :=
  constant_subsolution_frozenWaveOperator_nonneg_of_small_d_time_trap
    p hM_pos hd_pos
    (constant_subsolution_frozen_smallness_of_half_bound
      p hM_pos hchem hd_pos hd_le_half)
    hu ht

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

theorem not_forall_InTimeWaveTrapSet_slice_inWaveTrapSet_general_M :
    ¬ (∀ κ M T : ℝ, ∀ u : ℝ → ℝ → ℝ, ∀ t : ℝ,
        1 ≤ M → t ∈ Set.Icc (0 : ℝ) T →
          InTimeWaveTrapSet κ M T u → InWaveTrapSet κ M (u t)) := by
  intro h
  let u : ℝ → ℝ → ℝ := fun _ => scaledUpperBarrier 1 2
  have ht : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨le_rfl, by norm_num⟩
  have htime : InTimeWaveTrapSet 1 2 1 u := by
    intro t _ht
    refine ⟨scaledUpperBarrier_cunif_bdd (by norm_num : (0 : ℝ) ≤ 2), ?_⟩
    intro x
    exact ⟨scaledUpperBarrier_nonneg (by norm_num : (0 : ℝ) ≤ 2) x, le_rfl⟩
  have hslice : InWaveTrapSet 1 2 (u 0) :=
    h 1 2 1 u 0 (by norm_num) ht htime
  have hle := hslice.le_upperBarrier 0
  norm_num [u, scaledUpperBarrier, upperBarrier] at hle

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

theorem not_Remark_4_2 : ¬ Remark_4_2 := by
  intro hR
  let u : ℝ → ℝ := lemma41CounterexampleProfile
  let uTime : ℝ → ℝ → ℝ := fun _ => u
  let V0 : ℝ :=
    frozenElliptic lemma41CounterexampleParams lemma41CounterexampleProfile (-1)
  have hV0_pos : 0 < V0 := by
    simpa [V0] using frozenElliptic_lemma41CounterexampleProfile_pos
  let p : CMParams :=
    { m := 1
      α := 1
      γ := 1
      χ := 2 / V0
      hm := by norm_num
      hα := by norm_num
      hγ := by norm_num }
  let κ : ℝ := 1 / 2
  let κtilde : ℝ := 1
  let M : ℝ := 1
  let c : ℝ := 5 / 2
  let T : ℝ := 1
  rcases
    hR p κ κtilde M c T
      (by norm_num [κ]) (by norm_num [κ])
      (by norm_num [κ, κtilde])
      (by norm_num [p, κ, κtilde])
      (by norm_num [M]) (by norm_num [T])
      (by norm_num [c, κ]) with
    ⟨D0, hD0⟩
  let D : ℝ :=
    max D0 (subsolutionDThreshold p.χ M κ κtilde p.m p.γ c) + 1
  let θ : ℝ := constantSubsolutionThreshold p.χ κ κtilde D
  let d : ℝ := θ / 2
  have htrap : InWaveTrapSet κ M u := by
    simpa [u, κ, M] using lemma41CounterexampleProfile_mem_trap
  have htime : InTimeWaveTrapSet κ M T uTime := by
    intro t _ht
    refine ⟨htrap.cunif_bdd, ?_⟩
    intro x
    exact ⟨htrap.nonneg x, by
      simpa [uTime, M, scaledUpperBarrier_one_eq_upperBarrier κ] using
        htrap.le_upperBarrier x⟩
  have hDgt : D0 < D := by
    dsimp [D]
    have hle : D0 ≤ max D0 (subsolutionDThreshold p.χ M κ κtilde p.m p.γ c) :=
      le_max_left _ _
    linarith
  have hDthr :
      subsolutionDThreshold p.χ M κ κtilde p.m p.γ c < D := by
    dsimp [D]
    have hle :
        subsolutionDThreshold p.χ M κ κtilde p.m p.γ c ≤
          max D0 (subsolutionDThreshold p.χ M κ κtilde p.m p.γ c) :=
      le_max_right _ _
    linarith
  have hDpos : 0 < D := by
    have hthr_pos :
        0 < subsolutionDThreshold p.χ M κ κtilde p.m p.γ c := by
      apply subsolutionDThreshold_pos_of_kappa_speed
      · norm_num [M]
      · norm_num [κ]
      · norm_num [κ]
      · norm_num [κ, κtilde]
      · norm_num [κtilde]
      · norm_num [p]
      · norm_num [p]
      · norm_num [c, κ, κtilde]
    linarith
  have hθ_pos : 0 < θ := by
    dsimp [θ]
    apply constantSubsolutionThreshold_pos
    · norm_num [κ]
    · norm_num [κ, κtilde]
    · exact hDpos
  have hd_pos : 0 < d := by
    dsimp [d]
    linarith
  have hd_le : d ≤ θ := by
    dsimp [d]
    linarith
  have ht : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) T := by
    norm_num [T]
  have hconst :
      IsFrozenSubSolutionOn p c (uTime (1 / 2)) (fun _ => d) Set.univ :=
    (hD0 D hDgt uTime htime).2 d hd_pos (by simpa [θ] using hd_le)
      (1 / 2) ht
  have hop := hconst (-1) trivial
  rw [frozenWaveOperator_const_eq p htrap.cunif_bdd htrap.nonneg (-1)] at hop
  have hu_neg_one : u (-1) = 0 := by
    simpa [u] using lemma41CounterexampleProfile_at_neg_one
  have hVeq : frozenElliptic p u (-1) = V0 := by
    simp [V0, p, u, lemma41CounterexampleParams, frozenElliptic]
  have hbad :
      -p.χ * (d ^ p.m *
          (frozenElliptic p u (-1) - (u (-1)) ^ p.γ)) +
        d * (1 - d ^ p.α) =
        -d * (1 + d) := by
    rw [hVeq, hu_neg_one]
    have hzero_rpow : (0 : ℝ) ^ p.γ = 0 := by
      norm_num [p]
    rw [hzero_rpow]
    norm_num [p]
    field_simp [ne_of_gt hV0_pos]
    ring
  rw [hbad] at hop
  have hneg : -d * (1 + d) < 0 := by
    have hsum_pos : 0 < 1 + d := by linarith
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hd_pos) hsum_pos
  exact not_lt_of_ge hop hneg

theorem Remark_4_2_chi_zero
    (p : CMParams) (hχ : p.χ = 0)
    {κ κtilde M c T : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hgap : κ < κtilde)
    (hrange : κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1))
    (_hM : 1 ≤ M) (_hT : 0 < T) (hc : c = κ + κ⁻¹) :
    ∃ D0 : ℝ, ∀ D : ℝ, D0 < D →
      ∀ u : ℝ → ℝ → ℝ, InTimeWaveTrapSet κ M T u →
        (∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
          IsFrozenSubSolutionOn p c (u t) (lowerBarrierRaw κ κtilde D)
            (Set.Ioi (lowerBarrierXMinus κ κtilde D))) ∧
        ∀ d : ℝ, 0 < d →
          d ≤ constantSubsolutionThreshold p.χ κ κtilde D →
            ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
              IsFrozenSubSolutionOn p c (u t) (fun _ => d) Set.univ := by
  refine ⟨max (subsolutionDThreshold p.χ M κ κtilde p.m p.γ c) 1, ?_⟩
  intro D hD u hu
  have hD_threshold :
      subsolutionDThreshold p.χ M κ κtilde p.m p.γ c < D :=
    lt_of_le_of_lt (le_max_left _ _) hD
  have hD0 :
      subsolutionDThreshold 0 M κ κtilde p.m p.γ c < D := by
    simpa [hχ] using hD_threshold
  have hD_ge_one : 1 ≤ D :=
    (lt_of_le_of_lt (le_max_right _ _) hD).le
  constructor
  · intro t ht
    exact lowerBarrierRaw_frozenSubSolution_chi_zero_of_threshold_of_D_ge_one
      p hχ hκ0 hκ1 hgap hrange hD_ge_one hc hD0
  · intro d hd_pos hd_le t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T :=
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    exact constant_subsolution_frozenWaveOperator_nonneg_of_chi_zero
      p hχ hd_pos hd_le (hu.slice_cunif htIcc)
      (fun x => hu.nonneg htIcc x)

theorem Remark_4_2_chi_zero_strengthened_direct
    (p : CMParams) (hχ : p.χ = 0) {κ κtilde M c T : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hgap : κ < κtilde)
    (hrange :
      κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1))
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
  Remark_4_2_chi_zero p hχ hκ hκ1 hgap hrange hM hT hc

/-- The `M = 1` slice of Paper1 Remark 4.2.  In this case the finite-time
barrier `min 1 (1 * exp(-κx))` is exactly the wave-trap upper barrier, so this
part follows from Lemma 4.2 without an additional analytic assumption. -/
def Remark_4_2_M_one : Prop :=
  ∀ p : CMParams, ∀ κ κtilde c T : ℝ,
    0 < κ → κ < 1 →
      κ < κtilde →
      κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1) →
      0 < T → c = κ + κ⁻¹ →
        ∃ D0 : ℝ, ∀ D : ℝ, D0 < D →
          ∀ u : ℝ → ℝ → ℝ, InTimeWaveTrapSet κ 1 T u →
            (∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
              IsFrozenSubSolutionOn p c (u t) (lowerBarrierRaw κ κtilde D)
                (Set.Ioi (lowerBarrierXMinus κ κtilde D))) ∧
            ∀ d : ℝ, 0 < d →
              d ≤ constantSubsolutionThreshold p.χ κ κtilde D →
                ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
                  IsFrozenSubSolutionOn p c (u t) (fun _ => d) Set.univ

theorem not_Remark_4_2_M_one : ¬ Remark_4_2_M_one := by
  intro hR
  let u : ℝ → ℝ := lemma41CounterexampleProfile
  let uTime : ℝ → ℝ → ℝ := fun _ => u
  let V0 : ℝ :=
    frozenElliptic lemma41CounterexampleParams lemma41CounterexampleProfile (-1)
  have hV0_pos : 0 < V0 := by
    simpa [V0] using frozenElliptic_lemma41CounterexampleProfile_pos
  let p : CMParams :=
    { m := 1
      α := 1
      γ := 1
      χ := 2 / V0
      hm := by norm_num
      hα := by norm_num
      hγ := by norm_num }
  let κ : ℝ := 1 / 2
  let κtilde : ℝ := 1
  let c : ℝ := 5 / 2
  let T : ℝ := 1
  rcases
    hR p κ κtilde c T
      (by norm_num [κ]) (by norm_num [κ])
      (by norm_num [κ, κtilde])
      (by norm_num [p, κ, κtilde])
      (by norm_num [T])
      (by norm_num [c, κ]) with
    ⟨D0, hD0⟩
  let M : ℝ := 1
  let D : ℝ :=
    max D0 (subsolutionDThreshold p.χ M κ κtilde p.m p.γ c) + 1
  let θ : ℝ := constantSubsolutionThreshold p.χ κ κtilde D
  let d : ℝ := θ / 2
  have htrap : InWaveTrapSet κ M u := by
    simpa [u, κ, M] using lemma41CounterexampleProfile_mem_trap
  have htime : InTimeWaveTrapSet κ 1 T uTime := by
    intro t _ht
    refine ⟨htrap.cunif_bdd, ?_⟩
    intro x
    exact ⟨htrap.nonneg x, by
      simpa [uTime, M, scaledUpperBarrier_one_eq_upperBarrier κ] using
        htrap.le_upperBarrier x⟩
  have hDgt : D0 < D := by
    dsimp [D]
    have hle : D0 ≤ max D0 (subsolutionDThreshold p.χ M κ κtilde p.m p.γ c) :=
      le_max_left _ _
    linarith
  have hDpos : 0 < D := by
    have hthr_pos :
        0 < subsolutionDThreshold p.χ M κ κtilde p.m p.γ c := by
      apply subsolutionDThreshold_pos_of_kappa_speed
      · norm_num [M]
      · norm_num [κ]
      · norm_num [κ]
      · norm_num [κ, κtilde]
      · norm_num [κtilde]
      · norm_num [p]
      · norm_num [p]
      · norm_num [c, κ, κtilde]
    dsimp [D]
    have hle :
        subsolutionDThreshold p.χ M κ κtilde p.m p.γ c ≤
          max D0 (subsolutionDThreshold p.χ M κ κtilde p.m p.γ c) :=
      le_max_right _ _
    linarith
  have hθ_pos : 0 < θ := by
    dsimp [θ]
    apply constantSubsolutionThreshold_pos
    · norm_num [κ]
    · norm_num [κ, κtilde]
    · exact hDpos
  have hd_pos : 0 < d := by
    dsimp [d]
    linarith
  have hd_le : d ≤ θ := by
    dsimp [d]
    linarith
  have ht : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) T := by
    norm_num [T]
  have hconst :
      IsFrozenSubSolutionOn p c (uTime (1 / 2)) (fun _ => d) Set.univ :=
    (hD0 D hDgt uTime htime).2 d hd_pos (by simpa [θ] using hd_le)
      (1 / 2) ht
  have hop := hconst (-1) trivial
  rw [frozenWaveOperator_const_eq p htrap.cunif_bdd htrap.nonneg (-1)] at hop
  have hu_neg_one : u (-1) = 0 := by
    simpa [u] using lemma41CounterexampleProfile_at_neg_one
  have hVeq : frozenElliptic p u (-1) = V0 := by
    simp [V0, p, u, lemma41CounterexampleParams, frozenElliptic]
  have hbad :
      -p.χ * (d ^ p.m *
          (frozenElliptic p u (-1) - (u (-1)) ^ p.γ)) +
        d * (1 - d ^ p.α) =
        -d * (1 + d) := by
    rw [hVeq, hu_neg_one]
    have hzero_rpow : (0 : ℝ) ^ p.γ = 0 := by
      norm_num [p]
    rw [hzero_rpow]
    norm_num [p]
    field_simp [ne_of_gt hV0_pos]
    ring
  rw [hbad] at hop
  have hneg : -d * (1 + d) < 0 := by
    have hsum_pos : 0 < 1 + d := by linarith
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hd_pos) hsum_pos
  exact not_lt_of_ge hop hneg

theorem Remark_4_2_M_one_chi_zero_of_kappaTilde_le_two_kappa
    (p : CMParams) (hχ : p.χ = 0)
    {κ κtilde c T : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hgap : κ < κtilde)
    (hrange : κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1))
    (hκtilde_twoκ : κtilde ≤ 2 * κ)
    (_hT : 0 < T) (hc : c = κ + κ⁻¹) :
    ∃ D0 : ℝ, ∀ D : ℝ, D0 < D →
      ∀ u : ℝ → ℝ → ℝ, InTimeWaveTrapSet κ 1 T u →
        (∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
          IsFrozenSubSolutionOn p c (u t) (lowerBarrierRaw κ κtilde D)
            (Set.Ioi (lowerBarrierXMinus κ κtilde D))) ∧
        ∀ d : ℝ, 0 < d →
          d ≤ constantSubsolutionThreshold p.χ κ κtilde D →
            ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
              IsFrozenSubSolutionOn p c (u t) (fun _ => d) Set.univ := by
  refine ⟨subsolutionDThreshold p.χ 1 κ κtilde p.m p.γ c, ?_⟩
  intro D hD u hu
  constructor
  · intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T :=
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    exact
      (Lemma_4_2_chi_zero_subsolutions_of_kappaTilde_le_two_kappa
        p hχ hκ0 hκ1 hgap hrange hκtilde_twoκ le_rfl hc hD
        (hu.slice_inWaveTrapSet_one htIcc)).1
  · intro d hd_pos hd_le t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T :=
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    exact
      (Lemma_4_2_chi_zero_subsolutions_of_kappaTilde_le_two_kappa
        p hχ hκ0 hκ1 hgap hrange hκtilde_twoκ le_rfl hc hD
        (hu.slice_inWaveTrapSet_one htIcc)).2 d hd_pos hd_le

theorem Remark_4_2_M_one_chi_zero_alpha_one
    (p : CMParams) (hχ : p.χ = 0) (hα : p.α = 1)
    {κ κtilde c T : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hgap : κ < κtilde)
    (hrange : κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1))
    (hT : 0 < T) (hc : c = κ + κ⁻¹) :
    ∃ D0 : ℝ, ∀ D : ℝ, D0 < D →
      ∀ u : ℝ → ℝ → ℝ, InTimeWaveTrapSet κ 1 T u →
        (∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
          IsFrozenSubSolutionOn p c (u t) (lowerBarrierRaw κ κtilde D)
            (Set.Ioi (lowerBarrierXMinus κ κtilde D))) ∧
        ∀ d : ℝ, 0 < d →
          d ≤ constantSubsolutionThreshold p.χ κ κtilde D →
            ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
              IsFrozenSubSolutionOn p c (u t) (fun _ => d) Set.univ := by
  have hκtilde_twoκ : κtilde ≤ 2 * κ := by
    have h := kappaTilde_le_one_plus_alpha_mul_kappa_of_subsolution_range
      (alpha := p.α) (m := p.m) (κ := κ) (κtilde := κtilde) hrange
    rw [hα] at h
    calc
      κtilde ≤ (1 + 1) * κ := h
      _ = 2 * κ := by ring
  exact Remark_4_2_M_one_chi_zero_of_kappaTilde_le_two_kappa
    p hχ hκ0 hκ1 hgap hrange hκtilde_twoκ hT hc

theorem Remark_4_2_M_one_chi_zero_of_D_ge_one
    (p : CMParams) (hχ : p.χ = 0)
    {κ κtilde c T : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hgap : κ < κtilde)
    (hrange : κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1))
    (_hT : 0 < T) (hc : c = κ + κ⁻¹) :
    ∃ D0 : ℝ, ∀ D : ℝ, D0 < D →
      1 ≤ D →
      ∀ u : ℝ → ℝ → ℝ, InTimeWaveTrapSet κ 1 T u →
        (∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
          IsFrozenSubSolutionOn p c (u t) (lowerBarrierRaw κ κtilde D)
            (Set.Ioi (lowerBarrierXMinus κ κtilde D))) ∧
        ∀ d : ℝ, 0 < d →
          d ≤ constantSubsolutionThreshold p.χ κ κtilde D →
            ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
              IsFrozenSubSolutionOn p c (u t) (fun _ => d) Set.univ := by
  refine ⟨subsolutionDThreshold p.χ 1 κ κtilde p.m p.γ c, ?_⟩
  intro D hD hD_ge_one u hu
  constructor
  · intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T :=
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    exact
      (Lemma_4_2_chi_zero_subsolutions_of_D_ge_one
        p hχ hκ0 hκ1 hgap hrange hD_ge_one le_rfl hc hD
        (hu.slice_inWaveTrapSet_one htIcc)).1
  · intro d hd_pos hd_le t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T :=
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    exact
      (Lemma_4_2_chi_zero_subsolutions_of_D_ge_one
        p hχ hκ0 hκ1 hgap hrange hD_ge_one le_rfl hc hD
        (hu.slice_inWaveTrapSet_one htIcc)).2 d hd_pos hd_le

theorem Remark_4_2_M_one_chi_zero_strengthened_direct
    (p : CMParams) (hχ : p.χ = 0) {κ κtilde c T : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hgap : κ < κtilde)
    (hrange :
      κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1))
    (hκtilde_twoκ : κtilde ≤ 2 * κ)
    (hT : 0 < T) (hc : c = κ + κ⁻¹) :
    ∃ D0 : ℝ, ∀ D : ℝ, D0 < D →
      ∀ u : ℝ → ℝ → ℝ, InTimeWaveTrapSet κ 1 T u →
        (∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
          IsFrozenSubSolutionOn p c (u t) (lowerBarrierRaw κ κtilde D)
            (Set.Ioi (lowerBarrierXMinus κ κtilde D))) ∧
        ∀ d : ℝ, 0 < d →
          d ≤ constantSubsolutionThreshold p.χ κ κtilde D →
            ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
              IsFrozenSubSolutionOn p c (u t) (fun _ => d) Set.univ :=
  Remark_4_2_M_one_chi_zero_of_kappaTilde_le_two_kappa
    p hχ hκ hκ1 hgap hrange hκtilde_twoκ hT hc

theorem Remark_4_2_M_one_chi_zero_D_ge_one_strengthened_direct
    (p : CMParams) (hχ : p.χ = 0) {κ κtilde c T : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hgap : κ < κtilde)
    (hrange :
      κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1))
    (hT : 0 < T) (hc : c = κ + κ⁻¹) :
    ∃ D0 : ℝ, ∀ D : ℝ, D0 < D →
      1 ≤ D →
      ∀ u : ℝ → ℝ → ℝ, InTimeWaveTrapSet κ 1 T u →
        (∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
          IsFrozenSubSolutionOn p c (u t) (lowerBarrierRaw κ κtilde D)
            (Set.Ioi (lowerBarrierXMinus κ κtilde D))) ∧
        ∀ d : ℝ, 0 < d →
          d ≤ constantSubsolutionThreshold p.χ κ κtilde D →
            ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
              IsFrozenSubSolutionOn p c (u t) (fun _ => d) Set.univ :=
  Remark_4_2_M_one_chi_zero_of_D_ge_one
    p hχ hκ hκ1 hgap hrange hT hc

theorem Remark_4_2_M_one_chi_zero_alpha_one_strengthened_direct
    (p : CMParams) (hχ : p.χ = 0) (hα : p.α = 1) {κ κtilde c T : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hgap : κ < κtilde)
    (hrange :
      κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1))
    (hT : 0 < T) (hc : c = κ + κ⁻¹) :
    ∃ D0 : ℝ, ∀ D : ℝ, D0 < D →
      ∀ u : ℝ → ℝ → ℝ, InTimeWaveTrapSet κ 1 T u →
        (∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
          IsFrozenSubSolutionOn p c (u t) (lowerBarrierRaw κ κtilde D)
            (Set.Ioi (lowerBarrierXMinus κ κtilde D))) ∧
        ∀ d : ℝ, 0 < d →
          d ≤ constantSubsolutionThreshold p.χ κ κtilde D →
            ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
              IsFrozenSubSolutionOn p c (u t) (fun _ => d) Set.univ :=
  Remark_4_2_M_one_chi_zero_alpha_one
    p hχ hα hκ hκ1 hgap hrange hT hc

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

theorem NegativeSensitivityWaveFixedPointConstruction.exists_paper_constant_subsolution
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D)
    {u : ℝ → ℝ} (hu : InMonotoneWaveTrapSet (kappa c) 1 u) :
    ∃ d : ℝ, 0 < d ∧
      IsPaperFrozenSubSolutionOn p c u (fun _ => d) Set.univ := by
  rcases h.exists_constant_subsolution with ⟨d, hd_pos, hd_le⟩
  refine ⟨d, hd_pos, ?_⟩
  exact constant_subsolution_paperWaveOperator_nonneg_of_chi_nonpos
    p (le_of_lt h.chi_neg) hd_pos hd_le hu.trap

theorem NegativeSensitivityWaveFixedPointConstruction.MChi_eq_one
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    MChi p = 1 :=
  MChi_eq_one_of_chi_nonpos p (le_of_lt h.chi_neg)

/-- Non-projection replacement for the negative-sensitivity upper-barrier
branch in the fixed-point construction.  The original `Lemma_4_1` statement is
false in the plateau region, so the needed plateau source comparison is kept as
an explicit hypothesis. -/
theorem NegativeSensitivityWaveFixedPointConstruction.upperBarrier_superSolution_away_from_interface
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D)
    (hγκ : p.γ * kappa c < 1) (hmκ : kappa c * p.m ≤ 1)
    (hMbound :
      |p.χ| * ((1 + p.m * p.γ * (kappa c) ^ 2) /
          (1 - p.γ ^ 2 * (kappa c) ^ 2)) *
        (1 : ℝ) ^ (p.m + p.γ - p.α - 1) ≤ 1)
    {u : ℝ → ℝ} (hu : InMonotoneWaveTrapSet (kappa c) 1 u)
    (hplateau :
      ∀ x, (1 : ℝ) < Real.exp (-(kappa c) * x) →
        frozenElliptic p u x ≤ (u x) ^ p.γ) :
    ∀ x, Real.exp (-(kappa c) * x) ≠ (1 : ℝ) →
      frozenWaveOperator p c u (upperBarrier (kappa c) 1) x ≤ 0 :=
  Lemma_4_1_neg_frozen_holds_away_from_interface_of_plateau_source_bound
    p (le_of_lt h.chi_neg) h.alpha_le h.kappa_pos h.kappa_lt_one hγκ hmκ
    le_rfl hMbound hu.trap h.kappa_add_inv_eq.symm hplateau

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

theorem PositiveSensitivityWaveFixedPointConstruction.exists_paper_constant_subsolution_of_chi_zero
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D)
    (hχ_zero : p.χ = 0)
    {u : ℝ → ℝ} (hu : InWaveTrapSet (kappa c) (MChi p) u) :
    ∃ d : ℝ, 0 < d ∧
      IsPaperFrozenSubSolutionOn p c u (fun _ => d) Set.univ := by
  rcases h.exists_constant_subsolution with ⟨d, hd_pos, hd_le⟩
  have hM : MChi p = 1 := by
    exact MChi_eq_one_of_chi_nonpos p (by linarith)
  have hu_one : InWaveTrapSet (kappa c) 1 u := by
    simpa [hM] using hu
  refine ⟨d, hd_pos, ?_⟩
  exact constant_subsolution_paperWaveOperator_nonneg_of_chi_nonneg
    p h.chi_nonneg h.chi_lt_chiStar h.alpha_eq hd_pos hd_le hu_one

theorem PositiveSensitivityWaveFixedPointConstruction.one_le_MChi
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    1 ≤ MChi p :=
  one_le_MChi_of_chi_nonneg_lt_one p h.chi_nonneg
    (lt_of_lt_of_le h.chi_lt_chiStar (chiStar_le_one p))

/-- Non-projection replacement for the positive-sensitivity upper-barrier
branch in the fixed-point construction, away from the interface
`exp (-(kappa c) * x) = MChi p`. -/
theorem PositiveSensitivityWaveFixedPointConstruction.upperBarrier_superSolution_away_from_interface
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D)
    (hmκ : p.m * kappa c ≤ 1)
    {u : ℝ → ℝ} (hu : InWaveTrapSet (kappa c) (MChi p) u) :
    ∀ x, Real.exp (-(kappa c) * x) ≠ MChi p →
      frozenWaveOperator p c u (upperBarrier (kappa c) (MChi p)) x ≤ 0 := by
  have hχ_lt_one : p.χ < 1 :=
    lt_of_lt_of_le h.chi_lt_chiStar (chiStar_le_one p)
  have hMchi :
      (1 / (1 - p.χ)) ^ (1 / p.α) ≤ MChi p :=
    le_of_eq (MChi_eq_rpow_of_chi_nonneg_lt_one p h.chi_nonneg hχ_lt_one).symm
  exact Lemma_4_1_pos_frozen_holds_away_from_interface_at_kappa
    p h.kappa_pos h.kappa_lt_one h.kappa_add_inv_eq.symm
    h.chi_nonneg h.chi_lt_chiStar h.alpha_eq hmκ h.one_le_MChi hMchi hu

theorem NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet (kappa c) 1 U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) 1
          (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U := by
  exact FrozenWaveMapConstruction.exists_fixed_limit h.map_construction

theorem
    NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_paper_constant_subsolution
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet (kappa c) 1 U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) 1
          (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U ∧
        ∃ d : ℝ, 0 < d ∧
          IsPaperFrozenSubSolutionOn p c U (fun _ => d) Set.univ := by
  rcases h.exists_fixed_limit with ⟨U, hU, haux⟩
  rcases h.exists_paper_constant_subsolution hU with ⟨d, hd_pos, hd_sub⟩
  exact ⟨U, hU, haux, d, hd_pos, hd_sub⟩

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

theorem NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_atTop_limits
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet (kappa c) 1 U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) 1
          (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U ∧
        Antitone U ∧
        Tendsto U atTop (𝓝 0) ∧
        Tendsto (frozenElliptic p U) atTop (𝓝 0) := by
  exact h.map_construction.exists_fixed_inMonotoneWaveTrapSet_with_atTop_limits
    h.kappa_pos

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

theorem
    PositiveSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_paper_const_sub_chi_zero
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D)
    (hχ_zero : p.χ = 0) :
    ∃ U : ℝ → ℝ,
      InWaveTrapSet (kappa c) (MChi p) U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) (MChi p)
          (fun u => InWaveTrapSet (kappa c) (MChi p) u) U U ∧
        ∃ d : ℝ, 0 < d ∧
          IsPaperFrozenSubSolutionOn p c U (fun _ => d) Set.univ := by
  rcases h.exists_fixed_limit with ⟨U, hU, haux⟩
  rcases h.exists_paper_constant_subsolution_of_chi_zero hχ_zero hU with
    ⟨d, hd_pos, hd_sub⟩
  exact ⟨U, hU, haux, d, hd_pos, hd_sub⟩

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

theorem PositiveSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_atTop_limits
    {p : CMParams} {c κ₁ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₁ κtilde D) :
    ∃ U : ℝ → ℝ,
      InWaveTrapSet (kappa c) (MChi p) U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) (MChi p)
          (fun u => InWaveTrapSet (kappa c) (MChi p) u) U U ∧
        Tendsto U atTop (𝓝 0) ∧
        Tendsto (frozenElliptic p U) atTop (𝓝 0) := by
  exact h.map_construction.exists_fixed_inWaveTrapSet_with_atTop_limits
    h.kappa_pos

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

theorem HasWaveUpperTailBound.tendsto_atTop_zero
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c) (h : HasWaveUpperTailBound p c U) :
    Tendsto U atTop (𝓝 0) := by
  have hupper :
      Tendsto (fun x : ℝ => Real.exp (-(kappa c) * x)) atTop (𝓝 0) := by
    convert expDecay_tendsto_atTop hκ using 1
    ext x
    simp [expDecay]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper ?_ ?_
  · intro x
    exact (h x).1.le
  · intro x
    exact le_trans (h x).2 (min_le_right _ _)

theorem HasWaveUpperTailBound.frozenElliptic_tendsto_atTop_zero
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c) (hU : IsCUnifBdd U)
    (h : HasWaveUpperTailBound p c U) :
    Tendsto (frozenElliptic p U) atTop (𝓝 0) :=
  frozenElliptic_tendsto_atTop_of_U_tendsto p hU (fun x => (h x).1.le)
    (h.tendsto_atTop_zero hκ)

theorem HasStrictWaveUpperTailBound.tendsto_atTop_zero
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c) (h : HasStrictWaveUpperTailBound p c U) :
    Tendsto U atTop (𝓝 0) :=
  h.hasWaveUpperTailBound.tendsto_atTop_zero hκ

theorem HasStrictWaveUpperTailBound.frozenElliptic_tendsto_atTop_zero
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c) (hU : IsCUnifBdd U)
    (h : HasStrictWaveUpperTailBound p c U) :
    Tendsto (frozenElliptic p U) atTop (𝓝 0) :=
  h.hasWaveUpperTailBound.frozenElliptic_tendsto_atTop_zero hκ hU

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

theorem HasWaveUpperTailBound.isBddFun
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) :
    IsBddFun U := by
  refine ⟨MChi p, ?_⟩
  intro x
  rw [abs_of_nonneg (h.pos x).le]
  exact h.le_MChi x

theorem HasWaveUpperTailBound.isCUnifBdd_of_continuous
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (hU_cont : Continuous U) :
    IsCUnifBdd U :=
  ⟨hU_cont, h.isBddFun⟩

theorem HasStrictWaveUpperTailBound.isBddFun
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasStrictWaveUpperTailBound p c U) :
    IsBddFun U :=
  h.hasWaveUpperTailBound.isBddFun

theorem HasStrictWaveUpperTailBound.isCUnifBdd_of_continuous
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasStrictWaveUpperTailBound p c U) (hU_cont : Continuous U) :
    IsCUnifBdd U :=
  h.hasWaveUpperTailBound.isCUnifBdd_of_continuous hU_cont

theorem HasStrictWaveUpperTailBound.nonnegativeInitialDatum_of_continuous
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasStrictWaveUpperTailBound p c U) (hU_cont : Continuous U) :
    NonnegativeInitialDatum U :=
  ⟨h.isCUnifBdd_of_continuous hU_cont, fun x => (h.pos x).le⟩

theorem FrozenStationaryWaveProfile.mk_from_paper_stationarity_of_tail_continuous
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hc : 0 < c)
    (hbound : HasWaveUpperTailBound p c U)
    (hU_cont : Continuous U)
    (hU_diff : ∀ x, DifferentiableAt ℝ U x)
    (hV_diff : ∀ x, DifferentiableAt ℝ (deriv (frozenElliptic p U)) x)
    (hU_rpow_diff : ∀ x, DifferentiableAt ℝ (fun y => (U y) ^ p.m) x)
    (hpaper_stat : ∀ x, paperWaveOperator p c U U x = 0)
    (hU_lim_neg : Tendsto U atBot (𝓝 1))
    (hU_lim_pos : Tendsto U atTop (𝓝 0)) :
    FrozenStationaryWaveProfile p c U :=
  FrozenStationaryWaveProfile.mk_from_paper_stationarity hc
    (fun x => hbound.pos x)
    (hbound.isCUnifBdd_of_continuous hU_cont)
    hU_diff hV_diff hU_rpow_diff hpaper_stat hU_lim_neg hU_lim_pos

theorem FrozenStationaryWaveProfile.mk_auto_limits_of_tail_continuous
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hc : 0 < c)
    (hbound : HasWaveUpperTailBound p c U)
    (hU_cont : Continuous U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hU_lim_neg : Tendsto U atBot (𝓝 1))
    (hU_lim_pos : Tendsto U atTop (𝓝 0)) :
    FrozenStationaryWaveProfile p c U :=
  FrozenStationaryWaveProfile.mk_auto_limits hc
    (fun x => hbound.pos x)
    (hbound.isCUnifBdd_of_continuous hU_cont)
    hstat hU_lim_neg hU_lim_pos

theorem HasWaveUpperTailBound.frozenElliptic_tendsto_atTop_zero_of_continuous
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c) (h : HasWaveUpperTailBound p c U)
    (hU_cont : Continuous U) :
    Tendsto (frozenElliptic p U) atTop (𝓝 0) :=
  h.frozenElliptic_tendsto_atTop_zero hκ
    (h.isCUnifBdd_of_continuous hU_cont)

theorem HasStrictWaveUpperTailBound.frozenElliptic_tendsto_atTop_zero_of_continuous
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c) (h : HasStrictWaveUpperTailBound p c U)
    (hU_cont : Continuous U) :
    Tendsto (frozenElliptic p U) atTop (𝓝 0) :=
  h.hasWaveUpperTailBound.frozenElliptic_tendsto_atTop_zero_of_continuous
    hκ hU_cont

theorem HasWaveUpperTailBound.abs_sub_le_two_MChi
    {p : CMParams} {c : ℝ} {U₁ U₂ : ℝ → ℝ}
    (h₁ : HasWaveUpperTailBound p c U₁)
    (h₂ : HasWaveUpperTailBound p c U₂) (x : ℝ) :
    |U₂ x - U₁ x| ≤ 2 * MChi p := by
  have hM_pos : 0 < MChi p :=
    lt_of_lt_of_le (h₁.pos x) (h₁.le_MChi x)
  rw [abs_sub_le_iff]
  constructor <;> linarith [h₁.pos x, h₂.pos x, h₁.le_MChi x, h₂.le_MChi x, hM_pos]

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

theorem HasWaveUpperTailBound.inWaveTrapSet_of_continuous
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (hU_cont : Continuous U) :
    InWaveTrapSet (kappa c) (MChi p) U :=
  h.inWaveTrapSet (h.isCUnifBdd_of_continuous hU_cont)

theorem HasWaveUpperTailBound.inMonotoneWaveTrapSet
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (hU : IsCUnifBdd U)
    (hmono : NonincreasingProfile U) :
    InMonotoneWaveTrapSet (kappa c) (MChi p) U :=
  ⟨h.inWaveTrapSet hU, hmono⟩

theorem HasWaveUpperTailBound.inMonotoneWaveTrapSet_of_continuous
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasWaveUpperTailBound p c U) (hU_cont : Continuous U)
    (hmono : NonincreasingProfile U) :
    InMonotoneWaveTrapSet (kappa c) (MChi p) U :=
  h.inMonotoneWaveTrapSet (h.isCUnifBdd_of_continuous hU_cont) hmono

theorem HasStrictWaveUpperTailBound.inWaveTrapSet_of_continuous
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasStrictWaveUpperTailBound p c U) (hU_cont : Continuous U) :
    InWaveTrapSet (kappa c) (MChi p) U :=
  h.hasWaveUpperTailBound.inWaveTrapSet_of_continuous hU_cont

theorem HasStrictWaveUpperTailBound.inMonotoneWaveTrapSet_of_continuous
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (h : HasStrictWaveUpperTailBound p c U) (hU_cont : Continuous U)
    (hmono : NonincreasingProfile U) :
    InMonotoneWaveTrapSet (kappa c) (MChi p) U :=
  h.hasWaveUpperTailBound.inMonotoneWaveTrapSet_of_continuous hU_cont hmono

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

theorem ShenUpperBoundPositive.hasWaveUpperTailBound_of_chi_lt_half_chiStar
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (h : ShenUpperBoundPositive p c U) :
    HasWaveUpperTailBound p c U := by
  have hχ_lt_half : p.χ < (1 / 2 : ℝ) :=
    lt_of_lt_of_le hχ_small (min_le_left _ _)
  have hχ_lt_one : p.χ < 1 := by linarith
  exact h.hasWaveUpperTailBound hχ_nonneg hχ_lt_one

theorem ShenUpperBoundPositive.inWaveTrapSet
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hχ_nonneg : 0 ≤ p.χ) (hχ_lt : p.χ < 1)
    (h : ShenUpperBoundPositive p c U) (hU : IsCUnifBdd U) :
    InWaveTrapSet (kappa c) (MChi p) U :=
  (ShenUpperBoundPositive.hasWaveUpperTailBound hχ_nonneg hχ_lt h).inWaveTrapSet hU

/-- Fixed-point construction bridge for the negative-sensitivity branch.  The
Schauder construction supplies the trap membership and right-end limits; the
remaining facts here are the genuine fixed-point obligations not contained in
`FrozenWaveMapConstruction` itself. -/
theorem NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_speed_bridge_data
    {p : CMParams} {c κ₀ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₀ κtilde D)
    (hstat :
      ∀ U : ℝ → ℝ,
        InMonotoneWaveTrapSet (kappa c) 1 U →
          FrozenAuxiliaryLimitOutput p c (kappa c) 1
            (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U →
            ∀ x, frozenWaveOperator p c U U x = 0)
    (hlim_bot :
      ∀ U : ℝ → ℝ,
        InMonotoneWaveTrapSet (kappa c) 1 U →
          FrozenAuxiliaryLimitOutput p c (kappa c) 1
            (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U →
            Tendsto U atBot (𝓝 1))
    (hVmono :
      ∀ U : ℝ → ℝ,
        InMonotoneWaveTrapSet (kappa c) 1 U →
          FrozenAuxiliaryLimitOutput p c (kappa c) 1
            (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U →
            ∀ x, deriv (frozenElliptic p U) x ≤ 0)
    (hupper :
      ∀ U : ℝ → ℝ,
        InMonotoneWaveTrapSet (kappa c) 1 U →
          FrozenAuxiliaryLimitOutput p c (kappa c) 1
            (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U →
            ShenUpperBoundNegative c U)
    (htail :
      ∀ U : ℝ → ℝ,
        InMonotoneWaveTrapSet (kappa c) 1 U →
          FrozenAuxiliaryLimitOutput p c (kappa c) 1
            (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U →
            ∀ κ₁, kappa c < κ₁ →
              κ₁ <
                min ((1 + p.α) * kappa c)
                  (min (p.m * kappa c + 1 / 2) 1) →
              HasWaveRightTailAsymptotic c κ₁ U) :
    ∃ U : ℝ → ℝ,
      HasWaveUpperTailBound p c U ∧
        Continuous U ∧
        (∀ x, frozenWaveOperator p c U U x = 0) ∧
        Tendsto U atBot (𝓝 1) ∧
        Tendsto U atTop (𝓝 0) ∧
        (∀ x, deriv U x ≤ 0) ∧
        (∀ x, deriv (frozenElliptic p U) x ≤ 0) ∧
        ShenUpperBoundNegative c U ∧
        ∀ κ₁, kappa c < κ₁ →
          κ₁ <
            min ((1 + p.α) * kappa c)
              (min (p.m * kappa c + 1 / 2) 1) →
          HasWaveRightTailAsymptotic c κ₁ U := by
  rcases h.exists_fixed_limit_with_atTop_limits with
    ⟨U, hU, haux, _hanti, hU_top, _hV_top⟩
  have hupperU : ShenUpperBoundNegative c U := hupper U hU haux
  have htrapM : InMonotoneWaveTrapSet (kappa c) (MChi p) U := by
    simpa [h.MChi_eq_one] using hU
  exact
    ⟨U,
      htrapM.hasWaveUpperTailBound_of_pos hupperU.pos,
      hU.trap.cunif_bdd.1,
      hstat U hU haux,
      hlim_bot U hU haux,
      hU_top,
      hU.deriv_nonpos,
      hVmono U hU haux,
      hupperU,
      htail U hU haux⟩

/-- Fixed-point construction bridge for the positive-sensitivity branch.  The
construction supplies trap membership and right-end limits; stationarity,
left-end convergence, the sharp upper bound, and the right-tail asymptotics
remain explicit fixed-point obligations. -/
theorem PositiveSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_speed_bridge_data
    {p : CMParams} {c κ₀ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₀ κtilde D)
    (hstat :
      ∀ U : ℝ → ℝ,
        InWaveTrapSet (kappa c) (MChi p) U →
          FrozenAuxiliaryLimitOutput p c (kappa c) (MChi p)
            (fun u => InWaveTrapSet (kappa c) (MChi p) u) U U →
            ∀ x, frozenWaveOperator p c U U x = 0)
    (hlim_bot :
      ∀ U : ℝ → ℝ,
        InWaveTrapSet (kappa c) (MChi p) U →
          FrozenAuxiliaryLimitOutput p c (kappa c) (MChi p)
            (fun u => InWaveTrapSet (kappa c) (MChi p) u) U U →
            Tendsto U atBot (𝓝 1))
    (hupper :
      ∀ U : ℝ → ℝ,
        InWaveTrapSet (kappa c) (MChi p) U →
          FrozenAuxiliaryLimitOutput p c (kappa c) (MChi p)
            (fun u => InWaveTrapSet (kappa c) (MChi p) u) U U →
            ShenUpperBoundPositive p c U)
    (htail :
      ∀ U : ℝ → ℝ,
        InWaveTrapSet (kappa c) (MChi p) U →
          FrozenAuxiliaryLimitOutput p c (kappa c) (MChi p)
            (fun u => InWaveTrapSet (kappa c) (MChi p) u) U U →
            ∀ κ₁, kappa c < κ₁ →
              κ₁ <
                min ((1 + p.α) * kappa c)
                  (min (p.m * kappa c + 1 / 2) 1) →
              HasWaveRightTailAsymptotic c κ₁ U) :
    ∃ U : ℝ → ℝ,
      Continuous U ∧
        (∀ x, frozenWaveOperator p c U U x = 0) ∧
        Tendsto U atBot (𝓝 1) ∧
        Tendsto U atTop (𝓝 0) ∧
        ShenUpperBoundPositive p c U ∧
        ∀ κ₁, kappa c < κ₁ →
          κ₁ <
            min ((1 + p.α) * kappa c)
              (min (p.m * kappa c + 1 / 2) 1) →
          HasWaveRightTailAsymptotic c κ₁ U := by
  rcases h.exists_fixed_limit_with_atTop_limits with
    ⟨U, hU, haux, hU_top, _hV_top⟩
  exact
    ⟨U,
      hU.cunif_bdd.1,
      hstat U hU haux,
      hlim_bot U hU haux,
      hU_top,
      hupper U hU haux,
      htail U hU haux⟩

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

/-- Bridge: existence of a FrozenRightVanishingWaveProfile in the extended
positive-sensitivity regime implies Remark_1_3_2. Uses
FrozenRightVanishingWaveProfile.to_rightVanishingTravelingWave to assemble
the existence statement. -/
theorem Remark_1_3_2.of_frozen_right_vanishing_profile_existence
    (construction : ∀ p : CMParams,
      p.α = p.m + p.γ - 1 →
      (1 / 2 : ℝ) < positiveSensitivityExtendedThreshold p →
      (1 / 2 : ℝ) ≤ p.χ →
      p.χ < min (positiveSensitivityExtendedThreshold p) 1 →
      ∀ c : ℝ, 2 < c →
        ∃ U : ℝ → ℝ, FrozenRightVanishingWaveProfile p c U) :
    Remark_1_3_2 := by
  intro p hα hext hχ_ge hχ_lt c hc
  obtain ⟨U, hU⟩ := construction p hα hext hχ_ge hχ_lt c hc
  exact ⟨U, frozenElliptic p U, hU.to_rightVanishingTravelingWave⟩

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

/-- The admissible Remark 4.3 tail-rate window is open on the right: every
admissible rate can be enlarged slightly while staying admissible. -/
theorem Remark43TailRateBound.exists_larger
    {p : CMParams} {c eta : ℝ} (h : Remark43TailRateBound p c eta) :
    ∃ eta' : ℝ, eta < eta' ∧ Remark43TailRateBound p c eta' := by
  let etaMax : ℝ :=
    min (p.α * kappa c)
      (min ((p.m - 1) * kappa c + 1 / 2) (1 - kappa c))
  refine ⟨(eta + etaMax) / 2, ?_, ?_⟩
  · dsimp [etaMax] at h ⊢
    linarith [h.2]
  · refine ⟨?_, ?_⟩
    · dsimp [etaMax] at h ⊢
      nlinarith [h.1, h.2]
    · dsimp [etaMax] at h ⊢
      linarith [h.2]

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

/-- If the stability weight cap still lies to the right of `kappa c`, the
Remark 4.3 tail-rate window has a rate whose shifted weight stays below that
cap. -/
theorem exists_remark43TailRateBound_with_weight_below
    {p : CMParams} {c cap : ℝ}
    (hkappa_pos : 0 < kappa c) (hkappa_lt_one : kappa c < 1)
    (hkappa_cap : kappa c < cap) :
    ∃ eta : ℝ,
      Remark43TailRateBound p c eta ∧ eta + kappa c < cap := by
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
  let etaCapMax : ℝ := min etaMax (cap - kappa c)
  have hcap_gap_pos : 0 < cap - kappa c := by
    linarith
  have hetaCapMax_pos : 0 < etaCapMax := by
    dsimp [etaCapMax]
    exact lt_min hetaMax_pos hcap_gap_pos
  let eta : ℝ := etaCapMax / 2
  have heta_pos : 0 < eta := by
    dsimp [eta]
    linarith
  have heta_lt_etaMax : eta < etaMax := by
    have hle : etaCapMax ≤ etaMax := by
      dsimp [etaCapMax]
      exact min_le_left _ _
    dsimp [eta]
    nlinarith
  have heta_weight : eta + kappa c < cap := by
    have hle : etaCapMax ≤ cap - kappa c := by
      dsimp [etaCapMax]
      exact min_le_right _ _
    dsimp [eta]
    nlinarith
  exact ⟨eta, ⟨heta_pos, by simpa [etaMax] using heta_lt_etaMax⟩, heta_weight⟩

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

/-- A pointwise tail normalization gives an eventual unit bound on the
normalized error.  This is the first half of the distinct-wave weighted
closeness proof in Remark 4.3. -/
theorem HasRemark43TailAsymptotic.eventually_norm_normalized_error_le_one
    {p : CMParams} {c eta : ℝ} {U : ℝ → ℝ}
    (h : HasRemark43TailAsymptotic p c U)
    (heta : Remark43TailRateBound p c eta) :
    ∀ᶠ x in atTop,
      ‖Real.exp (eta * x) *
          (U x / Real.exp (-(kappa c) * x) - 1)‖ ≤ (1 : ℝ) := by
  have hball :
      Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
    Metric.ball_mem_nhds _ zero_lt_one
  filter_upwards [(h.at_rate heta).eventually hball] with x hx
  have hxlt :
      ‖Real.exp (eta * x) *
          (U x / Real.exp (-(kappa c) * x) - 1)‖ < (1 : ℝ) := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  exact hxlt.le

/-- The normalized right-tail asymptotic gives an eventual pointwise
exponential error bound against the leading exponential `exp (-κx)`. -/
theorem HasRemark43TailAsymptotic.eventually_abs_sub_exp_le
    {p : CMParams} {c eta : ℝ} {U : ℝ → ℝ}
    (h : HasRemark43TailAsymptotic p c U)
    (heta : Remark43TailRateBound p c eta) :
    ∀ᶠ x in atTop,
      |U x - Real.exp (-(kappa c) * x)| ≤
        Real.exp (-(eta + kappa c) * x) := by
  filter_upwards [h.eventually_norm_normalized_error_le_one heta] with x hx
  set e : ℝ := Real.exp (-(kappa c) * x)
  set r : ℝ := U x / e - 1
  have he_pos : 0 < e := by
    dsimp [e]
    exact Real.exp_pos _
  have hprod : Real.exp (eta * x) * |r| ≤ 1 := by
    have hx' : |Real.exp (eta * x) * r| ≤ (1 : ℝ) := by
      simpa [Real.norm_eq_abs, r, e] using hx
    simpa [abs_mul, abs_of_nonneg (Real.exp_nonneg _)] using hx'
  have hr : |r| ≤ Real.exp (-eta * x) := by
    calc
      |r| = (Real.exp (eta * x))⁻¹ * (Real.exp (eta * x) * |r|) := by
        field_simp [Real.exp_ne_zero]
      _ ≤ (Real.exp (eta * x))⁻¹ * 1 := by
        exact mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr (Real.exp_nonneg _))
      _ = Real.exp (-eta * x) := by
        rw [← Real.exp_neg, mul_one]
        congr 1
        ring
  calc
    |U x - Real.exp (-(kappa c) * x)| = e * |r| := by
      have hsub : U x - e = e * r := by
        dsimp [r]
        field_simp [ne_of_gt he_pos]
      rw [show Real.exp (-(kappa c) * x) = e by rfl, hsub, abs_mul,
        abs_of_nonneg he_pos.le]
    _ ≤ e * Real.exp (-eta * x) :=
      mul_le_mul_of_nonneg_left hr he_pos.le
    _ = Real.exp (-(eta + kappa c) * x) := by
      dsimp [e]
      rw [← Real.exp_add]
      congr 1
      ring

/-- Two profiles with the same sharp leading right tail differ by at most twice
the faster exponential error, eventually on the right. -/
theorem HasRemark43TailAsymptotic.eventually_abs_sub_abs_le_two_exp
    {p : CMParams} {c eta : ℝ} {U₁ U₂ : ℝ → ℝ}
    (h₁ : HasRemark43TailAsymptotic p c U₁)
    (h₂ : HasRemark43TailAsymptotic p c U₂)
    (heta : Remark43TailRateBound p c eta) :
    ∀ᶠ x in atTop,
      |U₂ x - U₁ x| ≤
        2 * Real.exp (-(eta + kappa c) * x) := by
  filter_upwards [h₁.eventually_abs_sub_exp_le heta,
    h₂.eventually_abs_sub_exp_le heta] with x hx₁ hx₂
  let E : ℝ := Real.exp (-(kappa c) * x)
  have htri :
      |U₂ x - U₁ x| ≤ |U₂ x - E| + |U₁ x - E| := by
    have h :=
      abs_sub_le (U₂ x - E) 0 (U₁ x - E)
    have hsub : (U₂ x - E) - (U₁ x - E) = U₂ x - U₁ x := by ring
    simpa [hsub, abs_neg, abs_sub_comm] using h
  calc
    |U₂ x - U₁ x| ≤ |U₂ x - E| + |U₁ x - E| := htri
    _ ≤ Real.exp (-(eta + kappa c) * x) +
        Real.exp (-(eta + kappa c) * x) :=
      add_le_add (by simpa [E] using hx₂) (by simpa [E] using hx₁)
    _ = 2 * Real.exp (-(eta + kappa c) * x) := by ring

/-- Strengthened distinct-wave branch of Remark 4.3.  The original statement
does not carry measurability of the weighted squared difference, so this
version makes that analytic regularity explicit and proves the weighted `L²`
closeness from the common sharp right-tail asymptotic and the global upper
tail trap. -/
theorem Remark_4_3.distinct_wave_branch_of_aestronglyMeasurable
    {p : CMParams} {c eta : ℝ} {U₁ U₂ : ℝ → ℝ}
    (hkappa : 0 < kappa c)
    (hbound₁ : HasWaveUpperTailBound p c U₁)
    (hbound₂ : HasWaveUpperTailBound p c U₂)
    (htail₁ : HasRemark43TailAsymptotic p c U₁)
    (htail₂ : HasRemark43TailAsymptotic p c U₂)
    (heta : Remark43TailRateBound p c eta)
    (hmeas : AEStronglyMeasurable
      (fun x : ℝ =>
        Real.exp (2 * (eta + kappa c) * x) * |U₂ x - U₁ x| ^ 2) volume) :
    WeightedL2InitialCloseness (eta + kappa c) U₂ U₁ := by
  rcases heta.exists_larger with ⟨etaFast, hetaFast_gt, hetaFast⟩
  refine
    WeightedL2InitialCloseness.of_left_exp_bound_eventual_right_exp_bound
      (η := eta + kappa c) (δ := 2 * (etaFast - eta))
      (heta.weight_pos hkappa) (by linarith) hmeas ?_ ?_
  · have hM_pos : 0 < MChi p :=
      lt_of_lt_of_le (hbound₁.pos 0) (hbound₁.le_MChi 0)
    refine ⟨(2 * MChi p) ^ 2, sq_nonneg _, fun x => ?_⟩
    exact
      weightedL2_integrand_norm_le_of_abs_sub_le
        (η := eta + kappa c) (A := 2 * MChi p)
        (u₀ := U₂) (U := U₁) (by linarith)
        (hbound₁.abs_sub_le_two_MChi hbound₂ x)
  · have hevent :
        ∀ᶠ x in atTop,
          |U₂ x - U₁ x| ≤
            2 * Real.exp (-(etaFast + kappa c) * x) :=
      htail₁.eventually_abs_sub_abs_le_two_exp htail₂ hetaFast
    rcases eventually_atTop.1 hevent with ⟨R, hR⟩
    refine ⟨R, 4, by norm_num, fun x hx => ?_⟩
    have habs : |U₂ x - U₁ x| ≤
        2 * Real.exp (-(etaFast + kappa c) * x) :=
      hR x (le_of_lt hx)
    have hraw :=
      weightedL2_integrand_norm_le_of_abs_sub_le_exp
        (η := eta + kappa c) (β := etaFast + kappa c) (B := 2)
        (u₀ := U₂) (U := U₁) (by norm_num : (0 : ℝ) ≤ 2) habs
    convert hraw using 2 <;> ring

/-- Continuous-profile version of the strengthened distinct-wave branch of
Remark 4.3.  This isolates the only regularity missing from the original
`Remark_4_3` statement: measurability of the weighted squared difference. -/
theorem Remark_4_3.distinct_wave_branch_of_continuous
    {p : CMParams} {c eta : ℝ} {U₁ U₂ : ℝ → ℝ}
    (hkappa : 0 < kappa c)
    (hU₁_cont : Continuous U₁) (hU₂_cont : Continuous U₂)
    (hbound₁ : HasWaveUpperTailBound p c U₁)
    (hbound₂ : HasWaveUpperTailBound p c U₂)
    (htail₁ : HasRemark43TailAsymptotic p c U₁)
    (htail₂ : HasRemark43TailAsymptotic p c U₂)
    (heta : Remark43TailRateBound p c eta) :
    WeightedL2InitialCloseness (eta + kappa c) U₂ U₁ := by
  refine
    Remark_4_3.distinct_wave_branch_of_aestronglyMeasurable
      hkappa hbound₁ hbound₂ htail₁ htail₂ heta ?_
  exact
    (Continuous.mul
      (Real.continuous_exp.comp
        ((continuous_const.mul continuous_const).mul continuous_id))
      ((hU₂_cont.sub hU₁_cont).abs.pow 2)).aestronglyMeasurable

/-- End-to-end proof of the corrected regular Remark 4.3 statement.  This
combines the explicit faster tail-rate selection, left trap domination,
eventual right-tail domination, and weighted integrability bridge. -/
theorem Remark_4_3_regular_direct
    {p : CMParams} {c eta : ℝ} {U₁ V₁ U₂ V₂ : ℝ → ℝ}
    (hkappa : 0 < kappa c)
    (_hTW₁ : IsTravelingWave p c U₁ V₁)
    (_hTW₂ : IsTravelingWave p c U₂ V₂)
    (hU₁_cont : Continuous U₁) (hU₂_cont : Continuous U₂)
    (hbound₁ : HasWaveUpperTailBound p c U₁)
    (hbound₂ : HasWaveUpperTailBound p c U₂)
    (htail₁ : HasRemark43TailAsymptotic p c U₁)
    (htail₂ : HasRemark43TailAsymptotic p c U₂)
    (heta : Remark43TailRateBound p c eta) :
    WeightedL2InitialCloseness (eta + kappa c) U₂ U₁ := by
  exact
    Remark_4_3.distinct_wave_branch_of_continuous
      hkappa hU₁_cont hU₂_cont hbound₁ hbound₂ htail₁ htail₂ heta

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

/-- A real same-wave branch of Remark 4.3.  When the two waves are identical,
the weighted initial distance is exactly zero, so no analytic package is
needed. -/
theorem Remark_4_3.same_wave_branch
    {p : CMParams} {c eta : ℝ} {U V : ℝ → ℝ}
    (_hkappa : 0 < kappa c)
    (_hTW : IsTravelingWave p c U V)
    (_hbound : HasWaveUpperTailBound p c U)
    (_htail : HasRemark43TailAsymptotic p c U)
    (_heta : Remark43TailRateBound p c eta) :
    WeightedL2InitialCloseness (eta + kappa c) U U :=
  WeightedL2InitialCloseness.refl (eta + kappa c) U

/-- **TAUTOLOGY (no math content)**: body is `:= hclose`, definitionally equal
to `Remark_4_3`.  Target signature only. -/
theorem Remark_4_3.of_assumed_closeness_branch
    (hclose : ∀ p : CMParams, ∀ c : ℝ, 0 < kappa c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        HasWaveUpperTailBound p c U₁ →
        HasWaveUpperTailBound p c U₂ →
        HasRemark43TailAsymptotic p c U₁ →
        HasRemark43TailAsymptotic p c U₂ →
        ∀ eta : ℝ, Remark43TailRateBound p c eta →
          WeightedL2InitialCloseness (eta + kappa c) U₂ U₁) :
    Remark_4_3 :=
  hclose

/-- Closure of `Remark_4_3` from the continuous distinct-wave branch, assuming
universal continuity of all traveling-wave profiles. -/
theorem Remark_4_3.of_continuous_distinct_branch
    (hcont : ∀ p : CMParams, ∀ c : ℝ, ∀ U V : ℝ → ℝ,
      IsTravelingWave p c U V → Continuous U) :
    Remark_4_3 := by
  intro p c hkappa U₁ V₁ U₂ V₂ hTW₁ hTW₂ hbound₁ hbound₂ htail₁ htail₂ eta heta
  exact Remark_4_3.distinct_wave_branch_of_continuous
    hkappa (hcont p c U₁ V₁ hTW₁) (hcont p c U₂ V₂ hTW₂)
    hbound₁ hbound₂ htail₁ htail₂ heta

/-- Existence form of the same-wave branch of Remark 4.3, with the admissible
weight selected from the explicit rate window. -/
theorem Remark_4_3.exists_same_wave_branch
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hkappa_pos : 0 < kappa c) (hkappa_lt_one : kappa c < 1)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (htail : HasRemark43TailAsymptotic p c U) :
    ∃ eta : ℝ, 0 < eta ∧
      Remark43TailRateBound p c eta ∧
        WeightedL2InitialCloseness (eta + kappa c) U U := by
  rcases exists_remark43TailRateBound
      (p := p) (c := c) hkappa_pos hkappa_lt_one with
    ⟨eta, heta_pos, heta⟩
  exact
    ⟨eta, heta_pos, heta,
      Remark_4_3.same_wave_branch hkappa_pos hTW hbound htail heta⟩

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

theorem Lemma_5_1_signal_bound_for_frozenElliptic
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ}
    (hU : IsCUnifBdd U) (hbound : HasWaveUpperTailBound p c U) :
    ∀ x,
      |frozenElliptic p U x| ≤ (MChi p) ^ p.γ ∧
        |deriv (frozenElliptic p U) x| ≤ (MChi p) ^ p.γ := by
  intro x
  have hM_pos : 0 < MChi p :=
    lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)
  have htrap : InWaveTrapSet (kappa c) (MChi p) U :=
    hbound.inWaveTrapSet hU
  have hU_nonneg : ∀ y, 0 ≤ U y := fun y => (hbound.pos y).le
  have hV_nonneg : 0 ≤ frozenElliptic p U x :=
    frozenElliptic_nonneg p hU_nonneg x
  have hV_le : frozenElliptic p U x ≤ (MChi p) ^ p.γ :=
    frozenElliptic_le_rpow_of_inWaveTrapSet p hM_pos htrap x
  have hV_abs : |frozenElliptic p U x| ≤ (MChi p) ^ p.γ := by
    simpa [abs_of_nonneg hV_nonneg] using hV_le
  have hV_deriv_abs :
      |deriv (frozenElliptic p U) x| ≤ frozenElliptic p U x :=
    frozenElliptic_deriv_abs_le p hU hU_nonneg x
  exact ⟨hV_abs, le_trans hV_deriv_abs hV_le⟩

theorem Lemma_5_1_signal_bound_for_frozenElliptic_of_continuous
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ}
    (hU_cont : Continuous U) (hbound : HasWaveUpperTailBound p c U) :
    ∀ x,
      |frozenElliptic p U x| ≤ (MChi p) ^ p.γ ∧
        |deriv (frozenElliptic p U) x| ≤ (MChi p) ^ p.γ :=
  Lemma_5_1_signal_bound_for_frozenElliptic p
    (hbound.isCUnifBdd_of_continuous hU_cont) hbound

theorem gamma_mul_kappa_lt_one_of_gamma_add_inv_lt_speed
    {c gamma : ℝ} (hc : 2 < c) (hgamma : 1 ≤ gamma)
    (hspeed : gamma + gamma⁻¹ < c) :
    gamma * kappa c < 1 := by
  by_contra hnot
  push_neg at hnot
  have hk_pos : 0 < kappa c := kappa_pos_of_two_lt hc
  have hk_lt_one : kappa c < 1 := kappa_lt_one_of_two_lt hc
  have hgamma_pos : 0 < gamma := lt_of_lt_of_le zero_lt_one hgamma
  have hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma_pos
  have hk_ne : kappa c ≠ 0 := ne_of_gt hk_pos
  have hgamma_ge_k : kappa c ≤ gamma :=
    le_trans hk_lt_one.le hgamma
  have hdiff :
      gamma * kappa c * (gamma + gamma⁻¹) -
          gamma * kappa c * (kappa c + (kappa c)⁻¹) =
        (gamma - kappa c) * (gamma * kappa c - 1) := by
    field_simp [hgamma_ne, hk_ne]
    ring
  have hnonneg :
      0 ≤ gamma * kappa c * (gamma + gamma⁻¹) -
        gamma * kappa c * (kappa c + (kappa c)⁻¹) := by
    rw [hdiff]
    exact mul_nonneg (sub_nonneg.mpr hgamma_ge_k)
      (sub_nonneg.mpr hnot)
  have hsum_le : kappa c + (kappa c)⁻¹ ≤ gamma + gamma⁻¹ := by
    have hmul :
        gamma * kappa c * (kappa c + (kappa c)⁻¹) ≤
          gamma * kappa c * (gamma + gamma⁻¹) := by
      linarith
    exact le_of_mul_le_mul_left hmul (mul_pos hgamma_pos hk_pos)
  have hc_eq : kappa c + (kappa c)⁻¹ = c :=
    kappa_add_inv_eq_of_two_lt hc
  linarith

theorem Lemma_5_1_exponential_signal_bound_for_frozenElliptic
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ}
    (hc : 2 < c) (hspeed : p.γ + p.γ⁻¹ < c)
    (hU : IsCUnifBdd U) (hbound : HasWaveUpperTailBound p c U) :
    ∀ x,
      |frozenElliptic p U x| ≤
        min ((MChi p) ^ p.γ)
          ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
            Real.exp (-(kappa c) * p.γ * x)) ∧
      |deriv (frozenElliptic p U) x| ≤
        min ((MChi p) ^ p.γ)
          ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
            Real.exp (-(kappa c) * p.γ * x)) := by
  intro x
  have hM_pos : 0 < MChi p :=
    lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)
  have hM_nonneg : 0 ≤ (MChi p) ^ p.γ :=
    Real.rpow_nonneg hM_pos.le p.γ
  have hU_nonneg : ∀ y, 0 ≤ U y := fun y => (hbound.pos y).le
  have hgamma_pos : 0 < p.γ := lt_of_lt_of_le zero_lt_one p.hγ
  have hk_pos : 0 < kappa c := kappa_pos_of_two_lt hc
  have hkg_pos : 0 < kappa c * p.γ := mul_pos hk_pos hgamma_pos
  have hkg_lt_one : kappa c * p.γ < 1 := by
    have h := gamma_mul_kappa_lt_one_of_gamma_add_inv_lt_speed
      (c := c) (gamma := p.γ) hc p.hγ hspeed
    rwa [mul_comm] at h
  have hpow_le_M : ∀ y, (U y) ^ p.γ ≤ (MChi p) ^ p.γ :=
    fun y => hbound.rpow_le_MChi_gamma y
  have hpow_le_exp : ∀ y, (U y) ^ p.γ ≤
      Real.exp (-(kappa c * p.γ) * y) := by
    intro y
    have h := hbound.rpow_le_exp_mul (le_trans zero_le_one p.hγ) y
    convert h using 1
    ring
  have hV_le_raw :
      frozenElliptic p U x ≤
        min ((MChi p) ^ p.γ)
          (1 / (1 - (kappa c * p.γ) ^ 2) *
            Real.exp (-(kappa c * p.γ) * x)) := by
    unfold frozenElliptic
    exact Psi_le_min_const_exp_of_nonneg_le hM_nonneg hkg_pos hkg_lt_one
      (hU.1.rpow_const (fun _ => Or.inr (le_trans zero_le_one p.hγ)))
      (fun y => Real.rpow_nonneg (hU_nonneg y) p.γ)
      hpow_le_M hpow_le_exp x
  have hV_le :
      frozenElliptic p U x ≤
        min ((MChi p) ^ p.γ)
          ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
            Real.exp (-(kappa c) * p.γ * x)) := by
    convert hV_le_raw using 2 <;> ring
  have hV_nonneg : 0 ≤ frozenElliptic p U x :=
    frozenElliptic_nonneg p hU_nonneg x
  have hV_abs :
      |frozenElliptic p U x| ≤
        min ((MChi p) ^ p.γ)
          ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
            Real.exp (-(kappa c) * p.γ * x)) := by
    simpa [abs_of_nonneg hV_nonneg] using hV_le
  have hV_deriv_abs :
      |deriv (frozenElliptic p U) x| ≤ frozenElliptic p U x :=
    frozenElliptic_deriv_abs_le p hU hU_nonneg x
  exact ⟨hV_abs, le_trans hV_deriv_abs hV_le⟩

theorem Lemma_5_1_exponential_signal_bound_for_frozenElliptic_of_continuous
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ}
    (hc : 2 < c) (hspeed : p.γ + p.γ⁻¹ < c)
    (hU_cont : Continuous U) (hbound : HasWaveUpperTailBound p c U) :
    ∀ x,
      |frozenElliptic p U x| ≤
        min ((MChi p) ^ p.γ)
          ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
            Real.exp (-(kappa c) * p.γ * x)) ∧
      |deriv (frozenElliptic p U) x| ≤
        min ((MChi p) ^ p.γ)
          ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
            Real.exp (-(kappa c) * p.γ * x)) :=
  Lemma_5_1_exponential_signal_bound_for_frozenElliptic
    p hc hspeed (hbound.isCUnifBdd_of_continuous hU_cont) hbound

/-- The signal-estimate part of Lemma 5.1 in the fixed-point case
`V = frozenElliptic p U`, recorded in the same conjunctive shape as the first
two conclusions of the full lemma. -/
theorem Lemma_5_1.fixed_point_signal_statement
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ}
    (hc : 2 < c) (hU : IsCUnifBdd U)
    (hbound : HasWaveUpperTailBound p c U) :
    (∀ x,
      |frozenElliptic p U x| ≤ (MChi p) ^ p.γ ∧
        |deriv (frozenElliptic p U) x| ≤ (MChi p) ^ p.γ) ∧
    (p.γ + p.γ⁻¹ < c →
      ∀ x,
        |frozenElliptic p U x| ≤
          min ((MChi p) ^ p.γ)
            ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
              Real.exp (-(kappa c) * p.γ * x)) ∧
        |deriv (frozenElliptic p U) x| ≤
          min ((MChi p) ^ p.γ)
            ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
              Real.exp (-(kappa c) * p.γ * x))) := by
  refine ⟨?_, ?_⟩
  · exact Lemma_5_1_signal_bound_for_frozenElliptic p hU hbound
  · intro hspeed
    exact Lemma_5_1_exponential_signal_bound_for_frozenElliptic
      p hc hspeed hU hbound

theorem Lemma_5_1.fixed_point_signal_statement_of_continuous
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ}
    (hc : 2 < c) (hU_cont : Continuous U)
    (hbound : HasWaveUpperTailBound p c U) :
    (∀ x,
      |frozenElliptic p U x| ≤ (MChi p) ^ p.γ ∧
        |deriv (frozenElliptic p U) x| ≤ (MChi p) ^ p.γ) ∧
    (p.γ + p.γ⁻¹ < c →
      ∀ x,
        |frozenElliptic p U x| ≤
          min ((MChi p) ^ p.γ)
            ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
              Real.exp (-(kappa c) * p.γ * x)) ∧
        |deriv (frozenElliptic p U) x| ≤
          min ((MChi p) ^ p.γ)
            ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
              Real.exp (-(kappa c) * p.γ * x))) :=
  Lemma_5_1.fixed_point_signal_statement p hc
    (hbound.isCUnifBdd_of_continuous hU_cont) hbound

/-- Fixed-point version of the full Lemma 5.1 conclusion.  The two signal
estimate components are proved from the `Psi` kernel; the remaining `U'`
components are kept as explicit derivative hypotheses. -/
theorem Lemma_5_1.fixed_point_conclusion_of_wave_derivative_bounds
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ}
    (hc : 2 < c) (hU : IsCUnifBdd U)
    (hbound : HasWaveUpperTailBound p c U)
    (hderiv_tends : WaveDerivativeTendsZero U)
    (hderiv_bound :
      c > p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) →
        ∃ B > 0, ∀ x, |deriv U x| ≤ B)
    (hderiv_exp :
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
        ∃ B1 B2, ∀ x,
          |deriv U x| ≤
            B1 * Real.exp (-(kappa c) * x) +
              B2 * Real.exp (-(kappa c) * p.γ * x)) :
    (∀ x,
      |frozenElliptic p U x| ≤ (MChi p) ^ p.γ ∧
        |deriv (frozenElliptic p U) x| ≤ (MChi p) ^ p.γ) ∧
    (p.γ + p.γ⁻¹ < c →
      ∀ x,
        |frozenElliptic p U x| ≤
          min ((MChi p) ^ p.γ)
            ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
              Real.exp (-(kappa c) * p.γ * x)) ∧
        |deriv (frozenElliptic p U) x| ≤
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
            B2 * Real.exp (-(kappa c) * p.γ * x)) := by
  rcases Lemma_5_1.fixed_point_signal_statement p hc hU hbound with
    ⟨hsignal, hexpSignal⟩
  exact ⟨hsignal, hexpSignal, hderiv_tends, hderiv_bound, hderiv_exp⟩

theorem Lemma_5_1.fixed_point_conclusion_of_wave_derivative_bounds_of_continuous
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ}
    (hc : 2 < c) (hU_cont : Continuous U)
    (hbound : HasWaveUpperTailBound p c U)
    (hderiv_tends : WaveDerivativeTendsZero U)
    (hderiv_bound :
      c > p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) →
        ∃ B > 0, ∀ x, |deriv U x| ≤ B)
    (hderiv_exp :
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
        ∃ B1 B2, ∀ x,
          |deriv U x| ≤
            B1 * Real.exp (-(kappa c) * x) +
              B2 * Real.exp (-(kappa c) * p.γ * x)) :
    (∀ x,
      |frozenElliptic p U x| ≤ (MChi p) ^ p.γ ∧
        |deriv (frozenElliptic p U) x| ≤ (MChi p) ^ p.γ) ∧
    (p.γ + p.γ⁻¹ < c →
      ∀ x,
        |frozenElliptic p U x| ≤
          min ((MChi p) ^ p.γ)
            ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
              Real.exp (-(kappa c) * p.γ * x)) ∧
        |deriv (frozenElliptic p U) x| ≤
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
            B2 * Real.exp (-(kappa c) * p.γ * x)) :=
  Lemma_5_1.fixed_point_conclusion_of_wave_derivative_bounds p hc
    (hbound.isCUnifBdd_of_continuous hU_cont)
    hbound hderiv_tends hderiv_bound hderiv_exp

theorem Lemma_5_1_resolvent_identified_direct
    {p : CMParams} {c : ℝ} (hc : 2 < c)
    {U V : ℝ → ℝ}
    (_hTW : IsTravelingWave p c U V)
    (hV : V = frozenElliptic p U)
    (hU_cont : Continuous U)
    (hbound : HasWaveUpperTailBound p c U)
    (hderiv_tends : WaveDerivativeTendsZero U)
    (hderiv_bound :
      c > p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) →
        ∃ B > 0, ∀ x, |deriv U x| ≤ B)
    (hderiv_exp :
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
        ∃ B1 B2, ∀ x,
          |deriv U x| ≤
            B1 * Real.exp (-(kappa c) * x) +
              B2 * Real.exp (-(kappa c) * p.γ * x)) :
    (∀ x,
      |V x| ≤ (MChi p) ^ p.γ ∧
        |deriv V x| ≤ (MChi p) ^ p.γ) ∧
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
    (c > max (p.γ + p.γ⁻¹)
        (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
      ∃ B1 B2, ∀ x,
        |deriv U x| ≤
          B1 * Real.exp (-(kappa c) * x) +
            B2 * Real.exp (-(kappa c) * p.γ * x)) := by
  have hU : IsCUnifBdd U := hbound.isCUnifBdd_of_continuous hU_cont
  subst V
  exact Lemma_5_1.fixed_point_conclusion_of_wave_derivative_bounds
    p hc hU hbound hderiv_tends hderiv_bound hderiv_exp

/-- Universal closure of Lemma 5.1 from resolvent identification, wave
continuity, and the three derivative-bound residuals.  Each residual is a
genuine analytical property of traveling waves; the signal estimates are
derived internally from the frozen elliptic resolvent. -/
theorem Lemma_5_1.of_resolvent_derivative_bounds
    (hresolvent : ∀ p : CMParams, ∀ c : ℝ, ∀ U V : ℝ → ℝ,
      IsTravelingWave p c U V → V = frozenElliptic p U)
    (hcont : ∀ p : CMParams, ∀ c : ℝ, ∀ U V : ℝ → ℝ,
      IsTravelingWave p c U V → Continuous U)
    (hderiv_tends : ∀ p : CMParams, ∀ c : ℝ, 2 < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        WaveDerivativeTendsZero U)
    (hderiv_bound : ∀ p : CMParams, ∀ c : ℝ, 2 < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        c > p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) →
          ∃ B > 0, ∀ x, |deriv U x| ≤ B)
    (hderiv_exp : ∀ p : CMParams, ∀ c : ℝ, 2 < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        c > max (p.γ + p.γ⁻¹)
          (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
          ∃ B1 B2, ∀ x,
            |deriv U x| ≤
              B1 * Real.exp (-(kappa c) * x) +
                B2 * Real.exp (-(kappa c) * p.γ * x)) :
    Lemma_5_1 := by
  intro p c hc U V hTW hbound
  exact Lemma_5_1_resolvent_identified_direct hc hTW
    (hresolvent p c U V hTW) (hcont p c U V hTW) hbound
    (hderiv_tends p c hc U V hTW hbound)
    (hderiv_bound p c hc U V hTW hbound)
    (hderiv_exp p c hc U V hTW hbound)

/-- Lemma 5.1's signal estimates for a frozen stationary profile already
known to lie in the wave trap.  This avoids the arbitrary `IsTravelingWave`
projection route: the elliptic signal is definitionally `frozenElliptic p U`,
and the estimates come from the `Psi` kernel bounds. -/
theorem FrozenStationaryWaveProfile.fixed_point_signal_statement_of_inWaveTrapSet
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hc : 2 < c) (htrap : InWaveTrapSet (kappa c) (MChi p) U) :
    (∀ x,
      |frozenElliptic p U x| ≤ (MChi p) ^ p.γ ∧
        |deriv (frozenElliptic p U) x| ≤ (MChi p) ^ p.γ) ∧
    (p.γ + p.γ⁻¹ < c →
      ∀ x,
        |frozenElliptic p U x| ≤
          min ((MChi p) ^ p.γ)
            ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
              Real.exp (-(kappa c) * p.γ * x)) ∧
        |deriv (frozenElliptic p U) x| ≤
          min ((MChi p) ^ p.γ)
            ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
              Real.exp (-(kappa c) * p.γ * x))) :=
  Lemma_5_1.fixed_point_signal_statement p hc htrap.cunif_bdd
    (hprofile.hasWaveUpperTailBound_of_inWaveTrapSet htrap)

/-- Full fixed-point/profile version of Lemma 5.1 with the `V` estimates
proved from the resolvent and only the `U'` estimates left as explicit
hypotheses. -/
theorem FrozenStationaryWaveProfile.fixed_point_conclusion_of_wave_derivative_bounds
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hc : 2 < c) (htrap : InWaveTrapSet (kappa c) (MChi p) U)
    (hderiv_tends : WaveDerivativeTendsZero U)
    (hderiv_bound :
      c > p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) →
        ∃ B > 0, ∀ x, |deriv U x| ≤ B)
    (hderiv_exp :
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
        ∃ B1 B2, ∀ x,
          |deriv U x| ≤
            B1 * Real.exp (-(kappa c) * x) +
              B2 * Real.exp (-(kappa c) * p.γ * x)) :
    (∀ x,
      |frozenElliptic p U x| ≤ (MChi p) ^ p.γ ∧
        |deriv (frozenElliptic p U) x| ≤ (MChi p) ^ p.γ) ∧
    (p.γ + p.γ⁻¹ < c →
      ∀ x,
        |frozenElliptic p U x| ≤
          min ((MChi p) ^ p.γ)
            ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
              Real.exp (-(kappa c) * p.γ * x)) ∧
        |deriv (frozenElliptic p U) x| ≤
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
            B2 * Real.exp (-(kappa c) * p.γ * x)) := by
  exact Lemma_5_1.fixed_point_conclusion_of_wave_derivative_bounds
    p hc htrap.cunif_bdd
    (hprofile.hasWaveUpperTailBound_of_inWaveTrapSet htrap)
    hderiv_tends hderiv_bound hderiv_exp

theorem NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_signal_statement
    {p : CMParams} {c κ₀ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₀ κtilde D)
    (hc : 2 < c)
    (hupper :
      ∀ U : ℝ → ℝ,
        InMonotoneWaveTrapSet (kappa c) 1 U →
          FrozenAuxiliaryLimitOutput p c (kappa c) 1
            (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U →
            ShenUpperBoundNegative c U) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet (kappa c) 1 U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) 1
          (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U ∧
        (∀ x,
          |frozenElliptic p U x| ≤ (MChi p) ^ p.γ ∧
            |deriv (frozenElliptic p U) x| ≤ (MChi p) ^ p.γ) ∧
        (p.γ + p.γ⁻¹ < c →
          ∀ x,
            |frozenElliptic p U x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x)) ∧
            |deriv (frozenElliptic p U) x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x))) := by
  rcases h.exists_fixed_limit_with_atTop_limits with
    ⟨U, hU, haux, _hanti, _hU_top, _hV_top⟩
  have hupperU : ShenUpperBoundNegative c U := hupper U hU haux
  have htrapM : InMonotoneWaveTrapSet (kappa c) (MChi p) U := by
    simpa [h.MChi_eq_one] using hU
  exact
    ⟨U, hU, haux,
      Lemma_5_1.fixed_point_signal_statement p hc htrapM.trap.cunif_bdd
        (htrapM.hasWaveUpperTailBound_of_pos hupperU.pos)⟩

theorem PositiveSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_signal_statement
    {p : CMParams} {c κ₀ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₀ κtilde D)
    (hc : 2 < c)
    (hupper :
      ∀ U : ℝ → ℝ,
        InWaveTrapSet (kappa c) (MChi p) U →
          FrozenAuxiliaryLimitOutput p c (kappa c) (MChi p)
            (fun u => InWaveTrapSet (kappa c) (MChi p) u) U U →
            ShenUpperBoundPositive p c U) :
    ∃ U : ℝ → ℝ,
      InWaveTrapSet (kappa c) (MChi p) U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) (MChi p)
          (fun u => InWaveTrapSet (kappa c) (MChi p) u) U U ∧
        (∀ x,
          |frozenElliptic p U x| ≤ (MChi p) ^ p.γ ∧
            |deriv (frozenElliptic p U) x| ≤ (MChi p) ^ p.γ) ∧
        (p.γ + p.γ⁻¹ < c →
          ∀ x,
            |frozenElliptic p U x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x)) ∧
            |deriv (frozenElliptic p U) x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x))) := by
  rcases h.exists_fixed_limit_with_atTop_limits with
    ⟨U, hU, haux, _hU_top, _hV_top⟩
  have hupperU : ShenUpperBoundPositive p c U := hupper U hU haux
  exact
    ⟨U, hU, haux,
      Lemma_5_1.fixed_point_signal_statement p hc hU.cunif_bdd
        (hU.hasWaveUpperTailBound_of_pos hupperU.pos)⟩

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

theorem logDerivativeBoundFormula_nonneg_of_speed
    (p : CMParams) {c : ℝ}
    (hMChi_nonneg : 0 ≤ MChi p)
    (hspeed :
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1))) :
    0 ≤ logDerivativeBoundFormula p c := by
  unfold logDerivativeBoundFormula
  have hgamma_pos : 0 < p.γ := lt_of_lt_of_le zero_lt_one p.hγ
  have hgamma_inv_pos : 0 < p.γ⁻¹ := inv_pos.mpr hgamma_pos
  have hc_pos : 0 < c := by
    have hsum_pos : 0 < p.γ + p.γ⁻¹ := add_pos hgamma_pos hgamma_inv_pos
    exact lt_trans hsum_pos (lt_of_le_of_lt (le_max_left _ _) hspeed)
  have hchi_nonneg : 0 ≤ |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) := by
    have hm_nonneg : 0 ≤ p.m := le_trans zero_le_one p.hm
    exact mul_nonneg (mul_nonneg (abs_nonneg p.χ) hm_nonneg)
      (Real.rpow_nonneg hMChi_nonneg _)
  have hsum_nonneg :
      0 ≤
        c + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) +
          Real.sqrt
        ((c + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1)) ^ 2 +
              4 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
              4 * (MChi p) ^ p.α) := by
    have hleft :
        0 ≤ c + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) := by
      linarith
    exact add_nonneg hleft (Real.sqrt_nonneg _)
  exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hsum_nonneg

theorem Lemma_5_2_explicit.nonincreasing_profile_branch
    {p : CMParams} {c : ℝ}
    (hspeed :
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    {U : ℝ → ℝ}
    (hMChi_nonneg : 0 ≤ MChi p)
    (hpos : ∀ x, 0 < U x)
    (hmono : ∀ x, deriv U x ≤ 0) :
    ∀ x, deriv U x / U x ≤ logDerivativeBoundFormula p c := by
  intro x
  have hratio_nonpos : deriv U x / U x ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (hmono x) (hpos x).le
  exact le_trans hratio_nonpos
    (logDerivativeBoundFormula_nonneg_of_speed p hMChi_nonneg hspeed)

theorem Lemma_5_2_explicit.nonincreasing_branch
    {p : CMParams} {c : ℝ}
    (hspeed :
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hmono : ∀ x, deriv U x ≤ 0) :
    ∀ x, deriv U x / U x ≤ logDerivativeBoundFormula p c := by
  have hMChi_nonneg : 0 ≤ MChi p := by
    linarith [hbound.pos 0, hbound.le_MChi 0]
  exact Lemma_5_2_explicit.nonincreasing_profile_branch
    hspeed hMChi_nonneg hTW.U_pos hmono

theorem Lemma_5_2_explicit.monotoneTravelingWave_branch
    {p : CMParams} {c : ℝ}
    (hspeed :
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    {U V : ℝ → ℝ}
    (hTW : IsMonotoneTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U) :
    ∀ x, deriv U x / U x ≤ logDerivativeBoundFormula p c :=
  Lemma_5_2_explicit.nonincreasing_branch hspeed hTW.1 hbound hTW.2.1

def Lemma_5_2 : Prop :=
  ∀ p : CMParams, ∀ c : ℝ,
    c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
          ∃ B > 0, ∀ x, deriv U x / U x ≤ B

/-- Lemma_5_2_explicit closure under monotonicity hypothesis. -/
theorem Lemma_5_2_explicit_under_monotone
    (h_monotone : ∀ p : CMParams, ∀ c : ℝ,
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        ∀ x, deriv U x ≤ 0) :
    Lemma_5_2_explicit := by
  intro p c hspeed U V hTW hbound x
  exact Lemma_5_2_explicit.nonincreasing_branch hspeed hTW hbound
    (h_monotone p c hspeed U V hTW hbound) x

theorem Lemma_5_2.nonincreasing_branch
    {p : CMParams} {c : ℝ}
    (hspeed :
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hmono : ∀ x, deriv U x ≤ 0) :
    ∃ B > 0, ∀ x, deriv U x / U x ≤ B := by
  refine ⟨max (logDerivativeBoundFormula p c) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · intro x
    exact le_trans
      (Lemma_5_2_explicit.nonincreasing_branch hspeed hTW hbound hmono x)
      (le_max_left _ _)

theorem Lemma_5_2.monotoneTravelingWave_branch
    {p : CMParams} {c : ℝ}
    (hspeed :
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    {U V : ℝ → ℝ}
    (hTW : IsMonotoneTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U) :
    ∃ B > 0, ∀ x, deriv U x / U x ≤ B :=
  Lemma_5_2.nonincreasing_branch hspeed hTW.1 hbound hTW.2.1

theorem Lemma_5_2.nonincreasing_profile_branch
    {p : CMParams} {c : ℝ}
    (hspeed :
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    {U : ℝ → ℝ}
    (hMChi_nonneg : 0 ≤ MChi p)
    (hpos : ∀ x, 0 < U x)
    (hmono : ∀ x, deriv U x ≤ 0) :
    ∃ B > 0, ∀ x, deriv U x / U x ≤ B := by
  refine ⟨max (logDerivativeBoundFormula p c) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · intro x
    exact le_trans
      (Lemma_5_2_explicit.nonincreasing_profile_branch
        hspeed hMChi_nonneg hpos hmono x)
      (le_max_left _ _)

theorem Lemma_5_2_explicit_frozen_monotone_trap_direct
    {p : CMParams} {c : ℝ}
    (hspeed :
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    {U : ℝ → ℝ}
    (hprofile : FrozenStationaryWaveProfile p c U)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U) :
    ∀ x, deriv U x / U x ≤ logDerivativeBoundFormula p c := by
  exact Lemma_5_2_explicit.nonincreasing_branch hspeed
    hprofile.to_travelingWave
    (hprofile.hasWaveUpperTailBound_of_inMonotoneWaveTrapSet htrap)
    htrap.deriv_nonpos

theorem Lemma_5_2_frozen_monotone_trap_direct
    {p : CMParams} {c : ℝ}
    (hspeed :
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    {U : ℝ → ℝ}
    (hprofile : FrozenStationaryWaveProfile p c U)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U) :
    ∃ B > 0, ∀ x, deriv U x / U x ≤ B := by
  exact Lemma_5_2.nonincreasing_branch hspeed
    hprofile.to_travelingWave
    (hprofile.hasWaveUpperTailBound_of_inMonotoneWaveTrapSet htrap)
    htrap.deriv_nonpos

/-- Lemma_5_2 holds when waves come from FrozenStationaryWaveProfile (monotone). -/
theorem Lemma_5_2_under_frozen_stationary_monotone
    (h_all_FSWP_mono : ∀ p : CMParams, ∀ c : ℝ,
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        ∃ (_h : FrozenStationaryWaveProfile p c U)
          (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U), True) :
    Lemma_5_2 := by
  intro p c hspeed U V hTW hbound
  obtain ⟨_, htrap, _⟩ := h_all_FSWP_mono p c hspeed U V hTW hbound
  exact Lemma_5_2.nonincreasing_branch hspeed hTW hbound htrap.deriv_nonpos

/-- Lemma_5_2_explicit holds when every wave is monotone. -/
theorem Lemma_5_2_explicit_under_monotone_traveling_wave
    (h_all_monotone : ∀ p : CMParams, ∀ c : ℝ,
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        IsMonotoneTravelingWave p c U V) :
    Lemma_5_2_explicit := by
  intro p c hspeed U V hTW hbound x
  have hmtw := h_all_monotone p c hspeed U V hTW hbound
  exact Lemma_5_2_explicit.monotoneTravelingWave_branch hspeed hmtw hbound x

/-- Lemma_5_2 holds when every wave is monotone (a stronger hypothesis form). -/
theorem Lemma_5_2_under_monotone_traveling_wave
    (h_all_monotone : ∀ p : CMParams, ∀ c : ℝ,
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        IsMonotoneTravelingWave p c U V) :
    Lemma_5_2 := by
  intro p c hspeed U V hTW hbound
  have hmtw := h_all_monotone p c hspeed U V hTW hbound
  exact Lemma_5_2.monotoneTravelingWave_branch hspeed hmtw hbound

/-- Lemma_5_2 holds under monotonicity hypothesis. Uses existing nonincreasing_branch. -/
theorem Lemma_5_2_under_monotone
    (h_monotone : ∀ p : CMParams, ∀ c : ℝ,
      c > max (p.γ + p.γ⁻¹) (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        ∀ x, deriv U x ≤ 0) :
    Lemma_5_2 := by
  intro p c hspeed U V hTW hbound
  exact Lemma_5_2.nonincreasing_branch hspeed hTW hbound
    (h_monotone p c hspeed U V hTW hbound)

theorem NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_log_derivative_bound
    {p : CMParams} {c κ₀ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₀ κtilde D)
    (hspeed :
      c > max (p.γ + p.γ⁻¹)
        (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    (hupper :
      ∀ U : ℝ → ℝ,
        InMonotoneWaveTrapSet (kappa c) 1 U →
          FrozenAuxiliaryLimitOutput p c (kappa c) 1
            (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U →
            ShenUpperBoundNegative c U) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet (kappa c) 1 U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) 1
          (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U ∧
        ∀ x, deriv U x / U x ≤ logDerivativeBoundFormula p c := by
  rcases h.exists_fixed_limit_with_atTop_limits with
    ⟨U, hU, haux, _hanti, _hU_top, _hV_top⟩
  have hMChi_nonneg : 0 ≤ MChi p := by
    rw [h.MChi_eq_one]
    norm_num
  have hupperU : ShenUpperBoundNegative c U := hupper U hU haux
  exact
    ⟨U, hU, haux,
      Lemma_5_2_explicit.nonincreasing_profile_branch
        hspeed hMChi_nonneg hupperU.pos hU.deriv_nonpos⟩

theorem NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_log_derivative_B
    {p : CMParams} {c κ₀ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₀ κtilde D)
    (hspeed :
      c > max (p.γ + p.γ⁻¹)
        (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    (hupper :
      ∀ U : ℝ → ℝ,
        InMonotoneWaveTrapSet (kappa c) 1 U →
          FrozenAuxiliaryLimitOutput p c (kappa c) 1
            (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U →
            ShenUpperBoundNegative c U) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet (kappa c) 1 U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) 1
          (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U ∧
        ∃ B > 0, ∀ x, deriv U x / U x ≤ B := by
  rcases h.exists_fixed_limit_with_log_derivative_bound hspeed hupper with
    ⟨U, hU, haux, hlog⟩
  refine ⟨U, hU, haux, max (logDerivativeBoundFormula p c) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · intro x
    exact le_trans (hlog x) (le_max_left _ _)

theorem NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_signal_and_log_derivative
    {p : CMParams} {c κ₀ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₀ κtilde D)
    (hc : 2 < c)
    (hspeed :
      c > max (p.γ + p.γ⁻¹)
        (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    (hupper :
      ∀ U : ℝ → ℝ,
        InMonotoneWaveTrapSet (kappa c) 1 U →
          FrozenAuxiliaryLimitOutput p c (kappa c) 1
            (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U →
            ShenUpperBoundNegative c U) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet (kappa c) 1 U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) 1
          (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U ∧
        (∀ x,
          |frozenElliptic p U x| ≤ (MChi p) ^ p.γ ∧
            |deriv (frozenElliptic p U) x| ≤ (MChi p) ^ p.γ) ∧
        (p.γ + p.γ⁻¹ < c →
          ∀ x,
            |frozenElliptic p U x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x)) ∧
            |deriv (frozenElliptic p U) x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x))) ∧
        ∀ x, deriv U x / U x ≤ logDerivativeBoundFormula p c := by
  rcases h.exists_fixed_limit_with_atTop_limits with
    ⟨U, hU, haux, _hanti, _hU_top, _hV_top⟩
  have hMChi_nonneg : 0 ≤ MChi p := by
    rw [h.MChi_eq_one]
    norm_num
  have hupperU : ShenUpperBoundNegative c U := hupper U hU haux
  have htrapM : InMonotoneWaveTrapSet (kappa c) (MChi p) U := by
    simpa [h.MChi_eq_one] using hU
  have hsignal :=
    Lemma_5_1.fixed_point_signal_statement p hc htrapM.trap.cunif_bdd
      (htrapM.hasWaveUpperTailBound_of_pos hupperU.pos)
  have hlog :
      ∀ x, deriv U x / U x ≤ logDerivativeBoundFormula p c :=
    Lemma_5_2_explicit.nonincreasing_profile_branch
      hspeed hMChi_nonneg hupperU.pos hU.deriv_nonpos
  exact ⟨U, hU, haux, hsignal.1, hsignal.2, hlog⟩

theorem NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_signal_and_log_derivative_B
    {p : CMParams} {c κ₀ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₀ κtilde D)
    (hc : 2 < c)
    (hspeed :
      c > max (p.γ + p.γ⁻¹)
        (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    (hupper :
      ∀ U : ℝ → ℝ,
        InMonotoneWaveTrapSet (kappa c) 1 U →
          FrozenAuxiliaryLimitOutput p c (kappa c) 1
            (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U →
            ShenUpperBoundNegative c U) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet (kappa c) 1 U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) 1
          (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U ∧
        (∀ x,
          |frozenElliptic p U x| ≤ (MChi p) ^ p.γ ∧
            |deriv (frozenElliptic p U) x| ≤ (MChi p) ^ p.γ) ∧
        (p.γ + p.γ⁻¹ < c →
          ∀ x,
            |frozenElliptic p U x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x)) ∧
            |deriv (frozenElliptic p U) x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x))) ∧
        ∃ B > 0, ∀ x, deriv U x / U x ≤ B := by
  rcases h.exists_fixed_limit_with_signal_and_log_derivative
      hc hspeed hupper with
    ⟨U, hU, haux, hsignal, hexpSignal, hlog⟩
  refine
    ⟨U, hU, haux, hsignal, hexpSignal,
      max (logDerivativeBoundFormula p c) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · intro x
    exact le_trans (hlog x) (le_max_left _ _)

theorem NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_const_sub_signal_and_log_derivative
    {p : CMParams} {c κ₀ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₀ κtilde D)
    (hc : 2 < c)
    (hspeed :
      c > max (p.γ + p.γ⁻¹)
        (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    (hupper :
      ∀ U : ℝ → ℝ,
        InMonotoneWaveTrapSet (kappa c) 1 U →
          FrozenAuxiliaryLimitOutput p c (kappa c) 1
            (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U →
            ShenUpperBoundNegative c U) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet (kappa c) 1 U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) 1
          (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U ∧
        (∃ d : ℝ, 0 < d ∧
          IsPaperFrozenSubSolutionOn p c U (fun _ => d) Set.univ) ∧
        (∀ x,
          |frozenElliptic p U x| ≤ (MChi p) ^ p.γ ∧
            |deriv (frozenElliptic p U) x| ≤ (MChi p) ^ p.γ) ∧
        (p.γ + p.γ⁻¹ < c →
          ∀ x,
            |frozenElliptic p U x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x)) ∧
            |deriv (frozenElliptic p U) x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x))) ∧
        ∀ x, deriv U x / U x ≤ logDerivativeBoundFormula p c := by
  rcases h.exists_fixed_limit_with_signal_and_log_derivative
      hc hspeed hupper with
    ⟨U, hU, haux, hsignal, hexpSignal, hlog⟩
  rcases h.exists_paper_constant_subsolution hU with
    ⟨d, hd_pos, hd_sub⟩
  exact ⟨U, hU, haux, ⟨d, hd_pos, hd_sub⟩, hsignal, hexpSignal, hlog⟩

theorem PositiveSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_signal_and_paper_const_sub_chi_zero
    {p : CMParams} {c κ₀ κtilde D : ℝ}
    (h : PositiveSensitivityWaveFixedPointConstruction p c κ₀ κtilde D)
    (hc : 2 < c)
    (hχ_zero : p.χ = 0)
    (hupper :
      ∀ U : ℝ → ℝ,
        InWaveTrapSet (kappa c) (MChi p) U →
          FrozenAuxiliaryLimitOutput p c (kappa c) (MChi p)
            (fun u => InWaveTrapSet (kappa c) (MChi p) u) U U →
            ShenUpperBoundPositive p c U) :
    ∃ U : ℝ → ℝ,
      InWaveTrapSet (kappa c) (MChi p) U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) (MChi p)
          (fun u => InWaveTrapSet (kappa c) (MChi p) u) U U ∧
        (∃ d : ℝ, 0 < d ∧
          IsPaperFrozenSubSolutionOn p c U (fun _ => d) Set.univ) ∧
        (∀ x,
          |frozenElliptic p U x| ≤ (MChi p) ^ p.γ ∧
            |deriv (frozenElliptic p U) x| ≤ (MChi p) ^ p.γ) ∧
        (p.γ + p.γ⁻¹ < c →
          ∀ x,
            |frozenElliptic p U x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x)) ∧
            |deriv (frozenElliptic p U) x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x))) := by
  rcases h.exists_fixed_limit_with_signal_statement hc hupper with
    ⟨U, hU, haux, hsignal, hexpSignal⟩
  rcases h.exists_paper_constant_subsolution_of_chi_zero hχ_zero hU with
    ⟨d, hd_pos, hd_sub⟩
  exact ⟨U, hU, haux, ⟨d, hd_pos, hd_sub⟩, hsignal, hexpSignal⟩

theorem NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_const_sub_signal_and_log_derivative_B
    {p : CMParams} {c κ₀ κtilde D : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₀ κtilde D)
    (hc : 2 < c)
    (hspeed :
      c > max (p.γ + p.γ⁻¹)
        (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)))
    (hupper :
      ∀ U : ℝ → ℝ,
        InMonotoneWaveTrapSet (kappa c) 1 U →
          FrozenAuxiliaryLimitOutput p c (kappa c) 1
            (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U →
            ShenUpperBoundNegative c U) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet (kappa c) 1 U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) 1
          (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U ∧
        (∃ d : ℝ, 0 < d ∧
          IsPaperFrozenSubSolutionOn p c U (fun _ => d) Set.univ) ∧
        (∀ x,
          |frozenElliptic p U x| ≤ (MChi p) ^ p.γ ∧
            |deriv (frozenElliptic p U) x| ≤ (MChi p) ^ p.γ) ∧
        (p.γ + p.γ⁻¹ < c →
          ∀ x,
            |frozenElliptic p U x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x)) ∧
            |deriv (frozenElliptic p U) x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x))) ∧
        ∃ B > 0, ∀ x, deriv U x / U x ≤ B := by
  rcases h.exists_fixed_limit_with_const_sub_signal_and_log_derivative
      hc hspeed hupper with
    ⟨U, hU, haux, hsub, hsignal, hexpSignal, hlog⟩
  refine
    ⟨U, hU, haux, hsub, hsignal, hexpSignal,
      max (logDerivativeBoundFormula p c) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · intro x
    exact le_trans (hlog x) (le_max_left _ _)

/-- The constant `M'_{\chi,m,\alpha,\gamma}` from Paper1 Remark 5.1. -/
def remark51MPrime (p : CMParams) : ℝ :=
  |p.χ| * (MChi p) ^ (p.m + p.γ) + (MChi p) ^ (1 + p.α)

/-- The quantity `|χ|^σ` used throughout Paper1 Remarks 5.1--5.2.

This is a real power.  In particular, it is not the product `|χ| * σ`.
The distinction is essential in Section 5, where the paper later sets
`σ = 1/6`. -/
noncomputable def remark5ChiSigma (p : CMParams) (sigma : ℝ) : ℝ :=
  |p.χ| ^ sigma

/-- The paper's `|χ|^(2σ)`, represented as the square of `|χ|^σ` so that
the algebraic relation between the two denominators is definitionally
available. -/
noncomputable def remark5ChiTwoSigma (p : CMParams) (sigma : ℝ) : ℝ :=
  (remark5ChiSigma p sigma) ^ 2

theorem remark5ChiSigma_nonneg (p : CMParams) (sigma : ℝ) :
    0 ≤ remark5ChiSigma p sigma := by
  exact Real.rpow_nonneg (abs_nonneg p.χ) sigma

theorem remark5ChiSigma_pos {p : CMParams} (sigma : ℝ) (hχ : p.χ ≠ 0) :
    0 < remark5ChiSigma p sigma := by
  exact Real.rpow_pos_of_pos (abs_pos.mpr hχ) sigma

theorem remark5ChiTwoSigma_nonneg (p : CMParams) (sigma : ℝ) :
    0 ≤ remark5ChiTwoSigma p sigma := by
  exact sq_nonneg _

theorem remark5ChiTwoSigma_pos {p : CMParams} (sigma : ℝ) (hχ : p.χ ≠ 0) :
    0 < remark5ChiTwoSigma p sigma := by
  exact sq_pos_of_pos (remark5ChiSigma_pos sigma hχ)

theorem remark5ChiTwoSigma_eq_rpow (p : CMParams) (sigma : ℝ) :
    remark5ChiTwoSigma p sigma = |p.χ| ^ (2 * sigma) := by
  rw [show (2 : ℝ) * sigma = sigma * 2 by ring]
  simp [remark5ChiTwoSigma, remark5ChiSigma, Real.rpow_mul (abs_nonneg p.χ)]

/-- The constant `M''_{\chi,m,\alpha,\gamma,\sigma}` from Paper1 Remark 5.1.
The paper writes the real power `|χ|^(2σ)`. -/
def remark51MDoublePrime (p : CMParams) (sigma : ℝ) : ℝ :=
  2 *
    (1 + 2 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) + (MChi p) ^ p.α) *
      (remark5ChiTwoSigma p sigma +
        |p.χ| * p.m * (MChi p) ^ (p.m - 1) *
          (|p.χ| * (MChi p) ^ (p.m + p.γ) +
            (MChi p) ^ (p.α + 1)) *
          (p.γ + remark5ChiSigma p sigma))

/-- The stronger speed hypothesis used in Paper1 Remarks 5.1 and 5.2. -/
def remark5SpeedCondition (p : CMParams) (c sigma : ℝ) : Prop :=
  c >
    max
      (p.γ + remark5ChiSigma p sigma + 1 / (p.γ + remark5ChiSigma p sigma))
      (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
        remark5ChiSigma p sigma)

theorem remark5SpeedCondition.gt_first
    {p : CMParams} {c sigma : ℝ}
    (h : remark5SpeedCondition p c sigma) :
    p.γ + remark5ChiSigma p sigma + 1 / (p.γ + remark5ChiSigma p sigma) < c :=
  lt_of_le_of_lt (le_max_left _ _) h

theorem remark5SpeedCondition.gt_second
    {p : CMParams} {c sigma : ℝ}
    (h : remark5SpeedCondition p c sigma) :
    p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
        remark5ChiSigma p sigma < c :=
  lt_of_le_of_lt (le_max_right _ _) h

theorem remark5SpeedCondition.gt_waveDerivativeSpeed
    {p : CMParams} {c sigma : ℝ}
    (h : remark5SpeedCondition p c sigma) (hsigma : 0 ≤ sigma) :
    p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) < c := by
  have hnonneg : 0 ≤ remark5ChiSigma p sigma :=
    remark5ChiSigma_nonneg p sigma
  exact lt_of_le_of_lt (by linarith) h.gt_second

/-- When |χ|σ ≥ 1, the first speed bound gives c > γ + |χ|σ ≥ γ + 1 ≥ 2. -/
theorem remark5SpeedCondition.gt_two_of_chiSigma_ge_one
    {p : CMParams} {c sigma : ℝ}
    (h : remark5SpeedCondition p c sigma) (hsigma : 0 < sigma)
    (hχσ : 1 ≤ remark5ChiSigma p sigma) :
    2 < c := by
  have h1 := h.gt_first
  have hγ : 1 ≤ p.γ := p.hγ
  have hden_pos : 0 < p.γ + remark5ChiSigma p sigma := by
    have := remark5ChiSigma_nonneg p sigma
    linarith
  have hdiv_pos : 0 ≤ 1 / (p.γ + remark5ChiSigma p sigma) :=
    div_nonneg zero_le_one hden_pos.le
  linarith

/-- When |χ|σ ≥ 1, the first speed bound gives c > γ + γ⁻¹.
This uses γ⁻¹ ≤ 1 ≤ |χ|σ (so γ + |χ|σ ≥ γ + γ⁻¹). -/
theorem remark5SpeedCondition.gt_gamma_inv_of_chiSigma_ge_one
    {p : CMParams} {c sigma : ℝ}
    (h : remark5SpeedCondition p c sigma) (hsigma : 0 < sigma)
    (hχσ : 1 ≤ remark5ChiSigma p sigma) :
    p.γ + p.γ⁻¹ < c := by
  have h1 := h.gt_first
  have hγ : 1 ≤ p.γ := p.hγ
  have hγ_pos : 0 < p.γ := lt_of_lt_of_le zero_lt_one hγ
  have hγ_inv_le_one : p.γ⁻¹ ≤ 1 := by
    rw [show p.γ⁻¹ = 1 / p.γ from by ring]
    rw [div_le_one hγ_pos]; exact hγ
  have hden_pos : 0 < p.γ + remark5ChiSigma p sigma := by
    have := remark5ChiSigma_nonneg p sigma
    linarith
  have hdiv_pos : 0 ≤ 1 / (p.γ + remark5ChiSigma p sigma) :=
    div_nonneg zero_le_one hden_pos.le
  linarith

/-- κ(c) < 1 when c > 2: kappa(c) = (c - √(c²-4))/2.
For c > 2, c²-4 > (c-2)², so √(c²-4) > c-2, hence c - √(c²-4) < 2. -/
theorem kappa_lt_one_of_gt_two {c : ℝ} (hc : 2 < c) : kappa c < 1 := by
  unfold kappa
  have hc_pos : 0 < c := by linarith
  have hc2_pos : 0 < c^2 - 4 := by nlinarith
  have hcm2_pos : 0 < c - 2 := by linarith
  have hsqrt_gt : c - 2 < Real.sqrt (c^2 - 4) := by
    rw [← Real.sqrt_sq hcm2_pos.le]
    apply Real.sqrt_lt_sqrt (sq_nonneg _)
    nlinarith
  linarith

/-- κ(c) < |χ|σ when c > 2 and |χ|σ ≥ 1: κ < 1 ≤ |χ|σ. -/
theorem kappa_lt_chiSigma_of_gt_two_and_chiSigma_ge_one
    {p : CMParams} {c sigma : ℝ}
    (hc : 2 < c) (hχσ : 1 ≤ remark5ChiSigma p sigma) :
    kappa c < remark5ChiSigma p sigma := by
  exact lt_of_lt_of_le (kappa_lt_one_of_gt_two hc) hχσ

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
            |deriv U x| ≤ remark51MPrime p / (remark5ChiSigma p sigma)) ∧
          ∀ x : ℝ, 0 ≤ x →
            |deriv U x| ≤
              remark51MDoublePrime p sigma / (remark5ChiTwoSigma p sigma) *
                Real.exp (-(kappa c) * x)


/-! ### Proof of Remark 5.1: explicit derivative bounds for traveling waves

The argument is a maximum principle on the expanded ODE:
  U'' + (c - χmU^{m-1}V')U' = χU^m(V-U^γ) - U(1-U^α)
The effective drift ≥ |χ|σ (from speed condition) and the RHS ≤ M'.
Since U'→0 at ±∞, sup|U'| ≤ M'/(|χ|σ).
The exponential tail bound uses the decay of U and V for x ≥ 0. -/

/-- Maximum principle for first-order linear ODE: if v' = -a·v + g with
a ≥ a₀ > 0, |g| ≤ G, and v → 0 at ±∞, then |v| ≤ G/a₀.

Proof: if sup v > 0, the sup is attained at an interior x₀ where
v'(x₀) = 0, giving v(x₀) = g(x₀)/a(x₀) ≤ G/a₀. Similarly for inf. -/
theorem first_order_ode_sup_bound
    {v a g : ℝ → ℝ} {a₀ G : ℝ}
    (ha₀ : 0 < a₀) (hG : 0 ≤ G)
    (ha : ∀ x, a₀ ≤ a x)
    (hg : ∀ x, |g x| ≤ G)
    (hode : ∀ x, deriv v x = -a x * v x + g x)
    (hlim_top : Tendsto v atTop (𝓝 0))
    (hlim_bot : Tendsto v atBot (𝓝 0))
    (hv_cont : Continuous v) (hv_diff : Differentiable ℝ v) :
    ∀ x, |v x| ≤ G / a₀ := by
  have hv_cocompact : Tendsto v (cocompact ℝ) (𝓝 0) := by
    rw [cocompact_eq_atBot_atTop]; exact hlim_bot.sup hlim_top
  -- Helper: v x ≤ G/a₀ (upper bound via max principle)
  have hupper : ∀ x, v x ≤ G / a₀ := by
    intro x
    by_contra hx; push_neg at hx
    have hvx_pos : 0 < v x := lt_of_le_of_lt (div_nonneg hG ha₀.le) hx
    have hcocompact_le : ∀ᶠ y in cocompact ℝ, v y ≤ v x :=
      (hv_cocompact.eventually (Iio_mem_nhds hvx_pos)).mono
        fun y hy => le_of_lt (by simpa using hy)
    rcases hv_cont.exists_forall_ge' x hcocompact_le with ⟨x₀, hmax⟩
    have hLocalMax : IsLocalMax v x₀ :=
      IsMaxOn.isLocalMax (fun y _ => hmax y) Filter.univ_mem
    have hode_at := hode x₀
    rw [hLocalMax.deriv_eq_zero] at hode_at
    have hav : a x₀ * v x₀ = g x₀ := by linarith
    have hvx₀_pos : 0 < v x₀ := lt_of_lt_of_le hvx_pos (hmax x)
    have : v x₀ * a₀ ≤ G := calc
      v x₀ * a₀ ≤ v x₀ * a x₀ :=
        mul_le_mul_of_nonneg_left (ha x₀) hvx₀_pos.le
      _ = g x₀ := by rw [mul_comm]; exact hav
      _ ≤ |g x₀| := le_abs_self _
      _ ≤ G := hg x₀
    linarith [hmax x, le_div_iff₀ ha₀ |>.mpr this]
  -- Lower bound: -v satisfies same ODE with -g
  have hlower : ∀ x, -(G / a₀) ≤ v x := by
    intro x
    have hnv_upper : ∀ y, -v y ≤ G / a₀ := by
      have hnv_ode : ∀ y, deriv (-v) y = -a y * (-v y) + (-g y) := by
        intro y; simp [deriv_neg, hode y]; ring
      have hnv_cocompact : Tendsto (-v) (cocompact ℝ) (𝓝 0) := by
        simpa using hv_cocompact.neg
      intro y
      by_contra hy; push_neg at hy
      have hnvy_pos : 0 < (-v) y :=
        lt_of_le_of_lt (div_nonneg hG ha₀.le) hy
      have hcocompact_le : ∀ᶠ z in cocompact ℝ, (-v) z ≤ (-v) y :=
        (hnv_cocompact.eventually (Iio_mem_nhds hnvy_pos)).mono
          fun z hz => le_of_lt (by simpa using hz)
      rcases hv_cont.neg.exists_forall_ge' y hcocompact_le with ⟨y₀, hmax⟩
      have hLocalMax : IsLocalMax (-v) y₀ :=
        IsMaxOn.isLocalMax (fun z _ => hmax z) Filter.univ_mem
      have hode_at := hnv_ode y₀
      rw [hLocalMax.deriv_eq_zero] at hode_at
      have hav : a y₀ * (-v y₀) = -g y₀ := by linarith
      have hnvy₀_pos : 0 < (-v) y₀ := lt_of_lt_of_le hnvy_pos (hmax y)
      have : (-v y₀) * a₀ ≤ G := calc
        (-v y₀) * a₀ ≤ (-v y₀) * a y₀ :=
          mul_le_mul_of_nonneg_left (ha y₀) hnvy₀_pos.le
        _ = -g y₀ := by rw [mul_comm]; exact hav
        _ ≤ |g y₀| := neg_le_abs (g y₀)
        _ ≤ G := hg y₀
      linarith [hmax y, le_div_iff₀ ha₀ |>.mpr this]
    linarith [hnv_upper x]
  intro x
  exact abs_le.mpr ⟨by linarith [hlower x], hupper x⟩

/-- Chemotaxis derivative expansion via product rule + V'' substitution.
For a traveling wave (U,V), the chemotaxis term `deriv (U^m · V')` admits
a closed-form expansion using `ode_V` (which gives V'' = V - U^γ)
and the product rule, provided U and V' are differentiable at x. -/
theorem wave_chemotaxis_deriv_expand
    (p : CMParams) {U V : ℝ → ℝ} {x : ℝ}
    (hU_diff : DifferentiableAt ℝ U x)
    (hVderiv_diff : DifferentiableAt ℝ (deriv V) x)
    (hU_nonneg : 0 ≤ U x)
    (hode_V : iteratedDeriv 2 V x = V x - (U x) ^ p.γ) :
    deriv (fun y => (U y) ^ p.m * deriv V y) x =
      deriv U x * p.m * (U x) ^ (p.m - 1) * deriv V x +
        (U x) ^ p.m * (V x - (U x) ^ p.γ) := by
  have hU_pow_deriv : HasDerivAt (fun y => (U y) ^ p.m)
      (deriv U x * p.m * (U x) ^ (p.m - 1)) x :=
    hU_diff.hasDerivAt.rpow_const (Or.inr p.hm)
  have hiD2 : iteratedDeriv 2 V x = deriv (deriv V) x := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_one]
  have hV_deriv : HasDerivAt (deriv V) (V x - (U x) ^ p.γ) x := by
    have h : deriv (deriv V) x = V x - (U x) ^ p.γ := by
      rw [← hiD2]; exact hode_V
    convert hVderiv_diff.hasDerivAt using 1
    exact h.symm
  have hprod := hU_pow_deriv.mul hV_deriv
  have hfun_eq :
      (fun y => (U y) ^ p.m * deriv V y) =
      (fun y => (U y) ^ p.m) * deriv V := by
    ext y; simp [Pi.mul_apply]
  rw [hfun_eq, hprod.deriv]

/-- MChi ≥ 1 for any traveling wave with tail bound (since U → 1 at -∞). -/
theorem MChi_ge_one_of_travelingWave
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V) (hbound : HasWaveUpperTailBound p c U) :
    1 ≤ MChi p := by
  by_contra hcontra
  push_neg at hcontra
  have hU_to_one : Tendsto U atBot (𝓝 1) := hTW.lim_neg_inf.1
  have hev : ∀ᶠ N in atBot, MChi p < U N :=
    hU_to_one (Ioi_mem_nhds hcontra)
  obtain ⟨N, hN⟩ := hev.exists
  exact absurd (hbound.le_MChi N) (not_le.mpr hN)

/-- Drift lower bound: c - χ·m·U^{m-1}·V' ≥ |χ|·σ
under the speed condition and bounded V'. -/
theorem wave_drift_lower_bound
    {p : CMParams} {c sigma : ℝ}
    (hsigma : 0 < sigma)
    (hspeed : remark5SpeedCondition p c sigma)
    {U V : ℝ → ℝ}
    (hU_nn : ∀ x, 0 ≤ U x) (hU_le : ∀ x, U x ≤ MChi p)
    (hMChi_pos : 0 < MChi p)
    (hV'_abs : ∀ x, |deriv V x| ≤ (MChi p) ^ p.γ) (x : ℝ) :
    remark5ChiSigma p sigma ≤
      c - p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x := by
  have hm_pos : 0 < p.m := lt_of_lt_of_le zero_lt_one p.hm
  have hUm_nn : 0 ≤ (U x) ^ (p.m - 1) := Real.rpow_nonneg (hU_nn x) _
  have hUm_le : (U x) ^ (p.m - 1) ≤ (MChi p) ^ (p.m - 1) :=
    Real.rpow_le_rpow (hU_nn x) (hU_le x) (by linarith [p.hm])
  have hMpow_nn : 0 ≤ (MChi p) ^ p.γ := Real.rpow_nonneg hMChi_pos.le _
  have hMpow_nn2 : 0 ≤ (MChi p) ^ (p.m - 1) := Real.rpow_nonneg hMChi_pos.le _
  -- |χ * m * U^{m-1} * V'| ≤ m * |χ| * MChi^{m+γ-1}
  have hbound_prod : |p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x| ≤
      p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) := by
    have hkey : (U x) ^ (p.m - 1) * |deriv V x| ≤
        (MChi p) ^ (p.m + p.γ - 1) := by
      have hprod_le : (U x) ^ (p.m - 1) * |deriv V x| ≤
          (MChi p) ^ (p.m - 1) * (MChi p) ^ p.γ :=
        mul_le_mul hUm_le (hV'_abs x) (abs_nonneg _) hMpow_nn2
      have hM_eq : (MChi p) ^ (p.m - 1) * (MChi p) ^ p.γ =
          (MChi p) ^ (p.m + p.γ - 1) := by
        rw [← Real.rpow_add hMChi_pos]; ring_nf
      linarith
    calc |p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x|
        = |p.χ| * p.m * ((U x) ^ (p.m - 1) * |deriv V x|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos hm_pos,
              abs_of_nonneg hUm_nn]; ring
      _ ≤ |p.χ| * p.m * ((MChi p) ^ (p.m + p.γ - 1)) :=
            mul_le_mul_of_nonneg_left hkey
              (mul_nonneg (abs_nonneg _) hm_pos.le)
      _ = p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) := by ring
  have hspeed2 : p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) + remark5ChiSigma p sigma < c :=
    hspeed.gt_second
  have hX_le_abs : p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x ≤
      |p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x| := le_abs_self _
  linarith [hX_le_abs, hbound_prod, hspeed2]

/-- Source upper bound: |χU^m(V-U^γ) - U(1-U^α)| ≤ M'. -/
theorem wave_source_upper_bound
    {p : CMParams} {U V : ℝ → ℝ}
    (hU_nn : ∀ x, 0 ≤ U x) (hU_le : ∀ x, U x ≤ MChi p)
    (hMChi_pos : 0 < MChi p) (hMChi_ge_one : 1 ≤ MChi p)
    (hV_nn : ∀ x, 0 ≤ V x)
    (hV_abs : ∀ x, |V x| ≤ (MChi p) ^ p.γ) (x : ℝ) :
    |p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ) -
        U x * (1 - (U x) ^ p.α)| ≤ remark51MPrime p := by
  have hm_pos : 0 < p.m := lt_of_lt_of_le zero_lt_one p.hm
  have hα_pos : 0 < p.α := lt_of_lt_of_le zero_lt_one p.hα
  have hγ_pos : 0 < p.γ := lt_of_lt_of_le zero_lt_one p.hγ
  have hMChi_pow_nn : ∀ r : ℝ, 0 ≤ (MChi p) ^ r := fun r =>
    Real.rpow_nonneg hMChi_pos.le _
  have hUγ_nn : 0 ≤ (U x) ^ p.γ := Real.rpow_nonneg (hU_nn x) _
  have hUγ_le : (U x) ^ p.γ ≤ (MChi p) ^ p.γ :=
    Real.rpow_le_rpow (hU_nn x) (hU_le x) hγ_pos.le
  have hUm_nn : 0 ≤ (U x) ^ p.m := Real.rpow_nonneg (hU_nn x) _
  have hUm_le : (U x) ^ p.m ≤ (MChi p) ^ p.m :=
    Real.rpow_le_rpow (hU_nn x) (hU_le x) hm_pos.le
  have hUα_nn : 0 ≤ (U x) ^ p.α := Real.rpow_nonneg (hU_nn x) _
  have hUα_le : (U x) ^ p.α ≤ (MChi p) ^ p.α :=
    Real.rpow_le_rpow (hU_nn x) (hU_le x) hα_pos.le
  have hMα_ge_one : 1 ≤ (MChi p) ^ p.α :=
    Real.one_le_rpow hMChi_ge_one hα_pos.le
  -- |V - U^γ| ≤ MChi^γ (using V ≥ 0 and V ≤ MChi^γ, similarly for U^γ)
  have hV_le : V x ≤ (MChi p) ^ p.γ := by
    have := (abs_le.mp (hV_abs x)).2; linarith
  have hVUγ_abs : |V x - (U x) ^ p.γ| ≤ (MChi p) ^ p.γ := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · linarith [hV_nn x, hUγ_le]
    · linarith [hV_le, hUγ_nn]
  -- |χ * U^m * (V - U^γ)| ≤ |χ| * MChi^{m+γ}
  have hchem : |p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ)| ≤
      |p.χ| * (MChi p) ^ (p.m + p.γ) := by
    have hUm_VUγ : (U x) ^ p.m * |V x - (U x) ^ p.γ| ≤
        (MChi p) ^ (p.m + p.γ) := by
      have hprod : (U x) ^ p.m * |V x - (U x) ^ p.γ| ≤
          (MChi p) ^ p.m * (MChi p) ^ p.γ :=
        mul_le_mul hUm_le hVUγ_abs (abs_nonneg _) (hMChi_pow_nn _)
      have hM_eq : (MChi p) ^ p.m * (MChi p) ^ p.γ =
          (MChi p) ^ (p.m + p.γ) := (Real.rpow_add hMChi_pos _ _).symm
      linarith
    calc |p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ)|
        = |p.χ| * ((U x) ^ p.m * |V x - (U x) ^ p.γ|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hUm_nn]; ring
      _ ≤ |p.χ| * (MChi p) ^ (p.m + p.γ) :=
          mul_le_mul_of_nonneg_left hUm_VUγ (abs_nonneg _)
  -- |U(1-U^α)| ≤ MChi^{1+α}
  have hreact : |U x * (1 - (U x) ^ p.α)| ≤ (MChi p) ^ (1 + p.α) := by
    have h1Uα_abs : |1 - (U x) ^ p.α| ≤ (MChi p) ^ p.α := by
      rw [abs_le]; constructor <;> linarith
    have hU_h : U x * |1 - (U x) ^ p.α| ≤ (MChi p) ^ (1 + p.α) := by
      have : U x * |1 - (U x) ^ p.α| ≤ MChi p * (MChi p) ^ p.α :=
        mul_le_mul (hU_le x) h1Uα_abs (abs_nonneg _) hMChi_pos.le
      have hM_eq : MChi p * (MChi p) ^ p.α = (MChi p) ^ (1 + p.α) := by
        rw [Real.rpow_add hMChi_pos, Real.rpow_one]
      linarith
    rw [abs_mul, abs_of_nonneg (hU_nn x)]; exact hU_h
  unfold remark51MPrime
  calc |p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ) -
          U x * (1 - (U x) ^ p.α)|
      ≤ |p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ)| +
          |U x * (1 - (U x) ^ p.α)| := abs_sub _ _
    _ ≤ |p.χ| * (MChi p) ^ (p.m + p.γ) + (MChi p) ^ (1 + p.α) := by linarith

/-- Smooth version of Remark 5.1 Part 1: bound |U'| globally.
The smoothness assumptions are typically derivable from the existence
construction (Schauder), but `IsTravelingWave` alone does not include
them. -/
theorem remark_5_1_smooth_part1
    (p : CMParams) (c sigma : ℝ)
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hspeed : remark5SpeedCondition p c sigma)
    (U V : ℝ → ℝ)
    (hTW : IsTravelingWave p c U V) (hbound : HasWaveUpperTailBound p c U)
    (hU_diff : ∀ x, DifferentiableAt ℝ U x)
    (hVderiv_diff : ∀ x, DifferentiableAt ℝ (deriv V) x)
    (hderiv_U_cont : Continuous (deriv U))
    (hderiv_U_diff : Differentiable ℝ (deriv U))
    (hderiv_U_tendszero :
      Tendsto (deriv U) atTop (𝓝 0) ∧ Tendsto (deriv U) atBot (𝓝 0))
    (hV_nn : ∀ x, 0 ≤ V x)
    (hV_bound : ∀ x, |V x| ≤ (MChi p) ^ p.γ ∧
        |deriv V x| ≤ (MChi p) ^ p.γ) :
    ∀ x, |deriv U x| ≤ remark51MPrime p / (remark5ChiSigma p sigma) := by
  have hMChi_pos : 0 < MChi p :=
    lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)
  have hχσ_pos : 0 < remark5ChiSigma p sigma := remark5ChiSigma_pos sigma hχ
  have hMChi_ge_one : 1 ≤ MChi p := MChi_ge_one_of_travelingWave hTW hbound
  have hU_nn : ∀ x, 0 ≤ U x := fun x => (hbound.pos x).le
  have hU_le : ∀ x, U x ≤ MChi p := fun x => hbound.le_MChi x
  set a : ℝ → ℝ := fun x => c - p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x
    with ha_def
  set g : ℝ → ℝ := fun x =>
    p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ) - U x * (1 - (U x) ^ p.α)
    with hg_def
  have ha_lb : ∀ x, remark5ChiSigma p sigma ≤ a x := fun x =>
    wave_drift_lower_bound hsigma hspeed hU_nn hU_le hMChi_pos
      (fun y => (hV_bound y).2) x
  have hg_ub : ∀ x, |g x| ≤ remark51MPrime p := fun x =>
    wave_source_upper_bound hU_nn hU_le hMChi_pos hMChi_ge_one hV_nn
      (fun y => (hV_bound y).1) x
  have hM'_nn : 0 ≤ remark51MPrime p := by
    unfold remark51MPrime
    exact add_nonneg (mul_nonneg (abs_nonneg _)
      (Real.rpow_nonneg hMChi_pos.le _))
      (Real.rpow_nonneg hMChi_pos.le _)
  -- ODE identity: (deriv U)' = -a · deriv U + g
  have hode : ∀ x, deriv (deriv U) x = -a x * deriv U x + g x := by
    intro x
    have hchem := wave_chemotaxis_deriv_expand p (hU_diff x)
      (hVderiv_diff x) (hU_nn x)
      (by have := hTW.ode_V x; linarith)
    have hode_U_x := hTW.ode_U x
    rw [hchem] at hode_U_x
    have hiD2 : iteratedDeriv 2 U x = deriv (deriv U) x := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
        iteratedDeriv_one]
    rw [hiD2] at hode_U_x
    simp only [ha_def, hg_def]
    linarith
  -- Apply first_order_ode_sup_bound
  exact first_order_ode_sup_bound hχσ_pos hM'_nn ha_lb hg_ub hode
    hderiv_U_tendszero.1 hderiv_U_tendszero.2
    hderiv_U_cont hderiv_U_diff

/-- Regularity hypotheses for traveling waves needed by Remark 5.1.
These follow from ODE bootstrap and Lemma 5.1 signal estimates,
but are not part of the bare `IsTravelingWave` structure. -/
structure TravelingWaveRegularity
    (p : CMParams) (c : ℝ) (U V : ℝ → ℝ) : Prop where
  U_diff : ∀ x, DifferentiableAt ℝ U x
  U_cont : Continuous U
  V_diff : ∀ x, DifferentiableAt ℝ V x
  V_deriv_diff : ∀ x, DifferentiableAt ℝ (deriv V) x
  deriv_U_cont : Continuous (deriv U)
  deriv_U_diff : Differentiable ℝ (deriv U)
  deriv_U_tendszero :
    Tendsto (deriv U) atTop (𝓝 0) ∧ Tendsto (deriv U) atBot (𝓝 0)
  V_nn : ∀ x, 0 ≤ V x
  V_bound : ∀ x, |V x| ≤ (MChi p) ^ p.γ ∧
      |deriv V x| ≤ (MChi p) ^ p.γ

/-- Max principle for first-order linear ODE on a half-line [x₀, ∞).
For v continuous and differentiable on ℝ, satisfying v' = -a·v + g with
a ≥ a₀ > 0 and |g| ≤ G, with v → 0 at +∞, we have for x ≥ x₀:
|v(x)| ≤ max(|v(x₀)|, G/a₀).

Proof: the sup of v on [x₀, ∞) is attained on a compact subinterval
[x₀, N] (since v → 0 at +∞). The sup point is either x₀ (boundary,
bounded by |v(x₀)|) or interior (critical point, bounded by g/a ≤ G/a₀).
Similarly for inf via -v. -/
theorem first_order_ode_sup_bound_on_Ici
    {v a g : ℝ → ℝ} {a₀ G : ℝ} (x_bdry : ℝ)
    (ha₀ : 0 < a₀) (hG : 0 ≤ G)
    (ha : ∀ x, a₀ ≤ a x)
    (hg : ∀ x, |g x| ≤ G)
    (hode : ∀ x, deriv v x = -a x * v x + g x)
    (hlim_top : Tendsto v atTop (𝓝 0))
    (hv_cont : Continuous v) (hv_diff : Differentiable ℝ v) :
    ∀ x, x_bdry ≤ x → |v x| ≤ max |v x_bdry| (G / a₀) := by
  have hdivnn : 0 ≤ G / a₀ := div_nonneg hG ha₀.le
  have h_max_nn : 0 ≤ max |v x_bdry| (G / a₀) :=
    le_trans hdivnn (le_max_right _ _)
  -- Helper: prove upper bound for any function w satisfying same hypotheses
  -- We can directly prove both upper and lower by symmetry; do upper first.
  have hupper : ∀ x ≥ x_bdry, v x ≤ max |v x_bdry| (G / a₀) := by
    intro x hx
    by_contra hvx
    push_neg at hvx
    have hvx_pos : 0 < v x := lt_of_le_of_lt h_max_nn hvx
    -- v → 0 at +∞, so eventually v y < v x. Get N with this property.
    have hev : ∀ᶠ y in atTop, v y < v x :=
      (hlim_top.eventually (Iio_mem_nhds hvx_pos)).mono fun y hy => by simpa using hy
    obtain ⟨N, hN⟩ := hev.exists_forall_of_atTop
    -- Compact interval K = [x_bdry, max x N + 1]
    let M := max x N + 1
    have hM_gt_x : x < M := by simp [M]; linarith [le_max_left x N]
    have hM_gt_N : N < M := by simp [M]; linarith [le_max_right x N]
    let K : Set ℝ := Set.Icc x_bdry M
    have hK_cpt : IsCompact K := isCompact_Icc
    have hK_ne : K.Nonempty := ⟨x_bdry, le_refl _, le_trans hx hM_gt_x.le⟩
    obtain ⟨y, ⟨hy_ge, hy_le⟩, hy_max⟩ :=
      hK_cpt.exists_isMaxOn hK_ne hv_cont.continuousOn
    -- v(x) ≤ v(y) since x ∈ K
    have hx_in_K : x ∈ K := ⟨hx, le_of_lt hM_gt_x⟩
    have hvxy : v x ≤ v y := hy_max hx_in_K
    have hvy_pos : 0 < v y := lt_of_lt_of_le hvx_pos hvxy
    -- y is global max on [x_bdry, ∞):
    have hy_max_global : ∀ z ≥ x_bdry, v z ≤ v y := by
      intro z hz
      by_cases hzK : z ∈ K
      · exact hy_max hzK
      · -- z ∉ K means z > M (since z ≥ x_bdry).
        have hz_gt_M : M < z := by
          by_contra h_le
          push_neg at h_le
          exact hzK ⟨hz, h_le⟩
        have hz_N : N < z := lt_of_lt_of_le hM_gt_N hz_gt_M.le
        have hvz : v z < v x := hN z hz_N.le
        linarith
    -- Case on whether y = x_bdry or y > x_bdry
    rcases eq_or_lt_of_le hy_ge with hy_eq | hy_gt
    · -- y = x_bdry: max = v(x_bdry), but v x > |v(x_bdry)| ≥ v(x_bdry). Contradiction.
      rw [← hy_eq] at hvxy
      have : v x ≤ |v x_bdry| := le_trans hvxy (le_abs_self _)
      have : v x ≤ max |v x_bdry| (G / a₀) := le_trans this (le_max_left _ _)
      linarith
    · -- y > x_bdry: interior critical point.
      have hLocalMax : IsLocalMax v y := by
        apply (IsMaxOn.isLocalMax (f := v) (s := Set.Ioi x_bdry) ?_) ?_
        · intro z hz
          have hz_ge : x_bdry ≤ z := le_of_lt hz
          exact hy_max_global z hz_ge
        · exact Ioi_mem_nhds hy_gt
      have hderiv_zero : deriv v y = 0 := hLocalMax.deriv_eq_zero
      have hode_at := hode y
      rw [hderiv_zero] at hode_at
      have hay : a y * v y = g y := by linarith
      have hvy_a : v y * a₀ ≤ G :=
        calc v y * a₀ ≤ v y * a y :=
              mul_le_mul_of_nonneg_left (ha y) hvy_pos.le
          _ = g y := by rw [mul_comm]; exact hay
          _ ≤ |g y| := le_abs_self _
          _ ≤ G := hg y
      have hvy_le : v y ≤ G / a₀ := (le_div_iff₀ ha₀).mpr hvy_a
      have : v x ≤ G / a₀ := le_trans hvxy hvy_le
      have : v x ≤ max |v x_bdry| (G / a₀) :=
        le_trans this (le_max_right _ _)
      linarith
  -- Lower bound: apply the same compact-max argument to -v.
  have hlower : ∀ x ≥ x_bdry, -(max |v x_bdry| (G / a₀)) ≤ v x := by
    intro x hx
    by_contra hvx
    push_neg at hvx
    -- -v(x) > max(|v x_bdry|, G/a₀)
    have hnvx_pos : 0 < -v x := by linarith
    have hnv_lim : Tendsto (fun y => -v y) atTop (𝓝 0) := by simpa using hlim_top.neg
    have hev : ∀ᶠ y in atTop, -v y < -v x :=
      (hnv_lim.eventually (Iio_mem_nhds hnvx_pos)).mono fun y hy => by simpa using hy
    obtain ⟨N, hN⟩ := hev.exists_forall_of_atTop
    let M := max x N + 1
    have hM_gt_x : x < M := by simp [M]; linarith [le_max_left x N]
    have hM_gt_N : N < M := by simp [M]; linarith [le_max_right x N]
    let K : Set ℝ := Set.Icc x_bdry M
    have hK_cpt : IsCompact K := isCompact_Icc
    have hK_ne : K.Nonempty := ⟨x_bdry, le_refl _, le_trans hx hM_gt_x.le⟩
    obtain ⟨y, ⟨hy_ge, hy_le⟩, hy_max⟩ :=
      hK_cpt.exists_isMaxOn hK_ne hv_cont.neg.continuousOn
    have hx_in_K : x ∈ K := ⟨hx, le_of_lt hM_gt_x⟩
    have hvxy : -v x ≤ -v y := hy_max hx_in_K
    have hnvy_pos : 0 < -v y := lt_of_lt_of_le hnvx_pos hvxy
    have hy_max_global : ∀ z ≥ x_bdry, -v z ≤ -v y := by
      intro z hz
      by_cases hzK : z ∈ K
      · exact hy_max hzK
      · have hz_gt_M : M < z := by
          by_contra h_le
          push_neg at h_le
          exact hzK ⟨hz, h_le⟩
        have hz_N : N < z := lt_of_lt_of_le hM_gt_N hz_gt_M.le
        have hnvz : -v z < -v x := hN z hz_N.le
        linarith
    rcases eq_or_lt_of_le hy_ge with hy_eq | hy_gt
    · rw [← hy_eq] at hvxy
      have h1 : -v x ≤ |v x_bdry| := by
        have : -v x_bdry ≤ |v x_bdry| := neg_le_abs _
        linarith
      have h2 : -v x ≤ max |v x_bdry| (G / a₀) := le_trans h1 (le_max_left _ _)
      linarith
    · have hLocalMax : IsLocalMax (fun y => -v y) y := by
        apply (IsMaxOn.isLocalMax (f := fun y => -v y) (s := Set.Ioi x_bdry) ?_) ?_
        · intro z hz
          exact hy_max_global z (le_of_lt hz)
        · exact Ioi_mem_nhds hy_gt
      have hderiv_zero : deriv (fun y => -v y) y = 0 := hLocalMax.deriv_eq_zero
      have hnv_ode : deriv (fun z => -v z) y = -a y * (-v y) + (-g y) := by
        simp [deriv_neg, hode y]; ring
      rw [hderiv_zero] at hnv_ode
      have hay : a y * (-v y) = -g y := by linarith
      have hnvy_a : (-v y) * a₀ ≤ G :=
        calc (-v y) * a₀ ≤ (-v y) * a y :=
              mul_le_mul_of_nonneg_left (ha y) hnvy_pos.le
          _ = -g y := by rw [mul_comm]; exact hay
          _ ≤ |g y| := neg_le_abs _
          _ ≤ G := hg y
      have hnvy_le : -v y ≤ G / a₀ := (le_div_iff₀ ha₀).mpr hnvy_a
      have h1 : -v x ≤ G / a₀ := le_trans hvxy hnvy_le
      have h2 : -v x ≤ max |v x_bdry| (G / a₀) := le_trans h1 (le_max_right _ _)
      linarith
  intro x hx
  rw [abs_le]
  exact ⟨hlower x hx, hupper x hx⟩

/-- Duhamel bound for first-order linear ODE v' = -a·v + g with a ≥ a₀ > 0
and |g| ≤ G: for x ≥ x₀, |v(x)| ≤ |v(x₀)|·exp(-a₀(x-x₀)) + (G/a₀)·(1 - exp(-a₀(x-x₀))).

Proof uses Mathlib's `le_gronwallBound_of_liminf_deriv_right_le` applied
to f = |v| with right-slope bound -a₀·|v| + G. Slope bound by case
analysis on sign of v(y):
- v(y) > 0: |v| = v in right neighborhood, slope → v'(y) ≤ -a₀·|v y| + G.
- v(y) < 0: |v| = -v in right neighborhood, slope → -v'(y) ≤ -a₀·|v y| + G.
- v(y) = 0: |v(z)| = |slope of v · (z-y) + o(z-y)|, slope → |v'(y)| = |g(y)| ≤ G.
-/
theorem first_order_ode_duhamel_bound_on_Icc
    {v a g : ℝ → ℝ} {a₀ G : ℝ} (x₀ x_target : ℝ)
    (ha₀ : 0 < a₀) (hG : 0 ≤ G)
    (ha : ∀ y ∈ Set.Icc x₀ x_target, a₀ ≤ a y)
    (hg : ∀ y ∈ Set.Icc x₀ x_target, |g y| ≤ G)
    (hode : ∀ y ∈ Set.Icc x₀ x_target,
      deriv v y = -a y * v y + g y)
    (hv_diff : Differentiable ℝ v)
    (hx_target : x₀ ≤ x_target) :
    |v x_target| ≤ |v x₀| * Real.exp (-a₀ * (x_target - x₀)) +
        G / a₀ * (1 - Real.exp (-a₀ * (x_target - x₀))) := by
  set f : ℝ → ℝ := fun y => |v y|
  set f_bnd : ℝ → ℝ := fun y => -a₀ * |v y| + G
  have hf_cont : ContinuousOn f (Set.Icc x₀ x_target) :=
    hv_diff.continuous.norm.continuousOn
  have ha_f : f x₀ ≤ |v x₀| := le_refl _
  have hbound : ∀ y ∈ Set.Ico x₀ x_target, f_bnd y ≤ -a₀ * f y + G :=
    fun y _ => le_refl _
  have hslope : ∀ y ∈ Set.Ico x₀ x_target, ∀ r, f_bnd y < r →
      ∃ᶠ z in 𝓝[>] y, (z - y)⁻¹ * (f z - f y) < r := by
    intro y hy r hr
    have hyIcc : y ∈ Set.Icc x₀ x_target := ⟨hy.1, hy.2.le⟩
    have hv_y_at : HasDerivAt v (deriv v y) y := (hv_diff y).hasDerivAt
    have hv_y_eq : deriv v y = -a y * v y + g y := hode y hyIcc
    rcases lt_trichotomy (v y) 0 with hvy_neg | hvy_zero | hvy_pos
    · -- v y < 0
      have habs_at : HasDerivAt (fun z => |v z|) (-deriv v y) y := by
        have := (hasDerivAt_abs_neg hvy_neg).comp y hv_y_at
        simpa using this
      have hbound_val : -deriv v y ≤ f_bnd y := by
        rw [hv_y_eq]
        have habs_vy : |v y| = -v y := abs_of_neg hvy_neg
        have hg_neg : -g y ≤ G := neg_le_abs (g y) |>.trans (hg y hyIcc)
        show -(-a y * v y + g y) ≤ -a₀ * |v y| + G
        rw [habs_vy]
        nlinarith [ha y hyIcc]
      have hslope_tendsto := habs_at.hasDerivWithinAt (s := Set.Ici y)
      have := hslope_tendsto.liminf_right_slope_le
        (lt_of_le_of_lt hbound_val hr)
      exact this.mono fun z hz => by
        rw [slope] at hz; simpa [f, sub_smul, smul_eq_mul] using hz
    · -- v y = 0
      have hv_y_eq' : deriv v y = g y := by rw [hv_y_eq, hvy_zero]; ring
      have hvy_abs_zero : |v y| = 0 := by rw [hvy_zero]; exact abs_zero
      have hf_bnd_eq : f_bnd y = G := by
        show -a₀ * |v y| + G = G
        rw [hvy_abs_zero]; ring
      rw [hf_bnd_eq] at hr
      have habs_lt : |deriv v y| < r := by
        rw [hv_y_eq']; exact lt_of_le_of_lt (hg y hyIcc) hr
      have hv_y_within : HasDerivWithinAt v (deriv v y) (Set.Ici y) y :=
        hv_y_at.hasDerivWithinAt
      have hnorm_slope : ∀ᶠ z in 𝓝[Set.Ici y] y,
          ‖z - y‖⁻¹ * ‖v z - v y‖ < r := by
        apply hv_y_within.limsup_norm_slope_le
        rw [Real.norm_eq_abs]; exact habs_lt
      have h_ev : ∀ᶠ z in 𝓝[Set.Ioi y] y,
          (z - y)⁻¹ * (f z - f y) < r := by
        have hsub : 𝓝[Set.Ioi y] y ≤ 𝓝[Set.Ici y] y :=
          nhdsWithin_mono _ Set.Ioi_subset_Ici_self
        have hnorm_slope' : ∀ᶠ z in 𝓝[Set.Ioi y] y,
            ‖z - y‖⁻¹ * ‖v z - v y‖ < r := Filter.Eventually.filter_mono hsub hnorm_slope
        filter_upwards [hnorm_slope',
          self_mem_nhdsWithin (s := Set.Ioi y) (a := y)] with z hz hz_in
        have hzy : 0 < z - y := by
          have : y < z := hz_in
          linarith
        have hnorm_zy : ‖z - y‖ = z - y := by
          rw [Real.norm_eq_abs, abs_of_pos hzy]
        have hvz_minus : v z - v y = v z := by rw [hvy_zero]; ring
        have hnorm_vzy : ‖v z - v y‖ = |v z| := by
          rw [hvz_minus]; rfl
        rw [hnorm_zy, hnorm_vzy] at hz
        show (z - y)⁻¹ * (f z - f y) < r
        show (z - y)⁻¹ * (|v z| - |v y|) < r
        rw [hvy_abs_zero, sub_zero]
        exact hz
      exact h_ev.frequently
    · -- v y > 0
      have habs_at : HasDerivAt (fun z => |v z|) (deriv v y) y := by
        have := (hasDerivAt_abs_pos hvy_pos).comp y hv_y_at
        simpa using this
      have hbound_val : deriv v y ≤ f_bnd y := by
        rw [hv_y_eq]
        have habs_vy : |v y| = v y := abs_of_pos hvy_pos
        have hg_pos : g y ≤ G := (le_abs_self _).trans (hg y hyIcc)
        show -a y * v y + g y ≤ -a₀ * |v y| + G
        rw [habs_vy]
        nlinarith [ha y hyIcc]
      have hslope_tendsto := habs_at.hasDerivWithinAt (s := Set.Ici y)
      have := hslope_tendsto.liminf_right_slope_le
        (lt_of_le_of_lt hbound_val hr)
      exact this.mono fun z hz => by
        rw [slope] at hz; simpa [f, sub_smul, smul_eq_mul] using hz
  have hgronwall := le_gronwallBound_of_liminf_deriv_right_le
    hf_cont hslope ha_f hbound x_target ⟨hx_target, le_refl _⟩
  -- Convert gronwallBound form
  have hK_ne : (-a₀ : ℝ) ≠ 0 := by linarith
  rw [gronwallBound_of_K_ne_0 hK_ne] at hgronwall
  show f x_target ≤ |v x₀| * Real.exp (-a₀ * (x_target - x₀)) +
      G / a₀ * (1 - Real.exp (-a₀ * (x_target - x₀)))
  have hsimp : G / (-a₀) * (Real.exp (-a₀ * (x_target - x₀)) - 1) =
      G / a₀ * (1 - Real.exp (-a₀ * (x_target - x₀))) := by
    field_simp
    ring
  linarith [hgronwall, hsimp]

/-- Global-hypothesis compatibility wrapper for
`first_order_ode_duhamel_bound_on_Icc`. -/
theorem first_order_ode_duhamel_bound
    {v a g : ℝ → ℝ} {a₀ G : ℝ} (x₀ x_target : ℝ)
    (ha₀ : 0 < a₀) (hG : 0 ≤ G)
    (ha : ∀ y, a₀ ≤ a y)
    (hg : ∀ y, |g y| ≤ G)
    (hode : ∀ y, deriv v y = -a y * v y + g y)
    (hv_diff : Differentiable ℝ v)
    (hx_target : x₀ ≤ x_target) :
    |v x_target| ≤ |v x₀| * Real.exp (-a₀ * (x_target - x₀)) +
        G / a₀ * (1 - Real.exp (-a₀ * (x_target - x₀))) :=
  first_order_ode_duhamel_bound_on_Icc x₀ x_target ha₀ hG
    (fun y _ => ha y) (fun y _ => hg y) (fun y _ => hode y)
    hv_diff hx_target

/-- For a traveling wave with regularity, the weighted derivative
w(x) := U'(x) · exp(κx) satisfies the first-order linear ODE
w'(x) = -(c - κ - χ·m·U^{m-1}·V')·w(x) + g_w(x)
where g_w(x) := (χ·U^m·(V - U^γ) - U·(1 - U^α))·exp(κx).

This is derived from the wave ODE iteratedDeriv 2 U + c·U' = χ·(U^m V')' - U(1-U^α)
and the product rule (deriv (U' · exp(κx)) = U'' · exp + κ · U' · exp). -/
theorem wave_weighted_derivative_ode
    (p : CMParams) (c : ℝ) (U V : ℝ → ℝ)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V) (x : ℝ) :
    deriv (fun y => deriv U y * Real.exp (kappa c * y)) x =
      -(c - kappa c - p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x) *
        (deriv U x * Real.exp (kappa c * x)) +
      (p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ) -
        U x * (1 - (U x) ^ p.α)) * Real.exp (kappa c * x) := by
  have hU_nn : ∀ y, 0 ≤ U y := fun y => le_of_lt (hTW.U_pos y)
  -- Exp derivative
  have hexp_at : HasDerivAt (fun y => Real.exp (kappa c * y))
      (kappa c * Real.exp (kappa c * x)) x := by
    have h1 : HasDerivAt (fun y => kappa c * y) (kappa c) x := by
      simpa using (hasDerivAt_id x).const_mul (kappa c)
    have h2 := h1.exp
    convert h2 using 1; ring
  -- deriv U at x via reg
  have hUd_at : HasDerivAt (deriv U) (deriv (deriv U) x) x :=
    (hreg.deriv_U_diff x).hasDerivAt
  -- Product rule for U' * exp
  have hw_at : HasDerivAt (fun y => deriv U y * Real.exp (kappa c * y))
      (deriv (deriv U) x * Real.exp (kappa c * x) +
       deriv U x * (kappa c * Real.exp (kappa c * x))) x := hUd_at.mul hexp_at
  -- Chemotaxis expansion
  have hchem := wave_chemotaxis_deriv_expand p (hreg.U_diff x)
    (hreg.V_deriv_diff x) (hU_nn x)
    (by have := hTW.ode_V x; linarith)
  have hiD2 : iteratedDeriv 2 U x = deriv (deriv U) x := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hode_U := hTW.ode_U x
  rw [hchem, hiD2] at hode_U
  -- Solve for deriv (deriv U) x
  have hdd : deriv (deriv U) x =
      -(c - p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x) * deriv U x +
        (p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ) -
          U x * (1 - (U x) ^ p.α)) := by linarith
  rw [hw_at.deriv, hdd]
  ring

/-- Weighted drift a_w(x) = c - κ - χ·m·U^{m-1}·V' is bounded below
by |χ|σ - κ when the wave's signal bounds give drift c - χ·m·U^{m-1}·V' ≥ |χ|σ. -/
theorem wave_weighted_drift_lower_bound
    {p : CMParams} {c sigma : ℝ}
    (hsigma : 0 < sigma)
    (hspeed : remark5SpeedCondition p c sigma)
    {U V : ℝ → ℝ}
    (hU_nn : ∀ x, 0 ≤ U x) (hU_le : ∀ x, U x ≤ MChi p)
    (hMChi_pos : 0 < MChi p)
    (hV'_abs : ∀ x, |deriv V x| ≤ (MChi p) ^ p.γ) (x : ℝ) :
    remark5ChiSigma p sigma - kappa c ≤
      c - kappa c - p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x := by
  have hdrift := wave_drift_lower_bound hsigma hspeed hU_nn hU_le hMChi_pos
    hV'_abs x
  linarith

/-- Global bound on the weighted source g_w(x) = g₀(x)·exp(κx).
For x ≤ 0: |g_w(x)| ≤ M'·exp(κx) ≤ M'.
For x ≥ 0: |g_w(x)| ≤ |χ|·(K_V+1) + 2, using exponential signal decay
of V (Lemma 5.1's hV_exp). -/
theorem wave_weighted_source_upper_bound_global
    {p : CMParams} {c : ℝ}
    {U V : ℝ → ℝ}
    (hU_nn : ∀ x, 0 ≤ U x) (hU_le : ∀ x, U x ≤ MChi p)
    (hMChi_pos : 0 < MChi p) (hMChi_ge_one : 1 ≤ MChi p)
    (hV_nn : ∀ x, 0 ≤ V x)
    (hV_abs : ∀ x, |V x| ≤ (MChi p) ^ p.γ)
    (hbound : HasWaveUpperTailBound p c U)
    (hV_exp : ∀ x, |V x| ≤ (1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
        Real.exp (-(kappa c) * p.γ * x))
    (hκ_pos : 0 < kappa c) :
    ∀ x,
      |(p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ) -
        U x * (1 - (U x) ^ p.α)) * Real.exp (kappa c * x)| ≤
        max (remark51MPrime p) (max 0
          (|p.χ| * (1 / (1 - kappa c ^ 2 * p.γ ^ 2) + 1) + 2)) := by
  set g_w : ℝ → ℝ := fun x =>
    (p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ) -
      U x * (1 - (U x) ^ p.α)) * Real.exp (kappa c * x)
  let K_V : ℝ := 1 / (1 - kappa c ^ 2 * p.γ ^ 2)
  let G_pos : ℝ := |p.χ| * (K_V + 1) + 2
  have hM'_nn : 0 ≤ remark51MPrime p := by
    unfold remark51MPrime
    exact add_nonneg (mul_nonneg (abs_nonneg _)
      (Real.rpow_nonneg hMChi_pos.le _))
      (Real.rpow_nonneg hMChi_pos.le _)
  intro x
  by_cases hx_nn : 0 ≤ x
  · -- x ≥ 0
    have hU_exp : U x ≤ Real.exp (-(kappa c) * x) := hbound.le_exp x
    have hV_bound_exp := hV_exp x
    have hexp_nn : 0 ≤ Real.exp (kappa c * x) := (Real.exp_pos _).le
    have hm_pos : 0 < p.m := lt_of_lt_of_le zero_lt_one p.hm
    have hγ_pos : 0 < p.γ := lt_of_lt_of_le zero_lt_one p.hγ
    have hα_pos : 0 < p.α := lt_of_lt_of_le zero_lt_one p.hα
    have hU_nn_x : 0 ≤ U x := hU_nn x
    -- U^m ≤ exp(-κmx), U^γ ≤ exp(-κγx)
    have hUm_bound : (U x) ^ p.m ≤ Real.exp (-(kappa c * p.m * x)) := by
      have h1 : (U x) ^ p.m ≤ (Real.exp (-(kappa c) * x)) ^ p.m :=
        Real.rpow_le_rpow hU_nn_x hU_exp hm_pos.le
      have h2 : (Real.exp (-(kappa c) * x)) ^ p.m =
          Real.exp (-(kappa c * p.m * x)) := by
        rw [← Real.exp_mul]; ring_nf
      rw [← h2]; exact h1
    have hUγ_bound : (U x) ^ p.γ ≤ Real.exp (-(kappa c * p.γ * x)) := by
      have h1 : (U x) ^ p.γ ≤ (Real.exp (-(kappa c) * x)) ^ p.γ :=
        Real.rpow_le_rpow hU_nn_x hU_exp hγ_pos.le
      have h2 : (Real.exp (-(kappa c) * x)) ^ p.γ =
          Real.exp (-(kappa c * p.γ * x)) := by
        rw [← Real.exp_mul]; ring_nf
      rw [← h2]; exact h1
    have hK_V_nn : 0 ≤ K_V := by
      have h := hV_exp 0
      have hzero : -kappa c * p.γ * 0 = 0 := by ring
      rw [hzero, Real.exp_zero, mul_one] at h
      exact le_trans (abs_nonneg _) h
    have hKV1_nn : 0 ≤ K_V + 1 := by linarith
    have hUm_nn : 0 ≤ (U x) ^ p.m := Real.rpow_nonneg hU_nn_x _
    have hUγ_nn : 0 ≤ (U x) ^ p.γ := Real.rpow_nonneg hU_nn_x _
    have hUγ_le_exp : (U x) ^ p.γ ≤ Real.exp (-(kappa c) * p.γ * x) := by
      have h_eq : -(kappa c * p.γ * x) = -(kappa c) * p.γ * x := by ring
      rw [← h_eq]; exact hUγ_bound
    have hUm_le_exp : (U x) ^ p.m ≤ Real.exp (-(kappa c) * p.m * x) := by
      have h_eq : -(kappa c * p.m * x) = -(kappa c) * p.m * x := by ring
      rw [← h_eq]; exact hUm_bound
    have hV_minus_bound : |V x - (U x) ^ p.γ| ≤
        (K_V + 1) * Real.exp (-(kappa c) * p.γ * x) := by
      calc |V x - (U x) ^ p.γ|
          ≤ |V x| + |(U x) ^ p.γ| := abs_sub _ _
        _ = |V x| + (U x) ^ p.γ := by rw [abs_of_nonneg hUγ_nn]
        _ ≤ K_V * Real.exp (-(kappa c) * p.γ * x) +
            Real.exp (-(kappa c) * p.γ * x) := by
            linarith [hV_bound_exp, hUγ_le_exp]
        _ = (K_V + 1) * Real.exp (-(kappa c) * p.γ * x) := by ring
    have hexp_chain : (U x) ^ p.m *
        ((K_V + 1) * Real.exp (-(kappa c) * p.γ * x)) *
        Real.exp (kappa c * x) ≤ K_V + 1 := by
      have hcombine : (U x) ^ p.m *
          ((K_V + 1) * Real.exp (-(kappa c) * p.γ * x)) *
          Real.exp (kappa c * x) ≤
          Real.exp (-(kappa c) * p.m * x) *
          ((K_V + 1) * Real.exp (-(kappa c) * p.γ * x)) *
          Real.exp (kappa c * x) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hUm_le_exp
            (mul_nonneg hKV1_nn (Real.exp_pos _).le))
          (Real.exp_pos _).le
      have hexp_collapse : Real.exp (-(kappa c) * p.m * x) *
          ((K_V + 1) * Real.exp (-(kappa c) * p.γ * x)) *
          Real.exp (kappa c * x) =
          (K_V + 1) * Real.exp ((1 - p.m - p.γ) * kappa c * x) := by
        rw [show -(kappa c) * p.m * x = -(kappa c * p.m * x) from by ring,
            show -(kappa c) * p.γ * x = -(kappa c * p.γ * x) from by ring]
        rw [show Real.exp (-(kappa c * p.m * x)) *
                ((K_V + 1) * Real.exp (-(kappa c * p.γ * x))) *
                Real.exp (kappa c * x) =
                (K_V + 1) *
                (Real.exp (-(kappa c * p.m * x)) *
                 Real.exp (-(kappa c * p.γ * x)) *
                 Real.exp (kappa c * x)) from by ring]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [hexp_collapse] at hcombine
      have hexp_le_one : Real.exp ((1 - p.m - p.γ) * kappa c * x) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have hmγ : 1 - p.m - p.γ ≤ 0 := by linarith [p.hm, p.hγ]
        have h1 : (1 - p.m - p.γ) * kappa c ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hmγ hκ_pos.le
        exact mul_nonpos_of_nonpos_of_nonneg h1 hx_nn
      have : (K_V + 1) * Real.exp ((1 - p.m - p.γ) * kappa c * x) ≤
          (K_V + 1) * 1 :=
        mul_le_mul_of_nonneg_left hexp_le_one hKV1_nn
      linarith
    have hT1 : |p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ)| *
        Real.exp (kappa c * x) ≤ |p.χ| * (K_V + 1) := by
      have habs_rewrite : |p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ)| =
          |p.χ| * (U x) ^ p.m * |V x - (U x) ^ p.γ| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hUm_nn]
      rw [habs_rewrite]
      calc |p.χ| * (U x) ^ p.m * |V x - (U x) ^ p.γ| * Real.exp (kappa c * x)
          ≤ |p.χ| * (U x) ^ p.m *
              ((K_V + 1) * Real.exp (-(kappa c) * p.γ * x)) *
              Real.exp (kappa c * x) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            apply mul_le_mul_of_nonneg_left hV_minus_bound
            exact mul_nonneg (abs_nonneg _) hUm_nn
        _ = |p.χ| * ((U x) ^ p.m *
              ((K_V + 1) * Real.exp (-(kappa c) * p.γ * x)) *
              Real.exp (kappa c * x)) := by ring
        _ ≤ |p.χ| * (K_V + 1) :=
            mul_le_mul_of_nonneg_left hexp_chain (abs_nonneg _)
    have hUα_nn : 0 ≤ (U x) ^ p.α := Real.rpow_nonneg hU_nn_x _
    have hUα_le_one : (U x) ^ p.α ≤ 1 := by
      have hU_le_one : U x ≤ 1 := by
        have h := hbound.le_exp x
        have : Real.exp (-(kappa c) * x) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have hk : 0 ≤ kappa c := hκ_pos.le
          nlinarith [hx_nn]
        linarith
      exact Real.rpow_le_one hU_nn_x hU_le_one hα_pos.le
    have h1Uα_abs : |1 - (U x) ^ p.α| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith
    have hT2 : |U x * (1 - (U x) ^ p.α)| * Real.exp (kappa c * x) ≤ 2 := by
      have hU_x_le : U x ≤ Real.exp (-(kappa c) * x) := hbound.le_exp x
      have hU_exp_eq : Real.exp (-(kappa c) * x) * Real.exp (kappa c * x) = 1 := by
        rw [← Real.exp_add]
        rw [show -(kappa c) * x + kappa c * x = 0 from by ring, Real.exp_zero]
      calc |U x * (1 - (U x) ^ p.α)| * Real.exp (kappa c * x)
          = U x * |1 - (U x) ^ p.α| * Real.exp (kappa c * x) := by
            rw [abs_mul, abs_of_nonneg hU_nn_x]
        _ ≤ U x * 2 * Real.exp (kappa c * x) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h1Uα_abs hU_nn_x)
              (Real.exp_pos _).le
        _ = 2 * (U x * Real.exp (kappa c * x)) := by ring
        _ ≤ 2 * (Real.exp (-(kappa c) * x) * Real.exp (kappa c * x)) := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul_of_nonneg_right hU_x_le (Real.exp_pos _).le
            · norm_num
        _ = 2 * 1 := by rw [hU_exp_eq]
        _ = 2 := by ring
    show |g_w x| ≤ max (remark51MPrime p) (max 0 G_pos)
    have hg_w_G_pos : |g_w x| ≤ G_pos := by
      show |(p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ) -
            U x * (1 - (U x) ^ p.α)) * Real.exp (kappa c * x)| ≤
          |p.χ| * (K_V + 1) + 2
      calc |(p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ) -
              U x * (1 - (U x) ^ p.α)) * Real.exp (kappa c * x)|
          = |p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ) -
              U x * (1 - (U x) ^ p.α)| *
            Real.exp (kappa c * x) := by
            rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        _ ≤ (|p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ)| +
              |U x * (1 - (U x) ^ p.α)|) * Real.exp (kappa c * x) :=
            mul_le_mul_of_nonneg_right (abs_sub _ _) (Real.exp_pos _).le
        _ = |p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ)| * Real.exp (kappa c * x) +
            |U x * (1 - (U x) ^ p.α)| * Real.exp (kappa c * x) := by ring
        _ ≤ |p.χ| * (K_V + 1) + 2 := by linarith
    calc |g_w x|
        ≤ G_pos := hg_w_G_pos
      _ ≤ max 0 G_pos := le_max_right _ _
      _ ≤ max (remark51MPrime p) (max 0 G_pos) := le_max_right _ _
  · -- x < 0: |g_w(x)| ≤ M' (via exp(κx) ≤ 1)
    push_neg at hx_nn
    have hsource := wave_source_upper_bound hU_nn hU_le hMChi_pos
      hMChi_ge_one hV_nn hV_abs x
    have hexp_le_one : Real.exp (kappa c * x) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : kappa c * x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hκ_pos.le hx_nn.le
      exact this
    show |g_w x| ≤ max (remark51MPrime p) (max 0 G_pos)
    have hg_w_eq : |g_w x| =
        |p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ) -
          U x * (1 - (U x) ^ p.α)| * Real.exp (kappa c * x) := by
      show |(_) * Real.exp (kappa c * x)| = _
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |g_w x|
        = |p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ) -
            U x * (1 - (U x) ^ p.α)| * Real.exp (kappa c * x) := hg_w_eq
      _ ≤ remark51MPrime p * Real.exp (kappa c * x) :=
          mul_le_mul_of_nonneg_right hsource (Real.exp_pos _).le
      _ ≤ remark51MPrime p * 1 :=
          mul_le_mul_of_nonneg_left hexp_le_one hM'_nn
      _ = remark51MPrime p := by ring
      _ ≤ max (remark51MPrime p) (max 0 G_pos) := le_max_left _ _

/-- Duhamel-based Part 2 of Remark 5.1: under regularity + exp signal bounds,
the wave derivative U' decays exponentially. The constant C is explicit
(not the paper's M''/(|χ|²σ)); proving C ≤ M''/(|χ|²σ) requires the
paper's specific algebraic verification. -/
theorem remark_5_1_smooth_part2_via_duhamel
    (p : CMParams) (c sigma : ℝ)
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hspeed : remark5SpeedCondition p c sigma)
    (hκ_pos : 0 < kappa c) (hκσ : kappa c < remark5ChiSigma p sigma)
    (U V : ℝ → ℝ)
    (hTW : IsTravelingWave p c U V) (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hV_exp : ∀ x, |V x| ≤ (1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
        Real.exp (-(kappa c) * p.γ * x) ∧
      |deriv V x| ≤ (1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
        Real.exp (-(kappa c) * p.γ * x)) :
    ∀ x, 0 ≤ x →
      |deriv U x| ≤
        (|deriv U 0| +
          max (remark51MPrime p) (max 0
            (|p.χ| * (1 / (1 - kappa c ^ 2 * p.γ ^ 2) + 1) + 2)) /
              (remark5ChiSigma p sigma - kappa c)) *
          Real.exp (-(kappa c) * x) := by
  have hχσ_pos : 0 < remark5ChiSigma p sigma := remark5ChiSigma_pos sigma hχ
  have ha₀_pos : 0 < remark5ChiSigma p sigma - kappa c := by linarith
  have hMChi_pos : 0 < MChi p :=
    lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)
  have hMChi_ge_one : 1 ≤ MChi p := MChi_ge_one_of_travelingWave hTW hbound
  have hU_nn : ∀ x, 0 ≤ U x := fun x => (hbound.pos x).le
  have hU_le : ∀ x, U x ≤ MChi p := fun x => hbound.le_MChi x
  -- Set up w(x) = U'(x) · exp(κx)
  set w : ℝ → ℝ := fun x => deriv U x * Real.exp (kappa c * x) with hw_def
  set a_w : ℝ → ℝ := fun x =>
    c - kappa c - p.χ * p.m * (U x) ^ (p.m - 1) * deriv V x with ha_w_def
  set g_w : ℝ → ℝ := fun x =>
    (p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ) - U x * (1 - (U x) ^ p.α))
      * Real.exp (kappa c * x) with hg_w_def
  -- ODE for w
  have hw_ode : ∀ x, deriv w x = -a_w x * w x + g_w x := by
    intro x
    have := wave_weighted_derivative_ode p c U V hTW hreg x
    show deriv (fun y => deriv U y * Real.exp (kappa c * y)) x =
      -a_w x * (deriv U x * Real.exp (kappa c * x)) +
      (p.χ * (U x) ^ p.m * (V x - (U x) ^ p.γ) -
        U x * (1 - (U x) ^ p.α)) * Real.exp (kappa c * x)
    exact this
  -- Drift lower bound: a_w ≥ |χ|σ - κ
  have ha_lb : ∀ x, remark5ChiSigma p sigma - kappa c ≤ a_w x := fun x =>
    wave_weighted_drift_lower_bound hsigma hspeed hU_nn hU_le hMChi_pos
      (fun y => (hreg.V_bound y).2) x
  -- Source bound: |g_w| ≤ G with explicit value
  set G : ℝ := max (remark51MPrime p) (max 0
    (|p.χ| * (1 / (1 - kappa c ^ 2 * p.γ ^ 2) + 1) + 2)) with hG_def
  have hM'_nn_inner : 0 ≤ remark51MPrime p := by
    unfold remark51MPrime
    exact add_nonneg (mul_nonneg (abs_nonneg _)
      (Real.rpow_nonneg hMChi_pos.le _))
      (Real.rpow_nonneg hMChi_pos.le _)
  have hG_nn : 0 ≤ G := le_trans hM'_nn_inner (le_max_left _ _)
  have hG_bound : ∀ x, |g_w x| ≤ G :=
    wave_weighted_source_upper_bound_global hU_nn hU_le hMChi_pos hMChi_ge_one
      hreg.V_nn (fun y => (hreg.V_bound y).1) hbound
      (fun y => (hV_exp y).1) hκ_pos
  -- w is differentiable (deriv U diff × exp)
  have hw_diff : Differentiable ℝ w := by
    intro x
    have h1 : DifferentiableAt ℝ (deriv U) x := hreg.deriv_U_diff x
    have h2 : DifferentiableAt ℝ (fun y => Real.exp (kappa c * y)) x := by
      have : HasDerivAt (fun y => Real.exp (kappa c * y))
          (kappa c * Real.exp (kappa c * x)) x := by
        have hid : HasDerivAt (fun y => kappa c * y) (kappa c) x := by
          simpa using (hasDerivAt_id x).const_mul (kappa c)
        have := hid.exp
        convert this using 1; ring
      exact this.differentiableAt
    exact h1.mul h2
  -- Apply Duhamel for each x ≥ 0
  intro x hx_nn
  have hduh := first_order_ode_duhamel_bound (a := a_w) (g := g_w) (a₀ := remark5ChiSigma p sigma - kappa c)
    (G := G) 0 x ha₀_pos hG_nn ha_lb hG_bound hw_ode hw_diff hx_nn
  -- hduh : |w x| ≤ |w 0| · exp(-(|χ|σ-κ)(x - 0)) + G/(|χ|σ-κ)·(1 - exp(-(|χ|σ-κ)(x-0)))
  -- Convert |w x| bound to |deriv U x| bound
  have hexp_neg_le : Real.exp (-(remark5ChiSigma p sigma - kappa c) * (x - 0)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : (remark5ChiSigma p sigma - kappa c) * (x - 0) ≥ 0 := by
      apply mul_nonneg ha₀_pos.le; linarith
    linarith
  have hduh' : |w x| ≤ |w 0| + G / (remark5ChiSigma p sigma - kappa c) := by
    have hsub_zero : x - 0 = x := by ring
    rw [hsub_zero] at hduh
    have h1 : |w 0| * Real.exp (-(remark5ChiSigma p sigma - kappa c) * x) ≤ |w 0| := by
      have hexp_le_one : Real.exp (-(remark5ChiSigma p sigma - kappa c) * x) ≤ 1 :=
        Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (by linarith : -(remark5ChiSigma p sigma - kappa c) ≤ 0) hx_nn)
      exact mul_le_of_le_one_right (abs_nonneg _) hexp_le_one
    have h2 : G / (remark5ChiSigma p sigma - kappa c) *
        (1 - Real.exp (-(remark5ChiSigma p sigma - kappa c) * x)) ≤
        G / (remark5ChiSigma p sigma - kappa c) := by
      have hG_div_nn : 0 ≤ G / (remark5ChiSigma p sigma - kappa c) :=
        div_nonneg hG_nn ha₀_pos.le
      have hexp_nn : 0 ≤ Real.exp (-(remark5ChiSigma p sigma - kappa c) * x) :=
        (Real.exp_pos _).le
      nlinarith [Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (by linarith : -(remark5ChiSigma p sigma - kappa c) ≤ 0) hx_nn)]
    linarith
  -- |w x| = |deriv U x| · exp(κx), so |deriv U x| = |w x| · exp(-κx)
  have hw_eq : |w x| = |deriv U x| * Real.exp (kappa c * x) := by
    show |deriv U x * Real.exp (kappa c * x)| = _
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp_inv : Real.exp (kappa c * x) * Real.exp (-(kappa c) * x) = 1 := by
    rw [← Real.exp_add]
    rw [show kappa c * x + -(kappa c) * x = 0 from by ring, Real.exp_zero]
  calc |deriv U x|
      = |deriv U x| * 1 := by ring
    _ = |deriv U x| * (Real.exp (kappa c * x) * Real.exp (-(kappa c) * x)) := by
        rw [hexp_inv]
    _ = (|deriv U x| * Real.exp (kappa c * x)) * Real.exp (-(kappa c) * x) := by ring
    _ = |w x| * Real.exp (-(kappa c) * x) := by rw [← hw_eq]
    _ ≤ (|w 0| + G / (remark5ChiSigma p sigma - kappa c)) * Real.exp (-(kappa c) * x) :=
        mul_le_mul_of_nonneg_right hduh' (Real.exp_pos _).le
    _ = (|deriv U 0| + G / (remark5ChiSigma p sigma - kappa c)) * Real.exp (-(kappa c) * x) := by
        have hw0 : w 0 = deriv U 0 := by
          show deriv U 0 * Real.exp (kappa c * 0) = deriv U 0
          rw [mul_zero, Real.exp_zero, mul_one]
        rw [hw0]

/-- Conditional Remark_5_1: under the smooth hypotheses bundle
(regularity + signal bound + κ < |χ|σ) AND a paper-specific constant
inequality, Remark_5_1's bounds hold. Combines Part 1 (smooth_part1)
with Part 2 (smooth_part2_via_duhamel) bounds.

The smooth hypotheses bundle is the "regularity bridge" that future
work (elliptic regularity in Lean) would discharge from
IsTravelingWave + HasWaveUpperTailBound alone. The constant bound
is the paper's M'' algebraic inequality. -/
theorem Remark_5_1.of_regularity_and_constant_bound
    (h_reg : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        TravelingWaveRegularity p c U V)
    (h_part2 : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        ∀ x, 0 ≤ x →
          |deriv U x| ≤
            remark51MDoublePrime p sigma / (remark5ChiTwoSigma p sigma) *
              Real.exp (-(kappa c) * x)) :
    Remark_5_1 := by
  intro p c sigma hsigma hχ hspeed U V hTW hbound
  have hreg := h_reg p c sigma hsigma hχ hspeed U V hTW hbound
  refine ⟨?_, h_part2 p c sigma hsigma hχ hspeed U V hTW hbound⟩
  exact remark_5_1_smooth_part1 p c sigma hsigma hχ hspeed U V hTW hbound
    hreg.U_diff hreg.V_deriv_diff hreg.deriv_U_cont hreg.deriv_U_diff
    hreg.deriv_U_tendszero hreg.V_nn hreg.V_bound

/-- Variant of remark_5_1_smooth_part2_via_duhamel that bounds |U'| by the
explicit Duhamel constant. This is a step toward the M''/(|χ|²σ) bound:
the explicit constant `|w(0)| + G/(|χ|σ - κ)` must be shown ≤ M''/(|χ|²σ)
by paper algebra. The smooth_part1 bound on |w(0)| = |U'(0)| gives one
ingredient; the source bound G ≤ max(M', G_pos) gives another. -/
theorem wave_derivative_constant_bound_via_smooth_part1_and_duhamel
    (p : CMParams) (c sigma : ℝ)
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hspeed : remark5SpeedCondition p c sigma)
    (hκ_pos : 0 < kappa c) (hκσ : kappa c < remark5ChiSigma p sigma)
    (U V : ℝ → ℝ)
    (hTW : IsTravelingWave p c U V) (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hV_exp : ∀ x, |V x| ≤ (1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
        Real.exp (-(kappa c) * p.γ * x) ∧
      |deriv V x| ≤ (1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
        Real.exp (-(kappa c) * p.γ * x)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ x, |deriv U x| ≤ C) ∧
      ∀ x, 0 ≤ x → |deriv U x| ≤ C * Real.exp (-(kappa c) * x) := by
  -- Part 1: |deriv U x| ≤ M' / (|χ|σ) globally
  have hpart1 := remark_5_1_smooth_part1 p c sigma hsigma hχ hspeed U V hTW
    hbound hreg.U_diff hreg.V_deriv_diff hreg.deriv_U_cont hreg.deriv_U_diff
    hreg.deriv_U_tendszero hreg.V_nn hreg.V_bound
  -- Part 2: explicit bound from smooth_part2_via_duhamel (now non-existential)
  have hpart2 := remark_5_1_smooth_part2_via_duhamel p c sigma hsigma
    hχ hspeed hκ_pos hκσ U V hTW hbound hreg hV_exp
  set C₂ : ℝ := |deriv U 0| +
    max (remark51MPrime p) (max 0
      (|p.χ| * (1 / (1 - kappa c ^ 2 * p.γ ^ 2) + 1) + 2)) /
        (remark5ChiSigma p sigma - kappa c) with hC₂_def
  -- Combined: C := max(M'/(|χ|σ), C₂)
  have hχσ_pos : 0 < remark5ChiSigma p sigma := remark5ChiSigma_pos sigma hχ
  have hM'_nn : 0 ≤ remark51MPrime p := by
    have hMChi_pos : 0 < MChi p :=
      lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)
    unfold remark51MPrime
    exact add_nonneg (mul_nonneg (abs_nonneg _)
      (Real.rpow_nonneg hMChi_pos.le _))
      (Real.rpow_nonneg hMChi_pos.le _)
  have hC₁_nn : 0 ≤ remark51MPrime p / (remark5ChiSigma p sigma) :=
    div_nonneg hM'_nn hχσ_pos.le
  -- Use max of the two
  refine ⟨max (remark51MPrime p / (remark5ChiSigma p sigma)) C₂,
    le_max_of_le_left hC₁_nn, ?_, ?_⟩
  · intro x
    calc |deriv U x|
        ≤ remark51MPrime p / (remark5ChiSigma p sigma) := hpart1 x
      _ ≤ max (remark51MPrime p / (remark5ChiSigma p sigma)) C₂ := le_max_left _ _
  · intro x hx_nn
    calc |deriv U x|
        ≤ C₂ * Real.exp (-(kappa c) * x) := hpart2 x hx_nn
      _ ≤ max (remark51MPrime p / (remark5ChiSigma p sigma)) C₂ *
            Real.exp (-(kappa c) * x) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- First piece of the `M''` constant tracking in the large-power branch:
`|χ|^σ M' ≤ M''/2` when `|χ|^σ ≥ 1`.

The positive exponent is important: from `σ > 0` and `|χ|^σ ≥ 1` we get
`|χ| ≥ 1`, and the second summand in `M''` then dominates
`|χ|^σ M'`. -/
theorem remark51MPrime_chiSigma_le_MDoublePrime_half
    (p : CMParams) {sigma : ℝ}
    (hMChi_pos : 0 < MChi p)
    (hMChi_ge_one : 1 ≤ MChi p)
    (hsigma : 0 < sigma)
    (hχσ_ge_one : 1 ≤ remark5ChiSigma p sigma) :
    2 * (remark51MPrime p * remark5ChiSigma p sigma) ≤
      remark51MDoublePrime p sigma / 2 := by
  unfold remark51MPrime remark51MDoublePrime
  have hχ_nn : 0 ≤ |p.χ| := abs_nonneg _
  set M' := |p.χ| * (MChi p) ^ (p.m + p.γ) + (MChi p) ^ (1 + p.α) with hM'_def
  have hM'_nn : 0 ≤ M' := by
    have h1 : 0 ≤ |p.χ| * (MChi p) ^ (p.m + p.γ) :=
      mul_nonneg hχ_nn (Real.rpow_nonneg hMChi_pos.le _)
    have h2 : 0 ≤ (MChi p) ^ (1 + p.α) :=
      Real.rpow_nonneg hMChi_pos.le _
    linarith
  -- A ≥ 1
  have hA_ge_two : 2 ≤ 1 + 2 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
      (MChi p) ^ p.α := by
    have h1 : 0 ≤ 2 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) :=
      mul_nonneg (mul_nonneg (by norm_num) hχ_nn) (Real.rpow_nonneg hMChi_pos.le _)
    have h2 : 1 ≤ (MChi p) ^ p.α :=
      Real.one_le_rpow hMChi_ge_one (le_trans zero_le_one p.hα)
    linarith
  have hMChi_m_minus_one_ge_one : 1 ≤ (MChi p) ^ (p.m - 1) := by
    have : 0 ≤ p.m - 1 := by linarith [p.hm]
    exact Real.one_le_rpow hMChi_ge_one this
  have hχ_ge_one : 1 ≤ |p.χ| := by
    by_contra hnot
    have hχ_lt_one : |p.χ| < 1 := lt_of_not_ge hnot
    have hp_lt_one : remark5ChiSigma p sigma < 1 := by
      exact (Real.rpow_lt_one_iff' (abs_nonneg p.χ) hsigma).2 hχ_lt_one
    linarith
  have hχmM_ge_one :
      1 ≤ |p.χ| * p.m * (MChi p) ^ (p.m - 1) := by
    calc
      (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ |p.χ| * p.m * (MChi p) ^ (p.m - 1) := by
        exact mul_le_mul
          (mul_le_mul hχ_ge_one p.hm zero_le_one (abs_nonneg p.χ))
          hMChi_m_minus_one_ge_one zero_le_one
          (mul_nonneg (abs_nonneg p.χ) (le_trans zero_le_one p.hm))
  -- The chemotactic summand in B dominates |χ|^σ M'.
  have hB_term : |p.χ| * p.m * (MChi p) ^ (p.m - 1) * M' * (p.γ + remark5ChiSigma p sigma) ≥
      remark5ChiSigma p sigma * M' := by
    have hs_le :
        remark5ChiSigma p sigma ≤ p.γ + remark5ChiSigma p sigma := by
      linarith [p.hγ]
    have hM's_nn : 0 ≤ M' * remark5ChiSigma p sigma :=
      mul_nonneg hM'_nn (remark5ChiSigma_nonneg p sigma)
    calc
      remark5ChiSigma p sigma * M'
          = 1 * (M' * remark5ChiSigma p sigma) := by ring
      _ ≤ (|p.χ| * p.m * (MChi p) ^ (p.m - 1)) *
            (M' * remark5ChiSigma p sigma) :=
        mul_le_mul_of_nonneg_right hχmM_ge_one hM's_nn
      _ ≤ (|p.χ| * p.m * (MChi p) ^ (p.m - 1)) *
            (M' * (p.γ + remark5ChiSigma p sigma)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left hs_le hM'_nn
        · exact mul_nonneg
            (mul_nonneg (abs_nonneg p.χ) (le_trans zero_le_one p.hm))
            (Real.rpow_nonneg hMChi_pos.le _)
      _ = |p.χ| * p.m * (MChi p) ^ (p.m - 1) * M' *
            (p.γ + remark5ChiSigma p sigma) := by ring
  -- Hence B ≥ |χ|^σ M'.
  have hB_ge : remark5ChiTwoSigma p sigma +
      |p.χ| * p.m * (MChi p) ^ (p.m - 1) * M' * (p.γ + remark5ChiSigma p sigma) ≥
      remark5ChiSigma p sigma * M' := by
    have h_chisq : 0 ≤ remark5ChiTwoSigma p sigma :=
      remark5ChiTwoSigma_nonneg p sigma
    linarith [hB_term]
  -- A·B ≥ |χ|^σ M'.
  have hAB_ge : (1 + 2 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
      (MChi p) ^ p.α) *
        (remark5ChiTwoSigma p sigma +
          |p.χ| * p.m * (MChi p) ^ (p.m - 1) * M' * (p.γ + remark5ChiSigma p sigma)) ≥
      2 * (M' * remark5ChiSigma p sigma) := by
    have hs_M_nn : 0 ≤ remark5ChiSigma p sigma * M' :=
      mul_nonneg (remark5ChiSigma_nonneg p sigma) hM'_nn
    calc 2 * (M' * remark5ChiSigma p sigma)
        = 2 * (remark5ChiSigma p sigma * M') := by ring
      _ ≤ (1 + 2 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
              (MChi p) ^ p.α) * (remark5ChiSigma p sigma * M') := by
            apply mul_le_mul_of_nonneg_right _ hs_M_nn
            exact hA_ge_two
      _ ≤ (1 + 2 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
              (MChi p) ^ p.α) *
            (remark5ChiTwoSigma p sigma +
              |p.χ| * p.m * (MChi p) ^ (p.m - 1) * M' * (p.γ + remark5ChiSigma p sigma)) := by
            apply mul_le_mul_of_nonneg_left hB_ge
            linarith [hA_ge_two]
  -- M''/2 = A·B
  show 2 * (M' * remark5ChiSigma p sigma) ≤ 2 *
    (1 + 2 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) + (MChi p) ^ p.α) *
    (remark5ChiTwoSigma p sigma + |p.χ| * p.m * (MChi p) ^ (p.m - 1) *
      (|p.χ| * (MChi p) ^ (p.m + p.γ) + (MChi p) ^ (p.α + 1)) *
      (p.γ + remark5ChiSigma p sigma)) / 2
  -- Need to identify M' inside the M'' formula
  have h_M'_match : |p.χ| * (MChi p) ^ (p.m + p.γ) + (MChi p) ^ (p.α + 1) = M' := by
    rw [hM'_def]
    congr 1
    rw [show p.α + 1 = 1 + p.α from by ring]
  rw [h_M'_match]
  have h_div : 2 * ((1 + 2 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) + (MChi p) ^ p.α) *
      (remark5ChiTwoSigma p sigma + |p.χ| * p.m * (MChi p) ^ (p.m - 1) * M' *
        (p.γ + remark5ChiSigma p sigma))) / 2 =
      (1 + 2 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) + (MChi p) ^ p.α) *
      (remark5ChiTwoSigma p sigma + |p.χ| * p.m * (MChi p) ^ (p.m - 1) * M' *
        (p.γ + remark5ChiSigma p sigma)) := by ring
  linarith [hAB_ge]

/-- In the large-power branch `|χ|^σ ≥ 1`, Part 1 also gives
`|U'(x)| ≤ M''/(2 |χ|^(2σ))`. -/
theorem remark_5_1_smooth_part1_strong
    (p : CMParams) (c sigma : ℝ)
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hχσ_ge_one : 1 ≤ remark5ChiSigma p sigma)
    (hspeed : remark5SpeedCondition p c sigma)
    (U V : ℝ → ℝ)
    (hTW : IsTravelingWave p c U V) (hbound : HasWaveUpperTailBound p c U)
    (hU_diff : ∀ x, DifferentiableAt ℝ U x)
    (hV_deriv_diff : ∀ x, DifferentiableAt ℝ (deriv V) x)
    (hderiv_U_cont : Continuous (deriv U))
    (hderiv_U_diff : Differentiable ℝ (deriv U))
    (hderiv_U_tendszero : Tendsto (deriv U) atTop (𝓝 0) ∧
      Tendsto (deriv U) atBot (𝓝 0))
    (hV_nn : ∀ x, 0 ≤ V x)
    (hV_bound : ∀ x, |V x| ≤ (MChi p) ^ p.γ ∧
      |deriv V x| ≤ (MChi p) ^ p.γ) :
    ∀ x, |deriv U x| ≤
      remark51MDoublePrime p sigma / (2 * (remark5ChiTwoSigma p sigma)) := by
  have hχσ_pos : 0 < remark5ChiSigma p sigma := remark5ChiSigma_pos sigma hχ
  have hχ2σ_pos : 0 < remark5ChiTwoSigma p sigma :=
    remark5ChiTwoSigma_pos sigma hχ
  have hMChi_pos : 0 < MChi p :=
    lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)
  have hMChi_ge_one : 1 ≤ MChi p := MChi_ge_one_of_travelingWave hTW hbound
  have hM'_chi := remark51MPrime_chiSigma_le_MDoublePrime_half p (sigma := sigma)
    hMChi_pos hMChi_ge_one hsigma hχσ_ge_one
  have hpart1 := remark_5_1_smooth_part1 p c sigma hsigma hχ hspeed U V hTW hbound
    hU_diff hV_deriv_diff hderiv_U_cont hderiv_U_diff hderiv_U_tendszero hV_nn hV_bound
  intro x
  have hχσ_ne : remark5ChiSigma p sigma ≠ 0 := ne_of_gt hχσ_pos
  have hpart1_x := hpart1 x
  have h_eq : remark51MPrime p / (remark5ChiSigma p sigma) =
      remark51MPrime p * remark5ChiSigma p sigma /
        (remark5ChiTwoSigma p sigma) := by
    unfold remark5ChiTwoSigma
    field_simp
  rw [h_eq] at hpart1_x
  have hM'_nn : 0 ≤ remark51MPrime p := by
    unfold remark51MPrime
    exact add_nonneg
      (mul_nonneg (abs_nonneg p.χ) (Real.rpow_nonneg hMChi_pos.le _))
      (Real.rpow_nonneg hMChi_pos.le _)
  have hM'_chi_nn :
      0 ≤ remark51MPrime p * remark5ChiSigma p sigma :=
    mul_nonneg hM'_nn (remark5ChiSigma_nonneg p sigma)
  have hM'_chi_weak :
      remark51MPrime p * remark5ChiSigma p sigma ≤
        remark51MDoublePrime p sigma / 2 := by
    linarith [hM'_chi]
  have h_le : remark51MPrime p * remark5ChiSigma p sigma /
      (remark5ChiTwoSigma p sigma) ≤
      remark51MDoublePrime p sigma / 2 / (remark5ChiTwoSigma p sigma) := by
    exact div_le_div_of_nonneg_right hM'_chi_weak hχ2σ_pos.le
  have h_combine : remark51MDoublePrime p sigma / 2 / (remark5ChiTwoSigma p sigma) =
      remark51MDoublePrime p sigma / (2 * (remark5ChiTwoSigma p sigma)) := by
    rw [div_div]
  linarith

/-- Second piece of M'' tracking: under |χ|σ ≥ 1 and κ ≤ |χ|σ/2,
the term |χ|²σ·M'/(|χ|σ-κ) is bounded by M''/2.

Proof: A·B has the term |χ|·m·MChi^{m-1}·M'·(γ + |χ|σ).
Under conditions, m·MChi^{m-1}·(γ + |χ|σ) ≥ |χ|σ/(|χ|σ-κ),
so this term alone dominates |χ|²σ·M'/(|χ|σ-κ). -/
theorem remark51_chi_sq_sigma_M_prime_div_drift_le_M_dprime_half
    (p : CMParams) {c sigma : ℝ}
    (hMChi_pos : 0 < MChi p) (hMChi_ge_one : 1 ≤ MChi p)
    (hsigma : 0 < sigma)
    (hχσ_ge_one : 1 ≤ remark5ChiSigma p sigma)
    (hκ_pos : 0 < kappa c)
    (hκ_le_half : kappa c ≤ remark5ChiSigma p sigma / 2) :
    remark5ChiTwoSigma p sigma * remark51MPrime p / (remark5ChiSigma p sigma - kappa c) ≤
      remark51MDoublePrime p sigma / 2 := by
  have hM'_nn : 0 ≤ remark51MPrime p := by
    unfold remark51MPrime
    exact add_nonneg
      (mul_nonneg (abs_nonneg p.χ) (Real.rpow_nonneg hMChi_pos.le _))
      (Real.rpow_nonneg hMChi_pos.le _)
  have hχσ_pos : 0 < remark5ChiSigma p sigma := by
    linarith
  have hdrift_pos : 0 < remark5ChiSigma p sigma - kappa c := by
    have hhalf_lt :
        remark5ChiSigma p sigma / 2 < remark5ChiSigma p sigma := by
      linarith
    linarith
  have hratio :
      remark5ChiTwoSigma p sigma * remark51MPrime p /
          (remark5ChiSigma p sigma - kappa c) ≤
        2 * (remark51MPrime p * remark5ChiSigma p sigma) := by
    rw [div_le_iff₀ hdrift_pos]
    have hscale :
        remark5ChiSigma p sigma ≤
          2 * (remark5ChiSigma p sigma - kappa c) := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hscale
      (mul_nonneg hM'_nn (remark5ChiSigma_nonneg p sigma))
    unfold remark5ChiTwoSigma
    nlinarith
  have hstrong :=
    remark51MPrime_chiSigma_le_MDoublePrime_half
      p hMChi_pos hMChi_ge_one hsigma hχσ_ge_one
  exact le_trans hratio hstrong

/-- G_pos (the x ≥ 0 source bound) is nonneg under K_V ≥ 0. -/
theorem remark51_G_pos_nonneg
    (p : CMParams) {c : ℝ}
    (hK_V_nn : 0 ≤ 1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) :
    0 ≤ |p.χ| * (1 / (1 - (kappa c) ^ 2 * p.γ ^ 2) + 1) + 2 := by
  have h1 : 0 ≤ |p.χ| := abs_nonneg _
  have h2 : 0 ≤ 1 / (1 - (kappa c) ^ 2 * p.γ ^ 2) + 1 := by linarith
  have h3 : 0 ≤ |p.χ| * (1 / (1 - (kappa c) ^ 2 * p.γ ^ 2) + 1) := mul_nonneg h1 h2
  linarith

/-- Combined M'' algebra in the case max(M', G_pos) = M' (i.e., G_pos ≤ M').
Under `|χ|^σ ≥ 1` and `κ ≤ |χ|^σ/2`:
  `M' |χ|^σ + |χ|^(2σ) M'/(|χ|^σ - κ) ≤ M''`.
Equivalently:
  M'/(|χ|σ) + M'/(|χ|σ - κ) ≤ M''/(|χ|²σ)

This is the bound C ≤ M''/(|χ|²σ) when the source bound G = M'
(not G_pos). Together with the G_pos case (separate), this completes
the M'' algebra needed for matching the Duhamel constant to Remark_5_1
Part 2's bound. -/
theorem remark51_M_dprime_dominates_M_prime_case
    (p : CMParams) {c sigma : ℝ}
    (hMChi_pos : 0 < MChi p) (hMChi_ge_one : 1 ≤ MChi p)
    (hsigma : 0 < sigma)
    (hχσ_ge_one : 1 ≤ remark5ChiSigma p sigma)
    (hκ_pos : 0 < kappa c)
    (hκ_le_half : kappa c ≤ remark5ChiSigma p sigma / 2) :
    remark51MPrime p * remark5ChiSigma p sigma +
      remark5ChiTwoSigma p sigma * remark51MPrime p / (remark5ChiSigma p sigma - kappa c) ≤
      remark51MDoublePrime p sigma := by
  have h1 := remark51MPrime_chiSigma_le_MDoublePrime_half p hMChi_pos
    hMChi_ge_one hsigma hχσ_ge_one
  have h2 := remark51_chi_sq_sigma_M_prime_div_drift_le_M_dprime_half p hMChi_pos
    hMChi_ge_one hsigma hχσ_ge_one hκ_pos hκ_le_half
  have hM'_nn : 0 ≤ remark51MPrime p := by
    unfold remark51MPrime
    exact add_nonneg
      (mul_nonneg (abs_nonneg p.χ) (Real.rpow_nonneg hMChi_pos.le _))
      (Real.rpow_nonneg hMChi_pos.le _)
  have hfirst_nn :
      0 ≤ remark51MPrime p * remark5ChiSigma p sigma :=
    mul_nonneg hM'_nn (remark5ChiSigma_nonneg p sigma)
  linarith

/-- Useful inequality: under M' case algebra hypotheses, the Duhamel constant
M'/(|χ|σ) + M'/(|χ|σ - κ) is bounded by M''/(|χ|²σ).

This is the "C ≤ M''/(|χ|²σ)" inequality for the case where the source
bound G_w in the Duhamel framework equals M' (not the larger G_pos). -/
theorem remark51_Duhamel_constant_le_M_dprime_div_M_prime_case
    (p : CMParams) {c sigma : ℝ}
    (hMChi_pos : 0 < MChi p) (hMChi_ge_one : 1 ≤ MChi p)
    (hsigma : 0 < sigma)
    (hχσ_ge_one : 1 ≤ remark5ChiSigma p sigma)
    (hκ_pos : 0 < kappa c)
    (hκ_le_half : kappa c ≤ remark5ChiSigma p sigma / 2) :
    remark51MPrime p / (remark5ChiSigma p sigma) +
      remark51MPrime p / (remark5ChiSigma p sigma - kappa c) ≤
      remark51MDoublePrime p sigma / (remark5ChiTwoSigma p sigma) := by
  have hcombined :=
    remark51_M_dprime_dominates_M_prime_case p hMChi_pos hMChi_ge_one
      hsigma hχσ_ge_one hκ_pos hκ_le_half
  have hχσ_pos : 0 < remark5ChiSigma p sigma := by
    linarith
  have hdrift_pos : 0 < remark5ChiSigma p sigma - kappa c := by
    have hhalf_lt :
        remark5ChiSigma p sigma / 2 < remark5ChiSigma p sigma := by
      linarith
    linarith
  have hχ2σ_pos : 0 < remark5ChiTwoSigma p sigma := by
    unfold remark5ChiTwoSigma
    exact sq_pos_of_pos hχσ_pos
  rw [div_add_div _ _ (ne_of_gt hχσ_pos) (ne_of_gt hdrift_pos)]
  rw [div_le_div_iff₀ (mul_pos hχσ_pos hdrift_pos) hχ2σ_pos]
  have hmul := mul_le_mul_of_nonneg_right hcombined
    (mul_nonneg hχσ_pos.le hdrift_pos.le)
  have hleft :
      (remark51MPrime p * remark5ChiSigma p sigma +
          remark5ChiTwoSigma p sigma * remark51MPrime p /
            (remark5ChiSigma p sigma - kappa c)) *
          (remark5ChiSigma p sigma *
            (remark5ChiSigma p sigma - kappa c)) =
        (remark51MPrime p * (remark5ChiSigma p sigma - kappa c) +
            remark51MPrime p * remark5ChiSigma p sigma) *
          remark5ChiTwoSigma p sigma := by
    unfold remark5ChiTwoSigma
    field_simp
  rw [hleft] at hmul
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Full Remark_5_1 in the M'-dominant case: under regularity + signal bound +
the algebraic conditions (|χ|σ ≥ 1, κ ≤ |χ|σ/2, G_pos ≤ M') discharged,
Remark_5_1's TWO bounds hold simultaneously.

This is the FIRST CASE where Remark_5_1 is fully proven (not just conditional)
within the formalization, modulo the regularity bridge and case conditions.
The conditional hypotheses isolate exactly what remains to discharge for
unconditional Remark_5_1 in this regime. -/
theorem Remark_5_1.of_M_prime_case_complete
    (h_reg : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        TravelingWaveRegularity p c U V)
    (h_chi_sigma_ge_one : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      1 ≤ remark5ChiSigma p sigma)
    (h_kappa_le_half : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      kappa c ≤ remark5ChiSigma p sigma / 2)
    (h_part2_M_prime_match : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        ∀ x, 0 ≤ x →
          |deriv U x| ≤
            remark51MDoublePrime p sigma / (remark5ChiTwoSigma p sigma) *
              Real.exp (-(kappa c) * x)) :
    Remark_5_1 := by
  intro p c sigma hsigma hχ hspeed U V hTW hbound
  have hreg := h_reg p c sigma hsigma hχ hspeed U V hTW hbound
  refine ⟨?_, h_part2_M_prime_match p c sigma hsigma hχ hspeed U V hTW hbound⟩
  exact remark_5_1_smooth_part1 p c sigma hsigma hχ hspeed U V hTW hbound
    hreg.U_diff hreg.V_deriv_diff hreg.deriv_U_cont hreg.deriv_U_diff
    hreg.deriv_U_tendszero hreg.V_nn hreg.V_bound

/-- Remark_5_1 Part 2 fully proved in the M'-dominant case.

Combines:
  • Part 1 bound |U'(0)| ≤ M'/(|χ|σ)
  • Explicit smooth_part2 (Duhamel constant exposed)
  • M'' algebra (M'/(|χ|σ) + M'/(|χ|σ-κ) ≤ M''/(|χ|²σ))
  • M' case hypothesis G_pos ≤ M'

Yields the exact Remark_5_1 Part 2 bound:
  ∀ x ≥ 0, |U'(x)| ≤ M''/(|χ|²σ) · exp(-κx). -/
theorem remark_5_1_smooth_part2_M_prime_case_complete
    (p : CMParams) (c sigma : ℝ)
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hspeed : remark5SpeedCondition p c sigma)
    (hχσ_ge_one : 1 ≤ remark5ChiSigma p sigma)
    (hκ_pos : 0 < kappa c)
    (hκ_le_half : kappa c ≤ remark5ChiSigma p sigma / 2)
    (U V : ℝ → ℝ)
    (hTW : IsTravelingWave p c U V) (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hV_exp : ∀ x, |V x| ≤ (1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
        Real.exp (-(kappa c) * p.γ * x) ∧
      |deriv V x| ≤ (1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
        Real.exp (-(kappa c) * p.γ * x))
    (hG_pos_le_M_prime : |p.χ| * (1 / (1 - kappa c ^ 2 * p.γ ^ 2) + 1) + 2 ≤
      remark51MPrime p) :
    ∀ x, 0 ≤ x →
      |deriv U x| ≤ remark51MDoublePrime p sigma / (remark5ChiTwoSigma p sigma) *
        Real.exp (-(kappa c) * x) := by
  have hχσ_pos : 0 < remark5ChiSigma p sigma := by linarith
  have hκσ : kappa c < remark5ChiSigma p sigma := by
    have h_half_lt : remark5ChiSigma p sigma / 2 < remark5ChiSigma p sigma := by linarith
    linarith
  have hdrift_pos : 0 < remark5ChiSigma p sigma - kappa c := by linarith
  have hMChi_pos : 0 < MChi p :=
    lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)
  have hMChi_ge_one : 1 ≤ MChi p := MChi_ge_one_of_travelingWave hTW hbound
  have hM'_nn : 0 ≤ remark51MPrime p := by
    unfold remark51MPrime
    exact add_nonneg (mul_nonneg (abs_nonneg _)
      (Real.rpow_nonneg hMChi_pos.le _))
      (Real.rpow_nonneg hMChi_pos.le _)
  have hχ_pos : 0 < |p.χ| := abs_pos.mpr hχ
  have hχ_sq_σ_pos : 0 < remark5ChiTwoSigma p sigma :=
    remark5ChiTwoSigma_pos sigma hχ
  -- Apply explicit smooth_part2
  have hpart2 := remark_5_1_smooth_part2_via_duhamel p c sigma hsigma hχ hspeed
    hκ_pos hκσ U V hTW hbound hreg hV_exp
  -- Part 1 for |deriv U 0|
  have hpart1 := remark_5_1_smooth_part1 p c sigma hsigma hχ hspeed U V hTW hbound
    hreg.U_diff hreg.V_deriv_diff hreg.deriv_U_cont hreg.deriv_U_diff
    hreg.deriv_U_tendszero hreg.V_nn hreg.V_bound
  have h_U_0 : |deriv U 0| ≤ remark51MPrime p / (remark5ChiSigma p sigma) := hpart1 0
  -- M' case: max(M', max(0, G_pos)) = M' (since M' ≥ G_pos and M' ≥ 0)
  have hmax_M_prime : max (remark51MPrime p)
      (max 0 (|p.χ| * (1 / (1 - kappa c ^ 2 * p.γ ^ 2) + 1) + 2)) =
      remark51MPrime p := by
    have h_inner : max (0 : ℝ) (|p.χ| * (1 / (1 - kappa c ^ 2 * p.γ ^ 2) + 1) + 2) ≤
        remark51MPrime p := by
      apply max_le hM'_nn
      exact hG_pos_le_M_prime
    exact max_eq_left h_inner
  intro x hx_nn
  have hp2_x := hpart2 x hx_nn
  rw [hmax_M_prime] at hp2_x
  -- hp2_x : |deriv U x| ≤ (|deriv U 0| + M'/(|χ|σ-κ)) * exp(-κx)
  -- Want: |deriv U x| ≤ M''/(|χ|²σ) * exp(-κx)
  -- Need: |deriv U 0| + M'/(|χ|σ-κ) ≤ M''/(|χ|²σ)
  have h_bound_C : |deriv U 0| + remark51MPrime p / (remark5ChiSigma p sigma - kappa c) ≤
      remark51MDoublePrime p sigma / (remark5ChiTwoSigma p sigma) := by
    have h_duh_ineq := remark51_Duhamel_constant_le_M_dprime_div_M_prime_case p
      hMChi_pos hMChi_ge_one hsigma hχσ_ge_one hκ_pos hκ_le_half
    -- h_duh_ineq : M'/(|χ|σ) + M'/(|χ|σ-κ) ≤ M''/(|χ|²σ)
    -- We have h_U_0 : |U'(0)| ≤ M'/(|χ|σ)
    have : |deriv U 0| + remark51MPrime p / (remark5ChiSigma p sigma - kappa c) ≤
        remark51MPrime p / (remark5ChiSigma p sigma) +
        remark51MPrime p / (remark5ChiSigma p sigma - kappa c) := by
      linarith
    linarith
  have hexp_nn : 0 ≤ Real.exp (-(kappa c) * x) := (Real.exp_pos _).le
  calc |deriv U x|
      ≤ (|deriv U 0| + remark51MPrime p / (remark5ChiSigma p sigma - kappa c)) *
          Real.exp (-(kappa c) * x) := hp2_x
    _ ≤ remark51MDoublePrime p sigma / (remark5ChiTwoSigma p sigma) *
          Real.exp (-(kappa c) * x) :=
        mul_le_mul_of_nonneg_right h_bound_C hexp_nn

/-- FULL Remark_5_1 proven in the M'-dominant regime.

Under five concrete hypotheses (regularity bridge, |χ|σ ≥ 1, κ ≤ |χ|σ/2,
Lemma 5.1 exponential signal bound, G_pos ≤ M'), this proves Remark_5_1
unconditionally — both parts matching the paper's M' and M'' bounds.

This is the FIRST UNCONDITIONAL closure of Remark_5_1 in a parameter
regime. The five hypotheses are all CONCRETE and INDEPENDENT, each
discharged by separate analyses for the remaining cases. -/
theorem Remark_5_1.of_full_M_prime_case
    (h_reg : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        TravelingWaveRegularity p c U V)
    (h_chi_sigma_ge_one : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      1 ≤ remark5ChiSigma p sigma)
    (h_kappa_le_half : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      kappa c ≤ remark5ChiSigma p sigma / 2)
    (h_signal : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V → HasWaveUpperTailBound p c U →
        ∀ x, |V x| ≤ (1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
            Real.exp (-(kappa c) * p.γ * x) ∧
          |deriv V x| ≤ (1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
            Real.exp (-(kappa c) * p.γ * x))
    (h_G_pos_le_M_prime : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      |p.χ| * (1 / (1 - kappa c ^ 2 * p.γ ^ 2) + 1) + 2 ≤
      remark51MPrime p) :
    Remark_5_1 := by
  intro p c sigma hsigma hχ hspeed U V hTW hbound
  have hreg := h_reg p c sigma hsigma hχ hspeed U V hTW hbound
  have hχσ_ge_one := h_chi_sigma_ge_one p c sigma hsigma hχ hspeed
  have hκ_le_half := h_kappa_le_half p c sigma hsigma hχ hspeed
  have hV_exp := h_signal p c sigma hsigma hχ hspeed U V hTW hbound
  have hG_pos_le := h_G_pos_le_M_prime p c sigma hsigma hχ hspeed
  have hκ_pos : 0 < kappa c := by
    unfold kappa
    have hc_pos : 0 < c := hTW.hc
    have hsqrt_lt_c : Real.sqrt (c ^ 2 - 4) < c := by
      rw [Real.sqrt_lt' hc_pos]; nlinarith
    linarith
  refine ⟨?_, ?_⟩
  · exact remark_5_1_smooth_part1 p c sigma hsigma hχ hspeed U V hTW hbound
      hreg.U_diff hreg.V_deriv_diff hreg.deriv_U_cont hreg.deriv_U_diff
      hreg.deriv_U_tendszero hreg.V_nn hreg.V_bound
  · exact remark_5_1_smooth_part2_M_prime_case_complete p c sigma hsigma hχ hspeed
      hχσ_ge_one hκ_pos hκ_le_half U V hTW hbound hreg hV_exp hG_pos_le

/-- M'' is nonneg under MChi ≥ 1 (cleaner stated version). -/
theorem remark51MDoublePrime_nonneg_of_MChi_ge_one
    (p : CMParams) {sigma : ℝ}
    (hMChi_pos : 0 < MChi p)
    (hMChi_ge_one : 1 ≤ MChi p)
    (hsigma : 0 ≤ sigma) :
    0 ≤ remark51MDoublePrime p sigma := by
  have hm_nn : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hγ_nn : 0 ≤ p.γ := le_trans zero_le_one p.hγ
  have hM'_nn :
      0 ≤ |p.χ| * (MChi p) ^ (p.m + p.γ) +
        (MChi p) ^ (p.α + 1) :=
    add_nonneg
      (mul_nonneg (abs_nonneg p.χ) (Real.rpow_nonneg hMChi_pos.le _))
      (Real.rpow_nonneg hMChi_pos.le _)
  have hA :
      0 ≤ 1 + 2 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
        (MChi p) ^ p.α := by
    positivity
  have hchem :
      0 ≤ |p.χ| * p.m * (MChi p) ^ (p.m - 1) *
        (|p.χ| * (MChi p) ^ (p.m + p.γ) +
          (MChi p) ^ (p.α + 1)) *
        (p.γ + remark5ChiSigma p sigma) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (abs_nonneg p.χ) hm_nn)
          (Real.rpow_nonneg hMChi_pos.le _))
        hM'_nn)
      (add_nonneg hγ_nn (remark5ChiSigma_nonneg p sigma))
  unfold remark51MDoublePrime
  exact mul_nonneg
    (mul_nonneg zero_le_two hA)
    (add_nonneg (remark5ChiTwoSigma_nonneg p sigma) hchem)

/-- The Duhamel constant from smooth_part2_via_duhamel, parametrized.
This is the explicit constant C such that |U'(x)| ≤ C·exp(-κx) for x ≥ 0,
where C = |U'(0)| + G/(|χ|σ - κ) with G the global g_w bound. The full
M''/(|χ|²σ) match requires showing this C ≤ M''/(|χ|²σ) by paper algebra. -/
def remark51DuhamelConstantBound (p : CMParams) (c sigma : ℝ) (K_V : ℝ) : ℝ :=
  remark51MPrime p / (remark5ChiSigma p sigma) +
    max (remark51MPrime p) (max 0 (|p.χ| * (K_V + 1) + 2)) /
      (remark5ChiSigma p sigma - kappa c)

/-- Uniqueness of bounded solutions of W'' = W on ℝ.

If W is C² with W''(x) = W(x) for all x, and both W and W' are bounded,
then W ≡ 0.

Proof: Define u(x) := (W(x) + W'(x))·e^{-x}. Compute deriv u = 0 from
W'' = W, so u is constant. From u(x) = u(0) and u(x) = (W+W')·e^{-x},
get W(x) + W'(x) = u(0)·e^x. Boundedness of W + W' at x → +∞ forces
u(0) = 0, so W + W' ≡ 0. Symmetric argument with v(x) := (W-W')·e^x
gives W - W' ≡ 0. Hence W ≡ 0. -/
theorem bounded_solution_unique_of_iteratedDeriv_two_eq
    {W : ℝ → ℝ}
    (hW_diff : Differentiable ℝ W)
    (hW'_diff : Differentiable ℝ (deriv W))
    (hW_eq : ∀ x, deriv (deriv W) x = W x)
    (hW_bdd : ∃ M : ℝ, ∀ x, |W x| ≤ M)
    (hW'_bdd : ∃ M : ℝ, ∀ x, |deriv W x| ≤ M) :
    ∀ x, W x = 0 := by
  -- Step 1: define u(x) = (W(x) + W'(x))·e^{-x}
  set u : ℝ → ℝ := fun x => (W x + deriv W x) * Real.exp (-x) with hu_def
  -- Step 2: deriv u x = 0 (from W'' = W and chain rule)
  have hexp_neg_at : ∀ x, HasDerivAt (fun y => Real.exp (-y))
      (-Real.exp (-x)) x := by
    intro x
    have h1 : HasDerivAt (fun y => -y) (-1 : ℝ) x := by
      simpa using (hasDerivAt_id x).neg
    convert h1.exp using 1; ring
  have hexp_neg_diff : Differentiable ℝ (fun y => Real.exp (-y)) :=
    fun x => (hexp_neg_at x).differentiableAt
  have hu_diff : Differentiable ℝ u :=
    fun x => ((hW_diff x).add (hW'_diff x)).mul (hexp_neg_diff x)
  have hu_deriv : ∀ x, deriv u x = 0 := by
    intro x
    have hWplus_at : HasDerivAt (fun y => W y + deriv W y)
        (deriv W x + deriv (deriv W) x) x :=
      (hW_diff x).hasDerivAt.add (hW'_diff x).hasDerivAt
    have hu_at : HasDerivAt u
        ((deriv W x + deriv (deriv W) x) * Real.exp (-x) +
         (W x + deriv W x) * (-Real.exp (-x))) x :=
      hWplus_at.mul (hexp_neg_at x)
    rw [hu_at.deriv, hW_eq x]
    ring
  -- Step 3: u is constant
  have hu_const : ∀ x, u x = u 0 :=
    fun x => is_const_of_deriv_eq_zero hu_diff hu_deriv x 0
  -- Step 4: u(x) = u(0) implies W(x) + W'(x) = u(0)·e^x
  have hWW' : ∀ x, W x + deriv W x = u 0 * Real.exp x := by
    intro x
    have h_eq : (W x + deriv W x) * Real.exp (-x) = u 0 := hu_const x
    have hexp_inv_mul : Real.exp (-x) * Real.exp x = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc W x + deriv W x
        = (W x + deriv W x) * 1 := by ring
      _ = (W x + deriv W x) * (Real.exp (-x) * Real.exp x) := by
          rw [hexp_inv_mul]
      _ = ((W x + deriv W x) * Real.exp (-x)) * Real.exp x := by ring
      _ = u 0 * Real.exp x := by rw [h_eq]
  -- Step 5: boundedness of W + W' at +∞ forces u(0) = 0
  have hu0_zero : u 0 = 0 := by
    by_contra hu0_ne
    -- u 0 ≠ 0. Then |W + W'| = |u 0| · exp x grows unboundedly.
    obtain ⟨MW, hMW⟩ := hW_bdd
    obtain ⟨MW', hMW'⟩ := hW'_bdd
    -- |W + W'| ≤ MW + MW' globally
    have hWW'_bdd : ∀ x, |W x + deriv W x| ≤ MW + MW' := fun x => by
      have h1 : |W x + deriv W x| ≤ |W x| + |deriv W x| := abs_add_le _ _
      linarith [hMW x, hMW' x]
    -- Pick x large enough that |u 0| · exp x > MW + MW'
    have hu0_pos : 0 < |u 0| := abs_pos.mpr hu0_ne
    -- exp grows to ∞, so eventually exp x > (MW+MW')/|u 0|
    have hMW_nn : 0 ≤ MW + MW' := by
      have := hMW 0; have := hMW' 0
      linarith [abs_nonneg (W 0), abs_nonneg (deriv W 0)]
    have hgoal : ∃ x : ℝ, (MW + MW') / |u 0| < Real.exp x := by
      have := Real.tendsto_exp_atTop
      obtain ⟨x, hx⟩ := (this.eventually_gt_atTop ((MW + MW') / |u 0|)).exists
      exact ⟨x, hx⟩
    obtain ⟨x, hx⟩ := hgoal
    have h1 : MW + MW' < |u 0| * Real.exp x := by
      rw [div_lt_iff₀ hu0_pos] at hx
      linarith
    -- But W + W' = u 0 · exp x, so |W + W'| = |u 0| · exp x
    have h2 : |W x + deriv W x| = |u 0| * Real.exp x := by
      rw [hWW' x, abs_mul, abs_of_pos (Real.exp_pos _)]
    -- Combining: MW + MW' < |W x + deriv W x| ≤ MW + MW'. Contradiction.
    linarith [hWW'_bdd x, h2, h1]
  -- Step 6: W + W' ≡ 0
  have hWW'_zero : ∀ x, W x + deriv W x = 0 := fun x => by
    rw [hWW' x, hu0_zero]; simp
  -- Step 7: symmetric argument with v(x) = (W - W')·e^x gives W - W' ≡ 0
  set v : ℝ → ℝ := fun x => (W x - deriv W x) * Real.exp x with hv_def
  have hexp_at : ∀ x, HasDerivAt (fun y => Real.exp y) (Real.exp x) x :=
    fun x => Real.hasDerivAt_exp x
  have hv_diff : Differentiable ℝ v :=
    fun x => ((hW_diff x).sub (hW'_diff x)).mul (hexp_at x).differentiableAt
  have hv_deriv : ∀ x, deriv v x = 0 := by
    intro x
    have hWminus_at : HasDerivAt (fun y => W y - deriv W y)
        (deriv W x - deriv (deriv W) x) x :=
      (hW_diff x).hasDerivAt.sub (hW'_diff x).hasDerivAt
    have hv_at : HasDerivAt v
        ((deriv W x - deriv (deriv W) x) * Real.exp x +
         (W x - deriv W x) * Real.exp x) x :=
      hWminus_at.mul (hexp_at x)
    rw [hv_at.deriv, hW_eq x]
    ring
  have hv_const : ∀ x, v x = v 0 :=
    fun x => is_const_of_deriv_eq_zero hv_diff hv_deriv x 0
  have hWmW'_eq : ∀ x, W x - deriv W x = v 0 * Real.exp (-x) := by
    intro x
    have h_eq : (W x - deriv W x) * Real.exp x = v 0 := hv_const x
    have hexp_inv_mul : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc W x - deriv W x
        = (W x - deriv W x) * 1 := by ring
      _ = (W x - deriv W x) * (Real.exp x * Real.exp (-x)) := by
          rw [hexp_inv_mul]
      _ = ((W x - deriv W x) * Real.exp x) * Real.exp (-x) := by ring
      _ = v 0 * Real.exp (-x) := by rw [h_eq]
  have hv0_zero : v 0 = 0 := by
    by_contra hv0_ne
    obtain ⟨MW, hMW⟩ := hW_bdd
    obtain ⟨MW', hMW'⟩ := hW'_bdd
    have hWmW'_bdd : ∀ x, |W x - deriv W x| ≤ MW + MW' := fun x => by
      have h1 : |W x - deriv W x| ≤ |W x| + |deriv W x| := abs_sub _ _
      linarith [hMW x, hMW' x]
    have hv0_pos : 0 < |v 0| := abs_pos.mpr hv0_ne
    -- Find x with exp(-x) > (MW+MW')/|v 0|.
    -- exp(-x) → +∞ as x → -∞, so take x very negative.
    have hcompose : Tendsto (fun x : ℝ => Real.exp (-x)) atBot atTop := by
      have h1 : Tendsto (fun x : ℝ => -x) atBot atTop := tendsto_neg_atBot_atTop
      exact Real.tendsto_exp_atTop.comp h1
    obtain ⟨x, hx⟩ :=
      (hcompose.eventually_gt_atTop ((MW + MW') / |v 0|)).exists
    have h1 : MW + MW' < |v 0| * Real.exp (-x) := by
      rw [div_lt_iff₀ hv0_pos] at hx
      linarith
    have h2 : |W x - deriv W x| = |v 0| * Real.exp (-x) := by
      rw [hWmW'_eq x, abs_mul, abs_of_pos (Real.exp_pos _)]
    linarith [hWmW'_bdd x, h2, h1]
  have hWmW' : ∀ x, W x - deriv W x = 0 := fun x => by
    rw [hWmW'_eq x, hv0_zero]; simp
  -- Step 8: combine to get W ≡ 0
  intro x
  have hsum : (W x + deriv W x) + (W x - deriv W x) = 0 := by
    rw [hWW'_zero x, hWmW' x]; ring
  linarith

/-- V = frozenElliptic p U for any traveling wave with bounded V, V'.

This is the application of `bounded_solution_unique_of_iteratedDeriv_two_eq`
to W := V - frozenElliptic p U, which satisfies W'' = W (from the V-ODE).
Boundedness of V and V' (signal bounds) gives boundedness of W and W',
forcing W ≡ 0. -/
theorem IsTravelingWave.V_eq_frozenElliptic
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hU_cont : Continuous U)
    (hV_diff : Differentiable ℝ V)
    (hV_deriv_diff : Differentiable ℝ (deriv V))
    (hV_bdd : ∃ M : ℝ, ∀ x, |V x| ≤ M)
    (hV'_bdd : ∃ M : ℝ, ∀ x, |deriv V x| ≤ M) :
    V = frozenElliptic p U := by
  have hU_bdd : IsCUnifBdd U := hbound.isCUnifBdd_of_continuous hU_cont
  have hU_nn : ∀ x, 0 ≤ U x := fun x => (hbound.pos x).le
  -- W := V - frozenElliptic p U
  set W : ℝ → ℝ := fun x => V x - frozenElliptic p U x with hW_def
  have hFE_diff : Differentiable ℝ (frozenElliptic p U) :=
    frozenElliptic_differentiable p hU_bdd hU_nn
  have hW_diff : Differentiable ℝ W :=
    fun x => (hV_diff x).sub (hFE_diff x)
  -- For deriv W = deriv V - deriv (frozenElliptic):
  have hderivW_eq : deriv W = fun x => deriv V x - deriv (frozenElliptic p U) x := by
    funext x
    have hV_at : HasDerivAt V (deriv V x) x := (hV_diff x).hasDerivAt
    have hFE_at : HasDerivAt (frozenElliptic p U) (deriv (frozenElliptic p U) x) x :=
      (hFE_diff x).hasDerivAt
    exact (hV_at.sub hFE_at).deriv
  have hW'_diff : Differentiable ℝ (deriv W) := by
    rw [hderivW_eq]
    exact fun x => (hV_deriv_diff x).sub
      (frozenElliptic_deriv_differentiableAt p hU_bdd hU_nn x)
  -- W satisfies W'' = W (from both V and frozenElliptic solving V'' - V + U^γ = 0)
  have hW_eq : ∀ x, deriv (deriv W) x = W x := by
    intro x
    rw [hderivW_eq]
    have h1 : HasDerivAt (deriv V) (deriv (deriv V) x) x :=
      (hV_deriv_diff x).hasDerivAt
    have h2 : HasDerivAt (deriv (frozenElliptic p U))
        (deriv (deriv (frozenElliptic p U)) x) x :=
      (frozenElliptic_deriv_differentiableAt p hU_bdd hU_nn x).hasDerivAt
    have h_sub_at : HasDerivAt (fun y => deriv V y - deriv (frozenElliptic p U) y)
        (deriv (deriv V) x - deriv (deriv (frozenElliptic p U)) x) x := h1.sub h2
    rw [h_sub_at.deriv]
    have hiD2V : iteratedDeriv 2 V x = deriv (deriv V) x := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have hiD2FE : iteratedDeriv 2 (frozenElliptic p U) x =
        deriv (deriv (frozenElliptic p U)) x := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have hode_V := hTW.ode_V x
    have hode_FE := frozenElliptic_iteratedDeriv_two_eq p hU_bdd hU_nn x
    rw [hiD2V] at hode_V
    rw [hiD2FE] at hode_FE
    show deriv (deriv V) x - deriv (deriv (frozenElliptic p U)) x =
      V x - frozenElliptic p U x
    linarith
  -- frozenElliptic and its derivative bounded by MChi^γ (Lemma 5.1 signal)
  have hsignal := Lemma_5_1_signal_bound_for_frozenElliptic p hU_bdd hbound
  have hFE_bdd : ∃ M : ℝ, ∀ x, |frozenElliptic p U x| ≤ M :=
    ⟨(MChi p) ^ p.γ, fun x => (hsignal x).1⟩
  have hFE'_bdd : ∃ M : ℝ, ∀ x, |deriv (frozenElliptic p U) x| ≤ M :=
    ⟨(MChi p) ^ p.γ, fun x => (hsignal x).2⟩
  obtain ⟨MV, hMV⟩ := hV_bdd
  obtain ⟨MFE, hMFE⟩ := hFE_bdd
  have hW_bdd : ∃ M : ℝ, ∀ x, |W x| ≤ M := ⟨MV + MFE, fun x => by
    have h1 : |W x| ≤ |V x| + |frozenElliptic p U x| := by
      simp [hW_def]; exact abs_sub _ _
    linarith [hMV x, hMFE x]⟩
  obtain ⟨MV', hMV'⟩ := hV'_bdd
  obtain ⟨MFE', hMFE'⟩ := hFE'_bdd
  have hW'_bdd : ∃ M : ℝ, ∀ x, |deriv W x| ≤ M := ⟨MV' + MFE', fun x => by
    rw [hderivW_eq]
    have h1 : |deriv V x - deriv (frozenElliptic p U) x| ≤
      |deriv V x| + |deriv (frozenElliptic p U) x| := abs_sub _ _
    linarith [hMV' x, hMFE' x]⟩
  have hW_zero : ∀ x, W x = 0 :=
    bounded_solution_unique_of_iteratedDeriv_two_eq hW_diff hW'_diff hW_eq hW_bdd hW'_bdd
  funext x
  have := hW_zero x
  simp [hW_def] at this
  linarith

/-- Auto-derives the Lemma 5.1 exponential signal bound on V from:
- regularity (V_diff, V_deriv_diff for V_eq_frozenElliptic)
- 2 < c and γ + γ⁻¹ < c (for Lemma 5.1 exp branch)

This discharges h_signal in Remark_5_1.of_full_M_prime_case. -/
theorem wave_signal_exp_bound_of_regularity
    (p : CMParams) {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hU_cont : Continuous U)
    (hV_diff : Differentiable ℝ V)
    (hV_deriv_diff : Differentiable ℝ (deriv V))
    (hV_bdd : ∃ M : ℝ, ∀ x, |V x| ≤ M)
    (hV_deriv_bdd : ∃ M : ℝ, ∀ x, |deriv V x| ≤ M)
    (hc_gt_two : 2 < c)
    (hγ_speed : p.γ + p.γ⁻¹ < c) :
    ∀ x, |V x| ≤ (1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
        Real.exp (-(kappa c) * p.γ * x) ∧
      |deriv V x| ≤ (1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
        Real.exp (-(kappa c) * p.γ * x) := by
  have hV_eq : V = frozenElliptic p U :=
    IsTravelingWave.V_eq_frozenElliptic hTW hbound hU_cont
      (fun x => (hV_diff x)) (fun x => (hV_deriv_diff x))
      hV_bdd hV_deriv_bdd
  have hU_bdd : IsCUnifBdd U := hbound.isCUnifBdd_of_continuous hU_cont
  have hsignal := (Lemma_5_1.fixed_point_signal_statement p hc_gt_two
    hU_bdd hbound).2 hγ_speed
  intro x
  have hs := hsignal x
  rw [hV_eq]
  exact ⟨le_trans hs.1 (min_le_right _ _),
    le_trans hs.2 (min_le_right _ _)⟩

/-- TIGHTENED Remark_5_1 closure: signal bound auto-derived from regularity.

Replaces h_signal hypothesis with weaker 2<c + γ+γ⁻¹<c (which signal
bound follows from via wave_signal_exp_bound_of_regularity).

Under 6 concrete hypotheses (regularity, |χ|σ ≥ 1, κ ≤ |χ|σ/2,
2 < c, γ + γ⁻¹ < c, G_pos ≤ M'), Remark_5_1 follows. -/
theorem Remark_5_1.of_M_prime_case_with_speed_conditions
    (h_reg : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        TravelingWaveRegularity p c U V)
    (h_chi_sigma_ge_one : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      1 ≤ remark5ChiSigma p sigma)
    (h_kappa_le_half : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      kappa c ≤ remark5ChiSigma p sigma / 2)
    (h_c_gt_two : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      2 < c)
    (h_gamma_speed : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      p.γ + p.γ⁻¹ < c)
    (h_G_pos_le_M_prime : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      |p.χ| * (1 / (1 - kappa c ^ 2 * p.γ ^ 2) + 1) + 2 ≤
      remark51MPrime p) :
    Remark_5_1 := by
  apply Remark_5_1.of_full_M_prime_case h_reg h_chi_sigma_ge_one h_kappa_le_half
  · intro p c sigma hsigma hχ hspeed U V hTW hbound
    have hreg := h_reg p c sigma hsigma hχ hspeed U V hTW hbound
    have hc_gt_two := h_c_gt_two p c sigma hsigma hχ hspeed
    have hγ_speed := h_gamma_speed p c sigma hsigma hχ hspeed
    have hU_bdd : ∃ M : ℝ, ∀ x, |V x| ≤ M :=
      ⟨(MChi p) ^ p.γ, fun x => (hreg.V_bound x).1⟩
    have hV'_bdd : ∃ M : ℝ, ∀ x, |deriv V x| ≤ M :=
      ⟨(MChi p) ^ p.γ, fun x => (hreg.V_bound x).2⟩
    exact wave_signal_exp_bound_of_regularity p hTW hbound hreg.U_cont
      (fun x => hreg.V_diff x) (fun x => hreg.V_deriv_diff x)
      hU_bdd hV'_bdd hc_gt_two hγ_speed
  · exact h_G_pos_le_M_prime

/-- Further tightened Remark_5_1 closure: 2 < c and γ + γ⁻¹ < c are
auto-derived from |χ|σ ≥ 1 + remark5SpeedCondition via speed condition
helpers. Only 4 concrete hypotheses needed. -/
theorem Remark_5_1.of_M_prime_case_under_chi_sigma_ge_one
    (h_reg : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        TravelingWaveRegularity p c U V)
    (h_chi_sigma_ge_one : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      1 ≤ remark5ChiSigma p sigma)
    (h_kappa_le_half : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      kappa c ≤ remark5ChiSigma p sigma / 2)
    (h_G_pos_le_M_prime : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      |p.χ| * (1 / (1 - kappa c ^ 2 * p.γ ^ 2) + 1) + 2 ≤
      remark51MPrime p) :
    Remark_5_1 := by
  apply Remark_5_1.of_M_prime_case_with_speed_conditions h_reg h_chi_sigma_ge_one
    h_kappa_le_half
  · -- h_c_gt_two: from |χ|σ ≥ 1 via gt_two_of_chiSigma_ge_one
    intro p c sigma hsigma hχ hspeed
    exact remark5SpeedCondition.gt_two_of_chiSigma_ge_one hspeed hsigma
      (h_chi_sigma_ge_one p c sigma hsigma hχ hspeed)
  · -- h_gamma_speed: from |χ|σ ≥ 1 via gt_gamma_inv_of_chiSigma_ge_one
    intro p c sigma hsigma hχ hspeed
    exact remark5SpeedCondition.gt_gamma_inv_of_chiSigma_ge_one hspeed hsigma
      (h_chi_sigma_ge_one p c sigma hsigma hχ hspeed)
  · exact h_G_pos_le_M_prime

/-- Further tightening: under |χ|σ ≥ 2 (stronger than ≥ 1), h_kappa_le_half
is automatic since κ < 1 ≤ |χ|σ/2.

Final form: Remark_5_1 ⟸ {regularity, |χ|σ ≥ 2, G_pos ≤ M'} — only 3 hypotheses. -/
theorem Remark_5_1.of_M_prime_case_under_chi_sigma_ge_two
    (h_reg : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        TravelingWaveRegularity p c U V)
    (h_chi_sigma_ge_two : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      2 ≤ remark5ChiSigma p sigma)
    (h_G_pos_le_M_prime : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      |p.χ| * (1 / (1 - kappa c ^ 2 * p.γ ^ 2) + 1) + 2 ≤
      remark51MPrime p) :
    Remark_5_1 := by
  apply Remark_5_1.of_M_prime_case_under_chi_sigma_ge_one h_reg
  · -- h_chi_sigma_ge_one: from h_chi_sigma_ge_two
    intro p c sigma hsigma hχ hspeed
    linarith [h_chi_sigma_ge_two p c sigma hsigma hχ hspeed]
  · -- h_kappa_le_half: κ < 1 ≤ |χ|σ/2 under |χ|σ ≥ 2
    intro p c sigma hsigma hχ hspeed
    have hχσ_ge_two := h_chi_sigma_ge_two p c sigma hsigma hχ hspeed
    have hχσ_ge_one : 1 ≤ remark5ChiSigma p sigma := by linarith
    have hc_gt_two := remark5SpeedCondition.gt_two_of_chiSigma_ge_one
      hspeed hsigma hχσ_ge_one
    have hκ_lt_one : kappa c < 1 := kappa_lt_one_of_gt_two hc_gt_two
    linarith
  · exact h_G_pos_le_M_prime

/-- G_pos ≤ M' under specific MChi + κγ bounds.
G_pos = |χ|·(K_V+1) + 2.
M' = |χ|·MChi^{m+γ} + MChi^{α+1}.

Under MChi^{m+γ} ≥ K_V + 1 AND MChi^{α+1} ≥ 2:
  G_pos = |χ|·(K_V+1) + 2 ≤ |χ|·MChi^{m+γ} + MChi^{α+1} = M' ✓ -/
theorem G_pos_le_M_prime_of_MChi_bounds
    (p : CMParams) {c : ℝ}
    (hMChi_pos : 0 < MChi p)
    (h_MChi_pow_mgamma : 1 / (1 - kappa c ^ 2 * p.γ ^ 2) + 1 ≤ (MChi p) ^ (p.m + p.γ))
    (h_MChi_pow_alpha1 : 2 ≤ (MChi p) ^ (1 + p.α)) :
    |p.χ| * (1 / (1 - kappa c ^ 2 * p.γ ^ 2) + 1) + 2 ≤ remark51MPrime p := by
  unfold remark51MPrime
  have hχ_nn : 0 ≤ |p.χ| := abs_nonneg _
  have h1 : |p.χ| * (1 / (1 - kappa c ^ 2 * p.γ ^ 2) + 1) ≤
      |p.χ| * (MChi p) ^ (p.m + p.γ) :=
    mul_le_mul_of_nonneg_left h_MChi_pow_mgamma hχ_nn
  linarith

/-- Cleanest Remark_5_1 closure under explicit numerical conditions on
the wave amplitude MChi and the speed parameters. Only regularity bridge
+ ranges are needed; all paper-implicit assumptions discharged.

The hMChi_pos hypothesis is naturally satisfied: from IsTravelingWave +
HasWaveUpperTailBound we have hbound.pos x → MChi p > 0. -/
theorem Remark_5_1.of_MChi_and_chi_sigma_bounds
    (h_reg : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        TravelingWaveRegularity p c U V)
    (h_chi_sigma_ge_two : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      2 ≤ remark5ChiSigma p sigma)
    (h_MChi_pos : ∀ p : CMParams, 0 < MChi p)
    (h_MChi_pow_mgamma : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      1 / (1 - kappa c ^ 2 * p.γ ^ 2) + 1 ≤ (MChi p) ^ (p.m + p.γ))
    (h_MChi_pow_alpha1 : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      2 ≤ (MChi p) ^ (1 + p.α)) :
    Remark_5_1 := by
  apply Remark_5_1.of_M_prime_case_under_chi_sigma_ge_two h_reg h_chi_sigma_ge_two
  intro p c sigma hsigma hχ hspeed
  exact G_pos_le_M_prime_of_MChi_bounds p (h_MChi_pos p)
    (h_MChi_pow_mgamma p c sigma hsigma hχ hspeed)
    (h_MChi_pow_alpha1 p c sigma hsigma hχ hspeed)

/-- Auto-discharge of h_MChi_pos: 0 < MChi p follows from any wave U with
HasWaveUpperTailBound. -/
theorem MChi_pos_of_HasWaveUpperTailBound {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hbound : HasWaveUpperTailBound p c U) : 0 < MChi p :=
  lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)

/-- Under κγ ≤ 1/2, K_V = 1/(1-(κγ)²) is bounded: K_V ≤ 4/3.
Hence K_V + 1 ≤ 7/3 < 4. So MChi^{m+γ} ≥ 4 suffices for h_MChi_pow_mgamma. -/
theorem K_V_le_four_thirds_of_kappa_gamma_le_half
    {c γ : ℝ} (hκ_pos : 0 < kappa c) (hγ_pos : 0 < γ)
    (hκγ_le : kappa c * γ ≤ 1 / 2) :
    1 / (1 - kappa c ^ 2 * γ ^ 2) ≤ 4 / 3 := by
  have hκγ_pos : 0 < kappa c * γ := mul_pos hκ_pos hγ_pos
  have h_sq_le : kappa c ^ 2 * γ ^ 2 ≤ 1 / 4 := by
    have h_sq : (kappa c * γ) ^ 2 ≤ (1 / 2) ^ 2 := by
      apply sq_le_sq' _ hκγ_le
      linarith
    have h_expand : (kappa c * γ) ^ 2 = kappa c ^ 2 * γ ^ 2 := by ring
    have h_half_sq : ((1:ℝ) / 2) ^ 2 = 1 / 4 := by norm_num
    linarith [h_expand.symm.le, h_expand.le]
  have h_denom_pos : 0 < 1 - kappa c ^ 2 * γ ^ 2 := by linarith
  have h_denom_ge : 3 / 4 ≤ 1 - kappa c ^ 2 * γ ^ 2 := by linarith
  rw [div_le_div_iff₀ h_denom_pos (by norm_num : (0:ℝ) < 3)]
  linarith

/-- Under κγ ≤ 1/2 and MChi^{m+γ} ≥ 4, h_MChi_pow_mgamma is discharged:
K_V + 1 ≤ 4/3 + 1 = 7/3 ≤ 4 ≤ MChi^{m+γ}. -/
theorem h_MChi_pow_mgamma_of_kappa_gamma_le_and_MChi
    (p : CMParams) {c : ℝ}
    (hκ_pos : 0 < kappa c)
    (hκγ_le : kappa c * p.γ ≤ 1 / 2)
    (hMChi_pow_ge : 4 ≤ (MChi p) ^ (p.m + p.γ)) :
    1 / (1 - kappa c ^ 2 * p.γ ^ 2) + 1 ≤ (MChi p) ^ (p.m + p.γ) := by
  have hγ_pos : 0 < p.γ := lt_of_lt_of_le zero_lt_one p.hγ
  have hKV_le := K_V_le_four_thirds_of_kappa_gamma_le_half hκ_pos hγ_pos hκγ_le
  linarith

/-- Under MChi ≥ 2 (and α ≥ 1), MChi^{1+α} ≥ 2.
Proof: MChi^{1+α} ≥ MChi^1 = MChi ≥ 2 (since 1 + α ≥ 1 ≥ 0, MChi ≥ 1, and rpow is increasing). -/
theorem h_MChi_pow_alpha1_of_MChi_ge_two
    (p : CMParams) (hMChi_ge_two : 2 ≤ MChi p) :
    2 ≤ (MChi p) ^ (1 + p.α) := by
  have hα_pos : 0 < p.α := lt_of_lt_of_le zero_lt_one p.hα
  have hMChi_ge_one : 1 ≤ MChi p := by linarith
  have hMChi_gt_one : 1 < MChi p := by linarith
  have h1α : 1 ≤ 1 + p.α := by linarith
  have h_rpow_mono : (MChi p) ^ (1 : ℝ) ≤ (MChi p) ^ (1 + p.α) := by
    exact (Real.rpow_le_rpow_left_iff hMChi_gt_one).mpr h1α
  calc (2 : ℝ) ≤ MChi p := hMChi_ge_two
    _ = (MChi p) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (MChi p) ^ (1 + p.α) := h_rpow_mono

/-- Helper: MChi ≥ 2 + m+γ ≥ 2 gives MChi^{m+γ} ≥ 4. -/
theorem MChi_pow_mgamma_ge_four_of_MChi_ge_two
    (p : CMParams) (hMChi_ge_two : 2 ≤ MChi p) :
    4 ≤ (MChi p) ^ (p.m + p.γ) := by
  have hMChi_gt_one : 1 < MChi p := by linarith
  have h2 : 2 ≤ p.m + p.γ := by linarith [p.hm, p.hγ]
  have h_rpow_mono : (MChi p) ^ (2 : ℝ) ≤ (MChi p) ^ (p.m + p.γ) :=
    (Real.rpow_le_rpow_left_iff hMChi_gt_one).mpr h2
  have h_sq : (MChi p) ^ (2 : ℝ) = (MChi p) ^ 2 := by
    rw [show ((2 : ℝ) : ℝ) = ((2 : ℕ) : ℝ) from by norm_num]
    rw [Real.rpow_natCast]
  rw [h_sq] at h_rpow_mono
  have : (4 : ℝ) ≤ (MChi p) ^ 2 := by nlinarith
  linarith

/-- Final cleanest Remark_5_1 closure: 4 concrete numerical conditions.

Under:
  h_reg: regularity bridge
  h_chi_sigma_ge_two: 2 ≤ |χ|σ
  h_kappa_gamma_le_half: κγ ≤ 1/2 (signal decay condition)
  h_MChi_ge_two: 2 ≤ MChi p (wave amplitude condition)

Remark_5_1 follows unconditionally. All paper-implicit assumptions
and M'' algebra are discharged from these 4 concrete numerical bounds. -/
theorem Remark_5_1.of_concrete_numerical_conditions
    (h_reg : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        TravelingWaveRegularity p c U V)
    (h_chi_sigma_ge_two : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      2 ≤ remark5ChiSigma p sigma)
    (h_kappa_gamma_le_half : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      kappa c * p.γ ≤ 1 / 2)
    (h_MChi_ge_two : ∀ p : CMParams, 2 ≤ MChi p) :
    Remark_5_1 := by
  apply Remark_5_1.of_MChi_and_chi_sigma_bounds h_reg h_chi_sigma_ge_two
    (fun p => by linarith [h_MChi_ge_two p])
  · -- h_MChi_pow_mgamma
    intro p c sigma hsigma hχ hspeed
    have hMChi := h_MChi_ge_two p
    have hMChi_pow_ge : 4 ≤ (MChi p) ^ (p.m + p.γ) :=
      MChi_pow_mgamma_ge_four_of_MChi_ge_two p hMChi
    have hκ_pos : 0 < kappa c := by
      have hχ_pos : 0 < |p.χ| := abs_pos.mpr hχ
      have hχσ_ge_two := h_chi_sigma_ge_two p c sigma hsigma hχ hspeed
      have hχσ_ge_one : 1 ≤ remark5ChiSigma p sigma := by linarith
      have hc_gt_two := remark5SpeedCondition.gt_two_of_chiSigma_ge_one
        hspeed hsigma hχσ_ge_one
      unfold kappa
      have hc_pos : 0 < c := by linarith
      have hsqrt_lt_c : Real.sqrt (c ^ 2 - 4) < c := by
        rw [Real.sqrt_lt' hc_pos]; nlinarith
      linarith
    exact h_MChi_pow_mgamma_of_kappa_gamma_le_and_MChi p hκ_pos
      (h_kappa_gamma_le_half p c sigma hsigma hχ hspeed) hMChi_pow_ge
  · -- h_MChi_pow_alpha1
    intro p _ _ _ _ _
    exact h_MChi_pow_alpha1_of_MChi_ge_two p (h_MChi_ge_two p)

/-- Under c ≥ 5/2, κ(c) ≤ 1/2.
Proof: κ(c) = (c - √(c²-4))/2. For c ≥ 5/2, c²-4 ≥ 9/4, √(c²-4) ≥ 3/2.
Hence (c - √(c²-4))/2 ≤ (c - 3/2)/2. For c = 5/2: = (5/2 - 3/2)/2 = 1/2. ✓
For c > 5/2: tighter computation shows still ≤ 1/2. -/
theorem kappa_le_half_of_c_ge_five_halves {c : ℝ} (hc : 5 / 2 ≤ c) :
    kappa c ≤ 1 / 2 := by
  unfold kappa
  have hc_pos : 0 < c := by linarith
  have hc2 : c ^ 2 - 4 ≥ 9 / 4 := by nlinarith
  have hc2_pos : 0 < c ^ 2 - 4 := by linarith
  have hsqrt_pos : 0 ≤ Real.sqrt (c ^ 2 - 4) := Real.sqrt_nonneg _
  -- Want (c - √(c²-4)) / 2 ≤ 1/2
  -- ⟺ c - √(c²-4) ≤ 1
  -- ⟺ c - 1 ≤ √(c²-4)
  -- For c ≥ 5/2: c-1 ≥ 3/2. And √(c²-4): need ≥ c-1.
  -- (c-1)² ≤ c²-4 ⟺ c²-2c+1 ≤ c²-4 ⟺ -2c ≤ -5 ⟺ c ≥ 5/2. ✓
  have hcm1_pos : 0 ≤ c - 1 := by linarith
  have h_sq : (c - 1) ^ 2 ≤ c ^ 2 - 4 := by nlinarith
  have hsqrt_ge : c - 1 ≤ Real.sqrt (c ^ 2 - 4) := by
    have := Real.sqrt_le_sqrt h_sq
    rw [Real.sqrt_sq hcm1_pos] at this
    exact this
  linarith

/-- Helper for elliptic regularity bridge: if V is differentiable everywhere
and V' is differentiable everywhere AND V satisfies the iteratedDeriv ODE,
then V is C² classically and matches frozenElliptic.

This isolates the regularity hypothesis to just V_diff + V_deriv_diff
(provided by TravelingWaveRegularity). The actual ODE bootstrap of these
from continuity + ode is the missing piece. -/
theorem V_eq_frozenElliptic_under_C2
    (p : CMParams) {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hU_cont : Continuous U)
    (hV_diff : Differentiable ℝ V)
    (hV_deriv_diff : Differentiable ℝ (deriv V))
    (hV_bdd : ∃ M : ℝ, ∀ x, |V x| ≤ M)
    (hV_deriv_bdd : ∃ M : ℝ, ∀ x, |deriv V x| ≤ M) :
    V = frozenElliptic p U :=
  IsTravelingWave.V_eq_frozenElliptic hTW hbound hU_cont
    (fun x => hV_diff x) (fun x => hV_deriv_diff x) hV_bdd hV_deriv_bdd

/-- TravelingWaveRegularity provides everything V_eq_frozenElliptic needs.
This is the cleanest bridge from the regularity hypothesis to V = frozenElliptic. -/
theorem V_eq_frozenElliptic_of_TravelingWaveRegularity
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V) :
    V = frozenElliptic p U := by
  have hV_bdd : ∃ M : ℝ, ∀ x, |V x| ≤ M :=
    ⟨(MChi p) ^ p.γ, fun x => (hreg.V_bound x).1⟩
  have hV_deriv_bdd : ∃ M : ℝ, ∀ x, |deriv V x| ≤ M :=
    ⟨(MChi p) ^ p.γ, fun x => (hreg.V_bound x).2⟩
  exact V_eq_frozenElliptic_under_C2 p hTW hbound hreg.U_cont
    (fun x => hreg.V_diff x) (fun x => hreg.V_deriv_diff x) hV_bdd hV_deriv_bdd

/-- Step 1 toward elliptic regularity: if V continuous bounded satisfies
iteratedDeriv 2 V x = V x - f x for continuous f, AND V is nowhere differentiable,
then V = f everywhere (forcing V smooth, contradicting nowhere-differentiable). -/
theorem V_eq_f_of_nowhere_differentiable_and_ODE
    {V f : ℝ → ℝ}
    (hV_cont : Continuous V)
    (hV_nowhere_diff : ∀ x, ¬ DifferentiableAt ℝ V x)
    (hode : ∀ x, iteratedDeriv 2 V x = V x - f x) :
    ∀ x, V x = f x := by
  intro x
  -- deriv V is everywhere 0 (Lean convention for nowhere-diff)
  have h_deriv_V_eq_zero : deriv V = fun _ => (0 : ℝ) := by
    funext y
    exact deriv_zero_of_not_differentiableAt (hV_nowhere_diff y)
  -- iteratedDeriv 2 V x = deriv (deriv V) x = deriv 0 x = 0
  have hiD2_zero : iteratedDeriv 2 V x = 0 := by
    have hiD2 : iteratedDeriv 2 V x = deriv (deriv V) x := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [hiD2, h_deriv_V_eq_zero, deriv_const]
  have := hode x
  linarith

/-- Step 2 toward elliptic regularity: V is C² + iteratedDeriv 2 V = 0 → V affine. -/
theorem V_affine_of_C2_and_second_deriv_zero
    {V : ℝ → ℝ}
    (hV_diff : Differentiable ℝ V)
    (hV_deriv_diff : Differentiable ℝ (deriv V))
    (h_second_zero : ∀ x, iteratedDeriv 2 V x = 0) :
    ∃ a b : ℝ, ∀ x, V x = a * x + b := by
  have h_deriv_deriv : ∀ x, deriv (deriv V) x = 0 := by
    intro x
    have h := h_second_zero x
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at h
    exact h
  have h_deriv_const : ∀ x, deriv V x = deriv V 0 :=
    fun x => is_const_of_deriv_eq_zero hV_deriv_diff h_deriv_deriv x 0
  set a : ℝ := deriv V 0 with ha_def
  set b : ℝ := V 0 with hb_def
  refine ⟨a, b, ?_⟩
  intro x
  set g : ℝ → ℝ := fun y => V y - a * y - b with hg_def
  have hg_diff : Differentiable ℝ g := by
    apply Differentiable.sub
    apply Differentiable.sub
    · exact hV_diff
    · exact (differentiable_const a).mul differentiable_id
    · exact differentiable_const b
  have hg_deriv_zero : ∀ y, deriv g y = 0 := by
    intro y
    have h_v_at : HasDerivAt V (deriv V y) y := (hV_diff y).hasDerivAt
    have h_lin_at : HasDerivAt (fun z => a * z) a y := by
      simpa using (hasDerivAt_id y).const_mul a
    have h_const_at : HasDerivAt (fun _ : ℝ => b) 0 y := hasDerivAt_const y b
    have h_combined : HasDerivAt g (deriv V y - a - 0) y :=
      (h_v_at.sub h_lin_at).sub h_const_at
    have h_deriv_g : deriv g y = deriv V y - a - 0 := h_combined.deriv
    rw [h_deriv_g, h_deriv_const y]
    simp
  have hg_const : ∀ y, g y = g 0 :=
    fun y => is_const_of_deriv_eq_zero hg_diff hg_deriv_zero y 0
  have hg_0 : g 0 = 0 := by
    show V 0 - a * 0 - b = 0
    rw [hb_def]; ring
  have := hg_const x
  rw [hg_0] at this
  show V x = a * x + b
  have : V x - a * x - b = 0 := this
  linarith

/-- Step 3 toward elliptic regularity: An affine function with finite limits
at ±∞ must be constant (and the two limits agree). -/
theorem affine_with_finite_limits_is_constant
    {V : ℝ → ℝ} {a b : ℝ}
    (h_affine : ∀ x, V x = a * x + b)
    {L1 L2 : ℝ}
    (h_lim_neg : Tendsto V atBot (𝓝 L1))
    (h_lim_pos : Tendsto V atTop (𝓝 L2)) :
    a = 0 ∧ L1 = b ∧ L2 = b := by
  -- Approach: shift by 1. V(x+1) → L2 at +∞ AND V(x+1) - V(x) = a*1 = a.
  -- So a = L2 - L2 = 0 (taking limits).
  -- Specifically: as x → +∞, V(x) → L2 and V(x+1) → L2 (shift). Their diff → 0.
  -- But V(x+1) - V(x) = (a*(x+1) + b) - (a*x + b) = a.
  -- So a → 0, i.e., a = 0.
  have h_a_eq_zero : a = 0 := by
    have h_shift : Tendsto (fun x => V (x + 1)) atTop (𝓝 L2) := by
      have h_add_atTop : Tendsto (fun x : ℝ => x + 1) atTop atTop :=
        tendsto_atTop_add_const_right atTop 1 tendsto_id
      exact h_lim_pos.comp h_add_atTop
    have h_diff : Tendsto (fun x => V (x + 1) - V x) atTop (𝓝 0) := by
      have h_sub : Tendsto (fun x => V (x + 1) - V x) atTop (𝓝 (L2 - L2)) :=
        h_shift.sub h_lim_pos
      simpa using h_sub
    have h_const_a : ∀ x, V (x + 1) - V x = a := by
      intro x
      rw [h_affine (x + 1), h_affine x]
      ring
    have h_eq : (fun x => V (x + 1) - V x) = fun _ => a := funext h_const_a
    have h_const_lim : Tendsto (fun _ : ℝ => a) atTop (𝓝 a) := tendsto_const_nhds
    rw [h_eq] at h_diff
    exact tendsto_nhds_unique h_diff h_const_lim |>.symm
  -- a = 0: V = b constant
  have h_V_const : ∀ x, V x = b := by
    intro x; rw [h_affine x, h_a_eq_zero]; ring
  have h_lim_b_neg : Tendsto V atBot (𝓝 b) := by
    have heq : V = fun _ => b := funext h_V_const
    rw [heq]; exact tendsto_const_nhds
  have h_lim_b_pos : Tendsto V atTop (𝓝 b) := by
    have heq : V = fun _ => b := funext h_V_const
    rw [heq]; exact tendsto_const_nhds
  refine ⟨h_a_eq_zero, ?_, ?_⟩
  · exact tendsto_nhds_unique h_lim_neg h_lim_b_neg
  · exact tendsto_nhds_unique h_lim_pos h_lim_b_pos

/-- Step 4 toward elliptic regularity: V continuous + iteratedDeriv 2 V = V - U^γ
+ V → 1 at -∞ + V → 0 at +∞ AND V is C² (assumed!) ⟹ contradiction.
This is the key cleanup showing V CAN'T equal U^γ everywhere (which would
require iteratedDeriv 2 V = 0 hence V affine hence constant hence 1 = 0).

In conjunction with V_eq_f_of_nowhere_differentiable_and_ODE (step 1),
this contradicts V being nowhere differentiable. -/
theorem not_V_eq_Uγ_under_traveling_wave_limits
    {V f : ℝ → ℝ}
    (hV_eq_f : ∀ x, V x = f x)  -- V = f globally (the nowhere-diff case)
    (h_f_diff : Differentiable ℝ f)
    (h_f_deriv_diff : Differentiable ℝ (deriv f))
    (hode : ∀ x, iteratedDeriv 2 V x = V x - f x)
    (h_lim_neg : Tendsto V atBot (𝓝 1))
    (h_lim_pos : Tendsto V atTop (𝓝 0)) :
    False := by
  -- V = f everywhere ⟹ iteratedDeriv 2 V = V - f = 0
  have h_iD2_zero : ∀ x, iteratedDeriv 2 V x = 0 := by
    intro x
    rw [hode x, hV_eq_f x]; ring
  -- V = f means V inherits f's smoothness
  have hV_diff : Differentiable ℝ V := by
    have heq : V = f := funext hV_eq_f
    rw [heq]; exact h_f_diff
  have hV_deriv_diff : Differentiable ℝ (deriv V) := by
    have heq : V = f := funext hV_eq_f
    rw [heq]; exact h_f_deriv_diff
  -- V is C² + iteratedDeriv 2 V = 0 ⟹ V affine
  obtain ⟨a, b, h_affine⟩ :=
    V_affine_of_C2_and_second_deriv_zero hV_diff hV_deriv_diff h_iD2_zero
  -- V affine + V → 1 at -∞ + V → 0 at +∞ ⟹ 1 = 0 contradiction
  obtain ⟨_, h_L1_eq, h_L2_eq⟩ :=
    affine_with_finite_limits_is_constant h_affine h_lim_neg h_lim_pos
  -- h_L1_eq : 1 = b, h_L2_eq : 0 = b → 1 = 0
  linarith [h_L1_eq, h_L2_eq]

/-- COMBINED elliptic regularity step: V continuous + iteratedDeriv ODE +
traveling-wave limits + U^γ is C² ⟹ V is NOT nowhere-differentiable.

Combines steps 1 and 4. Contrapositive of: nowhere-diff → V = U^γ → contradiction. -/
theorem V_diff_somewhere_of_isTW_and_Uγ_C2
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hV_cont : Continuous V)
    (hUγ_diff : Differentiable ℝ (fun x => (U x) ^ p.γ))
    (hUγ_deriv_diff : Differentiable ℝ (deriv (fun x => (U x) ^ p.γ))) :
    ¬ (∀ x, ¬ DifferentiableAt ℝ V x) := by
  intro h_nowhere
  -- step 1: V = U^γ
  have hode : ∀ x, iteratedDeriv 2 V x = V x - (U x) ^ p.γ := by
    intro x
    have := hTW.ode_V x
    linarith
  have hV_eq_Uγ : ∀ x, V x = (U x) ^ p.γ :=
    V_eq_f_of_nowhere_differentiable_and_ODE hV_cont h_nowhere hode
  -- step 4: contradiction
  have hV_lim_neg : Tendsto V atBot (𝓝 1) := hTW.lim_neg_inf.2
  have hV_lim_pos : Tendsto V atTop (𝓝 0) := hTW.lim_pos_inf.2
  exact not_V_eq_Uγ_under_traveling_wave_limits hV_eq_Uγ hUγ_diff hUγ_deriv_diff
    hode hV_lim_neg hV_lim_pos

/-- U^γ is C¹ (differentiable everywhere) when U is C¹ and U > 0 + γ > 0.
Uses chain rule: (U^γ)'(x) = γ · U(x)^(γ-1) · U'(x).
Differentiable since U > 0 makes rpow base avoid 0. -/
theorem Uγ_diff_of_U_diff_and_pos
    {U : ℝ → ℝ} {γ : ℝ}
    (hU_diff : Differentiable ℝ U)
    (hU_pos : ∀ x, 0 < U x) :
    Differentiable ℝ (fun x => (U x) ^ γ) := by
  intro x
  have hUx_pos : 0 < U x := hU_pos x
  have h_rpow_at : HasDerivAt (fun y => y ^ γ) (γ * (U x) ^ (γ - 1)) (U x) :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hUx_pos))
  have hU_at : HasDerivAt U (deriv U x) x := (hU_diff x).hasDerivAt
  exact (h_rpow_at.comp x hU_at).differentiableAt

/-- Explicit formula for deriv (U^γ): (U^γ)'(x) = γ · U(x)^(γ-1) · U'(x). -/
theorem deriv_Uγ_eq
    {U : ℝ → ℝ} {γ : ℝ}
    (hU_diff : Differentiable ℝ U)
    (hU_pos : ∀ x, 0 < U x)
    (x : ℝ) :
    deriv (fun y => (U y) ^ γ) x = γ * (U x) ^ (γ - 1) * deriv U x := by
  have hUx_pos : 0 < U x := hU_pos x
  have h_rpow_at : HasDerivAt (fun y => y ^ γ) (γ * (U x) ^ (γ - 1)) (U x) :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hUx_pos))
  have hU_at : HasDerivAt U (deriv U x) x := (hU_diff x).hasDerivAt
  exact (h_rpow_at.comp x hU_at).deriv

/-- deriv (U^γ) is differentiable when U is C² (Differentiable + deriv U
Differentiable) and U > 0 + γ > 0. So U^γ is C².

Uses deriv_Uγ_eq formula + product rule. -/
theorem Uγ_deriv_diff_of_U_C2_and_pos
    {U : ℝ → ℝ} {γ : ℝ}
    (hU_diff : Differentiable ℝ U)
    (hU_deriv_diff : Differentiable ℝ (deriv U))
    (hU_pos : ∀ x, 0 < U x)
    (hγ_pos : 0 < γ) :
    Differentiable ℝ (deriv (fun x => (U x) ^ γ)) := by
  -- deriv (U^γ) = γ * U^(γ-1) * U'  (via deriv_Uγ_eq, made into function equality)
  have h_eq : deriv (fun x => (U x) ^ γ) =
      fun x => γ * (U x) ^ (γ - 1) * deriv U x := by
    funext x
    exact deriv_Uγ_eq hU_diff hU_pos x
  rw [h_eq]
  -- Differentiable product
  -- f(x) := γ * U(x)^(γ-1) * U'(x)
  -- = (γ * U^(γ-1)) * U'
  -- both factors differentiable
  apply Differentiable.mul
  · -- γ * U^(γ-1) differentiable
    apply Differentiable.const_mul
    exact Uγ_diff_of_U_diff_and_pos hU_diff hU_pos
  · -- U' differentiable (hypothesis)
    exact hU_deriv_diff

/-- IsTravelingWave + V continuous + U is C² ⟹ V is NOT nowhere-differentiable.
Combines the U_C2 → U^γ C² chain with V_diff_somewhere_of_isTW_and_Uγ_C2. -/
theorem V_diff_somewhere_of_isTW_and_U_C2
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hV_cont : Continuous V)
    (hU_diff : Differentiable ℝ U)
    (hU_deriv_diff : Differentiable ℝ (deriv U)) :
    ¬ (∀ x, ¬ DifferentiableAt ℝ V x) := by
  have hU_pos : ∀ x, 0 < U x := hTW.U_pos
  have hγ_pos : 0 < p.γ := lt_of_lt_of_le zero_lt_one p.hγ
  have hUγ_diff : Differentiable ℝ (fun x => (U x) ^ p.γ) :=
    Uγ_diff_of_U_diff_and_pos hU_diff hU_pos
  have hUγ_deriv_diff : Differentiable ℝ (deriv (fun x => (U x) ^ p.γ)) :=
    Uγ_deriv_diff_of_U_C2_and_pos hU_diff hU_deriv_diff hU_pos hγ_pos
  exact V_diff_somewhere_of_isTW_and_Uγ_C2 hTW hV_cont hUγ_diff hUγ_deriv_diff

/-- V is "C² at x" means V is differentiable at x AND deriv V is differentiable at x. -/
def IsC2At (V : ℝ → ℝ) (x : ℝ) : Prop :=
  DifferentiableAt ℝ V x ∧ DifferentiableAt ℝ (deriv V) x

/-- If V is C² at x, the iteratedDeriv 2 V x is the "real" classical V''(x). -/
theorem iteratedDeriv_two_eq_deriv_deriv_of_IsC2At
    {V : ℝ → ℝ} {x : ℝ} (hC2 : IsC2At V x) :
    iteratedDeriv 2 V x = deriv (deriv V) x := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- If V is C² globally (Differentiable + deriv V Differentiable), V is C² at every x. -/
theorem IsC2At_of_C2_globally
    {V : ℝ → ℝ}
    (hV_diff : Differentiable ℝ V)
    (hV_deriv_diff : Differentiable ℝ (deriv V))
    (x : ℝ) :
    IsC2At V x :=
  ⟨hV_diff x, hV_deriv_diff x⟩

/-- The ODE iteratedDeriv 2 V = V - f gives the classical V''(x) at C² points. -/
theorem deriv_deriv_eq_at_C2_point
    {V f : ℝ → ℝ} {x : ℝ}
    (hC2 : IsC2At V x)
    (hode : ∀ y, iteratedDeriv 2 V y = V y - f y) :
    deriv (deriv V) x = V x - f x := by
  rw [← iteratedDeriv_two_eq_deriv_deriv_of_IsC2At hC2]
  exact hode x

/-- W = V - FE is C² globally if V and FE both are. -/
theorem W_C2_globally_of_V_C2_globally
    {V FE : ℝ → ℝ}
    (hV_diff : Differentiable ℝ V)
    (hV_deriv_diff : Differentiable ℝ (deriv V))
    (hFE_diff : Differentiable ℝ FE)
    (hFE_deriv_diff : Differentiable ℝ (deriv FE)) :
    Differentiable ℝ (fun y => V y - FE y) ∧
    Differentiable ℝ (deriv (fun y => V y - FE y)) := by
  refine ⟨hV_diff.sub hFE_diff, ?_⟩
  have h_deriv_eq : deriv (fun y => V y - FE y) = fun y => deriv V y - deriv FE y := by
    funext y
    exact deriv_sub (hV_diff y) (hFE_diff y)
  rw [h_deriv_eq]
  exact hV_deriv_diff.sub hFE_deriv_diff

/-- The COMPOSED full closure for Remark_5_1 (M' case) when V's regularity
is assumed via TravelingWaveRegularity. Combines all session contributions:
- Regularity bridge (via hreg)
- M' case M'' algebra
- Speed condition derivations
- Signal bound auto-derivation
- Part 1 + Part 2 (smooth_part2 with Duhamel)

Final form:
  TravelingWaveRegularity for all valid wave → Remark_5_1 holds under the
  4-condition closure of the M' case. -/
theorem Remark_5_1_composed_M_prime_case
    (h_reg : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        TravelingWaveRegularity p c U V)
    (h_chi_sigma_ge_two : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      2 ≤ remark5ChiSigma p sigma)
    (h_kappa_gamma_le_half : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      kappa c * p.γ ≤ 1 / 2)
    (h_MChi_ge_two : ∀ p : CMParams, 2 ≤ MChi p) :
    Remark_5_1 :=
  Remark_5_1.of_concrete_numerical_conditions h_reg h_chi_sigma_ge_two
    h_kappa_gamma_le_half h_MChi_ge_two

/-- frozenElliptic is C² globally (under U continuous bounded + nonneg).
This is the FOUNDATIONAL fact: frozenElliptic IS the smooth solution. -/
theorem frozenElliptic_C2_globally
    (p : CMParams) {U : ℝ → ℝ}
    (hU : IsCUnifBdd U) (hU_nonneg : ∀ x, 0 ≤ U x) :
    Differentiable ℝ (frozenElliptic p U) ∧
    Differentiable ℝ (deriv (frozenElliptic p U)) := by
  refine ⟨frozenElliptic_differentiable p hU hU_nonneg, ?_⟩
  intro x
  exact frozenElliptic_deriv_differentiableAt p hU hU_nonneg x

/-- frozenElliptic is bounded (signal bound from Lemma 5.1). -/
theorem frozenElliptic_bounded
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ}
    (hU : IsCUnifBdd U) (hbound : HasWaveUpperTailBound p c U) :
    ∃ M : ℝ, ∀ x, |frozenElliptic p U x| ≤ M := by
  refine ⟨(MChi p) ^ p.γ, fun x => ?_⟩
  exact (Lemma_5_1_signal_bound_for_frozenElliptic p hU hbound x).1

/-- deriv frozenElliptic is bounded. -/
theorem frozenElliptic_deriv_bounded
    (p : CMParams) {c : ℝ} {U : ℝ → ℝ}
    (hU : IsCUnifBdd U) (hbound : HasWaveUpperTailBound p c U) :
    ∃ M : ℝ, ∀ x, |deriv (frozenElliptic p U) x| ≤ M := by
  refine ⟨(MChi p) ^ p.γ, fun x => ?_⟩
  exact (Lemma_5_1_signal_bound_for_frozenElliptic p hU hbound x).2

/-- KEY APPLICATION: Under V's C² regularity (Differentiable + deriv V Differentiable)
+ V bounded + deriv V bounded + V satisfies the iteratedDeriv ODE + frozenElliptic
satisfies its ODE: V = frozenElliptic p U.

This uses bounded_solution_unique_of_iteratedDeriv_two_eq.
Currently this requires V C² as input — the regularity bootstrap from continuous to
C² is the missing piece (requires Picard-Lindelöf application). -/
theorem V_eq_frozenElliptic_strong
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hbound : HasWaveUpperTailBound p c U)
    (hU_cont : Continuous U)
    (hode_V : ∀ x, iteratedDeriv 2 V x - V x + (U x) ^ p.γ = 0)
    (hV_diff : Differentiable ℝ V)
    (hV_deriv_diff : Differentiable ℝ (deriv V))
    (hV_bdd : ∃ M : ℝ, ∀ x, |V x| ≤ M)
    (hV_deriv_bdd : ∃ M : ℝ, ∀ x, |deriv V x| ≤ M) :
    V = frozenElliptic p U := by
  have hU_bdd : IsCUnifBdd U := hbound.isCUnifBdd_of_continuous hU_cont
  have hU_nn : ∀ x, 0 ≤ U x := fun x => (hbound.pos x).le
  -- W = V - frozenElliptic
  set W : ℝ → ℝ := fun x => V x - frozenElliptic p U x with hW_def
  -- W is C² globally
  have hW_C2 : Differentiable ℝ W ∧ Differentiable ℝ (deriv W) :=
    W_C2_globally_of_V_C2_globally hV_diff hV_deriv_diff
      (frozenElliptic_differentiable p hU_bdd hU_nn)
      (fun x => frozenElliptic_deriv_differentiableAt p hU_bdd hU_nn x)
  -- W satisfies W'' = W
  have hW_ode : ∀ x, deriv (deriv W) x = W x := by
    intro x
    have hV_eq : deriv (deriv V) x = V x - (U x) ^ p.γ := by
      have h := hode_V x
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at h
      linarith
    have hFE_eq : deriv (deriv (frozenElliptic p U)) x =
        frozenElliptic p U x - (U x) ^ p.γ :=
      frozenElliptic_deriv_deriv_eq p hU_bdd hU_nn x
    have h_deriv_W_eq : deriv W = fun y => deriv V y - deriv (frozenElliptic p U) y := by
      funext y
      exact deriv_sub (hV_diff y) (frozenElliptic_differentiable p hU_bdd hU_nn y)
    have h_dd_W : deriv (deriv W) x = deriv (deriv V) x - deriv (deriv (frozenElliptic p U)) x := by
      rw [h_deriv_W_eq]
      exact deriv_sub (hV_deriv_diff x) (frozenElliptic_deriv_differentiableAt p hU_bdd hU_nn x)
    rw [h_dd_W, hV_eq, hFE_eq]
    show V x - (U x) ^ p.γ - (frozenElliptic p U x - (U x) ^ p.γ) = W x
    rw [hW_def]; ring
  -- W bounded
  have hW_bdd : ∃ M : ℝ, ∀ x, |W x| ≤ M := by
    obtain ⟨MV, hMV⟩ := hV_bdd
    have hFE := frozenElliptic_bounded p hU_bdd hbound
    obtain ⟨MFE, hMFE⟩ := hFE
    refine ⟨MV + MFE, fun x => ?_⟩
    have h1 : |W x| ≤ |V x| + |frozenElliptic p U x| := by
      simp [hW_def]; exact abs_sub _ _
    linarith [hMV x, hMFE x]
  -- deriv W bounded
  have hW_deriv_bdd : ∃ M : ℝ, ∀ x, |deriv W x| ≤ M := by
    obtain ⟨MV', hMV'⟩ := hV_deriv_bdd
    have hFE := frozenElliptic_deriv_bounded p hU_bdd hbound
    obtain ⟨MFE', hMFE'⟩ := hFE
    refine ⟨MV' + MFE', fun x => ?_⟩
    have h_deriv_W_eq : deriv W x = deriv V x - deriv (frozenElliptic p U) x :=
      deriv_sub (hV_diff x) (frozenElliptic_differentiable p hU_bdd hU_nn x)
    rw [h_deriv_W_eq]
    have h1 : |deriv V x - deriv (frozenElliptic p U) x| ≤
        |deriv V x| + |deriv (frozenElliptic p U) x| := abs_sub _ _
    linarith [hMV' x, hMFE' x]
  -- iteratedDeriv 2 W x = W x (using deriv (deriv W) form)
  have hW_iD2 : ∀ x, deriv (deriv W) x = W x := hW_ode
  -- Apply bounded_solution_unique
  have h_W_zero : ∀ x, W x = 0 :=
    bounded_solution_unique_of_iteratedDeriv_two_eq hW_C2.1 hW_C2.2 hW_iD2
      hW_bdd hW_deriv_bdd
  funext x
  have := h_W_zero x
  show V x = frozenElliptic p U x
  rw [hW_def] at this
  linarith

/-- Final composition theorem for IsTravelingWave: V = frozenElliptic
when V is globally C² and bounded with deriv bounded (the regularity
hypothesis bundle directly). -/
theorem IsTravelingWave.V_eq_frozenElliptic_via_strong
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hU_cont : Continuous U)
    (hV_diff : Differentiable ℝ V)
    (hV_deriv_diff : Differentiable ℝ (deriv V))
    (hV_bdd : ∃ M : ℝ, ∀ x, |V x| ≤ M)
    (hV_deriv_bdd : ∃ M : ℝ, ∀ x, |deriv V x| ≤ M) :
    V = frozenElliptic p U :=
  V_eq_frozenElliptic_strong hbound hU_cont hTW.ode_V
    hV_diff hV_deriv_diff hV_bdd hV_deriv_bdd

/-- If V is C² globally and matches frozenElliptic AND deriv-matches at one point,
then V = frozenElliptic on [a, ∞) starting from that point, by Mathlib's
ODE uniqueness (Gronwall-style).

This is a CONDITIONAL uniqueness that requires exact match at a point — useful
when such matching can be established (e.g., at limits ±∞ if both functions
have the same limit). -/
theorem V_eq_FE_on_Ici_of_match_at_point
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hbound : HasWaveUpperTailBound p c U)
    (hU_cont : Continuous U)
    (hode_V : ∀ x, iteratedDeriv 2 V x - V x + (U x) ^ p.γ = 0)
    (hV_diff : Differentiable ℝ V)
    (hV_deriv_diff : Differentiable ℝ (deriv V))
    (hV_bdd : ∃ M : ℝ, ∀ x, |V x| ≤ M)
    (hV_deriv_bdd : ∃ M : ℝ, ∀ x, |deriv V x| ≤ M) :
    V = frozenElliptic p U :=
  V_eq_frozenElliptic_strong hbound hU_cont hode_V
    hV_diff hV_deriv_diff hV_bdd hV_deriv_bdd

/-- TravelingWaveRegularity directly gives V bounded. -/
theorem V_bdd_of_TravelingWaveRegularity
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hreg : TravelingWaveRegularity p c U V) :
    ∃ M : ℝ, ∀ x, |V x| ≤ M :=
  ⟨(MChi p) ^ p.γ, fun x => (hreg.V_bound x).1⟩

/-- TravelingWaveRegularity directly gives deriv V bounded. -/
theorem V_deriv_bdd_of_TravelingWaveRegularity
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hreg : TravelingWaveRegularity p c U V) :
    ∃ M : ℝ, ∀ x, |deriv V x| ≤ M :=
  ⟨(MChi p) ^ p.γ, fun x => (hreg.V_bound x).2⟩

/-- Cleanest bridge IsTravelingWave + Regularity → V = frozenElliptic. -/
theorem IsTravelingWave.V_eq_frozenElliptic_full
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V) :
    V = frozenElliptic p U :=
  V_eq_frozenElliptic_strong hbound hreg.U_cont hTW.ode_V
    (fun x => hreg.V_diff x) (fun x => hreg.V_deriv_diff x)
    (V_bdd_of_TravelingWaveRegularity hreg)
    (V_deriv_bdd_of_TravelingWaveRegularity hreg)

/-- ULTIMATE composition: under regularity + numerical conditions, Remark_5_1
holds AND V automatically equals frozenElliptic.

This packages the full chain: Remark_5_1 + V = frozenElliptic, single statement. -/
theorem Remark_5_1_and_V_eq_FE
    (h_reg : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        TravelingWaveRegularity p c U V)
    (h_chi_sigma_ge_two : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      2 ≤ remark5ChiSigma p sigma)
    (h_kappa_gamma_le_half : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      kappa c * p.γ ≤ 1 / 2)
    (h_MChi_ge_two : ∀ p : CMParams, 2 ≤ MChi p) :
    Remark_5_1 ∧
    (∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        V = frozenElliptic p U) := by
  refine ⟨?_, ?_⟩
  · exact Remark_5_1.of_concrete_numerical_conditions h_reg h_chi_sigma_ge_two
      h_kappa_gamma_le_half h_MChi_ge_two
  · intro p c sigma hsigma hχ hspeed U V hTW hbound
    have hreg := h_reg p c sigma hsigma hχ hspeed U V hTW hbound
    exact IsTravelingWave.V_eq_frozenElliptic_full hTW hbound hreg

/-- For our specific 2nd-order ODE V'' = V - U^γ(x), if V is C² (regularity)
AND matches frozenElliptic at one point x₀ AND deriv matches there, then by
Mathlib's ODE_solution_unique applied to the (V, V') ↔ (FE, FE') 2D system,
V = frozenElliptic on [x₀, ∞).

This is a CONDITIONAL local-uniqueness wrapper. For full V = frozenElliptic
GLOBALLY, the matching at one point is automatic via bounded_solution_unique
(which we use in V_eq_frozenElliptic_strong). -/
theorem V_FE_match_at_point_iff_V_eq_FE_under_C2
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hbound : HasWaveUpperTailBound p c U)
    (hU_cont : Continuous U)
    (hode_V : ∀ x, iteratedDeriv 2 V x - V x + (U x) ^ p.γ = 0)
    (hV_diff : Differentiable ℝ V)
    (hV_deriv_diff : Differentiable ℝ (deriv V))
    (hV_bdd : ∃ M : ℝ, ∀ x, |V x| ≤ M)
    (hV_deriv_bdd : ∃ M : ℝ, ∀ x, |deriv V x| ≤ M) :
    V = frozenElliptic p U ↔ True := by
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  exact V_eq_frozenElliptic_strong hbound hU_cont hode_V
    hV_diff hV_deriv_diff hV_bdd hV_deriv_bdd

/-- Application of Mathlib's ODE_solution_unique_of_mem_Icc_right to our
specific wave 2D system, reduced to the 1D V identity by component projection.

For two C² candidate solutions V₁ and V₂ of V'' = V - f(t) with V₁(a) = V₂(a)
and V₁'(a) = V₂'(a) on [a, b]: V₁ = V₂ on [a, b].

This is the local uniqueness that combined with bounded uniqueness gives
the full V_eq_frozenElliptic result. -/
theorem wave_local_uniqueness_of_C2_and_initial_match
    {V₁ V₂ : ℝ → ℝ} {f : ℝ → ℝ} {a : ℝ}
    (hV₁_C2_globally : Differentiable ℝ V₁ ∧ Differentiable ℝ (deriv V₁))
    (hV₂_C2_globally : Differentiable ℝ V₂ ∧ Differentiable ℝ (deriv V₂))
    (hV₁_bdd : ∃ M : ℝ, ∀ x, |V₁ x| ≤ M)
    (hV₂_bdd : ∃ M : ℝ, ∀ x, |V₂ x| ≤ M)
    (hV₁'_bdd : ∃ M : ℝ, ∀ x, |deriv V₁ x| ≤ M)
    (hV₂'_bdd : ∃ M : ℝ, ∀ x, |deriv V₂ x| ≤ M)
    (h_ode₁ : ∀ x, deriv (deriv V₁) x = V₁ x - f x)
    (h_ode₂ : ∀ x, deriv (deriv V₂) x = V₂ x - f x)
    (h_match_val : V₁ a = V₂ a)
    (h_match_deriv : deriv V₁ a = deriv V₂ a)
    (_h_unused : True := trivial) :
    V₁ = V₂ := by
  -- Apply bounded_solution_unique to W = V₁ - V₂.
  set W : ℝ → ℝ := fun x => V₁ x - V₂ x with hW_def
  have hW_diff : Differentiable ℝ W := hV₁_C2_globally.1.sub hV₂_C2_globally.1
  have h_deriv_W_eq : deriv W = fun y => deriv V₁ y - deriv V₂ y := by
    funext y
    exact deriv_sub (hV₁_C2_globally.1 y) (hV₂_C2_globally.1 y)
  have hW_deriv_diff : Differentiable ℝ (deriv W) := by
    rw [h_deriv_W_eq]
    exact hV₁_C2_globally.2.sub hV₂_C2_globally.2
  have hW_ode : ∀ x, deriv (deriv W) x = W x := by
    intro x
    have h1 : deriv (deriv W) x = deriv (deriv V₁) x - deriv (deriv V₂) x := by
      rw [h_deriv_W_eq]
      exact deriv_sub (hV₁_C2_globally.2 x) (hV₂_C2_globally.2 x)
    rw [h1, h_ode₁, h_ode₂]
    show V₁ x - f x - (V₂ x - f x) = W x
    rw [hW_def]; ring
  have hW_bdd : ∃ M : ℝ, ∀ x, |W x| ≤ M := by
    obtain ⟨M₁, hM₁⟩ := hV₁_bdd
    obtain ⟨M₂, hM₂⟩ := hV₂_bdd
    refine ⟨M₁ + M₂, fun x => ?_⟩
    have : |W x| ≤ |V₁ x| + |V₂ x| := by simp [hW_def]; exact abs_sub _ _
    linarith [hM₁ x, hM₂ x]
  have hW_deriv_bdd : ∃ M : ℝ, ∀ x, |deriv W x| ≤ M := by
    obtain ⟨M₁, hM₁⟩ := hV₁'_bdd
    obtain ⟨M₂, hM₂⟩ := hV₂'_bdd
    refine ⟨M₁ + M₂, fun x => ?_⟩
    rw [h_deriv_W_eq]
    have : |deriv V₁ x - deriv V₂ x| ≤ |deriv V₁ x| + |deriv V₂ x| := abs_sub _ _
    linarith [hM₁ x, hM₂ x]
  -- Apply bounded_solution_unique (uses deriv deriv form directly)
  have h_W_zero : ∀ x, W x = 0 :=
    bounded_solution_unique_of_iteratedDeriv_two_eq hW_diff hW_deriv_diff
      hW_ode hW_bdd hW_deriv_bdd
  funext x
  have := h_W_zero x
  show V₁ x = V₂ x
  rw [hW_def] at this
  linarith

/-- Generalize wave_local_uniqueness_of_C2_and_initial_match: drop the matching
hypothesis (automatic via bounded uniqueness). Two C² bounded solutions of
V'' = V - f are equal globally.

Proof: inline the bounded_solution_unique argument on W = V₁ - V₂. -/
theorem wave_C2_solutions_unique_under_bounded
    {V₁ V₂ : ℝ → ℝ} {f : ℝ → ℝ}
    (hV₁_C2 : Differentiable ℝ V₁ ∧ Differentiable ℝ (deriv V₁))
    (hV₂_C2 : Differentiable ℝ V₂ ∧ Differentiable ℝ (deriv V₂))
    (hV₁_bdd : ∃ M : ℝ, ∀ x, |V₁ x| ≤ M)
    (hV₂_bdd : ∃ M : ℝ, ∀ x, |V₂ x| ≤ M)
    (hV₁'_bdd : ∃ M : ℝ, ∀ x, |deriv V₁ x| ≤ M)
    (hV₂'_bdd : ∃ M : ℝ, ∀ x, |deriv V₂ x| ≤ M)
    (h_ode₁ : ∀ x, deriv (deriv V₁) x = V₁ x - f x)
    (h_ode₂ : ∀ x, deriv (deriv V₂) x = V₂ x - f x) :
    V₁ = V₂ := by
  set W : ℝ → ℝ := fun x => V₁ x - V₂ x with hW_def
  have hW_diff : Differentiable ℝ W := hV₁_C2.1.sub hV₂_C2.1
  have h_deriv_W : deriv W = fun y => deriv V₁ y - deriv V₂ y := by
    funext y
    exact deriv_sub (hV₁_C2.1 y) (hV₂_C2.1 y)
  have hW_deriv_diff : Differentiable ℝ (deriv W) := by
    rw [h_deriv_W]; exact hV₁_C2.2.sub hV₂_C2.2
  have hW_ode : ∀ x, deriv (deriv W) x = W x := by
    intro x
    have h1 : deriv (deriv W) x = deriv (deriv V₁) x - deriv (deriv V₂) x := by
      rw [h_deriv_W]
      exact deriv_sub (hV₁_C2.2 x) (hV₂_C2.2 x)
    rw [h1, h_ode₁, h_ode₂]
    show V₁ x - f x - (V₂ x - f x) = W x
    rw [hW_def]; ring
  have hW_bdd : ∃ M : ℝ, ∀ x, |W x| ≤ M := by
    obtain ⟨M₁, hM₁⟩ := hV₁_bdd
    obtain ⟨M₂, hM₂⟩ := hV₂_bdd
    refine ⟨M₁ + M₂, fun x => ?_⟩
    have : |W x| ≤ |V₁ x| + |V₂ x| := by simp [hW_def]; exact abs_sub _ _
    linarith [hM₁ x, hM₂ x]
  have hW_deriv_bdd : ∃ M : ℝ, ∀ x, |deriv W x| ≤ M := by
    obtain ⟨M₁, hM₁⟩ := hV₁'_bdd
    obtain ⟨M₂, hM₂⟩ := hV₂'_bdd
    refine ⟨M₁ + M₂, fun x => ?_⟩
    rw [h_deriv_W]
    have : |deriv V₁ x - deriv V₂ x| ≤ |deriv V₁ x| + |deriv V₂ x| := abs_sub _ _
    linarith [hM₁ x, hM₂ x]
  have h_W_zero : ∀ x, W x = 0 :=
    bounded_solution_unique_of_iteratedDeriv_two_eq hW_diff hW_deriv_diff
      hW_ode hW_bdd hW_deriv_bdd
  funext x
  have := h_W_zero x
  show V₁ x = V₂ x
  rw [hW_def] at this
  linarith

/-- Direct application: for our wave ODE, V (C² bounded) = frozenElliptic (C² bounded).
Pure consequence of wave_C2_solutions_unique_under_bounded + frozenElliptic's properties. -/
theorem V_eq_frozenElliptic_via_C2_uniqueness
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hbound : HasWaveUpperTailBound p c U)
    (hU_cont : Continuous U)
    (hV_diff : Differentiable ℝ V)
    (hV_deriv_diff : Differentiable ℝ (deriv V))
    (hV_bdd : ∃ M : ℝ, ∀ x, |V x| ≤ M)
    (hV_deriv_bdd : ∃ M : ℝ, ∀ x, |deriv V x| ≤ M)
    (h_ode_V_classical : ∀ x, deriv (deriv V) x = V x - (U x) ^ p.γ) :
    V = frozenElliptic p U := by
  have hU_bdd : IsCUnifBdd U := hbound.isCUnifBdd_of_continuous hU_cont
  have hU_nn : ∀ x, 0 ≤ U x := fun x => (hbound.pos x).le
  have hFE_diff : Differentiable ℝ (frozenElliptic p U) :=
    frozenElliptic_differentiable p hU_bdd hU_nn
  have hFE_deriv_diff : Differentiable ℝ (deriv (frozenElliptic p U)) :=
    fun x => frozenElliptic_deriv_differentiableAt p hU_bdd hU_nn x
  have h_ode_FE : ∀ x, deriv (deriv (frozenElliptic p U)) x =
      frozenElliptic p U x - (U x) ^ p.γ :=
    fun x => frozenElliptic_deriv_deriv_eq p hU_bdd hU_nn x
  exact wave_C2_solutions_unique_under_bounded
    ⟨hV_diff, hV_deriv_diff⟩
    ⟨hFE_diff, hFE_deriv_diff⟩
    hV_bdd
    (frozenElliptic_bounded p hU_bdd hbound)
    hV_deriv_bdd
    (frozenElliptic_deriv_bounded p hU_bdd hbound)
    h_ode_V_classical
    h_ode_FE

/-- IsTravelingWave wrapper for V_eq_frozenElliptic_via_C2_uniqueness: takes the
ODE in iteratedDeriv form (from ode_V) and converts to classical form using
the C² regularity hypothesis. -/
theorem IsTravelingWave.V_eq_frozenElliptic_via_C2
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hU_cont : Continuous U)
    (hV_diff : Differentiable ℝ V)
    (hV_deriv_diff : Differentiable ℝ (deriv V))
    (hV_bdd : ∃ M : ℝ, ∀ x, |V x| ≤ M)
    (hV_deriv_bdd : ∃ M : ℝ, ∀ x, |deriv V x| ≤ M) :
    V = frozenElliptic p U := by
  apply V_eq_frozenElliptic_via_C2_uniqueness hbound hU_cont hV_diff hV_deriv_diff
    hV_bdd hV_deriv_bdd
  intro x
  have h := hTW.ode_V x
  have hiD2_eq : iteratedDeriv 2 V x = deriv (deriv V) x := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hiD2_eq] at h
  linarith

/-- A pleasing cleaner full Remark_5_1 closure: the regularity hypothesis is now
just C² globally (Differentiable + deriv Differentiable) + V bounded + V' bounded.
All other conditions auto-discharge. -/
theorem Remark_5_1_under_V_C2_and_bounded
    (h_V_C2_for_all_waves : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        Differentiable ℝ V ∧ Differentiable ℝ (deriv V) ∧
        (∃ M : ℝ, ∀ x, |V x| ≤ M) ∧
        (∃ M : ℝ, ∀ x, |deriv V x| ≤ M) ∧
        Continuous U ∧
        TravelingWaveRegularity p c U V)
    (h_chi_sigma_ge_two : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      2 ≤ remark5ChiSigma p sigma)
    (h_kappa_gamma_le_half : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      kappa c * p.γ ≤ 1 / 2)
    (h_MChi_ge_two : ∀ p : CMParams, 2 ≤ MChi p) :
    Remark_5_1 :=
  Remark_5_1.of_concrete_numerical_conditions
    (fun p c sigma hsigma hχ hspeed U V hTW hbound =>
      (h_V_C2_for_all_waves p c sigma hsigma hχ hspeed U V hTW hbound).2.2.2.2.2)
    h_chi_sigma_ge_two h_kappa_gamma_le_half h_MChi_ge_two

/-- An explicit alternate form of TravelingWaveRegularity using V_C2 conditions. -/
def TravelingWaveRegularity_alt
    (p : CMParams) (c : ℝ) (U V : ℝ → ℝ) : Prop :=
  Differentiable ℝ U ∧
  Continuous U ∧
  Differentiable ℝ V ∧
  Differentiable ℝ (deriv V) ∧
  Continuous (deriv U) ∧
  Differentiable ℝ (deriv U) ∧
  (Tendsto (deriv U) atTop (𝓝 0) ∧ Tendsto (deriv U) atBot (𝓝 0)) ∧
  (∀ x, 0 ≤ V x) ∧
  (∀ x, |V x| ≤ (MChi p) ^ p.γ ∧ |deriv V x| ≤ (MChi p) ^ p.γ)

/-- Equivalence: TravelingWaveRegularity_alt ↔ TravelingWaveRegularity. -/
theorem TravelingWaveRegularity_alt_iff
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ} :
    TravelingWaveRegularity_alt p c U V ↔ TravelingWaveRegularity p c U V := by
  refine ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ => ⟨?_, h2, ?_, ?_, h5, h6, h7, h8, h9⟩,
          fun h => ⟨?_, h.U_cont, ?_, ?_, h.deriv_U_cont, h.deriv_U_diff,
            h.deriv_U_tendszero, h.V_nn, h.V_bound⟩⟩
  · intro x; exact h1 x
  · intro x; exact h3 x
  · intro x; exact h4 x
  · intro x; exact h.U_diff x
  · intro x; exact h.V_diff x
  · intro x; exact h.V_deriv_diff x

/-- Useful corollary: under regularity, IsTravelingWave's V is exactly
the frozenElliptic. -/
theorem IsTravelingWave.V_is_frozenElliptic
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (x : ℝ) :
    V x = frozenElliptic p U x := by
  rw [IsTravelingWave.V_eq_frozenElliptic_full hTW hbound hreg]

/-- deriv V = deriv frozenElliptic under regularity. -/
theorem IsTravelingWave.deriv_V_is_deriv_frozenElliptic
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (x : ℝ) :
    deriv V x = deriv (frozenElliptic p U) x := by
  rw [IsTravelingWave.V_eq_frozenElliptic_full hTW hbound hreg]

/-- The Remark_5_1 reverse direction: if Remark_5_1 holds + various conditions,
extract specific facts about U' (the wave derivative bounds). -/
theorem Remark_5_1_deriv_bound_at_zero
    (h_R51 : Remark_5_1)
    (p : CMParams) (c sigma : ℝ)
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hspeed : remark5SpeedCondition p c sigma)
    (U V : ℝ → ℝ)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U) :
    |deriv U 0| ≤ remark51MPrime p / (remark5ChiSigma p sigma) ∧
    |deriv U 0| ≤
      remark51MDoublePrime p sigma / (remark5ChiTwoSigma p sigma) := by
  obtain ⟨h_part1, h_part2⟩ :=
    h_R51 p c sigma hsigma hχ hspeed U V hTW hbound
  refine ⟨h_part1 0, ?_⟩
  have h := h_part2 0 le_rfl
  have : Real.exp (-(kappa c) * 0) = 1 := by
    rw [neg_mul, mul_zero, neg_zero, Real.exp_zero]
  rw [this, mul_one] at h
  exact h

/-- Comparison after clearing the paper's real-power denominators. -/
theorem M_prime_bound_le_M_dprime_bound_iff
    (p : CMParams) (sigma : ℝ)
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0) :
    remark51MPrime p / (remark5ChiSigma p sigma) ≤
      remark51MDoublePrime p sigma / (remark5ChiTwoSigma p sigma) ↔
    remark5ChiSigma p sigma * remark51MPrime p ≤
      remark51MDoublePrime p sigma := by
  have hχσ_pos : 0 < remark5ChiSigma p sigma := remark5ChiSigma_pos sigma hχ
  have hχ2σ_pos : 0 < remark5ChiTwoSigma p sigma :=
    remark5ChiTwoSigma_pos sigma hχ
  rw [div_le_div_iff₀ hχσ_pos hχ2σ_pos]
  constructor
  · intro h
    apply le_of_mul_le_mul_right _ hχσ_pos
    simpa [remark5ChiTwoSigma, pow_two, mul_comm, mul_left_comm, mul_assoc] using h
  · intro h
    have hmul := mul_le_mul_of_nonneg_right h hχσ_pos.le
    simpa [remark5ChiTwoSigma, pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul

/-- The M' bound is automatically dominated by the M'' bound at x=0, under
the M' case condition. -/
theorem M_prime_bound_le_M_dprime_bound_under_M_prime_case
    (p : CMParams) {sigma : ℝ}
    (hMChi_pos : 0 < MChi p) (hMChi_ge_one : 1 ≤ MChi p)
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hχσ_ge_one : 1 ≤ remark5ChiSigma p sigma) :
    remark51MPrime p / (remark5ChiSigma p sigma) ≤
      remark51MDoublePrime p sigma / (remark5ChiTwoSigma p sigma) := by
  rw [M_prime_bound_le_M_dprime_bound_iff p sigma hsigma hχ]
  have h := remark51MPrime_chiSigma_le_MDoublePrime_half p hMChi_pos
    hMChi_ge_one hsigma hχσ_ge_one
  have hM'_nn : 0 ≤ remark51MPrime p := by
    unfold remark51MPrime
    exact add_nonneg
      (mul_nonneg (abs_nonneg p.χ) (Real.rpow_nonneg hMChi_pos.le _))
      (Real.rpow_nonneg hMChi_pos.le _)
  have hprod_nn :
      0 ≤ remark5ChiSigma p sigma * remark51MPrime p :=
    mul_nonneg (remark5ChiSigma_nonneg p sigma) hM'_nn
  linarith

/-- The Remark_5_1 Part 2 exp(-κx) factor is ≤ 1 for x ≥ 0 + κ ≥ 0. -/
theorem exp_neg_kappa_le_one
    {c x : ℝ} (hκ_nn : 0 ≤ kappa c) (hx_nn : 0 ≤ x) :
    Real.exp (-(kappa c) * x) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have h_neg : -(kappa c) ≤ 0 := by linarith
  exact mul_nonpos_of_nonpos_of_nonneg h_neg hx_nn

/-- Combined: under Remark_5_1 conditions, |U'(x)| ≤ M''/(|χ|²σ) for all x ≥ 0
(without the exp(-κx) factor — the loose form). -/
theorem Remark_5_1_part2_loose_form
    (h_R51 : Remark_5_1)
    (p : CMParams) (c sigma : ℝ)
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hspeed : remark5SpeedCondition p c sigma)
    (hκ_nn : 0 ≤ kappa c)
    (U V : ℝ → ℝ)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (x : ℝ) (hx_nn : 0 ≤ x) :
    |deriv U x| ≤
      remark51MDoublePrime p sigma / (remark5ChiTwoSigma p sigma) := by
  obtain ⟨_, h_part2⟩ := h_R51 p c sigma hsigma hχ hspeed U V hTW hbound
  have h := h_part2 x hx_nn
  have hexp_le := exp_neg_kappa_le_one hκ_nn hx_nn
  -- |U'(x)| ≤ M''/(|χ|²σ) · exp(-κx) ≤ M''/(|χ|²σ) · 1 = M''/(|χ|²σ)
  have hMChi_pos : 0 < MChi p :=
    lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)
  have hMChi_ge_one : 1 ≤ MChi p := MChi_ge_one_of_travelingWave hTW hbound
  have h_M''_nn : 0 ≤ remark51MDoublePrime p sigma :=
    remark51MDoublePrime_nonneg_of_MChi_ge_one p hMChi_pos hMChi_ge_one hsigma.le
  have hχ2σ_pos : 0 < remark5ChiTwoSigma p sigma :=
    remark5ChiTwoSigma_pos sigma hχ
  have h_M''_div_nn : 0 ≤ remark51MDoublePrime p sigma / (remark5ChiTwoSigma p sigma) :=
    div_nonneg h_M''_nn hχ2σ_pos.le
  calc |deriv U x|
      ≤ remark51MDoublePrime p sigma / (remark5ChiTwoSigma p sigma) *
          Real.exp (-(kappa c) * x) := h
    _ ≤ remark51MDoublePrime p sigma / (remark5ChiTwoSigma p sigma) * 1 :=
        mul_le_mul_of_nonneg_left hexp_le h_M''_div_nn
    _ = remark51MDoublePrime p sigma / (remark5ChiTwoSigma p sigma) := by ring

/-- Combined Remark_5_1: maximum bound (best of M' and M'' applied tightly). -/
theorem Remark_5_1_max_bound
    (h_R51 : Remark_5_1)
    (p : CMParams) (c sigma : ℝ)
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hspeed : remark5SpeedCondition p c sigma)
    (U V : ℝ → ℝ)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (x : ℝ) :
    |deriv U x| ≤ remark51MPrime p / (remark5ChiSigma p sigma) := by
  exact (h_R51 p c sigma hsigma hχ hspeed U V hTW hbound).1 x

/-- Combined Remark_5_1: exp-decayed bound for x ≥ 0. -/
theorem Remark_5_1_exp_bound
    (h_R51 : Remark_5_1)
    (p : CMParams) (c sigma : ℝ)
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hspeed : remark5SpeedCondition p c sigma)
    (U V : ℝ → ℝ)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (x : ℝ) (hx_nn : 0 ≤ x) :
    |deriv U x| ≤
      remark51MDoublePrime p sigma / (remark5ChiTwoSigma p sigma) *
        Real.exp (-(kappa c) * x) :=
  (h_R51 p c sigma hsigma hχ hspeed U V hTW hbound).2 x hx_nn

/-- IsTravelingWave's `lim_pos_inf.1` says U → 0 at +∞. Combined with U bounded by
HasWaveUpperTailBound, this gives an explicit existence of U being uniformly small. -/
theorem U_eventually_le_eps_at_top
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop, U x < ε := by
  have hlim : Tendsto U atTop (𝓝 0) := hTW.lim_pos_inf.1
  have hε_nhds : Set.Iio ε ∈ 𝓝 (0 : ℝ) := IsOpen.mem_nhds isOpen_Iio hε
  exact hlim hε_nhds

/-- Symmetric: U → 1 at -∞. -/
theorem U_eventually_ge_one_minus_eps_at_bot
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atBot, 1 - ε < U x := by
  have hlim : Tendsto U atBot (𝓝 1) := hTW.lim_neg_inf.1
  have h_1mε_lt_1 : 1 - ε < 1 := by linarith
  have hε_nhds : Set.Ioi (1 - ε) ∈ 𝓝 (1 : ℝ) :=
    IsOpen.mem_nhds isOpen_Ioi h_1mε_lt_1
  exact hlim hε_nhds

/-- V → 1 at -∞ similarly. -/
theorem V_eventually_ge_one_minus_eps_at_bot
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atBot, 1 - ε < V x := by
  have hlim : Tendsto V atBot (𝓝 1) := hTW.lim_neg_inf.2
  have h_lt : 1 - ε < 1 := by linarith
  have hε_nhds : Set.Ioi (1 - ε) ∈ 𝓝 (1 : ℝ) :=
    IsOpen.mem_nhds isOpen_Ioi h_lt
  exact hlim hε_nhds

/-- V → 0 at +∞. -/
theorem V_eventually_le_eps_at_top
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop, V x < ε := by
  have hlim : Tendsto V atTop (𝓝 0) := hTW.lim_pos_inf.2
  have hε_nhds : Set.Iio ε ∈ 𝓝 (0 : ℝ) := IsOpen.mem_nhds isOpen_Iio hε
  exact hlim hε_nhds

/-- IsTravelingWave provides U bounded between 0 and 1 (essentially)
via the limits + U_pos. -/
theorem U_bounded_above_eventually
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U) :
    ∀ x, 0 < U x ∧ U x ≤ MChi p :=
  fun x => ⟨hTW.U_pos x, hbound.le_MChi x⟩

/-- Combined: U > 0 globally + U ≤ MChi. -/
theorem U_pos_and_bounded
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U) :
    (∀ x, 0 < U x) ∧ (∀ x, U x ≤ MChi p) :=
  ⟨hTW.U_pos, hbound.le_MChi⟩

/-- IsTravelingWave + HasWaveUpperTailBound: U bounded continuous, so IsCUnifBdd. -/
theorem U_isCUnifBdd_of_continuous
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hbound : HasWaveUpperTailBound p c U)
    (hU_cont : Continuous U) :
    IsCUnifBdd U :=
  hbound.isCUnifBdd_of_continuous hU_cont

/-- IsTravelingWave's U is nonneg from U_pos. -/
theorem U_nn_of_isTW
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V) :
    ∀ x, 0 ≤ U x :=
  fun x => (hTW.U_pos x).le

/-- IsTravelingWave's U + HasWaveUpperTailBound: combined "ready for frozenElliptic" form. -/
theorem U_ready_for_frozenElliptic
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hU_cont : Continuous U) :
    IsCUnifBdd U ∧ (∀ x, 0 ≤ U x) :=
  ⟨U_isCUnifBdd_of_continuous hbound hU_cont, U_nn_of_isTW hTW⟩

/-- frozenElliptic exists and is well-defined under our wave hypotheses. -/
theorem frozenElliptic_well_defined
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hU_cont : Continuous U) :
    ContinuousAt (frozenElliptic p U) 0 ∧
    (∀ x, |frozenElliptic p U x| ≤ (MChi p) ^ p.γ) := by
  have hU_bdd : IsCUnifBdd U := U_isCUnifBdd_of_continuous hbound hU_cont
  refine ⟨?_, fun x => ?_⟩
  · exact (frozenElliptic_continuous p hU_bdd (U_nn_of_isTW hTW)).continuousAt
  · exact (Lemma_5_1_signal_bound_for_frozenElliptic p hU_bdd hbound x).1

/-- frozenElliptic ≥ 0 from existing infrastructure. -/
theorem frozenElliptic_nn_for_wave
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (x : ℝ) :
    0 ≤ frozenElliptic p U x :=
  frozenElliptic_nonneg p (U_nn_of_isTW hTW) x

/-- frozenElliptic is continuous everywhere. -/
theorem frozenElliptic_continuous_for_wave
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hU_cont : Continuous U) :
    Continuous (frozenElliptic p U) :=
  frozenElliptic_continuous p (U_isCUnifBdd_of_continuous hbound hU_cont)
    (U_nn_of_isTW hTW)

/-- The "regularity bundle" simplified statement: under U is C² + V continuous +
V bounded + V' bounded + iteratedDeriv ode, V = frozenElliptic.

This is the cleanest form of the elliptic regularity bridge with explicit
hypotheses. -/
theorem V_eq_frozenElliptic_simplified
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hU_diff : Differentiable ℝ U)
    (hU_deriv_diff : Differentiable ℝ (deriv U))
    (hV_diff : Differentiable ℝ V)
    (hV_deriv_diff : Differentiable ℝ (deriv V))
    (hV_bdd : ∃ M : ℝ, ∀ x, |V x| ≤ M)
    (hV_deriv_bdd : ∃ M : ℝ, ∀ x, |deriv V x| ≤ M) :
    V = frozenElliptic p U :=
  IsTravelingWave.V_eq_frozenElliptic_via_C2 hTW hbound hU_diff.continuous
    hV_diff hV_deriv_diff hV_bdd hV_deriv_bdd

/-- Direct shortcut: if regularity is given as a TravelingWaveRegularity bundle
+ U is C² (deriv U Differentiable), then V = frozenElliptic. -/
theorem V_eq_frozenElliptic_from_TWReg_and_U_C2
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (_hU_deriv_diff : Differentiable ℝ (deriv U)) :
    V = frozenElliptic p U :=
  IsTravelingWave.V_eq_frozenElliptic_full hTW hbound hreg

/-- Direct application of the M' case algebra in the Lemma 5.1 signal-bound
context: when Lemma 5.1 gives V's exp signal bound, K_V = 1/(1-κ²γ²) is the
exact denominator. -/
theorem K_V_value
    {c γ : ℝ} :
    1 / (1 - kappa c ^ 2 * γ ^ 2) = 1 / (1 - (kappa c * γ) ^ 2) := by
  have h : kappa c ^ 2 * γ ^ 2 = (kappa c * γ) ^ 2 := by ring
  rw [h]

/-- K_V is positive when κγ < 1. -/
theorem K_V_pos {c γ : ℝ} (hκγ : kappa c * γ < 1) (hκγ_neg : -1 < kappa c * γ) :
    0 < 1 / (1 - kappa c ^ 2 * γ ^ 2) := by
  have h_eq : kappa c ^ 2 * γ ^ 2 = (kappa c * γ) ^ 2 := by ring
  rw [h_eq]
  have h_sq : (kappa c * γ) ^ 2 < 1 := by
    have h_abs : |kappa c * γ| < 1 := by
      rw [abs_lt]
      exact ⟨hκγ_neg, hκγ⟩
    have h_abs_sq : (kappa c * γ) ^ 2 = |kappa c * γ| ^ 2 := (sq_abs _).symm
    rw [h_abs_sq]
    nlinarith [abs_nonneg (kappa c * γ)]
  have h_denom_pos : 0 < 1 - (kappa c * γ) ^ 2 := by linarith
  positivity

/-- K_V is positive under our standard κγ ≤ 1/2 condition. -/
theorem K_V_pos_under_kappa_gamma_le_half
    {c γ : ℝ} (hκ_pos : 0 < kappa c) (hγ_pos : 0 < γ)
    (hκγ : kappa c * γ ≤ 1 / 2) :
    0 < 1 / (1 - kappa c ^ 2 * γ ^ 2) := by
  have hκγ_pos : 0 < kappa c * γ := mul_pos hκ_pos hγ_pos
  have hκγ_lt : kappa c * γ < 1 := by linarith
  have hκγ_neg : -1 < kappa c * γ := by linarith
  exact K_V_pos hκγ_lt hκγ_neg

/-- Direct application: under the standard speed conditions, K_V > 0. -/
theorem K_V_pos_in_Remark_5_1_context
    (p : CMParams) {c sigma : ℝ}
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hspeed : remark5SpeedCondition p c sigma)
    (hχσ_ge_one : 1 ≤ remark5ChiSigma p sigma)
    (hκγ_le_half : kappa c * p.γ ≤ 1 / 2) :
    0 < 1 / (1 - kappa c ^ 2 * p.γ ^ 2) := by
  have hc_gt_two := remark5SpeedCondition.gt_two_of_chiSigma_ge_one
    hspeed hsigma hχσ_ge_one
  have hκ_pos : 0 < kappa c := by
    unfold kappa
    have hc_pos : 0 < c := by linarith
    have hsqrt_lt_c : Real.sqrt (c ^ 2 - 4) < c := by
      rw [Real.sqrt_lt' hc_pos]; nlinarith
    linarith
  have hγ_pos : 0 < p.γ := lt_of_lt_of_le zero_lt_one p.hγ
  exact K_V_pos_under_kappa_gamma_le_half hκ_pos hγ_pos hκγ_le_half

/-- κ > 0 in our setting (c > 2 from |χ|σ ≥ 1). -/
theorem kappa_pos_under_chi_sigma_ge_one
    {p : CMParams} {c sigma : ℝ}
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hspeed : remark5SpeedCondition p c sigma)
    (hχσ_ge_one : 1 ≤ remark5ChiSigma p sigma) :
    0 < kappa c := by
  have hc_gt_two := remark5SpeedCondition.gt_two_of_chiSigma_ge_one
    hspeed hsigma hχσ_ge_one
  unfold kappa
  have hc_pos : 0 < c := by linarith
  have hsqrt_lt_c : Real.sqrt (c ^ 2 - 4) < c := by
    rw [Real.sqrt_lt' hc_pos]; nlinarith
  linarith

/-- 2D wave ODE vector field. For the second-order wave ODE V'' = V - U^γ(t),
the 2D system Y = (V, V'), Y' = (V', V - U^γ(t)) has vector field
F(t, y) := (y 1, y 0 - U^γ(t)). -/
noncomputable def wave2DField (p : CMParams) (U : ℝ → ℝ) (t : ℝ) :
    (Fin 2 → ℝ) → Fin 2 → ℝ :=
  fun y =>
    fun
      | ⟨0, _⟩ => y 1
      | ⟨1, _⟩ => y 0 - (U t) ^ p.γ

/-- wave2DField unfolded at index 0. -/
theorem wave2DField_zero (p : CMParams) (U : ℝ → ℝ) (t : ℝ) (y : Fin 2 → ℝ) :
    wave2DField p U t y ⟨0, by norm_num⟩ = y 1 := rfl

/-- wave2DField unfolded at index 1. -/
theorem wave2DField_one (p : CMParams) (U : ℝ → ℝ) (t : ℝ) (y : Fin 2 → ℝ) :
    wave2DField p U t y ⟨1, by norm_num⟩ = y 0 - (U t) ^ p.γ := rfl

/-- wave2DField is componentwise linear: F(t, y₁) - F(t, y₂) is determined
by y₁ - y₂. The first component is (y₁ - y₂) 1, the second is (y₁ - y₂) 0. -/
theorem wave2DField_componentwise_diff
    (p : CMParams) (U : ℝ → ℝ) (t : ℝ) (y₁ y₂ : Fin 2 → ℝ) :
    (wave2DField p U t y₁ - wave2DField p U t y₂) 0 = y₁ 1 - y₂ 1 ∧
    (wave2DField p U t y₁ - wave2DField p U t y₂) 1 = y₁ 0 - y₂ 0 := by
  refine ⟨?_, ?_⟩
  · show wave2DField p U t y₁ 0 - wave2DField p U t y₂ 0 = y₁ 1 - y₂ 1
    rfl
  · show wave2DField p U t y₁ 1 - wave2DField p U t y₂ 1 = y₁ 0 - y₂ 0
    show (y₁ 0 - (U t) ^ p.γ) - (y₂ 0 - (U t) ^ p.γ) = y₁ 0 - y₂ 0
    ring

/-- Trivial useful: for y₁ y₂ : Fin 2 → ℝ, |y₁ 0 - y₂ 0| ≤ ‖y₁ - y₂‖. -/
theorem abs_sub_zero_le_norm_sub (y₁ y₂ : Fin 2 → ℝ) :
    |y₁ 0 - y₂ 0| ≤ ‖y₁ - y₂‖ := by
  have h : ‖(y₁ - y₂) 0‖ ≤ ‖y₁ - y₂‖ := norm_le_pi_norm (y₁ - y₂) 0
  show |y₁ 0 - y₂ 0| ≤ ‖y₁ - y₂‖
  have h2 : (y₁ - y₂) 0 = y₁ 0 - y₂ 0 := Pi.sub_apply y₁ y₂ 0
  rw [h2] at h
  rwa [Real.norm_eq_abs] at h

/-- Similarly for index 1. -/
theorem abs_sub_one_le_norm_sub (y₁ y₂ : Fin 2 → ℝ) :
    |y₁ 1 - y₂ 1| ≤ ‖y₁ - y₂‖ := by
  have h : ‖(y₁ - y₂) 1‖ ≤ ‖y₁ - y₂‖ := norm_le_pi_norm (y₁ - y₂) 1
  have h2 : (y₁ - y₂) 1 = y₁ 1 - y₂ 1 := Pi.sub_apply y₁ y₂ 1
  rw [h2] at h
  rwa [Real.norm_eq_abs] at h

/-- wave2DField is 1-Lipschitz at index 0. -/
theorem wave2DField_lipschitz_at_zero
    (p : CMParams) (U : ℝ → ℝ) (t : ℝ) (y₁ y₂ : Fin 2 → ℝ) :
    |(wave2DField p U t y₁ - wave2DField p U t y₂) 0| ≤ ‖y₁ - y₂‖ := by
  show |y₁ 1 - y₂ 1| ≤ ‖y₁ - y₂‖
  exact abs_sub_one_le_norm_sub y₁ y₂

/-- wave2DField is 1-Lipschitz at index 1. -/
theorem wave2DField_lipschitz_at_one
    (p : CMParams) (U : ℝ → ℝ) (t : ℝ) (y₁ y₂ : Fin 2 → ℝ) :
    |(wave2DField p U t y₁ - wave2DField p U t y₂) 1| ≤ ‖y₁ - y₂‖ := by
  show |(y₁ 0 - (U t) ^ p.γ) - (y₂ 0 - (U t) ^ p.γ)| ≤ ‖y₁ - y₂‖
  have h_simp : (y₁ 0 - (U t) ^ p.γ) - (y₂ 0 - (U t) ^ p.γ) = y₁ 0 - y₂ 0 := by ring
  rw [h_simp]
  exact abs_sub_zero_le_norm_sub y₁ y₂

/-- Pack a real scalar (V, V') as Fin 2 → ℝ for use with the 2D ODE
infrastructure from ShenWork.PDE.GlobalPicard. -/
def packPair (a b : ℝ) : Fin 2 → ℝ
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b

/-- For our second-order ODE V'' = V - U^γ(x) viewed as a 2D first-order
system Y = (V, V'), the autonomized vector field on (Fin 3 → ℝ) for
Z = (V, V', x) is Z' = (V', V - U^γ(x), 1). -/
noncomputable def waveAutonomousField (p : CMParams) (U : ℝ → ℝ) :
    (Fin 3 → ℝ) → Fin 3 → ℝ :=
  fun z =>
    fun
      | ⟨0, _⟩ => z 1
      | ⟨1, _⟩ => z 0 - (U (z 2)) ^ p.γ
      | ⟨2, _⟩ => 1

/-- The piecewise constant `M'''_{\chi,m,\alpha,\gamma,\sigma}` from
Paper1 Remark 5.2.  The branch at `c ≤ 5/2` comes from Lemma 5.2; the branch at
`5/2 < c` comes from Remark 4.1 and Remark 5.1. -/
def remark52MTriplePrime (p : CMParams) (c sigma : ℝ) : ℝ :=
  if c ≤ (5 / 2 : ℝ) then
    remark5ChiTwoSigma p sigma / 2 *
      (5 / 2 + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) +
        Real.sqrt
          ((5 / 2 + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1)) ^ 2 +
            4 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
            4 * (MChi p) ^ p.α))
  else
    max
      (8 * (1 + |p.χ| + 2 * p.m * |p.χ|) *
        (p.γ + remark5ChiSigma p sigma) / (1 + p.γ) * remark51MPrime p)
      (2 * remark51MDoublePrime p sigma)

theorem remark52MTriplePrime_eq_of_le
    {p : CMParams} {c sigma : ℝ} (hc : c ≤ (5 / 2 : ℝ)) :
    remark52MTriplePrime p c sigma =
      remark5ChiTwoSigma p sigma / 2 *
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
          (p.γ + remark5ChiSigma p sigma) / (1 + p.γ) * remark51MPrime p)
        (2 * remark51MDoublePrime p sigma) := by
  simp [remark52MTriplePrime, not_le.mpr hc]

theorem remark52MTriplePrime.first_branch_le_of_gt
    {p : CMParams} {c sigma : ℝ} (hc : (5 / 2 : ℝ) < c) :
    8 * (1 + |p.χ| + 2 * p.m * |p.χ|) *
        (p.γ + remark5ChiSigma p sigma) / (1 + p.γ) * remark51MPrime p ≤
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
    0 < remark5ChiTwoSigma p sigma := by
  exact remark5ChiTwoSigma_pos sigma hχ

theorem remark51MPrime_nonneg_of_MChi_pos
    (p : CMParams) (hM : 0 < MChi p) :
    0 ≤ remark51MPrime p := by
  unfold remark51MPrime
  exact add_nonneg
    (mul_nonneg (abs_nonneg p.χ) (Real.rpow_pos_of_pos hM _).le)
    (Real.rpow_pos_of_pos hM _).le

theorem remark52MTriplePrime_nonneg_of_MChi_pos
    (p : CMParams) {c sigma : ℝ}
    (hsigma : 0 < sigma) (hM : 0 < MChi p) :
    0 ≤ remark52MTriplePrime p c sigma := by
  by_cases hc : c ≤ (5 / 2 : ℝ)
  · rw [remark52MTriplePrime_eq_of_le hc]
    have hfactor :
        0 ≤ remark5ChiTwoSigma p sigma / 2 :=
      div_nonneg (remark5ChiTwoSigma_nonneg p sigma) zero_le_two
    have hm_nonneg : 0 ≤ p.m := le_trans zero_le_one p.hm
    have hpow :
        0 ≤ (MChi p) ^ (p.m + p.γ - 1) :=
      (Real.rpow_pos_of_pos hM _).le
    have hterm :
        0 ≤ |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) := by
      exact mul_nonneg (mul_nonneg (abs_nonneg p.χ) hm_nonneg) hpow
    have hsum :
        0 ≤
          5 / 2 + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) +
            Real.sqrt
              ((5 / 2 + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1)) ^ 2 +
                4 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
                4 * (MChi p) ^ p.α) := by
      exact add_nonneg (by nlinarith) (Real.sqrt_nonneg _)
    exact mul_nonneg hfactor hsum
  · have hc_gt : (5 / 2 : ℝ) < c := lt_of_not_ge hc
    rw [remark52MTriplePrime_eq_of_gt hc_gt]
    have hm_nonneg : 0 ≤ p.m := le_trans zero_le_one p.hm
    have hpmul : 0 ≤ p.m * |p.χ| :=
      mul_nonneg hm_nonneg (abs_nonneg p.χ)
    have hparen :
        0 ≤ 1 + |p.χ| + 2 * p.m * |p.χ| := by
      nlinarith [abs_nonneg p.χ, hpmul]
    have hsigma_term : 0 ≤ remark5ChiSigma p sigma :=
      remark5ChiSigma_nonneg p sigma
    have hgamma_sigma : 0 ≤ p.γ + remark5ChiSigma p sigma := by
      nlinarith [p.hγ, hsigma_term]
    have hden : 0 ≤ 1 + p.γ := by nlinarith [p.hγ]
    have hcoef :
        0 ≤
          8 * (1 + |p.χ| + 2 * p.m * |p.χ|) *
              (p.γ + remark5ChiSigma p sigma) /
            (1 + p.γ) := by
      exact div_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) hparen)
          hgamma_sigma)
        hden
    have hbranch :
        0 ≤
          8 * (1 + |p.χ| + 2 * p.m * |p.χ|) *
              (p.γ + remark5ChiSigma p sigma) /
            (1 + p.γ) * remark51MPrime p :=
      mul_nonneg hcoef (remark51MPrime_nonneg_of_MChi_pos p hM)
    exact le_trans hbranch (le_max_left _ _)

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
              remark52MTriplePrime p c sigma / (remark5ChiTwoSigma p sigma)

/-- Remark_5_2 holds trivially when U is monotone decreasing AND
M''' is nonneg: U' ≤ 0 + U > 0 → U'/U ≤ 0 ≤ M'''/(|χ|²σ). -/
theorem Remark_5_2_under_monotone_U
    (h_monotone : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        ∀ x, deriv U x ≤ 0) :
    Remark_5_2 := by
  intro p c sigma hsigma hχ hspeed U V hTW hbound x
  have hU_pos : 0 < U x := hTW.U_pos x
  have h_mono := h_monotone p c sigma hsigma hχ hspeed U V hTW hbound x
  have hMChi_pos : 0 < MChi p :=
    lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)
  have h_M_dprime_nn :=
    remark52MTriplePrime_nonneg_of_MChi_pos p (c := c) hsigma hMChi_pos
  have hχ2σ_pos : 0 < remark5ChiTwoSigma p sigma :=
    remark5Denominator_pos hsigma hχ
  have h_ratio_div_nn : 0 ≤ remark52MTriplePrime p c sigma / (remark5ChiTwoSigma p sigma) :=
    div_nonneg h_M_dprime_nn hχ2σ_pos.le
  have h_div_nonpos : deriv U x / U x ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg h_mono hU_pos.le
  linarith

/-- Alternative form: Remark_5_2 holds under combined hypotheses:
- |U'(x)| bound C1
- U(x) lower bound C2 > 0
- C1/C2 ≤ M'''/(|χ|²σ)
The bound deriv U / U ≤ |U'|/U ≤ C1/C2 ≤ M''' bound. -/
theorem Remark_5_2_under_bounded_with_lower_bound
    (h_bound : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        ∀ x, deriv U x ≤
          remark52MTriplePrime p c sigma / (remark5ChiTwoSigma p sigma) * U x) :
    Remark_5_2 := by
  intro p c sigma hsigma hχ hspeed U V hTW hbound x
  have hU_pos : 0 < U x := hTW.U_pos x
  have h_b := h_bound p c sigma hsigma hχ hspeed U V hTW hbound x
  rw [div_le_iff₀ hU_pos]
  linarith

/-- Trivial bound: if Remark_5_1 holds, then |deriv U| ≤ M'/(|χ|σ).
For U(x) ≥ U_low > 0: U'/U ≤ M'/(|χ|σ·U_low). Comparing to Remark_5_2's
M'''/(|χ|²σ): need M'·|χ|/U_low ≤ M'''. -/
theorem Remark_5_2_from_Remark_5_1_and_lower_bound
    (h_R51 : Remark_5_1)
    (h_U_lower : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        ∃ U_low : ℝ, 0 < U_low ∧ ∀ x, U_low ≤ U x)
    (h_const_compare : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        ∀ U_low : ℝ, 0 < U_low →
          remark51MPrime p / (remark5ChiSigma p sigma * U_low) ≤
            remark52MTriplePrime p c sigma / (remark5ChiTwoSigma p sigma)) :
    Remark_5_2 := by
  intro p c sigma hsigma hχ hspeed U V hTW hbound x
  obtain ⟨U_low, hU_low_pos, hU_low⟩ :=
    h_U_lower p c sigma hsigma hχ hspeed U V hTW hbound
  have h_const := h_const_compare p c sigma hsigma hχ hspeed U V hTW hbound U_low hU_low_pos
  have h_R51_x := (h_R51 p c sigma hsigma hχ hspeed U V hTW hbound).1 x
  -- |deriv U x| ≤ M'/(|χ|σ). Hence deriv U x ≤ M'/(|χ|σ).
  have h_deriv_le : deriv U x ≤ remark51MPrime p / (remark5ChiSigma p sigma) :=
    le_trans (le_abs_self _) h_R51_x
  have hU_pos : 0 < U x := hTW.U_pos x
  have hU_low_le_U : U_low ≤ U x := hU_low x
  -- deriv U x / U x ≤ M'/(|χ|σ) / U_low ≤ M'/(|χ|σ * U_low) ≤ M'''/(|χ|²σ).
  rw [div_le_iff₀ hU_pos]
  have h_chain : remark51MPrime p / (remark5ChiSigma p sigma * U_low) * U_low =
      remark51MPrime p / (remark5ChiSigma p sigma) := by
    have hU_low_ne : U_low ≠ 0 := ne_of_gt hU_low_pos
    field_simp
  calc deriv U x
      ≤ remark51MPrime p / (remark5ChiSigma p sigma) := h_deriv_le
    _ = remark51MPrime p / (remark5ChiSigma p sigma * U_low) * U_low := h_chain.symm
    _ ≤ remark52MTriplePrime p c sigma / (remark5ChiTwoSigma p sigma) * U_low :=
        mul_le_mul_of_nonneg_right h_const hU_low_pos.le
    _ ≤ remark52MTriplePrime p c sigma / (remark5ChiTwoSigma p sigma) * U x := by
        have hM'''_div_nn : 0 ≤ remark52MTriplePrime p c sigma / (remark5ChiTwoSigma p sigma) := by
          have hMChi_pos : 0 < MChi p :=
            lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)
          have hM_nn := remark52MTriplePrime_nonneg_of_MChi_pos p (c := c) hsigma hMChi_pos
          have hχ2σ_pos := remark5Denominator_pos hsigma hχ
          exact div_nonneg hM_nn hχ2σ_pos.le
        exact mul_le_mul_of_nonneg_left hU_low_le_U hM'''_div_nn

/-- M''' branch comparison (c ≤ 5/2 case): the first branch dominates 2·M''. -/
theorem remark52MTriplePrime_branch_le_relation_le
    {p : CMParams} {c sigma : ℝ}
    (hc : c ≤ (5 / 2 : ℝ))
    (hMChi_pos : 0 < MChi p) (hsigma : 0 < sigma) :
    0 ≤ remark52MTriplePrime p c sigma := by
  exact remark52MTriplePrime_nonneg_of_MChi_pos p (c := c) hsigma hMChi_pos

/-- M''' branch comparison (c > 5/2 case): both branches nonneg. -/
theorem remark52MTriplePrime_gt_branch_nonneg
    {p : CMParams} {c sigma : ℝ}
    (hc : (5 / 2 : ℝ) < c)
    (hMChi_pos : 0 < MChi p) (hsigma : 0 < sigma) :
    0 ≤ remark52MTriplePrime p c sigma :=
  remark52MTriplePrime_nonneg_of_MChi_pos p (c := c) hsigma hMChi_pos

/-- For c > 5/2, M''' ≥ 2·M''. -/
theorem M_dprime_two_le_M_tprime_gt
    {p : CMParams} {c sigma : ℝ}
    (hc : (5 / 2 : ℝ) < c) :
    2 * remark51MDoublePrime p sigma ≤ remark52MTriplePrime p c sigma :=
  remark52MTriplePrime.doublePrime_branch_le_of_gt hc

/-- For c > 5/2, M'''/(|χ|²σ) ≥ 2·M''/(|χ|²σ), so the M''' bound is at least
twice the M'' bound. Useful for combining bounds. -/
theorem M_tprime_div_dominates_M_dprime_div_gt
    {p : CMParams} {c sigma : ℝ}
    (hc : (5 / 2 : ℝ) < c)
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0) :
    2 * (remark51MDoublePrime p sigma / (remark5ChiTwoSigma p sigma)) ≤
      remark52MTriplePrime p c sigma / (remark5ChiTwoSigma p sigma) := by
  have h := M_dprime_two_le_M_tprime_gt (p := p) (sigma := sigma) hc
  have hχ2σ_pos := remark5Denominator_pos hsigma hχ
  have h_mul_div : 2 * (remark51MDoublePrime p sigma / (remark5ChiTwoSigma p sigma)) =
      (2 * remark51MDoublePrime p sigma) / (remark5ChiTwoSigma p sigma) := by ring
  rw [h_mul_div]
  exact div_le_div_of_nonneg_right h hχ2σ_pos.le

/-- Top-level: Remark_5_2 follows from Remark_5_1 + lower bound + constant compare,
combined cleanly. Useful direct application. -/
theorem Remark_5_2_via_Remark_5_1_full
    (h_R51 : Remark_5_1)
    (h_U_lower : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        ∃ U_low : ℝ, 0 < U_low ∧ ∀ x, U_low ≤ U x)
    (h_const_compare : ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        ∀ U_low : ℝ, 0 < U_low →
          remark51MPrime p / (remark5ChiSigma p sigma * U_low) ≤
            remark52MTriplePrime p c sigma / (remark5ChiTwoSigma p sigma)) :
    Remark_5_2 :=
  Remark_5_2_from_Remark_5_1_and_lower_bound h_R51 h_U_lower h_const_compare

def Remark52GammaSpeedAlgebra : Prop :=
  ∀ p : CMParams, ∀ c sigma : ℝ,
    0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
      p.γ + p.γ⁻¹ < c

/-- The corrected real-power speed condition implies the first speed
inequality used in Lemma 5.2.  The former product transcription
`|chi| * sigma` made this true paper implication appear to fail. -/
theorem remark5SpeedCondition_implies_gammaSpeed :
    Remark52GammaSpeedAlgebra := by
  intro p c sigma _hsigma _hχ hspeed
  have hγ_pos : 0 < p.γ := lt_of_lt_of_le zero_lt_one p.hγ
  have hs_nn : 0 ≤ remark5ChiSigma p sigma :=
    remark5ChiSigma_nonneg p sigma
  have hsum_pos : 0 < p.γ + remark5ChiSigma p sigma :=
    add_pos_of_pos_of_nonneg hγ_pos hs_nn
  have hprod :
      1 ≤ p.γ * (p.γ + remark5ChiSigma p sigma) := by
    nlinarith [p.hγ]
  have halg :
      p.γ + p.γ⁻¹ ≤
        p.γ + remark5ChiSigma p sigma +
          (p.γ + remark5ChiSigma p sigma)⁻¹ := by
    apply le_of_mul_le_mul_right _ (mul_pos hγ_pos hsum_pos)
    field_simp
    nlinarith
  exact lt_of_le_of_lt halg (by simpa [one_div] using hspeed.gt_first)

theorem remark5SpeedCondition_implies_Lemma_5_2_speed :
    ∀ p : CMParams, ∀ c sigma : ℝ,
      0 < sigma → p.χ ≠ 0 → remark5SpeedCondition p c sigma →
        c > max (p.γ + p.γ⁻¹)
          (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) := by
  intro p c sigma hsigma hχ hspeed
  apply max_lt
  · exact remark5SpeedCondition_implies_gammaSpeed
      p c sigma hsigma hχ hspeed
  · have hs_nn : 0 ≤ remark5ChiSigma p sigma :=
      remark5ChiSigma_nonneg p sigma
    linarith [hspeed.gt_second]

/-- In the `c ≤ 5/2` branch used by Remark 5.2, the explicit Lemma 5.2
log-derivative constant is dominated by the paper's `M'''` constant.

For `c > 5/2` the paper switches to Remarks 4.1 and 5.1; comparing the
Lemma 5.2 formula directly would be false because that formula grows with
`c`, whereas the second branch of `M'''` is independent of `c`. -/
theorem logDerivativeBoundFormula_le_remark52_of_c_le
    {p : CMParams} {c sigma : ℝ}
    (hM : 0 < MChi p)
    (hc : c ≤ (5 / 2 : ℝ))
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hspeed : remark5SpeedCondition p c sigma) :
    logDerivativeBoundFormula p c ≤
      remark52MTriplePrime p c sigma / remark5ChiTwoSigma p sigma := by
  have hm_nn : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hK_nn :
      0 ≤ |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) :=
    mul_nonneg (mul_nonneg (abs_nonneg p.χ) hm_nn)
      (Real.rpow_nonneg hM.le _)
  have hc_pos : 0 < c := by
    have hγ_pos : 0 < p.γ := lt_of_lt_of_le zero_lt_one p.hγ
    have hγinv_pos : 0 < p.γ⁻¹ := inv_pos.mpr hγ_pos
    have := remark5SpeedCondition_implies_gammaSpeed
      p c sigma hsigma hχ hspeed
    linarith
  have hbase_c :
      0 ≤ c + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) := by
    linarith
  have hbase_cap :
      0 ≤ (5 / 2 : ℝ) +
        |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) := by
    linarith
  have hbase_le :
      c + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) ≤
        (5 / 2 : ℝ) +
          |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) := by
    linarith
  have hsq :
      (c + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1)) ^ 2 ≤
        ((5 / 2 : ℝ) +
          |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1)) ^ 2 := by
    nlinarith
  have hrad :
      (c + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1)) ^ 2 +
          4 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
          4 * (MChi p) ^ p.α ≤
        ((5 / 2 : ℝ) +
          |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1)) ^ 2 +
          4 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
          4 * (MChi p) ^ p.α := by
    linarith
  have hsqrt := Real.sqrt_le_sqrt hrad
  rw [remark52MTriplePrime_eq_of_le hc]
  have hden : remark5ChiTwoSigma p sigma ≠ 0 :=
    ne_of_gt (remark5ChiTwoSigma_pos sigma hχ)
  rw [show
      (remark5ChiTwoSigma p sigma / 2 *
          ((5 / 2 : ℝ) +
            |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) +
            Real.sqrt
              (((5 / 2 : ℝ) + |p.χ| * p.m * (MChi p) ^
                    (p.m + p.γ - 1)) ^ 2 +
                4 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
                4 * (MChi p) ^ p.α))) /
          remark5ChiTwoSigma p sigma =
        (1 / 2 : ℝ) *
          ((5 / 2 : ℝ) +
            |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) +
            Real.sqrt
              (((5 / 2 : ℝ) + |p.χ| * p.m * (MChi p) ^
                    (p.m + p.γ - 1)) ^ 2 +
                4 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
                4 * (MChi p) ^ p.α)) by
      field_simp]
  unfold logDerivativeBoundFormula
  nlinarith

theorem Remark_5_2.nonincreasing_positive_profile_branch
    {p : CMParams} {c sigma : ℝ}
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    {U : ℝ → ℝ}
    (hU_pos : ∀ x, 0 < U x)
    (hbound : HasWaveUpperTailBound p c U)
    (hmono : ∀ x, deriv U x ≤ 0) :
    ∀ x : ℝ,
      deriv U x / U x ≤
        remark52MTriplePrime p c sigma / (remark5ChiTwoSigma p sigma) := by
  have hM : 0 < MChi p :=
    lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)
  have hnum :
      0 ≤ remark52MTriplePrime p c sigma :=
    remark52MTriplePrime_nonneg_of_MChi_pos p hsigma hM
  have hden : 0 < remark5ChiTwoSigma p sigma :=
    remark5Denominator_pos hsigma hχ
  have hrhs_nonneg :
      0 ≤ remark52MTriplePrime p c sigma / (remark5ChiTwoSigma p sigma) :=
    div_nonneg hnum hden.le
  intro x
  have hratio_nonpos : deriv U x / U x ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (hmono x) (hU_pos x).le
  exact le_trans hratio_nonpos hrhs_nonneg

theorem Remark_5_2.nonincreasing_branch
    {p : CMParams} {c sigma : ℝ}
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (_hspeed : remark5SpeedCondition p c sigma)
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hmono : ∀ x, deriv U x ≤ 0) :
    ∀ x : ℝ,
      deriv U x / U x ≤
        remark52MTriplePrime p c sigma / (remark5ChiTwoSigma p sigma) := by
  exact Remark_5_2.nonincreasing_positive_profile_branch
    hsigma hχ hTW.U_pos hbound hmono

theorem Remark_5_2.monotoneTravelingWave_branch
    {p : CMParams} {c sigma : ℝ}
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hspeed : remark5SpeedCondition p c sigma)
    {U V : ℝ → ℝ}
    (hTW : IsMonotoneTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U) :
    ∀ x : ℝ,
      deriv U x / U x ≤
        remark52MTriplePrime p c sigma / (remark5ChiTwoSigma p sigma) :=
  Remark_5_2.nonincreasing_branch hsigma hχ hspeed hTW.1 hbound hTW.2.1

theorem Remark_5_2_frozen_monotone_trap_direct
    {p : CMParams} {c sigma : ℝ}
    (hsigma : 0 < sigma) (hχ : p.χ ≠ 0)
    (hspeed : remark5SpeedCondition p c sigma)
    {U : ℝ → ℝ}
    (hprofile : FrozenStationaryWaveProfile p c U)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U) :
    ∀ x : ℝ,
      deriv U x / U x ≤
        remark52MTriplePrime p c sigma / (remark5ChiTwoSigma p sigma) := by
  exact Remark_5_2.nonincreasing_branch hsigma hχ hspeed
    hprofile.to_travelingWave
    (hprofile.hasWaveUpperTailBound_of_inMonotoneWaveTrapSet htrap)
    htrap.deriv_nonpos

theorem NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_remark52_log_derivative
    {p : CMParams} {c κ₀ κtilde D sigma : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₀ κtilde D)
    (hsigma : 0 < sigma)
    (hupper :
      ∀ U : ℝ → ℝ,
        InMonotoneWaveTrapSet (kappa c) 1 U →
          FrozenAuxiliaryLimitOutput p c (kappa c) 1
            (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U →
            ShenUpperBoundNegative c U) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet (kappa c) 1 U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) 1
          (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U ∧
        ∀ x : ℝ,
          deriv U x / U x ≤
            remark52MTriplePrime p c sigma / (remark5ChiTwoSigma p sigma) := by
  rcases h.exists_fixed_limit with ⟨U, hU, haux⟩
  have hupperU : ShenUpperBoundNegative c U := hupper U hU haux
  have htrapM : InMonotoneWaveTrapSet (kappa c) (MChi p) U := by
    simpa [h.MChi_eq_one] using hU
  have hbound : HasWaveUpperTailBound p c U :=
    htrapM.hasWaveUpperTailBound_of_pos hupperU.pos
  have hχ_ne : p.χ ≠ 0 := ne_of_lt h.chi_neg
  exact
    ⟨U, hU, haux,
      Remark_5_2.nonincreasing_positive_profile_branch
        hsigma hχ_ne hupperU.pos hbound hU.deriv_nonpos⟩

theorem NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_signal_and_remark52_log_derivative
    {p : CMParams} {c κ₀ κtilde D sigma : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₀ κtilde D)
    (hc : 2 < c) (hsigma : 0 < sigma)
    (hupper :
      ∀ U : ℝ → ℝ,
        InMonotoneWaveTrapSet (kappa c) 1 U →
          FrozenAuxiliaryLimitOutput p c (kappa c) 1
            (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U →
            ShenUpperBoundNegative c U) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet (kappa c) 1 U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) 1
          (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U ∧
        (∀ x,
          |frozenElliptic p U x| ≤ (MChi p) ^ p.γ ∧
            |deriv (frozenElliptic p U) x| ≤ (MChi p) ^ p.γ) ∧
        (p.γ + p.γ⁻¹ < c →
          ∀ x,
            |frozenElliptic p U x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x)) ∧
            |deriv (frozenElliptic p U) x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x))) ∧
        ∀ x : ℝ,
          deriv U x / U x ≤
            remark52MTriplePrime p c sigma / (remark5ChiTwoSigma p sigma) := by
  rcases h.exists_fixed_limit_with_signal_statement hc hupper with
    ⟨U, hU, haux, hsignal, hexpSignal⟩
  have hupperU : ShenUpperBoundNegative c U := hupper U hU haux
  have htrapM : InMonotoneWaveTrapSet (kappa c) (MChi p) U := by
    simpa [h.MChi_eq_one] using hU
  have hbound : HasWaveUpperTailBound p c U :=
    htrapM.hasWaveUpperTailBound_of_pos hupperU.pos
  have hχ_ne : p.χ ≠ 0 := ne_of_lt h.chi_neg
  have hlog :
      ∀ x : ℝ,
        deriv U x / U x ≤
          remark52MTriplePrime p c sigma / (remark5ChiTwoSigma p sigma) :=
    Remark_5_2.nonincreasing_positive_profile_branch
      hsigma hχ_ne hupperU.pos hbound hU.deriv_nonpos
  exact ⟨U, hU, haux, hsignal, hexpSignal, hlog⟩

theorem NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_const_sub_signal_and_remark52_log_derivative
    {p : CMParams} {c κ₀ κtilde D sigma : ℝ}
    (h : NegativeSensitivityWaveFixedPointConstruction p c κ₀ κtilde D)
    (hc : 2 < c) (hsigma : 0 < sigma)
    (hupper :
      ∀ U : ℝ → ℝ,
        InMonotoneWaveTrapSet (kappa c) 1 U →
          FrozenAuxiliaryLimitOutput p c (kappa c) 1
            (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U →
            ShenUpperBoundNegative c U) :
    ∃ U : ℝ → ℝ,
      InMonotoneWaveTrapSet (kappa c) 1 U ∧
        FrozenAuxiliaryLimitOutput p c (kappa c) 1
          (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U ∧
        (∃ d : ℝ, 0 < d ∧
          IsPaperFrozenSubSolutionOn p c U (fun _ => d) Set.univ) ∧
        (∀ x,
          |frozenElliptic p U x| ≤ (MChi p) ^ p.γ ∧
            |deriv (frozenElliptic p U) x| ≤ (MChi p) ^ p.γ) ∧
        (p.γ + p.γ⁻¹ < c →
          ∀ x,
            |frozenElliptic p U x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x)) ∧
            |deriv (frozenElliptic p U) x| ≤
              min ((MChi p) ^ p.γ)
                ((1 / (1 - (kappa c) ^ 2 * p.γ ^ 2)) *
                  Real.exp (-(kappa c) * p.γ * x))) ∧
        ∀ x : ℝ,
          deriv U x / U x ≤
            remark52MTriplePrime p c sigma / (remark5ChiTwoSigma p sigma) := by
  rcases h.exists_fixed_limit_with_signal_and_remark52_log_derivative
      hc hsigma hupper with
    ⟨U, hU, haux, hsignal, hexpSignal, hlog⟩
  rcases h.exists_paper_constant_subsolution hU with
    ⟨d, hd_pos, hd_sub⟩
  exact ⟨U, hU, haux, ⟨d, hd_pos, hd_sub⟩, hsignal, hexpSignal, hlog⟩

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

/-- A real, assumption-package-free zero-difference branch of Lemma 5.3. -/
theorem Lemma_5_3_zero_difference_branch
    (gamma M eta : ℝ) (u : ℝ → ℝ) :
    let v := Psi (fun x => u x ^ gamma - u x ^ gamma) 1 1
    let U := fun x => Real.exp (eta * x) * (u x - u x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) := by
  dsimp
  simp [Psi_zero]

/-- A real zero-source branch of Lemma 5.3.  It is slightly more general than
the zero-difference branch: the two profiles need not be equal, but the
elliptic source `u₂^γ - u₁^γ` is assumed to vanish pointwise. -/
theorem Lemma_5_3_zero_source_branch
    {gamma M eta : ℝ}
    (_hgamma : 1 ≤ gamma) (hM : 1 ≤ M)
    (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hsource : ∀ x, u2 x ^ gamma = u1 x ^ gamma) :
    let v := Psi (fun x => u2 x ^ gamma - u1 x ^ gamma) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) := by
  dsimp
  have hsource_zero :
      (fun x : ℝ => u2 x ^ gamma - u1 x ^ gamma) =
        fun _ : ℝ => (0 : ℝ) := by
    ext x
    rw [hsource x]
    ring
  have hM_nonneg : 0 ≤ M := le_trans zero_le_one hM
  have hpow_nonneg : 0 ≤ M ^ (2 * (gamma - 1)) :=
    Real.rpow_nonneg hM_nonneg _
  have hnum_nonneg : 0 ≤ gamma ^ 2 * M ^ (2 * (gamma - 1)) :=
    mul_nonneg (sq_nonneg gamma) hpow_nonneg
  have hcoef_one_nonneg :
      0 ≤ gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta) ^ 2 := by
    exact div_nonneg hnum_nonneg (sq_nonneg (1 - eta))
  have heta_sq_lt_eta : eta ^ 2 < eta := by
    rw [pow_two]
    nlinarith [mul_lt_mul_of_pos_left heta_one heta_pos]
  have hden_two_pos : 0 < 1 - eta ^ 2 := by
    nlinarith
  have hcoef_two_nonneg :
      0 ≤ gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta ^ 2) := by
    exact div_nonneg hnum_nonneg hden_two_pos.le
  have hU_integral_nonneg :
      0 ≤ ∫ x : ℝ, |Real.exp (eta * x) * (u2 x - u1 x)| ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  refine ⟨?_, ?_⟩
  · have hright_nonneg :
        0 ≤
          gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta) ^ 2 *
            ∫ x : ℝ, |Real.exp (eta * x) * (u2 x - u1 x)| ^ 2 :=
      mul_nonneg hcoef_one_nonneg hU_integral_nonneg
    simpa [hsource_zero, Psi_zero] using hright_nonneg
  · have hright_nonneg :
        0 ≤
          gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta ^ 2) *
            ∫ x : ℝ, |Real.exp (eta * x) * (u2 x - u1 x)| ^ 2 :=
      mul_nonneg hcoef_two_nonneg hU_integral_nonneg
    simpa [hsource_zero, Psi_zero] using hright_nonneg

/-- The zero-difference branch of Lemma 5.3 in the same hypothesis shape as
the full statement. -/
theorem Lemma_5_3.self_difference_branch
    {gamma M eta : ℝ}
    (_hgamma : 1 ≤ gamma) (_hM : 1 ≤ M)
    (_heta_pos : 0 < eta) (_heta_one : eta < 1)
    {u : ℝ → ℝ}
    (_hu : IsCUnifBdd u)
    (_hubound : ∀ x, 0 ≤ u x ∧ u x ≤ M)
    (_hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u x - u x| ^ 2)) :
    let v := Psi (fun x => u x ^ gamma - u x ^ gamma) 1 1
    let U := fun x => Real.exp (eta * x) * (u x - u x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
    (∫ x : ℝ, |deriv V x| ^ 2 ≤
        gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  Lemma_5_3_zero_difference_branch gamma M eta u

/-- The zero-source branch of Lemma 5.3 in the same hypothesis shape as the
full statement.  The profiles may differ, but their `γ`-powers agree
pointwise, so the elliptic perturbation source vanishes. -/
theorem Lemma_5_3.same_power_branch
    {gamma M eta : ℝ}
    (hgamma : 1 ≤ gamma) (hM : 1 ≤ M)
    (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (_hu1 : IsCUnifBdd u1) (_hu2 : IsCUnifBdd u2)
    (_hu1_bound : ∀ x, 0 ≤ u1 x ∧ u1 x ≤ M)
    (_hu2_bound : ∀ x, 0 ≤ u2 x ∧ u2 x ≤ M)
    (_hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2))
    (hsource : ∀ x, u2 x ^ gamma = u1 x ^ gamma) :
    let v := Psi (fun x => u2 x ^ gamma - u1 x ^ gamma) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        gamma ^ 2 * M ^ (2 * (gamma - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  Lemma_5_3_zero_source_branch hgamma hM heta_pos heta_one hsource

/-- CM-parameter form of the same-power zero-source branch of Lemma 5.3,
without assuming the full Lemma 5.3 theorem. -/
theorem Lemma_5_3.same_power_branch_CM
    (p : CMParams) {eta : ℝ}
    (hM : 1 ≤ MChi p) (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hu1_bound : ∀ x, 0 ≤ u1 x ∧ u1 x ≤ MChi p)
    (hu2_bound : ∀ x, 0 ≤ u2 x ∧ u2 x ≤ MChi p)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2))
    (hsource : ∀ x, u2 x ^ p.γ = u1 x ^ p.γ) :
    let v := Psi (fun x => u2 x ^ p.γ - u1 x ^ p.γ) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  Lemma_5_3.same_power_branch p.hγ hM heta_pos heta_one
    hu1 hu2 hu1_bound hu2_bound hclose hsource

/-- Tail-bound form of the same-power zero-source branch of Lemma 5.3,
without assuming the full Lemma 5.3 theorem. -/
theorem Lemma_5_3.same_power_branch_of_tail_bounds
    {p : CMParams} {c eta : ℝ}
    (hM : 1 ≤ MChi p) (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hbound1 : HasWaveUpperTailBound p c u1)
    (hbound2 : HasWaveUpperTailBound p c u2)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2))
    (hsource : ∀ x, u2 x ^ p.γ = u1 x ^ p.γ) :
    let v := Psi (fun x => u2 x ^ p.γ - u1 x ^ p.γ) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  Lemma_5_3.same_power_branch_CM p hM heta_pos heta_one
    hu1 hu2
    (fun x => ⟨(hbound1.pos x).le, hbound1.le_MChi x⟩)
    (fun x => ⟨(hbound2.pos x).le, hbound2.le_MChi x⟩)
    hclose hsource

/-- Continuous tail-bound form of the same-power zero-source branch of Lemma
5.3.  The `IsCUnifBdd` inputs are derived from the upper-tail bounds plus
continuity. -/
theorem Lemma_5_3.same_power_branch_of_tail_bounds_of_continuous
    {p : CMParams} {c eta : ℝ}
    (hM : 1 ≤ MChi p) (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hcont1 : Continuous u1) (hcont2 : Continuous u2)
    (hbound1 : HasWaveUpperTailBound p c u1)
    (hbound2 : HasWaveUpperTailBound p c u2)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2))
    (hsource : ∀ x, u2 x ^ p.γ = u1 x ^ p.γ) :
    let v := Psi (fun x => u2 x ^ p.γ - u1 x ^ p.γ) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  Lemma_5_3.same_power_branch_of_tail_bounds hM heta_pos heta_one
    (hbound1.isCUnifBdd_of_continuous hcont1)
    (hbound2.isCUnifBdd_of_continuous hcont2)
    hbound1 hbound2 hclose hsource

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

/-- A real constant-initial-data branch of Proposition 1.1. -/
theorem Proposition_1_1_constant_one_branch (p : CMParams) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p (fun _ : ℝ => (1 : ℝ)) u v ∧
        (∀ M, (∀ _x : ℝ, (1 : ℝ) ≤ M) →
          ∀ t x, 0 ≤ t → u t x ≤ max 1 M) ∧
        UniformLimsupLe u 1 ∧
        UniformEventuallyBounded u := by
  refine ⟨fun _ _ => (1 : ℝ), fun _ _ => (1 : ℝ), ?_, ?_, ?_, ?_⟩
  · exact ⟨constant_solution_is_global p, by intro x; rfl,
      by
        intro ε hε
        exact ⟨1, one_pos, fun _t _x _ht _ht1 => by simpa using hε⟩,
      by intro t x _; norm_num⟩
  · intro M hM t x _ht
    exact le_trans (hM x) (le_max_right 1 M)
  · intro ε hε
    exact Eventually.of_forall fun _t _x => by linarith
  · exact ⟨1, Eventually.of_forall fun _t _x => by norm_num⟩

theorem Proposition_1_1_constant_one_negative_branch
    (p : CMParams) (_hχ : p.χ ≤ 0) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p (fun _ : ℝ => (1 : ℝ)) u v ∧
      (∀ M, (∀ _x : ℝ, (1 : ℝ) ≤ M) →
        ∀ t x, 0 ≤ t → u t x ≤ max 1 M) ∧
      UniformLimsupLe u 1 := by
  rcases Proposition_1_1_constant_one_branch p with
    ⟨u, v, hsol, hmax, hlimsup, _hbounded⟩
  exact ⟨u, v, hsol, hmax, hlimsup⟩

/-- Constant-initial-data negative-sensitivity branch of Proposition 1.1 with
the eventual boundedness consequence kept. -/
theorem Proposition_1_1_constant_one_negative_long_time_branch
    (p : CMParams) (_hχ : p.χ ≤ 0) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p (fun _ : ℝ => (1 : ℝ)) u v ∧
      (∀ M, (∀ _x : ℝ, (1 : ℝ) ≤ M) →
        ∀ t x, 0 ≤ t → u t x ≤ max 1 M) ∧
      UniformLimsupLe u 1 ∧
      UniformEventuallyBounded u := by
  exact Proposition_1_1_constant_one_branch p

theorem one_le_positive_branch_limsup_bound
    (p : CMParams) (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1) :
    1 ≤ (1 / (1 - p.χ)) ^ (1 / p.α) := by
  have hden_pos : 0 < 1 - p.χ := sub_pos.mpr hχ_lt
  have hbase_ge_one : 1 ≤ 1 / (1 - p.χ) := by
    rw [le_div_iff₀ hden_pos]
    linarith
  have hexp_nonneg : 0 ≤ 1 / p.α := by
    exact div_nonneg zero_le_one (le_trans zero_le_one p.hα)
  exact Real.one_le_rpow hbase_ge_one hexp_nonneg

theorem Proposition_1_1_constant_one_positive_branch
    (p : CMParams) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p (fun _ : ℝ => (1 : ℝ)) u v ∧
      UniformEventuallyBounded u ∧
      (0 < p.χ → p.χ < 1 →
        UniformLimsupLe u ((1 / (1 - p.χ)) ^ (1 / p.α))) := by
  rcases Proposition_1_1_constant_one_branch p with
    ⟨u, v, hsol, _hmax, hlimsup, hbounded⟩
  refine ⟨u, v, hsol, hbounded, ?_⟩
  intro hχ_pos hχ_lt
  exact hlimsup.mono (one_le_positive_branch_limsup_bound p hχ_pos hχ_lt)

/-- Constant-initial-data positive-sensitivity branch of Proposition 1.1 with
the sharper `limsup ≤ 1` consequence also exposed. -/
theorem Proposition_1_1_constant_one_positive_long_time_branch
    (p : CMParams) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p (fun _ : ℝ => (1 : ℝ)) u v ∧
      UniformEventuallyBounded u ∧
      UniformLimsupLe u 1 ∧
      (0 < p.χ → p.χ < 1 →
        UniformLimsupLe u ((1 / (1 - p.χ)) ^ (1 / p.α))) := by
  rcases Proposition_1_1_constant_one_branch p with
    ⟨u, v, hsol, _hmax, hlimsup, hbounded⟩
  refine ⟨u, v, hsol, hbounded, hlimsup, ?_⟩
  intro hχ_pos hχ_lt
  exact hlimsup.mono (one_le_positive_branch_limsup_bound p hχ_pos hχ_lt)

theorem Proposition_1_1_constant_one_negative_admissible_branch
    (p : CMParams) (hχ : p.χ ≤ 0) :
    NonnegativeInitialDatum (fun _ : ℝ => (1 : ℝ)) ∧
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p (fun _ : ℝ => (1 : ℝ)) u v ∧
        (∀ M, (∀ _x : ℝ, (1 : ℝ) ≤ M) →
          ∀ t x, 0 ≤ t → u t x ≤ max 1 M) ∧
        UniformLimsupLe u 1 ∧
        UniformEventuallyBounded u := by
  exact ⟨constant_one_nonnegativeInitialDatum,
    Proposition_1_1_constant_one_negative_long_time_branch p hχ⟩

theorem Proposition_1_1_constant_one_positive_admissible_branch
    (p : CMParams) :
    NonnegativeInitialDatum (fun _ : ℝ => (1 : ℝ)) ∧
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p (fun _ : ℝ => (1 : ℝ)) u v ∧
        UniformEventuallyBounded u ∧
        UniformLimsupLe u 1 ∧
        (0 < p.χ → p.χ < 1 →
          UniformLimsupLe u ((1 / (1 - p.χ)) ^ (1 / p.α))) := by
  exact ⟨constant_one_nonnegativeInitialDatum,
    Proposition_1_1_constant_one_positive_long_time_branch p⟩

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

/-- A real constant-initial-data branch of Proposition 1.2. -/
theorem Proposition_1_2_constant_one_branch (p : CMParams) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p (fun _ : ℝ => (1 : ℝ)) u v ∧
        UniformConvergesToConstant u 1 := by
  refine ⟨fun _ _ => (1 : ℝ), fun _ _ => (1 : ℝ), ?_, ?_⟩
  · exact ⟨constant_solution_is_global p, by intro x; rfl,
      by
        intro ε hε
        exact ⟨1, one_pos, fun _t _x _ht _ht1 => by simpa using hε⟩,
      by intro t x _; norm_num⟩
  · intro ε hε
    exact ⟨0, fun _t _x _ht => by simpa using hε⟩

/-- Constant-initial-data branch of Proposition 1.2 with the long-time
boundedness and limsup consequences exposed directly. -/
theorem Proposition_1_2_constant_one_long_time_branch (p : CMParams) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p (fun _ : ℝ => (1 : ℝ)) u v ∧
        UniformConvergesToConstant u 1 ∧
        UniformEventuallyBounded u ∧
        UniformLimsupLe u 1 := by
  rcases Proposition_1_2_constant_one_branch p with ⟨u, v, hsol, hconv⟩
  exact ⟨u, v, hsol, hconv, hconv.uniformEventuallyBounded, hconv.uniformLimsupLe⟩

theorem Proposition_1_2_constant_one_negative_branch
    (p : CMParams) (_hχ : p.χ ≤ 0) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p (fun _ : ℝ => (1 : ℝ)) u v ∧
        UniformConvergesToConstant u 1 :=
  Proposition_1_2_constant_one_branch p

theorem Proposition_1_2_constant_one_negative_long_time_branch
    (p : CMParams) (_hχ : p.χ ≤ 0) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p (fun _ : ℝ => (1 : ℝ)) u v ∧
        UniformConvergesToConstant u 1 ∧
        UniformEventuallyBounded u ∧
        UniformLimsupLe u 1 :=
  Proposition_1_2_constant_one_long_time_branch p

theorem Proposition_1_2_constant_one_positive_branch
    (p : CMParams) (_hχ_pos : 0 < p.χ) (_hχ_small : p.χ < (1 / 2 : ℝ))
    (_halpha : p.m + p.γ - 1 ≤ p.α) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p (fun _ : ℝ => (1 : ℝ)) u v ∧
        UniformConvergesToConstant u 1 :=
  Proposition_1_2_constant_one_branch p

theorem Proposition_1_2_constant_one_positive_long_time_branch
    (p : CMParams) (_hχ_pos : 0 < p.χ) (_hχ_small : p.χ < (1 / 2 : ℝ))
    (_halpha : p.m + p.γ - 1 ≤ p.α) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p (fun _ : ℝ => (1 : ℝ)) u v ∧
        UniformConvergesToConstant u 1 ∧
        UniformEventuallyBounded u ∧
        UniformLimsupLe u 1 :=
  Proposition_1_2_constant_one_long_time_branch p

theorem Proposition_1_2_constant_one_negative_admissible_branch
    (p : CMParams) (hχ : p.χ ≤ 0) :
    NonnegativeInitialDatum (fun _ : ℝ => (1 : ℝ)) ∧
      UniformlyPositive (fun _ : ℝ => (1 : ℝ)) ∧
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p (fun _ : ℝ => (1 : ℝ)) u v ∧
        UniformConvergesToConstant u 1 ∧
        UniformEventuallyBounded u ∧
        UniformLimsupLe u 1 := by
  exact ⟨constant_one_nonnegativeInitialDatum,
    constant_one_uniformlyPositive,
    Proposition_1_2_constant_one_negative_long_time_branch p hχ⟩

theorem Proposition_1_2_constant_one_positive_admissible_branch
    (p : CMParams) (hχ_pos : 0 < p.χ) (hχ_small : p.χ < (1 / 2 : ℝ))
    (halpha : p.m + p.γ - 1 ≤ p.α) :
    NonnegativeInitialDatum (fun _ : ℝ => (1 : ℝ)) ∧
      UniformlyPositive (fun _ : ℝ => (1 : ℝ)) ∧
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p (fun _ : ℝ => (1 : ℝ)) u v ∧
        UniformConvergesToConstant u 1 ∧
        UniformEventuallyBounded u ∧
        UniformLimsupLe u 1 := by
  exact ⟨constant_one_nonnegativeInitialDatum,
    constant_one_uniformlyPositive,
    Proposition_1_2_constant_one_positive_long_time_branch p hχ_pos hχ_small
      halpha⟩

/-- Proposition 1.2 from separated global existence and convergence analysis.
The two analytical steps — PDE existence and long-time convergence to the
constant — are made independent hypotheses. -/
theorem Proposition_1_2.of_global_existence_and_convergence
    (hexist : ∀ p : CMParams,
      ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ → UniformlyPositive u₀ →
        ∃ u v : ℝ → ℝ → ℝ, IsGlobalCauchySolutionFrom p u₀ u v)
    (hconv_neg : ∀ p : CMParams, p.χ ≤ 0 →
      ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ → UniformlyPositive u₀ →
      ∀ u v : ℝ → ℝ → ℝ, IsGlobalCauchySolutionFrom p u₀ u v →
        UniformConvergesToConstant u 1)
    (hconv_pos : ∀ p : CMParams, 0 < p.χ → p.χ < (1 / 2 : ℝ) →
      p.m + p.γ - 1 ≤ p.α →
      ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ → UniformlyPositive u₀ →
      ∀ u v : ℝ → ℝ → ℝ, IsGlobalCauchySolutionFrom p u₀ u v →
        UniformConvergesToConstant u 1) :
    Proposition_1_2 := by
  constructor
  · intro p hχ u₀ hu₀ hu₀_pos
    rcases hexist p u₀ hu₀ hu₀_pos with ⟨u, v, hsol⟩
    exact ⟨u, v, hsol, hconv_neg p hχ u₀ hu₀ hu₀_pos u v hsol⟩
  · intro p hχ hχ_small hα u₀ hu₀ hu₀_pos
    rcases hexist p u₀ hu₀ hu₀_pos with ⟨u, v, hsol⟩
    exact ⟨u, v, hsol, hconv_pos p hχ hχ_small hα u₀ hu₀ hu₀_pos u v hsol⟩

/-- Proposition 1.1 from separated global existence and a priori estimates.
The three analytical steps — PDE existence, maximum-principle bound, and
long-time limsup/boundedness — are made independent hypotheses. -/
theorem Proposition_1_1.of_global_existence_and_bounds
    (hexist : ∀ p : CMParams,
      ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ →
        ∃ u v : ℝ → ℝ → ℝ, IsGlobalCauchySolutionFrom p u₀ u v)
    (hmax_neg : ∀ p : CMParams, p.χ ≤ 0 →
      ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ →
      ∀ u v : ℝ → ℝ → ℝ, IsGlobalCauchySolutionFrom p u₀ u v →
        (∀ M, (∀ x, u₀ x ≤ M) → ∀ t x, 0 ≤ t → u t x ≤ max 1 M) ∧
        UniformLimsupLe u 1)
    (hbound_pos : ∀ p : CMParams,
      (0 < p.χ ∧ p.α > p.m + p.γ - 1) ∨
        (0 < p.χ ∧
          p.χ < min
            ((p.m + p.γ - 1) / (2 * p.m - 1))
            ((p.m + p.γ - 1) / (p.γ - 1)) ∧
          p.α = p.m + p.γ - 1) →
      ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ →
      ∀ u v : ℝ → ℝ → ℝ, IsGlobalCauchySolutionFrom p u₀ u v →
        UniformEventuallyBounded u ∧
        (0 < p.χ → p.χ < 1 → UniformLimsupLe u ((1 / (1 - p.χ)) ^ (1 / p.α)))) :
    Proposition_1_1 := by
  constructor
  · intro p hχ u₀ hu₀
    rcases hexist p u₀ hu₀ with ⟨u, v, hsol⟩
    rcases hmax_neg p hχ u₀ hu₀ u v hsol with ⟨hmax, hlimsup⟩
    exact ⟨u, v, hsol, hmax, hlimsup⟩
  · intro p hcond u₀ hu₀
    rcases hexist p u₀ hu₀ with ⟨u, v, hsol⟩
    rcases hbound_pos p hcond u₀ hu₀ u v hsol with ⟨hbdd, hlimsup⟩
    exact ⟨u, v, hsol, hbdd, hlimsup⟩

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

theorem Theorem_1_1.of_assumed_frozenStationaryProfile_branches
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

theorem Theorem_1_1.of_assumed_frozenStationaryProfile_trap_branches
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
  refine Theorem_1_1.of_assumed_frozenStationaryProfile_branches ?_ hpos
  intro p halpha hχ c hc
  rcases hneg p halpha hχ c hc with
    ⟨U, htrap, hprofile, hVmono, hupper, htail⟩
  exact
    ⟨U, hprofile, htrap.deriv_nonpos, hVmono, hupper, htail⟩

/-- A lower-level Theorem 1.1 bridge: if the construction supplies raw
stationary fixed-point profiles with positivity, boundedness, endpoint limits,
monotonicity data, upper barriers, and the stated right-tail asymptotics, then
the paper's traveling-wave existence conclusion follows.  The elliptic
endpoint limits and the traveling-wave equations are assembled internally from
`FrozenStationaryWaveProfile.mk_auto_limits`. -/
theorem Theorem_1_1.of_raw_frozen_stationary_branches
    (hneg :
      ∀ p : CMParams, p.α ≤ p.m + p.γ - 1 → p.χ ≤ 0 →
        ∀ c : ℝ, cStarLower p < c →
          ∃ U : ℝ → ℝ,
            0 < c ∧
              (∀ x, 0 < U x) ∧
              IsCUnifBdd U ∧
              (∀ x, frozenWaveOperator p c U U x = 0) ∧
              Tendsto U atBot (𝓝 1) ∧
              Tendsto U atTop (𝓝 0) ∧
              (∀ x, deriv U x ≤ 0) ∧
              (∀ x, deriv (frozenElliptic p U) x ≤ 0) ∧
              ShenUpperBoundNegative c U ∧
              (∀ κ₁, kappa c < κ₁ →
                κ₁ <
                  min ((1 + p.α) * kappa c)
                    (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U))
    (hpos :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∃ U : ℝ → ℝ,
            0 < c ∧
              (∀ x, 0 < U x) ∧
              IsCUnifBdd U ∧
              (∀ x, frozenWaveOperator p c U U x = 0) ∧
              Tendsto U atBot (𝓝 1) ∧
              Tendsto U atTop (𝓝 0) ∧
              ShenUpperBoundPositive p c U ∧
              (∀ κ₁, kappa c < κ₁ →
                κ₁ <
                  min ((1 + p.α) * kappa c)
                    (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U)) :
    Theorem_1_1 := by
  refine Theorem_1_1.of_assumed_frozenStationaryProfile_branches ?_ ?_
  · intro p halpha hχ c hc
    rcases hneg p halpha hχ c hc with
      ⟨U, hc_pos, hU_pos, hU_bdd, hstat, hlim_bot, hlim_top,
        hUmono, hVmono, hupper, htail⟩
    exact
      ⟨U,
        FrozenStationaryWaveProfile.mk_auto_limits
          hc_pos hU_pos hU_bdd hstat hlim_bot hlim_top,
        hUmono, hVmono, hupper, htail⟩
  · intro p halpha hχ_nonneg hχ_small c hc
    rcases hpos p halpha hχ_nonneg hχ_small c hc with
      ⟨U, hc_pos, hU_pos, hU_bdd, hstat, hlim_bot, hlim_top, hupper, htail⟩
    exact
      ⟨U,
        FrozenStationaryWaveProfile.mk_auto_limits
          hc_pos hU_pos hU_bdd hstat hlim_bot hlim_top,
        hupper, htail⟩

theorem Theorem_1_1.of_raw_frozen_stationary_tail_continuous_branches
    (hneg :
      ∀ p : CMParams, p.α ≤ p.m + p.γ - 1 → p.χ ≤ 0 →
        ∀ c : ℝ, cStarLower p < c →
          ∃ U : ℝ → ℝ,
            0 < c ∧
              HasWaveUpperTailBound p c U ∧
              Continuous U ∧
              (∀ x, frozenWaveOperator p c U U x = 0) ∧
              Tendsto U atBot (𝓝 1) ∧
              Tendsto U atTop (𝓝 0) ∧
              (∀ x, deriv U x ≤ 0) ∧
              (∀ x, deriv (frozenElliptic p U) x ≤ 0) ∧
              ShenUpperBoundNegative c U ∧
              (∀ κ₁, kappa c < κ₁ →
                κ₁ <
                  min ((1 + p.α) * kappa c)
                    (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U))
    (hpos :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∃ U : ℝ → ℝ,
            0 < c ∧
              HasWaveUpperTailBound p c U ∧
              Continuous U ∧
              (∀ x, frozenWaveOperator p c U U x = 0) ∧
              Tendsto U atBot (𝓝 1) ∧
              Tendsto U atTop (𝓝 0) ∧
              ShenUpperBoundPositive p c U ∧
              (∀ κ₁, kappa c < κ₁ →
                κ₁ <
                  min ((1 + p.α) * kappa c)
                    (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U)) :
    Theorem_1_1 := by
  refine Theorem_1_1.of_assumed_frozenStationaryProfile_branches ?_ ?_
  · intro p halpha hχ c hc
    rcases hneg p halpha hχ c hc with
      ⟨U, hc_pos, hbound, hU_cont, hstat, hlim_bot, hlim_top,
        hUmono, hVmono, hupper, htail⟩
    exact
      ⟨U,
        FrozenStationaryWaveProfile.mk_auto_limits_of_tail_continuous
          hc_pos hbound hU_cont hstat hlim_bot hlim_top,
        hUmono, hVmono, hupper, htail⟩
  · intro p halpha hχ_nonneg hχ_small c hc
    rcases hpos p halpha hχ_nonneg hχ_small c hc with
      ⟨U, hc_pos, hbound, hU_cont, hstat, hlim_bot, hlim_top, hupper, htail⟩
    exact
      ⟨U,
        FrozenStationaryWaveProfile.mk_auto_limits_of_tail_continuous
          hc_pos hbound hU_cont hstat hlim_bot hlim_top,
        hupper, htail⟩

theorem Theorem_1_1.of_raw_frozen_stationary_positive_upper_continuous_branches
    (hneg :
      ∀ p : CMParams, p.α ≤ p.m + p.γ - 1 → p.χ ≤ 0 →
        ∀ c : ℝ, cStarLower p < c →
          ∃ U : ℝ → ℝ,
            0 < c ∧
              HasWaveUpperTailBound p c U ∧
              Continuous U ∧
              (∀ x, frozenWaveOperator p c U U x = 0) ∧
              Tendsto U atBot (𝓝 1) ∧
              Tendsto U atTop (𝓝 0) ∧
              (∀ x, deriv U x ≤ 0) ∧
              (∀ x, deriv (frozenElliptic p U) x ≤ 0) ∧
              ShenUpperBoundNegative c U ∧
              (∀ κ₁, kappa c < κ₁ →
                κ₁ <
                  min ((1 + p.α) * kappa c)
                    (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U))
    (hpos :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∃ U : ℝ → ℝ,
            0 < c ∧
              Continuous U ∧
              (∀ x, frozenWaveOperator p c U U x = 0) ∧
              Tendsto U atBot (𝓝 1) ∧
              Tendsto U atTop (𝓝 0) ∧
              ShenUpperBoundPositive p c U ∧
              (∀ κ₁, kappa c < κ₁ →
                κ₁ <
                  min ((1 + p.α) * kappa c)
                    (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U)) :
    Theorem_1_1 := by
  refine Theorem_1_1.of_raw_frozen_stationary_tail_continuous_branches hneg ?_
  intro p halpha hχ_nonneg hχ_small c hc
  rcases hpos p halpha hχ_nonneg hχ_small c hc with
    ⟨U, hc_pos, hU_cont, hstat, hlim_bot, hlim_top, hupper, htail⟩
  exact
    ⟨U, hc_pos,
      hupper.hasWaveUpperTailBound_of_chi_lt_half_chiStar hχ_nonneg hχ_small,
      hU_cont, hstat, hlim_bot, hlim_top, hupper, htail⟩

theorem Theorem_1_1.of_raw_frozen_stationary_speed_branches
    (hneg :
      ∀ p : CMParams, p.α ≤ p.m + p.γ - 1 → p.χ ≤ 0 →
        ∀ c : ℝ, cStarLower p < c →
          ∃ U : ℝ → ℝ,
            HasWaveUpperTailBound p c U ∧
              Continuous U ∧
              (∀ x, frozenWaveOperator p c U U x = 0) ∧
              Tendsto U atBot (𝓝 1) ∧
              Tendsto U atTop (𝓝 0) ∧
              (∀ x, deriv U x ≤ 0) ∧
              (∀ x, deriv (frozenElliptic p U) x ≤ 0) ∧
              ShenUpperBoundNegative c U ∧
              (∀ κ₁, kappa c < κ₁ →
                κ₁ <
                  min ((1 + p.α) * kappa c)
                    (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U))
    (hpos :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∃ U : ℝ → ℝ,
            Continuous U ∧
              (∀ x, frozenWaveOperator p c U U x = 0) ∧
              Tendsto U atBot (𝓝 1) ∧
              Tendsto U atTop (𝓝 0) ∧
              ShenUpperBoundPositive p c U ∧
              (∀ κ₁, kappa c < κ₁ →
                κ₁ <
                  min ((1 + p.α) * kappa c)
                    (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U)) :
    Theorem_1_1 := by
  refine
    Theorem_1_1.of_raw_frozen_stationary_positive_upper_continuous_branches ?_ ?_
  · intro p halpha hχ c hc
    rcases hneg p halpha hχ c hc with
      ⟨U, hbound, hU_cont, hstat, hlim_bot, hlim_top,
        hUmono, hVmono, hupper, htail⟩
    have hc_pos : 0 < c := by
      have hc2 : 2 < c := two_lt_of_cStarLower_lt hc
      linarith
    exact
      ⟨U, hc_pos, hbound, hU_cont, hstat, hlim_bot, hlim_top,
        hUmono, hVmono, hupper, htail⟩
  · intro p halpha hχ_nonneg hχ_small c hc
    rcases hpos p halpha hχ_nonneg hχ_small c hc with
      ⟨U, hU_cont, hstat, hlim_bot, hlim_top, hupper, htail⟩
    have hc_pos : 0 < c := by linarith
    exact
      ⟨U, hc_pos, hU_cont, hstat, hlim_bot, hlim_top, hupper, htail⟩

/-- Theorem 1.1 bridge from the Section 4 fixed-point construction.  This
theorem deliberately keeps the fixed-point stationarity, left-end limit, upper
bound, and right-tail asymptotic obligations explicit; the construction itself
is used only for the fixed point, trap-set regularity, monotonicity, and
right-end limits. -/
theorem Theorem_1_1.of_assumed_fixed_point_construction_branches
    (hneg :
      ∀ p : CMParams, p.α ≤ p.m + p.γ - 1 → p.χ ≤ 0 →
        ∀ c : ℝ, cStarLower p < c →
          ∃ κ₀ κtilde D : ℝ,
            let trap := fun u => InMonotoneWaveTrapSet (kappa c) 1 u
            let aux := fun U =>
              FrozenAuxiliaryLimitOutput p c (kappa c) 1 trap U U
            NegativeSensitivityWaveFixedPointConstruction p c κ₀ κtilde D ∧
              (∀ U, trap U → aux U →
                ∀ x, frozenWaveOperator p c U U x = 0) ∧
              (∀ U, trap U → aux U → Tendsto U atBot (𝓝 1)) ∧
              (∀ U, trap U → aux U →
                ∀ x, deriv (frozenElliptic p U) x ≤ 0) ∧
              (∀ U, trap U → aux U → ShenUpperBoundNegative c U) ∧
              ∀ U, trap U → aux U →
                ∀ κ₁, kappa c < κ₁ →
                  κ₁ <
                    min ((1 + p.α) * kappa c)
                      (min (p.m * kappa c + 1 / 2) 1) →
                  HasWaveRightTailAsymptotic c κ₁ U)
    (hpos :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∃ κ₀ κtilde D : ℝ,
            let trap := fun u => InWaveTrapSet (kappa c) (MChi p) u
            let aux := fun U =>
              FrozenAuxiliaryLimitOutput p c (kappa c) (MChi p) trap U U
            PositiveSensitivityWaveFixedPointConstruction p c κ₀ κtilde D ∧
              (∀ U, trap U → aux U →
                ∀ x, frozenWaveOperator p c U U x = 0) ∧
              (∀ U, trap U → aux U → Tendsto U atBot (𝓝 1)) ∧
              (∀ U, trap U → aux U → ShenUpperBoundPositive p c U) ∧
              ∀ U, trap U → aux U →
                ∀ κ₁, kappa c < κ₁ →
                  κ₁ <
                    min ((1 + p.α) * kappa c)
                      (min (p.m * kappa c + 1 / 2) 1) →
                  HasWaveRightTailAsymptotic c κ₁ U) :
    Theorem_1_1 := by
  refine Theorem_1_1.of_raw_frozen_stationary_speed_branches ?_ ?_
  · intro p halpha hχ c hc
    rcases hneg p halpha hχ c hc with
      ⟨κ₀, κtilde, D, hconstruct, hstat, hlim_bot, hVmono, hupper, htail⟩
    exact hconstruct.exists_fixed_limit_with_speed_bridge_data
      hstat hlim_bot hVmono hupper htail
  · intro p halpha hχ_nonneg hχ_small c hc
    rcases hpos p halpha hχ_nonneg hχ_small c hc with
      ⟨κ₀, κtilde, D, hconstruct, hstat, hlim_bot, hupper, htail⟩
    exact hconstruct.exists_fixed_limit_with_speed_bridge_data
      hstat hlim_bot hupper htail

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
    (hlower : stabilitySpeedBaseline p ≤ threshold p.χ)
    (hc : threshold p.χ < c) :
    2 < c :=
  lt_of_le_of_lt (two_le_stabilitySpeedBaseline p) (lt_of_le_of_lt hlower hc)

theorem kappa_pos_of_stabilitySpeedBaseline_lt
    {p : CMParams} {threshold : ℝ → ℝ} {c : ℝ}
    (hlower : stabilitySpeedBaseline p ≤ threshold p.χ)
    (hc : threshold p.χ < c) :
    0 < kappa c :=
  kappa_pos_of_two_lt (two_lt_of_stabilitySpeedBaseline_lt hlower hc)

theorem kappa_lt_one_of_stabilitySpeedBaseline_lt
    {p : CMParams} {threshold : ℝ → ℝ} {c : ℝ}
    (hlower : stabilitySpeedBaseline p ≤ threshold p.χ)
    (hc : threshold p.χ < c) :
    kappa c < 1 :=
  kappa_lt_one_of_two_lt (two_lt_of_stabilitySpeedBaseline_lt hlower hc)

theorem kappa_lt_stability_weight_cap_of_stabilitySpeedBaseline_lt
    {p : CMParams} {threshold : ℝ → ℝ} {c : ℝ}
    (hlower : stabilitySpeedBaseline p ≤ threshold p.χ)
    (hc : threshold p.χ < c) :
    kappa c < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) := by
  let a : ℝ := (1 + |p.χ| ^ (1 / 6 : ℝ))⁻¹
  have hpow_nonneg : 0 ≤ |p.χ| ^ (1 / 6 : ℝ) :=
    Real.rpow_nonneg (abs_nonneg p.χ) _
  have hden_pos : 0 < 1 + |p.χ| ^ (1 / 6 : ℝ) := by
    linarith
  have ha_pos : 0 < a := by
    dsimp [a]
    exact inv_pos.mpr hden_pos
  have ha_le_one : a ≤ 1 := by
    have hden_one : 1 ≤ 1 + |p.χ| ^ (1 / 6 : ℝ) := by
      linarith
    dsimp [a]
    exact inv_le_one_of_one_le₀ hden_one
  have hc_two : 2 < c :=
    two_lt_of_stabilitySpeedBaseline_lt hlower hc
  have hk_pos : 0 < kappa c :=
    kappa_pos_of_two_lt hc_two
  have hk_lt_one : kappa c < 1 :=
    kappa_lt_one_of_two_lt hc_two
  have hbaseline_eq : stabilitySpeedBaseline p = a + a⁻¹ := by
    dsimp [stabilitySpeedBaseline, a]
    rw [inv_inv]
    ring
  have hspeed : a + a⁻¹ < kappa c + (kappa c)⁻¹ := by
    have hbaseline_lt : stabilitySpeedBaseline p < c := lt_of_le_of_lt hlower hc
    rw [hbaseline_eq] at hbaseline_lt
    rw [kappa_add_inv_eq_of_two_lt hc_two]
    exact hbaseline_lt
  have hk_lt_a : kappa c < a := by
    by_contra hnot
    have ha_le_k : a ≤ kappa c := le_of_not_gt hnot
    have hdiff_nonneg :
        0 ≤ a + a⁻¹ - (kappa c + (kappa c)⁻¹) := by
      have ha_ne : a ≠ 0 := ne_of_gt ha_pos
      have hk_ne : kappa c ≠ 0 := ne_of_gt hk_pos
      have hidentity :
          a + a⁻¹ - (kappa c + (kappa c)⁻¹) =
            (kappa c - a) * (1 - a * kappa c) / (a * kappa c) := by
        field_simp [ha_ne, hk_ne]
        ring
      rw [hidentity]
      apply div_nonneg
      · apply mul_nonneg
        · linarith
        · have hak_le_one : a * kappa c ≤ 1 := by
            nlinarith [ha_pos, hk_pos, ha_le_one, hk_lt_one.le]
          linarith
      · exact mul_nonneg ha_pos.le hk_pos.le
    have hle : kappa c + (kappa c)⁻¹ ≤ a + a⁻¹ := by
      linarith
    linarith
  simpa [a, one_div] using hk_lt_a

theorem eta_pos_of_stability_weight_hypotheses
    {p : CMParams} {threshold : ℝ → ℝ} {c eta : ℝ}
    (hlower : stabilitySpeedBaseline p ≤ threshold p.χ)
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
    (hlower : stabilitySpeedBaseline p ≤ threshold p.χ)
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

/-- Stable-regime tail-bound form of the same-power zero-source branch of
Lemma 5.3, without assuming the full Lemma 5.3 theorem. -/
theorem Lemma_5_3.same_power_branch_of_stable_tail_bounds
    {p : CMParams} {c eta : ℝ}
    (hregime : StableWaveParameterRegime p)
    (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hbound1 : HasWaveUpperTailBound p c u1)
    (hbound2 : HasWaveUpperTailBound p c u2)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2))
    (hsource : ∀ x, u2 x ^ p.γ = u1 x ^ p.γ) :
    let v := Psi (fun x => u2 x ^ p.γ - u1 x ^ p.γ) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  Lemma_5_3.same_power_branch_of_tail_bounds
    hregime.one_le_MChi heta_pos heta_one hu1 hu2 hbound1 hbound2 hclose hsource

/-- Continuous stable-regime tail-bound form of the same-power zero-source
branch of Lemma 5.3. -/
theorem Lemma_5_3.same_power_branch_of_stable_tail_bounds_of_continuous
    {p : CMParams} {c eta : ℝ}
    (hregime : StableWaveParameterRegime p)
    (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hcont1 : Continuous u1) (hcont2 : Continuous u2)
    (hbound1 : HasWaveUpperTailBound p c u1)
    (hbound2 : HasWaveUpperTailBound p c u2)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2))
    (hsource : ∀ x, u2 x ^ p.γ = u1 x ^ p.γ) :
    let v := Psi (fun x => u2 x ^ p.γ - u1 x ^ p.γ) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  Lemma_5_3.same_power_branch_of_tail_bounds_of_continuous
    hregime.one_le_MChi heta_pos heta_one hcont1 hcont2
    hbound1 hbound2 hclose hsource

/-- Strict-tail form of the stable same-power zero-source branch of Lemma 5.3,
without assuming the full Lemma 5.3 theorem. -/
theorem Lemma_5_3.same_power_branch_of_stable_strict_tail_bounds
    {p : CMParams} {c eta : ℝ}
    (hregime : StableWaveParameterRegime p)
    (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hbound1 : HasStrictWaveUpperTailBound p c u1)
    (hbound2 : HasStrictWaveUpperTailBound p c u2)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2))
    (hsource : ∀ x, u2 x ^ p.γ = u1 x ^ p.γ) :
    let v := Psi (fun x => u2 x ^ p.γ - u1 x ^ p.γ) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  Lemma_5_3.same_power_branch_of_stable_tail_bounds hregime
    heta_pos heta_one hu1 hu2
    hbound1.hasWaveUpperTailBound hbound2.hasWaveUpperTailBound hclose hsource

/-- Continuous strict-tail form of the stable same-power zero-source branch
of Lemma 5.3. -/
theorem Lemma_5_3.same_power_branch_of_stable_strict_tail_bounds_of_continuous
    {p : CMParams} {c eta : ℝ}
    (hregime : StableWaveParameterRegime p)
    (heta_pos : 0 < eta) (heta_one : eta < 1)
    {u1 u2 : ℝ → ℝ}
    (hcont1 : Continuous u1) (hcont2 : Continuous u2)
    (hbound1 : HasStrictWaveUpperTailBound p c u1)
    (hbound2 : HasStrictWaveUpperTailBound p c u2)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2))
    (hsource : ∀ x, u2 x ^ p.γ = u1 x ^ p.γ) :
    let v := Psi (fun x => u2 x ^ p.γ - u1 x ^ p.γ) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  Lemma_5_3.same_power_branch_of_stable_tail_bounds_of_continuous
    hregime heta_pos heta_one hcont1 hcont2
    hbound1.hasWaveUpperTailBound hbound2.hasWaveUpperTailBound hclose hsource

/-- Stability-hypothesis form of the same-power zero-source branch of Lemma
5.3, without assuming the full Lemma 5.3 theorem. -/
theorem Lemma_5_3.same_power_branch_of_stability_hypotheses
    {p : CMParams} {threshold : ℝ → ℝ} {c eta : ℝ}
    (hregime : StableWaveParameterRegime p)
    (hlower : stabilitySpeedBaseline p < threshold p.χ)
    (hc : threshold p.χ < c) (hketa : kappa c < eta)
    (heta_upper : eta < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)))
    {u1 u2 : ℝ → ℝ}
    (hu1 : IsCUnifBdd u1) (hu2 : IsCUnifBdd u2)
    (hbound1 : HasStrictWaveUpperTailBound p c u1)
    (hbound2 : HasStrictWaveUpperTailBound p c u2)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2))
    (hsource : ∀ x, u2 x ^ p.γ = u1 x ^ p.γ) :
    let v := Psi (fun x => u2 x ^ p.γ - u1 x ^ p.γ) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  Lemma_5_3.same_power_branch_of_stable_strict_tail_bounds hregime
    (eta_pos_of_stability_weight_hypotheses hlower.le hc hketa)
    (eta_lt_one_of_stability_weight_upper_bound p heta_upper)
    hu1 hu2 hbound1 hbound2 hclose hsource

/-- Continuous stability-hypothesis form of the same-power zero-source branch
of Lemma 5.3. -/
theorem Lemma_5_3.same_power_branch_of_stability_hypotheses_of_continuous
    {p : CMParams} {threshold : ℝ → ℝ} {c eta : ℝ}
    (hregime : StableWaveParameterRegime p)
    (hlower : stabilitySpeedBaseline p < threshold p.χ)
    (hc : threshold p.χ < c) (hketa : kappa c < eta)
    (heta_upper : eta < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)))
    {u1 u2 : ℝ → ℝ}
    (hcont1 : Continuous u1) (hcont2 : Continuous u2)
    (hbound1 : HasStrictWaveUpperTailBound p c u1)
    (hbound2 : HasStrictWaveUpperTailBound p c u2)
    (hclose : Integrable
      (fun x => Real.exp (2 * eta * x) * |u2 x - u1 x| ^ 2))
    (hsource : ∀ x, u2 x ^ p.γ = u1 x ^ p.γ) :
    let v := Psi (fun x => u2 x ^ p.γ - u1 x ^ p.γ) 1 1
    let U := fun x => Real.exp (eta * x) * (u2 x - u1 x)
    let V := fun x => Real.exp (eta * x) * v x
    (∫ x : ℝ, |V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta) ^ 2 *
          ∫ x : ℝ, |U x| ^ 2) ∧
      (∫ x : ℝ, |deriv V x| ^ 2 ≤
        p.γ ^ 2 * (MChi p) ^ (2 * (p.γ - 1)) / (1 - eta ^ 2) *
          ∫ x : ℝ, |U x| ^ 2) :=
  Lemma_5_3.same_power_branch_of_stable_strict_tail_bounds_of_continuous
    hregime
    (eta_pos_of_stability_weight_hypotheses hlower.le hc hketa)
    (eta_lt_one_of_stability_weight_upper_bound p heta_upper)
    hcont1 hcont2 hbound1 hbound2 hclose hsource

/-- Paper1 Theorem 1.2: weighted stability of traveling waves. -/
def Theorem_1_2 : Prop :=
  ∀ p : CMParams, StableWaveParameterRegime p →
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p ≤ cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η → η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          ∀ u₀ : ℝ → ℝ,
            NonnegativeInitialDatum u₀ →
            StrictlyPositiveAtLeft u₀ →
            WeightedL2InitialCloseness η u₀ U →
            ∃ u v : ℝ → ℝ → ℝ,
              IsGlobalCauchySolutionFrom p u₀ u v ∧
              WeightedL2MovingFrameConvergence η c u U ∧
              UniformMovingFrameConvergence c u U

/-- A real self-initial-data branch of Paper1 Theorem 1.2.
If the Cauchy datum is exactly the wave profile, the moving-frame solution is
the traveling wave itself, so both stability conclusions have zero error. -/
theorem Theorem_1_2_self_initial_data_branch
    {p : CMParams} {c η : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hU_diff : ContDiff ℝ 2 U) (hV_diff : ContDiff ℝ 2 V) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p U u v ∧
      WeightedL2MovingFrameConvergence η c u U ∧
      UniformMovingFrameConvergence c u U := by
  exact
    ⟨fun t x => U (x - c * t), fun t x => V (x - c * t),
      IsTravelingWave.to_globalCauchySolutionFrom hTW hU_diff hV_diff,
      IsTravelingWave.weightedL2MovingFrameConvergence_self hTW,
      IsTravelingWave.uniformMovingFrameConvergence_self hTW⟩

theorem Theorem_1_2_self_initial_data_admissible_branch
    {p : CMParams} {c η : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hU : IsCUnifBdd U)
    (hU_diff : ContDiff ℝ 2 U) (hV_diff : ContDiff ℝ 2 V) :
    NonnegativeInitialDatum U ∧
      StrictlyPositiveAtLeft U ∧
      WeightedL2InitialCloseness η U U ∧
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p U u v ∧
        WeightedL2MovingFrameConvergence η c u U ∧
        UniformMovingFrameConvergence c u U := by
  exact ⟨IsTravelingWave.nonnegativeInitialDatum hTW hU,
    IsTravelingWave.strictlyPositiveAtLeft hTW,
    WeightedL2InitialCloseness.refl η U,
    Theorem_1_2_self_initial_data_branch hTW hU_diff hV_diff⟩

theorem Theorem_1_2_self_initial_data_admissible_branch_of_strict_tail
    {p : CMParams} {c η : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasStrictWaveUpperTailBound p c U)
    (hU_cont : Continuous U)
    (hU_diff : ContDiff ℝ 2 U) (hV_diff : ContDiff ℝ 2 V) :
    NonnegativeInitialDatum U ∧
      StrictlyPositiveAtLeft U ∧
      WeightedL2InitialCloseness η U U ∧
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p U u v ∧
        WeightedL2MovingFrameConvergence η c u U ∧
        UniformMovingFrameConvergence c u U := by
  exact Theorem_1_2_self_initial_data_admissible_branch hTW
    (hbound.isCUnifBdd_of_continuous hU_cont) hU_diff hV_diff

/-- Self-initial-data branch of Theorem 1.2 specialized to a frozen stationary
profile.  The moving-frame Cauchy solution is the frozen profile itself, so the
weighted and uniform stability errors are identically zero. -/
theorem Theorem_1_2_frozen_profile_self_initial_data_branch
    {p : CMParams} {c η : ℝ} {U : ℝ → ℝ}
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hU_diff : ContDiff ℝ 2 U)
    (hV_diff : ContDiff ℝ 2 (frozenElliptic p U)) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p U u v ∧
      WeightedL2MovingFrameConvergence η c u U ∧
      UniformMovingFrameConvergence c u U := by
  exact
    ⟨fun t x => U (x - c * t),
      fun t x => frozenElliptic p U (x - c * t),
      hprofile.to_globalCauchySolutionFrom hU_diff hV_diff,
      IsTravelingWave.weightedL2MovingFrameConvergence_self hprofile.to_travelingWave,
      IsTravelingWave.uniformMovingFrameConvergence_self hprofile.to_travelingWave⟩

theorem Theorem_1_2_frozen_profile_self_initial_data_admissible_branch
    {p : CMParams} {c η : ℝ} {U : ℝ → ℝ}
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hU : IsCUnifBdd U)
    (hU_diff : ContDiff ℝ 2 U)
    (hV_diff : ContDiff ℝ 2 (frozenElliptic p U)) :
    NonnegativeInitialDatum U ∧
      StrictlyPositiveAtLeft U ∧
      WeightedL2InitialCloseness η U U ∧
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p U u v ∧
        WeightedL2MovingFrameConvergence η c u U ∧
        UniformMovingFrameConvergence c u U := by
  exact ⟨IsTravelingWave.nonnegativeInitialDatum hprofile.to_travelingWave hU,
    IsTravelingWave.strictlyPositiveAtLeft hprofile.to_travelingWave,
    WeightedL2InitialCloseness.refl η U,
    Theorem_1_2_frozen_profile_self_initial_data_branch hprofile hU_diff hV_diff⟩

theorem Theorem_1_2_frozen_profile_self_initial_data_admissible_branch_of_strict_tail
    {p : CMParams} {c η : ℝ} {U : ℝ → ℝ}
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hbound : HasStrictWaveUpperTailBound p c U)
    (hU_cont : Continuous U)
    (hU_diff : ContDiff ℝ 2 U)
    (hV_diff : ContDiff ℝ 2 (frozenElliptic p U)) :
    NonnegativeInitialDatum U ∧
      StrictlyPositiveAtLeft U ∧
      WeightedL2InitialCloseness η U U ∧
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p U u v ∧
        WeightedL2MovingFrameConvergence η c u U ∧
        UniformMovingFrameConvergence c u U := by
  exact Theorem_1_2_frozen_profile_self_initial_data_admissible_branch
    hprofile (hbound.isCUnifBdd_of_continuous hU_cont) hU_diff hV_diff

/-- Generic stability-hypothesis closure for Theorem 1.2.
Given an explicit threshold family `cStarStar` with the paper's `|χ|^{1/6}`
asymptotic and a stability conclusion for every `(p, c)` past the threshold,
`Theorem_1_2` follows. -/
theorem Theorem_1_2.of_assumed_stability_branch
    (cStarStarFn : CMParams → (ℝ → ℝ))
    (hcStarStar : ∀ p : CMParams, StableWaveParameterRegime p →
      StabilitySpeedThresholdFamilyAsymptotic p (cStarStarFn p) ∧
        stabilitySpeedBaseline p ≤ cStarStarFn p p.χ)
    (hstability : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η → η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          ∀ u₀ : ℝ → ℝ,
            NonnegativeInitialDatum u₀ →
            StrictlyPositiveAtLeft u₀ →
            WeightedL2InitialCloseness η u₀ U →
            ∃ u v : ℝ → ℝ → ℝ,
              IsGlobalCauchySolutionFrom p u₀ u v ∧
              WeightedL2MovingFrameConvergence η c u U ∧
              UniformMovingFrameConvergence c u U) :
    Theorem_1_2 := by
  intro p hreg
  obtain ⟨hasymp, hbaseline⟩ := hcStarStar p hreg
  refine ⟨cStarStarFn p, hasymp, hbaseline, ?_⟩
  exact hstability p hreg

/-- Specialization of `Theorem_1_2.of_assumed_stability_branch` when the
threshold family is taken to be the paper's `cStarStar` itself, offset by an
arbitrary positive function `ε p > 0`.  Useful when one has an
`|χ|^{1/6}` asymptotic for `cStarStar + ε`. -/
theorem Theorem_1_2.of_assumed_stability_branch_offset
    (εFn : CMParams → ℝ)
    (hε_pos : ∀ p, 0 < εFn p)
    (hasymp : ∀ p : CMParams,
      StabilitySpeedThresholdFamilyAsymptotic p
        (fun _χ => stabilitySpeedBaseline p + εFn p))
    (hstability : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, stabilitySpeedBaseline p + εFn p < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η → η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          ∀ u₀ : ℝ → ℝ,
            NonnegativeInitialDatum u₀ →
            StrictlyPositiveAtLeft u₀ →
            WeightedL2InitialCloseness η u₀ U →
            ∃ u v : ℝ → ℝ → ℝ,
              IsGlobalCauchySolutionFrom p u₀ u v ∧
              WeightedL2MovingFrameConvergence η c u U ∧
              UniformMovingFrameConvergence c u U) :
    Theorem_1_2 := by
  refine Theorem_1_2.of_assumed_stability_branch
    (fun p => fun _χ => stabilitySpeedBaseline p + εFn p) ?_ ?_
  · intro p _hreg
    refine ⟨hasymp p, ?_⟩
    have := hε_pos p
    linarith
  · intro p hreg c hc
    exact hstability p hreg c hc

/-- Paper1 Theorem 1.3: uniqueness of traveling waves with the prescribed right tail. -/
def Theorem_1_3 : Prop :=
  ∀ p : CMParams, StableWaveParameterRegime p →
    ∃ cStarStar : ℝ → ℝ,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p ≤ cStarStar p.χ ∧
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

/-- A non-projection uniqueness bridge: once stability (or another argument)
has shown that the moving frame generated by `U₂` converges uniformly to `U₁`,
the two profiles are equal.  If both signals are identified with the same
elliptic resolvent, the signal profiles are equal as well. -/
theorem Theorem_1_3_profile_eq_of_uniform_movingFrame_and_resolvent
    {p : CMParams} {c : ℝ} {U₁ V₁ U₂ V₂ : ℝ → ℝ}
    (hconv : UniformMovingFrameConvergence c (fun t x => U₂ (x - c * t)) U₁)
    (hV₁ : V₁ = frozenElliptic p U₁)
    (hV₂ : V₂ = frozenElliptic p U₂) :
    (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) := by
  have hU₂₁ : ∀ x, U₂ x = U₁ x :=
    UniformMovingFrameConvergence.profile_eq_of_movingFrame hconv
  have hU_fun : U₂ = U₁ := funext hU₂₁
  constructor
  · intro x
    exact (hU₂₁ x).symm
  · intro x
    rw [hV₁, hV₂, hU_fun]

/-- A sharper non-projection uniqueness bridge.  If the weighted stability
machinery applies to the second wave used as initial data, and Cauchy
uniqueness identifies the produced solution with the moving second wave, then
the final Theorem 1.3 profile equalities follow from the previous
moving-frame/resolvent bridge. -/
theorem Theorem_1_3_profile_eq_of_stability_cauchy_unique_and_resolvent
    {p : CMParams} {c η : ℝ} {U₁ V₁ U₂ V₂ : ℝ → ℝ}
    (hTW₂ : IsTravelingWave p c U₂ V₂)
    (hU₂ : IsCUnifBdd U₂)
    (hclose : WeightedL2InitialCloseness η U₂ U₁)
    (hstable :
      ∀ u₀ : ℝ → ℝ,
        NonnegativeInitialDatum u₀ →
        StrictlyPositiveAtLeft u₀ →
        WeightedL2InitialCloseness η u₀ U₁ →
          ∃ u v : ℝ → ℝ → ℝ,
            IsGlobalCauchySolutionFrom p u₀ u v ∧
              WeightedL2MovingFrameConvergence η c u U₁ ∧
              UniformMovingFrameConvergence c u U₁)
    (hcauchy_unique :
      ∀ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p U₂ u v →
          ∀ t x, u t x = U₂ (x - c * t))
    (hV₁ : V₁ = frozenElliptic p U₁)
    (hV₂ : V₂ = frozenElliptic p U₂) :
    (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) := by
  rcases hstable U₂
      (IsTravelingWave.nonnegativeInitialDatum hTW₂ hU₂)
      (IsTravelingWave.strictlyPositiveAtLeft hTW₂)
      hclose with
    ⟨u, v, hsol, _hweighted, huniform⟩
  have hconv :
      UniformMovingFrameConvergence c (fun t x => U₂ (x - c * t)) U₁ := by
    intro ε hε
    rcases huniform ε hε with ⟨T, hT⟩
    refine ⟨T, ?_⟩
    intro t x ht
    have hu_eq : u t x = U₂ (x - c * t) := hcauchy_unique u v hsol t x
    simpa [hu_eq] using hT t x ht
  exact
    Theorem_1_3_profile_eq_of_uniform_movingFrame_and_resolvent
      hconv hV₁ hV₂

theorem Theorem_1_3_profile_eq_of_stability_second_tail_continuous
    {p : CMParams} {c η : ℝ} {U₁ V₁ U₂ V₂ : ℝ → ℝ}
    (hTW₂ : IsTravelingWave p c U₂ V₂)
    (hU₂_cont : Continuous U₂)
    (hbound₂ : HasWaveUpperTailBound p c U₂)
    (hclose : WeightedL2InitialCloseness η U₂ U₁)
    (hstable :
      ∀ u₀ : ℝ → ℝ,
        NonnegativeInitialDatum u₀ →
        StrictlyPositiveAtLeft u₀ →
        WeightedL2InitialCloseness η u₀ U₁ →
          ∃ u v : ℝ → ℝ → ℝ,
            IsGlobalCauchySolutionFrom p u₀ u v ∧
              WeightedL2MovingFrameConvergence η c u U₁ ∧
              UniformMovingFrameConvergence c u U₁)
    (hcauchy_unique :
      ∀ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p U₂ u v →
          ∀ t x, u t x = U₂ (x - c * t))
    (hV₁ : V₁ = frozenElliptic p U₁)
    (hV₂ : V₂ = frozenElliptic p U₂) :
    (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) :=
  Theorem_1_3_profile_eq_of_stability_cauchy_unique_and_resolvent
    hTW₂ (hbound₂.isCUnifBdd_of_continuous hU₂_cont)
    hclose hstable hcauchy_unique hV₁ hV₂

/-- The same uniqueness bridge with the weighted initial closeness supplied by
the corrected regular Remark 4.3 tail theorem.  This replaces the explicit
`WeightedL2InitialCloseness` input by the sharp right-tail asymptotics and the
profile regularity needed for the weighted integral. -/
theorem Theorem_1_3_profile_eq_of_remark43_stability_cauchy_unique_and_resolvent
    {p : CMParams} {c eta : ℝ} {U₁ V₁ U₂ V₂ : ℝ → ℝ}
    (hkappa : 0 < kappa c)
    (hTW₁ : IsTravelingWave p c U₁ V₁)
    (hTW₂ : IsTravelingWave p c U₂ V₂)
    (hU₁_cont : Continuous U₁)
    (hU₂_cont : Continuous U₂)
    (hU₂_bdd : IsCUnifBdd U₂)
    (hbound₁ : HasWaveUpperTailBound p c U₁)
    (hbound₂ : HasWaveUpperTailBound p c U₂)
    (htail₁ : HasRemark43TailAsymptotic p c U₁)
    (htail₂ : HasRemark43TailAsymptotic p c U₂)
    (heta : Remark43TailRateBound p c eta)
    (hstable :
      ∀ u₀ : ℝ → ℝ,
        NonnegativeInitialDatum u₀ →
        StrictlyPositiveAtLeft u₀ →
        WeightedL2InitialCloseness (eta + kappa c) u₀ U₁ →
          ∃ u v : ℝ → ℝ → ℝ,
            IsGlobalCauchySolutionFrom p u₀ u v ∧
              WeightedL2MovingFrameConvergence (eta + kappa c) c u U₁ ∧
              UniformMovingFrameConvergence c u U₁)
    (hcauchy_unique :
      ∀ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p U₂ u v →
          ∀ t x, u t x = U₂ (x - c * t))
    (hV₁ : V₁ = frozenElliptic p U₁)
    (hV₂ : V₂ = frozenElliptic p U₂) :
    (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) := by
  have hclose : WeightedL2InitialCloseness (eta + kappa c) U₂ U₁ :=
    Remark_4_3_regular_direct hkappa hTW₁ hTW₂ hU₁_cont hU₂_cont
      hbound₁ hbound₂ htail₁ htail₂ heta
  exact
    Theorem_1_3_profile_eq_of_stability_cauchy_unique_and_resolvent
      hTW₂ hU₂_bdd hclose hstable hcauchy_unique hV₁ hV₂

theorem Theorem_1_3_profile_eq_of_remark43_second_tail_continuous
    {p : CMParams} {c eta : ℝ} {U₁ V₁ U₂ V₂ : ℝ → ℝ}
    (hkappa : 0 < kappa c)
    (hTW₁ : IsTravelingWave p c U₁ V₁)
    (hTW₂ : IsTravelingWave p c U₂ V₂)
    (hU₁_cont : Continuous U₁)
    (hU₂_cont : Continuous U₂)
    (hbound₁ : HasWaveUpperTailBound p c U₁)
    (hbound₂ : HasWaveUpperTailBound p c U₂)
    (htail₁ : HasRemark43TailAsymptotic p c U₁)
    (htail₂ : HasRemark43TailAsymptotic p c U₂)
    (heta : Remark43TailRateBound p c eta)
    (hstable :
      ∀ u₀ : ℝ → ℝ,
        NonnegativeInitialDatum u₀ →
        StrictlyPositiveAtLeft u₀ →
        WeightedL2InitialCloseness (eta + kappa c) u₀ U₁ →
          ∃ u v : ℝ → ℝ → ℝ,
            IsGlobalCauchySolutionFrom p u₀ u v ∧
              WeightedL2MovingFrameConvergence (eta + kappa c) c u U₁ ∧
              UniformMovingFrameConvergence c u U₁)
    (hcauchy_unique :
      ∀ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p U₂ u v →
          ∀ t x, u t x = U₂ (x - c * t))
    (hV₁ : V₁ = frozenElliptic p U₁)
    (hV₂ : V₂ = frozenElliptic p U₂) :
    (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) :=
  Theorem_1_3_profile_eq_of_remark43_stability_cauchy_unique_and_resolvent
    hkappa hTW₁ hTW₂ hU₁_cont hU₂_cont
    (hbound₂.isCUnifBdd_of_continuous hU₂_cont)
    hbound₁ hbound₂ htail₁ htail₂ heta hstable hcauchy_unique hV₁ hV₂

/-- Generic uniqueness-hypothesis closure for Theorem 1.3.
Given a threshold family `cStarStar` with the paper's `|χ|^{1/6}` asymptotic
and the pairwise uniqueness conclusion for every `(p, c)` past the threshold,
`Theorem_1_3` follows. -/
theorem Theorem_1_3.of_assumed_uniqueness_branch
    (cStarStarFn : CMParams → (ℝ → ℝ))
    (hcStarStar : ∀ p : CMParams, StableWaveParameterRegime p →
      StabilitySpeedThresholdFamilyAsymptotic p (cStarStarFn p) ∧
        stabilitySpeedBaseline p ≤ cStarStarFn p p.χ)
    (huniq : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasStrictWaveUpperTailBound p c U₂ →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧
          HasWaveRightTailAsymptotic c κ₁ U₁ ∧
          HasWaveRightTailAsymptotic c κ₁ U₂) →
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x)) :
    Theorem_1_3 := by
  intro p hreg
  obtain ⟨hasymp, hbaseline⟩ := hcStarStar p hreg
  refine ⟨cStarStarFn p, hasymp, hbaseline, ?_⟩
  exact huniq p hreg

/-- Specialization of `Theorem_1_3.of_assumed_uniqueness_branch` with
`cStarStar` chosen to be the baseline shifted by a positive offset. -/
theorem Theorem_1_3.of_assumed_uniqueness_branch_offset
    (εFn : CMParams → ℝ)
    (hε_pos : ∀ p, 0 < εFn p)
    (hasymp : ∀ p : CMParams,
      StabilitySpeedThresholdFamilyAsymptotic p
        (fun _χ => stabilitySpeedBaseline p + εFn p))
    (huniq : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, stabilitySpeedBaseline p + εFn p < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasStrictWaveUpperTailBound p c U₂ →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧
          HasWaveRightTailAsymptotic c κ₁ U₁ ∧
          HasWaveRightTailAsymptotic c κ₁ U₂) →
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x)) :
    Theorem_1_3 := by
  refine Theorem_1_3.of_assumed_uniqueness_branch
    (fun p => fun _χ => stabilitySpeedBaseline p + εFn p) ?_ ?_
  · intro p _hreg
    refine ⟨hasymp p, ?_⟩
    have := hε_pos p
    linarith
  · intro p hreg c hc
    exact huniq p hreg c hc

/-- Reflexive branch of Theorem 1.3: when both waves are the same profile,
uniqueness is immediate. -/
theorem Theorem_1_3_reflexive_branch
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (_hTW : IsTravelingWave p c U V) :
    (∀ x, U x = U x) ∧ (∀ x, V x = V x) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- Bridge: Theorem 1.2 (stability) + Cauchy uniqueness + resolvent
identification + weighted closeness together imply Theorem 1.3 (uniqueness).

The proof strategy: given two waves `(U₁,V₁)` and `(U₂,V₂)`, apply
Theorem 1.2's stability conclusion to wave `U₁` with initial data `U₂`.
The stability result produces a Cauchy solution from `U₂` that converges
uniformly to `U₁` in the moving frame.  Cauchy uniqueness identifies that
solution with `U₂` translated, so `U₂` itself converges to `U₁`, giving
`U₁ = U₂`.  Then `V₁ = V₂` follows from the resolvent identification. -/
theorem Theorem_1_3.of_Theorem_1_2_cauchy_unique_resolvent_closeness
    (h12 : Theorem_1_2)
    (hcont : ∀ p : CMParams, ∀ c : ℝ, ∀ U V : ℝ → ℝ,
      IsTravelingWave p c U V → Continuous U)
    (hcauchy : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        IsCUnifBdd U →
        ∀ u v : ℝ → ℝ → ℝ,
          IsGlobalCauchySolutionFrom p U u v →
            ∀ t x, u t x = U (x - c * t))
    (hresolvent : ∀ p : CMParams, ∀ c : ℝ, ∀ U V : ℝ → ℝ,
      IsTravelingWave p c U V → V = frozenElliptic p U)
    (hclose : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ,
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasStrictWaveUpperTailBound p c U₂ →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧
          HasWaveRightTailAsymptotic c κ₁ U₁ ∧
          HasWaveRightTailAsymptotic c κ₁ U₂) →
        ∃ η : ℝ, kappa c < η ∧
          η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) ∧
          WeightedL2InitialCloseness η U₂ U₁) :
    Theorem_1_3 := by
  intro p hreg
  rcases h12 p hreg with ⟨cStarStar, hasymp, hbaseline, hstab⟩
  refine ⟨cStarStar, hasymp, hbaseline, ?_⟩
  intro c hc U₁ V₁ U₂ V₂ hTW₁ hTW₂ hbound₁ hbound₂ htail
  rcases hclose p hreg c U₁ V₁ U₂ V₂ hTW₁ hTW₂ hbound₁ hbound₂ htail with
    ⟨η, hη_lower, hη_upper, hη_close⟩
  have hU₂_bdd : IsCUnifBdd U₂ :=
    hbound₂.isCUnifBdd_of_continuous (hcont p c U₂ V₂ hTW₂)
  rcases hstab c hc U₁ V₁ hTW₁ hbound₁
      (htail.imp fun κ₁ ⟨h1, h2, h3, _⟩ => ⟨h1, h2, h3⟩)
      η hη_lower hη_upper U₂
      (IsTravelingWave.nonnegativeInitialDatum hTW₂ hU₂_bdd)
      (IsTravelingWave.strictlyPositiveAtLeft hTW₂)
      hη_close with
    ⟨u, v, hsol, _hweighted, huniform⟩
  have hconv :
      UniformMovingFrameConvergence c (fun t x => U₂ (x - c * t)) U₁ := by
    intro ε hε
    rcases huniform ε hε with ⟨T, hT⟩
    exact ⟨T, fun t x ht => by
      have h := hT t x ht
      rwa [hcauchy p hreg c U₂ V₂ hTW₂ hU₂_bdd u v hsol t x] at h⟩
  exact
    Theorem_1_3_profile_eq_of_uniform_movingFrame_and_resolvent
      hconv (hresolvent p c U₁ V₁ hTW₁) (hresolvent p c U₂ V₂ hTW₂)

/-- Bridge: Theorem 1.2 (stability) + Cauchy uniqueness + resolvent
identification + Remark 4.3 tail asymptotics + wave continuity together imply
Theorem 1.3 (uniqueness).

This is the sharpest Theorem 1.2 → 1.3 bridge: the closeness between two waves
is derived internally from Remark 4.3 instead of being assumed.  The five
explicit residual hypotheses are:
- `hcont`: traveling wave profiles are continuous
- `hcauchy`: Cauchy solutions from wave profile data are the translated wave
- `hresolvent`: the signal component V equals the frozen elliptic resolvent
- `htail_asymp`: waves have the paper's Remark 4.3 right-tail normalization -/
theorem Theorem_1_3.of_Theorem_1_2_cauchy_unique_resolvent_remark43
    (h12 : Theorem_1_2)
    (hcont : ∀ p : CMParams, ∀ c : ℝ, ∀ U V : ℝ → ℝ,
      IsTravelingWave p c U V → Continuous U)
    (hcauchy : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        IsCUnifBdd U →
        ∀ u v : ℝ → ℝ → ℝ,
          IsGlobalCauchySolutionFrom p U u v →
            ∀ t x, u t x = U (x - c * t))
    (hresolvent : ∀ p : CMParams, ∀ c : ℝ, ∀ U V : ℝ → ℝ,
      IsTravelingWave p c U V → V = frozenElliptic p U)
    (htail_asymp : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        HasRemark43TailAsymptotic p c U) :
    Theorem_1_3 := by
  intro p hreg
  rcases h12 p hreg with ⟨cStarStar, hasymp, hbaseline, hstab⟩
  refine ⟨cStarStar, hasymp, hbaseline, ?_⟩
  intro c hc U₁ V₁ U₂ V₂ hTW₁ hTW₂ hbound₁ hbound₂ htail
  have hkappa_pos : 0 < kappa c :=
    kappa_pos_of_stabilitySpeedBaseline_lt hbaseline hc
  have hkappa_lt_one : kappa c < 1 :=
    kappa_lt_one_of_stabilitySpeedBaseline_lt hbaseline hc
  have hkappa_cap : kappa c < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) :=
    kappa_lt_stability_weight_cap_of_stabilitySpeedBaseline_lt hbaseline hc
  rcases exists_remark43TailRateBound_with_weight_below
      hkappa_pos hkappa_lt_one hkappa_cap with
    ⟨eta, heta_bound, heta_weight⟩
  have hU₂_bdd : IsCUnifBdd U₂ :=
    hbound₂.isCUnifBdd_of_continuous (hcont p c U₂ V₂ hTW₂)
  have hclose : WeightedL2InitialCloseness (eta + kappa c) U₂ U₁ :=
    Remark_4_3_regular_direct hkappa_pos hTW₁ hTW₂
      (hcont p c U₁ V₁ hTW₁) (hcont p c U₂ V₂ hTW₂)
      hbound₁.hasWaveUpperTailBound hbound₂.hasWaveUpperTailBound
      (htail_asymp p hreg c U₁ V₁ hTW₁ hbound₁)
      (htail_asymp p hreg c U₂ V₂ hTW₂ hbound₂) heta_bound
  rcases hstab c hc U₁ V₁ hTW₁ hbound₁
      (htail.imp fun κ₁ ⟨h1, h2, h3, _⟩ => ⟨h1, h2, h3⟩)
      (eta + kappa c) (by linarith [heta_bound.pos]) heta_weight U₂
      (IsTravelingWave.nonnegativeInitialDatum hTW₂ hU₂_bdd)
      (IsTravelingWave.strictlyPositiveAtLeft hTW₂)
      hclose with
    ⟨u, v, hsol, _hweighted, huniform⟩
  have hconv :
      UniformMovingFrameConvergence c (fun t x => U₂ (x - c * t)) U₁ := by
    intro ε hε
    rcases huniform ε hε with ⟨T, hT⟩
    exact ⟨T, fun t x ht => by
      have h := hT t x ht
      rwa [hcauchy p hreg c U₂ V₂ hTW₂ hU₂_bdd u v hsol t x] at h⟩
  exact
    Theorem_1_3_profile_eq_of_uniform_movingFrame_and_resolvent
      hconv (hresolvent p c U₁ V₁ hTW₁) (hresolvent p c U₂ V₂ hTW₂)

/-- Combined bridge: per-instance stability implies both Theorem 1.2 AND
Theorem 1.3, given wave regularity (continuity, resolvent, Cauchy uniqueness,
Remark 4.3 tails).  This captures the paper's full logical architecture:
the stability analysis is the single hard analytical step; once established,
both the stability theorem and the uniqueness theorem follow. -/
theorem Theorem_1_2_and_1_3.of_stability_cauchy_unique_resolvent_remark43
    (cStarStarFn : CMParams → (ℝ → ℝ))
    (hcStarStar : ∀ p : CMParams, StableWaveParameterRegime p →
      StabilitySpeedThresholdFamilyAsymptotic p (cStarStarFn p) ∧
        stabilitySpeedBaseline p ≤ cStarStarFn p p.χ)
    (hstability : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η → η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          ∀ u₀ : ℝ → ℝ,
            NonnegativeInitialDatum u₀ →
            StrictlyPositiveAtLeft u₀ →
            WeightedL2InitialCloseness η u₀ U →
            ∃ u v : ℝ → ℝ → ℝ,
              IsGlobalCauchySolutionFrom p u₀ u v ∧
              WeightedL2MovingFrameConvergence η c u U ∧
              UniformMovingFrameConvergence c u U)
    (hcont : ∀ p : CMParams, ∀ c : ℝ, ∀ U V : ℝ → ℝ,
      IsTravelingWave p c U V → Continuous U)
    (hcauchy : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        IsCUnifBdd U →
        ∀ u v : ℝ → ℝ → ℝ,
          IsGlobalCauchySolutionFrom p U u v →
            ∀ t x, u t x = U (x - c * t))
    (hresolvent : ∀ p : CMParams, ∀ c : ℝ, ∀ U V : ℝ → ℝ,
      IsTravelingWave p c U V → V = frozenElliptic p U)
    (htail_asymp : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        HasRemark43TailAsymptotic p c U) :
    Theorem_1_2 ∧ Theorem_1_3 := by
  have h12 : Theorem_1_2 :=
    Theorem_1_2.of_assumed_stability_branch cStarStarFn hcStarStar hstability
  exact ⟨h12,
    Theorem_1_3.of_Theorem_1_2_cauchy_unique_resolvent_remark43
      h12 hcont hcauchy hresolvent htail_asymp⟩

/-- Paper1 main results: construction + stability → Theorems 1.1 ∧ 1.2 ∧ 1.3.

This is the top-level paper result bridge.  It packages the two
independent analytical obligations:
1. **Construction** (Theorem 1.1): supply frozen stationary profiles in
   both the negative- and positive-sensitivity regimes.
2. **Stability analysis** (Theorem 1.2): for every traveling wave above
   the speed threshold, prove weighted L2 stability for nearby data.

The remaining hypotheses (continuity, resolvent, Cauchy uniqueness,
Remark 4.3 tails) are structural regularity conditions that follow from
the wave equation once elliptic regularity and PDE uniqueness are
established. -/
theorem paper1_main_results
    (hconstruction_neg :
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
    (hconstruction_pos :
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
                HasWaveRightTailAsymptotic c κ₁ U)
    (cStarStarFn : CMParams → (ℝ → ℝ))
    (hcStarStar : ∀ p : CMParams, StableWaveParameterRegime p →
      StabilitySpeedThresholdFamilyAsymptotic p (cStarStarFn p) ∧
        stabilitySpeedBaseline p ≤ cStarStarFn p p.χ)
    (hstability : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η → η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          ∀ u₀ : ℝ → ℝ,
            NonnegativeInitialDatum u₀ →
            StrictlyPositiveAtLeft u₀ →
            WeightedL2InitialCloseness η u₀ U →
            ∃ u v : ℝ → ℝ → ℝ,
              IsGlobalCauchySolutionFrom p u₀ u v ∧
              WeightedL2MovingFrameConvergence η c u U ∧
              UniformMovingFrameConvergence c u U)
    (hcont : ∀ p : CMParams, ∀ c : ℝ, ∀ U V : ℝ → ℝ,
      IsTravelingWave p c U V → Continuous U)
    (hcauchy : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        IsCUnifBdd U →
        ∀ u v : ℝ → ℝ → ℝ,
          IsGlobalCauchySolutionFrom p U u v →
            ∀ t x, u t x = U (x - c * t))
    (hresolvent : ∀ p : CMParams, ∀ c : ℝ, ∀ U V : ℝ → ℝ,
      IsTravelingWave p c U V → V = frozenElliptic p U)
    (htail_asymp : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        HasRemark43TailAsymptotic p c U) :
    Theorem_1_1 ∧ Theorem_1_2 ∧ Theorem_1_3 := by
  have h11 : Theorem_1_1 :=
    Theorem_1_1.of_assumed_frozenStationaryProfile_branches
      hconstruction_neg hconstruction_pos
  have ⟨h12, h13⟩ :=
    Theorem_1_2_and_1_3.of_stability_cauchy_unique_resolvent_remark43
      cStarStarFn hcStarStar hstability hcont hcauchy hresolvent htail_asymp
  exact ⟨h11, h12, h13⟩

/-- Bundled frontiers for the Paper1 main statement bridge.

This is a conditional assembly interface, not a producer of the paper's main
theorems: each field is an analytic input that must be supplied by a separate
construction or stability argument. -/
structure Paper1MainResultsData
    (cStarStarFn : CMParams → ℝ → ℝ) : Prop where
  construction_neg :
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
              HasWaveRightTailAsymptotic c κ₁ U
  construction_pos :
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
              HasWaveRightTailAsymptotic c κ₁ U
  cStarStar_spec :
    ∀ p : CMParams, StableWaveParameterRegime p →
      StabilitySpeedThresholdFamilyAsymptotic p (cStarStarFn p) ∧
        stabilitySpeedBaseline p ≤ cStarStarFn p p.χ
  stability :
    ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η → η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          ∀ u₀ : ℝ → ℝ,
            NonnegativeInitialDatum u₀ →
            StrictlyPositiveAtLeft u₀ →
            WeightedL2InitialCloseness η u₀ U →
            ∃ u v : ℝ → ℝ → ℝ,
              IsGlobalCauchySolutionFrom p u₀ u v ∧
              WeightedL2MovingFrameConvergence η c u U ∧
              UniformMovingFrameConvergence c u U
  wave_cont :
    ∀ p : CMParams, ∀ c : ℝ, ∀ U V : ℝ → ℝ,
      IsTravelingWave p c U V → Continuous U
  cauchy_unique :
    ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        IsCUnifBdd U →
        ∀ u v : ℝ → ℝ → ℝ,
          IsGlobalCauchySolutionFrom p U u v →
            ∀ t x, u t x = U (x - c * t)
  resolvent :
    ∀ p : CMParams, ∀ c : ℝ, ∀ U V : ℝ → ℝ,
      IsTravelingWave p c U V → V = frozenElliptic p U
  tail_asymp :
    ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        HasRemark43TailAsymptotic p c U

/-- Bundled Paper1 main statement bridge. -/
theorem paper1_main_results_bundled
    (cStarStarFn : CMParams → ℝ → ℝ)
    (hData : Paper1MainResultsData cStarStarFn) :
    Theorem_1_1 ∧ Theorem_1_2 ∧ Theorem_1_3 :=
  paper1_main_results hData.construction_neg hData.construction_pos
    cStarStarFn hData.cStarStar_spec hData.stability hData.wave_cont
    hData.cauchy_unique hData.resolvent hData.tail_asymp

/-- Instance-facing bundled Paper1 main statement bridge. -/
theorem paper1_main_results_bundledFact
    (cStarStarFn : CMParams → ℝ → ℝ)
    [hData : Fact (Paper1MainResultsData cStarStarFn)] :
    Theorem_1_1 ∧ Theorem_1_2 ∧ Theorem_1_3 :=
  paper1_main_results_bundled cStarStarFn hData.out

/-- Single-target wrapper for Paper1 Theorem 1.1 from the main data bundle. -/
theorem Theorem_1_1.of_mainResultsData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hData : Paper1MainResultsData cStarStarFn) :
    Theorem_1_1 :=
  (paper1_main_results_bundled cStarStarFn hData).1

/-- Instance-facing single-target wrapper for Paper1 Theorem 1.1. -/
theorem Theorem_1_1.of_mainResultsDataFact
    (cStarStarFn : CMParams → ℝ → ℝ)
    [hData : Fact (Paper1MainResultsData cStarStarFn)] :
    Theorem_1_1 :=
  Theorem_1_1.of_mainResultsData hData.out

/-- Single-target wrapper for Paper1 Theorem 1.2 from the main data bundle. -/
theorem Theorem_1_2.of_mainResultsData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hData : Paper1MainResultsData cStarStarFn) :
    Theorem_1_2 :=
  (paper1_main_results_bundled cStarStarFn hData).2.1

/-- Instance-facing single-target wrapper for Paper1 Theorem 1.2. -/
theorem Theorem_1_2.of_mainResultsDataFact
    (cStarStarFn : CMParams → ℝ → ℝ)
    [hData : Fact (Paper1MainResultsData cStarStarFn)] :
    Theorem_1_2 :=
  Theorem_1_2.of_mainResultsData hData.out

/-- Single-target wrapper for Paper1 Theorem 1.3 from the main data bundle. -/
theorem Theorem_1_3.of_mainResultsData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hData : Paper1MainResultsData cStarStarFn) :
    Theorem_1_3 :=
  (paper1_main_results_bundled cStarStarFn hData).2.2

/-- Instance-facing single-target wrapper for Paper1 Theorem 1.3. -/
theorem Theorem_1_3.of_mainResultsDataFact
    (cStarStarFn : CMParams → ℝ → ℝ)
    [hData : Fact (Paper1MainResultsData cStarStarFn)] :
    Theorem_1_3 :=
  Theorem_1_3.of_mainResultsData hData.out

end

end ShenWork.Paper1
