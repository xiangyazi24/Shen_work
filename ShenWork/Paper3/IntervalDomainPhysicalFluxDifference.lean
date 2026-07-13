/- Actual polarized route-(a) flux derivative on two classical slices. -/
import ShenWork.Paper3.IntervalDomainFluxDerivativeDifference
import ShenWork.Paper3.IntervalDomainSignalDifferenceBounds
import ShenWork.Paper3.IntervalDomainPhysicalFluxDerivativeRouteA

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

/-- One common coefficient large enough for all value, gradient, sensitivity,
and sensitivity-gradient factors in the polarized flux algebra. -/
def paper3RouteAPolarizedPointConstant
    (p : CM2Params) (Cself Cdiff : ℝ) : ℝ :=
  1 + 2 * Cself + 3 * Cdiff + 2 * p.β * Cself +
    3 * p.β * Cdiff + 6 * p.β * (p.β + 1) * Cdiff * Cself

theorem paper3RouteAPolarizedPointConstant_pos
    (p : CM2Params) {Cself Cdiff : ℝ}
    (hself : 0 ≤ Cself) (hdiff : 0 ≤ Cdiff) :
    0 < paper3RouteAPolarizedPointConstant p Cself Cdiff := by
  unfold paper3RouteAPolarizedPointConstant
  have hβ1 : 0 ≤ p.β + 1 := by linarith [p.hβ]
  have h₂self : 0 ≤ 2 * Cself := mul_nonneg (by norm_num) hself
  have h₃diff : 0 ≤ 3 * Cdiff := mul_nonneg (by norm_num) hdiff
  have h₂βself : 0 ≤ 2 * p.β * Cself :=
    mul_nonneg (mul_nonneg (by norm_num) p.hβ) hself
  have h₃βdiff : 0 ≤ 3 * p.β * Cdiff :=
    mul_nonneg (mul_nonneg (by norm_num) p.hβ) hdiff
  have h₆ : 0 ≤ 6 * p.β * (p.β + 1) * Cdiff * Cself :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) p.hβ) hβ1) hdiff)
      hself
  linarith

set_option maxHeartbeats 3000000 in
/-- Actual physical route-(a) flux derivative is locally Lipschitz on two
strong positive slices.  The constant is independent of the slices and the
point. -/
theorem paper3ChemFluxRemainder_deriv_difference_pointwise
    {p : CM2Params} {T t uStar vStar M₁ M₂ D Cself Cdiff : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T u₂ v₂)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hm : p.m = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (Hsplit₁ : IntervalSolutionSignalSplitData p uStar (u₁ t))
    (Hsplit₂ : IntervalSolutionSignalSplitData p uStar (u₂ t))
    (Hlin₁ : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticLinearProfile p uStar (u₁ t)))
    (Hquad₁ : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticRemainderProfile p uStar (u₁ t)))
    (Hlin₂ : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticLinearProfile p uStar (u₂ t)))
    (Hquad₂ : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticRemainderProfile p uStar (u₂ t)))
    (hM₁0 : 0 ≤ M₁) (hM₂0 : 0 ≤ M₂)
    (hM₁1 : M₁ ≤ 1) (hM₂1 : M₂ ≤ 1) (hD0 : 0 ≤ D)
    (hCself : 0 < Cself) (hCdiff : 0 < Cdiff)
    (hw₁ : ∀ x : intervalDomainPoint, |u₁ t x - uStar| ≤ M₁)
    (hw₂ : ∀ x : intervalDomainPoint, |u₂ t x - uStar| ≤ M₂)
    (hwx₁ : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |deriv (intervalDomainLift (u₁ t)) x| ≤ M₁)
    (hwx₂ : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |deriv (intervalDomainLift (u₂ t)) x| ≤ M₂)
    (hwD : ∀ x : intervalDomainPoint, |u₁ t x - u₂ t x| ≤ D)
    (hwxD : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |deriv (intervalDomainLift (u₁ t)) x -
        deriv (intervalDomainLift (u₂ t)) x| ≤ D)
    (hsignal₁ : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3LinearSignalValue p uStar (u₁ t) x| ≤ Cself * M₁ ∧
      |paper3LinearSignalGradient p uStar (u₁ t) x| ≤ Cself * M₁ ∧
      |paper3LinearSignalLaplacian p uStar (u₁ t) x| ≤ Cself * M₁ ∧
      |paper3QuadraticSignalValue p uStar (u₁ t) x| ≤ Cself * M₁ ^ 2 ∧
      |paper3QuadraticSignalGradient p uStar (u₁ t) x| ≤ Cself * M₁ ^ 2 ∧
      |paper3QuadraticSignalLaplacian p uStar (u₁ t) x| ≤ Cself * M₁ ^ 2)
    (hsignal₂ : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3LinearSignalValue p uStar (u₂ t) x| ≤ Cself * M₂ ∧
      |paper3LinearSignalGradient p uStar (u₂ t) x| ≤ Cself * M₂ ∧
      |paper3LinearSignalLaplacian p uStar (u₂ t) x| ≤ Cself * M₂ ∧
      |paper3QuadraticSignalValue p uStar (u₂ t) x| ≤ Cself * M₂ ^ 2 ∧
      |paper3QuadraticSignalGradient p uStar (u₂ t) x| ≤ Cself * M₂ ^ 2 ∧
      |paper3QuadraticSignalLaplacian p uStar (u₂ t) x| ≤ Cself * M₂ ^ 2)
    (hsignalD : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3LinearSignalValue p uStar (u₁ t) x -
          paper3LinearSignalValue p uStar (u₂ t) x| ≤ Cdiff * D ∧
      |paper3LinearSignalGradient p uStar (u₁ t) x -
          paper3LinearSignalGradient p uStar (u₂ t) x| ≤ Cdiff * D ∧
      |paper3LinearSignalLaplacian p uStar (u₁ t) x -
          paper3LinearSignalLaplacian p uStar (u₂ t) x| ≤ Cdiff * D ∧
      |paper3QuadraticSignalValue p uStar (u₁ t) x -
          paper3QuadraticSignalValue p uStar (u₂ t) x| ≤
            Cdiff * (M₁ + M₂) * D ∧
      |paper3QuadraticSignalGradient p uStar (u₁ t) x -
          paper3QuadraticSignalGradient p uStar (u₂ t) x| ≤
            Cdiff * (M₁ + M₂) * D ∧
      |paper3QuadraticSignalLaplacian p uStar (u₁ t) x -
          paper3QuadraticSignalLaplacian p uStar (u₂ t) x| ≤
            Cdiff * (M₁ + M₂) * D) :
    let C := paper3RouteAPolarizedPointConstant p Cself Cdiff
    let K := EliminatedFluxDerivativePolarizedPointData.eliminatedFluxDerivativePolarizedConstant
      (paper3SensitivityFactor p.β vStar) C (uStar + 1)
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |deriv (paper3ChemFluxRemainderProfileM
          p uStar vStar (u₁ t) (v₁ t)) x -
        deriv (paper3ChemFluxRemainderProfileM
          p uStar vStar (u₂ t) (v₂ t)) x| ≤
        K * (M₁ + M₂) * D := by
  dsimp only
  let C := paper3RouteAPolarizedPointConstant p Cself Cdiff
  have hC : 0 < C := by
    simpa [C] using paper3RouteAPolarizedPointConstant_pos
      p hCself.le hCdiff.le
  let U := uStar + 1
  have hU : 0 ≤ U := by dsimp [U]; linarith [heq.u_pos]
  have hβ1 : 0 ≤ p.β + 1 := by linarith [p.hβ]
  have hβself0 : 0 ≤ p.β * Cself := mul_nonneg p.hβ hCself.le
  have hβdiff0 : 0 ≤ p.β * Cdiff := mul_nonneg p.hβ hCdiff.le
  have hβ1diffself0 : 0 ≤ p.β * (p.β + 1) * Cdiff * Cself :=
    mul_nonneg
      (mul_nonneg (mul_nonneg p.hβ hβ1) hCdiff.le) hCself.le
  have hC_self : Cself ≤ C := by
    dsimp [C, paper3RouteAPolarizedPointConstant]
    nlinarith
  have hC_2self : 2 * Cself ≤ C := by
    dsimp [C, paper3RouteAPolarizedPointConstant]
    nlinarith
  have hC_2βself : 2 * p.β * Cself ≤ C := by
    dsimp [C, paper3RouteAPolarizedPointConstant]
    nlinarith
  have hC_diff : Cdiff ≤ C := by
    dsimp [C, paper3RouteAPolarizedPointConstant]
    nlinarith
  have hC_3diff : 3 * Cdiff ≤ C := by
    dsimp [C, paper3RouteAPolarizedPointConstant]
    nlinarith
  have hC_3βdiff : 3 * p.β * Cdiff ≤ C := by
    dsimp [C, paper3RouteAPolarizedPointConstant]
    nlinarith
  have hC_sensitivityDiff :
      3 * p.β * Cdiff +
          6 * p.β * (p.β + 1) * Cdiff * Cself ≤ C := by
    dsimp [C, paper3RouteAPolarizedPointConstant]
    nlinarith
  intro x hx
  let xp : intervalDomainPoint := ⟨x, Set.Ioo_subset_Icc_self hx⟩
  have hlift₁ : intervalDomainLift (u₁ t) x = u₁ t xp := by
    simp [intervalDomainLift, xp, Set.Ioo_subset_Icc_self hx]
  have hlift₂ : intervalDomainLift (u₂ t) x = u₂ t xp := by
    simp [intervalDomainLift, xp, Set.Ioo_subset_Icc_self hx]
  rcases hsignal₁ x (Set.Ioo_subset_Icc_self hx) with
    ⟨hz1v₁, hz1x₁, hz1xx₁, hz2v₁, hz2x₁, hz2xx₁⟩
  rcases hsignal₂ x (Set.Ioo_subset_Icc_self hx) with
    ⟨hz1v₂, hz1x₂, hz1xx₂, hz2v₂, hz2x₂, hz2xx₂⟩
  rcases hsignalD x (Set.Ioo_subset_Icc_self hx) with
    ⟨hz1vD, hz1xD, hz1xxD, hz2vD, hz2xD, hz2xxD⟩
  have hS : M₁ + M₂ ≤ 2 := by linarith
  have hvval₁ := solution_lift_v_sub_eq_signalComponents
    hsol₁ ht heq Hsplit₁ hx
  have hvval₂ := solution_lift_v_sub_eq_signalComponents
    hsol₂ ht heq Hsplit₂ hx
  have hvgrad₁ := solution_lift_v_deriv_eq_signalGradientComponents
    hsol₁ ht heq Hsplit₁ (Set.Ioo_subset_Icc_self hx)
  have hvgrad₂ := solution_lift_v_deriv_eq_signalGradientComponents
    hsol₂ ht heq Hsplit₂ (Set.Ioo_subset_Icc_self hx)
  have hv_nonneg₁ := solution_lift_v_nonneg_Icc hsol₁ ht x
    (Set.Ioo_subset_Icc_self hx)
  have hv_nonneg₂ := solution_lift_v_nonneg_Icc hsol₂ ht x
    (Set.Ioo_subset_Icc_self hx)
  have hvsize₁ : |intervalDomainLift (v₁ t) x - vStar| ≤ 2 * Cself * M₁ := by
    rw [hvval₁]
    calc
      _ ≤ |paper3LinearSignalValue p uStar (u₁ t) x| +
          |paper3QuadraticSignalValue p uStar (u₁ t) x| := abs_add_le _ _
      _ ≤ Cself * M₁ + Cself * M₁ ^ 2 := add_le_add hz1v₁ hz2v₁
      _ ≤ 2 * Cself * M₁ := by
        nlinarith [mul_nonneg hCself.le hM₁0]
  have hvsize₂ : |intervalDomainLift (v₂ t) x - vStar| ≤ 2 * Cself * M₂ := by
    rw [hvval₂]
    calc
      _ ≤ |paper3LinearSignalValue p uStar (u₂ t) x| +
          |paper3QuadraticSignalValue p uStar (u₂ t) x| := abs_add_le _ _
      _ ≤ Cself * M₂ + Cself * M₂ ^ 2 := add_le_add hz1v₂ hz2v₂
      _ ≤ 2 * Cself * M₂ := by
        nlinarith [mul_nonneg hCself.le hM₂0]
  have hvgradsize₁ : |deriv (intervalDomainLift (v₁ t)) x| ≤
      2 * Cself * M₁ := by
    rw [hvgrad₁]
    calc
      _ ≤ |paper3LinearSignalGradient p uStar (u₁ t) x| +
          |paper3QuadraticSignalGradient p uStar (u₁ t) x| := abs_add_le _ _
      _ ≤ Cself * M₁ + Cself * M₁ ^ 2 := add_le_add hz1x₁ hz2x₁
      _ ≤ 2 * Cself * M₁ := by
        nlinarith [mul_nonneg hCself.le hM₁0]
  have hvgradsize₂ : |deriv (intervalDomainLift (v₂ t)) x| ≤
      2 * Cself * M₂ := by
    rw [hvgrad₂]
    calc
      _ ≤ |paper3LinearSignalGradient p uStar (u₂ t) x| +
          |paper3QuadraticSignalGradient p uStar (u₂ t) x| := abs_add_le _ _
      _ ≤ Cself * M₂ + Cself * M₂ ^ 2 := add_le_add hz1x₂ hz2x₂
      _ ≤ 2 * Cself * M₂ := by
        nlinarith [mul_nonneg hCself.le hM₂0]
  have hvD : |intervalDomainLift (v₁ t) x - intervalDomainLift (v₂ t) x| ≤
      3 * Cdiff * D := by
    rw [show intervalDomainLift (v₁ t) x - intervalDomainLift (v₂ t) x =
      (paper3LinearSignalValue p uStar (u₁ t) x -
        paper3LinearSignalValue p uStar (u₂ t) x) +
      (paper3QuadraticSignalValue p uStar (u₁ t) x -
        paper3QuadraticSignalValue p uStar (u₂ t) x) by linarith]
    calc
      _ ≤ |paper3LinearSignalValue p uStar (u₁ t) x -
            paper3LinearSignalValue p uStar (u₂ t) x| +
          |paper3QuadraticSignalValue p uStar (u₁ t) x -
            paper3QuadraticSignalValue p uStar (u₂ t) x| := abs_add_le _ _
      _ ≤ Cdiff * D + Cdiff * (M₁ + M₂) * D := add_le_add hz1vD hz2vD
      _ ≤ 3 * Cdiff * D := by
        nlinarith [mul_nonneg hCdiff.le hD0]
  have hvgradD : |deriv (intervalDomainLift (v₁ t)) x -
      deriv (intervalDomainLift (v₂ t)) x| ≤ 3 * Cdiff * D := by
    rw [hvgrad₁, hvgrad₂]
    rw [show
      (paper3LinearSignalGradient p uStar (u₁ t) x +
          paper3QuadraticSignalGradient p uStar (u₁ t) x) -
        (paper3LinearSignalGradient p uStar (u₂ t) x +
          paper3QuadraticSignalGradient p uStar (u₂ t) x) =
      (paper3LinearSignalGradient p uStar (u₁ t) x -
        paper3LinearSignalGradient p uStar (u₂ t) x) +
      (paper3QuadraticSignalGradient p uStar (u₁ t) x -
        paper3QuadraticSignalGradient p uStar (u₂ t) x) by ring]
    calc
      _ ≤ |paper3LinearSignalGradient p uStar (u₁ t) x -
            paper3LinearSignalGradient p uStar (u₂ t) x| +
          |paper3QuadraticSignalGradient p uStar (u₁ t) x -
            paper3QuadraticSignalGradient p uStar (u₂ t) x| := abs_add_le _ _
      _ ≤ Cdiff * D + Cdiff * (M₁ + M₂) * D := add_le_add hz1xD hz2xD
      _ ≤ 3 * Cdiff * D := by
        nlinarith [mul_nonneg hCdiff.le hD0]
  have hq₁ := paper3SensitivityFactor_sub_abs_le p.hβ hv_nonneg₁ heq.v_nonneg
  have hq₂ := paper3SensitivityFactor_sub_abs_le p.hβ hv_nonneg₂ heq.v_nonneg
  have hqD := paper3SensitivityFactor_sub_abs_le p.hβ hv_nonneg₁ hv_nonneg₂
  have hqx₁ := paper3SensitivityDerivativeValue_abs_le
    (vx := deriv (intervalDomainLift (v₁ t)) x) p.hβ hv_nonneg₁
  have hqx₂ := paper3SensitivityDerivativeValue_abs_le
    (vx := deriv (intervalDomainLift (v₂ t)) x) p.hβ hv_nonneg₂
  have hqxD := paper3SensitivityDerivativeValue_sub_abs_le
    (vx₁ := deriv (intervalDomainLift (v₁ t)) x)
    (vx₂ := deriv (intervalDomainLift (v₂ t)) x)
    p.hβ hv_nonneg₁ hv_nonneg₂
  let HP : EliminatedFluxDerivativePolarizedPointData :=
    { uStar := uStar
      qStar := paper3SensitivityFactor p.β vStar
      M₁ := M₁, M₂ := M₂, D := D, U := U, C := C
      w₁ := intervalDomainLift (u₁ t) x - uStar
      wx₁ := deriv (intervalDomainLift (u₁ t)) x
      z1x₁ := paper3LinearSignalGradient p uStar (u₁ t) x
      z1xx₁ := paper3LinearSignalLaplacian p uStar (u₁ t) x
      z2x₁ := paper3QuadraticSignalGradient p uStar (u₁ t) x
      z2xx₁ := paper3QuadraticSignalLaplacian p uStar (u₁ t) x
      qDiff₁ := paper3SensitivityFactor p.β (intervalDomainLift (v₁ t) x) -
        paper3SensitivityFactor p.β vStar
      qx₁ := paper3SensitivityDerivativeValue p.β
        (intervalDomainLift (v₁ t) x) (deriv (intervalDomainLift (v₁ t)) x)
      zx₁ := paper3LinearSignalGradient p uStar (u₁ t) x +
        paper3QuadraticSignalGradient p uStar (u₁ t) x
      zxx₁ := paper3LinearSignalLaplacian p uStar (u₁ t) x +
        paper3QuadraticSignalLaplacian p uStar (u₁ t) x
      w₂ := intervalDomainLift (u₂ t) x - uStar
      wx₂ := deriv (intervalDomainLift (u₂ t)) x
      z1x₂ := paper3LinearSignalGradient p uStar (u₂ t) x
      z1xx₂ := paper3LinearSignalLaplacian p uStar (u₂ t) x
      z2x₂ := paper3QuadraticSignalGradient p uStar (u₂ t) x
      z2xx₂ := paper3QuadraticSignalLaplacian p uStar (u₂ t) x
      qDiff₂ := paper3SensitivityFactor p.β (intervalDomainLift (v₂ t) x) -
        paper3SensitivityFactor p.β vStar
      qx₂ := paper3SensitivityDerivativeValue p.β
        (intervalDomainLift (v₂ t) x) (deriv (intervalDomainLift (v₂ t)) x)
      zx₂ := paper3LinearSignalGradient p uStar (u₂ t) x +
        paper3QuadraticSignalGradient p uStar (u₂ t) x
      zxx₂ := paper3LinearSignalLaplacian p uStar (u₂ t) x +
        paper3QuadraticSignalLaplacian p uStar (u₂ t) x
      M₁_nonneg := hM₁0, M₂_nonneg := hM₂0
      M₁_le_one := hM₁1, M₂_le_one := hM₂1, D_nonneg := hD0
      U_nonneg := hU, C_nonneg := hC.le
      w₁_bound := by simpa [hlift₁] using hw₁ xp
      wx₁_bound := hwx₁ x hx
      u₁_bound := by
        rw [show uStar + (intervalDomainLift (u₁ t) x - uStar) =
          intervalDomainLift (u₁ t) x by ring]
        simpa [U, hlift₁] using
        (calc |u₁ t xp| ≤ uStar + M₁ := by
                calc |u₁ t xp| = |uStar + (u₁ t xp - uStar)| := by ring_nf
                     _ ≤ |uStar| + |u₁ t xp - uStar| := abs_add_le _ _
                     _ ≤ uStar + M₁ := by
                       rw [abs_of_pos heq.u_pos]
                       linarith [hw₁ xp]
              _ ≤ uStar + 1 := by linarith)
      w₂_bound := by simpa [hlift₂] using hw₂ xp
      wx₂_bound := hwx₂ x hx
      u₂_bound := by
        rw [show uStar + (intervalDomainLift (u₂ t) x - uStar) =
          intervalDomainLift (u₂ t) x by ring]
        simpa [U, hlift₂] using
        (calc |u₂ t xp| ≤ uStar + M₂ := by
                calc |u₂ t xp| = |uStar + (u₂ t xp - uStar)| := by ring_nf
                     _ ≤ |uStar| + |u₂ t xp - uStar| := abs_add_le _ _
                     _ ≤ uStar + M₂ := by
                       rw [abs_of_pos heq.u_pos]
                       linarith [hw₂ xp]
              _ ≤ uStar + 1 := by linarith)
      linear₁_bounds := by
        have hselfM : Cself * M₁ ≤ C * M₁ :=
          mul_le_mul_of_nonneg_right hC_self hM₁0
        have h2selfM : 2 * Cself * M₁ ≤ C * M₁ :=
          mul_le_mul_of_nonneg_right hC_2self hM₁0
        have h2βselfM : 2 * p.β * Cself * M₁ ≤ C * M₁ :=
          mul_le_mul_of_nonneg_right hC_2βself hM₁0
        refine ⟨hz1x₁.trans hselfM, hz1xx₁.trans hselfM, ?_, ?_, ?_, ?_⟩
        · exact hq₁.trans <| (mul_le_mul_of_nonneg_left hvsize₁ p.hβ).trans <| by
            convert h2βselfM using 1
            all_goals ring
        · exact hqx₁.trans <| (mul_le_mul_of_nonneg_left hvgradsize₁ p.hβ).trans <| by
            convert h2βselfM using 1
            all_goals ring
        · exact (abs_add_le _ _).trans <| (add_le_add hz1x₁ hz2x₁).trans <| by
            calc
              Cself * M₁ + Cself * M₁ ^ 2 ≤ 2 * Cself * M₁ := by
                nlinarith [mul_nonneg hCself.le hM₁0]
              _ ≤ C * M₁ := h2selfM
        · exact (abs_add_le _ _).trans <| (add_le_add hz1xx₁ hz2xx₁).trans <| by
            calc
              Cself * M₁ + Cself * M₁ ^ 2 ≤ 2 * Cself * M₁ := by
                nlinarith [mul_nonneg hCself.le hM₁0]
              _ ≤ C * M₁ := h2selfM
      linear₂_bounds := by
        have hselfM : Cself * M₂ ≤ C * M₂ :=
          mul_le_mul_of_nonneg_right hC_self hM₂0
        have h2selfM : 2 * Cself * M₂ ≤ C * M₂ :=
          mul_le_mul_of_nonneg_right hC_2self hM₂0
        have h2βselfM : 2 * p.β * Cself * M₂ ≤ C * M₂ :=
          mul_le_mul_of_nonneg_right hC_2βself hM₂0
        refine ⟨hz1x₂.trans hselfM, hz1xx₂.trans hselfM, ?_, ?_, ?_, ?_⟩
        · exact hq₂.trans <| (mul_le_mul_of_nonneg_left hvsize₂ p.hβ).trans <| by
            convert h2βselfM using 1
            all_goals ring
        · exact hqx₂.trans <| (mul_le_mul_of_nonneg_left hvgradsize₂ p.hβ).trans <| by
            convert h2βselfM using 1
            all_goals ring
        · exact (abs_add_le _ _).trans <| (add_le_add hz1x₂ hz2x₂).trans <| by
            calc
              Cself * M₂ + Cself * M₂ ^ 2 ≤ 2 * Cself * M₂ := by
                nlinarith [mul_nonneg hCself.le hM₂0]
              _ ≤ C * M₂ := h2selfM
        · exact (abs_add_le _ _).trans <| (add_le_add hz1xx₂ hz2xx₂).trans <| by
            calc
              Cself * M₂ + Cself * M₂ ^ 2 ≤ 2 * Cself * M₂ := by
                nlinarith [mul_nonneg hCself.le hM₂0]
              _ ≤ C * M₂ := h2selfM
      quadratic₁_bounds := by
        exact ⟨hz2x₁.trans (mul_le_mul_of_nonneg_right hC_self (sq_nonneg M₁)),
          hz2xx₁.trans (mul_le_mul_of_nonneg_right hC_self (sq_nonneg M₁))⟩
      quadratic₂_bounds := by
        exact ⟨hz2x₂.trans (mul_le_mul_of_nonneg_right hC_self (sq_nonneg M₂)),
          hz2xx₂.trans (mul_le_mul_of_nonneg_right hC_self (sq_nonneg M₂))⟩
      w_diff := by simpa [hlift₁, hlift₂] using hwD xp
      wx_diff := hwxD x hx
      linear_diff_bounds := by
        have hdiffD : Cdiff * D ≤ C * D :=
          mul_le_mul_of_nonneg_right hC_diff hD0
        have h3diffD : 3 * Cdiff * D ≤ C * D :=
          mul_le_mul_of_nonneg_right hC_3diff hD0
        have h3βdiffD : 3 * p.β * Cdiff * D ≤ C * D :=
          mul_le_mul_of_nonneg_right hC_3βdiff hD0
        have hsensD :
            (3 * p.β * Cdiff +
                6 * p.β * (p.β + 1) * Cdiff * Cself) * D ≤ C * D :=
          mul_le_mul_of_nonneg_right hC_sensitivityDiff hD0
        refine ⟨hz1xD.trans hdiffD, hz1xxD.trans hdiffD, ?_, ?_, ?_, ?_⟩
        · rw [show
            (paper3SensitivityFactor p.β (intervalDomainLift (v₁ t) x) -
                paper3SensitivityFactor p.β vStar) -
              (paper3SensitivityFactor p.β (intervalDomainLift (v₂ t) x) -
                paper3SensitivityFactor p.β vStar) =
              paper3SensitivityFactor p.β (intervalDomainLift (v₁ t) x) -
                paper3SensitivityFactor p.β (intervalDomainLift (v₂ t) x) by ring]
          exact hqD.trans <| (mul_le_mul_of_nonneg_left hvD p.hβ).trans <| by
            convert h3βdiffD using 1
            all_goals ring
        · have hfirst :
              p.β * |deriv (intervalDomainLift (v₁ t)) x -
                  deriv (intervalDomainLift (v₂ t)) x| ≤
                3 * p.β * Cdiff * D := by
            calc
              _ ≤ p.β * (3 * Cdiff * D) :=
                mul_le_mul_of_nonneg_left hvgradD p.hβ
              _ = _ := by ring
          have hsecond :
              p.β * (p.β + 1) *
                  |intervalDomainLift (v₁ t) x - intervalDomainLift (v₂ t) x| *
                  |deriv (intervalDomainLift (v₂ t)) x| ≤
                6 * p.β * (p.β + 1) * Cdiff * Cself * D := by
            have hββ1 : 0 ≤ p.β * (p.β + 1) := mul_nonneg p.hβ hβ1
            have h3diffD0 : 0 ≤ 3 * Cdiff * D := by positivity
            have h2self : 0 ≤ 2 * Cself := by positivity
            calc
              _ ≤ p.β * (p.β + 1) * (3 * Cdiff * D) *
                  |deriv (intervalDomainLift (v₂ t)) x| := by
                apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                exact mul_le_mul_of_nonneg_left hvD hββ1
              _ ≤ p.β * (p.β + 1) * (3 * Cdiff * D) *
                  (2 * Cself * M₂) := by
                exact mul_le_mul_of_nonneg_left hvgradsize₂
                  (mul_nonneg hββ1 h3diffD0)
              _ ≤ p.β * (p.β + 1) * (3 * Cdiff * D) *
                  (2 * Cself * 1) := by
                apply mul_le_mul_of_nonneg_left _ (mul_nonneg hββ1 h3diffD0)
                exact mul_le_mul_of_nonneg_left hM₂1 h2self
              _ = _ := by ring
          exact hqxD.trans <| (add_le_add hfirst hsecond).trans <| by
            convert hsensD using 1
            all_goals ring
        · rw [show
            (paper3LinearSignalGradient p uStar (u₁ t) x +
                paper3QuadraticSignalGradient p uStar (u₁ t) x) -
              (paper3LinearSignalGradient p uStar (u₂ t) x +
                paper3QuadraticSignalGradient p uStar (u₂ t) x) =
              (paper3LinearSignalGradient p uStar (u₁ t) x -
                paper3LinearSignalGradient p uStar (u₂ t) x) +
              (paper3QuadraticSignalGradient p uStar (u₁ t) x -
                paper3QuadraticSignalGradient p uStar (u₂ t) x) by ring]
          exact (abs_add_le _ _).trans <| (add_le_add hz1xD hz2xD).trans <| by
            have hquadD : Cdiff * (M₁ + M₂) * D ≤ 2 * Cdiff * D := by
              calc
                _ ≤ Cdiff * 2 * D :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hS hCdiff.le) hD0
                _ = _ := by ring
            calc
              Cdiff * D + Cdiff * (M₁ + M₂) * D ≤
                  Cdiff * D + 2 * Cdiff * D := add_le_add (le_refl _) hquadD
              _ = 3 * Cdiff * D := by ring
              _ ≤ C * D := h3diffD
        · rw [show
            (paper3LinearSignalLaplacian p uStar (u₁ t) x +
                paper3QuadraticSignalLaplacian p uStar (u₁ t) x) -
              (paper3LinearSignalLaplacian p uStar (u₂ t) x +
                paper3QuadraticSignalLaplacian p uStar (u₂ t) x) =
              (paper3LinearSignalLaplacian p uStar (u₁ t) x -
                paper3LinearSignalLaplacian p uStar (u₂ t) x) +
              (paper3QuadraticSignalLaplacian p uStar (u₁ t) x -
                paper3QuadraticSignalLaplacian p uStar (u₂ t) x) by ring]
          exact (abs_add_le _ _).trans <| (add_le_add hz1xxD hz2xxD).trans <| by
            have hquadD : Cdiff * (M₁ + M₂) * D ≤ 2 * Cdiff * D := by
              calc
                _ ≤ Cdiff * 2 * D :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hS hCdiff.le) hD0
                _ = _ := by ring
            calc
              Cdiff * D + Cdiff * (M₁ + M₂) * D ≤
                  Cdiff * D + 2 * Cdiff * D := add_le_add (le_refl _) hquadD
              _ = 3 * Cdiff * D := by ring
              _ ≤ C * D := h3diffD
      quadratic_diff_bounds := by
        refine ⟨hz2xD.trans ?_, hz2xxD.trans ?_⟩
        all_goals
          calc
            Cdiff * (M₁ + M₂) * D = Cdiff * ((M₁ + M₂) * D) := by ring
            _ ≤ C * ((M₁ + M₂) * D) := mul_le_mul_of_nonneg_right hC_diff
              (mul_nonneg (add_nonneg hM₁0 hM₂0) hD0)
            _ = C * (M₁ + M₂) * D := by ring }
  have hderiv₁ := (solution_paper3ChemFluxRemainderProfileM_hasDerivAt_routeA
    hsol₁ ht hm heq Hsplit₁ Hlin₁ Hquad₁ hx).deriv
  have hderiv₂ := (solution_paper3ChemFluxRemainderProfileM_hasDerivAt_routeA
    hsol₂ ht hm heq Hsplit₂ Hlin₂ Hquad₂ hx).deriv
  rw [hderiv₁, hderiv₂]
  simpa [HP, EliminatedFluxDerivativePolarizedPointData.lipschitzConstant,
    U, C] using HP.difference_le

#print axioms paper3ChemFluxRemainder_deriv_difference_pointwise

end

end ShenWork.Paper3
