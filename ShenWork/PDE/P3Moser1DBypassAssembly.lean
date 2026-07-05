import ShenWork.PDE.IntervalDomain1DLinfRoute
import ShenWork.PDE.IntervalDomainAPrioriGlobal
import ShenWork.PDE.P3MoserBoundedBeforeProducer
import ShenWork.Paper2.IntervalDomainH1GradientBound
import ShenWork.Paper2.IntervalDomainMoserClosure
import ShenWork.Paper2.IntervalSingleSolutionL2Window

/-!
# 1D H¹ bypass assembly for the interval-domain Moser endpoint

This file assembles existing 1D ingredients:

* an `L²` seed for the constant mode,
* the H¹-energy producer for the pointwise `p = 2` Moser-gradient frontier,
* the direct 1D Agmon route from `Lp + gradient` to pointwise control.

The `L²` seed is kept explicit.  A bound on the H¹ seminorm alone does not
control the spatial constant mode.
-/

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy (H1energy)
open ShenWork.Paper2.IntervalSingleSolutionL2Window
  (L2energy intervalDomainLpAbsEnergy_two_eq_two_mul_L2energy_of_nonneg)
open ShenWork.Paper2.IntervalDomainH1GradientBound
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.IntervalDomain1DLinfRoute
open ShenWork.IntervalDomainExistence.P3MoserBoundedBeforeProducer
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3Moser1DBypassAssembly

/-- H¹ seminorm bound plus the p = 2 Lp seed gives a uniform pointwise L∞ bound. -/
theorem intervalDomain_Linf_bound_of_H1bound_and_Lp2
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    {Y₁ : ℝ} (hY1 : 0 ≤ Y₁)
    (hH1bnd : ∀ τ, 0 < τ → τ < T → H1energy u τ ≤ Y₁)
    (hLp2 : LpPowerBoundedBefore intervalDomain 2 T u) :
    ∃ Minf : ℝ, 0 ≤ Minf ∧
      ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, u t x ≤ Minf := by
  have hgrad2 :
      IntervalDomainPointwiseMoserGradientBoundBefore u T 2 :=
    produce_pointwiseGradientBound_of_H1energy_bound hsol hY1 hH1bnd
  rcases intervalDomain_Lp_energy_and_dissipation_of_Lp_and_pointwiseGradient
      (T := T) (pExp := 2) (u := u) hLp2 hgrad2 with
    ⟨M_Lp, M_diss, hMLp, hMdiss, hLp_bound, hgrad_bound⟩
  let C : ℝ := 2 * M_Lp + 2 * Real.sqrt M_Lp * Real.sqrt M_diss
  have hpower :
      ∀ t, 0 < t → t < T →
        ∀ x : intervalDomain.Point, (u t x) ^ (2 : ℝ) ≤ C :=
    intervalDomain_Linf_of_Lp_and_gradient
      (params := params) (T := T) (pExp := 2) (u := u) (v := v)
      hsol (by norm_num) hMLp hMdiss hLp_bound hgrad_bound
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    have hsqrt_prod_nonneg :
        0 ≤ Real.sqrt M_Lp * Real.sqrt M_diss :=
      mul_nonneg (Real.sqrt_nonneg M_Lp) (Real.sqrt_nonneg M_diss)
    nlinarith [hMLp, hsqrt_prod_nonneg]
  let Minf : ℝ := C ^ (2 : ℝ)⁻¹
  have hMinf : 0 ≤ Minf := by
    dsimp [Minf]
    exact Real.rpow_nonneg hC_nonneg _
  have hMinf_pow : Minf ^ (2 : ℝ) = C := by
    dsimp [Minf]
    exact Real.rpow_inv_rpow hC_nonneg (by norm_num : (2 : ℝ) ≠ 0)
  refine ⟨Minf, hMinf, ?_⟩
  intro t ht0 htT x
  have hu_nonneg : 0 ≤ u t x := (hsol.u_pos' ht0 htT (x := x)).le
  have hpow : (u t x) ^ (2 : ℝ) ≤ Minf ^ (2 : ℝ) := by
    rw [hMinf_pow]
    exact hpower t ht0 htT x
  exact
    (Real.rpow_le_rpow_iff hu_nonneg hMinf (by norm_num : (0 : ℝ) < 2)).mp hpow

/-- H¹ seminorm bound plus p = 2 Lp seed gives pointwise Moser-gradient bounds
at every exponent `p ≥ 2`. -/
theorem intervalDomain_pointwiseGradientBound_general_of_H1bound_and_Lp2
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    {Y₁ : ℝ} (hY1 : 0 ≤ Y₁)
    (hH1bnd : ∀ τ, 0 < τ → τ < T → H1energy u τ ≤ Y₁)
    (hLp2 : LpPowerBoundedBefore intervalDomain 2 T u) :
    ∀ pExp, 2 ≤ pExp →
      IntervalDomainPointwiseMoserGradientBoundBefore u T pExp := by
  rcases intervalDomain_Linf_bound_of_H1bound_and_Lp2
      hsol hY1 hH1bnd hLp2 with
    ⟨Minf, hMinf, hLinf⟩
  intro pExp hpExp2
  exact
    produce_pointwiseGradientBound_general_pExp
      hsol hY1 hH1bnd hMinf hLinf pExp hpExp2

/-- Local Proposition 2.5 endpoint: if the available Lp seed exponent is at
least `2`, the H¹ bypass supplies the gradient bound at that exponent and the
1D Agmon terminal estimate closes `BoundedBefore`. -/
theorem intervalDomain_boundedBefore_of_H1bound_logistic_and_Lpseed
    {params : CM2Params} {T pSeed : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (_hlogistic_dominates : 2 * params.γ < params.α)
    {Y₁ : ℝ} (hY1 : 0 ≤ Y₁)
    (hH1bnd : ∀ τ, 0 < τ → τ < T → H1energy u τ ≤ Y₁)
    (hpSeed2 : 2 ≤ pSeed)
    (hLpSeed : LpPowerBoundedBefore intervalDomain pSeed T u) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hLp2 : LpPowerBoundedBefore intervalDomain 2 T u :=
    intervalDomain_LpPowerBoundedBefore_mono_of_classical hsol
      (p := 2) (q := pSeed) (by norm_num) hpSeed2 hLpSeed
  rcases intervalDomain_Linf_bound_of_H1bound_and_Lp2
      hsol hY1 hH1bnd hLp2 with
    ⟨Minf, hMinf, hLinf⟩
  have hpoint : IntervalDomainMoserPointwisePowerControlBefore u T 2 Minf := by
    intro t ht0 htT x
    have hu_pos : 0 < u t x := hsol.u_pos' ht0 htT (x := x)
    have hu_le : u t x ≤ Minf := hLinf t ht0 htT x
    simpa [abs_of_pos hu_pos] using
      Real.rpow_le_rpow hu_pos.le hu_le (by norm_num : (0 : ℝ) ≤ 2)
  exact intervalDomain_boundedBefore_of_pointwise_power_control
    (u := u) (T := T) (pExp := 2) (R := Minf)
    (by norm_num) hMinf hpoint

/-- The most commonly useful p = 2-seed corollary of the 1D bypass. -/
theorem intervalDomain_boundedBefore_of_H1bound_logistic_and_Lp2
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hlogistic_dominates : 2 * params.γ < params.α)
    {Y₁ : ℝ} (hY1 : 0 ≤ Y₁)
    (hH1bnd : ∀ τ, 0 < τ → τ < T → H1energy u τ ≤ Y₁)
    (hLp2 : LpPowerBoundedBefore intervalDomain 2 T u) :
    IsPaper2BoundedBefore intervalDomain T u :=
  intervalDomain_boundedBefore_of_H1bound_logistic_and_Lpseed
    hsol hlogistic_dominates hY1 hH1bnd (pSeed := 2) (by norm_num) hLp2

/-- On the concrete interval domain, an `L²` seed plus a uniform H¹-energy bound
produce the paper's bounded-before conclusion via the already proved 1D Agmon
route. -/
theorem intervalDomain_boundedBefore_of_Lp2_and_H1bound
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    {Y₁ : ℝ} (hY1 : 0 ≤ Y₁)
    (hH1bnd : ∀ τ, 0 < τ → τ < T → H1energy u τ ≤ Y₁)
    (hLp2 : LpPowerBoundedBefore intervalDomain 2 T u) :
    IsPaper2BoundedBefore intervalDomain T u := by
  rcases intervalDomain_Linf_bound_of_H1bound_and_Lp2
      hsol hY1 hH1bnd hLp2 with
    ⟨Minf, hMinf, hLinf⟩
  have hpoint_power :
      ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point,
        |u t x| ^ (2 : ℝ) ≤ Minf ^ (2 : ℝ) := by
    intro t ht0 htT x
    have hpos : 0 < u t x := hsol.u_pos' ht0 htT
    have hle : u t x ≤ Minf := hLinf t ht0 htT x
    simpa [abs_of_pos hpos] using
      Real.rpow_le_rpow hpos.le hle (by norm_num : (0 : ℝ) ≤ 2)
  exact intervalDomain_boundedBefore_of_pointwise_power_control
    (u := u) (T := T) (pExp := 2) (R := Minf)
    (by norm_num : (0 : ℝ) < 2) hMinf hpoint_power

/-- Same terminal reducer, named with the lower-order seed as an `L²` bound.

This is the preferred interface name for downstream wiring: logistic estimates
belong upstream where the `L²` seed is produced. -/
theorem intervalDomain_boundedBefore_of_L2bound_and_H1bound
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    {Y₁ : ℝ} (hY1 : 0 ≤ Y₁)
    (hH1bnd : ∀ τ, 0 < τ → τ < T → H1energy u τ ≤ Y₁)
    (hLp2 : LpPowerBoundedBefore intervalDomain 2 T u) :
    IsPaper2BoundedBefore intervalDomain T u :=
  intervalDomain_boundedBefore_of_Lp2_and_H1bound hsol hY1 hH1bnd hLp2

/-- Compatibility wrapper for task statements that mention logistic dominance.

The logistic hypothesis is not used by the terminal Sobolev/Agmon step; it is
kept here only as provenance for future upstream `L²`-seed producers. -/
theorem intervalDomain_boundedBefore_of_H1bound_and_L2seed_logistic
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (_hlogistic : 2 * params.γ < params.α)
    {Y₁ : ℝ} (hY1 : 0 ≤ Y₁)
    (hH1bnd : ∀ τ, 0 < τ → τ < T → H1energy u τ ≤ Y₁)
    (hLp2 : LpPowerBoundedBefore intervalDomain 2 T u) :
    IsPaper2BoundedBefore intervalDomain T u :=
  intervalDomain_boundedBefore_of_L2bound_and_H1bound hsol hY1 hH1bnd hLp2

/-- Extract the half-energy bound required by the H¹ sliding-window theorem
from the repository's `p = 2` Lp seed. -/
theorem intervalDomain_L2energy_bound_of_Lp2
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hLp2 : LpPowerBoundedBefore intervalDomain 2 T u) :
    ∃ Y_L2 : ℝ, ∀ τ, 0 < τ → τ < T → L2energy u τ ≤ Y_L2 := by
  rcases hLp2 with ⟨C, hC⟩
  refine ⟨max 0 (C / 2), ?_⟩
  intro τ hτ0 hτT
  have hnonneg : ∀ x : intervalDomain.Point, 0 ≤ u τ x :=
    fun x => le_of_lt (hsol.u_pos' hτ0 hτT)
  have hLp_abs :
      ShenWork.Paper2.IntervalDomainLpMonotonicity.intervalDomainLpAbsEnergy
          2 u τ ≤ C := by
    have hfun :
        (fun x : intervalDomain.Point => (u τ x) ^ (2 : ℝ)) =
          fun x : intervalDomain.Point => |u τ x| ^ (2 : ℝ) := by
      funext x
      rw [abs_of_nonneg (hnonneg x)]
    have henergy_eq :
        intervalDomain.integral
            (fun x : intervalDomain.Point => (u τ x) ^ (2 : ℝ)) =
          ShenWork.Paper2.IntervalDomainLpMonotonicity.intervalDomainLpAbsEnergy
            2 u τ := by
      rw [hfun]
      rfl
    rw [← henergy_eq]
    exact hC τ hτ0 hτT
  have htwice :
      ShenWork.Paper2.IntervalDomainLpMonotonicity.intervalDomainLpAbsEnergy
          2 u τ = 2 * L2energy u τ :=
    intervalDomainLpAbsEnergy_two_eq_two_mul_L2energy_of_nonneg u τ hnonneg
  have hhalf : L2energy u τ ≤ C / 2 := by
    nlinarith
  exact le_trans hhalf (le_max_right 0 (C / 2))

/-- Upstream variant using the existing integrated absorbing L² seed producer. -/
theorem intervalDomain_boundedBefore_of_absorbingIntegratedL2_and_H1bound
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    {Y₁ : ℝ} (hY1 : 0 ≤ Y₁)
    (hH1bnd : ∀ τ, 0 < τ → τ < T → H1energy u τ ≤ Y₁)
    (habsorbing :
      IntervalDomainL2AbsorbingIntegratedInequalityResult params T u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hLp2 : LpPowerBoundedBefore intervalDomain 2 T u :=
    intervalDomainL2PowerBoundedBefore_of_absorbingIntegratedInequality
      hsol habsorbing hfrontier
  exact intervalDomain_boundedBefore_of_L2bound_and_H1bound hsol hY1 hH1bnd hLp2

/-- Upstream variant using the older differential absorbing L² seed producer. -/
theorem intervalDomain_boundedBefore_of_absorbingDifferentialL2_and_H1bound
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    {Y₁ : ℝ} (hY1 : 0 ≤ Y₁)
    (hH1bnd : ∀ τ, 0 < τ → τ < T → H1energy u τ ≤ Y₁)
    (habsorbing :
      IntervalDomainL2AbsorbingDifferentialInequalityResult params T u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hLp2 : LpPowerBoundedBefore intervalDomain 2 T u :=
    intervalDomainL2PowerBoundedBefore_of_absorbingDifferentialInequality
      hsol habsorbing hfrontier
  exact intervalDomain_boundedBefore_of_L2bound_and_H1bound hsol hY1 hH1bnd hLp2

/-- Integrated L² seed plus the existing H¹ window/local/average package. -/
theorem intervalDomain_boundedBefore_of_absorbingIntegratedL2_and_H1window
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    {A B C Ylocal : ℝ} (hA : 0 ≤ A) {W : ℝ → ℝ}
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → H1energy u τ ≤ Ylocal)
    (havg :
      ∀ τ, 1 ≤ τ →
        1 * H1energy u τ ≤ W τ + 1 * (A * W τ + B * 1))
    (hwin : ∀ τ, 1 ≤ τ → W τ ≤ C)
    (hWnn : ∀ τ, 1 ≤ τ → 0 ≤ W τ)
    (habsorbing :
      IntervalDomainL2AbsorbingIntegratedInequalityResult params T u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u) :
    IsPaper2BoundedBefore intervalDomain T u := by
  let Y₁ : ℝ := max Ylocal ((1 + A) * C + B)
  have hYlocal_nonneg : 0 ≤ Ylocal :=
    le_trans (ShenWork.Paper2.IntervalChiNegH1Energy.H1energy_nonneg u 1)
      (hlocal 1 ⟨one_pos, le_rfl⟩)
  have hY1 : 0 ≤ Y₁ := le_max_of_le_left hYlocal_nonneg
  have hH1bnd :
      ∀ τ, 0 < τ → τ < T → H1energy u τ ≤ Y₁ := by
    intro τ hτ0 _hτT
    exact ShenWork.Paper2.IntervalChiNegH1Energy.chiNeg_H1_norm_bound
      hsol hA hlocal havg hwin hWnn τ hτ0
  exact intervalDomain_boundedBefore_of_absorbingIntegratedL2_and_H1bound
    hsol hY1 hH1bnd habsorbing hfrontier

/-- Differential L² seed plus the existing H¹ window/local/average package. -/
theorem intervalDomain_boundedBefore_of_absorbingDifferentialL2_and_H1window
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    {A B C Ylocal : ℝ} (hA : 0 ≤ A) {W : ℝ → ℝ}
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → H1energy u τ ≤ Ylocal)
    (havg :
      ∀ τ, 1 ≤ τ →
        1 * H1energy u τ ≤ W τ + 1 * (A * W τ + B * 1))
    (hwin : ∀ τ, 1 ≤ τ → W τ ≤ C)
    (hWnn : ∀ τ, 1 ≤ τ → 0 ≤ W τ)
    (habsorbing :
      IntervalDomainL2AbsorbingDifferentialInequalityResult params T u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u) :
    IsPaper2BoundedBefore intervalDomain T u := by
  let Y₁ : ℝ := max Ylocal ((1 + A) * C + B)
  have hYlocal_nonneg : 0 ≤ Ylocal :=
    le_trans (ShenWork.Paper2.IntervalChiNegH1Energy.H1energy_nonneg u 1)
      (hlocal 1 ⟨one_pos, le_rfl⟩)
  have hY1 : 0 ≤ Y₁ := le_max_of_le_left hYlocal_nonneg
  have hH1bnd :
      ∀ τ, 0 < τ → τ < T → H1energy u τ ≤ Y₁ := by
    intro τ hτ0 _hτT
    exact ShenWork.Paper2.IntervalChiNegH1Energy.chiNeg_H1_norm_bound
      hsol hA hlocal havg hwin hWnn τ hτ0
  exact intervalDomain_boundedBefore_of_absorbingDifferentialL2_and_H1bound
    hsol hY1 hH1bnd habsorbing hfrontier

/-- Differential L² seed plus a carried L²-energy bound and the local/average
H¹ package.

Compared with `intervalDomain_boundedBefore_of_absorbingDifferentialL2_and_H1window`,
this discharges the explicit sliding-window hypotheses by using the existing
single-solution H¹ window theorem.  The local start and averaged H¹ differential
inequality are still explicit because they belong to the separate H¹ identity
frontier. -/
theorem intervalDomain_boundedBefore_of_absorbingDifferentialL2_H1local_average_L2energy
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (habsorbing :
      IntervalDomainL2AbsorbingDifferentialInequalityResult params T u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {Y_L2 : ℝ}
    (hL2 : ∀ τ, 0 < τ → τ < T →
      ShenWork.Paper2.IntervalSingleSolutionL2Window.L2energy u τ ≤ Y_L2)
    {A B Ylocal : ℝ} (hA : 0 ≤ A)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → H1energy u τ ≤ Ylocal)
    (havg : ∀ τ, 1 ≤ τ → τ < T →
      1 * H1energy u τ ≤
        (∫ s in (τ - 1)..τ, H1energy u s) +
          1 * (A * (∫ s in (τ - 1)..τ, H1energy u s) + B * 1)) :
    IsPaper2BoundedBefore intervalDomain T u := by
  rcases
      ShenWork.Paper2.IntervalSingleSolutionL2Window.singleSolution_H1_window_bound
        hsol habsorbing hfrontier hL2 with
    ⟨C, _hC_nonneg, hwinC⟩
  let Y₁ : ℝ := max Ylocal ((1 + A) * C + B)
  have hYlocal_nonneg : 0 ≤ Ylocal :=
    le_trans (ShenWork.Paper2.IntervalChiNegH1Energy.H1energy_nonneg u 1)
      (hlocal 1 ⟨one_pos, le_rfl⟩)
  have hY1 : 0 ≤ Y₁ := le_max_of_le_left hYlocal_nonneg
  have hH1bnd :
      ∀ τ, 0 < τ → τ < T → H1energy u τ ≤ Y₁ := by
    intro τ hτ0 hτT
    rcases le_or_gt τ 1 with hτ_le_one | hτ_gt_one
    · exact le_trans (hlocal τ ⟨hτ0, hτ_le_one⟩) (le_max_left _ _)
    · have hτ_one : 1 ≤ τ := le_of_lt hτ_gt_one
      have hWnn :
          0 ≤ ∫ s in (τ - 1)..τ, H1energy u s :=
        intervalIntegral.integral_nonneg (by linarith)
          (fun s _hs =>
            ShenWork.Paper2.IntervalChiNegH1Energy.H1energy_nonneg u s)
      have hbound := ShenWork.Paper2.IntervalChiNegH1Energy.uniform_bound_of_window_le
        (ytR := H1energy u τ)
        (W := ∫ s in (τ - 1)..τ, H1energy u s)
        (A := A) (B := B) (R := 1) (C := C)
        one_pos hA hWnn (hwinC τ hτ_one hτT) (havg τ hτ_one hτT)
      have hsimp : C / 1 + A * C + B * 1 = (1 + A) * C + B := by
        ring
      rw [hsimp] at hbound
      exact le_trans hbound (le_max_right _ _)
  exact intervalDomain_boundedBefore_of_absorbingDifferentialL2_and_H1bound
    hsol hY1 hH1bnd habsorbing hfrontier

/-- Differential L² seed plus the local/average H¹ package.

This removes the carried L²-energy bound from
`intervalDomain_boundedBefore_of_absorbingDifferentialL2_H1local_average_L2energy`:
the same absorbing L² inequality and seed frontier already produce the `p = 2`
Lp seed, hence the half-energy bound consumed by the sliding-window theorem. -/
theorem intervalDomain_boundedBefore_of_absorbingDifferentialL2_H1local_average
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (habsorbing :
      IntervalDomainL2AbsorbingDifferentialInequalityResult params T u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {A B Ylocal : ℝ} (hA : 0 ≤ A)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → H1energy u τ ≤ Ylocal)
    (havg : ∀ τ, 1 ≤ τ → τ < T →
      1 * H1energy u τ ≤
        (∫ s in (τ - 1)..τ, H1energy u s) +
          1 * (A * (∫ s in (τ - 1)..τ, H1energy u s) + B * 1)) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hLp2 : LpPowerBoundedBefore intervalDomain 2 T u :=
    intervalDomainL2PowerBoundedBefore_of_absorbingDifferentialInequality
      hsol habsorbing hfrontier
  rcases intervalDomain_L2energy_bound_of_Lp2 hsol hLp2 with
    ⟨Y_L2, hL2⟩
  exact intervalDomain_boundedBefore_of_absorbingDifferentialL2_H1local_average_L2energy
    hsol habsorbing hfrontier hL2 hA hlocal havg

/-- Produce the closed absorbing L² differential inequality from the existing
mass bound and interval-domain energy infrastructure. -/
theorem intervalDomain_absorbingDifferentialL2_of_mass
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hmass : IntervalDomainLogisticMassBound params T u) :
    IntervalDomainL2AbsorbingDifferentialInequalityResult params T u := by
  have hspatial :
      IntervalDomainL2SpatialAbsorptionEstimate params T u v hsol hmass :=
    intervalDomainL2SpatialAbsorptionEstimate_of_classical hbounded hsol hmass
  have henergy :
      IntervalDomainL2HalfEnergyDifferentialInequalityUniformCeps
        params T u v :=
    intervalDomainL2HalfEnergyDifferentialInequalityUniformCeps_of_classicalSolution
      hsol
  exact IntervalDomainL2AbsorbingDifferentialInequality
    hbounded.1 hsol hmass hspatial henergy

/-- Mass-level P3 bypass input theorem.

The remaining carried inputs are now the L² seed regularity frontier and the
local/averaged H¹ package.  The closed absorbing L² differential inequality,
the `p = 2` Lp seed, and the H¹ sliding-window bound are all produced inside. -/
theorem intervalDomain_boundedBefore_of_mass_H1local_average
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hmass : IntervalDomainLogisticMassBound params T u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {A B Ylocal : ℝ} (hA : 0 ≤ A)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → H1energy u τ ≤ Ylocal)
    (havg : ∀ τ, 1 ≤ τ → τ < T →
      1 * H1energy u τ ≤
        (∫ s in (τ - 1)..τ, H1energy u s) +
          1 * (A * (∫ s in (τ - 1)..τ, H1energy u s) + B * 1)) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have habsorbing :
      IntervalDomainL2AbsorbingDifferentialInequalityResult params T u :=
    intervalDomain_absorbingDifferentialL2_of_mass hbounded hsol hmass
  exact intervalDomain_boundedBefore_of_absorbingDifferentialL2_H1local_average
    hsol habsorbing hfrontier hA hlocal havg

/-- Paper-positive datum wrapper for the mass-level P3 bypass theorem.

This uses the proved interval-domain mass comparison theorem to supply the
mass bound from the initial trace.  The genuine remaining inputs are still the
L² seed regularity frontier and the local/averaged H¹ package, plus the
explicit boundedness hypotheses needed by the L² absorption route. -/
theorem intervalDomain_boundedBefore_of_paperPositive_H1local_average
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {A B Ylocal : ℝ} (hA : 0 ≤ A)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → H1energy u τ ≤ Ylocal)
    (havg : ∀ τ, 1 ≤ τ → τ < T →
      1 * H1energy u τ ≤
        (∫ s in (τ - 1)..τ, H1energy u s) +
          1 * (A * (∫ s in (τ - 1)..τ, H1energy u s) + B * 1)) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hmass : IntervalDomainLogisticMassBound params T u :=
    intervalDomainLogisticMassBound_of_proposition24
      (ShenWork.Paper2.intervalDomain_Proposition_2_4 params)
      ha hbounded.2.1 hu₀.toPositive hT hsol htrace
  exact intervalDomain_boundedBefore_of_mass_H1local_average
    hbounded hsol hmass hfrontier hA hlocal havg

#print axioms intervalDomain_boundedBefore_of_Lp2_and_H1bound
#print axioms intervalDomain_boundedBefore_of_L2bound_and_H1bound
#print axioms intervalDomain_boundedBefore_of_H1bound_and_L2seed_logistic
#print axioms intervalDomain_Linf_bound_of_H1bound_and_Lp2
#print axioms intervalDomain_pointwiseGradientBound_general_of_H1bound_and_Lp2
#print axioms intervalDomain_boundedBefore_of_H1bound_logistic_and_Lpseed
#print axioms intervalDomain_boundedBefore_of_H1bound_logistic_and_Lp2
#print axioms intervalDomain_L2energy_bound_of_Lp2
#print axioms intervalDomain_boundedBefore_of_absorbingIntegratedL2_and_H1bound
#print axioms intervalDomain_boundedBefore_of_absorbingDifferentialL2_and_H1bound
#print axioms intervalDomain_boundedBefore_of_absorbingIntegratedL2_and_H1window
#print axioms intervalDomain_boundedBefore_of_absorbingDifferentialL2_and_H1window
#print axioms intervalDomain_boundedBefore_of_absorbingDifferentialL2_H1local_average_L2energy
#print axioms intervalDomain_boundedBefore_of_absorbingDifferentialL2_H1local_average
#print axioms intervalDomain_absorbingDifferentialL2_of_mass
#print axioms intervalDomain_boundedBefore_of_mass_H1local_average
#print axioms intervalDomain_boundedBefore_of_paperPositive_H1local_average

end ShenWork.IntervalDomainExistence.P3Moser1DBypassAssembly
