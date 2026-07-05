import ShenWork.PDE.P3MoserGradientContinuityFromDx
import ShenWork.PDE.P3MoserBoundedBeforeProducer
import ShenWork.Paper2.IntervalDomainH1GradientBound

/-!
# 1D H¹ bypass assembly for the interval-domain Moser endpoint

This file assembles the proved one-dimensional H¹ route:

`H1energy` bound → p = 2 pointwise Moser-gradient bound → Agmon L∞ control
→ pointwise Moser-gradient bounds for every `p ≥ 2` → `BoundedBefore`.

The Agmon API needs an Lp input.  Since `H1energy` in the current repository is
the homogeneous seminorm `1/2 ∫ |u_x|²`, it does not itself control the mean.
Accordingly the fully formal endpoint below carries the p = 2 Lp seed explicitly.
-/

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
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

section AxiomAudit

#print axioms intervalDomain_Linf_bound_of_H1bound_and_Lp2
#print axioms intervalDomain_pointwiseGradientBound_general_of_H1bound_and_Lp2
#print axioms intervalDomain_boundedBefore_of_H1bound_logistic_and_Lpseed
#print axioms intervalDomain_boundedBefore_of_H1bound_logistic_and_Lp2

end AxiomAudit

end ShenWork.IntervalDomainExistence.P3Moser1DBypassAssembly

end
