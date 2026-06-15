/-
  χ₀<0 source-coefficient cosine inversion (EWA Route-A′).

  The two cosine-inversion lemmas for the coupled source coefficient families,
  mirroring the committed χ₀=0 template
  `ShenWork.IntervalDomainPdeUChiZero.source_inversion_eq_reaction_surrogate`.
  Each reduces to the SAME analytic primitive used there,
  `ShenWork.IntervalCosineInversion.intervalCosine_hasSum_pointwise`, fed through a
  CONTINUOUS surrogate `g` agreeing on `[0,1]` with the (2nd-order, not continuous
  as written) source lift, with the `ℓ¹` Fourier summability of `reflCircle g`
  carried as a hypothesis — the honest move the χ₀=0 template also makes.

  * LOGISTIC: cosine series of `coupledLogisticSourceCoeffs` sums, at an interior
    point, to the physical logistic reaction `u t x · (a − b·u t xᵅ)`.
  * CHEMDIV: cosine series of `coupledChemDivSourceCoeffs` sums, at an interior
    point, to the physical chemotaxis divergence
    `intervalDomainChemotaxisDiv p (u t) (coupledChemicalConcentration p u t) x`.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.Wiener.EWA.SourceStrongSolution
import ShenWork.Paper2.IntervalDomainPdeUChiZero
import ShenWork.PDE.IntervalCoupledSourceTimeC1

open Set MeasureTheory
open ShenWork.IntervalDomain
  (intervalDomainPoint intervalDomainLift intervalDomainChemotaxisDiv)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalCosineInversion (intervalCosine_hasSum_pointwise reflCircle)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledLogisticSourceLift coupledLogisticSourceCoeffs
   coupledChemDivSourceLift coupledChemDivSourceCoeffs
   coupledChemicalConcentration)

noncomputable section

namespace ShenWork.EWA

/-- **Cosine coefficients depend only on `[0,1]` values.**  `cosineCoeffs f n` is the
real cosine integral `∫₀¹ cos(nπx) f(x) dx` (normalised), so functions agreeing on
`Icc 0 1` have identical cosine coefficients.  This is what lets the continuous
surrogate `g` (agreeing with the source lift on `[0,1]`) carry the lift's coefficients. -/
theorem cosineCoeffs_congr_on_Icc {f g : ℝ → ℝ}
    (heq : Set.EqOn f g (Set.Icc (0 : ℝ) 1)) (n : ℕ) :
    cosineCoeffs f n = cosineCoeffs g n := by
  have hraw : ∀ m : ℕ,
      ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff
          (fun x => (f x : ℂ)) m
        = ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff
          (fun x => (g x : ℂ)) m := by
    intro m
    simp only [ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
      rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rw [heq hxIcc]
  simp only [cosineCoeffs,
    ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff, hraw]

/-- **Logistic source inversion (χ₀<0).**  The cosine series of the coupled
logistic source coefficients sums, at an interior point `x ∈ (0,1)`, to the
genuine physical logistic reaction `u t x · (a − b · (u t x)ᵅ)`.

Proved from a continuous surrogate `g` agreeing on `[0,1]` with the logistic
source lift `coupledLogisticSourceLift p u t`, via the committed primitive
`intervalCosine_hasSum_pointwise`: it gives `∑ₙ cosineCoeffs g n · cos = g x`,
and the `[0,1]` agreement (interior `x ∈ (0,1) ⊂ [0,1]`) rewrites `g x` into the
lift's logistic value, which at the interior `x` (via the `dif_pos` branch of
`intervalDomainLift`) is the physical reaction. -/
theorem logistic_source_inversion (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ)
    (g : ℝ → ℝ) (hcont : Continuous g)
    (hgeq : Set.EqOn g (coupledLogisticSourceLift p u t) (Set.Icc 0 1))
    (hsum : Summable (fun n : ℤ => fourierCoeff (reflCircle g) n))
    {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0 : ℝ) 1) :
    (∑' n, coupledLogisticSourceCoeffs p u t n * cosineMode n x.1)
      = u t x * (p.a - p.b * (u t x) ^ p.α) := by
  have hinv := intervalCosine_hasSum_pointwise g hcont hx hsum
  have hgx : g x.1 = coupledLogisticSourceLift p u t x.1 :=
    hgeq (Set.Ioo_subset_Icc_self hx)
  -- the coupled logistic coefficients ARE `cosineCoeffs g` (surrogate agrees, so
  -- the cosine coefficients of the lift equal those of `g` on `[0,1]`)
  have hsum_eq : (∑' n, coupledLogisticSourceCoeffs p u t n * cosineMode n x.1)
      = g x.1 := by
    rw [← hinv.tsum_eq]
    refine tsum_congr (fun n => ?_)
    rw [coupledLogisticSourceCoeffs, cosineCoeffs_congr_on_Icc hgeq.symm n]
    simp only [cosineMode, unitIntervalCosineMode]
    ring
  rw [hsum_eq, hgx, coupledLogisticSourceLift]
  have hlift : intervalDomainLift (intervalLogisticSource p (u t)) x.1
      = intervalLogisticSource p (u t) x := by
    simp only [intervalDomainLift]; exact dif_pos x.2
  rw [hlift, intervalLogisticSource]

/-- **Chemotaxis-divergence source inversion (χ₀<0).**  The cosine series of the
coupled chemotaxis-divergence source coefficients sums, at an interior point
`x ∈ (0,1)`, to the genuine physical chemotaxis divergence
`intervalDomainChemotaxisDiv p (u t) (coupledChemicalConcentration p u t) x`.

Same surrogate route: `intervalCosine_hasSum_pointwise` for the continuous `g`
agreeing on `[0,1]` with `coupledChemDivSourceLift p u t` gives
`∑ₙ cosineCoeffs g n · cos = g x`; the `[0,1]` agreement turns `g x` into the
chem-div lift value, and at the interior `x` the lift (`dif_pos` branch) returns
the physical chemotaxis divergence. -/
theorem chemDiv_source_inversion (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ)
    (g : ℝ → ℝ) (hcont : Continuous g)
    (hgeq : Set.EqOn g (coupledChemDivSourceLift p u t) (Set.Icc 0 1))
    (hsum : Summable (fun n : ℤ => fourierCoeff (reflCircle g) n))
    {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0 : ℝ) 1) :
    (∑' n, coupledChemDivSourceCoeffs p u t n * cosineMode n x.1)
      = intervalDomainChemotaxisDiv p (u t) (coupledChemicalConcentration p u t) x := by
  have hinv := intervalCosine_hasSum_pointwise g hcont hx hsum
  have hgx : g x.1 = coupledChemDivSourceLift p u t x.1 :=
    hgeq (Set.Ioo_subset_Icc_self hx)
  have hsum_eq : (∑' n, coupledChemDivSourceCoeffs p u t n * cosineMode n x.1)
      = g x.1 := by
    rw [← hinv.tsum_eq]
    refine tsum_congr (fun n => ?_)
    rw [coupledChemDivSourceCoeffs, cosineCoeffs_congr_on_Icc hgeq.symm n]
    simp only [cosineMode, unitIntervalCosineMode]
    ring
  rw [hsum_eq, hgx, coupledChemDivSourceLift]
  have hlift : intervalDomainLift
      (fun y => intervalDomainChemotaxisDiv p (u t)
        (coupledChemicalConcentration p u t) y) x.1
      = intervalDomainChemotaxisDiv p (u t) (coupledChemicalConcentration p u t) x := by
    simp only [intervalDomainLift]; exact dif_pos x.2
  exact hlift

end ShenWork.EWA
