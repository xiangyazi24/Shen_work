/-
  ShenWork/Paper2/IntervalChiNegFinalClose.lean

  FINAL ASSEMBLY for χ₀<0 boundedness via the B-form spectral route.

  This file wires the LANDED pieces:
    * the logistic leg `intervalFullSemigroupOperator_eq_cosineHeatValue_Icc`,
    * the chemotaxis leg `conjugateKernel_eq_heatValue_divMode`,
  into a closed reduction of the per-slice `hsource_bridge` required by the
  forward producer `conjugatePicardLimit_cosineSeries`, EXPOSING the single
  remaining genuine analytic obligation as an explicit, named hypothesis:

    `hDivMode` :  `nπ · intervalSineInner (chemFluxLifted p (u s)) n
                    = coupledChemDivSourceCoeffs p u s n`

  i.e. the divergence-mode integration-by-parts identity
  `nπ · sineₙ(flux) = cosineₙ(∂ₓ flux)` specialised to `∂ₓ(chemFlux)=chemDiv`.

  We show that GIVEN `hDivMode` (and the standard integrability/continuity/
  bound packages) the chemotaxis+logistic legs combine to the B-form value
  identity, so the bridge closes — confirming the rest of leg (ii) is wiring.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file, new names only.
-/
import ShenWork.Paper2.IntervalSourceBridgeTest
import ShenWork.Paper2.IntervalConjugateCosineSeries
import ShenWork.Paper2.IntervalDivergenceModeIdentity
import ShenWork.PDE.IntervalFullKernelSpectralClean
import ShenWork.PDE.IntervalCoupledSourceTimeC1
import ShenWork.PDE.IntervalCoupledDuhamelT6SliceAgreement

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegFinalClose

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.IntervalConjugateCosineSeries (intervalSineInner)
open ShenWork.Paper2.IntervalSourceBridgeTest (conjugateKernel_eq_heatValue_divMode)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs coupledChemDivSourceLift
   chemFluxLifted_endpoint_zero chemFluxLifted_endpoint_one)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs)
open ShenWork.IntervalSemigroupComposition (expEigSummable)
open ShenWork.IntervalFullKernelSpectralClean
  (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc)

/-- The heat-value summand is absolutely summable from a uniform coefficient
bound (the cosine mode is bounded by `1`, the eigenvalue exponentials sum). -/
private theorem heatValue_summand_summable
    {r x M : ℝ} (hr : 0 < r) {a : ℕ → ℝ} (hbound : ∀ n, |a n| ≤ M) :
    Summable (fun n => unitIntervalCosineHeatPointWeight r x n * a n) := by
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hbound 0)
  refine Summable.of_norm_bounded
    (g := fun n => Real.exp (-r * unitIntervalCosineEigenvalue n) * M)
    ((expEigSummable hr).mul_right M) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  unfold unitIntervalCosineHeatPointWeight
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hcos : |unitIntervalCosineMode n x| ≤ 1 := by
    simpa [unitIntervalCosineMode] using Real.abs_cos_le_one ((n : ℝ) * Real.pi * x)
  have hEnn : 0 ≤ Real.exp (-r * unitIntervalCosineEigenvalue n) := (Real.exp_pos _).le
  calc Real.exp (-r * unitIntervalCosineEigenvalue n)
          * |unitIntervalCosineMode n x| * |a n|
      ≤ Real.exp (-r * unitIntervalCosineEigenvalue n) * 1 * M := by
        apply mul_le_mul _ (hbound n) (abs_nonneg _)
          (mul_nonneg hEnn (by norm_num))
        exact mul_le_mul_of_nonneg_left hcos hEnn
    _ = Real.exp (-r * unitIntervalCosineEigenvalue n) * M := by ring

/-- **The per-slice source bridge, reduced to the divergence-mode identity.**

For a fixed slice (with `0 < r`), the χ₀-weighted chemotaxis leg plus the
logistic leg equals the heat value on the B-form coefficient family, provided
the divergence-mode identity `hDivMode` holds for the chemotaxis flux of `u s`
and the continuity/bound inputs are supplied. -/
theorem source_bridge_slice_of_divMode
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {s : ℝ}
    (hchem_cont : Continuous (chemFluxLifted p (u s)))
    (hlog_cont : Continuous (logisticLifted p (u s)))
    {Mlog : ℝ}
    (hlog_bound : ∀ n, |cosineCoeffs (logisticLifted p (u s)) n| ≤ Mlog)
    {Mchem : ℝ}
    (hchem_bound : ∀ n, |coupledChemDivSourceCoeffs p u s n| ≤ Mchem)
    (hDivMode : ∀ n : ℕ,
      ((n : ℝ) * Real.pi) * intervalSineInner (chemFluxLifted p (u s)) n
        = coupledChemDivSourceCoeffs p u s n) :
    (-p.χ₀) * intervalConjugateKernelOperator r (chemFluxLifted p (u s)) x
        + intervalFullSemigroupOperator r (logisticLifted p (u s)) x
      = unitIntervalCosineHeatValue r (bFormSourceCoeffs p u s) x := by
  -- chemotaxis leg → heat value on `nπ · sineInner (chemFlux)`
  rw [conjugateKernel_eq_heatValue_divMode hr hchem_cont x]
  -- logistic leg → heat value on `cosineCoeffs (logisticLifted (u s))`
  rw [intervalFullSemigroupOperator_eq_cosineHeatValue_Icc hr hlog_cont hlog_bound hx]
  -- rewrite the chemotaxis coefficient family by the divergence-mode identity
  unfold unitIntervalCosineHeatValue
  rw [show (fun n => unitIntervalCosineHeatPointWeight r x n *
        (((n : ℝ) * Real.pi) * intervalSineInner (chemFluxLifted p (u s)) n))
      = (fun n => unitIntervalCosineHeatPointWeight r x n *
          coupledChemDivSourceCoeffs p u s n) from
    funext (fun n => by rw [hDivMode n])]
  -- `(-χ₀)·∑ w·chemDiv + ∑ w·logistic = ∑ w·(logistic - χ₀·chemDiv)`
  rw [← tsum_mul_left]
  rw [← Summable.tsum_add
        ((heatValue_summand_summable (M := Mchem) hr hchem_bound).mul_left (-p.χ₀))
        (heatValue_summand_summable (M := Mlog) hr hlog_bound)]
  refine tsum_congr (fun n => ?_)
  show (-p.χ₀) * (unitIntervalCosineHeatPointWeight r x n *
          coupledChemDivSourceCoeffs p u s n)
      + unitIntervalCosineHeatPointWeight r x n *
          cosineCoeffs (logisticLifted p (u s)) n
    = unitIntervalCosineHeatPointWeight r x n * bFormSourceCoeffs p u s n
  -- logisticLifted (u s) ≡ coupledLogisticSourceLift p u s (definitional)
  show (-p.χ₀) * (unitIntervalCosineHeatPointWeight r x n *
          coupledChemDivSourceCoeffs p u s n)
      + unitIntervalCosineHeatPointWeight r x n *
          coupledLogisticSourceCoeffs p u s n
    = unitIntervalCosineHeatPointWeight r x n * bFormSourceCoeffs p u s n
  unfold bFormSourceCoeffs
  ring

/-- `intervalSineInner` (cosine-series file) is definitionally the same formula
as `sineCoeffs` (divergence-mode file). -/
private theorem sineInner_eq_sineCoeffs (g : ℝ → ℝ) (n : ℕ) :
    intervalSineInner g n
      = ShenWork.Paper2.IntervalDivergenceModeIdentity.sineCoeffs g n := by
  unfold intervalSineInner ShenWork.Paper2.IntervalDivergenceModeIdentity.sineCoeffs
  rfl

/-- **The divergence-mode identity, discharged from landed pieces.**

Given the per-slice C¹ data of the chemotaxis flux — `chemFlux p (u s)` has
derivative the chemotaxis divergence `coupledChemDivSourceLift p u s` everywhere
on `[0,1]` (`hderiv`) with that divergence continuous (`hdivcont`) — the
divergence-mode identity holds:

    `nπ · intervalSineInner (chemFlux p (u s)) n = coupledChemDivSourceCoeffs p u s n`.

This is the landed IBP identity `cosineCoeffs_deriv_eq_sqrtLambda_sineCoeff`
(`cosineCoeffs(∂ₓQ) = √λₙ·sineₙ(Q)`, `√λₙ = nπ`) combined with the landed
endpoint-vanishing facts `chemFluxLifted_endpoint_zero/one`.  No new analysis. -/
theorem divMode_of_sliceC1
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s : ℝ}
    (hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (chemFluxLifted p (u s)) (coupledChemDivSourceLift p u s x) x)
    (hdivcont : Continuous (coupledChemDivSourceLift p u s))
    (n : ℕ) :
    ((n : ℝ) * Real.pi) * intervalSineInner (chemFluxLifted p (u s)) n
      = coupledChemDivSourceCoeffs p u s n := by
  have hQ0 : chemFluxLifted p (u s) 0 = 0 := chemFluxLifted_endpoint_zero p (u s)
  have hQ1 : chemFluxLifted p (u s) 1 = 0 := chemFluxLifted_endpoint_one p (u s)
  have hibp :=
    ShenWork.Paper2.IntervalDivergenceModeIdentity.cosineCoeffs_deriv_eq_sqrtLambda_sineCoeff
      (Q := chemFluxLifted p (u s))
      (Q' := coupledChemDivSourceLift p u s) n hderiv hdivcont hQ0 hQ1
  -- `coupledChemDivSourceCoeffs = cosineCoeffs (coupledChemDivSourceLift)` (def),
  -- and `√(lam n) = nπ`.
  rw [coupledChemDivSourceCoeffs, hibp,
    ShenWork.Paper2.IntervalDivergenceModeIdentity.sqrt_lam_eq_kpi,
    sineInner_eq_sineCoeffs]

/-- **The per-slice source bridge from the per-slice C¹ data** (no carried
divergence-mode hypothesis: it is discharged internally by `divMode_of_sliceC1`).
This is the fully landed-pieces form of the chemotaxis+logistic leg of
`hsource_bridge`. -/
theorem source_bridge_slice_of_sliceC1
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {s : ℝ}
    (hchem_cont : Continuous (chemFluxLifted p (u s)))
    (hlog_cont : Continuous (logisticLifted p (u s)))
    {Mlog : ℝ}
    (hlog_bound : ∀ n, |cosineCoeffs (logisticLifted p (u s)) n| ≤ Mlog)
    {Mchem : ℝ}
    (hchem_bound : ∀ n, |coupledChemDivSourceCoeffs p u s n| ≤ Mchem)
    (hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (chemFluxLifted p (u s)) (coupledChemDivSourceLift p u s y) y)
    (hdivcont : Continuous (coupledChemDivSourceLift p u s)) :
    (-p.χ₀) * intervalConjugateKernelOperator r (chemFluxLifted p (u s)) x
        + intervalFullSemigroupOperator r (logisticLifted p (u s)) x
      = unitIntervalCosineHeatValue r (bFormSourceCoeffs p u s) x :=
  source_bridge_slice_of_divMode hr hx hchem_cont hlog_cont hlog_bound hchem_bound
    (divMode_of_sliceC1 hderiv hdivcont)

end ShenWork.Paper2.IntervalChiNegFinalClose
