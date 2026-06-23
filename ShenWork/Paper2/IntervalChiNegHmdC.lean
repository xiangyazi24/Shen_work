/-
# χ₀<0 — hmd source-regularity + C per-σ CarrySeam (landed dischargers)

This file discharges, from LANDED lemmas (two prior grep-misses corrected), the
analytic residuals the χ₀<0 capstone (`IntervalChiNegClose.chiNeg_H1_closed`)
carries for `hmd` and `C`, and records the precise `∀σ` formulation verdict for
the `C` slot.

GREP-MISS CORRECTIONS (verified by reading signatures):
  (1) `carrySeam_hvnn` (IntervalChiNegMemHSigmaOne:249) IS landed — `hvnn` is NOT
      an open obligation; it follows from per-slice continuity + nonnegativity of
      the conjugate solution.
  (2) the source regularity (slice continuity / nonnegativity feeding the legs)
      follows from the LANDED `ConjugateMildSolutionData` fields
      `hcont`/`hnonneg`/`hpos` (built via `conjugatePicardLimit_hasContinuousSlices`
      + `_bounded` + `_nonneg`).

Two-way audit: each field is DISCHARGED by a landed lemma whose hypotheses are
supplied here, or CARRIED with the precise missing lemma (see header notes by the
carried definitions).  No sorry/admit/native_decide/custom axiom.
-/
import ShenWork.Paper2.IntervalChiNegClose
import ShenWork.Paper2.IntervalCarrySeamGradientContinuousOn
import ShenWork.Paper2.IntervalChiNegMemHSigmaOne
import ShenWork.Paper2.IntervalDecompTauLift
import ShenWork.Paper2.IntervalBootstrapInputs
import ShenWork.Paper2.IntervalGradientCoeffDuhamel
import ShenWork.Paper2.IntervalMildPicardThreshold

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegHmdC

open Set MeasureTheory
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (ConjugateMildSolutionData)
open ShenWork.IntervalMildPicard (HasContinuousSlices)
open ShenWork.Paper2 (PaperPositiveInitialDatum)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma)
open ShenWork.Paper2.IntervalDenomEnvelopeResolver (resolverValue)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalDecompTauLift (conjQ conjFl)
open ShenWork.Paper2.IntervalTrajectoryEnvelope (TrajectoryHSigmaEnvelope)
open ShenWork.Paper2.IntervalChiNegSeamFixedReach (CarrySeam)
open ShenWork.Paper2.IntervalChiNegCapstone (conjugateMildData)
open ShenWork.Paper2.IntervalChiNegClose (uTilde uTilde_zero uTilde_pos)
open ShenWork.Paper2.IntervalChiNegMemHSigmaOne (carrySeam_hvnn)
open ShenWork.Paper2.IntervalGradientCoeffDuhamel
  (cosineCoeffs_intervalFullSemigroupOperator_diag)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_abs_le_of_continuous_bounded cosineCoeffs_eq_factor_mul_integral)
open ShenWork.Paper2.IntervalCarrySeamGradientContinuousOn
  (carrySeam_of_mild_gradient_cont continuousOn_intervalDomainLift_of_hasContinuousSlices)

/-! ## 1. Source regularity for `uTilde` — DERIVED from landed mild data. -/

/-- Per-slice continuity of `uTilde` on `[0, D.T]`.  At `τ = 0` it is the
continuous initial datum `u₀`; at `τ > 0` it is the mild slice, continuous by the
landed `D.hcont : HasContinuousSlices` (which packages
`conjugatePicardLimit_hasContinuousSlices`). -/
theorem uTilde_slice_cont (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ∀ τ ∈ Set.Icc (0 : ℝ) (conjugateMildData p hα hγ hu₀).T,
      Continuous (uTilde p hα hγ hu₀ τ) := by
  intro τ hτ
  rcases eq_or_lt_of_le hτ.1 with h0 | h0
  · rw [← h0, uTilde_zero]; exact hu₀.1.2
  · rw [uTilde_pos p hα hγ hu₀ h0]
    exact (conjugateMildData p hα hγ hu₀).hcont τ h0 hτ.2

/-- Per-slice nonnegativity of `uTilde` on `[0, D.T]`.  At `τ = 0` the floor of the
paper-positive datum gives `0 ≤ u₀`; at `τ > 0` it is the landed `D.hnonneg`. -/
theorem uTilde_slice_nonneg (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ∀ τ ∈ Set.Icc (0 : ℝ) (conjugateMildData p hα hγ hu₀).T,
      ∀ z, 0 ≤ uTilde p hα hγ hu₀ τ z := by
  intro τ hτ z
  rcases eq_or_lt_of_le hτ.1 with h0 | h0
  · rw [← h0, uTilde_zero]
    obtain ⟨η, hη, hfl⟩ := hu₀.2
    exact le_trans hη.le (hfl z)
  · rw [uTilde_pos p hα hγ hu₀ h0]
    exact (conjugateMildData p hα hγ hu₀).hnonneg τ h0 hτ.2 z

/-- **`hvnn` DISCHARGED** — the Neumann-resolver positivity field of `CarrySeam`
for `uTilde`, via the LANDED `carrySeam_hvnn` fed by `uTilde_slice_cont` +
`uTilde_slice_nonneg`.  (Correction of grep-miss (1): `hvnn` has a producer.) -/
theorem uTilde_hvnn (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    {μ : ℝ} (hμ : 0 < μ) :
    ∀ τ ∈ Set.Icc (0 : ℝ) (conjugateMildData p hα hγ hu₀).T, ∀ x,
      0 ≤ resolverValue μ (cosineCoeffs (intervalDomainLift (uTilde p hα hγ hu₀ τ))) x :=
  carrySeam_hvnn hμ (uTilde_slice_cont p hα hγ hu₀) (uTilde_slice_nonneg p hα hγ hu₀)

/-- **`hu_cont_on` DISCHARGED** — the `ContinuousOn [0,1]` slice hypothesis of
`carrySeam_of_mild_gradient_cont`, from `uTilde_slice_cont`. -/
theorem uTilde_cont_on (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ∀ τ ∈ Set.Icc (0 : ℝ) (conjugateMildData p hα hγ hu₀).T,
      ContinuousOn (intervalDomainLift (uTilde p hα hγ hu₀ τ)) (Set.Icc 0 1) := by
  intro τ hτ
  have hf : Continuous (uTilde p hα hγ hu₀ τ) := uTilde_slice_cont p hα hγ hu₀ τ hτ
  rw [continuousOn_iff_continuous_restrict]
  have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift (uTilde p hα hγ hu₀ τ))
      = uTilde p hα hγ hu₀ τ := by
    funext y
    simp only [Set.restrict_apply, intervalDomainLift]
    rw [dif_pos y.2]
    exact congr_arg (uTilde p hα hγ hu₀ τ) (Subtype.ext rfl)
  rw [heq]; exact hf

/-! ## 2. The C seam, per in-range sigma — DISCHARGED hvnn/hu_cont_on, carried factorization.

`carrySeam_of_mild_gradient_cont` (IntervalCarrySeamGradientContinuousOn:206) builds
`CarrySeam` for ONE sigma with `1/2 < sigma < 3/2`.  Here `hvnn` (grep-miss (1)) and
`hu_cont_on` (grep-miss (2)) are DISCHARGED from the landed mild data; the
chemotaxis-flux factorization `hQ : conjQ = W*vx`, the resolver definitions
`hvdef`/`hvxdef`, `hWdef`, the flux/logistic source continuities `hQ_cont`/`hFl_cont`,
the logistic envelope `L`, and `hu0hat` remain CARRIED seam data (no landed producer
ties `chemFluxLifted` to the resolver-gradient product `W*vx`; failed grep
`conjQ.*= fun x => W` / `chemFluxLifted.*= .*deriv` ⇒ only HYPOTHESIS occurrences). -/
def chiNeg_carrySeam_perσ (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    {μ β σ : ℝ} {v vx W : ℝ → ℝ → ℝ}
    (E : TrajectoryHSigmaEnvelope σ (conjugateMildData p hα hγ hu₀).T
      (fun τ => cosineCoeffs (intervalDomainLift (uTilde p hα hγ hu₀ τ))))
    (hμ : 0 < μ) (hμ1 : 1 ≤ μ) (hσ0 : 1 / 2 < σ) (hσ1 : σ < 3 / 2)
    (hβ : 0 ≤ β) (hT1 : (conjugateMildData p hα hγ hu₀).T ≤ 1)
    (hû₀ : MemHSigma (σ + 1 / 4)
      (cosineCoeffs (intervalDomainLift (uTilde p hα hγ hu₀ 0))))
    (hQ : ∀ τ, conjQ p (uTilde p hα hγ hu₀) τ = fun x => W τ x * vx τ x)
    (hWdef : ∀ τ, W τ = fun x => intervalDomainLift (uTilde p hα hγ hu₀ τ) x
      * (1 + resolverValue μ
          (cosineCoeffs (intervalDomainLift (uTilde p hα hγ hu₀ τ))) x) ^ (-β))
    (hvdef : ∀ τ, v τ = resolverValue μ
      (cosineCoeffs (intervalDomainLift (uTilde p hα hγ hu₀ τ))))
    (hvxdef : ∀ τ, vx τ = deriv (v τ))
    (hQ_cont : ∀ k, Continuous (fun τ => sineCoeffs (conjQ p (uTilde p hα hγ hu₀) τ) k))
    (L : TrajectoryHSigmaEnvelope σ (conjugateMildData p hα hγ hu₀).T
      (fun τ k => conjFl p (uTilde p hα hγ hu₀) k τ))
    (hFl_cont : ∀ k, Continuous (conjFl p (uTilde p hα hγ hu₀) k)) :
    CarrySeam p μ β (conjugateMildData p hα hγ hu₀).T (uTilde p hα hγ hu₀) v vx W σ E :=
  carrySeam_of_mild_gradient_cont E hμ hμ1 hσ0 hσ1 hβ
    (conjugateMildData p hα hγ hu₀).hT hT1 hû₀
    (uTilde_hvnn p hα hγ hu₀ hμ) hQ hWdef
    (uTilde_cont_on p hα hγ hu₀) hvdef hvxdef hQ_cont L hFl_cont

/-! ## 3. The hmd seam — heat diagonalization DISCHARGED; the two Fubini swaps CARRIED.

`conjugateSlice_decomp_tauLift_pos` (IntervalDecompTauLift:110) assembles `hmd`
GIVEN per-endpoint residuals.  Here we discharge the heat-diagonalization residual
`hpt_heat` for any continuous bounded initial datum, via
`cosineCoeffs_intervalFullSemigroupOperator_diag` (`lam = unitIntervalCosineEigenvalue`
definitionally).  The source continuities/bounds (`hQcont`/`hLcont`/`hLM`) and the
integrated-leg continuities (`hchemI_cont`/`hlogI_cont`) are the landed
`conjugateLeg_continuous_full`/`logisticLeg_continuous_full` route (their source
inputs from the mild-data slice continuity+boundedness — grep-miss (2)).

CARRIED — the two Fubini swaps `hswap_chem`/`hswap_log`.  They are NOT
`cosineCoeffs_integral_swap'` (IntervalBootstrapInputs:107): that swap REQUIRES the
INTEGRAND `(s,x) ↦ S(τ−s)(src s) x` to be `ContinuousOn` the CLOSED slab
`Icc 0 τ ×ˢ Icc 0 1`, but under this repo's `S(0)f = 0` convention
(`intervalFullSemigroupOperator_zero`) the integrand JUMPS at the diagonal `s = τ`
(value `0`, left limit `src τ x ≠ 0`), so it is NOT `ContinuousOn` the closed slab
— exactly `IntervalChiNegUniformClose`'s CARRIED 2.  Off the (Lebesgue-null)
diagonal it IS jointly continuous (`valueOp_src_jointCont`, valid for `τ−s ≥ τ₀>0`)
and bounded (`intervalFullSemigroupOperator_Linfty_bound`).
MISSING lemma (named): `cosineCoeffs_integral_swap_ae` — a Fubini swap tolerating a
Lebesgue-null diagonal discontinuity (product integrability from the L∞ majorant +
a.e.-continuity, via `MeasureTheory.integral_integral_swap`), discharging both swaps
from the off-diagonal joint continuity.  Failed grep:
`integral_swap.*ae` / `swap.*null` / `cosineCoeffs.*swap.*ae` ⇒ NONE. -/

/-- **`hpt_heat` DISCHARGED** — heat diagonalization of the cosine coefficients of
the propagator applied to a continuous, sup-bounded initial datum. -/
theorem hpt_heat_of_cont_bounded {f : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : Continuous f) (hfb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ B)
    {τ : ℝ} (hτ : 0 < τ) (k : ℕ) :
    cosineCoeffs (fun x => intervalFullSemigroupOperator τ f x) k
      = Real.exp (-(τ * lam k)) * cosineCoeffs f k := by
  have hbd : ∀ j, |cosineCoeffs f j| ≤ 2 * B :=
    cosineCoeffs_abs_le_of_continuous_bounded hf.continuousOn hB hfb
  have h := cosineCoeffs_intervalFullSemigroupOperator_diag hτ hf hbd k
  rw [h]
  congr 2
  change -τ * unitIntervalCosineEigenvalue k = -(τ * unitIntervalCosineEigenvalue k)
  ring

/-! ## 4. `cosineCoeffs_integral_swap_ae` — the null-diagonal-tolerant Fubini swap.

The a.e.-Fubini swap the two `hmd` swaps need: it replaces the closed-slab
`ContinuousOn` hypothesis of `cosineCoeffs_integral_swap'` by joint MEASURABILITY +
an L∞ bound (so a Lebesgue-null diagonal discontinuity is tolerated).  Product
integrability comes from boundedness on the finite product measure; the swap from
`MeasureTheory.integral_integral_swap`. -/
theorem cosineCoeffs_integral_swap_ae {t C : ℝ} (ht : 0 ≤ t) (g : ℝ → ℝ → ℝ)
    (hmeas : Measurable (Function.uncurry g))
    (hbnd : ∀ s x, |g s x| ≤ C) (k : ℕ) :
    cosineCoeffs (fun x => ∫ s in (0 : ℝ)..t, g s x) k
      = ∫ s in (0 : ℝ)..t, cosineCoeffs (g s) k := by
  set F : ℝ → ℝ → ℝ := fun s x => Real.cos ((k:ℝ) * Real.pi * x) * g s x with hF
  have hcos : Continuous (fun x : ℝ => Real.cos ((k:ℝ) * Real.pi * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id')
  have hFmeas : Measurable (Function.uncurry F) :=
    (hcos.measurable.comp measurable_snd).mul hmeas
  have hFbnd : ∀ p : ℝ × ℝ, ‖Function.uncurry F p‖ ≤ |C| := by
    intro p
    rw [Real.norm_eq_abs, hF]; simp only [Function.uncurry, abs_mul]
    calc |Real.cos ((k:ℝ) * Real.pi * p.2)| * |g p.1 p.2|
        ≤ 1 * |C| := by
          refine mul_le_mul (Real.abs_cos_le_one _)
            (le_trans (hbnd p.1 p.2) (le_abs_self C)) (abs_nonneg _) (by norm_num)
      _ = |C| := one_mul _
  have hcore : (∫ x in (0 : ℝ)..1,
        Real.cos ((k:ℝ) * Real.pi * x) * (∫ s in (0 : ℝ)..t, g s x))
      = ∫ s in (0 : ℝ)..t, ∫ x in (0 : ℝ)..1,
          Real.cos ((k:ℝ) * Real.pi * x) * g s x := by
    have hint_prod : Integrable (Function.uncurry F)
        ((volume.restrict (Set.Ioc (0 : ℝ) t)).prod
          (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
      haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) t)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
      haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
      refine ⟨hFmeas.aestronglyMeasurable, ?_⟩
      refine (hasFiniteIntegral_const |C|).mono (Filter.Eventually.of_forall ?_)
      intro p; rw [Real.norm_eq_abs (|C|), abs_abs]; exact hFbnd p
    have hswap := MeasureTheory.integral_integral_swap (f := F) hint_prod
    have hLHS : (∫ x in (0 : ℝ)..1,
          Real.cos ((k:ℝ) * Real.pi * x) * (∫ s in (0 : ℝ)..t, g s x))
        = ∫ x, (∫ s, F s x ∂(volume.restrict (Set.Ioc (0 : ℝ) t)))
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro x _; simp only
      rw [intervalIntegral.integral_of_le ht, ← MeasureTheory.integral_const_mul]
    have hRHS : (∫ s in (0 : ℝ)..t, ∫ x in (0 : ℝ)..1,
          Real.cos ((k:ℝ) * Real.pi * x) * g s x)
        = ∫ s, (∫ x, F s x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
            ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) := by
      rw [intervalIntegral.integral_of_le ht]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro s _; simp only
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [hLHS, hRHS, hswap]
  rw [cosineCoeffs_eq_factor_mul_integral, hcore]
  rw [show (∫ s in (0 : ℝ)..t, cosineCoeffs (g s) k)
      = ∫ s in (0 : ℝ)..t, (if k = 0 then (1:ℝ) else 2)
          * ∫ x in (0 : ℝ)..1, Real.cos ((k:ℝ) * Real.pi * x) * g s x from by
    apply intervalIntegral.integral_congr; intro s _; simp only
    rw [cosineCoeffs_eq_factor_mul_integral]]
  rw [intervalIntegral.integral_const_mul]

/-! ## 5. `cosineCoeffs_integral_swap_ae_L1` — null-diagonal swap with an integrable
(time-singular) majorant, for the SINGULAR chemotaxis kernel.

The chemotaxis integrand `(s,x) ↦ S_grad(τ−s)(Q s) x` is NOT L∞-bounded near the
diagonal (`intervalConjugateKernelOperator_abs_le` gives a `(τ−s)^{−1/2}` blow-up),
but that blow-up is INTEGRABLE in `s` (`intervalIntegrable_sub_rpow_neg_half`).  So
the swap holds with a per-time integrable majorant `μs` in place of the L∞ bound:
product integrability via `Integrable.mul_prod` of `μs` (in `s`) and `|cos|` (in
`x`). -/
theorem cosineCoeffs_integral_swap_ae_L1 {t : ℝ} (ht : 0 ≤ t) (g : ℝ → ℝ → ℝ)
    (hmeas : Measurable (Function.uncurry g)) {μs : ℝ → ℝ}
    (hμs_int : IntegrableOn μs (Set.Ioc (0 : ℝ) t) volume)
    (hbnd : ∀ s x, |g s x| ≤ μs s) (k : ℕ) :
    cosineCoeffs (fun x => ∫ s in (0 : ℝ)..t, g s x) k
      = ∫ s in (0 : ℝ)..t, cosineCoeffs (g s) k := by
  set F : ℝ → ℝ → ℝ := fun s x => Real.cos ((k:ℝ) * Real.pi * x) * g s x with hF
  have hcos : Continuous (fun x : ℝ => Real.cos ((k:ℝ) * Real.pi * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id')
  have hFmeas : Measurable (Function.uncurry F) :=
    (hcos.measurable.comp measurable_snd).mul hmeas
  have hμs_nonneg : ∀ s, 0 ≤ μs s := fun s => le_trans (abs_nonneg (g s 0)) (hbnd s 0)
  have hcore : (∫ x in (0 : ℝ)..1,
        Real.cos ((k:ℝ) * Real.pi * x) * (∫ s in (0 : ℝ)..t, g s x))
      = ∫ s in (0 : ℝ)..t, ∫ x in (0 : ℝ)..1,
          Real.cos ((k:ℝ) * Real.pi * x) * g s x := by
    -- integrable majorant `μs(s)·|cos(kπx)|` on the product, via `mul_prod`.
    have hcos_int : IntegrableOn (fun x => |Real.cos ((k:ℝ) * Real.pi * x)|)
        (Set.Ioc (0 : ℝ) 1) volume :=
      (hcos.abs.continuousOn.integrableOn_compact isCompact_Icc).mono_set
        Set.Ioc_subset_Icc_self
    have hmaj : Integrable (fun p : ℝ × ℝ => μs p.1 * |Real.cos ((k:ℝ) * Real.pi * p.2)|)
        ((volume.restrict (Set.Ioc (0 : ℝ) t)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
      Integrable.mul_prod hμs_int hcos_int
    have hint_prod : Integrable (Function.uncurry F)
        ((volume.restrict (Set.Ioc (0 : ℝ) t)).prod
          (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
      refine ⟨hFmeas.aestronglyMeasurable, hmaj.2.mono ?_⟩
      refine Filter.Eventually.of_forall (fun p => ?_)
      rw [Real.norm_eq_abs, hF]; simp only [Function.uncurry, abs_mul]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hμs_nonneg p.1), abs_abs]
      calc |Real.cos ((k:ℝ) * Real.pi * p.2)| * |g p.1 p.2|
          ≤ |Real.cos ((k:ℝ) * Real.pi * p.2)| * μs p.1 :=
            mul_le_mul_of_nonneg_left (hbnd p.1 p.2) (abs_nonneg _)
        _ = μs p.1 * |Real.cos ((k:ℝ) * Real.pi * p.2)| := mul_comm _ _
    have hswap := MeasureTheory.integral_integral_swap (f := F) hint_prod
    have hLHS : (∫ x in (0 : ℝ)..1,
          Real.cos ((k:ℝ) * Real.pi * x) * (∫ s in (0 : ℝ)..t, g s x))
        = ∫ x, (∫ s, F s x ∂(volume.restrict (Set.Ioc (0 : ℝ) t)))
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro x _; simp only
      rw [intervalIntegral.integral_of_le ht, ← MeasureTheory.integral_const_mul]
    have hRHS : (∫ s in (0 : ℝ)..t, ∫ x in (0 : ℝ)..1,
          Real.cos ((k:ℝ) * Real.pi * x) * g s x)
        = ∫ s, (∫ x, F s x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
            ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) := by
      rw [intervalIntegral.integral_of_le ht]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro s _; simp only
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [hLHS, hRHS, hswap]
  rw [cosineCoeffs_eq_factor_mul_integral, hcore]
  rw [show (∫ s in (0 : ℝ)..t, cosineCoeffs (g s) k)
      = ∫ s in (0 : ℝ)..t, (if k = 0 then (1:ℝ) else 2)
          * ∫ x in (0 : ℝ)..1, Real.cos ((k:ℝ) * Real.pi * x) * g s x from by
    apply intervalIntegral.integral_congr; intro s _; simp only
    rw [cosineCoeffs_eq_factor_mul_integral]]
  rw [intervalIntegral.integral_const_mul]

/-! ## 6. The `∀σ` formulation verdict for the `C` slot (report, no Lean obligation).

The capstone slot `C : ∀ σ E, CarrySeam p μ β (D).T (uTilde …) v vx W σ E`
(via `MeanBundleFamily`) is GENUINELY UNINHABITABLE as written: `CarrySeam`
(and `MeanStepBundle`) carry `hσ0 : 1/2 < σ` and `hσ1 : σ < 3/2` as FIELDS, so for
`σ ≤ 1/2` or `σ ≥ 3/2` NO term of type `CarrySeam … σ E` exists, and there is no
default (`CarrySeam` is a one-constructor structure with no `Inhabited`/`if-then-else`
fallback).  Hence the `fun σ E => if 1/2<σ∧σ<3/2 then carrySeam… else default`
escape does NOT typecheck.

The meanReach ladder (`meanStep_iterate`, IntervalChiNegMeanFixedIterate:139)
evaluates the family ONLY at `σ ∈ {σ₀, σ₀+1/4, …, σ₀+(n−1)/4}` (it starts at the
base `σ₀` and steps `+1/4` up to `< σ₀+n/4`), with `hreach : 1 ≤ σ₀ + n·(1/4)`.
So the ladder needs the seam only on a FINITE, in-range ladder set, never `∀σ:ℝ`.

PRECISE RE-TYPING NEEDED (an edit to `IntervalChiNegMeanFixedIterate` /
`IntervalChiNegSeamFixedReach`, out of scope for this new-file task):
  replace `MeanBundleFamily` and the `C`/`meanReach_H1_of_base` interfaces'
  `∀ σ : ℝ, ∀ E, …` by the LADDER-INDEXED family
  `∀ i : Fin (n+1), ∀ E : TrajectoryHSigmaEnvelope (σ₀ + i·(1/4)) t …,
     MeanStepBundle μ (σ₀ + i·(1/4)) β χ₀ t … E`
  (equivalently `∀ σ ∈ {σ₀ + i·(1/4) | i ≤ n}, …`), and re-thread
  `meanStep_iterate`/`meanReach_H1_of_base` to consume the seam at the ladder
  σ-values only.  Then `chiNeg_carrySeam_perσ` (this file) discharges each ladder
  index in-range, and the capstone `C` hypothesis becomes inhabitable.  With the
  current `∀σ:ℝ` typing, `C` can never be supplied by any producer — including
  `chiNeg_carrySeam_perσ`, which (correctly) demands `1/2 < σ < 3/2`. -/

end ShenWork.Paper2.IntervalChiNegHmdC

namespace ShenWork.Paper2.IntervalChiNegHmdC
section AxiomAudit
#print axioms uTilde_hvnn
#print axioms uTilde_cont_on
#print axioms chiNeg_carrySeam_perσ
#print axioms hpt_heat_of_cont_bounded
#print axioms cosineCoeffs_integral_swap_ae
#print axioms cosineCoeffs_integral_swap_ae_L1
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegHmdC
