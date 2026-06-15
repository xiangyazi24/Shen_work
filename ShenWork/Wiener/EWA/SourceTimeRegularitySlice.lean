/-
  ShenWork/Wiener/EWA/SourceTimeRegularitySlice.lean

  **χ₀<0 u_t (time-regularity) construction — BRICK 3 (final).**

  Term-by-term TIME-derivative of the cosine synthesis
  `t ↦ ∑'ₙ fullSourceCoeff p u u₀cos t n · cosineMode n x`, plus the classical
  time-slice extension.

  `fullSourceCoeff` (SourceStrongSolution.lean:109) is the three-leg coefficient
  `exp(−tλₙ)·u₀cos n + (−χ₀)·duhamel_chem + duhamel_log`.  Each leg's cosine
  synthesis already has a committed time-derivative engine:

  * heat leg → `homogeneousCosineSeries_hasDerivAt_time`
    (IntervalSourceCoefficientTimeC1.lean:601);
  * each Duhamel leg → `duhamelSpectralCosineSeries_hasDerivAt_time`
    (IntervalSourceCoefficientTimeC1.lean:519).

  The three `HasDerivAt`s are added (the chemDiv leg pre-scaled by `(−χ₀)` via
  `HasDerivAt.const_mul`), then the function and derivative `tsum`s are merged
  back into the `fullSourceCoeff` / `fullSourceCoeffDot` forms by `tsum_add`,
  `tsum_mul_left`, and `tsum_congr`.  The per-leg summabilities required for
  `tsum_add` are exactly the committed value-summable lemmas (heat-trace exp
  bound, the Duhamel eigenvalue-ℓ¹ ⇒ value-ℓ¹ extraction, and the uniform
  parabolic derivative bound).

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceTimeRegularityMajorant
import ShenWork.Paper2.IntervalResolverDirectTimeRegularity

noncomputable section

namespace ShenWork.EWA

open ShenWork.IntervalDuhamelClosedC2
  (duhamelSpectralCoeff DuhamelSourceTimeC1 duhamelSpectralCoeff_eigenvalue_summable
    cosineCoeff_summable_of_eigenvalue_summable)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalSourceCoefficientTimeC1
  (homogeneousCosineSeries_hasDerivAt_time duhamelSpectralCosineSeries_hasDerivAt_time
    duhamelSpectralCoeff_deriv_abs_summable)
open ShenWork.CosineSpectrum (cosineMode)
open Set Filter Topology

/-! ## Per-leg value summabilities at the interior time. -/

/-- `|cosineMode n x| ≤ 1`. -/
private theorem cosineMode_abs_le_one (n : ℕ) (x : ℝ) : |cosineMode n x| ≤ 1 := by
  simp only [cosineMode]; exact Real.abs_cos_le_one _

/-- **Heat-leg synthesis value summability** at `t₀ > 0`. -/
private theorem heatSynth_summable (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0) {t₀ : ℝ} (ht₀ : 0 < t₀) (x : ℝ) :
    Summable (fun n => Real.exp (-t₀ * unitIntervalCosineEigenvalue n) *
      u₀cos n * cosineMode n x) := by
  have hMu0 : 0 ≤ Mu0 := le_trans (abs_nonneg _) (hu0bd 0)
  refine Summable.of_norm_bounded
    (g := fun n => Real.exp (-t₀ * unitIntervalCosineEigenvalue n) * Mu0)
    ((ShenWork.HeatKernelGradientEstimates.unitIntervalCosineHeatTrace_single_exp_summable
      ht₀).mul_right Mu0) (fun n => ?_)
  rw [Real.norm_eq_abs,
    show Real.exp (-t₀ * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n x =
      Real.exp (-t₀ * unitIntervalCosineEigenvalue n) * (u₀cos n * cosineMode n x)
      from by ring, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
  rw [abs_mul]
  calc |u₀cos n| * |cosineMode n x|
      ≤ Mu0 * 1 := mul_le_mul (hu0bd n) (cosineMode_abs_le_one n x) (abs_nonneg _) hMu0
    _ = Mu0 := mul_one _

/-- **Duhamel-leg synthesis value summability** at `t₀ > 0`. -/
private theorem duhamelSynth_summable {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (x : ℝ) :
    Summable (fun n => duhamelSpectralCoeff a t₀ n * cosineMode n x) := by
  have ⟨_, habs⟩ := cosineCoeff_summable_of_eigenvalue_summable
    (duhamelSpectralCoeff_eigenvalue_summable src ht₀)
  exact Summable.of_norm (habs.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (cosineMode_abs_le_one n x)))

/-- **Duhamel-leg derivative value summability** at `t₀ > 0`. -/
private theorem duhamelDerivSynth_summable {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (x : ℝ) :
    Summable (fun n => (a t₀ n - unitIntervalCosineEigenvalue n *
      duhamelSpectralCoeff a t₀ n) * cosineMode n x) :=
  Summable.of_norm ((duhamelSpectralCoeff_deriv_abs_summable src ht₀).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (cosineMode_abs_le_one n x)))

/-- **Heat-leg derivative value summability** at `t₀ > 0`. -/
private theorem heatDerivSynth_summable (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0) {t₀ : ℝ} (ht₀ : 0 < t₀) (x : ℝ) :
    Summable (fun n => -(unitIntervalCosineEigenvalue n *
      Real.exp (-t₀ * unitIntervalCosineEigenvalue n)) * u₀cos n * cosineMode n x) := by
  have hMu0 : 0 ≤ Mu0 := le_trans (abs_nonneg _) (hu0bd 0)
  have ht₀2 : 0 < t₀ / 2 := by linarith
  apply Summable.of_norm
  refine ((ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable
    ht₀2).mul_right Mu0).of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
  have hlam_nn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  rw [Real.norm_eq_abs, show -(unitIntervalCosineEigenvalue n *
      Real.exp (-t₀ * unitIntervalCosineEigenvalue n)) * u₀cos n * cosineMode n x =
      -(unitIntervalCosineEigenvalue n *
        Real.exp (-t₀ * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n x)
      from by ring, abs_neg, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg hlam_nn, abs_of_nonneg (Real.exp_nonneg _)]
  have hexp_mono : Real.exp (-t₀ * unitIntervalCosineEigenvalue n) ≤
      Real.exp (-(t₀ / 2) * unitIntervalCosineEigenvalue n) :=
    Real.exp_le_exp_of_le (by nlinarith)
  calc unitIntervalCosineEigenvalue n *
        Real.exp (-t₀ * unitIntervalCosineEigenvalue n) * |u₀cos n| * |cosineMode n x|
      ≤ unitIntervalCosineEigenvalue n *
          Real.exp (-(t₀ / 2) * unitIntervalCosineEigenvalue n) * Mu0 * 1 := by
        apply mul_le_mul (mul_le_mul ?_ (hu0bd n) (abs_nonneg _) (by positivity))
          (cosineMode_abs_le_one n x) (abs_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left hexp_mono hlam_nn
    _ = unitIntervalCosineEigenvalue n *
          Real.exp (-(t₀ / 2) * unitIntervalCosineEigenvalue n) * Mu0 := mul_one _

/-! ## Part 1: the core time-derivative of the χ₀<0 solution synthesis. -/

/-- **THE χ₀<0 SOLUTION TIME-DERIVATIVE.**  The cosine synthesis
`t ↦ ∑'ₙ fullSourceCoeff p u u₀cos t n · cosineMode n x` has time derivative
`∑'ₙ fullSourceCoeffDot p u u₀cos t₀ n · cosineMode n x` at every interior time
`t₀ > 0`.

Assembled from the heat synthesis derivative (`homogeneousCosineSeries_…`) and the
two Duhamel synthesis derivatives (`duhamelSpectralCosineSeries_…`, the chemDiv leg
pre-scaled by `(−χ₀)`), merged via `tsum_add` / `tsum_mul_left`. -/
theorem fullSourceCoeff_hasDerivAt_time (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (u₀cos : ℕ → ℝ) {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u))
    {t₀ : ℝ} (ht₀ : 0 < t₀) (x : ℝ) :
    HasDerivAt (fun t => ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x)
      (∑' n, fullSourceCoeffDot p u u₀cos t₀ n * cosineMode n x) t₀ := by
  have hMu0 : 0 ≤ Mu0 := le_trans (abs_nonneg _) (hu0bd 0)
  set ach := coupledChemDivSourceCoeffs p u with hach
  set alog := coupledLogisticSourceCoeffs p u with halog
  -- the three component HasDerivAt's
  have hheat := homogeneousCosineSeries_hasDerivAt_time hMu0 hu0bd ht₀ x
  have hchemD := (duhamelSpectralCosineSeries_hasDerivAt_time hchem ht₀ x).const_mul (-p.χ₀)
  have hlogD := duhamelSpectralCosineSeries_hasDerivAt_time hlog ht₀ x
  have hcomb := (hheat.add hchemD).add hlogD
  -- merge the combined FUNCTION into the fullSourceCoeff synthesis, eventually near t₀
  have hfun_ev : (fun t => (∑' n, Real.exp (-t * unitIntervalCosineEigenvalue n) *
        u₀cos n * cosineMode n x) +
      -p.χ₀ * ∑' n, duhamelSpectralCoeff ach t n * cosineMode n x +
      ∑' n, duhamelSpectralCoeff alog t n * cosineMode n x) =ᶠ[𝓝 t₀]
      (fun t => ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x) := by
    refine Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht₀) (fun t ht => ?_)
    have htp : 0 < t := mem_Ioi.1 ht
    rw [← tsum_mul_left (a := -p.χ₀)]
    rw [← (heatSynth_summable u₀cos hu0bd htp x).tsum_add
        ((duhamelSynth_summable hchem htp x).mul_left (-p.χ₀)),
      ← (Summable.add (heatSynth_summable u₀cos hu0bd htp x)
          ((duhamelSynth_summable hchem htp x).mul_left (-p.χ₀))).tsum_add
        (duhamelSynth_summable hlog htp x)]
    refine tsum_congr (fun n => ?_)
    simp only [fullSourceCoeff, hach, halog]; ring
  -- merge the combined DERIVATIVE into the fullSourceCoeffDot synthesis
  have hderiv_eq : (∑' n, -(unitIntervalCosineEigenvalue n *
        Real.exp (-t₀ * unitIntervalCosineEigenvalue n)) * u₀cos n * cosineMode n x) +
      -p.χ₀ * ∑' n, (ach t₀ n - unitIntervalCosineEigenvalue n *
        duhamelSpectralCoeff ach t₀ n) * cosineMode n x +
      ∑' n, (alog t₀ n - unitIntervalCosineEigenvalue n *
        duhamelSpectralCoeff alog t₀ n) * cosineMode n x =
      ∑' n, fullSourceCoeffDot p u u₀cos t₀ n * cosineMode n x := by
    rw [← tsum_mul_left (a := -p.χ₀)]
    rw [← (heatDerivSynth_summable u₀cos hu0bd ht₀ x).tsum_add
        ((duhamelDerivSynth_summable hchem ht₀ x).mul_left (-p.χ₀)),
      ← (Summable.add (heatDerivSynth_summable u₀cos hu0bd ht₀ x)
          ((duhamelDerivSynth_summable hchem ht₀ x).mul_left (-p.χ₀))).tsum_add
        (duhamelDerivSynth_summable hlog ht₀ x)]
    refine tsum_congr (fun n => ?_)
    simp only [fullSourceCoeffDot, hach, halog]; ring
  rw [← hderiv_eq]
  exact hcomb.congr_of_eventuallyEq hfun_ev.symm

/-! ## Part 2: differentiability + classical time-slice. -/

/-- **Time differentiability** of the χ₀<0 solution synthesis at every interior time. -/
theorem fullSourceCoeff_differentiableAt_time (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u))
    {t₀ : ℝ} (ht₀ : 0 < t₀) (x : ℝ) :
    DifferentiableAt ℝ
      (fun t => ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x) t₀ :=
  (fullSourceCoeff_hasDerivAt_time p u u₀cos hu0bd hchem hlog ht₀ x).differentiableAt

/-- **Classical time-slice (time-regularity leg).**  At the record's interior time
`D.t`, for every `x`, the cosine synthesis is time-differentiable with derivative the
synthesis of `fullSourceCoeffDot`.  This is the time-derivative companion of
`SourceStrongSolutionData.isClassicalSpatialSlice`.

The chemDiv source's `DuhamelSourceTimeC1` package is supplied as `hchem` (genuinely
carried, as in Brick 1); the logistic one is the record's `logSrc`. -/
theorem SourceStrongSolutionData.isClassicalTimeSlice
    {T μ ν γ : ℝ} {hμ : 0 < μ} {p : CM2Params}
    (D : SourceStrongSolutionData T (μ := μ) (ν := ν) (γ := γ) hμ p)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p D.u)) (x : ℝ) :
    HasDerivAt (fun t => ∑' n, fullSourceCoeff p D.u D.u₀cos t n * cosineMode n x)
      (∑' n, fullSourceCoeffDot p D.u D.u₀cos D.t n * cosineMode n x) D.t :=
  fullSourceCoeff_hasDerivAt_time p D.u D.u₀cos D.hu0bd hchem D.logSrc D.htlo x

end ShenWork.EWA
