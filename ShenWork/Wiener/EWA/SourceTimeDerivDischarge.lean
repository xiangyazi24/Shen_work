/-
  ShenWork/Wiener/EWA/SourceTimeDerivDischarge.lean

  **χ₀<0 — discharging the two time-derivative carried hyps of
  `realSlice_classicalRegularity`** (SourceClassicalRegularity.lean:120):

  * `htimeDeriv`: `deriv (fun s => realSlice u_star s x) t
       = ∑'ₙ fullSourceCoeffDot p (realSlice u_star) u₀cos t n · cosineMode n x.1`;
  * `hdiffU`:    `DifferentiableAt ℝ (fun s => realSlice u_star s x) t`.

  **Route (verified analysis).**  On `Ioo 0 T` the lift slice equals its
  `fullSourceCoeff` synthesis (the carried slab `realizes`):
    `realSlice u_star s x = ∑'ₙ fullSourceCoeff p u u₀cos s n · cosineMode n x.1`.
  Term-by-term, `d/dt fullSourceCoeff = fullSourceCoeffDot`
  (`fullSourceCoeff_term_hasDerivAt_time`).  The differentiated series converges
  uniformly on a compact subinterval `Ioo c T` (`0 < c < t₀ < T`) because it is
  DOMINATED by a `t`-uniform summable majorant:
    HEAT      `λₙ e^{−cλₙ}·Mu0`     (heat smoothing; NOT `λₙ·envₙ`),
    chemDiv   `|χ₀|·(envₙ + Ṁ·recipₙ)`,
    logistic  `envₙ + Ṁ·recipₙ`.
  Mathlib `hasDerivAt_tsum_of_isPreconnected` on `Ioo c T` then interchanges
  `deriv` with `tsum`, giving a `HasDerivAt` for the synthesis; transferring along
  the eventual `realizes`-agreement yields a `HasDerivAt` for the `realSlice`
  slice — `hdiffU` is its `DifferentiableAt`, `htimeDeriv` its `deriv`.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceTimeRegularityMajorant

noncomputable section

namespace ShenWork.EWA

open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff DuhamelSourceTimeC1)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalPicardIterateRestart (abs_duhamelSpectralCoeff_le)
open ShenWork.IntervalDomainRegularityBootstrap
  (reciprocalSquareTerm reciprocalSquareTerm_summable)
open ShenWork.IntervalSourceCoefficientTimeC1
  (duhamelSpectralCoeff_deriv_summable_uniform_bound)
open ShenWork.IntervalMildRegularityBootstrap
  (unitIntervalCosineEigenvalue_mul_exp_summable)
open Set Filter Topology

/-! ### `|cosineMode| ≤ 1`. -/

private theorem cosineMode_abs_le_one'' (n : ℕ) (x : ℝ) : |cosineMode n x| ≤ 1 := by
  simp only [cosineMode]; exact Real.abs_cos_le_one _

/-! ### The `t`-uniform summable majorant on `Ioo c T` (`0 < c`). -/

/-- The per-mode majorant for `|fullSourceCoeffDot s n · cosineMode n x|`,
uniform over `s ≥ c` (`c > 0`): heat-smoothing leg `Mu0·λₙe^{−cλₙ}` plus the two
`t`-uniform Duhamel-derivative envelopes. -/
private def fscDotMajorant (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Mu0 c : ℝ)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u)) (n : ℕ) : ℝ :=
  Mu0 * (unitIntervalCosineEigenvalue n * Real.exp (-c * unitIntervalCosineEigenvalue n))
    + |(-p.χ₀)| * (hchem.envelope n + hchem.derivBound * reciprocalSquareTerm n)
    + (hlog.envelope n + hlog.derivBound * reciprocalSquareTerm n)

private theorem fscDotMajorant_summable (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (Mu0 : ℝ) {c : ℝ} (hc : 0 < c)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u)) :
    Summable (fun n => fscDotMajorant p u Mu0 c hchem hlog n) := by
  unfold fscDotMajorant
  have hheat : Summable (fun n => Mu0 * (unitIntervalCosineEigenvalue n
      * Real.exp (-c * unitIntervalCosineEigenvalue n))) :=
    (unitIntervalCosineEigenvalue_mul_exp_summable hc).mul_left Mu0
  have hchemM : Summable (fun n => |(-p.χ₀)|
      * (hchem.envelope n + hchem.derivBound * reciprocalSquareTerm n)) :=
    (hchem.henv_summable.add
      (reciprocalSquareTerm_summable.mul_left hchem.derivBound)).mul_left |(-p.χ₀)|
  have hlogM : Summable (fun n =>
      hlog.envelope n + hlog.derivBound * reciprocalSquareTerm n) :=
    hlog.henv_summable.add (reciprocalSquareTerm_summable.mul_left hlog.derivBound)
  exact (hheat.add hchemM).add hlogM

/-- Each differentiated summand is dominated by the majorant on `Ioo c T`. -/
private theorem fscDot_term_le_majorant (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u))
    {c T : ℝ} (hc : 0 < c) (x : ℝ) (n : ℕ) (s : ℝ) (hs : s ∈ Ioo c T) :
    ‖fullSourceCoeffDot p u u₀cos s n * cosineMode n x‖
      ≤ fscDotMajorant p u Mu0 c hchem hlog n := by
  have hMu0 : 0 ≤ Mu0 := le_trans (abs_nonneg _) (hu0bd 0)
  have hcs : c ≤ s := le_of_lt (mem_Ioo.1 hs).1
  have hs0 : 0 ≤ s := le_trans hc.le hcs
  have hlam : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  have hcos := cosineMode_abs_le_one'' n x
  -- bound the three legs of `fullSourceCoeffDot`.
  have hheat : |(-(unitIntervalCosineEigenvalue n)
        * Real.exp (-s * unitIntervalCosineEigenvalue n) * u₀cos n)|
      ≤ Mu0 * (unitIntervalCosineEigenvalue n
          * Real.exp (-c * unitIntervalCosineEigenvalue n)) := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hlam,
      abs_of_nonneg (Real.exp_nonneg _), mul_comm Mu0]
    refine mul_le_mul ?_ (hu0bd n) (abs_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp_of_le (by nlinarith [hcs, hlam])) hlam
  have hchemLeg : |(-p.χ₀) * (coupledChemDivSourceCoeffs p u s n
        - unitIntervalCosineEigenvalue n
          * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) s n)|
      ≤ |(-p.χ₀)| * (hchem.envelope n + hchem.derivBound * reciprocalSquareTerm n) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (duhamelSpectralCoeff_deriv_summable_uniform_bound hchem hs0 n) (abs_nonneg _)
  have hlogLeg : |(coupledLogisticSourceCoeffs p u s n
        - unitIntervalCosineEigenvalue n
          * duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) s n)|
      ≤ hlog.envelope n + hlog.derivBound * reciprocalSquareTerm n :=
    duhamelSpectralCoeff_deriv_summable_uniform_bound hlog hs0 n
  -- combine: `|fscDot·cos| ≤ |fscDot| ≤ heat+chem+log majorant`.
  rw [Real.norm_eq_abs, abs_mul]
  calc |fullSourceCoeffDot p u u₀cos s n| * |cosineMode n x|
      ≤ |fullSourceCoeffDot p u u₀cos s n| * 1 :=
        mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
    _ = |fullSourceCoeffDot p u u₀cos s n| := mul_one _
    _ ≤ |(-(unitIntervalCosineEigenvalue n)
            * Real.exp (-s * unitIntervalCosineEigenvalue n) * u₀cos n)|
          + |(-p.χ₀) * (coupledChemDivSourceCoeffs p u s n
              - unitIntervalCosineEigenvalue n
                * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) s n)|
          + |(coupledLogisticSourceCoeffs p u s n
              - unitIntervalCosineEigenvalue n
                * duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) s n)| := by
        simpa only [fullSourceCoeffDot] using abs_add_three _ _ _
    _ ≤ fscDotMajorant p u Mu0 c hchem hlog n := by
        unfold fscDotMajorant
        exact add_le_add (add_le_add hheat hchemLeg) hlogLeg

/-! ### Value-series base-point summability at `t₀ > 0`. -/

/-- `∑'ₙ fullSourceCoeff p u u₀cos t₀ n · cosineMode n x < ∞` at `t₀ > 0`. -/
private theorem fullSourceCoeffSeries_summable (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u))
    {t₀ : ℝ} (ht₀ : 0 < t₀) (x : ℝ) :
    Summable (fun n => fullSourceCoeff p u u₀cos t₀ n * cosineMode n x) := by
  have hMu0 : 0 ≤ Mu0 := le_trans (abs_nonneg _) (hu0bd 0)
  -- per-leg majorant at the fixed point `t₀`.
  have hmaj : Summable (fun n =>
      Mu0 * Real.exp (-t₀ * unitIntervalCosineEigenvalue n)
        + |(-p.χ₀)| * (t₀ * hchem.envelope n) + t₀ * hlog.envelope n) :=
    (((ShenWork.HeatKernelGradientEstimates.unitIntervalCosineHeatTrace_single_exp_summable
        ht₀).mul_left Mu0).add
      ((hchem.henv_summable.mul_left t₀).mul_left |(-p.χ₀)|)).add
      (hlog.henv_summable.mul_left t₀)
  refine Summable.of_norm (hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_))
  have hcos := cosineMode_abs_le_one'' n x
  have henvC : 0 ≤ hchem.envelope n := le_trans (abs_nonneg _) (hchem.henv_bound 0 le_rfl n)
  have henvL : 0 ≤ hlog.envelope n := le_trans (abs_nonneg _) (hlog.henv_bound 0 le_rfl n)
  rw [Real.norm_eq_abs, abs_mul]
  have hbound : |fullSourceCoeff p u u₀cos t₀ n|
      ≤ Mu0 * Real.exp (-t₀ * unitIntervalCosineEigenvalue n)
        + |(-p.χ₀)| * (t₀ * hchem.envelope n) + t₀ * hlog.envelope n := by
    have hheat : |Real.exp (-t₀ * unitIntervalCosineEigenvalue n) * u₀cos n|
        ≤ Mu0 * Real.exp (-t₀ * unitIntervalCosineEigenvalue n) := by
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _), mul_comm]
      exact mul_le_mul_of_nonneg_right (hu0bd n) (Real.exp_nonneg _)
    have hchemLeg : |(-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t₀ n|
        ≤ |(-p.χ₀)| * (t₀ * hchem.envelope n) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_duhamelSpectralCoeff_le hchem ht₀ n) (abs_nonneg _)
    have hlogLeg : |duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t₀ n|
        ≤ t₀ * hlog.envelope n := abs_duhamelSpectralCoeff_le hlog ht₀ n
    calc |fullSourceCoeff p u u₀cos t₀ n|
        ≤ |Real.exp (-t₀ * unitIntervalCosineEigenvalue n) * u₀cos n|
            + |(-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t₀ n|
            + |duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t₀ n| := by
          simpa only [fullSourceCoeff] using abs_add_three _ _ _
      _ ≤ _ := add_le_add (add_le_add hheat hchemLeg) hlogLeg
  calc |fullSourceCoeff p u u₀cos t₀ n| * |cosineMode n x|
      ≤ |fullSourceCoeff p u u₀cos t₀ n| * 1 :=
        mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
    _ = |fullSourceCoeff p u u₀cos t₀ n| := mul_one _
    _ ≤ _ := hbound

/-! ### `HasDerivAt` of the synthesis on `Ioo c T`. -/

/-- **The `fullSourceCoeff` cosine series is time-differentiable at `t₀ ∈ Ioo 0 T`,
with derivative the `fullSourceCoeffDot` synthesis.**  Term-by-term differentiation
via `hasDerivAt_tsum_of_isPreconnected` on `Ioo c T` (`c = t₀/2`), with the
`t`-uniform majorant `fscDotMajorant`. -/
theorem fullSourceCoeffSeries_hasDerivAt (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u))
    {T t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) T) (x : ℝ) :
    HasDerivAt (fun s => ∑' n, fullSourceCoeff p u u₀cos s n * cosineMode n x)
      (∑' n, fullSourceCoeffDot p u u₀cos t₀ n * cosineMode n x) t₀ := by
  obtain ⟨ht0, htT⟩ := ht₀
  set c := t₀ / 2 with hc_def
  have hc : 0 < c := by positivity
  have hct₀ : c < t₀ := by rw [hc_def]; linarith
  have ht₀mem : t₀ ∈ Ioo c T := ⟨hct₀, htT⟩
  -- per-mode HasDerivAt of `s ↦ fullSourceCoeff s n · cosineMode n x`.
  have hg : ∀ n s, s ∈ Ioo c T →
      HasDerivAt (fun r => fullSourceCoeff p u u₀cos r n * cosineMode n x)
        (fullSourceCoeffDot p u u₀cos s n * cosineMode n x) s :=
    fun n s _ =>
      (fullSourceCoeff_term_hasDerivAt_time p u u₀cos hchem hlog s n).mul_const (cosineMode n x)
  -- `t`-uniform summable derivative majorant on `Ioo c T`.
  have hg' : ∀ n s, s ∈ Ioo c T →
      ‖fullSourceCoeffDot p u u₀cos s n * cosineMode n x‖
        ≤ fscDotMajorant p u Mu0 c hchem hlog n :=
    fun n s hs => fscDot_term_le_majorant p u u₀cos hu0bd hchem hlog hc x n s hs
  exact hasDerivAt_tsum_of_isPreconnected
    (fscDotMajorant_summable p u Mu0 hc hchem hlog) isOpen_Ioo isPreconnected_Ioo
    hg hg' ht₀mem
    (fullSourceCoeffSeries_summable p u u₀cos hu0bd hchem hlog ht0 x) ht₀mem

/-! ### Transfer to the `realSlice` slice through the `realizes` agreement. -/

/-- **`HasDerivAt` for the `realSlice` time-slice at interior `t`.**  Transfer of
`fullSourceCoeffSeries_hasDerivAt` along the eventual `realizes`-agreement
(`Ioo 0 T` is open, so agreement holds on a neighborhood of `t`). -/
theorem realSlice_hasDerivAt_time (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u)) {T : ℝ}
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) x
        = ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : intervalDomainPoint) :
    HasDerivAt (fun s => u s x)
      (∑' n, fullSourceCoeffDot p u u₀cos t n * cosineMode n x.1) t := by
  -- eventual agreement: `u s x = synthesis at x.1` for `s` near `t`.
  have hagree : (fun s => u s x)
      =ᶠ[𝓝 t] (fun s => ∑' n, fullSourceCoeff p u u₀cos s n * cosineMode n x.1) := by
    refine Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) (fun s hs => ?_)
    have hx1 : x.1 ∈ Icc (0 : ℝ) 1 := x.2
    have hlift : intervalDomainLift (u s) x.1 = u s x := by
      simp [intervalDomainLift, x.2]
    rw [← hlift, hrealizes s hs x.1 hx1]
  exact (fullSourceCoeffSeries_hasDerivAt p u u₀cos hu0bd hchem hlog ht x.1).congr_of_eventuallyEq
    hagree

/-! ### THE TWO DISCHARGED CARRIED HYPS. -/

/-- **`htimeDeriv` of `realSlice_classicalRegularity`, discharged.** -/
theorem realSlice_timeDeriv_of_atoms (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u)) {T : ℝ}
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) x
        = ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      deriv (fun s : ℝ => u s x) t
        = ∑' n, fullSourceCoeffDot p u u₀cos t n * cosineMode n x.1 :=
  fun t ht x =>
    (realSlice_hasDerivAt_time p u u₀cos hu0bd hchem hlog hrealizes ht x).deriv

/-- **`hdiffU` of `realSlice_classicalRegularity`, discharged.** -/
theorem realSlice_diffU_of_atoms (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u)) {T : ℝ}
    (hrealizes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) x
        = ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      DifferentiableAt ℝ (fun s : ℝ => u s x) t :=
  fun t ht x =>
    (realSlice_hasDerivAt_time p u u₀cos hu0bd hchem hlog hrealizes ht x).differentiableAt

end ShenWork.EWA
