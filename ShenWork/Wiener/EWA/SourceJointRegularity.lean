/-
  ShenWork/Wiener/EWA/SourceJointRegularity.lean

  **χ₀<0 JOINT (t,x)-regularity — the slab-continuity frontier fields.**

  `intervalDomainClassicalRegularity` requires JOINT continuity of the
  source-form solution synthesis
  `S t x := ∑'ₙ fullSourceCoeff p u u₀cos t n · cosineMode n x`
  and its time-derivative synthesis
  `Sdot t x := ∑'ₙ fullSourceCoeffDot p u u₀cos t n · cosineMode n x`
  on the parabolic slab.  This is the χ₀<0 analogue of the χ₀=0
  `GradientMildClassicalRegularityFrontierData.jointSolutionClosed` /
  `jointTimeDerivClosed` fields (IntervalMildToClassical.lean) and mirrors the
  weight-1-adaptable templates `resolver_direct_jointSolutionClosed` /
  `resolver_direct_jointTimeDerivClosed`
  (IntervalResolverDirectTimeRegularity.lean).

  **Route.**  Both fields split three ways exactly as `fullSourceCoeff` /
  `fullSourceCoeffDot`: a heat leg plus two spectral-Duhamel legs.  The Duhamel
  legs' joint continuity is ALREADY committed —
  `duhamelSeries_jointContinuousOn` / `duhamelDerivSeries_jointContinuousOn`
  (IntervalSourceCoefficientTimeC1.lean) — on `Ioi 0 ×ˢ univ`, via the
  `continuousOn_tsum` / `reciprocalSquareTerm` parabolic-gain majorants.  Here we

  * prove the HEAT leg's joint continuity (value + time-derivative) on
    `Ioi 0 ×ˢ univ`, via local-box `continuousOn_tsum` with the t-uniform
    heat-trace majorants `Mu0·e^{−cλₙ}` and `Mu0·λₙe^{−cλₙ}` on `Ioo c d`;
  * split the `fullSourceCoeff` / `fullSourceCoeffDot` synthesis tsum into the
    three legs pointwise (the slice file's `tsum_add` / `tsum_mul_left` merge),
    add the three joint-continuous fields, and restrict to the slab domains.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceTimeRegularitySlice
import ShenWork.Wiener.EWA.SourceTimeRegularityMajorant
import ShenWork.Paper2.IntervalResolverDirectTimeRegularity

noncomputable section

namespace ShenWork.EWA

open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff DuhamelSourceTimeC1)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalSourceCoefficientTimeC1
  (duhamelSeries_jointContinuousOn duhamelDerivSeries_jointContinuousOn
    duhamelSpectralCoeff_deriv_summable_uniform_bound)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalPicardIterateRestart (abs_duhamelSpectralCoeff_le)
open ShenWork.IntervalDomainRegularityBootstrap
  (reciprocalSquareTerm reciprocalSquareTerm_summable)
open Set Filter Topology

/-! ## Helpers. -/

/-- `|cosineMode n x| ≤ 1`. -/
private theorem cosineMode_abs_le_one' (n : ℕ) (x : ℝ) : |cosineMode n x| ≤ 1 := by
  simp only [cosineMode]; exact Real.abs_cos_le_one _

/-- `cosineMode n` is continuous. -/
private theorem cosineMode_continuous (n : ℕ) : Continuous (fun x : ℝ => cosineMode n x) :=
  Real.continuous_cos.comp (continuous_const.mul continuous_id)

/-! ## Heat-leg joint continuity (value + derivative) on `Ioi 0 ×ˢ univ`. -/

/-- **HEAT VALUE leg — joint continuity** on `Ioi 0 ×ˢ univ`.
`(t,x) ↦ ∑'ₙ e^{−tλₙ}·u₀cos n · cosineMode n x` is jointly continuous, via
local-box `continuousOn_tsum` with the t-uniform majorant `Mu0·e^{−cλₙ}`. -/
private theorem heatValueSeries_jointContinuousOn (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0) :
    ContinuousOn
      (fun q : ℝ × ℝ =>
        ∑' n, Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n q.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  have hMu0 : 0 ≤ Mu0 := le_trans (abs_nonneg _) (hu0bd 0)
  apply continuousOn_of_forall_continuousAt
  intro p hp
  obtain ⟨hp1, _⟩ := mem_prod.1 hp
  have hp1 : 0 < p.1 := mem_Ioi.1 hp1
  set c := p.1 / 2 with hc_def
  have hc : 0 < c := by positivity
  have hcont : ContinuousOn
      (fun q : ℝ × ℝ =>
        ∑' n, Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n q.2)
      (Ioo c (p.1 + 1) ×ˢ univ) := by
    apply continuousOn_tsum
    · intro n
      have hheat : Continuous (fun t : ℝ =>
          Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n) :=
        (Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)).mul continuous_const
      exact ((hheat.comp continuous_fst).mul
        ((cosineMode_continuous n).comp continuous_snd)).continuousOn
    · exact (ShenWork.HeatKernelGradientEstimates.unitIntervalCosineHeatTrace_single_exp_summable
        hc).mul_left Mu0
    · intro n q hq
      obtain ⟨ht, _⟩ := mem_prod.1 hq
      obtain ⟨hct, _⟩ := mem_Ioo.1 ht
      have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
        unfold unitIntervalCosineEigenvalue; positivity
      rw [Real.norm_eq_abs,
        show Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n q.2
          = Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * (u₀cos n * cosineMode n q.2)
          from by ring, abs_mul, abs_of_nonneg (Real.exp_nonneg _), mul_comm Mu0]
      refine mul_le_mul ?_ ?_ (abs_nonneg _) (Real.exp_nonneg _)
      · exact Real.exp_le_exp_of_le (by nlinarith)
      · rw [abs_mul]
        calc |u₀cos n| * |cosineMode n q.2|
            ≤ Mu0 * 1 := mul_le_mul (hu0bd n) (cosineMode_abs_le_one' n q.2) (abs_nonneg _) hMu0
          _ = Mu0 := mul_one _
  exact hcont.continuousAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      (mem_prod.2 ⟨mem_Ioo.2 ⟨by simp [hc_def]; linarith, by linarith⟩, mem_univ _⟩))

/-- **HEAT DERIVATIVE leg — joint continuity** on `Ioi 0 ×ˢ univ`.
`(t,x) ↦ ∑'ₙ (−λₙ·e^{−tλₙ}·u₀cos n)·cosineMode n x` is jointly continuous, via
local-box `continuousOn_tsum` with the t-uniform majorant `Mu0·λₙe^{−cλₙ}`. -/
private theorem heatDerivSeries_jointContinuousOn (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0) :
    ContinuousOn
      (fun q : ℝ × ℝ =>
        ∑' n, -(unitIntervalCosineEigenvalue n) *
          Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n q.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  have hMu0 : 0 ≤ Mu0 := le_trans (abs_nonneg _) (hu0bd 0)
  apply continuousOn_of_forall_continuousAt
  intro p hp
  obtain ⟨hp1, _⟩ := mem_prod.1 hp
  have hp1 : 0 < p.1 := mem_Ioi.1 hp1
  set c := p.1 / 2 with hc_def
  have hc : 0 < c := by positivity
  have hcont : ContinuousOn
      (fun q : ℝ × ℝ =>
        ∑' n, -(unitIntervalCosineEigenvalue n) *
          Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n q.2)
      (Ioo c (p.1 + 1) ×ˢ univ) := by
    apply continuousOn_tsum
    · intro n
      have hheat : Continuous (fun t : ℝ => -(unitIntervalCosineEigenvalue n) *
          Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n) :=
        (continuous_const.mul
          (Real.continuous_exp.comp (continuous_id.neg.mul continuous_const))).mul continuous_const
      exact ((hheat.comp continuous_fst).mul
        ((cosineMode_continuous n).comp continuous_snd)).continuousOn
    · exact (ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable
        hc).mul_left Mu0
    · intro n q hq
      obtain ⟨ht, _⟩ := mem_prod.1 hq
      obtain ⟨hct, _⟩ := mem_Ioo.1 ht
      have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
        unfold unitIntervalCosineEigenvalue; positivity
      rw [Real.norm_eq_abs,
        show -(unitIntervalCosineEigenvalue n) *
            Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n q.2
          = -(unitIntervalCosineEigenvalue n *
              Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n q.2)
          from by ring, abs_neg, abs_mul, abs_mul, abs_mul, abs_of_nonneg hlam,
        abs_of_nonneg (Real.exp_nonneg _)]
      have hexp : Real.exp (-q.1 * unitIntervalCosineEigenvalue n) ≤
          Real.exp (-c * unitIntervalCosineEigenvalue n) :=
        Real.exp_le_exp_of_le (by nlinarith)
      calc unitIntervalCosineEigenvalue n *
            Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * |u₀cos n| * |cosineMode n q.2|
          ≤ unitIntervalCosineEigenvalue n *
              Real.exp (-c * unitIntervalCosineEigenvalue n) * Mu0 * 1 := by
            apply mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hexp hlam) (hu0bd n)
              (abs_nonneg _) (by positivity)) (cosineMode_abs_le_one' n q.2)
              (abs_nonneg _) (by positivity)
        _ = Mu0 * (unitIntervalCosineEigenvalue n *
              Real.exp (-c * unitIntervalCosineEigenvalue n)) := by ring
  exact hcont.continuousAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      (mem_prod.2 ⟨mem_Ioo.2 ⟨by simp [hc_def]; linarith, by linarith⟩, mem_univ _⟩))

/-! ## Per-leg value/derivative summabilities (inline, t-uniform-free, at fixed `t > 0`). -/

/-- Heat-leg value summability at `t > 0`. -/
private theorem heatVal_summable' (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun n =>
      Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n x) := by
  have hMu0 : 0 ≤ Mu0 := le_trans (abs_nonneg _) (hu0bd 0)
  refine Summable.of_norm_bounded
    (g := fun n => Real.exp (-t * unitIntervalCosineEigenvalue n) * Mu0)
    ((ShenWork.HeatKernelGradientEstimates.unitIntervalCosineHeatTrace_single_exp_summable
      ht).mul_right Mu0) (fun n => ?_)
  rw [Real.norm_eq_abs,
    show Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n x
      = Real.exp (-t * unitIntervalCosineEigenvalue n) * (u₀cos n * cosineMode n x) from by ring,
    abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
  rw [abs_mul]
  calc |u₀cos n| * |cosineMode n x|
      ≤ Mu0 * 1 := mul_le_mul (hu0bd n) (cosineMode_abs_le_one' n x) (abs_nonneg _) hMu0
    _ = Mu0 := mul_one _

/-- Duhamel-leg value summability at `t > 0`. -/
private theorem duhamelVal_summable' {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun n => duhamelSpectralCoeff a t n * cosineMode n x) := by
  refine Summable.of_norm ((src.henv_summable.mul_left t).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => ?_))
  rw [Real.norm_eq_abs, abs_mul]
  calc |duhamelSpectralCoeff a t n| * |cosineMode n x|
      ≤ (t * src.envelope n) * 1 :=
        mul_le_mul (abs_duhamelSpectralCoeff_le src ht n) (cosineMode_abs_le_one' n x)
          (abs_nonneg _) (mul_nonneg ht.le (le_trans (abs_nonneg _) (src.henv_bound 0 le_rfl n)))
    _ = t * src.envelope n := mul_one _

/-- Heat-leg derivative summability at `t > 0`. -/
private theorem heatDerivVal_summable' (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun n => -(unitIntervalCosineEigenvalue n) *
      Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n x) := by
  have hMu0 : 0 ≤ Mu0 := le_trans (abs_nonneg _) (hu0bd 0)
  refine Summable.of_norm
    (((ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable
      ht).mul_left Mu0).of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_))
  have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  rw [Real.norm_eq_abs, show -(unitIntervalCosineEigenvalue n) *
      Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n x =
      -(unitIntervalCosineEigenvalue n * Real.exp (-t * unitIntervalCosineEigenvalue n)
        * u₀cos n * cosineMode n x) from by ring, abs_neg, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg hlam, abs_of_nonneg (Real.exp_nonneg _)]
  calc unitIntervalCosineEigenvalue n * Real.exp (-t * unitIntervalCosineEigenvalue n)
        * |u₀cos n| * |cosineMode n x|
      ≤ unitIntervalCosineEigenvalue n * Real.exp (-t * unitIntervalCosineEigenvalue n)
          * Mu0 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hu0bd n) (by positivity))
          (cosineMode_abs_le_one' n x) (abs_nonneg _) (by positivity)
    _ = Mu0 * (unitIntervalCosineEigenvalue n
          * Real.exp (-t * unitIntervalCosineEigenvalue n)) := by ring

/-- Duhamel-leg derivative summability at `t > 0`. -/
private theorem duhamelDerivVal_summable' {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun n => (a t n - unitIntervalCosineEigenvalue n *
      duhamelSpectralCoeff a t n) * cosineMode n x) := by
  have hdb : 0 ≤ src.derivBound := le_trans (abs_nonneg _) (src.hderivBound 0 le_rfl 0)
  refine Summable.of_norm ((src.henv_summable.add
    (reciprocalSquareTerm_summable.mul_left src.derivBound)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => ?_))
  rw [Real.norm_eq_abs, abs_mul]
  have hnn : 0 ≤ src.envelope n + src.derivBound * reciprocalSquareTerm n :=
    add_nonneg (le_trans (abs_nonneg _) (src.henv_bound 0 le_rfl n))
      (mul_nonneg hdb (by unfold reciprocalSquareTerm; positivity))
  calc |a t n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a t n| * |cosineMode n x|
      ≤ (src.envelope n + src.derivBound * reciprocalSquareTerm n) * 1 :=
        mul_le_mul (duhamelSpectralCoeff_deriv_summable_uniform_bound src ht.le n)
          (cosineMode_abs_le_one' n x) (abs_nonneg _) hnn
    _ = src.envelope n + src.derivBound * reciprocalSquareTerm n := mul_one _

/-! ## The three-leg split of the synthesis tsums (pointwise, on `Ioi 0 ×ˢ univ`). -/

/-- The value synthesis tsum equals the sum of its three leg tsums, on `Ioi 0 ×ˢ univ`. -/
private theorem fullSourceCoeff_tsum_split (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u))
    {q : ℝ × ℝ} (hq : q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :
    (∑' n, fullSourceCoeff p u u₀cos q.1 n * cosineMode n q.2) =
      (∑' n, Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n q.2)
      + (-p.χ₀) * (∑' n, duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) q.1 n
          * cosineMode n q.2)
      + (∑' n, duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) q.1 n
          * cosineMode n q.2) := by
  obtain ⟨hq1, _⟩ := mem_prod.1 hq
  have hqp : 0 < q.1 := mem_Ioi.1 hq1
  have hheat := heatVal_summable' u₀cos hu0bd hqp q.2
  have hchemS := (duhamelVal_summable' hchem hqp q.2).mul_left (-p.χ₀)
  have hlogS := duhamelVal_summable' hlog hqp q.2
  rw [← tsum_mul_left (a := -p.χ₀), ← hheat.tsum_add hchemS,
    ← (hheat.add hchemS).tsum_add hlogS]
  refine (tsum_congr (fun n => ?_)).symm
  simp only [fullSourceCoeff]; ring

/-- The derivative synthesis tsum equals the sum of its three leg tsums, on
`Ioi 0 ×ˢ univ`. -/
private theorem fullSourceCoeffDot_tsum_split (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u))
    {q : ℝ × ℝ} (hq : q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :
    (∑' n, fullSourceCoeffDot p u u₀cos q.1 n * cosineMode n q.2) =
      (∑' n, -(unitIntervalCosineEigenvalue n) *
          Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n q.2)
      + (-p.χ₀) * (∑' n, (coupledChemDivSourceCoeffs p u q.1 n
          - unitIntervalCosineEigenvalue n
            * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) q.1 n) * cosineMode n q.2)
      + (∑' n, (coupledLogisticSourceCoeffs p u q.1 n
          - unitIntervalCosineEigenvalue n
            * duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) q.1 n) * cosineMode n q.2)
      := by
  obtain ⟨hq1, _⟩ := mem_prod.1 hq
  have hqp : 0 < q.1 := mem_Ioi.1 hq1
  have hheat := heatDerivVal_summable' u₀cos hu0bd hqp q.2
  have hchemS := (duhamelDerivVal_summable' hchem hqp q.2).mul_left (-p.χ₀)
  have hlogS := duhamelDerivVal_summable' hlog hqp q.2
  rw [← tsum_mul_left (a := -p.χ₀), ← hheat.tsum_add hchemS,
    ← (hheat.add hchemS).tsum_add hlogS]
  refine (tsum_congr (fun n => ?_)).symm
  simp only [fullSourceCoeffDot]; ring

/-! ## Joint continuity on `Ioi 0 ×ˢ univ`, then restricted to the slab domains. -/

/-- **VALUE field — joint continuity on `Ioi 0 ×ˢ univ`.** -/
private theorem fullSourceCoeff_jointContinuousOn (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u)) :
    ContinuousOn
      (fun q : ℝ × ℝ => ∑' n, fullSourceCoeff p u u₀cos q.1 n * cosineMode n q.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  have hheat := heatValueSeries_jointContinuousOn u₀cos hu0bd
  have hchemJ := duhamelSeries_jointContinuousOn hchem
  have hlogJ := duhamelSeries_jointContinuousOn hlog
  have hsum := ((hheat.add (hchemJ.const_smul (-p.χ₀))).add hlogJ)
  refine hsum.congr (fun q hq => ?_)
  have := fullSourceCoeff_tsum_split p u u₀cos hu0bd hchem hlog hq
  simp only [Pi.add_apply, Function.uncurry, smul_eq_mul] at this ⊢
  rw [this]

/-- **TIME-DERIV field — joint continuity on `Ioi 0 ×ˢ univ`.** -/
private theorem fullSourceCoeffDot_jointContinuousOn (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u)) :
    ContinuousOn
      (fun q : ℝ × ℝ => ∑' n, fullSourceCoeffDot p u u₀cos q.1 n * cosineMode n q.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  have hheat := heatDerivSeries_jointContinuousOn u₀cos hu0bd
  have hchemJ := duhamelDerivSeries_jointContinuousOn hchem
  have hlogJ := duhamelDerivSeries_jointContinuousOn hlog
  have hsum := ((hheat.add (hchemJ.const_smul (-p.χ₀))).add hlogJ)
  refine hsum.congr (fun q hq => ?_)
  have := fullSourceCoeffDot_tsum_split p u u₀cos hu0bd hchem hlog hq
  simp only [Pi.add_apply, Function.uncurry, smul_eq_mul] at this ⊢
  rw [this]

/-- The slab `Ioo 0 T ×ˢ Icc 0 1 ⊆ Ioi 0 ×ˢ univ`. -/
private theorem slabClosed_subset (T : ℝ) :
    Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) :=
  prod_mono (fun _ ht => mem_Ioi.2 (mem_Ioo.1 ht).1) (subset_univ _)

/-- The interior slab `Ioo 0 T ×ˢ Ioo 0 1 ⊆ Ioi 0 ×ˢ univ`. -/
private theorem slabOpen_subset (T : ℝ) :
    Ioo (0 : ℝ) T ×ˢ Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) :=
  prod_mono (fun _ ht => mem_Ioi.2 (mem_Ioo.1 ht).1) (subset_univ _)

/-! ## The frontier fields — exact slab domains matching `intervalDomainClassicalRegularity`. -/

/-- **(A) Joint continuity of the χ₀<0 solution field on the closed slab**
`Ioo 0 T ×ˢ Icc 0 1`. -/
theorem fullSourceCoeff_jointSolutionClosed (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u)) {T : ℝ} :
    ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  (fullSourceCoeff_jointContinuousOn p u u₀cos hu0bd hchem hlog).mono (slabClosed_subset T)

/-- **(A′) Joint continuity of the χ₀<0 solution field on the interior slab**
`Ioo 0 T ×ˢ Ioo 0 1`. -/
theorem fullSourceCoeff_jointSolutionInterior (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u)) {T : ℝ} :
    ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x))
      (Ioo (0 : ℝ) T ×ˢ Ioo (0 : ℝ) 1) :=
  (fullSourceCoeff_jointContinuousOn p u u₀cos hu0bd hchem hlog).mono (slabOpen_subset T)

/-- **(B) Joint continuity of the χ₀<0 time-derivative field on the closed slab**
`Ioo 0 T ×ˢ Icc 0 1`. -/
theorem fullSourceCoeffDot_jointTimeDerivClosed (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u)) {T : ℝ} :
    ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        ∑' n, fullSourceCoeffDot p u u₀cos t n * cosineMode n x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  (fullSourceCoeffDot_jointContinuousOn p u u₀cos hu0bd hchem hlog).mono (slabClosed_subset T)

/-- **(B′) Joint continuity of the χ₀<0 time-derivative field on the interior slab**
`Ioo 0 T ×ˢ Ioo 0 1`. -/
theorem fullSourceCoeffDot_jointTimeDerivInterior (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u)) {T : ℝ} :
    ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        ∑' n, fullSourceCoeffDot p u u₀cos t n * cosineMode n x))
      (Ioo (0 : ℝ) T ×ˢ Ioo (0 : ℝ) 1) :=
  (fullSourceCoeffDot_jointContinuousOn p u u₀cos hu0bd hchem hlog).mono (slabOpen_subset T)

end ShenWork.EWA
