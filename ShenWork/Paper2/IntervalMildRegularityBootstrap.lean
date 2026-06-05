/-
  ShenWork/Paper2/IntervalMildRegularityBootstrap.lean

  Half-step spatial regularity bridge for mild solutions.

  The analytic point is coefficient-level: if a restarted slice is represented by

    e^{-τλₙ} a₀ₙ + ∫₀ᵗ e^{-(τ-s)λₙ} a(s,n) ds,

  with bounded restart coefficients and a T6 time-C¹ source, then
  `∑ λₙ |bₙ|` is summable.  The generic cosine-series engine then gives `C²`
  regularity and Neumann endpoint limits for the represented slice.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalCosineSliceRegularity
import ShenWork.Paper2.IntervalMildPicard
import ShenWork.PDE.IntervalSemigroupNeumann

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalMildPicard
open ShenWork.IntervalSemigroupNeumann
open ShenWork.PDE.IntervalMildSourceDecayHelper

noncomputable section

namespace ShenWork.IntervalMildRegularityBootstrap

/-- The coefficient sequence obtained after restarting a mild formula at a positive
time gap `τ`: heat-smoothed restart datum plus a spectral Duhamel coefficient. -/
def restartDuhamelCoeff (a₀ : ℕ → ℝ) (a : ℝ → ℕ → ℝ) (τ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n +
    duhamelSpectralCoeff a τ n

/-- Heat smoothing supplies the missing polynomial weight:
`∑ λₙ e^{-τλₙ} < ∞` for every `τ > 0`. -/
theorem unitIntervalCosineEigenvalue_mul_exp_summable {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
  set r : ℝ := τ * Real.pi ^ 2 with hr_def
  have hr : 0 < r := by
    rw [hr_def]
    positivity
  have hbase : Summable (fun n : ℕ =>
      Real.pi ^ 2 * ((n : ℝ) ^ 2 * Real.exp (-r * (n : ℝ)))) := by
    simpa using
      (Real.summable_pow_mul_exp_neg_nat_mul 2 (r := r) hr).mul_left
        (Real.pi ^ 2)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbase
  · exact mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity) (Real.exp_nonneg _)
  · have hn_sq_ge : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      by_cases hn : n = 0
      · subst n
        norm_num
      · have hn0 : (0 : ℝ) ≤ n := by positivity
        have hn1 : (1 : ℝ) ≤ n := by
          exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
        have hmul : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) :=
          mul_nonneg hn0 (sub_nonneg.mpr hn1)
        nlinarith
    have hlam_eq : unitIntervalCosineEigenvalue n = (n : ℝ) ^ 2 * Real.pi ^ 2 := by
      unfold unitIntervalCosineEigenvalue
      ring
    have hexp_le :
        Real.exp (-τ * unitIntervalCosineEigenvalue n) ≤
          Real.exp (-r * (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hmul : r * (n : ℝ) ≤ r * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hn_sq_ge hr.le
      rw [hlam_eq]
      rw [hr_def] at hmul ⊢
      nlinarith
    calc unitIntervalCosineEigenvalue n *
          Real.exp (-τ * unitIntervalCosineEigenvalue n)
        = ((n : ℝ) ^ 2 * Real.pi ^ 2) *
          Real.exp (-τ * unitIntervalCosineEigenvalue n) := by rw [hlam_eq]
      _ ≤ ((n : ℝ) ^ 2 * Real.pi ^ 2) * Real.exp (-r * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hexp_le (by positivity)
      _ = Real.pi ^ 2 * ((n : ℝ) ^ 2 * Real.exp (-r * (n : ℝ))) := by ring

/-- The homogeneous restart coefficients satisfy the eigenvalue-weighted
summability condition whenever the restart coefficients are uniformly bounded. -/
theorem restartHomogeneousCoeff_eigenvalue_summable
    {τ M : ℝ} {a₀ : ℕ → ℝ} (hτ : 0 < τ)
    (ha₀ : ∀ n, |a₀ n| ≤ M) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|) := by
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg _) (ha₀ 0)
  have hmajor : Summable (fun n : ℕ =>
      M * (unitIntervalCosineEigenvalue n *
        Real.exp (-τ * unitIntervalCosineEigenvalue n))) :=
    (unitIntervalCosineEigenvalue_mul_exp_summable hτ).mul_left M
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmajor
  · exact mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity) (abs_nonneg _)
  · have hlam_nonneg : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    have hexp_nonneg : 0 ≤ Real.exp (-τ * unitIntervalCosineEigenvalue n) :=
      Real.exp_nonneg _
    calc unitIntervalCosineEigenvalue n *
          |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|
        = unitIntervalCosineEigenvalue n *
            (Real.exp (-τ * unitIntervalCosineEigenvalue n) * |a₀ n|) := by
            rw [abs_mul, abs_of_nonneg hexp_nonneg]
      _ ≤ unitIntervalCosineEigenvalue n *
            (Real.exp (-τ * unitIntervalCosineEigenvalue n) * M) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (ha₀ n) hexp_nonneg) hlam_nonneg
      _ = M * (unitIntervalCosineEigenvalue n *
            Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by ring

/-- Half-step restart coefficient package: bounded restart data plus a T6 time-C¹
source imply the exact `∑ λₙ |bₙ|` condition needed by the cosine C² engine. -/
theorem restartDuhamelCoeff_eigenvalue_summable
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC1 a) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        |restartDuhamelCoeff a₀ a τ n|) := by
  have hhom := restartHomogeneousCoeff_eigenvalue_summable (τ := τ) hτ ha₀
  have hduh := duhamelSpectralCoeff_eigenvalue_summable (t := τ) src hτ
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hhom.add hduh)
  · exact mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity) (abs_nonneg _)
  · have hlam_nonneg : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    calc unitIntervalCosineEigenvalue n *
          |restartDuhamelCoeff a₀ a τ n|
        ≤ unitIntervalCosineEigenvalue n *
            (|Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n| +
              |duhamelSpectralCoeff a τ n|) := by
            exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hlam_nonneg
      _ = unitIntervalCosineEigenvalue n *
            |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n| +
          unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a τ n| := by ring

/-- The restarted coefficient series is globally `C²` in space. -/
theorem restartDuhamelCoeffSeries_contDiff_two
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC1 a) :
    ContDiff ℝ 2 (fun x : ℝ =>
      ∑' n : ℕ, restartDuhamelCoeff a₀ a τ n * cosineMode n x) :=
  cosineCoeffSeries_contDiff_two
    (restartDuhamelCoeff_eigenvalue_summable hτ ha₀ src)

/-- Closed `C²` of the restarted heat+Duhamel formula, explicitly routed
through `intervalDuhamelTerm_closedC2_of_timeC1_source` for the Duhamel term
and the semigroup closed-`C²`/Neumann endpoint package for the homogeneous term.

This is the term-level bridge:
`DuhamelSourceTimeC1 → closedC2(Duhamel term) → closedC2(restart formula)`. -/
theorem restartDuhamelFormula_closedC2_of_timeC1_source
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC1 a) :
    ContDiff ℝ 2
        (fun x : ℝ =>
          unitIntervalCosineHeatValue τ a₀ x +
            ∫ s in (0 : ℝ)..τ, unitIntervalCosineHeatValue (τ - s) (a s) x)
      ∧ deriv
          (fun x : ℝ =>
            unitIntervalCosineHeatValue τ a₀ x +
              ∫ s in (0 : ℝ)..τ, unitIntervalCosineHeatValue (τ - s) (a s) x)
          0 = 0
      ∧ deriv
          (fun x : ℝ =>
            unitIntervalCosineHeatValue τ a₀ x +
              ∫ s in (0 : ℝ)..τ, unitIntervalCosineHeatValue (τ - s) (a s) x)
          1 = 0 := by
  let hhom : ℝ → ℝ := fun x => unitIntervalCosineHeatValue τ a₀ x
  let hduh : ℝ → ℝ := fun x =>
    ∫ s in (0 : ℝ)..τ, unitIntervalCosineHeatValue (τ - s) (a s) x
  have hhomC2 : ContDiff ℝ 2 hhom :=
    ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatValue_contDiff_two
      hτ ha₀
  have hduhClosed := intervalDuhamelTerm_closedC2_of_timeC1_source
    (t := τ) src hτ
  have hduhC2 : ContDiff ℝ 2 hduh := by
    simpa [hduh] using hduhClosed.1
  have hsumC2 : ContDiff ℝ 2 (fun x : ℝ => hhom x + hduh x) :=
    hhomC2.add hduhC2
  refine ⟨by simpa [hhom, hduh] using hsumC2, ?_, ?_⟩
  · have hhomDiff : DifferentiableAt ℝ hhom 0 :=
      hhomC2.differentiable (by norm_num) 0
    have hduhDiff : DifferentiableAt ℝ hduh 0 :=
      hduhC2.differentiable (by norm_num) 0
    have hderiv : HasDerivAt (fun x : ℝ => hhom x + hduh x)
        (deriv hhom 0 + deriv hduh 0) 0 := by
      simpa [Pi.add_apply] using hhomDiff.hasDerivAt.add hduhDiff.hasDerivAt
    change deriv (fun x : ℝ => hhom x + hduh x) 0 = 0
    rw [hderiv.deriv]
    have hhom0 : deriv hhom 0 = 0 := by
      simpa [hhom] using unitIntervalCosineHeatValue_deriv_at_zero hτ ha₀
    have hduh0 : deriv hduh 0 = 0 := by
      simpa [hduh] using hduhClosed.2.1
    rw [hhom0, hduh0]
    ring
  · have hhomDiff : DifferentiableAt ℝ hhom 1 :=
      hhomC2.differentiable (by norm_num) 1
    have hduhDiff : DifferentiableAt ℝ hduh 1 :=
      hduhC2.differentiable (by norm_num) 1
    have hderiv : HasDerivAt (fun x : ℝ => hhom x + hduh x)
        (deriv hhom 1 + deriv hduh 1) 1 := by
      simpa [Pi.add_apply] using hhomDiff.hasDerivAt.add hduhDiff.hasDerivAt
    change deriv (fun x : ℝ => hhom x + hduh x) 1 = 0
    rw [hderiv.deriv]
    have hhom1 : deriv hhom 1 = 0 := by
      simpa [hhom] using unitIntervalCosineHeatValue_deriv_at_one hτ ha₀
    have hduh1 : deriv hduh 1 = 0 := by
      simpa [hduh] using hduhClosed.2.2.1
    rw [hhom1, hduh1]
    ring

/-- Closed-interval `C²` bridge for any slice represented by the restarted
coefficient series. -/
theorem restartDuhamelSlice_conjunct7
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    {w : intervalDomainPoint → ℝ}
    (hτ : 0 < τ)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC1 a)
    (hagree : Set.EqOn (intervalDomainLift w)
        (fun x : ℝ => ∑' n : ℕ, restartDuhamelCoeff a₀ a τ n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hne0 : intervalDomainLift w 0 ≠ 0)
    (hne1 : intervalDomainLift w 1 ≠ 0) :
    ContDiffOn ℝ 2 (intervalDomainLift w) (Set.Icc (0 : ℝ) 1)
      ∧ deriv (intervalDomainLift w) 0 = 0
      ∧ deriv (intervalDomainLift w) 1 = 0 :=
  ShenWork.IntervalCosineSliceRegularity.intervalDomainCosineSlice_conjunct7
    (restartDuhamelCoeff_eigenvalue_summable hτ ha₀ src) hagree hne0 hne1

/-- Left Neumann limit for a slice represented by the restarted coefficient
series. -/
theorem restartDuhamelSlice_neumann_limit_left
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    {w : intervalDomainPoint → ℝ}
    (hτ : 0 < τ)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC1 a)
    (hagree : Set.EqOn (intervalDomainLift w)
        (fun x : ℝ => ∑' n : ℕ, restartDuhamelCoeff a₀ a τ n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1)) :
    Filter.Tendsto (deriv (intervalDomainLift w))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
  ShenWork.IntervalCosineSliceRegularity.intervalDomainCosineSlice_neumann_limit_left
    (restartDuhamelCoeff_eigenvalue_summable hτ ha₀ src) hagree

/-- Right Neumann limit for a slice represented by the restarted coefficient
series. -/
theorem restartDuhamelSlice_neumann_limit_right
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    {w : intervalDomainPoint → ℝ}
    (hτ : 0 < τ)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC1 a)
    (hagree : Set.EqOn (intervalDomainLift w)
        (fun x : ℝ => ∑' n : ℕ, restartDuhamelCoeff a₀ a τ n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1)) :
    Filter.Tendsto (deriv (intervalDomainLift w))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) :=
  ShenWork.IntervalCosineSliceRegularity.intervalDomainCosineSlice_neumann_limit_right
    (restartDuhamelCoeff_eigenvalue_summable hτ ha₀ src) hagree

/-- A concrete restarted cosine representation of one spatial slice.  This is the
remaining frontier after the coefficient summability bridge: it records the
half-step gap, bounded restart coefficients, a T6 time-C¹ source package, and
the actual agreement of the slice with the resulting cosine series. -/
structure RestartCosineRepresentation (w : intervalDomainPoint → ℝ) where
  τ : ℝ
  hτ : 0 < τ
  M : ℝ
  a₀ : ℕ → ℝ
  a : ℝ → ℕ → ℝ
  ha₀ : ∀ n, |a₀ n| ≤ M
  src : DuhamelSourceTimeC1 a
  hagree : Set.EqOn (intervalDomainLift w)
    (fun x : ℝ => ∑' n : ℕ, restartDuhamelCoeff a₀ a τ n * cosineMode n x)
    (Set.Icc (0 : ℝ) 1)

/-- A restarted cosine representation gives the closed-interval `C²` and endpoint
derivative package for a positive slice. -/
theorem RestartCosineRepresentation.conjunct7
    {w : intervalDomainPoint → ℝ} (R : RestartCosineRepresentation w)
    (hne0 : intervalDomainLift w 0 ≠ 0)
    (hne1 : intervalDomainLift w 1 ≠ 0) :
    ContDiffOn ℝ 2 (intervalDomainLift w) (Set.Icc (0 : ℝ) 1)
      ∧ deriv (intervalDomainLift w) 0 = 0
      ∧ deriv (intervalDomainLift w) 1 = 0 :=
  restartDuhamelSlice_conjunct7 R.hτ R.ha₀ R.src R.hagree hne0 hne1

/-- A restarted cosine representation gives the genuine left one-sided Neumann
limit. -/
theorem RestartCosineRepresentation.neumann_limit_left
    {w : intervalDomainPoint → ℝ} (R : RestartCosineRepresentation w) :
    Filter.Tendsto (deriv (intervalDomainLift w))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
  restartDuhamelSlice_neumann_limit_left R.hτ R.ha₀ R.src R.hagree

/-- A restarted cosine representation gives the genuine right one-sided Neumann
limit. -/
theorem RestartCosineRepresentation.neumann_limit_right
    {w : intervalDomainPoint → ℝ} (R : RestartCosineRepresentation w) :
    Filter.Tendsto (deriv (intervalDomainLift w))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) :=
  restartDuhamelSlice_neumann_limit_right R.hτ R.ha₀ R.src R.hagree

/-- Every positive-time slice has a restarted cosine representation. -/
def HasRestartCosineRepresentations (T : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t, 0 < t → t < T → Nonempty (RestartCosineRepresentation (u t))

/-- The half-step restart coefficients of a gradient mild solution, obtained by
taking the Neumann cosine coefficients of the slice `u(t/2)`. -/
def gradientMildHalfStepInitialCoeff
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) (t : ℝ) : ℕ → ℝ :=
  ShenWork.IntervalNeumannFullKernel.cosineCoeffs
    (intervalDomainLift (D.u (t / 2)))

/-- Uniform boundedness of the half-step restart coefficients.  This is the
easy part of the restart construction: the `L¹` coefficient bound plus
`GradientMildSolutionData.hbound` gives `|a₀ₙ| ≤ 2M`. -/
theorem gradientMildHalfStepInitialCoeff_abs_le
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t < D.T) :
    ∀ n, |gradientMildHalfStepInitialCoeff D t n| ≤ 2 * D.M := by
  intro n
  have ht_half_pos : 0 < t / 2 := by positivity
  have ht_half_le : t / 2 ≤ D.T := by
    have ht_le_T : t ≤ D.T := le_of_lt htT
    nlinarith
  have hcont_sub :
      Continuous (D.u (t / 2)) :=
    D.hcont (t / 2) ht_half_pos ht_half_le
  have hcont_on :
      ContinuousOn (fun x : ℝ =>
        ((intervalDomainLift (D.u (t / 2)) x : ℝ) : ℂ))
        (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq :
        Set.restrict (Set.Icc (0 : ℝ) 1)
            (fun x : ℝ =>
              ((intervalDomainLift (D.u (t / 2)) x : ℝ) : ℂ)) =
          fun x : intervalDomainPoint =>
            ((D.u (t / 2) x : ℝ) : ℂ) := by
      ext x
      change ((intervalDomainLift (D.u (t / 2)) x.1 : ℝ) : ℂ) =
        ((D.u (t / 2) x : ℝ) : ℂ)
      simp [intervalDomainLift, x.2]
    rw [heq]
    exact Complex.continuous_ofReal.comp hcont_sub
  have hfint :
      IntervalIntegrable
        (fun x : ℝ => ((intervalDomainLift (D.u (t / 2)) x : ℝ) : ℂ))
        volume (0 : ℝ) 1 :=
    (by
      refine ContinuousOn.intervalIntegrable ?_
      rwa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)])
  have hcoeff :=
    ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff_abs_le_two_integral_norm
      (f := fun x : ℝ => ((intervalDomainLift (D.u (t / 2)) x : ℝ) : ℂ))
      hfint n
  have hM_nonneg : 0 ≤ D.M := le_of_lt D.hM
  have hnorm_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖((intervalDomainLift (D.u (t / 2)) x : ℝ) : ℂ)‖ ≤ D.M := by
    intro x hx
    have hnorm_eq : ∀ r : ℝ, ‖(r : ℂ)‖ = |r| := by
      intro r
      have hsq : ‖(r : ℂ)‖ ^ 2 = |r| ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_ofReal]
        rw [sq_abs]
        ring
      have hnon1 : 0 ≤ ‖(r : ℂ)‖ := norm_nonneg _
      have hnon2 : 0 ≤ |r| := abs_nonneg _
      nlinarith
    have hxb : |D.u (t / 2) ⟨x, hx⟩| ≤ D.M :=
      D.hbound (t / 2) ht_half_pos ht_half_le ⟨x, hx⟩
    simpa [intervalDomainLift, hx, hnorm_eq] using hxb
  have hint_norm :
      IntervalIntegrable
        (fun x : ℝ =>
          ‖((intervalDomainLift (D.u (t / 2)) x : ℝ) : ℂ)‖)
        volume (0 : ℝ) 1 :=
    hfint.norm
  have hintegral_le :
      ∫ x in (0 : ℝ)..1,
          ‖((intervalDomainLift (D.u (t / 2)) x : ℝ) : ℂ)‖ ≤ D.M := by
    have hconst_int :
        IntervalIntegrable (fun _ : ℝ => D.M) volume (0 : ℝ) 1 :=
      intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on
      (show (0 : ℝ) ≤ 1 by norm_num) hint_norm hconst_int hnorm_bound
    have hconst :
        ∫ x in (0 : ℝ)..1, D.M = D.M := by
      simp
    simpa [hconst] using hmono
  calc
    |gradientMildHalfStepInitialCoeff D t n|
        ≤ 2 * ∫ x in (0 : ℝ)..1,
            ‖((intervalDomainLift (D.u (t / 2)) x : ℝ) : ℂ)‖ := by
          simpa [gradientMildHalfStepInitialCoeff,
            ShenWork.IntervalNeumannFullKernel.cosineCoeffs] using hcoeff
    _ ≤ 2 * D.M := by nlinarith

/-- The two analytic half-step obligations needed to restart a gradient mild
solution as a classical cosine-Duhamel series.  `src` is the T6 time-`C¹`
coefficient package for the restarted source; `hagree` is the exact equality of
the target slice with the corresponding half-step cosine series. -/
structure GradientMildHalfStepRestartData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) where
  a : ℝ → ℝ → ℕ → ℝ
  src : ∀ t, 0 < t → t < D.T → DuhamelSourceTimeC1 (a t)
  hagree : ∀ t, 0 < t → t < D.T →
    Set.EqOn (intervalDomainLift (D.u t))
      (fun x : ℝ =>
        ∑' n : ℕ,
          restartDuhamelCoeff (gradientMildHalfStepInitialCoeff D t)
            (a t) (t / 2) n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1)

/-- Half-step restart data with the `DuhamelSourceTimeC1` obligation replaced by
the H²-Neumann/time-C¹ coefficient hypotheses consumed by
`duhamelSourceTimeC1_of_H2Neumann_timeC1`.

The remaining genuinely algebraic restart obligation is `hagree`: identifying
the mild slice with the corresponding restarted cosine-Duhamel series. -/
structure GradientMildHalfStepH2SourceData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) where
  source : ℝ → ℝ → ℝ → ℝ
  C : ℝ → ℝ
  hC : ∀ t, 0 < t → t < D.T → 0 ≤ C t
  hH2 : ∀ t, 0 < t → t < D.T →
    ∀ s, 0 ≤ s → IntervalWeakH2Neumann (source t s)
  hdecay : ∀ t, 0 < t → t < D.T →
    ∀ s, 0 ≤ s → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (source t s) k| ≤ C t / ((k : ℝ) * Real.pi) ^ 2
  adot : ℝ → ℝ → ℕ → ℝ
  hderiv : ∀ t, 0 < t → t < D.T →
    ∀ s n, HasDerivAt
      (fun r : ℝ => cosineCoeffs (source t r) n) (adot t s n) s
  hadotcont : ∀ t, 0 < t → t < D.T →
    ∀ n, Continuous (fun s : ℝ => adot t s n)
  Mdot : ℝ → ℝ
  hMdot : ∀ t, 0 < t → t < D.T →
    ∀ s, 0 ≤ s → ∀ n, |adot t s n| ≤ Mdot t
  ha0_bound : ∀ t, 0 < t → t < D.T →
    ∀ s, 0 ≤ s → |cosineCoeffs (source t s) 0| ≤ C t
  hagree : ∀ t, 0 < t → t < D.T →
    Set.EqOn (intervalDomainLift (D.u t))
      (fun x : ℝ =>
        ∑' n : ℕ,
          restartDuhamelCoeff (gradientMildHalfStepInitialCoeff D t)
            (fun s n => cosineCoeffs (source t s) n) (t / 2) n *
            cosineMode n x)
      (Set.Icc (0 : ℝ) 1)

/-- H²-Neumann/time-C¹ half-step source data produces the older restart package:
the `src` field is supplied by
`duhamelSourceTimeC1_of_H2Neumann_timeC1`. -/
noncomputable def gradientMildHalfStepRestartData_of_H2SourceData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (S : GradientMildHalfStepH2SourceData D) :
    GradientMildHalfStepRestartData D where
  a := fun t s n => cosineCoeffs (S.source t s) n
  src := by
    intro t ht htT
    exact duhamelSourceTimeC1_of_H2Neumann_timeC1
      (S.hH2 t ht htT) (S.hC t ht htT)
      (S.hdecay t ht htT) (S.hderiv t ht htT)
      (S.hadotcont t ht htT) (S.hMdot t ht htT)
      (S.ha0_bound t ht htT)
  hagree := S.hagree

/-- Construct `HasRestartCosineRepresentations` for a `GradientMildSolutionData`
from the exact half-step source regularity and cosine-series agreement. -/
theorem hasRestartCosineRepresentations_of_gradientMildHalfStepRestartData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (R : GradientMildHalfStepRestartData D) :
    HasRestartCosineRepresentations D.T D.u := by
  intro t ht htT
  refine ⟨?_⟩
  refine
    { τ := t / 2
      hτ := ?_
      M := 2 * D.M
      a₀ := gradientMildHalfStepInitialCoeff D t
      a := R.a t
      ha₀ := gradientMildHalfStepInitialCoeff_abs_le D ht htT
      src := R.src t ht htT
      hagree := R.hagree t ht htT }
  positivity

/-- Construct `HasRestartCosineRepresentations` directly from H²-Neumann/time-C¹
half-step source data plus the restarted cosine-series agreement. -/
theorem hasRestartCosineRepresentations_of_gradientMildHalfStepH2SourceData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (S : GradientMildHalfStepH2SourceData D) :
    HasRestartCosineRepresentations D.T D.u :=
  hasRestartCosineRepresentations_of_gradientMildHalfStepRestartData D
    (gradientMildHalfStepRestartData_of_H2SourceData D S)

/-- Discharge the closed-interval `ContDiffOn` family from restarted cosine
representations of the mild slices. -/
theorem gradientMild_contDiffOn_of_restartCosineRepresentations
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (H : HasRestartCosineRepresentations D.T D.u) :
    ∀ t, 0 < t → t < D.T →
      ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1) := by
  intro t ht0 htT
  have h0 : intervalDomainLift (D.u t) 0 ≠ 0 := by
    have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
    simp only [intervalDomainLift, hmem, dif_pos]
    exact ne_of_gt (D.hpos t ht0 (le_of_lt htT) ⟨0, hmem⟩)
  have h1 : intervalDomainLift (D.u t) 1 ≠ 0 := by
    have hmem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
    simp only [intervalDomainLift, hmem, dif_pos]
    exact ne_of_gt (D.hpos t ht0 (le_of_lt htT) ⟨1, hmem⟩)
  exact ((Classical.choice (H t ht0 htT)).conjunct7 h0 h1).1

/-- Discharge the closed-interval spatial `C²` package, including endpoint
derivative values, from restarted cosine representations of the mild slices. -/
theorem gradientMild_closedC2_endpointDerivs_of_restartCosineRepresentations
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (H : HasRestartCosineRepresentations D.T D.u) :
    ∀ t, 0 < t → t < D.T →
      ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1)
        ∧ deriv (intervalDomainLift (D.u t)) 0 = 0
        ∧ deriv (intervalDomainLift (D.u t)) 1 = 0 := by
  intro t ht0 htT
  have h0 : intervalDomainLift (D.u t) 0 ≠ 0 := by
    have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
    simp only [intervalDomainLift, hmem, dif_pos]
    exact ne_of_gt (D.hpos t ht0 (le_of_lt htT) ⟨0, hmem⟩)
  have h1 : intervalDomainLift (D.u t) 1 ≠ 0 := by
    have hmem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
    simp only [intervalDomainLift, hmem, dif_pos]
    exact ne_of_gt (D.hpos t ht0 (le_of_lt htT) ⟨1, hmem⟩)
  exact (Classical.choice (H t ht0 htT)).conjunct7 h0 h1

/-- Half-step restart data discharges the closed-interval spatial `C²` package,
including endpoint derivative values. -/
theorem gradientMild_closedC2_endpointDerivs_of_halfStepRestartData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (R : GradientMildHalfStepRestartData D) :
    ∀ t, 0 < t → t < D.T →
      ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1)
        ∧ deriv (intervalDomainLift (D.u t)) 0 = 0
        ∧ deriv (intervalDomainLift (D.u t)) 1 = 0 :=
  gradientMild_closedC2_endpointDerivs_of_restartCosineRepresentations D
    (hasRestartCosineRepresentations_of_gradientMildHalfStepRestartData D R)

/-- H²/time-`C¹` half-step source data discharges the closed-interval spatial
`C²` package, including endpoint derivative values. -/
theorem gradientMild_closedC2_endpointDerivs_of_halfStepH2SourceData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (S : GradientMildHalfStepH2SourceData D) :
    ∀ t, 0 < t → t < D.T →
      ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1)
        ∧ deriv (intervalDomainLift (D.u t)) 0 = 0
        ∧ deriv (intervalDomainLift (D.u t)) 1 = 0 :=
  gradientMild_closedC2_endpointDerivs_of_halfStepRestartData D
    (gradientMildHalfStepRestartData_of_H2SourceData D S)

/-- Half-step restart data simultaneously gives closed-interval `C²` endpoint
data and the restart-cosine representation package. -/
theorem gradientMild_closedC2_endpointDerivs_and_hasRestart_of_halfStepRestartData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (R : GradientMildHalfStepRestartData D) :
    (∀ t, 0 < t → t < D.T →
      ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1)
        ∧ deriv (intervalDomainLift (D.u t)) 0 = 0
        ∧ deriv (intervalDomainLift (D.u t)) 1 = 0)
      ∧ HasRestartCosineRepresentations D.T D.u := by
  let H := hasRestartCosineRepresentations_of_gradientMildHalfStepRestartData D R
  exact
    ⟨gradientMild_closedC2_endpointDerivs_of_restartCosineRepresentations D H, H⟩

/-- H²/time-`C¹` source data simultaneously gives closed-interval `C²`
endpoint data and the restart-cosine representation package. -/
theorem gradientMild_closedC2_endpointDerivs_and_hasRestart_of_halfStepH2SourceData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (S : GradientMildHalfStepH2SourceData D) :
    (∀ t, 0 < t → t < D.T →
      ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1)
        ∧ deriv (intervalDomainLift (D.u t)) 0 = 0
        ∧ deriv (intervalDomainLift (D.u t)) 1 = 0)
      ∧ HasRestartCosineRepresentations D.T D.u :=
  gradientMild_closedC2_endpointDerivs_and_hasRestart_of_halfStepRestartData D
    (gradientMildHalfStepRestartData_of_H2SourceData D S)

/-- Discharge the left Neumann-limit family from restarted cosine
representations of the mild slices. -/
theorem gradientMild_neumann_left_of_restartCosineRepresentations
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (H : HasRestartCosineRepresentations D.T D.u) :
    ∀ t, 0 < t → t < D.T →
      Filter.Tendsto (deriv (intervalDomainLift (D.u t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  intro t ht0 htT
  exact (Classical.choice (H t ht0 htT)).neumann_limit_left

/-- Discharge the right Neumann-limit family from restarted cosine
representations of the mild slices. -/
theorem gradientMild_neumann_right_of_restartCosineRepresentations
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (H : HasRestartCosineRepresentations D.T D.u) :
    ∀ t, 0 < t → t < D.T →
      Filter.Tendsto (deriv (intervalDomainLift (D.u t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  intro t ht0 htT
  exact (Classical.choice (H t ht0 htT)).neumann_limit_right

/-- The exact triple of hypotheses consumed by `mildChemical_ellipticPDE` and
`mildSolution_neumannBC`, discharged from restarted cosine representations. -/
theorem gradientMild_closedC2_neumann_of_restartCosineRepresentations
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (H : HasRestartCosineRepresentations D.T D.u) :
    (∀ t, 0 < t → t < D.T →
      ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1))
    ∧ (∀ t, 0 < t → t < D.T →
      Filter.Tendsto (deriv (intervalDomainLift (D.u t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    ∧ (∀ t, 0 < t → t < D.T →
      Filter.Tendsto (deriv (intervalDomainLift (D.u t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)) :=
  ⟨gradientMild_contDiffOn_of_restartCosineRepresentations D H,
    gradientMild_neumann_left_of_restartCosineRepresentations D H,
    gradientMild_neumann_right_of_restartCosineRepresentations D H⟩

/-- Half-step restart data gives the exact closed-`C²`/Neumann triple consumed
downstream by the mild-to-classical bridge. -/
theorem gradientMild_closedC2_neumann_of_halfStepRestartData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (R : GradientMildHalfStepRestartData D) :
    (∀ t, 0 < t → t < D.T →
      ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1))
    ∧ (∀ t, 0 < t → t < D.T →
      Filter.Tendsto (deriv (intervalDomainLift (D.u t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    ∧ (∀ t, 0 < t → t < D.T →
      Filter.Tendsto (deriv (intervalDomainLift (D.u t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)) :=
  gradientMild_closedC2_neumann_of_restartCosineRepresentations D
    (hasRestartCosineRepresentations_of_gradientMildHalfStepRestartData D R)

/-- H²/time-`C¹` half-step source data gives the exact closed-`C²`/Neumann
triple consumed downstream by the mild-to-classical bridge. -/
theorem gradientMild_closedC2_neumann_of_halfStepH2SourceData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (S : GradientMildHalfStepH2SourceData D) :
    (∀ t, 0 < t → t < D.T →
      ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1))
    ∧ (∀ t, 0 < t → t < D.T →
      Filter.Tendsto (deriv (intervalDomainLift (D.u t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    ∧ (∀ t, 0 < t → t < D.T →
      Filter.Tendsto (deriv (intervalDomainLift (D.u t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)) :=
  gradientMild_closedC2_neumann_of_halfStepRestartData D
    (gradientMildHalfStepRestartData_of_H2SourceData D S)

end ShenWork.IntervalMildRegularityBootstrap
