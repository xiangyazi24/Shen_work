/-
  ShenWork/Paper2/IntervalHuRestartCoeffEnvelope.lean

  Local window envelopes for restart coefficients selected through `Hu`.

  This isolates the spectral estimate needed before the later finite-cover
  construction of compact Hu coefficient envelopes.
-/
import ShenWork.Paper2.IntervalHuRestartCoeffIdentity
import ShenWork.Paper2.IntervalPicardLimitRestartBdd

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalPicardIterateRestart (cosineCoeffs_of_l1_cosineSeries)
open ShenWork.IntervalMildRegularityBootstrap
  (unitIntervalCosineEigenvalue_mul_exp_summable)

noncomputable section

namespace ShenWork.Paper2.ResolverSourceWindowInput

/-- Chart-local eigenvalue envelope for restart coefficients on a window where
`ε ≤ τ`. -/
def restartCoeffWindowEigEnv
    (M : ℝ) {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    (ε : ℝ) (n : ℕ) : ℝ :=
  M * (unitIntervalCosineEigenvalue n *
    Real.exp (-ε * unitIntervalCosineEigenvalue n)) + src.envelope n

/-- The chart-local restart envelope is summable for every positive window
lower bound. -/
theorem restartCoeffWindowEigEnv_summable
    {M ε : ℝ} {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    (hε : 0 < ε) :
    Summable (restartCoeffWindowEigEnv M src ε) := by
  unfold restartCoeffWindowEigEnv
  exact ((unitIntervalCosineEigenvalue_mul_exp_summable hε).mul_left M).add
    src.henv_summable

/-- The chart-local restart envelope is nonnegative when the initial coefficient
bound is nonnegative. -/
theorem restartCoeffWindowEigEnv_nonneg
    {M ε : ℝ} {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    (hM : 0 ≤ M) (n : ℕ) :
    0 ≤ restartCoeffWindowEigEnv M src ε n := by
  have hEig : 0 ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue
    positivity
  have henv : 0 ≤ src.envelope n :=
    le_trans (abs_nonneg _) (src.henv_bound 0 le_rfl n)
  unfold restartCoeffWindowEigEnv
  exact add_nonneg (mul_nonneg hM (mul_nonneg hEig (Real.exp_nonneg _))) henv

/-- A single restart chart gives a uniform eigenvalue-weighted coefficient
envelope on every subwindow bounded away from its restart time. -/
theorem localRestartCoeff_eigen_abs_le_window
    {M ε τ : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC1 a)
    (hε : 0 < ε) (hετ : ε ≤ τ) (n : ℕ) :
    unitIntervalCosineEigenvalue n * |localRestartCoeff a₀ a τ n|
      ≤ restartCoeffWindowEigEnv M src ε n := by
  have hτ : 0 < τ := lt_of_lt_of_le hε hετ
  have hEig : 0 ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue
    positivity
  have hcont_a : Continuous (fun s : ℝ => a s n) :=
    continuous_iff_continuousAt.2 (fun s => (src.hderiv s n).continuousAt)
  have hduh :
      unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a τ n| ≤ src.envelope n :=
    ShenWork.IntervalPicardLimitRestartBdd.eigenvalue_mul_abs_duhamelSpectralCoeff_le_of_bound
      (a := a) hτ n
      (fun s hs _hst => src.henv_bound s hs n)
      hcont_a.continuousOn
  have hhom :
      unitIntervalCosineEigenvalue n *
          |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|
        ≤ M * (unitIntervalCosineEigenvalue n *
          Real.exp (-ε * unitIntervalCosineEigenvalue n)) := by
    rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    have hexp :
        Real.exp (-τ * unitIntervalCosineEigenvalue n) ≤
          Real.exp (-ε * unitIntervalCosineEigenvalue n) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc unitIntervalCosineEigenvalue n *
          (Real.exp (-τ * unitIntervalCosineEigenvalue n) * |a₀ n|)
        ≤ unitIntervalCosineEigenvalue n *
            (Real.exp (-ε * unitIntervalCosineEigenvalue n) * M) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul hexp (ha₀ n) (abs_nonneg _) (Real.exp_nonneg _)) hEig
      _ = M * (unitIntervalCosineEigenvalue n *
            Real.exp (-ε * unitIntervalCosineEigenvalue n)) := by
          ring
  calc
    unitIntervalCosineEigenvalue n * |localRestartCoeff a₀ a τ n|
        ≤ unitIntervalCosineEigenvalue n *
            (|Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n| +
              |duhamelSpectralCoeff a τ n|) := by
          exact mul_le_mul_of_nonneg_left
            (by simp only [localRestartCoeff]; exact abs_add_le _ _) hEig
    _ = unitIntervalCosineEigenvalue n *
          |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n| +
          unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a τ n| := by ring
    _ ≤ M * (unitIntervalCosineEigenvalue n *
          Real.exp (-ε * unitIntervalCosineEigenvalue n)) + src.envelope n :=
          add_le_add hhom hduh
    _ = restartCoeffWindowEigEnv M src ε n := by
          rfl

/-- If a concrete restart chart represents the slice at `σ`, its coefficients
are the same as the canonical `Hu`-selected coefficients. -/
theorem huRestartCoeff_eq_chartCoeff_of_agree
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hu : HasTimeNeighborhoodSpectralAgreement T u)
    {σ M offset : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hσ0 : 0 < σ) (hσT : σ < T)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC1 a)
    (hτ : 0 < σ - offset)
    (hagree : Set.EqOn (intervalDomainLift (u σ))
      (fun x => ∑' n, localRestartCoeff a₀ a (σ - offset) n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1))
    (k : ℕ) :
    huRestartCoeff Hu σ k = localRestartCoeff a₀ a (σ - offset) k := by
  have hbsum :
      Summable (fun n =>
        unitIntervalCosineEigenvalue n * |localRestartCoeff a₀ a (σ - offset) n|) :=
    ShenWork.IntervalResolverSpectralJointC2Producer.localRestartCoeff_eigenvalue_summable
      (τ := σ - offset) (M := M) (a₀ := a₀) (a := a) hτ ha₀ src
  have habs : Summable (fun n => |localRestartCoeff a₀ a (σ - offset) n|) :=
    summable_abs_of_eigenvalue_abs_summable hbsum
  have hcoeff_chart :
      cosineCoeffs (intervalDomainLift (u σ)) k =
        localRestartCoeff a₀ a (σ - offset) k := by
    rw [ShenWork.Paper2.cosineCoeffs_congr_on_Icc hagree k]
    exact cosineCoeffs_of_l1_cosineSeries habs k
  have hcoeff_hu :
      cosineCoeffs (intervalDomainLift (u σ)) k = huRestartCoeff Hu σ k :=
    cosineCoeffs_eq_huRestartCoeff Hu σ hσ0 hσT k
  exact hcoeff_hu.symm.trans hcoeff_chart

/-- A chart agreeing with the slice gives a local window envelope for the
canonical `Hu` coefficients. -/
theorem huRestartCoeff_eigen_abs_le_chart_window
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hu : HasTimeNeighborhoodSpectralAgreement T u)
    {σ M offset ε : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hσ0 : 0 < σ) (hσT : σ < T)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC1 a)
    (hε : 0 < ε) (hετ : ε ≤ σ - offset)
    (hagree : Set.EqOn (intervalDomainLift (u σ))
      (fun x => ∑' n, localRestartCoeff a₀ a (σ - offset) n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1))
    (n : ℕ) :
    unitIntervalCosineEigenvalue n * |huRestartCoeff Hu σ n|
      ≤ restartCoeffWindowEigEnv M src ε n := by
  have hτ : 0 < σ - offset := lt_of_lt_of_le hε hετ
  rw [huRestartCoeff_eq_chartCoeff_of_agree Hu hσ0 hσT ha₀ src hτ hagree n]
  exact localRestartCoeff_eigen_abs_le_window ha₀ src hε hετ n

end ShenWork.Paper2.ResolverSourceWindowInput
