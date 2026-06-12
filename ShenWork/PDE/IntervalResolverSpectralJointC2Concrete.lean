import ShenWork.PDE.IntervalResolverSpectralJointC2CutoffBounds

open Filter Topology Set

noncomputable section

namespace ShenWork.IntervalResolverSpectralJointC2Concrete

open ShenWork.IntervalResolverJointC2
open ShenWork.IntervalResolverSpectralJointC2Producer
  (localRestartCoeff_eigenvalue_summable)
open ShenWork.IntervalResolverSpectralTimeC2
  (DuhamelSourceTimeC2Coeff localRestartCoeff_contDiff_two)
open ShenWork.IntervalResolverSpectralJointC2Cutoff
open ShenWork.IntervalResolverSpectralJointC2CutoffBounds
open ShenWork.IntervalDuhamelClosedC2 (cosineCoeffSeries_grad_hasDerivAt)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.CosineSpectrum (cosineMode cosineMode_deriv)

/-- Left transition point for the concrete restart cutoff. -/
def restartCutoffLeft (offset s : ℝ) : ℝ :=
  offset + (s - offset) / 3

/-- Right transition point for the concrete restart cutoff. -/
def restartCutoffRight (offset s : ℝ) : ℝ :=
  offset + 2 * (s - offset) / 3

/-- Concrete smooth cutoff supported after the restart offset and equal to one
near the target time. -/
def restartSmoothCutoff (offset s : ℝ) : ℝ → ℝ :=
  smoothRightCutoff (restartCutoffLeft offset s) (restartCutoffRight offset s)

theorem restartCutoffLeft_lt_right {offset s : ℝ} (hτ : 0 < s - offset) :
    restartCutoffLeft offset s < restartCutoffRight offset s := by
  unfold restartCutoffLeft restartCutoffRight
  linarith

theorem restartCutoffRight_lt {offset s : ℝ} (hτ : 0 < s - offset) :
    restartCutoffRight offset s < s := by
  unfold restartCutoffRight
  linarith

theorem restartSmoothCutoff_contDiff {offset s : ℝ} :
    ContDiff ℝ (2 : ℕ∞) (restartSmoothCutoff offset s) :=
  smoothRightCutoff_contDiff

theorem restartSmoothCutoff_eventually_eq_one {offset s : ℝ}
    (hτ : 0 < s - offset) :
    restartSmoothCutoff offset s =ᶠ[𝓝 s] fun _ : ℝ => 1 :=
  smoothRightCutoff_eventually_eq_one
    (restartCutoffLeft_lt_right hτ) (restartCutoffRight_lt hτ)

/-- Concrete spatial-gradient summand for the restart resolver series. -/
def resolverSpectralConcreteGradTerm
    (a₀ : ℕ → ℝ) (a : ℝ → ℕ → ℝ) (offset : ℝ)
    (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q =>
    localRestartCoeff a₀ a (q.1 - offset) n *
      deriv (cosineMode n) q.2

theorem cutoffValueTerm_restartSmoothCutoff_contDiff
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (n : ℕ) :
    ContDiff ℝ (2 : ℕ∞)
      (cutoffValueTerm (restartSmoothCutoff offset s) a₀ a offset n) := by
  have hφ : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => restartSmoothCutoff offset s q.1) :=
    restartSmoothCutoff_contDiff.comp contDiff_fst
  have hcoeff : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => localRestartCoeff a₀ a (q.1 - offset) n) :=
    (localRestartCoeff_contDiff_two (a₀ := a₀) src n).comp
      (contDiff_fst.sub contDiff_const)
  have hcos : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => cosineMode n q.2) := by
    have hcos₀ : ContDiff ℝ (2 : ℕ∞) (cosineMode n) := by
      unfold cosineMode
      fun_prop
    exact hcos₀.comp contDiff_snd
  change ContDiff ℝ (2 : ℕ∞)
    (fun q : ℝ × ℝ =>
      (restartSmoothCutoff offset s q.1 *
        localRestartCoeff a₀ a (q.1 - offset) n) * cosineMode n q.2)
  exact (hφ.mul hcoeff).mul hcos

theorem resolverSpectralConcreteGradTerm_contDiff
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset : ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (n : ℕ) :
    ContDiff ℝ (2 : ℕ∞)
      (resolverSpectralConcreteGradTerm a₀ a offset n) := by
  have hcoeff : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => localRestartCoeff a₀ a (q.1 - offset) n) :=
    (localRestartCoeff_contDiff_two (a₀ := a₀) src n).comp
      (contDiff_fst.sub contDiff_const)
  have hderivCos₀ : ContDiff ℝ (2 : ℕ∞)
      (fun y : ℝ => deriv (cosineMode n) y) := by
    have hEq :
        (fun y : ℝ => deriv (cosineMode n) y) =
          fun y : ℝ =>
            -((n : ℝ) * Real.pi) *
              Real.sin ((n : ℝ) * Real.pi * y) := by
      funext y
      rw [cosineMode_deriv]
    rw [hEq]
    fun_prop
  have hderivCos : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => deriv (cosineMode n) q.2) :=
    hderivCos₀.comp contDiff_snd
  simpa [resolverSpectralConcreteGradTerm] using hcoeff.mul hderivCos

theorem cutoffGradTerm_restartSmoothCutoff_contDiff
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (n : ℕ) :
    ContDiff ℝ (2 : ℕ∞)
      (cutoffGradTerm (restartSmoothCutoff offset s)
        (resolverSpectralConcreteGradTerm a₀ a offset) n) := by
  have hφ : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => restartSmoothCutoff offset s q.1) :=
    restartSmoothCutoff_contDiff.comp contDiff_fst
  simpa [cutoffGradTerm] using
    hφ.mul (resolverSpectralConcreteGradTerm_contDiff
      (a₀ := a₀) (offset := offset) src n)

theorem resolverSpectralGradSeries_eventuallyEq_concreteGradTerm
    {a₀ : ℕ → ℝ} {M : ℝ} {a : ℝ → ℕ → ℝ} {offset s x : ℝ}
    (hτ : 0 < s - offset) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    resolverSpectralGradSeries a₀ a offset =ᶠ[𝓝 (s, x)]
      fun q : ℝ × ℝ =>
        ∑' n : ℕ, resolverSpectralConcreteGradTerm a₀ a offset n q := by
  have hpos :
      {q : ℝ × ℝ | 0 < q.1 - offset} ∈ 𝓝 (s, x) := by
    exact (isOpen_lt continuous_const (continuous_fst.sub continuous_const)).mem_nhds hτ
  filter_upwards [hpos] with q hq
  have hsum :
      Summable (fun n : ℕ =>
        unitIntervalCosineEigenvalue n *
          |localRestartCoeff a₀ a (q.1 - offset) n|) :=
    localRestartCoeff_eigenvalue_summable
      (τ := q.1 - offset) (M := M) (a₀ := a₀) (a := a)
      hq ha₀ src.toTimeC1
  unfold resolverSpectralGradSeries
  change
    deriv
        (fun y : ℝ =>
          ∑' n : ℕ,
            localRestartCoeff a₀ a (q.1 - offset) n * cosineMode n y)
        q.2 =
      ∑' n : ℕ, resolverSpectralConcreteGradTerm a₀ a offset n q
  rw [(cosineCoeffSeries_grad_hasDerivAt hsum q.2).deriv]
  apply tsum_congr
  intro n
  simp [resolverSpectralConcreteGradTerm, cosineMode_deriv, mul_assoc]

/-- Value-side concrete majorant used by the restart cutoff instantiation. -/
def concreteRestartValueMajorant
    (a₀ : ℕ → ℝ) (a : ℝ → ℕ → ℝ) (src : DuhamelSourceTimeC2Coeff a)
    (offset s : ℝ) (_k n : ℕ) : ℝ :=
  restartValueC2Majorant a₀ a src.toTimeC1.adot (s - offset) n

/-- Gradient-side concrete majorant used by the restart cutoff instantiation. -/
def concreteRestartGradMajorant
    (a₀ : ℕ → ℝ) (a : ℝ → ℕ → ℝ) (src : DuhamelSourceTimeC2Coeff a)
    (offset s : ℝ) (_k n : ℕ) : ℝ :=
  restartGradC2Majorant a₀ a src.toTimeC1.adot (s - offset) n

theorem concreteRestartValueMajorant_summable
    {a₀ : ℕ → ℝ} {M : ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (hτ : 0 < s - offset) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (concreteRestartValueMajorant a₀ a src offset s k) := by
  intro _k _hk
  exact restartValueC2Majorant_summable hτ ha₀ src

theorem concreteRestartGradMajorant_summable
    {a₀ : ℕ → ℝ} {M : ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (hτ : 0 < s - offset) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (concreteRestartGradMajorant a₀ a src offset s k) := by
  intro _k _hk
  exact restartGradC2Majorant_summable hτ ha₀ src

/-- Concrete cutoff instantiation of the generic producer, with only the two
global iterated-derivative majorant bounds left explicit. -/
theorem resolverSpectralJointC2At_of_restartSmoothCutoff_bounds
    {a₀ : ℕ → ℝ} {M : ℝ} {a : ℝ → ℕ → ℝ} {offset s x : ℝ}
    (hτ : 0 < s - offset) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a)
    (hValueBound :
      ∀ (k n : ℕ) (q : ℝ × ℝ), (k : ℕ∞) ≤ (2 : ℕ∞) →
        ‖iteratedFDeriv ℝ k
          (cutoffValueTerm (restartSmoothCutoff offset s) a₀ a offset n)
            q‖ ≤
          concreteRestartValueMajorant a₀ a src offset s k n)
    (hGradBound :
      ∀ (k n : ℕ) (q : ℝ × ℝ), (k : ℕ∞) ≤ (2 : ℕ∞) →
        ‖iteratedFDeriv ℝ k
          (cutoffGradTerm (restartSmoothCutoff offset s)
            (resolverSpectralConcreteGradTerm a₀ a offset) n) q‖ ≤
          concreteRestartGradMajorant a₀ a src offset s k n) :
    ResolverSpectralJointC2At a₀ a offset s x :=
  resolverSpectralJointC2At_of_smooth_cutoff_contDiff_tsum
    (φ := restartSmoothCutoff offset s)
    (gradTerm := resolverSpectralConcreteGradTerm a₀ a offset)
    (vValue := concreteRestartValueMajorant a₀ a src offset s)
    (vGrad := concreteRestartGradMajorant a₀ a src offset s)
    (restartSmoothCutoff_eventually_eq_one hτ)
    (cutoffValueTerm_restartSmoothCutoff_contDiff src)
    (concreteRestartValueMajorant_summable hτ ha₀ src)
    hValueBound
    (cutoffGradTerm_restartSmoothCutoff_contDiff src)
    (concreteRestartGradMajorant_summable hτ ha₀ src)
    hGradBound
    (resolverSpectralGradSeries_eventuallyEq_concreteGradTerm hτ ha₀ src)

end ShenWork.IntervalResolverSpectralJointC2Concrete
