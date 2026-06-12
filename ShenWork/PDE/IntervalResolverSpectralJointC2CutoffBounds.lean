import Mathlib.Analysis.Normed.Operator.Prod
import ShenWork.PDE.IntervalResolverSpectralJointC2Cutoff

open Filter Topology Set

noncomputable section

namespace ShenWork.IntervalResolverSpectralJointC2CutoffBounds

open ShenWork.IntervalResolverSpectralJointC2Cutoff
open ShenWork.IntervalResolverSpectralJointC2Closed
open ShenWork.IntervalResolverSpectralTimeC2
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.CosineSpectrum (cosineMode)

/-- Scalar value-side C² majorant committed in the closed coefficient lane. -/
def restartValueC2Majorant
    (a₀ : ℕ → ℝ) (a adot : ℝ → ℕ → ℝ) (τ : ℝ) (n : ℕ) : ℝ :=
  |localRestartCoeffAddot a₀ a adot τ n| +
    (n : ℝ) * |Real.pi| * |localRestartCoeffAdot a₀ a τ n| +
      unitIntervalCosineEigenvalue n * |localRestartCoeff a₀ a τ n|

/-- Scalar gradient-side C² majorant committed in the closed coefficient lane. -/
def restartGradC2Majorant
    (a₀ : ℕ → ℝ) (a adot : ℝ → ℕ → ℝ) (τ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * |Real.pi| * |localRestartCoeffAddot a₀ a adot τ n| +
    unitIntervalCosineEigenvalue n * |localRestartCoeffAdot a₀ a τ n| +
      (n : ℝ) * |Real.pi| * unitIntervalCosineEigenvalue n *
        |localRestartCoeff a₀ a τ n|

/-- Value-side scalar majorant summability, delegated to the committed lemma. -/
theorem restartValueC2Majorant_summable
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    Summable
      (restartValueC2Majorant a₀ a src.toTimeC1.adot τ) := by
  simpa [restartValueC2Majorant] using
    localRestartCoeff_value_c2_majorant_summable hτ ha₀ src

/-- Gradient-side scalar majorant summability, delegated to the committed lemma. -/
theorem restartGradC2Majorant_summable
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    Summable
      (restartGradC2Majorant a₀ a src.toTimeC1.adot τ) := by
  simpa [restartGradC2Majorant] using
    localRestartCoeff_grad_c2_majorant_summable hτ ha₀ src

/-- Leibniz bound for the separated cutoff value term. -/
theorem cutoffValueTerm_leibniz_bound
    {φ : ℝ → ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    {offset : ℝ} {n k : ℕ} {q : ℝ × ℝ}
    (hG : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ =>
        φ q.1 * localRestartCoeff a₀ a (q.1 - offset) n))
    (hH : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => cosineMode n q.2))
    (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) :
    ‖iteratedFDeriv ℝ k (cutoffValueTerm φ a₀ a offset n) q‖ ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i
          (fun q : ℝ × ℝ =>
            φ q.1 * localRestartCoeff a₀ a (q.1 - offset) n) q‖ *
        ‖iteratedFDeriv ℝ (k - i)
          (fun q : ℝ × ℝ => cosineMode n q.2) q‖ := by
  have hk' : (k : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast hk
  have hterm :
      cutoffValueTerm φ a₀ a offset n =
        fun q : ℝ × ℝ =>
          (φ q.1 * localRestartCoeff a₀ a (q.1 - offset) n) *
            cosineMode n q.2 := by
    funext q
    simp [cutoffValueTerm, mul_assoc]
  rw [hterm]
  simpa [mul_assoc] using
    norm_iteratedFDeriv_mul_le hG hH q hk'

theorem cutoffGradTerm_leibniz_bound
    {φ : ℝ → ℝ} {gradTerm : ℕ → ℝ × ℝ → ℝ}
    {n k : ℕ} {q : ℝ × ℝ}
    (hG : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => φ q.1))
    (hH : ContDiff ℝ (2 : ℕ∞) (gradTerm n))
    (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) :
    ‖iteratedFDeriv ℝ k (cutoffGradTerm φ gradTerm n) q‖ ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => φ q.1) q‖ *
        ‖iteratedFDeriv ℝ (k - i) (gradTerm n) q‖ := by
  have hk' : (k : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast hk
  have hterm :
      cutoffGradTerm φ gradTerm n =
        fun q : ℝ × ℝ => φ q.1 * gradTerm n q := by
    funext q
    rfl
  rw [hterm]
  simpa [mul_assoc] using norm_iteratedFDeriv_mul_le hG hH q hk'

/-- Projection bound for functions depending only on the first coordinate. -/
theorem norm_iteratedFDeriv_comp_fst_le
    {g : ℝ → ℝ} {N : WithTop ℕ∞} (hg : ContDiff ℝ N g)
    {k : ℕ} (hk : (k : ℕ∞) ≤ N) (q : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ k (fun q : ℝ × ℝ => g q.1) q‖ ≤
      ‖iteratedFDeriv ℝ k g q.1‖ := by
  let L : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  have hEq :
      iteratedFDeriv ℝ k (g ∘ L) q =
        (iteratedFDeriv ℝ k g (L q)).compContinuousLinearMap
          fun _ : Fin k => L :=
    L.iteratedFDeriv_comp_right hg q hk
  change ‖iteratedFDeriv ℝ k (g ∘ L) q‖ ≤
    ‖iteratedFDeriv ℝ k g (L q)‖
  rw [hEq]
  calc
    ‖(iteratedFDeriv ℝ k g (L q)).compContinuousLinearMap
          (fun _ : Fin k => L)‖
        ≤ ‖iteratedFDeriv ℝ k g (L q)‖ * ∏ _i : Fin k, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ k g (L q)‖ := by
      simp [L, ContinuousLinearMap.norm_fst]

/-- Projection bound for functions depending only on the second coordinate. -/
theorem norm_iteratedFDeriv_comp_snd_le
    {g : ℝ → ℝ} {N : WithTop ℕ∞} (hg : ContDiff ℝ N g)
    {k : ℕ} (hk : (k : ℕ∞) ≤ N) (q : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ k (fun q : ℝ × ℝ => g q.2) q‖ ≤
      ‖iteratedFDeriv ℝ k g q.2‖ := by
  let L : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hEq :
      iteratedFDeriv ℝ k (g ∘ L) q =
        (iteratedFDeriv ℝ k g (L q)).compContinuousLinearMap
          fun _ : Fin k => L :=
    L.iteratedFDeriv_comp_right hg q hk
  change ‖iteratedFDeriv ℝ k (g ∘ L) q‖ ≤
    ‖iteratedFDeriv ℝ k g (L q)‖
  rw [hEq]
  calc
    ‖(iteratedFDeriv ℝ k g (L q)).compContinuousLinearMap
          (fun _ : Fin k => L)‖
        ≤ ‖iteratedFDeriv ℝ k g (L q)‖ * ∏ _i : Fin k, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ k g (L q)‖ := by
      simp [L, ContinuousLinearMap.norm_snd]

end ShenWork.IntervalResolverSpectralJointC2CutoffBounds
