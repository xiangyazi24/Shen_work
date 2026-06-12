import ShenWork.Paper2.IntervalClampedK1SourceC2CoeffEnvelope
import ShenWork.PDE.IntervalCoupledSourceTimeC1

/-!
# Clamped K1 source cubic-bootstrap audit

This module pins the committed facts relevant to the `χ₀ < 0` K1 source
regularity question.

Committed regularity found by survey:

* `IntervalPicardWeightedC2Bootstrap.slice_source_coeff_decay` is the actual
  clamped/Picard source coefficient decay available in the K1 path.  It is
  quadratic: `|a_k| <= C / (k*pi)^2`.
* `intervalDomainClassicalRegularity` records spatial `ContDiffOn R 2`, plus
  time and boundary continuity.  It does not record spatial order `3` or higher.
* The coupled chem-div source producers similarly thread weak-H2 data and
  quadratic source decay into `DuhamelSourceTimeC1`.

Therefore the current committed branch does not derive the weighted source
envelopes required by `DuhamelSourceTimeC2Coeff`; those envelopes are the exact
minimal bootstrap target for the actual clamped K1 source family.
-/

noncomputable section

namespace ShenWork.Paper2.ClampedK1SourceCubicBootstrap

open ShenWork.Paper2.ClampedK1SourceC2CoeffEnvelope

/-- Best committed per-slice coefficient decay for the K1 source path. -/
abbrev bestCommittedSourceCoeffDecay :=
  ShenWork.IntervalPicardWeightedC2Bootstrap.slice_source_coeff_decay

/-- Exact local bootstrap site: source-side C2 coefficient fields close the
current `DuhamelSourceTimeC2Coeff` obligation. -/
def sourceFields_close_c2Coeff {a : ℝ → ℕ → ℝ}
    {src : ShenWork.IntervalDuhamelClosedC2.DuhamelSourceTimeC1 a}
    (fields :
      ShenWork.Paper2.PicardLimitK1C2Coeff.SourceC2CoeffFields src) :
    ShenWork.IntervalResolverSpectralTimeC2.DuhamelSourceTimeC2Coeff a :=
  fields.toC2Coeff

/-- The current C2-coefficient API requires a summable one-eigenvalue source
envelope. -/
theorem c2Coeff_requires_sourceEigenEnvelope {a : ℝ → ℕ → ℝ}
    (src : ShenWork.IntervalResolverSpectralTimeC2.DuhamelSourceTimeC2Coeff a) :
    Summable src.sourceEigenEnvelope :=
  src.sourceEigen_summable

/-- The current C2-coefficient API also requires a summable two-eigenvalue source
envelope. -/
theorem c2Coeff_requires_sourceEigenSqEnvelope {a : ℝ → ℕ → ℝ}
    (src : ShenWork.IntervalResolverSpectralTimeC2.DuhamelSourceTimeC2Coeff a) :
    Summable src.sourceEigenSqEnvelope :=
  src.sourceEigenSq_summable

/-- The time derivative of the source must satisfy the same one-eigenvalue
summability. -/
theorem c2Coeff_requires_adotEigenEnvelope {a : ℝ → ℕ → ℝ}
    (src : ShenWork.IntervalResolverSpectralTimeC2.DuhamelSourceTimeC2Coeff a) :
    Summable src.adotEigenEnvelope :=
  src.adotEigen_summable

/-- The time derivative of the source must satisfy the same two-eigenvalue
summability. -/
theorem c2Coeff_requires_adotEigenSqEnvelope {a : ℝ → ℕ → ℝ}
    (src : ShenWork.IntervalResolverSpectralTimeC2.DuhamelSourceTimeC2Coeff a) :
    Summable src.adotEigenSqEnvelope :=
  src.adotEigenSq_summable

/-- Re-export the obstruction algebra: the committed quadratic decay gives only
a modewise bounded `lambda_k * |a_k|` tail. -/
theorem committedQuadratic_oneEigenvalue_le_const
    {a : ℕ → ℝ} {C : ℝ}
    (hdecay : ∀ k : ℕ, 1 ≤ k →
      |a k| ≤ C / ((k : ℝ) * Real.pi) ^ 2)
    {k : ℕ} (hk : 1 ≤ k) :
    unitIntervalCosineEigenvalue k * |a k| ≤ C :=
  quadraticDecay_oneEigenvalue_le_const hdecay hk

/-- After two eigenvalue weights, the committed quadratic decay grows like
`C * lambda_k`, so it is not the missing C2-coefficient source envelope. -/
theorem committedQuadratic_twoEigenvalues_le_const_mul_eigen
    {a : ℕ → ℝ} {C : ℝ}
    (hdecay : ∀ k : ℕ, 1 ≤ k →
      |a k| ≤ C / ((k : ℝ) * Real.pi) ^ 2)
    {k : ℕ} (hk : 1 ≤ k) :
    unitIntervalCosineEigenvalue k *
      (unitIntervalCosineEigenvalue k * |a k|)
        ≤ C * unitIntervalCosineEigenvalue k :=
  quadraticDecay_twoEigenvalues_le_const_mul_eigen hdecay hk

end ShenWork.Paper2.ClampedK1SourceCubicBootstrap
