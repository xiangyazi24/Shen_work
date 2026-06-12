import ShenWork.Paper2.IntervalPicardLimitK1
import ShenWork.PDE.IntervalResolverJointC2C2Coeff
/-!
# K1 base `DuhamelSourceTimeC2Coeff` construction site

This module is the C2-coefficient strengthening of the K1 local-restart
construction.  The base producer must be filled from the concrete heat-kernel
smoothing data at the K1 site, not from the downstream restart transporters.
-/
open MeasureTheory Filter Topology Set
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalResolverSpectralTimeC2 (DuhamelSourceTimeC2Coeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section
namespace ShenWork.Paper2.PicardLimitK1C2Coeff
/-- The raw source-side fields needed to upgrade a K1 C1 source package to the
coefficient-level C2 package.  These are source fields, not restart transport
facts. -/
structure SourceC2CoeffFields {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC1 a) where
  sourceEigenEnvelope : ℕ → ℝ
  sourceEigen_nonneg : ∀ n, 0 ≤ sourceEigenEnvelope n
  sourceEigen_summable : Summable sourceEigenEnvelope
  sourceEigen_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n * |a s n| ≤ sourceEigenEnvelope n
  sourceEigenSqEnvelope : ℕ → ℝ
  sourceEigenSq_nonneg : ∀ n, 0 ≤ sourceEigenSqEnvelope n
  sourceEigenSq_summable : Summable sourceEigenSqEnvelope
  sourceEigenSq_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n * |a s n|) ≤ sourceEigenSqEnvelope n
  adotEigenEnvelope : ℕ → ℝ
  adotEigen_nonneg : ∀ n, 0 ≤ adotEigenEnvelope n
  adotEigen_summable : Summable adotEigenEnvelope
  adotEigen_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n * |src.adot s n| ≤ adotEigenEnvelope n
  adotEigenSqEnvelope : ℕ → ℝ
  adotEigenSq_nonneg : ∀ n, 0 ≤ adotEigenSqEnvelope n
  adotEigenSq_summable : Summable adotEigenSqEnvelope
  adotEigenSq_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n * |src.adot s n|) ≤ adotEigenSqEnvelope n
/-- Assemble the existing `DuhamelSourceTimeC2Coeff` API from source-side fields. -/
def SourceC2CoeffFields.toC2Coeff {a : ℝ → ℕ → ℝ}
    {src : DuhamelSourceTimeC1 a} (F : SourceC2CoeffFields src) :
    DuhamelSourceTimeC2Coeff a where
  toTimeC1 := src
  sourceEigenEnvelope := F.sourceEigenEnvelope
  sourceEigen_nonneg := F.sourceEigen_nonneg
  sourceEigen_summable := F.sourceEigen_summable
  sourceEigen_bound := F.sourceEigen_bound
  sourceEigenSqEnvelope := F.sourceEigenSqEnvelope
  sourceEigenSq_nonneg := F.sourceEigenSq_nonneg
  sourceEigenSq_summable := F.sourceEigenSq_summable
  sourceEigenSq_bound := F.sourceEigenSq_bound
  adotEigenEnvelope := F.adotEigenEnvelope
  adotEigen_nonneg := F.adotEigen_nonneg
  adotEigen_summable := F.adotEigen_summable
  adotEigen_bound := F.adotEigen_bound
  adotEigenSqEnvelope := F.adotEigenSqEnvelope
  adotEigenSq_nonneg := F.adotEigenSq_nonneg
  adotEigenSq_summable := F.adotEigenSq_summable
  adotEigenSq_bound := F.adotEigenSq_bound
/-- Local restart data at K1, strengthened with the base C2 coefficient package for
the same clamped source family. -/
structure LocalRestartC2
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (T σ : ℝ) where
  base : ShenWork.Paper2.PicardLimitK1.LocalRestart p u T σ
  srcC2 : DuhamelSourceTimeC2Coeff base.aC
/-- Forget the strengthened package and recover the original K1 local restart. -/
def LocalRestartC2.toLocalRestart
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T σ : ℝ}
    (L : LocalRestartC2 p u T σ) :
    ShenWork.Paper2.PicardLimitK1.LocalRestart p u T σ :=
  L.base
/-- The strengthened package carries a C1 source package for the same coefficient
family used by the original K1 local restart. -/
def LocalRestartC2.toTimeC1
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T σ : ℝ}
    (L : LocalRestartC2 p u T σ) :
    ShenWork.IntervalDuhamelClosedC2.DuhamelSourceTimeC1 L.base.aC :=
  L.srcC2.toTimeC1
/-- Upgrade an existing K1 local restart once the source-side C2 coefficient fields
have been proved from the heat-kernel smoothing construction. -/
def LocalRestartC2.ofSourceFields
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T σ : ℝ}
    (L : ShenWork.Paper2.PicardLimitK1.LocalRestart p u T σ)
    (F : SourceC2CoeffFields L.srcC) :
    LocalRestartC2 p u T σ where
  base := L
  srcC2 := F.toC2Coeff
end ShenWork.Paper2.PicardLimitK1C2Coeff
