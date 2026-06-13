import ShenWork.PDE.IntervalH3E
import ShenWork.Paper2.IntervalClampedK1SourceCubicBootstrap

/-!
# Lane BC2: H3E heat-factor audit for the clamped K1 source

This module is intentionally narrow.  It exposes the two committed tools that
BC2 is allowed to use:

* H3E's third spatial heat-tail estimate.
* the positive-time heat-factor producer for model coefficients already carrying
  `exp (-eps * lambda_n)`.

The actual clamped K1 source family is still the raw source package attached to
`LocalRestart.srcC`; no downstream C2 package is assumed here.
-/

noncomputable section

namespace ShenWork.Paper2.BC2H3EResolverAudit

open ShenWork.PDE
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalMildRegularityBootstrap
  (unitIntervalCosineEigenvalue_mul_exp_summable)
open ShenWork.IntervalResolverSpectralTimeC2
  (eigenvalue_sq_mul_exp_summable eigenvalue_cube_mul_exp_summable)
open ShenWork.Paper2.PicardLimitK1C2Coeff (SourceC2CoeffFields)

private abbrev bc2Lam (n : ℕ) : ℝ :=
  unitIntervalCosineEigenvalue n

private theorem bc2Lam_nonneg (n : ℕ) : 0 ≤ bc2Lam n := by
  unfold bc2Lam unitIntervalCosineEigenvalue
  positivity

/-- H3E route-(i): third spatial heat-kernel point weights have a summable
cube-tail majorant at positive time. -/
theorem h3e_third_terms_summable_of_bounded
    {t M : ℝ} (ht : 0 < t) {a : ℕ → ℝ}
    (hM : ∀ n, |a n| ≤ M) (x : ℝ) :
    Summable
      (fun n =>
        unitIntervalCosineHeatThirdPointWeight t x n * a n) :=
  h3e_route_i_third_terms_summable_of_bounded ht hM x

/-- In every K1 local restart, the represented target slice is a positive
restart time away from its base. -/
theorem local_restart_target_shift_pos
    {p : CM2Params}
    {u : ℝ → ShenWork.IntervalDomain.intervalDomainPoint → ℝ}
    {T sigma : ℝ}
    (L : ShenWork.Paper2.PicardLimitK1.LocalRestart p u T sigma) :
    0 < sigma - L.τ :=
  ShenWork.PDE.h3e_route_ii_target_shift_pos L

/-- H3E route-(ii): if a coefficient family already has the positive heat
factor, bounded initial coefficients are enough for all source-side C2
coefficient fields. -/
def heat_factor_source_fields
    {eps M : ℝ} {a0 : ℕ → ℝ} (heps : 0 < eps) (hM : 0 ≤ M)
    (ha0 : ∀ n, |a0 n| ≤ M) :
    ShenWork.Paper2.PicardLimitK1C2Coeff.SourceC2CoeffFields
      (ShenWork.Paper2.PicardLimitK1C2Heat.shiftedHeatCoeff_timeC1
        heps hM ha0) :=
  ShenWork.PDE.h3e_route_ii_heat_factor_fields heps hM ha0

/-- Raw-source heat-factor bridge.  This is the exact non-circular missing
shape for `LocalRestart.aC`: source coefficients carry `exp (-eps * lambda_n)`,
and source time derivatives carry one extra `lambda_n` times the same heat
factor. -/
def source_fields_of_heat_factor_bounds
    {a : ℝ → ℕ → ℝ} {src : DuhamelSourceTimeC1 a}
    {eps M Mdot : ℝ} (heps : 0 < eps) (hM : 0 ≤ M)
    (hMdot : 0 ≤ Mdot)
    (hsrc : ∀ s, 0 ≤ s → ∀ n,
      |a s n| ≤ Real.exp (-eps * bc2Lam n) * M)
    (hadot : ∀ s, 0 ≤ s → ∀ n,
      |src.adot s n| ≤
        bc2Lam n * Real.exp (-eps * bc2Lam n) * Mdot) :
    SourceC2CoeffFields src where
  sourceEigenEnvelope := fun n =>
    (bc2Lam n * Real.exp (-eps * bc2Lam n)) * M
  sourceEigen_nonneg := fun n =>
    mul_nonneg
      (mul_nonneg (bc2Lam_nonneg n) (Real.exp_nonneg _)) hM
  sourceEigen_summable :=
    (unitIntervalCosineEigenvalue_mul_exp_summable heps).mul_right M
  sourceEigen_bound := by
    intro s hs n
    have hlam : 0 ≤ bc2Lam n := bc2Lam_nonneg n
    calc bc2Lam n * |a s n|
        ≤ bc2Lam n * (Real.exp (-eps * bc2Lam n) * M) :=
          mul_le_mul_of_nonneg_left (hsrc s hs n) hlam
      _ = (bc2Lam n * Real.exp (-eps * bc2Lam n)) * M := by ring
  sourceEigenSqEnvelope := fun n =>
    (bc2Lam n * (bc2Lam n * Real.exp (-eps * bc2Lam n))) * M
  sourceEigenSq_nonneg := fun n =>
    mul_nonneg
      (mul_nonneg (bc2Lam_nonneg n)
        (mul_nonneg (bc2Lam_nonneg n) (Real.exp_nonneg _))) hM
  sourceEigenSq_summable :=
    (eigenvalue_sq_mul_exp_summable heps).mul_right M
  sourceEigenSq_bound := by
    intro s hs n
    have hlam : 0 ≤ bc2Lam n := bc2Lam_nonneg n
    calc bc2Lam n * (bc2Lam n * |a s n|)
        ≤ bc2Lam n *
            (bc2Lam n * (Real.exp (-eps * bc2Lam n) * M)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hsrc s hs n) hlam) hlam
      _ = (bc2Lam n * (bc2Lam n * Real.exp (-eps * bc2Lam n))) * M :=
          by ring
  adotEigenEnvelope := fun n =>
    (bc2Lam n * (bc2Lam n * Real.exp (-eps * bc2Lam n))) * Mdot
  adotEigen_nonneg := fun n =>
    mul_nonneg
      (mul_nonneg (bc2Lam_nonneg n)
        (mul_nonneg (bc2Lam_nonneg n) (Real.exp_nonneg _))) hMdot
  adotEigen_summable :=
    (eigenvalue_sq_mul_exp_summable heps).mul_right Mdot
  adotEigen_bound := by
    intro s hs n
    have hlam : 0 ≤ bc2Lam n := bc2Lam_nonneg n
    calc bc2Lam n * |src.adot s n|
        ≤ bc2Lam n *
            (bc2Lam n * Real.exp (-eps * bc2Lam n) * Mdot) :=
          mul_le_mul_of_nonneg_left (hadot s hs n) hlam
      _ = (bc2Lam n * (bc2Lam n * Real.exp (-eps * bc2Lam n))) *
            Mdot := by ring
  adotEigenSqEnvelope := fun n =>
    (bc2Lam n *
      (bc2Lam n * (bc2Lam n * Real.exp (-eps * bc2Lam n)))) * Mdot
  adotEigenSq_nonneg := fun n =>
    mul_nonneg
      (mul_nonneg (bc2Lam_nonneg n)
        (mul_nonneg (bc2Lam_nonneg n)
          (mul_nonneg (bc2Lam_nonneg n) (Real.exp_nonneg _)))) hMdot
  adotEigenSq_summable :=
    (eigenvalue_cube_mul_exp_summable heps).mul_right Mdot
  adotEigenSq_bound := by
    intro s hs n
    have hlam : 0 ≤ bc2Lam n := bc2Lam_nonneg n
    calc bc2Lam n * (bc2Lam n * |src.adot s n|)
        ≤ bc2Lam n *
            (bc2Lam n *
              (bc2Lam n * Real.exp (-eps * bc2Lam n) * Mdot)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hadot s hs n) hlam) hlam
      _ = (bc2Lam n *
            (bc2Lam n * (bc2Lam n * Real.exp (-eps * bc2Lam n)))) *
            Mdot := by ring

/-- Instantiation of the heat-factor bridge at the actual K1 local-restart
source family.  The two heat-factor hypotheses are the precise current
residual for the raw clamped `aC`. -/
def local_restart_source_fields_of_heat_factor_bounds
    {p : CM2Params}
    {u : ℝ → ShenWork.IntervalDomain.intervalDomainPoint → ℝ}
    {T sigma : ℝ}
    (L : ShenWork.Paper2.PicardLimitK1.LocalRestart p u T sigma)
    {eps M Mdot : ℝ} (heps : 0 < eps) (hM : 0 ≤ M)
    (hMdot : 0 ≤ Mdot)
    (hsrc : ∀ s, 0 ≤ s → ∀ n,
      |L.aC s n| ≤ Real.exp (-eps * bc2Lam n) * M)
    (hadot : ∀ s, 0 ≤ s → ∀ n,
      |L.srcC.adot s n| ≤
        bc2Lam n * Real.exp (-eps * bc2Lam n) * Mdot) :
    SourceC2CoeffFields L.srcC :=
  source_fields_of_heat_factor_bounds heps hM hMdot hsrc hadot

/-- The K1 C2 closure point remains exactly `SourceC2CoeffFields` for the raw
clamped source package. -/
def source_fields_to_c2Coeff
    {a : ℝ → ℕ → ℝ}
    {src : ShenWork.IntervalDuhamelClosedC2.DuhamelSourceTimeC1 a}
    (fields : ShenWork.Paper2.PicardLimitK1C2Coeff.SourceC2CoeffFields src) :
    ShenWork.IntervalResolverSpectralTimeC2.DuhamelSourceTimeC2Coeff a :=
  fields.toC2Coeff

end ShenWork.Paper2.BC2H3EResolverAudit
