import ShenWork.PDE.IntervalResolverSpectralJointC2Producer
import ShenWork.PDE.IntervalRestartDerivJointContinuity

open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalResolverJointC2
open ShenWork.CosineSpectrum (cosineMode)
open Filter Topology Set

noncomputable section

namespace ShenWork.IntervalResolverSpectralTimeC2

/-- The concrete time derivative of the restart coefficient. -/
def localRestartCoeffAdot
  (a₀ : ℕ → ℝ) (a : ℝ → ℕ → ℝ) (τ : ℝ) (n : ℕ) : ℝ :=
  a τ n - unitIntervalCosineEigenvalue n * localRestartCoeff a₀ a τ n

/-- The concrete second time derivative of the restart coefficient. -/
def localRestartCoeffAddot
  (a₀ : ℕ → ℝ) (a adot : ℝ → ℕ → ℝ) (τ : ℝ) (n : ℕ) : ℝ :=
  adot τ n -
    unitIntervalCosineEigenvalue n * localRestartCoeffAdot a₀ a τ n

/-- Concrete source regularity strong enough to differentiate the restart
coefficients with one eigenvalue weight.  This strengthens
`DuhamelSourceTimeC1` by adding summable λ-weighted envelopes for the source
coefficients and their time derivatives. -/
structure DuhamelSourceTimeC2Coeff (a : ℝ → ℕ → ℝ) where
  toTimeC1 : DuhamelSourceTimeC1 a
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
      (unitIntervalCosineEigenvalue n * |a s n|) ≤
        sourceEigenSqEnvelope n
  adotEigenEnvelope : ℕ → ℝ
  adotEigen_nonneg : ∀ n, 0 ≤ adotEigenEnvelope n
  adotEigen_summable : Summable adotEigenEnvelope
  adotEigen_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n * |toTimeC1.adot s n| ≤
      adotEigenEnvelope n
  adotEigenSqEnvelope : ℕ → ℝ
  adotEigenSq_nonneg : ∀ n, 0 ≤ adotEigenSqEnvelope n
  adotEigenSq_summable : Summable adotEigenSqEnvelope
  adotEigenSq_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n * |toTimeC1.adot s n|) ≤
        adotEigenSqEnvelope n

/-- The polynomially weighted homogeneous heat tail needed by the concrete
coefficient-derivative estimate: `∑ λₙ² e^{-τλₙ}` for `τ > 0`. -/
theorem eigenvalue_sq_mul_exp_summable {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          Real.exp (-τ * unitIntervalCosineEigenvalue n))) := by
  have hc : 0 < τ * Real.pi ^ 2 := by positivity
  have hbase : Summable (fun n : ℕ =>
      Real.pi ^ 4 * ((n : ℝ) ^ 4 *
        Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ)))) := by
    simpa [mul_assoc] using
      (Real.summable_pow_mul_exp_neg_nat_mul 4 hc).mul_left
        (Real.pi ^ 4)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbase
  · exact mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity)
      (mul_nonneg
        (by unfold unitIntervalCosineEigenvalue; positivity)
        (Real.exp_nonneg _))
  · have hn_sq_ge : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst n
        norm_num
      · exact le_self_pow₀ (by exact_mod_cast hn) (by norm_num)
    have hlam_eq :
        unitIntervalCosineEigenvalue n = (n : ℝ) ^ 2 * Real.pi ^ 2 := by
      unfold unitIntervalCosineEigenvalue
      ring
    have hexp_le :
        Real.exp (-τ * unitIntervalCosineEigenvalue n) ≤
          Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      rw [hlam_eq]
      nlinarith [mul_nonneg hτ.le (sq_nonneg Real.pi), hn_sq_ge]
    calc unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            Real.exp (-τ * unitIntervalCosineEigenvalue n))
        = Real.pi ^ 4 * ((n : ℝ) ^ 4 *
            Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
          rw [hlam_eq]
          ring
      _ ≤ Real.pi ^ 4 * ((n : ℝ) ^ 4 *
            Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexp_le (by positivity))
            (by positivity)

/-- One higher polynomial heat tail:
`∑ λₙ³ e^{-τλₙ}` for `τ > 0`. -/
theorem eigenvalue_cube_mul_exp_summable {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            Real.exp (-τ * unitIntervalCosineEigenvalue n)))) := by
  have hc : 0 < τ * Real.pi ^ 2 := by positivity
  have hbase : Summable (fun n : ℕ =>
      Real.pi ^ 6 * ((n : ℝ) ^ 6 *
        Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ)))) := by
    simpa [mul_assoc] using
      (Real.summable_pow_mul_exp_neg_nat_mul 6 hc).mul_left
        (Real.pi ^ 6)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbase
  · exact mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity)
      (mul_nonneg
        (by unfold unitIntervalCosineEigenvalue; positivity)
        (mul_nonneg
          (by unfold unitIntervalCosineEigenvalue; positivity)
          (Real.exp_nonneg _)))
  · have hn_sq_ge : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst n
        norm_num
      · exact le_self_pow₀ (by exact_mod_cast hn) (by norm_num)
    have hlam_eq :
        unitIntervalCosineEigenvalue n = (n : ℝ) ^ 2 * Real.pi ^ 2 := by
      unfold unitIntervalCosineEigenvalue
      ring
    have hexp_le :
        Real.exp (-τ * unitIntervalCosineEigenvalue n) ≤
          Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      rw [hlam_eq]
      nlinarith [mul_nonneg hτ.le (sq_nonneg Real.pi), hn_sq_ge]
    calc unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              Real.exp (-τ * unitIntervalCosineEigenvalue n)))
        = Real.pi ^ 6 * ((n : ℝ) ^ 6 *
            Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
          rw [hlam_eq]
          ring
      _ ≤ Real.pi ^ 6 * ((n : ℝ) ^ 6 *
            Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexp_le (by positivity))
            (by positivity)

/-- The homogeneous restart derivative has summable λ-weighted coefficients:
`λₙ |∂τ(e^{-τλₙ} a₀ₙ)|` is summable at every positive `τ`. -/
theorem restartHomogeneousCoeff_adot_eigenvalue_summable
    {τ M : ℝ} {a₀ : ℕ → ℝ}
    (hτ : 0 < τ) (ha₀ : ∀ n, |a₀ n| ≤ M) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        |-(unitIntervalCosineEigenvalue n *
          Real.exp (-τ * unitIntervalCosineEigenvalue n)) * a₀ n|) := by
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg _) (ha₀ 0)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((eigenvalue_sq_mul_exp_summable hτ).mul_right M)
  · exact mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity)
      (abs_nonneg _)
  · have hlam_nonneg : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    calc unitIntervalCosineEigenvalue n *
          |-(unitIntervalCosineEigenvalue n *
            Real.exp (-τ * unitIntervalCosineEigenvalue n)) * a₀ n|
        = unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              Real.exp (-τ * unitIntervalCosineEigenvalue n) * |a₀ n|) := by
          rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg hlam_nonneg,
            abs_of_nonneg (Real.exp_nonneg _)]
      _ ≤ unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              Real.exp (-τ * unitIntervalCosineEigenvalue n) * M) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (ha₀ n)
              (mul_nonneg hlam_nonneg (Real.exp_nonneg _)))
            hlam_nonneg
      _ = unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              Real.exp (-τ * unitIntervalCosineEigenvalue n)) * M := by
          ring

/-- The Duhamel coefficient derivative has summable λ-weighted coefficients
under the concrete λ-weighted source/adot package.  The proof uses the
committed IBP identity
`duhamelSpectralCoeff_deriv_eq_ibp`. -/
theorem duhamelSpectralCoeff_deriv_eigenvalue_summable
    {τ : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        |a τ n - unitIntervalCosineEigenvalue n *
          ShenWork.IntervalDuhamelClosedC2.duhamelSpectralCoeff a τ n|) := by
  classical
  let majorant : ℕ → ℝ := fun n =>
    src.sourceEigenEnvelope n + τ * src.adotEigenEnvelope n
  have hmajor : Summable majorant :=
    src.sourceEigen_summable.add (src.adotEigen_summable.mul_left τ)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmajor
  · exact mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity)
      (abs_nonneg _)
  · have hlam_nonneg : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    have hmain :
        unitIntervalCosineEigenvalue n *
          |a τ n - unitIntervalCosineEigenvalue n *
            ShenWork.IntervalDuhamelClosedC2.duhamelSpectralCoeff a τ n|
        ≤ majorant n := by
      rw [ShenWork.IntervalSourceCoefficientTimeC1.duhamelSpectralCoeff_deriv_eq_ibp
        src.toTimeC1 τ n]
      have hexp_le :
          Real.exp (-τ * unitIntervalCosineEigenvalue n) ≤ 1 := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hτ.le hlam_nonneg]
      have hpiece₀ :
          unitIntervalCosineEigenvalue n *
            |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a 0 n|
          ≤ src.sourceEigenEnvelope n := by
        rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
        calc unitIntervalCosineEigenvalue n *
              (Real.exp (-τ * unitIntervalCosineEigenvalue n) * |a 0 n|)
            = Real.exp (-τ * unitIntervalCosineEigenvalue n) *
                (unitIntervalCosineEigenvalue n * |a 0 n|) := by
              ring
          _ ≤ 1 * src.sourceEigenEnvelope n := by
              exact mul_le_mul hexp_le (src.sourceEigen_bound 0 le_rfl n)
                (mul_nonneg hlam_nonneg (abs_nonneg _))
                zero_le_one
          _ = src.sourceEigenEnvelope n := one_mul _
      have hpieceI :
          unitIntervalCosineEigenvalue n *
            |∫ s in (0 : ℝ)..τ,
              Real.exp (-(τ - s) * unitIntervalCosineEigenvalue n) *
                src.toTimeC1.adot s n|
          ≤ τ * src.adotEigenEnvelope n := by
        set f : ℝ → ℝ := fun s =>
          Real.exp (-(τ - s) * unitIntervalCosineEigenvalue n) *
            src.toTimeC1.adot s n
        have hf_cont : Continuous f := by
          dsimp [f]
          exact (Real.continuous_exp.comp (by fun_prop)).mul
            (src.toTimeC1.hadotcont n)
        have habs_int :
            |∫ s in (0 : ℝ)..τ, f s|
              ≤ ∫ s in (0 : ℝ)..τ, |f s| :=
          intervalIntegral.abs_integral_le_integral_abs hτ.le
        calc unitIntervalCosineEigenvalue n * |∫ s in (0 : ℝ)..τ, f s|
            ≤ unitIntervalCosineEigenvalue n *
                ∫ s in (0 : ℝ)..τ, |f s| :=
              mul_le_mul_of_nonneg_left habs_int hlam_nonneg
          _ = ∫ s in (0 : ℝ)..τ,
                unitIntervalCosineEigenvalue n * |f s| := by
              rw [← intervalIntegral.integral_const_mul]
          _ ≤ ∫ _s in (0 : ℝ)..τ, src.adotEigenEnvelope n := by
              apply intervalIntegral.integral_mono_on hτ.le
              · exact (continuous_const.mul hf_cont.abs).intervalIntegrable 0 τ
              · exact continuous_const.intervalIntegrable 0 τ
              · intro s hs
                have hsexp :
                    Real.exp (-(τ - s) * unitIntervalCosineEigenvalue n) ≤ 1 := by
                  rw [← Real.exp_zero]
                  apply Real.exp_le_exp.mpr
                  have hs0 : 0 ≤ τ - s := by linarith [hs.2]
                  nlinarith [mul_nonneg hs0 hlam_nonneg]
                rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
                calc unitIntervalCosineEigenvalue n *
                      (Real.exp (-(τ - s) *
                        unitIntervalCosineEigenvalue n) *
                        |src.toTimeC1.adot s n|)
                    = Real.exp (-(τ - s) *
                        unitIntervalCosineEigenvalue n) *
                        (unitIntervalCosineEigenvalue n *
                          |src.toTimeC1.adot s n|) := by
                      ring
                  _ ≤ 1 * src.adotEigenEnvelope n := by
                      exact mul_le_mul hsexp
                        (src.adotEigen_bound s hs.1 n)
                        (mul_nonneg hlam_nonneg (abs_nonneg _))
                        zero_le_one
                  _ = src.adotEigenEnvelope n := one_mul _
          _ = src.adotEigenEnvelope n * τ := by
              rw [intervalIntegral.integral_const, smul_eq_mul]
              ring
          _ = τ * src.adotEigenEnvelope n := by ring
      calc unitIntervalCosineEigenvalue n *
            |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a 0 n +
              ∫ s in (0 : ℝ)..τ,
                Real.exp (-(τ - s) * unitIntervalCosineEigenvalue n) *
                  src.toTimeC1.adot s n|
          ≤ unitIntervalCosineEigenvalue n *
              (|Real.exp (-τ * unitIntervalCosineEigenvalue n) * a 0 n| +
                |∫ s in (0 : ℝ)..τ,
                  Real.exp (-(τ - s) * unitIntervalCosineEigenvalue n) *
                    src.toTimeC1.adot s n|) := by
              exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hlam_nonneg
        _ = unitIntervalCosineEigenvalue n *
              |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a 0 n| +
            unitIntervalCosineEigenvalue n *
              |∫ s in (0 : ℝ)..τ,
                Real.exp (-(τ - s) * unitIntervalCosineEigenvalue n) *
                  src.toTimeC1.adot s n| := by
              ring
        _ ≤ src.sourceEigenEnvelope n +
            τ * src.adotEigenEnvelope n :=
              add_le_add hpiece₀ hpieceI
        _ = majorant n := rfl
    exact hmain

/-- The concrete derivative of the local restart coefficient is
`aₙ(τ) - λₙ cₙ(τ)`. -/
theorem localRestartCoeff_hasDerivAt
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (τ : ℝ) (n : ℕ) :
    HasDerivAt (fun r : ℝ => localRestartCoeff a₀ a r n)
      (localRestartCoeffAdot a₀ a τ n) τ := by
  set lam := unitIntervalCosineEigenvalue n
  have hhom : HasDerivAt
      (fun r : ℝ => Real.exp (-r * lam) * a₀ n)
      (-(lam * Real.exp (-τ * lam)) * a₀ n) τ := by
    have harg : HasDerivAt (fun r : ℝ => -r * lam) (-lam) τ := by
      simpa using (hasDerivAt_id τ).neg.mul_const lam
    exact (harg.exp.mul_const _).congr_deriv (by ring)
  have hduh :
      HasDerivAt
        (fun r : ℝ =>
          ShenWork.IntervalDuhamelClosedC2.duhamelSpectralCoeff a r n)
        (a τ n - lam *
          ShenWork.IntervalDuhamelClosedC2.duhamelSpectralCoeff a τ n) τ :=
    ShenWork.IntervalSourceCoefficientTimeC1.duhamelSpectralCoeff_hasDerivAt
      src.toTimeC1 τ n
  rw [show (fun r : ℝ => localRestartCoeff a₀ a r n) =
      fun r : ℝ =>
        Real.exp (-r * lam) * a₀ n +
          ShenWork.IntervalDuhamelClosedC2.duhamelSpectralCoeff a r n
      from by
        ext r
        simp [localRestartCoeff, lam]]
  convert hhom.add hduh using 1
  simp [localRestartCoeffAdot, localRestartCoeff, lam]
  ring

/-- The restart coefficient time derivative is differentiable once more:
`cₙ'' = aₙ' - λₙ cₙ'`. -/
theorem localRestartCoeffAdot_hasDerivAt
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (τ : ℝ) (n : ℕ) :
    HasDerivAt (fun r : ℝ => localRestartCoeffAdot a₀ a r n)
      (src.toTimeC1.adot τ n -
        unitIntervalCosineEigenvalue n *
          localRestartCoeffAdot a₀ a τ n) τ := by
  simpa [localRestartCoeffAdot] using
    (src.toTimeC1.hderiv τ n).sub
      ((localRestartCoeff_hasDerivAt
        (a₀ := a₀) (a := a) src τ n).const_mul
          (unitIntervalCosineEigenvalue n))

theorem localRestartCoeffAdot_hasDerivAt_addot
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (τ : ℝ) (n : ℕ) :
    HasDerivAt (fun r : ℝ => localRestartCoeffAdot a₀ a r n)
      (localRestartCoeffAddot a₀ a src.toTimeC1.adot τ n) τ := by
  simpa [localRestartCoeffAddot] using
    localRestartCoeffAdot_hasDerivAt (a₀ := a₀) (a := a) src τ n

/-- Continuity of the concrete restart-coefficient time derivative. -/
theorem localRestartCoeffAdot_continuous
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (n : ℕ) :
    Continuous (fun τ : ℝ => localRestartCoeffAdot a₀ a τ n) := by
  have ha : Continuous (fun τ : ℝ => a τ n) :=
    continuous_iff_continuousAt.2
      (fun τ => (src.toTimeC1.hderiv τ n).continuousAt)
  have hc : Continuous (fun τ : ℝ => localRestartCoeff a₀ a τ n) :=
    continuous_iff_continuousAt.2
      (fun τ => (localRestartCoeff_hasDerivAt
        (a₀ := a₀) (a := a) src τ n).continuousAt)
  simpa [localRestartCoeffAdot] using
    ha.sub (continuous_const.mul hc)

/-- The concrete restart-coefficient time derivative is `C¹`. -/
theorem localRestartCoeffAdot_contDiff_one
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (n : ℕ) :
    ContDiff ℝ 1 (fun τ : ℝ => localRestartCoeffAdot a₀ a τ n) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro τ
    exact (localRestartCoeffAdot_hasDerivAt
      (a₀ := a₀) (a := a) src τ n).differentiableAt
  · have hderiv :
        deriv (fun τ : ℝ => localRestartCoeffAdot a₀ a τ n) =
          fun τ : ℝ =>
            src.toTimeC1.adot τ n -
              unitIntervalCosineEigenvalue n *
                localRestartCoeffAdot a₀ a τ n := by
      funext τ
      exact (localRestartCoeffAdot_hasDerivAt
        (a₀ := a₀) (a := a) src τ n).deriv
    rw [hderiv]
    exact (src.toTimeC1.hadotcont n).sub
      (continuous_const.mul
        (localRestartCoeffAdot_continuous (a₀ := a₀) src n))

/-- Every concrete restart coefficient is globally `C²` in the time parameter. -/
theorem localRestartCoeff_contDiff_two
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (n : ℕ) :
    ContDiff ℝ 2 (fun τ : ℝ => localRestartCoeff a₀ a τ n) := by
  change ContDiff ℝ ((1 : ℕ∞) + 1)
    (fun τ : ℝ => localRestartCoeff a₀ a τ n)
  rw [contDiff_succ_iff_deriv]
  refine ⟨?_, ?_, ?_⟩
  · intro τ
    exact (localRestartCoeff_hasDerivAt
      (a₀ := a₀) (a := a) src τ n).differentiableAt
  · intro htop
    simp at htop
  · have hderiv :
        deriv (fun τ : ℝ => localRestartCoeff a₀ a τ n) =
          fun τ : ℝ => localRestartCoeffAdot a₀ a τ n := by
      funext τ
      exact (localRestartCoeff_hasDerivAt
        (a₀ := a₀) (a := a) src τ n).deriv
    rw [hderiv]
    exact localRestartCoeffAdot_contDiff_one (a₀ := a₀) src n

/-- The full local restart coefficient has summable λ-weighted time derivative.
This is the time analogue of
`IntervalResolverSpectralJointC2Producer.localRestartCoeff_eigenvalue_summable`,
with the extra λ produced by differentiating the concrete heat/Duhamel
coefficient formula. -/
theorem localRestartCoeffAdot_eigenvalue_summable
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        |localRestartCoeffAdot a₀ a τ n|) := by
  have hduh := duhamelSpectralCoeff_deriv_eigenvalue_summable src hτ
  have hhom :=
    restartHomogeneousCoeff_adot_eigenvalue_summable
      (τ := τ) (M := M) (a₀ := a₀) hτ ha₀
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (hduh.add hhom)
  · exact mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity)
      (abs_nonneg _)
  · set lam := unitIntervalCosineEigenvalue n
    set duh :=
      a τ n -
        lam * ShenWork.IntervalDuhamelClosedC2.duhamelSpectralCoeff a τ n
    set hom := -(lam * Real.exp (-τ * lam)) * a₀ n
    have hlam_nonneg : 0 ≤ lam := by
      unfold lam unitIntervalCosineEigenvalue
      positivity
    have hadot_eq :
        localRestartCoeffAdot a₀ a τ n = duh + hom := by
      simp [localRestartCoeffAdot, localRestartCoeff, duh, hom, lam]
      ring
    calc unitIntervalCosineEigenvalue n *
          |localRestartCoeffAdot a₀ a τ n|
        = lam * |duh + hom| := by
            rw [hadot_eq]
      _ ≤ lam * (|duh| + |hom|) :=
          mul_le_mul_of_nonneg_left (abs_add_le duh hom) hlam_nonneg
      _ = lam * |duh| + lam * |hom| := by ring
      _ =
          unitIntervalCosineEigenvalue n *
              |a τ n - unitIntervalCosineEigenvalue n *
                ShenWork.IntervalDuhamelClosedC2.duhamelSpectralCoeff a τ n| +
            unitIntervalCosineEigenvalue n *
              |-(unitIntervalCosineEigenvalue n *
                Real.exp (-τ * unitIntervalCosineEigenvalue n)) * a₀ n| := by
          simp [duh, hom, lam]

end ShenWork.IntervalResolverSpectralTimeC2
