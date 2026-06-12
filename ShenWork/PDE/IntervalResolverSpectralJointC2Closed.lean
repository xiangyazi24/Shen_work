import ShenWork.PDE.IntervalResolverSpectralTimeC2

open Filter Topology Set

noncomputable section

namespace ShenWork.IntervalResolverSpectralJointC2Closed

open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.IntervalResolverSpectralTimeC2
  (DuhamelSourceTimeC2Coeff localRestartCoeffAdot localRestartCoeffAddot)
open ShenWork.IntervalResolverJointC2
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)

/-- Marker namespace for the resolver spectral joint-`C²` closure increment. -/
def c2Coeff_to_timeC1 {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) : DuhamelSourceTimeC1 a :=
  src.toTimeC1

/-- Homogeneous restart term with two eigenvalue weights. -/
theorem restartHomogeneousCoeff_eigenvalue_sq_summable
    {τ M : ℝ} {a₀ : ℕ → ℝ}
    (hτ : 0 < τ) (ha₀ : ∀ n, |a₀ n| ≤ M) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|)) := by
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg _) (ha₀ 0)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((ShenWork.IntervalResolverSpectralTimeC2.eigenvalue_sq_mul_exp_summable
      hτ).mul_right M)
  · exact mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity)
      (mul_nonneg
        (by unfold unitIntervalCosineEigenvalue; positivity)
        (abs_nonneg _))
  · have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    have hexp : 0 ≤ Real.exp (-τ * unitIntervalCosineEigenvalue n) :=
      Real.exp_nonneg _
    calc unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|)
        = unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              (Real.exp (-τ * unitIntervalCosineEigenvalue n) *
                |a₀ n|)) := by
          rw [abs_mul, abs_of_nonneg hexp]
      _ ≤ unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              (Real.exp (-τ * unitIntervalCosineEigenvalue n) * M)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (ha₀ n) hexp) hlam)
            hlam
      _ = unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              Real.exp (-τ * unitIntervalCosineEigenvalue n)) * M := by
          ring

/-- Homogeneous restart term with three eigenvalue weights. -/
theorem restartHomogeneousCoeff_eigenvalue_cube_summable
    {τ M : ℝ} {a₀ : ℕ → ℝ}
    (hτ : 0 < τ) (ha₀ : ∀ n, |a₀ n| ≤ M) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|))) := by
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg _) (ha₀ 0)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((ShenWork.IntervalResolverSpectralTimeC2.eigenvalue_cube_mul_exp_summable
      hτ).mul_right M)
  · exact mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity)
      (mul_nonneg
        (by unfold unitIntervalCosineEigenvalue; positivity)
        (mul_nonneg
          (by unfold unitIntervalCosineEigenvalue; positivity)
          (abs_nonneg _)))
  · have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    have hexp : 0 ≤ Real.exp (-τ * unitIntervalCosineEigenvalue n) :=
      Real.exp_nonneg _
    calc unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|))
        = unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              (unitIntervalCosineEigenvalue n *
                (Real.exp (-τ * unitIntervalCosineEigenvalue n) *
                  |a₀ n|))) := by
          rw [abs_mul, abs_of_nonneg hexp]
      _ ≤ unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              (unitIntervalCosineEigenvalue n *
                (Real.exp (-τ * unitIntervalCosineEigenvalue n) * M))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (ha₀ n) hexp) hlam)
              hlam)
            hlam
      _ = unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              (unitIntervalCosineEigenvalue n *
                Real.exp (-τ * unitIntervalCosineEigenvalue n))) * M := by
          ring

/-- Duhamel coefficient with two eigenvalue weights, from the strengthened
source/adot eigenvalue envelopes. -/
theorem duhamelSpectralCoeff_eigenvalue_sq_summable
    {τ : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          |duhamelSpectralCoeff a τ n|)) := by
  let majorant : ℕ → ℝ := fun n =>
    2 * src.sourceEigenEnvelope n + τ * src.adotEigenEnvelope n
  have hmajor : Summable majorant :=
    (src.sourceEigen_summable.mul_left 2).add
      (src.adotEigen_summable.mul_left τ)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmajor
  · exact mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity)
      (mul_nonneg
        (by unfold unitIntervalCosineEigenvalue; positivity)
        (abs_nonneg _))
  · set lam := unitIntervalCosineEigenvalue n
    have hlam : 0 ≤ lam := by
      unfold lam unitIntervalCosineEigenvalue
      positivity
    have hconv :
        lam * (lam * |duhamelSpectralCoeff a τ n|)
          = lam *
            |a τ n -
              Real.exp (-τ * lam) * a 0 n -
              ∫ s in (0 : ℝ)..τ,
                Real.exp (-(τ - s) * lam) *
                  src.toTimeC1.adot s n| := by
      have hkey :=
        ShenWork.IntervalDuhamelClosedC2.duhamelCoeff_eigenvalue_mul
          (t := τ) (lam := lam) (a := fun s : ℝ => a s n)
          (adot := fun s : ℝ => src.toTimeC1.adot s n)
          (fun s => src.toTimeC1.hderiv s n)
          (src.toTimeC1.hadotcont n)
      have hduh :
          duhamelSpectralCoeff a τ n =
            ∫ s in (0 : ℝ)..τ, Real.exp (-(τ - s) * lam) * a s n := by
        simp [duhamelSpectralCoeff, lam]
      rw [hduh]
      calc lam *
            (lam *
              |∫ s in (0 : ℝ)..τ,
                Real.exp (-(τ - s) * lam) * a s n|)
            = lam *
                |lam * ∫ s in (0 : ℝ)..τ,
                  Real.exp (-(τ - s) * lam) * a s n| := by
              rw [abs_mul, abs_of_nonneg hlam]
          _ = lam *
            |a τ n -
              Real.exp (-τ * lam) * a 0 n -
              ∫ s in (0 : ℝ)..τ,
                Real.exp (-(τ - s) * lam) *
                  src.toTimeC1.adot s n| := by
            rw [hkey]
    rw [hconv]
    have hpiece₀ :
        lam * |a τ n| ≤ src.sourceEigenEnvelope n :=
      src.sourceEigen_bound τ hτ.le n
    have hexp_le : Real.exp (-τ * lam) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hτ.le hlam])
    have hpiece₁ :
        lam * |Real.exp (-τ * lam) * a 0 n| ≤
          src.sourceEigenEnvelope n := by
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      calc lam * (Real.exp (-τ * lam) * |a 0 n|)
          = Real.exp (-τ * lam) * (lam * |a 0 n|) := by
              ring
        _ ≤ 1 * src.sourceEigenEnvelope n := by
            exact mul_le_mul hexp_le
              (src.sourceEigen_bound 0 le_rfl n)
              (mul_nonneg hlam (abs_nonneg _)) zero_le_one
        _ = src.sourceEigenEnvelope n := one_mul _
    have hpieceI :
        lam *
          |∫ s in (0 : ℝ)..τ,
            Real.exp (-(τ - s) * lam) * src.toTimeC1.adot s n|
          ≤ τ * src.adotEigenEnvelope n := by
      set f : ℝ → ℝ := fun s =>
        Real.exp (-(τ - s) * lam) * src.toTimeC1.adot s n
      have hf_cont : Continuous f := by
        dsimp [f]
        exact (Real.continuous_exp.comp (by fun_prop)).mul
          (src.toTimeC1.hadotcont n)
      have habs_int :
          |∫ s in (0 : ℝ)..τ, f s| ≤
            ∫ s in (0 : ℝ)..τ, |f s| :=
        intervalIntegral.abs_integral_le_integral_abs hτ.le
      calc lam * |∫ s in (0 : ℝ)..τ, f s|
          ≤ lam * ∫ s in (0 : ℝ)..τ, |f s| :=
            mul_le_mul_of_nonneg_left habs_int hlam
        _ = ∫ s in (0 : ℝ)..τ, lam * |f s| := by
            rw [← intervalIntegral.integral_const_mul]
        _ ≤ ∫ _s in (0 : ℝ)..τ, src.adotEigenEnvelope n := by
            apply intervalIntegral.integral_mono_on hτ.le
            · exact (continuous_const.mul hf_cont.abs).intervalIntegrable 0 τ
            · exact continuous_const.intervalIntegrable 0 τ
            · intro s hs
              have hs_nonneg : 0 ≤ τ - s := by linarith [hs.2]
              have hexp_s :
                  Real.exp (-(τ - s) * lam) ≤ 1 := by
                rw [← Real.exp_zero]
                exact Real.exp_le_exp.mpr
                  (by nlinarith [mul_nonneg hs_nonneg hlam])
              rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
              calc lam *
                    (Real.exp (-(τ - s) * lam) *
                      |src.toTimeC1.adot s n|)
                  = Real.exp (-(τ - s) * lam) *
                      (lam * |src.toTimeC1.adot s n|) := by
                    ring
                _ ≤ 1 * src.adotEigenEnvelope n := by
                    exact mul_le_mul hexp_s
                      (src.adotEigen_bound s hs.1 n)
                      (mul_nonneg hlam (abs_nonneg _)) zero_le_one
                _ = src.adotEigenEnvelope n := one_mul _
        _ = src.adotEigenEnvelope n * τ := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
            ring
        _ = τ * src.adotEigenEnvelope n := by ring
    calc lam *
          |a τ n - Real.exp (-τ * lam) * a 0 n -
            ∫ s in (0 : ℝ)..τ,
              Real.exp (-(τ - s) * lam) *
                src.toTimeC1.adot s n|
        ≤ lam *
            (|a τ n| + |Real.exp (-τ * lam) * a 0 n| +
              |∫ s in (0 : ℝ)..τ,
                Real.exp (-(τ - s) * lam) *
                  src.toTimeC1.adot s n|) := by
            exact mul_le_mul_of_nonneg_left
              (by
                have h₀ :
                    |a τ n - Real.exp (-τ * lam) * a 0 n -
                      ∫ s in (0 : ℝ)..τ,
                        Real.exp (-(τ - s) * lam) *
                          src.toTimeC1.adot s n| ≤
                      |a τ n - Real.exp (-τ * lam) * a 0 n| +
                        |∫ s in (0 : ℝ)..τ,
                          Real.exp (-(τ - s) * lam) *
                            src.toTimeC1.adot s n| := by
                  have h :=
                    abs_add_le
                      (a τ n - Real.exp (-τ * lam) * a 0 n)
                      (-(∫ s in (0 : ℝ)..τ,
                        Real.exp (-(τ - s) * lam) *
                          src.toTimeC1.adot s n))
                  simpa [sub_eq_add_neg, abs_neg] using h
                have h₁ :
                    |a τ n - Real.exp (-τ * lam) * a 0 n| ≤
                      |a τ n| + |Real.exp (-τ * lam) * a 0 n| := by
                  have h :=
                    abs_add_le (a τ n)
                      (-(Real.exp (-τ * lam) * a 0 n))
                  simpa [sub_eq_add_neg, abs_neg] using h
                calc |a τ n - Real.exp (-τ * lam) * a 0 n -
                      ∫ s in (0 : ℝ)..τ,
                        Real.exp (-(τ - s) * lam) *
                          src.toTimeC1.adot s n|
                    ≤ |a τ n - Real.exp (-τ * lam) * a 0 n| +
                      |∫ s in (0 : ℝ)..τ,
                        Real.exp (-(τ - s) * lam) *
                          src.toTimeC1.adot s n| := h₀
                  _ ≤ (|a τ n| +
                      |Real.exp (-τ * lam) * a 0 n|) +
                        |∫ s in (0 : ℝ)..τ,
                          Real.exp (-(τ - s) * lam) *
                            src.toTimeC1.adot s n| :=
                        add_le_add h₁ le_rfl
                  _ = |a τ n| +
                      |Real.exp (-τ * lam) * a 0 n| +
                      |∫ s in (0 : ℝ)..τ,
                        Real.exp (-(τ - s) * lam) *
                          src.toTimeC1.adot s n| := by
                        ring)
              hlam
      _ = lam * |a τ n| +
            lam * |Real.exp (-τ * lam) * a 0 n| +
            lam * |∫ s in (0 : ℝ)..τ,
              Real.exp (-(τ - s) * lam) *
                src.toTimeC1.adot s n| := by
          ring
      _ ≤ src.sourceEigenEnvelope n + src.sourceEigenEnvelope n +
            τ * src.adotEigenEnvelope n :=
          add_le_add (add_le_add hpiece₀ hpiece₁) hpieceI
      _ = majorant n := by
          dsimp [majorant]
          ring

/-- Duhamel coefficient with three eigenvalue weights, from the λ²-weighted
source/adot envelopes. -/
theorem duhamelSpectralCoeff_eigenvalue_cube_summable
    {τ : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceTimeC2Coeff a) (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            |duhamelSpectralCoeff a τ n|))) := by
  let majorant : ℕ → ℝ := fun n =>
    2 * src.sourceEigenSqEnvelope n + τ * src.adotEigenSqEnvelope n
  have hmajor : Summable majorant :=
    (src.sourceEigenSq_summable.mul_left 2).add
      (src.adotEigenSq_summable.mul_left τ)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmajor
  · exact mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity)
      (mul_nonneg
        (by unfold unitIntervalCosineEigenvalue; positivity)
        (mul_nonneg
          (by unfold unitIntervalCosineEigenvalue; positivity)
          (abs_nonneg _)))
  · set lam := unitIntervalCosineEigenvalue n
    have hlam : 0 ≤ lam := by
      unfold lam unitIntervalCosineEigenvalue
      positivity
    have hconv :
        lam * (lam * (lam * |duhamelSpectralCoeff a τ n|))
          = lam * (lam *
            |a τ n -
              Real.exp (-τ * lam) * a 0 n -
              ∫ s in (0 : ℝ)..τ,
                Real.exp (-(τ - s) * lam) *
                  src.toTimeC1.adot s n|) := by
      have hkey :=
        ShenWork.IntervalDuhamelClosedC2.duhamelCoeff_eigenvalue_mul
          (t := τ) (lam := lam) (a := fun s : ℝ => a s n)
          (adot := fun s : ℝ => src.toTimeC1.adot s n)
          (fun s => src.toTimeC1.hderiv s n)
          (src.toTimeC1.hadotcont n)
      have hduh :
          duhamelSpectralCoeff a τ n =
            ∫ s in (0 : ℝ)..τ, Real.exp (-(τ - s) * lam) * a s n := by
        simp [duhamelSpectralCoeff, lam]
      rw [hduh]
      calc lam *
            (lam *
              (lam *
                |∫ s in (0 : ℝ)..τ,
                  Real.exp (-(τ - s) * lam) * a s n|))
          = lam * (lam *
              |lam * ∫ s in (0 : ℝ)..τ,
                Real.exp (-(τ - s) * lam) * a s n|) := by
              rw [abs_mul, abs_of_nonneg hlam]
        _ = lam * (lam *
            |a τ n -
              Real.exp (-τ * lam) * a 0 n -
              ∫ s in (0 : ℝ)..τ,
                Real.exp (-(τ - s) * lam) *
                  src.toTimeC1.adot s n|) := by
            rw [hkey]
    rw [hconv]
    have hpiece₀ :
        lam * (lam * |a τ n|) ≤ src.sourceEigenSqEnvelope n :=
      src.sourceEigenSq_bound τ hτ.le n
    have hexp_le : Real.exp (-τ * lam) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hτ.le hlam])
    have hpiece₁ :
        lam * (lam * |Real.exp (-τ * lam) * a 0 n|) ≤
          src.sourceEigenSqEnvelope n := by
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      calc lam * (lam * (Real.exp (-τ * lam) * |a 0 n|))
          = Real.exp (-τ * lam) * (lam * (lam * |a 0 n|)) := by
              ring
        _ ≤ 1 * src.sourceEigenSqEnvelope n := by
            exact mul_le_mul hexp_le
              (src.sourceEigenSq_bound 0 le_rfl n)
              (mul_nonneg hlam (mul_nonneg hlam (abs_nonneg _)))
              zero_le_one
        _ = src.sourceEigenSqEnvelope n := one_mul _
    have hpieceI :
        lam *
          (lam *
            |∫ s in (0 : ℝ)..τ,
              Real.exp (-(τ - s) * lam) * src.toTimeC1.adot s n|)
          ≤ τ * src.adotEigenSqEnvelope n := by
      set f : ℝ → ℝ := fun s =>
        Real.exp (-(τ - s) * lam) * src.toTimeC1.adot s n
      have hf_cont : Continuous f := by
        dsimp [f]
        exact (Real.continuous_exp.comp (by fun_prop)).mul
          (src.toTimeC1.hadotcont n)
      have habs_int :
          |∫ s in (0 : ℝ)..τ, f s| ≤
            ∫ s in (0 : ℝ)..τ, |f s| :=
        intervalIntegral.abs_integral_le_integral_abs hτ.le
      calc lam * (lam * |∫ s in (0 : ℝ)..τ, f s|)
          ≤ lam * (lam * ∫ s in (0 : ℝ)..τ, |f s|) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left habs_int hlam) hlam
        _ = ∫ s in (0 : ℝ)..τ, lam * (lam * |f s|) := by
            rw [← intervalIntegral.integral_const_mul]
            rw [← intervalIntegral.integral_const_mul]
        _ ≤ ∫ _s in (0 : ℝ)..τ, src.adotEigenSqEnvelope n := by
            apply intervalIntegral.integral_mono_on hτ.le
            · exact (continuous_const.mul
                (continuous_const.mul hf_cont.abs)).intervalIntegrable 0 τ
            · exact continuous_const.intervalIntegrable 0 τ
            · intro s hs
              have hs_nonneg : 0 ≤ τ - s := by linarith [hs.2]
              have hexp_s :
                  Real.exp (-(τ - s) * lam) ≤ 1 := by
                rw [← Real.exp_zero]
                exact Real.exp_le_exp.mpr
                  (by nlinarith [mul_nonneg hs_nonneg hlam])
              rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
              calc lam *
                    (lam *
                      (Real.exp (-(τ - s) * lam) *
                        |src.toTimeC1.adot s n|))
                  = Real.exp (-(τ - s) * lam) *
                      (lam * (lam * |src.toTimeC1.adot s n|)) := by
                    ring
                _ ≤ 1 * src.adotEigenSqEnvelope n := by
                    exact mul_le_mul hexp_s
                      (src.adotEigenSq_bound s hs.1 n)
                      (mul_nonneg hlam
                        (mul_nonneg hlam (abs_nonneg _)))
                      zero_le_one
                _ = src.adotEigenSqEnvelope n := one_mul _
        _ = src.adotEigenSqEnvelope n * τ := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
            ring
        _ = τ * src.adotEigenSqEnvelope n := by ring
    calc lam *
          (lam *
            |a τ n - Real.exp (-τ * lam) * a 0 n -
              ∫ s in (0 : ℝ)..τ,
                Real.exp (-(τ - s) * lam) *
                  src.toTimeC1.adot s n|)
        ≤ lam * (lam *
            (|a τ n| + |Real.exp (-τ * lam) * a 0 n| +
              |∫ s in (0 : ℝ)..τ,
                Real.exp (-(τ - s) * lam) *
                  src.toTimeC1.adot s n|)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (by
                  have h₀ :
                      |a τ n - Real.exp (-τ * lam) * a 0 n -
                        ∫ s in (0 : ℝ)..τ,
                          Real.exp (-(τ - s) * lam) *
                            src.toTimeC1.adot s n| ≤
                        |a τ n - Real.exp (-τ * lam) * a 0 n| +
                          |∫ s in (0 : ℝ)..τ,
                            Real.exp (-(τ - s) * lam) *
                              src.toTimeC1.adot s n| := by
                    have h :=
                      abs_add_le
                        (a τ n - Real.exp (-τ * lam) * a 0 n)
                        (-(∫ s in (0 : ℝ)..τ,
                          Real.exp (-(τ - s) * lam) *
                            src.toTimeC1.adot s n))
                    simpa [sub_eq_add_neg, abs_neg] using h
                  have h₁ :
                      |a τ n - Real.exp (-τ * lam) * a 0 n| ≤
                        |a τ n| + |Real.exp (-τ * lam) * a 0 n| := by
                    have h :=
                      abs_add_le (a τ n)
                        (-(Real.exp (-τ * lam) * a 0 n))
                    simpa [sub_eq_add_neg, abs_neg] using h
                  calc
                    |a τ n - Real.exp (-τ * lam) * a 0 n -
                      ∫ s in (0 : ℝ)..τ,
                        Real.exp (-(τ - s) * lam) *
                          src.toTimeC1.adot s n|
                        ≤ |a τ n - Real.exp (-τ * lam) * a 0 n| +
                          |∫ s in (0 : ℝ)..τ,
                            Real.exp (-(τ - s) * lam) *
                              src.toTimeC1.adot s n| := h₀
                    _ ≤ (|a τ n| +
                        |Real.exp (-τ * lam) * a 0 n|) +
                          |∫ s in (0 : ℝ)..τ,
                            Real.exp (-(τ - s) * lam) *
                              src.toTimeC1.adot s n| :=
                          add_le_add h₁ le_rfl
                    _ = |a τ n| +
                        |Real.exp (-τ * lam) * a 0 n| +
                        |∫ s in (0 : ℝ)..τ,
                          Real.exp (-(τ - s) * lam) *
                            src.toTimeC1.adot s n| := by
                          ring)
                hlam)
              hlam
      _ = lam * (lam * |a τ n|) +
            lam * (lam * |Real.exp (-τ * lam) * a 0 n|) +
            lam * (lam * |∫ s in (0 : ℝ)..τ,
              Real.exp (-(τ - s) * lam) *
                src.toTimeC1.adot s n|) := by
          ring
      _ ≤ src.sourceEigenSqEnvelope n + src.sourceEigenSqEnvelope n +
            τ * src.adotEigenSqEnvelope n :=
          add_le_add (add_le_add hpiece₀ hpiece₁) hpieceI
      _ = majorant n := by
          dsimp [majorant]
          ring

/-- The full local restart coefficient with two eigenvalue weights. -/
theorem localRestartCoeff_eigenvalue_sq_summable
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          |localRestartCoeff a₀ a τ n|)) := by
  have hhom :=
    restartHomogeneousCoeff_eigenvalue_sq_summable
      (τ := τ) (M := M) (a₀ := a₀) hτ ha₀
  have hduh := duhamelSpectralCoeff_eigenvalue_sq_summable src hτ
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (hhom.add hduh)
  · exact mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity)
      (mul_nonneg
        (by unfold unitIntervalCosineEigenvalue; positivity)
        (abs_nonneg _))
  · have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    calc unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            |localRestartCoeff a₀ a τ n|)
        ≤ unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              (|Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n| +
                |duhamelSpectralCoeff a τ n|)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (by
                simp only [localRestartCoeff]
                exact abs_add_le _ _)
              hlam)
            hlam
      _ = unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|) +
          unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              |duhamelSpectralCoeff a τ n|) := by
          ring

/-- The full local restart coefficient with three eigenvalue weights. -/
theorem localRestartCoeff_eigenvalue_cube_summable
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            |localRestartCoeff a₀ a τ n|))) := by
  have hhom :=
    restartHomogeneousCoeff_eigenvalue_cube_summable
      (τ := τ) (M := M) (a₀ := a₀) hτ ha₀
  have hduh := duhamelSpectralCoeff_eigenvalue_cube_summable src hτ
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (hhom.add hduh)
  · exact mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity)
      (mul_nonneg
        (by unfold unitIntervalCosineEigenvalue; positivity)
        (mul_nonneg
          (by unfold unitIntervalCosineEigenvalue; positivity)
          (abs_nonneg _)))
  · have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    calc unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              |localRestartCoeff a₀ a τ n|))
        ≤ unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              (unitIntervalCosineEigenvalue n *
                (|Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n| +
                  |duhamelSpectralCoeff a τ n|))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (by
                  simp only [localRestartCoeff]
                  exact abs_add_le _ _)
                hlam)
              hlam)
            hlam
      _ = unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              (unitIntervalCosineEigenvalue n *
                |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|)) +
          unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              (unitIntervalCosineEigenvalue n *
                |duhamelSpectralCoeff a τ n|)) := by
          ring

/-- Frequency times one eigenvalue is bounded by two eigenvalue weights. -/
theorem frequency_mul_eigenvalue_le_eigenvalue_sq (n : ℕ) :
    |(n : ℝ) * Real.pi| * unitIntervalCosineEigenvalue n ≤
      unitIntervalCosineEigenvalue n * unitIntervalCosineEigenvalue n := by
  by_cases hn : n = 0
  · subst n
    unfold unitIntervalCosineEigenvalue
    simp
  · have hn1 : (1 : ℝ) ≤ n := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
    have hfreq_nonneg : 0 ≤ (n : ℝ) * Real.pi := by positivity
    have hfreq_ge_one : 1 ≤ (n : ℝ) * Real.pi := by
      nlinarith [hn1, Real.pi_gt_three]
    have hfreq_le_sq :
        (n : ℝ) * Real.pi ≤ ((n : ℝ) * Real.pi) ^ 2 :=
      le_self_pow₀ hfreq_ge_one (by norm_num)
    have hlam :
        unitIntervalCosineEigenvalue n = ((n : ℝ) * Real.pi) ^ 2 := by
      unfold unitIntervalCosineEigenvalue
      ring
    rw [abs_of_nonneg hfreq_nonneg, hlam]
    exact mul_le_mul_of_nonneg_right hfreq_le_sq (by positivity)

/-- A nonzero cosine mode has eigenvalue at least one. -/
theorem one_le_eigenvalue_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    1 ≤ unitIntervalCosineEigenvalue n := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
  have hfreq_ge_one : 1 ≤ (n : ℝ) * Real.pi := by
    nlinarith [hn1, Real.pi_gt_three]
  have hlam :
      unitIntervalCosineEigenvalue n = ((n : ℝ) * Real.pi) ^ 2 := by
    unfold unitIntervalCosineEigenvalue
    ring
  rw [hlam]
  nlinarith [sq_nonneg ((n : ℝ) * Real.pi), hfreq_ge_one]

/-- The spatial frequency is bounded by the Neumann eigenvalue. -/
theorem frequency_le_eigenvalue (n : ℕ) :
    |(n : ℝ) * Real.pi| ≤ unitIntervalCosineEigenvalue n := by
  by_cases hn : n = 0
  · subst n
    simp [unitIntervalCosineEigenvalue]
  · have hfreq_nonneg : 0 ≤ (n : ℝ) * Real.pi := by positivity
    have hfreq_ge_one : 1 ≤ (n : ℝ) * Real.pi := by
      have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
      nlinarith [hn1, Real.pi_gt_three]
    have hfreq_le_sq :
        (n : ℝ) * Real.pi ≤ ((n : ℝ) * Real.pi) ^ 2 :=
      le_self_pow₀ hfreq_ge_one (by norm_num)
    rw [abs_of_nonneg hfreq_nonneg]
    simpa [unitIntervalCosineEigenvalue] using hfreq_le_sq

/-- Remove one eigenvalue weight from an absolutely summable sequence. -/
theorem summable_abs_of_eigenvalue_mul_abs_summable {b : ℕ → ℝ}
    (h : Summable (fun n : ℕ => unitIntervalCosineEigenvalue n * |b n|)) :
    Summable (fun n : ℕ => |b n|) := by
  let single : ℕ → ℝ := fun n => if n = 0 then |b 0| else 0
  have hsingle : Summable single := by
    refine summable_of_hasFiniteSupport ?_
    refine (Set.finite_singleton 0).subset ?_
    intro n hn
    simp only [Function.mem_support] at hn
    simp only [Set.mem_singleton_iff]
    by_contra hne
    simp [single, hne] at hn
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
    (hsingle.add h)
  by_cases hn : n = 0
  · subst n
    simp [single, unitIntervalCosineEigenvalue]
  · have hlam_ge := one_le_eigenvalue_of_ne_zero hn
    have hb : 0 ≤ |b n| := abs_nonneg _
    calc |b n|
        ≤ unitIntervalCosineEigenvalue n * |b n| :=
          le_mul_of_one_le_left hb hlam_ge
      _ ≤ single n + unitIntervalCosineEigenvalue n * |b n| := by
          simp [single, hn]

/-- A λ-weighted absolute summability controls the frequency-weighted sequence. -/
theorem summable_frequency_abs_of_eigenvalue_mul_abs_summable {b : ℕ → ℝ}
    (h : Summable (fun n : ℕ => unitIntervalCosineEigenvalue n * |b n|)) :
    Summable (fun n : ℕ => |(n : ℝ) * Real.pi| * |b n|) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) h
  · exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  · exact mul_le_mul_of_nonneg_right (frequency_le_eigenvalue n)
      (abs_nonneg _)

/-- The source time derivative has λ-weighted summable coefficients. -/
theorem sourceAdot_eigenvalue_summable
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC2Coeff a)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n * |src.toTimeC1.adot τ n|) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    src.adotEigen_summable
  · exact mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity) (abs_nonneg _)
  · exact src.adotEigen_bound τ hτ n

/-- The source time derivative has λ²-weighted summable coefficients. -/
theorem sourceAdot_eigenvalue_sq_summable
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC2Coeff a)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n * |src.toTimeC1.adot τ n|)) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    src.adotEigenSq_summable
  · exact mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity)
      (mul_nonneg
        (by unfold unitIntervalCosineEigenvalue; positivity)
        (abs_nonneg _))
  · exact src.adotEigenSq_bound τ hτ n

/-- The second time derivative coefficient is absolutely summable at positive
restart time. -/
theorem localRestartCoeffAddot_summable
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    Summable (fun n : ℕ =>
      |localRestartCoeffAddot a₀ a src.toTimeC1.adot τ n|) := by
  have hadot_eig := sourceAdot_eigenvalue_summable src hτ.le
  have hadot := summable_abs_of_eigenvalue_mul_abs_summable hadot_eig
  have hcadot_eig :=
    ShenWork.IntervalResolverSpectralTimeC2.localRestartCoeffAdot_eigenvalue_summable
      hτ ha₀ src
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
    (hadot.add hcadot_eig)
  have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue
    positivity
  calc |localRestartCoeffAddot a₀ a src.toTimeC1.adot τ n|
      ≤ |src.toTimeC1.adot τ n| +
          |unitIntervalCosineEigenvalue n *
            localRestartCoeffAdot a₀ a τ n| := by
        simpa [localRestartCoeffAddot, sub_eq_add_neg, abs_neg] using
          abs_add_le (src.toTimeC1.adot τ n)
            (-(unitIntervalCosineEigenvalue n *
              localRestartCoeffAdot a₀ a τ n))
    _ = |src.toTimeC1.adot τ n| +
          unitIntervalCosineEigenvalue n *
            |localRestartCoeffAdot a₀ a τ n| := by
        rw [abs_mul, abs_of_nonneg hlam]

/-- The restart coefficient time derivative has summable λ²-weighted
coefficients. -/
theorem localRestartCoeffAdot_eigenvalue_sq_summable
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          |localRestartCoeffAdot a₀ a τ n|)) := by
  have ha_sq : Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n * |a τ n|)) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      src.sourceEigenSq_summable
    · exact mul_nonneg
        (by unfold unitIntervalCosineEigenvalue; positivity)
        (mul_nonneg
          (by unfold unitIntervalCosineEigenvalue; positivity)
          (abs_nonneg _))
    · exact src.sourceEigenSq_bound τ hτ.le n
  have hc_cube := localRestartCoeff_eigenvalue_cube_summable hτ ha₀ src
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (ha_sq.add hc_cube)
  · exact mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity)
      (mul_nonneg
        (by unfold unitIntervalCosineEigenvalue; positivity)
        (abs_nonneg _))
  · have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    calc unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            |localRestartCoeffAdot a₀ a τ n|)
        ≤ unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              (|a τ n| +
                |unitIntervalCosineEigenvalue n *
                  localRestartCoeff a₀ a τ n|)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (by
                simpa [localRestartCoeffAdot, sub_eq_add_neg, abs_neg]
                  using abs_add_le (a τ n)
                    (-(unitIntervalCosineEigenvalue n *
                      localRestartCoeff a₀ a τ n)))
              hlam)
            hlam
      _ = unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n * |a τ n|) +
          unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              (unitIntervalCosineEigenvalue n *
                |localRestartCoeff a₀ a τ n|)) := by
          rw [abs_mul, abs_of_nonneg hlam]
          ring

/-- Frequency-weighted second time derivative coefficient summability. -/
theorem localRestartCoeffAddot_frequency_summable
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    Summable (fun n : ℕ =>
      |(n : ℝ) * Real.pi| *
        |localRestartCoeffAddot a₀ a src.toTimeC1.adot τ n|) := by
  have hadot_eig := sourceAdot_eigenvalue_summable src hτ.le
  have hcadot_sq := localRestartCoeffAdot_eigenvalue_sq_summable hτ ha₀ src
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (hadot_eig.add hcadot_sq)
  · exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  · have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    calc |(n : ℝ) * Real.pi| *
          |localRestartCoeffAddot a₀ a src.toTimeC1.adot τ n|
        ≤ |(n : ℝ) * Real.pi| *
            (|src.toTimeC1.adot τ n| +
              |unitIntervalCosineEigenvalue n *
                localRestartCoeffAdot a₀ a τ n|) := by
          exact mul_le_mul_of_nonneg_left
            (by
              simpa [localRestartCoeffAddot, sub_eq_add_neg, abs_neg]
                using abs_add_le (src.toTimeC1.adot τ n)
                  (-(unitIntervalCosineEigenvalue n *
                    localRestartCoeffAdot a₀ a τ n)))
            (abs_nonneg _)
      _ = |(n : ℝ) * Real.pi| * |src.toTimeC1.adot τ n| +
            (|(n : ℝ) * Real.pi| * unitIntervalCosineEigenvalue n) *
              |localRestartCoeffAdot a₀ a τ n| := by
          have hcoeff :
              |unitIntervalCosineEigenvalue n *
                  localRestartCoeffAdot a₀ a τ n| =
                unitIntervalCosineEigenvalue n *
                  |localRestartCoeffAdot a₀ a τ n| := by
            rw [abs_mul, abs_of_nonneg hlam]
          rw [hcoeff]
          ring
      _ ≤ unitIntervalCosineEigenvalue n * |src.toTimeC1.adot τ n| +
            (unitIntervalCosineEigenvalue n *
              unitIntervalCosineEigenvalue n) *
              |localRestartCoeffAdot a₀ a τ n| := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right (frequency_le_eigenvalue n)
              (abs_nonneg _))
            (mul_le_mul_of_nonneg_right
              (frequency_mul_eigenvalue_le_eigenvalue_sq n)
              (abs_nonneg _))
      _ = unitIntervalCosineEigenvalue n * |src.toTimeC1.adot τ n| +
            unitIntervalCosineEigenvalue n *
              (unitIntervalCosineEigenvalue n *
                |localRestartCoeffAdot a₀ a τ n|) := by
          ring

/-- Value-side order-2 majorant for the restart term:
`|cₙ''| + |nπ||cₙ'| + λₙ|cₙ|`. -/
theorem localRestartCoeff_value_c2_majorant_summable
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    Summable (fun n : ℕ =>
      |localRestartCoeffAddot a₀ a src.toTimeC1.adot τ n| +
        |(n : ℝ) * Real.pi| * |localRestartCoeffAdot a₀ a τ n| +
          unitIntervalCosineEigenvalue n *
            |localRestartCoeff a₀ a τ n|) := by
  have hddot := localRestartCoeffAddot_summable hτ ha₀ src
  have hadot_freq :=
    summable_frequency_abs_of_eigenvalue_mul_abs_summable
      (ShenWork.IntervalResolverSpectralTimeC2.localRestartCoeffAdot_eigenvalue_summable
        hτ ha₀ src)
  have hc_eig :=
    ShenWork.IntervalResolverSpectralJointC2Producer.localRestartCoeff_eigenvalue_summable
      hτ ha₀ src.toTimeC1
  simpa [add_assoc] using hddot.add (hadot_freq.add hc_eig)

/-- Spatial-gradient higher-order weight for the local restart coefficient. -/
theorem localRestartCoeff_grad_spatial_weight_summable
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    Summable (fun n : ℕ =>
      |(n : ℝ) * Real.pi| * unitIntervalCosineEigenvalue n *
        |localRestartCoeff a₀ a τ n|) := by
  refine (localRestartCoeff_eigenvalue_sq_summable hτ ha₀ src).of_nonneg_of_le
    (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg
      (mul_nonneg (abs_nonneg _)
        (by unfold unitIntervalCosineEigenvalue; positivity))
      (abs_nonneg _)
  · calc |(n : ℝ) * Real.pi| * unitIntervalCosineEigenvalue n *
          |localRestartCoeff a₀ a τ n|
        ≤ (unitIntervalCosineEigenvalue n * unitIntervalCosineEigenvalue n) *
            |localRestartCoeff a₀ a τ n| := by
          exact mul_le_mul_of_nonneg_right
            (frequency_mul_eigenvalue_le_eigenvalue_sq n) (abs_nonneg _)
      _ = unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            |localRestartCoeff a₀ a τ n|) := by
          ring

/-- Gradient-side order-2 majorant for the restart term:
`|nπ||cₙ''| + λₙ|cₙ'| + |nπ|λₙ|cₙ|`. -/
theorem localRestartCoeff_grad_c2_majorant_summable
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    Summable (fun n : ℕ =>
      |(n : ℝ) * Real.pi| *
          |localRestartCoeffAddot a₀ a src.toTimeC1.adot τ n| +
        unitIntervalCosineEigenvalue n *
          |localRestartCoeffAdot a₀ a τ n| +
          |(n : ℝ) * Real.pi| * unitIntervalCosineEigenvalue n *
            |localRestartCoeff a₀ a τ n|) := by
  have hddot_freq :=
    localRestartCoeffAddot_frequency_summable hτ ha₀ src
  have hadot_eig :=
    ShenWork.IntervalResolverSpectralTimeC2.localRestartCoeffAdot_eigenvalue_summable
      hτ ha₀ src
  have hc_grad := localRestartCoeff_grad_spatial_weight_summable hτ ha₀ src
  simpa [add_assoc] using hddot_freq.add (hadot_eig.add hc_grad)

end ShenWork.IntervalResolverSpectralJointC2Closed
