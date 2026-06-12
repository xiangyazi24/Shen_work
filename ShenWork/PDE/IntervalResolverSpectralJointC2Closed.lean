import ShenWork.PDE.IntervalResolverSpectralTimeC2

open Filter Topology Set

noncomputable section

namespace ShenWork.IntervalResolverSpectralJointC2Closed

open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.IntervalResolverSpectralTimeC2
  (DuhamelSourceTimeC2Coeff localRestartCoeffAdot)
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

end ShenWork.IntervalResolverSpectralJointC2Closed
