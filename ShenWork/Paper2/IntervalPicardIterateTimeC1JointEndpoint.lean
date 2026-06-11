import ShenWork.Paper2.IntervalPicardIterateTimeC1Endpoint

open MeasureTheory Filter Topology Set
open scoped Topology

noncomputable section

namespace ShenWork.IntervalPicardIterateTimeC1JointEndpoint

open ShenWork.IntervalDuhamelClosedC2
  (duhamelSpectralCoeff cosineCoeff_summable_of_eigenvalue_summable)
open ShenWork.IntervalDuhamelSourceTimeC1On
  (DuhamelSourceTimeC1On duhamelCoeff_eigenvalue_mul_on
    duhamelSpectralCoeff_eigenvalue_summable_on)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDomainRegularityBootstrap
  (reciprocalSquareTerm reciprocalSquareTerm_summable)
open ShenWork.IntervalPicardIterateTimeC1 (restartFieldTimeDeriv)
open ShenWork.IntervalPicardIterateTimeC1Endpoint
  (source_coeff_continuousOn_of_timeC1On)
open ShenWork.IntervalPicardLimitK1WeakEndpoint
  (hasDerivWithinAt_localRestartCoeff_mul_cos)

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-- Closed-window derivative-series majorant for the `_On` source package. -/
private def derivMajorant (src : DuhamelSourceTimeC1On a 0 W) (a' M : ℝ)
    (n : ℕ) : ℝ :=
  M * ((λ_ n) * Real.exp (-a' * (λ_ n))) +
    (2 * src.envelope n + src.derivBound * reciprocalSquareTerm n)

private theorem derivMajorant_summable
    (src : DuhamelSourceTimeC1On a 0 W) {a' M : ℝ} (ha' : 0 < a') :
    Summable (fun n => derivMajorant src a' M n) := by
  unfold derivMajorant
  have hexp :=
    ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable
      ha'
  exact (hexp.mul_left M).add
    ((src.henv_summable.mul_left 2).add
      (reciprocalSquareTerm_summable.mul_left src.derivBound))

private theorem duhamel_deriv_abs_le_on
    {a : ℝ → ℕ → ℝ} {W τ : ℝ} (src : DuhamelSourceTimeC1On a 0 W)
    (hτ0 : 0 ≤ τ) (hτW : τ ≤ W) (n : ℕ) :
    |a τ n - (λ_ n) * duhamelSpectralCoeff a τ n| ≤
      2 * src.envelope n + src.derivBound * reciprocalSquareTerm n := by
  have hdb_nn : 0 ≤ src.derivBound :=
    le_trans (abs_nonneg _) (src.hderivBound 0 ⟨le_rfl, le_trans hτ0 hτW⟩ 0)
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst n
    have hlam0 : unitIntervalCosineEigenvalue 0 = 0 := by
      simp [unitIntervalCosineEigenvalue]
    have hrec0 : reciprocalSquareTerm 0 = 0 := by
      simp [reciprocalSquareTerm]
    simp only [hlam0, hrec0, zero_mul, sub_zero, mul_zero, add_zero]
    have henvnn : 0 ≤ src.envelope 0 :=
      le_trans (abs_nonneg _) (src.henv_bound τ ⟨hτ0, hτW⟩ 0)
    linarith [src.henv_bound τ ⟨hτ0, hτW⟩ 0]
  · have hlam_nn : (0 : ℝ) ≤ (λ_ n) := by
      unfold unitIntervalCosineEigenvalue
      positivity
    have hlam_pos : 0 < (λ_ n) := by
      unfold unitIntervalCosineEigenvalue
      have : (0 : ℝ) < n := Nat.cast_pos.2 hn
      positivity
    have hkey := duhamelCoeff_eigenvalue_mul_on (lo := 0) (hi := W) (t := τ)
      (lam := (λ_ n)) (a := fun s => a s n) (adot := fun s => src.adot s n)
      (le_trans hτ0 hτW) hτ0 hτW
      (fun s hs => src.hderiv s ⟨hs.1, le_trans hs.2 hτW⟩ n)
      (src.hadotcont n)
    have hconv :
        (λ_ n) * duhamelSpectralCoeff a τ n =
          a τ n - Real.exp (-(τ - 0) * (λ_ n)) * a 0 n
            - ∫ s in (0 : ℝ)..τ,
                Real.exp (-(τ - s) * (λ_ n)) * src.adot s n := by
      simpa [duhamelSpectralCoeff] using hkey
    rw [hconv]
    have htri :
        |a τ n - (a τ n - Real.exp (-(τ - 0) * (λ_ n)) * a 0 n
            - ∫ s in (0 : ℝ)..τ,
                Real.exp (-(τ - s) * (λ_ n)) * src.adot s n)| ≤
          |Real.exp (-(τ - 0) * (λ_ n)) * a 0 n| +
            |∫ s in (0 : ℝ)..τ,
                Real.exp (-(τ - s) * (λ_ n)) * src.adot s n| := by
      convert abs_add_le
        (Real.exp (-(τ - 0) * (λ_ n)) * a 0 n)
        (∫ s in (0 : ℝ)..τ,
          Real.exp (-(τ - s) * (λ_ n)) * src.adot s n) using 1
      ring
    have hbexp : |Real.exp (-(τ - 0) * (λ_ n)) * a 0 n| ≤ src.envelope n := by
      have hexp_le : Real.exp (-(τ - 0) * (λ_ n)) ≤ 1 := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hτ0 hlam_nn]
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      calc Real.exp (-(τ - 0) * (λ_ n)) * |a 0 n|
          ≤ 1 * |a 0 n| := mul_le_mul_of_nonneg_right hexp_le (abs_nonneg _)
        _ = |a 0 n| := one_mul _
        _ ≤ src.envelope n := src.henv_bound 0 ⟨le_rfl, le_trans hτ0 hτW⟩ n
    have hI : |∫ s in (0 : ℝ)..τ,
          Real.exp (-(τ - s) * (λ_ n)) * src.adot s n|
        ≤ src.derivBound * ∫ s in (0 : ℝ)..τ,
            Real.exp (-(τ - s) * (λ_ n)) := by
      have hkernel : Continuous (fun s : ℝ => Real.exp (-(τ - s) * (λ_ n))) := by
        fun_prop
      have hii : IntervalIntegrable
          (fun s => Real.exp (-(τ - s) * (λ_ n)) * src.adot s n) volume 0 τ := by
        exact (hkernel.continuousOn.mul
          ((src.hadotcont n).mono
            (fun s hs => ⟨hs.1, le_trans hs.2 hτW⟩))).intervalIntegrable_of_Icc hτ0
      calc |∫ s in (0 : ℝ)..τ,
              Real.exp (-(τ - s) * (λ_ n)) * src.adot s n|
          = ‖∫ s in (0 : ℝ)..τ,
              Real.exp (-(τ - s) * (λ_ n)) * src.adot s n‖ :=
            (Real.norm_eq_abs _).symm
        _ ≤ ∫ s in (0 : ℝ)..τ,
              ‖Real.exp (-(τ - s) * (λ_ n)) * src.adot s n‖ :=
            intervalIntegral.norm_integral_le_integral_norm hτ0
        _ ≤ ∫ s in (0 : ℝ)..τ,
              src.derivBound * Real.exp (-(τ - s) * (λ_ n)) := by
            apply intervalIntegral.integral_mono_on hτ0 hii.norm
              (by apply Continuous.intervalIntegrable; fun_prop)
            intro s hs
            have hsI : s ∈ Set.Icc (0 : ℝ) τ := by
              simpa [Set.uIcc_of_le hτ0] using hs
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _),
              mul_comm src.derivBound]
            exact mul_le_mul_of_nonneg_left
              (src.hderivBound s ⟨hsI.1, le_trans hsI.2 hτW⟩ n) (Real.exp_nonneg _)
        _ = src.derivBound * ∫ s in (0 : ℝ)..τ,
              Real.exp (-(τ - s) * (λ_ n)) := by
            rw [intervalIntegral.integral_const_mul]
    have hgain := ShenWork.IntervalDuhamelRegularity.parabolicGain_le_one
      (lam := (λ_ n)) (t := τ) hlam_nn hτ0
    have hint_le_inv :
        ∫ s in (0 : ℝ)..τ, Real.exp (-(τ - s) * (λ_ n)) ≤ 1 / (λ_ n) := by
      rw [le_div_iff₀ hlam_pos]
      linarith
    have hinv_le_recip : 1 / (λ_ n) ≤ reciprocalSquareTerm n := by
      rw [reciprocalSquareTerm, unitIntervalCosineEigenvalue]
      apply div_le_div_of_nonneg_left (by linarith) (by positivity)
      calc ((n : ℝ) * Real.pi) ^ 2
          = (n : ℝ) ^ 2 * Real.pi ^ 2 := by ring
        _ ≥ (n : ℝ) ^ 2 * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith [Real.pi_gt_three]
        _ = (n : ℝ) ^ 2 := mul_one _
    have hI' :
        |∫ s in (0 : ℝ)..τ, Real.exp (-(τ - s) * (λ_ n)) * src.adot s n|
          ≤ src.derivBound * reciprocalSquareTerm n :=
      le_trans hI (mul_le_mul_of_nonneg_left (hint_le_inv.trans hinv_le_recip) hdb_nn)
    have henvnn : 0 ≤ src.envelope n :=
      le_trans (abs_nonneg _) (src.henv_bound 0 ⟨le_rfl, le_trans hτ0 hτW⟩ n)
    linarith

private theorem deriv_term_abs_le
    {a₀ : ℕ → ℝ} {M : ℝ} {a : ℝ → ℕ → ℝ} {W a' τ : ℝ}
    (src : DuhamelSourceTimeC1On a 0 W) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (ha'pos : 0 < a') (hτ : τ ∈ Set.Icc a' W) (x : ℝ) (n : ℕ) :
    ‖(a τ n - (λ_ n) * localRestartCoeff a₀ a τ n) * cosineMode n x‖
      ≤ derivMajorant src a' M n := by
  have hcos_le : |cosineMode n x| ≤ 1 := by
    simp only [cosineMode]
    exact Real.abs_cos_le_one _
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (ha₀ 0)
  have hlam_nn : (0 : ℝ) ≤ (λ_ n) := by
    unfold unitIntervalCosineEigenvalue
    positivity
  have hτ0 : 0 ≤ τ := le_trans ha'pos.le hτ.1
  have hduh := duhamel_deriv_abs_le_on src hτ0 hτ.2 n
  have hhom :
      (λ_ n) * (Real.exp (-τ * (λ_ n)) * |a₀ n|)
        ≤ M * ((λ_ n) * Real.exp (-a' * (λ_ n))) := by
    have hexp_mono : Real.exp (-τ * (λ_ n)) ≤ Real.exp (-a' * (λ_ n)) :=
      Real.exp_le_exp_of_le (by nlinarith [hτ.1, hlam_nn])
    calc (λ_ n) * (Real.exp (-τ * (λ_ n)) * |a₀ n|)
        ≤ (λ_ n) * (Real.exp (-a' * (λ_ n)) * M) := by
          apply mul_le_mul_of_nonneg_left _ hlam_nn
          exact mul_le_mul hexp_mono (ha₀ n) (abs_nonneg _) (Real.exp_nonneg _)
      _ = M * ((λ_ n) * Real.exp (-a' * (λ_ n))) := by ring
  rw [Real.norm_eq_abs, abs_mul]
  calc |a τ n - (λ_ n) * localRestartCoeff a₀ a τ n| * |cosineMode n x|
      ≤ |a τ n - (λ_ n) * localRestartCoeff a₀ a τ n| * 1 :=
        mul_le_mul_of_nonneg_left hcos_le (abs_nonneg _)
    _ = |a τ n - (λ_ n) * localRestartCoeff a₀ a τ n| := mul_one _
    _ ≤ |a τ n - (λ_ n) * duhamelSpectralCoeff a τ n| +
          (λ_ n) * (Real.exp (-τ * (λ_ n)) * |a₀ n|) := by
        simp only [localRestartCoeff]
        have : a τ n - (λ_ n) * (Real.exp (-τ * (λ_ n)) * a₀ n +
              duhamelSpectralCoeff a τ n)
            = (a τ n - (λ_ n) * duhamelSpectralCoeff a τ n)
              - (λ_ n) * (Real.exp (-τ * (λ_ n)) * a₀ n) := by ring
        rw [this]
        calc |(a τ n - (λ_ n) * duhamelSpectralCoeff a τ n)
              - (λ_ n) * (Real.exp (-τ * (λ_ n)) * a₀ n)|
            ≤ |a τ n - (λ_ n) * duhamelSpectralCoeff a τ n| +
                |(λ_ n) * (Real.exp (-τ * (λ_ n)) * a₀ n)| := by
              rw [sub_eq_add_neg]
              exact (abs_add_le _ _).trans (by rw [abs_neg])
          _ = |a τ n - (λ_ n) * duhamelSpectralCoeff a τ n| +
                (λ_ n) * (Real.exp (-τ * (λ_ n)) * |a₀ n|) := by
              rw [abs_mul, abs_of_nonneg hlam_nn, abs_mul,
                abs_of_nonneg (Real.exp_nonneg _)]
    _ ≤ (2 * src.envelope n + src.derivBound * reciprocalSquareTerm n) +
          M * ((λ_ n) * Real.exp (-a' * (λ_ n))) := add_le_add hduh hhom
    _ = derivMajorant src a' M n := by
        unfold derivMajorant
        ring

private theorem localRestartCoeff_continuousOn_Icc
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {W a' : ℝ}
    (_src : DuhamelSourceTimeC1On a 0 W)
    (hcont_a : ∀ n, ContinuousOn (fun s : ℝ => a s n) (Set.Icc 0 W))
    (ha'pos : 0 < a') (n : ℕ) :
    ContinuousOn (fun τ : ℝ => localRestartCoeff a₀ a τ n) (Set.Icc a' W) := by
  intro τ hτ
  have hderiv := hasDerivWithinAt_localRestartCoeff_mul_cos
    (a₀ := a₀) hcont_a ha'pos hτ n 0
  have hcos0 : cosineMode n 0 = 1 := by
    simp [cosineMode]
  have hcont_mul :
      ContinuousWithinAt (fun r : ℝ => localRestartCoeff a₀ a r n * cosineMode n 0)
        (Set.Icc a' W) τ := hderiv.continuousWithinAt
  have hfun :
      (fun r : ℝ => localRestartCoeff a₀ a r n * cosineMode n 0)
        = fun r : ℝ => localRestartCoeff a₀ a r n := by
    funext r
    rw [hcos0, mul_one]
  simpa [hfun] using hcont_mul

set_option maxHeartbeats 1600000 in
-- The closed-window tsum proof elaborates the per-mode continuity and majorant blocks.
/-- Closed-window `_On` mirror of `restartDerivField_continuousOn_joint`. -/
theorem restartDerivField_continuousOn_joint_On
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (_hM₀ : 0 ≤ M₀) (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} {W a' : ℝ} (src : DuhamelSourceTimeC1On a 0 W)
    (ha'pos : 0 < a') :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        ∑' n, (a p.1 n - unitIntervalCosineEigenvalue n *
          localRestartCoeff a₀ a p.1 n) * cosineMode n p.2)
      (Set.Icc a' W ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hcont_a : ∀ n, ContinuousOn (fun s : ℝ => a s n) (Set.Icc 0 W) :=
    source_coeff_continuousOn_of_timeC1On src
  apply continuousOn_tsum
  · intro n
    have ha_cont : ContinuousOn (fun p : ℝ × ℝ => a p.1 n)
        (Set.Icc a' W ×ˢ Set.Icc (0 : ℝ) 1) := by
      exact (hcont_a n).comp continuous_fst.continuousOn (fun p hp => by
        exact ⟨le_trans ha'pos.le (Set.mem_prod.1 hp).1.1, (Set.mem_prod.1 hp).1.2⟩)
    have hlc_cont : ContinuousOn (fun p : ℝ × ℝ => localRestartCoeff a₀ a p.1 n)
        (Set.Icc a' W ×ˢ Set.Icc (0 : ℝ) 1) := by
      exact (localRestartCoeff_continuousOn_Icc src hcont_a ha'pos n).comp
        continuous_fst.continuousOn (fun p hp => (Set.mem_prod.1 hp).1)
    have hcoeff : ContinuousOn
        (fun p : ℝ × ℝ => a p.1 n - unitIntervalCosineEigenvalue n *
          localRestartCoeff a₀ a p.1 n)
        (Set.Icc a' W ×ˢ Set.Icc (0 : ℝ) 1) :=
      ha_cont.sub (continuousOn_const.mul hlc_cont)
    have hcos : ContinuousOn (fun p : ℝ × ℝ => cosineMode n p.2)
        (Set.Icc a' W ×ˢ Set.Icc (0 : ℝ) 1) := by
      change ContinuousOn
        (fun p : ℝ × ℝ => Real.cos ((n : ℝ) * Real.pi * p.2))
        (Set.Icc a' W ×ˢ Set.Icc (0 : ℝ) 1)
      exact ((Real.continuous_cos.comp
        (continuous_const.mul continuous_snd)).continuousOn)
    exact hcoeff.mul hcos
  · exact derivMajorant_summable src (M := M₀) ha'pos
  · intro n p hp
    exact deriv_term_abs_le src ha₀ ha'pos (Set.mem_prod.1 hp).1 p.2 n

/-- Closed-window `_On` mirror of
`restartFieldTimeDeriv_continuousOn_joint`, obtained from the coefficient-window
base atom and the affine shift `σ ↦ σ - offset`. -/
theorem restartFieldTimeDeriv_continuousOn_joint_On
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} {offset W : ℝ} (src : DuhamelSourceTimeC1On a 0 W)
    {a' Wf : ℝ} (ha'pos : 0 < a')
    (hshift : Set.MapsTo (fun s : ℝ => s - offset)
      (Set.Icc a' Wf) (Set.Icc a' W)) :
    ContinuousOn (Function.uncurry (fun σ x => restartFieldTimeDeriv a₀ a offset σ x))
      (Set.Icc a' Wf ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hbase := restartDerivField_continuousOn_joint_On
    (a₀ := a₀) (M₀ := M₀) hM₀ ha₀ src ha'pos
  have hmap : Set.MapsTo
      (fun p : ℝ × ℝ => ((p.1 - offset, p.2) : ℝ × ℝ))
      (Set.Icc a' Wf ×ˢ Set.Icc (0 : ℝ) 1)
      (Set.Icc a' W ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro p hp
    exact Set.mk_mem_prod (hshift (Set.mem_prod.1 hp).1) (Set.mem_prod.1 hp).2
  have hcont_shift : ContinuousOn
      (fun p : ℝ × ℝ => ((p.1 - offset, p.2) : ℝ × ℝ))
      (Set.Icc a' Wf ×ˢ Set.Icc (0 : ℝ) 1) :=
    ((continuous_fst.sub continuous_const).prodMk continuous_snd).continuousOn
  have hcomp := hbase.comp hcont_shift hmap
  refine hcomp.congr (fun p hp => ?_)
  rfl

end ShenWork.IntervalPicardIterateTimeC1JointEndpoint
