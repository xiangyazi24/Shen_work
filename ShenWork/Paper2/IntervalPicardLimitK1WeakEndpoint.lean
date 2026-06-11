import ShenWork.Paper2.IntervalPicardLimitK1Weak
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On
import ShenWork.PDE.HasDerivWithinAtTsum

open MeasureTheory Filter Topology Set
open scoped Topology

noncomputable section

namespace ShenWork.IntervalPicardLimitK1WeakEndpoint

open ShenWork.IntervalDuhamelClosedC2
  (duhamelSpectralCoeff cosineCoeff_summable_of_eigenvalue_summable)
open ShenWork.IntervalSourceCoefficientTimeC1
  (localRestartCoeff)
open ShenWork.IntervalDuhamelSourceTimeC1On
  (DuhamelSourceTimeC1On duhamelCoeff_eigenvalue_mul_on
    duhamelSpectralCoeff_eigenvalue_summable_on)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDomainRegularityBootstrap
  (reciprocalSquareTerm reciprocalSquareTerm_summable)

local notation "λ_" n => unitIntervalCosineEigenvalue n

private def derivMajorant (src : DuhamelSourceTimeC1On a 0 W) (a' M : ℝ) (n : ℕ) : ℝ :=
  M * (((λ_ n)) * Real.exp (-a' * ((λ_ n)))) +
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

private theorem duhamelSpectralCoeff_hasDerivWithinAt_on
    {a : ℝ → ℕ → ℝ} {W a' τ : ℝ}
    (hcont_a : ∀ n, ContinuousOn (fun s => a s n) (Set.Icc 0 W))
    (ha'pos : 0 < a') (hτ : τ ∈ Set.Icc a' W) (n : ℕ) :
    HasDerivWithinAt (fun r => duhamelSpectralCoeff a r n)
      (a τ n - (λ_ n) * duhamelSpectralCoeff a τ n) (Set.Icc a' W) τ := by
  set lam := (λ_ n)
  set G : ℝ → ℝ := fun r => ∫ s in (0 : ℝ)..r, Real.exp (s * lam) * a s n
  have hfactor : ∀ r, duhamelSpectralCoeff a r n = Real.exp (-r * lam) * G r := by
    intro r
    change (∫ s in (0 : ℝ)..r, _) = _
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun s _ => by
      rw [show -(r - s) * lam = -r * lam + s * lam from by ring,
        Real.exp_add, mul_assoc])
  have hcont_int : ContinuousOn (fun s => Real.exp (s * lam) * a s n) (Set.Icc 0 W) :=
    ((Real.continuous_exp.comp (continuous_id.mul continuous_const)).continuousOn).mul
      (hcont_a n)
  have hτ0W : τ ∈ Set.Icc (0 : ℝ) W := ⟨le_trans ha'pos.le hτ.1, hτ.2⟩
  have hG : HasDerivWithinAt G (Real.exp (τ * lam) * a τ n) (Set.Icc a' W) τ := by
    by_cases hτltW : τ < W
    · have hτint : τ ∈ Set.Ioo (0 : ℝ) W :=
        ⟨lt_of_lt_of_le ha'pos hτ.1, hτltW⟩
      have hnhds : Set.Icc (0 : ℝ) W ∈ 𝓝 τ :=
        mem_of_superset (isOpen_Ioo.mem_nhds hτint) Set.Ioo_subset_Icc_self
      have hcont_at : ContinuousAt (fun s => Real.exp (s * lam) * a s n) τ :=
        (hcont_int.continuousWithinAt hτ0W).continuousAt hnhds
      have hcont_open :
          ContinuousOn (fun s => Real.exp (s * lam) * a s n) (Set.Ioo (0 : ℝ) W) :=
        hcont_int.mono Set.Ioo_subset_Icc_self
      have hsm :
          StronglyMeasurableAtFilter (fun s => Real.exp (s * lam) * a s n) (𝓝 τ) :=
        hcont_open.stronglyMeasurableAtFilter isOpen_Ioo τ hτint
      have hint : IntervalIntegrable (fun s => Real.exp (s * lam) * a s n)
          volume 0 τ :=
        (hcont_int.mono (fun y hy => ⟨hy.1, le_trans hy.2 hτ.2⟩)).intervalIntegrable_of_Icc
          hτ0W.1
      exact (intervalIntegral.integral_hasDerivAt_right hint
        hsm hcont_at).hasDerivWithinAt
    · have hτeqW : τ = W := le_antisymm hτ.2 (le_of_not_gt hτltW)
      subst τ
      have hWpos : 0 < W := lt_of_lt_of_le ha'pos hτ.1
      have hW0 : 0 ≤ W := hWpos.le
      have hIcc_mem : Set.Icc (0 : ℝ) W ∈ 𝓝[Set.Iic W] W := by
        have hIoi : Set.Ioi (0 : ℝ) ∈ 𝓝[Set.Iic W] W :=
          mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hWpos)
        filter_upwards [self_mem_nhdsWithin, hIoi] with y hyW hy0
        exact ⟨hy0.le, hyW⟩
      have hcw : ContinuousWithinAt (fun s => Real.exp (s * lam) * a s n)
          (Set.Icc (0 : ℝ) W) W :=
        hcont_int.continuousWithinAt ⟨hW0, le_rfl⟩
      have hcw_iic : ContinuousWithinAt (fun s => Real.exp (s * lam) * a s n)
          (Set.Iic W) W :=
        hcw.mono_of_mem_nhdsWithin hIcc_mem
      have hsm :
          StronglyMeasurableAtFilter (fun s => Real.exp (s * lam) * a s n)
            (𝓝[Set.Iic W] W) :=
        ⟨Set.Icc (0 : ℝ) W, hIcc_mem,
          hcont_int.aestronglyMeasurable measurableSet_Icc⟩
      have hleft : HasDerivWithinAt G (Real.exp (W * lam) * a W n)
          (Set.Iic W) W :=
        intervalIntegral.integral_hasDerivWithinAt_right
          (a := (0 : ℝ)) (b := W) (s := Set.Iic W) (t := Set.Iic W)
          (hcont_int.intervalIntegrable_of_Icc hW0) hsm hcw_iic
      exact hleft.mono (fun y hy => hy.2)
  have hd_exp : HasDerivWithinAt (fun r => Real.exp (-r * lam))
      (-lam * Real.exp (-τ * lam)) (Set.Icc a' W) τ :=
    by
      have hAt : HasDerivAt (fun r => Real.exp (-r * lam))
          (-lam * Real.exp (-τ * lam)) τ := by
        have h1 : HasDerivAt (fun r : ℝ => -r * lam) (-1 * lam) τ :=
          (hasDerivAt_id τ).neg.mul_const lam
        have h2 := h1.exp
        simp only [neg_mul, one_mul] at h2 ⊢
        convert h2 using 1
        ring
      exact hAt.hasDerivWithinAt
  have hexp_cancel : Real.exp (-τ * lam) * Real.exp (τ * lam) = 1 := by
    rw [← Real.exp_add, show -τ * lam + τ * lam = 0 from by ring, Real.exp_zero]
  have hderiv_val :
      -lam * Real.exp (-τ * lam) * G τ +
          Real.exp (-τ * lam) * (Real.exp (τ * lam) * a τ n) =
        a τ n - lam * (Real.exp (-τ * lam) * G τ) := by
    rw [← mul_assoc (Real.exp _), hexp_cancel, one_mul]
    ring
  have hprod : HasDerivWithinAt (fun r => Real.exp (-r * lam) * G r)
      (a τ n - lam * (Real.exp (-τ * lam) * G τ)) (Set.Icc a' W) τ :=
    (hd_exp.mul hG).congr_deriv hderiv_val
  rw [show (fun r => duhamelSpectralCoeff a r n) =
      (fun r => Real.exp (-r * lam) * G r) from funext hfactor, hfactor τ]
  exact hprod

theorem hasDerivWithinAt_localRestartCoeff_mul_cos
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {W a' τ : ℝ}
    (hcont_a : ∀ n, ContinuousOn (fun s => a s n) (Set.Icc 0 W))
    (ha'pos : 0 < a') (hτ : τ ∈ Set.Icc a' W) (n : ℕ) (x : ℝ) :
    HasDerivWithinAt (fun r => localRestartCoeff a₀ a r n * cosineMode n x)
      ((a τ n - unitIntervalCosineEigenvalue n * localRestartCoeff a₀ a τ n)
        * cosineMode n x) (Set.Icc a' W) τ := by
  set lam := (λ_ n)
  have hd_hom : HasDerivWithinAt (fun r => Real.exp (-r * lam) * a₀ n)
      (-lam * Real.exp (-τ * lam) * a₀ n) (Set.Icc a' W) τ :=
    by
      have hAt : HasDerivAt (fun r => Real.exp (-r * lam) * a₀ n)
          (-lam * Real.exp (-τ * lam) * a₀ n) τ := by
        have h1 : HasDerivAt (fun r : ℝ => -r * lam) (-1 * lam) τ :=
          (hasDerivAt_id τ).neg.mul_const lam
        have h2 := (h1.exp).mul_const (a₀ n)
        simp only [neg_mul, one_mul] at h2 ⊢
        convert h2 using 1
        ring
      exact hAt.hasDerivWithinAt
  have hd_duh := duhamelSpectralCoeff_hasDerivWithinAt_on
    hcont_a ha'pos hτ n
  have hsum : HasDerivWithinAt (fun r => localRestartCoeff a₀ a r n)
      (a τ n - lam * localRestartCoeff a₀ a τ n) (Set.Icc a' W) τ := by
    have hadd := hd_hom.add hd_duh
    have hfun : (fun r => localRestartCoeff a₀ a r n)
        = (fun r => Real.exp (-r * lam) * a₀ n + duhamelSpectralCoeff a r n) := by
      funext r
      simp only [localRestartCoeff, show (λ_ n) = lam from rfl]
    rw [hfun]
    refine hadd.congr_deriv ?_
    simp only [localRestartCoeff, show (λ_ n) = lam from rfl]
    ring
  exact hsum.mul_const _

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
        ≤ src.derivBound * ∫ s in (0 : ℝ)..τ, Real.exp (-(τ - s) * (λ_ n)) := by
      have hkernel : Continuous (fun s : ℝ => Real.exp (-(τ - s) * (λ_ n))) := by fun_prop
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

private theorem summable_localRestartCoeff_mul_cos
    {a₀ : ℕ → ℝ} {M : ℝ} {a : ℝ → ℕ → ℝ} {W τ : ℝ}
    (src : DuhamelSourceTimeC1On a 0 W) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (hτ : 0 < τ) (hτW : τ ≤ W) (x : ℝ) :
    Summable (fun n => localRestartCoeff a₀ a τ n * cosineMode n x) := by
  have hcos_le : ∀ n, |cosineMode n x| ≤ 1 := fun n => by
    simp only [cosineMode]
    exact Real.abs_cos_le_one _
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (ha₀ 0)
  have hhom : Summable (fun n =>
      Real.exp (-τ * ((λ_ n))) * a₀ n * cosineMode n x) := by
    refine Summable.of_norm_bounded
      (g := fun n => Real.exp (-τ * ((λ_ n))) * M)
      ((ShenWork.IntervalSemigroupComposition.expEigSummable hτ).mul_right M)
      (fun n => ?_)
    rw [Real.norm_eq_abs,
      show Real.exp (-τ * ((λ_ n))) * a₀ n * cosineMode n x =
        Real.exp (-τ * ((λ_ n))) * (a₀ n * cosineMode n x) from by ring,
      abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (by
        rw [abs_mul]
        calc |a₀ n| * |cosineMode n x| ≤ M * 1 :=
              mul_le_mul (ha₀ n) (hcos_le n) (abs_nonneg _) hM0
          _ = M := mul_one _)
      (Real.exp_nonneg _)
  have hduh : Summable (fun n => duhamelSpectralCoeff a τ n * cosineMode n x) := by
    have hduh_eig := duhamelSpectralCoeff_eigenvalue_summable_on
      (lo := 0) (hi := W) (t := τ) src hτ hτW
    have ⟨_, habs⟩ := cosineCoeff_summable_of_eigenvalue_summable hduh_eig
    refine Summable.of_norm_bounded habs (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hcos_le n)
  refine (hhom.add hduh).congr (fun n => ?_)
  simp only [localRestartCoeff]
  ring

set_option maxHeartbeats 1600000 in
-- The closed-window series assembly reuses the dominated-term proof at every mode.
theorem restartCosineSeries_hasDerivWithinAt_time_bdd_on
    {a₀ : ℕ → ℝ} {M : ℝ} (ha₀ : ∀ n, |a₀ n| ≤ M)
    {a : ℝ → ℕ → ℝ} {W : ℝ}
    (src : DuhamelSourceTimeC1On a 0 W)
    (hcont_a : ∀ n, ContinuousOn (fun s => a s n) (Set.Icc 0 W))
    {τ₀ a' : ℝ} (ha'pos : 0 < a') (ha'τ₀ : a' ≤ τ₀) (hτ₀W : τ₀ ≤ W) (x : ℝ) :
    HasDerivWithinAt
      (fun τ => ∑' n, localRestartCoeff a₀ a τ n * cosineMode n x)
      (∑' n, (a τ₀ n - unitIntervalCosineEigenvalue n *
        localRestartCoeff a₀ a τ₀ n) * cosineMode n x)
      (Set.Icc a' W) τ₀ := by
  set u : ℕ → ℝ := fun n => derivMajorant src a' M n
  have hu : Summable u := by
    simpa [u] using derivMajorant_summable src ha'pos (M := M)
  have hτ₀mem : τ₀ ∈ Set.Icc a' W := ⟨ha'τ₀, hτ₀W⟩
  have hg : ∀ n, ∀ τ ∈ Set.Icc a' W,
      HasDerivWithinAt
        (fun τ => localRestartCoeff a₀ a τ n * cosineMode n x)
        ((a τ n - unitIntervalCosineEigenvalue n *
          localRestartCoeff a₀ a τ n) * cosineMode n x)
        (Set.Icc a' W) τ :=
    fun n τ hτ => hasDerivWithinAt_localRestartCoeff_mul_cos
      hcont_a ha'pos hτ n x
  have hg' : ∀ n, ∀ τ ∈ Set.Icc a' W,
      |(a τ n - unitIntervalCosineEigenvalue n *
          localRestartCoeff a₀ a τ n) * cosineMode n x| ≤ u n := by
    intro n τ hτ
    simpa [Real.norm_eq_abs, u] using deriv_term_abs_le src ha₀ ha'pos hτ x n
  have hg0 : Summable (fun n => localRestartCoeff a₀ a τ₀ n * cosineMode n x) :=
    summable_localRestartCoeff_mul_cos src ha₀
      (lt_of_lt_of_le ha'pos ha'τ₀) hτ₀W x
  exact ShenWork.HasDerivWithinAtTsum.hasDerivWithinAt_tsum
    (convex_Icc a' W) hu hg hg' hτ₀mem hg0 hτ₀mem

end ShenWork.IntervalPicardLimitK1WeakEndpoint
