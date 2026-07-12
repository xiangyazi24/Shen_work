/-
  Tested-spectral-identity helper layer for the truncated Picard route.

  This file is additive.  It reduces the `testedSpectralIdentities` sorry of
  `IntervalChiNegV5SelfContained` (the three tested identities behind the A1
  negative-part weak-test atom) to two named analytic frontiers:

  * `cosine_parseval_pairing` — the bilinear cosine Parseval pairing on the
    unit interval (route: polarize
    `CosineParsevalBridge.unitIntervalEvenReflection_fourier_parseval_unit_mass`);
  * `truncatedPositiveTimeSpectralData_of_existenceData` — the positive-time
    spectral regularity bundle for the truncated Picard limit (route: the
    truncated analog of the ℓ¹ coefficient ladder +
    `IntervalMildTimeDerivReconstruction`).

  Everything else — the `∫ ↔ ∑'` pairing interchange, the single-mode Neumann
  gradient IBP with a countable exceptional set (which covers the negative-part
  test `φ = -u_-`, non-differentiable exactly at the isolated transversal
  zeros of `u_t`), the frequency/sine-to-cosine-derivative coefficient
  transfer for the chem branch, the flux endpoint vanishing, and the three
  assembly theorems — is proved here without `sorry`.
-/
import ShenWork.Paper2.IntervalBFormCron2TruncatedCoefficientWeakTest
import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergyA2
import ShenWork.Paper2.IntervalTruncatedPositiveTimeBootstrap
import ShenWork.Paper2.IntervalMildPicardRegularity
import ShenWork.Paper2.IntervalDomainL2UEnergyCombine
import ShenWork.Paper2.IntervalDuhamelIntegrability
import ShenWork.Paper2.IntervalNeumannHeatGradientL2BrickB
import ShenWork.PDE.P3MoserEnergyContinuity
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

open MeasureTheory Set
open scoped BigOperators Topology ENNReal

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure
   intervalMeasure_integrable_of_abs_bound)
open ShenWork.HeatKernelGradientEstimates
  (unitIntervalCosineHilbertBasis unitIntervalNormalizedCosineLp
   unitIntervalCosineLp unitIntervalCosineLp_inner_eq_coeff)
open ShenWork.CosineSpectrum
  (cosineMode cosineMode_hasDerivAt cosineMode_deriv
   cosineMode_neumann_left cosineMode_neumann_right)
open ShenWork.IntervalConjugateCosineSeries (intervalSineInner)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_eq_factor_mul_integral cosineCoeffs_pos_eq_integral
   cosineCoeffs_zero_eq_integral)

/-! ## Measure conversion -/

/-- The `intervalMeasure 1` integral is the `[0,1]` interval integral. -/
theorem intervalMeasure_one_integral_eq_intervalIntegral (f : ℝ → ℝ) :
    (∫ y, f y ∂ intervalMeasure 1) = ∫ y in (0 : ℝ)..1, f y := by
  simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
  change (∫ y in Set.Icc (0 : ℝ) 1, f y ∂volume) = ∫ y in (0 : ℝ)..1, f y
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- Complex-valued version of `intervalMeasure_one_integral_eq_intervalIntegral`. -/
theorem intervalMeasure_one_integral_eq_intervalIntegral_complex (f : ℝ → ℂ) :
    (∫ y, f y ∂ intervalMeasure 1) = ∫ y in (0 : ℝ)..1, f y := by
  simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
  change (∫ y in Set.Icc (0 : ℝ) 1, f y ∂volume) = ∫ y in (0 : ℝ)..1, f y
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

lemma memLp_two_of_continuousOn_Icc
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    MemLp f (2 : ℝ≥0∞) (intervalMeasure 1) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hfm :
      AEStronglyMeasurable f (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
      hf
  refine MemLp.of_bound hfm C ?_
  unfold intervalMeasure ShenWork.IntervalDomain.intervalSet
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simpa [Real.norm_eq_abs] using hC x hx

lemma memLp_two_of_aestronglyMeasurable_bound_Icc
    {φ : ℝ → ℝ}
    (hφm : AEStronglyMeasurable φ (intervalMeasure 1))
    {Cφ : ℝ} (hφb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |φ x| ≤ Cφ) :
    MemLp φ (2 : ℝ≥0∞) (intervalMeasure 1) := by
  refine MemLp.of_bound hφm Cφ ?_
  unfold intervalMeasure ShenWork.IntervalDomain.intervalSet
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simpa [Real.norm_eq_abs] using hφb x hx

/-! ## The `∫ ↔ ∑'` pairing interchange -/

/-- **Pairing interchange.**  If `w` agrees on `[0,1]` with an ℓ¹ mode series
`∑' n, c n * e n x` (each mode continuous, bounded by `B n` on `[0,1]`, with
`∑ |c n| * B n < ∞`), then pairing with a bounded a.e.-measurable test `ψ`
interchanges with the sum. -/
theorem integral_tsum_pairing
    {w ψ : ℝ → ℝ} {c B : ℕ → ℝ} {e : ℕ → ℝ → ℝ} {Cψ : ℝ}
    (he : ∀ n, Continuous (e n))
    (heB : ∀ n, ∀ x ∈ Set.Icc (0 : ℝ) 1, |e n x| ≤ B n)
    (hsum : Summable (fun n => |c n| * B n))
    (hrep : ∀ x ∈ Set.Icc (0 : ℝ) 1, w x = ∑' n, c n * e n x)
    (hψm : AEStronglyMeasurable ψ (intervalMeasure 1))
    (hψb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |ψ x| ≤ Cψ) :
    (∫ x, w x * ψ x ∂ intervalMeasure 1)
      = ∑' n, c n * ∫ x in (0 : ℝ)..1, e n x * ψ x := by
  classical
  have h01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    Set.left_mem_Icc.mpr (by norm_num)
  have hCψ : 0 ≤ Cψ :=
    le_trans (abs_nonneg _) (hψb 0 h01)
  set F : ℕ → ℝ → ℝ := fun n x => c n * (e n x * ψ x) with hF
  have hmemae : ∀ᵐ x ∂ intervalMeasure 1, x ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
    exact ae_restrict_mem measurableSet_Icc
  have hcong :
      (fun x => w x * ψ x) =ᵐ[intervalMeasure 1] fun x => ∑' n, F n x := by
    filter_upwards [hmemae] with x hx
    rw [hrep x hx, ← tsum_mul_right]
    exact tsum_congr fun n => by simp only [hF]; ring
  have hFm : ∀ n, AEStronglyMeasurable (F n) (intervalMeasure 1) := fun n =>
    (((he n).aestronglyMeasurable).mul hψm).const_mul (c n)
  have hBnn : ∀ n, 0 ≤ B n := fun n =>
    le_trans (abs_nonneg _) (heB n 0 h01)
  have hFbound : ∀ n, ∀ᵐ x ∂ intervalMeasure 1,
      ‖F n x‖ ≤ |c n| * B n * Cψ := by
    intro n
    filter_upwards [hmemae] with x hx
    have h1 : |e n x| ≤ B n := heB n x hx
    have h2 : |ψ x| ≤ Cψ := hψb x hx
    calc ‖F n x‖ = |c n| * (|e n x| * |ψ x|) := by
          rw [Real.norm_eq_abs]
          simp only [hF, abs_mul]
      _ ≤ |c n| * (B n * Cψ) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul h1 h2 (abs_nonneg _) (hBnn n)) (abs_nonneg _)
      _ = |c n| * B n * Cψ := by ring
  have hFint : ∀ n, Integrable (F n) (intervalMeasure 1) := fun n =>
    Integrable.mono' (integrable_const _) (hFm n) (hFbound n)
  have hμ : (intervalMeasure 1).real Set.univ = 1 := by
    rw [intervalMeasure, ShenWork.IntervalDomain.intervalSet,
      measureReal_restrict_apply_univ, measureReal_def, Real.volume_Icc]
    simp
  have hFsum : Summable (fun n => ∫ x, ‖F n x‖ ∂ intervalMeasure 1) := by
    refine Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun x => norm_nonneg _)
      (fun n => ?_) (hsum.mul_right Cψ)
    calc ∫ x, ‖F n x‖ ∂ intervalMeasure 1
        ≤ ∫ _x, |c n| * B n * Cψ ∂ intervalMeasure 1 :=
          integral_mono_ae ((hFint n).norm) (integrable_const _) (hFbound n)
      _ = |c n| * B n * Cψ := by
          rw [integral_const, hμ]
          simp
  calc (∫ x, w x * ψ x ∂ intervalMeasure 1)
      = ∫ x, (∑' n, F n x) ∂ intervalMeasure 1 := integral_congr_ae hcong
    _ = ∑' n, ∫ x, F n x ∂ intervalMeasure 1 :=
        (integral_tsum_of_summable_integral_norm hFint hFsum).symm
    _ = ∑' n, c n * ∫ x in (0 : ℝ)..1, e n x * ψ x := by
        refine tsum_congr fun n => ?_
        simp only [hF]
        rw [integral_const_mul, intervalMeasure_one_integral_eq_intervalIntegral]

/-! ## Single-mode Neumann gradient IBP with a countable exceptional set -/

private theorem deriv_cosineMode_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => deriv (cosineMode n) y)
      (-(unitIntervalCosineEigenvalue n) * cosineMode n x) x := by
  have hfun : (fun y : ℝ => deriv (cosineMode n) y)
      = fun y : ℝ => -((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * y) := by
    funext y; exact cosineMode_deriv n y
  rw [hfun]
  have hsin : HasDerivAt (fun y : ℝ => Real.sin ((n : ℝ) * Real.pi * y))
      (Real.cos ((n : ℝ) * Real.pi * x) * ((n : ℝ) * Real.pi)) x := by
    have hlin : HasDerivAt (fun y : ℝ => (n : ℝ) * Real.pi * y)
        ((n : ℝ) * Real.pi) x := by
      simpa using (hasDerivAt_id x).const_mul ((n : ℝ) * Real.pi)
    exact (Real.hasDerivAt_sin ((n : ℝ) * Real.pi * x)).comp x hlin
  have := hsin.const_mul (-((n : ℝ) * Real.pi))
  convert this using 1
  simp only [unitIntervalCosineEigenvalue, cosineMode]
  ring

private theorem continuous_deriv_cosineMode (n : ℕ) :
    Continuous fun x : ℝ => deriv (cosineMode n) x := by
  have hfun : (fun x : ℝ => deriv (cosineMode n) x)
      = fun x : ℝ => -((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x) := by
    funext x; exact cosineMode_deriv n x
  rw [hfun]
  fun_prop

private theorem continuous_cosineMode (n : ℕ) : Continuous (cosineMode n) := by
  show Continuous fun x : ℝ => Real.cos ((n : ℝ) * Real.pi * x)
  fun_prop

private theorem abs_deriv_cosineMode_le (n : ℕ) (x : ℝ) :
    |deriv (cosineMode n) x| ≤ (n : ℝ) * Real.pi := by
  rw [cosineMode_deriv n x, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) * Real.pi)]
  calc (n : ℝ) * Real.pi * |Real.sin ((n : ℝ) * Real.pi * x)|
      ≤ (n : ℝ) * Real.pi * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)
    _ = (n : ℝ) * Real.pi := by ring

/-- **Single-mode gradient IBP, countable exceptional set.**
`∫₀¹ e_n' φ' = λ_n ∫₀¹ e_n φ` for a test `φ` that is continuous on `[0,1]` and
differentiable off a countable set.  The boundary terms vanish because
`e_n'(0) = e_n'(1) = 0`; no boundary condition on `φ` is used. -/
theorem cosineMode_gradient_testCoeff_eq_off_countable
    (n : ℕ) {φ : ℝ → ℝ} {s : Set ℝ} (hs : s.Countable)
    (hφc : ContinuousOn φ (Set.Icc (0 : ℝ) 1))
    (hφd : ∀ x ∈ Set.Ioo (0 : ℝ) 1 \ s, HasDerivAt φ (deriv φ x) x)
    (hφ'i : IntervalIntegrable (deriv φ) volume 0 1) :
    (∫ x in (0 : ℝ)..1, deriv (cosineMode n) x * deriv φ x)
      = unitIntervalCosineEigenvalue n * cosineTestCoeff φ n := by
  set A : ℝ → ℝ := fun x =>
    -(unitIntervalCosineEigenvalue n) * (cosineMode n x * φ x) with hA
  set Bf : ℝ → ℝ := fun x => deriv (cosineMode n) x * deriv φ x with hB
  have hFc : ContinuousOn (fun x => deriv (cosineMode n) x * φ x)
      (Set.Icc (0 : ℝ) 1) :=
    ((continuous_deriv_cosineMode n).continuousOn).mul hφc
  have hFd : ∀ x ∈ Set.Ioo (0 : ℝ) 1 \ s,
      HasDerivAt (fun y => deriv (cosineMode n) y * φ y) (A x + Bf x) x := by
    intro x hx
    have h2 := (deriv_cosineMode_hasDerivAt n x).mul (hφd x hx)
    have harr : -(unitIntervalCosineEigenvalue n) * cosineMode n x * φ x
          + deriv (cosineMode n) x * deriv φ x
        = A x + Bf x := by
      simp only [hA, hB]; ring
    rw [← harr]
    exact h2
  have hAi : IntervalIntegrable A volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (continuousOn_const.mul
      (((continuous_cosineMode n).continuousOn).mul hφc))
  have hBi : IntervalIntegrable Bf volume 0 1 :=
    hφ'i.continuousOn_mul ((continuous_deriv_cosineMode n).continuousOn)
  have hFTC :=
    MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
      (fun x => deriv (cosineMode n) x * φ x) (fun x => A x + Bf x)
      (by norm_num : (0 : ℝ) ≤ 1) hs hFc hFd (hAi.add hBi)
  have hbdry : deriv (cosineMode n) 1 * φ 1 - deriv (cosineMode n) 0 * φ 0 = 0 := by
    rw [cosineMode_neumann_left n, cosineMode_neumann_right n]
    ring
  rw [hbdry] at hFTC
  have hsplit : (∫ x in (0 : ℝ)..1, A x) + (∫ x in (0 : ℝ)..1, Bf x) = 0 := by
    rw [← intervalIntegral.integral_add hAi hBi]
    exact hFTC
  have hAval : (∫ x in (0 : ℝ)..1, A x)
      = -(unitIntervalCosineEigenvalue n) * cosineTestCoeff φ n := by
    simp only [hA]
    rw [intervalIntegral.integral_const_mul]
    rfl
  have : (∫ x in (0 : ℝ)..1, Bf x)
      = unitIntervalCosineEigenvalue n * cosineTestCoeff φ n := by
    have := hsplit
    rw [hAval] at this
    linarith
  simpa only [hB] using this

/-! ## Chem-branch coefficient transfer and endpoint vanishing -/

/-- For a `C¹` flux vanishing at both endpoints, the frequency-weighted sine
pairing equals the Neumann cosine coefficient of the derivative:
`nπ·⟨g, sin_n⟩ = (ĝ')_n`. -/
theorem freq_sineInner_eq_cosineCoeffs_deriv
    {g : ℝ → ℝ} {s_g : Set ℝ} (hs_g : s_g.Countable)
    (hgc : ContinuousOn g (Set.Icc (0 : ℝ) 1))
    (hg : ∀ x ∈ Set.Ioo (0 : ℝ) 1 \ s_g, HasDerivAt g (deriv g x) x)
    (hg'i : IntervalIntegrable (deriv g) volume 0 1)
    (h0 : g 0 = 0) (h1 : g 1 = 0) (n : ℕ) :
    ((n : ℝ) * Real.pi) * intervalSineInner g n = cosineCoeffs (deriv g) n := by
  have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 :=
    Set.uIcc_of_le (by norm_num)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hFTC : (∫ x in (0 : ℝ)..1, deriv g x) = g 1 - g 0 :=
      MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
        g (deriv g) (by norm_num : (0 : ℝ) ≤ 1) hs_g hgc hg hg'i
    have : cosineCoeffs (deriv g) 0 = ∫ x in (0 : ℝ)..1, deriv g x := by
      rw [cosineCoeffs_eq_factor_mul_integral]
      simp
    rw [this, hFTC, h0, h1]
    simp [intervalSineInner]
  · have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
    have hFc : ContinuousOn (fun y => cosineMode n y * g y) (Set.Icc (0 : ℝ) 1) :=
      ((continuous_cosineMode n).continuousOn).mul hgc
    have hFd : ∀ x ∈ Set.Ioo (0 : ℝ) 1 \ s_g,
        HasDerivAt (fun y => cosineMode n y * g y)
          (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x) * g x
            + cosineMode n x * deriv g x) x := by
      intro x hx
      exact (cosineMode_hasDerivAt n x).mul (hg x hx)
    have hAi : IntervalIntegrable
        (fun x => -((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x) * g x)
        volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [huIcc]
      exact (Continuous.continuousOn (by fun_prop)).mul hgc
    have hBi : IntervalIntegrable (fun x => cosineMode n x * deriv g x)
        volume 0 1 :=
      hg'i.continuousOn_mul ((continuous_cosineMode n).continuousOn)
    have hFTC :=
      MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
        (fun y => cosineMode n y * g y)
        (fun x => -((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x) * g x
          + cosineMode n x * deriv g x)
        (by norm_num : (0 : ℝ) ≤ 1) hs_g hFc hFd (hAi.add hBi)
    have hbdry : cosineMode n 1 * g 1 - cosineMode n 0 * g 0 = 0 := by
      rw [h0, h1]; ring
    rw [hbdry] at hFTC
    have hsplit :
        (∫ x in (0 : ℝ)..1,
            -((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x) * g x)
          + (∫ x in (0 : ℝ)..1, cosineMode n x * deriv g x) = 0 := by
      rw [← intervalIntegral.integral_add hAi hBi]
      exact hFTC
    have hsin_int :
        (∫ x in (0 : ℝ)..1,
            -((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x) * g x)
          = -((n : ℝ) * Real.pi) *
              ∫ x in (0 : ℝ)..1, Real.sin ((n : ℝ) * Real.pi * x) * g x := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ => ?_
      ring
    rw [cosineCoeffs_pos_eq_integral hne]
    simp only [intervalSineInner, hne, if_false]
    rw [hsin_int] at hsplit
    have : (∫ x in (0 : ℝ)..1, cosineMode n x * deriv g x)
        = ((n : ℝ) * Real.pi) *
            ∫ x in (0 : ℝ)..1, Real.sin ((n : ℝ) * Real.pi * x) * g x := by
      linarith
    rw [show (fun x => Real.cos ((n : ℝ) * Real.pi * x) * deriv g x)
        = fun x => cosineMode n x * deriv g x from rfl]
    rw [this]
    ring

/-- The truncated chemotaxis flux vanishes at the left endpoint: the resolver
gradient factor is a pure sine series. -/
theorem truncatedChemFluxLifted_zero_left
    (p : CM2Params) (w : intervalDomainPoint → ℝ) :
    truncatedChemFluxLifted p w 0 = 0 := by
  unfold truncatedChemFluxLifted
  rw [ShenWork.Paper2.resolverGradReal_zero]
  simp

/-- The truncated chemotaxis flux vanishes at the right endpoint. -/
theorem truncatedChemFluxLifted_zero_right
    (p : CM2Params) (w : intervalDomainPoint → ℝ) :
    truncatedChemFluxLifted p w 1 = 0 := by
  unfold truncatedChemFluxLifted
  rw [ShenWork.Paper2.resolverGradReal_one]
  simp

/-! ## IBP transfer `∫ g' φ = -∫ g φ'` -/

/-- Integration by parts with vanishing flux endpoints and countable exceptional
sets for BOTH `g` and `φ`. -/
theorem integral_deriv_mul_eq_neg_mul_deriv
    {g φ : ℝ → ℝ} {s_φ s_g : Set ℝ} (hs_φ : s_φ.Countable) (hs_g : s_g.Countable)
    (hgc : ContinuousOn g (Set.Icc (0 : ℝ) 1))
    (hg : ∀ x ∈ Set.Ioo (0 : ℝ) 1 \ s_g, HasDerivAt g (deriv g x) x)
    (hg'i : IntervalIntegrable (deriv g) volume 0 1)
    (h0 : g 0 = 0) (h1 : g 1 = 0)
    (hφc : ContinuousOn φ (Set.Icc (0 : ℝ) 1))
    (hφd : ∀ x ∈ Set.Ioo (0 : ℝ) 1 \ s_φ, HasDerivAt φ (deriv φ x) x)
    (hφ'i : IntervalIntegrable (deriv φ) volume 0 1) :
    (∫ x in (0 : ℝ)..1, deriv g x * φ x)
      = -∫ x in (0 : ℝ)..1, g x * deriv φ x := by
  have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 :=
    Set.uIcc_of_le (by norm_num)
  have hFc : ContinuousOn (fun x => g x * φ x) (Set.Icc (0 : ℝ) 1) :=
    hgc.mul hφc
  have hs_union : (s_φ ∪ s_g).Countable := hs_φ.union hs_g
  have hFd : ∀ x ∈ Set.Ioo (0 : ℝ) 1 \ (s_φ ∪ s_g),
      HasDerivAt (fun y => g y * φ y)
        (deriv g x * φ x + g x * deriv φ x) x := by
    intro x hx
    have hxg : x ∈ Set.Ioo (0 : ℝ) 1 \ s_g := by
      exact ⟨hx.1, fun h => hx.2 (Set.mem_union_right _ h)⟩
    have hxφ : x ∈ Set.Ioo (0 : ℝ) 1 \ s_φ := by
      exact ⟨hx.1, fun h => hx.2 (Set.mem_union_left _ h)⟩
    exact (hg x hxg).mul (hφd x hxφ)
  have hAi : IntervalIntegrable (fun x => deriv g x * φ x) volume 0 1 := by
    rw [← huIcc] at hφc
    exact hg'i.mul_continuousOn hφc
  have hBi : IntervalIntegrable (fun x => g x * deriv φ x) volume 0 1 :=
    hφ'i.continuousOn_mul (by rw [huIcc]; exact hgc)
  have hFTC :=
    MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
      (fun x => g x * φ x) (fun x => deriv g x * φ x + g x * deriv φ x)
      (by norm_num : (0 : ℝ) ≤ 1) hs_union hFc hFd (hAi.add hBi)
  have hbdry : g 1 * φ 1 - g 0 * φ 0 = 0 := by
    rw [h0, h1]; ring
  rw [hbdry] at hFTC
  have hsplit : (∫ x in (0 : ℝ)..1, deriv g x * φ x)
      + (∫ x in (0 : ℝ)..1, g x * deriv φ x) = 0 := by
    rw [← intervalIntegral.integral_add hAi hBi]
    exact hFTC
  linarith

/-! ## Frontier 1: the bilinear cosine Parseval pairing -/

/-- **Cosine Parseval pairing (named frontier).**  For `f` continuous on
`[0,1]` and `φ` bounded and a.e.-measurable, the Neumann-normalized cosine
coefficient pairing is absolutely summable and sums to the `L²` pairing.

Proof route (self-contained, no PDE input):  polarize
`ShenWork.CosineParsevalBridge.unitIntervalEvenReflection_fourier_parseval_unit_mass`
applied to `f ± φ`, identify the Fourier coefficients of the even reflection
with the raw cosine integrals via
`unitIntervalEvenReflection_fourierCoeffOn_eq_cosineCoeff`, fold `ℤ → ℕ` by
evenness of the reflected coefficients, convert the normalization with
`cosineCoeffs_eq_factor_mul_integral`, and obtain the absolute summability
from coefficient `ℓ²` (both factors square-summable by the mass identity;
`|ab| ≤ (a² + b²)/2`). -/
theorem cosine_parseval_pairing_of_memLp_two
    {f φ : ℝ → ℝ}
    (hf : MemLp f (2 : ℝ≥0∞) (intervalMeasure 1))
    (hφ : MemLp φ (2 : ℝ≥0∞) (intervalMeasure 1)) :
    Summable (fun n : ℕ => cosineCoeffs f n * cosineTestCoeff φ n) ∧
      (∑' n : ℕ, cosineCoeffs f n * cosineTestCoeff φ n)
        = ∫ x in (0 : ℝ)..1, f x * φ x := by
  classical
  have hFmemC :
      MemLp (fun x : ℝ => (f x : ℂ)) (2 : ℝ≥0∞) (intervalMeasure 1) :=
    hf.ofReal
  have hΦmemC :
      MemLp (fun x : ℝ => (φ x : ℂ)) (2 : ℝ≥0∞) (intervalMeasure 1) :=
    hφ.ofReal
  let F : Lp ℂ 2 (intervalMeasure 1) :=
    hFmemC.toLp (fun x : ℝ => (f x : ℂ))
  let Φ : Lp ℂ 2 (intervalMeasure 1) :=
    hΦmemC.toLp (fun x : ℝ => (φ x : ℂ))
  have hFcoe :
      F =ᵐ[intervalMeasure 1] fun x : ℝ => (f x : ℂ) := by
    simpa [F] using
      MemLp.coeFn_toLp (μ := intervalMeasure 1)
        hFmemC
  have hΦcoe :
      Φ =ᵐ[intervalMeasure 1] fun x : ℝ => (φ x : ℂ) := by
    simpa [Φ] using
      MemLp.coeFn_toLp (μ := intervalMeasure 1)
        hΦmemC
  have hrawF : ∀ n : ℕ,
      inner ℂ (unitIntervalCosineLp n) F =
        ((∫ x in (0 : ℝ)..1,
          Real.cos ((n : ℝ) * Real.pi * x) * f x : ℝ) : ℂ) := by
    intro n
    rw [unitIntervalCosineLp_inner_eq_coeff]
    rw [← intervalMeasure_one_integral_eq_intervalIntegral_complex]
    calc
      (∫ x,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * F x
          ∂ intervalMeasure 1)
          =
        ∫ x,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * (f x : ℂ)
          ∂ intervalMeasure 1 := by
            exact integral_congr_ae
              (hFcoe.mono fun x hx => by
                simpa using congrArg
                  (fun z : ℂ =>
                    (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * z) hx)
      _ =
        ∫ x in (0 : ℝ)..1,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * (f x : ℂ) := by
            exact intervalMeasure_one_integral_eq_intervalIntegral_complex _
      _ = ((∫ x in (0 : ℝ)..1,
          Real.cos ((n : ℝ) * Real.pi * x) * f x : ℝ) : ℂ) := by
            rw [← intervalIntegral.integral_ofReal]
            congr 1
            funext x
            simp
  have hrawΦ : ∀ n : ℕ,
      inner ℂ (unitIntervalCosineLp n) Φ =
        ((cosineTestCoeff φ n : ℝ) : ℂ) := by
    intro n
    rw [unitIntervalCosineLp_inner_eq_coeff]
    rw [← intervalMeasure_one_integral_eq_intervalIntegral_complex]
    calc
      (∫ x,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * Φ x
          ∂ intervalMeasure 1)
          =
        ∫ x,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * (φ x : ℂ)
          ∂ intervalMeasure 1 := by
            exact integral_congr_ae
              (hΦcoe.mono fun x hx => by
                simpa using congrArg
                  (fun z : ℂ =>
                    (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * z) hx)
      _ =
        ∫ x in (0 : ℝ)..1,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * (φ x : ℂ) := by
            exact intervalMeasure_one_integral_eq_intervalIntegral_complex _
      _ = ((cosineTestCoeff φ n : ℝ) : ℂ) := by
            rw [cosineTestCoeff]
            rw [← intervalIntegral.integral_ofReal]
            congr 1
            funext x
            simp [cosineMode]
  have hrawF_right : ∀ n : ℕ,
      inner ℂ F (unitIntervalCosineLp n) =
        ((∫ x in (0 : ℝ)..1,
          Real.cos ((n : ℝ) * Real.pi * x) * f x : ℝ) : ℂ) := by
    intro n
    rw [← inner_conj_symm, hrawF n]
    simp
  have hterm : ∀ n : ℕ,
      inner ℂ F (unitIntervalNormalizedCosineLp n) *
          inner ℂ (unitIntervalNormalizedCosineLp n) Φ
        =
      ((cosineCoeffs f n * cosineTestCoeff φ n : ℝ) : ℂ) := by
    intro n
    by_cases hn : n = 0
    · subst n
      rw [show unitIntervalNormalizedCosineLp 0 = unitIntervalCosineLp 0 by
        simp [unitIntervalNormalizedCosineLp]]
      rw [hrawF_right 0, hrawΦ 0, cosineCoeffs_zero_eq_integral]
      simp [cosineTestCoeff, cosineMode]
    · have hnorm :
        unitIntervalNormalizedCosineLp n =
          (Real.sqrt 2 : ℂ) • unitIntervalCosineLp n := by
          simp [unitIntervalNormalizedCosineLp, hn]
      rw [hnorm, inner_smul_right, inner_smul_left, hrawF_right n, hrawΦ n]
      rw [cosineCoeffs_pos_eq_integral hn]
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
      set A : ℂ :=
        ((∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f x : ℝ) : ℂ)
      set B : ℂ := ((cosineTestCoeff φ n : ℝ) : ℂ)
      change (Real.sqrt 2 : ℂ) * A *
          ((starRingEnd ℂ) (Real.sqrt 2 : ℂ) * B) =
        2 * A * B
      have hsqrt_star :
          (starRingEnd ℂ) (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) := by
        simpa using Complex.conj_ofReal (Real.sqrt 2)
      have hsqrt_sq_complex : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
        norm_num [← Complex.ofReal_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hsqrt_star]
      calc
        (Real.sqrt 2 : ℂ) * A * ((Real.sqrt 2 : ℂ) * B)
            = ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) * (A * B) := by ring
        _ = 2 * (A * B) := by rw [hsqrt_sq_complex]
        _ = 2 * A * B := by ring
  have hinner :
      inner ℂ F Φ =
        ((∫ x in (0 : ℝ)..1, f x * φ x : ℝ) : ℂ) := by
    rw [L2.inner_def]
    calc
      (∫ x, inner ℂ (F x) (Φ x) ∂ intervalMeasure 1)
          =
        ∫ x, ((f x * φ x : ℝ) : ℂ) ∂ intervalMeasure 1 := by
          refine integral_congr_ae ?_
          filter_upwards [hFcoe, hΦcoe] with x hxF hxΦ
          rw [hxF, hxΦ]
          simp [RCLike.inner_apply]
          ring
      _ =
        ∫ x in (0 : ℝ)..1, ((f x * φ x : ℝ) : ℂ) := by
          exact intervalMeasure_one_integral_eq_intervalIntegral_complex _
      _ = ((∫ x in (0 : ℝ)..1, f x * φ x : ℝ) : ℂ) := by
          exact intervalIntegral.integral_ofReal
            (a := (0 : ℝ)) (b := 1) (μ := volume)
            (f := fun x : ℝ => f x * φ x)
  have hsumC :
      Summable fun n : ℕ =>
        ((cosineCoeffs f n * cosineTestCoeff φ n : ℝ) : ℂ) := by
    simpa [unitIntervalCosineHilbertBasis, hterm] using
      (unitIntervalCosineHilbertBasis.summable_inner_mul_inner F Φ)
  have htsumC :
      (∑' n : ℕ,
        ((cosineCoeffs f n * cosineTestCoeff φ n : ℝ) : ℂ))
        = ((∫ x in (0 : ℝ)..1, f x * φ x : ℝ) : ℂ) := by
    calc
      (∑' n : ℕ,
        ((cosineCoeffs f n * cosineTestCoeff φ n : ℝ) : ℂ))
          =
        ∑' n : ℕ,
          inner ℂ F (unitIntervalNormalizedCosineLp n) *
            inner ℂ (unitIntervalNormalizedCosineLp n) Φ := by
            exact tsum_congr fun n => (hterm n).symm
      _ = inner ℂ F Φ := by
          simpa [unitIntervalCosineHilbertBasis] using
            unitIntervalCosineHilbertBasis.tsum_inner_mul_inner F Φ
      _ = ((∫ x in (0 : ℝ)..1, f x * φ x : ℝ) : ℂ) := hinner
  constructor
  · exact Complex.summable_ofReal.mp hsumC
  · apply Complex.ofReal_injective
    rw [Complex.ofReal_tsum]
    exact htsumC

/-- Continuous/bounded wrapper around the `L² × L²` cosine Parseval pairing. -/
theorem cosine_parseval_pairing
    {f φ : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hφm : AEStronglyMeasurable φ (intervalMeasure 1))
    {Cφ : ℝ} (hφb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |φ x| ≤ Cφ) :
    Summable (fun n : ℕ => cosineCoeffs f n * cosineTestCoeff φ n) ∧
      (∑' n : ℕ, cosineCoeffs f n * cosineTestCoeff φ n)
        = ∫ x in (0 : ℝ)..1, f x * φ x :=
  cosine_parseval_pairing_of_memLp_two
    (memLp_two_of_continuousOn_Icc hf)
    (memLp_two_of_aestronglyMeasurable_bound_Icc hφm hφb)

/-- An absolutely summable cosine representative gives an `L²` slice and the
expected cosine coefficients.  This is a compatibility bridge for legacy
pointwise reconstruction producers; tested consumers can use the weaker `L²`
outputs. -/
theorem cosine_l1_rep_memLp_and_coeff
    {w : ℝ → ℝ} {c : ℕ → ℝ}
    (hc : Summable (fun k : ℕ => |c k|))
    (hrep : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      w x = ∑' k : ℕ, c k * cosineMode k x) :
    MemLp w (2 : ℝ≥0∞) (intervalMeasure 1) ∧
      ∀ k : ℕ, cosineCoeffs w k = c k := by
  let S : ℝ → ℝ := fun x => ∑' k : ℕ, c k * cosineMode k x
  have hScont : Continuous S := by
    dsimp only [S]
    refine continuous_tsum
      (fun k => continuous_const.mul (continuous_cosineMode k)) hc ?_
    intro k x
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |c k| * |cosineMode k x| ≤ |c k| * 1 :=
        mul_le_mul_of_nonneg_left
          (by simpa [cosineMode] using
            Real.abs_cos_le_one ((k : ℝ) * Real.pi * x))
          (abs_nonneg _)
      _ = |c k| := by ring
  have hSLp : MemLp S (2 : ℝ≥0∞) (intervalMeasure 1) :=
    memLp_two_of_continuousOn_Icc hScont.continuousOn
  have hmemae : ∀ᵐ x ∂ intervalMeasure 1, x ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
    exact ae_restrict_mem measurableSet_Icc
  have heq : w =ᵐ[intervalMeasure 1] S := by
    filter_upwards [hmemae] with x hx
    simpa [S] using hrep x hx
  refine ⟨(memLp_congr_ae heq).2 hSLp, ?_⟩
  intro k
  calc
    cosineCoeffs w k = cosineCoeffs S k :=
      ShenWork.Paper2.cosineCoeffs_congr_on_Icc
        (fun x hx => by simpa [S] using hrep x hx) k
    _ = c k := by
      simpa [S] using
        ShenWork.IntervalPicardIterateRestart.cosineCoeffs_of_l1_cosineSeries hc k

/-! ## Frontier 2: positive-time spectral regularity of the truncated limit -/

/-- Positive-time spectral regularity bundle for the truncated Picard limit.
These are exactly the pointwise reconstruction and spatial regularity outputs
needed by the three tested identities:

* an `L²` time-derivative slice with its cosine coefficients identified,
* the tested gradient representation with frequency-weighted ℓ¹ coefficients,
* differentiability of the negative-part test off a countable set with a
  bounded derivative (this follows from `C¹` slices: `-u_-` fails to be
  differentiable only at the transversal zeros of `u_t`, which are isolated),
* `C¹` regularity of the truncated chemotaxis flux slice.

The two tested-series summability conditions are deliberately not fields of
this structure.  They follow at the test level: the Laplacian series from
`grad_l1` and one integration by parts, and the source series from the bilinear
cosine Parseval pairing.  In particular, no absolute summability of the
truncated source coefficients is required. -/
structure TruncatedPositiveTimeSpectralData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀) (t : ℝ) : Prop where
  timeDeriv_memLp : MemLp
    (intervalDomainLift (fun z : intervalDomainPoint =>
      ShenWork.IntervalDomain.intervalDomain.timeDeriv
        (truncatedConjugatePicardLimit p u₀ DT.T) t z))
    (2 : ℝ≥0∞) (intervalMeasure 1)
  timeDeriv_coeff : ∀ k : ℕ,
    cosineCoeffs
      (intervalDomainLift (fun z : intervalDomainPoint =>
        ShenWork.IntervalDomain.intervalDomain.timeDeriv
          (truncatedConjugatePicardLimit p u₀ DT.T) t z)) k
      = truncatedPicardCoeffTimeDeriv p u₀
          (truncatedConjugatePicardLimit p u₀ DT.T) t k
  grad_l1 : Summable (fun k : ℕ =>
    |truncatedPicardCoeff p u₀
        (truncatedConjugatePicardLimit p u₀ DT.T) t k|
      * ((k : ℝ) * Real.pi))
  grad_rep : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    deriv (intervalDomainLift ((truncatedConjugatePicardLimit p u₀ DT.T) t)) x
      = ∑' k : ℕ, truncatedPicardCoeff p u₀
          (truncatedConjugatePicardLimit p u₀ DT.T) t k *
            deriv (cosineMode k) x
  test_diff_off_countable : ∃ s : Set ℝ, s.Countable ∧
    ∀ x ∈ Set.Ioo (0 : ℝ) 1 \ s,
      HasDerivAt (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t)
        (deriv (negativePartTest
          (truncatedConjugatePicardLimit p u₀ DT.T) t) x) x
  test_deriv_bound : ∃ C : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
    |deriv (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) x| ≤ C
  chem_cont : ContinuousOn
    (truncatedChemFluxLifted p ((truncatedConjugatePicardLimit p u₀ DT.T) t))
    (Set.Icc (0 : ℝ) 1)
  chem_diff_off_countable : ∃ s_chem : Set ℝ, s_chem.Countable ∧
    ∀ x ∈ Set.Ioo (0 : ℝ) 1 \ s_chem,
      HasDerivAt
        (truncatedChemFluxLifted p ((truncatedConjugatePicardLimit p u₀ DT.T) t))
        (deriv (truncatedChemFluxLifted p
          ((truncatedConjugatePicardLimit p u₀ DT.T) t)) x) x
  chem_deriv_bound : ∃ C_chem : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
    |deriv (truncatedChemFluxLifted p
      ((truncatedConjugatePicardLimit p u₀ DT.T) t)) x| ≤ C_chem

/-- **Positive-time spectral regularity (named frontier).**  This is the
truncated-route analog of the delivered non-truncated machinery:
`IntervalCoeffLadderFull` (ℓ¹ ladder envelopes on restarted windows),
`IntervalSourceCoeffContinuity` (source coefficient continuity),
`IntervalMildTimeDerivReconstruction` (per-mode ODE → `∂ₜu` reconstruction),
all instantiated at `truncatedBFormSourceCoeff` /
`truncatedConjugatePicardLimit` instead of `bFormSourceCoeffs` /
`conjugatePicardLimit`. -/
theorem truncatedPositiveTimeSpectralData_of_existenceData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t < DT.T) :
    TruncatedPositiveTimeSpectralData p DT t := by
  set U := truncatedConjugatePicardLimit p u₀ DT.T with hU
  have htime := cosine_l1_rep_memLp_and_coeff
    (TruncatedPositiveTimeBootstrap.truncatedPicardCoeffTimeDeriv_summable_positive_time
      DT ht htT.le)
    (TruncatedPositiveTimeBootstrap.truncatedPicardLimit_timeDeriv_rep_positive_time
      DT ht htT.le)
  exact
    { timeDeriv_memLp := htime.1
      timeDeriv_coeff := htime.2
      grad_l1 :=
        TruncatedPositiveTimeBootstrap.truncatedPicardCoeff_grad_l1_positive_time
          DT ht htT.le
      grad_rep :=
        TruncatedPositiveTimeBootstrap.truncatedPicardLimit_grad_rep_positive_time
          DT ht htT.le
      test_diff_off_countable :=
        TruncatedPositiveTimeBootstrap.negativePartTest_diff_off_countable_of_gradient_bound
          DT ht htT.le
      test_deriv_bound :=
        TruncatedPositiveTimeBootstrap.negativePartTest_deriv_bound_of_gradient_bound
          DT ht htT.le
      chem_cont :=
        TruncatedPositiveTimeBootstrap.truncatedChemFlux_continuousOn_positive_time
          DT ht htT.le
      chem_diff_off_countable :=
        TruncatedPositiveTimeBootstrap.truncatedChemFlux_diff_off_countable_positive_time
          DT ht htT.le
      chem_deriv_bound :=
        TruncatedPositiveTimeBootstrap.truncatedChemFlux_deriv_bound_positive_time
          DT ht htT.le }

/-- The truncated B-form source coefficients are square summable at every
positive time once the tested spectral package supplies the bounded weak
derivative of the chemotactic flux.  This is the honest pre-nonnegativity
replacement for the stronger (and unnecessary here) source `ℓ¹` claim. -/
theorem truncatedBFormSourceCoeff_l2_of_spectralData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DT : TruncatedConjugateMildExistenceData p u₀} {t : ℝ}
    (ht : 0 < t) (htT : t ≤ DT.T)
    (D : TruncatedPositiveTimeSpectralData p DT t) :
    Summable (fun k : ℕ =>
      (truncatedBFormSourceCoeff p
        (truncatedConjugatePicardLimit p u₀ DT.T) t k) ^ 2) := by
  classical
  let U := truncatedConjugatePicardLimit p u₀ DT.T
  let g := truncatedChemFluxLifted p (U t)
  let L := truncatedLogisticLifted p (U t)
  have hcont : Continuous (U t) :=
    (truncatedConjugateMildSolutionData_of_data DT).hcont t ht htT
  have hlift : ContinuousOn (intervalDomainLift (U t)) (Set.Icc (0 : ℝ) 1) :=
    ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity.intervalDomain_lift_continuousOn_Icc_of_continuous
      hcont
  have hposCont : Continuous fun r : ℝ => positivePart r := by
    simpa [positivePart] using (continuous_id.max continuous_const)
  have hlogLocal : ContinuousOn
      (fun r : ℝ => truncatedLogisticLocal p r) Set.univ := by
    unfold truncatedLogisticLocal
    have hpow : ContinuousOn (fun r : ℝ => positivePart r ^ p.α) Set.univ :=
      ContinuousOn.rpow_const hposCont.continuousOn
        (fun _ _ => Or.inr p.hα.le)
    exact continuousOn_id.mul
      (continuousOn_const.sub (continuousOn_const.mul hpow))
  have hLc : ContinuousOn L (Set.Icc (0 : ℝ) 1) := by
    dsimp only [L]
    exact hlogLocal.comp hlift (fun _ _ => Set.mem_univ _)
  have hLlp : MemLp L (2 : ℝ≥0∞) (intervalMeasure 1) :=
    memLp_two_of_continuousOn_Icc hLc
  obtain ⟨C_chem, hC_chem⟩ := D.chem_deriv_bound
  have hg'm : AEStronglyMeasurable (deriv g) (intervalMeasure 1) :=
    (measurable_deriv _).aestronglyMeasurable
  have hg'lp : MemLp (deriv g) (2 : ℝ≥0∞) (intervalMeasure 1) :=
    memLp_two_of_aestronglyMeasurable_bound_Icc hg'm hC_chem
  have hlog_sq : Summable (fun k : ℕ => (cosineCoeffs L k) ^ 2) :=
    (ShenWork.IntervalNHGBrickB.cosineCoeffs_l2_of_memLp hLlp).1
  have hchem_sq : Summable (fun k : ℕ => (cosineCoeffs (deriv g) k) ^ 2) :=
    (ShenWork.IntervalNHGBrickB.cosineCoeffs_l2_of_memLp hg'lp).1
  obtain ⟨s_chem, hsc_chem, hsd_chem⟩ := D.chem_diff_off_countable
  have hg'i : IntervalIntegrable (deriv g) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)]
    refine Integrable.mono' (integrable_const C_chem)
      ((measurable_deriv _).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs]
    exact hC_chem x (Set.mem_Icc.mpr ⟨hx.1.le, hx.2⟩)
  have hg0 : g 0 = 0 := by
    simpa [g, U] using
      truncatedChemFluxLifted_zero_left p (U t)
  have hg1 : g 1 = 0 := by
    simpa [g, U] using
      truncatedChemFluxLifted_zero_right p (U t)
  have htrans : ∀ k,
      truncatedChemDivSourceCoeff p U t k = cosineCoeffs (deriv g) k :=
    fun k => freq_sineInner_eq_cosineCoeffs_deriv hsc_chem D.chem_cont
      hsd_chem hg'i hg0 hg1 k
  have hmajor : Summable (fun k : ℕ =>
      2 * (cosineCoeffs L k) ^ 2
        + (2 * p.χ₀ ^ 2) * (cosineCoeffs (deriv g) k) ^ 2) :=
    (hlog_sq.mul_left 2).add (hchem_sq.mul_left (2 * p.χ₀ ^ 2))
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) hmajor
  have hsrc : truncatedBFormSourceCoeff p U t k =
      cosineCoeffs L k - p.χ₀ * cosineCoeffs (deriv g) k := by
    rw [show truncatedBFormSourceCoeff p U t k =
        truncatedLogisticSourceCoeff p U t k
          - p.χ₀ * truncatedChemDivSourceCoeff p U t k from rfl,
      htrans k]
    rfl
  rw [show truncatedConjugatePicardLimit p u₀ DT.T = U from rfl, hsrc]
  nlinarith [sq_nonneg (cosineCoeffs L k +
    p.χ₀ * cosineCoeffs (deriv g) k)]

/-! ## Test-function facts derived from the mild data -/

section TestFacts

variable {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
  {DT : TruncatedConjugateMildExistenceData p u₀} {t : ℝ}

/-- Continuity of the negative-part test on `[0,1]` from continuous slices. -/
theorem negativePartTest_contOn_of_data
    (ht : 0 < t) (htT : t ≤ DT.T) :
    ContinuousOn (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t)
      (Set.Icc (0 : ℝ) 1) := by
  have hcont : Continuous ((truncatedConjugatePicardLimit p u₀ DT.T) t) :=
    (truncatedConjugateMildSolutionData_of_data DT).hcont t ht htT
  have hlift : ContinuousOn
      (intervalDomainLift ((truncatedConjugatePicardLimit p u₀ DT.T) t))
      (Set.Icc (0 : ℝ) 1) :=
    ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity.intervalDomain_lift_continuousOn_Icc_of_continuous
      hcont
  have hneg : ContinuousOn
      (negativePartLift ((truncatedConjugatePicardLimit p u₀ DT.T) t))
      (Set.Icc (0 : ℝ) 1) :=
    negativePart_continuous.continuousOn.comp hlift (fun _ _ => Set.mem_univ _)
  simpa [negativePartTest] using hneg.neg

/-- Global bound for the negative-part test from the Picard ball bound. -/
theorem negativePartTest_abs_le_of_data
    (ht : 0 < t) (htT : t ≤ DT.T) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t x| ≤ DT.M := by
  intro x hx
  have hbound :=
    (truncatedConjugateMildSolutionData_of_data DT).hbound t ht htT ⟨x, hx⟩
  have hval : intervalDomainLift ((truncatedConjugatePicardLimit p u₀ DT.T) t) x
      = (truncatedConjugatePicardLimit p u₀ DT.T) t ⟨x, hx⟩ := by
    simp [intervalDomainLift, hx]
  simp only [negativePartTest, negativePartLift, abs_neg]
  rw [hval]
  set r := (truncatedConjugatePicardLimit p u₀ DT.T) t ⟨x, hx⟩ with hr
  have : |negativePart r| ≤ |r| := by
    simp only [negativePart]
    rcases le_total r 0 with h | h
    · rw [max_eq_left (by linarith), abs_neg]
    · rw [max_eq_right (by linarith)]
      simp [abs_nonneg]
  exact le_trans this hbound

/-- The derivative of the negative-part test is interval integrable on `[0,1]`
whenever it is bounded there (junk values off the differentiability set are
`0`; measurability is `measurable_deriv`). -/
theorem negativePartTest_deriv_intervalIntegrable_of_bound
    {C : ℝ}
    (hC : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) x| ≤ C) :
    IntervalIntegrable
      (deriv (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t))
      volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  refine Integrable.mono' (integrable_const C)
    ((measurable_deriv _).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs]
  exact hC x (Set.mem_Icc.mpr ⟨hx.1.le, hx.2⟩)

end TestFacts

/-! ## The three tested identities -/

section Assembly

variable {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
  {DT : TruncatedConjugateMildExistenceData p u₀} {t : ℝ}

/-- **Tested identity 1 (time Leibniz / tsum).** -/
theorem tested_time_leibniz_of_spectralData
    (ht : 0 < t) (htT : t ≤ DT.T)
    (D : TruncatedPositiveTimeSpectralData p DT t) :
    (∫ x,
        intervalDomainLift
            (fun z : intervalDomainPoint =>
              ShenWork.IntervalDomain.intervalDomain.timeDeriv
                (truncatedConjugatePicardLimit p u₀ DT.T) t z) x *
          negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t x
        ∂ intervalMeasure 1)
      =
    ∑' k : ℕ,
      truncatedPicardCoeffTimeDeriv p u₀
          (truncatedConjugatePicardLimit p u₀ DT.T) t k *
        cosineTestCoeff
          (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k := by
  let ut : ℝ → ℝ := intervalDomainLift
    (fun z : intervalDomainPoint =>
      ShenWork.IntervalDomain.intervalDomain.timeDeriv
        (truncatedConjugatePicardLimit p u₀ DT.T) t z)
  let φ := negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t
  have hφc := negativePartTest_contOn_of_data (DT := DT) ht htT
  have hφm : AEStronglyMeasurable
      φ (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
      hφc
  have hφb := negativePartTest_abs_le_of_data (DT := DT) ht htT
  have hφLp : MemLp φ (2 : ℝ≥0∞) (intervalMeasure 1) :=
    memLp_two_of_aestronglyMeasurable_bound_Icc hφm hφb
  obtain ⟨_hsum, hpair⟩ :=
    cosine_parseval_pairing_of_memLp_two
      (by simpa [ut] using D.timeDeriv_memLp) hφLp
  rw [intervalMeasure_one_integral_eq_intervalIntegral]
  calc
    (∫ x in (0 : ℝ)..1, ut x * φ x)
        = ∑' k : ℕ, cosineCoeffs ut k * cosineTestCoeff φ k := hpair.symm
    _ = ∑' k : ℕ,
        truncatedPicardCoeffTimeDeriv p u₀
            (truncatedConjugatePicardLimit p u₀ DT.T) t k *
          cosineTestCoeff φ k := by
            refine tsum_congr fun k => ?_
            rw [show cosineCoeffs ut k =
                truncatedPicardCoeffTimeDeriv p u₀
                  (truncatedConjugatePicardLimit p u₀ DT.T) t k by
              simpa [ut] using D.timeDeriv_coeff k]

/-- **Tested identity 2 (gradient IBP / tsum).** -/
theorem tested_gradient_ibp_of_spectralData
    (ht : 0 < t) (htT : t ≤ DT.T)
    (D : TruncatedPositiveTimeSpectralData p DT t) :
    (∫ x,
        deriv (intervalDomainLift
          ((truncatedConjugatePicardLimit p u₀ DT.T) t)) x *
          deriv
            (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) x
        ∂ intervalMeasure 1)
      =
    ∑' k : ℕ,
      unitIntervalCosineEigenvalue k *
        truncatedPicardCoeff p u₀
          (truncatedConjugatePicardLimit p u₀ DT.T) t k *
        cosineTestCoeff
          (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k := by
  obtain ⟨C, hC⟩ := D.test_deriv_bound
  obtain ⟨s, hsc, hsd⟩ := D.test_diff_off_countable
  have hφc := negativePartTest_contOn_of_data (DT := DT) ht htT
  have hφ'i := negativePartTest_deriv_intervalIntegrable_of_bound (DT := DT) hC
  have hinterchange :=
    integral_tsum_pairing
      (w := deriv (intervalDomainLift
        ((truncatedConjugatePicardLimit p u₀ DT.T) t)))
      (ψ := deriv (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t))
      (c := fun k => truncatedPicardCoeff p u₀
        (truncatedConjugatePicardLimit p u₀ DT.T) t k)
      (B := fun k => (k : ℝ) * Real.pi)
      (e := fun k => fun x => deriv (cosineMode k) x)
      (Cψ := C)
      (fun k => continuous_deriv_cosineMode k)
      (fun k x _ => abs_deriv_cosineMode_le k x)
      D.grad_l1
      D.grad_rep
      ((measurable_deriv _).aestronglyMeasurable)
      hC
  rw [hinterchange]
  refine tsum_congr fun k => ?_
  rw [cosineMode_gradient_testCoeff_eq_off_countable k hsc hφc hsd hφ'i]
  ring

/-- The Laplacian-tested series is summable already at the `W^{1,∞}` test
level.  One-mode Neumann integration by parts turns its `k`-th term into the
gradient coefficient paired with `φ'`; the latter is dominated by
`C * |aₖ| * kπ`, which is summable by `grad_l1`. -/
theorem tested_laplacian_summable_of_spectralData
    (ht : 0 < t) (htT : t ≤ DT.T)
    (D : TruncatedPositiveTimeSpectralData p DT t) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        truncatedPicardCoeff p u₀
          (truncatedConjugatePicardLimit p u₀ DT.T) t k *
        cosineTestCoeff
          (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k) := by
  let U := truncatedConjugatePicardLimit p u₀ DT.T
  let φ := negativePartTest U t
  let a : ℕ → ℝ := fun k => truncatedPicardCoeff p u₀ U t k
  obtain ⟨C, hC⟩ := D.test_deriv_bound
  obtain ⟨s, hsc, hsd⟩ := D.test_diff_off_countable
  have hφc : ContinuousOn φ (Set.Icc (0 : ℝ) 1) :=
    negativePartTest_contOn_of_data (DT := DT) ht htT
  have hφ'i : IntervalIntegrable (deriv φ) volume 0 1 :=
    negativePartTest_deriv_intervalIntegrable_of_bound (DT := DT) hC
  have hmode_bound : ∀ k : ℕ,
      |∫ x in (0 : ℝ)..1, deriv (cosineMode k) x * deriv φ x|
        ≤ ((k : ℝ) * Real.pi) * C := by
    intro k
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := ((k : ℝ) * Real.pi) * C)
      (f := fun x : ℝ => deriv (cosineMode k) x * deriv φ x)
      (fun x hx => by
        rw [Real.norm_eq_abs, abs_mul]
        have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
          have hx_uIcc : x ∈ Set.uIcc (0 : ℝ) 1 := Set.uIoc_subset_uIcc hx
          rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx_uIcc
        exact mul_le_mul (abs_deriv_cosineMode_le k x) (hC x hxIcc)
          (abs_nonneg _) (by positivity))
    simpa [Real.norm_eq_abs] using hnorm
  have hterm : ∀ k : ℕ,
      |unitIntervalCosineEigenvalue k * a k * cosineTestCoeff φ k|
        ≤ (|a k| * ((k : ℝ) * Real.pi)) * C := by
    intro k
    have hmode :=
      cosineMode_gradient_testCoeff_eq_off_countable k hsc hφc hsd hφ'i
    calc
      |unitIntervalCosineEigenvalue k * a k * cosineTestCoeff φ k|
          = |a k| *
              |unitIntervalCosineEigenvalue k * cosineTestCoeff φ k| := by
                simp only [abs_mul]
                ring
      _ = |a k| *
            |∫ x in (0 : ℝ)..1, deriv (cosineMode k) x * deriv φ x| := by
              rw [← hmode]
      _ ≤ |a k| * (((k : ℝ) * Real.pi) * C) :=
            mul_le_mul_of_nonneg_left (hmode_bound k) (abs_nonneg _)
      _ = (|a k| * ((k : ℝ) * Real.pi)) * C := by ring
  have hmajor : Summable (fun k : ℕ =>
      (|a k| * ((k : ℝ) * Real.pi)) * C) := by
    have hgrad : Summable (fun k : ℕ =>
        |a k| * ((k : ℝ) * Real.pi)) := by
      simpa [a, U] using D.grad_l1
    exact hgrad.mul_right C
  have habs : Summable (fun k : ℕ =>
      |unitIntervalCosineEigenvalue k * a k * cosineTestCoeff φ k|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hterm hmajor
  refine Summable.of_norm ?_
  simpa [Real.norm_eq_abs, a, φ, U] using habs

/-- Cosine coefficient pairing symmetry:
`cosineCoeffs f n * cosineTestCoeff g n = cosineCoeffs g n * cosineTestCoeff f n`. -/
lemma cosineCoeffs_cosineTestCoeff_comm (f g : ℝ → ℝ) (n : ℕ) :
    cosineCoeffs f n * cosineTestCoeff g n
      = cosineCoeffs g n * cosineTestCoeff f n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [cosineCoeffs_zero_eq_integral, cosineCoeffs_zero_eq_integral]
    simp only [cosineTestCoeff, cosineMode, Nat.cast_zero, zero_mul,
      Real.cos_zero, one_mul]
    ring
  · rw [cosineCoeffs_pos_eq_integral (Nat.pos_iff_ne_zero.mp hn),
      cosineCoeffs_pos_eq_integral (Nat.pos_iff_ne_zero.mp hn)]
    simp only [cosineTestCoeff, cosineMode]
    ring

/-- The source-tested series is summable and equals the physical source
pairing.  Both conclusions come from the same two Hilbert-basis Parseval
pairings; absolute summability of the source coefficients themselves is not
used. -/
private theorem tested_source_pairing_core_of_spectralData
    (ht : 0 < t) (htT : t ≤ DT.T)
    (D : TruncatedPositiveTimeSpectralData p DT t) :
    Summable (fun k : ℕ =>
      truncatedBFormSourceCoeff p
          (truncatedConjugatePicardLimit p u₀ DT.T) t k *
        cosineTestCoeff
          (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k)
      ∧
      (∑' k : ℕ,
        truncatedBFormSourceCoeff p
            (truncatedConjugatePicardLimit p u₀ DT.T) t k *
          cosineTestCoeff
            (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k)
        =
      p.χ₀ *
        (∫ x,
          truncatedChemFluxLifted p
              ((truncatedConjugatePicardLimit p u₀ DT.T) t) x *
            deriv
              (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) x
          ∂ intervalMeasure 1)
        + (∫ x,
            truncatedLogisticLifted p
                ((truncatedConjugatePicardLimit p u₀ DT.T) t) x *
              negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t x
            ∂ intervalMeasure 1) := by
  classical
  set U := truncatedConjugatePicardLimit p u₀ DT.T with hU
  set φ := negativePartTest U t with hφ
  set g := truncatedChemFluxLifted p (U t) with hg
  set L := truncatedLogisticLifted p (U t) with hL
  -- test facts
  have hφc : ContinuousOn φ (Set.Icc (0 : ℝ) 1) :=
    negativePartTest_contOn_of_data (DT := DT) ht htT
  have hφm : AEStronglyMeasurable φ (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
      hφc
  have hφb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |φ x| ≤ DT.M :=
    negativePartTest_abs_le_of_data (DT := DT) ht htT
  obtain ⟨C, hC⟩ := D.test_deriv_bound
  obtain ⟨s, hsc, hsd⟩ := D.test_diff_off_countable
  have hφ'i := negativePartTest_deriv_intervalIntegrable_of_bound (DT := DT) hC
  -- logistic slice is continuous on [0,1]
  have hcont : Continuous (U t) :=
    (truncatedConjugateMildSolutionData_of_data DT).hcont t ht htT
  have hlift : ContinuousOn (intervalDomainLift (U t)) (Set.Icc (0 : ℝ) 1) :=
    ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity.intervalDomain_lift_continuousOn_Icc_of_continuous
      hcont
  have hposCont : Continuous fun r : ℝ => positivePart r := by
    simpa [positivePart] using (continuous_id.max continuous_const)
  have hlogLocal : ContinuousOn
      (fun r : ℝ => truncatedLogisticLocal p r) Set.univ := by
    unfold truncatedLogisticLocal
    have hpow : ContinuousOn (fun r : ℝ => positivePart r ^ p.α) Set.univ :=
      ContinuousOn.rpow_const hposCont.continuousOn
      (fun _ _ => Or.inr p.hα.le)
    exact continuousOn_id.mul
      (continuousOn_const.sub (continuousOn_const.mul hpow))
  have hLc : ContinuousOn L (Set.Icc (0 : ℝ) 1) := by
    simp only [hL]
    exact hlogLocal.comp hlift (fun _ _ => Set.mem_univ _)
  -- chem flux endpoints
  have hg0 : g 0 = 0 := truncatedChemFluxLifted_zero_left p (U t)
  have hg1 : g 1 = 0 := truncatedChemFluxLifted_zero_right p (U t)
  -- chem off-countable data
  obtain ⟨s_chem, hsc_chem, hsd_chem⟩ := D.chem_diff_off_countable
  obtain ⟨C_chem, hC_chem⟩ := D.chem_deriv_bound
  have hg'i : IntervalIntegrable (deriv g) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    refine Integrable.mono' (integrable_const C_chem)
      ((measurable_deriv _).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs]
    exact hC_chem x (Set.mem_Icc.mpr ⟨hx.1.le, hx.2⟩)
  -- Parseval branches
  obtain ⟨hlog_sum, hlog⟩ := cosine_parseval_pairing hLc hφm hφb
  -- For chem branch, swap roles: φ is continuous, deriv g is bounded measurable
  have hg'm : AEStronglyMeasurable (deriv g) (intervalMeasure 1) :=
    (measurable_deriv _).aestronglyMeasurable
  obtain ⟨hchem_sum_swap, hchem_swap⟩ := cosine_parseval_pairing hφc hg'm hC_chem
  -- Parseval symmetry: convert swapped coefficients back
  have hchem_sum : Summable (fun n : ℕ =>
      cosineCoeffs (deriv g) n * cosineTestCoeff φ n) :=
    hchem_sum_swap.congr
      (fun n => cosineCoeffs_cosineTestCoeff_comm φ (deriv g) n)
  have hchem : (∑' n : ℕ, cosineCoeffs (deriv g) n * cosineTestCoeff φ n)
      = ∫ x in (0 : ℝ)..1, deriv g x * φ x := by
    rw [tsum_congr (fun n =>
          cosineCoeffs_cosineTestCoeff_comm (deriv g) φ n),
        hchem_swap]
    exact intervalIntegral.integral_congr fun x _ => mul_comm (φ x) (deriv g x)
  -- coefficient transfer for the chem branch
  have htrans : ∀ k, truncatedChemDivSourceCoeff p U t k
      = cosineCoeffs (deriv g) k := fun k =>
    freq_sineInner_eq_cosineCoeffs_deriv hsc_chem D.chem_cont hsd_chem hg'i hg0 hg1 k
  -- IBP transfer
  have hibp : (∫ x in (0 : ℝ)..1, deriv g x * φ x)
      = -∫ x in (0 : ℝ)..1, g x * deriv φ x :=
    integral_deriv_mul_eq_neg_mul_deriv hsc hsc_chem D.chem_cont hsd_chem hg'i
      hg0 hg1 hφc hsd hφ'i
  -- assemble
  have hsrc_eq : ∀ k : ℕ,
      truncatedBFormSourceCoeff p U t k * cosineTestCoeff φ k
        = cosineCoeffs L k * cosineTestCoeff φ k
          - p.χ₀ * (cosineCoeffs (deriv g) k * cosineTestCoeff φ k) := by
    intro k
    have hlogc : truncatedLogisticSourceCoeff p U t k = cosineCoeffs L k := rfl
    rw [show truncatedBFormSourceCoeff p U t k
        = truncatedLogisticSourceCoeff p U t k
          - p.χ₀ * truncatedChemDivSourceCoeff p U t k from rfl,
      hlogc, htrans k]
    ring
  have hsrc_sum : Summable (fun k : ℕ =>
      truncatedBFormSourceCoeff p U t k * cosineTestCoeff φ k) :=
    (hlog_sum.sub (hchem_sum.mul_left p.χ₀)).congr
      (fun k => (hsrc_eq k).symm)
  refine ⟨hsrc_sum, ?_⟩
  calc (∑' k : ℕ, truncatedBFormSourceCoeff p U t k * cosineTestCoeff φ k)
      = ∑' k : ℕ,
          (cosineCoeffs L k * cosineTestCoeff φ k
            - p.χ₀ * (cosineCoeffs (deriv g) k * cosineTestCoeff φ k)) :=
        tsum_congr hsrc_eq
    _ = (∑' k : ℕ, cosineCoeffs L k * cosineTestCoeff φ k)
          - ∑' k : ℕ, p.χ₀ * (cosineCoeffs (deriv g) k * cosineTestCoeff φ k) :=
        Summable.tsum_sub hlog_sum (hchem_sum.mul_left p.χ₀)
    _ = (∫ x in (0 : ℝ)..1, L x * φ x)
          - p.χ₀ * ∫ x in (0 : ℝ)..1, deriv g x * φ x := by
        rw [tsum_mul_left, hlog, hchem]
    _ = p.χ₀ * (∫ x in (0 : ℝ)..1, g x * deriv φ x)
          + ∫ x in (0 : ℝ)..1, L x * φ x := by
        rw [hibp]; ring
    _ = p.χ₀ * (∫ x, g x * deriv φ x ∂ intervalMeasure 1)
          + ∫ x, L x * φ x ∂ intervalMeasure 1 := by
        rw [intervalMeasure_one_integral_eq_intervalIntegral,
          intervalMeasure_one_integral_eq_intervalIntegral]

/-- **Tested identity 3 (source pairing).** -/
theorem tested_source_pairing_of_spectralData
    (ht : 0 < t) (htT : t ≤ DT.T)
    (D : TruncatedPositiveTimeSpectralData p DT t) :
    (∑' k : ℕ,
      truncatedBFormSourceCoeff p
          (truncatedConjugatePicardLimit p u₀ DT.T) t k *
        cosineTestCoeff
          (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k)
      =
    p.χ₀ *
      (∫ x,
        truncatedChemFluxLifted p
            ((truncatedConjugatePicardLimit p u₀ DT.T) t) x *
          deriv
            (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) x
        ∂ intervalMeasure 1)
      + (∫ x,
          truncatedLogisticLifted p
              ((truncatedConjugatePicardLimit p u₀ DT.T) t) x *
            negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t x
          ∂ intervalMeasure 1) :=
  (tested_source_pairing_core_of_spectralData ht htT D).2

/-- The two summability side conditions required by the coefficient weak-test
package, derived at the tested level rather than from coefficientwise `ℓ¹`
regularity of the truncated source. -/
theorem weightedCoeff_summable_of_spectralData
    (ht : 0 < t) (htT : t ≤ DT.T)
    (D : TruncatedPositiveTimeSpectralData p DT t) :
    Summable (fun k : ℕ =>
        unitIntervalCosineEigenvalue k *
          truncatedPicardCoeff p u₀
            (truncatedConjugatePicardLimit p u₀ DT.T) t k *
          cosineTestCoeff
            (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k)
      ∧
    Summable (fun k : ℕ =>
        truncatedBFormSourceCoeff p
            (truncatedConjugatePicardLimit p u₀ DT.T) t k *
          cosineTestCoeff
            (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k) := by
  exact ⟨tested_laplacian_summable_of_spectralData ht htT D,
    (tested_source_pairing_core_of_spectralData ht htT D).1⟩

end Assembly

end ShenWork.Paper2.BFormPositiveDatumNegPart
