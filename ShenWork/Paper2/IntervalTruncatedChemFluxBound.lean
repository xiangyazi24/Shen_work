/-
  Uniform pointwise bound for the truncated chemotaxis flux on an absolute
  Picard ball.  This module sits below the positive-time bootstrap: it uses
  only the weak resolver spectral estimates and the truncated flux definition.
-/

import ShenWork.Paper2.IntervalBFormNegativePartCron2
import ShenWork.Paper2.IntervalResolverWeakBounds
import ShenWork.PDE.CosineSpectrum

open MeasureTheory Set
open scoped BigOperators Topology Real

noncomputable section

namespace ShenWork.Paper2.TruncatedPositiveTimeBootstrap

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.Paper2 (positivePart resolverGradReal)
open ShenWork.Paper2.BFormPositiveDatumNegPart
  (truncatedChemFluxLifted truncatedLogisticLifted truncatedLogisticLocal)
open ShenWork.PDE.ResolventEstimate (coeffL2Energy coeffL2Norm)
open ShenWork.Paper3 (unitIntervalNeumannSpectrum)

private theorem lift_continuousOn_Icc_of_continuous
    {w : intervalDomainPoint → ℝ} (hw : Continuous w) :
    ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have hres : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift w) = w := by
    funext z
    obtain ⟨z, hz⟩ := z
    show intervalDomainLift w z = w ⟨z, hz⟩
    rw [intervalDomainLift, dif_pos hz]
  rw [hres]
  exact hw

private theorem positivePart_le_abs (r : ℝ) :
    positivePart r ≤ |r| := by
  by_cases hr : 0 ≤ r
  · simp [positivePart, hr, abs_of_nonneg hr]
  · have hr' : r ≤ 0 := le_of_not_ge hr
    simp [positivePart, hr', abs_of_nonpos hr']

/-- The resolver driven by the positive part of a continuous slice is
nonnegative on the lifted closed interval, with no smallness assumption. -/
theorem resolverR_positivePart_lift_nonneg_of_continuous
    (p : CM2Params) {w : intervalDomainPoint → ℝ}
    (hw_cont : Continuous w) (y : ℝ) :
    0 ≤ intervalDomainLift
      (ShenWork.PDE.intervalNeumannResolverR p
        (fun x => positivePart (w x))) y := by
  let wPos : intervalDomainPoint → ℝ := fun x => positivePart (w x)
  have hwPos_cont : Continuous wPos := by
    simpa [wPos, positivePart] using hw_cont.max continuous_const
  have hwPos_nonneg : ∀ x, 0 ≤ wPos x := fun x => positivePart_nonneg (w x)
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · have hcont_on :
        ContinuousOn (intervalDomainLift wPos) (Set.Icc (0 : ℝ) 1) :=
      lift_continuousOn_Icc_of_continuous hwPos_cont
    open ShenWork.PDE ShenWork.IntervalResolverGradientBridge
        ShenWork.IntervalResolverWeakBounds ShenWork.Paper2
        ShenWork.IntervalNeumannFullKernel ShenWork.IntervalResolverPositivity in
    have hR_nonneg_pt : 0 ≤ intervalNeumannResolverR p wPos ⟨y, hy⟩ := by
      have hcont_src : Continuous
          (fun x : intervalDomainPoint => p.ν * (wPos x) ^ p.γ) :=
        continuous_const.mul
          (hwPos_cont.rpow_const (fun _ => Or.inr p.hγ.le))
      set clip : ℝ → intervalDomainPoint := fun x =>
        ⟨max 0 (min x 1), le_max_left 0 _,
          max_le (by norm_num) (min_le_right x 1)⟩
      have hclip_cont : Continuous clip :=
        Continuous.subtype_mk
          (continuous_const.max (continuous_id.min continuous_const)) _
      set f : ℝ → ℝ :=
        (fun x : intervalDomainPoint => p.ν * (wPos x) ^ p.γ) ∘ clip
      have hf_cont : Continuous f := hcont_src.comp hclip_cont
      have hf_nonneg : ∀ z, 0 ≤ f z := fun z =>
        mul_nonneg p.hν.le (Real.rpow_nonneg (hwPos_nonneg _) _)
      have hf_coeff : ∀ k, cosineCoeffs f k =
          (intervalNeumannResolverSourceCoeff p wPos k).re := by
        intro k
        have hsrc_eq :
            (intervalNeumannResolverSourceCoeff p wPos k).re =
            cosineCoeffs
              (fun x => p.ν * intervalDomainLift wPos x ^ p.γ) k := by
          simp [cosineCoeffs, intervalNeumannResolverSourceCoeff,
            Complex.ofReal_re]
        rw [hsrc_eq]
        exact cosineCoeffs_congr_on_Icc (fun x hx => by
          simp only [f, Function.comp, clip]
          have hclip_eq : max 0 (min x 1) = x := by
            rw [min_eq_left hx.2, max_eq_right hx.1]
          simp only [hclip_eq, intervalDomainLift,
            dif_pos (Set.mem_Icc.mpr hx)]) k
      have ha : Summable (fun k => (cosineCoeffs f k) ^ 2) := by
        have h := resolverSourceCoeff_re_sq_summable_of_continuousOn p hcont_on
        simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
        exact h.congr (fun k => by rw [hf_coeff])
      exact intervalNeumannResolverR_nonneg_of_nonneg_source
        hf_cont hf_nonneg hf_coeff ha ⟨y, hy⟩
    simpa [wPos, intervalDomainLift, hy] using hR_nonneg_pt
  · simp [intervalDomainLift, hy]

private theorem truncatedLogisticLocal_abs_le_of_abs_le
    (p : CM2Params) {M r : ℝ} (hM : 0 < M) (hr : |r| ≤ M) :
    |truncatedLogisticLocal p r| ≤
      M * (p.a + p.b * M ^ p.α) := by
  have hM_nonneg : 0 ≤ M := hM.le
  have hpos_nonneg : 0 ≤ positivePart r := positivePart_nonneg r
  have hpos_le : positivePart r ≤ M := (positivePart_le_abs r).trans hr
  have hpow_nonneg : 0 ≤ (positivePart r) ^ p.α :=
    Real.rpow_nonneg hpos_nonneg _
  have hpow_le : (positivePart r) ^ p.α ≤ M ^ p.α :=
    Real.rpow_le_rpow hpos_nonneg hpos_le p.hα.le
  have hinner :
      |p.a - p.b * (positivePart r) ^ p.α| ≤
        p.a + p.b * M ^ p.α := by
    calc
      |p.a - p.b * (positivePart r) ^ p.α|
          ≤ |p.a| + |p.b * (positivePart r) ^ p.α| := abs_sub _ _
      _ = p.a + p.b * (positivePart r) ^ p.α := by
        rw [abs_of_nonneg p.ha, abs_mul, abs_of_nonneg p.hb,
          abs_of_nonneg hpow_nonneg]
      _ ≤ p.a + p.b * M ^ p.α := by
        exact add_le_add (le_refl p.a)
          (mul_le_mul_of_nonneg_left hpow_le p.hb)
  calc
    |truncatedLogisticLocal p r|
        = |r| * |p.a - p.b * (positivePart r) ^ p.α| := by
          simp [truncatedLogisticLocal, abs_mul]
    _ ≤ M * (p.a + p.b * M ^ p.α) :=
      mul_le_mul hr hinner (abs_nonneg _) hM_nonneg

/-- Uniform pointwise bound for the lifted truncated logistic source on an
absolute ball. -/
theorem truncatedLogisticLifted_abs_le_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M) :
    ∀ y : ℝ,
      |truncatedLogisticLifted p w y| ≤
        M * (p.a + p.b * M ^ p.α) := by
  intro y
  have hlift_abs : |intervalDomainLift w y| ≤ M := by
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · simpa [intervalDomainLift, hy] using hball ⟨y, hy⟩
    · simp [intervalDomainLift, hy, hM.le]
  simpa [truncatedLogisticLifted] using
    truncatedLogisticLocal_abs_le_of_abs_le p hM hlift_abs

/-- The resolver source coefficients have the same `L²` bound on a signed
absolute ball as on a nonnegative order interval. -/
theorem resolverSourceCoeff_l2Norm_le_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M) :
    coeffL2Norm (fun k : ℕ =>
      ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k -
        ShenWork.PDE.intervalNeumannResolverSourceCoeff p (fun _ => 0) k)
      ≤ 2 * (p.ν * M ^ p.γ) := by
  classical
  have hUcont : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) :=
    lift_continuousOn_Icc_of_continuous hw_cont
  have hM_nonneg : 0 ≤ M := hM.le
  let A : ℕ → ℂ := fun k =>
    ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k -
      ShenWork.PDE.intervalNeumannResolverSourceCoeff p (fun _ => 0) k
  have hgcont : ContinuousOn
      (fun x : ℝ => p.ν * intervalDomainLift w x ^ p.γ) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.mul
      (hUcont.rpow_const (fun _ _ => Or.inr p.hγ.le))
  have hzero_cont : ContinuousOn
      (fun x : ℝ =>
        p.ν * intervalDomainLift (fun _ : intervalDomainPoint => 0) x ^ p.γ)
      (Set.Icc (0 : ℝ) 1) := by
    simpa [intervalDomainLift, Real.zero_rpow p.hγ.ne'] using
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc (0 : ℝ) 1))
  have hA_energy :
      coeffL2Energy A ≤
        4 * ∫ x in (0 : ℝ)..1,
          (p.ν * intervalDomainLift w x ^ p.γ) ^ 2 := by
    have hbase :=
      ShenWork.IntervalResolverWeakBounds.sourceCoeff_diff_energy_le_integral_of_continuousOn
        (p := p) (u₁ := w) (u₂ := fun _ : intervalDomainPoint => 0)
        hgcont hzero_cont
    simpa [A, ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero,
      intervalDomainLift, Real.zero_rpow p.hγ.ne'] using hbase
  have hsource_sq_le :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (p.ν * intervalDomainLift w x ^ p.γ) ^ 2 ≤
          (p.ν * M ^ p.γ) ^ 2 := by
    intro x hx
    have hlift_abs : |intervalDomainLift w x| ≤ M := by
      simp only [intervalDomainLift, dif_pos hx]
      exact hball ⟨x, hx⟩
    have hpow_abs :
        |intervalDomainLift w x ^ p.γ| ≤ M ^ p.γ :=
      (Real.abs_rpow_le_abs_rpow (intervalDomainLift w x) p.γ).trans
        (Real.rpow_le_rpow (abs_nonneg _) hlift_abs p.hγ.le)
    have hB_nonneg : 0 ≤ p.ν * M ^ p.γ :=
      mul_nonneg p.hν.le (Real.rpow_nonneg hM_nonneg _)
    have hsrc_abs :
        |p.ν * intervalDomainLift w x ^ p.γ| ≤ p.ν * M ^ p.γ := by
      rw [abs_mul, abs_of_pos p.hν]
      exact mul_le_mul_of_nonneg_left hpow_abs p.hν.le
    rw [← sq_abs]
    nlinarith [abs_nonneg (p.ν * intervalDomainLift w x ^ p.γ), hsrc_abs,
      hB_nonneg,
      sq_nonneg (p.ν * M ^ p.γ - |p.ν * intervalDomainLift w x ^ p.γ|)]
  have hsource_sq_cont : ContinuousOn
      (fun x : ℝ => (p.ν * intervalDomainLift w x ^ p.γ) ^ 2)
      (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hgcont.pow 2
  have hIle :
      (∫ x in (0 : ℝ)..1, (p.ν * intervalDomainLift w x ^ p.γ) ^ 2)
        ≤ (p.ν * M ^ p.γ) ^ 2 := by
    have hcI : IntervalIntegrable
        (fun _ : ℝ => (p.ν * M ^ p.γ) ^ 2) volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have hmono := intervalIntegral.integral_mono_on (by norm_num)
      hsource_sq_cont.intervalIntegrable hcI hsource_sq_le
    have hconst :
        (∫ _x in (0 : ℝ)..1, (p.ν * M ^ p.γ) ^ 2 ∂volume)
          = (p.ν * M ^ p.γ) ^ 2 := by
      rw [intervalIntegral.integral_const, sub_zero, one_smul]
    rwa [hconst] at hmono
  have hB_nonneg : 0 ≤ p.ν * M ^ p.γ :=
    mul_nonneg p.hν.le (Real.rpow_nonneg hM_nonneg _)
  have henergy_bound :
      coeffL2Energy A ≤ 4 * (p.ν * M ^ p.γ) ^ 2 :=
    hA_energy.trans (mul_le_mul_of_nonneg_left hIle (by norm_num))
  change coeffL2Norm A ≤ _
  rw [coeffL2Norm]
  calc
    Real.sqrt (coeffL2Energy A)
        ≤ Real.sqrt (4 * (p.ν * M ^ p.γ) ^ 2) :=
      Real.sqrt_le_sqrt henergy_bound
    _ = 2 * (p.ν * M ^ p.γ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← mul_pow,
        Real.sqrt_sq (mul_nonneg (by norm_num) hB_nonneg)]

/-- Resolver-gradient bound on a signed absolute ball. -/
theorem resolverGrad_abs_le_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M) (y : ℝ) :
    |resolverGradReal p w y| ≤
      Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ)) := by
  classical
  have hUcont : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) :=
    lift_continuousOn_Icc_of_continuous hw_cont
  let A : ℕ → ℂ := fun k =>
    ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k -
      ShenWork.PDE.intervalNeumannResolverSourceCoeff p (fun _ => 0) k
  let e : ℕ → ℝ := fun k => (A k).re
  let m : ℕ → ℝ := fun k =>
    (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * y)) /
      (p.μ + unitIntervalNeumannSpectrum.eigenvalue k)
  have hsrc : Summable fun k : ℕ =>
      ((ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k -
        ShenWork.PDE.intervalNeumannResolverSourceCoeff p (fun _ => 0) k).re) ^ 2 := by
    simpa [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      ShenWork.IntervalResolverWeakBounds.resolverSourceCoeff_re_sq_summable_of_continuousOn
        p hUcont
  have he_sq : Summable fun k : ℕ => (e k) ^ 2 := by
    simpa [e, A] using hsrc
  have hm_sq : Summable fun k : ℕ => (m k) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) ?_
      (ShenWork.PDE.intervalNeumannResolverGradWeight_sq_summable p)
    intro k
    have hsin : (Real.sin ((k : ℝ) * Real.pi * y)) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]
      exact Real.abs_sin_le_one _
    have hgweq :
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2 =
          ((k : ℝ) * Real.pi) ^ 2 /
            (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) ^ 2 := by
      rw [ShenWork.PDE.intervalNeumannResolverGradWeight, div_pow]
    rw [hgweq]
    dsimp [m]
    rw [div_pow, mul_pow, neg_pow]
    have hkp : (0 : ℝ) ≤ ((k : ℝ) * Real.pi) ^ 2 := by positivity
    have hnum :
        (-1 : ℝ) ^ 2 * ((k : ℝ) * Real.pi) ^ 2 *
            (Real.sin ((k : ℝ) * Real.pi * y)) ^ 2 ≤
          ((k : ℝ) * Real.pi) ^ 2 := by
      have h1 : (-1 : ℝ) ^ 2 = 1 := by norm_num
      rw [h1, one_mul]
      nlinarith [hkp, hsin, sq_nonneg (Real.sin ((k : ℝ) * Real.pi * y))]
    gcongr
  have hterm : ∀ k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverCoeff p w k).re *
          (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * y)) =
        e k * m k := by
    intro k
    have hden : p.μ + unitIntervalNeumannSpectrum.eigenvalue k ≠ 0 :=
      ne_of_gt (ShenWork.PDE.intervalNeumannResolver_denom_pos p k)
    dsimp [e, A, m]
    rw [ShenWork.IntervalResolverGradientBridge.resolverCoeff_re_eq p w k]
    simp only [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero]
    field_simp [hden]
    rw [Complex.zero_re]
    ring
  have hsum_eq : resolverGradReal p w y = ∑' k : ℕ, e k * m k := by
    unfold resolverGradReal
    exact tsum_congr hterm
  have hCS :
      |∑' k : ℕ, e k * m k| ≤
        Real.sqrt (∑' k : ℕ, (e k) ^ 2) *
          Real.sqrt (∑' k : ℕ, (m k) ^ 2) :=
    real_abs_tsum_mul_le_sqrt_tsum_sq_mul_sqrt_tsum_sq he_sq hm_sq
  have hA_l2 :
      Real.sqrt (∑' k : ℕ, (e k) ^ 2) ≤ coeffL2Norm A := by
    rw [coeffL2Norm, coeffL2Energy]
    apply Real.sqrt_le_sqrt
    refine he_sq.tsum_le_tsum ?_
      (ShenWork.PDE.intervalNeumannResolverR_source_l2_summable p w (fun _ => 0) hsrc)
    intro k
    have heq : (e k) ^ 2 = (A k).re * (A k).re := by
      dsimp [e]
      ring
    rw [heq]
    calc
      (A k).re * (A k).re ≤ Complex.normSq (A k) := Complex.re_sq_le_normSq _
      _ = ‖A k‖ ^ 2 := (Complex.sq_norm _).symm
  have hmW :
      Real.sqrt (∑' k : ℕ, (m k) ^ 2) ≤
        Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) := by
    apply Real.sqrt_le_sqrt
    refine hm_sq.tsum_le_tsum ?_
      (ShenWork.PDE.intervalNeumannResolverGradWeight_sq_summable p)
    intro k
    have hsin : (Real.sin ((k : ℝ) * Real.pi * y)) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]
      exact Real.abs_sin_le_one _
    have hgweq :
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2 =
          ((k : ℝ) * Real.pi) ^ 2 /
            (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) ^ 2 := by
      rw [ShenWork.PDE.intervalNeumannResolverGradWeight, div_pow]
    rw [hgweq]
    dsimp [m]
    rw [div_pow, mul_pow, neg_pow]
    have hkp : (0 : ℝ) ≤ ((k : ℝ) * Real.pi) ^ 2 := by positivity
    have hnum :
        (-1 : ℝ) ^ 2 * ((k : ℝ) * Real.pi) ^ 2 *
            (Real.sin ((k : ℝ) * Real.pi * y)) ^ 2 ≤
          ((k : ℝ) * Real.pi) ^ 2 := by
      have h1 : (-1 : ℝ) ^ 2 = 1 := by norm_num
      rw [h1, one_mul]
      nlinarith [hkp, hsin, sq_nonneg (Real.sin ((k : ℝ) * Real.pi * y))]
    gcongr
  rw [hsum_eq]
  have hcoeff := resolverSourceCoeff_l2Norm_le_of_abs_ball p hM hw_cont hball
  have hcoeff_nn : 0 ≤ coeffL2Norm A := Real.sqrt_nonneg _
  have hW_nn :
      0 ≤ Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) :=
    Real.sqrt_nonneg _
  calc
    |∑' k : ℕ, e k * m k|
        ≤ Real.sqrt (∑' k : ℕ, (e k) ^ 2) *
            Real.sqrt (∑' k : ℕ, (m k) ^ 2) := hCS
    _ ≤ coeffL2Norm A *
          Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) :=
      mul_le_mul hA_l2 hmW (Real.sqrt_nonneg _) hcoeff_nn
    _ ≤ (2 * (p.ν * M ^ p.γ)) *
          Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) :=
      mul_le_mul_of_nonneg_right hcoeff hW_nn
    _ = Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * M ^ p.γ)) := by ring

/-- Resolver-value series bound on a signed absolute ball. -/
theorem resolverValueSeries_abs_le_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M) (y : ℝ) :
    |∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverCoeff p w k).re *
        Real.cos ((k : ℝ) * Real.pi * y)| ≤
      Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ)) := by
  classical
  have hUcont : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) :=
    lift_continuousOn_Icc_of_continuous hw_cont
  let A : ℕ → ℂ := fun k =>
    ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k -
      ShenWork.PDE.intervalNeumannResolverSourceCoeff p (fun _ => 0) k
  let e : ℕ → ℝ := fun k => (A k).re
  let m : ℕ → ℝ := fun k =>
    Real.cos ((k : ℝ) * Real.pi * y) /
      (p.μ + unitIntervalNeumannSpectrum.eigenvalue k)
  have hsrc : Summable fun k : ℕ =>
      ((ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k -
        ShenWork.PDE.intervalNeumannResolverSourceCoeff p (fun _ => 0) k).re) ^ 2 := by
    simpa [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      ShenWork.IntervalResolverWeakBounds.resolverSourceCoeff_re_sq_summable_of_continuousOn
        p hUcont
  have he_sq : Summable fun k : ℕ => (e k) ^ 2 := by
    simpa [e, A] using hsrc
  have hm_sq : Summable fun k : ℕ => (m k) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) ?_
      (ShenWork.PDE.intervalNeumannResolverWeight_sq_summable p)
    intro k
    have hcos : (Real.cos ((k : ℝ) * Real.pi * y)) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]
      exact Real.abs_cos_le_one _
    have hweq :
        (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2 =
          1 / (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) ^ 2 := by
      rw [ShenWork.PDE.intervalNeumannResolverWeight]
      field_simp
    rw [hweq]
    dsimp [m]
    rw [div_pow]
    gcongr
  have hterm : ∀ k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverCoeff p w k).re *
          Real.cos ((k : ℝ) * Real.pi * y) = e k * m k := by
    intro k
    have hden : p.μ + unitIntervalNeumannSpectrum.eigenvalue k ≠ 0 :=
      ne_of_gt (ShenWork.PDE.intervalNeumannResolver_denom_pos p k)
    dsimp [e, A, m]
    rw [ShenWork.IntervalResolverGradientBridge.resolverCoeff_re_eq p w k]
    simp only [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero]
    field_simp [hden]
    rw [Complex.zero_re]
    ring
  have hsum_eq :
      (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverCoeff p w k).re *
          Real.cos ((k : ℝ) * Real.pi * y)) =
        ∑' k : ℕ, e k * m k :=
    tsum_congr hterm
  have hCS :
      |∑' k : ℕ, e k * m k| ≤
        Real.sqrt (∑' k : ℕ, (e k) ^ 2) *
          Real.sqrt (∑' k : ℕ, (m k) ^ 2) :=
    real_abs_tsum_mul_le_sqrt_tsum_sq_mul_sqrt_tsum_sq he_sq hm_sq
  have hA_l2 :
      Real.sqrt (∑' k : ℕ, (e k) ^ 2) ≤ coeffL2Norm A := by
    rw [coeffL2Norm, coeffL2Energy]
    apply Real.sqrt_le_sqrt
    refine he_sq.tsum_le_tsum ?_
      (ShenWork.PDE.intervalNeumannResolverR_source_l2_summable p w (fun _ => 0) hsrc)
    intro k
    have heq : (e k) ^ 2 = (A k).re * (A k).re := by
      dsimp [e]
      ring
    rw [heq]
    calc
      (A k).re * (A k).re ≤ Complex.normSq (A k) := Complex.re_sq_le_normSq _
      _ = ‖A k‖ ^ 2 := (Complex.sq_norm _).symm
  have hmW :
      Real.sqrt (∑' k : ℕ, (m k) ^ 2) ≤
        Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) := by
    apply Real.sqrt_le_sqrt
    refine hm_sq.tsum_le_tsum ?_
      (ShenWork.PDE.intervalNeumannResolverWeight_sq_summable p)
    intro k
    have hcos : (Real.cos ((k : ℝ) * Real.pi * y)) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]
      exact Real.abs_cos_le_one _
    have hweq :
        (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2 =
          1 / (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) ^ 2 := by
      rw [ShenWork.PDE.intervalNeumannResolverWeight]
      field_simp
    rw [hweq]
    dsimp [m]
    rw [div_pow]
    gcongr
  rw [hsum_eq]
  have hcoeff := resolverSourceCoeff_l2Norm_le_of_abs_ball p hM hw_cont hball
  have hcoeff_nn : 0 ≤ coeffL2Norm A := Real.sqrt_nonneg _
  have hW_nn :
      0 ≤ Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) :=
    Real.sqrt_nonneg _
  calc
    |∑' k : ℕ, e k * m k|
        ≤ Real.sqrt (∑' k : ℕ, (e k) ^ 2) *
            Real.sqrt (∑' k : ℕ, (m k) ^ 2) := hCS
    _ ≤ coeffL2Norm A *
          Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) :=
      mul_le_mul hA_l2 hmW (Real.sqrt_nonneg _) hcoeff_nn
    _ ≤ (2 * (p.ν * M ^ p.γ)) *
          Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) :=
      mul_le_mul_of_nonneg_right hcoeff hW_nn
    _ = Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
          (2 * (p.ν * M ^ p.γ)) := by ring

/-- Lifted resolver-value bound on a signed absolute ball. -/
theorem resolverR_lift_abs_le_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M) (y : ℝ) :
    |intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y| ≤
      Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
          (2 * (p.ν * M ^ p.γ)) := by
  classical
  let V : ℝ := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
      (2 * (p.ν * M ^ p.γ))
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · simpa [V, intervalDomainLift, hy, ShenWork.PDE.intervalNeumannResolverR,
      unitIntervalCosineMode] using
      resolverValueSeries_abs_le_of_abs_ball
        (p := p) (w := w) (M := M) hM hw_cont hball y
  · simp [intervalDomainLift, hy]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM.le _)))

/-- Uniform pointwise bound for the truncated chemotaxis flux on a signed
absolute ball. -/
theorem truncatedChemFluxLifted_abs_le_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M) :
    ∀ y : ℝ,
      |truncatedChemFluxLifted p w y| ≤
        M *
          (Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
              (2 * (p.ν * M ^ p.γ))) := by
  classical
  intro y
  let wPos : intervalDomainPoint → ℝ := fun x => positivePart (w x)
  let Γ : ℝ := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
      (2 * (p.ν * M ^ p.γ))
  have hM_nonneg : 0 ≤ M := hM.le
  have hΓ_nonneg : 0 ≤ Γ := by
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM_nonneg _)))
  have hwPos_cont : Continuous wPos := by
    simpa [wPos, positivePart] using hw_cont.max continuous_const
  have hwPos_ball : ∀ x : intervalDomainPoint, |wPos x| ≤ M := by
    intro x
    rw [abs_of_nonneg (positivePart_nonneg (w x))]
    exact (positivePart_le_abs (w x)).trans (hball x)
  have hgrad : |resolverGradReal p wPos y| ≤ Γ := by
    simpa [Γ] using
      resolverGrad_abs_le_of_abs_ball p hM hwPos_cont hwPos_ball y
  have hlift_abs : |intervalDomainLift w y| ≤ M := by
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · simpa [intervalDomainLift, hy] using hball ⟨y, hy⟩
    · simp [intervalDomainLift, hy, hM_nonneg]
  have hpos_abs : |positivePart (intervalDomainLift w y)| ≤ M := by
    rw [abs_of_nonneg (positivePart_nonneg _)]
    exact (positivePart_le_abs _).trans hlift_abs
  have hR_nonneg :
      0 ≤ intervalDomainLift
        (ShenWork.PDE.intervalNeumannResolverR p wPos) y := by
    simpa [wPos] using
      resolverR_positivePart_lift_nonneg_of_continuous p hw_cont y
  have hden_ge_one :
      1 ≤ (1 + intervalDomainLift
        (ShenWork.PDE.intervalNeumannResolverR p wPos) y) ^ p.β :=
    Real.one_le_rpow (by linarith [hR_nonneg]) p.hβ
  have hnum :
      |positivePart (intervalDomainLift w y)| * |resolverGradReal p wPos y| ≤
        M * Γ :=
    mul_le_mul hpos_abs hgrad (abs_nonneg _) hM_nonneg
  unfold truncatedChemFluxLifted
  calc
    |positivePart (intervalDomainLift w y) * resolverGradReal p wPos y /
        (1 + intervalDomainLift
          (ShenWork.PDE.intervalNeumannResolverR p wPos) y) ^ p.β|
        = |positivePart (intervalDomainLift w y) * resolverGradReal p wPos y| /
            |(1 + intervalDomainLift
              (ShenWork.PDE.intervalNeumannResolverR p wPos) y) ^ p.β| :=
          abs_div _ _
    _ ≤ |positivePart (intervalDomainLift w y) * resolverGradReal p wPos y| / 1 := by
      apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos
      rwa [abs_of_nonneg (zero_le_one.trans hden_ge_one)]
    _ = |positivePart (intervalDomainLift w y)| * |resolverGradReal p wPos y| := by
      rw [div_one, abs_mul]
    _ ≤ M * Γ := hnum
    _ = M *
          (Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
              (2 * (p.ν * M ^ p.γ))) := by
      rfl

/-- Time-family wrapper of `truncatedChemFluxLifted_abs_le_of_abs_ball`; only
the requested closed time window is quantified. -/
theorem truncatedChemFluxLifted_abs_le_on_window_of_abs_ball
    (p : CM2Params) {w : ℝ → intervalDomainPoint → ℝ} {M a hi : ℝ}
    (hM : 0 < M)
    (hw_cont : ∀ s, a ≤ s → s ≤ hi → Continuous (w s))
    (hball : ∀ s, a ≤ s → s ≤ hi →
      ∀ x : intervalDomainPoint, |w s x| ≤ M) :
    ∀ s, a ≤ s → s ≤ hi → ∀ y : ℝ,
      |truncatedChemFluxLifted p (w s) y| ≤
        M *
          (Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
              (2 * (p.ν * M ^ p.γ))) := by
  intro s has hshi
  exact truncatedChemFluxLifted_abs_le_of_abs_ball
    p hM (hw_cont s has hshi) (hball s has hshi)

end ShenWork.Paper2.TruncatedPositiveTimeBootstrap
