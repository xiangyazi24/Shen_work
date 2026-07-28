/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import ShenWork.Liang.StateSpace
import ShenWork.Liang.LinearDeterminacy
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Uniform extinction in a fast shifting habitat

This file proves the corrected fast-habitat extinction theorem.  The proof has
two independent analytic ingredients.

* A fixed exponential moment gives a global exponential supersolution for
  each component.
* Behind any intermediate speed, the negative left-hand environmental limit
  supplies a uniform contraction.  Ahead of that speed, the exponential
  supersolution is uniformly small.

Combining the two regions gives a scalar sup-norm recurrence with a geometric
forcing term, and hence uniform extinction.
-/

open Filter MeasureTheory Topology
open scoped BoundedContinuousFunction

namespace ShenWork.Liang

noncomputable section

/-- Integrability of the exponentially weighted kernel is exactly what is
needed to convolve the kernel against a translated exponential tail. -/
theorem kernel_mul_exponentialTail_integrable
    {K : ℝ → ℝ} {μ x : ℝ}
    (hKμ : Integrable (fun z => K z * Real.exp (μ * z))) :
    Integrable
      (fun y => K (x - y) * ShenWork.Analysis.exponentialTail μ y) := by
  have hshift :
      Integrable
        (fun y => K (x - y) * Real.exp (μ * (x - y))) :=
    hKμ.comp_sub_left x
  have hscaled :=
    hshift.const_mul (Real.exp (-μ * x))
  convert hscaled using 1
  funext y
  unfold ShenWork.Analysis.exponentialTail
  rw [show -μ * y = -μ * x + μ * (x - y) by ring, Real.exp_add]
  ring

/-- Every time slice of the explicit exponential orbit is integrable against
the translated kernel. -/
theorem kernel_mul_exponentialOrbit_integrable
    {K : ℝ → ℝ} {amplitude growth μ x : ℝ} {n : ℕ}
    (hKμ : Integrable (fun z => K z * Real.exp (μ * z))) :
    Integrable
      (fun y =>
        K (x - y) *
          ShenWork.Analysis.exponentialOrbit amplitude growth
            (ShenWork.Analysis.kernelMoment K μ) μ n y) := by
  have htail :=
    kernel_mul_exponentialTail_integrable (x := x) hKμ
  have hscaled :=
    htail.const_mul
      (amplitude *
        (growth * ShenWork.Analysis.kernelMoment K μ) ^ n)
  convert hscaled using 1
  funext y
  unfold ShenWork.Analysis.exponentialOrbit
  ring

/-- The corrected nonlinear component is bounded for all generations by the
explicit exponential orbit selected by one positive exponential moment. -/
theorem correctedComponent_le_exponentialOrbit
    (K ρ : ℝ → ℝ)
    (hKcont : Continuous K) (hKint : Integrable K)
    (hKnonneg : ∀ z, 0 ≤ K z)
    (hρcont : Continuous ρ) (hρlow : ∀ z, -1 < ρ z)
    (ρplus α c amplitude growth μ : ℝ)
    (hρup : ∀ z, ρ z ≤ ρplus)
    (hα : 0 ≤ α)
    (w competitor : ℕ → ℝ →ᵇ ℝ)
    (hw_nonneg : ∀ n x, 0 ≤ w n x)
    (hw_le_one : ∀ n x, w n x ≤ 1)
    (hcompetitor_nonneg : ∀ n x, 0 ≤ competitor n x)
    (hstep :
      ∀ n,
        w (n + 1) =
          correctedStepBCF K ρ hKcont hKint hρcont hρlow
            α hα c n (w n) (competitor n)
              (hw_nonneg n) (hw_le_one n) (hcompetitor_nonneg n))
    (hgrowth : growth = 1 + ρplus)
    (hgrowth_nonneg : 0 ≤ growth)
    (hinit :
      ∀ x,
        w 0 x ≤
          amplitude * ShenWork.Analysis.exponentialTail μ x)
    (hKμ : Integrable (fun z => K z * Real.exp (μ * z))) :
    ∀ n x,
      w n x ≤
        ShenWork.Analysis.exponentialOrbit amplitude growth
          (ShenWork.Analysis.kernelMoment K μ) μ n x := by
  subst growth
  apply sublinear_orbit_le_exponentialOrbit
    K (fun n x => w n x) amplitude (1 + ρplus) μ
    hKnonneg hgrowth_nonneg hinit
  · intro n x
    rw [hstep n, correctedStepBCF_apply]
    apply heterogeneousCorrectedStep_le_linear
      hKnonneg hρlow hρup hα
      (hw_nonneg n) (hcompetitor_nonneg n)
    · exact heterogeneousCorrectedIntegrable
        hKint hKcont hρcont hρlow hα
        (w n).continuous (hw_nonneg n) (hw_le_one n)
        (competitor n).continuous (hcompetitor_nonneg n)
    · have hwint :=
        ShenWork.Paper1.kernelConv_integrand_integrable
          hKcont hKint (w n) x
      have hscaled := hwint.const_mul (1 + ρplus)
      convert hscaled using 1
      · funext y
        ring
  · intro n x
    exact ShenWork.Paper1.kernelConv_integrand_integrable
      hKcont hKint (w n) x
  · intro n x
    exact kernel_mul_exponentialOrbit_integrable hKμ

/-- An exponential orbit decreases in space when its exponential weight is
positive. -/
theorem exponentialOrbit_le_movingFrame_of_ge
    {amplitude growth moment μ s y : ℝ} {n : ℕ}
    (hamplitude : 0 ≤ amplitude)
    (hR : 0 ≤ growth * moment)
    (hμ : 0 < μ)
    (hy : s * (n : ℝ) ≤ y) :
    ShenWork.Analysis.exponentialOrbit amplitude growth moment μ n y ≤
      ShenWork.Analysis.exponentialOrbit amplitude growth moment μ n
        (s * (n : ℝ)) := by
  unfold ShenWork.Analysis.exponentialOrbit
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg hamplitude (pow_nonneg hR n))
  unfold ShenWork.Analysis.exponentialTail
  apply Real.exp_le_exp.mpr
  nlinarith

/-- A probability convolution preserves a uniform nonnegative upper bound on
the corrected local source. -/
theorem correctedStepBCF_norm_le_of_source_le
    (K ρ : ℝ → ℝ)
    (hKcont : Continuous K) (hKint : Integrable K)
    (hKnonneg : ∀ z, 0 ≤ K z) (hKmass : ∫ z, K z = 1)
    (hρcont : Continuous ρ) (hρlow : ∀ z, -1 < ρ z)
    (α : ℝ) (hα : 0 ≤ α) (c : ℝ) (n : ℕ)
    (u v : ℝ →ᵇ ℝ)
    (hu : ∀ x, 0 ≤ u x) (hu1 : ∀ x, u x ≤ 1)
    (hv : ∀ x, 0 ≤ v x)
    (C : ℝ) (hC : 0 ≤ C)
    (hsource :
      ∀ y,
        correctedResponse (ρ (y - c * (n : ℝ))) α (u y) (v y) ≤ C) :
    ‖correctedStepBCF K ρ hKcont hKint hρcont hρlow
        α hα c n u v hu hu1 hv‖ ≤ C := by
  rw [BoundedContinuousFunction.norm_le hC]
  intro x
  have hout0 :
      0 ≤
        correctedStepBCF K ρ hKcont hKint hρcont hρlow
          α hα c n u v hu hu1 hv x := by
    rw [correctedStepBCF_apply]
    exact
      (heterogeneousCorrectedStep_mem_unitInterval_of_continuous
        hKint hKcont hKnonneg hKmass hρcont hρlow hα
        u.continuous hu hu1 v.continuous hv).1
  rw [Real.norm_eq_abs, abs_of_nonneg hout0]
  rw [correctedStepBCF_apply]
  unfold heterogeneousCorrectedStep ShenWork.Analysis.dispersal
  have hleft :
      Integrable
        (fun y =>
          K (x - y) *
            correctedResponse (ρ (y - c * (n : ℝ))) α (u y) (v y)) :=
    heterogeneousCorrectedIntegrable
      hKint hKcont hρcont hρlow hα
      u.continuous hu hu1 v.continuous hv
  have hright : Integrable (fun y => K (x - y) * C) :=
    (hKint.comp_sub_left x).mul_const C
  calc
    (∫ y,
        K (x - y) *
          correctedResponse (ρ (y - c * (n : ℝ))) α (u y) (v y)) ≤
        (∫ y, K (x - y) * C) := by
      apply integral_mono hleft hright
      intro y
      exact mul_le_mul_of_nonneg_left (hsource y) (hKnonneg (x - y))
    _ = C * ∫ y, K (x - y) := by
      rw [show (fun y => K (x - y) * C) =
          fun y => C * K (x - y) by
        funext y
        ring]
      rw [integral_const_mul]
    _ = C * ∫ z, K z := by
      rw [integral_sub_left_eq_self K (volume : Measure ℝ) x]
    _ = C := by rw [hKmass, mul_one]

/-- Explicit majorant used for the forced scalar contraction below. -/
private def fastGeometricMajorant (θ B D : ℝ) (n : ℕ) : ℝ :=
  θ ^ n * (B + D * (n : ℝ))

private theorem fastGeometricMajorant_step
    {q r C θ B D : ℝ}
    (hr0 : 0 ≤ r) (hC0 : 0 ≤ C)
    (hθ0 : 0 ≤ θ) (hB0 : 0 ≤ B) (hD0 : 0 ≤ D)
    (hqθ : q ≤ θ) (hrθ : r ≤ θ) (hCD : C ≤ θ * D)
    (n : ℕ) :
    q * fastGeometricMajorant θ B D n + C * r ^ n ≤
      fastGeometricMajorant θ B D (n + 1) := by
  have hmajor0 : 0 ≤ fastGeometricMajorant θ B D n := by
    unfold fastGeometricMajorant
    positivity
  have hqpart :
      q * fastGeometricMajorant θ B D n ≤
        θ * fastGeometricMajorant θ B D n :=
    mul_le_mul_of_nonneg_right hqθ hmajor0
  have hrpow : r ^ n ≤ θ ^ n :=
    pow_le_pow_left₀ hr0 hrθ n
  have hforce :
      C * r ^ n ≤ (θ * D) * θ ^ n := by
    calc
      C * r ^ n ≤ C * θ ^ n :=
        mul_le_mul_of_nonneg_left hrpow hC0
      _ ≤ (θ * D) * θ ^ n :=
        mul_le_mul_of_nonneg_right hCD (pow_nonneg hθ0 n)
  calc
    q * fastGeometricMajorant θ B D n + C * r ^ n ≤
        θ * fastGeometricMajorant θ B D n + (θ * D) * θ ^ n :=
      add_le_add hqpart hforce
    _ = fastGeometricMajorant θ B D (n + 1) := by
      simp only [fastGeometricMajorant, pow_succ, Nat.cast_add,
        Nat.cast_one]
      ring

/-- A nonnegative scalar contraction with geometric forcing converges to
zero. -/
theorem fastExtinction_recurrence_tendsto_zero
    {b : ℕ → ℝ} {q r C B : ℝ}
    (hb0 : ∀ n, 0 ≤ b n)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hC0 : 0 ≤ C) (hB0 : 0 ≤ B) (hb_init : b 0 ≤ B)
    (hstep : ∀ n, b (n + 1) ≤ q * b n + C * r ^ n) :
    Tendsto b atTop (𝓝 0) := by
  let θ := (1 + max q r) / 2
  have hm0 : 0 ≤ max q r :=
    hq0.trans (le_max_left q r)
  have hm1 : max q r < 1 :=
    max_lt hq1 hr1
  have hθ0 : 0 < θ := by
    dsimp [θ]
    linarith
  have hθ1 : θ < 1 := by
    dsimp [θ]
    linarith
  have hqθ : q ≤ θ := by
    have hqm : q ≤ max q r := le_max_left _ _
    dsimp [θ]
    linarith
  have hrθ : r ≤ θ := by
    have hrm : r ≤ max q r := le_max_right _ _
    dsimp [θ]
    linarith
  let D := C / θ
  have hD0 : 0 ≤ D := div_nonneg hC0 hθ0.le
  have hCD : C ≤ θ * D := by
    have heq : C = θ * (C / θ) :=
      (mul_div_cancel₀ C (ne_of_gt hθ0)).symm
    simpa [D] using heq.le
  have hmajor :
      ∀ n, b n ≤ fastGeometricMajorant θ B D n := by
    intro n
    induction n with
    | zero =>
        simpa [fastGeometricMajorant] using hb_init
    | succ n ih =>
        calc
          b (n + 1) ≤ q * b n + C * r ^ n := hstep n
          _ ≤
              q * fastGeometricMajorant θ B D n + C * r ^ n :=
            add_le_add (mul_le_mul_of_nonneg_left ih hq0) le_rfl
          _ ≤ fastGeometricMajorant θ B D (n + 1) :=
            fastGeometricMajorant_step
              hr0 hC0 hθ0.le hB0 hD0 hqθ hrθ hCD n
  have hpow :
      Tendsto (fun n : ℕ => θ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hθ0.le hθ1
  have hnpow :
      Tendsto (fun n : ℕ => (n : ℝ) * θ ^ n) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_lt_one hθ0.le hθ1
  have hmajor_tendsto :
      Tendsto (fastGeometricMajorant θ B D) atTop (𝓝 0) := by
    have hsum :=
      (hpow.mul_const B).add (hnpow.const_mul D)
    have heq :
        fastGeometricMajorant θ B D =
          fun n : ℕ => θ ^ n * B + D * ((n : ℝ) * θ ^ n) := by
      funext n
      unfold fastGeometricMajorant
      ring
    rw [heq]
    simpa using hsum
  exact squeeze_zero hb0 hmajor hmajor_tendsto

/-- One corrected component goes extinct uniformly when a fixed exponential
weight has speed below an intermediate frame, while that frame remains behind
the habitat.  The environmental hypotheses are precisely the monotonicity and
negative left limit used to obtain contraction in the trailing region. -/
theorem correctedComponent_fastHabitat_extinction_of_witness
    (K ρ : ℝ → ℝ)
    (hKcont : Continuous K) (hKint : Integrable K)
    (hKnonneg : ∀ z, 0 ≤ K z) (hKmass : ∫ z, K z = 1)
    (hρcont : Continuous ρ) (hρlow : ∀ z, -1 < ρ z)
    (hρmono : Monotone ρ)
    (ρminus ρplus α c amplitude μ s : ℝ)
    (hρminus_low : -1 < ρminus) (hρminus_neg : ρminus < 0)
    (hρminus : Tendsto ρ atBot (𝓝 ρminus))
    (hρup : ∀ z, ρ z ≤ ρplus)
    (hα : 0 ≤ α)
    (hamplitude : 0 ≤ amplitude)
    (hgrowth_nonneg : 0 ≤ 1 + ρplus)
    (hR :
      0 <
        (1 + ρplus) *
          ShenWork.Analysis.kernelMoment K μ)
    (hμ : 0 < μ)
    (hspeed : kernelSpeedAt K (1 + ρplus) μ < s)
    (hframe : s < c)
    (hKμ : Integrable (fun z => K z * Real.exp (μ * z)))
    (w competitor : ℕ → ℝ →ᵇ ℝ)
    (hw_nonneg : ∀ n x, 0 ≤ w n x)
    (hw_le_one : ∀ n x, w n x ≤ 1)
    (hcompetitor_nonneg : ∀ n x, 0 ≤ competitor n x)
    (hstep :
      ∀ n,
        w (n + 1) =
          correctedStepBCF K ρ hKcont hKint hρcont hρlow
            α hα c n (w n) (competitor n)
              (hw_nonneg n) (hw_le_one n) (hcompetitor_nonneg n))
    (hinit :
      ∀ x,
        w 0 x ≤
          amplitude * ShenWork.Analysis.exponentialTail μ x) :
    Tendsto (fun n => ‖w n‖) atTop (𝓝 0) := by
  let growth : ℝ := 1 + ρplus
  let R : ℝ :=
    growth * ShenWork.Analysis.kernelMoment K μ
  let r : ℝ := R * Real.exp (-μ * s)
  let q : ℝ := 1 + ρminus / 2
  have hgrowth0 : 0 ≤ growth := by
    simpa [growth] using hgrowth_nonneg
  have hRpos : 0 < R := by
    simpa [R, growth] using hR
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    have :=
      ShenWork.Analysis.movingFrame_ratio_lt_one_of_speed_gt
        hR hμ hspeed
    simpa [r, R, growth, kernelSpeedAt, exponentialSpeed] using this
  have hq0 : 0 ≤ q := by
    dsimp [q]
    linarith
  have hq1 : q < 1 := by
    dsimp [q]
    linarith
  have hbarrier :
      ∀ n x,
        w n x ≤
          ShenWork.Analysis.exponentialOrbit amplitude growth
            (ShenWork.Analysis.kernelMoment K μ) μ n x := by
    exact correctedComponent_le_exponentialOrbit
      K ρ hKcont hKint hKnonneg hρcont hρlow
      ρplus α c amplitude growth μ hρup hα
      w competitor hw_nonneg hw_le_one hcompetitor_nonneg
      hstep rfl hgrowth0 hinit hKμ
  have hargument :
      Tendsto (fun n : ℕ => (s - c) * (n : ℝ)) atTop atBot := by
    exact
      tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg
        (by linarith)
  have hρframe :
      Tendsto (fun n : ℕ => ρ ((s - c) * (n : ℝ)))
        atTop (𝓝 ρminus) :=
    hρminus.comp hargument
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        ρ ((s - c) * (n : ℝ)) < ρminus / 2 :=
    (tendsto_order.1 hρframe).2 _ (by linarith)
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hevent)
  have hzone :
      ∀ n, N ≤ n → ∀ y, y ≤ s * (n : ℝ) →
        1 + ρ (y - c * (n : ℝ)) ≤ q := by
    intro n hn y hy
    have hargle :
        y - c * (n : ℝ) ≤ (s - c) * (n : ℝ) := by
      nlinarith
    have hmonole :=
      hρmono hargle
    have htail := hN n hn
    dsimp [q]
    linarith
  have hnorm_step :
      ∀ n, N ≤ n →
        ‖w (n + 1)‖ ≤
          q * ‖w n‖ + growth * amplitude * r ^ n := by
    intro n hn
    rw [hstep n]
    apply correctedStepBCF_norm_le_of_source_le
      K ρ hKcont hKint hKnonneg hKmass hρcont hρlow
      α hα c n (w n) (competitor n)
      (hw_nonneg n) (hw_le_one n) (hcompetitor_nonneg n)
    · positivity
    · intro y
      by_cases hy : y ≤ s * (n : ℝ)
      · have hcontract := hzone n hn y hy
        have hρnonpos :
            ρ (y - c * (n : ℝ)) ≤ 0 := by
          linarith
        rw [correctedResponse_eq_linear_of_nonpos hρnonpos]
        calc
          (1 + ρ (y - c * (n : ℝ))) * w n y ≤
              q * w n y :=
            mul_le_mul_of_nonneg_right hcontract (hw_nonneg n y)
          _ ≤ q * ‖w n‖ :=
            mul_le_mul_of_nonneg_left
              (BoundedContinuousFunction.apply_le_norm (w n) y) hq0
          _ ≤ q * ‖w n‖ + growth * amplitude * r ^ n := by
            exact le_add_of_nonneg_right
              (mul_nonneg
                (mul_nonneg hgrowth0 hamplitude)
                (pow_nonneg hr0 n))
      · have hy' : s * (n : ℝ) ≤ y :=
          le_of_not_ge hy
        have hmoving :
            w n y ≤ amplitude * r ^ n := by
          calc
            w n y ≤
                ShenWork.Analysis.exponentialOrbit amplitude growth
                  (ShenWork.Analysis.kernelMoment K μ) μ n y :=
              hbarrier n y
            _ ≤
                ShenWork.Analysis.exponentialOrbit amplitude growth
                  (ShenWork.Analysis.kernelMoment K μ) μ n
                    (s * (n : ℝ)) :=
              exponentialOrbit_le_movingFrame_of_ge
                hamplitude hRpos.le hμ hy'
            _ = amplitude * r ^ n := by
              rw [ShenWork.Analysis.exponentialOrbit_movingFrame]
        calc
          correctedResponse (ρ (y - c * (n : ℝ))) α
              (w n y) (competitor n y) ≤
              (1 + ρ (y - c * (n : ℝ))) * w n y :=
            correctedResponse_le_linear
              (hρlow _) hα (hw_nonneg n y)
                (hcompetitor_nonneg n y)
          _ ≤ growth * w n y := by
            apply mul_le_mul_of_nonneg_right _ (hw_nonneg n y)
            dsimp [growth]
            linarith [hρup (y - c * (n : ℝ))]
          _ ≤ growth * (amplitude * r ^ n) :=
            mul_le_mul_of_nonneg_left hmoving hgrowth0
          _ ≤ q * ‖w n‖ + growth * amplitude * r ^ n := by
            have hqnorm : 0 ≤ q * ‖w n‖ :=
              mul_nonneg hq0 (norm_nonneg _)
            nlinarith
  let b : ℕ → ℝ := fun m => ‖w (m + N)‖
  let C : ℝ := growth * amplitude * r ^ N
  have hb0 : ∀ m, 0 ≤ b m :=
    fun m => norm_nonneg _
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbrec :
      ∀ m, b (m + 1) ≤ q * b m + C * r ^ m := by
    intro m
    dsimp [b]
    have h :=
      hnorm_step (m + N) (Nat.le_add_left N m)
    rw [show m + 1 + N = (m + N) + 1 by omega]
    calc
      ‖w (m + N + 1)‖ ≤
          q * ‖w (m + N)‖ +
            growth * amplitude * r ^ (m + N) := h
      _ = q * ‖w (m + N)‖ + C * r ^ m := by
        dsimp [C]
        rw [pow_add]
        ring
  have hb_tendsto :
      Tendsto b atTop (𝓝 0) :=
    fastExtinction_recurrence_tendsto_zero
      hb0 hq0 hq1 hr0 hr1 hC0 (norm_nonneg (w N))
        (by simp [b]) hbrec
  apply (tendsto_add_atTop_iff_nat N).mp
  simpa only [b, Nat.add_comm] using hb_tendsto

/-! ## Variational speed and the corrected component theorem -/

/-- A positive exponential weight at which the kernel moment is genuinely
finite and the corresponding linear multiplier is positive. -/
structure ExtinctionWeight (K : ℝ → ℝ) (growth : ℝ) where
  exponent : ℝ
  exponent_pos : 0 < exponent
  weightedKernel_integrable :
    Integrable (fun z => K z * Real.exp (exponent * z))
  linearMultiplier_pos :
    0 <
      growth *
        ShenWork.Analysis.kernelMoment K exponent

/-- The variational speed over the exponential weights for which the
linearized IDE is analytically well-defined. -/
def extinctionCriticalSpeed (K : ℝ → ℝ) (growth : ℝ) : ℝ :=
  ⨅ η : ExtinctionWeight K growth,
    kernelSpeedAt K growth η.exponent

/-- A habitat moving faster than the admissible variational speed leaves room
for an intermediate frame and a concrete admissible exponential weight. -/
theorem exists_extinctionWeight_and_frame
    {K : ℝ → ℝ} {growth c : ℝ}
    (hweights : Nonempty (ExtinctionWeight K growth))
    (hc : extinctionCriticalSpeed K growth < c) :
    ∃ s : ℝ, ∃ η : ExtinctionWeight K growth,
      extinctionCriticalSpeed K growth < s ∧
      s < c ∧
      kernelSpeedAt K growth η.exponent < s := by
  let s := (extinctionCriticalSpeed K growth + c) / 2
  have hcritical_s : extinctionCriticalSpeed K growth < s := by
    dsimp [s]
    linarith
  have hs_c : s < c := by
    dsimp [s]
    linarith
  letI := hweights
  unfold extinctionCriticalSpeed at hcritical_s
  obtain ⟨η, hη⟩ := exists_lt_of_ciInf_lt hcritical_s
  exact ⟨s, η, by simpa [s], hs_c, hη⟩

/-- A profile bounded by one and vanishing to the right of `L` is bounded by
every positive exponential tail, with explicit amplitude `exp (μL)`. -/
theorem initial_le_exponentialTail_of_right_support
    (u : ℝ →ᵇ ℝ) {μ L : ℝ}
    (hμ : 0 < μ)
    (hu_le_one : ∀ x, u x ≤ 1)
    (hsupport : ∀ x, L < x → u x = 0) :
    ∀ x,
      u x ≤
        Real.exp (μ * L) *
          ShenWork.Analysis.exponentialTail μ x := by
  intro x
  by_cases hx : x ≤ L
  · calc
      u x ≤ 1 := hu_le_one x
      _ ≤
          Real.exp (μ * L) *
            ShenWork.Analysis.exponentialTail μ x := by
        unfold ShenWork.Analysis.exponentialTail
        rw [← Real.exp_add]
        have hexp :
            Real.exp 0 ≤ Real.exp (μ * L + -μ * x) :=
          Real.exp_le_exp.mpr (by nlinarith)
        simpa using hexp
  · rw [hsupport x (lt_of_not_ge hx)]
    exact mul_nonneg (Real.exp_pos _).le
      (by
        unfold ShenWork.Analysis.exponentialTail
        exact (Real.exp_pos _).le)

/-- Variational form of the corrected one-component fast-habitat theorem.
The right-support hypothesis is implied by compact support and supplies the
initial exponential bound for the selected weight. -/
theorem correctedComponent_fastHabitat_extinction
    (K ρ : ℝ → ℝ)
    (hKcont : Continuous K) (hKint : Integrable K)
    (hKnonneg : ∀ z, 0 ≤ K z) (hKmass : ∫ z, K z = 1)
    (hρcont : Continuous ρ) (hρlow : ∀ z, -1 < ρ z)
    (hρmono : Monotone ρ)
    (ρminus ρplus α c L : ℝ)
    (hρminus_low : -1 < ρminus) (hρminus_neg : ρminus < 0)
    (hρminus : Tendsto ρ atBot (𝓝 ρminus))
    (hρup : ∀ z, ρ z ≤ ρplus)
    (hα : 0 ≤ α)
    (hgrowth_nonneg : 0 ≤ 1 + ρplus)
    (hweights :
      Nonempty (ExtinctionWeight K (1 + ρplus)))
    (hfast :
      extinctionCriticalSpeed K (1 + ρplus) < c)
    (w competitor : ℕ → ℝ →ᵇ ℝ)
    (hw_nonneg : ∀ n x, 0 ≤ w n x)
    (hw_le_one : ∀ n x, w n x ≤ 1)
    (hcompetitor_nonneg : ∀ n x, 0 ≤ competitor n x)
    (hstep :
      ∀ n,
        w (n + 1) =
          correctedStepBCF K ρ hKcont hKint hρcont hρlow
            α hα c n (w n) (competitor n)
              (hw_nonneg n) (hw_le_one n) (hcompetitor_nonneg n))
    (hsupport : ∀ x, L < x → w 0 x = 0) :
    Tendsto (fun n => ‖w n‖) atTop (𝓝 0) := by
  obtain ⟨s, η, _hcritical_s, hs_c, hηs⟩ :=
    exists_extinctionWeight_and_frame hweights hfast
  let amplitude := Real.exp (η.exponent * L)
  have hamplitude : 0 ≤ amplitude := by
    dsimp [amplitude]
    positivity
  have hinit :
      ∀ x,
        w 0 x ≤
          amplitude *
            ShenWork.Analysis.exponentialTail η.exponent x := by
    exact initial_le_exponentialTail_of_right_support
      (w 0) η.exponent_pos (hw_le_one 0) hsupport
  exact correctedComponent_fastHabitat_extinction_of_witness
    K ρ hKcont hKint hKnonneg hKmass
    hρcont hρlow hρmono
    ρminus ρplus α c amplitude η.exponent s
    hρminus_low hρminus_neg hρminus hρup hα
    hamplitude hgrowth_nonneg η.linearMultiplier_pos
    η.exponent_pos hηs hs_c η.weightedKernel_integrable
    w competitor hw_nonneg hw_le_one hcompetitor_nonneg
    hstep hinit

/-! ## Two-species state-space theorem -/

/-- A nondecreasing profile never exceeds its finite limit at `+∞`. -/
theorem monotone_le_atTop_limit
    {ρ : ℝ → ℝ} {ρplus : ℝ}
    (hρmono : Monotone ρ)
    (hρplus : Tendsto ρ atTop (𝓝 ρplus)) :
    ∀ x, ρ x ≤ ρplus := by
  intro x
  apply ge_of_tendsto hρplus
  filter_upwards [eventually_ge_atTop x] with y hy
  exact hρmono hy

/-- Corrected Theorem 2.1: if the habitat outruns both admissible
linear-determinacy speeds, then both species go extinct uniformly.  Compactly
supported initial data enter only through the stated right-support bounds. -/
theorem correctedIDEOrbit_fastHabitat_extinction
    (p : CorrectedIDEData) (s₀ : UnitIDEState)
    (ρminus₁ ρplus₁ ρminus₂ ρplus₂ L₁ L₂ : ℝ)
    (hρmono₁ : Monotone p.environment₁)
    (hρmono₂ : Monotone p.environment₂)
    (hρminus₁_low : -1 < ρminus₁)
    (hρminus₂_low : -1 < ρminus₂)
    (hρminus₁_neg : ρminus₁ < 0)
    (hρminus₂_neg : ρminus₂ < 0)
    (hρminus₁ :
      Tendsto p.environment₁ atBot (𝓝 ρminus₁))
    (hρminus₂ :
      Tendsto p.environment₂ atBot (𝓝 ρminus₂))
    (hρplus₁ :
      Tendsto p.environment₁ atTop (𝓝 ρplus₁))
    (hρplus₂ :
      Tendsto p.environment₂ atTop (𝓝 ρplus₂))
    (hρplus₁_pos : 0 < ρplus₁)
    (hρplus₂_pos : 0 < ρplus₂)
    (hweights₁ :
      Nonempty
        (ExtinctionWeight p.kernel₁ (1 + ρplus₁)))
    (hweights₂ :
      Nonempty
        (ExtinctionWeight p.kernel₂ (1 + ρplus₂)))
    (hfast :
      max
          (extinctionCriticalSpeed p.kernel₁ (1 + ρplus₁))
          (extinctionCriticalSpeed p.kernel₂ (1 + ρplus₂)) <
        p.habitatSpeed)
    (hsupport₁ : ∀ x, L₁ < x → s₀.u x = 0)
    (hsupport₂ : ∀ x, L₂ < x → s₀.v x = 0) :
    Tendsto
        (fun n => ‖(correctedIDEOrbit p s₀ n).u‖)
        atTop (𝓝 0) ∧
      Tendsto
        (fun n => ‖(correctedIDEOrbit p s₀ n).v‖)
        atTop (𝓝 0) := by
  let u : ℕ → ℝ →ᵇ ℝ :=
    fun n => (correctedIDEOrbit p s₀ n).u
  let v : ℕ → ℝ →ᵇ ℝ :=
    fun n => (correctedIDEOrbit p s₀ n).v
  have hu_nonneg : ∀ n x, 0 ≤ u n x :=
    fun n => (correctedIDEOrbit p s₀ n).u_nonnegative
  have hu_le_one : ∀ n x, u n x ≤ 1 :=
    fun n => (correctedIDEOrbit p s₀ n).u_le_one
  have hv_nonneg : ∀ n x, 0 ≤ v n x :=
    fun n => (correctedIDEOrbit p s₀ n).v_nonnegative
  have hv_le_one : ∀ n x, v n x ≤ 1 :=
    fun n => (correctedIDEOrbit p s₀ n).v_le_one
  have hstep_u :
      ∀ n,
        u (n + 1) =
          correctedStepBCF
            p.kernel₁ p.environment₁
            p.kernel₁_continuous p.kernel₁_integrable
            p.environment₁_continuous p.environment₁_gt_neg_one
            p.competition₁ p.competition₁_nonnegative
            p.habitatSpeed n (u n) (v n)
              (hu_nonneg n) (hu_le_one n) (hv_nonneg n) := by
    intro n
    change
      (correctedIDEOrbit p s₀ (n + 1)).u =
        correctedStepBCF
          p.kernel₁ p.environment₁
          p.kernel₁_continuous p.kernel₁_integrable
          p.environment₁_continuous p.environment₁_gt_neg_one
          p.competition₁ p.competition₁_nonnegative
          p.habitatSpeed n
          (correctedIDEOrbit p s₀ n).u
          (correctedIDEOrbit p s₀ n).v _ _ _
    rw [correctedIDEOrbit_succ]
    rfl
  have hstep_v :
      ∀ n,
        v (n + 1) =
          correctedStepBCF
            p.kernel₂ p.environment₂
            p.kernel₂_continuous p.kernel₂_integrable
            p.environment₂_continuous p.environment₂_gt_neg_one
            p.competition₂ p.competition₂_nonnegative
            p.habitatSpeed n (v n) (u n)
              (hv_nonneg n) (hv_le_one n) (hu_nonneg n) := by
    intro n
    change
      (correctedIDEOrbit p s₀ (n + 1)).v =
        correctedStepBCF
          p.kernel₂ p.environment₂
          p.kernel₂_continuous p.kernel₂_integrable
          p.environment₂_continuous p.environment₂_gt_neg_one
          p.competition₂ p.competition₂_nonnegative
          p.habitatSpeed n
          (correctedIDEOrbit p s₀ n).v
          (correctedIDEOrbit p s₀ n).u _ _ _
    rw [correctedIDEOrbit_succ]
    rfl
  have hρup₁ : ∀ z, p.environment₁ z ≤ ρplus₁ :=
    monotone_le_atTop_limit hρmono₁ hρplus₁
  have hρup₂ : ∀ z, p.environment₂ z ≤ ρplus₂ :=
    monotone_le_atTop_limit hρmono₂ hρplus₂
  have hfast₁ :
      extinctionCriticalSpeed p.kernel₁ (1 + ρplus₁) <
        p.habitatSpeed :=
    lt_of_le_of_lt (le_max_left _ _) hfast
  have hfast₂ :
      extinctionCriticalSpeed p.kernel₂ (1 + ρplus₂) <
        p.habitatSpeed :=
    lt_of_le_of_lt (le_max_right _ _) hfast
  have hu_extinct :
      Tendsto (fun n => ‖u n‖) atTop (𝓝 0) := by
    apply correctedComponent_fastHabitat_extinction
      p.kernel₁ p.environment₁
      p.kernel₁_continuous p.kernel₁_integrable
      p.kernel₁_nonnegative p.kernel₁_mass
      p.environment₁_continuous p.environment₁_gt_neg_one
      hρmono₁ ρminus₁ ρplus₁ p.competition₁
      p.habitatSpeed L₁ hρminus₁_low hρminus₁_neg
      hρminus₁ hρup₁ p.competition₁_nonnegative
      (by linarith) hweights₁ hfast₁
      u v hu_nonneg hu_le_one hv_nonneg hstep_u
    simpa [u] using hsupport₁
  have hv_extinct :
      Tendsto (fun n => ‖v n‖) atTop (𝓝 0) := by
    apply correctedComponent_fastHabitat_extinction
      p.kernel₂ p.environment₂
      p.kernel₂_continuous p.kernel₂_integrable
      p.kernel₂_nonnegative p.kernel₂_mass
      p.environment₂_continuous p.environment₂_gt_neg_one
      hρmono₂ ρminus₂ ρplus₂ p.competition₂
      p.habitatSpeed L₂ hρminus₂_low hρminus₂_neg
      hρminus₂ hρup₂ p.competition₂_nonnegative
      (by linarith) hweights₂ hfast₂
      v u hv_nonneg hv_le_one hu_nonneg hstep_v
    simpa [v] using hsupport₂
  simpa only [u, v] using And.intro hu_extinct hv_extinct

section AxiomAudit

#print axioms correctedComponent_fastHabitat_extinction_of_witness
#print axioms correctedComponent_fastHabitat_extinction
#print axioms correctedIDEOrbit_fastHabitat_extinction

end AxiomAudit

end

end ShenWork.Liang
