import ShenWork.Paper1.WholeLineWeightedRegularityRawDQPDEOneStep
import ShenWork.Paper1.WholeLineWeightedRegularityRawDQTimeShift
import ShenWork.Paper1.WholeLineWeightedRegularityRawDQUniformWave

open MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Scalarization of the raw-DQ restart inequality

The concrete PDE estimate is written with separate homogeneous, flux, and
reaction majorants on an absolute-time interval.  This file changes to
restart-time coordinates, removes the remaining dependence on the spatial
difference step, and collects the result into the native Henry kernel.
-/

def rawDQHenryA0 (eta c T F : ℝ) : ℝ :=
  Real.exp eta *
    (2 * capMildGrowthBound eta c T *
      (2 / Real.sqrt (4 * Real.pi))) * F

def rawDQHenryA1 (eta c T F : ℝ) : ℝ :=
  (2 * capMildGrowthBound eta c T * eta +
    Real.exp eta * (2 * capMildGrowthBound eta c T * eta)) * F

def rawDQHenryC0
    (p : CMParams) (M eta c T : ℝ) : ℝ :=
  |p.χ| * (2 * capMildGrowthBound eta c T * eta) *
      Real.sqrt (matchedFluxRawQSquareConstant p M eta) +
    2 * capMildGrowthBound eta c T *
      Real.sqrt (matchedShiftedReactionRawQSquareConstant p M)

def rawDQHenryC1
    (p : CMParams) (M eta c T : ℝ) : ℝ :=
  |p.χ| *
    (2 * capMildGrowthBound eta c T *
      (2 / Real.sqrt (4 * Real.pi))) *
    Real.sqrt (matchedFluxRawQSquareConstant p M eta)

def rawDQHenryD0
    (p : CMParams) (M Brel DU eta c T : ℝ) : ℝ :=
  |p.χ| * (2 * capMildGrowthBound eta c T * eta) *
      Real.sqrt (matchedFluxRawWSquareConstant p M Brel DU eta 1) +
    2 * capMildGrowthBound eta c T *
      Real.sqrt (matchedShiftedReactionRawWSquareConstant p M eta DU)

def rawDQHenryD1
    (p : CMParams) (M Brel DU eta c T : ℝ) : ℝ :=
  |p.χ| *
    (2 * capMildGrowthBound eta c T *
      (2 / Real.sqrt (4 * Real.pi))) *
    Real.sqrt (matchedFluxRawWSquareConstant p M Brel DU eta 1)

theorem rawDQHenryA0_nonneg
    {eta c T F : ℝ} (_heta : 0 ≤ eta) (hF : 0 ≤ F) :
    0 ≤ rawDQHenryA0 eta c T F := by
  simp only [rawDQHenryA0, capMildGrowthBound]
  positivity

theorem rawDQHenryA1_nonneg
    {eta c T F : ℝ} (heta : 0 ≤ eta) (hF : 0 ≤ F) :
    0 ≤ rawDQHenryA1 eta c T F := by
  simp only [rawDQHenryA1, capMildGrowthBound]
  positivity

theorem rawDQHenryC0_nonneg
    (p : CMParams) {M eta c T : ℝ} (heta : 0 ≤ eta) :
    0 ≤ rawDQHenryC0 p M eta c T := by
  simp only [rawDQHenryC0, capMildGrowthBound]
  positivity

theorem rawDQHenryC1_nonneg
    (p : CMParams) {M eta c T : ℝ} (_heta : 0 ≤ eta) :
    0 ≤ rawDQHenryC1 p M eta c T := by
  simp only [rawDQHenryC1, capMildGrowthBound]
  positivity

theorem rawDQHenryD0_nonneg
    (p : CMParams) {M Brel DU eta c T : ℝ} (heta : 0 ≤ eta) :
    0 ≤ rawDQHenryD0 p M Brel DU eta c T := by
  simp only [rawDQHenryD0, capMildGrowthBound]
  positivity

theorem rawDQHenryD1_nonneg
    (p : CMParams) {M Brel DU eta c T : ℝ} (_heta : 0 ≤ eta) :
    0 ≤ rawDQHenryD1 p M Brel DU eta c T := by
  simp only [rawDQHenryD1, capMildGrowthBound]
  positivity

private theorem intervalIntegral_two_affine_sources_eq_henry
    {q K G0 G1 AQ AW L RQ RW F : ℝ} {y : ℝ → ℝ}
    (hq : 0 < q)
    (hy : IntervalIntegrable y volume 0 q)
    (hky : IntervalIntegrable
      (fun τ : ℝ ↦ (q - τ) ^ (-(1 / 2 : ℝ)) * y τ) volume 0 q) :
    K * (∫ τ in (0 : ℝ)..q,
        (G0 + G1 * (q - τ) ^ (-(1 / 2 : ℝ))) *
          (AQ * y τ + AW * F)) +
      ∫ τ in (0 : ℝ)..q, L * (RQ * y τ + RW * F) =
      F * ((K * G0 * AW + L * RW) * q +
        2 * (K * G1 * AW) * Real.sqrt q) +
        ∫ τ in (0 : ℝ)..q,
          ((K * G0 * AQ + L * RQ) +
              (K * G1 * AQ) * (q - τ) ^ (-(1 / 2 : ℝ))) * y τ := by
  let k : ℝ → ℝ := fun τ ↦ (q - τ) ^ (-(1 / 2 : ℝ))
  have hk : IntervalIntegrable k volume 0 q := by
    simpa only [k] using (intervalIntegrable_invSqrt_sub (t := q))
  have h0 : IntervalIntegrable (fun τ : ℝ ↦ (G0 * AQ) * y τ) volume 0 q :=
    hy.const_mul _
  have h1 : IntervalIntegrable (fun τ : ℝ ↦ (G1 * AQ) * (k τ * y τ)) volume 0 q :=
    hky.const_mul _
  have h2 : IntervalIntegrable (fun _ : ℝ ↦ G0 * AW * F) volume 0 q :=
    intervalIntegrable_const
  have h3 : IntervalIntegrable (fun τ : ℝ ↦ (G1 * AW * F) * k τ) volume 0 q :=
    hk.const_mul _
  have hk_mass : (∫ τ in (0 : ℝ)..q, k τ) = 2 * Real.sqrt q := by
    simpa only [k] using intervalIntegral_invSqrt_sub_eq_two_sqrt hq
  have h0_int :
      (∫ τ in (0 : ℝ)..q, (G0 * AQ) * y τ) =
        G0 * AQ * (∫ τ in (0 : ℝ)..q, y τ) := by
    rw [intervalIntegral.integral_const_mul]
  have h1_int :
      (∫ τ in (0 : ℝ)..q, (G1 * AQ) * (k τ * y τ)) =
        G1 * AQ * (∫ τ in (0 : ℝ)..q, k τ * y τ) := by
    rw [intervalIntegral.integral_const_mul]
  have h2_int :
      (∫ _τ in (0 : ℝ)..q, G0 * AW * F) = G0 * AW * F * q := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have h3_int :
      (∫ τ in (0 : ℝ)..q, (G1 * AW * F) * k τ) =
        G1 * AW * F * (2 * Real.sqrt q) := by
    rw [intervalIntegral.integral_const_mul, hk_mass]
  have hflux :
      (∫ τ in (0 : ℝ)..q,
          (G0 + G1 * k τ) * (AQ * y τ + AW * F)) =
        G0 * AQ * (∫ τ in (0 : ℝ)..q, y τ) +
          G1 * AQ * (∫ τ in (0 : ℝ)..q, k τ * y τ) +
          G0 * AW * F * q +
          G1 * AW * F * (2 * Real.sqrt q) := by
    rw [show (fun τ : ℝ ↦
          (G0 + G1 * k τ) * (AQ * y τ + AW * F)) =
        fun τ : ℝ ↦
          (G0 * AQ) * y τ + (G1 * AQ) * (k τ * y τ) +
            (G0 * AW * F) + (G1 * AW * F) * k τ by
      funext τ
      ring]
    rw [intervalIntegral.integral_add ((h0.add h1).add h2) h3,
      intervalIntegral.integral_add (h0.add h1) h2,
      intervalIntegral.integral_add h0 h1,
      h0_int, h1_int, h2_int, h3_int]
  have hr0 : IntervalIntegrable (fun τ : ℝ ↦ (L * RQ) * y τ) volume 0 q :=
    hy.const_mul _
  have hr1 : IntervalIntegrable (fun _ : ℝ ↦ L * RW * F) volume 0 q :=
    intervalIntegrable_const
  have hreact :
      (∫ τ in (0 : ℝ)..q, L * (RQ * y τ + RW * F)) =
        L * RQ * (∫ τ in (0 : ℝ)..q, y τ) + L * RW * F * q := by
    rw [show (fun τ : ℝ ↦ L * (RQ * y τ + RW * F)) =
        fun τ : ℝ ↦ (L * RQ) * y τ + L * RW * F by
      funext τ
      ring]
    rw [intervalIntegral.integral_add hr0 hr1,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const,
      smul_eq_mul]
    ring
  have hc0 : IntervalIntegrable
      (fun τ : ℝ ↦ (K * G0 * AQ + L * RQ) * y τ) volume 0 q :=
    hy.const_mul _
  have hc1 : IntervalIntegrable
      (fun τ : ℝ ↦ (K * G1 * AQ) * (k τ * y τ)) volume 0 q :=
    hky.const_mul _
  have hconv :
      (∫ τ in (0 : ℝ)..q,
          ((K * G0 * AQ + L * RQ) + (K * G1 * AQ) * k τ) * y τ) =
        (K * G0 * AQ + L * RQ) * (∫ τ in (0 : ℝ)..q, y τ) +
          (K * G1 * AQ) * (∫ τ in (0 : ℝ)..q, k τ * y τ) := by
    rw [show (fun τ : ℝ ↦
          ((K * G0 * AQ + L * RQ) + (K * G1 * AQ) * k τ) * y τ) =
        fun τ : ℝ ↦
          (K * G0 * AQ + L * RQ) * y τ +
            (K * G1 * AQ) * (k τ * y τ) by
      funext τ
      ring]
    rw [intervalIntegral.integral_add hc0 hc1,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  simp only [k] at hflux hconv ⊢
  rw [hflux, hreact, hconv]
  ring

/-- Convert the concrete absolute-time PDE majorants on `[a,a+q]` into the
constant-plus-inverse-square-root Henry inequality in restart time.  The
coefficients are independent of the nonzero difference step whenever
`|h| ≤ 1`. -/
theorem rawDQPDE_majorants_le_henry_restart
    (p : CMParams) {M Brel DU eta c T h a q F : ℝ} {x : ℝ → ℝ}
    (hq : 0 < q) (heta : 0 ≤ eta) (hh : |h| ≤ 1) (hF : 0 ≤ F)
    (hx_int : IntervalIntegrable (fun τ : ℝ ↦ x (a + τ)) volume 0 q)
    (hconv_int : IntervalIntegrable
      (fun τ : ℝ ↦ (q - τ) ^ (-(1 / 2 : ℝ)) * x (a + τ)) volume 0 q)
    (hstep :
      x (a + q) ≤ rawDQHomogeneousMajorant eta c T q F +
        |p.χ| * (∫ s in a..a + q,
          rawDQFluxMajorant p M Brel DU eta c T h (x s) F (a + q - s)) +
        ∫ s in a..a + q,
          rawDQReactionMajorant p M DU eta c T (x s) F) :
    x (a + q) ≤
      rawDQHenryA0 eta c T F * q ^ (-(1 / 2 : ℝ)) +
        rawDQHenryA1 eta c T F +
        F * (rawDQHenryD0 p M Brel DU eta c T * q +
          2 * rawDQHenryD1 p M Brel DU eta c T * Real.sqrt q) +
        ∫ τ in (0 : ℝ)..q,
          (rawDQHenryC0 p M eta c T +
              rawDQHenryC1 p M eta c T *
                (q - τ) ^ (-(1 / 2 : ℝ))) * x (a + τ) := by
  let G : ℝ := capMildGrowthBound eta c T
  let G0 : ℝ := 2 * G * eta
  let G1 : ℝ := 2 * G * (2 / Real.sqrt (4 * Real.pi))
  let AQ : ℝ := Real.sqrt (matchedFluxRawQSquareConstant p M eta)
  let AWh : ℝ := Real.sqrt (matchedFluxRawWSquareConstant p M Brel DU eta h)
  let AW : ℝ := Real.sqrt (matchedFluxRawWSquareConstant p M Brel DU eta 1)
  let L : ℝ := 2 * G
  let RQ : ℝ := Real.sqrt (matchedShiftedReactionRawQSquareConstant p M)
  let RW : ℝ :=
    Real.sqrt (matchedShiftedReactionRawWSquareConstant p M eta DU)
  let y : ℝ → ℝ := fun τ ↦ x (a + τ)
  have hG0 : 0 ≤ G0 := by
    dsimp only [G0, G, capMildGrowthBound]
    positivity
  have hG1 : 0 ≤ G1 := by
    dsimp only [G1, G, capMildGrowthBound]
    positivity
  have hAW : AWh ≤ AW := by
    dsimp only [AWh, AW]
    exact Real.sqrt_le_sqrt
      (matchedFluxRawWSquareConstant_le_one p heta hh)
  have hk : IntervalIntegrable
      (fun τ : ℝ ↦ (q - τ) ^ (-(1 / 2 : ℝ))) volume 0 q :=
    intervalIntegrable_invSqrt_sub
  have hfluxInt : ∀ A : ℝ, IntervalIntegrable
      (fun τ : ℝ ↦
        (G0 + G1 * (q - τ) ^ (-(1 / 2 : ℝ))) *
          (AQ * y τ + A * F)) volume 0 q := by
    intro A
    have h0 : IntervalIntegrable (fun τ : ℝ ↦ (G0 * AQ) * y τ) volume 0 q :=
      hx_int.const_mul _
    have h1 : IntervalIntegrable
        (fun τ : ℝ ↦ (G1 * AQ) *
          ((q - τ) ^ (-(1 / 2 : ℝ)) * y τ)) volume 0 q :=
      hconv_int.const_mul _
    have h2 : IntervalIntegrable (fun _ : ℝ ↦ G0 * A * F) volume 0 q :=
      intervalIntegrable_const
    have h3 : IntervalIntegrable
        (fun τ : ℝ ↦ (G1 * A * F) *
          (q - τ) ^ (-(1 / 2 : ℝ))) volume 0 q :=
      hk.const_mul _
    rw [show (fun τ : ℝ ↦
          (G0 + G1 * (q - τ) ^ (-(1 / 2 : ℝ))) *
            (AQ * y τ + A * F)) =
        fun τ : ℝ ↦
          (G0 * AQ) * y τ +
            (G1 * AQ) * ((q - τ) ^ (-(1 / 2 : ℝ)) * y τ) +
            G0 * A * F +
            (G1 * A * F) * (q - τ) ^ (-(1 / 2 : ℝ)) by
      funext τ
      ring]
    exact ((h0.add h1).add h2).add h3
  have hflux_le :
      (∫ τ in (0 : ℝ)..q,
          (G0 + G1 * (q - τ) ^ (-(1 / 2 : ℝ))) *
            (AQ * y τ + AWh * F)) ≤
        ∫ τ in (0 : ℝ)..q,
          (G0 + G1 * (q - τ) ^ (-(1 / 2 : ℝ))) *
            (AQ * y τ + AW * F) := by
    apply intervalIntegral.integral_mono_on hq.le (hfluxInt AWh) (hfluxInt AW)
    intro τ hτ
    have hk0 : 0 ≤ (q - τ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_nonneg (sub_nonneg.mpr hτ.2) _
    have hinner : AQ * y τ + AWh * F ≤ AQ * y τ + AW * F := by
      nlinarith [mul_le_mul_of_nonneg_right hAW hF]
    exact mul_le_mul_of_nonneg_left
      hinner (add_nonneg hG0 (mul_nonneg hG1 hk0))
  have hshiftFlux :
      (∫ s in a..a + q,
          rawDQFluxMajorant p M Brel DU eta c T h (x s) F (a + q - s)) =
        ∫ τ in (0 : ℝ)..q,
          (G0 + G1 * (q - τ) ^ (-(1 / 2 : ℝ))) *
            (AQ * y τ + AWh * F) := by
    rw [intervalIntegral_restart_eq]
    apply intervalIntegral.integral_congr
    intro τ _
    dsimp only [rawDQFluxMajorant, G0, G1, G, AQ, AWh, y]
    congr 3
    ring
  have hshiftReact :
      (∫ s in a..a + q,
          rawDQReactionMajorant p M DU eta c T (x s) F) =
        ∫ τ in (0 : ℝ)..q, L * (RQ * y τ + RW * F) := by
    rw [intervalIntegral_restart_eq]
    apply intervalIntegral.integral_congr
    intro τ _
    rfl
  have hsource :
      |p.χ| * (∫ s in a..a + q,
          rawDQFluxMajorant p M Brel DU eta c T h (x s) F (a + q - s)) +
        ∫ s in a..a + q,
          rawDQReactionMajorant p M DU eta c T (x s) F ≤
        F * (rawDQHenryD0 p M Brel DU eta c T * q +
          2 * rawDQHenryD1 p M Brel DU eta c T * Real.sqrt q) +
        ∫ τ in (0 : ℝ)..q,
          (rawDQHenryC0 p M eta c T +
              rawDQHenryC1 p M eta c T *
                (q - τ) ^ (-(1 / 2 : ℝ))) * x (a + τ) := by
    rw [hshiftFlux, hshiftReact]
    calc
      |p.χ| * (∫ τ in (0 : ℝ)..q,
          (G0 + G1 * (q - τ) ^ (-(1 / 2 : ℝ))) *
            (AQ * y τ + AWh * F)) +
          ∫ τ in (0 : ℝ)..q, L * (RQ * y τ + RW * F) ≤
        |p.χ| * (∫ τ in (0 : ℝ)..q,
          (G0 + G1 * (q - τ) ^ (-(1 / 2 : ℝ))) *
            (AQ * y τ + AW * F)) +
          ∫ τ in (0 : ℝ)..q, L * (RQ * y τ + RW * F) := by
            gcongr
      _ = F * (rawDQHenryD0 p M Brel DU eta c T * q +
            2 * rawDQHenryD1 p M Brel DU eta c T * Real.sqrt q) +
          ∫ τ in (0 : ℝ)..q,
            (rawDQHenryC0 p M eta c T +
                rawDQHenryC1 p M eta c T *
                  (q - τ) ^ (-(1 / 2 : ℝ))) * x (a + τ) := by
        simpa only [rawDQHenryC0, rawDQHenryC1, rawDQHenryD0,
          rawDQHenryD1, G0, G1, G, AQ, AW, L, RQ, RW, y] using
          intervalIntegral_two_affine_sources_eq_henry
            (q := q) (K := |p.χ|) (G0 := G0) (G1 := G1)
            (AQ := AQ) (AW := AW) (L := L) (RQ := RQ) (RW := RW)
            (F := F) (y := y) hq hx_int hconv_int
  have hhom :
      rawDQHomogeneousMajorant eta c T q F =
        rawDQHenryA0 eta c T F * q ^ (-(1 / 2 : ℝ)) +
          rawDQHenryA1 eta c T F := by
    simp only [rawDQHomogeneousMajorant, rawDQHenryA0, rawDQHenryA1]
    ring
  rw [hhom] at hstep
  linarith

end ShenWork.Paper1

#print axioms ShenWork.Paper1.rawDQHenryA0_nonneg
#print axioms ShenWork.Paper1.rawDQHenryA1_nonneg
#print axioms ShenWork.Paper1.rawDQHenryC0_nonneg
#print axioms ShenWork.Paper1.rawDQHenryC1_nonneg
#print axioms ShenWork.Paper1.rawDQHenryD0_nonneg
#print axioms ShenWork.Paper1.rawDQHenryD1_nonneg
#print axioms ShenWork.Paper1.rawDQPDE_majorants_le_henry_restart
