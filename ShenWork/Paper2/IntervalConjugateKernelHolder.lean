/-
  ShenWork/Paper2/IntervalConjugateKernelHolder.lean

  Spatial Holder smoothing for the interval conjugate-kernel operator

    B_N(t) Q (x) = - integral_0^1 partial_y K_N(t,x,y) Q(y) dy.

  The new kernel input is the mixed derivative bound

    integral_0^1 |partial_x partial_y K_N(t,x,y)| dy
      <= (5 sqrt(2) / 2) t^{-1}.

  It follows from the same whole-line Hessian lattice majorant and cell tiling
  already used for the pure second derivative.  Interpolating this derivative
  bound with the committed t^{-1/2} value bound gives the integrable
  t^{-(1+theta)/2} Holder smoothing estimate for 0 < theta < 1.
-/
import ShenWork.PDE.IntervalFullKernelSecondDerivLinfty
import ShenWork.Paper2.IntervalConjugateDuhamelMap
import ShenWork.Paper2.ChemMildHolder

open MeasureTheory
open scoped Topology

noncomputable section

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain

/-! ## The mixed full-kernel derivative -/

/-- Differentiating the second-variable kernel derivative in the first variable.
The direct image has a minus sign and the reflected image a plus sign. -/
theorem hasDerivAt_deriv_intervalNeumannFullKernel_snd_fst
    {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt
      (fun x : ℝ => deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y)
      (-(∑' k : ℤ,
          deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u)
            (x - y + 2 * (k : ℝ)))
        + (∑' k : ℤ,
          deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u)
            (x + y + 2 * (k : ℝ)))) x := by
  have hfun :
      (fun x : ℝ => deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y)
        = fun w : ℝ =>
            -(∑' k : ℤ,
              deriv (fun u : ℝ => heatKernel t u) (w - y + 2 * (k : ℝ)))
            + (∑' k : ℤ,
              deriv (fun u : ℝ => heatKernel t u) (w + y + 2 * (k : ℝ))) := by
    funext w
    exact (hasDerivAt_intervalNeumannFullKernel_snd ht w y).deriv
  rw [hfun]
  have hL : HasDerivAt
      (fun w : ℝ => ∑' k : ℤ,
        deriv (fun u : ℝ => heatKernel t u) (w - y + 2 * (k : ℝ)))
      (∑' k : ℤ,
        deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
          (x - y + 2 * (k : ℝ))) x := by
    simpa only [sub_eq_add_neg] using
      hasDerivAt_deriv_heatKernel_lattice_tsum ht (-y) x
  have hR : HasDerivAt
      (fun w : ℝ => ∑' k : ℤ,
        deriv (fun u : ℝ => heatKernel t u) (w + y + 2 * (k : ℝ)))
      (∑' k : ℤ,
        deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
          (x + y + 2 * (k : ℝ))) x :=
    hasDerivAt_deriv_heatKernel_lattice_tsum ht y x
  exact hL.neg.add hR

/-- The nonnegative lattice majorant shared by the pure and mixed second
derivatives of the interval kernel. -/
def intervalHeatHessLatticeMajorant (t x y : ℝ) : ℝ :=
  ∑' k : ℤ,
    (|deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
        (x - y + 2 * (k : ℝ))|
      + |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
        (x + y + 2 * (k : ℝ))|)

/-- Pointwise domination of the mixed kernel derivative by the Hessian lattice
majorant. -/
theorem abs_mixedDeriv_intervalNeumannFullKernel_le
    {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    |deriv (fun x : ℝ =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y) x|
      ≤ intervalHeatHessLatticeMajorant t x y := by
  rw [(hasDerivAt_deriv_intervalNeumannFullKernel_snd_fst ht x y).deriv]
  have hsumA : Summable
      (fun k : ℤ =>
        |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
          (x - y + 2 * (k : ℝ))|) :=
    summable_abs_iff.mpr (latticeGaussianHessSummable ht (x - y))
  have hsumB : Summable
      (fun k : ℤ =>
        |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
          (x + y + 2 * (k : ℝ))|) :=
    summable_abs_iff.mpr (latticeGaussianHessSummable ht (x + y))
  have hA :
      |∑' k : ℤ,
          deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
            (x - y + 2 * (k : ℝ))|
        ≤ ∑' k : ℤ,
          |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
            (x - y + 2 * (k : ℝ))| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm
        (f := fun k : ℤ =>
          deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
            (x - y + 2 * (k : ℝ)))
        (by simpa [Real.norm_eq_abs] using hsumA)
  have hB :
      |∑' k : ℤ,
          deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
            (x + y + 2 * (k : ℝ))|
        ≤ ∑' k : ℤ,
          |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
            (x + y + 2 * (k : ℝ))| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm
        (f := fun k : ℤ =>
          deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
            (x + y + 2 * (k : ℝ)))
        (by simpa [Real.norm_eq_abs] using hsumB)
  unfold intervalHeatHessLatticeMajorant
  calc
    |-(∑' k : ℤ,
          deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
            (x - y + 2 * (k : ℝ)))
        + (∑' k : ℤ,
          deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
            (x + y + 2 * (k : ℝ)))|
        ≤ |∑' k : ℤ,
            deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
              (x - y + 2 * (k : ℝ))|
          + |∑' k : ℤ,
            deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
              (x + y + 2 * (k : ℝ))| := by
            simpa only [abs_neg] using
              abs_add_le
                (-(∑' k : ℤ,
                  deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
                    (x - y + 2 * (k : ℝ))))
                (∑' k : ℤ,
                  deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
                    (x + y + 2 * (k : ℝ)))
    _ ≤ (∑' k : ℤ,
            |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
              (x - y + 2 * (k : ℝ))|)
          + (∑' k : ℤ,
            |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
              (x + y + 2 * (k : ℝ))|) := add_le_add hA hB
    _ = ∑' k : ℤ,
        (|deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
            (x - y + 2 * (k : ℝ))|
          + |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
            (x + y + 2 * (k : ℝ))|) :=
      (Summable.tsum_add hsumA hsumB).symm

/-- Continuity of the Hessian lattice majorant on the integration interval. -/
theorem continuousOn_intervalHeatHessLatticeMajorant
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ContinuousOn (intervalHeatHessLatticeMajorant t x) (Set.Icc 0 1) := by
  have hcd := continuous_secondDeriv_heatKernel ht
  have hAcont : ∀ k : ℤ, Continuous (fun y : ℝ =>
      |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
        (x - y + 2 * (k : ℝ))|) :=
    fun k => (hcd.comp (by fun_prop)).abs
  have hBcont : ∀ k : ℤ, Continuous (fun y : ℝ =>
      |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
        (x + y + 2 * (k : ℝ))|) :=
    fun k => (hcd.comp (by fun_prop)).abs
  have hu : Summable (fun k : ℤ =>
      heatHessWindowBound t x 1 k + heatHessWindowBound t x 1 k) :=
    (summable_heatHessWindowBound ht x 1).add
      (summable_heatHessWindowBound ht x 1)
  unfold intervalHeatHessLatticeMajorant
  refine continuousOn_tsum
    (fun k => ((hAcont k).add (hBcont k)).continuousOn) hu (fun k y hy => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
          (x - y + 2 * (k : ℝ))|
      + |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
          (x + y + 2 * (k : ℝ))|)]
  have hyabs : |y| ≤ (1 : ℝ) :=
    abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hA := abs_secondDeriv_heatKernel_le_windowShift ht x 1 k
    (w := x - y + 2 * (k : ℝ)) (by
      rw [show x - y + 2 * (k : ℝ) - (x + 2 * (k : ℝ)) = -y by ring, abs_neg]
      exact hyabs)
  have hB := abs_secondDeriv_heatKernel_le_windowShift ht x 1 k
    (w := x + y + 2 * (k : ℝ)) (by
      rw [show x + y + 2 * (k : ℝ) - (x + 2 * (k : ℝ)) = y by ring]
      exact hyabs)
  exact add_le_add hA hB

/-- The Hessian lattice majorant is interval-integrable. -/
theorem intervalIntegrable_intervalHeatHessLatticeMajorant
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    IntervalIntegrable (intervalHeatHessLatticeMajorant t x)
      MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact continuousOn_intervalHeatHessLatticeMajorant ht x

/-- Cell tiling identifies the integral of the Hessian lattice majorant with
the whole-line L1 mass of the heat-kernel Hessian. -/
theorem intervalHeatHessLatticeMajorant_interval_integral_eq
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ y in (0 : ℝ)..1, intervalHeatHessLatticeMajorant t x y)
      = ∫ w : ℝ,
          |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w| := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hcd := continuous_secondDeriv_heatKernel ht
  have hAcont : ∀ k : ℤ, Continuous (fun y : ℝ =>
      |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
        (x - y + 2 * (k : ℝ))|) :=
    fun k => (hcd.comp (by fun_prop)).abs
  have hBcont : ∀ k : ℤ, Continuous (fun y : ℝ =>
      |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
        (x + y + 2 * (k : ℝ))|) :=
    fun k => (hcd.comp (by fun_prop)).abs
  have hAii : ∀ k : ℤ, IntervalIntegrable (fun y : ℝ =>
      |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
        (x - y + 2 * (k : ℝ))|) MeasureTheory.volume 0 1 :=
    fun k => (hAcont k).intervalIntegrable 0 1
  have hBii : ∀ k : ℤ, IntervalIntegrable (fun y : ℝ =>
      |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
        (x + y + 2 * (k : ℝ))|) MeasureTheory.volume 0 1 :=
    fun k => (hBcont k).intervalIntegrable 0 1
  set hk : ℤ → ℝ → ℝ := fun k y =>
    |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
      (x - y + 2 * (k : ℝ))|
      + |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
        (x + y + 2 * (k : ℝ))| with hk_def
  have hk_nonneg : ∀ k y, 0 ≤ hk k y := fun k y => by rw [hk_def]; positivity
  have hμint : ∀ k : ℤ,
      Integrable (hk k) (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro k
    rw [hk_def]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mp
      ((hAii k).add (hBii k))
  have heq : ∀ k : ℤ,
      (∫ y, ‖hk k y‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)))
        = (∫ y in (0 : ℝ)..1,
            |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
              (x - y + 2 * (k : ℝ))|)
          + (∫ y in (0 : ℝ)..1,
            |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
              (x + y + 2 * (k : ℝ))|) := by
    intro k
    have e1 :
        (∫ y, ‖hk k y‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)))
          = ∫ y in (0 : ℝ)..1, hk k y := by
      rw [intervalIntegral.integral_of_le h01]
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun y => Real.norm_of_nonneg (hk_nonneg k y))
    rw [e1]
    exact intervalIntegral.integral_add (hAii k) (hBii k)
  have hμsum : Summable
      (fun k : ℤ =>
        ∫ y, ‖hk k y‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    (summable_cell_heatHess_interval_integral ht x).congr
      (fun k => (heq k).symm)
  have key := integral_tsum_of_summable_integral_norm
    (μ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))
    (F := hk) hμint hμsum
  calc
    (∫ y in (0 : ℝ)..1, intervalHeatHessLatticeMajorant t x y)
        = ∫ y, (∑' k : ℤ, hk k y)
            ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
          rw [intervalIntegral.integral_of_le h01]
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun y => by
            rw [hk_def, intervalHeatHessLatticeMajorant]
    _ = ∑' k : ℤ,
          ∫ y, hk k y
            ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := key.symm
    _ = ∑' k : ℤ,
          ((∫ y in (0 : ℝ)..1,
              |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
                (x - y + 2 * (k : ℝ))|)
            + (∫ y in (0 : ℝ)..1,
              |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
                (x + y + 2 * (k : ℝ))|)) := by
          refine tsum_congr (fun k => ?_)
          rw [← intervalIntegral.integral_of_le h01]
          rw [hk_def]
          exact intervalIntegral.integral_add (hAii k) (hBii k)
    _ = ∫ w : ℝ,
          |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w| :=
      ShenWork.tsum_cell_integral_eq_integral
        (secondDeriv_heatKernel_abs_integrable ht) x

/-- Continuity of the mixed kernel derivative on the integration interval. -/
theorem continuousOn_mixedDeriv_intervalNeumannFullKernel
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ContinuousOn
      (fun y : ℝ => deriv (fun x : ℝ =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y) x)
      (Set.Icc 0 1) := by
  have hcd := continuous_secondDeriv_heatKernel ht
  have hfun :
      (fun y : ℝ => deriv (fun x : ℝ =>
          deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y) x)
        = fun y : ℝ =>
            -(∑' k : ℤ,
              deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
                (x - y + 2 * (k : ℝ)))
            + (∑' k : ℤ,
              deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
                (x + y + 2 * (k : ℝ))) := by
    funext y
    exact (hasDerivAt_deriv_intervalNeumannFullKernel_snd_fst ht x y).deriv
  rw [hfun]
  have hu : Summable (fun k : ℤ => heatHessWindowBound t x 1 k) :=
    summable_heatHessWindowBound ht x 1
  have hbnd : ∀ (s : ℝ), |s| ≤ (1 : ℝ) → ∀ k : ℤ,
      ‖deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
          (x + s + 2 * (k : ℝ))‖ ≤ heatHessWindowBound t x 1 k := by
    intro s hs k
    rw [Real.norm_eq_abs]
    exact abs_secondDeriv_heatKernel_le_windowShift ht x 1 k (by
      rw [show x + s + 2 * (k : ℝ) - (x + 2 * (k : ℝ)) = s by ring]
      exact hs)
  refine ContinuousOn.add ?_ ?_
  · refine (continuousOn_tsum
      (fun k => (hcd.comp (by fun_prop)).continuousOn) hu
      (fun k y hy => ?_)).neg
    change ‖deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
      (x - y + 2 * (k : ℝ))‖ ≤ heatHessWindowBound t x 1 k
    rw [show x - y + 2 * (k : ℝ) = x + (-y) + 2 * (k : ℝ) by ring]
    exact hbnd (-y)
      (by rw [abs_neg]; exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩) k
  · refine continuousOn_tsum
      (fun k => (hcd.comp (by fun_prop)).continuousOn) hu
      (fun k y hy => ?_)
    change ‖deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
      (x + y + 2 * (k : ℝ))‖ ≤ heatHessWindowBound t x 1 k
    exact hbnd y
      (abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩) k

/-- The mixed kernel derivative is interval-integrable. -/
theorem intervalIntegrable_mixedDeriv_intervalNeumannFullKernel
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    IntervalIntegrable
      (fun y : ℝ => deriv (fun x : ℝ =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y) x)
      MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact continuousOn_mixedDeriv_intervalNeumannFullKernel ht x

/-- The mixed derivative has the same `t^{-1}` L1 bound as the pure second
derivative. -/
theorem intervalNeumannFullKernel_mixedDeriv_abs_interval_integral_le
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ y in (0 : ℝ)..1,
      |deriv (fun x : ℝ =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y) x|)
      ≤ (5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ)) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hmono :
      (∫ y in (0 : ℝ)..1,
        |deriv (fun x : ℝ =>
          deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y) x|)
        ≤ ∫ y in (0 : ℝ)..1, intervalHeatHessLatticeMajorant t x y := by
    refine intervalIntegral.integral_mono_on h01
      (intervalIntegrable_mixedDeriv_intervalNeumannFullKernel ht x).abs
      (intervalIntegrable_intervalHeatHessLatticeMajorant ht x)
      (fun y _ => abs_mixedDeriv_intervalNeumannFullKernel_le ht x y)
  rw [intervalHeatHessLatticeMajorant_interval_integral_eq ht x] at hmono
  exact hmono.trans (secondDeriv_heatKernel_abs_integral_le ht)

/-- Uniform mixed-derivative bound on `ball(x,1) x [0,1]`, used for
differentiation under the integral. -/
theorem abs_mixedDeriv_intervalNeumannFullKernel_le_const
    {t : ℝ} (ht : 0 < t) (x : ℝ)
    {z y : ℝ} (hz : |z - x| ≤ 1) (hy : |y| ≤ 1) :
    |deriv (fun z : ℝ =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel t z y') y) z|
      ≤ ∑' k : ℤ,
        (heatHessWindowBound t x 2 k + heatHessWindowBound t x 2 k) := by
  refine (abs_mixedDeriv_intervalNeumannFullKernel_le ht z y).trans ?_
  unfold intervalHeatHessLatticeMajorant
  refine Summable.tsum_le_tsum (fun k => ?_)
    ((summable_abs_iff.mpr (latticeGaussianHessSummable ht (z - y))).add
      (summable_abs_iff.mpr (latticeGaussianHessSummable ht (z + y))))
    ((summable_heatHessWindowBound ht x 2).add
      (summable_heatHessWindowBound ht x 2))
  have hzb := abs_le.mp hz
  have hyb := abs_le.mp hy
  have hA := abs_secondDeriv_heatKernel_le_windowShift ht x 2 k
    (w := z - y + 2 * (k : ℝ)) (by
      rw [show z - y + 2 * (k : ℝ) - (x + 2 * (k : ℝ)) = z - x - y by ring]
      exact abs_le.mpr
        ⟨by linarith [hzb.1, hyb.2], by linarith [hzb.2, hyb.1]⟩)
  have hB := abs_secondDeriv_heatKernel_le_windowShift ht x 2 k
    (w := z + y + 2 * (k : ℝ)) (by
      rw [show z + y + 2 * (k : ℝ) - (x + 2 * (k : ℝ)) = z - x + y by ring]
      exact abs_le.mpr
        ⟨by linarith [hzb.1, hyb.1], by linarith [hzb.2, hyb.2]⟩)
  exact add_le_add hA hB

end ShenWork.IntervalNeumannFullKernel

namespace ShenWork.IntervalConjugateDuhamelMap

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)

/-! ## Differentiation and the mixed-derivative `L∞` bound -/

/-- Differentiate the conjugate-kernel operator under the integral. -/
theorem intervalConjugateKernelOperator_hasDerivAt
    {t : ℝ} (ht : 0 < t) {Q : ℝ → ℝ}
    (hQ_int : Integrable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ : ∀ y, |Q y| ≤ CQ) (x : ℝ) :
    HasDerivAt (fun z : ℝ => intervalConjugateKernelOperator t Q z)
      (-(∫ y,
        deriv (fun z : ℝ =>
          deriv (fun y' : ℝ => intervalNeumannFullKernel t z y') y) x * Q y
          ∂(intervalMeasure 1))) x := by
  haveI : IsFiniteMeasure (intervalMeasure 1) :=
    ⟨intervalMeasure_univ_lt_top 1⟩
  have hbdd : ∀ᵐ y ∂(intervalMeasure 1), ‖Q y‖ ≤ CQ :=
    Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hQ y
  set M : ℝ := ∑' k : ℤ,
    (heatHessWindowBound t x 2 k + heatHessWindowBound t x 2 k) with hM
  have hMnn : 0 ≤ M := by
    rw [hM]
    exact tsum_nonneg fun k => by
      unfold heatHessWindowBound heatHessPointwiseBound
      positivity
  unfold intervalConjugateKernelOperator
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := x)
    (bound := fun _ => M * CQ)
    (F := fun z y =>
      deriv (fun y' : ℝ => intervalNeumannFullKernel t z y') y * Q y)
    (F' := fun z y =>
      deriv (fun z' : ℝ =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel t z' y') y) z * Q y)
    (Metric.ball_mem_nhds x one_pos)
    ?hFmeas ?hFint ?hF'meas ?hbound ?hbdint ?hdiff).2.neg
  case hFmeas =>
    exact Filter.Eventually.of_forall fun z =>
      ((continuousOn_deriv_intervalNeumannFullKernel_snd ht z).aestronglyMeasurable
        measurableSet_Icc).mul hQ_int.aestronglyMeasurable
  case hFint =>
    exact ((continuousOn_deriv_intervalNeumannFullKernel_snd ht x).integrableOn_Icc).mul_bdd
      hQ_int.aestronglyMeasurable hbdd
  case hF'meas =>
    exact ((continuousOn_mixedDeriv_intervalNeumannFullKernel ht x).aestronglyMeasurable
      measurableSet_Icc).mul hQ_int.aestronglyMeasurable
  case hbound =>
    simp only [intervalMeasure, intervalSet]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun y hy z hz => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have hz1 : |z - x| ≤ 1 := by
      rw [← Real.dist_eq]
      exact le_of_lt (Metric.mem_ball.mp hz)
    have hy1 : |y| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    exact mul_le_mul
      (abs_mixedDeriv_intervalNeumannFullKernel_le_const ht x hz1 hy1)
      (hQ y) (abs_nonneg _) hMnn
  case hbdint => exact integrable_const _
  case hdiff =>
    refine Filter.Eventually.of_forall fun y z _ => ?_
    show HasDerivAt
      (fun z' : ℝ =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel t z' y') y * Q y)
      (deriv (fun z' : ℝ =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel t z' y') y) z * Q y) z
    rw [(hasDerivAt_deriv_intervalNeumannFullKernel_snd_fst ht z y).deriv]
    exact (hasDerivAt_deriv_intervalNeumannFullKernel_snd_fst ht z y).mul_const (Q y)

/-- Pointwise `t^{-1}` derivative bound for the conjugate-kernel operator. -/
theorem intervalConjugateKernelOperator_deriv_abs_le
    {t : ℝ} (ht : 0 < t) {Q : ℝ → ℝ}
    (hQ_int : Integrable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ : ∀ y, |Q y| ≤ CQ) (x : ℝ) :
    |deriv (fun z : ℝ => intervalConjugateKernelOperator t Q z) x|
      ≤ (5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ)) * CQ := by
  have hCQ : 0 ≤ CQ := le_trans (abs_nonneg (Q 0)) (hQ 0)
  have hKint : Integrable
      (fun y : ℝ => deriv (fun z : ℝ =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel t z y') y) x)
      (intervalMeasure 1) := by
    simp only [intervalMeasure, intervalSet]
    exact (continuousOn_mixedDeriv_intervalNeumannFullKernel ht x).integrableOn_Icc
  have hbdd : ∀ᵐ y ∂(intervalMeasure 1), ‖Q y‖ ≤ CQ :=
    Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hQ y
  have hprod_int : Integrable
      (fun y : ℝ => deriv (fun z : ℝ =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel t z y') y) x * Q y)
      (intervalMeasure 1) :=
    hKint.mul_bdd hQ_int.aestronglyMeasurable hbdd
  have hint_le :
      (∫ y, |deriv (fun z : ℝ =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel t z y') y) x|
          ∂(intervalMeasure 1))
        ≤ (5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ)) := by
    have hcv :
        (∫ y, |deriv (fun z : ℝ =>
          deriv (fun y' : ℝ => intervalNeumannFullKernel t z y') y) x|
            ∂(intervalMeasure 1))
          = ∫ y in (0 : ℝ)..1,
              |deriv (fun z : ℝ =>
                deriv (fun y' : ℝ => intervalNeumannFullKernel t z y') y) x| := by
      simp only [intervalMeasure, intervalSet]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [hcv]
    exact intervalNeumannFullKernel_mixedDeriv_abs_interval_integral_le ht x
  rw [(intervalConjugateKernelOperator_hasDerivAt ht hQ_int hQ x).deriv, abs_neg]
  calc
    |∫ y, deriv (fun z : ℝ =>
          deriv (fun y' : ℝ => intervalNeumannFullKernel t z y') y) x * Q y
        ∂(intervalMeasure 1)|
        ≤ ∫ y, ‖deriv (fun z : ℝ =>
            deriv (fun y' : ℝ => intervalNeumannFullKernel t z y') y) x * Q y‖
          ∂(intervalMeasure 1) := by
            rw [← Real.norm_eq_abs]
            exact norm_integral_le_integral_norm _
    _ ≤ ∫ y, |deriv (fun z : ℝ =>
          deriv (fun y' : ℝ => intervalNeumannFullKernel t z y') y) x| * CQ
          ∂(intervalMeasure 1) := by
            refine MeasureTheory.integral_mono hprod_int.norm
              (hKint.abs.mul_const CQ) (fun y => ?_)
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul_of_nonneg_left (hQ y) (abs_nonneg _)
    _ = (∫ y, |deriv (fun z : ℝ =>
          deriv (fun y' : ℝ => intervalNeumannFullKernel t z y') y) x|
          ∂(intervalMeasure 1)) * CQ := by
            rw [MeasureTheory.integral_mul_const]
    _ ≤ ((5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ))) * CQ :=
      mul_le_mul_of_nonneg_right hint_le hCQ
    _ = (5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ)) * CQ := by ring

/-! ## `L∞` to spatial Holder smoothing -/

/-- The mixed-derivative estimate makes the conjugate-kernel output globally
Lipschitz in its spatial variable. -/
theorem intervalConjugateKernelOperator_lipschitz
    {t : ℝ} (ht : 0 < t) {Q : ℝ → ℝ}
    (hQ_int : Integrable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ : ∀ y, |Q y| ≤ CQ) (x y : ℝ) :
    |intervalConjugateKernelOperator t Q x
        - intervalConjugateKernelOperator t Q y|
      ≤ (5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ)) * CQ * |x - y| := by
  set g : ℝ → ℝ := fun z => intervalConjugateKernelOperator t Q z with hg
  set C : ℝ := (5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ)) * CQ with hC
  have hderiv : ∀ z ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt g (deriv g z) Set.univ z := by
    intro z _
    have hz := intervalConjugateKernelOperator_hasDerivAt ht hQ_int hQ z
    exact (hz.differentiableAt.hasDerivAt).hasDerivWithinAt
  have hbound : ∀ z ∈ (Set.univ : Set ℝ), ‖deriv g z‖ ≤ C := by
    intro z _
    rw [Real.norm_eq_abs, hg, hC]
    exact intervalConjugateKernelOperator_deriv_abs_le ht hQ_int hQ z
  have hmvt :=
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound (Set.mem_univ y) (Set.mem_univ x)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  simpa [hg, hC] using hmvt

/-- Interpolating the `t^{-1/2}` value bound with the `t^{-1}` derivative bound
gives the conjugate-kernel `L∞ -> C^theta` estimate. -/
theorem intervalConjugateKernelOperator_Linf_to_Ctheta
    {t θ : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {Q : ℝ → ℝ} (hQ_int : Integrable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ : ∀ y, |Q y| ≤ CQ) (x y : ℝ) :
    |intervalConjugateKernelOperator t Q x
        - intervalConjugateKernelOperator t Q y|
      ≤ (2 : ℝ) ^ (1 - θ)
          * ((5 * Real.sqrt 2 / 2) ^ θ
            * heatGradientLinftyLinftyConstant ^ (1 - θ))
          * t ^ (-((1 + θ) / 2) : ℝ) * CQ * |x - y| ^ θ := by
  have hCQ : 0 ≤ CQ := le_trans (abs_nonneg (Q 0)) (hQ 0)
  have hCg : 0 ≤ heatGradientLinftyLinftyConstant :=
    heatGradientLinftyLinftyConstant_nonneg
  have hCgg : 0 ≤ (5 * Real.sqrt 2 / 2 : ℝ) := by positivity
  set A : ℝ := heatGradientLinftyLinftyConstant
    * t ^ (-(1 / 2) : ℝ) * CQ with hA
  have hAnn : 0 ≤ A := by
    rw [hA]
    have := Real.rpow_pos_of_pos ht (-(1 / 2) : ℝ)
    positivity
  have hxval : |intervalConjugateKernelOperator t Q x| ≤ A := by
    rw [hA]
    exact intervalConjugateKernelOperator_abs_le ht hQ_int hQ x
  have hyval : |intervalConjugateKernelOperator t Q y| ≤ A := by
    rw [hA]
    exact intervalConjugateKernelOperator_abs_le ht hQ_int hQ y
  have hval :
      |intervalConjugateKernelOperator t Q x
          - intervalConjugateKernelOperator t Q y| ≤ 2 * A := by
    calc
      |intervalConjugateKernelOperator t Q x
          - intervalConjugateKernelOperator t Q y|
          ≤ |intervalConjugateKernelOperator t Q x|
            + |intervalConjugateKernelOperator t Q y| := abs_sub _ _
      _ ≤ A + A := add_le_add hxval hyval
      _ = 2 * A := by ring
  set B : ℝ := (5 * Real.sqrt 2 / 2)
    * t ^ (-(1 : ℝ)) * CQ with hB
  have htm1 : (0 : ℝ) < t ^ (-(1 : ℝ)) :=
    Real.rpow_pos_of_pos ht _
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have hlip :
      |intervalConjugateKernelOperator t Q x
          - intervalConjugateKernelOperator t Q y| ≤ B * |x - y| := by
    rw [hB]
    exact intervalConjugateKernelOperator_lipschitz ht hQ_int hQ x y
  set a : ℝ := 2 * A with ha
  set b : ℝ := B * |x - y| with hb
  have hann : 0 ≤ a := by rw [ha]; positivity
  have hbnn : 0 ≤ b := by rw [hb]; positivity
  have hmin :
      |intervalConjugateKernelOperator t Q x
          - intervalConjugateKernelOperator t Q y| ≤ min a b :=
    le_min hval hlip
  have hinterp : min a b ≤ a ^ (1 - θ) * b ^ θ :=
    ShenWork.Paper2.min_le_rpow_interp hann hbnn hθ0.le hθ1.le
  have hchain :
      |intervalConjugateKernelOperator t Q x
          - intervalConjugateKernelOperator t Q y|
        ≤ a ^ (1 - θ) * b ^ θ := hmin.trans hinterp
  have hapow :
      a ^ (1 - θ) = (2 : ℝ) ^ (1 - θ)
        * (heatGradientLinftyLinftyConstant ^ (1 - θ)
          * t ^ (-(1 - θ) / 2 : ℝ) * CQ ^ (1 - θ)) := by
    have htA : (t ^ (-(1 / 2) : ℝ)) ^ (1 - θ)
        = t ^ (-(1 - θ) / 2 : ℝ) := by
      rw [← Real.rpow_mul ht.le]
      congr 1
      ring
    rw [ha, hA, Real.mul_rpow (by norm_num) hAnn,
      Real.mul_rpow (by positivity) hCQ,
      Real.mul_rpow hCg (Real.rpow_pos_of_pos ht _).le, htA]
  have hbpow :
      b ^ θ = (5 * Real.sqrt 2 / 2) ^ θ * t ^ (-(θ : ℝ))
        * CQ ^ θ * |x - y| ^ θ := by
    have htB : (t ^ (-(1 : ℝ))) ^ θ = t ^ (-(θ : ℝ)) := by
      rw [← Real.rpow_mul ht.le]
      congr 1
      ring
    rw [hb, hB, Real.mul_rpow hBnn (abs_nonneg _),
      Real.mul_rpow (by positivity) hCQ,
      Real.mul_rpow hCgg htm1.le, htB]
  have hexp :
      t ^ (-(1 - θ) / 2 : ℝ) * t ^ (-(θ : ℝ))
        = t ^ (-((1 + θ) / 2) : ℝ) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have hCQcollapse : CQ ^ (1 - θ) * CQ ^ θ = CQ := by
    rw [← Real.rpow_add' hCQ (by simp)]
    simp
  have hfinal :
      a ^ (1 - θ) * b ^ θ
        = (2 : ℝ) ^ (1 - θ)
            * ((5 * Real.sqrt 2 / 2) ^ θ
              * heatGradientLinftyLinftyConstant ^ (1 - θ))
            * t ^ (-((1 + θ) / 2) : ℝ) * CQ * |x - y| ^ θ := by
    rw [hapow, hbpow]
    rw [show
      (2 : ℝ) ^ (1 - θ)
          * (heatGradientLinftyLinftyConstant ^ (1 - θ)
            * t ^ (-(1 - θ) / 2 : ℝ) * CQ ^ (1 - θ))
          * ((5 * Real.sqrt 2 / 2) ^ θ * t ^ (-(θ : ℝ))
            * CQ ^ θ * |x - y| ^ θ)
        = (2 : ℝ) ^ (1 - θ)
            * ((5 * Real.sqrt 2 / 2) ^ θ
              * heatGradientLinftyLinftyConstant ^ (1 - θ))
            * (t ^ (-(1 - θ) / 2 : ℝ) * t ^ (-(θ : ℝ)))
            * (CQ ^ (1 - θ) * CQ ^ θ) * |x - y| ^ θ by ring]
    rw [hexp, hCQcollapse]
  rw [hfinal] at hchain
  exact hchain

end ShenWork.IntervalConjugateDuhamelMap
