import ShenWork.Paper1.WholeLineCauchyC2Bootstrap
import ShenWork.Paper1.WholeLineCauchyBUCHeatContinuity
import ShenWork.Paper1.WholeLineCauchyCanonicalRestart
import ShenWork.Paper1.WholeLineWeightedRegularityConjugation
import ShenWork.Paper1.WholeLineWeightedRegularityLinearSource

open Filter Topology MeasureTheory Real Set
open scoped Topology Interval
open intervalIntegral

noncomputable section

namespace ShenWork.Paper1

/-!
# Moving-frame restart identities for the weighted whole-line argument

The modified heat operator used by the Cauchy construction has generator
`partial_xx - 1`.  In a frame moving at speed `c`, its generator is therefore
`partial_xx + c * partial_x - 1`.  This file proves that generator directly
from the Gaussian convolution and records the exact shifted-reaction and
weighted-divergence algebra needed before subtracting a traveling wave.
-/

/-- Root-compatible moving-frame version of the Cauchy modified heat
operator.  We do not import the older `PaperOne` mild-map hierarchy, whose
legacy declarations collide with the live Paper 1 root closure. -/
def wholeLineCauchyMovingHeatOp
    (c t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  wholeLineCauchyHeatOp t f (x + c * t)

/-- Pointwise moving-frame modified heat flow, totalized at nonpositive time
by the identity on the BUC phase space.  This is the endpoint-correct path
used in the stationary mild formula. -/
def wholeLineCauchyMovingHeatBUCTotalVal
    (c t : ℝ) (f : WholeLineBUC) (x : ℝ) : ℝ :=
  (wholeLineCauchyHeatBUCTotal t f).1 (x + c * t)

@[simp] theorem wholeLineCauchyMovingHeatBUCTotalVal_zero
    (c : ℝ) (f : WholeLineBUC) (x : ℝ) :
    wholeLineCauchyMovingHeatBUCTotalVal c 0 f x = f.1 x := by
  simp [wholeLineCauchyMovingHeatBUCTotalVal]

theorem wholeLineCauchyMovingHeatBUCTotalVal_of_pos
    {c t : ℝ} (ht : 0 < t) (f : WholeLineBUC) (x : ℝ) :
    wholeLineCauchyMovingHeatBUCTotalVal c t f x =
      wholeLineCauchyMovingHeatOp c t f.1 x := by
  simp [wholeLineCauchyMovingHeatBUCTotalVal, wholeLineCauchyHeatBUCTotal,
    wholeLineCauchyMovingHeatOp, ht, wholeLineCauchyHeatBUC_apply]

/-- Strong continuity at the restart endpoint survives the moving spatial
translation. -/
theorem wholeLineCauchyMovingHeatBUCTotalVal_continuousAt_zero
    (c : ℝ) (f : WholeLineBUC) (x : ℝ) :
    ContinuousAt (fun t : ℝ =>
      wholeLineCauchyMovingHeatBUCTotalVal c t f x) 0 := by
  have hpair : ContinuousAt (fun t : ℝ =>
      (wholeLineCauchyHeatBUCTotal t f, x + c * t)) 0 :=
    (wholeLineCauchyHeatBUCTotal_continuousAt_zero f).prodMk
      ((continuous_const.add (continuous_const.mul continuous_id)).continuousAt)
  have heval : Continuous (fun z : WholeLineBUC × ℝ => z.1.1 z.2) := by
    fun_prop
  simpa [wholeLineCauchyMovingHeatBUCTotalVal] using
    heval.continuousAt.comp hpair

/-- Moving the observation point in the Gaussian convolution is the same as
translating the input in the opposite integration variable. -/
theorem wholeLineCauchyMovingHeatOp_eq_heatOp_translated_input
    (c t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    wholeLineCauchyMovingHeatOp c t f x =
      wholeLineCauchyHeatOp t (fun y => f (y + c * t)) x := by
  unfold wholeLineCauchyMovingHeatOp wholeLineCauchyHeatOp modifiedSemigroup
    heatSemigroup
  congr 1
  let g : ℝ → ℝ := fun y => heatKernel t (x + c * t - y) * f y
  have hshift := integral_add_right_eq_self (μ := volume) g (c * t)
  rw [show (∫ y : ℝ, heatKernel t (x + c * t - y) * f y) = ∫ y : ℝ, g y by rfl]
  rw [← hshift]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  dsimp [g]
  congr 2
  ring

/-- Arbitrary spatial translation version of the same heat-convolution
identity. -/
theorem wholeLineCauchyHeatOp_eval_shift_eq_input_shift
    (t d : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    wholeLineCauchyHeatOp t f (x + d) =
      wholeLineCauchyHeatOp t (fun y => f (y + d)) x := by
  unfold wholeLineCauchyHeatOp modifiedSemigroup heatSemigroup
  congr 1
  let g : ℝ → ℝ := fun y => heatKernel t (x + d - y) * f y
  have hshift := integral_add_right_eq_self (μ := volume) g d
  rw [show (∫ y : ℝ, heatKernel t (x + d - y) * f y) =
      ∫ y : ℝ, g y by rfl]
  rw [← hshift]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  dsimp [g]
  congr 2
  ring

/-- Arbitrary spatial translation also commutes with the kernel-gradient
operator. -/
theorem wholeLineCauchyHeatGradOp_eval_shift_eq_input_shift
    (t d : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    wholeLineCauchyHeatGradOp t f (x + d) =
      wholeLineCauchyHeatGradOp t (fun y => f (y + d)) x := by
  unfold wholeLineCauchyHeatGradOp
  let g : ℝ → ℝ := fun y => Real.exp (-t) *
    (deriv (fun z : ℝ => heatKernel t (z - y)) (x + d) * f y)
  have hshift := integral_add_right_eq_self (μ := volume) g d
  rw [show (∫ y : ℝ, Real.exp (-t) *
      (deriv (fun z : ℝ => heatKernel t (z - y)) (x + d) * f y)) =
      ∫ y : ℝ, g y by rfl]
  rw [← hshift]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  dsimp [g]
  rw [deriv_heatKernel_translated_left_global,
    deriv_heatKernel_translated_left_global]
  congr 2
  ring

/-- A Gaussian majorant for the heat kernel on a compact positive-time
neighborhood.  It is deliberately weakened to the same Gaussian used for the
Hessian majorant in `WholeLineConvolutionDifferentiation`. -/
lemma abs_heatKernel_local_time_le {t s : ℝ} (ht : 0 < t)
    (hs : s ∈ Metric.ball t (t / 2)) (w : ℝ) :
    |heatKernel s w| ≤
      (1 / Real.sqrt (2 * Real.pi * t)) *
        Real.exp (-(1 / (12 * t)) * w ^ 2) := by
  have hdist := Metric.mem_ball.mp hs
  rw [Real.dist_eq] at hdist
  have hlow : t / 2 < s := by
    have hlt := (abs_lt.mp hdist).1
    linarith
  have hup : s < 3 * t / 2 := by
    have hlt := (abs_lt.mp hdist).2
    linarith
  have hspos : 0 < s := by linarith
  rw [abs_of_nonneg (heatKernel_nonneg hspos w)]
  unfold heatKernel
  have hsqrt_le :
      Real.sqrt (2 * Real.pi * t) ≤ Real.sqrt (4 * Real.pi * s) := by
    apply Real.sqrt_le_sqrt
    nlinarith [Real.pi_pos]
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * t) := by positivity
  have hcoeff :
      1 / Real.sqrt (4 * Real.pi * s) ≤
        1 / Real.sqrt (2 * Real.pi * t) :=
    one_div_le_one_div_of_le hsqrt_pos hsqrt_le
  have hden : 4 * s ≤ 12 * t := by linarith
  have hden_pos : 0 < 4 * s := by positivity
  have hinv : 1 / (12 * t) ≤ 1 / (4 * s) :=
    one_div_le_one_div_of_le hden_pos hden
  have hmul := mul_le_mul_of_nonneg_right hinv (sq_nonneg w)
  have hexp :
      Real.exp (-w ^ 2 / (4 * s)) ≤
        Real.exp (-(1 / (12 * t)) * w ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hneg := neg_le_neg hmul
    convert hneg using 1 <;> ring
  exact mul_le_mul hcoeff hexp (Real.exp_nonneg _) (by positivity)

/-- The integrand used after translating the moving observation point onto
the input. -/
private def movingFrameHeatTranslatedIntegrand
    (c x : ℝ) (f : ℝ → ℝ) (s y : ℝ) : ℝ :=
  Real.exp (-s) * heatKernel s (x - y) * f (y + c * s)

/-- Its pointwise time derivative. -/
private def movingFrameHeatTranslatedIntegrandDeriv
    (c x : ℝ) (f : ℝ → ℝ) (s y : ℝ) : ℝ :=
  Real.exp (-s) *
    (deriv (fun q : ℝ => deriv (fun z : ℝ => heatKernel s z) q) (x - y) *
        f (y + c * s) +
      heatKernel s (x - y) * (c * deriv f (y + c * s)) -
      heatKernel s (x - y) * f (y + c * s))

/-- Direct pointwise differentiation of the translated moving-frame kernel.
No two-variable chain-rule package is assumed. -/
private theorem movingFrameHeatTranslatedIntegrand_hasDerivAt
    {c x s y : ℝ} {f : ℝ → ℝ} (hs : 0 < s)
    (hf : ∀ q, HasDerivAt f (deriv f q) q) :
    HasDerivAt
      (fun r => movingFrameHeatTranslatedIntegrand c x f r y)
      (movingFrameHeatTranslatedIntegrandDeriv c x f s y) s := by
  have hexp : HasDerivAt (fun r : ℝ => Real.exp (-r)) (-Real.exp (-s)) s := by
    convert (hasDerivAt_neg s).exp using 1 <;> ring
  have hker := heatKernel_time_hasDerivAt hs (x - y)
  have hinner : HasDerivAt (fun r : ℝ => y + c * r) c s := by
    have hc : HasDerivAt (fun r : ℝ => c * r) c s := by
      simpa using (hasDerivAt_id s).const_mul c
    convert (hasDerivAt_const s y).add hc using 1 <;> ring
  have hdata := (hf (y + c * s)).comp s hinner
  have hmain := (hexp.mul hker).mul hdata
  convert hmain using 1 <;>
    simp [movingFrameHeatTranslatedIntegrand,
      movingFrameHeatTranslatedIntegrandDeriv, Function.comp_apply] <;> ring

/-- Direct positive-time generator theorem for the moving-frame modified heat
operator on bounded `C1` data.  This discharges the conditional chain-rule
frontier in `WholeLineMovingFrameGenerator` for the regularity class used by
the traveling wave. -/
theorem wholeLineCauchyMovingHeatOp_time_hasDerivAt_of_bounded_C1
    {c : ℝ} {f : ℝ → ℝ} {t x M D : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hf : ∀ y, |f y| ≤ M)
    (hfd : ∀ y, |deriv f y| ≤ D)
    (hfderiv : ∀ y, HasDerivAt f (deriv f y) y)
    (hfdcont : Continuous (deriv f)) :
    HasDerivAt (fun s : ℝ => wholeLineCauchyMovingHeatOp c s f x)
      (wholeLineCauchyHeatHessOp t f (x + c * t) +
        c * wholeLineCauchyHeatOp t (deriv f) (x + c * t) -
        wholeLineCauchyHeatOp t f (x + c * t)) t := by
  let F : ℝ → ℝ → ℝ := movingFrameHeatTranslatedIntegrand c x f
  let F' : ℝ → ℝ → ℝ := movingFrameHeatTranslatedIntegrandDeriv c x f
  let Ch : ℝ := 5 * ((1 / t) * (1 / Real.sqrt (2 * Real.pi * t)))
  let Ck : ℝ := 1 / Real.sqrt (2 * Real.pi * t)
  let C : ℝ := Ch * M + Ck * (|c| * D + M)
  let bound : ℝ → ℝ := fun y =>
    C * Real.exp (-(1 / (12 * t)) * (x - y) ^ 2)
  have hfcont : Continuous f :=
    continuous_iff_continuousAt.2 (fun y => (hfderiv y).continuousAt)
  have hsball : Metric.ball t (t / 2) ∈ 𝓝 t :=
    Metric.ball_mem_nhds t (half_pos ht)
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) volume := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hspos
    change AEStronglyMeasurable
      (fun y : ℝ => Real.exp (-s) * heatKernel s (x - y) * f (y + c * s)) volume
    apply Continuous.aestronglyMeasurable
    unfold heatKernel
    fun_prop
  have hF_int : Integrable (F t) volume := by
    change Integrable
      (fun y : ℝ => Real.exp (-t) * heatKernel t (x - y) * f (y + c * t)) volume
    have hdata : AEStronglyMeasurable (fun y => f (y + c * t)) volume := by
      exact (hfcont.comp (continuous_id.add continuous_const)).aestronglyMeasurable
    have hbound_data : ∀ y, |f (y + c * t)| ≤ M := fun y => hf _
    have hbase :=
      (heatKernel_mul_bounded_integrable ht x hbound_data hdata).const_mul
        (Real.exp (-t))
    exact hbase.congr (Filter.Eventually.of_forall fun y => by ring)
  have hF'_meas : AEStronglyMeasurable (F' t) volume := by
    have hhess : Continuous (fun y : ℝ =>
        deriv (fun q : ℝ => deriv (fun z : ℝ => heatKernel t z) q) (x - y)) :=
      ShenWork.IntervalNeumannFullKernel.continuous_secondDeriv_heatKernel ht |>.comp
        (continuous_const.sub continuous_id)
    have hker : Continuous (fun y : ℝ => heatKernel t (x - y)) := by
      unfold heatKernel
      fun_prop
    have hfshift : Continuous (fun y : ℝ => f (y + c * t)) := by
      exact hfcont.comp (continuous_id.add continuous_const)
    have hfdshift : Continuous (fun y : ℝ => deriv f (y + c * t)) := by
      exact hfdcont.comp (continuous_id.add continuous_const)
    dsimp [F', movingFrameHeatTranslatedIntegrandDeriv]
    exact (continuous_const.mul
      ((hhess.mul hfshift).add
        (hker.mul (continuous_const.mul hfdshift)) |>.sub
        (hker.mul hfshift))).aestronglyMeasurable
  have hC : 0 ≤ C := by
    dsimp [C, Ch, Ck]
    positivity
  have h_bound :
      ∀ᵐ y ∂volume, ∀ s ∈ Metric.ball t (t / 2), ‖F' s y‖ ≤ bound y := by
    filter_upwards with y s hs
    have hdist := Metric.mem_ball.mp hs
    rw [Real.dist_eq] at hdist
    have hspos : 0 < s := by
      have hlt := (abs_lt.mp hdist).1
      linarith
    have hexp : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hhess :=
      ShenWork.PaperOne.ConvLeibniz.abs_secondDeriv_heatKernel_local_time_le
        ht hs (x - y)
    have hker := abs_heatKernel_local_time_le ht hs (x - y)
    have hcD : |c * deriv f (y + c * s)| ≤ |c| * D := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hfd _) (abs_nonneg c)
    have hinside :
        |deriv (fun q : ℝ => deriv (fun z : ℝ => heatKernel s z) q) (x - y) *
              f (y + c * s) +
            heatKernel s (x - y) * (c * deriv f (y + c * s)) -
            heatKernel s (x - y) * f (y + c * s)| ≤
          C * Real.exp (-(1 / (12 * t)) * (x - y) ^ 2) := by
      have htri2 := abs_sub
        (heatKernel s (x - y) * (c * deriv f (y + c * s)))
        (heatKernel s (x - y) * f (y + c * s))
      have htri' :
        |deriv (fun q : ℝ => deriv (fun z : ℝ => heatKernel s z) q) (x - y) *
              f (y + c * s) +
            heatKernel s (x - y) * (c * deriv f (y + c * s)) -
            heatKernel s (x - y) * f (y + c * s)|
            ≤ |deriv (fun q : ℝ => deriv (fun z : ℝ => heatKernel s z) q)
                  (x - y)| * |f (y + c * s)| +
                (|heatKernel s (x - y)| * |c * deriv f (y + c * s)| +
                  |heatKernel s (x - y)| * |f (y + c * s)|) := by
        calc
          _ = |deriv (fun q : ℝ => deriv (fun z : ℝ => heatKernel s z) q)
                  (x - y) * f (y + c * s) +
                (heatKernel s (x - y) * (c * deriv f (y + c * s)) -
                  heatKernel s (x - y) * f (y + c * s))| := by ring
          _ ≤ |deriv (fun q : ℝ => deriv (fun z : ℝ => heatKernel s z) q)
                  (x - y) * f (y + c * s)| +
                |heatKernel s (x - y) * (c * deriv f (y + c * s)) -
                  heatKernel s (x - y) * f (y + c * s)| := abs_add_le _ _
          _ = |deriv (fun q : ℝ => deriv (fun z : ℝ => heatKernel s z) q)
                  (x - y)| * |f (y + c * s)| +
                |heatKernel s (x - y) * (c * deriv f (y + c * s)) -
                  heatKernel s (x - y) * f (y + c * s)| := by rw [abs_mul]
          _ ≤ _ := by
            exact add_le_add (le_refl _)
              (by simpa [abs_mul] using htri2)
      calc
        _ ≤ _ := htri'
        _ ≤ (Ch * Real.exp (-(1 / (12 * t)) * (x - y) ^ 2)) * M +
              ((Ck * Real.exp (-(1 / (12 * t)) * (x - y) ^ 2)) *
                  (|c| * D) +
                (Ck * Real.exp (-(1 / (12 * t)) * (x - y) ^ 2)) * M) := by
          exact add_le_add
            (mul_le_mul hhess (hf _) (abs_nonneg _) (by positivity))
            (add_le_add
              (mul_le_mul hker hcD (abs_nonneg _) (by positivity))
              (mul_le_mul hker (hf _) (abs_nonneg _) (by positivity)))
        _ = (Ch * M + Ck * (|c| * D + M)) *
              Real.exp (-(1 / (12 * t)) * (x - y) ^ 2) := by ring
        _ = C * Real.exp (-(1 / (12 * t)) * (x - y) ^ 2) := by rfl
    rw [Real.norm_eq_abs]
    dsimp [F', movingFrameHeatTranslatedIntegrandDeriv, bound]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-s) *
          |deriv (fun q : ℝ => deriv (fun z : ℝ => heatKernel s z) q) (x - y) *
                f (y + c * s) +
              heatKernel s (x - y) * (c * deriv f (y + c * s)) -
              heatKernel s (x - y) * f (y + c * s)|
          ≤ Real.exp (-s) *
              (C * Real.exp (-(1 / (12 * t)) * (x - y) ^ 2)) :=
        mul_le_mul_of_nonneg_left hinside (Real.exp_nonneg _)
      _ ≤ 1 * (C * Real.exp (-(1 / (12 * t)) * (x - y) ^ 2)) :=
        mul_le_mul_of_nonneg_right hexp
          (mul_nonneg hC (Real.exp_nonneg _))
      _ = C * Real.exp (-(1 / (12 * t)) * (x - y) ^ 2) := one_mul _
  have hbound_int : Integrable bound volume := by
    have hb : 0 < 1 / (12 * t) := by positivity
    dsimp [bound]
    exact (ShenWork.PaperOne.ConvLeibniz.integrable_exp_neg_mul_sq_shift hb x).const_mul C
  have h_diff :
      ∀ᵐ y ∂volume, ∀ s ∈ Metric.ball t (t / 2),
        HasDerivAt (fun r : ℝ => F r y) (F' s y) s := by
    filter_upwards with y s hs
    have hdist := Metric.mem_ball.mp hs
    rw [Real.dist_eq] at hdist
    have hspos : 0 < s := by
      have hlt := (abs_lt.mp hdist).1
      linarith
    exact movingFrameHeatTranslatedIntegrand_hasDerivAt hspos hfderiv
  have hraw :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (bound := bound) (F := F) (F' := F')
      (x₀ := t) (s := Metric.ball t (t / 2))
      hsball hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  have hpath :
      (fun s : ℝ => wholeLineCauchyMovingHeatOp c s f x) =
        fun s => ∫ y : ℝ, F s y := by
    funext s
    rw [wholeLineCauchyMovingHeatOp_eq_heatOp_translated_input]
    unfold wholeLineCauchyHeatOp modifiedSemigroup heatSemigroup
    change Real.exp (-s) *
        (∫ y : ℝ, heatKernel s (x - y) * f (y + c * s)) =
      ∫ y : ℝ, Real.exp (-s) * heatKernel s (x - y) * f (y + c * s)
    calc
      _ = ∫ y : ℝ, Real.exp (-s) *
          (heatKernel s (x - y) * f (y + c * s)) :=
        (MeasureTheory.integral_const_mul _ _).symm
      _ = _ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with y
        ring
  rw [hpath]
  convert hraw using 1
  let z : ℝ := x + c * t
  let A : ℝ → ℝ := fun y => Real.exp (-t) *
    (deriv (fun q : ℝ => deriv (fun w : ℝ => heatKernel t w) q) (z - y) * f y)
  let B : ℝ → ℝ := fun y => Real.exp (-t) *
    (heatKernel t (z - y) * (c * deriv f y))
  let C0 : ℝ → ℝ := fun y => Real.exp (-t) *
    (heatKernel t (z - y) * f y)
  let G : ℝ → ℝ := fun y => A y + B y - C0 y
  have hfmeas : AEStronglyMeasurable f volume := hfcont.aestronglyMeasurable
  have hA : Integrable A volume := by
    have hbase :=
      ShenWork.PaperOne.ConvLeibniz.secondDeriv_heatKernel_mul_bounded_integrable
        ht z hf hfmeas
    exact (hbase.const_mul (Real.exp (-t))).congr
      (Filter.Eventually.of_forall fun y => by simp [A])
  have hcfdmeas : AEStronglyMeasurable (fun y => c * deriv f y) volume :=
    hfdcont.aestronglyMeasurable.const_mul c
  have hcfd : ∀ y, |c * deriv f y| ≤ |c| * D := by
    intro y
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hfd y) (abs_nonneg c)
  have hB : Integrable B volume := by
    have hbase := heatKernel_mul_bounded_integrable ht z hcfd hcfdmeas
    exact (hbase.const_mul (Real.exp (-t))).congr
      (Filter.Eventually.of_forall fun y => by simp [B])
  have hC0 : Integrable C0 volume := by
    have hbase := heatKernel_mul_bounded_integrable ht z hf hfmeas
    exact (hbase.const_mul (Real.exp (-t))).congr
      (Filter.Eventually.of_forall fun y => by simp [C0])
  have hG : Integrable G volume := (hA.add hB).sub hC0
  have hsplit : (∫ y : ℝ, G y) =
      (∫ y : ℝ, A y) + (∫ y : ℝ, B y) - (∫ y : ℝ, C0 y) := by
    calc
      (∫ y : ℝ, G y) = ∫ y : ℝ, (A y + B y) - C0 y := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with y
        rfl
      _ = (∫ y : ℝ, A y + B y) - ∫ y : ℝ, C0 y :=
        MeasureTheory.integral_sub (hA.add hB) hC0
      _ = (∫ y : ℝ, A y) + (∫ y : ℝ, B y) - (∫ y : ℝ, C0 y) := by
        rw [MeasureTheory.integral_add hA hB]
  have hAeq : (∫ y : ℝ, A y) = Real.exp (-t) *
      ∫ y : ℝ,
        deriv (fun q : ℝ => deriv (fun w : ℝ => heatKernel t w) q) (z - y) *
          f y := by
    rw [show A = fun y => Real.exp (-t) *
        (deriv (fun q : ℝ => deriv (fun w : ℝ => heatKernel t w) q) (z - y) *
          f y) by rfl,
      MeasureTheory.integral_const_mul]
  have hBeq : (∫ y : ℝ, B y) = Real.exp (-t) *
      ∫ y : ℝ, heatKernel t (z - y) * (c * deriv f y) := by
    rw [show B = fun y => Real.exp (-t) *
        (heatKernel t (z - y) * (c * deriv f y)) by rfl,
      MeasureTheory.integral_const_mul]
  have hCeq : (∫ y : ℝ, C0 y) = Real.exp (-t) *
      ∫ y : ℝ, heatKernel t (z - y) * f y := by
    rw [show C0 = fun y => Real.exp (-t) *
        (heatKernel t (z - y) * f y) by rfl,
      MeasureTheory.integral_const_mul]
  have hBinner :
      (∫ y : ℝ, heatKernel t (z - y) * (c * deriv f y)) =
        c * ∫ y : ℝ, heatKernel t (z - y) * deriv f y := by
    rw [show (fun y => heatKernel t (z - y) * (c * deriv f y)) =
        fun y => c * (heatKernel t (z - y) * deriv f y) by
      funext y; ring,
      MeasureTheory.integral_const_mul]
  have htarget :
      wholeLineCauchyHeatHessOp t f z +
          c * wholeLineCauchyHeatOp t (deriv f) z -
          wholeLineCauchyHeatOp t f z =
        ∫ y : ℝ, G y := by
    unfold wholeLineCauchyHeatHessOp wholeLineCauchyHeatOp modifiedSemigroup
      heatSemigroup
    rw [hsplit, hAeq, hBeq, hCeq, hBinner]
    ring
  have hshift := integral_add_right_eq_self (μ := volume) G (c * t)
  calc
    wholeLineCauchyHeatHessOp t f (x + c * t) +
          c * wholeLineCauchyHeatOp t (deriv f) (x + c * t) -
          wholeLineCauchyHeatOp t f (x + c * t)
        = ∫ y : ℝ, G y := by simpa [z] using htarget
    _ = ∫ y : ℝ, G (y + c * t) := hshift.symm
    _ = ∫ y : ℝ, F' t y := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      simp [G, A, B, C0, F', movingFrameHeatTranslatedIntegrandDeriv, z]
      ring

/-- Two integrations by parts move the modified heat Hessian from the
Gaussian kernel onto a bounded `C2` input. -/
theorem wholeLineCauchyHeatHessOp_eq_heatOp_secondDeriv
    {f : ℝ → ℝ} {t x C D E : ℝ}
    (ht : 0 < t)
    (hf : ∀ y, |f y| ≤ C)
    (hfd : ∀ y, |deriv f y| ≤ D)
    (hfdd : ∀ y, |deriv (deriv f) y| ≤ E)
    (hfderiv : ∀ y, HasDerivAt f (deriv f y) y)
    (hfdderiv : ∀ y, HasDerivAt (deriv f) (deriv (deriv f) y) y)
    (hfdcont : Continuous (deriv f))
    (hfddcont : Continuous (deriv (deriv f))) :
    wholeLineCauchyHeatHessOp t f x =
      wholeLineCauchyHeatOp t (deriv (deriv f)) x := by
  calc
    wholeLineCauchyHeatHessOp t f x =
        wholeLineCauchyHeatGradOp t (deriv f) x :=
      wholeLineCauchyHeatHessOp_eq_gradOp_deriv
        ht hf hfd hfderiv hfdcont
    _ = wholeLineCauchyHeatOp t (deriv (deriv f)) x :=
      wholeLineCauchyHeatGradOp_eq_heatOp_deriv
        ht hfd hfdd hfdderiv hfddcont

/-- Moving-frame generator with all spatial derivatives transferred to the
input. -/
theorem wholeLineCauchyMovingHeatOp_time_hasDerivAt_of_bounded_C2
    {c : ℝ} {f : ℝ → ℝ} {t x C D E : ℝ}
    (ht : 0 < t) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ∀ y, |f y| ≤ C)
    (hfd : ∀ y, |deriv f y| ≤ D)
    (hfdd : ∀ y, |deriv (deriv f) y| ≤ E)
    (hfderiv : ∀ y, HasDerivAt f (deriv f y) y)
    (hfdderiv : ∀ y, HasDerivAt (deriv f) (deriv (deriv f) y) y)
    (hfdcont : Continuous (deriv f))
    (hfddcont : Continuous (deriv (deriv f))) :
    HasDerivAt (fun s : ℝ => wholeLineCauchyMovingHeatOp c s f x)
      (wholeLineCauchyHeatOp t (deriv (deriv f)) (x + c * t) +
        c * wholeLineCauchyHeatOp t (deriv f) (x + c * t) -
        wholeLineCauchyHeatOp t f (x + c * t)) t := by
  convert wholeLineCauchyMovingHeatOp_time_hasDerivAt_of_bounded_C1
    ht hC hD hf hfd hfderiv hfdcont using 1
  rw [wholeLineCauchyHeatHessOp_eq_heatOp_secondDeriv
    ht hf hfd hfdd hfderiv hfdderiv hfdcont hfddcont]

/-- Measurability in the positive lag variable for the moving heat flow. -/
theorem wholeLineCauchyMovingHeatOp_aestronglyMeasurable
    {c x : ℝ} {f : ℝ → ℝ} (hf : Continuous f) :
    AEStronglyMeasurable
      (fun t : ℝ => wholeLineCauchyMovingHeatOp c t f x) volume := by
  let J : ℝ × ℝ → ℝ := fun q =>
    Real.exp (-q.1) * heatKernel q.1 (x + c * q.1 - q.2) * f q.2
  have hJ : AEStronglyMeasurable J (volume.prod volume) := by
    have hker : AEStronglyMeasurable
        (fun q : ℝ × ℝ => heatKernel q.1 (x + c * q.1 - q.2))
        (volume.prod volume) := by
      unfold heatKernel
      fun_prop
    exact ((Real.continuous_exp.comp
      (continuous_fst.neg)).aestronglyMeasurable.mul hker) |>.mul
        (hf.comp continuous_snd).aestronglyMeasurable
  have hint : AEStronglyMeasurable
      (fun t : ℝ => ∫ y : ℝ, J (t, y)) volume :=
    AEStronglyMeasurable.integral_prod_right'
      (μ := volume) (ν := volume) (f := J) hJ
  have heq : (fun t : ℝ => wholeLineCauchyMovingHeatOp c t f x) =
      fun t => ∫ y : ℝ, J (t, y) := by
    funext t
    unfold wholeLineCauchyMovingHeatOp wholeLineCauchyHeatOp
      modifiedSemigroup heatSemigroup
    dsimp [J]
    rw [show (fun y : ℝ => Real.exp (-t) *
        heatKernel t (x + c * t - y) * f y) =
      fun y => Real.exp (-t) *
        (heatKernel t (x + c * t - y) * f y) by
          funext y
          ring]
    rw [MeasureTheory.integral_const_mul]
  rw [heq]
  exact hint

/-- A bounded continuous source has an interval-integrable moving heat
history on every finite positive lag interval. -/
theorem wholeLineCauchyMovingHeatOp_intervalIntegrable
    {c t x M : ℝ} {f : ℝ → ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hf : Continuous f) (hfb : ∀ y, |f y| ≤ M) :
    IntervalIntegrable
      (fun r : ℝ => wholeLineCauchyMovingHeatOp c r f x) volume 0 t := by
  apply intervalIntegrable_of_aestronglyMeasurable_of_norm_le ht.le
    (wholeLineCauchyMovingHeatOp_aestronglyMeasurable hf)
  intro r hr
  rw [Real.norm_eq_abs]
  exact wholeLineCauchyHeatOp_abs_bound_of_nonneg_time hfb hM
    hf.aestronglyMeasurable hr.1 (x + c * r)

/-- If a bounded `C2` profile solves the stationary equation for the moving
generator, differentiation of its moving heat orbit gives minus the moved
source. -/
theorem wholeLineCauchyMovingHeatOp_time_hasDerivAt_of_stationary_balance
    {c : ℝ} {f source : ℝ → ℝ} {t x C D E : ℝ}
    (ht : 0 < t) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ∀ y, |f y| ≤ C)
    (hfd : ∀ y, |deriv f y| ≤ D)
    (hfdd : ∀ y, |deriv (deriv f) y| ≤ E)
    (hfderiv : ∀ y, HasDerivAt f (deriv f y) y)
    (hfdderiv : ∀ y, HasDerivAt (deriv f) (deriv (deriv f) y) y)
    (hfdcont : Continuous (deriv f))
    (hfddcont : Continuous (deriv (deriv f)))
    (hbalance : ∀ y,
      deriv (deriv f) y + c * deriv f y - f y = -source y) :
    HasDerivAt (fun r : ℝ => wholeLineCauchyMovingHeatOp c r f x)
      (-wholeLineCauchyMovingHeatOp c t source x) t := by
  have hgen := wholeLineCauchyMovingHeatOp_time_hasDerivAt_of_bounded_C2
    (c := c) (x := x)
    ht hC hD hf hfd hfdd hfderiv hfdderiv hfdcont hfddcont
  apply hgen.congr_deriv
  let z := x + c * t
  have hfdd_meas : AEStronglyMeasurable (deriv (deriv f)) volume :=
    hfddcont.aestronglyMeasurable
  have hfd_meas : AEStronglyMeasurable (deriv f) volume :=
    hfdcont.aestronglyMeasurable
  have hf_cont : Continuous f :=
    continuous_iff_continuousAt.2 (fun y => (hfderiv y).continuousAt)
  have hf_meas : AEStronglyMeasurable f volume := hf_cont.aestronglyMeasurable
  have hcfd : ∀ y, |c * deriv f y| ≤ |c| * D := by
    intro y
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hfd y) (abs_nonneg c)
  have hcfd_meas : AEStronglyMeasurable (fun y => c * deriv f y) volume :=
    hfd_meas.const_mul c
  have hsum : ∀ y,
      |deriv (deriv f) y + c * deriv f y| ≤ E + |c| * D := by
    intro y
    exact (abs_add_le _ _).trans (add_le_add (hfdd y) (hcfd y))
  have hsum_meas : AEStronglyMeasurable
      (fun y => deriv (deriv f) y + c * deriv f y) volume :=
    hfdd_meas.add hcfd_meas
  have hadd := modifiedSemigroup_add_bounded hfdd hcfd
    hfdd_meas hcfd_meas ht z
  have hsub := modifiedSemigroup_sub_bounded hsum hf
    hsum_meas hf_meas ht z
  have hcmul := modifiedSemigroup_const_mul c (deriv f) t z
  have hpoint : (fun y =>
      deriv (deriv f) y + c * deriv f y - f y) = fun y => -source y := by
    funext y
    exact hbalance y
  unfold wholeLineCauchyMovingHeatOp wholeLineCauchyHeatOp
  rw [← hcmul, ← hadd, ← hsub, hpoint, modifiedSemigroup_neg]

/-- Actual stationary mild identity for the moving generator `dxx+c*dx-I`.
The time integral is written in lag variables, so the only endpoint issue is
the BUC strong continuity of the homogeneous orbit at lag zero. -/
theorem wholeLine_stationary_mild_identity_of_bounded_C2
    {c : ℝ} {f source : ℝ → ℝ} {t x C D E M : ℝ}
    (ht : 0 < t) (hC : 0 ≤ C) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hf : ∀ y, |f y| ≤ C)
    (hfd : ∀ y, |deriv f y| ≤ D)
    (hfdd : ∀ y, |deriv (deriv f) y| ≤ E)
    (hfderiv : ∀ y, HasDerivAt f (deriv f y) y)
    (hfdderiv : ∀ y, HasDerivAt (deriv f) (deriv (deriv f) y) y)
    (hfdcont : Continuous (deriv f))
    (hfddcont : Continuous (deriv (deriv f)))
    (hfunif : UniformContinuous f)
    (hsource_cont : Continuous source)
    (hsource_bound : ∀ y, |source y| ≤ M)
    (hbalance : ∀ y,
      deriv (deriv f) y + c * deriv f y - f y = -source y) :
    f x = wholeLineCauchyMovingHeatOp c t f x +
      ∫ r in (0 : ℝ)..t, wholeLineCauchyMovingHeatOp c r source x := by
  let fBUC : WholeLineBUC := wholeLineBUCOfUniformBound f hfunif C hf
  let path : ℝ → ℝ := fun r => wholeLineCauchyMovingHeatOp c r f x
  let sourcePath : ℝ → ℝ := fun r =>
    wholeLineCauchyMovingHeatOp c r source x
  have hderiv : ∀ r ∈ Set.Ioo (0 : ℝ) t,
      HasDerivAt path (-sourcePath r) r := by
    intro r hr
    exact wholeLineCauchyMovingHeatOp_time_hasDerivAt_of_stationary_balance
      hr.1 hC hD hf hfd hfdd hfderiv hfdderiv hfdcont hfddcont hbalance
  have hint : IntervalIntegrable (fun r => -sourcePath r) volume 0 t :=
    (wholeLineCauchyMovingHeatOp_intervalIntegrable ht hM
      hsource_cont hsource_bound).neg
  have hzero : Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
    have htotal : Tendsto
        (fun r : ℝ => wholeLineCauchyMovingHeatBUCTotalVal c r fBUC x)
        (𝓝[>] (0 : ℝ))
        (𝓝 (wholeLineCauchyMovingHeatBUCTotalVal c 0 fBUC x)) :=
      (wholeLineCauchyMovingHeatBUCTotalVal_continuousAt_zero c fBUC x).continuousWithinAt
    have heq : path =ᶠ[𝓝[>] (0 : ℝ)] fun r =>
        wholeLineCauchyMovingHeatBUCTotalVal c r fBUC x := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (wholeLineCauchyMovingHeatBUCTotalVal_of_pos hr fBUC x).symm
    simpa [path, fBUC] using htotal.congr' heq.symm
  have htend : Tendsto path (𝓝[<] t)
      (𝓝 (wholeLineCauchyMovingHeatOp c t f x)) := by
    have hcont : ContinuousAt path t := by
      simpa [path] using
        (wholeLineCauchyMovingHeatOp_time_hasDerivAt_of_stationary_balance
          (x := x) ht hC hD hf hfd hfdd hfderiv hfdderiv hfdcont hfddcont
          hbalance).continuousAt
    exact hcont.continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    ht hderiv hint hzero htend
  rw [intervalIntegral.integral_neg] at hftc
  dsimp [path, sourcePath] at hftc
  linarith

/-- Exact recent-window restart equation for the canonical physical BUC
fixed point.  Unlike a second local fixed-point construction, this identity
uses the semigroup cocycle directly and therefore keeps the original source
trajectory on the interval `[a,a+h]`. -/
theorem wholeLineCauchyBUCMildFixedPoint_restart_identity
    (p : CMParams) {M T a h : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ha : 0 < a) (hh : 0 < h) (hah : a + h ≤ T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let za : Set.Icc (0 : ℝ) T :=
      ⟨a, ha.le, (le_add_of_nonneg_right hh.le).trans hah⟩
    let zah : Set.Icc (0 : ℝ) T :=
      ⟨a + h, (add_pos ha hh).le, hah⟩
    U zah = wholeLineCauchyHeatBUCTotal h (U za) +
      (-p.χ) • (∫ s in a..(a + h),
        wholeLineCauchyGradientBUCIntegrand p hM hT U (a + h) s) +
      ∫ s in a..(a + h),
        wholeLineCauchyValueBUCIntegrand p hM hT U (a + h) s := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let za : Set.Icc (0 : ℝ) T :=
    ⟨a, ha.le, (le_add_of_nonneg_right hh.le).trans hah⟩
  let zah : Set.Icc (0 : ℝ) T :=
    ⟨a + h, (add_pos ha hh).le, hah⟩
  have hUa : U za =
      wholeLineCauchyHeatBUCTotal a u₀ +
        (-p.χ) • wholeLineCauchyGradientDuhamelBUC p hM hT U a +
        wholeLineCauchyValueDuhamelBUC p hM hT U a := by
    have hfix := congrArg (fun W : WholeLineBUCTrajectory T => W za)
      (wholeLineCauchyBUCMildFixedPoint_eq_mildMap
        p hM hT u₀ hsmall)
    simpa [U, za, wholeLineCauchyBUCMildMap] using hfix
  have hUah : U zah =
      wholeLineCauchyHeatBUCTotal (a + h) u₀ +
        (-p.χ) • wholeLineCauchyGradientDuhamelBUC p hM hT U (a + h) +
        wholeLineCauchyValueDuhamelBUC p hM hT U (a + h) := by
    have hfix := congrArg (fun W : WholeLineBUCTrajectory T => W zah)
      (wholeLineCauchyBUCMildFixedPoint_eq_mildMap
        p hM hT u₀ hsmall)
    simpa [U, zah, wholeLineCauchyBUCMildMap] using hfix
  have hGrestart := wholeLineCauchyGradientDuhamelBUC_restart_fixedPoint
    p hM hT u₀ hsmall ha
    ((le_add_of_nonneg_right hh.le).trans hah) hh
    (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hstrip
  have hRrestart := wholeLineCauchyValueDuhamelBUC_restart
    p hM hT U ha hh
  have heat_add (v w : WholeLineBUC) :
      wholeLineCauchyHeatBUCTotal h (v + w) =
        wholeLineCauchyHeatBUCTotal h v +
          wholeLineCauchyHeatBUCTotal h w := by
    simp only [wholeLineCauchyHeatBUCTotal, dif_pos hh]
    change wholeLineCauchyHeatBUCCLM h hh (v + w) =
      wholeLineCauchyHeatBUCCLM h hh v +
        wholeLineCauchyHeatBUCCLM h hh w
    exact map_add (wholeLineCauchyHeatBUCCLM h hh) v w
  have heat_smul (q : ℝ) (v : WholeLineBUC) :
      wholeLineCauchyHeatBUCTotal h (q • v) =
        q • wholeLineCauchyHeatBUCTotal h v := by
    simp only [wholeLineCauchyHeatBUCTotal, dif_pos hh]
    change wholeLineCauchyHeatBUCCLM h hh (q • v) =
      q • wholeLineCauchyHeatBUCCLM h hh v
    exact map_smul (wholeLineCauchyHeatBUCCLM h hh) q v
  have hheatUa : wholeLineCauchyHeatBUCTotal h (U za) =
      wholeLineCauchyHeatBUCTotal (a + h) u₀ +
        (-p.χ) • wholeLineCauchyHeatBUCTotal h
          (wholeLineCauchyGradientDuhamelBUC p hM hT U a) +
        wholeLineCauchyHeatBUCTotal h
          (wholeLineCauchyValueDuhamelBUC p hM hT U a) := by
    rw [hUa, heat_add, heat_add, heat_smul]
    rw [wholeLineCauchyHeatBUCTotal_add_time hh ha]
    simpa [add_comm]
  rw [hUah, hGrestart, hRrestart, hheatUa]
  module

/-- Physical canonical flux source observed in the frame moving at speed
`c`. -/
def wholeLineCauchyCoMovingFluxSource
    (p : CMParams) (c : ℝ) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (s x : ℝ) : ℝ :=
  (wholeLineCauchyFluxSourceTrajectory p hM hT U s).1 (x + c * s)

/-- Physical canonical shifted reaction source in the moving frame. -/
def wholeLineCauchyCoMovingReactionSource
    (p : CMParams) (c : ℝ) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
  (U : WholeLineBUCTrajectory T) (s x : ℝ) : ℝ :=
  (wholeLineCauchyReactionSourceTrajectory p hM hT U s).1 (x + c * s)

/-- The canonical fixed point, totalized outside its construction horizon and
observed in the frame moving at speed `c`.  Only the on-horizon simp theorem
is used in restart identities. -/
def wholeLineCauchyBUCMildFixedPointCoMovingPath
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (c s x : ℝ) : ℝ :=
  if hs : s ∈ Set.Icc (0 : ℝ) T then
    (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall ⟨s, hs⟩).1
      (x + c * s)
  else 0

@[simp] theorem wholeLineCauchyBUCMildFixedPointCoMovingPath_of_mem
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (c s x : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T) :
    wholeLineCauchyBUCMildFixedPointCoMovingPath
        p hM hT u₀ hsmall c s x =
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall ⟨s, hs⟩).1
        (x + c * s) := by
  simp [wholeLineCauchyBUCMildFixedPointCoMovingPath, hs]

/-- Pointwise moving-frame form of the canonical recent-window restart. -/
theorem wholeLineCauchyBUCMildFixedPoint_coMoving_restart_identity
    (p : CMParams) {M T a h c x : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ha : 0 < a) (hh : 0 < h) (hah : a + h ≤ T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 y ∈
        Set.Icc (0 : ℝ) M) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let za : Set.Icc (0 : ℝ) T :=
      ⟨a, ha.le, (le_add_of_nonneg_right hh.le).trans hah⟩
    let zah : Set.Icc (0 : ℝ) T :=
      ⟨a + h, (add_pos ha hh).le, hah⟩
    (U zah).1 (x + c * (a + h)) =
      paper5MovingFrameHeatOp c h
        (fun y => (U za).1 (y + c * a)) x +
      (-p.χ) * (∫ s in a..(a + h),
        paper5MovingFrameHeatGradOp c (a + h - s)
          (wholeLineCauchyCoMovingFluxSource p c hM hT U s) x) +
      ∫ s in a..(a + h),
        paper5MovingFrameHeatOp c (a + h - s)
          (wholeLineCauchyCoMovingReactionSource p c hM hT U s) x := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let za : Set.Icc (0 : ℝ) T :=
    ⟨a, ha.le, (le_add_of_nonneg_right hh.le).trans hah⟩
  let zah : Set.Icc (0 : ℝ) T :=
    ⟨a + h, (add_pos ha hh).le, hah⟩
  let X : ℝ := x + c * (a + h)
  have hrestart := wholeLineCauchyBUCMildFixedPoint_restart_identity
    p hM hT u₀ hsmall ha hh hah hstrip
  dsimp only at hrestart
  have hpoint := congrArg (fun w : WholeLineBUC => w.1 X) hrestart
  have htarget0 : 0 ≤ a + h := (add_pos ha hh).le
  have hGfull := wholeLineCauchyGradientBUCIntegrand_intervalIntegrable
    p hM hT U htarget0
  have hGint : IntervalIntegrable
      (wholeLineCauchyGradientBUCIntegrand p hM hT U (a + h))
      volume a (a + h) := by
    apply hGfull.mono_set
    rw [Set.uIcc_of_le (le_add_of_nonneg_right hh.le),
      Set.uIcc_of_le htarget0]
    exact Set.Icc_subset_Icc_left ha.le
  have hRfull := wholeLineCauchyValueBUCIntegrand_intervalIntegrable
    p hM hT U htarget0
  have hRint : IntervalIntegrable
      (wholeLineCauchyValueBUCIntegrand p hM hT U (a + h))
      volume a (a + h) := by
    apply hRfull.mono_set
    rw [Set.uIcc_of_le (le_add_of_nonneg_right hh.le),
      Set.uIcc_of_le htarget0]
    exact Set.Icc_subset_Icc_left ha.le
  change (U zah).1 X =
      (wholeLineCauchyHeatBUCTotal h (U za)).1 X +
        (-p.χ) *
          (∫ s in a..(a + h),
            wholeLineCauchyGradientBUCIntegrand p hM hT U (a + h) s).1 X +
        (∫ s in a..(a + h),
          wholeLineCauchyValueBUCIntegrand p hM hT U (a + h) s).1 X
    at hpoint
  rw [wholeLineBUC_intervalIntegral_apply hGint X,
    wholeLineBUC_intervalIntegral_apply hRint X] at hpoint
  have hhom :
      (wholeLineCauchyHeatBUCTotal h (U za)).1 X =
        paper5MovingFrameHeatOp c h
          (fun y => (U za).1 (y + c * a)) x := by
    have htotal : wholeLineCauchyHeatBUCTotal h (U za) =
        wholeLineCauchyHeatBUC h hh (U za) := by
      simp [wholeLineCauchyHeatBUCTotal, hh]
    rw [htotal]
    rw [wholeLineCauchyHeatBUC_apply]
    unfold paper5MovingFrameHeatOp
    rw [show X = (x + c * h) + c * a by
      dsimp [X]
      ring]
    exact wholeLineCauchyHeatOp_eval_shift_eq_input_shift
      h (c * a) (U za).1 (x + c * h)
  have hGmove :
      (∫ s in a..(a + h),
        (wholeLineCauchyGradientBUCIntegrand p hM hT U (a + h) s).1 X) =
      ∫ s in a..(a + h),
        paper5MovingFrameHeatGradOp c (a + h - s)
          (wholeLineCauchyCoMovingFluxSource p c hM hT U s) x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (a + h)] with s hne hs
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hh.le)] at hs
    have hlag : 0 < a + h - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hne)
    unfold wholeLineCauchyGradientBUCIntegrand
    have htotal : wholeLineCauchyHeatGradientBUCTotal (a + h - s)
          (wholeLineCauchyFluxSourceTrajectory p hM hT U s) =
        wholeLineCauchyHeatGradientBUC (a + h - s) hlag
          (wholeLineCauchyFluxSourceTrajectory p hM hT U s) := by
      simp [wholeLineCauchyHeatGradientBUCTotal, hlag]
    rw [htotal]
    rw [wholeLineCauchyHeatGradientBUC_apply]
    unfold paper5MovingFrameHeatGradOp wholeLineCauchyCoMovingFluxSource
    rw [show X = (x + c * (a + h - s)) + c * s by
      dsimp [X]
      ring]
    exact wholeLineCauchyHeatGradOp_eval_shift_eq_input_shift
      (a + h - s) (c * s)
        (wholeLineCauchyFluxSourceTrajectory p hM hT U s).1
        (x + c * (a + h - s))
  have hRmove :
      (∫ s in a..(a + h),
        (wholeLineCauchyValueBUCIntegrand p hM hT U (a + h) s).1 X) =
      ∫ s in a..(a + h),
        paper5MovingFrameHeatOp c (a + h - s)
          (wholeLineCauchyCoMovingReactionSource p c hM hT U s) x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (a + h)] with s hne hs
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hh.le)] at hs
    have hlag : 0 < a + h - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hne)
    unfold wholeLineCauchyValueBUCIntegrand
    have htotal : wholeLineCauchyHeatBUCTotal (a + h - s)
          (wholeLineCauchyReactionSourceTrajectory p hM hT U s) =
        wholeLineCauchyHeatBUC (a + h - s) hlag
          (wholeLineCauchyReactionSourceTrajectory p hM hT U s) := by
      simp [wholeLineCauchyHeatBUCTotal, hlag]
    rw [htotal]
    rw [wholeLineCauchyHeatBUC_apply]
    unfold paper5MovingFrameHeatOp wholeLineCauchyCoMovingReactionSource
    rw [show X = (x + c * (a + h - s)) + c * s by
      dsimp [X]
      ring]
    exact wholeLineCauchyHeatOp_eval_shift_eq_input_shift
      (a + h - s) (c * s)
        (wholeLineCauchyReactionSourceTrajectory p hM hT U s).1
        (x + c * (a + h - s))
  rw [hhom, hGmove, hRmove] at hpoint
  simpa [U, za, zah, X, smul_eq_mul] using hpoint

/-- Exact exponentially conjugated canonical restart in the moving frame.
The divergence history contains both the weighted heat-gradient and the
indispensable `-eta` weighted heat term. -/
theorem wholeLineCauchyBUCMildFixedPoint_weighted_coMoving_restart_identity
    (p : CMParams) {M T a h eta c x : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ha : 0 < a) (hh : 0 < h) (hah : a + h ≤ T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 y ∈
        Set.Icc (0 : ℝ) M)
    (hflux_grad_int : ∀ s ∈ Set.Ioc a (a + h),
      Integrable (fun y : ℝ =>
        deriv (fun z : ℝ => heatKernel (a + h - s) z)
            (x + (c - 2 * eta) * (a + h - s) - y) *
          (Real.exp (eta * y) *
            wholeLineCauchyCoMovingFluxSource p c hM hT
              (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s y)))
    (hflux_heat_int : ∀ s ∈ Set.Ioc a (a + h),
      Integrable (fun y : ℝ =>
        weightedMovingHeatMarkovKernel eta c (a + h - s) x y *
          (Real.exp (eta * y) *
            wholeLineCauchyCoMovingFluxSource p c hM hT
              (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s y))) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let za : Set.Icc (0 : ℝ) T :=
      ⟨a, ha.le, (le_add_of_nonneg_right hh.le).trans hah⟩
    let zah : Set.Icc (0 : ℝ) T :=
      ⟨a + h, (add_pos ha hh).le, hah⟩
    Real.exp (eta * x) * (U zah).1 (x + c * (a + h)) =
      Real.exp (-h) * weightedMovingHeatEta eta c h
        (fun y => Real.exp (eta * y) * (U za).1 (y + c * a)) x +
      (-p.χ) * (∫ s in a..(a + h),
        Real.exp (-(a + h - s)) *
          (weightedMovingHeatGradientEta eta c (a + h - s)
              (fun y => Real.exp (eta * y) *
                wholeLineCauchyCoMovingFluxSource p c hM hT U s y) x -
            eta * weightedMovingHeatEta eta c (a + h - s)
              (fun y => Real.exp (eta * y) *
                wholeLineCauchyCoMovingFluxSource p c hM hT U s y) x)) +
      ∫ s in a..(a + h),
        Real.exp (-(a + h - s)) *
          weightedMovingHeatEta eta c (a + h - s)
            (fun y => Real.exp (eta * y) *
              wholeLineCauchyCoMovingReactionSource p c hM hT U s y) x := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let za : Set.Icc (0 : ℝ) T :=
    ⟨a, ha.le, (le_add_of_nonneg_right hh.le).trans hah⟩
  let zah : Set.Icc (0 : ℝ) T :=
    ⟨a + h, (add_pos ha hh).le, hah⟩
  have hco := wholeLineCauchyBUCMildFixedPoint_coMoving_restart_identity
    p hM hT u₀ hsmall ha hh hah hstrip (c := c) (x := x)
  dsimp only at hco
  have hhom := exp_mul_movingFrameHeatOp_eq_weightedMovingHeatEta
    hh (fun y => (U za).1 (y + c * a)) x (eta := eta) (c := c)
  have hG : Real.exp (eta * x) *
      (∫ s in a..(a + h),
        paper5MovingFrameHeatGradOp c (a + h - s)
          (wholeLineCauchyCoMovingFluxSource p c hM hT U s) x) =
      ∫ s in a..(a + h),
        Real.exp (-(a + h - s)) *
          (weightedMovingHeatGradientEta eta c (a + h - s)
              (fun y => Real.exp (eta * y) *
                wholeLineCauchyCoMovingFluxSource p c hM hT U s y) x -
            eta * weightedMovingHeatEta eta c (a + h - s)
              (fun y => Real.exp (eta * y) *
                wholeLineCauchyCoMovingFluxSource p c hM hT U s y) x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (a + h)] with s hne hs
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hh.le)] at hs
    have hlag : 0 < a + h - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hne)
    exact exp_mul_movingFrameHeatGradOp_eq_weightedMovingHeatGradientEta_sub
      hlag (wholeLineCauchyCoMovingFluxSource p c hM hT U s) x
      (by simpa [U] using hflux_grad_int s hs)
      (by simpa [U] using hflux_heat_int s hs)
  have hR : Real.exp (eta * x) *
      (∫ s in a..(a + h),
        paper5MovingFrameHeatOp c (a + h - s)
          (wholeLineCauchyCoMovingReactionSource p c hM hT U s) x) =
      ∫ s in a..(a + h),
        Real.exp (-(a + h - s)) *
          weightedMovingHeatEta eta c (a + h - s)
            (fun y => Real.exp (eta * y) *
              wholeLineCauchyCoMovingReactionSource p c hM hT U s y) x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (a + h)] with s hne hs
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hh.le)] at hs
    have hlag : 0 < a + h - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hne)
    exact exp_mul_movingFrameHeatOp_eq_weightedMovingHeatEta
      hlag (wholeLineCauchyCoMovingReactionSource p c hM hT U s) x
  rw [hco]
  calc
    Real.exp (eta * x) *
        (paper5MovingFrameHeatOp c h
            (fun y => (U za).1 (y + c * a)) x +
          (-p.χ) * (∫ s in a..(a + h),
            paper5MovingFrameHeatGradOp c (a + h - s)
              (wholeLineCauchyCoMovingFluxSource p c hM hT U s) x) +
          ∫ s in a..(a + h),
            paper5MovingFrameHeatOp c (a + h - s)
              (wholeLineCauchyCoMovingReactionSource p c hM hT U s) x) =
      Real.exp (eta * x) * paper5MovingFrameHeatOp c h
          (fun y => (U za).1 (y + c * a)) x +
        (-p.χ) * (Real.exp (eta * x) *
          (∫ s in a..(a + h),
            paper5MovingFrameHeatGradOp c (a + h - s)
              (wholeLineCauchyCoMovingFluxSource p c hM hT U s) x)) +
        Real.exp (eta * x) *
          (∫ s in a..(a + h),
            paper5MovingFrameHeatOp c (a + h - s)
              (wholeLineCauchyCoMovingReactionSource p c hM hT U s) x) := by
        ring
    _ = _ := by rw [hhom, hG, hR]

/-- Linearity of the conjugated moving heat operator on two genuinely
integrable kernel inputs. -/
theorem weightedMovingHeatEta_sub_of_integrable
    {eta c t x : ℝ} {f g : ℝ → ℝ}
    (hf : Integrable (fun y : ℝ =>
      weightedMovingHeatMarkovKernel eta c t x y * f y))
    (hg : Integrable (fun y : ℝ =>
      weightedMovingHeatMarkovKernel eta c t x y * g y)) :
    weightedMovingHeatEta eta c t (fun y => f y - g y) x =
      weightedMovingHeatEta eta c t f x -
        weightedMovingHeatEta eta c t g x := by
  unfold weightedMovingHeatEta
  rw [show (fun y : ℝ =>
      weightedMovingHeatMarkovKernel eta c t x y * (f y - g y)) =
      fun y => weightedMovingHeatMarkovKernel eta c t x y * f y -
        weightedMovingHeatMarkovKernel eta c t x y * g y by
      funext y
      ring,
    MeasureTheory.integral_sub hf hg]
  ring

/-- Linearity of the conjugated moving heat-gradient operator on two
genuinely integrable kernel inputs. -/
theorem weightedMovingHeatGradientEta_sub_of_integrable
    {eta c t x : ℝ} {f g : ℝ → ℝ}
    (hf : Integrable (fun y : ℝ =>
      deriv (fun z : ℝ => heatKernel t z)
          (x + (c - 2 * eta) * t - y) * f y))
    (hg : Integrable (fun y : ℝ =>
      deriv (fun z : ℝ => heatKernel t z)
          (x + (c - 2 * eta) * t - y) * g y)) :
    weightedMovingHeatGradientEta eta c t (fun y => f y - g y) x =
      weightedMovingHeatGradientEta eta c t f x -
        weightedMovingHeatGradientEta eta c t g x := by
  unfold weightedMovingHeatGradientEta
  rw [show (fun y : ℝ =>
      deriv (fun z : ℝ => heatKernel t z)
          (x + (c - 2 * eta) * t - y) * (f y - g y)) =
      fun y =>
        deriv (fun z : ℝ => heatKernel t z)
            (x + (c - 2 * eta) * t - y) * f y -
          deriv (fun z : ℝ => heatKernel t z)
            (x + (c - 2 * eta) * t - y) * g y by
      funext y
      ring,
    MeasureTheory.integral_sub hf hg]
  ring

/-- One lag of the conjugated divergence Duhamel operator. -/
def paper5WeightedDivergenceRestartTerm
    (eta c lag : ℝ) (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-lag) *
    (weightedMovingHeatGradientEta eta c lag q x -
      eta * weightedMovingHeatEta eta c lag q x)

/-- One lag of the conjugated value Duhamel operator. -/
def paper5WeightedValueRestartTerm
    (eta c lag : ℝ) (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-lag) * weightedMovingHeatEta eta c lag q x

/-- Physical traveling-wave chemotaxis flux. -/
def wholeLineTravelingWaveFlux
    (p : CMParams) (U V : ℝ → ℝ) (x : ℝ) : ℝ :=
  (U x) ^ p.m * deriv V x

/-- Source paired with the moving modified generator.  The extra `U` in the
shifted reaction exactly compensates the `-I` in the generator. -/
def wholeLineTravelingWaveShiftedSource
    (p : CMParams) (U V : ℝ → ℝ) (x : ℝ) : ℝ :=
  -p.χ * deriv (wholeLineTravelingWaveFlux p U V) x +
    wholeLineCauchyShiftedReaction p U x

/-- Weighted canonical flux slice in the moving frame. -/
def paper5WeightedCanonicalFluxSource
    (p : CMParams) (eta c : ℝ) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (s y : ℝ) : ℝ :=
  Real.exp (eta * y) *
    wholeLineCauchyCoMovingFluxSource p c hM hT U s y

/-- Weighted traveling-wave flux slice. -/
def paper5WeightedTravelingWaveFluxSource
    (p : CMParams) (eta : ℝ) (U V : ℝ → ℝ) (y : ℝ) : ℝ :=
  Real.exp (eta * y) * wholeLineTravelingWaveFlux p U V y

/-- Weighted flux perturbation appearing in the exact restart identity. -/
def paper5WeightedFluxDifferenceSource
    (p : CMParams) (eta c : ℝ) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (Uw Vw : ℝ → ℝ)
    (s y : ℝ) : ℝ :=
  paper5WeightedCanonicalFluxSource p eta c hM hT U s y -
    paper5WeightedTravelingWaveFluxSource p eta Uw Vw y

/-- Weighted canonical shifted-reaction slice in the moving frame. -/
def paper5WeightedCanonicalReactionSource
    (p : CMParams) (eta c : ℝ) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (s y : ℝ) : ℝ :=
  Real.exp (eta * y) *
    wholeLineCauchyCoMovingReactionSource p c hM hT U s y

/-- Weighted traveling-wave shifted-reaction slice. -/
def paper5WeightedTravelingWaveReactionSource
    (p : CMParams) (eta : ℝ) (U : ℝ → ℝ) (y : ℝ) : ℝ :=
  Real.exp (eta * y) * wholeLineCauchyShiftedReaction p U y

/-- Weighted reaction perturbation appearing in the exact restart identity. -/
def paper5WeightedReactionDifferenceSource
    (p : CMParams) (eta c : ℝ) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (Uw : ℝ → ℝ)
    (s y : ℝ) : ℝ :=
  paper5WeightedCanonicalReactionSource p eta c hM hT U s y -
    paper5WeightedTravelingWaveReactionSource p eta Uw y

/-- Exact stationary balance for the moving generator. -/
theorem wholeLineTravelingWave_movingGenerator_balance
    (p : CMParams) {c x : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V) :
    deriv (deriv U) x + c * deriv U x - U x +
      wholeLineTravelingWaveShiftedSource p U V x = 0 := by
  have hode := hTW.ode_U x
  have hiter : iteratedDeriv 2 U = deriv (deriv U) := by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ]
    rw [show 1 = 0 + 1 by norm_num, iteratedDeriv_succ]
    rfl
  rw [hiter] at hode
  change deriv (deriv U) x + c * deriv U x -
      p.χ * deriv (fun y => (U y) ^ p.m * deriv V y) x +
      U x * (1 - (U x) ^ p.α) = 0 at hode
  unfold wholeLineTravelingWaveShiftedSource wholeLineTravelingWaveFlux
    wholeLineCauchyShiftedReaction wholeLineLogisticSource reactionFun
  linear_combination hode

/-- Traveling-wave specialization of the actual stationary mild identity.
The remaining hypotheses are precisely global bounds and continuity of the
second derivative/source needed to justify the whole-line Gaussian FTC; the
stationary equation itself is discharged by `IsTravelingWave.ode_U`. -/
theorem IsTravelingWave.stationary_mild_identity
    (p : CMParams) {c t x D E M : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (ht : 0 < t) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hUd : ∀ y, |deriv U y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv U) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv U)))
    (hsource_cont : Continuous
      (wholeLineTravelingWaveShiftedSource p U V))
    (hsource_bound : ∀ y,
      |wholeLineTravelingWaveShiftedSource p U V y| ≤ M) :
    U x = wholeLineCauchyMovingHeatOp c t U x +
      ∫ r in (0 : ℝ)..t,
        wholeLineCauchyMovingHeatOp c r
          (wholeLineTravelingWaveShiftedSource p U V) x := by
  have hC : 0 ≤ MChi p :=
    le_trans (hbound.pos 0).le (hbound.le_MChi 0)
  apply wholeLine_stationary_mild_identity_of_bounded_C2
    ht hC hD hM (fun y => by
      rw [abs_of_pos (hbound.pos y)]
      exact hbound.le_MChi y)
    hUd hUdd
    (fun y => (hreg.U_diff y).hasDerivAt)
    (fun y => (hreg.deriv_U_diff y).hasDerivAt)
    hreg.deriv_U_cont hUddcont
    (travelingWave_U_uniformContinuous hTW hreg.U_cont)
    hsource_cont hsource_bound
  intro y
  have hbal := wholeLineTravelingWave_movingGenerator_balance
    p hTW (x := y)
  linarith

/-- Moving heat applied to the stationary shifted source splits into the
kernel-gradient flux leg and the shifted reaction leg. -/
theorem wholeLineTravelingWaveShiftedSource_movingHeat_eq
    (p : CMParams) {c t x F D R : ℝ} {U V : ℝ → ℝ}
    (ht : 0 < t)
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p U V y| ≤ F)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p U V) y| ≤ D)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p U V)
      (deriv (wholeLineTravelingWaveFlux p U V) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p U V)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p U y| ≤ R)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p U)) :
    paper5MovingFrameHeatOp c t
        (wholeLineTravelingWaveShiftedSource p U V) x =
      (-p.χ) * paper5MovingFrameHeatGradOp c t
        (wholeLineTravelingWaveFlux p U V) x +
      paper5MovingFrameHeatOp c t
        (wholeLineCauchyShiftedReaction p U) x := by
  let z := x + c * t
  have hscaled : ∀ y,
      |-p.χ * deriv (wholeLineTravelingWaveFlux p U V) y| ≤ |p.χ| * D := by
    intro y
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hfluxd y) (abs_nonneg p.χ)
  have hscaled_meas : AEStronglyMeasurable
      (fun y => -p.χ * deriv (wholeLineTravelingWaveFlux p U V) y) volume :=
    hfluxd_cont.aestronglyMeasurable.const_mul (-p.χ)
  have hreact_meas : AEStronglyMeasurable
      (wholeLineCauchyShiftedReaction p U) volume :=
    hreact_cont.aestronglyMeasurable
  have hadd := modifiedSemigroup_add_bounded hscaled hreact
    hscaled_meas hreact_meas ht z
  have hcmul := modifiedSemigroup_const_mul (-p.χ)
    (deriv (wholeLineTravelingWaveFlux p U V)) t z
  have hgrad := wholeLineCauchyHeatGradOp_eq_heatOp_deriv
    (x := z) ht hflux hfluxd hflux_has hfluxd_cont
  unfold paper5MovingFrameHeatOp paper5MovingFrameHeatGradOp
    wholeLineTravelingWaveShiftedSource wholeLineCauchyHeatOp at *
  rw [hadd, hcmul, ← hgrad]

/-- Stationary traveling-wave mild formula in the same divergence/value
splitting used by the canonical Cauchy restart. -/
theorem IsTravelingWave.stationary_divergence_mild_identity
    (p : CMParams) {c t x D E F FD R : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (ht : 0 < t) (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hR : 0 ≤ R)
    (hUd : ∀ y, |deriv U y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv U) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv U)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p U V y| ≤ F)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p U V) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p U V)
      (deriv (wholeLineTravelingWaveFlux p U V) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p U V)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p U y| ≤ R)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p U))
    (hgrad_int : IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p U V) x) volume 0 t) :
    U x = paper5MovingFrameHeatOp c t U x +
      (-p.χ) * (∫ r in (0 : ℝ)..t,
        paper5MovingFrameHeatGradOp c r
          (wholeLineTravelingWaveFlux p U V) x) +
      ∫ r in (0 : ℝ)..t,
        paper5MovingFrameHeatOp c r
          (wholeLineCauchyShiftedReaction p U) x := by
  have hsource_cont : Continuous
      (wholeLineTravelingWaveShiftedSource p U V) := by
    unfold wholeLineTravelingWaveShiftedSource
    exact (hfluxd_cont.const_mul (-p.χ)).add hreact_cont
  have hsource_bound : ∀ y,
      |wholeLineTravelingWaveShiftedSource p U V y| ≤ |p.χ| * FD + R := by
    intro y
    unfold wholeLineTravelingWaveShiftedSource
    calc
      |-p.χ * deriv (wholeLineTravelingWaveFlux p U V) y +
          wholeLineCauchyShiftedReaction p U y| ≤
        |-p.χ * deriv (wholeLineTravelingWaveFlux p U V) y| +
          |wholeLineCauchyShiftedReaction p U y| := abs_add_le _ _
      _ ≤ |p.χ| * FD + R := by
        rw [abs_mul, abs_neg]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hfluxd y) (abs_nonneg p.χ))
          (hreact y)
  have hvalue := IsTravelingWave.stationary_mild_identity p hTW hbound hreg ht hD
    (add_nonneg (mul_nonneg (abs_nonneg p.χ) hFD) hR)
    hUd hUdd hUddcont hsource_cont hsource_bound (x := x)
  have hreact_int : IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatOp c r
        (wholeLineCauchyShiftedReaction p U) x) volume 0 t := by
    exact wholeLineCauchyMovingHeatOp_intervalIntegrable
      ht hR hreact_cont hreact
  have hsplit :
      (∫ r in (0 : ℝ)..t,
        paper5MovingFrameHeatOp c r
          (wholeLineTravelingWaveShiftedSource p U V) x) =
      (-p.χ) * (∫ r in (0 : ℝ)..t,
        paper5MovingFrameHeatGradOp c r
          (wholeLineTravelingWaveFlux p U V) x) +
      ∫ r in (0 : ℝ)..t,
        paper5MovingFrameHeatOp c r
          (wholeLineCauchyShiftedReaction p U) x := by
    calc
      _ = ∫ r in (0 : ℝ)..t,
          ((-p.χ) * paper5MovingFrameHeatGradOp c r
              (wholeLineTravelingWaveFlux p U V) x +
            paper5MovingFrameHeatOp c r
              (wholeLineCauchyShiftedReaction p U) x) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with r hr
        rw [Set.uIoc_of_le ht.le] at hr
        exact wholeLineTravelingWaveShiftedSource_movingHeat_eq
          p hr.1 hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont
      _ = _ := by
        rw [intervalIntegral.integral_add (hgrad_int.const_mul (-p.χ))
          hreact_int, intervalIntegral.integral_const_mul]
  have hvalue' : U x = paper5MovingFrameHeatOp c t U x +
      ∫ r in (0 : ℝ)..t,
        paper5MovingFrameHeatOp c r
          (wholeLineTravelingWaveShiftedSource p U V) x := by
    simpa [wholeLineCauchyMovingHeatOp, paper5MovingFrameHeatOp] using hvalue
  rw [hsplit] at hvalue'
  simpa [add_assoc] using hvalue'

/-- Exponentially weighted stationary traveling-wave mild formula.  The
divergence leg retains the zero-order `-eta` term generated by conjugation. -/
theorem IsTravelingWave.stationary_weighted_divergence_mild_identity
    (p : CMParams) {c t x eta D E F FD R : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (ht : 0 < t) (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hR : 0 ≤ R)
    (hUd : ∀ y, |deriv U y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv U) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv U)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p U V y| ≤ F)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p U V) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p U V)
      (deriv (wholeLineTravelingWaveFlux p U V) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p U V)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p U y| ≤ R)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p U))
    (hgrad_int : IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p U V) x) volume 0 t)
    (hflux_grad_int : ∀ r ∈ Set.Ioc (0 : ℝ) t,
      Integrable (fun y : ℝ =>
        deriv (fun z : ℝ => heatKernel r z)
            (x + (c - 2 * eta) * r - y) *
          (Real.exp (eta * y) * wholeLineTravelingWaveFlux p U V y)))
    (hflux_heat_int : ∀ r ∈ Set.Ioc (0 : ℝ) t,
      Integrable (fun y : ℝ =>
        weightedMovingHeatMarkovKernel eta c r x y *
          (Real.exp (eta * y) * wholeLineTravelingWaveFlux p U V y))) :
    Real.exp (eta * x) * U x =
      Real.exp (-t) * weightedMovingHeatEta eta c t
        (fun y => Real.exp (eta * y) * U y) x +
      (-p.χ) * (∫ r in (0 : ℝ)..t,
        Real.exp (-r) *
          (weightedMovingHeatGradientEta eta c r
              (fun y => Real.exp (eta * y) *
                wholeLineTravelingWaveFlux p U V y) x -
            eta * weightedMovingHeatEta eta c r
              (fun y => Real.exp (eta * y) *
                wholeLineTravelingWaveFlux p U V y) x)) +
      ∫ r in (0 : ℝ)..t,
        Real.exp (-r) * weightedMovingHeatEta eta c r
          (fun y => Real.exp (eta * y) *
            wholeLineCauchyShiftedReaction p U y) x := by
  have hdiv := IsTravelingWave.stationary_divergence_mild_identity
    p hTW hbound hreg ht hD hFD hR hUd hUdd hUddcont
      hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont hgrad_int
      (x := x)
  have hhom := exp_mul_movingFrameHeatOp_eq_weightedMovingHeatEta
    ht U x (eta := eta) (c := c)
  have hG : Real.exp (eta * x) *
      (∫ r in (0 : ℝ)..t,
        paper5MovingFrameHeatGradOp c r
          (wholeLineTravelingWaveFlux p U V) x) =
      ∫ r in (0 : ℝ)..t,
        Real.exp (-r) *
          (weightedMovingHeatGradientEta eta c r
              (fun y => Real.exp (eta * y) *
                wholeLineTravelingWaveFlux p U V y) x -
            eta * weightedMovingHeatEta eta c r
              (fun y => Real.exp (eta * y) *
                wholeLineTravelingWaveFlux p U V y) x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume t] with r hr_ne hr
    rw [Set.uIoc_of_le ht.le] at hr
    have hrpos : 0 < r := hr.1
    exact exp_mul_movingFrameHeatGradOp_eq_weightedMovingHeatGradientEta_sub
      hrpos (wholeLineTravelingWaveFlux p U V) x
      (hflux_grad_int r hr) (hflux_heat_int r hr)
  have hRconj : Real.exp (eta * x) *
      (∫ r in (0 : ℝ)..t,
        paper5MovingFrameHeatOp c r
          (wholeLineCauchyShiftedReaction p U) x) =
      ∫ r in (0 : ℝ)..t,
        Real.exp (-r) * weightedMovingHeatEta eta c r
          (fun y => Real.exp (eta * y) *
            wholeLineCauchyShiftedReaction p U y) x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume t] with r hr_ne hr
    rw [Set.uIoc_of_le ht.le] at hr
    exact exp_mul_movingFrameHeatOp_eq_weightedMovingHeatEta
      hr.1 (wholeLineCauchyShiftedReaction p U) x
  rw [hdiv]
  calc
    Real.exp (eta * x) *
        (paper5MovingFrameHeatOp c t U x +
          (-p.χ) * (∫ r in (0 : ℝ)..t,
            paper5MovingFrameHeatGradOp c r
              (wholeLineTravelingWaveFlux p U V) x) +
          ∫ r in (0 : ℝ)..t,
            paper5MovingFrameHeatOp c r
              (wholeLineCauchyShiftedReaction p U) x) =
      Real.exp (eta * x) * paper5MovingFrameHeatOp c t U x +
        (-p.χ) * (Real.exp (eta * x) *
          (∫ r in (0 : ℝ)..t,
            paper5MovingFrameHeatGradOp c r
              (wholeLineTravelingWaveFlux p U V) x)) +
        Real.exp (eta * x) *
          (∫ r in (0 : ℝ)..t,
            paper5MovingFrameHeatOp c r
              (wholeLineCauchyShiftedReaction p U) x) := by ring
    _ = _ := by rw [hhom, hG, hRconj]

/-- The weighted stationary formula rewritten on the same absolute-time
window `[a,a+h]` as the canonical restart. -/
theorem IsTravelingWave.stationary_weighted_divergence_mild_identity_on_window
    (p : CMParams) {a h c x eta D E F FD R : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hh : 0 < h) (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hR : 0 ≤ R)
    (hUd : ∀ y, |deriv U y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv U) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv U)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p U V y| ≤ F)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p U V) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p U V)
      (deriv (wholeLineTravelingWaveFlux p U V) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p U V)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p U y| ≤ R)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p U))
    (hgrad_int : IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p U V) x) volume 0 h)
    (hflux_grad_int : ∀ r ∈ Set.Ioc (0 : ℝ) h,
      Integrable (fun y : ℝ =>
        deriv (fun z : ℝ => heatKernel r z)
            (x + (c - 2 * eta) * r - y) *
          (Real.exp (eta * y) * wholeLineTravelingWaveFlux p U V y)))
    (hflux_heat_int : ∀ r ∈ Set.Ioc (0 : ℝ) h,
      Integrable (fun y : ℝ =>
        weightedMovingHeatMarkovKernel eta c r x y *
          (Real.exp (eta * y) * wholeLineTravelingWaveFlux p U V y))) :
    Real.exp (eta * x) * U x =
      Real.exp (-h) * weightedMovingHeatEta eta c h
        (fun y => Real.exp (eta * y) * U y) x +
      (-p.χ) * (∫ s in a..(a + h),
        Real.exp (-(a + h - s)) *
          (weightedMovingHeatGradientEta eta c (a + h - s)
              (fun y => Real.exp (eta * y) *
                wholeLineTravelingWaveFlux p U V y) x -
            eta * weightedMovingHeatEta eta c (a + h - s)
              (fun y => Real.exp (eta * y) *
                wholeLineTravelingWaveFlux p U V y) x)) +
      ∫ s in a..(a + h),
        Real.exp (-(a + h - s)) *
          weightedMovingHeatEta eta c (a + h - s)
            (fun y => Real.exp (eta * y) *
              wholeLineCauchyShiftedReaction p U y) x := by
  have hlag := IsTravelingWave.stationary_weighted_divergence_mild_identity
    p hTW hbound hreg hh hD hFD hR hUd hUdd hUddcont
      hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont hgrad_int
      hflux_grad_int hflux_heat_int (x := x) (eta := eta)
  let G : ℝ → ℝ := fun r =>
    Real.exp (-r) *
      (weightedMovingHeatGradientEta eta c r
          (fun y => Real.exp (eta * y) *
            wholeLineTravelingWaveFlux p U V y) x -
        eta * weightedMovingHeatEta eta c r
          (fun y => Real.exp (eta * y) *
            wholeLineTravelingWaveFlux p U V y) x)
  let Q : ℝ → ℝ := fun r =>
    Real.exp (-r) * weightedMovingHeatEta eta c r
      (fun y => Real.exp (eta * y) *
        wholeLineCauchyShiftedReaction p U y) x
  have hGchange : (∫ r in (0 : ℝ)..h, G r) =
      ∫ s in a..(a + h), G (a + h - s) := by
    have hchange := intervalIntegral.integral_comp_sub_left
      (a := a) (b := a + h) G (a + h)
    simpa using hchange.symm
  have hQchange : (∫ r in (0 : ℝ)..h, Q r) =
      ∫ s in a..(a + h), Q (a + h - s) := by
    have hchange := intervalIntegral.integral_comp_sub_left
      (a := a) (b := a + h) Q (a + h)
    simpa using hchange.symm
  change Real.exp (eta * x) * U x =
      Real.exp (-h) * weightedMovingHeatEta eta c h
        (fun y => Real.exp (eta * y) * U y) x +
      (-p.χ) * (∫ r in (0 : ℝ)..h, G r) +
      ∫ r in (0 : ℝ)..h, Q r at hlag
  rw [hGchange, hQchange] at hlag
  simpa [G, Q] using hlag

/-- Exact exponentially weighted restart identity for the population
perturbation `W = exp(eta*x) (u-U)`.  Both the canonical solution and the
stationary wave are produced internally; the hypotheses are only the
concrete spatial and time integrability statements needed for linearity of
the whole-line Bochner integrals. -/
theorem paper5WeightedPopulation_restart_identity
    (p : CMParams) {M T a h eta c x D E F FD R : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ha : 0 < a) (hh : 0 < h) (hah : a + h ≤ T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 y ∈
        Set.Icc (0 : ℝ) M)
    {Uw Vw : ℝ → ℝ}
    (hTW : IsTravelingWave p c Uw Vw)
    (hbound : HasWaveUpperTailBound p c Uw)
    (hreg : TravelingWaveRegularity p c Uw Vw)
    (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hR : 0 ≤ R)
    (hUd : ∀ y, |deriv Uw y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv Uw) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv Uw)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p Uw Vw y| ≤ F)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p Uw Vw) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p Uw Vw)
      (deriv (wholeLineTravelingWaveFlux p Uw Vw) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p Uw Vw)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p Uw y| ≤ R)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p Uw))
    (hwave_grad_int : IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p Uw Vw) x) volume 0 h)
    (hcanon_flux_grad_int : ∀ s ∈ Set.Ioc a (a + h),
      Integrable (fun y : ℝ =>
        deriv (fun z : ℝ => heatKernel (a + h - s) z)
            (x + (c - 2 * eta) * (a + h - s) - y) *
          paper5WeightedCanonicalFluxSource p eta c hM hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s y))
    (hcanon_flux_heat_int : ∀ s ∈ Set.Ioc a (a + h),
      Integrable (fun y : ℝ =>
        weightedMovingHeatMarkovKernel eta c (a + h - s) x y *
          paper5WeightedCanonicalFluxSource p eta c hM hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s y))
    (hwave_flux_grad_int : ∀ r ∈ Set.Ioc (0 : ℝ) h,
      Integrable (fun y : ℝ =>
        deriv (fun z : ℝ => heatKernel r z)
            (x + (c - 2 * eta) * r - y) *
          paper5WeightedTravelingWaveFluxSource p eta Uw Vw y))
    (hwave_flux_heat_int : ∀ r ∈ Set.Ioc (0 : ℝ) h,
      Integrable (fun y : ℝ =>
        weightedMovingHeatMarkovKernel eta c r x y *
          paper5WeightedTravelingWaveFluxSource p eta Uw Vw y))
    (hcanon_hom_heat_int : Integrable (fun y : ℝ =>
      weightedMovingHeatMarkovKernel eta c h x y *
        (Real.exp (eta * y) *
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
            ⟨a, ha.le, (le_add_of_nonneg_right hh.le).trans hah⟩).1
              (y + c * a))))
    (hwave_hom_heat_int : Integrable (fun y : ℝ =>
      weightedMovingHeatMarkovKernel eta c h x y *
        (Real.exp (eta * y) * Uw y)))
    (hcanon_react_heat_int : ∀ s ∈ Set.Ioc a (a + h),
      Integrable (fun y : ℝ =>
        weightedMovingHeatMarkovKernel eta c (a + h - s) x y *
          paper5WeightedCanonicalReactionSource p eta c hM hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s y))
    (hwave_react_heat_int : ∀ s ∈ Set.Ioc a (a + h),
      Integrable (fun y : ℝ =>
        weightedMovingHeatMarkovKernel eta c (a + h - s) x y *
          paper5WeightedTravelingWaveReactionSource p eta Uw y))
    (hcanon_flux_time_int : IntervalIntegrable
      (fun s : ℝ => paper5WeightedDivergenceRestartTerm eta c (a + h - s)
        (paper5WeightedCanonicalFluxSource p eta c hM hT
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s) x)
      volume a (a + h))
    (hwave_flux_time_int : IntervalIntegrable
      (fun s : ℝ => paper5WeightedDivergenceRestartTerm eta c (a + h - s)
        (paper5WeightedTravelingWaveFluxSource p eta Uw Vw) x)
      volume a (a + h))
    (hcanon_react_time_int : IntervalIntegrable
      (fun s : ℝ => paper5WeightedValueRestartTerm eta c (a + h - s)
        (paper5WeightedCanonicalReactionSource p eta c hM hT
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s) x)
      volume a (a + h))
    (hwave_react_time_int : IntervalIntegrable
      (fun s : ℝ => paper5WeightedValueRestartTerm eta c (a + h - s)
        (paper5WeightedTravelingWaveReactionSource p eta Uw) x)
      volume a (a + h)) :
    let Uc := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let u := wholeLineCauchyBUCMildFixedPointCoMovingPath
      p hM hT u₀ hsmall c
    paper5WeightedPopulation eta u Uw (a + h) x =
      Real.exp (-h) * weightedMovingHeatEta eta c h
        (paper5WeightedPopulation eta u Uw a) x +
      (-p.χ) * (∫ s in a..(a + h),
        paper5WeightedDivergenceRestartTerm eta c (a + h - s)
          (paper5WeightedFluxDifferenceSource p eta c hM hT Uc Uw Vw s) x) +
      ∫ s in a..(a + h),
        paper5WeightedValueRestartTerm eta c (a + h - s)
          (paper5WeightedReactionDifferenceSource p eta c hM hT Uc Uw s) x := by
  dsimp only
  let Uc : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let u : ℝ → ℝ → ℝ :=
    wholeLineCauchyBUCMildFixedPointCoMovingPath p hM hT u₀ hsmall c
  let za : Set.Icc (0 : ℝ) T :=
    ⟨a, ha.le, (le_add_of_nonneg_right hh.le).trans hah⟩
  let zah : Set.Icc (0 : ℝ) T :=
    ⟨a + h, (add_pos ha hh).le, hah⟩
  let fc : ℝ → ℝ := fun y =>
    Real.exp (eta * y) * (Uc za).1 (y + c * a)
  let fw : ℝ → ℝ := fun y => Real.exp (eta * y) * Uw y
  let Fc : ℝ → ℝ → ℝ := fun s =>
    paper5WeightedCanonicalFluxSource p eta c hM hT Uc s
  let Fw : ℝ → ℝ :=
    paper5WeightedTravelingWaveFluxSource p eta Uw Vw
  let Rc : ℝ → ℝ → ℝ := fun s =>
    paper5WeightedCanonicalReactionSource p eta c hM hT Uc s
  let Rw : ℝ → ℝ :=
    paper5WeightedTravelingWaveReactionSource p eta Uw
  let Gc : ℝ → ℝ := fun s =>
    paper5WeightedDivergenceRestartTerm eta c (a + h - s) (Fc s) x
  let Gw : ℝ → ℝ := fun s =>
    paper5WeightedDivergenceRestartTerm eta c (a + h - s) Fw x
  let Gd : ℝ → ℝ := fun s =>
    paper5WeightedDivergenceRestartTerm eta c (a + h - s)
      (paper5WeightedFluxDifferenceSource p eta c hM hT Uc Uw Vw s) x
  let Qc : ℝ → ℝ := fun s =>
    paper5WeightedValueRestartTerm eta c (a + h - s) (Rc s) x
  let Qw : ℝ → ℝ := fun s =>
    paper5WeightedValueRestartTerm eta c (a + h - s) Rw x
  let Qd : ℝ → ℝ := fun s =>
    paper5WeightedValueRestartTerm eta c (a + h - s)
      (paper5WeightedReactionDifferenceSource p eta c hM hT Uc Uw s) x
  have hcanon :=
    wholeLineCauchyBUCMildFixedPoint_weighted_coMoving_restart_identity
      p hM hT u₀ hsmall ha hh hah hstrip
        (hflux_grad_int := by
          intro s hs
          simpa [Uc, Fc, paper5WeightedCanonicalFluxSource] using
            hcanon_flux_grad_int s hs)
        (hflux_heat_int := by
          intro s hs
          simpa [Uc, Fc, paper5WeightedCanonicalFluxSource] using
            hcanon_flux_heat_int s hs)
        (eta := eta) (c := c) (x := x)
  dsimp only at hcanon
  change Real.exp (eta * x) * (Uc zah).1 (x + c * (a + h)) =
      Real.exp (-h) * weightedMovingHeatEta eta c h fc x +
        (-p.χ) * (∫ s in a..(a + h), Gc s) +
        ∫ s in a..(a + h), Qc s at hcanon
  have hwave :=
    IsTravelingWave.stationary_weighted_divergence_mild_identity_on_window
      p hTW hbound hreg hh hD hFD hR hUd hUdd hUddcont
        hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont hwave_grad_int
        hwave_flux_grad_int hwave_flux_heat_int
        (a := a) (x := x) (eta := eta)
  change Real.exp (eta * x) * Uw x =
      Real.exp (-h) * weightedMovingHeatEta eta c h fw x +
        (-p.χ) * (∫ s in a..(a + h), Gw s) +
        ∫ s in a..(a + h), Qw s at hwave
  have hdelta :
      Real.exp (eta * x) * (Uc zah).1 (x + c * (a + h)) -
          Real.exp (eta * x) * Uw x =
        Real.exp (-h) *
            (weightedMovingHeatEta eta c h fc x -
              weightedMovingHeatEta eta c h fw x) +
          (-p.χ) *
            ((∫ s in a..(a + h), Gc s) -
              ∫ s in a..(a + h), Gw s) +
          ((∫ s in a..(a + h), Qc s) -
            ∫ s in a..(a + h), Qw s) := by
    linear_combination hcanon - hwave
  have hhomlin : weightedMovingHeatEta eta c h (fun y => fc y - fw y) x =
      weightedMovingHeatEta eta c h fc x -
        weightedMovingHeatEta eta c h fw x := by
    apply weightedMovingHeatEta_sub_of_integrable hcanon_hom_heat_int
    simpa [fw] using hwave_hom_heat_int
  have hGpoint : ∀ s ∈ Set.Ioo a (a + h), Gc s - Gw s = Gd s := by
    intro s hs
    have hlag : a + h - s ∈ Set.Ioc (0 : ℝ) h := by
      constructor
      · exact sub_pos.mpr hs.2
      · linarith [hs.1]
    have hgradlin := weightedMovingHeatGradientEta_sub_of_integrable
      (hcanon_flux_grad_int s ⟨hs.1, hs.2.le⟩)
      (hwave_flux_grad_int _ hlag)
    have hheatlin := weightedMovingHeatEta_sub_of_integrable
      (hcanon_flux_heat_int s ⟨hs.1, hs.2.le⟩)
      (hwave_flux_heat_int _ hlag)
    dsimp [Gc, Gw, Gd, Fc, Fw, paper5WeightedDivergenceRestartTerm]
    unfold paper5WeightedFluxDifferenceSource
    rw [hgradlin, hheatlin]
    ring
  have hQpoint : ∀ s ∈ Set.Ioc a (a + h), Qc s - Qw s = Qd s := by
    intro s hs
    have hheatlin := weightedMovingHeatEta_sub_of_integrable
      (hcanon_react_heat_int s hs) (hwave_react_heat_int s hs)
    dsimp [Qc, Qw, Qd, Rc, Rw, Uc, paper5WeightedValueRestartTerm]
    unfold paper5WeightedReactionDifferenceSource
    rw [hheatlin]
    ring
  have hGc_int : IntervalIntegrable Gc volume a (a + h) := by
    simpa [Gc, Fc, Uc] using hcanon_flux_time_int
  have hGw_int : IntervalIntegrable Gw volume a (a + h) := by
    simpa [Gw, Fw] using hwave_flux_time_int
  have hQc_int : IntervalIntegrable Qc volume a (a + h) := by
    simpa [Qc, Rc, Uc] using hcanon_react_time_int
  have hQw_int : IntervalIntegrable Qw volume a (a + h) := by
    simpa [Qw, Rw] using hwave_react_time_int
  have hGsub :
      (∫ s in a..(a + h), Gc s) - ∫ s in a..(a + h), Gw s =
        ∫ s in a..(a + h), Gd s := by
    rw [← intervalIntegral.integral_sub hGc_int hGw_int]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (a + h)] with s hne hs
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hh.le)] at hs
    exact hGpoint s ⟨hs.1, lt_of_le_of_ne hs.2 hne⟩
  have hQsub :
      (∫ s in a..(a + h), Qc s) - ∫ s in a..(a + h), Qw s =
        ∫ s in a..(a + h), Qd s := by
    rw [← intervalIntegral.integral_sub hQc_int hQw_int]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (a + h)] with s hne hs
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hh.le)] at hs
    exact hQpoint s hs
  have ha_mem : a ∈ Set.Icc (0 : ℝ) T :=
    ⟨ha.le, (le_add_of_nonneg_right hh.le).trans hah⟩
  have hah_mem : a + h ∈ Set.Icc (0 : ℝ) T :=
    ⟨(add_pos ha hh).le, hah⟩
  have hWa : paper5WeightedPopulation eta u Uw a = fun y => fc y - fw y := by
    funext y
    simp [paper5WeightedPopulation, u,
      wholeLineCauchyBUCMildFixedPointCoMovingPath, ha_mem, fc, fw, Uc, za]
    ring
  have hWah : paper5WeightedPopulation eta u Uw (a + h) x =
      Real.exp (eta * x) * (Uc zah).1 (x + c * (a + h)) -
        Real.exp (eta * x) * Uw x := by
    simp [paper5WeightedPopulation, u,
      wholeLineCauchyBUCMildFixedPointCoMovingPath, hah_mem, Uc, zah]
    ring
  rw [hWah, hdelta, ← hhomlin, hGsub, hQsub, ← hWa]

/-- Conjugating the physical divergence by the exponential weight produces
the required zero-order `eta * flux` correction. -/
theorem weighted_travelingWave_divergence_conjugation
    (p : CMParams) {eta x : ℝ} {U V : ℝ → ℝ}
    (hflux : DifferentiableAt ℝ (wholeLineTravelingWaveFlux p U V) x) :
    Real.exp (eta * x) *
        (-p.χ * deriv (wholeLineTravelingWaveFlux p U V) x) =
      -p.χ * deriv (fun y => Real.exp (eta * y) *
        wholeLineTravelingWaveFlux p U V y) x +
      p.χ * eta * (Real.exp (eta * x) *
        wholeLineTravelingWaveFlux p U V x) := by
  have hconj := weighted_divergence_conjugation_identity
    (eta := eta) (x := x) hflux
  linear_combination (-p.χ) * hconj

/-! ## Pure-drift value semigroup

The nondivergence perturbation equation uses the principal operator
`partial_xx + (c - 2 * eta) * partial_x`, with no zero-order term.  The
canonical fixed-point construction instead uses the modified heat generator
`partial_xx - 1`.  The factor `exp t` below removes that damping exactly.
This distinction is load-bearing: using `weightedMovingHeatEta` without also
removing its growth would change the four-term lower-order source.
-/

/-- Undamped whole-line heat flow in a frame moving at speed `d`. -/
def wholeLineDriftHeatOp
    (d t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp t * wholeLineCauchyMovingHeatOp d t f x

/-- Positive-time integral realization of the pure-drift heat flow, with the
moving observation point translated onto the input. -/
theorem wholeLineDriftHeatOp_eq_translated_integral
    {d t : ℝ} (ht : 0 < t) (f : ℝ → ℝ) (x : ℝ) :
    wholeLineDriftHeatOp d t f x =
      ∫ y : ℝ, heatKernel t (x - y) * f (y + d * t) := by
  rw [wholeLineDriftHeatOp,
    wholeLineCauchyMovingHeatOp_eq_heatOp_translated_input]
  unfold wholeLineCauchyHeatOp modifiedSemigroup heatSemigroup
  rw [← mul_assoc, ← Real.exp_add]
  simp

/-- The pure-drift heat flow is the zero-growth normalization of the
weighted moving heat operator. -/
theorem wholeLineDriftHeatOp_eq_weightedMovingHeatEta
    {eta c t : ℝ} (f : ℝ → ℝ) (x : ℝ) :
    wholeLineDriftHeatOp (c - 2 * eta) t f x =
      Real.exp (-((eta ^ 2 - c * eta) * t)) *
        weightedMovingHeatEta eta c t f x := by
  unfold wholeLineDriftHeatOp wholeLineCauchyMovingHeatOp
    wholeLineCauchyHeatOp modifiedSemigroup heatSemigroup
    weightedMovingHeatEta weightedMovingHeatGrowth
    weightedMovingHeatMarkovKernel
  calc
    Real.exp t *
        (Real.exp (-t) *
          ∫ y : ℝ, heatKernel t (x + (c - 2 * eta) * t - y) * f y) =
      ∫ y : ℝ, heatKernel t (x + (c - 2 * eta) * t - y) * f y := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
    _ = Real.exp (-((eta ^ 2 - c * eta) * t)) *
        (Real.exp ((eta ^ 2 - c * eta) * t) *
          ∫ y : ℝ, heatKernel t (x + (c - 2 * eta) * t - y) * f y) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp

/-- A varying-datum contraction converges whenever its fixed-datum orbit
and the datum itself converge. -/
theorem metric_tendsto_varying_of_contraction
    {α X : Type*} [PseudoMetricSpace X] {l : Filter α}
    {op : α → X → X} {datum : α → X} {f target : X}
    (hdatum : Tendsto datum l (𝓝 f))
    (hfixed : Tendsto (fun z => op z f) l (𝓝 target))
    (hcontract : ∀ᶠ z in l,
      dist (op z (datum z)) (op z f) ≤ dist (datum z) f) :
    Tendsto (fun z => op z (datum z)) l (𝓝 target) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hdatum_event :=
    (Metric.tendsto_nhds.mp hdatum) (epsilon / 2) (by linarith)
  have hfixed_event :=
    (Metric.tendsto_nhds.mp hfixed) (epsilon / 2) (by linarith)
  filter_upwards [hcontract, hdatum_event, hfixed_event] with z hc hd hfz
  calc
    dist (op z (datum z)) target ≤
        dist (op z (datum z)) (op z f) + dist (op z f) target :=
      dist_triangle _ _ _
    _ ≤ dist (datum z) f + dist (op z f) target :=
      add_le_add hc le_rfl
    _ < epsilon / 2 + epsilon / 2 := add_lt_add hd hfz
    _ = epsilon := by ring

/-- Joint strong continuity of the totalized modified heat flow at lag zero.
The datum may vary in the genuine BUC norm. -/
theorem wholeLineCauchyHeatBUCTotal_tendsto_zero_of_tendsto
    {α : Type*} {l : Filter α} {lag : α → ℝ}
    {datum : α → WholeLineBUC} {f : WholeLineBUC}
    (hlag : Tendsto lag l (𝓝 0))
    (hlag_nonneg : ∀ᶠ z in l, 0 ≤ lag z)
    (hdatum : Tendsto datum l (𝓝 f)) :
    Tendsto
      (fun z => wholeLineCauchyHeatBUCTotal (lag z) (datum z))
      l (𝓝 f) := by
  have hfixed : Tendsto
      (fun z => wholeLineCauchyHeatBUCTotal (lag z) f) l (𝓝 f) :=
    by
      simpa only [Function.comp_apply, wholeLineCauchyHeatBUCTotal_zero] using
        (wholeLineCauchyHeatBUCTotal_continuousAt_zero f).tendsto.comp hlag
  apply metric_tendsto_varying_of_contraction hdatum hfixed
  filter_upwards [hlag_nonneg] with z hz
  exact wholeLineCauchyHeatBUCTotal_dist_le_of_nonneg hz _ _

/-- Joint strong continuity of the totalized modified heat flow at a
strictly positive lag. -/
theorem wholeLineCauchyHeatBUCTotal_tendsto_positive_of_tendsto
    {α : Type*} {l : Filter α} {lag : α → ℝ} {t : ℝ}
    {datum : α → WholeLineBUC} {f : WholeLineBUC}
    (ht : 0 < t) (hlag : Tendsto lag l (𝓝 t))
    (hlag_nonneg : ∀ᶠ z in l, 0 ≤ lag z)
    (hdatum : Tendsto datum l (𝓝 f)) :
    Tendsto
      (fun z => wholeLineCauchyHeatBUCTotal (lag z) (datum z)) l
      (𝓝 (wholeLineCauchyHeatBUCTotal t f)) := by
  have hfixed : Tendsto
      (fun z => wholeLineCauchyHeatBUCTotal (lag z) f) l
      (𝓝 (wholeLineCauchyHeatBUCTotal t f)) :=
    by
      simpa only [Function.comp_apply] using
        (wholeLineCauchyHeatBUCTotal_continuousAt_of_pos ht f).tendsto.comp hlag
  apply metric_tendsto_varying_of_contraction hdatum hfixed
  filter_upwards [hlag_nonneg] with z hz
  exact wholeLineCauchyHeatBUCTotal_dist_le_of_nonneg hz _ _

/-- Totalized BUC realization of the undamped drift heat flow. -/
def wholeLineDriftHeatBUCTotalVal
    (d t : ℝ) (f : WholeLineBUC) (x : ℝ) : ℝ :=
  Real.exp t * (wholeLineCauchyHeatBUCTotal t f).1 (x + d * t)

@[simp] theorem wholeLineDriftHeatBUCTotalVal_zero
    (d : ℝ) (f : WholeLineBUC) (x : ℝ) :
    wholeLineDriftHeatBUCTotalVal d 0 f x = f.1 x := by
  simp [wholeLineDriftHeatBUCTotalVal]

theorem wholeLineDriftHeatBUCTotalVal_of_pos
    {d t : ℝ} (ht : 0 < t) (f : WholeLineBUC) (x : ℝ) :
    wholeLineDriftHeatBUCTotalVal d t f x =
      wholeLineDriftHeatOp d t f.1 x := by
  simp [wholeLineDriftHeatBUCTotalVal, wholeLineDriftHeatOp,
    wholeLineCauchyMovingHeatOp, wholeLineCauchyHeatBUCTotal, ht,
    wholeLineCauchyHeatBUC_apply]

/-- Joint endpoint continuity of the undamped drift heat flow at lag zero. -/
theorem wholeLineDriftHeatBUCTotalVal_tendsto_zero_of_tendsto
    {α : Type*} {l : Filter α} {lag : α → ℝ}
    {datum : α → WholeLineBUC} {f : WholeLineBUC}
    (d x : ℝ) (hlag : Tendsto lag l (𝓝 0))
    (hlag_nonneg : ∀ᶠ z in l, 0 ≤ lag z)
    (hdatum : Tendsto datum l (𝓝 f)) :
    Tendsto
      (fun z => wholeLineDriftHeatBUCTotalVal d (lag z) (datum z) x)
      l (𝓝 (f.1 x)) := by
  have hheat := wholeLineCauchyHeatBUCTotal_tendsto_zero_of_tendsto
    hlag hlag_nonneg hdatum
  have hx : Tendsto (fun z => x + d * lag z) l (𝓝 x) := by
    convert tendsto_const_nhds.add (tendsto_const_nhds.mul hlag) using 1 <;>
      ring
  have heval : Continuous (fun q : WholeLineBUC × ℝ => q.1.1 q.2) := by
    fun_prop
  have heval_lim := (heval.tendsto (f, x)).comp (hheat.prodMk_nhds hx)
  have hexp : Tendsto (fun z => Real.exp (lag z)) l (𝓝 1) := by
    simpa only [Function.comp_apply, Real.exp_zero] using
      (Real.continuous_exp.tendsto 0).comp hlag
  simpa [wholeLineDriftHeatBUCTotalVal] using hexp.mul heval_lim

/-- Joint endpoint continuity of the undamped drift heat flow at a strictly
positive lag. -/
theorem wholeLineDriftHeatBUCTotalVal_tendsto_positive_of_tendsto
    {α : Type*} {l : Filter α} {lag : α → ℝ} {t : ℝ}
    {datum : α → WholeLineBUC} {f : WholeLineBUC}
    (d x : ℝ) (ht : 0 < t) (hlag : Tendsto lag l (𝓝 t))
    (hlag_nonneg : ∀ᶠ z in l, 0 ≤ lag z)
    (hdatum : Tendsto datum l (𝓝 f)) :
    Tendsto
      (fun z => wholeLineDriftHeatBUCTotalVal d (lag z) (datum z) x)
      l (𝓝 (wholeLineDriftHeatBUCTotalVal d t f x)) := by
  have hheat := wholeLineCauchyHeatBUCTotal_tendsto_positive_of_tendsto
    ht hlag hlag_nonneg hdatum
  have hx : Tendsto (fun z => x + d * lag z) l (𝓝 (x + d * t)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hlag)
  have heval : Continuous (fun q : WholeLineBUC × ℝ => q.1.1 q.2) := by
    fun_prop
  have heval_lim :=
    (heval.tendsto (wholeLineCauchyHeatBUCTotal t f, x + d * t)).comp
      (hheat.prodMk_nhds hx)
  have hexp : Tendsto (fun z => Real.exp (lag z)) l (𝓝 (Real.exp t)) :=
    (Real.continuous_exp.tendsto t).comp hlag
  simpa [wholeLineDriftHeatBUCTotalVal] using hexp.mul heval_lim

/-- Generator theorem for the undamped moving heat flow.  All spatial
derivatives are transferred to the bounded `C2` input. -/
theorem wholeLineDriftHeatOp_time_hasDerivAt_of_bounded_C2
    {d : ℝ} {f : ℝ → ℝ} {t x C D E : ℝ}
    (ht : 0 < t) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ∀ y, |f y| ≤ C)
    (hfd : ∀ y, |deriv f y| ≤ D)
    (hfdd : ∀ y, |deriv (deriv f) y| ≤ E)
    (hfderiv : ∀ y, HasDerivAt f (deriv f y) y)
    (hfdderiv : ∀ y, HasDerivAt (deriv f) (deriv (deriv f) y) y)
    (hfdcont : Continuous (deriv f))
    (hfddcont : Continuous (deriv (deriv f))) :
    HasDerivAt (fun s : ℝ => wholeLineDriftHeatOp d s f x)
      (wholeLineDriftHeatOp d t
        (fun y => deriv (deriv f) y + d * deriv f y) x) t := by
  have hmodified :=
    wholeLineCauchyMovingHeatOp_time_hasDerivAt_of_bounded_C2
      (c := d) (f := f) (t := t) (x := x)
      ht hC hD hf hfd hfdd hfderiv hfdderiv hfdcont hfddcont
  have hprod := Real.hasDerivAt_exp t |>.mul hmodified
  have hadd := modifiedSemigroup_add_bounded hfdd
    (fun y => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hfd y) (abs_nonneg d))
    hfddcont.aestronglyMeasurable
    (hfdcont.aestronglyMeasurable.const_mul d) ht (x + d * t)
  have hcmul := modifiedSemigroup_const_mul d (deriv f) t (x + d * t)
  apply hprod.congr_deriv
  have hsource : wholeLineCauchyHeatOp t
      (fun y => deriv (deriv f) y + d * deriv f y) (x + d * t) =
        wholeLineCauchyHeatOp t (deriv (deriv f)) (x + d * t) +
          d * wholeLineCauchyHeatOp t (deriv f) (x + d * t) := by
    unfold wholeLineCauchyHeatOp
    rw [hadd, hcmul]
  unfold wholeLineDriftHeatOp wholeLineCauchyMovingHeatOp
  rw [hsource]
  ring

/-- Whole-line Gaussian integration by parts with both derivatives moved
from the kernel to a bounded `C2` input, stated without the harmless
modified-semigroup damping factor. -/
theorem integral_heatKernel_secondDeriv_mul_eq_integral_mul_secondDeriv
    {f : ℝ → ℝ} {t x C D E : ℝ}
    (ht : 0 < t)
    (hf : ∀ y, |f y| ≤ C)
    (hfd : ∀ y, |deriv f y| ≤ D)
    (hfdd : ∀ y, |deriv (deriv f) y| ≤ E)
    (hfderiv : ∀ y, HasDerivAt f (deriv f y) y)
    (hfdderiv : ∀ y, HasDerivAt (deriv f) (deriv (deriv f) y) y)
    (hfdcont : Continuous (deriv f))
    (hfddcont : Continuous (deriv (deriv f))) :
    (∫ y : ℝ,
        deriv (fun q : ℝ => deriv (fun z : ℝ => heatKernel t z) q)
          (x - y) * f y) =
      ∫ y : ℝ, heatKernel t (x - y) * deriv (deriv f) y := by
  have hbase := wholeLineCauchyHeatHessOp_eq_heatOp_secondDeriv
    (x := x) ht hf hfd hfdd hfderiv hfdderiv hfdcont hfddcont
  unfold wholeLineCauchyHeatHessOp wholeLineCauchyHeatOp
    modifiedSemigroup heatSemigroup at hbase
  have hexp : Real.exp (-t) ≠ 0 := Real.exp_ne_zero _
  apply (mul_left_cancel₀ hexp)
  simpa [MeasureTheory.integral_const_mul, mul_assoc] using hbase

/-- Integrand of the backward pure-drift orbit
`s ↦ P(b-s) (W s) x`, after translating the moving kernel onto the data. -/
private def wholeLineDriftBackwardIntegrand
    (d b x : ℝ) (W : ℝ → ℝ → ℝ) (s y : ℝ) : ℝ :=
  heatKernel (b - s) (x - y) * W s (y + d * (b - s))

/-- Pointwise time derivative of `wholeLineDriftBackwardIntegrand`. -/
private def wholeLineDriftBackwardIntegrandDeriv
    (d b x : ℝ) (W Wt Wx : ℝ → ℝ → ℝ) (s y : ℝ) : ℝ :=
  -deriv
      (fun q : ℝ => deriv (fun z : ℝ => heatKernel (b - s) z) q)
      (x - y) * W s (y + d * (b - s)) +
    heatKernel (b - s) (x - y) *
      (Wt s (y + d * (b - s)) - d * Wx s (y + d * (b - s)))

/-- Pointwise chain rule for the backward drift orbit.  The trajectory is
differentiated jointly in time and space; no derivative of a nonlinear flux
appears. -/
private theorem wholeLineDriftBackwardIntegrand_hasDerivAt
    {d b x s y : ℝ} {W Wt Wx : ℝ → ℝ → ℝ}
    (hsb : s < b)
    (hjoint : HasFDerivAt
      (fun q : ℝ × ℝ => W q.1 q.2)
      (Wt s (y + d * (b - s)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        Wx s (y + d * (b - s)) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (s, y + d * (b - s))) :
    HasDerivAt
      (fun r : ℝ => wholeLineDriftBackwardIntegrand d b x W r y)
      (wholeLineDriftBackwardIntegrandDeriv d b x W Wt Wx s y) s := by
  have hlag : HasDerivAt (fun r : ℝ => b - r) (-1) s := by
    simpa using (hasDerivAt_const s b).sub (hasDerivAt_id s)
  have hker0 := heatKernel_time_hasDerivAt (sub_pos.mpr hsb) (x - y)
  have hker := hker0.comp s hlag
  have hshift : HasDerivAt
      (fun r : ℝ => y + d * (b - r)) (-d) s := by
    have hmul := hlag.const_mul d
    convert (hasDerivAt_const s y).add hmul using 1 <;> ring
  have hpair : HasDerivAt
      (fun r : ℝ => (r, y + d * (b - r))) (1, -d) s :=
    (hasDerivAt_id s).prodMk hshift
  have hdata := hjoint.comp_hasDerivAt
    (f := fun r : ℝ => (r, y + d * (b - r))) (x := s) hpair
  have hprod := hker.mul hdata
  have hfun :
      (fun r : ℝ => wholeLineDriftBackwardIntegrand d b x W r y) =ᶠ[𝓝 s]
        ((fun τ : ℝ => heatKernel τ (x - y)) ∘ (fun r : ℝ => b - r) *
          (fun q : ℝ × ℝ => W q.1 q.2) ∘
            (fun r : ℝ => (r, y + d * (b - r)))) := by
    filter_upwards with r
    rfl
  have hprod' := hprod.congr_of_eventuallyEq hfun
  apply hprod'.congr_deriv
  simp only [wholeLineDriftBackwardIntegrandDeriv,
    Function.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul]
  ring

/-- Backward-orbit derivative for the pure-drift heat semigroup.  The
assumptions are concrete classical regularity and uniform bounds on a finite
open time window.  In particular, the source contains only
`Wt - Wxx - d * Wx`; no spatial derivative of that source is requested. -/
theorem wholeLineDriftBackwardOrbit_hasDerivAt_of_bounded_joint
    {a b d x s CW CWt CWx CWxx : ℝ}
    {W Wt Wx Wxx : ℝ → ℝ → ℝ}
    (has : a < s) (hsb : s < b)
    (hCW : 0 ≤ CW) (hCWt : 0 ≤ CWt) (hCWx : 0 ≤ CWx)
    (hW : ∀ r ∈ Set.Ioo a b, ∀ y, |W r y| ≤ CW)
    (hWt : ∀ r ∈ Set.Ioo a b, ∀ y, |Wt r y| ≤ CWt)
    (hWx : ∀ r ∈ Set.Ioo a b, ∀ y, |Wx r y| ≤ CWx)
    (hWxx : ∀ r ∈ Set.Ioo a b, ∀ y, |Wxx r y| ≤ CWxx)
    (hW_cont : ∀ r ∈ Set.Ioo a b, Continuous (W r))
    (hWt_cont : ∀ r ∈ Set.Ioo a b, Continuous (Wt r))
    (hWx_cont : ∀ r ∈ Set.Ioo a b, Continuous (Wx r))
    (hWxx_cont : ∀ r ∈ Set.Ioo a b, Continuous (Wxx r))
    (hspace1 : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasDerivAt (W r) (Wx r y) y)
    (hspace2 : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasDerivAt (Wx r) (Wxx r y) y)
    (hjoint : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasFDerivAt
        (fun q : ℝ × ℝ => W q.1 q.2)
        (Wt r y • ContinuousLinearMap.fst ℝ ℝ ℝ +
          Wx r y • ContinuousLinearMap.snd ℝ ℝ ℝ)
        (r, y)) :
    HasDerivAt
      (fun r : ℝ => wholeLineDriftHeatOp d (b - r) (W r) x)
      (wholeLineDriftHeatOp d (b - s)
        (fun y => Wt s y - Wxx s y - d * Wx s y) x) s := by
  let tau : ℝ := b - s
  let delta : ℝ := min ((s - a) / 2) (tau / 2)
  let F : ℝ → ℝ → ℝ := wholeLineDriftBackwardIntegrand d b x W
  let F' : ℝ → ℝ → ℝ :=
    wholeLineDriftBackwardIntegrandDeriv d b x W Wt Wx
  let Ch : ℝ := 5 * ((1 / tau) * (1 / Real.sqrt (2 * Real.pi * tau)))
  let Ck : ℝ := 1 / Real.sqrt (2 * Real.pi * tau)
  let C : ℝ := Ch * CW + Ck * (CWt + |d| * CWx)
  let bound : ℝ → ℝ := fun y =>
    C * Real.exp (-(1 / (12 * tau)) * (x - y) ^ 2)
  have htau : 0 < tau := by dsimp [tau]; linarith
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (half_pos (sub_pos.mpr has)) (half_pos htau)
  have hrange : ∀ {r : ℝ}, r ∈ Metric.ball s delta → r ∈ Set.Ioo a b := by
    intro r hr
    have hdist := Metric.mem_ball.mp hr
    rw [Real.dist_eq] at hdist
    have habs := abs_lt.mp hdist
    have hda : delta ≤ (s - a) / 2 := min_le_left _ _
    have hdb : delta ≤ (b - s) / 2 := by
      dsimp [delta, tau]
      exact min_le_right _ _
    constructor <;> linarith
  have hlag_ball : ∀ {r : ℝ}, r ∈ Metric.ball s delta →
      b - r ∈ Metric.ball tau (tau / 2) := by
    intro r hr
    have hdist := Metric.mem_ball.mp hr
    rw [Real.dist_eq] at hdist
    rw [Metric.mem_ball, Real.dist_eq]
    have hdelta_tau : delta ≤ tau / 2 := min_le_right _ _
    calc
      |b - r - tau| = |s - r| := by dsimp [tau]; congr 1; ring
      _ = |r - s| := abs_sub_comm s r
      _ < delta := hdist
      _ ≤ tau / 2 := hdelta_tau
  have hlag_pos : ∀ {r : ℝ}, r ∈ Metric.ball s delta → 0 < b - r := by
    intro r hr
    exact sub_pos.mpr (hrange hr).2
  have hs_mem : s ∈ Set.Ioo a b := ⟨has, hsb⟩
  have hsball : Metric.ball s delta ∈ 𝓝 s :=
    Metric.ball_mem_nhds s hdelta
  have hF_meas : ∀ᶠ r in 𝓝 s, AEStronglyMeasurable (F r) volume := by
    filter_upwards [hsball] with r hr
    have hrI := hrange hr
    change AEStronglyMeasurable
      (fun y : ℝ => heatKernel (b - r) (x - y) *
        W r (y + d * (b - r))) volume
    apply Continuous.aestronglyMeasurable
    exact (by
      have hker : Continuous (fun y : ℝ => heatKernel (b - r) (x - y)) := by
        unfold heatKernel
        fun_prop
      exact hker.mul ((hW_cont r hrI).comp
        (continuous_id.add continuous_const)))
  have hF_int : Integrable (F s) volume := by
    change Integrable (fun y : ℝ => heatKernel tau (x - y) *
      W s (y + d * tau)) volume
    exact heatKernel_mul_bounded_integrable htau x
      (fun y => hW s hs_mem (y + d * tau))
      ((hW_cont s hs_mem).comp
        (continuous_id.add continuous_const)).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (F' s) volume := by
    have hhess : Continuous (fun y : ℝ =>
        deriv (fun q : ℝ => deriv (fun z : ℝ => heatKernel tau z) q)
          (x - y)) :=
      ShenWork.IntervalNeumannFullKernel.continuous_secondDeriv_heatKernel htau |>.comp
        (continuous_const.sub continuous_id)
    have hker : Continuous (fun y : ℝ => heatKernel tau (x - y)) := by
      unfold heatKernel
      fun_prop
    have hshift : Continuous (fun y : ℝ => y + d * tau) :=
      continuous_id.add continuous_const
    dsimp [F', wholeLineDriftBackwardIntegrandDeriv, tau]
    exact ((hhess.neg.mul ((hW_cont s hs_mem).comp hshift)).add
      (hker.mul (((hWt_cont s hs_mem).comp hshift).sub
        (continuous_const.mul ((hWx_cont s hs_mem).comp hshift))))).aestronglyMeasurable
  have hC : 0 ≤ C := by
    dsimp [C, Ch, Ck]
    positivity
  have h_bound :
      ∀ᵐ y ∂volume, ∀ r ∈ Metric.ball s delta, ‖F' r y‖ ≤ bound y := by
    filter_upwards with y r hr
    have hrI := hrange hr
    have hlagb := hlag_ball hr
    have hhess :=
      ShenWork.PaperOne.ConvLeibniz.abs_secondDeriv_heatKernel_local_time_le
        htau hlagb (x - y)
    have hker := abs_heatKernel_local_time_le htau hlagb (x - y)
    have hdx : |d * Wx r (y + d * (b - r))| ≤ |d| * CWx := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hWx r hrI _) (abs_nonneg d)
    have hinterior :
        |Wt r (y + d * (b - r)) - d * Wx r (y + d * (b - r))| ≤
          CWt + |d| * CWx :=
      (abs_sub _ _).trans (add_le_add (hWt r hrI _) hdx)
    have hpoint :
        |-deriv
              (fun q : ℝ => deriv (fun z : ℝ => heatKernel (b - r) z) q)
              (x - y) * W r (y + d * (b - r)) +
            heatKernel (b - r) (x - y) *
              (Wt r (y + d * (b - r)) -
                d * Wx r (y + d * (b - r)))| ≤
          C * Real.exp (-(1 / (12 * tau)) * (x - y) ^ 2) := by
      calc
        _ ≤ |deriv
              (fun q : ℝ => deriv (fun z : ℝ => heatKernel (b - r) z) q)
              (x - y)| * |W r (y + d * (b - r))| +
            |heatKernel (b - r) (x - y)| *
              |Wt r (y + d * (b - r)) -
                d * Wx r (y + d * (b - r))| := by
          simpa [abs_mul] using abs_add_le
            (-deriv
              (fun q : ℝ => deriv (fun z : ℝ => heatKernel (b - r) z) q)
              (x - y) * W r (y + d * (b - r)))
            (heatKernel (b - r) (x - y) *
              (Wt r (y + d * (b - r)) -
                d * Wx r (y + d * (b - r))))
        _ ≤ (Ch * Real.exp (-(1 / (12 * tau)) * (x - y) ^ 2)) * CW +
            (Ck * Real.exp (-(1 / (12 * tau)) * (x - y) ^ 2)) *
              (CWt + |d| * CWx) := by
          exact add_le_add
            (mul_le_mul hhess (hW r hrI _) (abs_nonneg _) (by positivity))
            (mul_le_mul hker hinterior (abs_nonneg _) (by positivity))
        _ = C * Real.exp (-(1 / (12 * tau)) * (x - y) ^ 2) := by
          dsimp [C]
          ring
    rw [Real.norm_eq_abs]
    simpa [F', wholeLineDriftBackwardIntegrandDeriv, bound] using hpoint
  have hbound_int : Integrable bound volume := by
    have hcoef : 0 < 1 / (12 * tau) := by positivity
    dsimp [bound]
    exact
      (ShenWork.PaperOne.ConvLeibniz.integrable_exp_neg_mul_sq_shift
        hcoef x).const_mul C
  have h_diff :
      ∀ᵐ y ∂volume, ∀ r ∈ Metric.ball s delta,
        HasDerivAt (fun q : ℝ => F q y) (F' r y) r := by
    filter_upwards with y r hr
    have hrI := hrange hr
    exact wholeLineDriftBackwardIntegrand_hasDerivAt
      hrI.2 (hjoint r hrI (y + d * (b - r)))
  have hraw :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (bound := bound) (F := F) (F' := F')
      (x₀ := s) (s := Metric.ball s delta)
      hsball hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  have hpath :
      (fun r : ℝ => wholeLineDriftHeatOp d (b - r) (W r) x) =ᶠ[𝓝 s]
        (fun r => ∫ y : ℝ, F r y) := by
    filter_upwards [hsball] with r hr
    simpa [F, wholeLineDriftBackwardIntegrand] using
      wholeLineDriftHeatOp_eq_translated_integral
        (hlag_pos hr) (W r) x
  have horbit := hraw.congr_of_eventuallyEq hpath
  apply horbit.congr_deriv
  let fshift : ℝ → ℝ := fun y => W s (y + d * tau)
  let fxshift : ℝ → ℝ := fun y => Wx s (y + d * tau)
  let fxxshift : ℝ → ℝ := fun y => Wxx s (y + d * tau)
  have hfshift1 : ∀ y, HasDerivAt fshift (fxshift y) y := by
    intro y
    have hadd : HasDerivAt (fun z : ℝ => z + d * tau) 1 y := by
      simpa using (hasDerivAt_id y).add_const (d * tau)
    simpa [fshift, fxshift] using
      (hspace1 s hs_mem (y + d * tau)).comp y hadd
  have hfxshift1 : ∀ y, HasDerivAt fxshift (fxxshift y) y := by
    intro y
    have hadd : HasDerivAt (fun z : ℝ => z + d * tau) 1 y := by
      simpa using (hasDerivAt_id y).add_const (d * tau)
    simpa [fxshift, fxxshift] using
      (hspace2 s hs_mem (y + d * tau)).comp y hadd
  have hderiv_fshift : deriv fshift = fxshift := by
    funext y
    exact (hfshift1 y).deriv
  have hderiv_fxshift : deriv fxshift = fxxshift := by
    funext y
    exact (hfxshift1 y).deriv
  have hderiv2_fshift : deriv (deriv fshift) = fxxshift := by
    rw [hderiv_fshift]
    exact hderiv_fxshift
  have hfshift_cont : Continuous fshift :=
    (hW_cont s hs_mem).comp (continuous_id.add continuous_const)
  have hfxshift_cont : Continuous fxshift :=
    (hWx_cont s hs_mem).comp (continuous_id.add continuous_const)
  have hfxxshift_cont : Continuous fxxshift :=
    (hWxx_cont s hs_mem).comp (continuous_id.add continuous_const)
  have hhess :
      (∫ y : ℝ,
          deriv (fun q : ℝ => deriv (fun z : ℝ => heatKernel tau z) q)
            (x - y) * fshift y) =
        ∫ y : ℝ, heatKernel tau (x - y) * fxxshift y := by
    have hbase :=
      integral_heatKernel_secondDeriv_mul_eq_integral_mul_secondDeriv
        (f := fshift) (t := tau) (x := x)
        (C := CW) (D := CWx) (E := CWxx) htau
        (fun y => hW s hs_mem _)
        (fun y => by rw [hderiv_fshift]; exact hWx s hs_mem _)
        (fun y => by rw [hderiv2_fshift]; exact hWxx s hs_mem _)
        (fun y => by rw [hderiv_fshift]; exact hfshift1 y)
        (fun y => by
          rw [hderiv_fshift, hderiv_fxshift]
          exact hfxshift1 y)
        (by simpa [hderiv_fshift] using hfxshift_cont)
        (by simpa [hderiv2_fshift] using hfxxshift_cont)
    simpa [hderiv2_fshift] using hbase
  let H : ℝ → ℝ := fun y =>
    deriv (fun q : ℝ => deriv (fun z : ℝ => heatKernel tau z) q)
      (x - y) * fshift y
  let Tm : ℝ → ℝ := fun y => heatKernel tau (x - y) * Wt s (y + d * tau)
  let Xm : ℝ → ℝ := fun y => heatKernel tau (x - y) * fxshift y
  let XXm : ℝ → ℝ := fun y => heatKernel tau (x - y) * fxxshift y
  have hH_int : Integrable H volume := by
    have hbase :=
      ShenWork.PaperOne.ConvLeibniz.secondDeriv_heatKernel_mul_bounded_integrable
        htau x (fun y => hW s hs_mem (y + d * tau))
          hfshift_cont.aestronglyMeasurable
    simpa [H, fshift] using hbase
  have hTm_int : Integrable Tm volume := by
    exact heatKernel_mul_bounded_integrable htau x
      (fun y => hWt s hs_mem (y + d * tau))
      (((hWt_cont s hs_mem).comp
        (continuous_id.add continuous_const)).aestronglyMeasurable)
  have hXm_int : Integrable Xm volume := by
    exact heatKernel_mul_bounded_integrable htau x
      (fun y => hWx s hs_mem (y + d * tau))
      hfxshift_cont.aestronglyMeasurable
  have hXXm_int : Integrable XXm volume := by
    exact heatKernel_mul_bounded_integrable htau x
      (fun y => hWxx s hs_mem (y + d * tau))
      hfxxshift_cont.aestronglyMeasurable
  have hFprime_fun : F' s = fun y => -H y + Tm y - d * Xm y := by
    funext y
    simp [F', wholeLineDriftBackwardIntegrandDeriv, H, Tm, Xm,
      fshift, fxshift, tau]
    ring
  have hsource_fun :
      (fun y => heatKernel tau (x - y) *
        ((fun z => Wt s z - Wxx s z - d * Wx s z)
          (y + d * tau))) =
        fun y => Tm y - XXm y - d * Xm y := by
    funext y
    simp [Tm, XXm, Xm, fxshift, fxxshift]
    ring
  have hFprime_integral :
      (∫ y : ℝ, F' s y) =
        -(∫ y : ℝ, H y) + (∫ y : ℝ, Tm y) -
          d * (∫ y : ℝ, Xm y) := by
    rw [hFprime_fun]
    calc
      (∫ y : ℝ, (-H y + Tm y) - d * Xm y) =
          (∫ y : ℝ, -H y + Tm y) - (∫ y : ℝ, d * Xm y) :=
        MeasureTheory.integral_sub (hH_int.neg.add hTm_int)
          (hXm_int.const_mul d)
      _ = (-(∫ y : ℝ, H y) + (∫ y : ℝ, Tm y)) -
          d * (∫ y : ℝ, Xm y) := by
        have hadd : (∫ y : ℝ, -H y + Tm y) =
            (∫ y : ℝ, -H y) + (∫ y : ℝ, Tm y) := by
          simpa only [Pi.neg_apply] using
            MeasureTheory.integral_add hH_int.neg hTm_int
        have hneg : (∫ y : ℝ, -H y) = -(∫ y : ℝ, H y) := by
          simpa only [Pi.neg_apply] using MeasureTheory.integral_neg H
        have hmul : (∫ y : ℝ, d * Xm y) = d * (∫ y : ℝ, Xm y) :=
          MeasureTheory.integral_const_mul d Xm
        rw [hadd, hneg, hmul]
  have hsource_integral :
      (∫ y : ℝ, heatKernel tau (x - y) *
        ((fun z => Wt s z - Wxx s z - d * Wx s z)
          (y + d * tau))) =
        (∫ y : ℝ, Tm y) - (∫ y : ℝ, XXm y) -
          d * (∫ y : ℝ, Xm y) := by
    rw [hsource_fun]
    calc
      (∫ y : ℝ, (Tm y - XXm y) - d * Xm y) =
          (∫ y : ℝ, Tm y - XXm y) - (∫ y : ℝ, d * Xm y) :=
        MeasureTheory.integral_sub (hTm_int.sub hXXm_int)
          (hXm_int.const_mul d)
      _ = ((∫ y : ℝ, Tm y) - (∫ y : ℝ, XXm y)) -
          d * (∫ y : ℝ, Xm y) := by
        rw [MeasureTheory.integral_sub hTm_int hXXm_int,
          MeasureTheory.integral_const_mul]
  rw [wholeLineDriftHeatOp_eq_translated_integral htau]
  rw [hFprime_integral, hsource_integral]
  have hhess' : (∫ y : ℝ, H y) = ∫ y : ℝ, XXm y := by
    simpa [H, XXm] using hhess
  rw [hhess']
  ring

/-- Exact restart identity for the undamped drift heat flow on a positive
time window.  The endpoint hypotheses live in the genuine BUC norm; the
interior hypotheses are the concrete classical bounds used by the backward
orbit generator theorem. -/
theorem wholeLineDrift_restart_identity_of_bounded_joint
    {a b d x CW CWt CWx CWxx : ℝ}
    {W : ℝ → WholeLineBUC} {Wt Wx Wxx : ℝ → ℝ → ℝ}
    (hab : a < b)
    (hW_left : Tendsto W (𝓝[>] a) (𝓝 (W a)))
    (hW_right : Tendsto W (𝓝[<] b) (𝓝 (W b)))
    (hCW : 0 ≤ CW) (hCWt : 0 ≤ CWt) (hCWx : 0 ≤ CWx)
    (hW : ∀ r ∈ Set.Ioo a b, ∀ y, |(W r).1 y| ≤ CW)
    (hWt : ∀ r ∈ Set.Ioo a b, ∀ y, |Wt r y| ≤ CWt)
    (hWx : ∀ r ∈ Set.Ioo a b, ∀ y, |Wx r y| ≤ CWx)
    (hWxx : ∀ r ∈ Set.Ioo a b, ∀ y, |Wxx r y| ≤ CWxx)
    (hWt_cont : ∀ r ∈ Set.Ioo a b, Continuous (Wt r))
    (hWx_cont : ∀ r ∈ Set.Ioo a b, Continuous (Wx r))
    (hWxx_cont : ∀ r ∈ Set.Ioo a b, Continuous (Wxx r))
    (hspace1 : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasDerivAt (W r).1 (Wx r y) y)
    (hspace2 : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasDerivAt (Wx r) (Wxx r y) y)
    (hjoint : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasFDerivAt
        (fun q : ℝ × ℝ => (W q.1).1 q.2)
        (Wt r y • ContinuousLinearMap.fst ℝ ℝ ℝ +
          Wx r y • ContinuousLinearMap.snd ℝ ℝ ℝ)
        (r, y))
    (hint : IntervalIntegrable
      (fun s => wholeLineDriftHeatOp d (b - s)
        (fun y => Wt s y - Wxx s y - d * Wx s y) x)
      volume a b) :
    (W b).1 x = wholeLineDriftHeatOp d (b - a) (W a).1 x +
      ∫ s in a..b, wholeLineDriftHeatOp d (b - s)
        (fun y => Wt s y - Wxx s y - d * Wx s y) x := by
  let path : ℝ → ℝ := fun r =>
    wholeLineDriftHeatOp d (b - r) (W r).1 x
  let totalPath : ℝ → ℝ := fun r =>
    wholeLineDriftHeatBUCTotalVal d (b - r) (W r) x
  let sourcePath : ℝ → ℝ := fun r =>
    wholeLineDriftHeatOp d (b - r)
      (fun y => Wt r y - Wxx r y - d * Wx r y) x
  have hderiv : ∀ r ∈ Set.Ioo a b,
      HasDerivAt path (sourcePath r) r := by
    intro r hr
    exact wholeLineDriftBackwardOrbit_hasDerivAt_of_bounded_joint
      hr.1 hr.2 hCW hCWt hCWx hW hWt hWx hWxx
      (fun q hq => (W q).1.continuous) hWt_cont hWx_cont hWxx_cont
      hspace1 hspace2 hjoint
  have hlag_left : Tendsto (fun r : ℝ => b - r) (𝓝[>] a)
      (𝓝 (b - a)) := by
    exact (continuousAt_const.sub continuousAt_id).continuousWithinAt
  have hlag_left_nonneg : ∀ᶠ r in 𝓝[>] a, 0 ≤ b - r := by
    have hltb : ∀ᶠ r in 𝓝[>] a, r < b := by
      exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Iio_mem_nhds hab)
    filter_upwards [hltb] with r hr
    exact sub_nonneg.mpr hr.le
  have htotal_left : Tendsto totalPath (𝓝[>] a)
      (𝓝 (wholeLineDriftHeatBUCTotalVal d (b - a) (W a) x)) := by
    exact wholeLineDriftHeatBUCTotalVal_tendsto_positive_of_tendsto
      d x (sub_pos.mpr hab) hlag_left hlag_left_nonneg hW_left
  have hpath_total_left : path =ᶠ[𝓝[>] a] totalPath := by
    have hltb : ∀ᶠ r in 𝓝[>] a, r < b := by
      exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Iio_mem_nhds hab)
    filter_upwards [hltb] with r hr
    exact (wholeLineDriftHeatBUCTotalVal_of_pos
      (sub_pos.mpr hr) (W r) x).symm
  have hpath_left : Tendsto path (𝓝[>] a)
      (𝓝 (wholeLineDriftHeatOp d (b - a) (W a).1 x)) := by
    rw [wholeLineDriftHeatBUCTotalVal_of_pos (sub_pos.mpr hab)] at htotal_left
    exact htotal_left.congr' hpath_total_left.symm
  have hlag_right : Tendsto (fun r : ℝ => b - r) (𝓝[<] b)
      (𝓝 0) := by
    simpa only [sub_self] using
      (show Tendsto (fun r : ℝ => b - r) (𝓝[<] b) (𝓝 (b - b)) from
        (continuousAt_const.sub continuousAt_id).continuousWithinAt)
  have hlag_right_nonneg : ∀ᶠ r in 𝓝[<] b, 0 ≤ b - r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact sub_nonneg.mpr hr.le
  have htotal_right : Tendsto totalPath (𝓝[<] b) (𝓝 ((W b).1 x)) := by
    exact wholeLineDriftHeatBUCTotalVal_tendsto_zero_of_tendsto
      d x hlag_right hlag_right_nonneg hW_right
  have hpath_total_right : path =ᶠ[𝓝[<] b] totalPath := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (wholeLineDriftHeatBUCTotalVal_of_pos
      (sub_pos.mpr hr) (W r) x).symm
  have hpath_right : Tendsto path (𝓝[<] b) (𝓝 ((W b).1 x)) :=
    htotal_right.congr' hpath_total_right.symm
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    hab hderiv hint hpath_left hpath_right
  dsimp [path, sourcePath] at hftc
  linarith

#print axioms wholeLineCauchyMovingHeatOp_eq_heatOp_translated_input
#print axioms wholeLineCauchyMovingHeatOp_time_hasDerivAt_of_bounded_C1
#print axioms wholeLineCauchyHeatHessOp_eq_heatOp_secondDeriv
#print axioms wholeLineCauchyMovingHeatOp_time_hasDerivAt_of_bounded_C2
#print axioms wholeLineCauchyMovingHeatBUCTotalVal_continuousAt_zero
#print axioms wholeLineCauchyMovingHeatOp_intervalIntegrable
#print axioms wholeLineCauchyMovingHeatOp_time_hasDerivAt_of_stationary_balance
#print axioms wholeLine_stationary_mild_identity_of_bounded_C2
#print axioms wholeLineCauchyBUCMildFixedPoint_restart_identity
#print axioms wholeLineCauchyBUCMildFixedPoint_coMoving_restart_identity
#print axioms wholeLineCauchyBUCMildFixedPoint_weighted_coMoving_restart_identity
#print axioms weightedMovingHeatEta_sub_of_integrable
#print axioms weightedMovingHeatGradientEta_sub_of_integrable
#print axioms wholeLineTravelingWave_movingGenerator_balance
#print axioms IsTravelingWave.stationary_mild_identity
#print axioms wholeLineTravelingWaveShiftedSource_movingHeat_eq
#print axioms IsTravelingWave.stationary_divergence_mild_identity
#print axioms IsTravelingWave.stationary_weighted_divergence_mild_identity
#print axioms IsTravelingWave.stationary_weighted_divergence_mild_identity_on_window
#print axioms paper5WeightedPopulation_restart_identity
#print axioms weighted_travelingWave_divergence_conjugation
#print axioms wholeLineDriftHeatOp_eq_translated_integral
#print axioms wholeLineDriftHeatOp_eq_weightedMovingHeatEta
#print axioms wholeLineDriftHeatOp_time_hasDerivAt_of_bounded_C2
#print axioms integral_heatKernel_secondDeriv_mul_eq_integral_mul_secondDeriv
#print axioms wholeLineDriftBackwardOrbit_hasDerivAt_of_bounded_joint
#print axioms wholeLineDrift_restart_identity_of_bounded_joint

end ShenWork.Paper1
