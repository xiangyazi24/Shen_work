import ShenWork.Paper1.WholeLineCauchyC2Bootstrap

open Filter Topology MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Whole-line Gaussian semigroup and restart infrastructure

This module proves the actual Gaussian convolution law used by positive-time
restart arguments.  The proof is at the implemented kernel level: complete
the square, evaluate the translated Gaussian integral, and justify the
Fubini swap for bounded continuous data.
-/

private theorem heatKernel_convolution_coeff
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    (1 / Real.sqrt (4 * Real.pi * t)) *
        (1 / Real.sqrt (4 * Real.pi * s)) *
        Real.sqrt (Real.pi / ((t + s) / (4 * t * s))) =
      1 / Real.sqrt (4 * Real.pi * (t + s)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hts : 0 < t + s := add_pos ht hs
  have h1 : 0 < Real.sqrt (4 * Real.pi * t) :=
    Real.sqrt_pos.mpr (by positivity)
  have h2 : 0 < Real.sqrt (4 * Real.pi * s) :=
    Real.sqrt_pos.mpr (by positivity)
  have h3 : 0 < Real.sqrt (Real.pi / ((t + s) / (4 * t * s))) :=
    Real.sqrt_pos.mpr (by positivity)
  have h4 : 0 < Real.sqrt (4 * Real.pi * (t + s)) :=
    Real.sqrt_pos.mpr (by positivity)
  have hsq :
      ((1 / Real.sqrt (4 * Real.pi * t)) *
          (1 / Real.sqrt (4 * Real.pi * s)) *
          Real.sqrt (Real.pi / ((t + s) / (4 * t * s)))) ^ 2 =
        (1 / Real.sqrt (4 * Real.pi * (t + s))) ^ 2 := by
    field_simp [ne_of_gt h1, ne_of_gt h2, ne_of_gt h4]
    rw [sq_sqrt (by positivity), sq_sqrt (by positivity),
      sq_sqrt (by positivity), sq_sqrt (by positivity)]
    field_simp [ne_of_gt ht, ne_of_gt hs, ne_of_gt hts, ne_of_gt hpi]
  nlinarith [mul_pos (mul_pos (one_div_pos.mpr h1) (one_div_pos.mpr h2)) h3,
    one_div_pos.mpr h4]

/-- Convolution of two implemented whole-line heat kernels. -/
theorem heatKernel_convolution_add
    {t s x z : ℝ} (ht : 0 < t) (hs : 0 < s) :
    (∫ y : ℝ, heatKernel t (x - y) * heatKernel s (y - z)) =
      heatKernel (t + s) (x - z) := by
  have hts : 0 < t + s := add_pos ht hs
  let b : ℝ := (t + s) / (4 * t * s)
  let m : ℝ := (s * x + t * z) / (t + s)
  have hb : 0 < b := by dsimp [b]; positivity
  have hquad : ∀ y : ℝ,
      -(x - y) ^ 2 / (4 * t) + -(y - z) ^ 2 / (4 * s) =
        -(x - z) ^ 2 / (4 * (t + s)) - b * (y - m) ^ 2 := by
    intro y
    dsimp [b, m]
    field_simp [ne_of_gt ht, ne_of_gt hs, ne_of_gt hts]
    ring
  let c : ℝ :=
    (1 / Real.sqrt (4 * Real.pi * t)) *
      (1 / Real.sqrt (4 * Real.pi * s)) *
      Real.exp (-(x - z) ^ 2 / (4 * (t + s)))
  have hint :
      (∫ y : ℝ, Real.exp (-b * (y - m) ^ 2)) =
        Real.sqrt (Real.pi / b) := by
    calc
      (∫ y : ℝ, Real.exp (-b * (y - m) ^ 2)) =
          ∫ y : ℝ, Real.exp (-b * y ^ 2) := by
        change (∫ y : ℝ,
          (fun q : ℝ => Real.exp (-b * q ^ 2)) (y - m)) = _
        rw [integral_sub_right_eq_self
          (fun q : ℝ => Real.exp (-b * q ^ 2)) m]
      _ = Real.sqrt (Real.pi / b) := integral_gaussian b
  have hcoeff :
      (1 / Real.sqrt (4 * Real.pi * t)) *
          (1 / Real.sqrt (4 * Real.pi * s)) *
          Real.sqrt (Real.pi / b) =
        1 / Real.sqrt (4 * Real.pi * (t + s)) := by
    simpa [b] using heatKernel_convolution_coeff ht hs
  have hintegrand : ∀ y : ℝ,
      heatKernel t (x - y) * heatKernel s (y - z) =
        c * Real.exp (-b * (y - m) ^ 2) := by
    intro y
    unfold heatKernel
    rw [show
      1 / Real.sqrt (4 * Real.pi * t) *
            Real.exp (-(x - y) ^ 2 / (4 * t)) *
          (1 / Real.sqrt (4 * Real.pi * s) *
            Real.exp (-(y - z) ^ 2 / (4 * s))) =
        (1 / Real.sqrt (4 * Real.pi * t)) *
          (1 / Real.sqrt (4 * Real.pi * s)) *
          (Real.exp (-(x - y) ^ 2 / (4 * t)) *
            Real.exp (-(y - z) ^ 2 / (4 * s))) by ring]
    rw [← Real.exp_add, hquad y]
    rw [show -(x - z) ^ 2 / (4 * (t + s)) - b * (y - m) ^ 2 =
      -(x - z) ^ 2 / (4 * (t + s)) + (-b * (y - m) ^ 2) by ring,
      Real.exp_add]
    dsimp [c]
    ring
  calc
    (∫ y : ℝ, heatKernel t (x - y) * heatKernel s (y - z)) =
        ∫ y : ℝ, c * Real.exp (-b * (y - m) ^ 2) := by
      apply integral_congr_ae
      filter_upwards with y
      exact hintegrand y
    _ = c * Real.sqrt (Real.pi / b) := by
      rw [integral_const_mul, hint]
    _ = heatKernel (t + s) (x - z) := by
      unfold heatKernel
      rw [← hcoeff]
      dsimp [c]
      ring

/-- The implemented heat semigroup satisfies the addition law on bounded
continuous data. -/
theorem heatSemigroup_add_time
    {f : ℝ → ℝ} {M t s x : ℝ}
    (ht : 0 < t) (hs : 0 < s)
    (hfcont : Continuous f) (hf : ∀ z, |f z| ≤ M) :
    heatSemigroup t (heatSemigroup s f) x =
      heatSemigroup (t + s) f x := by
  have hts : 0 < t + s := add_pos ht hs
  let J : ℝ × ℝ → ℝ := fun q =>
    heatKernel t (x - q.1) * heatKernel s (q.1 - q.2) * f q.2
  have hJmeas : AEStronglyMeasurable J (volume.prod volume) := by
    apply Continuous.aestronglyMeasurable
    dsimp [J]
    unfold heatKernel
    fun_prop
  have hJint : Integrable J (volume.prod volume) := by
    refine (integrable_prod_iff' hJmeas).2 ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall fun z => by
        have hbound : ∀ y,
            |heatKernel s (y - z) * f z| ≤
              (1 / Real.sqrt (4 * Real.pi * s)) * |f z| := by
          intro y
          rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hs _)]
          exact mul_le_mul_of_nonneg_right
            (heatKernel_pointwise_bound hs _) (abs_nonneg _)
        have hmeas : AEStronglyMeasurable
            (fun y : ℝ => heatKernel s (y - z) * f z) volume := by
          apply Continuous.aestronglyMeasurable
          unfold heatKernel
          fun_prop
        simpa [J, mul_assoc] using heatKernel_mul_bounded_integrable
          ht x hbound hmeas
    · have heq :
          (fun z : ℝ => ∫ y : ℝ, ‖J (y, z)‖) =
            fun z : ℝ => |f z| * heatKernel (t + s) (x - z) := by
          funext z
          calc
            (∫ y : ℝ, ‖J (y, z)‖) =
                ∫ y : ℝ,
                  |f z| * (heatKernel t (x - y) * heatKernel s (y - z)) := by
              apply integral_congr_ae
              filter_upwards with y
              rw [Real.norm_eq_abs]
              dsimp [J]
              rw [abs_mul, abs_mul,
                abs_of_nonneg (heatKernel_nonneg ht _),
                abs_of_nonneg (heatKernel_nonneg hs _)]
              ring
            _ = |f z| *
                (∫ y : ℝ,
                  heatKernel t (x - y) * heatKernel s (y - z)) := by
              rw [integral_const_mul]
            _ = |f z| * heatKernel (t + s) (x - z) := by
              rw [heatKernel_convolution_add ht hs]
      rw [heq]
      simpa [mul_comm] using heatKernel_mul_bounded_integrable hts x
        (fun z => by simpa using hf z) hfcont.abs.aestronglyMeasurable
  unfold heatSemigroup
  have hswap := MeasureTheory.integral_integral_swap
    (f := fun y z : ℝ => J (y, z)) hJint
  rw [show (∫ y : ℝ, heatKernel t (x - y) *
      (∫ z : ℝ, heatKernel s (y - z) * f z)) =
      ∫ y : ℝ, ∫ z : ℝ, J (y, z) by
    apply integral_congr_ae
    filter_upwards with y
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    dsimp [J]
    ring]
  rw [hswap]
  apply integral_congr_ae
  filter_upwards with z
  have hz : (∫ y : ℝ, J (y, z)) =
      heatKernel (t + s) (x - z) * f z := by
    dsimp [J]
    rw [integral_mul_const, heatKernel_convolution_add ht hs]
  rw [hz]

/-- Addition law for the modified semigroup generated by `Delta-I`. -/
theorem wholeLineCauchyHeatOp_add_time
    {f : ℝ → ℝ} {M t s x : ℝ}
    (ht : 0 < t) (hs : 0 < s)
    (hfcont : Continuous f) (hf : ∀ z, |f z| ≤ M) :
    wholeLineCauchyHeatOp t (wholeLineCauchyHeatOp s f) x =
      wholeLineCauchyHeatOp (t + s) f x := by
  unfold wholeLineCauchyHeatOp modifiedSemigroup
  rw [heatSemigroup_const_mul, heatSemigroup_add_time ht hs hfcont hf]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The modified heat flow satisfies the addition law in the actual BUC phase
space. -/
theorem wholeLineCauchyHeatBUCTotal_add_time
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (u : WholeLineBUC) :
    wholeLineCauchyHeatBUCTotal t
        (wholeLineCauchyHeatBUCTotal s u) =
      wholeLineCauchyHeatBUCTotal (t + s) u := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  simp only [wholeLineCauchyHeatBUCTotal, dif_pos ht, dif_pos hs,
    dif_pos (add_pos ht hs), wholeLineCauchyHeatBUC_apply]
  have hsfun :
      ((wholeLineCauchyHeatBUC s hs u).1 : ℝ → ℝ) =
        wholeLineCauchyHeatOp s u.1 := by
    funext z
    exact wholeLineCauchyHeatBUC_apply s hs u z
  rw [hsfun]
  exact wholeLineCauchyHeatOp_add_time ht hs u.1.continuous
    (fun z => by
      simpa [Real.norm_eq_abs] using u.1.norm_coe_le_norm z)

/-- Applying the modified heat flow after a gradient flow adds the two
positive times.  The integration-by-parts input is stated explicitly because
the source need not be globally integrable. -/
theorem wholeLineCauchyHeatOp_comp_heatGradOp
    {f : ℝ → ℝ} {t s x C D : ℝ}
    (ht : 0 < t) (hs : 0 < s)
    (hf : ∀ y, |f y| ≤ C)
    (hfd : ∀ y, |deriv f y| ≤ D)
    (hfderiv : ∀ y, HasDerivAt f (deriv f y) y)
    (hfdcont : Continuous (deriv f)) :
    wholeLineCauchyHeatOp t
        (fun y => wholeLineCauchyHeatGradOp s f y) x =
      wholeLineCauchyHeatGradOp (t + s) f x := by
  have hsfun :
      (fun y => wholeLineCauchyHeatGradOp s f y) =
        wholeLineCauchyHeatOp s (deriv f) := by
    funext y
    exact wholeLineCauchyHeatGradOp_eq_heatOp_deriv
      hs hf hfd hfderiv hfdcont
  rw [hsfun, wholeLineCauchyHeatOp_add_time ht hs hfdcont hfd]
  exact (wholeLineCauchyHeatGradOp_eq_heatOp_deriv
    (add_pos ht hs) hf hfd hfderiv hfdcont).symm

/-- The positive-time modified heat flow as a continuous linear operator on
the BUC phase space. -/
def wholeLineCauchyHeatBUCCLM (t : ℝ) (ht : 0 < t) :
    WholeLineBUC →L[ℝ] WholeLineBUC :=
  kernelConvBUCCLM (wholeLineModifiedHeatKernel_continuous ht)
    (wholeLineModifiedHeatKernel_integrable ht)

@[simp] theorem wholeLineCauchyHeatBUCCLM_apply
    (t : ℝ) (ht : 0 < t) (u : WholeLineBUC) :
    wholeLineCauchyHeatBUCCLM t ht u = wholeLineCauchyHeatBUC t ht u := by
  rfl

/-- Positive modified heat flow commutes with BUC-valued interval
integration. -/
theorem wholeLineCauchyHeatBUCTotal_intervalIntegral
    {t a b : ℝ} (ht : 0 < t) {F : ℝ → WholeLineBUC}
    (hF : IntervalIntegrable F volume a b) :
    wholeLineCauchyHeatBUCTotal t (∫ s in a..b, F s) =
      ∫ s in a..b, wholeLineCauchyHeatBUCTotal t (F s) := by
  simp only [wholeLineCauchyHeatBUCTotal, dif_pos ht]
  change wholeLineCauchyHeatBUCCLM t ht (∫ s in a..b, F s) =
    ∫ s in a..b, wholeLineCauchyHeatBUCCLM t ht (F s)
  have hcomm :
      (∫ s in a..b, wholeLineCauchyHeatBUCCLM t ht (F s)) =
        wholeLineCauchyHeatBUCCLM t ht (∫ s in a..b, F s) :=
    @ContinuousLinearMap.intervalIntegral_comp_comm
      ℝ WholeLineBUC WholeLineBUC
      WholeLineBUC.normedAddCommGroup inferInstance
      a b volume F
      inferInstance inferInstance WholeLineBUC.normedAddCommGroup
      inferInstance inferInstance
      wholeLineBUCMetricCompleteSpace wholeLineBUCMetricCompleteSpace
      (wholeLineCauchyHeatBUCCLM t ht) hF
  exact hcomm.symm

section WholeLineCauchySemigroupRestartAxiomAudit

#print axioms heatKernel_convolution_add
#print axioms heatSemigroup_add_time
#print axioms wholeLineCauchyHeatOp_add_time
#print axioms wholeLineCauchyHeatBUCTotal_add_time
#print axioms wholeLineCauchyHeatOp_comp_heatGradOp
#print axioms wholeLineCauchyHeatBUCTotal_intervalIntegral

end WholeLineCauchySemigroupRestartAxiomAudit

end ShenWork.Paper1
