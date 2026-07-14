import ShenWork.Paper1.WholeLineCauchyBUCHeat
import ShenWork.PDE.IntervalSemigroupUniform

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction

noncomputable section

namespace ShenWork.Paper1

/-!
# Strong continuity at time zero on `BUC(ℝ)`

The raw Gaussian formulas are only used at positive time.  The totalized
operators below take the identity value at nonpositive time.  This file proves
the paper-critical right-continuity at zero in the genuine BUC norm.
-/

theorem heatKernel_continuous {t : ℝ} (_ht : 0 < t) :
    Continuous (heatKernel t) := by
  unfold heatKernel
  fun_prop

theorem abs_mul_heatKernel_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun z : ℝ => |z| * heatKernel t z) := by
  have hb : (0 : ℝ) < 1 / (4 * t) := by positivity
  have hfun : (fun z : ℝ => |z| * heatKernel t z) =
      fun z => 1 / Real.sqrt (4 * Real.pi * t) *
        (|z| * Real.exp (-(1 / (4 * t)) * z ^ 2)) := by
    ext z
    unfold heatKernel
    rw [show -z ^ 2 / (4 * t) = -(1 / (4 * t)) * z ^ 2 by ring]
    ring
  have habs : (fun z : ℝ =>
      1 / Real.sqrt (4 * Real.pi * t) *
        (|z| * Real.exp (-(1 / (4 * t)) * z ^ 2))) =
      fun z => 1 / Real.sqrt (4 * Real.pi * t) *
        ‖z * Real.exp (-(1 / (4 * t)) * z ^ 2)‖ := by
    ext z
    congr 1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  rw [hfun, habs]
  exact (integrable_mul_exp_neg_mul_sq hb).norm.const_mul _

/-- Positive-time unmodified heat flow on `BUC(ℝ)`. -/
def wholeLineHeatBUC (t : ℝ) (ht : 0 < t) (u : WholeLineBUC) :
    WholeLineBUC :=
  kernelConvBUC (heatKernel_continuous ht) (heatKernel_integrable ht) u

@[simp] theorem wholeLineHeatBUC_apply
    (t : ℝ) (ht : 0 < t) (u : WholeLineBUC) (x : ℝ) :
    (wholeLineHeatBUC t ht u).1 x = heatSemigroup t u.1 x := by
  rfl

theorem wholeLineCauchyHeatBUC_eq_smul
    (t : ℝ) (ht : 0 < t) (u : WholeLineBUC) :
    wholeLineCauchyHeatBUC t ht u =
      Real.exp (-t) • wholeLineHeatBUC t ht u := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  simp only [wholeLineCauchyHeatBUC_apply, wholeLineHeatBUC_apply,
    Submodule.coe_smul_of_tower, BoundedContinuousFunction.coe_smul,
    smul_eq_mul]
  rfl

/-- The modified heat flow, totalized by the identity outside positive time. -/
def wholeLineCauchyHeatBUCTotal (t : ℝ) (u : WholeLineBUC) : WholeLineBUC :=
  if ht : 0 < t then wholeLineCauchyHeatBUC t ht u else u

@[simp] theorem wholeLineCauchyHeatBUCTotal_zero (u : WholeLineBUC) :
    wholeLineCauchyHeatBUCTotal 0 u = u := by
  simp [wholeLineCauchyHeatBUCTotal]

@[simp] theorem wholeLineCauchyHeatBUCTotal_of_nonpos
    {t : ℝ} (ht : t ≤ 0) (u : WholeLineBUC) :
    wholeLineCauchyHeatBUCTotal t u = u := by
  simp [wholeLineCauchyHeatBUCTotal, not_lt.mpr ht]

theorem wholeLineHeatBUC_dist_le_of_linear_modulus
    {t A C : ℝ} (ht : 0 < t)
    (u : WholeLineBUC)
    (hmod : ∀ x y : ℝ, |u.1 y - u.1 x| ≤ A + C * |y - x|) :
    dist (wholeLineHeatBUC t ht u) u ≤
      A + C * (4 * t / Real.sqrt (4 * Real.pi * t)) := by
  change dist
      (greenConvBCF (heatKernel_continuous ht) (heatKernel_integrable ht) u.1)
      u.1 ≤ _
  rw [BoundedContinuousFunction.dist_le_iff_of_nonempty]
  intro x
  rw [Real.dist_eq]
  simp only [greenConvBCF_apply]
  rw [kernelConvVal_eq_shift]
  have hshift_int : Integrable (fun z : ℝ => heatKernel t z * u.1 (x - z)) := by
    refine (heatKernel_integrable ht).mul_bdd (c := ‖u.1‖)
      (u.1.continuous.comp (by fun_prop)).aestronglyMeasurable ?_
    exact Eventually.of_forall fun z => by
      simpa [Real.norm_eq_abs] using u.1.norm_coe_le_norm (x - z)
  have hconst_int : Integrable (fun z : ℝ => heatKernel t z * u.1 x) :=
    (heatKernel_integrable ht).mul_const _
  have hrewrite :
      (∫ z : ℝ, heatKernel t z * u.1 (x - z)) - u.1 x =
        ∫ z : ℝ, heatKernel t z * (u.1 (x - z) - u.1 x) := by
    have hxmass : u.1 x = ∫ z : ℝ, heatKernel t z * u.1 x := by
      rw [integral_mul_const, heatKernel_integral_eq_one ht, one_mul]
    calc
      (∫ z : ℝ, heatKernel t z * u.1 (x - z)) - u.1 x =
          (∫ z : ℝ, heatKernel t z * u.1 (x - z)) -
            ∫ z : ℝ, heatKernel t z * u.1 x := by
        exact congrArg
          (fun q : ℝ => (∫ z : ℝ, heatKernel t z * u.1 (x - z)) - q)
          hxmass
      _ = ∫ z : ℝ,
          (heatKernel t z * u.1 (x - z) - heatKernel t z * u.1 x) :=
        (integral_sub hshift_int hconst_int).symm
      _ = ∫ z : ℝ, heatKernel t z * (u.1 (x - z) - u.1 x) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by ring
  have hmajor_int :
      Integrable (fun z : ℝ => heatKernel t z * (A + C * |z|)) := by
    rw [show (fun z : ℝ => heatKernel t z * (A + C * |z|)) =
        fun z : ℝ => A * heatKernel t z + C * (|z| * heatKernel t z) by
      funext z
      ring]
    exact ((heatKernel_integrable ht).const_mul A).add
      ((abs_mul_heatKernel_integrable ht).const_mul C)
  rw [hrewrite]
  calc
    |∫ z : ℝ, heatKernel t z * (u.1 (x - z) - u.1 x)|
        ≤ ∫ z : ℝ, |heatKernel t z * (u.1 (x - z) - u.1 x)| := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (fun z : ℝ => heatKernel t z * (u.1 (x - z) - u.1 x))
    _ ≤ ∫ z : ℝ, heatKernel t z * (A + C * |z|) := by
      apply integral_mono
      · simpa only [mul_sub] using (hshift_int.sub hconst_int).abs
      · exact hmajor_int
      · intro z
        change |heatKernel t z * (u.1 (x - z) - u.1 x)| ≤
          heatKernel t z * (A + C * |z|)
        rw [abs_mul, abs_of_nonneg (heatKernel_nonneg ht z)]
        exact mul_le_mul_of_nonneg_left
          (by simpa [sub_sub] using hmod x (x - z))
          (heatKernel_nonneg ht z)
    _ = A + C * (4 * t / Real.sqrt (4 * Real.pi * t)) := by
      rw [show (fun z : ℝ => heatKernel t z * (A + C * |z|)) =
          fun z : ℝ => A * heatKernel t z + C * (|z| * heatKernel t z) by
        funext z
        ring]
      rw [integral_add, integral_const_mul, integral_const_mul,
        heatKernel_integral_eq_one ht,
        ShenWork.IntervalSemigroupUniform.heatKernel_first_abs_moment ht,
        mul_one]
      · exact (heatKernel_integrable ht).const_mul A
      · exact (abs_mul_heatKernel_integrable ht).const_mul C

theorem heatKernel_first_abs_moment_le_two_sqrt
    {t : ℝ} (ht : 0 < t) :
    4 * t / Real.sqrt (4 * Real.pi * t) ≤ 2 * Real.sqrt t := by
  have h4pit_pos : 0 < 4 * Real.pi * t := by positivity
  have hpi_ge : 4 * t ≤ 4 * Real.pi * t := by
    nlinarith [Real.pi_gt_three]
  have hsqrt4t : Real.sqrt (4 * t) = 2 * Real.sqrt t := by
    have h4t_eq : (4 : ℝ) * t =
        (2 * Real.sqrt t) * (2 * Real.sqrt t) := by
      have := Real.mul_self_sqrt ht.le
      nlinarith
    rw [h4t_eq, Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt t)]
  rw [div_le_iff₀ (Real.sqrt_pos_of_pos h4pit_pos)]
  calc
    4 * t = 2 * Real.sqrt t * Real.sqrt (4 * t) := by
      rw [hsqrt4t]
      nlinarith [Real.mul_self_sqrt ht.le]
    _ ≤ 2 * Real.sqrt t * Real.sqrt (4 * Real.pi * t) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hpi_ge) (by positivity)

/-- The ordinary heat flow, totalized by the identity outside positive time. -/
def wholeLineHeatBUCTotal (t : ℝ) (u : WholeLineBUC) : WholeLineBUC :=
  if ht : 0 < t then wholeLineHeatBUC t ht u else u

@[simp] theorem wholeLineHeatBUCTotal_zero (u : WholeLineBUC) :
    wholeLineHeatBUCTotal 0 u = u := by
  simp [wholeLineHeatBUCTotal]

@[simp] theorem wholeLineHeatBUCTotal_of_nonpos
    {t : ℝ} (ht : t ≤ 0) (u : WholeLineBUC) :
    wholeLineHeatBUCTotal t u = u := by
  simp [wholeLineHeatBUCTotal, not_lt.mpr ht]

theorem wholeLineHeatBUCTotal_continuousAt_zero (u : WholeLineBUC) :
    ContinuousAt (fun t : ℝ => wholeLineHeatBUCTotal t u) 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let N : ℝ := ‖u.1‖
  have hN : 0 ≤ N := norm_nonneg _
  have huc : UniformContinuous (u.1 : ℝ → ℝ) := u.2
  rw [Metric.uniformContinuous_iff] at huc
  obtain ⟨δ, hδ, hδu⟩ := huc (ε / 2) (by linarith)
  let C : ℝ := 2 * N / δ + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hlinmod : ∀ x y : ℝ,
      |u.1 y - u.1 x| ≤ ε / 2 + C * |y - x| := by
    intro x y
    by_cases hclose : dist y x < δ
    · have hsmall := hδu hclose
      rw [Real.dist_eq] at hsmall
      linarith [mul_nonneg hC.le (abs_nonneg (y - x))]
    · have hfar : δ ≤ |y - x| := by
        rw [← Real.dist_eq]
        exact le_of_not_gt hclose
      have hab : |u.1 y - u.1 x| ≤ 2 * N := by
        calc
          |u.1 y - u.1 x| ≤ |u.1 y| + |u.1 x| := abs_sub _ _
          _ ≤ N + N := add_le_add
            (by simpa [N, Real.norm_eq_abs] using u.1.norm_coe_le_norm y)
            (by simpa [N, Real.norm_eq_abs] using u.1.norm_coe_le_norm x)
          _ = 2 * N := by ring
      have hCδ : C * δ = 2 * N + δ := by
        dsimp [C]
        field_simp
      have htail : 2 * N ≤ C * |y - x| := by
        have := mul_le_mul_of_nonneg_left hfar hC.le
        linarith
      linarith
  let τ : ℝ := (ε / (4 * C)) ^ 2
  have hτ : 0 < τ := by
    dsimp [τ]
    positivity
  refine ⟨min τ 1, lt_min hτ zero_lt_one, ?_⟩
  intro t ht0
  rw [wholeLineHeatBUCTotal_zero]
  rw [Real.dist_eq, sub_zero] at ht0
  by_cases ht : 0 < t
  · have htτ : t < τ := by
      rw [abs_of_pos ht] at ht0
      exact lt_of_lt_of_le ht0 (min_le_left _ _)
    have hsqrt : Real.sqrt t < ε / (4 * C) := by
      rw [← Real.sqrt_sq (show (0 : ℝ) ≤ ε / (4 * C) by positivity)]
      exact Real.sqrt_lt_sqrt ht.le htτ
    have htail : C * (4 * t / Real.sqrt (4 * Real.pi * t)) < ε / 2 := by
      calc
        C * (4 * t / Real.sqrt (4 * Real.pi * t))
            ≤ C * (2 * Real.sqrt t) :=
          mul_le_mul_of_nonneg_left
            (heatKernel_first_abs_moment_le_two_sqrt ht) hC.le
        _ < C * (2 * (ε / (4 * C))) :=
          mul_lt_mul_of_pos_left (by linarith) hC
        _ = ε / 2 := by field_simp; ring
    simp only [wholeLineHeatBUCTotal, dif_pos ht]
    exact lt_of_le_of_lt
      (wholeLineHeatBUC_dist_le_of_linear_modulus ht u hlinmod)
      (by linarith)
  · rw [wholeLineHeatBUCTotal_of_nonpos (le_of_not_gt ht)]
    simpa using hε

theorem wholeLineCauchyHeatBUCTotal_eq
    (t : ℝ) (u : WholeLineBUC) :
    wholeLineCauchyHeatBUCTotal t u =
      Real.exp (-(max t 0)) • wholeLineHeatBUCTotal t u := by
  by_cases ht : 0 < t
  · simp only [wholeLineCauchyHeatBUCTotal, wholeLineHeatBUCTotal,
      dif_pos ht, wholeLineCauchyHeatBUC_eq_smul]
    rw [max_eq_left ht.le]
  · have hnonpos : t ≤ 0 := le_of_not_gt ht
    simp [wholeLineCauchyHeatBUCTotal, wholeLineHeatBUCTotal, ht,
      max_eq_right hnonpos]

theorem wholeLineCauchyHeatBUCTotal_continuousAt_zero
    (u : WholeLineBUC) :
    ContinuousAt (fun t : ℝ => wholeLineCauchyHeatBUCTotal t u) 0 := by
  have hmax : Continuous (fun t : ℝ => max t 0) :=
    continuous_id.max continuous_const
  have hscalar : ContinuousAt (fun t : ℝ => Real.exp (-(max t 0))) 0 :=
    Real.continuous_exp.continuousAt.comp' hmax.continuousAt.neg
  rw [show (fun t : ℝ => wholeLineCauchyHeatBUCTotal t u) =
      fun t : ℝ => Real.exp (-(max t 0)) • wholeLineHeatBUCTotal t u by
    funext t
    exact wholeLineCauchyHeatBUCTotal_eq t u]
  exact hscalar.smul (wholeLineHeatBUCTotal_continuousAt_zero u)

section WholeLineCauchyBUCHeatContinuityAxiomAudit

#print axioms wholeLineHeatBUC_dist_le_of_linear_modulus
#print axioms wholeLineHeatBUCTotal_continuousAt_zero
#print axioms wholeLineCauchyHeatBUCTotal_continuousAt_zero

end WholeLineCauchyBUCHeatContinuityAxiomAudit

end ShenWork.Paper1
