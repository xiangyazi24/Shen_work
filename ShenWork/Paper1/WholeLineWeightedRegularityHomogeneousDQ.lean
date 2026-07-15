import ShenWork.Paper1.WholeLineWeightedRegularitySpatialDifference

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

private theorem abs_intervalIntegral_unit_sq_le
    (q : ℝ → ℝ) (hq : Continuous q) :
    |∫ r in (0 : ℝ)..1, q r| ^ 2 ≤
      ∫ r in (0 : ℝ)..1, |q r| ^ 2 := by
  have hJ := (even_two.convexOn_pow :
      ConvexOn ℝ Set.univ (fun z : ℝ => z ^ 2)).map_set_average_le
    (μ := volume) (t := Set.Ioc (0 : ℝ) 1)
    (continuousOn_pow 2) isClosed_univ
    (by simp [Real.volume_Ioc]) (by simp [Real.volume_Ioc])
    (by simp) (hq.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
    (((continuous_pow 2).comp hq).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self)
  have hμ : volume.real (Set.Ioc (0 : ℝ) 1) = 1 := by
    rw [Measure.real, Real.volume_Ioc]
    norm_num
  have hAvg_q :
      (⨍ r in Set.Ioc (0 : ℝ) 1, q r ∂volume) =
        ∫ r in (0 : ℝ)..1, q r := by
    rw [MeasureTheory.setAverage_eq, hμ]
    simp [intervalIntegral.integral_of_le zero_le_one]
  have hAvg_sq :
      (⨍ r in Set.Ioc (0 : ℝ) 1, q r ^ 2 ∂volume) =
        ∫ r in (0 : ℝ)..1, q r ^ 2 := by
    rw [MeasureTheory.setAverage_eq, hμ]
    simp [intervalIntegral.integral_of_le zero_le_one]
  rw [hAvg_q, hAvg_sq] at hJ
  simpa [sq_abs] using hJ

private theorem capWeight_segmentAverage_sq_integrable_and_integral_le
    {eta R h : ℝ} (heta : 0 ≤ eta) {f : ℝ → ℝ}
    (hf : Continuous f)
    (hint : Integrable (fun x : ℝ =>
      capWeight eta R x * |f x| ^ 2)) :
    Integrable (fun x : ℝ => capWeight eta R x *
        |∫ r in (0 : ℝ)..1, f (x + r * h)| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
          |∫ r in (0 : ℝ)..1, f (x + r * h)| ^ 2) ≤
        Real.exp (2 * eta * |h|) *
          ∫ x : ℝ, capWeight eta R x * |f x| ^ 2 := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let F : ℝ × ℝ → ℝ := fun z =>
    capWeight eta R z.1 * |f (z.1 + z.2 * h)| ^ 2
  have hFcont : Continuous F := by
    dsimp only [F]
    exact ((capWeight_continuous eta R).comp continuous_fst).mul
      (((hf.comp (continuous_fst.add (continuous_snd.mul continuous_const))).abs).pow 2)
  have hFmeas : AEStronglyMeasurable F (volume.prod ν) :=
    hFcont.measurable.aestronglyMeasurable
  have hsections : ∀ᵐ r ∂ν,
      Integrable (fun x : ℝ => F (x, r)) volume := by
    rw [show ν = volume.restrict (Set.Ioc (0 : ℝ) 1) by rfl,
      ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun r _ =>
      (capWeight_shift_sq_integrable_and_integral_le
        (d := r * h) heta hf hint).1
  have hinnerMeas : AEStronglyMeasurable
      (fun r : ℝ => ∫ x : ℝ, ‖F (x, r)‖) ν := by
    simpa only [Function.comp_apply, Prod.swap_prod_mk] using
      hFmeas.prod_swap.norm.integral_prod_right'
  have hbase_nonneg : 0 ≤
      ∫ x : ℝ, capWeight eta R x * |f x| ^ 2 :=
    integral_nonneg fun x => mul_nonneg (capWeight_pos eta R x).le (sq_nonneg _)
  have hinnerBound : ∀ᵐ r ∂ν,
      ‖∫ x : ℝ, ‖F (x, r)‖‖ ≤
        Real.exp (2 * eta * |h|) *
          ∫ x : ℝ, capWeight eta R x * |f x| ^ 2 := by
    rw [show ν = volume.restrict (Set.Ioc (0 : ℝ) 1) by rfl,
      ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun r hr => by
      have hs := capWeight_shift_sq_integrable_and_integral_le
        (d := r * h) heta hf hint
      have hrabs : |r * h| ≤ |h| := by
        rw [abs_mul]
        nlinarith [abs_nonneg h, abs_of_nonneg (le_of_lt hr.1), hr.2]
      have hexp : Real.exp (2 * eta * |r * h|) ≤
          Real.exp (2 * eta * |h|) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hrabs (mul_nonneg (by norm_num) heta)
      have hFnorm : (∫ x : ℝ, ‖F (x, r)‖) =
          ∫ x : ℝ, capWeight eta R x * |f (x + r * h)| ^ 2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change ‖capWeight eta R x * |f (x + r * h)| ^ 2‖ =
            capWeight eta R x * |f (x + r * h)| ^ 2
          rw [Real.norm_eq_abs, abs_of_nonneg]
          exact mul_nonneg (capWeight_pos eta R x).le (sq_nonneg _)
      rw [hFnorm, Real.norm_eq_abs, abs_of_nonneg]
      · exact hs.2.trans (mul_le_mul_of_nonneg_right hexp hbase_nonneg)
      · exact integral_nonneg fun x =>
          mul_nonneg (capWeight_pos eta R x).le (sq_nonneg _)
  have hinnerInt : Integrable
      (fun r : ℝ => ∫ x : ℝ, ‖F (x, r)‖) ν := by
    refine Integrable.mono'
      (integrable_const
        (Real.exp (2 * eta * |h|) *
          ∫ x : ℝ, capWeight eta R x * |f x| ^ 2))
      hinnerMeas hinnerBound
  have hprod : Integrable F (volume.prod ν) :=
    (integrable_prod_iff' hFmeas).2 ⟨hsections, hinnerInt⟩
  let B : ℝ → ℝ := fun x => ∫ r, F (x, r) ∂ν
  have hBint : Integrable B volume := by
    exact hprod.integral_prod_left
  have hBpoint : ∀ x,
      B x = capWeight eta R x *
        ∫ r in (0 : ℝ)..1, |f (x + r * h)| ^ 2 := by
    intro x
    dsimp only [B, F, ν]
    rw [intervalIntegral.integral_of_le zero_le_one]
    rw [← integral_const_mul]
  have hpoint : ∀ x,
      capWeight eta R x *
          |∫ r in (0 : ℝ)..1, f (x + r * h)| ^ 2 ≤ B x := by
    intro x
    rw [hBpoint]
    exact mul_le_mul_of_nonneg_left
      (abs_intervalIntegral_unit_sq_le
        (fun r => f (x + r * h)) (hf.comp (by fun_prop)))
      (capWeight_pos eta R x).le
  have htargetMeas : AEStronglyMeasurable
      (fun x : ℝ => capWeight eta R x *
        |∫ r in (0 : ℝ)..1, f (x + r * h)| ^ 2) volume := by
    have hi : Continuous (fun x : ℝ =>
        ∫ r in (0 : ℝ)..1, f (x + r * h)) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun x r : ℝ => f (x + r * h)) (by fun_prop) 0 1
    exact ((capWeight_continuous eta R).mul (hi.abs.pow 2)).aestronglyMeasurable
  have htargetInt : Integrable
      (fun x : ℝ => capWeight eta R x *
        |∫ r in (0 : ℝ)..1, f (x + r * h)| ^ 2) volume := by
    refine Integrable.mono' hBint htargetMeas ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact hpoint x
      · exact mul_nonneg (capWeight_pos eta R x).le (sq_nonneg _)
  refine ⟨htargetInt, (integral_mono htargetInt hBint hpoint).trans ?_⟩
  have hFubini : (∫ x : ℝ, B x) =
      ∫ r, ∫ x : ℝ, F (x, r) ∂volume ∂ν := by
    dsimp only [B]
    exact MeasureTheory.integral_integral_swap hprod
  rw [hFubini]
  have hsectionBound : ∀ᵐ r ∂ν,
      (∫ x : ℝ, F (x, r)) ≤
        Real.exp (2 * eta * |h|) *
          ∫ x : ℝ, capWeight eta R x * |f x| ^ 2 := by
    rw [show ν = volume.restrict (Set.Ioc (0 : ℝ) 1) by rfl,
      ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun r hr => by
      have hs := capWeight_shift_sq_integrable_and_integral_le
        (d := r * h) heta hf hint
      have hrabs : |r * h| ≤ |h| := by
        rw [abs_mul]
        nlinarith [abs_nonneg h, abs_of_nonneg (le_of_lt hr.1), hr.2]
      have hexp : Real.exp (2 * eta * |r * h|) ≤
          Real.exp (2 * eta * |h|) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hrabs (mul_nonneg (by norm_num) heta)
      exact hs.2.trans (mul_le_mul_of_nonneg_right hexp hbase_nonneg)
  have hsectionInt : Integrable (fun r => ∫ x, F (x, r) ∂volume) ν :=
    hprod.integral_prod_right
  let C : ℝ := Real.exp (2 * eta * |h|) *
    ∫ x : ℝ, capWeight eta R x * |f x| ^ 2
  calc
    (∫ r, ∫ x : ℝ, F (x, r) ∂volume ∂ν) ≤
        ∫ _r : ℝ, C ∂ν :=
      integral_mono_ae hsectionInt (integrable_const C)
        (by simpa only [C] using hsectionBound)
    _ = C := by
      simp [ν, C]
    _ = Real.exp (2 * eta * |h|) *
          ∫ x : ℝ, capWeight eta R x * |f x| ^ 2 := rfl

/-- A positive-time moving heat output has cap-weighted spatial difference
quotients controlled by its cap-weighted heat-gradient output.  The quotient
is represented by the segment average of the output gradient; it is not moved
onto the input. -/
theorem capWeight_spatialDifferenceQuotient_movingFrameHeatOp_l2_bounded
    {eta R c t h : ℝ} (heta : 0 ≤ eta) (ht : 0 < t) (hh : h ≠ 0)
    {f : ℝ → ℝ} (hf : IsCUnifBdd f)
    (hcap : Integrable (fun y : ℝ =>
      capWeight eta R y * |f y| ^ 2)) :
    Integrable (fun x : ℝ => capWeight eta R x *
        |spatialDifferenceQuotient h
          (paper5MovingFrameHeatOp c t f) x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h
            (paper5MovingFrameHeatOp c t f) x| ^ 2) ≤
        Real.exp (2 * eta * |h|) *
          ∫ x : ℝ, capWeight eta R x *
            |paper5MovingFrameHeatGradOp c t f x| ^ 2 := by
  rcases hf.2 with ⟨M, hM⟩
  have hfmeas : AEStronglyMeasurable f volume :=
    hf.1.measurable.aestronglyMeasurable
  have hderiv : ∀ x : ℝ,
      HasDerivAt (paper5MovingFrameHeatOp c t f)
        (paper5MovingFrameHeatGradOp c t f x) x := by
    intro x
    have hbase := wholeLineCauchyHeatOp_hasDerivAt
      (f := f) (t := t) (x := x + c * t) (M := M) ht hfmeas hM
    have hinner : HasDerivAt (fun z : ℝ => z + c * t) 1 x := by
      simpa using (hasDerivAt_id x).add_const (c * t)
    simpa [paper5MovingFrameHeatOp, paper5MovingFrameHeatGradOp] using
      hbase.comp x hinner
  have hgradCont : Continuous (paper5MovingFrameHeatGradOp c t f) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hbase := wholeLineCauchyHeatGradOp_hasDerivAt
      (f := f) (t := t) (x := x + c * t) (M := M) ht hfmeas hM
    have hinner : HasDerivAt (fun z : ℝ => z + c * t) 1 x := by
      simpa using (hasDerivAt_id x).add_const (c * t)
    have hcomp := hbase.comp x hinner
    exact (by
      simpa [paper5MovingFrameHeatGradOp] using hcomp.continuousAt)
  have hgradInt := (capWeight_movingFrameHeatGradOp_l2_bounded
    heta ht R c hf.1.measurable hcap).1
  have hseg := capWeight_segmentAverage_sq_integrable_and_integral_le
    (eta := eta) (R := R) (h := h) heta hgradCont hgradInt
  have hquot : ∀ x : ℝ,
      spatialDifferenceQuotient h (paper5MovingFrameHeatOp c t f) x =
        ∫ r in (0 : ℝ)..1,
          paper5MovingFrameHeatGradOp c t f (x + r * h) := by
    intro x
    have hftc := intervalIntegral.integral_unitInterval_deriv_eq_sub
      (f := paper5MovingFrameHeatOp c t f)
      (f' := paper5MovingFrameHeatGradOp c t f)
      (z₀ := x) (z₁ := h)
      ((hgradCont.comp
        (continuous_const.add (continuous_id.smul continuous_const))).continuousOn)
      (fun r _ => hderiv (x + r • h))
    unfold spatialDifferenceQuotient
    have hftc' : h * (∫ r in (0 : ℝ)..1,
        paper5MovingFrameHeatGradOp c t f (x + r * h)) =
        paper5MovingFrameHeatOp c t f (x + h) -
          paper5MovingFrameHeatOp c t f x := by
      simpa [smul_eq_mul] using hftc
    rw [← hftc']
    exact mul_div_cancel_left₀ _ hh
  simpa only [hquot] using hseg

/-- Input-energy form of the homogeneous moving-heat difference-quotient
bound. -/
theorem capWeight_spatialDifferenceQuotient_movingFrameHeatOp_l2_bounded_of_input
    {eta R c t h : ℝ} (heta : 0 ≤ eta) (ht : 0 < t) (hh : h ≠ 0)
    {f : ℝ → ℝ} (hf : IsCUnifBdd f)
    (hcap : Integrable (fun y : ℝ =>
      capWeight eta R y * |f y| ^ 2)) :
    Integrable (fun x : ℝ => capWeight eta R x *
        |spatialDifferenceQuotient h
          (paper5MovingFrameHeatOp c t f) x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h
            (paper5MovingFrameHeatOp c t f) x| ^ 2) ≤
        Real.exp (2 * eta * |h|) *
          (Real.exp (-t) * capHeatGradientSchurMass eta c t) ^ 2 *
            ∫ y : ℝ, capWeight eta R y * |f y| ^ 2 := by
  have hraw := capWeight_spatialDifferenceQuotient_movingFrameHeatOp_l2_bounded
    (eta := eta) (R := R) (c := c) (t := t) (h := h)
    heta ht hh hf hcap
  have hgrad := capWeight_movingFrameHeatGradOp_l2_bounded
    heta ht R c hf.1.measurable hcap
  refine ⟨hraw.1, hraw.2.trans ?_⟩
  calc
    Real.exp (2 * eta * |h|) *
        ∫ x : ℝ, capWeight eta R x *
          |paper5MovingFrameHeatGradOp c t f x| ^ 2 ≤
      Real.exp (2 * eta * |h|) *
        ((Real.exp (-t) * capHeatGradientSchurMass eta c t) ^ 2 *
          ∫ y : ℝ, capWeight eta R y * |f y| ^ 2) :=
      mul_le_mul_of_nonneg_left hgrad.2 (Real.exp_nonneg _)
    _ = Real.exp (2 * eta * |h|) *
          (Real.exp (-t) * capHeatGradientSchurMass eta c t) ^ 2 *
            ∫ y : ℝ, capWeight eta R y * |f y| ^ 2 := by ring

#print axioms capWeight_spatialDifferenceQuotient_movingFrameHeatOp_l2_bounded
#print axioms capWeight_spatialDifferenceQuotient_movingFrameHeatOp_l2_bounded_of_input

end ShenWork.Paper1
