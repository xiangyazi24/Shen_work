/-
  ShenWork/Paper2/IntervalConjugateKernelJointMeas.lean

  Joint (s,y)-parameter measurability of the lagged conjugate kernel operator
  `s ↦ B_N(t−s)(Q s) x` as a function of `((t,x),s)`, plus the resulting joint
  measurability of the conjugate Duhamel map.  This is the conjugate-kernel
  analogue of the gradient-route
  `intervalFullSemigroupOperator_deriv_s_param_joint_measurable`.

  Bridge: `B_N(τ) Q x = −∫ DerivSeries(τ, y, x)·Q(y) dy`, using the kernel
  symmetry `∂ᵧK(τ,x,y) = ∂_z K(τ,z,x)|_{z=y} = DerivSeries(τ,y,x)` (τ>0), and
  both sides vanish for `τ ≤ 0`.  `DerivSeries` joint measurability is the
  public atom `intervalNeumannFullKernelDerivSeries_joint_measurable`.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New names only.
-/
import ShenWork.Paper2.IntervalConjugateChemFluxIntegrable
import ShenWork.Paper2.IntervalBFormBNDualityAvailableFrontier
import ShenWork.Paper2.IntervalBFormCron2BNDuality

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.IntervalConjugateKernelJointMeas

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator intervalConjugateKernelOperator_abs_le)
open ShenWork.HeatKernelGradientEstimates (heatGradientLinftyLinftyConstant)
open ShenWork.IntervalNeumannFullKernel
  (intervalNeumannFullKernelDerivSeries
   intervalNeumannFullKernelDerivSeries_joint_measurable
   intervalNeumannFullKernelDerivSeries_eq_deriv_fst)

/-- `DerivSeries τ y x = 0` when `τ ≤ 0` (each lattice `deriv` of the
zero heat kernel vanishes). -/
theorem intervalNeumannFullKernelDerivSeries_eq_zero_of_nonpos
    {τ : ℝ} (hτ : τ ≤ 0) (y x : ℝ) :
    intervalNeumannFullKernelDerivSeries τ y x = 0 := by
  have hderiv : deriv (fun z : ℝ => heatKernel τ z) = fun _ : ℝ => (0 : ℝ) := by
    have hz : (fun z : ℝ => heatKernel τ z) = fun _ : ℝ => (0 : ℝ) := by
      funext z; exact heatKernel_of_nonpos hτ z
    rw [hz, deriv_const']
  unfold intervalNeumannFullKernelDerivSeries
  rw [hderiv]
  simp

/-- Bridge: the conjugate kernel operator is the negative `DerivSeries`-weighted
integral, valid for all `τ` (for `τ ≤ 0` both sides are the integral of `0`). -/
theorem intervalConjugateKernelOperator_eq_neg_derivSeries_integral
    (τ : ℝ) (Q : ℝ → ℝ) (x : ℝ) :
    intervalConjugateKernelOperator τ Q x
      = -∫ y, intervalNeumannFullKernelDerivSeries τ y x * Q y ∂ intervalMeasure 1 := by
  unfold intervalConjugateKernelOperator
  congr 1
  apply MeasureTheory.integral_congr_ae
  refine Filter.Eventually.of_forall fun y => ?_
  show deriv (fun y' : ℝ => intervalNeumannFullKernel τ x y') y * Q y
      = intervalNeumannFullKernelDerivSeries τ y x * Q y
  rcases lt_or_ge 0 τ with hτ | hτ
  · have hswap :
        deriv (fun y' : ℝ => intervalNeumannFullKernel τ x y') y
          = deriv (fun z : ℝ => intervalNeumannFullKernel τ z x) y :=
      ShenWork.IntervalNeumannFullKernel.deriv_intervalNeumannFullKernel_snd_eq_fst_swap
        hτ x y
    rw [hswap, ← intervalNeumannFullKernelDerivSeries_eq_deriv_fst hτ y x]
  · have hzero : deriv (fun y' : ℝ => intervalNeumannFullKernel τ x y') y = 0 := by
      have hk : (fun y' : ℝ => intervalNeumannFullKernel τ x y') = fun _ : ℝ => (0 : ℝ) := by
        funext y'
        simp only [intervalNeumannFullKernel]
        rw [show (fun k : ℤ => heatKernel τ (x - y' + 2 * (k : ℝ))
              + heatKernel τ (x + y' + 2 * (k : ℝ))) = fun _ : ℤ => (0 : ℝ) from by
          funext k; rw [heatKernel_of_nonpos hτ, heatKernel_of_nonpos hτ, add_zero]]
        exact tsum_zero
      rw [hk, deriv_const]
    rw [hzero, intervalNeumannFullKernelDerivSeries_eq_zero_of_nonpos hτ y x]

/-- **Joint measurability of the lagged conjugate-kernel operator over `((t,x),s)`.**
For a jointly `(s,y)`-measurable source family `F`, the map
`r ↦ B_N(r.1.1 − r.2)(F r.2) r.1.2` is `Measurable`. -/
theorem intervalConjugateKernelOperator_s_param_joint_measurable
    {F : ℝ → ℝ → ℝ} (hF : Measurable (Function.uncurry F)) :
    Measurable (fun r : (ℝ × ℝ) × ℝ =>
      intervalConjugateKernelOperator (r.1.1 - r.2) (F r.2) r.1.2) := by
  set Ks : (ℝ × ℝ) × ℝ → ℝ := fun q =>
    intervalNeumannFullKernelDerivSeries q.1.1 q.1.2 q.2 with hKs
  have hKs_meas : Measurable Ks := by
    simpa [Ks] using intervalNeumannFullKernelDerivSeries_joint_measurable
  -- integrand `((t,x),s,y) ↦ DerivSeries(t-s, y, x)·F s y`
  have hprod : Measurable (fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
      Ks ((q.1.1.1 - q.1.2, q.2), q.1.1.2) * F q.1.2 q.2) := by
    have hK : Measurable (fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
        Ks ((q.1.1.1 - q.1.2, q.2), q.1.1.2)) :=
      hKs_meas.comp
        (((measurable_fst.fst.fst.sub measurable_fst.snd).prodMk measurable_snd).prodMk
          measurable_fst.fst.snd)
    have hsrc : Measurable (fun q : ((ℝ × ℝ) × ℝ) × ℝ => F q.1.2 q.2) :=
      hF.comp (measurable_fst.snd.prodMk measurable_snd)
    exact hK.mul hsrc
  have hI : StronglyMeasurable (fun r : (ℝ × ℝ) × ℝ =>
      ∫ y, Ks ((r.1.1 - r.2, y), r.1.2) * F r.2 y ∂(intervalMeasure 1)) :=
    MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := intervalMeasure 1) hprod.stronglyMeasurable
  have hD : Measurable (fun r : (ℝ × ℝ) × ℝ =>
      ∫ y, Ks ((r.1.1 - r.2, y), r.1.2) * F r.2 y ∂(intervalMeasure 1)) := hI.measurable
  have h_eq :
      (fun r : (ℝ × ℝ) × ℝ =>
        intervalConjugateKernelOperator (r.1.1 - r.2) (F r.2) r.1.2)
        = fun r : (ℝ × ℝ) × ℝ =>
          -∫ y, Ks ((r.1.1 - r.2, y), r.1.2) * F r.2 y ∂(intervalMeasure 1) := by
    funext r
    rw [intervalConjugateKernelOperator_eq_neg_derivSeries_integral]
  rw [h_eq]
  exact hD.neg

/-- Continuity in the *third* argument of `DerivSeries τ y x` on `[0,1]`
(the conjugate-leg analogue of `continuousOn_deriv_..._fst_in_x`). -/
theorem continuousOn_intervalNeumannFullKernelDerivSeries_in_x
    {τ : ℝ} (hτ : 0 < τ) {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousOn (fun x : ℝ => intervalNeumannFullKernelDerivSeries τ y x)
      (Set.Icc (0 : ℝ) 1) := by
  have hcd := continuous_deriv_heatKernel hτ
  have hfun : (fun x : ℝ => intervalNeumannFullKernelDerivSeries τ y x)
      = fun x : ℝ =>
          (∑' k : ℤ, deriv (fun z : ℝ => heatKernel τ z) (y - x + 2 * (k : ℝ))) +
          (∑' k : ℤ, deriv (fun z : ℝ => heatKernel τ z) (y + x + 2 * (k : ℝ))) := by
    funext x; rfl
  rw [hfun]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_tsum (fun k => (hcd.comp (by fun_prop)).continuousOn)
      (summable_heatGradWindowBound hτ 0 1) (fun k x hx => ?_)
    rw [Real.norm_eq_abs]
    refine abs_deriv_heatKernel_le_windowShift hτ 0 1 k ?_
    rw [show y - x + 2 * (k : ℝ) - (0 + 2 * (k : ℝ)) = y - x by ring]
    exact abs_le.mpr ⟨by linarith [hx.2, hy.1], by linarith [hx.1, hy.2]⟩
  · refine continuousOn_tsum (fun k => (hcd.comp (by fun_prop)).continuousOn)
      (summable_heatGradWindowBound hτ 0 2) (fun k x hx => ?_)
    rw [Real.norm_eq_abs]
    refine abs_deriv_heatKernel_le_windowShift hτ 0 2 k ?_
    rw [show y + x + 2 * (k : ℝ) - (0 + 2 * (k : ℝ)) = y + x by ring]
    exact abs_le.mpr ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩

/-- **Continuity in `x` of the conjugate kernel operator** for a bounded
integrable source `Q` (`τ > 0`).  This is the conjugate analogue of
`intervalFullSemigroupOperator_deriv_continuous_of_bounded`. -/
theorem intervalConjugateKernelOperator_continuous_of_bounded
    {τ : ℝ} (hτ : 0 < τ) {Q : ℝ → ℝ} {CQ : ℝ}
    (hQ_int : Integrable Q (intervalMeasure 1)) (hQ_bound : ∀ y, |Q y| ≤ CQ) :
    Continuous (fun x : intervalDomainPoint =>
      intervalConjugateKernelOperator τ Q x.1) := by
  haveI : IsFiniteMeasure (intervalMeasure 1) :=
    ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
  have hCQ : 0 ≤ CQ := le_trans (abs_nonneg (Q 0)) (hQ_bound 0)
  set B : ℝ := ∑' k : ℤ,
    (heatGradWindowBound τ 0 2 k + heatGradWindowBound τ 0 2 k) with hBdef
  have hB_nn : 0 ≤ B := by
    rw [hBdef]
    exact tsum_nonneg fun k => by
      unfold heatGradWindowBound heatGradPointwiseBound; positivity
  have hcont_int :
      Continuous (fun x : intervalDomainPoint =>
        ∫ y, intervalNeumannFullKernelDerivSeries τ y x.1 * Q y ∂(intervalMeasure 1)) := by
    refine MeasureTheory.continuous_of_dominated
      (μ := intervalMeasure 1)
      (F := fun x : intervalDomainPoint => fun y : ℝ =>
        intervalNeumannFullKernelDerivSeries τ y x.1 * Q y)
      (bound := fun _ : ℝ => B * CQ) ?meas ?bound ?bint ?cont
    · intro x
      have hKy : AEStronglyMeasurable
          (fun y : ℝ => intervalNeumannFullKernelDerivSeries τ y x.1) (intervalMeasure 1) := by
        have hm : Measurable (fun y : ℝ => intervalNeumannFullKernelDerivSeries τ y x.1) :=
          (intervalNeumannFullKernelDerivSeries_joint_measurable).comp
            ((measurable_const.prodMk measurable_id).prodMk measurable_const)
        exact hm.aestronglyMeasurable
      exact hKy.mul hQ_int.aestronglyMeasurable
    · intro x
      change ∀ᵐ y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        ‖intervalNeumannFullKernelDerivSeries τ y x.1 * Q y‖ ≤ B * CQ
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall fun y hy => ?_
      rw [Real.norm_eq_abs, abs_mul]
      have hx_abs : |x.1| ≤ 1 :=
        abs_le.mpr ⟨by linarith [x.2.1], by linarith [x.2.2]⟩
      have hy_abs : |y| ≤ 1 :=
        abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have hKbound : |intervalNeumannFullKernelDerivSeries τ y x.1| ≤ B := by
        rw [intervalNeumannFullKernelDerivSeries_eq_deriv_fst hτ y x.1]
        simpa [hBdef] using
          ShenWork.IntervalNeumannFullKernel.abs_deriv_intervalNeumannFullKernel_fst_le_const
            (t := τ) hτ (0 : ℝ) (z := y) (y := x.1) (by simpa using hy_abs) hx_abs
      exact mul_le_mul hKbound (hQ_bound y) (abs_nonneg _) hB_nn
    · exact integrable_const _
    · change ∀ᵐ y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        Continuous (fun x : intervalDomainPoint =>
          intervalNeumannFullKernelDerivSeries τ y x.1 * Q y)
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hcx : Continuous (fun x : intervalDomainPoint =>
          intervalNeumannFullKernelDerivSeries τ y x.1) := by
        change Continuous (Set.restrict (Set.Icc (0 : ℝ) 1)
          (fun x : ℝ => intervalNeumannFullKernelDerivSeries τ y x))
        exact continuousOn_iff_continuous_restrict.mp
          (continuousOn_intervalNeumannFullKernelDerivSeries_in_x hτ hy)
      exact hcx.mul continuous_const
  have hrepr :
      (fun x : intervalDomainPoint => intervalConjugateKernelOperator τ Q x.1) =
        fun x : intervalDomainPoint =>
          -∫ y, intervalNeumannFullKernelDerivSeries τ y x.1 * Q y ∂(intervalMeasure 1) := by
    funext x
    exact intervalConjugateKernelOperator_eq_neg_derivSeries_integral τ Q x.1
  rw [hrepr]
  exact hcont_int.neg

end ShenWork.IntervalConjugateKernelJointMeas
