import ShenWork.PaperOne.WholeLineMovingFrameGenerator

open MeasureTheory Filter Topology Real Set
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

namespace MovingFrameChainRule

/-- The affine moving-frame curve `s ↦ (s, x + c*s)` has velocity `(1,c)`. -/
theorem affine_curve_hasDerivAt (c x t : ℝ) :
    HasDerivAt (fun s : ℝ => ((s, x + c * s) : ℝ × ℝ)) (1, c) t := by
  have h₁ : HasDerivAt (fun s : ℝ => s) 1 t := by
    simpa using (hasDerivAt_id t)
  have h₂ : HasDerivAt (fun s : ℝ => x + c * s) c t := by
    have hc : HasDerivAt (fun s : ℝ => c * s) c t := by
      simpa using (hasDerivAt_id t).const_mul c
    simpa [add_comm] using hc.const_add x
  exact h₁.prodMk h₂

/-- A differentiable scalar function on `ℝ × ℝ` has Fréchet derivative
`A·fst + B·snd` once its two coordinate restrictions have derivatives `A` and
`B`. -/
theorem hasFDerivAt_of_differentiableAt_of_coord_derivs
    {h : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {A B : ℝ}
    (hdiff : DifferentiableAt ℝ h p)
    (hfst : HasDerivAt (fun s : ℝ => h (s, p.2)) A p.1)
    (hsnd : HasDerivAt (fun y : ℝ => h (p.1, y)) B p.2) :
    HasFDerivAt h
      (A • ContinuousLinearMap.fst ℝ ℝ ℝ +
        B • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  let D : ℝ × ℝ →L[ℝ] ℝ := fderiv ℝ h p
  have hD : HasFDerivAt h D p := hdiff.hasFDerivAt
  have hcurve₁ : HasDerivAt (fun s : ℝ => ((s, p.2) : ℝ × ℝ)) (1, 0) p.1 := by
    exact (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have hcurve₂ : HasDerivAt (fun y : ℝ => ((p.1, y) : ℝ × ℝ)) (0, 1) p.2 := by
    exact (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have hDfst : D (1, 0) = A := by
    have hcomp := hD.comp_hasDerivAt
      (f := fun s : ℝ => ((s, p.2) : ℝ × ℝ)) (x := p.1) hcurve₁
    exact hcomp.unique hfst
  have hDsnd : D (0, 1) = B := by
    have hcomp := hD.comp_hasDerivAt
      (f := fun y : ℝ => ((p.1, y) : ℝ × ℝ)) (x := p.2) hcurve₂
    exact hcomp.unique hsnd
  refine hD.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  have hv :
      v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  calc
    D v = D (v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ))) :=
      congrArg D hv
    _ = v.1 * D ((1 : ℝ), (0 : ℝ)) + v.2 * D ((0 : ℝ), (1 : ℝ)) := by
      rw [map_add, map_smul, map_smul]
      simp
    _ = (A • ContinuousLinearMap.fst ℝ ℝ ℝ +
          B • ContinuousLinearMap.snd ℝ ℝ ℝ) v := by
      rw [hDfst, hDsnd]
      simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
      ring

/-- If `h(s,y)=wholeLineHeatOp s f y` has the stated Fréchet derivative at the
base point, then composing with the affine moving-frame curve gives the desired
one-variable chain rule. -/
theorem movingFrameHeatOp_chainRule_of_hasFDerivAt
    {c : ℝ} {f : ℝ → ℝ} {t x A B : ℝ}
    (hjoint :
      HasFDerivAt
        (fun p : ℝ × ℝ => wholeLineHeatOp p.1 f p.2)
        (A • ContinuousLinearMap.fst ℝ ℝ ℝ +
          B • ContinuousLinearMap.snd ℝ ℝ ℝ)
        (t, x + c * t)) :
    HasDerivAt (fun s : ℝ => movingFrameHeatOp c s f x) (A + c * B) t := by
  have hcurve := affine_curve_hasDerivAt c x t
  have hcomp :=
    hjoint.comp_hasDerivAt
      (f := fun s : ℝ => ((s, x + c * s) : ℝ × ℝ))
      (x := t) hcurve
  have hcomp' :
      HasDerivAt
        (fun s : ℝ => wholeLineHeatOp s f (x + c * s))
        ((A • ContinuousLinearMap.fst ℝ ℝ ℝ +
            B • ContinuousLinearMap.snd ℝ ℝ ℝ) (1, c)) t := by
    simpa [Function.comp_def] using hcomp
  change HasDerivAt (fun s : ℝ => wholeLineHeatOp s f (x + c * s)) (A + c * B) t
  convert hcomp' using 1
  · simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    ring

/-- The exact joint-differentiability datum needed to remove
`MovingFrameHeatOpTimeChainRuleData`. -/
def WholeLineHeatOpJointFDerivData
    (c : ℝ) (f : ℝ → ℝ) (t x : ℝ) : Prop :=
  ∀ A B : ℝ,
    HasDerivAt (fun s : ℝ => wholeLineHeatOp s f (x + c * t)) A t →
      HasDerivAt (fun z : ℝ => wholeLineHeatOp t f z) B (x + c * t) →
        HasFDerivAt
          (fun p : ℝ × ℝ => wholeLineHeatOp p.1 f p.2)
          (A • ContinuousLinearMap.fst ℝ ℝ ℝ +
            B • ContinuousLinearMap.snd ℝ ℝ ℝ)
          (t, x + c * t)

/-- Joint Fréchet differentiability implies the existing moving-frame chain-rule
package. -/
theorem movingFrameHeatOp_chainRuleData_of_jointFDeriv
    {c : ℝ} {f : ℝ → ℝ} {t x : ℝ}
    (hjoint : WholeLineHeatOpJointFDerivData c f t x) :
    MovingFrameHeatOpTimeChainRuleData c f t x := by
  intro A B htime hspace
  exact movingFrameHeatOp_chainRule_of_hasFDerivAt
    (c := c) (f := f) (t := t) (x := x) (A := A) (B := B)
    (hjoint A B htime hspace)

/-- Joint differentiability at the base point is enough to build the exact
joint-Fréchet datum, because the two coordinate derivatives are the two supplied
partials. -/
theorem wholeLineHeatOp_jointFDerivData_of_differentiableAt
    {c : ℝ} {f : ℝ → ℝ} {t x : ℝ}
    (hdiff :
      DifferentiableAt ℝ
        (fun p : ℝ × ℝ => wholeLineHeatOp p.1 f p.2)
        (t, x + c * t)) :
    WholeLineHeatOpJointFDerivData c f t x := by
  intro A B htime hspace
  exact hasFDerivAt_of_differentiableAt_of_coord_derivs
    (h := fun p : ℝ × ℝ => wholeLineHeatOp p.1 f p.2)
    (p := (t, x + c * t)) (A := A) (B := B)
    hdiff htime hspace

/-- Moving-frame chain rule reduced exactly to joint differentiability of the
unshifted two-variable heat operator at the base point. -/
theorem movingFrameHeatOp_chainRule_of_differentiableAt
    {c : ℝ} {f : ℝ → ℝ} {t x A B : ℝ}
    (hdiff :
      DifferentiableAt ℝ
        (fun p : ℝ × ℝ => wholeLineHeatOp p.1 f p.2)
        (t, x + c * t))
    (htime : HasDerivAt (fun s : ℝ => wholeLineHeatOp s f (x + c * t)) A t)
    (hspace : HasDerivAt (fun z : ℝ => wholeLineHeatOp t f z) B (x + c * t)) :
    HasDerivAt (fun s : ℝ => movingFrameHeatOp c s f x) (A + c * B) t := by
  exact (movingFrameHeatOp_chainRuleData_of_jointFDeriv
      (wholeLineHeatOp_jointFDerivData_of_differentiableAt hdiff))
    A B htime hspace

/-- The Gaussian kernel is jointly differentiable in positive time and space
after a fixed spatial translation. -/
theorem heatKernel_time_space_differentiableAt
    {t z y : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ => heatKernel p.1 (p.2 - y)) (t, z) := by
  unfold heatKernel
  fun_prop (disch := positivity)

/-- Kernel-level joint differentiability survives multiplication by a fixed
datum value. -/
theorem heatKernel_time_space_mul_differentiableAt
    {t z y : ℝ} (ht : 0 < t) (a : ℝ) :
    DifferentiableAt ℝ
      (fun p : ℝ × ℝ => heatKernel p.1 (p.2 - y) * a) (t, z) := by
  exact (heatKernel_time_space_differentiableAt (z := z) (y := y) ht).mul
    (differentiableAt_const (c := a))

/-- The remaining analytic frontier: joint differentiability of the
whole-line heat integral at positive time. -/
def WholeLineHeatOpJointDifferentiability
    (f : ℝ → ℝ) (t y : ℝ) : Prop :=
  DifferentiableAt ℝ
    (fun p : ℝ × ℝ => wholeLineHeatOp p.1 f p.2) (t, y)

/-- Bounded-data chain rule once the joint heat-integral differentiability
frontier is supplied. -/
theorem movingFrameHeatOp_chainRule_bounded_of_differentiableAt
    {c : ℝ} {f : ℝ → ℝ} {t x M : ℝ}
    (ht : 0 < t) (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M)
    (hdiff : WholeLineHeatOpJointDifferentiability f t (x + c * t)) :
    HasDerivAt (fun s : ℝ => movingFrameHeatOp c s f x)
      ((deriv (deriv (fun z : ℝ => wholeLineHeatOp t f z)) (x + c * t) -
          wholeLineHeatOp t f (x + c * t)) +
        c * deriv (fun z : ℝ => wholeLineHeatOp t f z) (x + c * t)) t := by
  have htime :=
    ConvLeibniz.wholeLineHeatOp_time_hasDerivAt_of_bounded
      (f := f) (t := t) (x := x + c * t) (M := M) ht hf_meas hf
  have hspace :=
    wholeLineHeatOp_space_hasDerivAt_of_bounded
      (f := f) (t := t) (x := x + c * t) (M := M) ht hf_meas hf
  exact movingFrameHeatOp_chainRule_of_differentiableAt
    (c := c) (f := f) (t := t) (x := x)
    (A := deriv (deriv (fun z : ℝ => wholeLineHeatOp t f z)) (x + c * t) -
      wholeLineHeatOp t f (x + c * t))
    (B := deriv (fun z : ℝ => wholeLineHeatOp t f z) (x + c * t))
    hdiff htime hspace

/-- Moving-frame generator reduced to the single joint-differentiability
frontier for the unshifted whole-line heat integral. -/
theorem movingFrameHeatOp_time_hasDerivAt_of_differentiableAt
    {c : ℝ} {f : ℝ → ℝ} {t x M : ℝ}
    (ht : 0 < t) (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M)
    (hdiff : WholeLineHeatOpJointDifferentiability f t (x + c * t)) :
    HasDerivAt (fun s : ℝ => movingFrameHeatOp c s f x)
      (deriv (deriv (fun z : ℝ => movingFrameHeatOp c t f z)) x +
        c * deriv (fun z : ℝ => movingFrameHeatOp c t f z) x -
          movingFrameHeatOp c t f x) t := by
  exact movingFrameHeatOp_time_hasDerivAt
    (c := c) (f := f) (t := t) (x := x) (M := M)
    ht hf_meas hf
    (movingFrameHeatOp_chainRuleData_of_jointFDeriv
      (wholeLineHeatOp_jointFDerivData_of_differentiableAt hdiff))

/-- Moving-frame generator with the remaining frontier isolated as the concrete
joint Fréchet differentiability of the unshifted heat operator. -/
theorem movingFrameHeatOp_time_hasDerivAt_of_jointFDeriv
    {c : ℝ} {f : ℝ → ℝ} {t x M : ℝ}
    (ht : 0 < t) (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M)
    (hjoint : WholeLineHeatOpJointFDerivData c f t x) :
    HasDerivAt (fun s : ℝ => movingFrameHeatOp c s f x)
      (deriv (deriv (fun z : ℝ => movingFrameHeatOp c t f z)) x +
        c * deriv (fun z : ℝ => movingFrameHeatOp c t f z) x -
          movingFrameHeatOp c t f x) t := by
  exact movingFrameHeatOp_time_hasDerivAt
    (c := c) (f := f) (t := t) (x := x) (M := M)
    ht hf_meas hf (movingFrameHeatOp_chainRuleData_of_jointFDeriv hjoint)

end MovingFrameChainRule

#print axioms MovingFrameChainRule.affine_curve_hasDerivAt
#print axioms MovingFrameChainRule.hasFDerivAt_of_differentiableAt_of_coord_derivs
#print axioms MovingFrameChainRule.movingFrameHeatOp_chainRule_of_hasFDerivAt
#print axioms MovingFrameChainRule.WholeLineHeatOpJointFDerivData
#print axioms MovingFrameChainRule.movingFrameHeatOp_chainRuleData_of_jointFDeriv
#print axioms MovingFrameChainRule.wholeLineHeatOp_jointFDerivData_of_differentiableAt
#print axioms MovingFrameChainRule.movingFrameHeatOp_chainRule_of_differentiableAt
#print axioms MovingFrameChainRule.heatKernel_time_space_differentiableAt
#print axioms MovingFrameChainRule.heatKernel_time_space_mul_differentiableAt
#print axioms MovingFrameChainRule.WholeLineHeatOpJointDifferentiability
#print axioms MovingFrameChainRule.movingFrameHeatOp_chainRule_bounded_of_differentiableAt
#print axioms MovingFrameChainRule.movingFrameHeatOp_time_hasDerivAt_of_jointFDeriv
#print axioms MovingFrameChainRule.movingFrameHeatOp_time_hasDerivAt_of_differentiableAt

end ShenWork.PaperOne
