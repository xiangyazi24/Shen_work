/-
  Scalar regularity atoms for positive-part truncations.

  If a differentiable real function crosses zero transversally, the crossing
  is isolated.  Hence the set of transversal zeros on an interval is
  countable, and `positivePart ∘ f` is differentiable away from that set.
-/

import ShenWork.Paper2.IntervalBFormPositiveDatumNegPartFrontier

open Filter Set Topology

noncomputable section

namespace ShenWork.Paper2.TruncatedPositiveTimeBootstrap

open ShenWork.Paper2 (positivePart)

private theorem positivePart_le_abs_scalar (r : ℝ) :
    positivePart r ≤ |r| := by
  by_cases hr : 0 ≤ r
  · simp [positivePart, hr, abs_of_nonneg hr]
  · have hr' : r ≤ 0 := le_of_not_ge hr
    simp [positivePart, hr', abs_of_nonpos hr']

theorem positivePart_comp_hasDerivAt_zero_of_hasDerivAt_zero
    {f : ℝ → ℝ} {x : ℝ}
    (hf : HasDerivAt f 0 x) (hfx : f x = 0) :
    HasDerivAt (fun y : ℝ => positivePart (f y)) 0 x := by
  rw [hasDerivAt_iff_isLittleO]
  have hf_little :
      (fun y : ℝ => f y) =o[𝓝 x] fun y : ℝ => y - x := by
    simpa [hfx] using hf.isLittleO
  have hpp_bigO :
      (fun y : ℝ => positivePart (f y)) =O[𝓝 x] fun y : ℝ => f y := by
    refine Asymptotics.IsBigO.of_bound' (Filter.Eventually.of_forall ?_)
    intro y
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    simpa [abs_of_nonneg (positivePart_nonneg (f y))] using
      positivePart_le_abs_scalar (f y)
  have hpp_little :
      (fun y : ℝ => positivePart (f y)) =o[𝓝 x] fun y : ℝ => y - x :=
    hpp_bigO.trans_isLittleO hf_little
  simpa [hfx, positivePart_eq_zero_of_nonpos (le_refl (0 : ℝ))] using hpp_little

theorem positivePart_comp_hasDerivAt_of_hasDerivAt_not_bad
    {f : ℝ → ℝ} {x f' : ℝ}
    (hf : HasDerivAt f f' x)
    (hnot_bad : f x = 0 → f' = 0) :
    ∃ d : ℝ, HasDerivAt (fun y : ℝ => positivePart (f y)) d x := by
  by_cases hpos : 0 < f x
  · have hpos_ev : ∀ᶠ y in 𝓝 x, 0 < f y :=
      hf.continuousAt.tendsto.eventually (isOpen_Ioi.mem_nhds hpos)
    have hev : (fun y : ℝ => positivePart (f y)) =ᶠ[𝓝 x] f := by
      filter_upwards [hpos_ev] with y hy
      exact positivePart_eq_self_of_nonneg hy.le
    exact ⟨f', hf.congr_of_eventuallyEq hev⟩
  · by_cases hneg : f x < 0
    · have hneg_ev : ∀ᶠ y in 𝓝 x, f y < 0 :=
        hf.continuousAt.tendsto.eventually (isOpen_Iio.mem_nhds hneg)
      have hev : (fun y : ℝ => positivePart (f y)) =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
        filter_upwards [hneg_ev] with y hy
        exact positivePart_eq_zero_of_nonpos hy.le
      exact ⟨0, (hasDerivAt_const (x := x) (c := (0 : ℝ))).congr_of_eventuallyEq hev⟩
    · have hzero : f x = 0 :=
        le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      have hf0 : HasDerivAt f 0 x := by
        simpa [hnot_bad hzero] using hf
      exact ⟨0, positivePart_comp_hasDerivAt_zero_of_hasDerivAt_zero hf0 hzero⟩

def picardTransversalZeroSet (f : ℝ → ℝ) : Set ℝ :=
  {x : ℝ | x ∈ Ioo (0 : ℝ) 1 ∧ f x = 0 ∧ deriv f x ≠ 0}

theorem picardTransversalZeroSet_countable_of_differentiableAt
    {f : ℝ → ℝ}
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ f x) :
    (picardTransversalZeroSet f).Countable := by
  let S : Set ℝ := picardTransversalZeroSet f
  have hdisc : IsDiscrete S := by
    rw [isDiscrete_iff_nhdsNE]
    intro x hx
    have hxIoo : x ∈ Ioo (0 : ℝ) 1 := hx.1
    have hxderiv : deriv f x ≠ 0 := hx.2.2
    have hev : ∀ᶠ z in 𝓝[≠] x, f z ≠ (0 : ℝ) :=
      (hf x hxIoo).hasDerivAt.eventually_ne hxderiv
    have hcompl : Sᶜ ∈ 𝓝[≠] x := by
      filter_upwards [hev] with z hz
      intro hzS
      exact hz hzS.2.1
    simpa using (Filter.mem_iff_inf_principal_compl.mp hcompl)
  simpa [S] using
    (HereditarilyLindelofSpace.isLindelof S).countable_of_isDiscrete hdisc

end ShenWork.Paper2.TruncatedPositiveTimeBootstrap
