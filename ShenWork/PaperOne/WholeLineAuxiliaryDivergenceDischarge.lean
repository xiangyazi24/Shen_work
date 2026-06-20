import ShenWork.PaperOne.WholeLineAuxiliaryDivergenceGlobal
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

open MeasureTheory Filter Topology Real Set
open scoped Topology NNReal
open ProbabilityTheory

noncomputable section

namespace ShenWork.PaperOne

/-!
# Honest divergence-form Haux discharge layer

This file records the explicit exponential-tail part of the divergence-form
auxiliary discharge, and isolates the obstruction in the current heat-trap
margin interface.

The upper heat-trap margin follows from the exact moving-frame heat action on
`exp (-κ x)` and the strict tail comparison
`exp (-κ (m + 1) x) = o(exp (-κ x))` for `m ≥ 1`.

The lower heat-trap margin in
`AuxiliaryMildMapDivHeatTrapMargin`, however, is not satisfiable from the same
explicit comparison when the moving-frame heat factor
`q = exp ((κ^2 - 1 - κ c)t)` is strictly below `1`: the lower barrier has
right-tail leading coefficient `1`, while the homogeneous heat step has leading
coefficient `q`.  The theorem `lowerBarrier_tail_obstruction_eventually`
formalizes this rather than carrying a false hypothesis.
-/

/-- The pure exponential right-tail profile. -/
def pureExpTail (κ : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-κ * x)

lemma heatKernel_eq_gaussianPDFReal_two_mul
    {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    heatKernel t (x - y) =
      gaussianPDFReal x (⟨2 * t, by positivity⟩ : ℝ≥0) y := by
  unfold heatKernel gaussianPDFReal
  simp only [NNReal.coe_mk]
  congr 1
  · congr 1
    ring
  · congr 1
    ring

/-- The whole-line heat semigroup sends `exp (-κ x)` to
`exp (κ^2 t) exp (-κ x)`. -/
theorem heatSemigroup_pureExpTail_eq
    {κ t x : ℝ} (ht : 0 < t) :
    heatSemigroup t (pureExpTail κ) x =
      Real.exp (κ ^ 2 * t) * pureExpTail κ x := by
  let v : ℝ≥0 := ⟨2 * t, by positivity⟩
  have hv : v ≠ 0 := by
    intro hv0
    have hcoe : (v : ℝ) = 0 := by simp [hv0]
    dsimp [v] at hcoe
    linarith
  have hmgf :=
    congrFun (mgf_id_gaussianReal (μ := x) (v := v)) (-κ)
  have hmgf_integral :
      (∫ y : ℝ, Real.exp (-κ * y) ∂gaussianReal x v) =
        Real.exp (x * (-κ) + (v : ℝ) * (-κ) ^ 2 / 2) := by
    simpa [mgf] using hmgf
  have hdens :=
    integral_gaussianReal_eq_integral_smul
      (μ := x) (v := v) (f := fun y : ℝ => Real.exp (-κ * y)) hv
  have hdens_integral :
      (∫ y : ℝ, Real.exp (-κ * y) ∂gaussianReal x v) =
        ∫ y : ℝ, gaussianPDFReal x v y * Real.exp (-κ * y) := by
    simpa using hdens
  unfold heatSemigroup pureExpTail
  rw [show
      (fun y : ℝ => heatKernel t (x - y) * Real.exp (-κ * y)) =
        fun y : ℝ => gaussianPDFReal x v y * Real.exp (-κ * y) by
        ext y
        rw [heatKernel_eq_gaussianPDFReal_two_mul ht]]
  rw [← hdens_integral, hmgf_integral]
  have hexp_arg :
      x * (-κ) + (v : ℝ) * (-κ) ^ 2 / 2 = κ ^ 2 * t + -κ * x := by
    dsimp [v]
    ring
  rw [hexp_arg, Real.exp_add]

/-- The modified whole-line heat semigroup action on `exp (-κ x)`. -/
theorem wholeLineHeatOp_pureExpTail_eq
    {κ t x : ℝ} (ht : 0 < t) :
    wholeLineHeatOp t (pureExpTail κ) x =
      Real.exp ((κ ^ 2 - 1) * t) * pureExpTail κ x := by
  unfold wholeLineHeatOp modifiedSemigroup
  rw [heatSemigroup_pureExpTail_eq (κ := κ) (t := t) (x := x) ht,
      ← mul_assoc, ← Real.exp_add,
      show -t + κ ^ 2 * t = (κ ^ 2 - 1) * t by ring]

/-- Explicit moving-frame heat action on the exponential tail:
`e^{t(Δ-I)} exp (-κ·)` followed by the shift `x ↦ x + c t`. -/
theorem movingFrameHeatOp_exp_eq
    {κ c t x : ℝ} (ht : 0 < t) :
    movingFrameHeatOp c t (pureExpTail κ) x =
      Real.exp ((κ ^ 2 - 1) * t) * Real.exp (-κ * (x + c * t)) := by
  simpa [movingFrameHeatOp, pureExpTail] using
    wholeLineHeatOp_pureExpTail_eq (κ := κ) (t := t) (x := x + c * t) ht

/-- The same formula with the moving-frame decay factor pulled out in front of
`exp (-κ x)`. -/
theorem movingFrameHeatOp_exp_eq_decay
    {κ c t x : ℝ} (ht : 0 < t) :
    movingFrameHeatOp c t (pureExpTail κ) x =
      Real.exp ((κ ^ 2 - 1 - κ * c) * t) * pureExpTail κ x := by
  rw [movingFrameHeatOp_exp_eq (κ := κ) (c := c) (t := t) (x := x) ht]
  unfold pureExpTail
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- For `0 < κ < 1`, nonnegative speed gives the strict decay factor
`exp ((κ^2 - 1 - κ c)t) < 1` at every positive time. -/
theorem movingFrame_exp_decay_factor_lt_one
    {κ c t : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hc : 0 ≤ c) (ht : 0 < t) :
    Real.exp ((κ ^ 2 - 1 - κ * c) * t) < 1 := by
  have hκsq : κ ^ 2 < 1 := by nlinarith [hκ0, hκ1]
  have hκc : 0 ≤ κ * c := mul_nonneg hκ0.le hc
  have hcoef : κ ^ 2 - 1 - κ * c < 0 := by
    nlinarith
  have harg : (κ ^ 2 - 1 - κ * c) * t < 0 :=
    mul_neg_of_neg_of_pos hcoef ht
  exact Real.exp_lt_one_iff.mpr harg

/-- The explicit upper margin coefficient is nonnegative when the moving-frame
tail factor is at most one. -/
theorem explicitUpperTailMargin_nonneg
    {κ q x : ℝ} (hq : q ≤ 1) :
    0 ≤ (1 - q) * pureExpTail κ x := by
  exact mul_nonneg (sub_nonneg.mpr hq) (Real.exp_pos _).le

/-- Upper heat-trap tail absorption: if the correction budget is bounded by
the explicit margin `(1-q) exp (-κx)`, then `q exp (-κx) + E` stays below the
upper exponential tail. -/
theorem pureExpTail_upper_margin_of_budget
    {κ q E x : ℝ}
    (hE : E ≤ (1 - q) * pureExpTail κ x) :
    q * pureExpTail κ x + E ≤ pureExpTail κ x := by
  calc
    q * pureExpTail κ x + E
        ≤ q * pureExpTail κ x + (1 - q) * pureExpTail κ x := by
          linarith [hE]
    _ = pureExpTail κ x := by ring

/-- Tail comparison in eventual form: for `m ≥ 1`, the correction tail
`C exp (-κ (m+1)x)` is eventually dominated by any positive multiple of
`exp (-κx)`. -/
theorem eventually_exp_tail_correction_le_margin
    {κ m C η : ℝ} (hκ : 0 < κ) (hm : 1 ≤ m) (hC : 0 ≤ C) (hη : 0 < η) :
    ∀ᶠ x in atTop,
      C * Real.exp (-(κ * (m + 1)) * x) ≤
        η * pureExpTail κ x := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hκm : 0 < κ * m := mul_pos hκ hmpos
  have hneg : -(κ * m) < 0 := neg_lt_zero.mpr hκm
  have htend :
      Tendsto (fun x : ℝ => C * Real.exp (-(κ * m) * x)) atTop (𝓝 0) := by
    have hexp :
        Tendsto (fun x : ℝ => Real.exp (-(κ * m) * x)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg hneg)
    simpa using hexp.const_mul C
  have hsmall :
      ∀ᶠ x in atTop, C * Real.exp (-(κ * m) * x) < η :=
    htend (isOpen_Iio.mem_nhds hη)
  filter_upwards [hsmall] with x hx
  have hright_nonneg : 0 ≤ Real.exp (-κ * x) := (Real.exp_pos _).le
  have hmul :=
    mul_le_mul_of_nonneg_right (le_of_lt hx) hright_nonneg
  calc
    C * Real.exp (-(κ * (m + 1)) * x)
        = (C * Real.exp (-(κ * m) * x)) * Real.exp (-κ * x) := by
          rw [show -(κ * (m + 1)) * x = -(κ * m) * x + -κ * x by ring,
              Real.exp_add, ← mul_assoc]
    _ ≤ η * Real.exp (-κ * x) := hmul
    _ = η * pureExpTail κ x := rfl

/-- Combining the explicit moving-frame decay factor with the faster correction
tail gives the upper heat-trap inequality eventually in the right tail. -/
theorem eventually_movingFrame_exp_upper_margin
    {κ c t m C : ℝ}
    (ht : 0 < t) (hκ0 : 0 < κ) (hκ1 : κ < 1) (hc : 0 ≤ c)
    (hm : 1 ≤ m) (hC : 0 ≤ C) :
    ∀ᶠ x in atTop,
      movingFrameHeatOp c t (pureExpTail κ) x +
          C * Real.exp (-(κ * (m + 1)) * x) ≤ pureExpTail κ x := by
  let q : ℝ := Real.exp ((κ ^ 2 - 1 - κ * c) * t)
  have hq_lt : q < 1 :=
    movingFrame_exp_decay_factor_lt_one hκ0 hκ1 hc ht
  have htail :=
    eventually_exp_tail_correction_le_margin
      (κ := κ) (m := m) (C := C) (η := 1 - q)
      hκ0 hm hC (sub_pos.mpr hq_lt)
  filter_upwards [htail] with x hx
  rw [movingFrameHeatOp_exp_eq_decay (κ := κ) (c := c) (t := t) (x := x) ht]
  exact pureExpTail_upper_margin_of_budget (κ := κ) (q := q)
    (E := C * Real.exp (-(κ * (m + 1)) * x)) hx

/-- Pointwise right-tail obstruction to the lower heat-trap margin when the
homogeneous exponential heat factor is `q < 1`.

Once `D exp (-(κt-κ)x) < 1-q`, the lower barrier lies strictly above
`q exp (-κx)`. -/
theorem lowerBarrier_tail_obstruction_pointwise
    {κ κt D q x : ℝ}
    (hq_nonneg : 0 ≤ q) (hq_lt : q < 1)
    (hsmall : D * Real.exp (-(κt - κ) * x) < 1 - q) :
    q * pureExpTail κ x < lowerBarrier κ κt D x := by
  have hexp_pos : 0 < Real.exp (-κ * x) := Real.exp_pos _
  have hscaled :=
    mul_lt_mul_of_pos_right hsmall hexp_pos
  have hDlt :
      D * Real.exp (-κt * x) < (1 - q) * Real.exp (-κ * x) := by
    calc
      D * Real.exp (-κt * x)
          = (D * Real.exp (-(κt - κ) * x)) * Real.exp (-κ * x) := by
            rw [show -κt * x = -(κt - κ) * x + -κ * x by ring,
                Real.exp_add, ← mul_assoc]
      _ < (1 - q) * Real.exp (-κ * x) := hscaled
  have hDlt' :
      D * Real.exp (-κt * x) < Real.exp (-κ * x) - q * Real.exp (-κ * x) := by
    calc
      D * Real.exp (-κt * x)
          < (1 - q) * Real.exp (-κ * x) := hDlt
      _ = Real.exp (-κ * x) - q * Real.exp (-κ * x) := by ring
  have hmain :
      q * Real.exp (-κ * x) <
        Real.exp (-κ * x) - D * Real.exp (-κt * x) := by
    linarith
  have hdiff_pos :
      0 < Real.exp (-κ * x) - D * Real.exp (-κt * x) := by
    exact lt_of_le_of_lt (mul_nonneg hq_nonneg hexp_pos.le) hmain
  have hlower :
      lowerBarrier κ κt D x =
        Real.exp (-κ * x) - D * Real.exp (-κt * x) := by
    unfold lowerBarrier
    rw [max_eq_right hdiff_pos.le]
  simpa [pureExpTail, hlower] using hmain

/-- The lower-barrier obstruction is not a compact artifact: if `κt > κ`, it
holds eventually as `x → +∞`. -/
theorem lowerBarrier_tail_obstruction_eventually
    {κ κt D q : ℝ}
    (hgap : κ < κt) (hq_nonneg : 0 ≤ q) (hq_lt : q < 1) :
    ∀ᶠ x in atTop, q * pureExpTail κ x < lowerBarrier κ κt D x := by
  have hdelta : 0 < κt - κ := sub_pos.mpr hgap
  have hneg : -(κt - κ) < 0 := neg_lt_zero.mpr hdelta
  have htend :
      Tendsto (fun x : ℝ => D * Real.exp (-(κt - κ) * x)) atTop (𝓝 0) := by
    have hexp :
        Tendsto (fun x : ℝ => Real.exp (-(κt - κ) * x)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg hneg)
    simpa using hexp.const_mul D
  have hsmall :
      ∀ᶠ x in atTop, D * Real.exp (-(κt - κ) * x) < 1 - q :=
    htend (isOpen_Iio.mem_nhds (sub_pos.mpr hq_lt))
  filter_upwards [hsmall] with x hx
  exact lowerBarrier_tail_obstruction_pointwise
    (κ := κ) (κt := κt) (D := D) (q := q) (x := x)
    hq_nonneg hq_lt hx

/-- Specialization of the obstruction to the explicit moving-frame heat factor.
This is the formal reason the current two-sided
`AuxiliaryMildMapDivHeatTrapMargin` cannot be closed from the stated
`q < 1` exponential comparison for a fixed lower barrier with leading
right-tail coefficient `1`. -/
theorem lowerBarrier_obstructs_explicit_heat_margin_eventually
    {κ κt c t D : ℝ}
    (ht : 0 < t) (hκ0 : 0 < κ) (hκ1 : κ < 1) (hc : 0 ≤ c)
    (hgap : κ < κt) :
    ∀ᶠ x in atTop,
      movingFrameHeatOp c t (pureExpTail κ) x < lowerBarrier κ κt D x := by
  let q : ℝ := Real.exp ((κ ^ 2 - 1 - κ * c) * t)
  have hq_pos : 0 < q := Real.exp_pos _
  have hq_lt : q < 1 :=
    movingFrame_exp_decay_factor_lt_one hκ0 hκ1 hc ht
  have hobst :=
    lowerBarrier_tail_obstruction_eventually
      (κ := κ) (κt := κt) (D := D) (q := q)
      hgap hq_pos.le hq_lt
  filter_upwards [hobst] with x hx
  rw [movingFrameHeatOp_exp_eq_decay (κ := κ) (c := c) (t := t) (x := x) ht]
  exact hx

/-- The non-margin pieces of the frozen-signal divergence Haux data.  These are
the parts that are still satisfiable through the banked kernel-integrability,
continuous Banach-realization, and uniform restart arguments.

The heat-trap margin is intentionally not included here: the obstruction above
shows that the current lower-margin interface is false under the explicit
`q < 1` tail comparison. -/
structure WholeLineAuxiliaryDivFrozenSignalNonMarginData
    (p : CMParams) (c κt D : ℝ) where
  realize :
    ∀ U, (hU : U ∈ WaveTrap (waveExponent c) κt D) →
      Continuous U →
      ∀ C : AuxiliaryMildMapDivContinuousContractionData p c
          (upperBarrier (waveExponent c))
          (frozenSignal p.γ U)
          (fun x => deriv (frozenSignal p.γ U) x)
          U
          (waveExponent c) κt D,
        AuxiliaryMildMapDivContinuousBanachRealizationData p c
          (upperBarrier (waveExponent c))
          (frozenSignal p.γ U)
          (fun x => deriv (frozenSignal p.γ U) x)
          U
          (waveExponent c) κt D C
  restart :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D → Continuous U →
      AuxiliaryMildMapDivUniformRestartGluingFromLocalBanach p c
        (upperBarrier (waveExponent c))
        (frozenSignal p.γ U)
        (fun x => deriv (frozenSignal p.γ U) x)
        U
        (waveExponent c) κt D
  value_duhamel_integrable :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D → Continuous U →
      ∀ T W Z dist, 0 ≤ dist →
        AuxiliaryBarrierTrap (waveExponent c) κt D T W →
        AuxiliaryBarrierTrap (waveExponent c) κt D T Z →
        AuxiliaryValueDistanceBound T dist W Z →
        AuxiliaryOrbitSliceContinuousOn T W →
        AuxiliaryOrbitSliceContinuousOn T Z →
          ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
            AuxiliaryValueDuhamelSubIntegrability p c W Z U t x
  value_duhamel_heat_integrable :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D → Continuous U →
      ∀ T W Z dist, 0 ≤ dist →
        AuxiliaryBarrierTrap (waveExponent c) κt D T W →
        AuxiliaryBarrierTrap (waveExponent c) κt D T Z →
        AuxiliaryValueDistanceBound T dist W Z →
        AuxiliaryOrbitSliceContinuousOn T W →
        AuxiliaryOrbitSliceContinuousOn T Z →
          ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
            AuxiliaryValueDuhamelSubHeatIntegrability p c W Z U t x
  div_grad_integrable :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D → Continuous U →
      AuxiliaryMildMapDivGradIntegrableContinuous p c
        (frozenSignal p.γ U)
        (fun x => deriv (frozenSignal p.γ U) x)
        (waveExponent c) κt D
  div_grad_duhamel_sub :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D → Continuous U →
      AuxiliaryMildMapDivGradDuhamelSubContinuous p c
        (frozenSignal p.γ U)
        (fun x => deriv (frozenSignal p.γ U) x)
        (waveExponent c) κt D

/-- If a corrected maps-to/heat-margin input is supplied, the non-margin data
assemble the existing frozen-signal family structure.  This theorem does not
claim the current heat-margin input is satisfiable; the obstruction above is
the reason it is kept separate. -/
def wholeLineAuxiliaryDivFrozenSignalFamilyData_of_nonMargin
    {p : CMParams} {c κt D : ℝ}
    (H : WholeLineAuxiliaryDivFrozenSignalNonMarginData p c κt D)
    (hmaps :
      ∀ U, U ∈ WaveTrap (waveExponent c) κt D → Continuous U →
        AuxiliaryMildMapDivMapsToLinfTrapData p c
          (upperBarrier (waveExponent c))
          (frozenSignal p.γ U)
          (fun x => deriv (frozenSignal p.γ U) x)
          U
          (waveExponent c) κt D
          (auxiliaryMildMapDivGradientRate p 1)
          (auxiliaryValueSourceLipConst p)) :
    WholeLineAuxiliaryDivFrozenSignalFamilyData p c κt D where
  realize := H.realize
  restart := H.restart
  mapsTo_linfTrap := hmaps
  value_duhamel_integrable := H.value_duhamel_integrable
  value_duhamel_heat_integrable := H.value_duhamel_heat_integrable
  div_grad_integrable := H.div_grad_integrable
  div_grad_duhamel_sub := H.div_grad_duhamel_sub

#print axioms movingFrameHeatOp_exp_eq
#print axioms movingFrameHeatOp_exp_eq_decay
#print axioms eventually_movingFrame_exp_upper_margin
#print axioms lowerBarrier_obstructs_explicit_heat_margin_eventually
#print axioms wholeLineAuxiliaryDivFrozenSignalFamilyData_of_nonMargin

end ShenWork.PaperOne
