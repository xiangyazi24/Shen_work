import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import ShenWork.PDE.PoincareInequality

/-!
# The co-moving half-line drift-flux obstruction

This is the co-moving analogue of the growing-mirror-weight obstruction.  On a
raw half-line, integration by parts produces a drift boundary flux with the
anti-dissipative sign.  Once the interval length exceeds the sharp threshold
`2 / c`, the linear ramp makes that drift flux strictly larger than the bulk
gradient dissipation.

Consequently the energy method for far-left convergence cannot close on a raw
half-line from bulk dissipation alone: the cut flux has to be controlled, for
example by front-localization.  This is only an obstruction to that energy
method.  It makes no assertion about whether the underlying PDE convergence is
true or false.
-/

open MeasureTheory intervalIntegral
open Set
open scoped Topology Interval

noncomputable section

namespace ShenWork.Paper1

/-- Integration by parts for the diffusion and drift terms in a co-moving
frame, with both endpoint fluxes retained. -/
theorem coMoving_halfLine_driftFlux_energy_identity
    {A Z c : ℝ} {w w1 w2 : ℝ → ℝ}
    (_hAZ : A ≤ Z)
    (hw : ∀ x ∈ Set.uIcc A Z, HasDerivAt w (w1 x) x)
    (hw1 : ∀ x ∈ Set.uIcc A Z, HasDerivAt w1 (w2 x) x)
    (hw2_int : IntervalIntegrable w2 volume A Z) :
    (∫ x in A..Z, w x * (w2 x + c * w1 x)) =
      -(∫ x in A..Z, (w1 x) ^ 2) +
        (w Z * w1 Z - w A * w1 A) +
          (c / 2) * (w Z ^ 2 - w A ^ 2) := by
  have hw_cont : ContinuousOn w (Set.uIcc A Z) :=
    fun x hx ↦ (hw x hx).continuousAt.continuousWithinAt
  have hw1_cont : ContinuousOn w1 (Set.uIcc A Z) :=
    fun x hx ↦ (hw1 x hx).continuousAt.continuousWithinAt
  have hw1_int : IntervalIntegrable w1 volume A Z := hw1_cont.intervalIntegrable
  have hw_mul_w2_int : IntervalIntegrable (fun x ↦ w x * w2 x) volume A Z :=
    hw2_int.continuousOn_mul hw_cont
  have hw_mul_w1_int : IntervalIntegrable (fun x ↦ w x * w1 x) volume A Z :=
    hw1_int.continuousOn_mul hw_cont
  have hibp_second :
      (∫ x in A..Z, w x * w2 x) =
        w Z * w1 Z - w A * w1 A - ∫ x in A..Z, (w1 x) ^ 2 := by
    simpa only [pow_two] using
      intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (a := A) (b := Z) (u := w) (v := w1) (u' := w1) (v' := w2)
        hw hw1 hw1_int hw2_int
  have hibp_first :
      (∫ x in A..Z, w x * w1 x) =
        w Z ^ 2 - w A ^ 2 - ∫ x in A..Z, w1 x * w x := by
    simpa only [pow_two] using
      intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (a := A) (b := Z) (u := w) (v := w) (u' := w1) (v' := w1)
        hw hw hw1_int hw1_int
  have hcomm : (∫ x in A..Z, w1 x * w x) = ∫ x in A..Z, w x * w1 x := by
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  rw [hcomm] at hibp_first
  have hdrift :
      (∫ x in A..Z, w x * w1 x) = (w Z ^ 2 - w A ^ 2) / 2 := by
    nlinarith [hibp_first]
  rw [show (fun x ↦ w x * (w2 x + c * w1 x)) =
      (fun x ↦ w x * w2 x + c * (w x * w1 x)) by funext x; ring]
  rw [intervalIntegral.integral_add hw_mul_w2_int (hw_mul_w1_int.const_mul c)]
  rw [intervalIntegral.integral_const_mul]
  rw [hibp_second, hdrift]
  ring

/-- With the left endpoint quenched, the co-moving identity contains the
nonnegative drift cut flux `(c / 2) * w Z ^ 2`; its sign is anti-dissipative. -/
theorem coMoving_halfLine_driftFlux_identity_of_quenched_left
    {A Z c : ℝ} {w w1 w2 : ℝ → ℝ}
    (hAZ : A ≤ Z)
    (hc : 0 ≤ c)
    (hw : ∀ x ∈ Set.uIcc A Z, HasDerivAt w (w1 x) x)
    (hw1 : ∀ x ∈ Set.uIcc A Z, HasDerivAt w1 (w2 x) x)
    (hw2_int : IntervalIntegrable w2 volume A Z)
    (hwA : w A = 0)
    (hw1A : w1 A = 0) :
    ((∫ x in A..Z, w x * (w2 x + c * w1 x)) =
        -(∫ x in A..Z, (w1 x) ^ 2) + w Z * w1 Z +
          (c / 2) * w Z ^ 2) ∧
      0 ≤ (c / 2) * w Z ^ 2 := by
  constructor
  · have hidentity :=
      coMoving_halfLine_driftFlux_energy_identity (c := c) hAZ hw hw1 hw2_int
    rw [hwA, hw1A] at hidentity
    simpa using hidentity
  · exact mul_nonneg (div_nonneg hc (by norm_num)) (sq_nonneg (w Z))

/-- The endpoint trace of a profile vanishing at the left endpoint is bounded
by the interval length times its bulk derivative energy. -/
theorem sq_endpoint_le_length_mul_integral_deriv_sq
    {A Z : ℝ} {w w1 : ℝ → ℝ}
    (hAZ : A ≤ Z)
    (hw : ∀ x ∈ Set.uIcc A Z, HasDerivAt w (w1 x) x)
    (hw1_int : IntervalIntegrable w1 volume A Z)
    (hw1_sq_int : IntervalIntegrable (fun x ↦ w1 x ^ 2) volume A Z)
    (hwA : w A = 0) :
    w Z ^ 2 ≤ (Z - A) * ∫ x in A..Z, w1 x ^ 2 := by
  rcases hAZ.eq_or_lt with hZA | hAZlt
  · subst Z
    simp [hwA]
  · have hlength : 0 < Z - A := sub_pos.mpr hAZlt
    have hw1_shift_int :
        IntervalIntegrable (fun y ↦ w1 (y + A)) volume 0 (Z - A) := by
      simpa using hw1_int.comp_add_right A
    have hw1_shift_sq_int :
        IntervalIntegrable (fun y ↦ w1 (y + A) ^ 2) volume 0 (Z - A) := by
      simpa using hw1_sq_int.comp_add_right A
    have hCSshift := ShenWork.Poincare.integral_abs_sq_le_length_mul_integral_sq
      hlength hw1_shift_int hw1_shift_sq_int
    have habs_shift :
        (∫ y in 0..Z - A, |w1 (y + A)|) = ∫ x in A..Z, |w1 x| := by
      simpa only [zero_add, sub_add_cancel] using
        (intervalIntegral.integral_comp_add_right
          (a := 0) (b := Z - A) (f := fun x ↦ |w1 x|) A)
    have hsq_shift :
        (∫ y in 0..Z - A, w1 (y + A) ^ 2) = ∫ x in A..Z, w1 x ^ 2 := by
      simpa only [zero_add, sub_add_cancel] using
        (intervalIntegral.integral_comp_add_right
          (a := 0) (b := Z - A) (f := fun x ↦ w1 x ^ 2) A)
    have hCS :
        (∫ x in A..Z, |w1 x|) ^ 2 ≤
          (Z - A) * ∫ x in A..Z, w1 x ^ 2 := by
      simpa only [habs_shift, hsq_shift] using hCSshift
    have hftc : ∫ x in A..Z, w1 x = w Z - w A :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hw hw1_int
    have habs : |∫ x in A..Z, w1 x| ≤ ∫ x in A..Z, |w1 x| :=
      intervalIntegral.abs_integral_le_integral_abs hAZ
    have habs_int_nonneg : 0 ≤ ∫ x in A..Z, |w1 x| :=
      intervalIntegral.integral_nonneg hAZ (fun x _hx ↦ abs_nonneg _)
    have hsquare :
        (∫ x in A..Z, w1 x) ^ 2 ≤ (∫ x in A..Z, |w1 x|) ^ 2 := by
      rw [← sq_abs (∫ x in A..Z, w1 x)]
      exact (sq_le_sq₀ (abs_nonneg _) habs_int_nonneg).2 habs
    rw [hftc, hwA, sub_zero] at hsquare
    exact hsquare.trans hCS

/-- The threshold `2 / c` is sharp for the linear ramp: above it, the drift
flux minus the ramp's bulk dissipation is strictly positive. -/
theorem coMoving_driftFlux_net_pos_of_two_div_lt_length
    {A Z c : ℝ}
    (hc : 0 < c)
    (hcritical : 2 / c < Z - A) :
    0 < c / 2 - 1 / (Z - A) := by
  have htwo_div_pos : 0 < 2 / c := div_pos (by norm_num) hc
  have hlength : 0 < Z - A := htwo_div_pos.trans hcritical
  have hcross : 2 < (Z - A) * c := (div_lt_iff₀ hc).mp hcritical
  have hinv_lt : 1 / (Z - A) < c / 2 := by
    rw [div_lt_div_iff₀ hlength (by norm_num)]
    nlinarith
  linarith

/-- At the critical length `2 / c`, the linear ramp's drift flux and bulk
dissipation agree exactly. -/
theorem coMoving_driftFlux_net_eq_zero_of_length_eq_two_div
    {A Z c : ℝ}
    (_hc : 0 < c)
    (hcritical : Z - A = 2 / c) :
    c / 2 - 1 / (Z - A) = 0 := by
  rw [hcritical]
  field_simp
  ring

/-- Below (or at) the critical length, the endpoint trace estimate absorbs the
drift flux into the bulk derivative energy.  Together with the ramp above the
threshold, this identifies `2 / c` as the sharp onset. -/
theorem coMoving_driftFlux_le_dissipation_of_length_le_two_div
    {A Z c : ℝ} {w w1 : ℝ → ℝ}
    (hc : 0 < c)
    (hAZ : A ≤ Z)
    (hlength : Z - A ≤ 2 / c)
    (hw : ∀ x ∈ Set.uIcc A Z, HasDerivAt w (w1 x) x)
    (hw1_int : IntervalIntegrable w1 volume A Z)
    (hw1_sq_int : IntervalIntegrable (fun x ↦ w1 x ^ 2) volume A Z)
    (hwA : w A = 0) :
    (c / 2) * w Z ^ 2 ≤ ∫ x in A..Z, w1 x ^ 2 := by
  have htrace := sq_endpoint_le_length_mul_integral_deriv_sq
    hAZ hw hw1_int hw1_sq_int hwA
  have henergy_nonneg : 0 ≤ ∫ x in A..Z, w1 x ^ 2 :=
    intervalIntegral.integral_nonneg hAZ (fun x _hx ↦ sq_nonneg _)
  have hc_half_nonneg : 0 ≤ c / 2 := div_nonneg hc.le (by norm_num)
  have hcoefficient : (c / 2) * (Z - A) ≤ 1 := by
    calc
      (c / 2) * (Z - A) ≤ (c / 2) * (2 / c) :=
        mul_le_mul_of_nonneg_left hlength hc_half_nonneg
      _ = 1 := by field_simp [ne_of_gt hc]
  calc
    (c / 2) * w Z ^ 2 ≤ (c / 2) * ((Z - A) * ∫ x in A..Z, w1 x ^ 2) :=
      mul_le_mul_of_nonneg_left htrace hc_half_nonneg
    _ = ((c / 2) * (Z - A)) * ∫ x in A..Z, w1 x ^ 2 := by ring
    _ ≤ 1 * ∫ x in A..Z, w1 x ^ 2 :=
      mul_le_mul_of_nonneg_right hcoefficient henergy_nonneg
    _ = ∫ x in A..Z, w1 x ^ 2 := one_mul _

/-- On every interval longer than `2 / c`, the global `C¹` linear ramp is a
quenched-left profile whose drift flux strictly exceeds its bulk dissipation. -/
theorem exists_linearRamp_driftFlux_gt_dissipation
    {A Z c : ℝ}
    (hc : 0 < c)
    (hcritical : 2 / c < Z - A) :
    ∃ w w1 : ℝ → ℝ,
      (∀ x, HasDerivAt w (w1 x) x) ∧
      Continuous w1 ∧
      (∀ x, w1 x = 1 / (Z - A)) ∧
      w A = 0 ∧
      w Z = 1 ∧
      (c / 2) * w Z ^ 2 - (∫ x in A..Z, w1 x ^ 2) > 0 := by
  have hnet := coMoving_driftFlux_net_pos_of_two_div_lt_length hc hcritical
  have htwo_div_pos : 0 < 2 / c := div_pos (by norm_num) hc
  have hlength : 0 < Z - A := htwo_div_pos.trans hcritical
  have hlength_ne : Z - A ≠ 0 := ne_of_gt hlength
  refine ⟨(fun x ↦ (x - A) / (Z - A)), (fun _ ↦ 1 / (Z - A)), ?_,
    continuous_const, (fun _ ↦ rfl), ?_, ?_, ?_⟩
  · intro x
    simpa using (hasDerivAt_id x).sub_const A |>.div_const (Z - A)
  · simp
  · field_simp
  · simp only [div_self hlength_ne, one_pow, mul_one]
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    rw [show (Z - A) * (1 / (Z - A)) ^ 2 = 1 / (Z - A) by
      field_simp]
    simpa using hnet

/-- Headline coefficient-one absorption obstruction.  For every auxiliary
constant `K`, the same quenched-left `C¹` ramp (which is independent of `K`)
leaves a strictly positive drift-minus-bulk defect.  Thus, once the half-line
length exceeds the sharp value `2 / c`, the raw co-moving half-line energy
method cannot close from bulk dissipation alone; controlling the cut flux by
front-localization is necessary.  This does not decide whether the PDE
convergence itself is true. -/
theorem coMoving_halfLine_driftFlux_obstruction
    {A Z c : ℝ}
    (hc : 0 < c)
    (hcritical : 2 / c < Z - A)
    (_K : ℝ) :
    ∃ w w1 : ℝ → ℝ,
      (∀ x, HasDerivAt w (w1 x) x) ∧
      Continuous w1 ∧
      w A = 0 ∧
      w Z = 1 ∧
      (c / 2) * w Z ^ 2 > (∫ x in A..Z, w1 x ^ 2) ∧
      (∫ x in A..Z, w1 x ^ 2) <
        w Z * w1 Z + (c / 2) * w Z ^ 2 ∧
      0 < w Z * w1 Z + (c / 2) * w Z ^ 2 := by
  obtain ⟨w, w1, hw, hw1_cont, hw1_const, hwA, hwZ, hpositive⟩ :=
    exists_linearRamp_driftFlux_gt_dissipation hc hcritical
  have htwo_div_pos : 0 < 2 / c := div_pos (by norm_num) hc
  have hlength : 0 < Z - A := htwo_div_pos.trans hcritical
  have hAZ : A ≤ Z := (sub_pos.mp hlength).le
  have henergy_nonneg : 0 ≤ ∫ x in A..Z, w1 x ^ 2 :=
    intervalIntegral.integral_nonneg hAZ (fun x _hx ↦ sq_nonneg _)
  have hw1Z_pos : 0 < w1 Z := by
    rw [hw1_const]
    exact one_div_pos.mpr hlength
  have hdrift_gt : (∫ x in A..Z, w1 x ^ 2) < (c / 2) * w Z ^ 2 := by
    linarith
  rw [hwZ] at hdrift_gt
  have hfullFlux_gt :
      (∫ x in A..Z, w1 x ^ 2) <
        w Z * w1 Z + (c / 2) * w Z ^ 2 := by
    rw [hwZ]
    nlinarith
  refine ⟨w, w1, hw, hw1_cont, hwA, hwZ, ?_, hfullFlux_gt, ?_⟩
  · simpa [hwZ] using hdrift_gt
  · linarith

section AxiomAudit

#print axioms coMoving_halfLine_driftFlux_energy_identity
#print axioms coMoving_halfLine_driftFlux_identity_of_quenched_left
#print axioms sq_endpoint_le_length_mul_integral_deriv_sq
#print axioms coMoving_driftFlux_net_pos_of_two_div_lt_length
#print axioms coMoving_driftFlux_net_eq_zero_of_length_eq_two_div
#print axioms coMoving_driftFlux_le_dissipation_of_length_le_two_div
#print axioms exists_linearRamp_driftFlux_gt_dissipation
#print axioms coMoving_halfLine_driftFlux_obstruction

end AxiomAudit

end ShenWork.Paper1
