import ShenWork.Paper1.WholeLineWeightedRegularityDuhamel
import Mathlib.MeasureTheory.Function.Holder

open Filter MeasureTheory
open scoped BigOperators

noncomputable section

namespace ShenWork.Paper1

/-!
# Time Holder closure for finite linear sources

The weighted lower-order source is a sum of four terms, each consisting of
a bounded time-dependent multiplication operator applied to an `L2` field.
This file isolates the Banach-space algebra needed to propagate a common
positive time-Holder modulus through that finite sum.
-/

/-! ## Bounded scalar multipliers on whole-line `L2` -/

/-- The whole-line real `L-infinity` coefficient space. -/
abbrev WholeLineRealLInf :=
  MeasureTheory.Lp ℝ ⊤ (volume : Measure ℝ)

/-- Canonical `L-infinity` class of a measurable uniformly bounded scalar
coefficient. -/
def wholeLineRealLInfOfBound
    (a : ℝ → ℝ) (ha : AEStronglyMeasurable a volume)
    (K : ℝ) (hbound : ∀ x, |a x| ≤ K) : WholeLineRealLInf :=
  (memLp_top_of_bound ha K <|
    Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hbound x).toLp a

theorem wholeLineRealLInfOfBound_coe_ae
    (a : ℝ → ℝ) (ha : AEStronglyMeasurable a volume)
    (K : ℝ) (hbound : ∀ x, |a x| ≤ K) :
    ((wholeLineRealLInfOfBound a ha K hbound : WholeLineRealLInf) : ℝ → ℝ)
      =ᵐ[volume] a := by
  exact MemLp.coeFn_toLp _

theorem wholeLineRealLInfOfBound_norm_le
    (a : ℝ → ℝ) (ha : AEStronglyMeasurable a volume)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ x, |a x| ≤ K) :
    ‖wholeLineRealLInfOfBound a ha K hbound‖ ≤ K := by
  unfold wholeLineRealLInfOfBound
  rw [Lp.norm_toLp]
  have hess : eLpNorm a ⊤ volume ≤ ENNReal.ofReal K := by
    simpa only [eLpNorm, if_pos rfl] using
      (eLpNormEssSup_le_of_ae_bound
        (Eventually.of_forall fun x => by
          simpa only [Real.norm_eq_abs] using hbound x))
  have hleft : eLpNorm a ⊤ volume ≠ ⊤ := by
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hess
  have hreal := (ENNReal.toReal_le_toReal
    hleft ENNReal.ofReal_ne_top).2 hess
  simpa only [ENNReal.toReal_ofReal hK] using hreal

/-- Pointwise multiplication by an `L-infinity` coefficient, bundled as a
continuous endomorphism of `WholeLineRealL2`. -/
def wholeLineRealL2Multiplier
    (a : WholeLineRealLInf) : WholeLineRealL2 →L[ℝ] WholeLineRealL2 :=
  ((ContinuousLinearMap.lsmul ℝ ℝ).holderL
    (volume : Measure ℝ) ⊤ 2 2) a

/-- The bundled multiplier has the expected pointwise representative. -/
theorem wholeLineRealL2Multiplier_coe_ae
    (a : WholeLineRealLInf) (f : WholeLineRealL2) :
    ((wholeLineRealL2Multiplier a f : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] fun x => a x * f x := by
  unfold wholeLineRealL2Multiplier
  rw [ContinuousLinearMap.holderL_apply_apply]
  filter_upwards
    [ContinuousLinearMap.coeFn_holder
      (μ := (volume : Measure ℝ)) (p := ⊤) (q := 2) (r := 2)
      (ContinuousLinearMap.lsmul ℝ ℝ) a f] with x hx
  simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hx

/-- Multiplication by an `L-infinity` coefficient obeys the standard
`L-infinity`--`L2` product estimate. -/
theorem wholeLineRealL2Multiplier_apply_norm_le
    (a : WholeLineRealLInf) (f : WholeLineRealL2) :
    ‖wholeLineRealL2Multiplier a f‖ ≤ ‖a‖ * ‖f‖ := by
  unfold wholeLineRealL2Multiplier
  rw [ContinuousLinearMap.holderL_apply_apply]
  simpa only [ContinuousLinearMap.opNorm_lsmul, one_mul] using
    (ContinuousLinearMap.norm_holder_apply_apply_le
      (ContinuousLinearMap.lsmul ℝ ℝ) a f)

/-- Operator-norm form of the multiplier estimate. -/
theorem wholeLineRealL2Multiplier_norm_le
    (a : WholeLineRealLInf) :
    ‖wholeLineRealL2Multiplier a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
  intro f
  exact wholeLineRealL2Multiplier_apply_norm_le a f

section OperatorProducts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Difference estimate for a time-dependent bounded operator applied to a
time-dependent vector.  The decomposition uses the vector at the second
time, so only its norm is needed. -/
theorem continuousLinearMap_apply_sub_apply_norm_le
    (A B : E →L[ℝ] E) (x y : E) :
    ‖A x - B y‖ ≤ ‖A‖ * ‖x - y‖ + ‖A - B‖ * ‖y‖ := by
  have hid : A x - B y = A (x - y) + (A - B) y := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [hid]
  exact (norm_add_le _ _).trans <|
    add_le_add (A.le_opNorm (x - y)) ((A - B).le_opNorm y)

/-- A finite sum of time-dependent bounded operators applied to
time-dependent vectors inherits their common Holder exponent.

The constants are kept componentwise.  This is the form used for the four
terms of `paper5WeightedLowerOrderSource`: the operator bounds control the
field increments, while the operator increments multiply a uniform bound
for the fields themselves. -/
theorem finite_operator_source_holder
    {I : Type*} [Fintype I]
    {theta s t : ℝ}
    (A : I → ℝ → E →L[ℝ] E) (X : I → ℝ → E)
    (KA HA KX HX : I → ℝ)
    (hA_nonneg : ∀ i, 0 ≤ KA i)
    (hHA_nonneg : ∀ i, 0 ≤ HA i)
    (hA_bound : ∀ i, ‖A i s‖ ≤ KA i)
    (hX_bound : ∀ i, ‖X i t‖ ≤ KX i)
    (hA_holder : ∀ i,
      ‖A i s - A i t‖ ≤ HA i * |s - t| ^ theta)
    (hX_holder : ∀ i,
      ‖X i s - X i t‖ ≤ HX i * |s - t| ^ theta) :
    ‖(∑ i, A i s (X i s)) - ∑ i, A i t (X i t)‖ ≤
      (∑ i, (KA i * HX i + HA i * KX i)) * |s - t| ^ theta := by
  have hrpow : 0 ≤ |s - t| ^ theta := Real.rpow_nonneg (abs_nonneg _) _
  calc
    ‖(∑ i, A i s (X i s)) - ∑ i, A i t (X i t)‖ =
        ‖∑ i, (A i s (X i s) - A i t (X i t))‖ := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, ‖A i s (X i s) - A i t (X i t)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i,
        ((KA i * HX i + HA i * KX i) * |s - t| ^ theta) := by
      apply Finset.sum_le_sum
      intro i _hi
      calc
        ‖A i s (X i s) - A i t (X i t)‖ ≤
            ‖A i s‖ * ‖X i s - X i t‖ +
              ‖A i s - A i t‖ * ‖X i t‖ :=
          continuousLinearMap_apply_sub_apply_norm_le
            (A i s) (A i t) (X i s) (X i t)
        _ ≤ KA i * (HX i * |s - t| ^ theta) +
              (HA i * |s - t| ^ theta) * KX i := by
          exact add_le_add
            (mul_le_mul (hA_bound i) (hX_holder i)
              (norm_nonneg _) (hA_nonneg i))
            (mul_le_mul (hA_holder i) (hX_bound i)
              (norm_nonneg _) (mul_nonneg (hHA_nonneg i) hrpow))
        _ = (KA i * HX i + HA i * KX i) * |s - t| ^ theta := by
          ring
    _ = (∑ i, (KA i * HX i + HA i * KX i)) *
          |s - t| ^ theta := by
      rw [Finset.sum_mul]

end OperatorProducts

section AxiomAudit

#print axioms continuousLinearMap_apply_sub_apply_norm_le
#print axioms finite_operator_source_holder
#print axioms wholeLineRealL2Multiplier_coe_ae
#print axioms wholeLineRealL2Multiplier_norm_le
#print axioms wholeLineRealLInfOfBound_coe_ae
#print axioms wholeLineRealLInfOfBound_norm_le

end AxiomAudit

end ShenWork.Paper1
