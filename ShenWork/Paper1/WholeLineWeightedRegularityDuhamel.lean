import ShenWork.Paper1.WholeLineWeightedRegularityTime
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Filter MeasureTheory Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Whole-line `L²` lifts for weighted Duhamel histories

The BUC mild formula is pointwise in space, whereas the Henry estimate is
an estimate in the Hilbert space `L²(ℝ)`.  This file records the concrete
bridge from a square-integrable representative to `WholeLineRealL2` and the
Bochner triangle inequality used for its Duhamel history.  In particular,
the time derivative of the quadratic energy can subsequently be obtained
from `paper5WeightedHalfEnergy_hasDerivAt_of_L2_differenceQuotient`, without
postulating a pointwise-in-space common dominator.
-/

/-- The canonical `L²(ℝ)` class of a measurable square-integrable real
function. -/
def wholeLineRealL2OfSqIntegrable
    (f : ℝ → ℝ) (hf_meas : AEStronglyMeasurable f volume)
    (hf_sq : Integrable (fun x => f x ^ 2) volume) : WholeLineRealL2 :=
  (MeasureTheory.memLp_two_iff_integrable_sq hf_meas).2 hf_sq |>.toLp f

/-- The canonical lift agrees almost everywhere with its representative. -/
theorem wholeLineRealL2OfSqIntegrable_coe_ae
    (f : ℝ → ℝ) (hf_meas : AEStronglyMeasurable f volume)
    (hf_sq : Integrable (fun x => f x ^ 2) volume) :
    ((wholeLineRealL2OfSqIntegrable f hf_meas hf_sq : WholeLineRealL2) :
        ℝ → ℝ) =ᵐ[volume] f := by
  exact MeasureTheory.MemLp.coeFn_toLp
    ((MeasureTheory.memLp_two_iff_integrable_sq hf_meas).2 hf_sq)

/-- The squared Hilbert norm of the canonical lift is the concrete square
integral of its representative. -/
theorem wholeLineRealL2OfSqIntegrable_norm_sq
    (f : ℝ → ℝ) (hf_meas : AEStronglyMeasurable f volume)
    (hf_sq : Integrable (fun x => f x ^ 2) volume) :
    ‖wholeLineRealL2OfSqIntegrable f hf_meas hf_sq‖ ^ 2 =
      ∫ x : ℝ, f x ^ 2 := by
  let Z : WholeLineRealL2 :=
    wholeLineRealL2OfSqIntegrable f hf_meas hf_sq
  have hrep : (Z : ℝ → ℝ) =ᵐ[volume] f :=
    wholeLineRealL2OfSqIntegrable_coe_ae f hf_meas hf_sq
  have hinner := wholeLineIntegral_mul_eq_inner_of_aeEq Z Z hrep hrep
  rw [real_inner_self_eq_norm_sq] at hinner
  simpa [Z, pow_two] using hinner.symm

/-- The native Bochner estimate for a whole-line `L²` Duhamel history. -/
theorem wholeLineRealL2_intervalIntegral_norm_le
    {a b : ℝ} (hab : a ≤ b) {Z : ℝ → WholeLineRealL2} :
    ‖∫ s in a..b, Z s‖ ≤ ∫ s in a..b, ‖Z s‖ := by
  exact intervalIntegral.norm_integral_le_integral_norm hab

/-- A pointwise scalar majorant for the `L²` norm controls the Bochner
Duhamel history.  All integrability hypotheses are explicit, so this lemma
cannot silently use Mathlib's convention that a non-integrable integral is
zero. -/
theorem wholeLineRealL2_intervalIntegral_norm_le_of_majorant
    {a b : ℝ} (hab : a ≤ b) {Z : ℝ → WholeLineRealL2} {g : ℝ → ℝ}
    (hZ : IntervalIntegrable Z volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hmajor : ∀ s ∈ Set.Icc a b, ‖Z s‖ ≤ g s) :
    ‖∫ s in a..b, Z s‖ ≤ ∫ s in a..b, g s := by
  calc
    ‖∫ s in a..b, Z s‖ ≤ ∫ s in a..b, ‖Z s‖ :=
      wholeLineRealL2_intervalIntegral_norm_le hab
    _ ≤ ∫ s in a..b, g s :=
      intervalIntegral.integral_mono_on hab hZ.norm hg hmajor

/-- Squared form of the majorant estimate, matching the cap-energy
bookkeeping used later. -/
theorem wholeLineRealL2_intervalIntegral_norm_sq_le_of_majorant
    {a b : ℝ} (hab : a ≤ b) {Z : ℝ → WholeLineRealL2} {g : ℝ → ℝ}
    (hZ : IntervalIntegrable Z volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hg_nonneg : ∀ s ∈ Set.Icc a b, 0 ≤ g s)
    (hmajor : ∀ s ∈ Set.Icc a b, ‖Z s‖ ≤ g s) :
    ‖∫ s in a..b, Z s‖ ^ 2 ≤ (∫ s in a..b, g s) ^ 2 := by
  have hle := wholeLineRealL2_intervalIntegral_norm_le_of_majorant
    hab hZ hg hmajor
  have hleft : 0 ≤ ‖∫ s in a..b, Z s‖ := norm_nonneg _
  have hright : 0 ≤ ∫ s in a..b, g s :=
    intervalIntegral.integral_nonneg hab hg_nonneg
  nlinarith

/-- The locally integrable singular kernel occurring in the spatial
gradient of the heat Duhamel term. -/
theorem intervalIntegrable_invSqrt_sub
    {t : ℝ} :
    IntervalIntegrable
      (fun s : ℝ => (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t := by
  have hbase : IntervalIntegrable
      (fun r : ℝ => r ^ (-(1 / 2 : ℝ))) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hcomp := hbase.comp_sub_left t
  simpa using hcomp.symm

/-- Exact mass of the heat-gradient singular kernel on a forward time
interval. -/
theorem intervalIntegral_invSqrt_sub_eq_two_sqrt
    {t : ℝ} (_ht : 0 < t) :
    ∫ s in (0 : ℝ)..t, (t - s) ^ (-(1 / 2 : ℝ)) =
      2 * Real.sqrt t := by
  have hcomp :
      (∫ s in (0 : ℝ)..t, (t - s) ^ (-(1 / 2 : ℝ))) =
        ∫ r in (t - t)..(t - 0), r ^ (-(1 / 2 : ℝ)) := by
    rw [intervalIntegral.integral_comp_sub_left
      (fun r : ℝ => r ^ (-(1 / 2 : ℝ))) t]
  rw [hcomp]
  norm_num
  have hrpow := integral_rpow
    (a := (0 : ℝ)) (b := t) (r := -(1 / 2 : ℝ))
    (Or.inl (by norm_num))
  rw [hrpow]
  have hzero : (0 : ℝ) ^ (1 / 2 : ℝ) = 0 :=
    Real.zero_rpow (by norm_num)
  rw [show (-(1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) by ring,
    hzero, sub_zero, show t ^ (1 / 2 : ℝ) = Real.sqrt t by
      exact (Real.sqrt_eq_rpow t).symm]
  ring

/-- The heat-gradient Duhamel history has the expected `2√t` Hilbert-norm
bound.  The endpoint convention is left visible in `hmajor`; for the
totalized moving heat-gradient operator its zero-time value is zero. -/
theorem wholeLineRealL2_intervalIntegral_norm_le_invSqrt
    {t A : ℝ} (ht : 0 < t)
    {Z : ℝ → WholeLineRealL2}
    (hZ : IntervalIntegrable Z volume 0 t)
    (hmajor : ∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖Z s‖ ≤ A * (t - s) ^ (-(1 / 2 : ℝ))) :
    ‖∫ s in (0 : ℝ)..t, Z s‖ ≤ 2 * A * Real.sqrt t := by
  let g : ℝ → ℝ := fun s => A * (t - s) ^ (-(1 / 2 : ℝ))
  have hg : IntervalIntegrable g volume 0 t :=
    intervalIntegrable_invSqrt_sub.const_mul A
  have hbound := wholeLineRealL2_intervalIntegral_norm_le_of_majorant
    ht.le hZ hg hmajor
  calc
    ‖∫ s in (0 : ℝ)..t, Z s‖ ≤ ∫ s in (0 : ℝ)..t, g s := hbound
    _ = A * ∫ s in (0 : ℝ)..t,
        (t - s) ^ (-(1 / 2 : ℝ)) := by
      dsimp only [g]
      rw [intervalIntegral.integral_const_mul]
    _ = A * (2 * Real.sqrt t) := by
      rw [intervalIntegral_invSqrt_sub_eq_two_sqrt ht]
    _ = 2 * A * Real.sqrt t := by ring

section AxiomAudit

#print axioms wholeLineRealL2OfSqIntegrable_coe_ae
#print axioms wholeLineRealL2OfSqIntegrable_norm_sq
#print axioms wholeLineRealL2_intervalIntegral_norm_le_of_majorant
#print axioms wholeLineRealL2_intervalIntegral_norm_sq_le_of_majorant
#print axioms intervalIntegral_invSqrt_sub_eq_two_sqrt
#print axioms wholeLineRealL2_intervalIntegral_norm_le_invSqrt

end AxiomAudit

end ShenWork.Paper1
