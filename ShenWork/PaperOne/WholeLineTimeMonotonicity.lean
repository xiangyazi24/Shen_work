import ShenWork.PaperOne.WholeLineWeakParabolicComparison

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-!
Time monotonicity of the auxiliary whole-line parabolic flow, reduced to the
weak comparison principle from `WholeLineWeakParabolicComparison`.

The nonlinear difference calculation is kept as named data: the shifted
difference `q(t,x) = w(t+s,x) - w(t,x)` is assumed to satisfy a pointwise
linearized inequality with coefficients `a,b`.  This file only converts that
linearized inequality to Brick 7's weighted PDE datum and applies the banked
comparison theorem.
-/

/-- Difference between a time-shifted slice and the current slice. -/
def wholeLineTimeShiftDifference (w : ℝ → ℝ → ℝ) (s t x : ℝ) : ℝ :=
  w (t + s) x - w t x

/-- A pointwise linear parabolic inequality for a whole-line difference field. -/
structure WholeLineLinearizedPDEData
    (q qt qx qxx a b : ℝ → ℝ → ℝ) (T : ℝ) where
  time_int : ∀ t, 0 < t → t < T →
    Integrable (fun x : ℝ => wholeLineQPositivePart q t x * qt t x) volume
  diffusion_int : ∀ t, 0 < t → t < T →
    Integrable (fun x : ℝ => wholeLineQPositivePart q t x * qxx t x) volume
  drift_int : ∀ t, 0 < t → t < T →
    Integrable
      (fun x : ℝ => wholeLineQPositivePart q t x * (a t x * qx t x))
      volume
  reaction_int : ∀ t, 0 < t → t < T →
    Integrable
      (fun x : ℝ => b t x * (wholeLineQPositivePart q t x) ^ 2)
      volume
  pointwise_ineq : ∀ t, 0 < t → t < T →
    ∀ᵐ x ∂volume, qt t x ≤ qxx t x + a t x * qx t x + b t x * q t x

/-- On the positive part support, multiplying by `q` is the same as multiplying
by `q_+`. -/
theorem wholeLineQPositivePart_mul_self_eq_sq
    (q : ℝ → ℝ → ℝ) (t x : ℝ) :
    wholeLineQPositivePart q t x * q t x =
      (wholeLineQPositivePart q t x) ^ 2 := by
  unfold wholeLineQPositivePart
  by_cases hx : 0 < q t x
  · rw [max_eq_left (le_of_lt hx)]
    ring
  · rw [max_eq_right (not_lt.mp hx)]
    ring

/-- Algebraic rewriting of the linearized right-hand side after weighting by
the positive part. -/
theorem wholeLineQPositivePart_mul_linearized_rhs
    (q qx qxx a b : ℝ → ℝ → ℝ) (t x : ℝ) :
    wholeLineQPositivePart q t x
        * (qxx t x + a t x * qx t x + b t x * q t x)
      =
        wholeLineQPositivePart q t x * qxx t x
          + wholeLineQPositivePart q t x * (a t x * qx t x)
          + b t x * (wholeLineQPositivePart q t x) ^ 2 := by
  have hq :
      wholeLineQPositivePart q t x * q t x =
        (wholeLineQPositivePart q t x) ^ 2 :=
    wholeLineQPositivePart_mul_self_eq_sq q t x
  calc
    wholeLineQPositivePart q t x
        * (qxx t x + a t x * qx t x + b t x * q t x)
        =
          wholeLineQPositivePart q t x * qxx t x
            + wholeLineQPositivePart q t x * (a t x * qx t x)
            + b t x * (wholeLineQPositivePart q t x * q t x) := by
          ring
    _ =
        wholeLineQPositivePart q t x * qxx t x
          + wholeLineQPositivePart q t x * (a t x * qx t x)
          + b t x * (wholeLineQPositivePart q t x) ^ 2 := by
        rw [hq]

/-- Convert the pointwise linearized inequality to Brick 7's weighted PDE
integral datum. -/
def wholeLineWeakParabolicPDEIntegralData_of_linearized
    {q qt qx qxx a b : ℝ → ℝ → ℝ} {T : ℝ}
    (H : WholeLineLinearizedPDEData q qt qx qxx a b T) :
    WholeLineWeakParabolicPDEIntegralData q qt qx qxx a b T where
  time_int := H.time_int
  diffusion_int := H.diffusion_int
  drift_int := H.drift_int
  reaction_int := H.reaction_int
  weighted_ineq := by
    intro t ht0 htT
    filter_upwards [H.pointwise_ineq t ht0 htT] with x hx
    have hnonneg : 0 ≤ wholeLineQPositivePart q t x :=
      wholeLineQPositivePart_nonneg q t x
    have hmul :
        wholeLineQPositivePart q t x * qt t x ≤
          wholeLineQPositivePart q t x
            * (qxx t x + a t x * qx t x + b t x * q t x) :=
      mul_le_mul_of_nonneg_left hx hnonneg
    calc
      wholeLineQPositivePart q t x * qt t x
          ≤
            wholeLineQPositivePart q t x
              * (qxx t x + a t x * qx t x + b t x * q t x) := hmul
      _ =
          wholeLineQPositivePart q t x * qxx t x
            + wholeLineQPositivePart q t x * (a t x * qx t x)
            + b t x * (wholeLineQPositivePart q t x) ^ 2 := by
          rw [wholeLineQPositivePart_mul_linearized_rhs]

/-- Named hypotheses for time monotonicity of a shifted auxiliary flow.

`linearizedPDE` is the mean-value linearization of the difference between two
time-shifted copies of the same auxiliary equation.  The remaining fields are
exactly the comparison-side regularity and coercivity data required by Brick 7. -/
structure WholeLineTimeMonotonicityData
    (w wt wx wxx : ℝ → ℝ → ℝ) (Uplus : ℝ → ℝ)
    (a b : ℝ → ℝ → ℝ) (s T A Bb : ℝ) where
  shift_pos : 0 < s
  initial_eq_upper : ∀ x, w 0 x = Uplus x
  upper_trap_at_shift : ∀ x, w s x ≤ Uplus x
  linearizedPDE :
    WholeLineLinearizedPDEData
      (wholeLineTimeShiftDifference w s)
      (wholeLineTimeShiftDifference wt s)
      (wholeLineTimeShiftDifference wx s)
      (wholeLineTimeShiftDifference wxx s)
      a b T
  A_nonneg : 0 ≤ A
  Bb_nonneg : 0 ≤ Bb
  a_bound : ∀ t, 0 < t → t < T → ∀ x, |a t x| ≤ A
  b_bound : ∀ t, 0 < t → t < T → ∀ x, |b t x| ≤ Bb
  cont : ∀ r t, 0 < r → r ≤ t → t < T →
    ContinuousOn
      (wholeLineWeakParabolicEnergy (wholeLineTimeShiftDifference w s))
      (Set.Icc r t)
  endpoint_cont : ∀ r, 0 < r → r ≤ T →
    ContinuousOn
      (wholeLineWeakParabolicEnergy (wholeLineTimeShiftDifference w s))
      (Set.Icc r T)
  initial_vanishes : ∀ ε > 0, ∃ δ > 0, ∀ r, 0 < r → r < δ → r < T →
    wholeLineWeakParabolicEnergy (wholeLineTimeShiftDifference w s) r < ε
  timeLeibniz :
    WholeLineWeakParabolicTimeLeibnizData
      (wholeLineTimeShiftDifference w s)
      (wholeLineTimeShiftDifference wt s) T
  diffusion :
    WholeLineWeakParabolicDiffusionIBPData
      (wholeLineTimeShiftDifference w s)
      (wholeLineTimeShiftDifference wxx s) T
  positivePart_sq_int : ∀ t, 0 < t → t < T →
    Integrable
      (fun x : ℝ =>
        (wholeLineQPositivePart (wholeLineTimeShiftDifference w s) t x) ^ 2)
      volume
  flux_drift_int : ∀ t, 0 < t → t < T →
    Integrable
      (fun x : ℝ =>
        wholeLineQPositivePart (wholeLineTimeShiftDifference w s) t x
          * (a t x * diffusion.flux t x))
      volume
  qx_eq_flux_on_pos : ∀ t, 0 < t → t < T →
    ∀ x, 0 < wholeLineTimeShiftDifference w s t x →
      wholeLineTimeShiftDifference wx s t x = diffusion.flux t x
  energy_zero_controls : ∀ t, 0 < t → t ≤ T →
    wholeLineWeakParabolicEnergy (wholeLineTimeShiftDifference w s) t = 0 →
      ∀ x, wholeLineTimeShiftDifference w s t x ≤ 0

/-- Assemble the Brick 7 comparison datum for the shifted difference. -/
def WholeLineTimeMonotonicityData.toComparisonData
    {w wt wx wxx : ℝ → ℝ → ℝ} {Uplus : ℝ → ℝ}
    {a b : ℝ → ℝ → ℝ} {s T A Bb : ℝ}
    (H : WholeLineTimeMonotonicityData w wt wx wxx Uplus a b s T A Bb) :
    WholeLineWeakParabolicComparisonData
      (wholeLineTimeShiftDifference w s)
      (wholeLineTimeShiftDifference wt s)
      (wholeLineTimeShiftDifference wx s)
      (wholeLineTimeShiftDifference wxx s)
      a b T A Bb where
  A_nonneg := H.A_nonneg
  Bb_nonneg := H.Bb_nonneg
  a_bound := H.a_bound
  b_bound := H.b_bound
  cont := H.cont
  endpoint_cont := H.endpoint_cont
  initial_vanishes := H.initial_vanishes
  timeLeibniz := H.timeLeibniz
  pde := wholeLineWeakParabolicPDEIntegralData_of_linearized H.linearizedPDE
  diffusion := H.diffusion
  positivePart_sq_int := H.positivePart_sq_int
  flux_drift_int := H.flux_drift_int
  qx_eq_flux_on_pos := H.qx_eq_flux_on_pos
  energy_zero_controls := H.energy_zero_controls

/-- The shifted difference has nonpositive initial trace because the orbit starts
from the upper barrier and the shifted slice remains below that barrier. -/
theorem wholeLine_timeShiftDifference_initial_nonpos
    {w wt wx wxx : ℝ → ℝ → ℝ} {Uplus : ℝ → ℝ}
    {a b : ℝ → ℝ → ℝ} {s T A Bb : ℝ}
    (H : WholeLineTimeMonotonicityData w wt wx wxx Uplus a b s T A Bb) :
    ∀ x, wholeLineTimeShiftDifference w s 0 x ≤ 0 := by
  intro x
  calc
    wholeLineTimeShiftDifference w s 0 x = w s x - Uplus x := by
      rw [wholeLineTimeShiftDifference, zero_add, H.initial_eq_upper x]
    _ ≤ 0 := sub_nonpos.mpr (H.upper_trap_at_shift x)

/-- Time monotonicity of the auxiliary whole-line flow:
`w(t+s,x) ≤ w(t,x)` for every `0 ≤ t ≤ T`. -/
theorem wholeLine_time_monotone
    {w wt wx wxx : ℝ → ℝ → ℝ} {Uplus : ℝ → ℝ}
    {a b : ℝ → ℝ → ℝ} {s T A Bb : ℝ}
    (H : WholeLineTimeMonotonicityData w wt wx wxx Uplus a b s T A Bb) :
    ∀ t, 0 ≤ t → t ≤ T → ∀ x, w (t + s) x ≤ w t x := by
  intro t ht0 htT x
  have hq :
      wholeLineTimeShiftDifference w s t x ≤ 0 :=
    wholeLine_weak_parabolic_comparison
      (q := wholeLineTimeShiftDifference w s)
      (qt := wholeLineTimeShiftDifference wt s)
      (qx := wholeLineTimeShiftDifference wx s)
      (qxx := wholeLineTimeShiftDifference wxx s)
      (a := a) (b := b) (T := T) (A := A) (Bb := Bb)
      (hinitial := wholeLine_timeShiftDifference_initial_nonpos H)
      (H := H.toComparisonData) t ht0 htT x
  have hsub : w (t + s) x - w t x ≤ 0 := by
    simpa [wholeLineTimeShiftDifference] using hq
  exact sub_nonpos.mp hsub

#print axioms wholeLineQPositivePart_mul_self_eq_sq
#print axioms wholeLineQPositivePart_mul_linearized_rhs
#print axioms wholeLineWeakParabolicPDEIntegralData_of_linearized
#print axioms WholeLineTimeMonotonicityData.toComparisonData
#print axioms wholeLine_timeShiftDifference_initial_nonpos
#print axioms wholeLine_time_monotone

end ShenWork.PaperOne
