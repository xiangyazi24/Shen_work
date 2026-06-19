import ShenWork.PaperOne.WholeLineAuxiliaryMildMap
import ShenWork.PaperOne.WholeLineExponentialBarriers
import ShenWork.PaperOne.WholeLineWeakParabolicComparison
import Mathlib.Tactic

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-!
Exponential-barrier trapping for the auxiliary moving-frame equation.

The analytic comparison layer is closed here by reusing
`wholeLine_weak_parabolic_comparison`.  The branchwise exponential barrier
residual inequalities are recorded as named hypotheses with the explicit
exponent bookkeeping; discharging those inequalities is the carried algebraic
part.
-/

/-- The exponential tail `e^{-κx}`. -/
def expBarrierTail (κ x : ℝ) : ℝ :=
  Real.exp (-κ * x)

/-- The lower-barrier core before truncation by `max 0`. -/
def lowerBarrierCore (κ κt D x : ℝ) : ℝ :=
  expBarrierTail κ x - D * expBarrierTail κt x

/-- Spatial derivative of the pure upper exponential branch. -/
def upperExpBranchDx (κ x : ℝ) : ℝ :=
  -κ * expBarrierTail κ x

/-- Spatial second derivative of the pure upper exponential branch. -/
def upperExpBranchDxx (κ x : ℝ) : ℝ :=
  κ ^ 2 * expBarrierTail κ x

/-- Spatial derivative of the positive lower-barrier branch. -/
def lowerPositiveBranchDx (κ κt D x : ℝ) : ℝ :=
  -κ * expBarrierTail κ x + D * κt * expBarrierTail κt x

/-- Spatial second derivative of the positive lower-barrier branch. -/
def lowerPositiveBranchDxx (κ κt D x : ℝ) : ℝ :=
  κ ^ 2 * expBarrierTail κ x - D * κt ^ 2 * expBarrierTail κt x

/--
Stationary auxiliary residual, written with the sign convention requested for
the barrier checks: `N[B] = B_xx + c B_x + F(B, B_x; V, V_x)`.
-/
def auxiliaryStationaryResidual (p : CMParams) (c : ℝ)
    (B Bx Bxx V Vx : ℝ → ℝ) (x : ℝ) : ℝ :=
  Bxx x + c * Bx x + auxiliaryFrozenNonlinearity p B Bx V Vx x

/-- Expanded residual on the upper exponential branch `B=e^{-κx}`. -/
def upperExponentialBranchResidual
    (p : CMParams) (c κ : ℝ) (V Vx : ℝ → ℝ) (x : ℝ) : ℝ :=
  (κ ^ 2 - c * κ + 1) * expBarrierTail κ x
    - (expBarrierTail κ x) ^ (p.α + 1)
    - p.χ * p.m * (expBarrierTail κ x) ^ (p.m - 1)
        * upperExpBranchDx κ x * Vx x
    - p.χ * (expBarrierTail κ x) ^ p.m * V x
    + p.χ * (expBarrierTail κ x) ^ (p.m + p.γ)

/--
Expanded residual on the positive branch of the lower barrier
`B=e^{-κx}-D e^{-κ̃x}`.
-/
def lowerPositiveBranchResidual
    (p : CMParams) (c κ κt D : ℝ) (V Vx : ℝ → ℝ) (x : ℝ) : ℝ :=
  (κ ^ 2 - c * κ + 1) * expBarrierTail κ x
    - D * (κt ^ 2 - c * κt + 1) * expBarrierTail κt x
    - (lowerBarrierCore κ κt D x) ^ (p.α + 1)
    - p.χ * p.m * (lowerBarrierCore κ κt D x) ^ (p.m - 1)
        * lowerPositiveBranchDx κ κt D x * Vx x
    - p.χ * (lowerBarrierCore κ κt D x) ^ p.m * V x
    + p.χ * (lowerBarrierCore κ κt D x) ^ (p.m + p.γ)

/-- Parameter hypotheses used by the exponential barriers. -/
structure ExponentialBarrierParameterData
    (p : CMParams) (c κ κt D : ℝ) : Prop where
  kappa_quadratic : κ ^ 2 - c * κ + 1 = 0
  kappa_nonneg : 0 ≤ κ
  kappa_lt_kappat : κ < κt
  D_ge_one : 1 ≤ D
  kappat_le_alpha : κt ≤ (1 + p.α) * κ
  kappat_le_m : κt ≤ p.m * κ + 1 / 2
  kappat_le_one : κt ≤ 1

/-- Build the parameter package when `κ` is chosen as `waveExponent c`. -/
theorem exponentialBarrierParameterData_of_waveExponent
    {p : CMParams} {c κt D : ℝ}
    (hc : 2 ≤ c)
    (hκt : waveExponent c < κt)
    (hD : 1 ≤ D)
    (hκtα : κt ≤ (1 + p.α) * waveExponent c)
    (hκtm : κt ≤ p.m * waveExponent c + 1 / 2)
    (hκt1 : κt ≤ 1) :
    ExponentialBarrierParameterData p c (waveExponent c) κt D where
  kappa_quadratic := waveExponent_quadratic hc
  kappa_nonneg := (waveExponent_pos hc).le
  kappa_lt_kappat := hκt
  D_ge_one := hD
  kappat_le_alpha := hκtα
  kappat_le_m := hκtm
  kappat_le_one := hκt1

/--
Branchwise residual inequalities for the exponential barriers.

`upper_exp_branch` and `lower_positive_branch` expose the exact exponent
bookkeeping where `κ²-cκ+1=0` removes the leading upper tail and the
`κ̃` bounds are meant to dominate the lower correction.
-/
structure WholeLineExponentialBarrierInequalities
    (p : CMParams) (c κ κt D : ℝ) (V Vx : ℝ → ℝ) : Prop where
  params : ExponentialBarrierParameterData p c κ κt D
  upper_constant_branch :
    ∀ x, x ≤ 0 →
      0 ≤ auxiliaryStationaryResidual p c
        (fun _ : ℝ => 1) (fun _ : ℝ => 0) (fun _ : ℝ => 0) V Vx x
  upper_exp_branch :
    ∀ x, 0 ≤ x →
      0 ≤ upperExponentialBranchResidual p c κ V Vx x
  lower_zero_branch :
    ∀ x, lowerBarrierCore κ κt D x ≤ 0 →
      auxiliaryStationaryResidual p c
        (fun _ : ℝ => 0) (fun _ : ℝ => 0) (fun _ : ℝ => 0) V Vx x ≤ 0
  lower_positive_branch :
    ∀ x, 0 < lowerBarrierCore κ κt D x →
      lowerPositiveBranchResidual p c κ κt D V Vx x ≤ 0

/-- Weak-comparison data for the upper test `q=w-U⁺`. -/
structure WholeLineExponentialUpperComparisonData
    (κ T : ℝ) (w : ℝ → ℝ → ℝ) where
  qt : ℝ → ℝ → ℝ
  qx : ℝ → ℝ → ℝ
  qxx : ℝ → ℝ → ℝ
  a : ℝ → ℝ → ℝ
  b : ℝ → ℝ → ℝ
  A : ℝ
  Bb : ℝ
  comparison :
    WholeLineWeakParabolicComparisonData
      (fun t x => w t x - upperBarrier κ x) qt qx qxx a b T A Bb

/-- Weak-comparison data for the lower test `q=U⁻-w`. -/
structure WholeLineExponentialLowerComparisonData
    (κ κt D T : ℝ) (w : ℝ → ℝ → ℝ) where
  qt : ℝ → ℝ → ℝ
  qx : ℝ → ℝ → ℝ
  qxx : ℝ → ℝ → ℝ
  a : ℝ → ℝ → ℝ
  b : ℝ → ℝ → ℝ
  A : ℝ
  Bb : ℝ
  comparison :
    WholeLineWeakParabolicComparisonData
      (fun t x => lowerBarrier κ κt D x - w t x) qt qx qxx a b T A Bb

/--
Finite-horizon data: barrier residual inequalities plus the two weak-comparison
packages generated by applying the auxiliary equation to `w-U⁺` and `U⁻-w`.
-/
structure WholeLineExponentialBarrierTrappingData
    (p : CMParams) (c κ κt D T : ℝ)
    (w : ℝ → ℝ → ℝ) (V Vx : ℝ → ℝ) where
  barrier_ineq : WholeLineExponentialBarrierInequalities p c κ κt D V Vx
  upper : WholeLineExponentialUpperComparisonData κ T w
  lower : WholeLineExponentialLowerComparisonData κ κt D T w

/-- Upper exponential trapping on a finite horizon. -/
theorem wholeLine_exponential_upperBarrier_trapping_on
    {κ T : ℝ} {w : ℝ → ℝ → ℝ}
    (hinit : ∀ x, w 0 x = upperBarrier κ x)
    (H : WholeLineExponentialUpperComparisonData κ T w) :
    ∀ t, 0 ≤ t → t ≤ T → ∀ x, w t x ≤ upperBarrier κ x := by
  have hq0 : ∀ x, w 0 x - upperBarrier κ x ≤ 0 := by
    intro x
    rw [hinit x]
    linarith
  have hcomp :
      ∀ t, 0 ≤ t → t ≤ T → ∀ x,
        w t x - upperBarrier κ x ≤ 0 :=
    wholeLine_weak_parabolic_comparison
      (q := fun t x => w t x - upperBarrier κ x)
      (qt := H.qt) (qx := H.qx) (qxx := H.qxx)
      (a := H.a) (b := H.b) (T := T) (A := H.A) (Bb := H.Bb)
      hq0 H.comparison
  intro t ht0 htT x
  have h := hcomp t ht0 htT x
  linarith

/-- Lower exponential trapping on a finite horizon. -/
theorem wholeLine_exponential_lowerBarrier_trapping_on
    {κ κt D T : ℝ} {w : ℝ → ℝ → ℝ}
    (hκ : 0 ≤ κ) (hκt : κ < κt) (hD : 1 ≤ D)
    (hinit : ∀ x, w 0 x = upperBarrier κ x)
    (H : WholeLineExponentialLowerComparisonData κ κt D T w) :
    ∀ t, 0 ≤ t → t ≤ T → ∀ x, lowerBarrier κ κt D x ≤ w t x := by
  have hq0 : ∀ x, lowerBarrier κ κt D x - w 0 x ≤ 0 := by
    intro x
    rw [hinit x]
    have hle := lowerBarrier_le_upper (κ := κ) (κt := κt) (D := D) (x := x)
      hκ hκt hD
    linarith
  have hcomp :
      ∀ t, 0 ≤ t → t ≤ T → ∀ x,
        lowerBarrier κ κt D x - w t x ≤ 0 :=
    wholeLine_weak_parabolic_comparison
      (q := fun t x => lowerBarrier κ κt D x - w t x)
      (qt := H.qt) (qx := H.qx) (qxx := H.qxx)
      (a := H.a) (b := H.b) (T := T) (A := H.A) (Bb := H.Bb)
      hq0 H.comparison
  intro t ht0 htT x
  have h := hcomp t ht0 htT x
  linarith

/-- Exponential-barrier trapping on a finite closed time horizon. -/
theorem wholeLine_exponential_barrier_trapping_on
    {p : CMParams} {c κ κt D T : ℝ}
    {w : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ}
    (hinit : ∀ x, w 0 x = upperBarrier κ x)
    (H : WholeLineExponentialBarrierTrappingData p c κ κt D T w V Vx) :
    ∀ t, 0 ≤ t → t ≤ T → ∀ x,
      lowerBarrier κ κt D x ≤ w t x ∧ w t x ≤ upperBarrier κ x := by
  intro t ht0 htT x
  have hupper :=
    wholeLine_exponential_upperBarrier_trapping_on hinit H.upper t ht0 htT x
  have hlower :=
    wholeLine_exponential_lowerBarrier_trapping_on
      H.barrier_ineq.params.kappa_nonneg
      H.barrier_ineq.params.kappa_lt_kappat
      H.barrier_ineq.params.D_ge_one
      hinit H.lower t ht0 htT x
  exact ⟨hlower, hupper⟩

/--
Global exponential-barrier trapping.  The finite-horizon comparison data may be
supplied on every positive horizon; choosing `T=t+1` closes each time slice.
-/
theorem wholeLine_exponential_barrier_trapping
    {p : CMParams} {c κ κt D : ℝ}
    {w : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ}
    (hinit : ∀ x, w 0 x = upperBarrier κ x)
    (H : ∀ T, 0 < T →
      WholeLineExponentialBarrierTrappingData p c κ κt D T w V Vx) :
    ∀ t, 0 ≤ t → ∀ x,
      lowerBarrier κ κt D x ≤ w t x ∧ w t x ≤ upperBarrier κ x := by
  intro t ht0 x
  have hTpos : 0 < t + 1 := by linarith
  have htT : t ≤ t + 1 := by linarith
  exact wholeLine_exponential_barrier_trapping_on
    hinit (H (t + 1) hTpos) t ht0 htT x

#print axioms wholeLine_exponential_upperBarrier_trapping_on
#print axioms wholeLine_exponential_lowerBarrier_trapping_on
#print axioms wholeLine_exponential_barrier_trapping_on
#print axioms wholeLine_exponential_barrier_trapping
#print axioms exponentialBarrierParameterData_of_waveExponent

end ShenWork.PaperOne
