import ShenWork.PDE.P3MoserEnergyContinuity
import ShenWork.Paper2.IntervalDomainL2HalfEnergyTimeLeibniz

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

theorem intervalDomainLpAbsEnergy_two_eq_domain_powerEnergy
    (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) :
    intervalDomainLpAbsEnergy 2 u t =
      intervalDomain.integral (fun x : intervalDomain.Point => (u t x) ^ (2 : ℝ)) := by
  unfold intervalDomainLpAbsEnergy intervalDomain
  change
    intervalDomainIntegral (fun x : intervalDomain.Point => |u t x| ^ (2 : ℝ)) =
      intervalDomainIntegral (fun x : intervalDomain.Point => (u t x) ^ (2 : ℝ))
  unfold intervalDomainIntegral
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le (zero_le_one)] at hy
  unfold intervalDomainLift
  rw [dif_pos hy, dif_pos hy]
  simp [sq_abs]

theorem intervalDomainLpAbsEnergy_two_eq_powerEnergy
    (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) :
    intervalDomainLpAbsEnergy 2 u t = intervalDomainPowerEnergy 2 u t := by
  unfold intervalDomainLpAbsEnergy intervalDomainPowerEnergy intervalDomain
  change
    intervalDomainIntegral (fun x : intervalDomain.Point => |u t x| ^ (2 : ℝ)) =
      ∫ y in (0 : ℝ)..1, (intervalDomainLift (u t) y) ^ (2 : ℝ)
  unfold intervalDomainIntegral
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le (zero_le_one)] at hy
  unfold intervalDomainLift
  rw [dif_pos hy, dif_pos hy]
  simp [sq_abs]

theorem intervalDomainLpAbsEnergy_two_eq_two_mul_L2HalfEnergy
    (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) :
    intervalDomainLpAbsEnergy 2 u t = 2 * intervalDomainL2HalfEnergy u t := by
  unfold intervalDomainLpAbsEnergy intervalDomainL2HalfEnergy intervalDomain
  change
    intervalDomainIntegral (fun x : intervalDomain.Point => |u t x| ^ (2 : ℝ)) =
      2 * ((1 / 2 : ℝ) *
        intervalDomainIntegral (fun x : intervalDomain.Point => (u t x) ^ 2))
  have hcongr :
      intervalDomainIntegral (fun x : intervalDomain.Point => |u t x| ^ (2 : ℝ)) =
        intervalDomainIntegral (fun x : intervalDomain.Point => (u t x) ^ 2) := by
    unfold intervalDomainIntegral
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le (zero_le_one)] at hy
    unfold intervalDomainLift
    rw [dif_pos hy, dif_pos hy]
    simp [sq_abs]
  rw [hcongr]
  ring

theorem intervalDomainLpAbsEnergy_two_nonneg
    (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) :
    0 ≤ intervalDomainLpAbsEnergy 2 u t := by
  unfold intervalDomainLpAbsEnergy intervalDomain intervalDomainIntegral
  refine intervalIntegral.integral_nonneg (by norm_num) (fun y hy => ?_)
  unfold intervalDomainLift
  rw [dif_pos hy]
  exact Real.rpow_nonneg (abs_nonneg (u t ⟨y, hy⟩)) 2

/-- The `t = 0` right-derivative input needed by
`IntervalDomainL2SeedRegularityFrontier`.

`IsPaper2ClassicalSolution` only gives time differentiability on `(0,T)`, while
endpoint energy continuity gives continuity but not a one-sided derivative. -/
def IntervalDomainL2SeedZeroRightDerivative
    (u : ℝ → intervalDomain.Point → ℝ) : Prop :=
  HasDerivWithinAt
    (fun τ => intervalDomainLpAbsEnergy 2 u τ)
    (deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) 0)
    (Set.Ici (0 : ℝ)) 0

/-- Build the closed-time L² seed frontier from a classical solution, closed
endpoint power-energy continuity, and the explicit zero-time right derivative
required by the frontier interface. -/
theorem intervalDomainL2SeedRegularityFrontier_of_classical_and_endpointContinuity
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (_hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hendpoint : IntervalDomainPowerEnergyEndpointContinuity u T 2)
    (hzero : IntervalDomainL2SeedZeroRightDerivative u) :
    IntervalDomainL2SeedRegularityFrontier T u where
  energyContinuous := by
    have hpow :
        ContinuousOn
          (fun t => intervalDomain.integral
            (fun x : intervalDomain.Point => (u t x) ^ (2 : ℝ)))
          (Set.Icc (0 : ℝ) T) :=
      intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity
        (params := p) (T := T) (p0 := (2 : ℝ)) (u := u) (v := v)
        hsol hendpoint (2 : ℝ) le_rfl
    exact hpow.congr (fun t _ht =>
      intervalDomainLpAbsEnergy_two_eq_domain_powerEnergy u t)
  energyHasDerivWithin := by
    intro t ht
    by_cases ht_zero : t = 0
    · subst t
      exact hzero
    · have ht0 : 0 < t := lt_of_le_of_ne ht.1 (fun h => ht_zero h.symm)
      have htT : t < T := ht.2
      have hpow :
          HasDerivAt (fun s => intervalDomainPowerEnergy 2 u s)
            (∫ y in (0 : ℝ)..1, intervalDomainPowerDeriv 2 u t y) t :=
        intervalDomainPowerEnergy_hasDerivAt
          (p := p) (T := T) (q := (2 : ℝ)) (u := u) (v := v)
          hsol ⟨ht0, htT⟩
      have hfun :
          (fun s => intervalDomainLpAbsEnergy 2 u s) =
            fun s => intervalDomainPowerEnergy 2 u s := by
        funext s
        exact intervalDomainLpAbsEnergy_two_eq_powerEnergy u s
      have habs :
          HasDerivAt (fun s => intervalDomainLpAbsEnergy 2 u s)
            (∫ y in (0 : ℝ)..1, intervalDomainPowerDeriv 2 u t y) t := by
        rw [hfun]
        exact hpow
      exact habs.hasDerivWithinAt.congr_deriv habs.deriv.symm
  initialBound := by
    refine ⟨intervalDomainLpAbsEnergy 2 u 0,
      intervalDomainLpAbsEnergy_two_nonneg u 0, le_rfl⟩
  derivativeAlignment := by
    intro t _ht
    have hfun :
        (fun τ => intervalDomainLpAbsEnergy 2 u τ) =
          fun τ => 2 * intervalDomainL2HalfEnergy u τ := by
      funext τ
      exact intervalDomainLpAbsEnergy_two_eq_two_mul_L2HalfEnergy u τ
    rw [hfun]
    exact
      (deriv_const_mul_field
        (x := t) (v := fun τ : ℝ => intervalDomainL2HalfEnergy u τ) (2 : ℝ))

/-- A spatially constant trajectory has the closed-time L² seed regularity
frontier. -/
theorem intervalDomainL2SeedRegularityFrontier_const {T c : ℝ} :
    IntervalDomainL2SeedRegularityFrontier T
      (fun _ (_ : intervalDomain.Point) => c) where
  energyContinuous := by
    let E : ℝ :=
      intervalDomainLpAbsEnergy 2 (fun _ (_ : intervalDomain.Point) => c) 0
    have hfun :
        (fun t : ℝ =>
          intervalDomainLpAbsEnergy 2 (fun _ (_ : intervalDomain.Point) => c) t)
          = fun _ : ℝ => E := by
      funext t
      rfl
    rw [hfun]
    exact continuousOn_const
  energyHasDerivWithin := by
    intro t _ht
    let E : ℝ :=
      intervalDomainLpAbsEnergy 2 (fun _ (_ : intervalDomain.Point) => c) 0
    have hfun :
        (fun τ : ℝ =>
          intervalDomainLpAbsEnergy 2 (fun _ (_ : intervalDomain.Point) => c) τ)
          = fun _ : ℝ => E := by
      funext τ
      rfl
    rw [hfun, deriv_const]
    exact hasDerivWithinAt_const t (Set.Ici t) E
  initialBound := by
    refine ⟨intervalDomainLpAbsEnergy 2 (fun _ (_ : intervalDomain.Point) => c) 0,
      intervalDomainLpAbsEnergy_two_nonneg (fun _ (_ : intervalDomain.Point) => c) 0,
      le_rfl⟩
  derivativeAlignment := by
    intro t _ht
    let E : ℝ :=
      intervalDomainLpAbsEnergy 2 (fun _ (_ : intervalDomain.Point) => c) 0
    let H : ℝ :=
      intervalDomainL2HalfEnergy (fun _ (_ : intervalDomain.Point) => c) 0
    have hE :
        (fun τ : ℝ =>
          intervalDomainLpAbsEnergy 2 (fun _ (_ : intervalDomain.Point) => c) τ)
          = fun _ : ℝ => E := by
      funext τ
      rfl
    have hH :
        (fun τ : ℝ =>
          intervalDomainL2HalfEnergy (fun _ (_ : intervalDomain.Point) => c) τ)
          = fun _ : ℝ => H := by
      funext τ
      rfl
    rw [hE, hH, deriv_const, deriv_const]
    ring

#print axioms intervalDomainL2SeedRegularityFrontier_const

end ShenWork.Paper2

end
