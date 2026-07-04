import ShenWork.PDE.P3MoserLemmaDischarge
import ShenWork.Paper2.IntervalDomainL2SeedFrontierProducer

/-!
# Closed-energy trace producer survey

This file records the current executable frontier for
`ClosedEnergyIdentityTraceData`.

What is discharged here:
* `nonnegT`, from `IsPaper2ClassicalSolution.T_pos`;
* `initial_trace_energy`, for the re-anchored representative
  `intervalDomainWithInitialSlice u₀ u`;
* `energyHasDerivWithin` on strict positive times, from
  `IsPaper2ClassicalSolution`;
* `derivativeAlignment`, unconditionally from
  `intervalDomainLpAbsEnergy 2 = 2 * intervalDomainL2HalfEnergy`.

What remains explicit:
* the closed-window FTC data (`g`, `g_integrable`, `energy_eq`);
* the right derivative at `t = 0`.

For the raw trajectory `u`, `InitialTrace` gives only deleted-right convergence
and does not identify the stored slice `u 0` with `u₀`; use
`intervalDomainLpAbsEnergy_two_zero_eq_of_zeroSlice` if a zero-slice equality is
available.
-/

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserLemmaDischarge

/-- Pointwise zero-slice compatibility gives the initial trace energy for the
raw trajectory.  This is not a consequence of `InitialTrace` alone. -/
theorem intervalDomainLpAbsEnergy_two_zero_eq_of_zeroSlice
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hzeroSlice : u 0 = u₀) :
    intervalDomainLpAbsEnergy 2 u 0 =
      intervalDomain.integral
        (fun x : intervalDomain.Point => |u₀ x| ^ (2 : ℝ)) := by
  exact intervalDomainLpAbsEnergy_two_zero_eq_of_pointwise_trace
    (u₀ := u₀) (u := u) (fun x => congrFun hzeroSlice x)

/-- The re-anchored representative has the prescribed initial energy
definitionally at `t = 0`. -/
theorem intervalDomainLpAbsEnergy_two_zero_eq_withInitialSlice
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ} :
    intervalDomainLpAbsEnergy 2 (intervalDomainWithInitialSlice u₀ u) 0 =
      intervalDomain.integral
        (fun x : intervalDomain.Point => |u₀ x| ^ (2 : ℝ)) := by
  exact intervalDomainLpAbsEnergy_two_zero_eq_of_pointwise_trace
    (u₀ := u₀) (u := intervalDomainWithInitialSlice u₀ u)
    (fun x => by simp [intervalDomainWithInitialSlice])

/-- The derivative alignment field of `ClosedEnergyIdentityTraceData` is
purely algebraic and does not use the PDE. -/
theorem intervalDomainLpAbsEnergy_two_derivativeAlignment
    {T : ℝ} {u : ℝ → intervalDomain.Point → ℝ} :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) t =
        2 * deriv (fun τ => intervalDomainL2HalfEnergy u τ) t := by
  intro t _ht
  have hfun :
      (fun τ => intervalDomainLpAbsEnergy 2 u τ) =
        fun τ => 2 * intervalDomainL2HalfEnergy u τ := by
    funext τ
    exact ShenWork.Paper2.intervalDomainLpAbsEnergy_two_eq_two_mul_L2HalfEnergy u τ
  rw [hfun]
  exact
    (deriv_const_mul_field
      (x := t) (v := fun τ : ℝ => intervalDomainL2HalfEnergy u τ) (2 : ℝ))

/-- Classical regularity gives the energy right-derivative field on positive
interior times.  The closed interface still needs a separate `t = 0` input. -/
theorem intervalDomainLpAbsEnergy_two_hasDerivWithinAt_of_classical_interior
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivWithinAt
      (fun τ => intervalDomainLpAbsEnergy 2 u τ)
      (deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) t)
      (Set.Ici t) t := by
  have hpow :
      HasDerivAt (fun s => intervalDomainPowerEnergy 2 u s)
        (∫ y in (0 : ℝ)..1, intervalDomainPowerDeriv 2 u t y) t :=
    intervalDomainPowerEnergy_hasDerivAt
      (p := params) (T := T) (q := (2 : ℝ)) (u := u) (v := v)
      hsol ht
  have hfun :
      (fun s => intervalDomainLpAbsEnergy 2 u s) =
        fun s => intervalDomainPowerEnergy 2 u s := by
    funext s
    exact ShenWork.Paper2.intervalDomainLpAbsEnergy_two_eq_powerEnergy u s
  have habs :
      HasDerivAt (fun s => intervalDomainLpAbsEnergy 2 u s)
        (∫ y in (0 : ℝ)..1, intervalDomainPowerDeriv 2 u t y) t := by
    rw [hfun]
    exact hpow
  exact habs.hasDerivWithinAt.congr_deriv habs.deriv.symm

/-- Add the missing zero-time right derivative to the positive-time classical
derivative result. -/
theorem intervalDomainLpAbsEnergy_two_hasDerivWithinAt_of_classical_and_zero
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hzero : IntervalDomainL2SeedZeroRightDerivative u) :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt
        (fun τ => intervalDomainLpAbsEnergy 2 u τ)
        (deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) t)
        (Set.Ici t) t := by
  intro t ht
  by_cases ht_zero : t = 0
  · subst t
    exact hzero
  · have htIoo : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_of_le_of_ne ht.1 (fun h : (0 : ℝ) = t => ht_zero h.symm), ht.2⟩
    exact intervalDomainLpAbsEnergy_two_hasDerivWithinAt_of_classical_interior
      hsol htIoo

/-- The fields currently discharged from the classical solution and the
re-anchored initial trace. -/
structure ClosedEnergyIdentityTracePartialData
    (T : ℝ) (u₀ : intervalDomain.Point → ℝ)
    (u : ℝ → intervalDomain.Point → ℝ) where
  nonnegT : 0 ≤ T
  initial_trace_energy :
    intervalDomainLpAbsEnergy 2 u 0 =
      intervalDomain.integral
        (fun x : intervalDomain.Point => |u₀ x| ^ (2 : ℝ))
  positiveTimeEnergyHasDerivWithin :
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt
        (fun τ => intervalDomainLpAbsEnergy 2 u τ)
        (deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) t)
        (Set.Ici t) t
  derivativeAlignment :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) t =
        2 * deriv (fun τ => intervalDomainL2HalfEnergy u τ) t

/-- Remaining data needed to turn the partial producer into the full closed
energy trace package. -/
structure ClosedEnergyIdentityTraceRemainingData
    (T : ℝ) (u : ℝ → intervalDomain.Point → ℝ) where
  g : ℝ → ℝ
  g_integrable : IntegrableOn g (Set.uIcc (0 : ℝ) T) volume
  energy_eq :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      intervalDomainLpAbsEnergy 2 u t =
        intervalDomainLpAbsEnergy 2 u 0 + ∫ s in (0 : ℝ)..t, g s
  zeroRightDerivative : IntervalDomainL2SeedZeroRightDerivative u

namespace ClosedEnergyIdentityTracePartialData

/-- Convert partial closed-energy fields plus the explicit remaining FTC and
zero-derivative data into the full `ClosedEnergyIdentityTraceData`. -/
def to_closedEnergyIdentityTraceData
    {T : ℝ} {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (h : ClosedEnergyIdentityTracePartialData T u₀ u)
    (hrem : ClosedEnergyIdentityTraceRemainingData T u) :
    ClosedEnergyIdentityTraceData T u₀ u where
  nonnegT := h.nonnegT
  g := hrem.g
  g_integrable := hrem.g_integrable
  energy_eq := hrem.energy_eq
  initial_trace_energy := h.initial_trace_energy
  energyHasDerivWithin := by
    intro t ht
    by_cases ht_zero : t = 0
    · subst t
      exact hrem.zeroRightDerivative
    · have htIoo : t ∈ Set.Ioo (0 : ℝ) T :=
        ⟨lt_of_le_of_ne ht.1 (fun hz : (0 : ℝ) = t => ht_zero hz.symm), ht.2⟩
      exact h.positiveTimeEnergyHasDerivWithin t htIoo
  derivativeAlignment := h.derivativeAlignment

end ClosedEnergyIdentityTracePartialData

/-- Partial closed-energy producer for the re-anchored representative.  The
`InitialTrace` and `PaperPositiveInitialDatum` inputs are part of the faithful
source package; the actual initial-energy field is discharged by re-anchoring
the zero slice. -/
theorem closedEnergyIdentityTracePartialData_withInitialSlice_of_classical
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (_htrace : InitialTrace intervalDomain u₀ u)
    (_hdatum : PaperPositiveInitialDatum intervalDomain u₀) :
    ClosedEnergyIdentityTracePartialData T u₀
      (intervalDomainWithInitialSlice u₀ u) where
  nonnegT := (IsPaper2ClassicalSolution.T_pos hsol).le
  initial_trace_energy := intervalDomainLpAbsEnergy_two_zero_eq_withInitialSlice
  positiveTimeEnergyHasDerivWithin := by
    intro t ht
    exact intervalDomainLpAbsEnergy_two_hasDerivWithinAt_of_classical_interior
      (intervalDomain_classical_withInitialSlice (u₀ := u₀) hsol) ht
  derivativeAlignment := intervalDomainLpAbsEnergy_two_derivativeAlignment

/-- Full producer for the re-anchored representative, with the irreducible FTC
and zero-right-derivative fields supplied explicitly. -/
def closedEnergyIdentityTraceData_withInitialSlice_of_classical
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hrem :
      ClosedEnergyIdentityTraceRemainingData T
        (intervalDomainWithInitialSlice u₀ u)) :
    ClosedEnergyIdentityTraceData T u₀
      (intervalDomainWithInitialSlice u₀ u) :=
  (closedEnergyIdentityTracePartialData_withInitialSlice_of_classical
    hsol htrace hdatum).to_closedEnergyIdentityTraceData hrem

#print axioms intervalDomainLpAbsEnergy_two_zero_eq_of_zeroSlice
#print axioms intervalDomainLpAbsEnergy_two_zero_eq_withInitialSlice
#print axioms intervalDomainLpAbsEnergy_two_derivativeAlignment
#print axioms intervalDomainLpAbsEnergy_two_hasDerivWithinAt_of_classical_interior
#print axioms intervalDomainLpAbsEnergy_two_hasDerivWithinAt_of_classical_and_zero
#print axioms closedEnergyIdentityTracePartialData_withInitialSlice_of_classical
#print axioms closedEnergyIdentityTraceData_withInitialSlice_of_classical

end ShenWork.IntervalDomainExistence.P3MoserLemmaDischarge

end
