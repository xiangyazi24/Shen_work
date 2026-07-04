import Mathlib.Analysis.Calculus.FDeriv.Extend
import ShenWork.PDE.P3MoserClosedEnergyProducer

/-!
# Audit: the zero-time L2 right derivative frontier

This file is an audit artifact for frontier #1, not a replacement wiring file.

Findings from reading the sources:

* `IntervalDomainL2SeedZeroRightDerivative` is defined in
  `ShenWork/Paper2/IntervalDomainL2SeedFrontierProducer.lean` as
  `HasDerivWithinAt E (deriv E 0) (Set.Ici 0) 0`, where
  `E t = intervalDomainLpAbsEnergy 2 u t`.
* Mathlib's `deriv` is the two-sided derivative.  If `E` is not differentiable
  at `0` as a function on all real times, then `deriv E 0` is the conventional
  junk value `0`, by `deriv_zero_of_not_differentiableAt`.
* `intervalDomainWithInitialSlice u0 u` is exactly
  `fun t x => if t = 0 then u0 x else u t x`.  Thus negative times are not
  re-anchored; for `t < 0` the stored slice is the raw `u t`.  The PDE and the
  classical-solution interfaces used here control positive times, not the
  left-hand difference quotient at `0`.
* Therefore the current statement is not satisfiable from the intended PDE
  data unless an extra two-sided differentiability/equality fact is supplied.
  A typical obstruction is a right-time energy with genuine slope at `0` but an
  unrelated raw negative-time branch: the right derivative exists, while the
  two-sided derivative need not exist; in that case `deriv E 0 = 0` and the
  old statement asks for right derivative `0`.

Consumer audit:

* `IntervalDomainL2SeedFrontierProducer` uses `hzero` only to fill the
  `t = 0` case of `IntervalDomainL2SeedRegularityFrontier.energyHasDerivWithin`.
* `P3MoserClosedEnergyProducer` stores `zeroRightDerivative` in
  `ClosedEnergyIdentityTraceRemainingData`, then uses it only for the `t = 0`
  case of `ClosedEnergyIdentityTraceData.energyHasDerivWithin`.
* `P3MoserFTCInfrastructure` forwards this same field after discharging the
  FTC data.
* No direct consumer computes the numeric value from `hzero`, but the enclosing
  interfaces also write the endpoint derivative as `deriv E 0`.  Downstream,
  the old differential Gronwall route even forms `max K (deriv E 0)`, so the
  junk value can be observed.  The integrated route uses only continuity plus
  an integrated inequality and avoids this endpoint derivative.

Correct fix:

* Replace the endpoint value by
  `derivWithin E (Set.Ici 0) 0`.
* The Mathlib endpoint theorem
  `hasDerivWithinAt_Ici_of_tendsto_deriv` is the right production mechanism:
  it proves a one-sided derivative at a left endpoint from interior
  differentiability, endpoint continuity, and convergence of the interior
  derivative.
* A corrected value can be coerced back to the old interface only under the
  extra equality `deriv E 0 = derivWithin E (Set.Ici 0) 0`, i.e. exactly the
  two-sided compatibility that the intended PDE data does not provide.

Impact if the fix is applied globally:

* Update `IntervalDomainL2SeedZeroRightDerivative`.
* Update endpoint fields in `IntervalDomainL2SeedRegularityFrontier`,
  `ClosedEnergyIdentityTraceData`, `ClosedEnergyIdentityTraceRemainingData`,
  and `IntervalDomainClosedL2SeedBridge` so their derivative value is
  `derivWithin (Set.Ici t) t`, not `deriv`.
* Update direct producers in
  `IntervalDomainL2SeedFrontierProducer`, `P3MoserClosedEnergyProducer`, and
  `P3MoserFTCInfrastructure`.
* Audit scalar consumers of the old differential Gronwall route in
  `IntervalDomainLpMonotonicity` / `IntervalDomainAPrioriGlobal`; the integrated
  route is the safer consumer because it does not need `deriv E 0`.
-/

open MeasureTheory Set Filter
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open scoped Topology

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserZeroDerivAudit

/-- The audited one-sided replacement for
`IntervalDomainL2SeedZeroRightDerivative`. -/
def IntervalDomainL2SeedZeroRightDerivativeWithin
    (u : ℝ -> intervalDomain.Point -> ℝ) : Prop :=
  HasDerivWithinAt
    (fun τ => intervalDomainLpAbsEnergy 2 u τ)
    (derivWithin (fun τ => intervalDomainLpAbsEnergy 2 u τ)
      (Set.Ici (0 : ℝ)) 0)
    (Set.Ici (0 : ℝ)) 0

/-- Any existing proof of the old, stronger/junk-valued statement implies the
corrected statement, because a proved within-derivative identifies
`derivWithin`. -/
theorem zeroRightDerivativeWithin_of_old
    {u : ℝ -> intervalDomain.Point -> ℝ}
    (h : IntervalDomainL2SeedZeroRightDerivative u) :
    IntervalDomainL2SeedZeroRightDerivativeWithin u := by
  let E : ℝ -> ℝ := fun τ => intervalDomainLpAbsEnergy 2 u τ
  have hE :
      HasDerivWithinAt E (deriv E 0) (Set.Ici (0 : ℝ)) 0 := h
  have hderivWithin :
      derivWithin E (Set.Ici (0 : ℝ)) 0 = deriv E 0 :=
    hE.derivWithin (uniqueDiffWithinAt_Ici (0 : ℝ))
  exact hE.congr_deriv hderivWithin.symm

/-- A corrected proof can feed the current old consumers only when the two-sided
`deriv` value agrees with the right-sided `derivWithin` value.  This equality is
the extra compatibility missing from the intended re-anchored PDE trajectory. -/
theorem old_zeroRightDerivative_of_within_of_deriv_eq
    {u : ℝ -> intervalDomain.Point -> ℝ}
    (h : IntervalDomainL2SeedZeroRightDerivativeWithin u)
    (hderiv :
      deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) 0 =
        derivWithin (fun τ => intervalDomainLpAbsEnergy 2 u τ)
          (Set.Ici (0 : ℝ)) 0) :
    IntervalDomainL2SeedZeroRightDerivative u := by
  exact h.congr_deriv hderiv.symm

/-- Endpoint theorem restated with `derivWithin` as the derivative value.  This
is the Mathlib-supported one-sided shape the frontier should use. -/
theorem hasDerivWithinAt_Ici_derivWithin_of_tendsto_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set ℝ} {e : E} {a : ℝ} {f : ℝ -> E}
    (hdiff : DifferentiableOn ℝ f s)
    (hcont : ContinuousWithinAt f s a)
    (hs : s ∈ 𝓝[>] a)
    (hlim : Tendsto (fun x => deriv f x) (𝓝[>] a) (𝓝 e)) :
    HasDerivWithinAt f (derivWithin f (Set.Ici a) a) (Set.Ici a) a := by
  have hendpoint :
      HasDerivWithinAt f e (Set.Ici a) a :=
    hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hcont hs hlim
  have hderivWithin :
      derivWithin f (Set.Ici a) a = e :=
    hendpoint.derivWithin (uniqueDiffWithinAt_Ici a)
  exact hendpoint.congr_deriv hderivWithin.symm

/-- Conditional producer for the corrected re-anchored endpoint.  This records
the exact remaining analytic input: differentiability on a right neighborhood,
continuity at `0`, and convergence of the positive-time energy derivative. -/
theorem zeroRightDerivativeWithin_withInitialSlice_of_tendsto_deriv
    {u0 : intervalDomain.Point -> ℝ}
    {u : ℝ -> intervalDomain.Point -> ℝ}
    {s : Set ℝ} {e : ℝ}
    (hdiff :
      DifferentiableOn ℝ
        (fun τ =>
          intervalDomainLpAbsEnergy 2 (intervalDomainWithInitialSlice u0 u) τ)
        s)
    (hcont :
      ContinuousWithinAt
        (fun τ =>
          intervalDomainLpAbsEnergy 2 (intervalDomainWithInitialSlice u0 u) τ)
        s 0)
    (hs : s ∈ 𝓝[>] (0 : ℝ))
    (hlim :
      Tendsto
        (fun t =>
          deriv
            (fun τ =>
              intervalDomainLpAbsEnergy 2
                (intervalDomainWithInitialSlice u0 u) τ) t)
        (𝓝[>] (0 : ℝ)) (𝓝 e)) :
    IntervalDomainL2SeedZeroRightDerivativeWithin
      (intervalDomainWithInitialSlice u0 u) := by
  exact
    hasDerivWithinAt_Ici_derivWithin_of_tendsto_deriv
      (f := fun τ =>
        intervalDomainLpAbsEnergy 2 (intervalDomainWithInitialSlice u0 u) τ)
      hdiff hcont hs hlim

/-- Corrected analogue of the remaining closed-energy data: only the zero-time
derivative field is changed. -/
structure ClosedEnergyIdentityTraceRemainingDataWithin
    (T : ℝ) (u : ℝ -> intervalDomain.Point -> ℝ) where
  g : ℝ -> ℝ
  g_integrable : IntegrableOn g (Set.uIcc (0 : ℝ) T) volume
  energy_eq :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      intervalDomainLpAbsEnergy 2 u t =
        intervalDomainLpAbsEnergy 2 u 0 + ∫ s in (0 : ℝ)..t, g s
  zeroRightDerivative : IntervalDomainL2SeedZeroRightDerivativeWithin u

/-- Conditional adapter back to the current old structure.  The required equality
is intentionally explicit: without it the old consumer asks for the wrong
endpoint derivative value. -/
def ClosedEnergyIdentityTraceRemainingDataWithin.to_old_of_deriv_eq
    {T : ℝ} {u : ℝ -> intervalDomain.Point -> ℝ}
    (h : ClosedEnergyIdentityTraceRemainingDataWithin T u)
    (hderiv :
      deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) 0 =
        derivWithin (fun τ => intervalDomainLpAbsEnergy 2 u τ)
          (Set.Ici (0 : ℝ)) 0) :
    ShenWork.IntervalDomainExistence.P3MoserLemmaDischarge.ClosedEnergyIdentityTraceRemainingData T u where
  g := h.g
  g_integrable := h.g_integrable
  energy_eq := h.energy_eq
  zeroRightDerivative :=
    old_zeroRightDerivative_of_within_of_deriv_eq h.zeroRightDerivative hderiv

#print axioms zeroRightDerivativeWithin_of_old
#print axioms old_zeroRightDerivative_of_within_of_deriv_eq
#print axioms hasDerivWithinAt_Ici_derivWithin_of_tendsto_deriv
#print axioms zeroRightDerivativeWithin_withInitialSlice_of_tendsto_deriv
#print axioms ClosedEnergyIdentityTraceRemainingDataWithin.to_old_of_deriv_eq

end ShenWork.IntervalDomainExistence.P3MoserZeroDerivAudit

end
