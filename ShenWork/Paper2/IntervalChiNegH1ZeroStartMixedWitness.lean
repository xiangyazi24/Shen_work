import ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents
import ShenWork.PDE.IntervalChemDivMixedReprWitness

/-!
# Mixed-witness contribution to the zero-start H¹ PDE seam

The raw mixed chemotaxis-divergence witness contains a continuous representative
of `∂ₜu`, so it can supply the `time_cont0` half of
`H1ZeroStartPhysicalPDEInitialCompatibilityBefore`.  It does not supply the
initial-time PDE trace `eq0Interior`.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1LiftDeriv2Transfer
open ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative
open ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents

noncomputable section

namespace ShenWork.IntervalChemDivMixedReprWitness

/-- Raw mixed witnesses covering every zero-start slab.  This is stronger than
the H¹ route's direct `time_cont0` field; it is useful only when the construction
already carries the spectral witness data. -/
structure H1ZeroStartTimeDerivMixedWitnessBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop where
  witness : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ∃ τ δ : ℝ,
      Set.Icc (0 : ℝ) b ⊆ Set.Icc (τ - δ) (τ + δ) ∧
      Nonempty (ChemDivMixedReprWitnessData p u τ δ)

/-- The raw mixed witness package implies the `time_cont0` half of the H¹
zero-start PDE compatibility record, through the `Utc` representative. -/
theorem time_cont0_of_mixedWitnessBefore
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (H : H1ZeroStartTimeDerivMixedWitnessBefore p u T) :
    ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn
        (Function.uncurry (fun t x => liftTimeDeriv u t x))
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) := by
  intro b hb0 hbT
  rcases H.witness (b := b) hb0 hbT with ⟨τ, δ, hcover, hW⟩
  rcases hW with ⟨W⟩
  refine W.cont_Utc.continuousOn.congr ?_
  intro z hz
  rcases z with ⟨t, x⟩
  rcases hz with ⟨ht, hx⟩
  have ht' : t ∈ Set.Icc (τ - δ) (τ + δ) := hcover ht
  simpa [Function.uncurry, liftTimeDeriv, ShenWork.Paper2.PicardLimitK1.slopeSlice]
    using (W.Utc_eq t ht' x hx).symm

/-- A mixed-facing version of the initial compatibility package.  The mixed
witness only replaces `time_cont0`; the literal initial PDE trace remains an
explicit source-facing field. -/
structure H1ZeroStartPhysicalPDEInitialCompatibilityViaMixedBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop where
  mixed_time : H1ZeroStartTimeDerivMixedWitnessBefore p u T
  eq0Interior :
    Set.EqOn
      (fun x => liftDeriv2 u (0 : ℝ) x)
      (fun x =>
        liftDeriv2PhysicalRHSWithChemRep p u
          (liftChemotaxisDivPhysicalRep p u v) (0 : ℝ) x)
      (Set.Ioo (0 : ℝ) 1)

/-- The mixed-facing package is only a reducer to the direct initial
compatibility frontier; it does not prove the initial PDE trace. -/
theorem H1ZeroStartPhysicalPDEInitialCompatibilityBefore_of_mixed
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (H : H1ZeroStartPhysicalPDEInitialCompatibilityViaMixedBefore p u v T) :
    H1ZeroStartPhysicalPDEInitialCompatibilityBefore p u v T where
  time_cont0 := time_cont0_of_mixedWitnessBefore H.mixed_time
  eq0Interior := H.eq0Interior

section AxiomAudit

#print axioms time_cont0_of_mixedWitnessBefore
#print axioms H1ZeroStartPhysicalPDEInitialCompatibilityBefore_of_mixed

end AxiomAudit

end ShenWork.IntervalChemDivMixedReprWitness
