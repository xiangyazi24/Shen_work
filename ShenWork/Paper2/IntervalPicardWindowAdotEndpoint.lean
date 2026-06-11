import ShenWork.Paper2.IntervalPicardWindowAdot
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On
import ShenWork.PDE.HasDerivWithinAtTsum

/-!
# One-sided endpoint window adot legs

This file records the closed-window endpoint predicate required at the cone
horizon.  The full endpoint producer needs a one-sided replacement for
`picardIterate_K1_full_from_restart_of_representation`; the existing producer is
open-window/two-sided.  The theorem below gives the exact coercion available from
the current two-sided legs.
-/

open Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)

noncomputable section

namespace ShenWork.IntervalPicardWindowAdotEndpoint

/-- Closed-window one-sided analogue of `WindowAdotLegs`. -/
def WindowAdotLegsOn (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (n : ℕ) (lo hi : ℝ) : Prop :=
  ∃ adot : ℝ → ℕ → ℝ,
    (∀ σ ∈ Set.Icc lo hi, ∀ k, HasDerivWithinAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α
          (intervalDomainLift (picardIter p u₀ n r))) k)
      (adot σ k) (Set.Icc lo hi) σ)
    ∧ (∃ Mdot : ℝ, ∀ σ ∈ Set.Icc lo hi, ∀ k, |adot σ k| ≤ Mdot)
    ∧ (∀ k, ContinuousOn (fun σ => adot σ k) (Set.Icc lo hi))

/-- Two-sided window legs immediately imply one-sided closed-window legs. -/
theorem windowAdotLegsOn_of_windowAdotLegs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {n : ℕ} {lo hi : ℝ}
    (h :
      ShenWork.IntervalPicardWindowAdot.WindowAdotLegs p u₀ n lo hi) :
    WindowAdotLegsOn p u₀ n lo hi := by
  rcases h with ⟨adot, hderiv, hbound, hcont⟩
  refine ⟨adot, ?_, hbound, hcont⟩
  intro σ hσ k
  exact (hderiv σ hσ k).hasDerivWithinAt

/-- Endpoint coercion from already-built two-sided legs on `[T / 2, T]`. -/
theorem windowAdotLegs_endpoint
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) {T : ℝ}
    (h :
      ShenWork.IntervalPicardWindowAdot.WindowAdotLegs p u₀ n (T / 2) T) :
    WindowAdotLegsOn p u₀ n (T / 2) T :=
  windowAdotLegsOn_of_windowAdotLegs h

end ShenWork.IntervalPicardWindowAdotEndpoint

