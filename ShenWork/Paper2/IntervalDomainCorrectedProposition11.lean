import ShenWork.Paper2.IntervalDomainLocalExistenceAllExponents
import ShenWork.PDE.IntervalDomainExistence

/-!
# Corrected Paper 2 Proposition 1.1 on the interval

The legacy `Proposition_1_1` chooses an arbitrary finite local horizon and
requires the maximal-time alternative there.  That is false: the positive
logistic equilibrium is a classical solution on every finite horizon and is
neither unbounded nor approaching zero.

The paper instead constructs a distinguished maximal continuation.  It has
either a finite branch carrying (1.14)/(1.15), or a global branch.  The
corrected headline below uses the existing `Paper2MaximalContinuation`
carrier, and its closer consumes exactly the standard continuation dichotomy
plus the already formalized gluing theorem.
-/

open Set
open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalDomainCorrectedProposition11

open ShenWork.IntervalDomainExistence

/-- The exact legacy frontier used by
`Proposition_1_1_intervalDomain_of_localExistence_and_finiteHorizonAlternative`.
It incorrectly asks every finite local witness to satisfy a maximal-time
alternative. -/
def LegacyFiniteHorizonAlternativeProducer (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomainPoint → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
  ∀ Tmax > 0, ∀ u v : ℝ → intervalDomainPoint → ℝ,
    IsPaper2ClassicalSolution intervalDomain p Tmax u v →
    InitialTrace intervalDomain u₀ u →
      FiniteHorizonAlternative intervalDomain Tmax u ∧
      (1 ≤ p.m → MGeOneFiniteHorizonAlternative intervalDomain Tmax u)

/-- Strict failure certificate for the requested legacy producer.  Any
parameter set with a positive logistic equilibrium refutes it, already on the
unit time horizon. -/
theorem not_legacyFiniteHorizonAlternativeProducer_of_positive_equilibrium
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) :
    ¬ LegacyFiniteHorizonAlternativeProducer p := by
  intro hlegacy
  let c : ℝ := (p.a / p.b) ^ (1 / p.α)
  let u₀ : intervalDomainPoint → ℝ := constOnInterval c
  have hc : 0 < c := by
    simpa [c] using equilibrium_pos p ha hb
  have hu₀ : PositiveInitialDatum intervalDomain u₀ := by
    simpa [u₀] using constOnInterval_pos hc
  have hsol :
      IsPaper2ClassicalSolution intervalDomain p 1
        (fun _ _ => c) (fun _ _ => ellipticV p c) := by
    simpa [c] using
      (equilibrium_isPaper2ClassicalSolution p ha hb) 1 zero_lt_one
  have htrace : InitialTrace intervalDomain u₀ (fun _ _ => c) := by
    simpa [u₀] using constantSolution_initialTrace c
  have halt :=
    (hlegacy u₀ hu₀ 1 zero_lt_one
      (fun _ _ => c) (fun _ _ => ellipticV p c) hsol htrace).1
  exact const_positive_not_finiteHorizonAlternative hc halt

/-- Paper-faithful corrected Proposition 1.1: every paper-positive datum has
one maximal-continuation branch.  The finite constructor stores (1.14) and,
when `m >= 1`, (1.15); the global constructor represents `Tmax = infinity`. -/
def CorrectedProposition_1_1 (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomainPoint → ℝ,
    PaperPositiveInitialDatum intervalDomain u₀ →
      Nonempty (Paper2MaximalContinuation intervalDomain p u₀)

/-- Corrected Proposition 1.1 from the actual maximal-continuation dichotomy.
The unbounded-reachability branch is converted to one global pair by overlap
uniqueness/gluing; the finite branch is already exactly the finite constructor
of `Paper2MaximalContinuation`. -/
theorem correctedProposition_1_1_of_standardContinuation_and_gluing
    (p : CM2Params)
    (hstandard :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PaperPositiveInitialDatum intervalDomain u₀ →
          StandardContinuationAlternative p u₀)
    (hglue : GlobalSolutionGluingFromReachability p) :
    CorrectedProposition_1_1 p := by
  intro u₀ hu₀
  rcases hstandard u₀ hu₀ with hlong | hfinite
  · obtain ⟨u, v, hglobal, htrace⟩ :=
      hglue u₀ hu₀.toPositive hlong
    exact ⟨Paper2MaximalContinuation.global u v hglobal htrace⟩
  · obtain ⟨Tmax, hTmax, u, v, hsol, htrace, halt, hmge⟩ := hfinite
    exact
      ⟨Paper2MaximalContinuation.finite
        Tmax u v hTmax hsol htrace halt hmge⟩

/-- The already proved all-exponent local theorem supplies the local Cauchy
part of the corrected proposition.  It is recorded separately because local
existence alone cannot choose the maximal branch. -/
theorem correctedProposition_1_1_local_part_allExponents
    (p : CM2Params) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ T > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p T u v ∧
          InitialTrace intervalDomain u₀ u :=
  ShenWork.Paper2.IntervalDomainM.intervalDomain_localExistence_paperPositive_allExponents p

#print axioms
  not_legacyFiniteHorizonAlternativeProducer_of_positive_equilibrium
#print axioms correctedProposition_1_1_of_standardContinuation_and_gluing
#print axioms correctedProposition_1_1_local_part_allExponents

end ShenWork.Paper2.IntervalDomainCorrectedProposition11

end
