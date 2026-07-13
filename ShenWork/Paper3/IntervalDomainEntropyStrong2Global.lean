import ShenWork.Paper3.IntervalDomainEntropyBasinEntry

/-! # Unconditional second-branch global stability on the unit interval -/

namespace ShenWork.Paper3

open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

/-- Branch-two entropy persistence and dissipation followed by the proved
weak-sup Stage B theorem. -/
theorem intervalDomain_strong2_eventualC1
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b) (hβ : 1 ≤ p.β)
    (hrel : 2 * p.γ ≤ p.α + 1)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong2Formula p
      (positiveEquilibrium p ⟨ha, hb⟩).1)
    (hstable : LinearlyStable unitIntervalNeumannSpectrum p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
      EventualExponentialC1ConvergenceWith intervalDomain
        intervalDomainSectorialStabilityNorms u v
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 C rate t₀ := by
  let uStar := (positiveEquilibrium p ⟨ha, hb⟩).1
  let vStar := (positiveEquilibrium p ⟨ha, hb⟩).2
  have heq : Paper3ConstantEquilibrium p uStar vStar := by
    simpa [uStar, vStar] using paper3ConstantEquilibrium_positive p ha hb
  have horbit := intervalDomain_weakSupEventualSpectralSemigroupOrbitBound p hm
  let witness := horbit.2 uStar vStar ha heq (by simpa [uStar, vStar] using hstable)
  let delta : ℝ := Classical.choose witness
  have hdelta : 0 < delta := (Classical.choose_spec witness).1
  have hlate : ∀ {T q : ℝ}, 0 < q →
      ∃ t, T ≤ t ∧
        chemotaxisThetaDissipation intervalDomain uStar p.α (u t) < q := by
    intro T q hq
    simpa [uStar] using
      (intervalDomain_strong2_exists_late_thetaDissipation_lt
        p hm ha hb hβ hrel hχpos hχ huv (T := T) hq)
  obtain ⟨tau, htauOne, hclose⟩ :=
    intervalDomain_exists_late_supClose_of_thetaDissipation_slices
      p hm heq.u_pos p.hα huv hlate (T := (1 : ℝ)) hdelta
  have htau : 0 < tau := lt_of_lt_of_le zero_lt_one htauOne
  simpa [uStar, vStar] using
    (intervalDomain_eventualC1_of_supCloseSlice_of_linearlyStable
      p hm ha heq (by simpa [uStar, vStar] using hstable) huv htau
        (by simpa [witness, delta] using hclose))

/-- Unconditional second formula branch of faithful eventual Theorem 2.4 on
the currently implemented `m = 1` unit-interval equation. -/
theorem
    intervalDomain_eventuallyGloballyExponentiallyStableNonminimal_strong2
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b) (hβ : 1 ≤ p.β)
    (hrel : 2 * p.γ ≤ p.α + 1)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong2Formula p
      (positiveEquilibrium p ⟨ha, hb⟩).1) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    EventuallyGloballyExponentiallyStableNonminimal intervalDomain p
      intervalDomainSectorialStabilityNorms eq.1 eq.2 := by
  let eq := positiveEquilibrium p ⟨ha, hb⟩
  have hmge : 1 ≤ p.m := by rw [hm]
  have hcond : NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 0 :=
    Or.inr (Or.inl ⟨hmge, hβ, hrel, hχpos, by simpa [eq] using hχ⟩)
  have hstable : LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
    simpa [eq] using hcond.linearlyStable_unitInterval p ha hb
  have hproduce : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      PositiveGlobalBoundedSolution intervalDomain p u v →
      ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
        EventualExponentialC1ConvergenceWith intervalDomain
          intervalDomainSectorialStabilityNorms u v eq.1 eq.2 C rate t₀ := by
    intro u v huv
    simpa [eq] using intervalDomain_strong2_eventualC1
      p hm ha hb hβ hrel hχpos hχ (by simpa [eq] using hstable) huv
  refine ⟨?_, hproduce⟩
  intro u v huv
  obtain ⟨C, hC, rate, hrate, t₀, ht₀, hbound⟩ := hproduce u v huv
  exact intervalDomain_uniformConvergesInSup_of_eventualExponentialC1
    hrate hbound

#print axioms intervalDomain_strong2_eventualC1
#print axioms
  intervalDomain_eventuallyGloballyExponentiallyStableNonminimal_strong2

end

end ShenWork.Paper3
