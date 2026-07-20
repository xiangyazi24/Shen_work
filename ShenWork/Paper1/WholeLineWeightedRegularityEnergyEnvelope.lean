import ShenWork.Paper1.WholeLineWeightedRegularityTailEnergyDecay

open Filter Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# A global exponential envelope for an eventually controlled scalar energy

The physical weighted energy is naturally differentiable only at strictly
positive times, and its differential inequality may hold only on a time tail.
Starting the scalar Grönwall estimate on that tail produces an explicit
exponential function.  Unlike the physical energy, this envelope is smooth on
all of `ℝ`, including the initial endpoint required by the Section 5 consumer.
-/

/-- An eventually controlled positive-time scalar energy admits a globally
smooth exponential envelope with the same differential coefficient.

No sign condition on `C` is needed.  In the stability application the common
bound is still arbitrary here; strict negativity is used only after the caller
selects a sufficiently small common bound. -/
theorem scalarEnergy_eventual_exponential_envelope_of_eventual_positive_time_deriv
    {F : ℝ → ℝ} {C : ℝ}
    (hcont : ContinuousOn F (Set.Ioi (0 : ℝ)))
    (hderiv : ∀ t : ℝ, 0 < t → HasDerivAt F (deriv F t) t)
    (hgrowth : ∀ᶠ t in atTop, deriv F t ≤ C * F t) :
    ∃ E : ℝ → ℝ,
      (∀ᶠ t in atTop, F t ≤ E t) ∧
      (∀ T : ℝ, 0 ≤ T → ContinuousOn E (Set.Icc 0 T)) ∧
      (∀ T : ℝ, 0 ≤ T → ∀ t ∈ Set.Ico 0 T,
        HasDerivWithinAt E (deriv E t) (Set.Ici t) t) ∧
      (∀ t : ℝ, 0 ≤ t → deriv E t ≤ C * E t) := by
  obtain ⟨a, ha, htail⟩ :=
    scalarEnergy_eventual_exponential_bound_of_eventual_positive_time_deriv
      hcont hderiv hgrowth
  let E : ℝ → ℝ := fun t => F a * Real.exp (C * (t - a))
  have hEcont : Continuous E := by
    dsimp only [E]
    fun_prop
  have hEderiv : ∀ t : ℝ, HasDerivAt E (C * E t) t := by
    intro t
    have hlin : HasDerivAt (fun s : ℝ => C * (s - a)) C t := by
      simpa using ((hasDerivAt_id t).sub_const a).const_mul C
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (C * (s - a)))
        (C * Real.exp (C * (t - a))) t := by
      simpa [mul_comm] using
        (Real.hasDerivAt_exp (C * (t - a))).comp t hlin
    dsimp only [E]
    convert hexp.const_mul (F a) using 1
    ring
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop a] with t ht
    exact htail t ht
  · intro T _hT
    exact hEcont.continuousOn
  · intro T _hT t _ht
    simpa only [(hEderiv t).deriv] using (hEderiv t).hasDerivWithinAt
  · intro t _ht
    rw [(hEderiv t).deriv]

section AxiomAudit

#print axioms
  scalarEnergy_eventual_exponential_envelope_of_eventual_positive_time_deriv

end AxiomAudit

end ShenWork.Paper1
