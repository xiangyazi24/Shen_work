import ShenWork.Paper1.Theorem12WeightedAPrioriPropagation

open Filter Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Scalar Gronwall from positive-time differential control

The weighted PDE energy has an ordinary (hence right) derivative at every
strictly positive time, while its value is only known to be continuous at the
initial endpoint.  This file isolates the scalar endpoint passage: apply the
standard right-derivative Gronwall estimate on `[a, t]` and let `a ↓ 0`.
-/

/-- A homogeneous differential inequality on strictly positive times gives
the usual exponential estimate from the continuous initial value.  No
derivative at `t = 0` is required. -/
theorem scalarEnergy_crude_exponential_bound_of_positive_time_deriv
    {E : ℝ → ℝ} {C T : ℝ}
    (hT : 0 ≤ T)
    (hcont : ContinuousOn E (Set.Icc 0 T))
    (hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt E (deriv E s) (Set.Ici s) s)
    (hgrowth : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      deriv E s ≤ C * E s) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      E t ≤ E 0 * Real.exp (C * t) := by
  intro t ht
  rcases ht.1.eq_or_lt with ht0 | ht0
  · subst t
    simp
  have h0closure : (0 : ℝ) ∈ closure (Set.Ioc 0 t) := by
    rw [closure_Ioc (ne_of_lt ht0)]
    exact ⟨le_rfl, ht0.le⟩
  have hEcont : ContinuousWithinAt E (Set.Ioc 0 t) 0 := by
    apply (hcont 0 ⟨le_rfl, hT⟩).mono
    intro a ha
    exact ⟨ha.1.le, ha.2.trans ht.2⟩
  have hexpcont : ContinuousAt
      (fun a : ℝ => Real.exp (C * (t - a))) 0 := by
    fun_prop
  have hrhscont : ContinuousWithinAt
      (fun a : ℝ => E a * Real.exp (C * (t - a))) (Set.Ioc 0 t) 0 :=
    hEcont.mul hexpcont.continuousWithinAt
  have hfrom : ∀ a ∈ Set.Ioc (0 : ℝ) t,
      E t ≤ E a * Real.exp (C * (t - a)) := by
    intro a ha
    have hcont_at : ContinuousOn E (Set.Icc a t) := by
      apply hcont.mono
      intro s hs
      exact ⟨ha.1.le.trans hs.1, hs.2.trans ht.2⟩
    have hderiv_at : ∀ s ∈ Set.Ico a t,
        HasDerivWithinAt E (deriv E s) (Set.Ici s) s := by
      intro s hs
      exact hderiv s
        ⟨ha.1.trans_le hs.1, hs.2.trans_le ht.2⟩
    have hgrowth_at : ∀ s ∈ Set.Ico a t,
        deriv E s ≤ C * E s + 0 := by
      intro s hs
      simpa using hgrowth s
        ⟨ha.1.trans_le hs.1, hs.2.trans_le ht.2⟩
    have hgronwall := le_gronwallBound_of_liminf_deriv_right_le
      (f := E) (f' := fun s => deriv E s)
      (δ := E a) (K := C) (ε := 0) (a := a) (b := t)
      hcont_at
      (fun s hs r hr => (hderiv_at s hs).liminf_right_slope_le hr)
      (le_refl _) hgrowth_at t ⟨ha.2, le_rfl⟩
    simpa only [gronwallBound_ε0] using hgronwall
  have hlimit := ContinuousWithinAt.closure_le h0closure
    continuousWithinAt_const hrhscont hfrom
  simpa using hlimit

section AxiomAudit

#print axioms scalarEnergy_crude_exponential_bound_of_positive_time_deriv

end AxiomAudit

end ShenWork.Paper1
