import ShenWork.Paper1.Theorem12Corrected
import ShenWork.Paper1.Theorem12EnergyProducer

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Tail-start decay of the whole-line weighted energy

The weighted PDE energy inequality is naturally available only at strictly
positive times and, after the population has entered a sufficiently small
uniform box, only eventually.  This file starts Gronwall at a positive tail
time.  In particular, it requires neither an energy derivative nor a PDE
identity at the initial endpoint.
-/

/-- An eventually dissipative scalar energy decays exponentially from some
strictly positive tail time.  The continuity and derivative hypotheses are
needed only on the open positive-time half-line. -/
theorem scalarEnergy_eventual_exponential_bound_of_eventual_positive_time_deriv
    {E : ℝ → ℝ} {C : ℝ}
    (hcont : ContinuousOn E (Set.Ioi (0 : ℝ)))
    (hderiv : ∀ t : ℝ, 0 < t → HasDerivAt E (deriv E t) t)
    (hgrowth : ∀ᶠ t in atTop, deriv E t ≤ C * E t) :
    ∃ a : ℝ, 0 < a ∧
      ∀ t : ℝ, a ≤ t → E t ≤ E a * Real.exp (C * (t - a)) := by
  rcases eventually_atTop.1 hgrowth with ⟨T, hT⟩
  let a : ℝ := max 1 T
  have ha_pos : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_left 1 T)
  have hTa : T ≤ a := le_max_right 1 T
  refine ⟨a, ha_pos, ?_⟩
  intro t hat
  have hcont_at : ContinuousOn E (Set.Icc a t) := by
    apply hcont.mono
    intro s hs
    exact lt_of_lt_of_le ha_pos hs.1
  have hderiv_at : ∀ s ∈ Set.Ico a t,
      HasDerivWithinAt E (deriv E s) (Set.Ici s) s := by
    intro s hs
    exact (hderiv s (lt_of_lt_of_le ha_pos hs.1)).hasDerivWithinAt
  have hgrowth_at : ∀ s ∈ Set.Ico a t,
      deriv E s ≤ C * E s + 0 := by
    intro s hs
    simpa using hT s (hTa.trans hs.1)
  have hgronwall := le_gronwallBound_of_liminf_deriv_right_le
    (f := E) (f' := fun s => deriv E s)
    (δ := E a) (K := C) (ε := 0) (a := a) (b := t)
    hcont_at
    (fun s hs r hr => (hderiv_at s hs).liminf_right_slope_le hr)
    (le_refl _) hgrowth_at t ⟨hat, le_rfl⟩
  simpa only [gronwallBound_ε0] using hgronwall

/-- The canonical weighted energy converges to zero when its positive-time
derivative is eventually bounded by a strictly negative multiple of itself.
Eventual integrability is retained explicitly to exclude the convention that
the integral of a non-integrable function is zero. -/
theorem CoMovingWeightedL2Convergence.of_paper5WeightedEnergy_eventual_decay
    {eta c C : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hC : C < 0)
    (hcont : ContinuousOn
      (paper5WeightedEnergy eta c u U) (Set.Ioi (0 : ℝ)))
    (hderiv : ∀ t : ℝ, 0 < t →
      HasDerivAt (paper5WeightedEnergy eta c u U)
        (deriv (paper5WeightedEnergy eta c u U) t) t)
    (hgrowth : ∀ᶠ t in atTop,
      deriv (paper5WeightedEnergy eta c u U) t ≤
        C * paper5WeightedEnergy eta c u U t)
    (henergy_int : ∀ᶠ t in atTop, Integrable (fun z : ℝ =>
      Real.exp (2 * eta * z) * |u t (z + c * t) - U z| ^ 2)) :
    CoMovingWeightedL2Convergence eta c u U := by
  rcases
      scalarEnergy_eventual_exponential_bound_of_eventual_positive_time_deriv
        hcont hderiv hgrowth with
    ⟨a, _ha, hdecay_tail⟩
  let lam : ℝ := -C
  let A : ℝ := paper5WeightedEnergy eta c u U a * Real.exp (-C * a)
  have hlam : 0 < lam := by
    dsimp [lam]
    linarith
  have hdecay : ∀ᶠ t in atTop,
      coMovingWeightedL2Energy eta c u U t ≤
        A * Real.exp (-lam * t) := by
    filter_upwards [eventually_ge_atTop a] with t hat
    rw [← paper5WeightedEnergy_eq_coMovingWeightedL2Energy]
    calc
      paper5WeightedEnergy eta c u U t ≤
          paper5WeightedEnergy eta c u U a * Real.exp (C * (t - a)) :=
        hdecay_tail t hat
      _ = A * Real.exp (-lam * t) := by
        dsimp [A, lam]
        have hsign : - -C * t = C * t := by ring
        rw [hsign, mul_assoc, ← Real.exp_add]
        congr 2
        ring
  exact CoMovingWeightedL2Convergence.of_eventual_exponential_decay
    hlam hdecay henergy_int

section AxiomAudit

#print axioms
  scalarEnergy_eventual_exponential_bound_of_eventual_positive_time_deriv
#print axioms
  CoMovingWeightedL2Convergence.of_paper5WeightedEnergy_eventual_decay

end AxiomAudit

end ShenWork.Paper1
