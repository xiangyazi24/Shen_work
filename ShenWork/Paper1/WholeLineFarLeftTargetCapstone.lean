import ShenWork.Paper1.WholeLineFarLeftDirect
import ShenWork.Paper1.WholeLineCauchyLeftTailBridge

/-!
# Final adapter: direct barrier ⟹ `UniformCoMovingLeftEquilibriumConvergence`

`far_left_convergence_direct` produces the whole-line, still-frame statement
`∀ ε > 0, ∃ T, ∀ t z, T ≤ t → 0 ≤ t → |w t z − 1| < ε`.  The paper's target

`UniformCoMovingLeftEquilibriumConvergence c u :=`
`  ∀ ε > 0, ∃ R T, ∀ t z, T ≤ t → z ≤ −R → |coMovingPath c u t z − 1| < ε`

is the SAME convergence, applied to the co-moving field `w = coMovingPath c u`
(`coMovingPath c u t z = u t (z + c t)`), and further RESTRICTED to the far-left
half-line `z ≤ −R`.  Since the barrier bound holds for every `z`, the restriction
is free (`R = 0`), and the `0 ≤ t` side-condition is absorbed by taking the
threshold `max T 0`.

This file is pure logic — it plugs the proved direct capstone into the exact
target definition, leaving only the co-moving solution's PDE-structural
hypotheses (time-derivative = RHS, attained continuous band envelopes, `hstart`,
touch-slope rates) as inputs.  Those inputs are exactly what the companion files
(`WholeLineHstartProducer`, `WholeLineInfSupNormControl`, and the dispatched
regularity/attainment/rate questions) supply.
-/

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- **Adapter.**  A whole-line, still-frame exponential-barrier convergence for
`coMovingPath c u` yields the far-left target definition. -/
theorem uniformCoMoving_of_wholeLine {c : ℝ} {u : ℝ → ℝ → ℝ}
    (h : ∀ ε > 0, ∃ T : ℝ, ∀ t z : ℝ,
      T ≤ t → 0 ≤ t → |coMovingPath c u t z - 1| < ε) :
    UniformCoMovingLeftEquilibriumConvergence c u := by
  intro ε hε
  obtain ⟨T, hT⟩ := h ε hε
  refine ⟨0, max T 0, ?_⟩
  intro t z ht _hz
  have htT : T ≤ t := le_trans (le_max_left T 0) ht
  have ht0 : 0 ≤ t := le_trans (le_max_right T 0) ht
  exact hT t z htT ht0

/-- **Final far-left capstone.**  Given the co-moving solution `w = coMovingPath c u`
as a classical solution on its regularity set — time-derivative `wt` equal to the
PDE right-hand side, an attained continuous lower/upper band `[a,b]`, the initial
confinement `hstart`, and the two touch-slope rate inequalities — the paper's
`UniformCoMovingLeftEquilibriumConvergence` holds.  Every hypothesis here is a
statement about the specific solution; the abstract machinery is discharged. -/
theorem uniformCoMoving_far_left
    {c : ℝ} {u : ℝ → ℝ → ℝ} {a b : ℝ → ℝ} {wt : ℝ → ℝ → ℝ} {D lam : ℝ}
    (hlam : 0 < lam)
    (hwt : ∀ t z, HasDerivAt (fun s => coMovingPath c u s z) (wt t z) t)
    (ha_cont : Continuous a) (hb_cont : Continuous b)
    (ha_lb : ∀ t z, a t ≤ coMovingPath c u t z)
    (hb_ub : ∀ t z, coMovingPath c u t z ≤ b t)
    (ha_attain : ∀ t, ∃ z0, a t = coMovingPath c u t z0)
    (hb_attain : ∀ t, ∃ z0, b t = coMovingPath c u t z0)
    (hstartLo : ∃ ε, 0 < ε ∧ ∀ t, 0 ≤ t → t ≤ ε →
      1 - D * Real.exp (-lam * t) ≤ a t)
    (hstartHi : ∃ ε, 0 < ε ∧ ∀ t, 0 ≤ t → t ≤ ε →
      b t ≤ 1 + D * Real.exp (-lam * t))
    (hrateLo : ∀ t z0, 0 ≤ t → (∀ z, coMovingPath c u t z0 ≤ coMovingPath c u t z) →
      coMovingPath c u t z0 = 1 - D * Real.exp (-lam * t) →
      lam * (D * Real.exp (-lam * t)) < wt t z0)
    (hrateHi : ∀ t z0, 0 ≤ t → (∀ z, coMovingPath c u t z ≤ coMovingPath c u t z0) →
      coMovingPath c u t z0 = 1 + D * Real.exp (-lam * t) →
      wt t z0 < -(lam * (D * Real.exp (-lam * t)))) :
    UniformCoMovingLeftEquilibriumConvergence c u :=
  uniformCoMoving_of_wholeLine
    (far_left_convergence_direct (u := coMovingPath c u) hlam hwt ha_cont hb_cont
      ha_lb hb_ub ha_attain hb_attain hstartLo hstartHi hrateLo hrateHi)

section AxiomAudit

#print axioms uniformCoMoving_of_wholeLine
#print axioms uniformCoMoving_far_left

end AxiomAudit

end ShenWork.Paper1
