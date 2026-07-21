import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Scalar Gronwall comparison (barrier core)

The scalar shadow of the parabolic first-touch comparison: if `g` starts
nonpositive and satisfies the one-sided linear differential inequality
`g'(t) ≤ L · g(t)` for `t ≥ 0`, then `g(t) ≤ 0` for all `t ≥ 0`.

Proof: `G(t) = e^{−Lt} g(t)` has `G'(t) = e^{−Lt}(g'(t) − L g(t)) ≤ 0`, so `G` is
antitone on `[0,∞)`, giving `G(t) ≤ G(0) = g(0) ≤ 0`, and `e^{−Lt} > 0` yields
`g(t) ≤ 0`.  This is the integrating-factor comparison (same tool as
`AbstractEnergyDecay`) and it is what the barrier argument reduces to once the
PDE first-touch supplies the differential inequality for `g = α − u` (or
`u − β`).
-/

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- **Scalar Gronwall barrier.**  If `g 0 ≤ 0` and `g'(t) ≤ L g(t)` for `t ≥ 0`,
then `g t ≤ 0` for all `t ≥ 0`. -/
theorem gronwall_barrier {g dg : ℝ → ℝ} {L : ℝ}
    (hg : ∀ t, HasDerivAt g (dg t) t)
    (h0 : g 0 ≤ 0)
    (hineq : ∀ t, 0 ≤ t → dg t ≤ L * g t) :
    ∀ t, 0 ≤ t → g t ≤ 0 := by
  set G : ℝ → ℝ := fun t => Real.exp (-L * t) * g t with hG
  -- G'(t) = e^{-Lt}(dg t - L g t)
  have hGderiv : ∀ t, HasDerivAt G
      (Real.exp (-L * t) * (dg t - L * g t)) t := by
    intro t
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-L * t))
        (Real.exp (-L * t) * (-L)) t := by
      have h := (((hasDerivAt_id t).const_mul (-L))).exp
      simpa using h
    have hprod := hexp.mul (hg t)
    convert hprod using 1
    ring
  intro t ht
  -- G antitone on [0,t]: G'(s) ≤ 0
  have hanti : G t ≤ G 0 := by
    have hmono : AntitoneOn G (Set.Icc 0 t) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
      · exact fun s _ => (hGderiv s).continuousAt.continuousWithinAt
      · exact fun s _ => (hGderiv s).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        rw [(hGderiv s).deriv]
        have hs0 : 0 ≤ s := le_of_lt hs.1
        have h1 : dg s - L * g s ≤ 0 := by
          have := hineq s hs0; linarith
        exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le h1
    exact hmono (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht) ht
  -- G 0 = g 0 ≤ 0, and G t = e^{-Lt} g t with e^{-Lt} > 0
  have hG0 : G 0 = g 0 := by simp [hG]
  have hGt : G t = Real.exp (-L * t) * g t := rfl
  have hexp_pos : 0 < Real.exp (-L * t) := Real.exp_pos _
  rw [hG0] at hanti
  rw [hGt] at hanti
  -- e^{-Lt} g t ≤ g 0 ≤ 0, so g t ≤ 0
  nlinarith [hanti, h0, hexp_pos, mul_pos hexp_pos (Real.exp_pos (L * t))]

/-- Upper-barrier form: if `g 0 ≥ 0` and `L g(t) ≤ g'(t)` for `t ≥ 0`, then
`g t ≥ 0` (apply `gronwall_barrier` to `−g`). -/
theorem gronwall_barrier_ge {g dg : ℝ → ℝ} {L : ℝ}
    (hg : ∀ t, HasDerivAt g (dg t) t)
    (h0 : 0 ≤ g 0)
    (hineq : ∀ t, 0 ≤ t → L * g t ≤ dg t) :
    ∀ t, 0 ≤ t → 0 ≤ g t := by
  have hneg := gronwall_barrier (g := fun t => -g t) (dg := fun t => -dg t) (L := L)
    (fun t => (hg t).neg) (by simpa using h0)
    (by intro t ht; have := hineq t ht; simp only; nlinarith [this])
  intro t ht
  have := hneg t ht
  simpa using this

section AxiomAudit

#print axioms gronwall_barrier
#print axioms gronwall_barrier_ge

end AxiomAudit

end ShenWork.Paper1
