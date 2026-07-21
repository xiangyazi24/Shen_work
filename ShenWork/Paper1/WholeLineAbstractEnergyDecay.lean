import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Abstract exponential energy decay (the thin capstone of the L² tower)

The sharp-threshold far-left stability argument reduces, once the measure-theoretic
bridge is in place, to a single ODE fact: a nonnegative energy whose derivative is
bounded by `-2λ` times itself decays exponentially and tends to `0`.  This file
records that fact as a self-contained structure so the analytic layer
(differentiation under the integral, weighted IBP, the resolver identities as
actual integrals) can be developed separately and plugged in as the fields.

The design (per the L²-framework plan in `INTEGRITY_GAPS.md`, 2026-07-21) is a
two-layer split: ALL the measure theory lives in a thick `WeightedEnergySolution`
bundle whose construction is deferred; this thin `AbstractEnergyDecay` interface is
pure calculus and its capstone `decay_to_zero` is unconditional.  The sharp
threshold `χγ < (1 + √α)²` enters at exactly one place — the construction of the
`coercive` field from the already-proven dissipation brick — and nowhere here.
-/

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- A nonnegative energy with an exponential dissipation budget.  `E` is the
energy, `D t` its time-derivative, and `coercive` is the dissipation inequality
`Ė ≤ -2λ E`.  Everything is scalar calculus — no PDE objects, no measure theory. -/
structure AbstractEnergyDecay where
  E : ℝ → ℝ
  D : ℝ → ℝ
  lam : ℝ
  hlam : 0 < lam
  E_nonneg : ∀ t, 0 ≤ E t
  E_deriv : ∀ t, HasDerivAt E (D t) t
  coercive : ∀ t, D t ≤ -2 * lam * E t

namespace AbstractEnergyDecay

variable (A : AbstractEnergyDecay)

/-- The integrating-factor potential `G t = E t · e^{2λ t}` is antitone: its
derivative `(D t + 2λ E t) e^{2λ t}` is `≤ 0` by the dissipation inequality. -/
theorem exp_energy_antitone :
    ∀ t, HasDerivAt (fun s => A.E s * Real.exp (2 * A.lam * s))
      ((A.D t + 2 * A.lam * A.E t) * Real.exp (2 * A.lam * t)) t := by
  intro t
  have hE := A.E_deriv t
  have hexp : HasDerivAt (fun s => Real.exp (2 * A.lam * s))
      (Real.exp (2 * A.lam * t) * (2 * A.lam)) t := by
    have h := ((hasDerivAt_id t).const_mul (2 * A.lam)).exp
    simpa using h
  have hprod := hE.mul hexp
  convert hprod using 1
  ring

/-- **Exponential decay.**  `E t ≤ E 0 · e^{-2λ t}` for `t ≥ 0`. -/
theorem energy_le (t : ℝ) (ht : 0 ≤ t) :
    A.E t ≤ A.E 0 * Real.exp (-2 * A.lam * t) := by
  set G : ℝ → ℝ := fun s => A.E s * Real.exp (2 * A.lam * s) with hG
  have hderiv : ∀ s, HasDerivAt G ((A.D s + 2 * A.lam * A.E s) *
      Real.exp (2 * A.lam * s)) s := A.exp_energy_antitone
  have hGdiff : Differentiable ℝ G := fun s => (hderiv s).differentiableAt
  have hGderiv_nonpos : ∀ s, deriv G s ≤ 0 := by
    intro s
    rw [(hderiv s).deriv]
    have h1 : A.D s + 2 * A.lam * A.E s ≤ 0 := by
      have hc := A.coercive s
      have hn := A.E_nonneg s
      linarith
    exact mul_nonpos_of_nonpos_of_nonneg h1 (Real.exp_pos _).le
  have hanti : G t ≤ G 0 := antitone_of_deriv_nonpos hGdiff hGderiv_nonpos ht
  -- G t ≤ G 0 = E 0, and G t = E t · e^{2λt}
  have hG0 : G 0 = A.E 0 := by simp [hG]
  have hGt : G t = A.E t * Real.exp (2 * A.lam * t) := rfl
  rw [hG0] at hanti
  have hexp_pos : 0 < Real.exp (2 * A.lam * t) := Real.exp_pos _
  -- from E t · e^{2λt} ≤ E 0 divide
  have hfin : A.E t ≤ A.E 0 / Real.exp (2 * A.lam * t) := by
    rw [le_div_iff₀ hexp_pos]; rw [hGt] at hanti; linarith
  have hrw : A.E 0 / Real.exp (2 * A.lam * t) = A.E 0 * Real.exp (-2 * A.lam * t) := by
    rw [div_eq_mul_inv, ← Real.exp_neg]; congr 2; ring
  rwa [hrw] at hfin

/-- **The energy tends to `0`.** -/
theorem decay_to_zero : Tendsto A.E atTop (𝓝 0) := by
  -- inner: -2λ t → atBot
  have h1 : Tendsto (fun t : ℝ => 2 * A.lam * t) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by linarith [A.hlam] : (0:ℝ) < 2 * A.lam)
      tendsto_id
  have hlin : Tendsto (fun t : ℝ => -2 * A.lam * t) atTop atBot := by
    have h2 := tendsto_neg_atTop_atBot.comp h1
    have heq : (fun t : ℝ => -2 * A.lam * t) = (Neg.neg ∘ fun t : ℝ => 2 * A.lam * t) := by
      funext s; simp only [Function.comp]; ring
    rw [heq]; exact h2
  have hexp0 : Tendsto (fun t : ℝ => Real.exp (-2 * A.lam * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  have hub : Tendsto (fun t => A.E 0 * Real.exp (-2 * A.lam * t)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := A.E 0) (f := atTop (α := ℝ))).mul hexp0
    simpa using this
  -- squeeze 0 ≤ E t ≤ E 0 · e^{-2λt} → 0 (eventually, for t ≥ 0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub ?_ ?_
  · exact Eventually.of_forall (fun t => A.E_nonneg t)
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact A.energy_le t ht

end AbstractEnergyDecay

end ShenWork.Paper1

namespace ShenWork.Paper1.AbstractEnergyDecay
section AxiomAudit
#print axioms ShenWork.Paper1.AbstractEnergyDecay.energy_le
#print axioms ShenWork.Paper1.AbstractEnergyDecay.decay_to_zero
end AxiomAudit
end ShenWork.Paper1.AbstractEnergyDecay
