/-
  ShenWork/Wiener/EWA/ChiNegFrontierAssembly.lean

  **χ₀<0 faithful realization frontier — the `hfp`-free capstone.**

  This file defines `ChiNegFaithfulRealizationFrontier p`, the PER-DATUM
  realization-track obligation for the faithful (no-`hfp`) χ₀<0 route, and
  proves it feeds the datum-uniform construction
  `ChiNegDatumUniformConstructionFaithful p` (via the lifespan reorder from
  `exists_uniform_EWA_lifespan`), and hence the headline
  `Theorem_1_1 intervalDomain p`.

  ## Relationship to the existing non-faithful frontier

  `ChiNegRealizationFrontier p` (`SourceChiNegDatumUniform.lean:98`) carries, per
  datum, BOTH:
  * `hfp` — the realized-slice Duhamel identity in `intervalDuhamelOperator` form; AND
  * `C`  — `CoupledDuhamelReducedClassicalCore p δ u₀ (realSlice u_star)`.

  But `hfp` uses `intervalDuhamelOperator`, which is the LOGISTIC-ONLY mild map,
  making it unsatisfiable for χ₀<0 (where the chemotaxis Duhamel term is nonzero).
  The faithful route (`SourceChiNegFaithful.lean`) proved that the headline follows
  from `C` ALONE — no `hfp` needed — through the unconditional regularity bootstrap
  `regularityBootstrap_of_coupledDuhamel_reducedClassicalCore` +
  `IsPaper2ClassicalSolution.of_components`.

  `ChiNegFaithfulRealizationFrontier p` is the per-datum carrier of `C` WITHOUT
  `hfp`, exactly the satisfiable portion of the realization atoms.  The quantifier
  shape `∀ M, ∀ δ, ∀ u₀` matches `ChiNegRealizationFrontier` so the `∃ δ` is
  discharged here (not inside the frontier) from `exists_uniform_EWA_lifespan`.

  ## What this file proves

  1. `ChiNegFaithfulRealizationFrontier p → ChiNegDatumUniformConstructionFaithful p`
     (`chiNeg_datumUniformFaithful_of_frontier`): the lifespan reorder.

  2. `ChiNegFaithfulRealizationFrontier p → Theorem_1_1 intervalDomain p`
     (`chiNeg_theorem_1_1_of_faithfulFrontier`): the full headline, composing the
     lifespan reorder with `chiNeg_theorem_1_1_faithful`.

  3. The projection from the non-faithful frontier to the faithful one (forgetful
     direction: drop `hfp`, keep `C`).

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceChiNegFaithful
import ShenWork.Wiener.EWA.SourceChiNegDatumUniform
import ShenWork.Wiener.EWA.ChiNegUniformLifespan

noncomputable section

namespace ShenWork.EWA

open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint)
open ShenWork.Paper2 (PositiveInitialDatum Theorem_1_1)
open ShenWork.IntervalCoupledRegularityBootstrap (CoupledDuhamelReducedClassicalCore)

/-! ### The faithful realization frontier (no `hfp`). -/

/-- **The χ₀<0 faithful realization-track frontier (no `hfp`).**

For each datum size `M > 0` and each lifespan `δ > 0` (the one
`exists_uniform_EWA_lifespan` will return), and for each positive admissible
datum `u₀` with `|u₀| ≤ M`, this supplies the per-datum realized-track atoms
on exactly that `δ`:

* the EWA fixed point `u_star : EWA δ 1`;
* `C` — the reduced coupled-Duhamel classical core
  `CoupledDuhamelReducedClassicalCore p δ u₀ (realSlice u_star)`.

Unlike `ChiNegRealizationFrontier p`, this does NOT carry the Duhamel
fixed-point identity `hfp` (the `intervalDuhamelOperator`-form mild equation),
which is unsatisfiable for χ₀<0 because `intervalDuhamelOperator` is the
logistic-only mild map.  The faithful discharge route
(`chiNeg_theorem_1_1_faithful`) proves the headline from `C` alone via the
unconditional regularity bootstrap, so `hfp` is unnecessary.

The `∀ δ, 0 < δ →` quantifier shape matches `ChiNegRealizationFrontier`: the
frontier does NOT introduce its own `δ`; the `∃ δ` of
`ChiNegDatumUniformConstructionFaithful` is discharged externally from
`exists_uniform_EWA_lifespan`. -/
def ChiNegFaithfulRealizationFrontier (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∀ {u0 : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u0 →
      (∀ x, |u0 x| ≤ M) →
        ∃ u_star : EWA δ 1,
          CoupledDuhamelReducedClassicalCore p δ u0 (realSlice u_star)

/-! ### The faithful frontier implies the faithful datum-uniform construction. -/

/-- **The faithful datum-uniform construction follows from the faithful frontier.**

The shared lifespan `δ(M)` is produced HERE by `exists_uniform_EWA_lifespan`
(specialized at zero uniform constant-bounds and `ρ = 1`, admissible since
`exists_uniform_EWA_lifespan` only needs `0 ≤ ·` bounds and `0 < ρ`); the
per-datum realized-track atoms on that `δ` come from the faithful frontier.
This is the clean `∀ u₀ ∃ T → ∃ δ ∀ u₀` lifespan reorder, with the genuine
analytic content quarantined in the frontier — and NO `hfp` anywhere.

Mirrors `chiNeg_datumUniform_of_realizationFrontier` for the non-faithful
chain, but drops the `hfp` component throughout. -/
theorem chiNeg_datumUniformFaithful_of_frontier (p : CM2Params)
    (hF : ChiNegFaithfulRealizationFrontier p) :
    ChiNegDatumUniformConstructionFaithful p := by
  intro M hM
  obtain ⟨δ, hδpos, _⟩ :=
    exists_uniform_EWA_lifespan (χ₀ := p.χ₀)
      (LQbar := 0) (LGbar := 0) (MQbar := 0) (MGbar := 0) (ρ := 1)
      le_rfl le_rfl le_rfl le_rfl one_pos
  refine ⟨δ, hδpos, ?_⟩
  intro u0 hu0 hbd
  exact hF M hM δ hδpos hu0 hbd

/-- **Faithful datum-uniform construction (assembled modulo the faithful frontier).**

`ChiNegDatumUniformConstructionFaithful p` holds once the faithful frontier
`ChiNegFaithfulRealizationFrontier p` is provided; the shared lifespan is
discharged here. -/
theorem chiNeg_datumUniformConstructionFaithful_of_frontier (p : CM2Params)
    (hF : ChiNegFaithfulRealizationFrontier p) :
    ChiNegDatumUniformConstructionFaithful p :=
  chiNeg_datumUniformFaithful_of_frontier p hF

/-! ### The full headline from the faithful frontier. -/

/-- **χ₀<0 Paper-2 Theorem 1.1 — modulo the faithful realization frontier.**

Combines `chiNeg_datumUniformFaithful_of_frontier` with
`chiNeg_theorem_1_1_faithful` (`SourceChiNegFaithful.lean`).  This is the
χ₀<0 headline `Theorem_1_1 intervalDomain p` produced from ONE crisply-named,
SATISFIABLE analytic residual — the faithful realization-track frontier (no
`hfp`) — with the datum-uniform lifespan bookkeeping, the reduced-core wiring,
and the no-`hfp` regularity-bootstrap discharge all banked.

The frontier carries ONLY `(u_star, C)` per datum — the EWA fixed point and its
coupled-Duhamel reduced classical core — which are genuine `evalST`-realization
facts, not the false logistic-only Duhamel identity.

Not unconditional: the frontier is an explicit hypothesis (no hidden `axiom`). -/
theorem chiNeg_theorem_1_1_of_faithfulFrontier (p : CM2Params) (hchi : p.χ₀ < 0)
    (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hF : ChiNegFaithfulRealizationFrontier p) :
    Theorem_1_1 intervalDomain p :=
  chiNeg_theorem_1_1_faithful p hchi ha hb hα hγ
    (chiNeg_datumUniformFaithful_of_frontier p hF)

/-! ### Projection from the non-faithful frontier. -/

/-- **The (non-faithful) realization frontier implies the faithful one.**

`ChiNegRealizationFrontier p` carries `∃ u_star, (hfp ∧ C)` per datum;
projecting away `hfp` (the second component of the conjunction) yields the
faithful frontier `∃ u_star, C`.  This is the forgetful direction: the faithful
frontier is genuinely WEAKER than the non-faithful one (it asks for less). -/
theorem chiNeg_faithfulFrontier_of_realizationFrontier (p : CM2Params)
    (hF : ChiNegRealizationFrontier p) :
    ChiNegFaithfulRealizationFrontier p := by
  intro M hM δ hδ u0 hu0 hbd
  obtain ⟨u_star, _, hC⟩ := hF M hM δ hδ hu0 hbd
  exact ⟨u_star, hC⟩

end ShenWork.EWA

namespace ShenWork.EWA
section AxiomAudit
#print axioms chiNeg_datumUniformFaithful_of_frontier
#print axioms chiNeg_datumUniformConstructionFaithful_of_frontier
#print axioms chiNeg_theorem_1_1_of_faithfulFrontier
#print axioms chiNeg_faithfulFrontier_of_realizationFrontier
end AxiomAudit
end ShenWork.EWA
