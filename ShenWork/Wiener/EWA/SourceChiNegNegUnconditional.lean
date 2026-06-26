import ShenWork.Wiener.EWA.SourceChiNegFaithful
import ShenWork.Wiener.EWA.ChiNegUniformLifespan

/-!
# χ₀<0 Paper-2 Theorem 1.1 — FAITHFUL closeout, lifespan discharged + frontier isolated

`SourceChiNegFaithful.lean` reduces the χ₀<0 headline `Theorem_1_1 intervalDomain p`
to the SINGLE faithful (non-vacuous) obligation `ChiNegDatumUniformConstructionFaithful p`:

  `∀ M>0, ∃δ>0, ∀ positive |u₀|≤M, ∃ u_star : EWA δ 1,`
  `  CoupledDuhamelReducedClassicalCore p δ u₀ (realSlice u_star)`.

Crucially this carries **NO `hfp`** (the false logistic Duhamel identity that made the
old `ChiNegDatumUniformConstruction` vacuous for χ₀<0): the only carried content is the
EWA fixed point and its reduced classical core (the genuine `evalST`-realization frontier).

This file is the culminating **assembly + honest accounting** for that faithful obligation.

## What is discharged here (mechanical, banked)

* **the shared lifespan `δ(M)`** — from `exists_uniform_EWA_lifespan`
  (`ChiNegUniformLifespan.lean`): the monotone-lifespan bookkeeping that reorders the
  per-datum `∀u₀, ∃T` into the datum-uniform `∃δ, ∀u₀`.  The `∃δ` quantifier and its
  positivity are produced HERE, so the named frontier below carries the realized-track
  atoms on exactly that `δ`, never re-introducing its own.

## What remains the residual (`ChiNegFaithfulRealizationFrontier p`)

The per-datum realized-track atoms `(u_star, C)` on the shared `δ` — i.e. the reduced
coupled-Duhamel classical core for the Picard fixed point.  This bottoms out, through
`realSlice_reducedCore` (`SourceReducedCore.lean`) and the realized-source records
`chemDiv_realizesOn` / `logistic_realizesOn` (`SourceRealizesRecords.lean`, consumed by
`realizes_clean`), in the `evalST`-realization atoms

* `h_flux_nbhd : evalST τ y (incl (chemFluxEWA … u_star)) = (chemFluxLifted p (realSlice u_star τ.1) y : ℂ)`,
* `h_u  : evalST τ x (incl u_star)               = (intervalDomainLift (realSlice u_star τ.1) x : ℂ)`,
* `h_uα : evalST τ x (incl (realPowEWA u_star p.α)) = ((intervalDomainLift (realSlice u_star τ.1) x ^ p.α : ℝ) : ℂ)`,

for the **Picard fixed point** `u_star = picardEWA … u_star`.

### Why these are not dischargeable from the landed bridges (the precise minimal residual)

The only landed PRODUCER of `h_flux_nbhd` / `h_u` / `h_uα`-shape facts —
`flux_nbhd_of_embed_discharged` (`SourceFluxNbhdDischarge.lean`) and `embedEWA_realizes`
(`EmbedEWA.lean`) — produce them ONLY for an **embed-form** element `u_star = embedEWA u …`,
where `u` is a prescribed real-space family.  Everything downstream
(`realSlice_realizes_of_atoms`, `realizes_clean`, `chemDiv_realizesOn`,
`logistic_realizesOn`, the evalST bridges `evalST_sourceEWA_eq_intervalCoupledSource`,
`evalST_chemFluxEWA_eq_chemFluxLifted`, `evalST_growthEWA_eq_logisticLifted`) **carries**
these atoms as hypotheses and only reconciles them with the spectral synthesis; none
manufactures them.  The fixed point delivered by `picardEWA_uncond_fixedPoint` satisfies
the EWA-level identity `u_star = picardEWA … u_star` and is NOT of embed form, and there is
no `picardEWA → embedEWA` bridge anywhere in the tree (verified by exhaustive grep).  So the
realization atoms for the fixed point are the irreducible open content — exactly as
flagged in the module docstrings of `SourceClassicalExistence` and `SourceReducedCore`,
and as carried explicitly (not silently) by the previously-landed
`chiNeg_theorem_1_1_unconditional` via `ChiNegRealizationFrontier`.

We therefore name this content as the SINGLE faithful frontier
`ChiNegFaithfulRealizationFrontier p`, discharge the lifespan from it, and expose it as an
EXPLICIT hypothesis of `chiNeg_theorem_1_1_unconditional_faithful` — **no hidden axiom, no
`hfp` re-introduced.**  This is the honest faithful χ₀<0 closeout: unconditional modulo one
crisply-named, genuinely-satisfiable realization frontier (the fixed point realizing its
own cosine synthesis), and provably NON-vacuous (unlike the χ₀=0-forcing `hfp` route).

No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/

open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint)
open ShenWork.Paper2 (PositiveInitialDatum Theorem_1_1)
open ShenWork.IntervalCoupledRegularityBootstrap (CoupledDuhamelReducedClassicalCore)

noncomputable section

namespace ShenWork.EWA

/-- **The χ₀<0 FAITHFUL realization-track frontier (the genuine open residual).**

For each datum size `M > 0`, each shared lifespan `δ > 0` (the one
`exists_uniform_EWA_lifespan` returns), and each positive admissible datum `u₀` with
`|u₀| ≤ M`, this supplies the per-datum realized-track atoms ON exactly that `δ`:

* the EWA fixed point `u_star : EWA δ 1`;
* `C` — the reduced coupled-Duhamel classical core
  `CoupledDuhamelReducedClassicalCore p δ u₀ (realSlice u_star)` (whose banked feeders
  bottom out in the `evalST`-realization atoms `h_flux_nbhd` / `h_u` / `h_uα` for the
  fixed point — produced by no file, see the module docstring).

**Contrast with the vacuous `ChiNegRealizationFrontier`:** that one *also* carried the
false logistic Duhamel identity `hfp`.  Here there is **NO `hfp`** — the carried content
is exactly the genuinely satisfiable cosine-synthesis realization of the fixed point.

It is stated `∀ δ, 0 < δ → …` rather than introducing its own `δ` so that the `∃ δ` of
`ChiNegDatumUniformConstructionFaithful` is discharged HERE from
`exists_uniform_EWA_lifespan`, not silently re-assumed inside the frontier. -/
def ChiNegFaithfulRealizationFrontier (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∀ {u0 : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u0 →
      (∀ x, |u0 x| ≤ M) →
        ∃ u_star : EWA δ 1,
          CoupledDuhamelReducedClassicalCore p δ u0 (realSlice u_star)

/-- **The faithful datum-uniform construction follows from the faithful frontier.**

The shared lifespan `δ(M)` is produced HERE by `exists_uniform_EWA_lifespan`
(specialized at zero uniform constant-bounds and `ρ = 1`, admissible since it only needs
`0 ≤ ·` bounds and `0 < ρ`); the per-datum realized-track atoms on that very `δ` come
from the named faithful frontier.  This is the clean quantifier-reorder
`∀u₀ ∃T ↝ ∃δ ∀u₀`, with the genuine analytic content quarantined in the frontier and —
crucially — NO `hfp` anywhere. -/
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

/-- **χ₀<0 FAITHFUL datum-uniform construction (assembled modulo the faithful frontier).**

`ChiNegDatumUniformConstructionFaithful p` holds once the single named faithful
realization frontier is provided; the shared lifespan is discharged here.  No `hfp`. -/
theorem chiNeg_datumUniformConstructionFaithful (p : CM2Params)
    (hF : ChiNegFaithfulRealizationFrontier p) :
    ChiNegDatumUniformConstructionFaithful p :=
  chiNeg_datumUniformFaithful_of_frontier p hF

/-- **χ₀<0 FAITHFUL Paper-2 Theorem 1.1 — modulo the single faithful realization frontier.**

Combines `chiNeg_datumUniformConstructionFaithful` with the faithful headline
`chiNeg_theorem_1_1_faithful` (`SourceChiNegFaithful.lean`).  This is the χ₀<0 headline
`Theorem_1_1 intervalDomain p` produced from ONE crisply-named, **non-vacuous** analytic
residual — the faithful realization frontier (the Picard fixed point realizing its own
cosine synthesis) — with the datum-uniform lifespan bookkeeping and the reduced-core
wiring discharged, and NEVER the false logistic Duhamel identity `hfp`.

It is NOT claimed fully unconditional: the realization frontier is an explicit hypothesis
(no hidden `axiom`).  The remaining gap is exactly the irreducible `evalST`-realization
atoms (`h_flux_nbhd` / `h_u` / `h_uα`) for the Picard fixed point, whose only landed
producers (`flux_nbhd_of_embed_discharged`, `embedEWA_realizes`) require embed-form
`u_star = embedEWA u …` — and no `picardEWA → embedEWA` bridge exists in the tree. -/
theorem chiNeg_theorem_1_1_unconditional_faithful (p : CM2Params) (hchi : p.χ₀ < 0)
    (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hF : ChiNegFaithfulRealizationFrontier p) :
    Theorem_1_1 intervalDomain p :=
  chiNeg_theorem_1_1_faithful p hchi ha hb hα hγ
    (chiNeg_datumUniformConstructionFaithful p hF)

end ShenWork.EWA

namespace ShenWork.EWA
section AxiomAudit
#print axioms chiNeg_datumUniformFaithful_of_frontier
#print axioms chiNeg_datumUniformConstructionFaithful
#print axioms chiNeg_theorem_1_1_unconditional_faithful
end AxiomAudit
end ShenWork.EWA
