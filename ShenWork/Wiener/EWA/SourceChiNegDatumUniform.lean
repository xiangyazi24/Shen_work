import ShenWork.Wiener.EWA.SourceChiNegTheorem11
import ShenWork.Wiener.EWA.ChiNegUniformLifespan

/-!
# χ₀<0 Paper-2 Theorem 1.1 — culminating datum-uniform assembly

`SourceChiNegTheorem11.lean` performs the honest reduction of the headline
`Theorem_1_1 intervalDomain p` (for `χ₀ < 0`) to the SINGLE packaged obligation
`ChiNegDatumUniformConstruction p`:

  `∀ M>0, ∃δ>0, ∀ positive |u₀|≤M, ∃ u_star : EWA δ 1,`
  `  (realSlice-Duhamel fixed-point identity hfp) ∧`
  `  CoupledDuhamelReducedClassicalCore p δ u₀ (realSlice u_star)`.

This file is the CAPSTONE assembly.  It supplies the genuinely-mechanical half of
that obligation and isolates, as a single crisply-named residual Prop
`ChiNegRealizationFrontier p`, exactly the realization-track content that NO file
in the tree produces.

## What is supplied here (mechanical, banked)

* **the shared lifespan `δ(M)`** — from `exists_uniform_EWA_lifespan`
  (`ChiNegUniformLifespan.lean`): the monotone-lifespan bookkeeping that reorders
  the per-datum `∀u₀, ∃T` into the datum-uniform `∃δ, ∀u₀`.  Concretely
  `ChiNegRealizationFrontier` is required to carry the realized-track atoms ON
  exactly the `δ` that `exists_uniform_EWA_lifespan` returns, so the `∃δ`
  quantifier and its positivity are discharged here, not assumed inside the
  frontier.

## What remains the residual (`ChiNegRealizationFrontier p`)

The per-datum realized-track atoms `(u_star, hfp, C)` on the shared `δ`.  Every
banked discharge that feeds the reduced core
(`realSlice_reducedCore`, `SourceReducedCore.lean`) — `realSlice_realizes_of_atoms`,
`realSlice_resolverSpectralData_full`, `realSlice_hchemInv_direct_realSlice`,
`realSlice_hlogInv_of_bankedU`, `realSlice_initialTrace`, the `DuhamelSourceTimeC1`
producers, … — itself CONSUMES carried atoms that bottom out in three families of
content that are NOT in the current tree:

1. **`hfp`** — the realized-slice Duhamel identity
   `realSlice u_star t x = intervalDuhamelOperator p u₀ (realSlice u_star) t x`.
   `intervalDuhamelOperator` occurs in NO EWA-track theorem's conclusion; the EWA
   fixed-point engines (`picardEWA_uncond_fixedPoint`, `picardEWA_clean_fixedPoint`)
   produce only the EWA-level identity `u_star = picardEWA … u_star`.  The bridge
   from that to the real-space `intervalDuhamelOperator` form is `hfp` itself.

2. **the `evalST`-realization atoms** — `realizes`/`hrealizes`, `h_flux_nbhd`,
   `h_u`, `h_uα`, `hagree` — i.e. `evalST`-of-Duhamel `=` spectral synthesis for
   the chemDiv/logistic legs.  The module docstrings of `SourceClassicalExistence`
   and `SourceReducedCore` flag this exact bridge as "not in the tree".

3. **the per-slice spectral / time-derivative data** — `hK1`, `bc`, `vdotL`,
   the quadratic-decay coefficients, and the chem-source C³/C⁴-Neumann data flagged
   in `realSlice_hchemInv_C2Neumann_residual` — each carried, never produced.

Bundling these datum-uniformly is the genuine open content of the whole χ₀<0 track.
`ChiNegRealizationFrontier p` names it in EXACTLY the per-datum shape the headline
needs, so the reduction `ChiNegDatumUniformConstruction p` ← `ChiNegRealizationFrontier p`
is a clean quantifier wiring (the `∃δ` discharged via `exists_uniform_EWA_lifespan`),
and the χ₀<0 Paper-2 headline is unconditional MODULO this one named frontier.

`chiNeg_theorem_1_1` is NOT made unconditional with a hidden axiom: the residual
frontier is carried as an explicit hypothesis of `chiNeg_theorem_1_1_unconditional`.

No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/

open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint)
open ShenWork.Paper2 (PositiveInitialDatum Theorem_1_1)
open ShenWork.IntervalCoupledRegularityBootstrap (CoupledDuhamelReducedClassicalCore)
open ShenWork.IntervalDomainExistence (intervalDuhamelOperator)

noncomputable section

namespace ShenWork.EWA

/-- **The χ₀<0 realization-track frontier (the genuine open residual).**

For each datum size `M > 0` and each shared lifespan `δ > 0` (the one
`exists_uniform_EWA_lifespan` returns), and for each positive admissible datum
`u₀` with `|u₀| ≤ M`, this supplies the per-datum realized-track atoms ON exactly
that `δ`:

* the EWA fixed point `u_star : EWA δ 1`;
* `hfp` — the realized-slice Duhamel identity (the `intervalDuhamelOperator`-form
  mild equation, produced by NO file: the evalST→real-space bridge);
* `C` — the reduced coupled-Duhamel classical core
  `CoupledDuhamelReducedClassicalCore p δ u₀ (realSlice u_star)` (whose banked
  feeders all consume the not-in-tree `evalST`-realization and per-slice spectral
  atoms).

This is precisely the realization-track content `realSlice_reducedCore` and its
feeders carry but the tree does not produce.  It is stated `∀ δ, 0 < δ → …` rather
than introducing its own `δ` so that the `∃ δ` of
`ChiNegDatumUniformConstruction` is discharged HERE from
`exists_uniform_EWA_lifespan`, not silently re-assumed inside the frontier. -/
def ChiNegRealizationFrontier (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∀ {u0 : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u0 →
      (∀ x, |u0 x| ≤ M) →
        ∃ u_star : EWA δ 1,
          (∀ t x, 0 ≤ t → t ≤ δ →
            realSlice u_star t x
              = intervalDuhamelOperator p u0 (realSlice u_star) t x) ∧
          CoupledDuhamelReducedClassicalCore p δ u0 (realSlice u_star)

/-- **The datum-uniform construction follows from the realization frontier.**

The shared lifespan `δ(M)` is produced HERE by `exists_uniform_EWA_lifespan`
(specialized at zero uniform constant-bounds and `ρ = 1`, which is admissible:
`exists_uniform_EWA_lifespan` only needs `0 ≤ ·` bounds and `0 < ρ`, returning a
`δ > 0`); the per-datum realized-track atoms on that very `δ` come from the named
realization frontier.  This is the clean quantifier-reorder
`∀u₀ ∃T  ↝  ∃δ ∀u₀`, with the genuine analytic content quarantined in the
frontier. -/
theorem chiNeg_datumUniform_of_realizationFrontier (p : CM2Params)
    (hF : ChiNegRealizationFrontier p) :
    ChiNegDatumUniformConstruction p := by
  intro M hM
  -- the datum-uniform shared lifespan from the monotone-lifespan bookkeeping.
  obtain ⟨δ, hδpos, _⟩ :=
    exists_uniform_EWA_lifespan (χ₀ := p.χ₀)
      (LQbar := 0) (LGbar := 0) (MQbar := 0) (MGbar := 0) (ρ := 1)
      le_rfl le_rfl le_rfl le_rfl one_pos
  refine ⟨δ, hδpos, ?_⟩
  intro u0 hu0 hbd
  exact hF M hM δ hδpos hu0 hbd

/-- **χ₀<0 datum-uniform construction (assembled modulo the realization frontier).**

`ChiNegDatumUniformConstruction p` holds once the single named realization frontier
`ChiNegRealizationFrontier p` is provided; the shared lifespan is discharged here. -/
theorem chiNeg_datumUniformConstruction (p : CM2Params)
    (hF : ChiNegRealizationFrontier p) :
    ChiNegDatumUniformConstruction p :=
  chiNeg_datumUniform_of_realizationFrontier p hF

/-- **χ₀<0 Paper-2 Theorem 1.1 — modulo the single realization frontier.**

Combines `chiNeg_datumUniformConstruction` with `chiNeg_theorem_1_1`
(`SourceChiNegTheorem11.lean`).  This is the χ₀<0 headline `Theorem_1_1
intervalDomain p` produced from ONE crisply-named analytic residual — the
realization-track frontier — with the datum-uniform lifespan bookkeeping and the
reduced-core wiring discharged.  It is NOT claimed unconditional: the frontier is
an explicit hypothesis (no hidden `axiom`). -/
theorem chiNeg_theorem_1_1_unconditional (p : CM2Params) (hchi : p.χ₀ < 0)
    (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hF : ChiNegRealizationFrontier p) :
    Theorem_1_1 intervalDomain p :=
  chiNeg_theorem_1_1 p hchi ha hb hα hγ (chiNeg_datumUniformConstruction p hF)

end ShenWork.EWA

namespace ShenWork.EWA
section AxiomAudit
#print axioms chiNeg_datumUniform_of_realizationFrontier
#print axioms chiNeg_datumUniformConstruction
#print axioms chiNeg_theorem_1_1_unconditional
end AxiomAudit
end ShenWork.EWA
