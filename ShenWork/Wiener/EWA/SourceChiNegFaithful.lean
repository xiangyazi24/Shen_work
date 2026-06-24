import ShenWork.Wiener.EWA.SourceReducedCore
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual

/-!
  # χ₀<0 EWA closeout of Paper 2 Theorem 1.1 — the FAITHFUL, non-vacuous route

  ## Why this file exists

  The previously-landed `chiNeg_theorem_1_1`
  (`ShenWork.Wiener.EWA.SourceChiNegTheorem11`) reduces the χ₀<0 headline
  `Theorem_1_1 intervalDomain p` to the named obligation
  `ChiNegDatumUniformConstruction p`.  That obligation, however, is **VACUOUS for
  χ₀<0**: per datum it carries the Duhamel fixed-point identity

      hfp : ∀ t x, 0 ≤ t → t ≤ δ →
        realSlice u_star t x = intervalDuhamelOperator p u₀ (realSlice u_star) t x

  where `intervalDuhamelOperator` is the **logistic-only** mild map
  (heat + `∫ intervalLogisticSource`, NO chemotaxis term).  But for the EWA fixed
  point, `realSlice u_star = realSlice (picardEWA u_star)` realizes the
  **chemotaxis-inclusive** map

      picardEWA = heatEWA + (-χ₀)·divDuhamelEWA(chemFluxEWA) + valDuhamelEWA(growthEWA),

  so `hfp` forces `(-χ₀)·chemFlux = 0`, i.e. (since the chemotaxis flux does not
  vanish) `χ₀ = 0` — UNSATISFIABLE for `χ₀ < 0`.  The reduction therefore proves
  `Theorem_1_1` only under a hypothesis no χ₀<0 instance can supply: vacuous.

  ## The fix

  The false `hfp` enters the old chain **only** through
  `isMildSolutionData_of_fp_and_regularity`
  (`ShenWork.IntervalDomainExistence`), which uses `hfp` purely to *carry* the
  mild-solution identity into the `IsMildSolutionData` package.  But the residual
  `CoupledFluxClassicalLocalExistenceResidual` — and hence `Theorem_1_1` — needs
  only `∃ u v, IsPaper2ClassicalSolution intervalDomain p δ u v ∧ InitialTrace …`,
  which carries **no** Duhamel-mild identity in its conclusion.

  We therefore route around `hfp` entirely:

    reduced core `C`  (carries ONLY the realization atoms, NO hfp)
      —[`regularityBootstrap_of_coupledDuhamel_reducedClassicalCore`, uncond.]→
        `RegularityBootstrap p δ u₀ (realSlice u_star)`
      —[destructure + `IsPaper2ClassicalSolution.of_components`]→
        `∃ u v, IsPaper2ClassicalSolution … ∧ InitialTrace …`.

  This is exactly the no-hfp engine `localExistence_of_regularityBootstrap`
  (`ShenWork.IntervalDomainExistence`, which only destructures
  `RegularityBootstrap` and rebuilds via `of_components` — confirmed to need NO
  logistic-Duhamel `hfp`), unrolled one level lower so the solution lands on the
  **literal** shared horizon `δ` demanded by the residual body.

  ## The satisfiable frontier

  The faithful obligation `ChiNegDatumUniformConstructionFaithful p` carries, per
  datum, ONLY:

    * the EWA fixed point `u_star : EWA δ 1`, and
    * the reduced coupled-Duhamel classical core
      `CoupledDuhamelReducedClassicalCore p δ u₀ (realSlice u_star)`.

  The reduced core bundles the **realization atoms** (the slab `realizes`, the
  eigenvalue-ℓ¹ summabilities, the `DuhamelSourceTimeC1` packages, the
  spectral-inversion / trace / resolver / heat-floor atoms).  These are genuine
  `evalST`-realization facts: `realSlice` IS the cosine synthesis of its
  coefficients — a TRUE statement about the EWA fixed point, distinct from and
  unrelated to the FALSE logistic `hfp`.  Crucially, **no `hfp` of any kind
  appears anywhere in this file or in the discharge chain.**

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/

open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomain)
open ShenWork.Paper2
  (InitialTrace PositiveInitialDatum IsPaper2ClassicalSolution Theorem_1_1)
open ShenWork.IntervalCoupledRegularityBootstrap
  (CoupledDuhamelReducedClassicalCore
    regularityBootstrap_of_coupledDuhamel_reducedClassicalCore)
open ShenWork.Paper2.ChiNegResidual
  (CoupledFluxClassicalLocalExistenceResidual
    theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual)

noncomputable section

namespace ShenWork.EWA

/-- **The single FAITHFUL remaining analytic obligation for the χ₀<0 EWA track.**

For each datum size `M > 0` it supplies ONE shared lifespan `δ > 0`, and for each
positive admissible datum `u₀` with `|u₀| ≤ M` the realized-track atoms on exactly
that horizon `δ`:

* the EWA fixed point `u_star : EWA δ 1` for this datum;
* `C` — the reduced coupled-Duhamel classical core
  `CoupledDuhamelReducedClassicalCore p δ u₀ (realSlice u_star)` (which bundles the
  realized-track frontier atoms: spectral-inversion / eigenvalue-ℓ¹ /
  `DuhamelSourceTimeC1` / realized-cosine / frontier-summability content fed into
  `realSlice_reducedCore`).

**Contrast with the vacuous `ChiNegDatumUniformConstruction`:** that one *also*
carried the Duhamel fixed-point identity `hfp`, which is the LOGISTIC-only mild
map and hence unsatisfiable for `χ₀ < 0`.  Here there is NO `hfp`: the carried
content is exactly the genuinely satisfiable `evalST`-realization frontier of the
EWA fixed point (`realSlice` realizing its cosine synthesis), nothing more. -/
def ChiNegDatumUniformConstructionFaithful (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
    ∀ {u0 : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u0 →
      (∀ x, |u0 x| ≤ M) →
        ∃ u_star : EWA δ 1,
          CoupledDuhamelReducedClassicalCore p δ u0 (realSlice u_star)

/-- The faithful (no-`hfp`) datum-uniform χ₀<0 construction discharges the
coupled-flux classical local-existence residual.

The shared `δ` is threaded as the residual's lifespan; per datum the carried
reduced core `C` feeds the **unconditional** regularity bootstrap, then the
solution is assembled directly via `IsPaper2ClassicalSolution.of_components` on
exactly that literal `δ`.  This is the no-`hfp` local-existence route
(`localExistence_of_regularityBootstrap`, unrolled to the literal horizon): the
false logistic Duhamel identity is NEVER consumed. -/
theorem chiNeg_residual_of_datumUniformFaithful (p : CM2Params)
    (hU : ChiNegDatumUniformConstructionFaithful p) :
    CoupledFluxClassicalLocalExistenceResidual p := by
  intro M hM
  obtain ⟨δ, hδ, hbody⟩ := hU M hM
  refine ⟨δ, hδ, ?_⟩
  intro u0 hu0 hbd
  obtain ⟨u_star, C⟩ := hbody hu0 hbd
  -- Unconditional reduced-core → RegularityBootstrap.  NO `hfp` here.
  have hreg :
      ShenWork.IntervalDomainExistence.RegularityBootstrap p δ u0
        (realSlice u_star) :=
    regularityBootstrap_of_coupledDuhamel_reducedClassicalCore p C
  -- Destructure the bootstrap and rebuild the classical solution directly,
  -- exactly as `localExistence_of_regularityBootstrap` does — no mild-Duhamel
  -- identity is touched.
  obtain ⟨v, hpos, hvnn, hpde_u, hpde_v, hbc, hclassreg, htrace⟩ := hreg
  exact ⟨realSlice u_star, v,
    IsPaper2ClassicalSolution.of_components hδ hclassreg hpos hvnn hpde_u
      hpde_v hbc,
    htrace⟩

/-- **χ₀<0 FAITHFUL closeout.** The Paper 2 headline `Theorem_1_1 intervalDomain p`
holds for `χ₀ < 0` MODULO the single packaged hypothesis
`ChiNegDatumUniformConstructionFaithful p`.

Unlike the previously-landed `chiNeg_theorem_1_1`, the carried obligation here is
**non-vacuous / satisfiable**: it carries only the EWA fixed point and its
reduced classical core (the `evalST`-realization frontier — `realSlice` realizing
its cosine synthesis), and NEVER the false logistic Duhamel identity `hfp`.  The
discharge routes through the unconditional `regularityBootstrap_of_coupledDuhamel_…`
and the no-`hfp` `IsPaper2ClassicalSolution.of_components` assembly.  This is the
faithful χ₀<0 reduction. -/
theorem chiNeg_theorem_1_1_faithful (p : CM2Params) (hchi : p.χ₀ < 0)
    (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hU : ChiNegDatumUniformConstructionFaithful p) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual
    p hchi ha hb hα hγ (chiNeg_residual_of_datumUniformFaithful p hU)

end ShenWork.EWA
