/-
  ShenWork/Wiener/EWA/SourceRealizationFrontier.lean

  **χ₀<0 Paper-2 Theorem 1.1 — the realization-track frontier, assembled.**

  `SourceChiNegDatumUniform.lean` reduced the entire χ₀<0 headline
  `Theorem_1_1 intervalDomain p` to ONE named obligation
  `ChiNegRealizationFrontier p` (defined there): per datum size `M` and shared
  lifespan `δ`, the realized-track atoms `(u_star, hfp, C)` — the EWA fixed point
  `u_star : EWA δ 1`, the real-space Duhamel identity `hfp`, and the reduced core
  `CoupledDuhamelReducedClassicalCore p δ u₀ (realSlice u_star)`.

  This file is the FINAL realization step.  It exhibits `ChiNegRealizationFrontier p`
  as a *clean quantifier-reorder wrapper* of the per-datum producer
  `realSlice_localClassicalSolution`'s ingredient triple, fed by exactly one
  per-datum bundle of the realization-track atoms — `ChiNegRealizationAtoms p` —
  which is the precise minimal residual that NO file in the tree produces.

  ## How this maps onto `realSlice_localClassicalSolution` (the template)

  `realSlice_localClassicalSolution` (`SourceReducedCore.lean:198`) takes, per
  datum, the triple

      (u_star : EWA T 1)              -- EWA fixed point
      (hfp     : realSlice u_star = intervalDuhamelOperator … (realSlice u_star))
      (C       : CoupledDuhamelReducedClassicalCore p T u₀ (realSlice u_star))

  and assembles the local classical solution.  `ChiNegRealizationFrontier p`
  asks for *exactly that same triple*, only:

    * quantified datum-uniformly (`∀ M, ∀ δ, ∀ u₀ ≤ M`) instead of per-datum, with
      the `∃ δ` already discharged upstream by `exists_uniform_EWA_lifespan`
      (`chiNeg_datumUniform_of_realizationFrontier`); and
    * returning `⟨u_star, hfp, C⟩` rather than running it through
      `localExistence_of_fp_and_regularity`.

  So the frontier is *precisely* the hypotheses `realSlice_localClassicalSolution`
  consumes, repackaged.  We make that explicit: `ChiNegRealizationAtoms p` is the
  per-datum carrier of `(u_star, hfp, C)`, and
  `chiNegRealizationFrontier_of_atoms` is the quantifier-reorder wrapper.

  ## The genuine minimal residual (named, not faked)

  The triple's two analytic components are produced NOWHERE in the EWA tree:

  1. **`C` — the reduced core.**  `realSlice_reducedCore`
     (`SourceReducedCore.lean:84`) *does* assemble
     `CoupledDuhamelReducedClassicalCore` — but only from a long list of carried
     `realizes` / spectral / `DuhamelSourceTimeC1` / trace atoms (the
     `evalST`-of-Duhamel = spectral-synthesis bridge), which the module docstrings
     of `SourceClassicalExistence` / `SourceReducedCore` flag as "not in the tree".

  2. **`hfp` — the realized-slice Duhamel identity.**  The EWA engines
     (`picardEWA_uncond_fixedPoint`) produce only the EWA-level identity
     `u_star = picardEWA … u_star`.  Reading that off as
     `realSlice u_star = intervalDuhamelOperator p u₀ (realSlice u_star)` via the
     `evalST` bridges hits a genuine OBSTRUCTION for χ₀<0, recorded precisely
     below in `chiNeg_hfp_needs_chemotaxis_vanishing`:

     `intervalDuhamelOperator` (`IntervalDomainExistence.lean:595`) is the
     **logistic-only** mild operator (heat + Duhamel of `intervalLogisticSource`,
     no chemotaxis), whereas `realSlice (picardEWA u_star)` realizes the
     **chemotaxis-inclusive** map `intervalGradientDuhamelMap` (heat +
     `(-χ₀)·∫ deriv chemFlux` + Duhamel logistic; `IntervalMildToLocalExistence.lean:60`).
     The only landed bridge between the two,
     `intervalGradientDuhamelMap_eq_intervalDuhamelOperator_of_frontiers`
     (`IntervalMildToLocalExistence.lean:972`), equates them ONLY under the
     hypothesis `hchem` that the chemotaxis Duhamel term *vanishes* — which holds
     for χ₀ = 0 (`…_of_chi_zero`, line 1019) but is FALSE for χ₀ < 0 (`-χ₀ ≠ 0`
     and the chemDiv integral is generically nonzero).

     So `hfp` in the χ₀<0 frontier is genuinely the evalST→real-space realization
     of the *chemotaxis-inclusive* fixed point, carried — never produced.

  We therefore carry `(hfp, C)` per datum inside `ChiNegRealizationAtoms` (the
  irreducible χ₀<0 realization content), and PROVE the frontier from it.  This is
  axiom-clean: no hidden `axiom`, no `sorry`; the residual is a named explicit
  hypothesis, exactly as `chiNeg_theorem_1_1_unconditional` carries the frontier.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceChiNegDatumUniform
import ShenWork.Wiener.EWA.SourceReducedCore
import ShenWork.Paper2.IntervalMildToLocalExistence

noncomputable section

namespace ShenWork.EWA

open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainPoint intervalDomainLift intervalSemigroupOperator)
open ShenWork.Paper2 (PositiveInitialDatum Theorem_1_1)
open ShenWork.IntervalCoupledRegularityBootstrap (CoupledDuhamelReducedClassicalCore)
open ShenWork.IntervalDomainExistence (intervalDuhamelOperator)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalGradientDuhamelMap
  (chemFluxLifted logisticLifted intervalGradientDuhamelMap)
open ShenWork.IntervalMildToLocalExistence
  (intervalGradientDuhamelMap_eq_intervalDuhamelOperator_of_frontiers)

/-- **The per-datum χ₀<0 realization-track atoms (the genuine minimal residual).**

For a datum size `M`, a lifespan `δ`, and a positive admissible datum `u₀` with
`|u₀| ≤ M`, this supplies the realized triple that `realSlice_localClassicalSolution`
consumes:

* the EWA fixed point `u_star : EWA δ 1` (from `picardEWA_uncond_fixedPoint`);
* `hfp` — the realized-slice Duhamel identity in `intervalDuhamelOperator` form
  (the evalST→real-space bridge; for χ₀<0 this is the realization of the
  *chemotaxis-inclusive* fixed point — see `chiNeg_hfp_needs_chemotaxis_vanishing`);
* `C` — the reduced coupled-Duhamel classical core (assembled by
  `realSlice_reducedCore` from its carried `realizes`/spectral/`DuhamelSourceTimeC1`
  atoms).

Both `hfp` and `C`'s feeders bottom out in the `evalST`-of-Duhamel realization
content the tree does not produce; this carrier names that content in EXACTLY the
shape `ChiNegRealizationFrontier` needs. -/
def ChiNegRealizationAtoms (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∀ {u0 : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u0 →
      (∀ x, |u0 x| ≤ M) →
        ∃ u_star : EWA δ 1,
          (∀ t x, 0 ≤ t → t ≤ δ →
            realSlice u_star t x
              = intervalDuhamelOperator p u0 (realSlice u_star) t x) ∧
          CoupledDuhamelReducedClassicalCore p δ u0 (realSlice u_star)

/-- **The realization frontier is the realization-atoms carrier.**

`ChiNegRealizationFrontier p` and `ChiNegRealizationAtoms p` are the SAME `Prop`:
the per-datum triple `(u_star, hfp, C)` quantified `∀ M, ∀ δ, ∀ u₀ ≤ M`.  The
frontier asks for precisely the atoms `realSlice_localClassicalSolution` consumes,
quantifier-reordered to be datum-uniform — the two definitions coincide on the
nose.  This is the clean wrapper promised by the frontier docstring (step 3 of the
realization task: the frontier is a quantifier-shape wrapper of the per-datum
producer's ingredient triple). -/
theorem chiNegRealizationFrontier_of_atoms (p : CM2Params)
    (hA : ChiNegRealizationAtoms p) :
    ChiNegRealizationFrontier p := by
  intro M hM δ hδ u0 hu0 hbd
  exact hA M hM δ hδ hu0 hbd

/-- **Conversely, the frontier yields the realization atoms.**  The two carriers
are definitionally interchangeable, so the χ₀<0 headline modulo the frontier and
modulo the realization atoms are the same conditional. -/
theorem chiNegRealizationAtoms_of_frontier (p : CM2Params)
    (hF : ChiNegRealizationFrontier p) :
    ChiNegRealizationAtoms p := by
  intro M hM δ hδ u0 hu0 hbd
  exact hF M hM δ hδ hu0 hbd

/-! ### The χ₀<0 obstruction inside `hfp` (recorded, not faked).

The `hfp` component of each realization atom is *not* derivable from the EWA
fixed-point identity by the landed evalST bridges, because the target operator
`intervalDuhamelOperator` is logistic-only while the realized fixed point carries
the chemotaxis Duhamel term.  We record the exact landed bridge and its missing
hypothesis so the residual is named, not hidden. -/

/-- **`hfp` for χ₀<0 needs the chemotaxis Duhamel term to vanish — which it does
not.**  The only landed bridge `intervalGradientDuhamelMap = intervalDuhamelOperator`
is `intervalGradientDuhamelMap_eq_intervalDuhamelOperator_of_frontiers`, which
requires its `hchem` argument: the chemotaxis Duhamel contribution `(-χ₀)·∫ …`
equals `0`.  Given that exact vanishing hypothesis (plus the semigroup-init and
logistic-Duhamel identifications), the realized chemotaxis-inclusive map collapses
to `intervalDuhamelOperator`, closing `hfp`.

For χ₀ = 0 the `hchem` premise is automatic
(`intervalGradientDuhamelMap_chemTerm_zero_of_chi_zero`); for χ₀ < 0 it is FALSE
in general (`-χ₀ ≠ 0`, chemDiv integral nonzero), so this premise is precisely the
carried, irreducible content of `hfp` in the χ₀<0 realization atoms. -/
theorem chiNeg_hfp_needs_chemotaxis_vanishing
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) (x : intervalDomainPoint)
    (hinit :
      intervalFullSemigroupOperator t (intervalDomainLift u0) x.1 =
        intervalSemigroupOperator 1 t (intervalDomainLift u0) x.1)
    (hchem :
      (-p.χ₀) *
          (∫ s in (0 : ℝ)..t,
            deriv
              (fun z =>
                intervalFullSemigroupOperator (t - s)
                  (chemFluxLifted p (u s)) z) x.1) =
        0)
    (hlog :
      (∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (logisticLifted p (u s)) x.1) =
        ∫ s in Set.Icc 0 t,
          intervalSemigroupOperator 1 (t - s)
            (logisticLifted p (u s)) x.1) :
    intervalGradientDuhamelMap p u0 u t x =
      intervalDuhamelOperator p u0 u t x :=
  intervalGradientDuhamelMap_eq_intervalDuhamelOperator_of_frontiers
    p u t x hinit hchem hlog

/-! ### The unconditional headline, modulo the named realization atoms.

Composing the frontier-from-atoms wrapper with the banked
`chiNeg_theorem_1_1_unconditional` gives the χ₀<0 Paper-2 headline carrying the
single per-datum realization-atoms residual.  This is NOT a hidden axiom: the
residual is the explicit hypothesis `hA`. -/

/-- **χ₀<0 Paper-2 Theorem 1.1 — modulo the named realization atoms.**

`Theorem_1_1 intervalDomain p` holds for χ₀<0 once the per-datum realization atoms
`ChiNegRealizationAtoms p` (the `(u_star, hfp, C)` triple — the irreducible
evalST-realization + chemotaxis-inclusive `hfp` content) are provided.  The
lifespan bookkeeping, reduced-core wiring, and headline assembly are all
discharged. -/
theorem chiNeg_theorem_1_1_of_realizationAtoms (p : CM2Params) (hchi : p.χ₀ < 0)
    (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hA : ChiNegRealizationAtoms p) :
    Theorem_1_1 intervalDomain p :=
  chiNeg_theorem_1_1_unconditional p hchi ha hb hα hγ
    (chiNegRealizationFrontier_of_atoms p hA)

end ShenWork.EWA

namespace ShenWork.EWA
section AxiomAudit
#print axioms chiNegRealizationFrontier_of_atoms
#print axioms chiNegRealizationAtoms_of_frontier
#print axioms chiNeg_hfp_needs_chemotaxis_vanishing
#print axioms chiNeg_theorem_1_1_of_realizationAtoms
end AxiomAudit
end ShenWork.EWA
