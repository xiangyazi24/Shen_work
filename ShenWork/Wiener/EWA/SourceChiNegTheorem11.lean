import ShenWork.Wiener.EWA.SourceReducedCore
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual

/-!
  # χ₀<0 EWA closeout of Paper 2 Theorem 1.1 on the interval domain

  This file performs the **honest reduction** of the `χ₀ < 0` headline
  `Theorem_1_1 intervalDomain p` to a SINGLE named analytic obligation:
  the datum-uniform EWA fixed-point construction.

  The committed per-datum local-existence engine `realSlice_localClassicalSolution`
  (`ShenWork.Wiener.EWA.SourceReducedCore`) takes, for one datum `u₀` on one
  horizon `δ`, the realized-track atoms
  (the EWA fixed point `u_star`, the Duhamel fixed-point identity `hfp`, and the
  reduced coupled-Duhamel classical core `C`) and yields a Paper 2 classical
  solution with initial trace.

  The headline residual `CoupledFluxClassicalLocalExistenceResidual`
  (`ShenWork.Paper2.ChiNegResidual`) instead demands ONE shared lifespan `δ(M)`
  good for every positive admissible datum with `|u₀| ≤ M`.  The genuine
  remaining content is therefore the *datum-uniform* version of those atoms:
  one `δ(M)`, and for each such datum the realized-track atoms on that very `δ`.

  We isolate exactly this content as the named Prop
  `ChiNegDatumUniformConstruction p` and prove:

  * `chiNeg_residual_of_datumUniform` — the residual follows from it;
  * `chiNeg_theorem_1_1` — the χ₀<0 headline `Theorem_1_1 intervalDomain p`
    follows MODULO this single hypothesis.

  This is **not** a discharge of the analytic frontier.  It is the honest
  reduction of the headline to one packaged atom that crisply names the
  datum-uniform EWA construction + realized-track frontier the whole χ₀<0 track
  carries.  `Theorem_1_1 intervalDomain p` is here produced for χ₀<0 ONLY under
  `ChiNegDatumUniformConstruction p`; it is not claimed unconditional.

  ## Horizon handling (honest note)
  `realSlice_localClassicalSolution` returns `∃ Tmax > 0, …` (its `Tmax` is the
  input horizon by construction, but the statement hides it behind an
  existential).  The residual body needs the solution on the *literal shared*
  `δ`, quantified BEFORE the datum.  We therefore do not call
  `realSlice_localClassicalSolution`'s existential output; we re-run the same
  underlying engine one level lower — `regularityBootstrap_of_coupledDuhamel_…`
  then `isMildSolutionData_of_fp_and_regularity` then
  `IsPaper2ClassicalSolution.of_components` — which delivers the solution on the
  exact literal `δ`.  No horizon is faked.
-/

open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomain)
open ShenWork.Paper2
  (InitialTrace PositiveInitialDatum IsPaper2ClassicalSolution Theorem_1_1)
open ShenWork.IntervalCoupledRegularityBootstrap
  (CoupledDuhamelReducedClassicalCore
    regularityBootstrap_of_coupledDuhamel_reducedClassicalCore)
open ShenWork.IntervalDomainExistence
  (intervalDuhamelOperator isMildSolutionData_of_fp_and_regularity)
open ShenWork.Paper2.ChiNegResidual
  (CoupledFluxClassicalLocalExistenceResidual
    theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual)

noncomputable section

namespace ShenWork.EWA

/-- **The single honest remaining analytic obligation for the χ₀<0 EWA track.**

For each datum size `M > 0` it supplies ONE shared lifespan `δ > 0`, and for each
positive admissible datum `u₀` with `|u₀| ≤ M` the realized-track atoms on exactly
that horizon `δ`:

* the EWA fixed point `u_star : EWA δ 1` for this datum;
* `hfp` — the Duhamel fixed-point identity for `realSlice u_star` on `δ`;
* `C` — the reduced coupled-Duhamel classical core
  `CoupledDuhamelReducedClassicalCore p δ u₀ (realSlice u_star)` (which itself
  bundles the realized-track frontier atoms: the spectral-inversion /
  eigenvalue-ℓ¹ / `DuhamelSourceTimeC1` / realized-cosine / frontier-summability
  content fed into `realSlice_reducedCore`).

These are precisely the hypotheses that `realSlice_localClassicalSolution`
consumes; packaging them datum-uniformly is the genuine open content. -/
def ChiNegDatumUniformConstruction (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
    ∀ {u0 : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u0 →
      (∀ x, |u0 x| ≤ M) →
        ∃ u_star : EWA δ 1,
          (∀ t x, 0 ≤ t → t ≤ δ →
            realSlice u_star t x
              = intervalDuhamelOperator p u0 (realSlice u_star) t x) ∧
          CoupledDuhamelReducedClassicalCore p δ u0 (realSlice u_star)

/-- The datum-uniform χ₀<0 construction discharges the coupled-flux classical
local-existence residual.

The shared `δ` is threaded as the residual's lifespan; per datum the carried
atoms `(u_star, hfp, C)` feed the regularity bootstrap and the literal-horizon
mild-solution assembly, producing the Paper 2 classical solution on exactly that
`δ`. -/
theorem chiNeg_residual_of_datumUniform (p : CM2Params)
    (hU : ChiNegDatumUniformConstruction p) :
    CoupledFluxClassicalLocalExistenceResidual p := by
  intro M hM
  obtain ⟨δ, hδ, hbody⟩ := hU M hM
  refine ⟨δ, hδ, ?_⟩
  intro u0 hu0 hbd
  obtain ⟨u_star, hfp, C⟩ := hbody hu0 hbd
  have hreg :
      ShenWork.IntervalDomainExistence.RegularityBootstrap p δ u0
        (realSlice u_star) :=
    regularityBootstrap_of_coupledDuhamel_reducedClassicalCore p C
  obtain ⟨v, hdata⟩ :=
    isMildSolutionData_of_fp_and_regularity p u0 hfp hreg
  exact ⟨realSlice u_star, v,
    IsPaper2ClassicalSolution.of_components hδ
      hdata.2.2.2.2.2.2.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2.1
      hdata.2.2.2.2.1 hdata.2.2.2.2.2.1,
    hdata.2.2.2.2.2.2.2⟩

/-- **χ₀<0 closeout.** The Paper 2 headline `Theorem_1_1 intervalDomain p` holds
for `χ₀ < 0` MODULO the single packaged hypothesis
`ChiNegDatumUniformConstruction p`.

This is the honest reduction of the headline to one named analytic atom (the
datum-uniform EWA fixed-point construction + realized-track frontier), NOT an
unconditional proof of `Theorem_1_1`. -/
theorem chiNeg_theorem_1_1 (p : CM2Params) (hchi : p.χ₀ < 0)
    (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hU : ChiNegDatumUniformConstruction p) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual
    p hchi ha hb hα hγ (chiNeg_residual_of_datumUniform p hU)

end ShenWork.EWA
