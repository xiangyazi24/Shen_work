# Q1002 / cron1

Repo inspected: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target drop file:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## What I treated `cron1` as

The prompt body only names `cron1`, without a separate mathematical theorem, Lean symbol, or file path. I therefore treated this as a cron-style status/audit drop for the repo’s existing `cron1` thread rather than as a request to edit Lean code.

The strongest `cron1`-relevant facts visible in the current branch are about faithfulness and over-strong frontier hypotheses in the Paper 2/Paper 3/Paper 1 orchestration notes.

## Repository facts checked

### 1. `hSupNormDeriv` is still an over-strong / false predicate if read literally

`ShenWork/Paper2/IntervalHsupNormProof.lean` contains the repo’s own integrity note: the unconditional predicate

```text
IntervalDomainSupNormDerivativeNonposOn D.u (Set.Ioo 0 D.T)
```

claims non-positive derivative of the sup norm on the whole interior time interval. The note explains why this is false for flat positive data below carrying capacity: with `χ₀ = 0`, the solution is spatially constant and follows the logistic ODE

```text
u'(t) = u(t) * (a - b * u(t)^α),
```

which is positive when `0 < u < (a / b)^(1 / α)`. So the sup norm initially increases, contradicting unconditional derivative non-positivity.

The same file correctly records the faithful replacement: use conditional above-capacity decay, and use a separate pure-heat non-increase fact for the `a = 0 ∧ b = 0` case. The constructor `nonposOn_of_locally_eq` is a reusable honest helper, not a proof of the false unconditional field.

### 2. Downstream code currently discards `hSupNormDeriv` in the local bridge

`ShenWork/Paper2/IntervalDomainEndToEnd.lean` destructures the per-datum frontier as

```text
obtain ⟨D, S, hTimeNhd, hResolverData, _hSupNormDeriv,
  hVpos, hInitialApproach, hpde_u⟩ := hPerDatum u₀ hu₀
```

and then calls `gradientMildClassicalFrontierCoreData_of_perDatum` without using `_hSupNormDeriv`.

So there are two distinct facts:

1. As a proposition, the field is still too strong / false for admissible small logistic data.
2. In this bridge, it is not semantically used after destructuring.

That means the faithful cleanup remains: remove the field from `PerDatumSpectralFrontier` or replace it by the two true consumer-specific statements. Merely leaving it as an unused hypothesis still makes the existential per-datum frontier harder or impossible to inhabit.

### 3. The current global campaign notes locate the χ₀ < 0 Paper 2 core at direct parabolic regularity, not at a bookkeeping leaf

`BANK_CHECKLIST.md` records that earlier `cron1` / `cron1c` work found several global or closed-at-zero packages to be over-strong for the weak mild limit. The corrected object is positive-time/windowed regularity plus integrable singular behavior near zero.

Later notes sharpen the status further: the χ₀ < 0 route is reduced to a direct parabolic C² bootstrap for the gradient fixed point, breaking the circular route that tries to obtain a source package from regularity that itself depends on such a package.

The most honest summary is:

```text
Gradient mild fixed point + L∞/positive-time smoothing
  -> direct H^σ / C² bootstrap for u and the chemotaxis flux
  -> IterateSourceTimeData / source regularity window
  -> end gate for χ₀ < 0 classical solution
```

The danger to avoid is using `ResolverHasSpectralAgreement` or any source-C¹ package as an input to prove the same source-C¹ regularity. That is the circularity the notes explicitly identify.

## Practical recommendation

For the next Lean edits, I would not spend effort proving the existing all-time or unconditional sup-norm derivative predicate. It is mathematically false in the logistic-below-capacity regime.

The safe cleanup order is:

1. **Remove or refactor `hSupNormDeriv` from `PerDatumSpectralFrontier`.** Since `hMildLocal_of_perDatum` already discards it, this should be a low-risk interface simplification. It removes an unsatisfiable inhabitance burden.
2. **Introduce the true max-principle outputs where actually consumed.** Use conditional above-capacity decay for the logistic comparison, and pure-heat non-increase for the zero-reaction case.
3. **Keep the χ₀ < 0 regularity route positive-time/windowed.** Any global-in-time or closed-at-zero source-C¹ statement should be treated as suspect unless it explicitly accounts for the near-zero singularity.
4. **For the real χ₀ < 0 core, focus on the direct heat-kernel/B-form smoothing bootstrap.** The target is to produce the needed positive-time C² / time-regularity data from the fixed point without passing through the circular source-package route.

## Minimal Lean-facing sketch for the cleanup

This is not a full patch, but it shows the intended direction. The exact tuple destructuring must be adjusted wherever `PerDatumSpectralFrontier` is unpacked.

```lean
import ShenWork.Paper2.IntervalDomainThm11Assembly
import ShenWork.Paper2.IntervalRegularityFrontierWiring
import ShenWork.Paper2.IntervalDomainRestartExtension
import ShenWork.Paper2.IntervalMildPicardRegularity

open ShenWork.IntervalDomain
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardRegularity
open ShenWork.IntervalMildToClassical
open ShenWork.IntervalMildToLocalExistence
open ShenWork.IntervalMildRegularityBootstrap
  (HasRestartCosineRepresentations)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData)
open ShenWork.Paper2
open ShenWork.Paper2.RegularityFrontierWiring
open ShenWork.Paper2.RestartExtension
open ShenWork.Paper2.Theorem11Assembly

noncomputable section

namespace ShenWork.Paper2.EndToEnd

/-- Proposed faithful per-datum frontier shape: remove the globally false and
currently discarded `IntervalDomainSupNormDerivativeNonposOn` field. The actual
maximum-principle facts should live at their real consumers, with the correct
conditional hypotheses. -/
def PerDatumSpectralFrontierNoFalseSupNorm
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
  HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
  HasResolverDirectSpectralData D.T
    (mildChemicalConcentration p D.u) p ∧
  (∀ t, 0 < t → t < D.T → ∀ x : intervalDomainPoint,
    0 < mildChemicalConcentration p D.u t x) ∧
  (∀ ε, 0 < ε →
    ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x : intervalDomainPoint,
        |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε) ∧
  (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
    intervalDomain.timeDeriv D.u t x =
      intervalDomain.laplacian (D.u t) x
        - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
            (mildChemicalConcentration p D.u t) x
        + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

end ShenWork.Paper2.EndToEnd
```

## Bottom line

`cron1`’s actionable conclusion is faithfulness-oriented: do not try to prove the global/unconditional sup-norm derivative field. It is false as stated. Since the current bridge discards it, the best next move is to delete or refactor that field and keep the genuine maximum-principle estimates at their actual consumers. The remaining χ₀ < 0 difficulty is not this discarded field; it is the direct positive-time parabolic C²/bootstrap regularity of the gradient fixed point, avoiding the documented source-package circularity.