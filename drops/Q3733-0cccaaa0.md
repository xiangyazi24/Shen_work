ANSWER Q3733 0cccaaa0

# Q3733 audit: chi-nonpositive local-existence residual path

## Bottom line

Yes: `ShenWork.Paper2.ChiNegResidual.CoupledFluxClassicalLocalExistenceResidual p` is already producible from smaller landed assumptions. There is not yet an unconditional negative-`chi` proof, and the next real analytic target should not be `CoupledFluxResolverAnalyticData p`; the repo already has a narrower resolver-facing interface, `CoupledFluxResolverReducedCoreData p`.

The current best split is:

* **narrowest hfp-free EWA producer of the primitive weak local-existence residual:**
  `ShenWork.EWA.chiNeg_residual_of_datumUniformFaithful` in
  `ShenWork/Wiener/EWA/SourceChiNegFaithful.lean:125-145`, consuming
  `ShenWork.EWA.ChiNegDatumUniformConstructionFaithful p` from
  `SourceChiNegFaithful.lean:108-114`.
* **narrowest resolver/PDE producer of the primitive weak local-existence residual:**
  `ShenWork.Paper2.ChiNegResidual.coupledFluxClassicalLocalExistenceResidual_of_reducedCoreData`
  in `ShenWork/Paper2/IntervalDomainThm11ChiNegReducedCoreData.lean:67-72`, consuming
  `ShenWork.Paper2.ChiNegResidual.CoupledFluxResolverReducedCoreData p` from
  `IntervalDomainThm11ChiNegReducedCoreData.lean:28-44` and `hα : 1 ≤ p.α`.

The existing public chi-nonpositive aliases in
`ShenWork/Paper2/IntervalDomainChiNonposHeadline.lean` currently expose the primitive local residual,
`ChiNegStrongFaithfulRealizationFrontier`, and `ChiNegDatumUniformCore`, but not the narrower
`CoupledFluxResolverReducedCoreData` route.

## 1. Is `CoupledFluxClassicalLocalExistenceResidual p` already producible?

Yes.

The primitive residual itself is defined in
`ShenWork/Paper2/IntervalDomainThm11ChiNegResidual.lean:32-39`:

```lean
def CoupledFluxClassicalLocalExistenceResidual (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M → ∃ delta : ℝ, 0 < delta ∧
    ∀ {u0 : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u0 →
      (∀ x, |u0 x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p delta u v ∧
          InitialTrace intervalDomain u0 u
```

There are three relevant producers/wrappers, with different meanings.

### A. Direct hfp-free EWA producer

`ShenWork/Wiener/EWA/SourceChiNegFaithful.lean` is the clean no-`hfp` path. It defines
`ChiNegDatumUniformConstructionFaithful p` as a uniform weak-`PositiveInitialDatum` construction carrying only
`∃ u_star : EWA δ 1, CoupledDuhamelReducedClassicalCore p δ u0 (realSlice u_star)`
(`SourceChiNegFaithful.lean:108-114`). Then:

```lean
theorem chiNeg_residual_of_datumUniformFaithful (p : CM2Params)
    (hU : ChiNegDatumUniformConstructionFaithful p) :
    CoupledFluxClassicalLocalExistenceResidual p
```

is proved at `SourceChiNegFaithful.lean:125-145`. Its proof uses
`regularityBootstrap_of_coupledDuhamel_reducedClassicalCore` and then destructures the resulting
`RegularityBootstrap`, rebuilding the exact-horizon classical solution with
`IsPaper2ClassicalSolution.of_components`. This is the narrowest landed direct theorem whose conclusion is the primitive residual and which avoids the known false `hfp` route.

A still more external frontier is available in `ShenWork/Wiener/EWA/ChiNegFrontierAssembly.lean`:

```lean
def ChiNegFaithfulRealizationFrontier (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∀ {u0 : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u0 →
      (∀ x, |u0 x| ≤ M) →
        ∃ u_star : EWA δ 1,
          CoupledDuhamelReducedClassicalCore p δ u0 (realSlice u_star)
```

See `ChiNegFrontierAssembly.lean:85-91`. It feeds the faithful datum-uniform construction through
`chiNeg_datumUniformFaithful_of_frontier` (`ChiNegFrontierAssembly.lean:106-117`), and then the above residual producer can be composed. That composition is useful as route documentation, but the narrowest direct residual producer is still
`chiNeg_residual_of_datumUniformFaithful`.

### B. Direct resolver/PDE producer

`ShenWork/Paper2/IntervalDomainThm11ChiNegReducedCoreData.lean` gives the narrowed resolver-facing interface:

```lean
def CoupledFluxResolverReducedCoreData (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M →
    ∃ Mball : ℝ, 0 < Mball ∧ M ≤ Mball ∧
      ∀ L : ℝ, 0 < L →
        ∃ T A K : ℝ, 0 < T ∧ 0 < A ∧ 0 ≤ K ∧ A * T < 1 ∧
          |p.χ₀| * K + L ≤ A ∧
            ∀ {u0 : intervalDomain.Point → ℝ},
              PositiveInitialDatum intervalDomain u0 →
              (∀ x, |u0 x| ≤ M) →
                IntervalCoupledResolverBallEstimates p
                  (intervalNeumannResolverR p) u0 T Mball K ∧
                ∀ u : ℝ → intervalDomain.Point → ℝ,
                  intervalTrajectoryBoundedOn T Mball u →
                  (∀ t x, 0 ≤ t → t ≤ T →
                    u t x = intervalCoupledDuhamelOperator p
                      (intervalNeumannResolverR p) u0 u t x) →
                    CoupledDuhamelReducedClassicalCore p T u0 u
```

It is consumed by:

```lean
theorem coupledFluxClassicalLocalExistenceResidual_of_reducedCoreData
    (p : CM2Params) (hα : 1 ≤ p.α)
    (H : CoupledFluxResolverReducedCoreData p) :
    CoupledFluxClassicalLocalExistenceResidual p
```

at `IntervalDomainThm11ChiNegReducedCoreData.lean:67-72`.

This is strictly narrower than `CoupledFluxResolverAnalyticData p`, because it asks the regularization leg to produce only
`CoupledDuhamelReducedClassicalCore p T u0 u`; the already-landed theorem
`regularityBootstrap_of_coupledDuhamel_reducedClassicalCore` upgrades that core to `RegularityBootstrap`. The bridge is
`coupledFluxResolverAnalyticData_of_reducedCoreData` at
`IntervalDomainThm11ChiNegReducedCoreData.lean:48-63`.

### C. B1 local residual is not smaller

`ShenWork/Paper2/IntervalDomainThm11ChiNegativeResidualB1.lean` defines
`ChiNegativeNonminimalCoupledLocalExistenceResidual p` (`:19-28`), but its sole field is the same local-existence factory as the primitive residual. The theorem

```lean
theorem coupledFluxResidual_of_coupledLocalResidual
    {p : CM2Params}
    (H : ChiNegativeNonminimalCoupledLocalExistenceResidual p) :
    ChiNegResidual.CoupledFluxClassicalLocalExistenceResidual p :=
  H.localExistence
```

at `IntervalDomainThm11ChiNegativeResidualB1.lean:32-36` is just a projection. It is useful naming/wiring, not a narrower analytic producer.

## 2. Is `CoupledFluxResolverAnalyticData p` the correct next residual?

No. It is already superseded by `CoupledFluxResolverReducedCoreData p` as the narrower resolver-facing residual.

`CoupledFluxResolverAnalyticData p` is defined in
`IntervalDomainThm11ChiNegResidual.lean:108-125`. It asks, per datum, for:

1. `IntervalCoupledResolverBallEstimates p (intervalNeumannResolverR p) u0 T Mball K`, and
2. a regularization bridge from every coupled-Duhamel fixed point to `RegularityBootstrap p T u0 u`.

The reduced-core residual asks for the same resolver-ball estimate, but replaces the second field by the smaller conclusion
`CoupledDuhamelReducedClassicalCore p T u0 u`; see
`IntervalDomainThm11ChiNegReducedCoreData.lean:28-44`.

The reason this is faithful is that `CoupledDuhamelReducedClassicalCore` has exactly four fields:

```lean
structure CoupledDuhamelReducedClassicalCore
    (p : CM2Params) (T : ℝ) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  u_pos : ∀ t x, 0 < t → t < T → 0 < u t x
  pde_u : ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
    intervalDomain.timeDeriv u t x =
      intervalDomain.laplacian (u t) x
        - p.χ₀ * intervalDomain.chemotaxisDiv p (u t)
            (coupledChemicalConcentration p u t) x
        + u t x * (p.a - p.b * (u t x) ^ p.α)
  classicalRegularity :
    intervalDomainClassicalRegularity T u (coupledChemicalConcentration p u)
  initialTrace : InitialTrace intervalDomain u₀ u
```

This is from `ShenWork/PDE/IntervalCoupledClassicalCoreDischarge.lean:27-39`. The already-proved discharge
`regularityBootstrap_of_coupledDuhamel_reducedClassicalCore` is at
`IntervalCoupledClassicalCoreDischarge.lean:128-134`.

Therefore the next real analytic target should be a producer for
`CoupledFluxResolverReducedCoreData p`, not for `CoupledFluxResolverAnalyticData p`.

## 3. Search results around the requested files

### `IntervalDomainThm11ChiNegResidual.lean`

This file supplies the primitive residual and the older analytic-data route:

* `CoupledFluxClassicalLocalExistenceResidual`, lines `32-39`.
* `exactLocalClassicalSolution_of_coupledDuhamel_resolver_estimates`, lines `47-98`.
* `CoupledFluxResolverAnalyticData`, lines `108-125`.
* `coupledFluxClassicalLocalExistenceResidual_of_resolverAnalyticData`, lines `131-147`.
* `theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual`, lines `201-208`.

### `IntervalDomainThm11ChiNegReducedCoreData.lean`

This is the key narrower resolver interface:

* `CoupledFluxResolverReducedCoreData`, lines `28-44`.
* `coupledFluxResolverAnalyticData_of_reducedCoreData`, lines `48-63`.
* `coupledFluxClassicalLocalExistenceResidual_of_reducedCoreData`, lines `67-72`.
* `theorem_1_1_intervalDomain_chiNeg_of_reducedCoreData`, lines `75-83`.

### `IntervalDomainThm11ChiNegativeResidualB1.lean`

This is a naming/wiring layer, not a narrower analytic route:

* `ChiNegativeNonminimalCoupledLocalExistenceResidual`, lines `19-28`.
* `coupledFluxResidual_of_coupledLocalResidual`, lines `32-36`.
* `Theorem_1_1_intervalDomain_chiNegative_nonminimal_of_coupledLocalResidual`, lines `56-63`.

### `SourceChiNegFaithful.lean`

This is the important no-`hfp` EWA residual route:

* The file explicitly records why the old `hfp` route is vacuous for `χ₀ < 0`: lines `11-29`.
* `ChiNegDatumUniformConstructionFaithful`, lines `108-114`.
* `chiNeg_residual_of_datumUniformFaithful`, lines `125-145`.
* `chiNeg_theorem_1_1_faithful`, lines `158-163`.

### `SourceChiNegTheorem11.lean`

Do not use this as the next route. Its `ChiNegDatumUniformConstruction` carries the logistic-only Duhamel identity
`hfp` at lines `84-93`, and `chiNeg_residual_of_datumUniform` consumes that `hfp` at lines `102-120`. This is the known dead/vacuous route identified and repaired by `SourceChiNegFaithful.lean`.

### `ChiNegFrontierAssembly.lean` and `ChiNegStrongFrontierAssembly.lean`

`ChiNegFrontierAssembly.lean` gives the weak-datum faithful frontier:

* `ChiNegFaithfulRealizationFrontier`, lines `85-91`.
* `chiNeg_datumUniformFaithful_of_frontier`, lines `106-117`.
* `chiNeg_theorem_1_1_of_faithfulFrontier`, lines `144-149`.

`ChiNegStrongFrontierAssembly.lean` gives the PPID headline-facing frontier:

* `ChiNegStrongFaithfulRealizationFrontier`, lines `33-39`.
* `chiNeg_strongDatumUniform_of_faithfulFrontier`, lines `43-53`.
* `chiNeg_theorem_1_1_of_strongFaithfulFrontier`, lines `57-64`.

The strong frontier is already exposed by the chi-nonpositive headline alias, but it is PPID-typed and should not be confused with a producer for the primitive weak `PositiveInitialDatum` residual.

### Resolver/regularity producer files

`ShenWork/Paper2/IntervalCoupledResolverBallEstimatesProducer.lean` has a structural resolver-ball assembler:

```lean
theorem produce :
  ... → IntervalCoupledResolverBallEstimates p R u₀ T M K
```

at lines `56-118`. It assembles `hmap`, `hchem`, `hint`, and `hlift_int` from supplied source bounds, chemDiv Lipschitz, and measurability data. This is useful for the first conjunct of `CoupledFluxResolverReducedCoreData`, but it does not produce the fixed-point-to-reduced-core field.

`ShenWork/PDE/IntervalCoupledC1ResolverBallBridge.lean` is a more concrete C¹-snapshot resolver-ball bridge. It proves:

```lean
theorem intervalCoupledResolverBallEstimates_of_C1Snapshot :
  ... → IntervalCoupledResolverBallEstimates p R u₀ T M
        (chemKDConst p M G_u G H L_V L_R L_H L_u)
```

at lines `203-325` of the file as fetched around `IntervalCoupledC1ResolverBallBridge.lean:20-142` in the relevant chunk. It still assumes the honest C¹ snapshot, resolver Lipschitz/sup legs, the gradient wiring, closure to boundary/time, source sup bounds, and measurability.

`ShenWork/PDE/IntervalCoupledClassicalBallEstimates.lean` documents a remaining analytic obstruction: flux-value Lipschitz is proved, but conversion to the chemotaxis-divergence form requires second-derivative/product-rule level control; see its module comments around lines `40-60`.

`ShenWork/Paper2/IntervalChemFluxHolderSourceDecay.lean` contains useful Holder/source package assemblers, but again they are not full local-existence residual producers. For example,
`resolverGradReal_uniform_holder_Icc_of_sourceDecay_grad2Bound` consumes source decay plus a uniform `resolverGrad2Real` bound and explicitly documents that it does not produce that uniform grad2 bound (`IntervalChemFluxHolderSourceDecay.lean:10-25` in the final chunk).

## 4. Concrete next commit plan

### If the next commit is route exposure only

Add one more wrapper exposing the narrower resolver reduced-core path through the chi-nonpositive headline. This is an alias/wrapper commit only; it does not close new analytic fields.

New file:

`ShenWork/Paper2/IntervalDomainTheorem11ChiNonposReducedCoreDataSplit.lean`

```lean
/-
  ShenWork/Paper2/IntervalDomainTheorem11ChiNonposReducedCoreDataSplit.lean

  Chi-nonpositive split whose strict-negative branch carries the narrower
  resolver reduced-core data.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainTheorem11ChiNonposLocalExistenceSplit
import ShenWork.Paper2.IntervalDomainThm11ChiNegReducedCoreData

open ShenWork.IntervalDomain (intervalDomain)

noncomputable section

namespace ShenWork.Paper2

/-- General chi-nonpositive split with the narrower resolver reduced-core data
restricted to the strict-negative branch.  This is only route exposure: the
negative branch still carries `CoupledFluxResolverReducedCoreData p`. -/
theorem intervalDomain_theorem_1_1_chiNonpos_of_reducedCoreData_negative
    (p : CM2Params) (hchi : p.χ₀ ≤ 0)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (halpha : 1 ≤ p.α) (hgamma : 1 ≤ p.γ)
    (hnegReduced :
      p.χ₀ < 0 → ChiNegResidual.CoupledFluxResolverReducedCoreData p) :
    Theorem_1_1 intervalDomain p :=
  intervalDomain_theorem_1_1_chiNonpos_of_coupledFluxLocalExistence_negative
    p hchi ha hb halpha hgamma
    (fun hneg =>
      ChiNegResidual.coupledFluxClassicalLocalExistenceResidual_of_reducedCoreData
        p halpha (hnegReduced hneg))

#print axioms intervalDomain_theorem_1_1_chiNonpos_of_reducedCoreData_negative

end ShenWork.Paper2
```

Then modify `ShenWork/Paper2/IntervalDomainChiNonposHeadline.lean` to import the new file and add a public alias:

```lean
import ShenWork.Paper2.IntervalDomainTheorem11ChiNonposReducedCoreDataSplit

/-- Public PDE-level chi-nonpositive interval-domain theorem in the strict
logistic regime.  The zero branch is unconditional; the strict-negative branch
carries the narrower resolver reduced-core data. -/
theorem paper2_theorem_1_1_intervalDomain_chiNonpos_strictLogistic_of_reducedCoreData
    (p : CM2Params) (hchi : p.χ₀ ≤ 0)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (halpha : 1 ≤ p.α) (hgamma : 1 ≤ p.γ)
    (hnegReduced :
      p.χ₀ < 0 → ChiNegResidual.CoupledFluxResolverReducedCoreData p) :
    Theorem_1_1 intervalDomain p :=
  intervalDomain_theorem_1_1_chiNonpos_of_reducedCoreData_negative
    p hchi ha hb halpha hgamma hnegReduced
```

Acceptance checks for this wrapper commit:

```bash
lake env lean ShenWork/Paper2/IntervalDomainTheorem11ChiNonposReducedCoreDataSplit.lean
lake env lean ShenWork/Paper2/IntervalDomainChiNonposHeadline.lean
grep -R "intervalDuhamelOperator" ShenWork/Paper2/IntervalDomainTheorem11ChiNonposReducedCoreDataSplit.lean
grep -R "ChiNegDatumUniformConstruction " ShenWork/Paper2/IntervalDomainTheorem11ChiNonposReducedCoreDataSplit.lean
```

The two grep checks should be empty. The point is to avoid the old logistic-only `hfp` path.

### If the next commit must be genuine analytic progress

Then another alias/wrapper is not enough. The next real target should be a producer for
`CoupledFluxResolverReducedCoreData p`, or a clearly named subrecord feeding it.

The smallest honest new interface would split `CoupledFluxResolverReducedCoreData` into its two actual analytic conjuncts:

1. **resolver-ball estimates** on the concrete resolver:
   `IntervalCoupledResolverBallEstimates p (intervalNeumannResolverR p) u0 T Mball K`;
2. **fixed-point-to-reduced-core regularization**:
   every bounded coupled-Duhamel fixed point produces
   `CoupledDuhamelReducedClassicalCore p T u0 u`.

A faithful split record could be:

```lean
import ShenWork.Paper2.IntervalDomainThm11ChiNegReducedCoreData

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.PDE
open ShenWork.IntervalCoupledRegularityBootstrap

noncomputable section

namespace ShenWork.Paper2.ChiNegResidual

/-- Smaller analytic fields whose combination is exactly the reduced-core
resolver data needed for the weak local-existence residual. -/
structure CoupledFluxReducedCoreLocalAnalyticFields (p : CM2Params) : Prop where
  data : ∀ M : ℝ, 0 < M →
    ∃ Mball : ℝ, 0 < Mball ∧ M ≤ Mball ∧
      ∀ L : ℝ, 0 < L →
        ∃ T A K : ℝ, 0 < T ∧ 0 < A ∧ 0 ≤ K ∧ A * T < 1 ∧
          |p.χ₀| * K + L ≤ A ∧
            ∀ {u0 : intervalDomain.Point → ℝ},
              PositiveInitialDatum intervalDomain u0 →
              (∀ x, |u0 x| ≤ M) →
                IntervalCoupledResolverBallEstimates p
                  (intervalNeumannResolverR p) u0 T Mball K ∧
                ∀ u : ℝ → intervalDomain.Point → ℝ,
                  intervalTrajectoryBoundedOn T Mball u →
                  (∀ t x, 0 ≤ t → t ≤ T →
                    u t x = intervalCoupledDuhamelOperator p
                      (intervalNeumannResolverR p) u0 u t x) →
                    CoupledDuhamelReducedClassicalCore p T u0 u

theorem coupledFluxResolverReducedCoreData_of_localAnalyticFields
    (p : CM2Params)
    (H : CoupledFluxReducedCoreLocalAnalyticFields p) :
    CoupledFluxResolverReducedCoreData p :=
  H.data

end ShenWork.Paper2.ChiNegResidual
```

However, this split as written is definitionally the same shape with a record wrapper, so it is only useful if the next commit immediately replaces one of the fields by a landed producer. The real analytic work is to fill the resolver-ball conjunct from `IntervalCoupledResolverBallEstimatesProducer.produce` or
`IntervalCoupledC1ResolverBallBridge.intervalCoupledResolverBallEstimates_of_C1Snapshot`, and separately fill the reduced-core field.

The remaining genuine analytic fields are exactly:

* the constant/horizon chooser: `Mball`, `T`, `A`, `K` with `A*T<1` and `|p.χ₀|*K+L≤A`;
* the concrete resolver-ball estimates: self-map, chemDiv Lipschitz, Duhamel-integrand integrability, lifted-source integrability;
* the fixed-point-to-core bridge producing `CoupledDuhamelReducedClassicalCore`, whose fields are `u_pos`, `pde_u`, `classicalRegularity`, and `initialTrace`;
* inside the EWA realization route, the actual carried atoms for `realSlice_reducedCore`: heat-floor/ball positivity, `htime`, `hlap`, `hchemInv`, `hlogInv`, summability of lap/chem/log series, `hclassReg`, `hrealizes`, initial cosine summability/reconstruction, defect summability, and defect tendsto. These are listed in the signature of `realSlice_reducedCore` at `SourceReducedCore.lean:87-143`.

## Recommendation

For a small next Lean commit after the aliases, add the reduced-core chi-nonpositive wrapper above. Be explicit in the docstring that it is route exposure only.

For the next non-alias analytic commit, target `CoupledFluxResolverReducedCoreData p`, not `CoupledFluxResolverAnalyticData p`, and do not route through:

* `SourceChiNegTheorem11.ChiNegDatumUniformConstruction`, because it carries the old logistic-only `hfp`;
* all-PPID uniform-floor/Wiener assumptions as a producer for the weak `CoupledFluxClassicalLocalExistenceResidual`, because the weak `PositiveInitialDatum` class lacks the uniform closed-domain floor. The PPID paths are headline-facing routes, not weak-residual producers.

No unconditional negative-`chi` claim is supported by the audited source.
