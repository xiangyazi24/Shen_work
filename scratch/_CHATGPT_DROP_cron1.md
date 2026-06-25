# ChatGPT git-drop (cron1)

## Q344 — χ₀<0 local-existence producer audit

### Executive verdict

I do **not** find a closed canonical local-classical-existence producer for `χ₀ < 0` analogous to the χ₀=0 route.

What exists for χ₀<0 is:

1. a real **contraction-smallness core** in `ChemMildLocal.lean`, valid for arbitrary `χ₀` through `|χ₀|`, but not by itself a Paper 2 local classical solution producer;
2. a conditional **canonical/non-EWA residual producer**
   ```lean
   coupledFluxClassicalLocalExistenceResidual_of_resolverAnalyticData
   ```
   from the big analytic package
   ```lean
   CoupledFluxResolverAnalyticData p
   ```
   but that package is not produced unconditionally;
3. an EWA route
   ```lean
   chiNeg_residual_of_datumUniformFaithful
   ```
   from
   ```lean
   ChiNegDatumUniformConstructionFaithful p
   ```
   but that faithful construction is still an explicit carried frontier;
4. a one-field residual wrapper
   ```lean
   ChiNegativeNonminimalCoupledLocalExistenceResidual p
   ```
   whose field is exactly the quantitative coupled local factory, but again it is a residual, not a producer.

So the answer to the critical question is:

```text
No: I do not see a fully closed canonical χ₀<0 hlocal producer.
Yes: there are conditional χ₀<0 residual closures and a real Banach-contraction core.
```

---

## 1. Search result: no closed `quantitativeLocalExistence` for χ₀<0 / χ₀≤0

I searched for the requested families:

```text
quantitativeLocalExistence.*chiNeg
quantitativeLocalExistence.*chi_le
localExistence.*chiNeg
localExistence.*chi_le
hlocal.*chiNeg
CoupledFluxClassicalLocalExistenceResidual.*chi
```

The hits point to residual / audit / EWA files, not to a closed theorem of the shape:

```lean
∀ u₀, PositiveInitialDatum intervalDomain u₀ →
  ∃ Tmax > 0, ∃ u v,
    IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
    InitialTrace intervalDomain u₀ u
```

or the stronger quantitative factory:

```lean
∀ M > 0, ∃ δ > 0,
  ∀ {u₀}, PositiveInitialDatum intervalDomain u₀ →
  (∀ x, |u₀ x| ≤ M) →
    ∃ u v,
      IsPaper2ClassicalSolution intervalDomain p δ u v ∧
      InitialTrace intervalDomain u₀ u
```

for χ₀<0 / χ₀≤0, without additional residual hypotheses.

---

## 2. What `ChemMildLocal.lean` actually closes

`ChemMildLocal.lean` is real progress, but it is a **contraction core**, not the full local-classical-existence theorem.

The key theorem is:

```lean
import ShenWork.Paper2.ChemMildLocal

#check ShenWork.Paper2.chemMildLocal_orderBox_exists
```

with type:

```lean
theorem chemMildLocal_orderBox_exists (χ₀ L : ℝ) (hL : 0 ≤ L) :
    ∃ T : ℝ, 0 < T ∧ ∃ q : ℝ≥0,
      (q : ℝ) = chemMildLocalLipConst χ₀ L T ∧ q < 1
```

The file explicitly says the contraction constant is

```text
q(T) = |χ₀| · C∇ · 2√T + L · T
```

and that `q(T) → 0` as `T → 0`.  It also has:

```lean
theorem chemMildLocal_orderBox_fixedPoint (χ₀ L : ℝ) (hL : 0 ≤ L)
    {α : Type*} [MetricSpace α] [CompleteSpace α] [Nonempty α] :
    ∃ T : ℝ, 0 < T ∧ ∃ q : ℝ≥0,
      (q : ℝ) = chemMildLocalLipConst χ₀ L T ∧ q < 1 ∧
      ∀ {f : α → α}, ContractingWith q f → ∀ x₀ : α,
        ∃ y : α, Function.IsFixedPt f y ∧
          Tendsto (fun n => f^[n] x₀) atTop (𝓝 y)
```

This is not sign-restricted; the theorem takes `χ₀` and uses `|χ₀|`.  But the file header is explicit that the remaining datum-shape bookkeeping is still open: instantiate the genuine `C([0,T],C(Ω̄))` order-box, prove the mild map is the concrete `ContractingWith` map, and bridge the fixed point to classical regularity.  Therefore it is not the hlocal producer by itself.

---

## 3. `IntervalChiNegLocalExist.lean`: envelope-lattice reduction, not a closed producer

`IntervalChiNegLocalExist.lean` proves candidate-generic invariance and an abstract fixed-point reduction, but it deliberately carries the concrete Banach instantiation as hypotheses.

The important theorem is:

```lean
import ShenWork.Paper2.IntervalChiNegLocalExist

#check ShenWork.Paper2.IntervalChiNegLocalExist.localExist_of_envBall_fixedPoint
```

It assumes, among other things:

```lean
{α : Type*} [MetricSpace α]
(hcomplete : IsComplete s)
(hself : MapsTo Φ s s)
(hdist : ∀ a b : s,
  dist (hself.restrict Φ s s a) (hself.restrict Φ s s b) ≤ q * dist a b)
(hreadout : ∀ y ∈ s, Function.IsFixedPt Φ y →
  (∀ k, |cosineCoeffs (u r) k| ≤ E_base k))
```

and then returns the `LocalExist`-style pair:

```lean
(∀ k, |cosineCoeffs (u r) k| ≤ E_base k)
  ∧ (∀ k τ, |G k τ| ≤ Llog * E_base k)
```

The file header states the missing frontier exactly: no concrete `MetricSpace`/`IsComplete` model of the envelope ball, no concrete `Φ` with `MapsTo` plus contraction, and no fixed-point-to-`cosineCoeffs (u r)` readout is built in the repo.  So this is not a full hlocal producer either.

---

## 4. Canonical/non-EWA conditional route: `CoupledFluxResolverAnalyticData`

The closest canonical χ₀<0 local-existence producer is conditional:

```lean
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual

#check ShenWork.Paper2.ChiNegResidual.CoupledFluxResolverAnalyticData
#check ShenWork.Paper2.ChiNegResidual.coupledFluxClassicalLocalExistenceResidual_of_resolverAnalyticData
```

The residual target is:

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

The canonical analytic package is:

```lean
def CoupledFluxResolverAnalyticData (p : CM2Params) : Prop :=
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
                ∀ u v : ℝ → intervalDomain.Point → ℝ,
                  intervalTrajectoryBoundedOn T Mball u →
                  (∀ t x, 0 ≤ t → t ≤ T →
                    u t x = intervalCoupledDuhamelOperator p
                      (intervalNeumannResolverR p) u0 u t x) →
                  (∀ t, v t = intervalNeumannResolverR p (u t)) →
                    RegularityBootstrap p T u0 u
```

And the theorem is:

```lean
theorem coupledFluxClassicalLocalExistenceResidual_of_resolverAnalyticData
    (p : CM2Params) (hα : 1 ≤ p.α)
    (H : CoupledFluxResolverAnalyticData p) :
    CoupledFluxClassicalLocalExistenceResidual p
```

So this is a canonical/non-EWA conditional local-existence route, but the big analytic package `CoupledFluxResolverAnalyticData p` is still an input.  I do not see a theorem producing it unconditionally.

---

## 5. The one-field B1 residual is just the same quantitative local factory

`IntervalDomainThm11ChiNegativeResidualB1.lean` defines:

```lean
structure ChiNegativeNonminimalCoupledLocalExistenceResidual
    (p : CM2Params) : Prop where
  localExistence :
    ∀ M : ℝ, 0 < M → ∃ delta : ℝ, 0 < delta ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
          ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p delta u v ∧
            InitialTrace intervalDomain u₀ u
```

It proves:

```lean
theorem coupledFluxResidual_of_coupledLocalResidual
    {p : CM2Params}
    (H : ChiNegativeNonminimalCoupledLocalExistenceResidual p) :
    ChiNegResidual.CoupledFluxClassicalLocalExistenceResidual p :=
  H.localExistence
```

and:

```lean
theorem Theorem_1_1_intervalDomain_chiNegative_nonminimal_of_coupledLocalResidual
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (H : ChiNegativeNonminimalCoupledLocalExistenceResidual p) :
    Theorem_1_1 intervalDomain p
```

This is useful cleanup, but it is still a residual field, not a producer.

---

## 6. The EWA faithful route: not canonical hlocal, still a residual route

`SourceChiNegFaithful.lean` defines:

```lean
def ChiNegDatumUniformConstructionFaithful (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
    ∀ {u0 : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u0 →
      (∀ x, |u0 x| ≤ M) →
        ∃ u_star : EWA δ 1,
          CoupledDuhamelReducedClassicalCore p δ u0 (realSlice u_star)
```

and proves:

```lean
theorem chiNeg_residual_of_datumUniformFaithful (p : CM2Params)
    (hU : ChiNegDatumUniformConstructionFaithful p) :
    CoupledFluxClassicalLocalExistenceResidual p
```

The proof does not use the old false logistic-only `hfp`.  It destructures the reduced core:

```lean
have hreg : RegularityBootstrap p δ u0 (realSlice u_star) :=
  regularityBootstrap_of_coupledDuhamel_reducedClassicalCore p C
obtain ⟨v, hpos, hvnn, hpde_u, hpde_v, hbc, hclassreg, htrace⟩ := hreg
exact ⟨realSlice u_star, v,
  IsPaper2ClassicalSolution.of_components hδ hclassreg hpos hvnn hpde_u hpde_v hbc,
  htrace⟩
```

So this is a different way to manufacture the same quantitative residual — from EWA realization data.  But the construction itself is still the carried frontier `ChiNegDatumUniformConstructionFaithful p`.

`ChiNegFrontierAssembly.lean` repackages this through:

```lean
def ChiNegFaithfulRealizationFrontier (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∀ {u0 : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u0 →
      (∀ x, |u0 x| ≤ M) →
        ∃ u_star : EWA δ 1,
          CoupledDuhamelReducedClassicalCore p δ u0 (realSlice u_star)
```

and proves:

```lean
theorem chiNeg_datumUniformFaithful_of_frontier (p : CM2Params)
    (hF : ChiNegFaithfulRealizationFrontier p) :
    ChiNegDatumUniformConstructionFaithful p
```

plus:

```lean
theorem chiNeg_theorem_1_1_of_faithfulFrontier ... :
    Theorem_1_1 intervalDomain p
```

Again: useful faithful reduction, but not unconditional.

---

## 7. Does `theorem_1_1_intervalDomain_chiNeg_of_coupledFlux...` go through the umbrella?

Yes.  It is not a direct EWA-only path.

The theorem is:

```lean
theorem theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual
    (p : CM2Params) (hchi_neg : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (_halpha : 1 ≤ p.α) (hgamma : 1 ≤ p.γ)
    (hExist : CoupledFluxClassicalLocalExistenceResidual p) :
    Theorem_1_1 intervalDomain p :=
  RestartLocalWiring.paper2_theorem_1_1_from_quant_and_hlocal
    p (le_of_lt hchi_neg) ha hb hgamma hExist
    (localExistence_of_coupledFluxClassicalLocalExistenceResidual p hExist)
```

So it takes the quantitative residual `hExist` as `hQuant` and also derives ordinary `hlocal` from the same residual by:

```lean
localExistence_of_coupledFluxClassicalLocalExistenceResidual p hExist
```

Then `RestartLocalWiring.paper2_theorem_1_1_from_quant_and_hlocal` calls the umbrella theorem:

```lean
Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
```

and builds the uniform restart/glue continuation using `hQuant` and the Lemma 3.1 sup-norm bound.  Thus:

```text
EWA faithful construction
  → CoupledFluxClassicalLocalExistenceResidual
  → RestartLocalWiring.paper2_theorem_1_1_from_quant_and_hlocal
  → umbrella/final wiring
  → Theorem_1_1 intervalDomain p.
```

It does **not** bypass the umbrella.  It supplies the umbrella's local-existence and quantitative restart inputs from the residual.

---

## Final classification

### Closed / canonical for χ₀<0?

```text
No fully closed canonical hlocal producer found.
```

### Real pieces that exist

```text
ChemMildLocal.chemMildLocal_orderBox_exists
  Real short-time contraction-smallness core, any χ₀ via |χ₀|.

ChemMildLocal.chemMildLocal_orderBox_fixedPoint
  Banach fixed-point core on an arbitrary complete metric model.

ChiNegResidual.coupledFluxClassicalLocalExistenceResidual_of_resolverAnalyticData
  Conditional canonical/non-EWA residual producer from CoupledFluxResolverAnalyticData.

EWA.chiNeg_residual_of_datumUniformFaithful
  Conditional EWA residual producer from ChiNegDatumUniformConstructionFaithful.

ChiNegativeResidual.Theorem_1_1_intervalDomain_chiNegative_nonminimal_of_coupledLocalResidual
  One-field residual closeout to Theorem 1.1.
```

### Still open / carried

```text
Concrete χ₀<0 local classical existence for arbitrary positive interval data.
Concrete quantitative factory ∀M ∃δ uniform over |u₀|≤M.
Concrete order-box Banach instantiation + regularization bridge, unless supplied by CoupledFluxResolverAnalyticData or EWA faithful realization frontier.
```

### Relation to χ₀=0

The χ₀=0 route has canonical Picard/restart scaffolding specialized to the no-flux case.  The χ₀<0 route does **not** currently have an analogous unconditional canonical local-existence producer.  It has a faithful EWA reduction and a canonical analytic-data reduction, both conditional on named residuals.
