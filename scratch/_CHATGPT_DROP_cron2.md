# Q426 (cron2): B-form consumption of `BFormBankedInputs.Hinf`

## Executive verdict

I read the current `IntervalBFormDirectClassical.lean` and the inf-threshold definitions/proofs.

In the current B-form direct chain, `B.Hinf : ConjugatePicardInfThresholdData p u₀ DB.T` is consumed for **strict positivity of the B-form Picard limit**, not for the B-form source regularity itself. The live consumers are:

1. `BFormBankedInputs.hpde_u` — passes `B.Hinf` and `B.hsmall` to the windowed `On` PDE theorem. Inside the `On` theorem, `Hinf` is used only to derive `hpost : ∀ σ∈(0,T), ∀x∈[0,1], 0 < lift(u σ) x` via `conjugatePicardLimit_hpost_of_PID`.
2. `bform_u_pos` — directly proves `0 < conjugatePicardLimit ... t x` from `B.huPaper`, `B.Hinf`, and `B.hsmall` using `conjugatePicardLimit_pos_of_PID`.
3. All later uses of `B.Hinf` in `IntervalBFormDirectClassical.lean` are indirect through `bform_u_pos`: endpoint nonzero for `u`, source-decay positivity for the resolver source, v-regularity, classical solution positivity, and elliptic PDE/Neumann bridge hypotheses.

No theorem in `IntervalBFormDirectClassical.lean` directly projects `B.Hinf.CQ`, `B.Hinf.CL`, `B.Hinf.hQ_bound`, `B.Hinf.hgeom`, etc. The direct file passes the whole `Hinf` package into the inf-threshold lemmas.

Inside the inf-threshold lemmas, the actual fields used are:

* `CQ`, `CL` occur in the stated smallness budget `hsmall`:

  ```lean
  |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * H.CQ)
    + T * H.CL ≤ paperPositiveFloor hu₀ / 2
  ```

* The one-step lower-bound proof uses chem/logistic source bounds/integrability:
  `H.hQ_int`, `H.hCQ`, `H.hQ_bound`, `H.hB_int`, `H.hCL`, `H.hL_bound`, `H.hL_int`.
* The limit-passage proof uses the geometric convergence data:
  `H.hK`, `H.hK_nn`, `H.hC₀`, `H.hgeom`.
* I did not find a live use of `H.hT` in these proofs; the theorem statements already carry the required time hypotheses externally.

The important range issue: every downstream consumer in the B-form chain only needs positivity/source bounds on **positive-time windows** (`0 < t`, `t < T` or `t ≤ T`). The fields in `ConjugatePicardInfThresholdData` are over-strong where they quantify over all `s` unconditionally:

```lean
hQ_int   : ∀ n s, Integrable ...
hQ_bound : ∀ n s y, |chemFluxLifted ... n s y| ≤ CQ
hL_bound : ∀ n s y, |logisticLifted ... n s y| ≤ CL
```

The proofs only invoke them for `s` in the integration interval `0 < s ≤ t ≤ T`. Because the current fields are unconditional, the proof can pass `fun s _ _ => H.hQ_int n s`, `fun s _ _ => H.hQ_bound n s`, and `H.hL_bound n` without threading window hypotheses. A windowed structure would be enough for these consumers, but the proof signatures would need to carry/pass the `0 < s` and `s ≤ T` hypotheses to the fields.

So: `Hinf` is not merely an algebraic package for `hsmall`. It supplies the analytic source-bound/integrability and geometric convergence data used to prove positivity of iterates and the limit. But all of that use is **windowed positive-time use**. It is not using unconditional-in-`s` facts in an essential way; those fields are over-typed for the live B-form consumers.

## Lean probes used

```lean
import ShenWork.Paper2.IntervalBFormDirectClassical

open Filter Topology Set
open ShenWork.IntervalDomain
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData ConjugatePicardInfThresholdData
   conjugatePicardLimit paperPositiveFloor)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalBFormSpectral
  (bFormSourceCoeffs bFormSource_duhamelSourceTimeC1On)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.Paper2
open ShenWork.Paper2.BFormDirectClassical

#check BFormBankedInputs
#check BFormBankedInputs.hpde_u
#check BFormDirectFrontier
#check intervalConjugatePicardLimit_classicalRegularity_direct
#check intervalConjugatePicardLimit_isClassicalSolution_direct
```

```lean
import ShenWork.Paper2.IntervalConjugatePicardInfThreshold

open MeasureTheory Set Filter
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateDuhamelMap intervalConjugateKernelOperator)
open ShenWork.IntervalConjugatePicard
  (conjugatePicardIter conjugatePicardLimit)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant)
open ShenWork.Paper2 (PaperPositiveInitialDatum)

namespace ShenWork.IntervalConjugatePicard

#check ConjugatePicardInfThresholdData
#check intervalConjugateDuhamelMap_ge_half_floor
#check conjugatePicardIter_ge_half_floor_of_PID
#check conjugatePicardLimit_pos_of_PID
#check conjugatePicardLimit_hpost_of_PID

end ShenWork.IntervalConjugatePicard
```

```lean
import ShenWork.Paper2.IntervalBFormSpectralProviderDischargeOn

open Filter Topology Set

namespace ShenWork.IntervalConjugatePicard

#check pde_u_of_localized_data_with_hpost_on
#check pde_u_PID_global_restart_on
#check intervalConjugateMildSolution_pde_u_PID_global_restart_on

end ShenWork.IntervalConjugatePicard
```

## 1. Current `BFormBankedInputs` shape

Current `BFormBankedInputs` has already moved to the windowed `On` source and `hchemIoo` shape:

```lean
import ShenWork.Paper2.IntervalBFormDirectClassical

open Filter Topology Set
open ShenWork.IntervalDomain
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData ConjugatePicardInfThresholdData
   conjugatePicardLimit paperPositiveFloor)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.Paper2
open ShenWork.Paper2.BFormDirectClassical

-- Current relevant excerpt:
--
-- structure BFormBankedInputs
--     (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
--     (DB : ConjugateMildExistenceData p u₀) where
--   huPaper : PaperPositiveInitialDatum intervalDomain u₀
--   Hinf : ConjugatePicardInfThresholdData p u₀ DB.T
--   hsmall :
--     |p.χ₀| * (heatGradientLinftyLinftyConstant *
--         (2 * Real.sqrt DB.T) * Hinf.CQ)
--       + DB.T * Hinf.CL ≤ paperPositiveFloor huPaper / 2
--   MInit : ℝ
--   haInit : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ MInit
--   hlogSrc : DuhamelSourceTimeC1On
--     (coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) 0 DB.T
--   hchemSrc : DuhamelSourceTimeC1On
--     (coupledChemDivSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) 0 DB.T
--   hB_global : ∀ t, 0 < t → t ≤ DB.T → Set.EqOn ...
--   hlogCont : ...
--   hlogFourier : ...
--   hchemIoo : ∀ t, 0 < t → t < DB.T →
--     ChemDivCosineFourierDataIoo p
--       ((conjugatePicardLimit p u₀ DB.T) t)
--       (coupledChemicalConcentration p
--         (conjugatePicardLimit p u₀ DB.T) t)
#check BFormBankedInputs
```

So in the current file, the field name is still `Hinf`, but the source machinery is now windowed; the false `hchemCont` has been replaced by `hchemIoo`.

## 2. Direct consumers of `B.Hinf` in `IntervalBFormDirectClassical.lean`

### Consumer A: `BFormBankedInputs.hpde_u`

`BFormBankedInputs.hpde_u` passes `B.Hinf` and `B.hsmall` into the `On` PDE theorem:

```lean
import ShenWork.Paper2.IntervalBFormDirectClassical

open ShenWork.Paper2.BFormDirectClassical

-- Current body excerpt:
--
-- theorem BFormBankedInputs.hpde_u ... (B : BFormBankedInputs p DB) : ... :=
--   ShenWork.IntervalConjugatePicard.intervalConjugateMildSolution_pde_u_PID_global_restart_on
--       DB B.huPaper B.Hinf B.hsmall
--       ...
#check BFormBankedInputs.hpde_u
```

In the `On` theorem, `Hinf` is not used for source estimates; source estimates come from `hsrcB_on`, `hB_global`, `hlogData`, and `hchemData`. `Hinf` is used to derive `hpost`:

```lean
-- In pde_u_PID_global_restart_on:
-- have hpost := conjugatePicardLimit_hpost_of_PID
--   (p := p) (u₀ := u₀) (T := D.T) hu₀ Hinf hsmall
-- ...
-- exact pde_u_of_localized_data_with_hpost_on
--   D hpost bc hbsum hagree aB hsrcB_on hsource_split hB_restart hlogData
--     hchemData
```

Thus in the PDE branch, `B.Hinf` is only a provider for the strict positive-slice hypothesis `hpost`; after that, the local PDE proof does not inspect `Hinf`.

### Consumer B: `bform_u_pos`

`bform_u_pos` directly consumes `B.Hinf`:

```lean
import ShenWork.Paper2.IntervalBFormDirectClassical

open ShenWork.Paper2.BFormDirectClassical

-- private theorem bform_u_pos ... (B : BFormBankedInputs p DB) :
--     ∀ t x, 0 < t → t < DB.T →
--       0 < conjugatePicardLimit p u₀ DB.T t x := by
--   intro t x ht htT
--   exact ShenWork.IntervalConjugatePicard.conjugatePicardLimit_pos_of_PID
--     B.huPaper B.Hinf B.hsmall t ht (le_of_lt htT) x
```

This is the main direct positivity consumer in the classical solution assembly.

### Indirect consumers through `bform_u_pos`

Several later helpers consume the positivity produced by `bform_u_pos`, hence indirectly depend on `B.Hinf`:

```lean
import ShenWork.Paper2.IntervalBFormDirectClassical

open ShenWork.Paper2.BFormDirectClassical

#check intervalConjugatePicardLimit_classicalRegularity_direct
#check intervalConjugatePicardLimit_isClassicalSolution_direct
```

From the file:

* `bform_u_closedC2_endpointDerivs` uses `bform_u_pos` only to prove endpoint nonzero (`h0`, `h1`) before applying `intervalDomainCosineSlice_conjunct7`.
* `bform_sourceDecay` uses `bform_u_pos` to prove the positive `hpos_lift` needed by `sourceCoeffQuadraticDecay_of_closedC2_neumann_slice`.
* `bform_vSpatialInterior`, `bform_vNeumannLimits`, and `bform_vClosedSpatial` consume `bform_sourceDecay`, hence indirectly depend on positivity from `Hinf`.
* `intervalConjugatePicardLimit_isClassicalSolution_direct` uses `bform_u_pos` directly for the `u_pos` field, and again as an input to `coupledChemical_ellipticPDE_of_closedC2_neumann` and `coupledChemical_neumannBC_of_closedC2_neumann`.

Notably, these are all positive-time/interior classical-solution uses. They do not require source bounds at arbitrary global `s` outside the horizon.

## 3. Definition of `ConjugatePicardInfThresholdData`

The structure is:

```lean
import ShenWork.Paper2.IntervalConjugatePicardInfThreshold

open MeasureTheory Set Filter
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugatePicard
  (conjugatePicardIter conjugatePicardLimit)

namespace ShenWork.IntervalConjugatePicard

-- structure ConjugatePicardInfThresholdData
--     (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T : ℝ) where
--   K : ℝ
--   C₀ : ℝ
--   CQ : ℝ
--   CL : ℝ
--   hT : 0 < T
--   hK : K < 1
--   hK_nn : 0 ≤ K
--   hC₀ : 0 ≤ C₀
--   hCQ : 0 ≤ CQ
--   hCL : 0 ≤ CL
--   hgeom : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
--     ∀ x : intervalDomainPoint,
--       |conjugatePicardIter p u₀ (n + 1) t x
--         - conjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀
--   hQ_int : ∀ n s,
--     Integrable (chemFluxLifted p (conjugatePicardIter p u₀ n s))
--       (intervalMeasure 1)
--   hQ_bound : ∀ n s y,
--     |chemFluxLifted p (conjugatePicardIter p u₀ n s) y| ≤ CQ
--   hB_int : ∀ n t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
--     IntervalIntegrable
--       (fun s : ℝ =>
--         intervalConjugateKernelOperator (t - s)
--           (chemFluxLifted p (conjugatePicardIter p u₀ n s)) x.1)
--       volume 0 t
--   hL_bound : ∀ n s y,
--     |logisticLifted p (conjugatePicardIter p u₀ n s) y| ≤ CL
--   hL_int : ∀ n t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
--     IntervalIntegrable
--       (fun s : ℝ =>
--         intervalFullSemigroupOperator (t - s)
--           (logisticLifted p (conjugatePicardIter p u₀ n s)) x.1)
--       volume 0 t
#check ConjugatePicardInfThresholdData

end ShenWork.IntervalConjugatePicard
```

This is a mixed package:

* Algebraic/geometric convergence: `K`, `C₀`, `hK`, `hK_nn`, `hC₀`, `hgeom`.
* Chemotaxis source estimates: `CQ`, `hCQ`, `hQ_int`, `hQ_bound`, `hB_int`.
* Logistic source estimates: `CL`, `hCL`, `hL_bound`, `hL_int`.
* Horizon positivity: `hT`, apparently not essential in the downstream proofs I read.

## 4. What fields are extracted by the positivity lemmas?

### `intervalConjugateDuhamelMap_ge_half_floor`

This is the one-step lower bound for the conjugate map. It uses:

* `H.CQ` and `H.CL` in the smallness statement `hsmall`.
* Chem leg:
  * `H.hQ_int n s`,
  * `H.hCQ`,
  * `H.hQ_bound n s`,
  * `H.hB_int n t ht htT x`.
* Logistic leg:
  * `H.hCL`,
  * `H.hL_bound n`,
  * `H.hL_int n t ht htT x`.

The proof invokes the chem bound as:

```lean
ShenWork.IntervalConjugateDuhamelMap.conjugateDuhamel_sup_bound
  ht htT (fun s _ _ => H.hQ_int n s) H.hCQ
  (fun s _ _ => H.hQ_bound n s) x.1 (H.hB_int n t ht htT x)
```

and the logistic bound as:

```lean
ShenWork.IntervalGradDuhamelBound.valueDuhamel_sup_bound
  ht htT H.hCL (H.hL_bound n) x.1 (H.hL_int n t ht htT x)
```

The `_ _` arguments in the first call are the tell: the theorem only asks for facts on the integration window, but the current `H.hQ_int` and `H.hQ_bound` are unconditional, so the proof simply ignores those window hypotheses.

### `conjugatePicardIter_ge_half_floor_of_PID`

This uses the one-step lemma above inductively. It consumes the same fields indirectly.

### `conjugatePicardLimit_pos_of_PID`

This first gets the iterate lower bound, then passes to the limit. The limit passage uses:

* `H.hK`,
* `H.hK_nn`,
* `H.hC₀`,
* `H.hgeom`.

Specifically:

```lean
real_cauchySeq_of_geometric_bound H.hK H.hK_nn H.hC₀
  (fun n => H.hgeom n t ht htT x)
```

Again, this is a positive-window use: `hgeom` is invoked only at `0 < t`, `t ≤ T`.

### `conjugatePicardLimit_hpost_of_PID`

This just converts `conjugatePicardLimit_pos_of_PID` into the lifted closed-interval form:

```lean
∀ σ, 0 < σ → σ < T →
  ∀ x ∈ Set.Icc 0 1,
    0 < intervalDomainLift (conjugatePicardLimit p u₀ T σ) x
```

It passes `σ hσ hσT.le` to `conjugatePicardLimit_pos_of_PID`.

## 5. Windowed versus unconditional: is `Hinf` over-typed?

For the B-form direct consumers: yes, the unconditional parts are over-typed.

The live B-form consumers only ask for:

* `0 < t`, `t < DB.T` / `t ≤ DB.T` positivity of the limit;
* bounds/integrability of source terms only inside Duhamel integrals over `s ∈ (0,t]` with `t ≤ T`;
* geometric convergence only for positive `t ≤ T`.

Thus a windowed version would be enough, for example:

```lean
structure ConjugatePicardInfThresholdDataOn
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T : ℝ) where
  K : ℝ
  C₀ : ℝ
  CQ : ℝ
  CL : ℝ
  hK : K < 1
  hK_nn : 0 ≤ K
  hC₀ : 0 ≤ C₀
  hCQ : 0 ≤ CQ
  hCL : 0 ≤ CL
  hgeom : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
    ∀ x : intervalDomainPoint,
      |conjugatePicardIter p u₀ (n + 1) t x
        - conjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀
  hQ_int : ∀ n s, 0 < s → s ≤ T →
    Integrable (chemFluxLifted p (conjugatePicardIter p u₀ n s))
      (intervalMeasure 1)
  hQ_bound : ∀ n s, 0 < s → s ≤ T → ∀ y,
    |chemFluxLifted p (conjugatePicardIter p u₀ n s) y| ≤ CQ
  hB_int : ∀ n t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    IntervalIntegrable
      (fun s : ℝ =>
        intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (conjugatePicardIter p u₀ n s)) x.1)
      volume 0 t
  hL_bound : ∀ n s, 0 < s → s ≤ T → ∀ y,
    |logisticLifted p (conjugatePicardIter p u₀ n s) y| ≤ CL
  hL_int : ∀ n t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    IntervalIntegrable
      (fun s : ℝ =>
        intervalFullSemigroupOperator (t - s)
          (logisticLifted p (conjugatePicardIter p u₀ n s)) x.1)
      volume 0 t
```

Then `intervalConjugateDuhamelMap_ge_half_floor` would pass the window facts instead of dropping them:

```lean
-- schematic replacement in the chem leg:
(fun s hs0 hst => H.hQ_int n s hs0 (le_trans hst htT))
(fun s hs0 hst => H.hQ_bound n s hs0 (le_trans hst htT))
```

and logistic:

```lean
(fun s hs0 hst => H.hL_bound n s hs0 (le_trans hst htT))
```

The `hB_int`/`hL_int` fields are already windowed in the current structure. The real over-typed fields are `hQ_int`, `hQ_bound`, and `hL_bound` (and arguably `hT`, which appears redundant in the uses I inspected).

## 6. Is `Hinf` only supplying `hsmall` and algebraic contraction data?

No. It supplies more than `hsmall`.

`hsmall` only references the scalar constants `CQ` and `CL`. But to prove the positivity theorem, the code also uses:

* chem integrability and bound fields (`hQ_int`, `hQ_bound`, `hB_int`),
* logistic bound and integrability fields (`hL_bound`, `hL_int`),
* geometric convergence (`hgeom`) and contraction scalars (`hK`, `hK_nn`, `hC₀`).

However, all of those uses are in the positive-time window. So the right conclusion is:

```text
Hinf is not just algebraic budget data.
It is a positivity/inf-threshold package containing source bounds + integrability + geometric convergence.
But its unconditional-in-s fields are stronger than the B-form consumers need.
A windowed `ConjugatePicardInfThresholdDataOn` would suffice for the current chain.
```

## 7. Practical refactor recommendation

For minimum churn, do not retype `BFormBankedInputs.Hinf` immediately. Instead introduce an adapter theorem:

```lean
-- Schematic:
def ConjugatePicardInfThresholdData.toOn
    (H : ConjugatePicardInfThresholdData p u₀ T) :
    ConjugatePicardInfThresholdDataOn p u₀ T :=
  { K := H.K
    C₀ := H.C₀
    CQ := H.CQ
    CL := H.CL
    hK := H.hK
    hK_nn := H.hK_nn
    hC₀ := H.hC₀
    hCQ := H.hCQ
    hCL := H.hCL
    hgeom := H.hgeom
    hQ_int := fun n s _hs _hsT => H.hQ_int n s
    hQ_bound := fun n s _hs _hsT y => H.hQ_bound n s y
    hB_int := H.hB_int
    hL_bound := fun n s _hs _hsT y => H.hL_bound n s y
    hL_int := H.hL_int }
```

Then prove the inf-threshold lemmas from the `On` structure. Existing unconditional callers can use `.toOn`; future producers need only build the windowed structure.

## Final answer

`BFormBankedInputs.Hinf` is consumed in the B-form chain to prove strict positivity of `conjugatePicardLimit` on `(0,T]` / `(0,T)`. Direct uses in `IntervalBFormDirectClassical.lean` are `BFormBankedInputs.hpde_u` and `bform_u_pos`; subsequent classical-regularity and solution theorems use it indirectly through `bform_u_pos` and `bform_sourceDecay`.

Internally, the inf-threshold proof extracts more than just `CQ`/`CL`: it uses chem/logistic bounds and integrability (`hQ_int`, `hQ_bound`, `hB_int`, `hL_bound`, `hL_int`) for the one-step lower bound, and `hgeom` plus `hK/hK_nn/hC₀` for the limit passage. But all source-bound uses are windowed inside Duhamel integrals, so the unconditional fields `∀ n s` are over-typed. A windowed structure would suffice, with the proof passing `0 < s` and `s ≤ T` through to the fields.
