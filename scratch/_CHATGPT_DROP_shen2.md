# Q2287 shen2: Route-A wiring to lower-barrier branch data

## Verdict

The shortest honest wiring is pure assembly:

1. Build the cap-specialized `PositivePaperLemma42ExactConditions` with
   `kappa c` and `positiveBranchTailCap p c`.
2. Feed current positive Route-A/cubeApprox producer
   `b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData`.
3. Use the produced `U`, lower pin, and profile to fill
   `Paper1PositiveLowerPinnedRawContactBranchData`.
4. Keep `PositiveUpperBarrierContactContradictions p c U` as an explicit residual.

No-contact is not proved by this route. The tail is already handled downstream by
`paper1_positiveContactBranch_of_lowerPinnedRawContactData`, which calls the raw lower-pin tail theorem.

## Existing names

```lean
#check positiveBranchTailCap
#check kappa_lt_positiveBranchTailCap
#check Paper1PositiveLowerPinnedRawContactBranchData
#check paper1_positiveContactBranch_of_lowerPinnedRawContactData
#check paper1_mainStatementTargets_of_lowerPinnedRawContactData
#check PositivePaperLemma42ExactConditions
#check PaperLowerPinnedStationaryFlatFloor
#check PaperLowerRawParabolicFloorRouteAParamCoreNoBar
#check paperLowerRawRouteAParamProducer
#check b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
#check b1_chiPos_existence_paper_routeA_core_noBar_of_cubeApproxData
```

Use a new file:

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveLemma42ParamCore

open Filter Topology

namespace ShenWork.Paper1

noncomputable section
```

## Scalar helper

```lean
theorem positivePaperLemma42ExactConditions_of_branchCap
    (p : CMParams) {c : Real}
    (h_alpha : p.α = p.m + p.γ - 1)
    (h_chi_nonneg : 0 <= p.χ)
    (h_chi_small : p.χ < min (1 / 2 : Real) (chiStar p))
    (hc : 2 < c) :
    PositivePaperLemma42ExactConditions p c (kappa c)
      (positiveBranchTailCap p c) (MChi p) := by
  have h_chi_half : p.χ < (1 / 2 : Real) :=
    lt_of_lt_of_le h_chi_small (min_le_left _ _)
  have h_chi_one : p.χ < 1 := by linarith
  exact
    { hκ0 := kappa_pos_of_two_lt hc
      hκ1 := kappa_lt_one_of_two_lt hc
      hgap := kappa_lt_positiveBranchTailCap p hc
      hrange := by
        simp [positiveBranchTailCap]
      hM := one_le_MChi_of_chi_nonneg_lt_one p h_chi_nonneg h_chi_one
      hc := (kappa_add_inv_eq_of_two_lt hc).symm
      hχ_nonneg := h_chi_nonneg
      hχ_small := h_chi_small
      hα_eq := h_alpha }
```

## Route-A parameter package

```lean
structure Paper1PositiveLowerRawCapRouteAParamData : Prop where
  produce :
    forall p : CMParams,
      forall h_alpha : p.α = p.m + p.γ - 1,
      forall h_chi_nonneg : 0 <= p.χ,
      forall h_chi_small : p.χ < min (1 / 2 : Real) (chiStar p),
      forall c : Real, forall hc : 2 < c,
        exists lam D Lambda : Real,
          let hcond : PositivePaperLemma42ExactConditions p c (kappa c)
              (positiveBranchTailCap p c) (MChi p) :=
            positivePaperLemma42ExactConditions_of_branchCap
              p h_alpha h_chi_nonneg h_chi_small hc
          exists hpar :
            PaperLowerRawParabolicFloorRouteAParamCoreNoBar
              p c lam (MChi p) (kappa c) (positiveBranchTailCap p c)
              D Lambda hcond.hκ0.le (le_trans zero_le_one hcond.hM),
              1 <= D /\
              paperDMin p.χ (MChi p) (kappa c) (positiveBranchTailCap p c)
                p.m p.γ c < D /\
              0 <= Lambda /\ Lambda <= MChi p /\
              PaperLowerPinnedStationaryFlatFloor p c (kappa c) (MChi p)
                (lowerBarrierRaw (kappa c) (positiveBranchTailCap p c) D)
                (rotheSeqOfPaperFromPositiveCond p c lam (MChi p) (kappa c)
                  (positiveBranchTailCap p c) Lambda hcond
                  (fun u => paperLowerRawRouteAParamProducer (hpar.producer u))) /\
              StationaryStrongMaxPrinciple p c (kappa c) (MChi p) /\
              (forall U : Real -> Real,
                InLowerPinnedMonotoneTrap (kappa c) (MChi p)
                  (lowerBarrierRaw (kappa c) (positiveBranchTailCap p c) D) U ->
                FrozenStationaryWaveProfile p c U ->
                  PositiveUpperBarrierContactContradictions p c U)
```

## Assembly theorem

```lean
theorem paper1_positiveRawBranchData_of_routeAParamData
    (hData : Paper1PositiveLowerRawCapRouteAParamData) :
    Paper1PositiveLowerPinnedRawContactBranchData := by
  refine ⟨?_⟩
  intro p h_alpha h_chi_nonneg h_chi_small c hc
  let hcond : PositivePaperLemma42ExactConditions p c (kappa c)
      (positiveBranchTailCap p c) (MChi p) :=
    positivePaperLemma42ExactConditions_of_branchCap
      p h_alpha h_chi_nonneg h_chi_small hc
  rcases hData.produce p h_alpha h_chi_nonneg h_chi_small c hc with
    ⟨lam, D, Lambda, hpar, hD_ge_one, hD_gt, hLambda0, hLambdaM,
      hconv, hsmp, hcontact⟩
  obtain ⟨U, hpin, hprofile⟩ :=
    b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
      p c lam (MChi p) (kappa c) (positiveBranchTailCap p c) D Lambda
      hcond hD_gt hD_ge_one hLambda0 hLambdaM hpar hconv hsmp
  exact
    ⟨positiveBranchTailCap p c, D, U,
      le_trans zero_le_one hD_ge_one,
      le_rfl,
      hprofile,
      hpin,
      hcontact U hpin hprofile⟩
```

Field closure summary:

```lean
κtilde := positiveBranchTailCap p c
0 <= D := le_trans zero_le_one hD_ge_one
positiveBranchTailCap p c <= κtilde := le_rfl
FrozenStationaryWaveProfile p c U := hprofile
InLowerPinnedMonotoneTrap ... := hpin
PositiveUpperBarrierContactContradictions p c U := hcontact U hpin hprofile
```

## Downstream wrapper

```lean
theorem paper1_positiveContactBranch_of_routeAParamData
    (hData : Paper1PositiveLowerRawCapRouteAParamData) :
    Paper1PositiveCriticalFrozenStationaryContactBranch :=
  paper1_positiveContactBranch_of_lowerPinnedRawContactData
    (paper1_positiveRawBranchData_of_routeAParamData hData)
```

Then:

```lean
example {cStarStarFn : CMParams -> Real}
    (hneg : ConstructionNegSMPProvider)
    (hroute : Paper1PositiveLowerRawCapRouteAParamData)
    (hmain : Paper1MainlineExistence cStarStarFn) :
    Paper1MainStatementTargets :=
  paper1_mainStatementTargets_of_lowerPinnedRawContactData
    { constructionNeg := hneg
      positiveLowerPinnedRawContact :=
        paper1_positiveRawBranchData_of_routeAParamData hroute
      mainline := hmain }
```

## Core-noBar variant

If the input is `PaperLowerRawParabolicFloorRouteACoreNoBar`, use the same scalar helper and call:

```lean
b1_chiPos_existence_paper_routeA_core_noBar_of_cubeApproxData
```

The `hconv` field must use the exact sequence in that theorem:

```lean
rotheSeqOfPaperFromPositiveCond p c lam (MChi p) (kappa c)
  (positiveBranchTailCap p c) Lambda hcond
  (fun u =>
    (paperLowerRawParabolicFloor_of_routeA_core
      (positivePaperLowerRawParabolicFloorRouteACore_of_noBar hcond hpar)).producer u
      |>.producer)
```

The proof body is identical except the producer call is:

```lean
obtain ⟨U, hpin, hprofile⟩ :=
  b1_chiPos_existence_paper_routeA_core_noBar_of_cubeApproxData
    p c lam (MChi p) (kappa c) (positiveBranchTailCap p c) D Lambda
    hcond hD_gt hD_ge_one hLambda0 hLambdaM hpar hconv hsmp
```

## Residuals that remain honest

The new package still carries:

```lean
PaperLowerRawParabolicFloorRouteAParamCoreNoBar ...
PaperLowerPinnedStationaryFlatFloor ...
StationaryStrongMaxPrinciple p c (kappa c) (MChi p)
forall U, InLowerPinnedMonotoneTrap ... U ->
  FrozenStationaryWaveProfile p c U ->
  PositiveUpperBarrierContactContradictions p c U
```

The last field is the no-contact residual.  Current Route-A/cubeApprox producers do not prove it.
