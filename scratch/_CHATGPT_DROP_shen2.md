# Q2749 shen2: remaining Paper2/Paper3 headline frontiers after Agmon closure

Repo target: `xiangyazi24/Shen_work`, Lean 4.

Current user-supplied state taken as baseline:

```text
lake build ShenWork   # succeeded remotely, 8988 jobs
IntervalAgmonInterpolation.lean proves unitIntervalPositiveAgmonInterpolation
IntervalAgmonInterpolation.lean proves intervalDomain_classicalSolutionPositiveInterpolation
#print axioms only propext/Classical.choice/Quot.sound for those endpoints
```

Scope honored: I did not propose edits to Zinan-owned files

```text
ShenWork/PDE/P3MoserHighExcursionProducer.lean
ShenWork/PDE/P3MoserThresholdPlanProducer.lean
```

I inspected the current statement surfaces in:

```text
ShenWork/Paper2/IntervalDomainStatementAssembly.lean
ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean
```

## 0. Immediate consequence of the Agmon closure

The Agmon residual is now closed at the statement-surface level.

The old explicit-Agmon wrapper is still present:

```lean
structure
  IntervalDomainPaper2StatementChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinAgmonFrontierData
  (p : CM2Params) (C : Paper2Constants p) : Prop where
  section2 : IntervalDomainPaper2BootstrapEstimateThinFrontierData p
  agmon : UnitIntervalPositiveAgmonInterpolation
  localAndMain :
    IntervalDomainPaper2LocalAndMainChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21FrontierData
      p C
```

but the new preferred wrapper has removed `agmon`:

```lean
structure
  IntervalDomainPaper2StatementChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData
  (p : CM2Params) (C : Paper2Constants p) : Prop where
  section2 : IntervalDomainPaper2BootstrapEstimateThinFrontierData p
  localAndMain :
    IntervalDomainPaper2LocalAndMainChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21FrontierData
      p C
```

and fills it with the proved theorem:

```lean
def
  IntervalDomainPaper2StatementChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData.toAgmon
  {p : CM2Params} {C : Paper2Constants p}
  (h :
    IntervalDomainPaper2StatementChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData
      p C) :
  IntervalDomainPaper2StatementChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinAgmonFrontierData
    p C where
  section2 := h.section2
  agmon := unitIntervalPositiveAgmonInterpolation
  localAndMain := h.localAndMain
```

The full statement target is also already wired:

```lean
theorem
  intervalDomainPaper2_statementTargets_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData
  (p : CM2Params) (C : Paper2Constants p)
  (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
  (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
  (hData :
    IntervalDomainPaper2StatementChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData
      p C) :
  IntervalDomainPaper2StatementTargets p C
```

So `UnitIntervalPositiveAgmonInterpolation` and `IntervalDomainClassicalSolutionPositiveInterpolation` should no longer be counted as headline residuals in the preferred Paper2 route.

## 1. Remaining inputs that are now wiring / should be discharged from already-proved code

These are not analytic residuals anymore; they are conversion/assembly surfaces.

| Package / theorem | Status | Notes |
|---|---:|---|
| `UnitIntervalPositiveAgmonInterpolation` | wiring / closed | Use `unitIntervalPositiveAgmonInterpolation`. Do not carry this in preferred headline data. |
| `IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation p` | wiring / closed | Use `intervalDomain_classicalSolutionPositiveInterpolation` or `intervalDomain_classicalSolutionPositiveInterpolation_of_uniform_agmon (params := p) unitIntervalPositiveAgmonInterpolation`. |
| `IntervalDomainPaper2AgmonPositiveSolutionInterpolationEnergyFrontierData.toPositive` | wiring | Still useful for older explicit-Agmon data, but the preferred route should use the proved-Agmon data instead. |
| `IntervalDomainPaper2StatementChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinAgmonFrontierData.toSolutionInterpolation` | wiring | Converts explicit Agmon to positive solution interpolation. The `agmon` field is now fillable by theorem. |
| `IntervalDomainPaper2StatementChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData.toAgmon` | wiring | Correct bridge from current preferred data to old explicit-Agmon surface. |
| `intervalDomainPaper2_statementTargets_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData` | wiring | Current preferred full Paper2 statement target from `section2` and `localAndMain`. |
| `IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData.toTerminalEndpoint` | wiring | Packages `rawMoserDrop` into `MoserDissipationDropBeforeNonnegB` and forwards relative/terminal fields. |
| `IntervalDomainPaper2Prop25ActualAtomMassGradientTerminalEndpointFrontierData.toMassGradient` | wiring | Converts terminal endpoint to `pSeq/rootBound` endpoint via constant sequences. |
| `IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData.toActualAtoms` | wiring | Converts mass-gradient relative data to `RelativeMoserInterpolationBefore`. |
| `intervalDomainPaper2_Proposition_2_5_of_actualAtomRawDropMassGradientTerminalEndpointFrontierData` | wiring over atoms | Produces Prop. 2.5 once the three actual atoms are supplied. |
| `intervalDomainPaper2_Corollary_2_1_of_actualAtomRawDropMassGradientTerminalEndpointFrontierData` | wiring over atoms | Produces Cor. 2.1 once the same actual atoms are supplied. |
| `intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData` | wiring over branch frontiers | Main theorem 1.2/1.3 assembly; local existence is already the proved `χ₀ = 0` producer in this route. |
| `intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData` | wiring | Adds proved Theorem 1.1 to the local-free 1.2/1.3 result. |
| `IntervalDomainPaper3Stability24ActualLinearFrontierData.toStability23To25` | wiring | In actual-linear-small (`0 < a`, `0 < χ₀`) the Theorem 2.3 branches are false by `0 < χ₀`, and Theorem 2.5 branches are false by `0 < a`; only Theorem 2.4 fields remain. |
| `IntervalDomainPaper3MainlineActualLinear22ThinFrontierData.toCurrent` | wiring | Builds the current Paper3 mainline surface from thin actual-linear data. |
| `intervalDomain_paper3_Theorem_2_1_of_actualLinearSmall`, `intervalDomain_paper3_Theorem_2_1_partTargets_of_actualLinearSmall`, `intervalDomain_paper3_Theorem_2_1_sectorial_of_actualLinearSmall` | closed/wiring | Persistence is already produced internally by `intervalDomain_sectorialTheorem21Persistence_actualLinearSmall`. |

A useful accounting change: older names carrying `agmon : UnitIntervalPositiveAgmonInterpolation` should be treated as compatibility wrappers, not as headline routes. The preferred Paper2 route is now the proved-Agmon one.

## 2. Genuine analytic residuals and ownership

### Paper2 residuals

| Residual | Exact names | Owner / file family to attack |
|---|---|---|
| Thin section-2 estimate package | `IntervalDomainPaper2BootstrapEstimateThinFrontierData.lemma26`, `.lemma27`, `.prop22`, `.prop23` | Paper2 estimate/PDE side; likely non-Zinan. Candidate files around `IntervalDomainLpBootstrapEnergyInequality`, `IntervalDomainLpMonotonicity`, resolver/signal estimate files. This is not Agmon anymore. |
| Finite-horizon alternative | `IntervalDomainPaper2Proposition11ChiZeroFrontierData.finiteHorizonAlternative` | Paper2 existence/continuation side; non-Zinan unless someone owns the continuation package separately. Candidate files around `IntervalDomainExistence`, `IntervalDomainTheorem11Umbrella`, `IntervalDomainTheorem11ChiZeroUnconditional`. |
| Global extension / continuation | `IntervalDomainPaper2GlobalExtensionFrontier p` | Paper2 continuation/globalization. Candidate files around `IntervalDomainTheorem11*`, `IntervalDomainAPrioriGlobal`, `IntervalDomainMoserLadderAtoms`. |
| Raw physical Moser drop | `IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData.rawMoserDrop` | Moser energy/dissipation side. Candidate non-Zinan files: `P3MoserDissipationShape.lean`, `P3MoserLemmaDischarge.lean`, `P3MoserLemmas.lean`. Do not push this into Zinan files unless Zinan elects to. |
| Relative mass-gradient package | `IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData.relativeMassGradient` | Moser lemma/algebra side; non-Zinan candidate files `P3MoserLemmas.lean`, `P3MoserLemmaDischarge.lean`, existing interval mass-gradient estimate files. Agmon is no longer the blocker. |
| Terminal Moser endpoint | `IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData.terminalEndpoint` | Genuine Moser endpoint / root-tower / high-excursion residual. If the proof route goes through `P3MoserHighExcursionProducer.lean` or `P3MoserThresholdPlanProducer.lean`, it is Zinan-owned. Non-Zinan work should only adjust wrappers around it, not the producer files. |
| Branch bootstrap seeds | `slowBootstrap`, `criticalBootstrap`, `strongBootstrap` fields in the `IntervalDomainPaper2Theorem12And13*` and preferred `ChiZero...` packages | Paper2/PDE bootstrap side. These are real estimates producing `IntervalDomainPaper2BootstrapOutput p T u v`. Candidate files: `IntervalDomainTheorem12.lean`, `IntervalDomainAPrioriGlobal.lean`, `IntervalDomainMoserLadderAtoms.lean`; if they call high-excursion producers, hand that subgoal to Zinan. |
| Long-time/eventual sup bounds | `criticalEventualSupBound`, `strongEventualSupBound` | Paper2 global boundedness / long-time PDE side. Candidate files: `IntervalDomainAPrioriGlobal.lean`, `IntervalDomainMoserLadderAtoms.lean`, theorem 1.2/1.3 assembly files. |

### Paper3 residuals

| Residual | Exact names | Owner / file family to attack |
|---|---|---|
| Negative sensitivity global eventual bound | `NegativeSensitivityGlobalEventualBound intervalDomain p`, `IntervalDomainPaper3NegativeSensitivityFrontierData.globalSolution`, `.eventualSupBound` | Paper3/Paper2 global negative-sensitivity side. In actual-linear-small routes with `0 < p.χ₀`, this should be discharged by contradiction rather than carried. See the edit below. |
| Initial continuity for stability norm | `IntervalDomainInitialContinuityRaw p` | Paper3 stability/initial-continuity side; candidate files around `IntervalDomainStatementAssembly.lean`, `IntervalDomainStabilityChain.lean`. |
| Raw linear Theorem 2.2 branches | `LinearStabilityInstabilityNonminimalRaw ...`, `LinearStabilityInstabilityMinimalRaw ...` in `IntervalDomainPaper3CoreStatementActualLinear22Data` | Paper3 linear stability/sectorial owner. Candidate files around `IntervalDomainPersistenceActualLinearSectorial.lean`, `IntervalDomainSectorialNonlinearBridges.lean`. |
| Compactness | `IntervalDomainPaper3SupNormCompactnessAPosData.compact : TimeTranslateCompactnessRaw ...` | Paper3 compactness/regularization owner. Candidate files around `IntervalDomainStatementAssembly.lean`, sectorial compactness files. |
| Resolvent gradient bound | `IntervalDomainPaper3SupNormCompactnessAPosData.resolvent : NeumannResolventGradientBoundExistsRaw ...` | Paper3 elliptic/sectorial support. |
| Nonminimal stability/convergence | `IntervalDomainPaper3Stability24ActualLinearFrontierData.global24`, `.exp24` | Paper3 stability owner. These are the non-vacuous actual-linear Theorem 2.4 frontiers. |

Important parameter note: do **not** try to feed the Paper2 `χ₀ = 0` proved-Agmon statement route directly into the actual-linear-small Paper3 route, because the latter assumes `0 < p.χ₀`. The proved-Agmon closure is a Paper2 `χ₀ = 0` headline simplification. The Paper3 actual-linear-small route should instead eliminate negative-sensitivity fields by contradiction from `0 < p.χ₀` and continue to carry same-parameter Paper2 main targets only when those are available from a positive-sensitivity Paper2 route.

## 3. Concrete next Lean edit for Codex, low-conflict and non-Zinan

Best next edit: remove the unnecessary Paper3 negative-sensitivity assumption from the actual-linear-small `0 < χ₀` statement route.

Why this is low-conflict:

* It touches only `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`.
* It uses pure logic: `NegativeSensitivityGlobalEventualBound` is vacuous under `0 < p.χ₀` because its first argument is `p.χ₀ ≤ 0`.
* It avoids all Zinan-owned Moser producer files.
* It reduces Paper3 headline assumptions immediately: `IntervalDomainPaper3StatementActualLinear22ThinP2MainData` currently carries `propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C`, whose first field is `negativeBound`; the new wrapper should carry only `paper2Main` plus `mainline`.

Suggested code:

```lean
import ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly

open ShenWork.IntervalDomain
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- In the actual-linear-small regime `0 < χ₀`, the negative-sensitivity
Proposition 1.2 hypothesis is vacuous. -/
theorem intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
    (p : CM2Params) (hχ0 : 0 < p.χ₀) :
    NegativeSensitivityGlobalEventualBound intervalDomain p := by
  intro hχ_nonpos _hm _u₀ _hu₀
  exact False.elim (not_le_of_gt hχ0 hχ_nonpos)

/-- Full Paper3 statement frontiers in the actual-linear-small regime, with
Paper3 Proposition 1.2 discharged by `0 < χ₀`, and Proposition 1.3/1.4 routed
through supplied Paper2 main theorem targets. -/
structure IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineActualLinear22ThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound

/-- Actual-linear-small Paper3 statement target from Paper2 main theorem targets
without carrying a separate negative-sensitivity residual. -/
theorem intervalDomain_paper3_statementTargets_of_actualLinear22ThinP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData
        p C M0 uBar vLower locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_statementTargets_of_actualLinear22ThinP2MainData
    p C M0 uBar vLower locallyConverges neumannResolventGradientBound
    ha hb hχ0 hm hβ hχ
    { propositions :=
        { negativeBound :=
            intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
              p hχ0
          paper2Main := hData.paper2Main }
      mainline := hData.mainline }

end

end ShenWork.Paper3
```

Optional follow-up in the same file: add the `Fact` wrapper mirroring nearby style.

```lean
theorem intervalDomain_paper3_statementTargets_of_actualLinear22ThinP2MainNoNegDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData
        p C M0 uBar vLower locallyConverges neumannResolventGradientBound)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_statementTargets_of_actualLinear22ThinP2MainNoNegData
    p C M0 uBar vLower locallyConverges neumannResolventGradientBound
    ha hb hχ0 hm hβ hχ hData.out
```

Expected imports: none if appended to `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`; otherwise import that file.

## Secondary non-Zinan edit candidate

If Codex wants a Paper2-only edit instead, add extractor wrappers from the preferred proved-Agmon full-statement data to the already nested local/main and main theorem targets. This does not close analytic residuals, but it improves downstream reuse and prevents consumers from carrying both a full statement package and a separate Paper2 main package.

```lean
theorem
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData
  (p : CM2Params) (C : Paper2Constants p)
  (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
  (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
  (hData :
    IntervalDomainPaper2StatementChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinProvedAgmonFrontierData
      p C) :
  IntervalDomainPaper2MainTheoremTargets p C :=
  (intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21FrontierData
    p C hχ0 ha hb hα hγ hData.localAndMain).2
```

This is less assumption-reducing than the Paper3 vacuity edit, but it is also low-risk and purely structural.

## Bottom line

After Agmon closure, the preferred Paper2 `χ₀ = 0` full-statement surface has only two real fields left at the top:

```lean
section2 : IntervalDomainPaper2BootstrapEstimateThinFrontierData p
localAndMain :
  IntervalDomainPaper2LocalAndMainChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21FrontierData p C
```

Unfolding `localAndMain`, the hard content is now exactly continuation/global extension, branch bootstrap/eventual sup bounds, and the raw-drop/mass-gradient/terminal-endpoint Moser atoms. Paper3 still has independent stability/compactness/linear frontiers, but in the actual-linear-small positive-χ route the negative-sensitivity Proposition 1.2 residual should be eliminated immediately by the small non-Zinan wrapper above.
