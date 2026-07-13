ANSWER Q4579 65560949

# Paper 1 Theorem 1.1: exact frontiers and the minimal Green–Rothe closure route

Audit target: `chatgpt-scratch`, chiefly

- `ShenWork/Paper1/Statements.lean`
- `ShenWork/Paper1/StationaryUpperTail.lean`
- `ShenWork/Paper1/WaveRothePos.lean`
- `ShenWork/Paper1/WaveRotheDep.lean`
- `ShenWork/Paper1/WaveRotheSchauderData.lean`
- `ShenWork/Paper1/WaveRotheResidualClose.lean`
- `ShenWork/Paper1/WaveFrozenEllipticDep.lean`

## Bottom line

1. The two requested `Theorem_1_1` theorems are **pure statement-layer adapters**. They contain no Rothe analysis. Their hypotheses are the full branch constructions.
2. The `_trap_branches` theorem weakens only one negative-branch field: it replaces the carried proof `∀ x, deriv U x ≤ 0` by `InMonotoneWaveTrapSet (kappa c) 1 U`, then obtains the derivative sign mechanically as `htrap.deriv_nonpos`.
3. At the current Rothe boundary, **fixed-profile orbit compactness is already closed**: equi-Lipschitz estimates, local-uniform convergence to `rotheLimit`, Helly selection, and compactness of the map range are all proved and wireable.
4. `frozenEllipticDerivDependence` is also now proved. Comments in older files that call it uncommitted are stale.
5. The remaining Q4382 orbit block is exactly the passage from the canonical Green implicit step to:
   - `RotheSeqStepDependence`; and
   - a family-uniform tail at the outer Rothe index, currently exposed as `RotheTailUniform`.
6. The single genuine hard core for that block should be formalized as a **parameterized Green-step compact closed-graph theorem, including the moving-index (`kₙ → ∞`) case**. Finite-index induction then gives `RotheSeqStepDependence`; the moving-index compactness argument gives the needed tail. This is a Green-kernel/local-uniform proof, not Minty and not an Aubin–Lions-only argument.
7. For the smallest Lean surface, do **not** first prove the present globally quantified `RotheTailUniform` unless a uniform outer convergence rate is available. It is stronger than continuity of `Tmap` needs. Introduce a tail uniform only along one locally-uniformly convergent family, and reuse the existing ε/3 proof with a tiny adapter.

---

## 1. Exact carried frontier of `of_assumed_frozenStationaryProfile_branches`

The exact theorem in `Statements.lean` is:

```lean
theorem Theorem_1_1.of_assumed_frozenStationaryProfile_branches
    (hneg :
      ∀ p : CMParams, p.α ≤ p.m + p.γ - 1 → p.χ ≤ 0 →
        ∀ c : ℝ, cStarLower p < c →
          ∃ U : ℝ → ℝ,
            FrozenStationaryWaveProfile p c U ∧
              (∀ x, deriv U x ≤ 0) ∧
              (∀ x, deriv (frozenElliptic p U) x ≤ 0) ∧
              ShenUpperBoundNegative c U ∧
              ∀ κ₁, kappa c < κ₁ →
                κ₁ <
                  min ((1 + p.α) * kappa c)
                    (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U)
    (hpos :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∃ U : ℝ → ℝ,
            FrozenStationaryWaveProfile p c U ∧
              ShenUpperBoundPositive p c U ∧
              ∀ κ₁, kappa c < κ₁ →
                κ₁ <
                  min ((1 + p.α) * kappa c)
                    (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U) :
    Theorem_1_1
```

Its proof merely sets `V := frozenElliptic p U` and calls:

```lean
hprofile.to_monotoneTravelingWave hUmono hVmono
hprofile.to_travelingWave
```

Thus the theorem itself is entirely mechanical.

### Negative branch: item-by-item classification

| Carried item | Status | Minimal current route |
|---|---|---|
| `FrozenStationaryWaveProfile p c U` | **Genuine hard construction at source**, but much of the bundle is mechanical once a trapped fixed point exists | Rothe producer → Schauder fixed point → stationarity/floor/root-pin wrappers. The raw bridge shows the underlying fields are `0 < c`, `U > 0`, `IsCUnifBdd U`, `frozenWaveOperator p c U U = 0`, and the two endpoint limits. |
| `∀ x, deriv U x ≤ 0` | **Mechanical if trap membership is retained** | `InMonotoneWaveTrapSet.deriv_nonpos`; exposed as `constructionNeg_hUmono`. |
| `∀ x, deriv (frozenElliptic p U) x ≤ 0` | **Already proved and mechanical from the monotone trap** | `frozenElliptic_deriv_nonpos_of_monotone_trap`; wrapper `constructionNeg_hVmono`. |
| `ShenUpperBoundNegative c U` | Mostly mechanical; one real strictness/SMP atom remains | `ShenUpperBoundNegative_of_strictAtZero`, or `ShenUpperBoundNegative_of_stationary_strongMaxPrinciple`. The substantive scalar is `U 0 < 1`; positivity and the strict bound away from zero come from the trap. |
| Right-tail family | **Mechanical if the lower pin survives with a covering exponent; hard if only bare stationarity/trap is retained** | `lowerPinnedMonotoneTrap_tail_family_for_branch` or `lowerPinnedRawMonotoneTrap_tail_family_for_branch`. The current identity theorem `HasWaveRightTailAsymptotic_of_stationary` does not prove the tail; it merely carries it. |

The lower-pin route needs the exact scalar cover

```lean
min ((1 + p.α) * kappa c)
  (min (p.m * kappa c + 1 / 2) 1) ≤ κtilde
```

plus `0 ≤ D`. Once those are present, the whole family of `κ₁`-tails is discharged by squeeze, not by a new asymptotic linearization proof.

### Positive branch: item-by-item classification

| Carried item | Status | Minimal current route |
|---|---|---|
| `FrozenStationaryWaveProfile p c U` | **Genuine hard Rothe/Schauder source construction** | Positive super-barrier + common sign-agnostic Rothe machinery in `WaveRothePos.lean`; current strongest clean wrappers include `b1_chiPos_existence_profileClean_stationary_floor_rootPin`. |
| `ShenUpperBoundPositive p c U` | **Genuine maximum-principle/contact analysis**, although most bookkeeping is already closed | First prove strict comparison with `upperBarrier (kappa c) (MChi p)`, then use `ShenUpperBoundPositive.of_pos_strict_upperBarrier_MChi`. `UpperBarrierContact.lean` closes the nonsmooth interface and the constant branch under the stated hypotheses, and reduces the remaining issue to the exponential-contact strict-superbarrier residual. On the `p.m * kappa c ≤ 1` positive-region subregime, `PositiveUpperBarrierContactContradictions.of_profile_chi_pos_hmk_regularStationary` closes it. |
| Right-tail family | **Mechanical on the present lower-pinned Route-A output** | Choose/preserve `κtilde ≥ positiveBranchTailCap p c`; use `lowerPinnedRawMonotoneTrap_tail_family_for_branch`. `positiveBranchTailCap` and `kappa_lt_positiveBranchTailCap` are already proved. |

So the positive right tail is no longer a reason to abandon the lower-pinned Route-A construction. The independently hard positive branch atom is upper-barrier no-contact, not the tail squeeze.

---

## 2. Exact carried frontier of `of_assumed_frozenStationaryProfile_trap_branches`

The exact theorem is:

```lean
theorem Theorem_1_1.of_assumed_frozenStationaryProfile_trap_branches
    (hneg :
      ∀ p : CMParams, p.α ≤ p.m + p.γ - 1 → p.χ ≤ 0 →
        ∀ c : ℝ, cStarLower p < c →
          ∃ U : ℝ → ℝ,
            InMonotoneWaveTrapSet (kappa c) 1 U ∧
              FrozenStationaryWaveProfile p c U ∧
              (∀ x, deriv (frozenElliptic p U) x ≤ 0) ∧
              ShenUpperBoundNegative c U ∧
              ∀ κ₁, kappa c < κ₁ →
                κ₁ <
                  min ((1 + p.α) * kappa c)
                    (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U)
    (hpos :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∃ U : ℝ → ℝ,
            FrozenStationaryWaveProfile p c U ∧
              ShenUpperBoundPositive p c U ∧
              ∀ κ₁, kappa c < κ₁ →
                κ₁ <
                  min ((1 + p.α) * kappa c)
                    (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U) :
    Theorem_1_1
```

The entire difference from the first theorem is this one proof term:

```lean
htrap.deriv_nonpos
```

The positive branch is literally unchanged. Therefore:

- `_trap_branches` is the better final entry point for the negative construction;
- carrying a separate `∀ x, deriv U x ≤ 0` hypothesis upstream is redundant;
- it still carries `deriv (frozenElliptic p U) ≤ 0`, though that too is already derivable from the same trap by `constructionNeg_hVmono`.

A still thinner negative headline adapter could accept only

```lean
InMonotoneWaveTrapSet (kappa c) 1 U
FrozenStationaryWaveProfile p c U
ShenUpperBoundNegative c U
right-tail family
```

and produce both derivative-sign fields internally. That would be a small mechanical cleanup, not new mathematics.

---

## 3. The exact current Rothe boundary in `WaveRothePos.lean`

The clean positive existence wrappers still visibly carry three Rothe-side blocks:

```lean
hcoreAll : ∀ v, RotheFloorResidualCore p c lam M κ Λ v

hstep : RotheSeqStepDependence p c lam M κ Λ hprodTrap hκ hM

htail : RotheTailUniform p c lam M κ Λ hprodTrap hκ hM
```

where the producer is assembled by

```lean
RotheFloorResidualCore
  -> rotheFloorResidual_of_core
  -> rotheStepFloor_of_residual
  -> rotheStepProducer_of_floor
```

and the orbit is

```lean
rotheSeqFromTrap p c lam M κ Λ hprodTrap hκ hM
```

The newer, smaller per-profile source boundary is actually

```lean
RotheFloorResidualCoreSlim p c lam M κ Λ v
```

with adapter

```lean
rotheFloorResidual_of_slimCore
```

`RotheFloorResidualCoreSlim.produceCore` still carries the genuinely nontrivial per-step Green data:

- `W = greenConv c lam R` and the raw integral representation;
- continuity and a uniform bound for `R`;
- `RotheSlimSourceAntitone R`;
- the differential implicit-step identity;
- nonnegativity and the fixed-point identity `W = crossImplicitMap ... W`;
- the contraction/smallness scalar;
- `RotheSlimEndpointAsymptotics`;
- the `Z`-at-maximum `C²` and range facts;
- `RotheStepAntitoneData` and the two `RotheStepChemData` packets.

The slim adapter already fills the mechanical/committed fields:

- weighted source tails;
- translated Green-kernel integrability;
- continuity of `W - Z` and `W - upperBarrier`;
- the upper-barrier `C²`-at-maximum field;
- the super-solution/order bookkeeping.

For a minimal new implementation, add a positive slim builder rather than continuing to supply the old full core:

```lean
def rotheFloorResidual_of_trap_pos_slim
    ...
    (hcore : RotheFloorResidualCoreSlim p c lam M κ Λ u) :
    RotheFloorResidual p c lam M κ Λ u :=
  rotheFloorResidual_of_slimCore
    (whole_line_super_barrier_pos ...) hκ hMpos hcore
```

The corresponding negative builder uses `whole_line_super_barrier`. This adapter is mechanical.

---

## 4. What orbit compactness is already proved

The phrase “Rothe orbit compactness” should not be treated as one wholly missing theorem. Most of it is already in the repository.

### Fixed frozen profile

From a `RotheStepProducer`, the following chain is available:

```text
rotheSeqOf / rotheSeqFromTrap
  -> rotheSeqOf_* per-step facts
  -> crossImplicitStep_lipschitz
  -> equi-Lipschitz orbit
  -> rotheLimit_locallyUniform
  -> rotheLimit_continuous
```

The key names are:

- `crossImplicitStep_lipschitz`
- `locallyUniform_of_pointwise_of_equiLipschitz`
- `rotheLimit_locallyUniform`
- `rotheLimit_continuous`
- `rotheOrbitData_fromTrap`
- `RotheOrbitData.locallyUniform`
- `RotheOrbitData.limit_continuous`

This is already axiom-clean wiring.

### Compact range of the Rothe map

The map is

```lean
Tmap u := rotheLimit (rotheSeq u)
```

The compact-range field is already assembled by:

```text
helly_pointwise_selection M
  -> locallyUniform_of_helly_pointwise
  -> Tmap_compactRange
```

with final packaging in

```lean
rotheSchauderData
rotheSchauderData_lowerPinned
```

`helly_pointwise_selection` is proved in `WaveRotheHelly.lean`; it is no longer an open combinatorial frontier.

### Frozen elliptic dependence

The old comments in `WaveRotheSchauderData.lean` say `FrozenEllipticDerivDependence` is uncommitted. That is no longer true. The exact public theorem is:

```lean
theorem frozenEllipticDerivDependence
    (p : CMParams) {κ M : ℝ} (hM : 0 ≤ M) :
    FrozenEllipticDerivDependence p (InMonotoneWaveTrapSet κ M)
```

Its proof already implements the correct whole-line Green-kernel argument:

```text
frozenElliptic_deriv_eq_kernel_integral
  -> frozenElliptic_deriv_diff_abs_le
  -> deriv_diff_integral_split_le
  -> frozenEllipticDerivDependence
```

The split is local-uniform on `[-R',R']` plus exponential kernel tails outside. This is exactly the pattern the Rothe step should mirror.

### The final ε/3 assembly

Once the two currently named inputs exist, the rest is done:

```text
RotheSeqStepDependence + RotheTailUniform
  -> rotheLimit_dep_of_step_and_tail
  -> rotheContinuousDependence
  -> Tmap_continuousOn
  -> rotheSchauderData
```

No new analysis belongs after `hstep` and `htail`.

---

## 5. Exact open orbit hypotheses

### `RotheSeqStepDependence`

This says that for a locally-uniformly convergent trapped family `seq n -> u`, every fixed outer Rothe iterate converges locally uniformly:

```lean
∀ k,
  LocallyUniformConverges
    (fun n => rotheSeqOf ... (seq n) ... k)
    (rotheSeqOf ... u ... k)
```

Why it is not currently automatic: `rotheSeqOf` is constructed with independent `Classical.choose` calls from an existence-only producer. Without uniqueness/identification, the chosen step for `seq n` and the chosen step for `u` need not be related by the API.

The analytic route is nevertheless clear:

1. identify the chosen `RotheStepFacts` solution with the canonical Green fixed point;
2. use `crossStep_concrete_unique` to remove choice dependence;
3. prove local-uniform closedness of the Green step under convergence of `u`, `Z`, and `V'_u`;
4. induct on the fixed Rothe index `k`.

The already proved inputs include:

- `crossStep_concrete_solution`
- `crossStep_concrete_unique`
- `greenKernel_l1_eq`
- `greenKernel_smallness_iff`
- `frozenEllipticDerivDependence`
- `rothe_fluxIntegral_tendsto`
- the source/reaction Lipschitz constants and trap bounds.

### `RotheTailUniform`

The current definition is global:

```lean
∀ R > 0, ∀ ε > 0,
  ∃ K, ∀ v, trap v -> ∀ k ≥ K, ∀ x ∈ Icc (-R) R,
    |rotheSeqOf ... v ... k x - rotheLimit (...) x| < ε
```

This is substantially stronger than the per-profile theorem `rotheLimit_locallyUniform`. It is also stronger than what is logically required to prove sequential continuity of `Tmap`: for a given proof of continuity, one only needs a common `K` for the compact/convergent family `{seq n} ∪ {u}`.

There is no visible committed uniform outer contraction rate in `k`. The Banach contraction used to solve the **inner** Green fixed-point equation for one implicit step does not by itself imply geometric convergence of the **outer** Rothe iteration. Therefore a proof of the global `RotheTailUniform` cannot honestly be called mechanical.

---

## 6. Minimal new Green theorem

### Recommended smaller API

Introduce the tail actually needed by `RotheContinuousDependence`:

```lean
def RotheTailUniformAlongConvergentSeq
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hprodTrap : ∀ v, InMonotoneWaveTrapSet κ M v ->
      RotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Prop :=
  ∀ (seq : ℕ -> ℝ -> ℝ) (u : ℝ -> ℝ),
    (hseq : ∀ n, InMonotoneWaveTrapSet κ M (seq n)) ->
    (hu : InMonotoneWaveTrapSet κ M u) ->
    LocallyUniformConverges seq u ->
    ∀ R > 0, ∀ ε > 0,
      ∃ K, (∀ n, ∀ k ≥ K, ∀ x ∈ Set.Icc (-R) R,
        |rotheSeqOf p c lam M κ Λ (seq n)
            (hprodTrap (seq n) (hseq n)) hκ hM k x -
          rotheLimit (rotheSeqOf p c lam M κ Λ (seq n)
            (hprodTrap (seq n) (hseq n)) hκ hM) x| < ε) ∧
        (∀ k ≥ K, ∀ x ∈ Set.Icc (-R) R,
          |rotheSeqOf p c lam M κ Λ u
              (hprodTrap u hu) hκ hM k x -
            rotheLimit (rotheSeqOf p c lam M κ Λ u
              (hprodTrap u hu) hκ hM) x| < ε)
```

Then add

```lean
theorem rotheLimit_dep_of_step_and_tailAlong ...
```

by copying the existing proof of `rotheLimit_dep_of_step_and_tail`; only the call site for the common cutoff changes. This adapter is mechanical.

### The single genuine hard theorem

The mathematical core should be one theorem returning both finite-index stability and the sequence-local moving-index tail:

```lean
theorem greenRothe_stepDependence_and_tailAlong
    (hslim : ∀ v, InMonotoneWaveTrapSet κ M v ->
      RotheFloorResidualCoreSlim p c lam M κ Λ v)
    (hside : GreenRotheUniformSideConditions p c lam M κ Λ) :
    let hprodTrap :=
      rotheStepProducer_of_floor
        (fun v hv => rotheStepFloor_of_residual
          (rotheFloorResidual_of_slimCore
            (hside.superBarrier v hv) hside.hκ hside.hMpos
            (hslim v hv)))
    RotheSeqStepDependence p c lam M κ Λ hprodTrap hside.hκ.le hside.hM ∧
    RotheTailUniformAlongConvergentSeq
      p c lam M κ Λ hprodTrap hside.hκ.le hside.hM
```

`GreenRotheUniformSideConditions` is just a suggested small record for the already recurring scalar bounds; it need not contain analysis.

The proof should center on one reusable closed-graph lemma:

```lean
theorem greenImplicitStep_locallyUniform_closedGraph
    (hu : LocallyUniformConverges uSeq u)
    (hZ : LocallyUniformConverges ZSeq Z)
    (hV : LocallyUniformConverges
      (fun n => deriv (frozenElliptic p (uSeq n)))
      (deriv (frozenElliptic p u)))
    (hsteps : ∀ n, GreenImplicitStepGraph p c lam (uSeq n) (ZSeq n) (WSeq n))
    (hstep : GreenImplicitStepGraph p c lam u Z W)
    (huniq : GreenImplicitStepUnique p c lam ...) :
    LocallyUniformConverges WSeq W
```

The precise graph predicate can be built directly from the fields already present in `RotheFloorResidualCoreSlim` rather than inventing a second mathematical definition.

### Proof architecture of the hard core

1. **Canonicalize the selected step.** Use `crossStep_concrete_unique` to show that any `Classical.choose` witness satisfying the current step facts equals the unique Green fixed point. After this lemma, choice is no longer an obstacle.
2. **Local Green convergence.** Split every whole-line convolution into `[-R',R']` and its complement. On the inner interval use local-uniform convergence and the power/reaction Lipschitz estimates. On the complement use the exponential Green-kernel tails and uniform trap bounds. This is the same architecture already formalized in `frozenEllipticDerivDependence`.
3. **Fixed-index induction.** Base index is the common `upperBarrier`. The closed-graph step proves index `k+1` from index `k`, yielding `RotheSeqStepDependence`.
4. **Moving-index compactness.** To obtain the tail along a convergent family, argue by contradiction. From bad `n_j`, `k_j -> ∞`, and `x_j ∈ [-R,R]`:
   - extract local-uniform subsequences of the orbit states using the existing uniform Lipschitz bounds and `helly_pointwise_selection`/finite-grid upgrade;
   - diagonalize over each fixed Rothe index;
   - pass every Green step through the closed graph;
   - use antitonicity in `k`, lower boundedness, and uniqueness/identification of the selected limit to show the moving-index limit is the same `rotheLimit`;
   - contradict the retained `ε` gap.
5. Feed the resulting pair into the existing ε/3 theorem (or its `tailAlong` refactor).

That is the Q4382 route: Green-kernel tail splitting + locally-uniform compactness + closed graph. No Minty argument appears, because the frozen chemotaxis coupling is not a monotone operator in the required variables. Aubin–Lions is also unnecessary for this whole-line stationary Green formulation; it would solve a different time-dependent compactness problem and still leave the spatial Green tails and choice/closed-graph identification.

### If the existing global `RotheTailUniform` API must be kept

Then one additional genuinely strong input is required:

- either a uniform rate

```lean
∃ omega : ℕ -> ℝ,
  Tendsto omega atTop (𝓝 0) ∧
  ∀ v hv k x,
    |rotheSeqOf ... v ... k x - rotheLimit (...) x| ≤ omega k
```

- or compactness of the entire parameterized orbit graph strong enough to run a global Dini argument over all trapped profiles.

The current trap alone is not visibly a compact parameter space, and the repository does not currently expose a uniform outer rate. Therefore the sequence-local tail is the safer minimal theorem.

---

## 7. Complete lemma DAG to the headline

### Common Green/Rothe core

```text
RotheFloorResidualCoreSlim (new producer proof)
  + positive: whole_line_super_barrier_pos
  + negative: whole_line_super_barrier
    -> rotheFloorResidual_of_slimCore
    -> rotheStepFloor_of_residual
    -> rotheStepProducer_of_floor
    -> rotheSeqFromTrap
```

### Fixed-profile orbit and compact range — already proved

```text
rotheStepProducer_of_floor
  -> rotheOrbitData_fromTrap
     using:
       crossImplicitStep_lipschitz
       frozenElliptic_deriv_continuous_trap
       uniform V' bound
  -> RotheOrbitData.locallyUniform
  -> RotheOrbitData.limit_continuous

helly_pointwise_selection M
  + RotheOrbitData.limitLip / limit bounds
  -> locallyUniform_of_helly_pointwise
  -> Tmap_compactRange
```

### Parameter continuity — one hard Green closed-graph module

```text
frozenEllipticDerivDependence                 [PROVED]
  + crossStep_concrete_unique                 [PROVED]
  + Green kernel L1/tail estimates            [PROVED]
  + canonical chosen-step identification      [small but essential adapter]
  + greenImplicitStep_locallyUniform_closedGraph   [HARD CORE]
    -> RotheSeqStepDependence
    -> sequence-local moving-index tail
    -> rotheLimit_dep_of_step_and_tailAlong
    -> RotheContinuousDependence
    -> Tmap_continuousOn
```

If retaining the current stronger API, replace the sequence-local line by a proof of `RotheTailUniform`, then use the already existing:

```text
RotheSeqStepDependence + RotheTailUniform
  -> rotheLimit_dep_of_step_and_tail
  -> rotheContinuousDependence
```

### Schauder/profile assembly — largely wireable

```text
Tmap_maps_trap
Tmap_crossDiagonal
Tmap_continuousOn
Tmap_compactRange
  -> rotheSchauderData
  -> rotheSchauderData_lowerPinned

ProjectedCubeApproxData / branch-specific cube data
  -> localUniformApproxFixedPointSequence_of_schauderProjectionData
  -> localUniformFixedPoint_of_schauderProjectionData
```

The branch files already expose `_of_cubeApproxData` entry points, so there is no reason to re-prove abstract Schauder.

Then:

```text
positive:
  b1_chiPos_existence_profileClean_stationary_floor_rootPin
  + raw lower pin at positiveBranchTailCap
    -> lowerPinnedRawMonotoneTrap_tail_family_for_branch
  + positive upper contact package
    -> hpos

negative:
  lower-pinned Rothe/Schauder profile
  -> constructionNeg_hUmono
  -> constructionNeg_hVmono
  + U 0 < 1
    -> ShenUpperBoundNegative_of_stationary_strongMaxPrinciple
  + lower-pin exponent cover
    -> lowerPinnedMonotoneTrap_tail_family_for_branch
  -> hneg

hneg + hpos
  -> Theorem_1_1.of_assumed_frozenStationaryProfile_trap_branches
  -> Theorem_1_1
```

---

## 8. What remains genuinely hard outside the Q4382 orbit block

It is important not to overstate “one hard lemma” for the entire headline.

For the **orbit compactness/continuous-dependence block**, the single hard core is the parameterized Green-step closed graph with the moving-index compactness/tail identification.

For a completely unconditional `Theorem_1_1`, there are still independent branch-facing analytic obligations unless their current specialized providers are used:

1. the producer for `RotheFloorResidualCoreSlim` (per-step whole-line Green/max-principle data), if not already supplied by a Route-A param-core package;
2. negative strictness `U 0 < 1` for the stationary fixed point;
3. positive upper-barrier no-contact outside the already closed `p.m * kappa c ≤ 1` subroute.

The sharp right-tail family is **not** an independent hard atom once the lower pin is preserved with the covering exponent.

## Honest verdict

- The requested headline adapters: mechanical, already complete.
- Fixed-profile Rothe compactness and map-range compactness: already complete and wireable.
- Frozen elliptic dependence: already complete and wireable.
- The ε/3 passage from step + tail to map continuity: already complete.
- The current genuine orbit blocker: one substantial Green compact-closed-graph proof, not a collection of small rewrites.
- Best Lean implementation: one dedicated file proving canonical step identification, local Green closedness, fixed-index dependence, and moving-index tail along convergent families; then a short adapter into the existing `rotheContinuousDependence`/Schauder DAG.
