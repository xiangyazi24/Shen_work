# P1 discharge distance audit — `Paper1MainResultsData`

Repo: `xiangyazi24/Shen_work`  
Branch: `main`  
Audited HEAD: `103c3b20378d5c282d4b6660633fe0cff5aed60b`  
Report commits: initial `296dc66ee304f1eb7efded4d1b64c85b43174666`; corrected `THIS_COMMIT`

## Scope note

The user-facing question names four core fields of `Paper1MainResultsData`:

- `construction_neg`
- `construction_pos`
- `cStarStar_spec`
- `stability`

The actual structure in `ShenWork/Paper1/Statements.lean` also contains four auxiliary fields used for Theorems 1.2/1.3 (`wave_cont`, `cauchy_unique`, `resolvent`, `tail_asymp`). This audit maps the four requested core fields only. No producer for the full `Paper1MainResultsData` bundle was found; the only direct uses are the statement wrappers in `StatementAssembly.lean`.

## Summary table

| Field | Already discharged? | Status | Satisfiable? | Main missing theorem / fix |
|---|---:|---:|---:|---|
| `construction_neg` | No; carried through the bundle | 🟡 partial | Yes | A completed negative-branch construction producer assembling Rothe/Schauder fixed point, stationary equation, strict bounds, and sharp right-tail asymptotic |
| `construction_pos` | No; carried through the bundle | 🟡 partial | Yes | Same construction producer under the positive-sign super-barrier regime |
| `cStarStar_spec` | No landed producer found | 🟥 over-strong as typed | No, if the stable regime includes `χ=0, γ=1` | Refactor the strict baseline field at `χ=0` (`≤`, or exclude `χ=0`, or asymptotic punctured at 0 with explicit positive offset) |
| `stability` | No; carried | 🔨 open | Yes | Full weighted orbital stability theorem for the nonlinear Cauchy problem |

## 1. `construction_neg`

### What the field requires

`construction_neg` asks, for `α ≤ m+γ-1`, `χ≤0`, and `cStarLower p < c`, for a frozen stationary wave profile with monotone `U`, monotone elliptic field, `ShenUpperBoundNegative`, and the full right-tail asymptotic family.

### Landed pieces

- `paper1_Theorem_1_1_of_mainResultsData` is only a wrapper from `Paper1MainResultsData` to `Theorem_1_1`; it does not produce the field.
- `Paper1MainResultsData` itself carries `construction_neg` as a structure field.
- `Theorem_1_1.of_assumed_fixed_point_construction_branches` wires a negative fixed-point construction into the lower-level construction branch, but deliberately keeps `hstat`, `hlim_bot`, `hVmono`, `hupper`, and `htail` explicit.
- `WaveBridgeWrappers.lean` proves `b1_neg_hVmono`: the elliptic derivative monotonicity property-function is closed from trap monotonicity.
- The same file documents the remaining four negative-branch property functions as stalled: stationary equation (`hstat`), left-end limit (`hlim_bot`), strict upper bound (`hupper`), and right-tail asymptotic (`htail`).
- `WaveRotheClose.lean` discharges `hVcont` and reduces the older `b1_chiNeg_existence` chain to carried `hprodTrap` and `hdep`, explicitly identifying the per-step producer and continuous dependence as the remaining hard pieces.
- `WaveRotheSchauder.lean` supplies several useful Schauder wrappers. In particular, the lower-pinned wrapper is non-vacuous and avoids the false “nontrivial Schauder principle on a bare trap” route, but it still consumes the Schauder data and stationary/flatness inputs.

### Classification

🟡 **Partial.** Substantial wiring and reductions are landed, especially monotone elliptic derivative, sign-specific super-barrier reductions, lower-pinned Schauder wrappers, and some Rothe cleanup. But no theorem currently produces the exact `construction_neg` field.

The hard residual is not a Lean assembly detail: it is a construction theorem combining:

1. the per-step Rothe/Green producer (`RotheFloorResidualCore` / `RotheStepProducer` level),
2. Rothe continuous dependence / Schauder fixed point,
3. stationarity of the fixed point,
4. strict lower/upper bounds,
5. right-tail linearization/asymptotic.

### Satisfiability / vacuity

Satisfiable/non-vacuous. The field matches the paper’s negative-sensitivity regime and no contradiction was found. The tree explicitly repairs a vacuity trap: `LocalUniformNontrivialSchauderFixedPointPrinciple` is false for the bare trap, and the lower-pinned trap route is introduced as the non-vacuous replacement.

## 2. `construction_pos`

### What the field requires

`construction_pos` asks, for `α=m+γ-1`, `0≤χ<min(1/2, chiStar p)`, and `2<c`, for a frozen stationary wave profile with `ShenUpperBoundPositive` and the full right-tail asymptotic family.

### Landed pieces

- `WaveRothePos.lean` explains that the Rothe/Schauder infrastructure is sign-agnostic; the positive branch swaps in `whole_line_super_barrier_pos`.
- `rotheFloorResidual_of_trap_pos` discharges the positive-sign super-barrier field from `whole_line_super_barrier_pos`, but still carries the deep whole-line Green core.
- `b1_chiPos_existence` reuses the negative-branch existence chain and carries the same deep obligations: `hcoreAll`, step/tail dependence, Schauder principle, Green identity, positivity, boundedness, left/right limits.
- `b1_chiPos_existence_profileClean` and its route-pin variants discharge some trap-derived profile obligations such as `hbdd` and `hlim_pos`, but still carry Green/stationary, positivity/floor, and left endpoint/flatness obligations.
- `TravelingWaveConstruction.lean` proves explicit logistic-profile `ShenUpperBoundPositive`, `HasStrictWaveUpperTailBound`, and related barrier facts. These are useful barriers, not producers for the arbitrary fixed point `U` required by `construction_pos`.

### Classification

🟡 **Partial.** The positive-sign super-barrier replacement is landed and the downstream chain is mostly reused from the negative branch. But no theorem discharges the full `construction_pos` field.

The remaining analytic gap is the same fixed-point/Rothe construction core as the negative branch, plus the positive-branch profile obligations required to turn the produced fixed point into the stated profile with tail asymptotic.

### Satisfiability / vacuity

Satisfiable/non-vacuous. The parameter regime is consistent: `0≤χ<min(1/2, chiStar p)` is the paper’s small-positive regime and aligns with the positive super-barrier machinery. No over-strong contradiction was found in this field alone.

## 3. `cStarStar_spec`

### What the field requires

For every stable-wave parameter regime, it asks for a threshold family `cStarStarFn p` with:

1. `StabilitySpeedThresholdFamilyAsymptotic p (cStarStarFn p)`, i.e. a bound
   `|c**(χ) - (p.γ+p.γ⁻¹)| ≤ A |χ|^(1/6)` for all sufficiently small `χ`;
2. the strict pointwise baseline inequality `stabilitySpeedBaseline p < cStarStarFn p p.χ`.

### Landed pieces

- `stabilitySpeedBaseline` and `StabilitySpeedThresholdFamilyAsymptotic` are defined in `Statements.lean`.
- The tree has elementary lemmas deriving speed consequences from a threshold exceeding `stabilitySpeedBaseline`, including `two_lt_of_stabilitySpeedBaseline_lt`, `kappa_pos_of_stabilitySpeedBaseline_lt`, `kappa_lt_one_of_stabilitySpeedBaseline_lt`, and `kappa_lt_stability_weight_cap_of_stabilitySpeedBaseline_lt`.
- No concrete `cStarStarFn` producer was found.

### Classification

🟥 **Over-strong as typed, not merely undischargeable.** The asymptotic definition is not punctured at zero. Plugging `χ=0` into the bound forces

```text
cStarStarFn p 0 = p.γ + p.γ⁻¹.
```

But

```text
stabilitySpeedBaseline p = 1 + |p.χ|^(1/6) + (1+|p.χ|^(1/6))⁻¹,
```

so at `p.χ = 0`, the baseline is `2`. If `p.γ = 1`, then `p.γ + p.γ⁻¹ = 2`, making the required strict inequality

```text
2 < 2
```

impossible. `CMParams` permits `γ = 1`, and `StableWaveParameterRegime` contains the nonnegative branch at `χ = 0` whenever the small-positive side accepts it.

### Satisfiability / vacuity

Not globally satisfiable as currently typed if the stable regime includes `χ=0, γ=1`. This is a type-level endpoint bug, not PDE content.

Minimal fixes, in increasing faithfulness:

1. weaken the pointwise baseline field to `≤` at the `χ=0, γ=1` endpoint;
2. make the asymptotic statement punctured at zero, so `cStarStarFn p 0` can be chosen strictly above the baseline;
3. restrict the strict baseline comparison to `p.χ ≠ 0` or to `p.γ + p.γ⁻¹ > stabilitySpeedBaseline p` at the evaluated parameter;
4. separate the speed threshold used for stability from the asymptotic representative.

After such a refactor, the proof is elementary real algebra.

## 4. `stability`

### What the field requires

For stable-wave parameters and speeds above the threshold, for every traveling wave with strict upper-tail bound and a right-tail asymptotic, every nonnegative/left-positive perturbation close in weighted `L²` must generate a global Cauchy solution converging in both weighted `L²` moving frame and uniform moving frame.

### Landed pieces

- `Theorem_1_2.of_assumed_stability_branch` is only a bridge: if `cStarStar_spec` and this stability field are supplied, then `Theorem_1_2` follows.
- `Theorem_1_2_self_initial_data_branch` and the frozen-profile self-initial-data variants prove only the trivial self-data branch where the solution is the traveling wave itself.
- `Theorem_1_3` bridges show how stability plus Cauchy uniqueness/resolvent/tail asymptotics imply uniqueness; they do not prove stability.
- Lemma 2.5 helper estimates and weighted resolvent estimates are landed toward the energy machinery, but no theorem in the audited files proves the full nonlinear orbital stability field.

### Classification

🔨 **Open.** This is the genuine hard stability theorem for the nonlinear whole-line Cauchy problem. The existing tree contains statement-level bridges and some weighted estimates, but no producer for the full `stability` field.

Minimal missing theorem:

```lean
theorem paper1_weighted_orbital_stability
    (p : CMParams) (hreg : StableWaveParameterRegime p)
    (cStarStar : ℝ → ℝ)
    (hcStar : StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p < cStarStar p.χ) :
    ∀ c, cStarStar p.χ < c →
    ∀ U V, IsTravelingWave p c U V →
      HasStrictWaveUpperTailBound p c U →
      (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
      ∀ η, kappa c < η → η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
      ∀ u₀, NonnegativeInitialDatum u₀ → StrictlyPositiveAtLeft u₀ →
        WeightedL2InitialCloseness η u₀ U →
        ∃ u v,
          IsGlobalCauchySolutionFrom p u₀ u v ∧
          WeightedL2MovingFrameConvergence η c u U ∧
          UniformMovingFrameConvergence c u U
```

### Satisfiability / vacuity

Satisfiable/non-vacuous. The field is mathematically strong but aligned with Paper 1’s Theorem 1.2. No formal inconsistency was detected in the stability statement itself. It is simply unproved.

## Most tractable next target

The most tractable target is now the **`cStarStar_spec` type correction**, not a proof of the existing field.

### Precise route

1. Refactor the structure field. The minimal mechanically safe variant is:

```lean
cStarStar_spec : ∀ p : CMParams, StableWaveParameterRegime p →
  StabilitySpeedThresholdFamilyAsymptotic p (cStarStarFn p) ∧
    (p.χ = 0 ∧ p.γ = 1 ∨ stabilitySpeedBaseline p < cStarStarFn p p.χ)
```

A cleaner mathematical variant is to make the asymptotic punctured at zero and keep the strict baseline condition.

2. After refactor, prove the explicit threshold algebra. A punctured-asymptotic version can use, for instance:

```lean
def paper1_cStarStarFn_explicit (p : CMParams) (χ : ℝ) : ℝ :=
  if χ = 0 then stabilitySpeedBaseline p + 1
  else p.γ + p.γ⁻¹ + 2 * |χ| ^ (1 / 6 : ℝ)
```

3. Mirror the existing speed-consequence lemmas (`kappa_pos_of_stabilitySpeedBaseline_lt`, `kappa_lt_one_of_stabilitySpeedBaseline_lt`, `kappa_lt_stability_weight_cap_of_stabilitySpeedBaseline_lt`) after the refactor, because these consumers only need the strict baseline inequality at the actual evaluated parameter.

## Final distance map

- `construction_neg`: 🟡 partial; hard construction producer still missing.
- `construction_pos`: 🟡 partial; same construction producer, positive-sign super-barrier already swapped in.
- `cStarStar_spec`: 🟥 over-strong as typed at the `χ=0, γ=1` endpoint; fix/refactor first.
- `stability`: 🔨 open; full nonlinear orbital stability theorem.

The current P1 headline remains a sorry-free conditional wrapper. The requested 4-field bundle is not fully non-vacuous as typed until the `cStarStar_spec` endpoint issue is repaired.
