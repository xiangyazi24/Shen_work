ANSWER Q4592 2f4a96f0

# Definitive verdict

A parameterized Green-step closed-graph theorem is the right replacement for the over-strong global `PaperRotheTailUniform` route, but two corrections are essential.

1. **The connector-visible Paper 1 implementation is a whole-line traveling-wave construction.** Its kernel is
   ```lean
   greenKernel c lam : ℝ → ℝ
   greenConv c lam H : ℝ → ℝ
   ```
   not the Neumann Green kernel on `[0,1]`. The `[0,1]` cosh/sinh kernel is a valid reusable bounded-interval analogue, but it must not be wired into the existing whole-line Paper 1 branch.

2. **Moving-index compactness alone does not produce a tail estimate.** Even if every individual orbit is antitone and converges, an arbitrary sequence `k n → ∞` can remain before the slow part of the `n`-th orbit. The elementary counterexample is
   ```text
   a(n,k) = 1  if k ≤ n,
            0  if n < k.
   ```
   Each `k ↦ a(n,k)` decreases to `0`, but with `k n = n` one has `a(n,k n)=1` for every `n`.

The sound route is therefore:

```plain text
per-orbit local-uniform convergence
→ choose kₙ adaptively so the successor residual is < 1/n on [-n,n]
→ moving-index compactness extracts a locally-uniform cluster limit
→ parameterized Green closed graph passes the step equation
→ old and new iterates have the same limit
→ the limit satisfies the self implicit step
→ paperWaveOperator_eq_zero_of_paperImplicitStepOp_self
→ stationary frozen profile.
```

This uses no Minty argument and no Aubin–Lions theorem. It also avoids proving a uniform tail over every profile in the trap.

# 1. The repository objects and the correct topology

The current Paper 1 orbit is

```lean
rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM : ℕ → ℝ → ℝ
```

with exact per-step facts

```lean
rotheSeqOfPaper_stepFacts
```

and, in particular,

```lean
PaperRotheStepFacts.step_op :
  ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x
```

for old iterate `Z` and new iterate `W`.

Each orbit already carries:

```lean
PaperRotheOrbitData.locallyUniform
PaperRotheOrbitData.limit_continuous
paperTmap_compactRange
```

and the visible frontier definitions are

```lean
PaperRotheSeqStepDependence
PaperRotheTailUniform
paperRotheContinuousDependence
```

The old `PaperRotheTailUniform` quantifies one `K` uniformly over **every** frozen profile in `InMonotoneWaveTrapSet κ M`. That is stronger than what the compact closed-graph limit passage needs.

## Local-uniform topology

Use the repository predicate

```lean
LocallyUniformConverges (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
```

which is the compact-open topology expressed by epsilon estimates on every window `Icc (-R) R`.

For nonlinear source terms involving first spatial derivatives, use the following explicit `C¹_loc` sequential topology rather than trying to construct a Fréchet-space instance immediately:

```lean
def LocallyC1Converges
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  LocallyUniformConverges f g ∧
  LocallyUniformConverges (fun n => deriv (f n)) (deriv g)
```

The accompanying hypotheses should state that each `f n` and `g` is differentiable. If the Green source depends only on values, ordinary `LocallyUniformConverges` is enough. For the actual chemotaxis source, `C¹_loc` is the safe interface.

## Sequential compact closed graph

For a family of maps `T n : X → X` and a limit map `T∞`, the exact useful notion is:

```lean
def SequentialApproxClosedGraph
    (T : ℕ → (ℝ → ℝ) → ℝ → ℝ)
    (T∞ : (ℝ → ℝ) → ℝ → ℝ) : Prop :=
  ∀ Uₙ U,
    LocallyC1Converges Uₙ U →
    LocallyUniformConverges
      (fun n x => Uₙ n x - T n (Uₙ n) x)
      (fun _ => 0) →
    U = T∞ U
```

For the Rothe step there are normally two profiles, the old iterate `Zₙ` and the new iterate `Wₙ`. The more faithful form is:

```lean
def SequentialTwoInputClosedGraph
    (Step : ℕ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ)
    (Step∞ : (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ) : Prop :=
  ∀ Zₙ Wₙ Z W,
    LocallyC1Converges Zₙ Z →
    LocallyC1Converges Wₙ W →
    LocallyUniformConverges
      (fun n x => Wₙ n x - Step n (Zₙ n) (Wₙ n) x)
      (fun _ => 0) →
    W = Step∞ Z W
```

The stationary conclusion uses this with `Z=W`, obtained from the vanishing old/new successor gap.

# 2. The kernel-level closed-graph theorem

The cleanest implementation separates the kernel theorem from the nonlinear source theorem.

## Abstract whole-line Green theorem

The load-bearing kernel result should have the following shape.

```lean
theorem greenConv_param_closedGraph
    {cₙ lamₙ : ℕ → ℝ} {c lam : ℝ}
    {Hₙ : ℕ → ℝ → ℝ} {H : ℝ → ℝ}
    {Wₙ : ℕ → ℝ → ℝ} {W : ℝ → ℝ}
    (hc : Tendsto cₙ atTop (𝓝 c))
    (hlam : Tendsto lamₙ atTop (𝓝 lam))
    (hlam_pos : 0 < lam)
    (hH_cont : ∀ n, Continuous (Hₙ n))
    (hH_lim_cont : Continuous H)
    (hH_lu : LocallyUniformConverges Hₙ H)
    (hH_bdd : ∃ B : ℝ, 0 ≤ B ∧ ∀ n y, |Hₙ n y| ≤ B)
    (hW_lu : LocallyUniformConverges Wₙ W)
    (hres : LocallyUniformConverges
      (fun n x =>
        Wₙ n x - greenConv (cₙ n) (lamₙ n) (Hₙ n) x)
      (fun _ => 0)) :
    W = greenConv c lam H
```

For an exact Green relation, `hres` is discharged by `simp`. The approximate form is preferable because it also handles numerical, truncated, cube-approximation, and moving-index residuals.

## Kernel parameter lemmas needed underneath

Prove these two facts first.

```lean
theorem greenKernel_param_locallyUniform
    (hc : Tendsto cₙ atTop (𝓝 c))
    (hlam : Tendsto lamₙ atTop (𝓝 lam))
    (hlam_pos : 0 < lam) :
    LocallyUniformConverges
      (fun n => greenKernel (cₙ n) (lamₙ n))
      (greenKernel c lam)
```

and

```lean
theorem greenKernel_param_common_dominator
    (hc : Tendsto cₙ atTop (𝓝 c))
    (hlam : Tendsto lamₙ atTop (𝓝 lam))
    (hlam_pos : 0 < lam) :
    ∃ A a : ℝ,
      0 ≤ A ∧ 0 < a ∧
      ∀ᶠ n in atTop, ∀ z,
        |greenKernel (cₙ n) (lamₙ n) z| ≤
          A * Real.exp (-a * |z|)
```

The second right-hand side is integrable. It follows from continuity of `greenRootPlus`, `greenRootMinus`, and `greenDelta`: after restricting to an eventual compact parameter neighborhood with `lamₙ ≥ lam/2`, both exponential rates stay uniformly separated from zero and the prefactor stays bounded.

## Proof of `greenConv_param_closedGraph`

Write the convolution in translated form:

```text
GₙHₙ(x) = ∫ z, greenKernel(cₙ,lamₙ,z) * Hₙ(x-z) dz.
```

Fix a compact output window `|x|≤R` and `ε>0`.

1. Obtain a common source bound `B`.
2. Use the common integrable kernel dominator to choose `A` so that
   ```text
   B * ∫_{|z|>A} dominator(z) dz < ε/6.
   ```
   This controls both convolution tails uniformly in `n` and uniformly for `|x|≤R`.
3. On `|z|≤A`, one has `x-z ∈ [-(R+A),R+A]`. Thus `hH_lu` gives uniform convergence of `Hₙ(x-z)` to `H(x-z)`.
4. `greenKernel_param_locallyUniform` gives uniform convergence of the kernels on `[-A,A]`.
5. Split
   ```text
   KₙHₙ - KH = Kₙ(Hₙ-H) + (Kₙ-K)H
   ```
   and bound each central integral by finite-measure uniform estimates.
6. Reattach the two tails. This proves
   ```lean
   LocallyUniformConverges
     (fun n => greenConv (cₙ n) (lamₙ n) (Hₙ n))
     (greenConv c lam H).
   ```
7. Combine with `hW_lu` and `hres`; uniqueness of limits in `ℝ` gives pointwise equality, then `funext`.

Existing whole-line ingredients to reuse include:

```lean
greenKernel_continuous
greenKernel_integrable
greenKernel_integral_eq
greenConv_eq_translated_integral_of_bounded
greenConv_contDiff_two
greenConv_tendsto_atBot_of_source_tendsto
greenConv_tendsto_atTop_of_source_tendsto
```

The last two are not themselves the compact-open closed-graph theorem, but their DCT proofs already contain the right kernel domination pattern.

# 3. The `[0,1]` Neumann analogue

For a reusable bounded-interval lemma, the Green kernel of

```text
-φ'' + μ φ = f,
φ'(0)=φ'(1)=0,
```

for `μ>0` is

```text
Gμᴺ(x,y) =
  cosh(√μ * min(x,y)) * cosh(√μ * (1-max(x,y)))
  / (√μ * sinh(√μ)).
```

On the compact square `[0,1]²`, `μₙ→μ>0` implies uniform convergence of `Gμₙᴺ` to `Gμᴺ`. Thus the bounded-interval version is easier:

```lean
theorem intervalNeumannGreen_param_closedGraph
    {μₙ : ℕ → ℝ} {μ : ℝ}
    {Hₙ : ℕ → ℝ → ℝ} {H : ℝ → ℝ}
    (hμ : Tendsto μₙ atTop (𝓝 μ))
    (hμpos : 0 < μ)
    (hH : UniformConvergesOnIcc Hₙ H 0 1)
    (hrel : UniformConvergesOnIcc
      (fun n x => Wₙ n x -
        ∫ y in (0:ℝ)..1,
          intervalNeumannGreen (μₙ n) x y * Hₙ n y)
      (fun _ => 0) 0 1) :
    ∀ x ∈ Set.Icc (0:ℝ) 1,
      W x = ∫ y in (0:ℝ)..1,
        intervalNeumannGreen μ x y * H y
```

There is no tail/tightness issue because the integration domain is compact. Again: this is not the kernel currently used by the Paper 1 whole-line wave files.

# 4. Nonlinear source closed graph

Do not prove the whole nonlinear theorem inside the kernel lemma. Expose a source-convergence adapter.

```lean
def PaperStepSourceConvergesAlong
    (pₙ : ℕ → CMParams) (cₙ lamₙ : ℕ → ℝ)
    (uₙ Zₙ Wₙ : ℕ → ℝ → ℝ)
    (p : CMParams) (c lam : ℝ)
    (u Z W : ℝ → ℝ) : Prop :=
  LocallyUniformConverges
    (fun n => paperStepSource_truncated
      (pₙ n) (cₙ n) (lamₙ n) M κ (uₙ n) (Zₙ n) (Wₙ n))
    (paperStepSource_truncated p c lam M κ u Z W)
```

The exact argument list should be adjusted to the committed definition. The point is to make source convergence a separately testable theorem.

A repository-facing producer should be:

```lean
theorem paperStepSource_locallyUniform_of_locallyC1
    (hp : PaperParamsConverge pₙ p)
    (hc : Tendsto cₙ atTop (𝓝 c))
    (hlam : Tendsto lamₙ atTop (𝓝 lam))
    (hu : LocallyC1Converges uₙ u)
    (hZ : LocallyC1Converges Zₙ Z)
    (hW : LocallyC1Converges Wₙ W)
    (htrap : common trap/bound/rate data) :
    PaperStepSourceConvergesAlong
      pₙ cₙ lamₙ uₙ Zₙ Wₙ p c lam u Z W
```

Its proof is algebraic once the following already-developed pieces are invoked:

- local continuity of powers on the trapped nonnegative range;
- `frozenElliptic` and its derivative dependence on the frozen profile;
- products and denominator powers;
- the common `L∞` and derivative bounds;
- exponential left-rate/two-sided tail data where needed.

For `CMParams`, do not spend time installing a global topology unless useful elsewhere. A small predicate `PaperParamsConverge pₙ p` listing convergence of the finitely many scalar fields is more robust in Lean.

# 5. The exact moving-index Rothe theorem

## The insufficient version

This statement is false without an extra residual assumption:

```lean
-- FALSE from compactness alone
Tendsto kₙ atTop atTop →
LocallyUniformConverges uₙ u →
LocallyUniformConverges
  (fun n => rotheSeqOfPaper ... (uₙ n) ... (kₙ n)) U →
U is stationary.
```

The missing fact is that the old and new iterates converge to the same limit.

## The sufficient weak property

Define only the successor-gap estimate along the one selected family:

```lean
def PaperRotheSuccessorGapAlong
    (Z : ℕ → ℕ → ℝ → ℝ) (kₙ : ℕ → ℕ) : Prop :=
  ∀ R > 0, ∀ ε > 0,
    ∀ᶠ n in atTop, ∀ x ∈ Set.Icc (-R) R,
      |Z n (kₙ n + 1) x - Z n (kₙ n) x| < ε
```

This is strictly weaker than convergence to each orbit's named `rotheLimit`, and it is exactly what stationarity needs.

Then the main moving-index theorem should be:

```lean
theorem paperRothe_movingIndex_closedGraph
    {pₙ : ℕ → CMParams} {p : CMParams}
    {cₙ lamₙ : ℕ → ℝ} {c lam : ℝ}
    {uₙ : ℕ → ℝ → ℝ} {u : ℝ → ℝ}
    {Z : ℕ → ℕ → ℝ → ℝ} {kₙ : ℕ → ℕ}
    {U : ℝ → ℝ}
    (hk : Tendsto kₙ atTop atTop)
    (hp : PaperParamsConverge pₙ p)
    (hc : Tendsto cₙ atTop (𝓝 c))
    (hlam : Tendsto lamₙ atTop (𝓝 lam))
    (hlam_pos : 0 < lam)
    (hu : LocallyC1Converges uₙ u)
    (hnew : LocallyC1Converges
      (fun n => Z n (kₙ n + 1)) U)
    (hgap : PaperRotheSuccessorGapAlong Z kₙ)
    (hstep : ∀ n x,
      paperImplicitStepOp (pₙ n) (cₙ n) (1 / lamₙ n)
        (uₙ n) (Z n (kₙ n + 1)) x
        = Z n (kₙ n) x)
    (hgreen : the per-step Green representation/source data)
    (hsource : the source-convergence adapter) :
    ∀ x,
      paperImplicitStepOp p c (1 / lam) u U x = U x
```

Proof:

1. `hgap` plus `hnew` gives
   ```lean
   LocallyUniformConverges (fun n => Z n (kₙ n)) U.
   ```
2. Use the Green representation of `hstep`, not pointwise convergence of second derivatives.
3. Apply `paperStepSource_locallyUniform_of_locallyC1`.
4. Apply `greenConv_param_closedGraph`.
5. Obtain the limiting self-step identity.

The stationary wrapper is then immediate:

```lean
theorem paperRothe_movingIndex_stationary
    ...
    (hself : ∀ x,
      paperImplicitStepOp p c (1 / lam) u U x = U x) :
    ∀ x, paperWaveOperator p c u U x = 0 :=
  paperWaveOperator_eq_zero_of_paperImplicitStepOp_self
    p c lam U hlam_pos hself
```

Adjust the final theorem's frozen profile argument if the committed theorem uses `U` both as frozen profile and solution. The algebraic endpoint theorem already exists; the missing content is the moving-index Green passage.

# 6. Adaptive choice of the moving indices

The best way to obtain `PaperRotheSuccessorGapAlong` requires **no family-uniform tail theorem**.

For the `n`-th orbit, `PaperRotheOrbitData.locallyUniform` gives local-uniform convergence to its own `rotheLimit`. Apply this on the growing window `[-n,n]` with tolerance `1/(4(n+1))`. Choose `Kₙ` such that every `k≥Kₙ` is that close to the limit, and set

```text
kₙ = max n Kₙ.
```

Then:

```text
kₙ ≥ n,
```

so `kₙ→∞`, and both `Zₙ(kₙ)` and `Zₙ(kₙ+1)` are within `1/(4(n+1))` of the same per-orbit limit on `[-n,n]`. Therefore

```text
sup_{|x|≤n} |Zₙ(kₙ+1,x)-Zₙ(kₙ,x)| < 1/(2(n+1)).
```

This implies `PaperRotheSuccessorGapAlong Z kₙ` on every fixed compact window.

The Lean target is:

```lean
theorem exists_movingIndex_successorGap
    (hlu : ∀ n,
      LocallyUniformConverges (Z n) (rotheLimit (Z n))) :
    ∃ kₙ : ℕ → ℕ,
      Tendsto kₙ atTop atTop ∧
      PaperRotheSuccessorGapAlong Z kₙ
```

This diagonal choice is the crucial repair. It does not give an arbitrary-index theorem, and it does not give the old globally quantified `PaperRotheTailUniform`; neither is needed for the stationary subsequence passage.

# 7. Finite-index dependence

The existing target

```lean
PaperRotheSeqStepDependence p c lam M κ Λ hprodAll hκ hM
```

can be proved by induction on the fixed index `k` once a one-step Green closed-graph/uniqueness lemma is available.

## Base

At `k=0`,

```lean
rotheSeqOfPaper_zero
```

reduces the sequence to `upperBarrier κ M`. If `κ,M` are fixed, convergence is trivial. If they vary, add the elementary parameter continuity of `upperBarrier`.

## Induction step

Assume the old iterates converge locally in `C¹`. For the new iterates:

1. `PaperRotheStepFacts.deriv_le`, `nonneg`, and `le_barrier` give local precompactness.
2. Extract a locally-uniformly convergent subsubsequence by the existing Helly/Arzelà–Ascoli infrastructure.
3. Apply the one-step Green closed-graph theorem to show every cluster limit solves the limiting implicit step with the limiting old iterate.
4. Invoke the already-proved uniqueness of the per-step fixed-source/implicit solution.
5. Hence every cluster limit is the selected limiting step.
6. Conclude the full sequence converges. A direct contradiction proof on a fixed window avoids needing a specialized abstract subsequence theorem: failure of convergence gives a bad subsequence, compactness gives a convergent subsubsequence, and closed graph plus uniqueness contradicts the fixed positive error.

This is the right role of finite-index induction. It proves continuity of every fixed step; it does not by itself control a moving index.

# 8. Recommended Lean lemma decomposition

Build these in dependency order.

## Lemma 1 — parameterized kernel domination

```lean
greenKernel_param_common_dominator
```

Proves an eventual common bound `A * exp (-a*|z|)` from `cₙ→c`, `lamₙ→lam>0`.

## Lemma 2 — parameterized Green convolution continuity

```lean
greenConv_locallyUniform_of_param_source
```

From kernel parameter convergence, local-uniform source convergence, and a common global source bound, proves local-uniform convergence of `greenConv`.

## Lemma 3 — nonlinear source continuity

```lean
paperStepSource_locallyUniform_of_locallyC1
```

Converts parameter/profile/old/new `C¹_loc` convergence plus common trap/rate bounds into local-uniform convergence of the paper step source.

## Lemma 4 — approximate one-step closed graph

```lean
paperGreenStep_approx_closedGraph
```

Combines Lemmas 2–3 with an approximate Green fixed-point residual and concludes the limiting Green step relation.

## Lemma 5 — fixed-index Rothe dependence

```lean
paperRotheSeqStepDependence_of_greenClosedGraph
```

Induction on fixed `k`; compactness plus step uniqueness removes subsequences.

## Lemma 6 — adaptive moving-index selector

```lean
exists_movingIndex_successorGap
```

Uses only the already-proved per-orbit local-uniform convergence. Produces `kₙ→∞` and the along-family successor-gap property.

## Lemma 7 — moving-index stationary closed graph

```lean
paperRothe_movingIndex_closedGraph
```

Extracts a cluster limit of the selected new iterates, transfers the old iterates to the same limit via the successor gap, and passes the Green step relation.

## Lemma 8 — stationary/profile wrapper

```lean
paperRothe_movingIndex_stationary
```

Calls

```lean
paperWaveOperator_eq_zero_of_paperImplicitStepOp_self
```

and packages the trap, monotonicity, lower pin, and frozen stationary profile fields.

# 9. Interface consequence for the current roadmap

The current structure

```lean
PaperLowerRawParabolicFloorRouteAParamCoreNoBar
```

still contains

```lean
tail : PaperRotheTailUniform ...
```

and `paperRotheContinuousDependence` explicitly consumes that globally uniform tail. The weaker moving-index theorem cannot inhabit this old field by definitional wiring.

Therefore one of the following must be done honestly:

1. add a new final assembly route whose compactness passage consumes
   ```lean
   paperRotheSeqStepDependence
   + exists_movingIndex_successorGap
   + paperRothe_movingIndex_closedGraph;
   ```
   or
2. weaken/replace the old `tail` field in a new floor structure.

Do not claim that compactness proves the old `PaperRotheTailUniform`. It does not.

# Bottom line

The buildable theorem is a **sequential approximate closed graph for Green representations**, coupled to an **adaptively selected moving Rothe index**. The exact sufficient residual is the old/new successor gap on each compact window. Per-orbit local-uniform convergence already supplies such indices one orbit at a time; no globally uniform tail over the trap is required.

The one mathematically false step to avoid is:

```plain text
individual convergence + compactness + arbitrary kₙ→∞
⇒ family-uniform tail.
```

Replace it by:

```plain text
individual convergence
⇒ choose kₙ adaptively with residual <1/n on [-n,n]
⇒ compactness + Green closed graph
⇒ stationary limit.
```

That is the shortest sound Green–Rothe continuum-limit route for the remaining Paper 1 core.