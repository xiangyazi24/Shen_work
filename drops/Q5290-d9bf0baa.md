ANSWER Q5290 d9bf0baa

# Paper 1 Henry window: exact discharge route for measurability, strong `L²` continuity, and canonical representatives

## Executive verdict

There are three different issues here, and separating them removes most of the apparent circularity.

1. **`hphi_meas` is already discharged on current `main`.** Use
   `paper5WeightedEnergy_coreIntegrability_of_exactGeneratorWindow_local`
   from
   `ShenWork/Paper1/WholeLineWeightedRegularityCoreWindowLocal.lean`,
   rather than the older all-positive-time theorem in
   `WholeLineWeightedRegularityCoreWindow.lean`. The local theorem derives the
   weighted population’s spatial `AEStronglyMeasurable` property directly from
   positive-time `C²` spatial slices and `U ∈ C²`.

2. **`hZcont` is strong Hilbert-space continuity, not merely continuity of the
   scalar energy.** A direct dominated-convergence proof is short only after one
   has a **single locally uniform integrable spatial envelope**. Joint pointwise
   time continuity plus separate square integrability of every slice does not
   produce such an envelope. A uniform numerical `L²` bound is also insufficient:
   weighted mass can escape to the right.

3. **Canonical definitions solve `hXrep` and `hFrep`, but not `hXcont` or
   `hFcont`.** Define the trajectories with
   `wholeLineRealL2PositiveWindowTrajectory`, or use the specialized natural
   forcing trajectory. The representative equalities are then one-line uses of
   the existing `..._coe_ae_of_mem` theorems. They are canonical, but not
   definitionally `rfl`, because `Lp` is an a.e.-quotient.

The strict noncircular dependency order is therefore:

```text
positive-time spatial classical regularity
  -> spatial measurability of W, Wx, F

H0 weighted mild/restart formula, in divergence form
  + weighted resolver bounds
  + bounded physical box
  -> W : C(time; L2_eta)                         [hZcont]
     (no W_t and no hWx2)

independent positive-time H1 producer
  -> Wx(q) in L2 for each q
  + BUC time moduli and same-weight no-escape/tightness
  -> X : C(time; L2)                             [hXcont]

static forcing estimate from W and Wx
  -> F(q) in L2 for each q
  + strong-L2 forcing continuity
  -> F : C(time; L2)                             [hFcont]

canonical positive-window trajectories
  -> hXrep, hFrep

all of the above
  -> paper5WeightedEnergy_coreIntegrability_of_exactGeneratorWindow_local
```

A source/version detail matters for theorem lookup: the audited repository’s
`lake-manifest.json` pins Mathlib `v4.29.1` at commit
`5e932f97dd25535344f80f9dd8da3aab83df0fe6`. The Mathlib names below were
checked against that pin, not against a later API.

---

# 1. `hphi_meas`: continuity is enough, and the exponential weight causes no problem

Write

```lean
W q x := paper5WeightedPopulation eta (coMovingPath c u) U q x
```

so, definitionally, this is the continuous product

```text
exp(eta*x) * (coMovingPath c u q x - U x).
```

For each fixed positive time `q`, the needed proof is exactly:

```lean
have hphi_meas : ∀ q ∈ Set.Ioo L R,
    AEStronglyMeasurable
      (paper5WeightedPopulation eta (coMovingPath c u) U q) volume := by
  intro q hq
  exact
    ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).mul
      ((hu2 q hq).continuous.sub hU2.continuous)).aestronglyMeasurable
```

This is already the proof in
`paper5WeightedEnergy_coreIntegrability_of_exactGeneratorWindow_local`.

The logical ingredients are only:

```text
x ↦ exp(eta*x)                              continuous
x ↦ coMovingPath c u q x                   continuous
x ↦ U x                                    continuous
product and subtraction                    continuous
Continuous.aestronglyMeasurable             closes measurability
```

No integrability is needed for `AEStronglyMeasurable`. In particular, the fact
that `exp(eta*x)` grows at `+∞` is irrelevant to measurability. It matters only
when proving square integrability.

The positivity assumption `q>0` is also not intrinsically a measurability
assumption. It is used upstream to obtain the positive-time spatial classical
slice `hu2 q hq`.

## 1.1 The square-integrability companion is also already local

The same local theorem derives the square-integrability field from `hclose`:

```lean
have hphi_sq : ∀ q ∈ Set.Ioo L R, Integrable (fun x : ℝ =>
    paper5WeightedPopulation eta (coMovingPath c u) U q x ^ 2) volume := by
  intro q hq
  exact paper5WeightedPopulation_sq_integrable_of_weighted_difference
    (hclose q hq)
```

Hence the first implementation change should be:

```text
replace
  paper5WeightedEnergy_coreIntegrability_of_exactGeneratorWindow
by
  paper5WeightedEnergy_coreIntegrability_of_exactGeneratorWindow_local.
```

That removes both the unnecessarily global

```lean
∀ q, 0 < q -> hphi_meas q
∀ q, 0 < q -> hphi_sq q
```

premises from the assembler call.

---

# 2. What `hZcont` actually asks for

Set

```lean
W q := paper5WeightedPopulation eta (coMovingPath c u) U q
Z q := wholeLineRealL2Total (W q).
```

The target is

```lean
ContinuousOn Z (Set.Ioo L R).
```

On valid slices, the squared Hilbert distance is the scalar difference-square
integral:

```text
||Z q - Z t||² = ∫ x, (W q x - W t x)².
```

The repository packages this identity for canonical sections as

```lean
wholeLineRealL2Section_norm_sub_sq
```

and packages the resulting continuity argument as

```lean
wholeLineRealL2Section_continuous_of_integral_sub_sq_tendsto_zero.
```

For a positive closed time window, the better interface is

```lean
wholeLineRealL2PositiveWindowTrajectory_continuous
```

from
`ShenWork/Paper1/WholeLineWeightedRegularityPositiveWindowForcing.lean`.
It asks for exactly:

```lean
hW_meas   : ∀ q ∈ Icc a b, AEStronglyMeasurable (W q) volume
hW_sq     : ∀ q ∈ Icc a b, Integrable (fun x => W q x ^ 2) volume
hW_strong : ∀ q ∈ Icc a b,
  Tendsto (fun r => ∫ x, (W r x - W q x)^2)
    (nhdsWithin q (Icc a b)) (nhds 0)
```

and returns a globally continuous clamped `WholeLineRealL2` trajectory.
On the physical window, the clamp is the identity.

Thus the real analytic leaf is `hW_strong`.

## 2.1 Continuity of `∫ W(q)^2` is not enough

Do not replace `hW_strong` by

```text
q ↦ ∫ W(q,x)^2 dx is continuous.
```

Norm continuity by itself does not imply strong vector continuity. The needed
quantity is the norm of the **difference**, not the difference of the norms.
The practical scalar target is

```lean
Tendsto (fun q => ∫ x, (W q x - W t x)^2)
  (nhdsWithin t S) (nhds 0).
```

---

# 3. The direct dominated-convergence route for `hZcont`

Yes: if a locally uniform integrable envelope is already available, dominated
convergence is the shortest proof. The important qualification is that the
mild solution’s joint pointwise continuity does not itself supply the envelope.

Fix a target time `t` and a time set `S`, for example a compact positive window
`Set.Icc a b`. Assume that there is a spatial function `G : ℝ → ℝ` such that

```lean
hG2 : Integrable (fun x => G x ^ 2) volume
hG  : ∀ᶠ q in nhdsWithin t S, ∀ᵐ x ∂volume, |W q x| ≤ G x
```

and, after shrinking the neighborhood if necessary, the same bound holds for
`W t`.

Apply dominated continuity to

```lean
Phi q x := (W q x - W t x)^2.
```

The exact common dominator is

```lean
bound x := 4 * G x ^ 2.
```

Indeed,

```text
(W q x - W t x)^2
  <= 2*(W q x)^2 + 2*(W t x)^2
  <= 4*G x^2.
```

The pointwise limit is zero by time continuity at fixed `x`.

## 3.1 Exact Mathlib theorem names at the repository pin

The relevant names are:

```lean
MeasureTheory.continuousWithinAt_of_dominated
MeasureTheory.continuousAt_of_dominated
MeasureTheory.continuousOn_of_dominated
MeasureTheory.continuous_of_dominated
```

There is no theorem named

```lean
MeasureTheory.continuousOn_integral_of_dominated
```

at the pinned Mathlib version.

The filter-form dominated convergence theorem is

```lean
MeasureTheory.tendsto_integral_filter_of_dominated_convergence
```

and the sequence form is

```lean
MeasureTheory.tendsto_integral_of_dominated_convergence.
```

For `nhdsWithin t S` on `ℝ`, the filter-form theorem’s countable-generation
instance is available. Either the continuity wrapper or the filter theorem is
sound; the continuity wrapper usually creates fewer explicit filter goals.

## 3.2 Lean proof shape

The following is schematic but follows the actual API shape:

```lean
let W : ℝ → ℝ → ℝ :=
  fun q => paper5WeightedPopulation eta (coMovingPath c u) U q
let Phi : ℝ → ℝ → ℝ := fun q x => (W q x - W t x) ^ 2
let bound : ℝ → ℝ := fun x => 4 * G x ^ 2

have hPhi_cont : ContinuousWithinAt
    (fun q => ∫ x, Phi q x ∂volume) S t := by
  apply MeasureTheory.continuousWithinAt_of_dominated
  · -- eventual spatial measurability
    filter_upwards with q
    exact ((hW_meas q).sub (hW_meas t)).pow 2
  · -- domination
    filter_upwards [hG] with q hq
    filter_upwards [hq, hGt] with x hqx htx
    rw [Real.norm_eq_abs, abs_sq]
    dsimp only [Phi, bound]
    nlinarith [sq_nonneg (W q x + W t x)]
  · exact hG2.const_mul 4
  · -- pointwise time continuity
    filter_upwards with x
    exact (((hW_time x).sub_const).pow 2).continuousWithinAt
```

The target integral at `t` is zero, so:

```lean
have hstrong_t : Tendsto
    (fun q => ∫ x, (W q x - W t x)^2)
    (nhdsWithin t S) (nhds 0) := by
  simpa [W, Phi] using hPhi_cont.tendsto
```

Finally call:

```lean
wholeLineRealL2PositiveWindowTrajectory_continuous
  hab hW_meas hW_sq hW_strong
```

and restrict its `Continuous` conclusion to `Set.Ioo L R`.

## 3.3 If the envelope is stated in physical variables

Suppose instead that near `t` one knows

```text
|coMovingPath c u q x - U x| <= Ht x
```

and

```lean
Integrable
  (fun x => exp(2*eta*x) * Ht x^2)
  volume.
```

Then take

```lean
G x := Real.exp (eta*x) * Ht x
```

and the difference-square dominator becomes

```lean
bound x := 4 * Real.exp (2*eta*x) * Ht x^2.
```

This is the exact weighted dominator. The algebraic normalization uses

```text
(exp(eta*x))^2 = exp(2*eta*x).
```

---

# 4. Why the listed hypotheses do not yet supply that dominator

The following data are insufficient by themselves:

```text
for each q, W(q) ∈ L²;
joint or pointwise continuity of (q,x) ↦ W(q,x);
a uniform numerical bound sup_q ||W(q)||₂ < ∞;
BUC time continuity of the unweighted solution.
```

A family of unit `L²` bumps can move to the right while converging to zero on
every compact spatial interval. The norms stay bounded, every slice is square
integrable, and local convergence holds, but there is no strong `L²`
convergence. In the exponentially weighted variable, this is exactly the
right-tail escape that must be ruled out.

The current repository explicitly isolates this issue in

```text
ShenWork/Paper1/WholeLineWeightedRegularityGradientTimeNatural.lean
```

through:

```lean
WholeLineSquareTightAt
tendsto_integral_sub_sq_zero_of_local_and_tight
```

and an escaping-unit-bump counterexample.

The same generic theorem can be applied to `W`, not only to `Wx`:

```text
local compact-interval strong convergence
  + square integrability of the target slice
  + WholeLineSquareTightAt W (nhdsWithin t S)
  -> global strong L² convergence.
```

So there are two honest direct routes:

```text
A. one pointwise integrable envelope G          -> dominated convergence;
B. local convergence + same-weight tightness    -> repository tightness theorem.
```

A uniform `L²` norm bound is neither A nor B.

A particularly common false move is to use BUC time continuity

```text
|u(q,x)-u(t,x)| <= delta(q)
```

and multiply by the exponential weight. This produces

```text
|W(q,x)-W(t,x)| <= delta(q) * exp(eta*x),
```

whose square is not integrable on the right when `eta>0`.

---

# 5. The clean noncircular route to `hZcont` without `hWx2`

If no common tail envelope has already been proved, the best source-faithful
route is to obtain `hZcont` from the **weighted H⁰ mild equation in divergence
form**, before constructing the weighted gradient.

The key flux decomposition is

```text
u^m v_x - U^m V_x
  = (u^m-U^m) v_x + U^m (v_x-V_x).
```

On a finite physical box `0 <= u,U <= M` with `m>=1`,

```text
|u^m-U^m| <= m*M^(m-1)*|u-U|.
```

The elliptic resolver gives, at the same exponential weight,

```text
||exp(eta*x)*(v-V)||₂
  + ||exp(eta*x)*(v_x-V_x)||₂
  <= C(M,eta,p) ||W||₂.
```

Consequently the weighted flux difference has the H⁰ estimate

```text
||weightedFluxDifference(q)||₂ <= Cflux ||W(q)||₂,
```

and the reaction difference similarly satisfies

```text
||weightedReactionDifference(q)||₂ <= Creact ||W(q)||₂.
```

Neither estimate uses `Wx`.

The weighted mild equation then has the schematic form

```text
W(t)
 = S_eta(t-a) W(a)
   + ∫_a^t ∂x S_eta(t-s) Flux(s) ds
   + ∫_a^t S_eta(t-s) Reaction(s) ds.
```

The repository already contains the principal continuity atoms:

```lean
weightedMovingHeatL2Semigroup_tendsto_zero
```

in `WholeLineWeightedRegularityL2Semigroup.lean`, and

```lean
weightedMovingHeatL2Semigroup_duhamel_continuousAt_of_uniform_norm_bound
```

in `WholeLineWeightedRegularityDuhamelContinuity.lean`.

For the divergence term, the heat-gradient history has the integrable
`(t-s)^(-1/2)` singularity. The concrete estimates and square-root time-modulus
machinery are in

```text
WholeLineWeightedRegularityHeatGradientDuhamelHolder.lean
```

including

```lean
weightedMovingHeatL2Gradient_apply_norm_le_rpow_neg_half.
```

Thus the smallest genuinely new public lemma, if not already assembled, should
look like:

```lean
theorem paper5WeightedPopulation_continuousOn_of_divergenceMild_H0_window
    (hW_restart : exact weighted divergence-form mild identity on [a,b])
    (hW_bound : ∀ q ∈ Icc a b, ‖W q‖ ≤ Cw)
    (hFlux_bound : ∀ q ∈ Icc a b, ‖Flux q‖ ≤ Cf)
    (hReact_bound : ∀ q ∈ Icc a b, ‖Reaction q‖ ≤ Cr)
    (hFlux_meas : ...)
    (hReact_meas : ...) :
  ContinuousOn
    (fun q => wholeLineRealL2Total (W q))
    (Icc a b)
```

Its proof is semigroup strong continuity plus the two Duhamel continuity
lemmas. It requires no weighted-population time derivative and no `hWx2`.

## 5.1 Current full-generator shortcut and its dependency warning

Current `main` also contains a shorter *post-H¹* route:

```lean
weightedMovingHeat_fullGenerator_restart_of_damped_uniform_forcing_ambient_bounded_of_short
paper5WeightedPopulation_continuousOn_of_candidate_window_uniform_forcing
```

from

```text
WholeLineWeightedRegularityBoundedVolterraUniqueness.lean
WholeLineWeightedRegularityCandidateContinuity.lean.
```

This proves actual-state continuity by identifying it with the continuous full
candidate on a short window. It is useful once the full generator forcing is
already available.

It is **not** the right route for the strict H⁰ startup requested here, because
the current natural uniform generator-forcing square producer

```lean
exists_uniform_weightedGeneratorForcing_square_bound_mildFixedPoint_wave
```

uses the weighted `H¹` budget, hence `hWx2`, internally. Using that route to
prove the first `hZcont` would merely hide the forbidden dependency.

---

# 6. Canonical construction of `X` and `hXrep`

Let

```lean
gX q x := paper5WeightedPopulationX eta (coMovingPath c u) U q x.
```

## 6.1 Spatial measurability

For each fixed positive time, `gX q` is continuous. The proof uses:

```text
coMovingPath c u q             C² in space
U                              C² in space
therefore their values and first derivatives are continuous
exp(eta*x)                     continuous.
```

A robust tactic shape is:

```lean
have hXmeas : ∀ q ∈ Set.Icc a b,
    AEStronglyMeasurable (gX q) volume := by
  intro q hq
  have hu0 : Continuous (coMovingPath c u q) := (hu2 q hq).continuous
  have hux : Continuous (deriv (coMovingPath c u q)) :=
    (hu2 q hq).continuous_deriv (by norm_num)
  have hU0 : Continuous U := hU2.continuous
  have hUx : Continuous (deriv U) :=
    hU2.continuous_deriv (by norm_num)
  unfold gX paper5WeightedPopulationX paper5WeightedPopulation
  exact (... continuous expression ...).aestronglyMeasurable
```

In many local contexts, after exposing the definitions, `fun_prop` closes the
continuous expression.

## 6.2 Square integrability and `MemLp`

The needed square-integrability fact is exactly

```lean
hWx2 q hq : Integrable (fun x => gX q x ^ 2) volume.
```

The corresponding Mathlib `MemLp` fact is:

```lean
have hXmem : MemLp (gX q) 2 volume :=
  (memLp_two_iff_integrable_sq (hXmeas q hq)).2 (hWx2 q hq)
```

However, the repository’s canonical constructors take

```text
AEStronglyMeasurable + Integrable square
```

directly, so introducing `hXmem` is optional.

## 6.3 Define the canonical positive-window trajectory

Use:

```lean
let X : ℝ → WholeLineRealL2 :=
  wholeLineRealL2PositiveWindowTrajectory hab gX
```

Then the representative seam is one theorem call:

```lean
have hXrep : ∀ q ∈ Set.Icc a b,
    (((X q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] gX q) := by
  intro q hq
  exact wholeLineRealL2PositiveWindowTrajectory_coe_ae_of_mem
    hab hXmeas hXsq hq
```

This is canonical, but it is not `rfl`. The coercion from an `Lp` class chooses
an a.e. representative, so the correct equality notion is `=ᵐ[volume]` and the
correct bridge is `..._coe_ae_of_mem`.

## 6.4 `hXcont` remains a separate theorem

Defining `X` canonically does not prove continuity. Call

```lean
wholeLineRealL2PositiveWindowTrajectory_continuous
```

only after proving

```lean
hXstrong : ∀ q ∈ Icc a b,
  Tendsto (fun r => ∫ x, (gX r x - gX q x)^2)
    (nhdsWithin q (Icc a b)) (nhds 0).
```

The current repository’s honest endpoint-weight route is in
`WholeLineWeightedRegularityGradientTimeNatural.lean`:

```lean
paper5WeightedPopulationX_strongL2At_of_BUC_moduli_and_tight
paper5WeightedPopulationX_eventually_integrable_and_strongL2At_of_BUC_moduli_and_tight.
```

It correctly requires same-weight square tightness in addition to local BUC
moduli. Per-slice `hWx2` alone does not imply `hXcont`.

---

# 7. Canonical construction of `F` and `hFrep`

For the physical generator forcing, use the specialized trajectory already in

```text
ShenWork/Paper1/WholeLineWeightedRegularityForcingContinuityNatural.lean.
```

Define:

```lean
let F : ℝ → WholeLineRealL2 :=
  paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
    p eta c u v U V hab
```

## 7.1 Spatial measurability

Use:

```lean
paper5WeightedGeneratorForcing_aestronglyMeasurable_of_classical_slices
```

from
`WholeLineWeightedRegularityGeneratorForcingNatural.lean`.
It realizes the differentiated flux by the continuous physical product-rule
expression and combines it with the continuous reaction expression. This is
precisely where positive-time `C²` slices and the wave `C²` data are used.
No weighted time derivative is involved.

## 7.2 Square integrability

The natural static theorem is:

```lean
paper5WeightedGeneratorForcing_data_of_population_H1_natural.
```

Its final two analytic inputs are exactly:

```lean
hclose : Integrable
  (fun x => exp(2*eta*x) * |coMovingPath c u q x - U x|^2)

hWx2 : Integrable
  (fun x => paper5WeightedPopulationX ... q x ^ 2).
```

It returns:

```text
Integrable (fun x => paper5WeightedGeneratorForcing ... q x ^ 2)
and an explicit square bound.
```

Thus the precise answer to “does it follow from `hclose+hWx2`?” is:

- for `X`, square integrability follows directly from `hWx2`;
- for `F`, it follows from `hclose+hWx2` **together with** the bounded physical
  box, classical `C²` slices, wave regularity/tail data, resolver identity, and
  the parameter assumptions required by
  `paper5WeightedGeneratorForcing_data_of_population_H1_natural`;
- it does not follow from the two bare propositions in isolation.

The optional explicit `MemLp` line is again:

```lean
have hFmem : MemLp (gF q) 2 volume :=
  (memLp_two_iff_integrable_sq (hFmeas q hq)).2 (hFsq q hq)
```

## 7.3 Representative seam

The existing theorem is:

```lean
paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_coe_ae.
```

Therefore:

```lean
have hFrep : ∀ q ∈ Set.Icc a b,
    (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V q) := by
  intro q hq
  exact
    paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_coe_ae
      p eta c u v U V hab hFmeas hFsq hq
```

Again, this is not definitional equality; it is the canonical a.e. equality
supplied by the constructor theorem.

## 7.4 `hFcont` is also separate

Use:

```lean
paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_continuous
```

only after proving the scalar strong-`L²` condition `hF_strong` appearing in
its signature. Static square integrability does not imply temporal strong
continuity.

The natural forcing-continuity file already transfers strong population
continuity through the elliptic resolver via

```lean
paper5WeightedSignal_strongL2At_of_population_strongL2At,
```

and the later power/flux continuity lemmas combine the population, gradient,
signal, and signal-gradient strong limits. This ordering is noncircular when
`hZcont` is first obtained by the H⁰ divergence-mild route and `hXcont` is
obtained independently from positive-time gradient regularity.

---

# 8. Recommended concrete assembler wiring

Choose a compact closed positive window `Set.Icc a b` containing the target
and lying inside `(L,R)`, or derive the endpoint data at `L,R` from the global
positive-time producers and use `Icc L R` directly.

Then wire the proof in this order.

## Step A — population spatial data

```lean
have hWmeas := ... Continuous.aestronglyMeasurable ...
have hWsq   := ... paper5WeightedPopulation_sq_integrable_of_weighted_difference ...
```

These are already internal to
`paper5WeightedEnergy_coreIntegrability_of_exactGeneratorWindow_local`.

## Step B — population time continuity, with no `hWx2`

Prove the H⁰ divergence-form weighted mild identity and apply the concrete
weighted heat and heat-gradient Duhamel continuity atoms. Obtain:

```lean
hZcont : ContinuousOn
  (fun q => wholeLineRealL2Total (W q))
  (Set.Ioo L R).
```

If a genuine local common spatial envelope is available, the DCT proof in
Section 3 is an equally sound shorter substitute.

## Step C — gradient trajectory

```lean
let X := wholeLineRealL2PositiveWindowTrajectory hab gX
have hXrep := wholeLineRealL2PositiveWindowTrajectory_coe_ae_of_mem ...
have hXcont := wholeLineRealL2PositiveWindowTrajectory_continuous
  hab hXmeas hXsq hXstrong
```

Here `hXsq` is `hWx2`; `hXstrong` needs the independently proved no-escape or
mild-gradient continuity theorem.

## Step D — forcing trajectory

```lean
let F :=
  paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
    p eta c u v U V hab

have hFrep :=
  paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_coe_ae ...

have hFcont :=
  paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_continuous
    ... hFmeas hFsq hFstrong
```

## Step E — call the local core theorem

Feed `hZcont`, the restrictions of the global `hXcont/hFcont`, and the two
representative equalities into:

```lean
paper5WeightedEnergy_coreIntegrability_of_exactGeneratorWindow_local.
```

That theorem already reconstructs the weighted population measurability and
square-integrability data needed downstream.

---

# 9. False shortcuts to reject

1. **`Continuous -> AEStronglyMeasurable` is valid; `Continuous -> Integrable`
   is not.** The exponential weight is harmless for the first implication and
   decisive for the second.

2. **Separate slice integrability is not a dominated-convergence hypothesis.**
   One needs a common integrable envelope or same-weight uniform tightness.

3. **A uniform bound on `∫ W(q)^2` is not a pointwise dominator.** It does not
   prevent rightward escape.

4. **Continuity of `q ↦ ||W(q)||₂` is not continuity of `q ↦ W(q)` in `L²`.**
   Prove the difference-square limit.

5. **Do not use `hWx2` to manufacture the first `hZcont` through the full
   generator forcing.** That reverses the intended H⁰-to-H¹ dependency even if
   the circularity is hidden inside a package theorem.

6. **Do not use a weighted-population time derivative to prove `hZcont`.** The
   continuous Hilbert trajectory is part of the regularity needed before the
   Hilbert-space derivative/energy identity is justified.

7. **Canonical representatives are not `rfl`.** Use
   `wholeLineRealL2Total_coe_ae`,
   `wholeLineRealL2Section_coe_ae`, or
   `wholeLineRealL2PositiveWindowTrajectory_coe_ae_of_mem`.

8. **Defining `X` and `F` canonically proves only the representative seams.**
   `hXcont` and `hFcont` still require strong `L²` time continuity.

9. **Remember that `wholeLineRealL2Total` is totalized to zero on an invalid
   slice.** Before rewriting its coercion to the explicit function, always
   provide both `AEStronglyMeasurable` and square-integrability for that slice.

# Bottom line

- `hphi_meas`: use the proof already present in
  `paper5WeightedEnergy_coreIntegrability_of_exactGeneratorWindow_local`.
- `hZcont`: DCT is correct only with a real common weighted envelope; the exact
  dominator for the difference square is `4*G^2`. From the currently listed
  hypotheses alone, use a noncircular H⁰ weighted divergence-mild continuity
  theorem instead.
- `hXrep/hFrep`: define canonical positive-window `L²` trajectories and use the
  existing a.e.-representation theorems. `hWx2` supplies the `X` square data;
  `hclose+hWx2`, together with the natural static forcing hypotheses, supplies
  the `F` square data.
- `hXcont/hFcont`: these are genuine strong-`L²` continuity leaves and do not
  follow merely from choosing canonical representatives.