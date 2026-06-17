═══ BRIDGE cron | 072b580d | 11007 chars 1833 words 412 lines | 618s | prov=network | OK ═══
═══ BRIDGE cron | 072b580d | 11007 chars 1833 words 412 lines | 618s | prov=network | OK ═══
## Bottom line

The paper’s lower-solution proof is for the **paper auxiliary parabolic operator** `A(W;u)`, i.e. the operator encoded by `paperWaveOperator`, not for the repo’s current Rothe step based on `frozenWaveOperator`.

So the faithful fix is:

```lean
def paperImplicitStepOp (p : CMParams) (c h : ℝ)
    (u W : ℝ → ℝ) : ℝ → ℝ :=
  fun x => W x - h * paperWaveOperator p c u W x
```

and then build the lower comparison / dual maximum principle for `paperImplicitStepOp`, or bypass the discrete Rothe layer and formalize the paper’s continuous-time auxiliary parabolic map directly.

Do **not** try to infer frozen lower-invariance from `paperWaveOperator φ ≥ 0`: the operator difference has the wrong sign for that implication.

---

## (1) What is the paper’s actual map?

For fixed frozen profile `u ∈ E'_{κ,1}`, the paper defines `u(t,x; U⁺_{κ,1}, u)` as the solution of the parabolic problem

```text
w_t =
  w_xx + c w_x
  - χ m w^{m-1} w_x V_x
  - χ w^m V
  + χ w^{m+γ}
  + w(1 - w^α),
```

with initial condition

```text
w(0,x) = U⁺_{κ,1}(x),
```

where

```text
V(x) = Ψ(x; u^γ, 1, 1)
```

is frozen from the input profile `u`. This is equation (4.12) in the paper. citeturn261620view0

Then the paper proves, by Lemmas 4.1 and 4.2 plus parabolic comparison, that

```text
U⁻_{κ,κ~,D}(x)
≤ u(t,x; U⁺_{κ,1}, u)
≤ U⁺_{κ,1}(x)
```

for all `t ≥ 0`, `x ∈ ℝ`. citeturn261620view1turn261620view3

It then defines the Schauder map by the long-time limit:

```text
U(x;u) := lim_{t→∞} u(t,x; U⁺_{κ,1}, u),
T_{κ,1} u := U(·;u).
```

The paper explicitly says `T_{κ,1} : E'_{κ,1} → E'_{κ,1}` is the map to which Schauder is applied. citeturn261620view2

So the comparison principle used for preserving `U⁻ ≤ w ≤ U⁺` is the parabolic comparison principle for **equation (4.12)**, i.e. for `paperWaveOperator`.

In repo terms, equation (4.12) corresponds to:

```lean
paperWaveOperator p c u W
```

whose definition has the `W^(m+γ-1)` / `W^(m+γ)` paper term. fileciteturn126file0L54-L60

It is not the same off-diagonal operator as:

```lean
frozenWaveOperator p c u W
```

which keeps the literal divergence form

```lean
- χ * deriv (fun y => W y ^ m * deriv (frozenElliptic p u) y)
+ W * (1 - W ^ α).
```

fileciteturn126file0L47-L52

---

## (2) Cleanest Lean bridge

### Best faithful route: build the paper version

Define a paper-step operator:

```lean
def paperImplicitStepOp (p : CMParams) (c h : ℝ)
    (u W : ℝ → ℝ) : ℝ → ℝ :=
  fun x => W x - h * paperWaveOperator p c u W x
```

Then prove the direct lower-barrier maximum principle:

```lean
theorem paperImplicitStep_ge_of_barrier_maxPrinciple
    (p : CMParams)
    {c h M C : ℝ} {u Z W φ : ℝ → ℝ} {x₀ : ℝ}
    (hh : 0 < h)
    (hCsmall : h * C < 1)
    (hstep : ∀ x, paperImplicitStepOp p c h u W x = Z x)
    (hφsub : ∀ x, 0 ≤ paperWaveOperator p c u φ x)
    (hφZ : ∀ x, φ x ≤ Z x)
    -- negative minimum data for W - φ:
    (hattain : IsMinOn (fun x => W x - φ x) Set.univ x₀)
    (hloc : IsLocalMin (fun x => W x - φ x) x₀)
    (hderiv2 : iteratedDeriv 2 φ x₀ ≤ iteratedDeriv 2 W x₀)
    -- one-sided operator estimate at the negative minimum:
    (hone :
      paperWaveOperator p c u W x₀ - paperWaveOperator p c u φ x₀
        ≥ C * (W x₀ - φ x₀)) :
    ∀ x, φ x ≤ W x := by
  ...
```

This is the exact dual of the existing frozen upper-barrier maximum principle. The existing theorem is built for

```lean
implicitStepOp p c h u W = W - h * frozenWaveOperator p c u W
```

and assumes a frozen super-barrier `frozenWaveOperator p c u B ≤ 0`. fileciteturn121file0L79-L85 fileciteturn121file0L150-L185

The paper lower-solution theorem you proved should feed:

```lean
hφsub : ∀ x, 0 ≤ paperWaveOperator p c u Uminus x
```

directly into this paper-step maximum principle.

### Green-map analogue, if you need a fixed-point step

The current `crossImplicitMap` is also frozen-divergence based:

```lean
∫ K * (reactionFun(W) + λZ)
  - χ ∫ K' * (W^m * V_u')
```

fileciteturn125file0L16-L30

For the paper operator, define:

```lean
def paperCrossImplicitMap
    (p : CMParams) (c lam : ℝ)
    (u Z W : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    (∫ y, greenKernel c lam (x - y) *
      (reactionFun p.α (W y)
        + p.χ * (W y)^p.m * ((W y)^p.γ - (u y)^p.γ)
        + lam * Z y))
    - p.χ * ∫ y, greenKernelDeriv c lam (x - y) *
      ((W y)^p.m * deriv (frozenElliptic p u) y)
```

because

```text
paperWaveOperator p c u W
= frozenWaveOperator p c u W
  + χ W^m (W^γ - u^γ).
```

The new source term is therefore

```text
χ W^m (W^γ - u^γ).
```

Then prove:

```lean
theorem paperCrossImplicitMap_fixed_iff_paperImplicitStep
```

analogous to the current `crossImplicitMap` / `implicitStepOp` bridge.

### Least Lean infrastructure?

If you want to stay faithful to the paper, the least painful route is:

```text
paperWaveOperator lower-solution estimate
→ paper parabolic/implicit comparison
→ paper long-time map Tκ,1 preserves E'
→ Schauder fixed point
→ at fixed point, paper operator = actual stationary operator
```

So: **option (a)** if you keep the discrete Rothe layer; **option (c)** if you are willing to formalize the paper’s continuous-time map. The current option (b), proving the two operators agree during comparison, is not valid off-diagonal.

---

## (3) Is the current frozen Rothe step the right discretization?

For the paper’s lower-solution construction: **no**.

The current repo Rothe step is explicitly documented as the implicit Euler step for

```text
F_u(W) = W'' + cW' − χ ∂x(W^m V_u') + W(1 − W^α),
```

i.e. `frozenWaveOperator`. fileciteturn124file0L10-L24

But the paper’s equation (4.12) is

```text
w_t =
  w_xx + c w_x
  - χ m w^{m-1} w_x V_x
  - χ w^m V
  + χ w^{m+γ}
  + w(1 - w^α),
```

i.e. `paperWaveOperator`. citeturn261620view0

These two agree only when `W = u`, because

```text
paperWaveOperator(p,c,u,W)
= frozenWaveOperator(p,c,u,W)
  + χ W^m (W^γ - u^γ).
```

At a final fixed point with frozen input `u = W`, the extra term vanishes. That is exactly why the repo has a final bridge from frozen stationarity to paper-form stationarity at the fixed point. fileciteturn131file0L90-L108

But during lower-barrier comparison, `W` is the iterate/solution being compared and `u` is the frozen input. They are not equal.

Even worse, the sign does not rescue the frozen step. If the frozen input is lower-pinned and the barrier satisfies `φ ≤ u`, then for `W = φ`,

```text
paper(φ;u) - frozen(φ;u)
= χ φ^m (φ^γ - u^γ).
```

For `χ ≤ 0` and `φ ≤ u`, we have `φ^γ - u^γ ≤ 0`, hence

```text
paper(φ;u) - frozen(φ;u) ≥ 0,
```

so

```text
frozen(φ;u) ≤ paper(φ;u).
```

Thus

```text
paper(φ;u) ≥ 0
```

does **not** imply

```text
frozen(φ;u) ≥ 0.
```

That is the wrong direction for a lower-barrier maximum principle.

At a hypothetical negative minimum of `W - φ`, you similarly have `W < φ ≤ u`, and the frozen operator is below the paper operator, so a frozen-step solution is not automatically a supersolution of the paper comparison problem. So option (b) fails except at the final diagonal `W = u`.

---

## Concrete Lean plan

### Step 1: Add the algebraic difference lemma

```lean
theorem paperWaveOperator_eq_frozenWaveOperator_add_extra
    (p : CMParams) (c : ℝ) (u W : ℝ → ℝ)
    -- differentiability hypotheses needed to expand deriv(W^m V')
    :
    paperWaveOperator p c u W x
      =
    frozenWaveOperator p c u W x
      + p.χ * (W x)^p.m * ((W x)^p.γ - (u x)^p.γ) := by
  -- use frozenElliptic_deriv_deriv_eq:
  -- V'' = V - u^γ
  ...
```

You will need the usual product-rule differentiability assumptions for `W^m` and `V'`. The repo already has `V'' = V - u^γ` as `frozenElliptic_deriv_deriv_eq`. fileciteturn126file0L20-L26

This lemma is not for proving lower invariance from frozen; it is for making the discrepancy explicit and for diagonal finalization.

### Step 2: Define the paper implicit step

```lean
def paperImplicitStepOp (p : CMParams) (c h : ℝ)
    (u W : ℝ → ℝ) : ℝ → ℝ :=
  fun x => W x - h * paperWaveOperator p c u W x
```

### Step 3: Clone the maximum-principle skeleton

Reuse the same structure as

```lean
implicitStep_le_of_barrier_maxPrinciple
```

but with `paperWaveOperator` and the lower-barrier negative-minimum sign. The existing theorem’s proof is algebraic once the one-sided estimate is supplied. fileciteturn121file0L170-L185

Name it something like:

```lean
paperImplicitStep_ge_of_barrier_maxPrinciple
```

### Step 4: Define paper map data, not frozen map data

For the faithful paper route, your Schauder data should be for:

```lean
PaperStationaryMapSchauderData
```

not for the existing `FrozenStationaryMapSchauderData`, unless you intentionally choose a different theorem than the paper.

Possible shape:

```lean
def PaperStationaryMapSchauderData
    (p : CMParams) (c lam : ℝ)
    (trap : (ℝ → ℝ) → Prop)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ) : Prop :=
  (∀ u, trap u → trap (Tmap u))
  ∧ (∀ u, trap u → paperAuxMap p c lam u (Tmap u) (Tmap u) = Tmap u)
  ∧ LocalUniformContinuousOn trap Tmap
  ∧ LocalUniformSequentiallyCompactRange trap Tmap
```

or, closer to the paper:

```lean
def PaperLongTimeMapData ... :=
  ∀ u ∈ E', ∃ w,
    SolvesPaperParabolic412 p c u Uplus w
    ∧ (∀ t x, Uminus x ≤ w t x ∧ w t x ≤ Uplus x)
    ∧ Tendsto (fun t => w t) atTop (𝓝 (Tmap u))
```

### Step 5: Final diagonal bridge

Once Schauder gives

```lean
Tmap U = U
```

and the limiting stationary equation is

```lean
∀ x, paperWaveOperator p c U U x = 0,
```

prove the actual frozen/stationary equation by diagonal equality:

```lean
theorem frozenWaveOperator_eq_paperWaveOperator_at_diagonal
    ... :
    frozenWaveOperator p c U U x = paperWaveOperator p c U U x := by
  -- extra term χ U^m (U^γ - U^γ) = 0
```

Then feed the existing wave-profile assembly.

---

## Answer to the three options

**(a) Build `implicitStep_ge_of_paperBarrier_maxPrinciple`: yes.**  
This is the right discrete analogue if you keep a Rothe scheme.

**(b) Prove frozen/paper agree during comparison: no.**  
They agree only on the diagonal `W = u`. Off-diagonal, the extra term has a sign, but the sign goes the wrong way for deriving a frozen lower subsolution from a paper lower subsolution.

**(c) Reformulate lower-invariance on the paper auxiliary parabolic map: yes, most faithful.**  
This matches equation (4.12), the proof of (4.14), the long-time definition of `Tκ,1`, and the Schauder fixed point in `E'κ,1`. citeturn261620view0turn261620view2

So the recommended Lean path is:

```text
For paper fidelity:
  introduce paper operator/map layer;
  prove lower/upper trapping there;
  apply Schauder there;
  use diagonal equality only at the final fixed point.

For minimal code reuse:
  clone current frozen implicit max-principle to paperWaveOperator,
  then replace the lower-pinned Rothe data with paper-pinned Rothe data.
```

The current frozen Rothe step is a real discrepancy for Lemma 4.2-based nontriviality; it is not just an algebraic bridge waiting to be filled.
