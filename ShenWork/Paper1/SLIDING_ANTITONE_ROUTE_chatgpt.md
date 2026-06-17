The sliding idea is the right **shape**, but with a frozen chemical it is **not closed from `u` antitone alone**. The frozen field gives useful one-sided facts,

```lean
Antitone (frozenElliptic p u)
∀ x, deriv (frozenElliptic p u) x ≤ 0
```

and the repo already proves exactly these from `InMonotoneWaveTrapSet`. fileciteturn168file0L104-L132 But that is not enough to compare the shifted flux term, because the shifted derivative `(V_u)'(x+s)` is not ordered against `(V_u)'(x)`.

## 1. What `W_s` actually solves

Let

```lean
W_s x := W (x + s)
Z_s x := Z (x + s)
V x   := frozenElliptic p u x
V_s x := V (x + s)
```

Then `W_s` solves the **shifted-frozen** step:

```text
W_s - h A_{V_s}(W_s) = Z_s,
```

not the original step

```text
W - h A_V(W) = Z.
```

So the comparison `W_s ≤ W` cannot be a pure translation argument.

From `Z` antitone we do get:

```text
s ≥ 0 ⇒ Z_s ≤ Z.
```

From `u` antitone we get:

```text
V_s ≤ V,
V' ≤ 0,
V_s' ≤ 0.
```

The repo proves `V` antitone and then `V'≤0` by writing `V` as a positive convolution of `u^γ`. fileciteturn168file0L6-L25

But the missing comparison is:

```text
V_s'(x) ? V'(x)
```

and antitonicity of `V` gives **no order** between these two derivatives. That is the obstruction.

For the expanded paper operator, with `χ = -a`, `a ≥ 0`,

```text
A_V(W)
= W'' + cW'
  + a m W^{m-1} V' W'
  + reaction(W)
  + a W^m (V - W^γ).
```

For the same `W`, the frozen-shift discrepancy is

```text
A_{V_s}(W) - A_V(W)
= a m W^{m-1} (V_s' - V') W'
  + a W^m (V_s - V).
```

The second term is good because `V_s ≤ V`, hence

```text
a W^m (V_s - V) ≤ 0.
```

The first term has no sign unless you also know something like

```text
(V_s' - V') * W' ≤ 0.
```

But `W'≤0` is exactly what you are trying to prove, and even if you already had it, you would need `V_s' ≥ V'`, i.e. monotonicity of `V'`, which does not follow from `u` antitone.

So the answer to (1) is:

```text
u antitone ⇒ V antitone and V'≤0, yes.
u antitone ⇒ shifted chemotaxis term is ordered, no.
```

The sliding lemma needs an additional frozen-shift compatibility hypothesis; it is not a consequence of the current trap hypotheses.

## 2. Exact comparison inequality needed

There are two clean forms.

### Strong global source-order form

For the divergence-form frozen Green step, define the source

```lean
crossSource p lam u Z W y =
  reactionFun p.α (W y) + lam * Z y
    - p.χ * deriv (fun t =>
        (W t)^p.m * deriv (frozenElliptic p u) t) y
```

The repo has this source definition. fileciteturn160file0L85-L92

A sufficient sliding hypothesis is:

```lean
∀ s ≥ 0, ∀ y,
  crossSource p lam u_s Z_s W_s y
    ≤ crossSource p lam u Z W y
```

plus the two Green representations. Then resolvent positivity gives immediately:

```lean
W_s ≤ W.
```

The repo already has the comparison engine:

```lean
implicitStep_comparison
```

which proves `W ≤ B` from Green representations and source order. fileciteturn160file0L93-L109

This is the cleanest *if* source order is available. But as above, source order is not derivable from `u` antitone alone.

### Local maximum-principle form

A weaker and more useful hypothesis is the shifted-operator one-sided estimate:

```lean
def ShiftedFrozenOneSided
    (p : CMParams) (c h C : ℝ)
    (u Z W : ℝ → ℝ) : Prop :=
  ∀ s, 0 ≤ s →
    ∀ x₀,
      IsMaxOn (fun x => W (x+s) - W x) Set.univ x₀ →
      0 < W (x₀+s) - W x₀ →
        A_{u_s} (W_s) x₀ - A_u W x₀
          ≤ C * (W (x₀+s) - W x₀)
```

where `A` is either `frozenWaveOperator` or `paperWaveOperator`, consistently with the step.

Then the comparison proof is algebraic. At a positive maximum of

```text
φ(x) = W(x+s) - W(x),
```

the two step equations give:

```text
W_s(x₀) - h A_{u_s}(W_s)(x₀) = Z_s(x₀)
W(x₀)   - h A_u(W)(x₀)       = Z(x₀)
```

and since `Z_s(x₀) ≤ Z(x₀)`,

```text
Δ - h (A_{u_s}(W_s) - A_u(W)) ≤ 0,
```

where `Δ = W_s(x₀)-W(x₀)>0`.

If

```text
A_{u_s}(W_s) - A_u(W) ≤ C Δ
```

and

```text
h*C < 1,
```

then

```text
0 ≥ Δ - h(A_{u_s}(W_s)-A_u(W))
  ≥ (1-hC)Δ > 0,
```

contradiction.

This is the exact sliding/max-principle lemma to formalize:

```lean
theorem implicitStep_preserves_antitone_by_shift
    (hh : 0 < h)
    (hsmall : h * C < 1)
    (hstep : ∀ x, implicitStepOp p c h u W x = Z x)
    (hZanti : Antitone Z)
    (hshift :
      ∀ s, 0 ≤ s →
        ∀ x₀,
          IsMaxOn (fun x => W (x+s) - W x) Set.univ x₀ →
          0 < W (x₀+s) - W x₀ →
            frozenWaveOperator p c (shift u s) (shift W s) x₀
              - frozenWaveOperator p c u W x₀
              ≤ C * (W (x₀+s) - W x₀))
    -- continuity/tails to attain positive max:
    :
    Antitone W
```

For the paper step, replace `implicitStepOp` and `frozenWaveOperator` by:

```lean
paperImplicitStepOp
paperWaveOperator
```

The repo’s paper producer already uses this style of clean maximum principle: the upper/lower comparison data carries one-sided paper operator estimates at extrema rather than trying to prove raw source signs. fileciteturn164file0L18-L55

## 3. Does `u` antitone imply the needed shifted estimate?

Not without extra structure.

You can decompose:

```text
A_{V_s}(W_s) - A_V(W)
= [A_{V_s}(W_s) - A_{V_s}(W)]
  + [A_{V_s}(W) - A_V(W)].
```

The first bracket is the normal one-sided increment and can be bounded by

```text
C * (W_s - W)
```

at a positive maximum, with the same kind of reaction/chemotaxis Lipschitz estimates already used in the max-principle files.

The second bracket is the frozen-shift coefficient discrepancy. For the paper operator:

```text
A_{V_s}(W) - A_V(W)
= (-χ) m W^{m-1} (V_s' - V') W'
  + (-χ) W^m (V_s - V).
```

The `V_s - V` term is good. The `(V_s' - V') W'` term is uncontrolled from `u` antitone alone.

Thus a correct proof must either carry or prove a hypothesis like:

```lean
frozenShiftFluxCompat :
  ∀ s, 0 ≤ s →
    ∀ x₀,
      IsMaxOn (fun x => W (x+s) - W x) Set.univ x₀ →
        (-p.χ) * p.m * (W x₀)^(p.m-1)
          * (deriv V (x₀+s) - deriv V x₀)
          * deriv W x₀
        + (-p.χ) * (W x₀)^p.m * (V (x₀+s) - V x₀)
        ≤ 0
```

or a more flexible version bounded by `C_shift * Δ`.

But if it is bounded by a positive constant independent of `Δ`, the standard maximum-principle contradiction will not close, because the positive maximum could be arbitrarily small. For the clean argument you need either a nonpositive coefficient-shift term or a term proportional to `Δ`.

## 4. Direct derivative route is worse

Differentiating the step to prove `W'≤0` is not cleaner in Lean.

It would require differentiating:

```text
W - hA(W;u) = Z
```

and then proving a maximum principle for `q = W'`.

Problems:

1. The old iterate `Z` in the per-step construction is only continuous and antitone, not classically differentiable. So `Z'≤0` is not available pointwise.
2. Differentiating the chemotaxis flux introduces higher derivatives of `V_u`, and hence more regularity/integrability obligations.
3. The differentiated reaction term has coefficient `1 - (α+1)W^α`, which changes sign.
4. In the paper-expanded operator, differentiating creates terms involving `V''`, `V'''`, `W''`, and power-chain-rule obligations.

The sliding/max-principle route only needs continuity, extrema, and the original second-order operator. It is much better aligned with the existing `paperImplicitStep_*_maxPrinciple` infrastructure.

## 5. Recommended Lean formalization

Do **not** put the burden back on `R_anti`. The current sufficient lemma

```lean
implicitStep_preserves_antitone :
  W = ∫ K R →
  Antitone R →
  Antitone W
```

is correct but too strong. fileciteturn162file0L32-L44

Instead, define a step monotonicity data packet:

```lean
structure PaperStepShiftData
    (p : CMParams) (c lam M Cshift : ℝ)
    (u Z W : ℝ → ℝ) : Prop where
  φcont :
    ∀ s, 0 ≤ s → Continuous (fun x => W (x+s) - W x)
  tails :
    ∀ s, 0 ≤ s →
      ∃ La Lb,
        Tendsto (fun x => W (x+s) - W x) atBot (𝓝 La) ∧ La ≤ 0 ∧
        Tendsto (fun x => W (x+s) - W x) atTop (𝓝 Lb) ∧ Lb ≤ 0
  shifted_one_sided :
    ∀ s, 0 ≤ s →
      ∀ x₀,
        IsMaxOn (fun x => W (x+s) - W x) Set.univ x₀ →
        0 < W (x₀+s) - W x₀ →
          paperWaveOperator p c (shift u s) (shift W s) x₀
            - paperWaveOperator p c u W x₀
            ≤ Cshift * (W (x₀+s) - W x₀)
  small :
    (1 / lam) * Cshift < 1
```

Then prove:

```lean
theorem paperStep_antitone_of_shiftData
    (hlam : 0 < lam)
    (hstep : ∀ x, paperImplicitStepOp p c (1/lam) u W x = Z x)
    (hZanti : Antitone Z)
    (hshift : PaperStepShiftData p c lam M Cshift u Z W) :
    Antitone W
```

Proof:

```text
Assume ∃ x₁≤x₂ with W x₁ < W x₂.
Set s = x₂-x₁ ≥ 0.
Then φ(x)=W(x+s)-W(x) is positive somewhere.
Use tails to get a positive global maximum x₀.
At x₀, use shifted step equation and unshifted step equation.
Z(x₀+s)≤Z(x₀).
Use shifted_one_sided and smallness for contradiction.
```

For the frozen divergence version, define the same packet with `frozenWaveOperator`.

### What hypotheses on `u` are actually useful?

From `InMonotoneWaveTrapSet κ M u` you can prove:

```lean
Antitone u
Antitone (fun x => (u x)^p.γ)
Antitone (frozenElliptic p u)
∀ x, deriv (frozenElliptic p u) x ≤ 0
∀ s≥0, frozenElliptic p u (x+s) ≤ frozenElliptic p u x
```

The repo already proves the key `V` facts. fileciteturn168file0L96-L132

But for shift comparison you still need one extra coefficient-shift control involving `V'`:

```text
(V'(x+s)-V'(x)) * W'(x) ≤ controlled.
```

So the honest statement is:

```text
InMonotoneWaveTrapSet u is necessary but not sufficient.
Add `PaperStepShiftData` / `FrozenStepShiftData` as the exact residual, or prove a separate lemma that supplies its `shifted_one_sided` field from stronger assumptions on V.
```

## Final answer

The sliding comparison is still the most Lean-friendly route, but **not** in the naive translation-invariant form. The correct lemma compares a shifted solution of the shifted-frozen problem with the unshifted solution and requires a local shifted-operator one-sided estimate. The facts `u` antitone ⇒ `V` antitone and `V'≤0` are true and already proved, but they do **not** order `V'(x+s)` against `V'(x)`, so they do not by themselves control the chemotaxis shift term.

The derivative route is heavier and less compatible with the available regularity. Refactor the per-step floor to carry/prove `PaperStepShiftData` and derive `Antitone W` from that, rather than requiring `R_anti`.
