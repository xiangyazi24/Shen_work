## Core diagnosis

The weak/viscosity route does **not** remove the structural obstruction for the **literal frozen divergence operator**. The problem is not merely that the comparison is not classical; it is that the shifted frozen coefficient is not ordered in the way the comparison needs.

The existing Green facts give the right 1-D shortcut **if the source is antitone/distributionally antitone**. The repo already has this: convolution is written in shifted form, and `implicitStep_preserves_antitone` proves that an antitone Green source gives an antitone step solution. fileciteturn170file0L4-L16 fileciteturn162file0L14-L44 But for the actual chemotaxis source, that antitone source condition is not a consequence of `u`, `Z`, and `W` being monotone.

So: **full Crandall–Ishii viscosity theory is overkill, but a weak kernel-source comparison also does not close under the frozen operator.** The dischargeable path is either:

```text
A. use the paper-expanded operator and prove monotonicity by a derivative/weak-derivative maximum principle, preferably via smooth approximation; or

B. keep the frozen operator but add a genuine extra monotonicity/shift-source hypothesis.
```

Under only the current frozen-trap hypotheses, there is no sign-complete proof of `Antitone W`.

---

## (1) Why the Green-integral shortcut does not close

For any source `R`,

```text
W(x) = ∫ Kλ(x-y) R(y) dy
```

implies

```text
W(x+s) - W(x)
= ∫ Kλ(x-y) (R(y+s) - R(y)) dy.
```

Since `Kλ ≥ 0`, this proves `W(x+s) ≤ W(x)` if

```text
R(y+s) ≤ R(y)     for all y.
```

This is the current single-shot lemma in the repo: source antitone plus kernel positivity gives step antitone. fileciteturn162file0L14-L44

For the frozen divergence source,

```lean
crossSource p lam u Z W y =
  reactionFun p.α (W y) + lam * Z y
    - p.χ * deriv (fun t =>
        (W t)^p.m * deriv (frozenElliptic p u) t) y
```

fileciteturn160file0L85-L92

as distributions,

```text
R_s - R
= [reaction(W_s)-reaction(W)]
  + λ[Z_s-Z]
  - χ ∂x[W_s^m V_s' - W^m V'].
```

After integrating by parts against the kernel,

```text
K * (R_s - R)
= K * ([reaction diff] + λ[Z_s-Z])
  - χ K' * [W_s^m V_s' - W^m V'].
```

This does **not** have a sign:

1. `reaction(W)` is not antitone as a function of an antitone `W`; `r ↦ r(1-r^α)` rises and then falls.
2. `Kλ'` changes sign.
3. `V_s' - V'` has no sign. The repo proves `V` is antitone and `V'≤0`, but this gives no order between `V'(x+s)` and `V'(x)`. fileciteturn168file0L104-L132

The proposed IBP is still useful for regularity and for writing the fixed-point map without differentiating `W`, but it does not create a positive-kernel comparison. The term with `Kλ'` is the same obstruction in integrated form.

A clean weak criterion would be:

```lean
-- distributional/source version
∀ s ≥ 0, ∀ x,
  ∫ y, greenKernel c lam (x-y) * (R (y+s) - R y) ≤ 0
```

but for `R = crossSource u Z W` this is essentially the desired monotonicity statement in source form, not something implied by `u` antitone.

---

## (2) Weak formulation: what would be enough?

A minimal 1-D weak criterion is:

```text
D R ≤ 0 as a signed measure
```

because then

```text
D W = D(K * R) = K * D R ≤ 0
```

in the distributional sense, since `K ≥ 0`. Equivalently,

```text
for every nonnegative compactly supported test φ,
  -∫ R φ' ≤ 0.
```

Then `W` is antitone.

In Lean-ish form:

```lean
def DistributionallyAntitone (R : ℝ → ℝ) : Prop :=
  ∀ φ : TestFunction ℝ,
    (∀ x, 0 ≤ φ x) →
      -∫ x, R x * deriv φ x ≤ 0

theorem greenConv_antitone_of_distributional_source
    (hKpos : ∀ x, 0 ≤ greenKernel c lam x)
    (hR : DistributionallyAntitone R)
    :
    Antitone (fun x => greenConv c lam R x)
```

But the frozen source does not satisfy this from the available assumptions. Its distributional derivative contains, morally,

```text
D[reaction(W)] + λ DZ - χ D²(W^m V')
```

and the chemotaxis part has no sign. If you expand using `V'' = V-u^γ`, the derivative of the frozen zeroth-order term brings in `D(u^γ)`, which is a negative measure; with `χ≤0` it appears with a **bad positive forcing** that is not proportional to `W'`.

This is exactly why the paper-expanded operator is more suitable: it replaces the off-diagonal frozen `u^γ` term by a diagonal `W^γ` term, so the derivative terms become proportional to `q = W'` and can be controlled by a maximum principle.

---

## (3) Minimal replacement for full viscosity theory

You do **not** need full viscosity theory for the 1-D problem. The smallest workable replacement is:

```text
smooth approximation of the old iterate Z
+ classical derivative maximum principle for the smooth approximating steps
+ continuous dependence of the Green/Banach step on Z
+ uniform/pointwise limit of antitone functions is antitone.
```

This avoids Crandall–Ishii doubling entirely.

### Step A: smooth monotone approximation

For a continuous antitone `Z`, choose a nonnegative mollifier `ρ_ε` and define

```text
Z_ε = ρ_ε * Z.
```

Then:

```text
Z_ε ∈ C∞,
Z_ε is antitone,
(Z_ε)' ≤ 0,
Z_ε → Z locally uniformly.
```

Lean theorem shape:

```lean
theorem mollify_antitone
    (hZ : Antitone Z) :
    Antitone (mollify ε Z) ∧ ∀ x, deriv (mollify ε Z) x ≤ 0
```

This is much smaller than viscosity theory: it is positivity of convolution with a nonnegative kernel.

### Step B: solve the smooth paper step

For each `Z_ε`, solve the implicit step with the **paper-expanded operator**, not the frozen divergence operator:

```text
W_ε - h * paperWaveOperator p c u W_ε = Z_ε.
```

The repo already has the paper step layer:

```lean
paperStepNonlinearity
paperStepSource
paperImplicitStepOp_of_greenConv_source
PaperStepAnalyticCore
```

including the Green source/regularity packaging. fileciteturn163file0L43-L64 fileciteturn166file0L25-L67

### Step C: classical derivative maximum principle

Let

```text
q = W_ε'.
```

Assume the regularity needed to differentiate the paper step; practically:

```text
W_ε ∈ C³,
V ∈ C²,
Z_ε ∈ C¹,
0 ≤ W_ε ≤ M,
V' ≤ 0,
|V| ≤ B_V,
|V''| ≤ B_V2.
```

At a positive maximum of `q`, one has

```text
q > 0, q' = 0, q'' ≤ 0.
```

For the paper operator,

```text
A_V(W)
= W'' + cW'
  + a m W^{m-1} V' W'
  + reaction(W)
  + a W^m(V - W^γ),
```

where `a = -χ ≥ 0`.

At a positive maximum of `q`,

```text
(A_V(W))'
≤ Cmono * q,
```

with for example

```text
Cmono =
  reactionLip(α,M)
  + a*m*M^{m-1}*(B_V2 + B_V).
```

Reason:

```text
q'' ≤ 0,
c q' = 0,
a*m*(m-1)W^{m-2}q²V' ≤ 0   because V'≤0,
a*m*W^{m-1}V'q' = 0,
a*W^m V' ≤ 0,
-a*(m+γ)W^{m+γ-1}q ≤ 0,
```

and the remaining terms are bounded by the displayed `Cmono*q`.

Differentiate the step:

```text
q - h*(A_V(W))' = Z_ε' ≤ 0.
```

Thus at a positive maximum,

```text
q ≤ h*Cmono*q.
```

If

```text
h*Cmono < 1,
```

this contradicts `q>0`. Therefore `q≤0`, hence `W_ε` is antitone.

Lean theorem shape:

```lean
theorem paperStep_antitone_smooth
    (hlam : 0 < lam)
    (hχ : p.χ ≤ 0)
    (hstep : ∀ x, paperImplicitStepOp p c (1/lam) u W x = Z x)
    (hZderiv : ∀ x, deriv Z x ≤ 0)
    (hWreg : ContDiff ℝ 3 W)
    (hVreg : ContDiff ℝ 2 (frozenElliptic p u))
    (hVderiv_nonpos : ∀ x, deriv (frozenElliptic p u) x ≤ 0)
    (hWrange : ∀ x, W x ∈ Set.Icc (0:ℝ) M)
    (hVbound : ∀ x, |frozenElliptic p u x| ≤ BV)
    (hV2bound : ∀ x, |deriv (deriv (frozenElliptic p u)) x| ≤ BV2)
    (hsmall : (1/lam) *
        (reactionLip p.α M + (-p.χ)*p.m*M^(p.m-1)*(BV2+BV)) < 1)
    (hqtails : derivative_tails_nonpos W) :
    Antitone W
```

### Step D: pass to the nonsmooth `Z`

Use continuous dependence of the contraction fixed point on the old iterate:

```text
‖W_ε - W‖∞ ≤ C ‖Z_ε - Z‖∞.
```

Then `W_ε → W` locally uniformly or uniformly, and a pointwise limit of antitone functions is antitone:

```lean
theorem antitone_of_pointwise_limit
    (hεanti : ∀ ε, Antitone (Wε ε))
    (hlim : ∀ x, Tendsto (fun ε => Wε ε x) ... (𝓝 (W x))) :
    Antitone W :=
by
  intro x y hxy
  exact le_of_tendsto_of_tendsto
    (hlim y) (hlim x)
    (eventually_of_forall fun ε => hεanti ε hxy)
```

This is the minimal “weak/viscosity” substitute: no doubling of variables, no semicontinuous envelopes, no viscosity library.

---

## Why this does not work for the literal frozen operator

If you insist on differentiating the literal frozen divergence operator

```text
W'' + cW' - χ ∂x(W^m V_u') + reaction(W),
```

and use

```text
V'' = V - u^γ,
```

then differentiating introduces a term involving

```text
D(u^γ)
```

or, in a smooth approximation,

```text
(u^γ)'.
```

Since `u` is antitone, `(u^γ)' ≤ 0`, and with `χ≤0` the corresponding term has the **wrong sign** as a forcing independent of `q = W'`. It cannot be absorbed by `C*q` at a positive maximum of `q`.

That is the structural reason the frozen off-diagonal operator is not the right layer for proving monotonicity preservation. At the final diagonal `W=u`, the paper and frozen operators agree; but during the per-step comparison, they do not.

---

## Answer to the three questions

### (1) Does the Green integral reduce to a weak source comparison that closes?

It reduces to a weak source comparison, but that comparison does **not** close for `crossSource`. The derivative has no sign; `K'` changes sign; `V_s' - V'` is unordered. IBP moves the derivative, but it does not make the chemotaxis contribution positive.

### (2) Is there a clean weak monotonicity criterion?

Yes:

```text
DistributionallyAntitone R ⇒ Antitone (K * R).
```

In shift form:

```text
∀ s ≥ 0, ∀ x,
  ∫ K(x-y) (R(y+s)-R(y)) dy ≤ 0
⇒ Antitone (K*R).
```

But `R = reaction(W)+λZ-χ∂x(W^mV')` does not satisfy this from `u,Z,W` monotone. The criterion is useful as an abstract lemma, not as the final chemotaxis proof.

### (3) Is full viscosity unavoidable?

No. For 1-D, the minimal machinery is a **smooth approximation + derivative maximum principle + limit**. But it should be done for the **paper-expanded operator**. For the literal frozen operator, the monotonicity theorem is not dischargeable from the stated hypotheses; one must either add a true monotonicity residual or switch to the paper operator layer for the per-step map.
