## Verdict

The finite-shift `hshift` is **not dischargeable from the current trap hypotheses**. The term

```text
a*m*(W_s^{m-1} V_s' - W^{m-1} V')*W'
```

contains a coefficient-shift piece

```text
a*m*W^{m-1}*(V_s' - V')*W',
```

and `u` antitone gives `V` antitone and `V'≤0`, but it does **not** compare `V'(x+s)` and `V'(x)`. The repo already proves the true available facts: `frozenElliptic p U` is antitone on the monotone trap, and therefore its derivative is nonpositive. fileciteturn168file0L104-L132

The clean route is the **infinitesimal derivative maximum principle for `q = W'`**, but it requires stronger regularity than the current bare Rothe floor: essentially `Z` differentiable with `Z'≤0`, `W` regular enough that `q` has a classical second derivative, and bounded `V`, `V'`, `V''`. If you only know `Z` is antitone/continuous, then the classical derivative route must be replaced by a weak/viscosity or approximation argument.

---

## (1) Why finite-shift `hshift` does not close

At a positive maximum of

```text
φ_s(x) = W(x+s) - W(x),
Δ = φ_s(x₀) > 0,
```

you have

```text
W_s'(x₀) = W'(x₀) = p,
W_s''(x₀) ≤ W''(x₀).
```

For the paper operator, with `χ = -a`, `a ≥ 0`,

```text
A_V(W)
= W'' + cW'
  + a*m*W^{m-1} V' W'
  + reaction(W)
  + a*W^m*(V - W^γ).
```

The derivative-chemotaxis part splits as

```text
a*m*(W_s^{m-1} V_s' - W^{m-1} V')*p
=
a*m*(W_s^{m-1}-W^{m-1})*V_s'*p
+
a*m*W^{m-1}*(V_s'-V')*p.
```

The first term is already delicate because `p` has no sign at a finite-shift maximum. The second term is the real obstruction: `V_s'-V'` has no sign from `V` antitone.

A Lipschitz bound gives only

```text
|V_s'(x₀)-V'(x₀)| ≤ ‖V''‖∞ * s,
```

hence

```text
|a*m*W^{m-1}(V_s'-V')p| ≤ C * s * |p|.
```

But the sliding contradiction needs a bound of the form

```text
≤ C * Δ.
```

There is no general estimate

```text
s*|W'(x₀)| ≤ C*|W(x₀+s)-W(x₀)|
```

at a finite-difference maximum. The endpoint derivative `p` can be small, large, positive, or negative relative to the average difference `Δ/s`. So an `O(s)` coefficient-shift error does not close the maximum-principle contradiction.

Thus the finite-shift wrapper is valid only if you add an explicit hypothesis like

```lean
∀ s ≥ 0, ∀ x₀,
  IsMaxOn (fun x => W (x+s) - W x) Set.univ x₀ →
  0 < W (x₀+s) - W x₀ →
    a*m*W x₀^(m-1)*
      (deriv V (x₀+s) - deriv V x₀)*
      deriv W x₀
    ≤ Cshift * (W (x₀+s) - W x₀)
```

But that hypothesis is essentially the hard monotonicity statement in disguise. It is not a consequence of `u` antitone alone.

---

## (2) Infinitesimal route: the estimate that closes

Let

```text
q = W'.
```

Assume the paper implicit step

```text
W - h*A_V(W) = Z,
h = 1/λ,
```

and differentiate:

```text
q - h*(A_V(W))' = Z'.
```

At a positive maximum of `q`, say `q(x₀)>0`, we have

```text
q'(x₀)=0,
q''(x₀)≤0.
```

Now expand the derivative of the paper operator:

```text
(A_V(W))'
=
q''
+ c q'
+ a*m*((m-1)W^{m-2} q^2 V'
       + W^{m-1} V'' q
       + W^{m-1} V' q')
+ reaction'(W) q
+ a*m*W^{m-1} q V
+ a*W^m V'
- a*(m+γ)*W^{m+γ-1} q.
```

At a positive maximum of `q`:

```text
q'' ≤ 0,          good
c q' = 0,
V' ≤ 0,
q > 0,
W ≥ 0.
```

So the following terms are nonpositive and may be dropped:

```text
a*m*(m-1)W^{m-2} q^2 V' ≤ 0,
a*W^m V' ≤ 0,
-a*(m+γ)*W^{m+γ-1} q ≤ 0.
```

The only positive/bounded linear terms are:

```text
reaction'(W) q,
a*m*W^{m-1} V'' q,
a*m*W^{m-1} V q.
```

Using

```text
|reaction'(W)| ≤ reactionLip(α,M),
0 ≤ W ≤ M,
|V| ≤ B_V,
|V''| ≤ B_V2,
```

we get

```text
(A_V(W))'(x₀)
≤ Cmono * q(x₀),
```

where a convenient constant is

```text
Cmono =
  reactionLip(α,M)
  + a*m*M^{m-1}*(B_V2 + B_V).
```

Then from the differentiated step and `Z'(x₀) ≤ 0`:

```text
q(x₀) - h*(A_V(W))'(x₀) = Z'(x₀) ≤ 0,
```

so

```text
q(x₀) ≤ h*Cmono*q(x₀).
```

If

```text
h*Cmono < 1,
```

this contradicts `q(x₀)>0`. Hence `q≤0`, so `W` is antitone.

This is the clean estimate. Notice that the bad finite-shift term has become the manageable infinitesimal term

```text
V'' * q,
```

which is proportional to `q`, exactly what the maximum principle needs.

---

## Lean-formalizable theorem shape

I would introduce a separate derivative maximum-principle theorem for the paper step:

```lean
theorem paperImplicitStep_preserves_antitone_deriv
    {p : CMParams} {c lam M BV BV2 Cmono : ℝ}
    {u Z W : ℝ → ℝ}
    (hlam : 0 < lam)
    (hχ : p.χ ≤ 0)
    (hWpos : ∀ x, 0 < W x)        -- avoids rpow derivative singularities
    (hWrange : ∀ x, W x ∈ Set.Icc (0 : ℝ) M)
    (hZdiff : Differentiable ℝ Z)
    (hZderiv_nonpos : ∀ x, deriv Z x ≤ 0)
    (hWreg : ContDiff ℝ 3 W)
    (hVreg : ContDiff ℝ 2 (frozenElliptic p u))
    (hVderiv_nonpos : ∀ x, deriv (frozenElliptic p u) x ≤ 0)
    (hVbound : ∀ x, |frozenElliptic p u x| ≤ BV)
    (hV2bound : ∀ x,
      |deriv (deriv (frozenElliptic p u)) x| ≤ BV2)
    (hCmono :
      reactionLip p.α M
        + (-p.χ) * p.m * M ^ (p.m - 1) * (BV2 + BV) ≤ Cmono)
    (hsmall : (1 / lam) * Cmono < 1)
    (hstep : ∀ x,
      paperImplicitStepOp p c (1 / lam) u W x = Z x)
    (hqtails :
      ∃ La Lb,
        Tendsto (fun x => deriv W x) atBot (𝓝 La) ∧ La ≤ 0 ∧
        Tendsto (fun x => deriv W x) atTop (𝓝 Lb) ∧ Lb ≤ 0) :
    Antitone W := by
  -- prove `∀ x, deriv W x ≤ 0` by contradiction:
  -- if deriv W positive somewhere, tails + continuity give positive global max.
  -- at max: q'=0, q''≤0.
  -- differentiate `hstep`, expand `(paperWaveOperator)'`, apply the estimate above.
  -- then derive q ≤ h*Cmono*q contradiction.
  -- finally, `deriv_nonpos` + differentiability gives antitone.
```

The proof should be split into smaller lemmas:

```lean
lemma paperWaveOperator_deriv_at_pos_max_bound
    ...
    (hqmax : IsMaxOn (fun x => deriv W x) Set.univ x₀)
    (hqpos : 0 < deriv W x₀) :
    deriv (fun x => paperWaveOperator p c u W x) x₀
      ≤ Cmono * deriv W x₀
```

and

```lean
lemma deriv_step_at_max
    ...
    (hstep : ∀ x, paperImplicitStepOp p c h u W x = Z x) :
    deriv W x₀
      - h * deriv (fun x => paperWaveOperator p c u W x) x₀
      = deriv Z x₀
```

Then the contradiction is just `nlinarith`.

The repo already has the paper-step operator and its source/step infrastructure; `paperWaveOperator` is the expanded operator, and `paperImplicitStepOp_of_greenConv_source` proves a Green-represented source satisfies the paper implicit step equation. fileciteturn163file0L43-L64 fileciteturn163file0L94-L123

---

## Required regularity

The infinitesimal route is clean analytically, but it is not free.

It needs enough regularity to speak classically about `q''`, i.e.

```text
q = W' is C², so W is C³.
```

It also needs

```text
Z is differentiable with Z'≤0.
```

This is stronger than mere `Z` antitone. A continuous antitone `Z` has a distributional derivative which is a negative measure, but formalizing that weak maximum principle would be much heavier.

So there are two realistic Lean choices:

### Option A: classical differentiable-step theorem

Use the theorem above under:

```lean
ContDiff ℝ 3 W
Differentiable ℝ Z
∀ x, deriv Z x ≤ 0
```

This is the easiest to formalize. It may require smoothing the initial upper barrier or proving that after the first Green step, all future `Z` are regular enough.

### Option B: weak/viscosity monotonicity theorem

Keep only `Z` antitone and prove a viscosity or distributional derivative maximum principle for `q`. This is mathematically robust but a much larger Lean project.

For this repo, I would choose **Option A** first, because it gives a concrete closable theorem and isolates the remaining mismatch with the nonsmooth initial barrier.

---

## What about the literal frozen divergence operator?

The derivative route is clean for `paperWaveOperator`, because differentiating the expanded paper operator only requires `V`, `V'`, and `V''`.

For the literal frozen divergence operator

```lean
frozenWaveOperator p c u W =
  W'' + cW' - χ ∂x(W^m V_u') + W(1-W^α),
```

differentiating classically would introduce either:

```text
∂xx(W^m V')
```

or, after using `V'' = V - u^γ`, derivatives of `u^γ`.
```

That is much worse unless `u` is smooth. This is another reason the monotonicity-preservation proof should be done in the **paper expanded operator layer**, not the literal frozen-divergence layer.

The repo already distinguishes these layers in the paper producer: `paperStepNonlinearity`, `paperStepSource`, and `paperWaveOperator_eq_linear_add_paperStepNonlinearity` are defined specifically for the paper step. fileciteturn163file0L43-L64

---

## Bottom line

The finite-shift `hshift` cannot be discharged under the current hypotheses because the `V_s' - V'` term is only `O(s)`, not `O(Δ)`, and no trap fact relates it to the positive finite difference `Δ`.

The genuinely dischargeable route is:

```text
differentiate the paper implicit step,
apply a maximum principle to q = W',
use V'≤0 to make the q² and V' terms good,
bound V and V'' to control the remaining zeroth-order terms,
choose λ large so (1/λ)*Cmono < 1.
```

In Lean, formalize this as a classical lemma requiring `W∈C³`, `Z` differentiable with `Z'≤0`, `W>0`, `0≤W≤M`, `V'≤0`, and bounded `V,V''`. This closes the monotonicity estimate; the only remaining project is ensuring the Rothe iterates satisfy the needed differentiability, or smoothing/approximating the nonsmooth initial barrier.
