## Bottom line

Step C **does close** for the **smooth paper-expanded step**, but not because the whole zeroth-order coefficient is automatically nonpositive. The right argument is:

```text
At a positive max of q = W',
all genuinely non-q forcing terms are ≤ 0;
all remaining possibly positive terms are proportional to q;
bound their coefficient above by Cmono;
choose λ large so (1/λ) Cmono < 1.
```

So the proof is a quasi-monotone maximum principle, not a pure sign maximum principle.

The paper operator is exactly the right layer because its expanded nonlinearity is

```lean
-p.χ * p.m * W^(p.m-1) * V' * W'
+ W * (1 - p.χ * W^(p.m-1) * V
        - (W^p.α - p.χ * W^(p.m+p.γ-1)))
```

which, for `χ = -a ≤ 0`, becomes

```text
a m W^{m-1} V' W' + reaction(W) + a W^m(V - W^γ).
```

This is the form in `paperStepNonlinearity` / `paperWaveOperator_eq_linear_add_paperStepNonlinearity`. fileciteturn171file0L3-L21

---

## 1. Differentiated equation

Let

```text
a := -χ ≥ 0,
V := Vε = frozenElliptic p uε,
W := Wε,
Z := Zε,
q := W'.
```

The smooth implicit step is

```text
W - h A(W) = Z,       h = 1/λ.
```

Differentiate:

```text
q - h (A(W))' = Z'.
```

With

```text
A(W)
= W'' + cW'
  + a m W^{m-1} V' W'
  + reaction(W)
  + a W^m(V - W^γ),
```

we get

```text
(A(W))'
=
q'' + c q'
+ a m (m-1) W^{m-2} q^2 V'
+ a m W^{m-1} V'' q
+ a m W^{m-1} V' q'
+ reaction'(W) q
+ a m W^{m-1} q V
+ a W^m V'
- a (m+γ) W^{m+γ-1} q.
```

A useful grouping is:

```text
(A(W))'
=
q'' + c q'
+ b(x) q
+ a m W^{m-1} V' q'
+ G_good,
```

where

```text
b(x)
=
reaction'(W)
+ a m W^{m-1} V''
+ a m W^{m-1} V
- a (m+γ) W^{m+γ-1},
```

and

```text
G_good
=
a m (m-1) W^{m-2} V' q^2
+ a W^m V'.
```

This is the clean Lean split.

At a positive global maximum `x₀` of `q`:

```text
q(x₀) > 0,
q'(x₀) = 0,
q''(x₀) ≤ 0.
```

Also `V'≤0` from the elliptic monotonicity lemma, provided `uε` is nonnegative and antitone. The repo already proves that a monotone trapped profile gives `frozenElliptic` antitone and hence `deriv (frozenElliptic p U) x ≤ 0`. fileciteturn168file0L104-L132

Thus at `x₀`:

```text
q'' ≤ 0,
c q' = 0,
a m W^{m-1} V' q' = 0,
a m (m-1) W^{m-2} V' q^2 ≤ 0,
a W^m V' ≤ 0,
-a(m+γ)W^{m+γ-1}q ≤ 0.
```

The last term is a good negative diagonal term. It helps, but the proof should not rely on it making the whole coefficient nonpositive.

---

## 2. The coefficient bound

The only terms that may be positive at the max are proportional to `q`:

```text
reaction'(W) q
+ a m W^{m-1} V'' q
+ a m W^{m-1} V q.
```

Assume the range and coefficient bounds:

```text
0 < W(x),        W(x) ≤ M,
|V(x)| ≤ BV,
|V''(x)| ≤ BV2.
```

Then

```text
reaction'(W) ≤ reactionLip(α,M),
a m W^{m-1} V'' ≤ a m M^{m-1} BV2,
a m W^{m-1} V  ≤ a m M^{m-1} BV.
```

The repo’s `reactionLip` is

```lean
reactionLip a M = 1 + (a + 1) * M ^ a
```

and the file proves it bounds the derivative of `reactionFun` on `[0,M]`. fileciteturn173file0L3-L7 fileciteturn173file0L45-L77

So set

```text
Cmono :=
reactionLip(α,M)
+ a m M^{m-1} (BV2 + BV).
```

Then at the positive max:

```text
(A(W))'(x₀) ≤ Cmono · q(x₀).
```

The elliptic identity gives a convenient source for `V''` bounds:

```lean
deriv (deriv (frozenElliptic p u)) x =
  frozenElliptic p u x - (u x)^p.γ
```

so if `0≤u≤M` and `V` is bounded, then `V''` is bounded. fileciteturn172file0L20-L26

---

## 3. Maximum-principle contradiction

At the positive max `x₀`, the differentiated step gives

```text
q(x₀) - h (A(W))'(x₀) = Z'(x₀).
```

Since the mollified old iterate is antitone,

```text
Z'(x₀) ≤ 0.
```

Using `(A(W))'(x₀) ≤ Cmono q(x₀)`,

```text
q(x₀) - h(A(W))'(x₀)
≥ q(x₀) - h Cmono q(x₀)
= (1 - h Cmono) q(x₀).
```

If

```text
h Cmono < 1,
```

then

```text
(1 - h Cmono) q(x₀) > 0,
```

contradicting

```text
q(x₀) - h(A(W))'(x₀) = Z'(x₀) ≤ 0.
```

Hence `q` has no positive maximum. With derivative tails nonpositive at `±∞`, this yields

```text
∀ x, q(x) ≤ 0.
```

Then `W` is antitone.

---

## 4. Answer to the “forcing” question

There is **no positive forcing** left after the paper expansion.

The terms are:

```text
Z'                         ≤ 0     good forcing
q''                        ≤ 0     good at max
a m W^{m-1} V' q'          = 0      vanishes at max
a m(m-1)W^{m-2}V' q²       ≤ 0     good because V'≤0
a W^m V'                   ≤ 0     good because V'≤0
-a(m+γ)W^{m+γ-1}q          ≤ 0     good diagonal
reaction'(W)q              ≤ C q   absorbed
a m W^{m-1}V''q            ≤ C q   absorbed
a m W^{m-1}Vq              ≤ C q   absorbed
```

So the correct statement is:

```text
All non-q forcing terms are ≤ 0.
The V'' and V terms are q-coefficients, not forcing.
The diagonal -a(m+γ)W^{m+γ-1}q is good, but not needed for the upper bound.
```

Trying to prove the total coefficient is `≤0` is unnecessary and probably false in general, because `reaction'(W)`, `V''`, and `V` can contribute positively.

---

## 5. Lean lemma shape

I would split Step C into two lemmas.

### Lemma 1: derivative of the paper operator at a positive max

```lean
theorem paperWaveOperator_deriv_at_pos_max_le
    {p : CMParams} {c M a BV BV2 Cmono : ℝ}
    {u W : ℝ → ℝ} {x₀ : ℝ}
    (ha : a = -p.χ) (ha_nonneg : 0 ≤ a)
    (hM_nonneg : 0 ≤ M)
    (hWpos : 0 < W x₀)
    (hWleM : W x₀ ≤ M)
    (hVderiv_nonpos :
      deriv (frozenElliptic p u) x₀ ≤ 0)
    (hVbound : |frozenElliptic p u x₀| ≤ BV)
    (hV2bound :
      |deriv (deriv (frozenElliptic p u)) x₀| ≤ BV2)
    (hqpos : 0 < deriv W x₀)
    (hqmax : IsLocalMax (fun x => deriv W x) x₀)
    (hWreg : enough_derivatives_for_expansion_at x₀)
    (hCmono :
      reactionLip p.α M
        + a * p.m * M ^ (p.m - 1) * (BV2 + BV) ≤ Cmono) :
    deriv (fun x => paperWaveOperator p c u W x) x₀
      ≤ Cmono * deriv W x₀ := by
  -- expand derivative;
  -- use q'=0 and q''≤0 from local max;
  -- use V'≤0 for the q² and W^m V' terms;
  -- bound the q-coefficient.
```

In practice, Lean will be much easier if you first prove an explicit expansion lemma:

```lean
theorem deriv_paperWaveOperator_eq
    ... :
    deriv (fun x => paperWaveOperator p c u W x) x =
      deriv (deriv (deriv W)) x
      + c * deriv (deriv W) x
      + ...
```

or use `HasDerivAt` expansions locally and keep the formula as a named theorem.

For the maximum facts, use:

```lean
hq' : deriv (fun x => deriv W x) x₀ = 0
hq'' : deriv (deriv (fun x => deriv W x)) x₀ ≤ 0
```

rather than trying to invoke them inside the expansion lemma.

### Lemma 2: smooth paper step preserves antitonicity

```lean
theorem smooth_paperStep_deriv_nonpos
    {p : CMParams} {c lam M a BV BV2 Cmono : ℝ}
    {u Z W : ℝ → ℝ}
    (hlam : 0 < lam)
    (ha : a = -p.χ) (ha_nonneg : 0 ≤ a)
    (hstep :
      ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x)
    (hZderiv_nonpos : ∀ x, deriv Z x ≤ 0)
    (hWpos : ∀ x, 0 < W x)
    (hWrange : ∀ x, W x ≤ M)
    (hVderiv_nonpos :
      ∀ x, deriv (frozenElliptic p u) x ≤ 0)
    (hVbound : ∀ x, |frozenElliptic p u x| ≤ BV)
    (hV2bound :
      ∀ x, |deriv (deriv (frozenElliptic p u)) x| ≤ BV2)
    (hCmono :
      reactionLip p.α M
        + a * p.m * M ^ (p.m - 1) * (BV2 + BV) ≤ Cmono)
    (hsmall : (1 / lam) * Cmono < 1)
    (hregW : ContDiff ℝ 3 W)
    (hregZ : Differentiable ℝ Z)
    (hqtails :
      ∃ La Lb,
        Tendsto (fun x => deriv W x) atBot (𝓝 La) ∧ La ≤ 0 ∧
        Tendsto (fun x => deriv W x) atTop (𝓝 Lb) ∧ Lb ≤ 0) :
    ∀ x, deriv W x ≤ 0 := by
  intro x
  by_contra hxpos
  -- q = deriv W is continuous from hregW
  -- q positive somewhere.
  -- tails give positive global max x₀.
  -- at x₀:
  --   q' = 0, q'' ≤ 0
  -- differentiate hstep:
  --   q - (1/lam) * deriv(A W) = deriv Z
  -- use paperWaveOperator_deriv_at_pos_max_le
  -- contradiction with hsmall.
```

Then:

```lean
theorem smooth_paperStep_preserves_antitone
    (...) :
    Antitone W := by
  have hq_nonpos := smooth_paperStep_deriv_nonpos ...
  exact antitone_of_deriv_nonpos_on_univ hregW.differentiable hq_nonpos
```

The exact final Mathlib helper might be `antitoneOn_of_deriv_nonpos` on `Set.univ`; your repo already uses derivative-nonpositive-to-antitone style lemmas elsewhere for lower barriers, so this should be routine.

---

## 6. Regularity and positivity caveats

For the `rpow` derivative expansions, the cleanest hypotheses are:

```lean
∀ x, 0 < W x
```

and smoothness:

```lean
ContDiff ℝ 3 W
ContDiff ℝ 2 (frozenElliptic p u)
```

The strict positivity is natural in your lower-pinned construction: the lower barrier is positive at every finite point, and comparison gives `U⁻ ≤ W`.

Without strict positivity, the derivatives of terms like `W^(m-1)` can become painful when `1 ≤ m < 2`. There are ways around this with careful `rpow` lemmas, but they are not worth it for this proof.

---

## 7. Step D is routine

Yes. If

```text
Wε → W
```

pointwise, or locally uniformly, and every `Wε` is antitone, then `W` is antitone.

Lean lemma:

```lean
theorem antitone_of_pointwise_limit
    {ι : Type*} {l : Filter ι} [NeBot l]
    {Wε : ι → ℝ → ℝ} {W : ℝ → ℝ}
    (hanti : ∀ᶠ ε in l, Antitone (Wε ε))
    (hlim : ∀ x, Tendsto (fun ε => Wε ε x) l (𝓝 (W x))) :
    Antitone W := by
  intro x y hxy
  have hyx_eventually :
      ∀ᶠ ε in l, Wε ε y ≤ Wε ε x := by
    filter_upwards [hanti] with ε hε
    exact hε hxy
  exact le_of_tendsto_of_tendsto
    (hlim y) (hlim x) hyx_eventually
```

No viscosity infrastructure is needed for this passage.

---

## Final Step C summary

The proof closes with the estimate:

```text
(A(W))'(x₀) ≤ Cmono q(x₀)
```

at a positive max of `q = W'`, where

```text
Cmono =
reactionLip(α,M)
+ (-χ) m M^{m-1} (BV2 + BV).
```

Then

```text
q - h(A(W))' = Z' ≤ 0
```

contradicts

```text
q - h(A(W))' ≥ (1-hCmono)q > 0.
```

The paper-expanded diagonal term `-a W^{m+γ}` is good, but the real mechanism is not that the full coefficient is nonpositive; it is that the only bad terms are proportional to `q` and are absorbed by choosing `λ` large.
