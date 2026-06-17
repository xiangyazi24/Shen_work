═══ BRIDGE cron | 1f72a1ac | 12712 chars 2122 words 400 lines | 605s | prov=network | OK ═══
═══ BRIDGE cron | 1f72a1ac | 12712 chars 2122 words 400 lines | 605s | prov=network | OK ═══
## Verdict

The **correct lower-barrier sign** for the Rothe implicit step is

```lean
∀ x, 0 ≤ frozenWaveOperator p c u φ x
```

or equivalently `frozenWaveOperator p c u φ x ≥ 0`.

But the **plateau-then-tail profile is not automatically a subsolution**. The committed `lowerBarrierPlateau` is useful as a positive, monotone, upper-compatible comparison profile, but the full subsolution inequality needs extra analytic work: chemotaxis can break the sign, and the plateau edge is not a classical `C²` pointwise subsolution unless you either smooth it or switch to a weak/viscosity comparison theorem.

The safest Lean route is to introduce a `LowerBarrierData` structure that explicitly carries the subsolution inequality, then prove it later for a **smoothed two-exponential lower barrier** under explicit domination hypotheses.

---

## 0. Sign convention: why the lower barrier needs `F(φ) ≥ 0`

In the repo, the implicit step is

```lean
implicitStepOp p c h u W x = W x - h * frozenWaveOperator p c u W x
```

so `G_h(W) = W - h F_u(W)`. fileciteturn82file0L79-L85

The existing super-barrier comparison proves `W ≤ B` from

```lean
F_u(B) ≤ 0
Z ≤ B
G_h(W) = Z
```

as documented in `implicitStep_le_of_barrier_maxPrinciple`. fileciteturn83file0L6-L41

The lower-barrier dual is therefore:

```lean
F_u(φ) ≥ 0
φ ≤ Z
G_h(W) = Z
--------------------------------
φ ≤ W
```

At a hypothetical negative minimum of `W - φ`, one has `W < φ`, `W' = φ'`, `W'' ≥ φ''`, and the same one-sided Lipschitz machinery gives a contradiction. Algebraically,

```text
F(φ) ≥ 0  ⇒  G_h(φ) = φ - h F(φ) ≤ φ ≤ Z = G_h(W),
```

while the minimum estimate should force `G_h(W) - G_h(φ) < 0`.

So your sign `frozenWaveOperator(φ) ≥ 0` is the right one for preserving `φ ≤ U`.

The operator itself is exactly

```lean
W'' + c W' - χ * deriv (fun y => W y ^ m * deriv (frozenElliptic p u) y)
  + W * (1 - W ^ α)
```

in the committed definition. fileciteturn90file0L135-L140

---

## 1. Is `lowerBarrierPlateau` a genuine subsolution?

### Important correction: the committed tail is not pure `e^{-κtilde x}`

The committed raw lower profile is

```lean
lowerBarrierRaw κ κtilde D x = exp (-κ*x) - D * exp (-κtilde*x)
```

not just a faster exponential. fileciteturn87file0L3-L4 This is crucial. A pure faster exponential `A e^{-κtilde x}` has scalar linear part

```text
(κtilde² - c κtilde + 1) A e^{-κtilde x}.
```

For the KPP speed parametrization `c = κ + κ⁻¹`, with `0 < κ < κtilde < 1`, this coefficient is

```text
(κtilde - κ)(κtilde - κ⁻¹) < 0.
```

So a **pure faster exponential is the wrong sign** for a lower subsolution. It is scalar-super-solution-like, not subsolution-like.

The two-exponential profile fixes this: because `exp(-κx)` solves the linearized equation at speed `c = κ + κ⁻¹`, subtracting the faster exponential gives a positive scalar margin:

```lean
U'' + c U' + U
  = -D * (κtilde² - c*κtilde + 1) * exp(-κtilde*x)
```

and the repo proves this scalar linear part is positive under the usual `κ < κtilde ≤ 1` regime. fileciteturn87file0L87-L105 fileciteturn86file0L65-L77

So the correct tail candidate is:

```text
φ_raw(x) = e^{-κx} - D e^{-κtilde x},
```

not

```text
φ_tail(x) = A e^{-κtilde x}.
```

### (i) Plateau region

On the plateau, say `φ = C`, the scalar derivative terms vanish:

```text
φ'' = 0,   φ' = 0.
```

The operator becomes, away from the edge,

```text
F_u(C)
= C(1 - C^α) - χ * deriv(C^m V_u')
= C(1 - C^α) - χ * C^m * V_u''.
```

The elliptic equation gives

```lean
deriv (deriv (frozenElliptic p u)) x =
  frozenElliptic p u x - (u x) ^ p.γ
```

so the plateau chemotaxis term is

```text
- χ C^m (V_u - u^γ).
```

The repo has this exact `V'' = V - u^γ` identity. fileciteturn90file0L108-L114

There is **no unconditional sign** for `V_u - u^γ`. Thus the plateau is not automatically a subsolution.

What you need is an explicit domination hypothesis, for example:

```lean
hVpp_bound :
  ∀ u, InMonotoneWaveTrapSet κ M u →
    ∀ x, |frozenElliptic p u x - (u x) ^ p.γ| ≤ B₂
```

and then require, for the plateau value `C`,

```text
C(1 - C^α) ≥ |χ| * C^m * B₂.
```

If `m > 1`, this can usually be achieved by taking `C` small, because the reaction is order `C` while the chemotaxis plateau term is order `C^m`. If `m = 1`, smallness of `C` does **not** separate the orders; you need a genuine coefficient condition like

```text
1 - C^α ≥ |χ| B₂.
```

So the plateau region is safe only with an explicit chemotaxis budget.

### (ii) Plateau edge

The committed plateau is

```lean
if x ≤ lowerBarrierXPlus κ κtilde D then
  lowerBarrierRaw κ κtilde D (lowerBarrierXPlus κ κtilde D)
else
  lowerBarrierRaw κ κtilde D x
```

and the repo proves it is continuous and positive. fileciteturn73file0L91-L120 It also proves the raw derivative vanishes at the join point. fileciteturn84file0L63-L100

That is good: the committed profile is **C¹-compatible** at the join. It avoids the truly bad case where `φ'` jumps from `0` to a negative value, which would create a negative singular second derivative in a weak formulation.

But it is still not a clean **classical C²** subsolution at the join. The right second derivative of the raw branch is negative at the maximum, while the left second derivative of the constant branch is zero. Since the pointwise `frozenWaveOperator` uses `iteratedDeriv 2`, a classical Lean proof of

```lean
∀ x, 0 ≤ frozenWaveOperator p c u (lowerBarrierPlateau κ κtilde D) x
```

will be painful or semantically misleading at the edge.

So the edge verdict is:

```text
C¹ plateau is acceptable for a weak/viscosity subsolution argument.
It is not a clean pointwise C² subsolution for the current operator interface.
```

For Lean, either smooth the edge or add a weak/viscosity comparison theorem. Smoothing is much less infrastructure.

### (iii) Tail region

For the committed raw tail,

```text
φ = e^{-κx} - D e^{-κtilde x},
```

the scalar linear margin is positive:

```text
φ'' + cφ' + φ
= D(cκtilde - κtilde² - 1)e^{-κtilde x} > 0.
```

That part is already formalized. fileciteturn86file0L65-L77

The full operator is

```text
φ'' + cφ' + φ(1 - φ^α)
  - χ * (φ^m V_u')'.
```

So the positive scalar margin must dominate two losses:

```text
nonlinear loss:      φ^(α+1)
chemotaxis loss:     |χ| * |(φ^m V_u')'|.
```

Using the product split,

```text
(φ^m V')' = m φ^(m-1) φ' V' + φ^m V'',
```

a typical sufficient tail bound is

```text
|χ| * (m φ^(m-1) |φ'| |V'| + φ^m |V''|)
  + φ^(α+1)
≤ D(cκtilde - κtilde² - 1)e^{-κtilde x}.
```

With only bounded `V'` and `V''`, this requires exponent domination such as

```text
m κ ≥ κtilde,
(α + 1) κ ≥ κtilde,
```

plus constant inequalities. If you have stronger decay for `V'` or `V''`, the chemotaxis exponent can improve, but that decay must be stated and proved.

So the tail is promising, but only for the **two-exponential raw profile** and only after you record the chemotactic domination constants.

---

## 2. What lower barrier should be used?

The least painful **mathematical** lower barrier is:

```text
smooth plateau + two-exponential KPP tail
```

not a pure faster exponential.

The least painful **Lean** route is to first abstract the barrier data:

```lean
structure LowerBarrierData
    (p : CMParams) (c κ M : ℝ) (φ : ℝ → ℝ) : Prop where
  cunif_bdd : IsCUnifBdd φ
  nonneg : ∀ x, 0 ≤ φ x
  pos : ∀ x, 0 < φ x
  le_upper : ∀ x, φ x ≤ upperBarrier κ M x
  antitone : Antitone φ
  regular : ∀ x, DifferentiableAt ℝ φ x  -- plus whatever the max principle needs
  sub :
    ∀ u, InMonotoneWaveTrapSet κ M u →
      ∀ x, 0 ≤ frozenWaveOperator p c u φ x
```

Then prove the pinned-trap invariance from `LowerBarrierData.sub` using the dual maximum principle:

```lean
theorem implicitStep_ge_of_lowerBarrier_maxPrinciple
    (hstep : ∀ x, implicitStepOp p c h u W x = Z x)
    (hφsub : ∀ x, 0 ≤ frozenWaveOperator p c u φ x)
    (hφZ : ∀ x, φ x ≤ Z x)
    -- lower one-sided estimate at a negative minimum of W - φ
    :
    ∀ x, φ x ≤ W x
```

This is the exact dual of the existing super-barrier theorem. The existing theorem assumes `F(B) ≤ 0` and `Z ≤ B` to prove `W ≤ B`; the lower version should assume `F(φ) ≥ 0` and `φ ≤ Z` to prove `φ ≤ W`. fileciteturn83file0L9-L25

After that, prove the concrete `LowerBarrierData` in a separate file. I would not try to make the current nonsmoothed `lowerBarrierPlateau` satisfy a pointwise `∀ x` C² operator inequality.

### Best concrete barrier

Use

```text
φ_raw(x) = e^{-κx} - D e^{-κtilde x}
```

on the right tail, because the repo already proves its positive linear margin. fileciteturn87file0L3-L4 fileciteturn86file0L65-L77

Then replace the hard plateau cutoff by a smooth `C²` cap near the maximum. Conceptually:

```text
φ(x) = smooth_min_or_cap(C, φ_raw(x))
```

with the cap chosen so that

```text
φ' ≤ 0,
φ'' + cφ' + φ has a positive lower margin,
0 < φ ≤ upperBarrier,
```

and the chemotaxis and nonlinear losses are dominated.

Do **not** use a pure exponential `A e^{-κtilde x}` in the tail; its scalar sign is wrong in the usual `κ < κtilde < 1` KPP speed window.

### Compactly supported bump?

A compactly supported bump is useful if the only goal is **nontriviality**:

```lean
∃ x, 0 < U x
```

Then strict positivity can later come from ODE uniqueness / strong maximum principle. But it does **not** give a globally positive lower pin `∀ x, 0 < φ x`, and a smooth compactly supported subsolution has its own edge/eigenvalue proof obligations. It is not obviously less work in Lean unless you are willing to weaken the pinned trap to

```lean
φ ≤ U ∧ ∃ x, 0 < φ x
```

rather than requiring `φ > 0` everywhere.

### Linearization-at-zero barrier

This is the best route. The two-exponential `e^{-κx} - D e^{-κtilde x}` is precisely the standard KPP lower solution built from the linearization at zero. The committed lemmas already align with that: the first exponential is the neutral linearized mode and the subtracted faster mode creates positive residual. fileciteturn87file0L87-L105

---

## 3. Standard proof pattern to mirror

Yes: the standard traveling-wave fixed-point/monotone-iteration argument uses an ordered interval between lower and upper solutions. Many traveling-wave existence papers reduce the existence problem to constructing suitable upper and lower solutions and then apply monotone iteration or Schauder fixed point; for example, Lin–Ruan explicitly phrase traveling-wave existence for delayed diffusion systems via Schauder and generalized upper/lower solutions, and similar papers use upper/lower solutions plus Schauder for nonclassical or delayed reaction-diffusion waves. citeturn663728academia1 citeturn663728academia3

The Lean skeleton should be:

```lean
def LowerPinnedTrap (κ M : ℝ) (φ : ℝ → ℝ) (U : ℝ → ℝ) : Prop :=
  InMonotoneWaveTrapSet κ M U ∧ ∀ x, φ x ≤ U x

theorem lowerPinned_invariant
    (hbar : LowerBarrierData p c κ M φ)
    (hstep_preserves : ... implicit Rothe step data ...)
    :
    ∀ U, LowerPinnedTrap κ M φ U →
      LowerPinnedTrap κ M φ (Tmap U)
```

Then apply Schauder on `LowerPinnedTrap`, not on the bare trap.

The concrete analytic file should prove something like:

```lean
theorem smoothLowerBarrier_subsolution
    (hκ : 0 < κ) (hκ1 : κ < 1)
    (hκtilde : κ < κtilde) (hκtilde1 : κtilde ≤ 1)
    (hc : c = κ + κ⁻¹)
    (hchem_tail : ...)
    (hchem_plateau : ...)
    (hnonlinear_tail : ...)
    :
    ∀ u, InMonotoneWaveTrapSet κ M u →
      ∀ x, 0 ≤ frozenWaveOperator p c u φ x
```

where the domination hypotheses are explicit constants/exponents, not hidden sign guesses.

---

## Concrete answer to your three region checks

For the operator sign `F(φ) ≥ 0`:

| Region | Safe? | Reason |
|---|---:|---|
| Plateau | **Not automatically** | `reaction(C)>0`, but chemotaxis contributes `-χ C^m(V-u^γ)`, whose sign is not fixed. Need a bound like `C(1-C^α) ≥ |χ|C^m B₂`. |
| Plateau edge | **Not classically safe** | The committed plateau is continuous and C¹-matched, but not a clean C² pointwise subsolution at the join. Smooth it or use weak/viscosity comparison. |
| Pure faster exponential tail `e^{-κtilde x}` | **Wrong sign** | For `c=κ+κ⁻¹`, `κ<κtilde<1`, the scalar coefficient `κtilde²-cκtilde+1` is negative. |
| Two-exponential tail `e^{-κx}-D e^{-κtilde x}` | **Right scalar sign** | Repo proves positive scalar linear residual; still must dominate `φ^(α+1)` and chemotaxis. |

So: the plateau/tail lower barrier is a good **candidate**, but it is not yet a proved subsolution. The Lean-formalizable fix is a **smoothed two-exponential lower barrier with explicit chemotaxis domination hypotheses**, abstracted first through `LowerBarrierData`.
