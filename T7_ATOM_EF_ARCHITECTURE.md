# T7 Atom E/F — fixed-point assembly: architecture for ChatGPT

Status 2026-05-31 (HEAD `028649e`, build green 8385, axiom-clean).

**Everything analytic is done.** Atom B/C/D, O1 (resolver positivity `R(u)≥0`
on closed `[0,1]`), glue1 (flux sup-Lipschitz), glue2 (contraction core), and the
operator + predicate are defined:

- `intervalGradientDuhamelMap` (= Φ) and `IntervalMildSolution`
  (`ShenWork/Paper2/IntervalGradientDuhamelMap.lean`).
- Φ(u₀,u)(t,x) = `S(t)u₀(x) − χ₀∫₀ᵗ∂ₓ[S(t−s)Q(u(s))](x)ds + ∫₀ᵗS(t−s)L(u(s))(x)ds`,
  `S = intervalFullSemigroupOperator`, `Q = chemFluxLifted`, `L = logisticLifted`.

The remaining **Atom E (MapsTo + contraction) / F (Banach → IntervalMildSolution)**
is the fixed-point assembly.  Below is the precise scoping — the analytic inputs
are all proved; the open questions are the metric-space construction and the
prerequisite discharge.

## Mathlib API actually needed (verified)

`ContractingWith.exists_fixedPoint'`
(`Mathlib/Topology/MetricSpace/Contracting.lean:151`):

```
theorem exists_fixedPoint' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K (hsf.restrict f s s)) {x : α} (hxs : x ∈ s)
    (hx : edist x (f x) ≠ ∞) :
    ∃ y ∈ s, IsFixedPt f y ∧ … 
```

**Key:** `hf` is `ContractingWith K (hsf.restrict f s s)` — the contraction is on
the **subtype `↥s`** (the ball), NOT global.  So **NO clamping / global Lipschitz
is needed** — glue2's ball contraction `‖Φu−Φw‖ ≤ K·‖u−w‖` (for `u,w ∈ B_{T,M}`)
plugs in directly.  This removes the main worry from the earlier plan.

Requirements, in order:
1. `α` an `EMetricSpace` (or `MetricSpace`) — the trajectory space.
2. `s = B_{T,M}` with `IsComplete s`.
3. `MapsTo Φ s s` — the sup self-map bound.
4. `ContractingWith K (restrict Φ s s)` with `K < 1`.
5. a basepoint `x ∈ s` with `edist x (Φ x) ≠ ∞` (automatic in a genuine metric
   space — `edist` is always finite).

## The two genuine open design questions (for ChatGPT)

**Q1 — which `α` (the trajectory metric space)?**  The mild trajectory
`(t,x) ↦ u t x` is bounded and continuous on `(0,T]×Ī`, but **NOT continuous at
`t=0`** (`u₀` from `PositiveInitialDatum` need not be continuous).  Options:
- **(A) `BoundedContinuousFunction (↥((Set.Ioc 0 T) ×ˢ Set.Icc 0 1)) ℝ`** — the
  domain excludes `t=0`, where the trajectory IS bounded-continuous; this space
  is complete (sup metric, no compactness needed).  Φ must be reformulated as a
  self-map here, and one must prove `Φu` is bounded-continuous on `(0,T]×Ī` (the
  joint `(t,x)`-continuity of the gradient-Duhamel integral — see Q2).  The
  closed ball `B_{T,M} = {u : ‖u‖∞ ≤ M}` is complete (closed in a complete
  space).  InitialTrace (`u(t)→u₀` as `t→0⁺`) is proved separately from the
  Duhamel structure (`S(t)u₀→u₀`, Duhamel→0), NOT inside the metric.
- **(B)** a custom weighted space (`t>0` continuous + weight controlling
  `u(t)−S(t)u₀` at `t→0⁺`).  More faithful but needs a from-scratch
  `EMetricSpace`+completeness instance.

Recommendation to evaluate: **(A)** reuses Mathlib's complete
`BoundedContinuousFunction` and isolates all the real work into "Φ is a
bounded-continuous self-map", avoiding a custom metric/completeness proof.

**Q2 — discharging the joint `(t,x)`-continuity / Atom D per-slice
prerequisites.**  For Φ to land in `BoundedContinuousFunction` (and for Atom D's
sup/Lipschitz bounds to apply), one needs, for `u` a bounded-continuous
trajectory:
- the flux path `s ↦ Q(u(s))` and logistic path `s ↦ L(u(s))` are
  bounded-continuous (⟹ the per-slice integrability `Integrable`,
  `AEStronglyMeasurable`, and the spatial-differentiability prerequisites that
  `valueDuhamel_*`/`gradDuhamel_*` take as named hypotheses);
- the gradient-Duhamel value `∫₀ᵗ∂ₓS(t−s)Q(u(s))(x)ds` is jointly continuous in
  `(t,x)` (this is the one genuinely new regularity lemma — joint continuity of
  the `(t−s)^{−1/2}`-singular but integrable gradient integral).
This reduces to: `Q(u(s))` continuous in `(s,y)` (from `u` continuous + the
resolver-in-trajectory regularity: `R(u(s))`, `resolverGradReal(u(s))` continuous
in `(s,y)`, which follows from Atom B's `ℓ¹` cosine/gradient series being
continuous — `continuous_tsum`, already used in O1's closed-domain extension).

## Analytic inputs (all PROVED, ready to plug in)

- `MapsTo` sup bound: `valueDuhamel_sup_bound` (`≤T·‖·‖`), `gradDuhamel_sup_bound`
  (`≤C·2√T·‖·‖`) + flux sup bound (from glue1's constants + Atom B sup) + logistic
  sup bound (Atom C-style) ⟹ `‖Φu‖∞ ≤ ‖u₀‖∞ + |χ₀|C·2√T·B_Q + T·B_L ≤ M` for `M >
  ‖u₀‖∞` and small `T`.
- `ContractingWith K`: `gradientDuhamel_contraction_pointwise` +
  `valueDuhamel_diff_sup_bound`/`gradDuhamel_diff_sup_bound` + `chemFlux_div_lipschitz`
  + `intervalLogisticReaction_lipschitz_on_bounded` ⟹ `K = 2|χ₀|C·C_Q·√T + C_L·T`,
  `< 1` by `exists_small_contraction_time`.

## Net

The fixed-point existence is no longer blocked by any *analytic* gap — only by
the **metric-space construction (Q1)** and the **joint-continuity / prerequisite
discharge (Q2)**, both of which are infrastructure, not new estimates.  Decision
needed: option (A) vs (B) for `α`, and confirmation that the `BoundedContinuousFunction`
route's Φ-self-map continuity (Q2) is the intended next build.
