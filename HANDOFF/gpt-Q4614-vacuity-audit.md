ANSWER Q4614 64e81be9

# Vacuity audit: the finite-\(L^P\) and restarted-Duhamel core is genuine, but the headline wrapper is vacuous

## Executive verdict

The audit has a split result.

| Question | Verdict |
|---|---|
| (1) Is the finite \(L^P\) bound merely assumed? | **CONFIRM NON-VACUOUS.** The low-level `boundedBefore_of_lp_restarted_affine` theorem takes an `LpPowerBoundedBefore` hypothesis, but both critical wrappers construct it internally through the critical seed and finite-power bootstrap. The top theorem carries no \(L^P\) hypothesis. |
| (2) Is the seed interval empty? | **CONFIRM NONEMPTY.** `exists_critical_seed_exponent` proves the strict interval is nonempty by an explicit midpoint construction. For a concrete admissible parameter set the interval is `(1,2)` and `p₀ = 3/2` works. |
| (3) Are the solution/regularity/bound predicates internally impossible? | **The analytic chain itself is satisfiable**, and the repository has explicit constant classical-solution witnesses. **However, the top theorem's explicit `hglobalExtension` hypothesis is unsatisfiable.** This is a fatal vacuity defect in the headline wrapper. |
| (4) Is `a = 0 ∨ 0 < b` vacuous or over-restrictive? | **CONFIRM CORRECT.** Under the standing `0 ≤ a, 0 ≤ b`, it excludes exactly the false branch `a > 0, b = 0`. The mass proof handles the `b>0` and `a=b=0` cases separately and does not divide by zero in the latter branch. |

Therefore the overall theorem

```lean
Theorem_1_2_intervalDomain_positive_critical_branch
```

**does not pass the non-vacuity audit as currently stated**. Its boundedness core is real, but the tuple of top-level assumptions is empty because `hglobalExtension` quantifies over arbitrary total functions extending a finite-horizon solution and demands that every such arbitrary extension already be global.

This is exactly a situation in which

```text
#print axioms = [propext, Classical.choice, Quot.sound]
```

is compatible with vacuity: Lean needs no custom axiom to prove a theorem from an impossible hypothesis.

## Audited source snapshot

The fetched `chatgpt-scratch` files were:

```text
ShenWork/Paper2/IntervalDomainTheorem12PositiveCritical.lean
SHA 78d324d41c31038816599945ec5e46dc0af793ba

ShenWork/Paper2/IntervalDomainRestartedLpLinfProducer.lean
SHA 79a8a9619930c6c2b2df15a3a9e1a060cac02fe2
```

I also traced the producers into:

```text
IntervalDomainMCriticalLpSeed.lean
IntervalDomainMCriticalLpBootstrap.lean
IntervalDomainMCriticalGlobalLpSeed.lean
IntervalDomainMCriticalGlobalLpBootstrap.lean
IntervalDomainMMass.lean
P3MoserAgmonDirectRoute.lean
Statements.lean
IntervalDomain.lean
IntervalDomainExistence.lean
IntervalDomainAPrioriGlobal.lean
IntervalDomainTheorem12Refutation.lean
```

# 1. The finite \(L^P\) bound is genuinely produced

## 1.1 What actually carries an \(L^P\) hypothesis

The low-level endpoint theorem does carry the expected input:

```lean
-- IntervalDomainRestartedLpLinfProducer.lean:558--614
theorem boundedBefore_of_lp_restarted_affine
    ...
    (hLp : LpPowerBoundedBefore intervalDomainM P T u) :
    IsPaper2BoundedBefore intervalDomainM T u
```

Likewise the all-time endpoint takes a global power bound:

```lean
-- same file:640--689
theorem boundedGlobal_of_lp_restarted_affine
    ...
    (hpower : ∀ t, 0 < t →
      intervalDomainM.integral (fun z => (u t z) ^ P) ≤ C) :
    IsPaper2Bounded intervalDomainM u
```

Those are mathematically appropriate intermediate interfaces. The audit question is whether the critical wrappers discharge them. They do.

## 1.2 The finite-horizon critical wrapper discharges `hLp`

The critical wrapper is:

```lean
-- IntervalDomainRestartedLpLinfProducer.lean:709--725
theorem critical_bounded_before_positive_restarted_affine ... :
    IsPaper2BoundedBefore intervalDomainM T u := by
  obtain ⟨P, hPmax, hLp⟩ := exists_critical_lp_above_gamma
    hguard hu₀ hsol htrace hbeta hm hchi hthreshold
  exact boundedBefore_of_lp_restarted_affine ... hLp
```

The interval-domain transport is at lines 726--745. Thus the theorem used by the headline at

```lean
IntervalDomainTheorem12PositiveCritical.lean:52--54
```

has no undischarged power-bound premise.

The producer `exists_critical_lp_above_gamma` is genuine:

```lean
-- IntervalDomainMCriticalLpBootstrap.lean:296--324
theorem exists_critical_lp_above_gamma ... :
    ∃ pExp : ℝ, max 1 p.γ < pExp ∧
      LpPowerBoundedBefore intervalDomainM pExp T u
```

Its proof does all of the following:

```text
exists_high_critical_lp_power_bounded_before
  -> obtains p₀ and an actual L^{p₀} bound;
sets P = p₀ + γ;
proves max{1,γ} < P;
critical_lp_power_bounded_before_positive_of_seed
  -> produces the actual L^P bound.
```

The seed-to-target producer is at `IntervalDomainMCriticalLpBootstrap.lean:246--275`:

```lean
theorem critical_lp_power_bounded_before_positive_of_seed
    ...
    (hp0 : max 1 (p.γ * (p.N : ℝ) / 2) < p0)
    (hseed : LpPowerBoundedBefore intervalDomainM p0 T u)
    (hpExp : p0 ≤ pExp) :
    LpPowerBoundedBefore intervalDomainM pExp T u
```

It constructs:

```text
intervalDomain_crossDiffusionBootstrapEstimate_sharp
AbstractLpBootstrapHypothesis
critical_bootstrap_linear_damping
lp_power_bounded_before_of_linear_damping
```

The interpolation atom is not assumed: `produce_AgmonAbsorbedInterpolationBefore_of_classical` in `P3MoserAgmonDirectRoute.lean:648ff` constructs it from classical regularity, the seed bound, Hölder/Agmon, and Young absorption.

### Important call-graph correction

The top theorem does **not** actually pass through

```lean
Proposition_2_5_intervalDomain_of_restarted_affine
```

although that sibling wrapper exists at `IntervalDomainRestartedLpLinfProducer.lean:615--639`. The top finite branch calls `critical_bounded_before_positive_restarted_affine_intervalDomain`, which goes directly from the produced high finite power to `boundedBefore_of_lp_restarted_affine`.

This is not a defect; it is simply the exact call graph.

## 1.3 The global critical wrapper also constructs its power bound

After a genuine global solution has been supplied, the global wrapper at `IntervalDomainRestartedLpLinfProducer.lean:692--708` does:

```lean
obtain ⟨P, hPmax, C, hpower⟩ :=
  exists_critical_lp_above_gamma_global ...
exact boundedGlobal_of_lp_restarted_affine ... hpower
```

The producer is:

```lean
-- IntervalDomainMCriticalGlobalLpBootstrap.lean:571--601
theorem exists_critical_lp_above_gamma_global ... :
    ∃ pExp : ℝ, max 1 p.γ < pExp ∧
      ∃ C, ∀ t, 0 < t →
        intervalDomainM.integral (fun x => (u t x) ^ pExp) ≤ C
```

It calls the horizon-independent seed

```lean
exists_high_critical_lp_power_bounded_global
-- IntervalDomainMCriticalGlobalLpSeed.lean:352--379
```

and then

```lean
critical_lp_power_bounded_global_positive_of_seed
-- IntervalDomainMCriticalGlobalLpBootstrap.lean:535--570
```

So the global \(L^P\) bound is also produced, not projected from a hidden hypothesis.

## 1.4 Honest characterization of the finite-power route

The current proof is slightly stronger and more direct than the phrase “window-ladder Moser” suggests. Once the critical seed is available, the one-dimensional seed-relative Agmon interpolation produces a linear damping inequality at every target exponent `pExp ≥ p₀`; it does not need to visit a sequence of intermediate windows.

That is a valid route. It is not a disguised all-\(p\) hypothesis.

# 2. The critical seed interval is constructively nonempty

The decisive theorem is:

```lean
-- IntervalDomainMCriticalLpSeed.lean:683--729
theorem exists_critical_seed_exponent
    (p : CM2Params) (hbeta : 1 ≤ p.β)
    (hchi : 0 < p.χ₀) (hthreshold : p.χ₀ < chiBeta p) :
    ∃ pExp : ℝ,
      max 1 (p.γ * (p.N : ℝ) / 2) < pExp ∧
        pExp < (2 * p.β - 1) / p.χ₀
```

The proof does not invoke choice on an unproved nonempty set. It defines

```text
η     = 2β - 1,
q     = γN,
d     = max 2 q,
lower = max 1 (q/2),
upper = η/χ₀,
p₀    = (lower + upper)/2.
```

Unfolding

```text
chiBeta = 2(2β-1) / max{2,γN}
```

turns `χ₀ < chiBeta` into

```text
max{2,γN}/2 < (2β-1)/χ₀.
```

The proof establishes the identity

```text
max{2,γN}/2 = max{1,γN/2}
```

and then uses the midpoint. The strict interval is therefore nonempty.

For the unit interval with `N=1`, this is exactly the interval in the question:

```text
max{1,γ/2} < p₀ < (2β-1)/χ₀.
```

## Concrete numerical witness

Take

```text
N = 1,
α = γ = m = μ = ν = β = a = b = 1,
χ₀ = 1/2.
```

Then

```text
chiBeta = 2(2·1-1)/max{2,1} = 1,
0 < χ₀ = 1/2 < 1,
lower = max{1,1/2} = 1,
upper = 1/(1/2) = 2.
```

Hence

```text
p₀ = 3/2
```

is an explicit critical seed exponent. The later producer may take

```text
P = p₀ + γ = 5/2 > max{1,γ}.
```

There is no collapsing exponent interval and no vacuous use of `χ₀ < chiBeta`.

# 3. The analytic predicates are inhabited — but `hglobalExtension` is impossible

## 3.1 Real witnesses for the PDE-side predicates

The repository itself proves nonemptiness of the classical-solution class.

In `ShenWork/PDE/IntervalDomainExistence.lean`:

```lean
constOnInterval_pos
-- lines 45--50

equilibrium_isPaper2ClassicalSolution
-- begins at line 447

zeroReaction_isPaper2ClassicalSolution
-- begins at line 490

constantSolution_globalExistence
-- begins at line 522

constantSolution_initialTrace
-- begins at line 532
```

For the numerical parameters above, set

```text
u₀(x) = 1,
u(t,x) = 1,
v(t,x) = 1.
```

Then:

```text
u_t = u_x = u_xx = v_x = v_xx = 0,
μv = νu^γ = 1,
u(a-bu^α) = 1(1-1) = 0.
```

Thus the chemotaxis term and logistic term both vanish. This is a positive global classical solution with exact initial trace and

```text
∫₀¹ u(t,x)^P dx = 1
```

for every finite `P`. It satisfies every local hypothesis consumed by the finite-power and restarted-Duhamel chain. On this solution the chemotaxis and logistic Duhamel legs vanish, so there is no possibility that their hypotheses describe an empty class.

The zero-reaction branch is also inhabited: with `a=b=0`, any positive constant `u≡c`, together with `v≡(ν/μ)c^γ`, is the formal witness supplied by `zeroReaction_isPaper2ClassicalSolution`.

Hence no conjunction such as

```text
IsPaper2ClassicalSolution ∧ InitialTrace ∧ LpPowerBoundedBefore
```

is intrinsically contradictory.

## 3.2 Fatal defect: the explicit continuation hypothesis

The problematic hypothesis is not hidden in the \(L^P\) chain. It is the explicit hypothesis at

```lean
-- IntervalDomainTheorem12PositiveCritical.lean:32--40
(hglobalExtension :
  ∀ u₀, PositiveInitialDatum intervalDomain u₀ →
  ∀ Tmax > 0, ∀ u v,
    IsPaper2ClassicalSolution intervalDomain p Tmax u v →
    InitialTrace intervalDomain u₀ u →
    IsPaper2BoundedBefore intervalDomain Tmax u →
    1 ≤ p.m →
    IsPaper2GlobalClassicalSolution intervalDomain p u v)
```

This says that **every pair of total functions whose restriction to `(0,Tmax)` is a bounded local solution must already be a global solution without changing those functions after `Tmax`**.

That proposition is false.

The reason is visible in the definitions:

```text
Statements.lean:70--102
  IsPaper2ClassicalSolution only constrains 0 < t < T.

Statements.lean:265--268
  InitialTrace only constrains sufficiently small positive t.

Statements.lean:352--355
  IsPaper2BoundedBefore only constrains 0 < t < T.

IntervalDomain.lean:2768ff
  intervalDomainClassicalRegularity uses time sets Set.Ioo 0 T.
```

Therefore values after the local horizon are completely free.

## 3.3 Concrete counterextension

Use the same admissible parameters

```text
N=1, α=γ=m=μ=ν=β=a=b=1, χ₀=1/2
```

and take `Tmax = 1`, `u₀ ≡ 1`. Define total functions

```lean
uBad(t,x) = if t ≤ 2 then 1 else -1,
vBad(t,x) = if t ≤ 2 then 1 else 0.
```

Then:

1. On every `0 < t < 1`, `uBad=vBad=1`, so
   ```lean
   IsPaper2ClassicalSolution intervalDomain p 1 uBad vBad
   ```
   holds. The discontinuity at time `2` is outside the local horizon and even outside a full neighbourhood of its closure.
2. `InitialTrace intervalDomain (fun _ => 1) uBad` holds exactly.
3. `IsPaper2BoundedBefore intervalDomain 1 uBad` holds with bound `1`.
4. `p.m = 1`.

If `hglobalExtension` existed, it would imply

```lean
IsPaper2GlobalClassicalSolution intervalDomain p uBad vBad.
```

Apply this alleged global solution on horizon `4` and inspect time `t=3`. Closed-domain positivity in `IsPaper2ClassicalSolution` would give

```text
0 < uBad(3,x) = -1,
```

for every interval point `x`, a contradiction.

Thus `hglobalExtension` is not merely currently unproved; its stated type has no real instance for this concrete admissible parameter set.

## 3.4 The two top hypotheses are jointly inconsistent in the intended regime

There is an even more general argument. Assume `hlocal` from lines 26--31. Apply it to the positive constant datum `u₀≡1`, obtaining some local branch `(Tmax,u,v)`. Modify that branch only after `Tmax+1`, setting the modified cell density to `-1` later. The modified pair still satisfies the same local-solution and trace predicates.

The already proved theorem

```lean
critical_bounded_before_positive_restarted_affine_intervalDomain
```

then supplies `IsPaper2BoundedBefore` for the modified local branch. Applying `hglobalExtension` again forces the arbitrary bad extension to be global, contradicting positivity after `Tmax+1`.

Consequently, in the positive critical parameter regime,

```text
hlocal ∧ hglobalExtension
```

is itself inconsistent. The complete hypothesis class of the headline theorem is empty.

## 3.5 Minimal correction

Continuation must return or identify a **canonical extension**, not claim that every arbitrary total continuation is already global. A minimally sane interface is:

```lean
(hglobalExtension :
  ∀ u₀, PositiveInitialDatum intervalDomain u₀ →
  ∀ Tmax > 0, ∀ u v,
    IsPaper2ClassicalSolution intervalDomain p Tmax u v →
    InitialTrace intervalDomain u₀ u →
    IsPaper2BoundedBefore intervalDomain Tmax u →
    1 ≤ p.m →
      ∃ uGlobal vGlobal,
        IsPaper2GlobalClassicalSolution intervalDomain p uGlobal vGlobal ∧
        InitialTrace intervalDomain u₀ uGlobal ∧
        (∀ t, 0 < t → t < Tmax →
          uGlobal t = u t ∧ vGlobal t = v t))
```

Even better, use a maximal/reachable solution object plus uniqueness and gluing. The repository already has the intended structural API:

```lean
IntervalDomainStandardContinuationGluingData
-- IntervalDomainAPrioriGlobal.lean:241ff

StandardContinuationAlternative
GlobalSolutionGluingFromReachability
```

`IntervalDomainStandardContinuationGluingData` separates:

```text
localExistence,
standardContinuation,
gluing.
```

That is the correct shape. The headline should obtain a genuinely constructed global pair and run

```lean
critical_bounded_global_positive_restarted_affine_intervalDomain
```

on that pair, rather than reusing an arbitrary post-horizon assignment to the local functions.

# 4. The parameter guard is correct and non-vacuous

The guard is

```lean
hguard : p.a = 0 ∨ 0 < p.b.
```

Because `CM2Params` already carries

```text
0 ≤ a,
0 ≤ b,
```

this is equivalent to excluding exactly

```text
a > 0 ∧ b = 0.
```

The companion theorem

```lean
not_Theorem_1_2_intervalDomain_of_a_pos_b_zero
-- IntervalDomainTheorem12Refutation.lean:50--161
```

proves that excluded branch is genuinely false: Neumann integration gives `M'(t)=aM(t)`, and positive mass is incompatible with eventual boundedness.

## 4.1 The mass producer uses the guard correctly

The exact implementation is

```lean
-- IntervalDomainMMass.lean:428--448
theorem mass_le_uniformMassBoundConstant_of_guard ...
```

It splits on `0 < b`:

```text
b > 0:
  use mass_le_max_initial_threshold_of_b_pos;

not (b > 0):
  p.hb gives b=0;
  hguard then gives a=0;
  use mass_le_initial_of_a_eq_b_eq_zero.
```

So the proof does not smuggle a division by zero into the `a=b=0` branch. Although `massThreshold p = (a/b)^(1/α)` is a total Lean term, the zero-damping proof uses mass conservation, not a false positive equilibrium calculation.

## 4.2 Explicit nonempty guard branches

Two formal solution witnesses are already in the repository:

```text
a>0, b>0:
  u ≡ (a/b)^(1/α),
  v ≡ (ν/μ)u^γ;

a=b=0:
  u ≡ c>0,
  v ≡ (ν/μ)c^γ.
```

The guard also includes `a=0,b>0`. This branch is mathematically nonempty; for spatially constant data `c>0`, one has the explicit decreasing solution

```text
u(t) = (c^{-α} + α b t)^(-1/α),
v(t) = (ν/μ)u(t)^γ.
```

Thus the guard neither forces `a=0` nor collapses the parameter set. It is the right correction to the published mixed undamped counterexample.

# Final classification

## What passes

The following pieces are genuine, satisfiable, and useful:

```text
critical seed exponent arithmetic;
signal-weighted critical L^{p₀} seed;
seed-relative finite-power bootstrap;
finite and global high-L^P producers;
restart flux / chemotaxis / logistic estimates;
fresh-window L^P -> L∞ endpoint;
finite-horizon boundedness;
global boundedness conditional on an actual global solution;
parameter guard a=0 ∨ b>0.
```

In particular, this theorem is a meaningful non-vacuous analytic endpoint:

```lean
critical_bounded_before_positive_restarted_affine_intervalDomain
```

and so is this one when supplied a genuine global orbit:

```lean
critical_bounded_global_positive_restarted_affine_intervalDomain
```

## What fails

The local-to-global assembly

```lean
Theorem_1_2_intervalDomain_positive_critical_branch
```

is vacuous because its `hglobalExtension` field requires every arbitrary post-horizon modification of a bounded local solution to be a global solution.

## Honest one-line verdict

> **REFUTE the headline theorem's non-vacuity, but not its boundedness analysis:** the finite-\(L^P\) seed and restarted-Duhamel chain are genuinely closed; the sole fatal vacuity is the malformed universal continuation hypothesis at `IntervalDomainTheorem12PositiveCritical.lean:32--40`.
