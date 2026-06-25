# Q618 (cron2): fillability ranking for the 11 remaining sorries

Static inspection only; I did not run a Lean build.  The `chatgpt-scratch` branch exists as a scratch/drop branch, but the two source files were not present there through the connector, so I inspected the current source tree on `main` and wrote this report to `chatgpt-scratch`.

Files inspected:

- `ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean` — 6 sorries.
- `ShenWork/Paper2/IntervalConjugateBFormSourceTower.lean` — 5 sorries.

## Executive verdict

The closest sorries are not the deep chemDiv analytic ones.  The best first targets are the tower/wiring gaps and the compact-window boundedness/continuity gaps.  The real hard frontier is still the chemDiv source regularity: resolver `C⁴`, local chemDiv chain rule, and especially the uniform-in-mode bound for time-derivative coefficients.

Existing infrastructure already includes:

- heat semigroup `C⁴` on positive windows (`heatSemigroup_contDiff_four`);
- the spatial chemDiv weak-`H²` consumer once `U_cos` and `V_cos` are both `C⁴` (`chemDivSource_weakH2_of_cosineRep`);
- `DuhamelSourceTimeC1On` algebra/closures (`toOn`, `shift_zero`, `restrict_hi`, `const_mul`, `add`);
- level-0 and successor logistic source machinery;
- the windowed uniform-limit theorem `duhamelSourceTimeC1On_of_uniform_limit`;
- a named residual route for general chemDiv source regularity (`ChemDivSolutionRegularityResidual`).

Existing infrastructure does **not** yet appear to include:

- resolver `C⁴` for the chemical concentration; the committed resolver route I found gives `resolverValue_contDiff_two`;
- a general lower-endpoint extension theorem for `DuhamelSourceTimeC1On` from all `[c,T]`, `c>0`, to `[0,T]`;
- the `H²`/summable-envelope package for `∂ₜ(chemDiv source)` needed to get a uniform `Mdot` bound over all modes.

## Ranked locations, closest first

### 1. `IntervalConjugateBFormSourceTower.lean:60`

```lean
| zero =>
  intro c hc hcT
  sorry
```

**Fillability: high after a small interface repair; not a pure one-liner at the current type.**

This is only the tower base case.  The intended consumer is clearly the level-0 B-form source package from `IntervalConjugateLevel0BFormSourceOn.lean`, and the file comment already says it should use the level-0 theorem.  The local combination theorem `bFormSource_duhamelSourceTimeC1On` is already proved.

Obstacle: the current tower signature only has `DB`, `huPaper`, `hu₀pos`, and `Hinf`.  The level-0 auto theorem still needs hypotheses such as `1 ≤ p.α`, initial coefficient bound data, and the heat-window derivative bounds `G1/G2/Udot`.  `CM2Params` carries `0 < p.α`, `0 ≤ p.a`, `0 ≤ p.b`, but not `1 ≤ p.α`.  So the base case is close structurally, but the theorem signature/banked-input interface needs to expose the missing assumptions.

### 2. `IntervalConjugateLevel0BFormSourceOn.lean:273`

```lean
have hSup : ∃ (Msup : ℝ), 0 ≤ Msup ∧
    (∀ s ∈ Icc c T,
      ContinuousOn (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s)
        (Icc (0 : ℝ) 1)) ∧
    (∀ s ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s x| ≤ Msup) := by
  sorry
```

**Fillability: medium-high.**

This is just a compact-window value bound plus slice continuity for the chemDiv source.  It does not require coefficient decay, a time-derivative coefficient package, or a uniform derivative envelope.  The heat side is smooth on `[c,T]`, and existing resolver/chemDiv expression infrastructure should plausibly give continuity and boundedness on `[c,T] × [0,1]`.

Main remaining work: wire boundedness of the resolver/concentration and its spatial derivative into the explicit chemDiv expression, then use compactness to choose `Msup`.

### 3. `IntervalConjugateLevel0BFormSourceOn.lean:385`

```lean
have hjointcont : ContinuousOn
    (Function.uncurry (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivTimeDerivativeLift
      p (conjugatePicardIter p u₀ 0)))
    (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
  sorry
```

**Fillability: medium.**

There is already resolver time-regularity infrastructure around `coupledChemicalTimeDerivative_jointContinuousOn_closed` and `coupledChemicalTimeDerivative_continuousOn_Icc_of_lt_horizon`.  This sorry is mostly a composition/joint-continuity bridge for the explicit `coupledChemDivTimeDerivativeLift` field on a closed positive slab.

It is not as trivial as `hSup`, because `coupledChemDivTimeDerivativeLift` contains the heat time derivative/slope slice, the resolver time derivative, and spatial derivatives of those fields.  But it is still closer than the coefficient-envelope sorries: it only asks for joint continuity, not summable decay.

### 4. `IntervalConjugateBFormSourceTower.lean:73`

```lean
have _hlog : DuhamelSourceTimeC1On
    (coupledLogisticSourceCoeffs p (conjugatePicardIter p u₀ (n + 1))) c DB.T := by
  sorry -- Wires ih + intervalConjugateDuhamelMap_cosineSeries + sourceTimeC1On_succ
```

**Fillability: medium.**

The ordinary logistic recursion infrastructure is already present: `sourceTimeC1On_succ_of_sourceTimeC1On` consumes a predecessor source package, restart representation, positivity, boundedness, `G1/G2`, and joint profile continuity.  The B-form-specific representation theorem `intervalConjugateDuhamelMap_cosineSeries` is also present.

This looks like a substantial wiring proof rather than a new analytic theorem.  The nontrivial parts are threading the B-form restart coefficients/source bridge and exposing the same window bounds required by the logistic successor theorem.

### 5. `IntervalConjugateBFormSourceTower.lean:92`

```lean
noncomputable def conjBFormSourceTimeC1On_limit ... := by
  sorry
```

**Fillability: medium-low / data-heavy.**

The exact abstract tool exists: `duhamelSourceTimeC1On_of_uniform_limit`.  It already proves passage to the limit from pointwise coefficient convergence, derivative packages for the approximants, uniform derivative convergence, a common summable envelope, and a common derivative bound.

This is therefore not a new calculus theorem.  But the data it needs are heavy: coefficient convergence for the B-form source, uniform convergence of the `adot` fields, and common envelopes/bounds across the iterate tower.  It should be attempted only after the all-level tower packages have a uniform/banked version, not before.

### 6. `IntervalConjugateLevel0BFormSourceOn.lean:258`

```lean
have hL1_uniform : ∃ (B : ℝ), 0 ≤ B ∧ ∀ s (hs : s ∈ Icc c T),
    (∫ x in (0 : ℝ)..1, |(hH2_per_slice s hs).secondDeriv x|) ≤ B := by
  sorry
```

**Fillability: medium-low.**

Once the per-slice weak-`H²` object is available, this is conceptually a compactness argument: show the second-derivative representative is jointly continuous in `(s,x)`, then bound its `L¹` norm on `[c,T]`.

However, it depends on the preceding `hV_data`/per-slice `H²` construction and on identifying the chosen `secondDeriv` with a jointly continuous classical expression.  So it is less close than the plain value-bound `hSup`.

### 7. `IntervalConjugateLevel0BFormSourceOn.lean:370`

```lean
have hchain : ShenWork.IntervalCoupledRegularityBootstrap.CoupledChemDivLocalChainRule
    p (conjugatePicardIter p u₀ 0) := by
  sorry
```

**Fillability: low-medium.**

The target structure is already named and is exactly what the coefficient derivative proof consumes.  For level 0, the heat semigroup special case should be easier than the general iterate/limit case: `∂ₜu = Δu` is explicit on `s>0`.

Still, this is a real analytic chain-rule slab, not just algebra.  The repo’s later `ChemDivWinDischarge` audit treats this chain-rule/joint-`C²` leg as part of the genuine regularity residual for general solutions.  For level 0 it may be fillable by specializing heat/resolver time regularity, but it is not among the easiest sorries.

### 8. `IntervalConjugateLevel0BFormSourceOn.lean:241`

```lean
have hV_data : ∃ V_cos : ℝ → ℝ,
    ContDiff ℝ 4 V_cos ∧
    (∀ x, (0 : ℝ) < 1 + V_cos x) ∧
    (∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (coupledChemicalConcentration p
        (conjugatePicardIter p u₀ 0) s) x = V_cos x) ∧
    (∀ x, V_cos (-x) = V_cos x) ∧
    (∀ x, V_cos (2 - x) = V_cos x) := by
  sorry
```

**Fillability: low.**

The consumer is ready: `chemDivSource_weakH2_of_cosineRep` will produce the weak-`H²` chemDiv source once `U_cos` and `V_cos` are both `C⁴`, positive/agreed/parity compatible.  The heat `U_cos` side is also ready via `heatSemigroup_contDiff_four`.

The missing piece is the resolver/concentration representative `V_cos` with `ContDiff ℝ 4`.  The committed resolver route I found proves `resolverValue_contDiff_two`, not `C⁴`.  The comment in the file is accurate: this needs the higher Sobolev/resolver gain route (`H^σ` with `σ > 4.5` or equivalent) plus agreement/parity/positivity.  That is new infrastructure, not just local proof search.

### 9. `IntervalConjugateBFormSourceTower.lean:111`

```lean
noncomputable def hsrcBDirect_of_data ... :
    DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) 0 DB.T := by
  sorry
```

**Fillability: low.**

This is the endpoint wall: convert positive-window packages `[c,T]`, for every `c>0`, into a package on `[0,T]`.  Existing `DuhamelSourceTimeC1On` has `toOn`, `shift_zero`, and `restrict_hi`, but I did not find a lower-endpoint extension theorem.  `restrict_hi` only moves the upper endpoint.

A direct construction at `s=0` may be possible using the `dite` definition of `conjugatePicardLimit`, but then one must prove the value envelope and derivative-bound fields at `0` and reconcile them with the positive-window packages.  This is a separate endpoint bridge, not currently packaged.

### 10. `IntervalConjugateBFormSourceTower.lean:77`

```lean
have _hchem : DuhamelSourceTimeC1On
    (coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ (n + 1))) c DB.T := by
  sorry -- Needs chemDiv C² for iterate n+1 (same gap as level 0)
```

**Fillability: very low.**

This is the general-iterate chemDiv source package.  It inherits the same spatial/time chemDiv regularity gap as level 0, but without the simplifying heat semigroup formula.  For successors, the source must be recovered from the B-form restart/cosine representation and the regularity bootstrap.

The closest existing pattern is not a direct proof but the residual abstraction in `IntervalChemDivWinDischarge.lean`: supply a `ChemDivSolutionRegularityResidual` carrying `IterateSourceTimeData`, FAC slab data, weak-`H²`/decay, `hadotcont`, and `hMdot`, then produce the chemDiv source package.  So this sorry is probably not fillable without adding or threading such residual data through the tower.

### 11. `IntervalConjugateLevel0BFormSourceOn.lean:432`

```lean
have hMdot : ∃ (Mdot : ℝ), ∀ s ∈ Icc c T, ∀ n, |adot s n| ≤ Mdot := by
  sorry
```

**Fillability: very low / hardest.**

The file itself labels this a genuine residual, and I agree.  The preceding proof already gets per-mode differentiability and continuity once `hchain`/`hjointcont` are available.  What is missing here is a bound uniform in `n` for all time-derivative coefficients.

That requires the time-derivative field `coupledChemDivTimeDerivativeLift` to have a summable or at least uniformly bounded cosine-coefficient envelope.  The comment says the right route is `H²` of `∂ₜ(chemDiv source)`, which means controlling additional spatial derivatives plus one time derivative of the chemDiv functional.  I did not find that package in the current repo infrastructure.

## Suggested attack order

1. Fix the tower interfaces first: expose or bank the assumptions needed by the level-0 and successor logistic packages (`1 ≤ p.α`, initial coefficient bound, `G1/G2/Udot`, profile/joint bounds).  This should make the tower base and logistic successor mostly wiring.
2. Fill `hSup` next.  It is a compactness/value-continuity lemma and avoids coefficient derivative decay.
3. Then try `hjointcont`, using the resolver time-regularity lemmas already present.
4. Do not start with `hMdot` or successor `_hchem`; factor those through a named residual/banked package, analogous to `ChemDivSolutionRegularityResidual`, unless the goal is specifically to build the missing high-regularity analytic chain.
