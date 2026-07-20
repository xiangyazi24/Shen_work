ANSWER Q129 533e74e7

# Interface audit at commit 503e085561e3bf1d0cfd513eb2da2404974e93c8

## Verdict

1. Yes. The repository has ceiling-regime-free short-time existence for every nonnegative WholeLineBUC datum. There is both an original, unclamped mild-solution theorem and a classical-solution theorem. Neither assumes WholeLineCauchyCeilingRegime p.

1. No. At this commit there is no Paper 1 whole-line maximal-solution object, blow-up alternative, finite-horizon alternative, or theorem saying that a bounded solution on [0,T) extends past T. The closest interfaces are a uniform local restart factory for bounded BUC data and a canonical restart-uniqueness theorem inside an already existing time interval.

1. In the canonical gluing chain, WholeLineCauchyCeilingRegime p is used only to manufacture and propagate one reusable scalar invariant ceiling. The Banach fixed point, nonnegativity, restart identities, restriction identities, and fixed-point uniqueness are regime-free. No call in the traced chain uses the regime for a structural feature that an independently supplied a-priori strip bound could not replace. The current definitions do, however, hard-code wholeLineCauchyStableCeiling, so injecting a different bound requires a new parameterized segment family or a parallel gluing theorem.

# 1. Local existence is ceiling-regime-free

## 1.1 Raw Banach fixed point for the truncated mild map

WholeLineCauchyBUCFixedPoint.lean:446-449 states:

```javascript
theorem exists_wholeLineCauchyBUCMildFixedPoint
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) (u₀ : WholeLineBUC) :
    ∃ (T : ℝ) (hT : 0 < T) (U : WholeLineBUCTrajectory T),
      IsFixedPt (wholeLineCauchyBUCMildMap p hM hT.le u₀) U := by
```

This theorem has no sign or parameter-regime hypothesis at all. It constructs the Banach fixed point of the globally truncated map at an arbitrary chosen clamp height M≥0.

The contraction time is supplied by WholeLineCauchyBUCFixedPoint.lean:256-277:

```javascript
theorem exists_pos_time_wholeLineCauchyBUCMildRate_lt_one
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) :
    ∃ T : ℝ, 0 < T ∧ wholeLineCauchyBUCMildRate p M T < 1 := by
```

Again, there is no WholeLineCauchyCeilingRegime hypothesis.

## 1.2 Original unclamped mild equation for arbitrary nonnegative BUC data

The exact theorem answering the question is WholeLineCauchyNonnegativity.lean:593-605:

```javascript
theorem exists_wholeLineCauchy_original_BUC_mildSolution
    (p : CMParams) (u₀ : WholeLineBUC)
    (hu₀ : ∀ x : ℝ, 0 ≤ u₀.1 x) :
    let M := ‖u₀‖ + 1
    ∃ (T : ℝ) (hT : 0 < T)
      (hsmall : wholeLineCauchyBUCMildRate p M T < 1),
      let U := wholeLineCauchyBUCMildFixedPoint p (by positivity) hT.le
        u₀ hsmall
      (∀ (z : Set.Icc (0 : ℝ) T) (x : ℝ),
        (U z).1 x ∈ Set.Ico (0 : ℝ) M) ∧
      ∀ (z : Set.Icc (0 : ℝ) T) (x : ℝ),
        (U z).1 x = wholeLineCauchyMildMap p u₀.1
          (fun t y => (wholeLineBUCTrajectoryExtend hT.le U t).1 y) z.1 x := by
```

Its only substantive hypotheses are:

```javascript
p : CMParams
u₀ : WholeLineBUC
hu₀ : ∀ x, 0 ≤ u₀.1 x
```

The proof chooses the temporary local clamp M=‖u₀‖+1, proves that the fixed point lies in 0≤u<M, and then proves that the clamped equation equals the original unclamped Duhamel equation. Thus it is ceiling-regime-free, although the Banach construction internally uses a temporary local truncation.

The physical-strip producer used by that theorem is WholeLineCauchyNonnegativity.lean:502-513:

```javascript
theorem exists_wholeLineCauchyBUCMildFixedPoint_in_physical_strip
    (p : CMParams) (u₀ : WholeLineBUC)
    (hu₀ : ∀ x : ℝ, 0 ≤ u₀.1 x) :
    let M := ‖u₀‖ + 1
    ∃ (T : ℝ) (hT : 0 < T)
      (hsmall : wholeLineCauchyBUCMildRate p M T < 1),
      ∀ (z : Set.Icc (0 : ℝ) T) (x : ℝ),
        (wholeLineCauchyBUCMildFixedPoint p (by positivity) hT.le
          u₀ hsmall z).1 x ∈ Set.Ico (0 : ℝ) M := by
```

## 1.3 Classical local solution, also regime-free

WholeLineCauchyClassicalSolution.lean:123-130 states:

```javascript
theorem exists_wholeLineCauchy_classicalSolution
    (p : CMParams) (u₀ : WholeLineBUC)
    (hu₀ : ∀ x : ℝ, 0 ≤ u₀.1 x) :
    ∃ (T : ℝ) (u v : ℝ → ℝ → ℝ),
      0 < T ∧ IsClassicalSolution p T u v ∧
        HasInitialDatum u u₀.1 ∧ HasUniformInitialTrace u u₀.1 := by
```

This is a genuine local classical solution of the original system with the prescribed datum and uniform initial trace. It also has no WholeLineCauchyCeilingRegime hypothesis.

Answer to (1): yes. The local theory is already ceiling-regime-free at both the mild and classical interfaces.

# 2. No whole-line maximal-continuation or blow-up-alternative theorem

I found no Paper 1 whole-line theorem at this commit with any of the following interfaces:

```javascript
MaximalCauchySolution ...
FiniteHorizonAlternative ...
Tmax ...
BoundedOn [0,T) → extends past T
```

Repository searches for maximalTime, blowupAlternative, finiteHorizonAlternative, Tmax, and whole-line continuation terminology found no such Paper 1 theorem. WholeLineWeightedRegularityMaximal.lean concerns maximal weighted regularity, not maximal lifespan or continuation.

The code’s own frontier audit confirms that Paper 1 is presently formulated as a direct global-existence obligation. Proposition11FrontierAudit.lean:24-29 reads:

```javascript
abbrev GlobalExistenceField : Prop :=
  ∀ p : CMParams,
    ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ →
      ∃ u v : ℝ → ℝ → ℝ, IsGlobalCauchySolutionFrom p u₀ u v
```

By contrast, the same audit gives Paper 2 an explicit finite-horizon alternative field. Proposition11FrontierAudit.lean:97-105 reads:

```javascript
abbrev FiniteHorizonAlternativeField (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
    ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v →
      InitialTrace intervalDomain u₀ u →
        FiniteHorizonAlternative intervalDomain Tmax u ∧
        (1 ≤ p.m → MGeOneFiniteHorizonAlternative intervalDomain Tmax u)
```

There is no analogous whole-line declaration.

## Closest interface 1: uniform local restart factory

WholeLineCauchyUniformRestart.lean:22-32 states:

```javascript
theorem exists_uniform_wholeLineCauchy_classicalRestart
    (p : CMParams) {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 < eta) :
    ∃ T > 0, ∀ u₀ : WholeLineBUC,
      (∀ x : ℝ, 0 ≤ u₀.1 x) → ‖u₀‖ + eta ≤ M →
        ∃ u v : ℝ → ℝ → ℝ,
          IsClassicalSolution p T u v ∧
            HasInitialDatum u u₀.1 ∧ HasUniformInitialTrace u u₀.1 ∧
            ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ,
              u t x ∈ Set.Icc (0 : ℝ) M := by
```

This is the correct local lifespan atom: one fixed norm ceiling and positive margin produce a common restart time. But it starts from a supplied WholeLineBUC datum; it does not accept a solution on [0,T) and prove extension through the endpoint.

## Closest interface 2: canonical restart consistency inside an existing horizon

WholeLineCauchyCanonicalRestart.lean:135-149 states:

```javascript
theorem wholeLineCauchyBUCMildFixedPoint_shift_eq
    (p : CMParams) {M T t h : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmallT : wholeLineCauchyBUCMildRate p M T < 1)
    (ht : 0 < t) (hh : 0 < h) (hth : t + h ≤ T)
    (hsmallh : wholeLineCauchyBUCMildRate p M h < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmallT z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmallT
    let zt : Set.Icc (0 : ℝ) T :=
      ⟨t, ht.le, (le_add_of_nonneg_right hh.le).trans hth⟩
    wholeLineBUCTrajectoryShift ht.le hh.le hth U =
      wholeLineCauchyBUCMildFixedPoint p hM hh.le (U zt) hsmallh := by
```

The hypothesis t+h≤T is decisive: the larger trajectory already exists. This is a restart-uniqueness identity, not an extension theorem.

Similarly, WholeLineCauchyCanonicalRestart.lean:242-251 only identifies a restriction of an existing fixed point with the directly constructed shorter-horizon fixed point.

## Current global factory still requires the ceiling regime

WholeLineCauchyGlobalGluing.lean:435-439 states:

```javascript
theorem wholeLineCauchyGlobal_isGlobalClassicalSolution
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x) :
    IsGlobalClassicalSolution p
      (wholeLineCauchyGlobalU p u₀) (wholeLineCauchyGlobalV p u₀) := by
```

Answer to (2): no. The ingredients for a continuation theorem are partially present, but no theorem packages them into a maximal solution, endpoint extension, or blow-up alternative. Missing interfaces include at least: an arbitrary partial-solution object, a theorem producing a BUC endpoint/restart slice from a bounded orbit, arbitrary-solution uniqueness/pasting, and the actual extension theorem.

# 3. Exact entry points of WholeLineCauchyCeilingRegime in canonical gluing

## 3.1 Target theorem signature

WholeLineCauchyCanonicalSegments.lean:199-211 states:

```javascript
theorem wholeLineCauchyGlobalDatum_segment_bounds
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x) :
    ∀ n,
      ((∀ x, 0 ≤ (wholeLineCauchyGlobalDatum p u₀ n).1 x) ∧
        (∀ x, (wholeLineCauchyGlobalDatum p u₀ n).1 x ≤
          wholeLineCauchyStableCeiling p u₀)) ∧
      ((∀ z x, (wholeLineCauchyGlobalSegment p u₀ n z).1 x ∈
          Set.Icc (0 : ℝ) (wholeLineCauchyGlobalClamp p u₀)) ∧
        (∀ z x, (wholeLineCauchyGlobalSegment p u₀ n z).1 x ≤
          wholeLineCauchyStableCeiling p u₀)) := by
```

The recursive definitions wholeLineCauchyGlobalDatum and wholeLineCauchyGlobalSegment themselves do not take hregime; they are total definitions built from the truncated fixed point. The regime is needed to prove that every recursively generated datum remains in the same reusable box.

## 3.2 Direct uses inside wholeLineCauchyGlobalDatum_segment_bounds

There is exactly one regime-consuming lemma called directly, twice:

- Base case: WholeLineCauchyCanonicalSegments.lean:223-230

- Successor case: WholeLineCauchyCanonicalSegments.lean:245-252

Both calls are:

```javascript
wholeLineCauchyCanonicalSegment_bounds_of_datum
  p hregime u₀ ... hdatum.1 hdatum.2
```

Everything else in the induction merely reads the midpoint slice of the preceding segment.

## 3.3 Full transitive call chain

```plain text
wholeLineCauchyGlobalDatum_segment_bounds
└─ wholeLineCauchyCanonicalSegment_bounds_of_datum
   ├─ wholeLineCauchyStableCeiling_one_le
   ├─ wholeLineCauchyStableCeiling_margin
   │  └─ wholeLineCauchyStableCeiling_one_le
   └─ wholeLineCauchyBUCMildFixedPoint_stable_ceiling_Icc
      └─ wholeLineCauchyBUCMildFixedPoint_stable_ceiling_Ico
         └─ wholeLineSlabSup_le_of_stable_resolver_pde
            └─ wholeLineCauchyCeiling_strict_margin_above
```

No other named lemma in this transitive proof consumes WholeLineCauchyCeilingRegime.

## 3.4 Classification of every regime-consuming lemma

### A. wholeLineCauchyCanonicalSegment_bounds_of_datum — category (i)

Signature at WholeLineCauchyCanonicalSegments.lean:119-132:

```javascript
theorem wholeLineCauchyCanonicalSegment_bounds_of_datum
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ w : WholeLineBUC)
    (hw0 : ∀ x, 0 ≤ w.1 x)
    (hwC : ∀ x, w.1 x ≤ wholeLineCauchyStableCeiling p u₀) :
    let U := wholeLineCauchyBUCMildFixedPoint p
      (wholeLineCauchyGlobalClamp_pos p u₀).le
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le w
      (wholeLineCauchyGlobalSegmentTime_rate p u₀)
    (∀ z x, (U z).1 x ∈ Set.Icc (0 : ℝ)
      (wholeLineCauchyGlobalClamp p u₀)) ∧
    (∀ z x, (U z).1 x ≤ wholeLineCauchyStableCeiling p u₀) := by
```

Its local fixed-point construction, displacement estimate, temporary clamp bound, and nonnegativity proof are regime-free. In its body, the regime is used at lines 141, 186-194 only to establish and propagate the sharper scalar ceiling C=wholeLineCauchyStableCeiling p u₀.

Classification: (i) only a scalar invariant upper bound.

### B. wholeLineCauchyStableCeiling_one_le — category (i)

WholeLineCauchyGlobalBounds.lean:80-95:

```javascript
theorem wholeLineCauchyStableCeiling_one_le
    {p : CMParams} (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) :
    1 ≤ wholeLineCauchyStableCeiling p u₀ := by
```

This supplies C≥1 and hence C≥0 for the norm and scalar-barrier calculations.

Classification: (i), purely scalar.

### C. wholeLineCauchyStableCeiling_margin — category (i)

WholeLineCauchyGlobalBounds.lean:190-229:

```javascript
theorem wholeLineCauchyStableCeiling_margin
    {p : CMParams} (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) :
    1 + max p.χ 0 *
        (wholeLineCauchyStableCeiling p u₀) ^ (p.m + p.γ - 1) ≤
      (wholeLineCauchyStableCeiling p u₀) ^ p.α := by
```

This is exactly the constant supersolution inequality for the chosen ceiling.

Classification: (i), purely scalar.

### D. wholeLineCauchyBUCMildFixedPoint_stable_ceiling_Icc — category (i)

WholeLineCauchyStableCeilingCanonical.lean:160-173:

```javascript
theorem wholeLineCauchyBUCMildFixedPoint_stable_ceiling_Icc
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    {M T C : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    (hC1 : 1 ≤ C)
    (hmargin : 1 + max p.χ 0 * C ^ (p.m + p.γ - 1) ≤ C ^ p.α)
    (hinit : ∀ x, u₀.1 x ≤ C) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineBUCTrajectoryExtend hT.le
        (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall) t).1 x ≤ C := by
```

It forwards the regime to the open-endpoint theorem and then closes the terminal endpoint by time continuity.

Classification: (i), propagation of a scalar ceiling.

### E. wholeLineCauchyBUCMildFixedPoint_stable_ceiling_Ico — category (i)

WholeLineCauchyStableCeilingCanonical.lean:24-37 has the same scalar inputs and returns u≤C on Ico 0 T. Its only regime-consuming call is the slab maximum principle at lines 72-74:

```javascript
apply wholeLineSlabSup_le_of_stable_resolver_pde
  p hregime hSpos hC1 hmargin hjoint
```

Classification: (i), propagation of a scalar ceiling.

### F. wholeLineSlabSup_le_of_stable_resolver_pde — category (i), with an internal sign split

WholeLineCauchyStableCeilingPDE.lean:26-54 states:

```javascript
theorem wholeLineSlabSup_le_of_stable_resolver_pde
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    {T C A : ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0 < T) (hC1 : 1 ≤ C)
    (hmargin : 1 + max p.χ 0 * C ^ (p.m + p.γ - 1) ≤ C ^ p.α)
    ... :
    wholeLineSlabSup T u ≤ C := by
```

Its two actual regime uses are visible at lines 67-71:

```javascript
have hstrictMargin : ∀ r, C < r →
    1 + max p.χ 0 * r ^ (p.m + p.γ - 1) < r ^ p.α :=
  fun r hr => wholeLineCauchyCeiling_strict_margin_above
    hregime hC1 hmargin hr
rcases hregime with hχ | hpos
```

The case split chooses the appropriate contact estimate for χ≤0 or χ≥0. This is internally essential to this particular maximum-principle proof, but its output is only slabSup≤C. An independently supplied a-priori strip bound would replace this entire theorem without changing the fixed-point or restart machinery.

Classification: (i), not (ii).

### G. wholeLineCauchyCeiling_strict_margin_above — category (i)

WholeLineCauchyGlobalBounds.lean:233-241 states:

```javascript
theorem wholeLineCauchyCeiling_strict_margin_above
    {p : CMParams} (hregime : WholeLineCauchyCeilingRegime p)
    {C L : ℝ} (hC1 : 1 ≤ C)
    (hmargin :
      1 + max p.χ 0 * C ^ (p.m + p.γ - 1) ≤ C ^ p.α)
    (hCL : C < L) :
    1 + max p.χ 0 * L ^ (p.m + p.γ - 1) < L ^ p.α := by
```

Classification: (i), scalar strictness above the barrier.

## 3.5 The overlap/uniqueness part of gluing is regime-free once the strip is known

wholeLineCauchyGlobalSegment_overlap takes hregime, but the body uses it only to obtain the physical strip:

```javascript
have hstripn :=
  (wholeLineCauchyGlobalDatum_segment_bounds p hregime u₀ hu₀ n).2.1
```

See WholeLineCauchyCanonicalSegments.lean:277-290. It then calls:

```javascript
wholeLineCauchyBUCMildFixedPoint_shift_eq
wholeLineCauchyBUCMildFixedPoint_restrict_eq
```

Neither theorem takes WholeLineCauchyCeilingRegime; both are fixed-point uniqueness/restart identities.

# Final one-paragraph verdict

The current codebase does contain a ceiling-regime-free local Cauchy theory: nonnegative BUC data generate an original unclamped mild solution and a classical solution on a positive interval. It also contains the two principal local continuation ingredients—a norm-uniform restart lifespan and canonical restart uniqueness. It does not contain a ceiling-free continuation theorem or blow-up alternative. The committed global construction instead fixes one stable ceiling and one uniform segment time in advance and recursively glues canonical segments; WholeLineCauchyCeilingRegime is used solely to prove that every restart datum remains under that same ceiling. A different a-priori bound could replace the regime mathematically, but the present canonical segment definitions are hard-wired to wholeLineCauchyStableCeiling, so a usable ceiling-free continuation route still requires a new parameterized gluing/maximal-continuation interface.