# Q2637 shen1 — audit of actual-linear-small statement thinning plan

Repo: `xiangyazi24/Shen_work`

Target file: `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`

Verdict: the plan is sound.  The useful Lean-level adjustments are mostly about exact field names, avoiding brittle `linarith` in impossible branches, and keeping the two Paper3 constants packages separate.

## Main Lean pitfalls to avoid

1. The CM2Params field is spelled `p.χ₀`, not `p.chi0` or `p.chi0`.  Use names like `hχ0` / `hchi_pos`, but the field projection itself must be `p.χ₀`.

2. The raw Theorem 2.2 fields in `IntervalDomainPaper3CoreStatementActualLinear22Data` use **sectorial** constants and sectorial C¹ distance:

```lean
LinearStabilityInstabilityNonminimalRaw intervalDomain p
  unitIntervalNeumannSpectrum
  intervalDomainSectorialStabilityNorms.c1Distance
  (intervalDomainSectorialPaper3Constants p M0 uBar vLower).chiCritical
```

Do **not** switch these to `intervalDomainPaper3Constants`.  The `stability24` fields use `intervalDomainPaper3Constants`; the raw Theorem 2.2 fields use `intervalDomainSectorialPaper3Constants`.

3. Do not thread or derive `0 ≤ p.β` in the thinning wrappers.  The `global24` / `exp24` fields already take `0 ≤ p.β` as an argument.  The actual-linear wrapper theorem still needs `hβ : 1 ≤ p.β` for persistence, but `.toStability23To25` should simply forward `h.global24` and `h.exp24`.

4. For impossible branches, prefer robust `False.elim` terms over `exfalso; linarith`:

```lean
False.elim (not_le_of_gt hchi_pos hchi_nonpos)
False.elim ((ne_of_gt ha_pos) ha0)
```

`linarith` probably closes both contradictions, but the direct proofs are less fragile and avoid any issue with equality normalization.

5. `IntervalDomainPaper3SupNormCompactnessRegularizationData.toConcrete` has exactly these fields to fill before conversion:

```lean
compact
initialContinuity
minimalUpper
resolvent
```

`.toConcrete` fills `upperEq` definitionally for:

```lean
intervalDomainSupNormCompactnessData locallyConverges neumannResolventGradientBound
```

6. Place the new declarations after the existing theorem:

```lean
intervalDomain_paper3_mainlineTargets_of_actualLinear22FrontierData
```

or at least after `IntervalDomainPaper3MainlineActualLinear22FrontierData` and after any declarations the final wrapper calls.  Lean has no forward references.

## Confident patch skeleton

This should be insertable in `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean` after the existing `intervalDomain_paper3_mainlineTargets_of_actualLinear22FrontierData` theorem and before or after its `Fact` wrapper.  No extra imports are needed in that file.

```lean
/-- In the actual-linear-small route, the only non-vacuous Theorem 2.3--2.5
stability frontiers are the positive-sensitivity nonminimal Theorem 2.4 branches.
The Theorem 2.3 branches assume `p.χ₀ ≤ 0`, contradicting the wrapper hypothesis
`0 < p.χ₀`; the Theorem 2.5 branches assume `p.a = 0`, contradicting `0 < p.a`. -/
structure IntervalDomainPaper3Stability24ActualLinearFrontierData
    (p : CM2Params) (C : Paper3Constants intervalDomain p) : Prop where
  global24 :
    0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        NonminimalGlobalStabilityCondition intervalDomain p C eq.1 →
          GloballyAsymptoticallyStableNonminimal intervalDomain p
            eq.1 eq.2
  exp24 :
    0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        NonminimalGlobalStabilityCondition intervalDomain p C eq.1 →
          ∃ A > 0, ∃ rate > 0,
            ∀ u v : ℝ → intervalDomain.Point → ℝ,
              PositiveGlobalBoundedSolution intervalDomain p u v →
              UniformConvergesInSup intervalDomain u eq.1 →
                ExponentialC1ConvergenceWith intervalDomain
                  intervalDomainStabilityNorms u v eq.1 eq.2 A rate

/-- Expand the actual-linear-small Theorem 2.4-only stability frontier into the
existing full Theorem 2.3--2.5 frontier by filling the impossible sign/branch
cases by contradiction. -/
def IntervalDomainPaper3Stability24ActualLinearFrontierData.toStability23To25
    {p : CM2Params} {C : Paper3Constants intervalDomain p}
    (h : IntervalDomainPaper3Stability24ActualLinearFrontierData p C)
    (ha_pos : 0 < p.a) (hchi_pos : 0 < p.χ₀) :
    IntervalDomainPaper3Stability23To25FrontierData p C where
  globalNonminimal23 := by
    intro hchi_nonpos _hm _ha _hb
    exact False.elim (not_le_of_gt hchi_pos hchi_nonpos)
  globalMinimal23 := by
    intro hchi_nonpos _hm _ha0 _hb0 _uStar _huStar
    exact False.elim (not_le_of_gt hchi_pos hchi_nonpos)
  expNonminimal23 := by
    intro hchi_nonpos _hm _ha _hb
    exact False.elim (not_le_of_gt hchi_pos hchi_nonpos)
  expMinimal23 := by
    intro hchi_nonpos _hm _ha0 _hb0 _uStar _huStar
    exact False.elim (not_le_of_gt hchi_pos hchi_nonpos)
  global24 := h.global24
  exp24 := h.exp24
  global25 := by
    intro ha0 _hb0 _hm _hbeta _uStar _huStar
    exact False.elim ((ne_of_gt ha_pos) ha0)
  exp25 := by
    intro ha0 _hb0 _hm _hbeta _uStar _huStar
    exact False.elim ((ne_of_gt ha_pos) ha0)

/-- Compactness/regularization data for the actual-linear-small route after
choosing the canonical sup-norm compactness package and using `0 < p.a` to make
the minimal-upper branch impossible.  Initial continuity is supplied once by the
surrounding thin mainline data. -/
structure IntervalDomainPaper3SupNormCompactnessAPosData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  compact : TimeTranslateCompactnessRaw intervalDomain p locallyConverges
  resolvent :
    NeumannResolventGradientBoundExistsRaw intervalDomain
      neumannResolventGradientBound

/-- Convert the positive-`a` sup-norm compactness data into the existing sup-norm
compactness/regularization data surface. -/
def IntervalDomainPaper3SupNormCompactnessAPosData.toSupNormData
    {p : CM2Params} {M0 uBar vLower : ℝ}
    {locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop}
    {neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop}
    (h : IntervalDomainPaper3SupNormCompactnessAPosData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound)
    (ha_pos : 0 < p.a)
    (hcont : IntervalDomainInitialContinuityRaw p) :
    IntervalDomainPaper3SupNormCompactnessRegularizationData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound where
  compact := h.compact
  initialContinuity := hcont
  minimalUpper := by
    intro ha0 _hb0 _hm _hbeta _hchi0 _hchi _u _v _huv
    exact False.elim ((ne_of_gt ha_pos) ha0)
  resolvent := h.resolvent

/-- Thin actual-linear raw-Theorem-2.2 mainline data.  It carries initial
continuity once, uses the sectorial constants for raw Theorem 2.2, uses the
canonical sup-norm compactness package, and carries only the non-vacuous
positive-sensitivity Theorem 2.4 stability frontiers. -/
structure IntervalDomainPaper3MainlineActualLinear22ThinFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  initialContinuity : IntervalDomainInitialContinuityRaw p
  theorem22Nonminimal :
    LinearStabilityInstabilityNonminimalRaw intervalDomain p
      unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms.c1Distance
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower).chiCritical
  theorem22Minimal :
    LinearStabilityInstabilityMinimalRaw intervalDomain p
      unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms.c1Distance
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower).chiCritical
  compactness :
    IntervalDomainPaper3SupNormCompactnessAPosData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound
  stability24 :
    IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Convert the thin actual-linear mainline data to the existing full surface. -/
def IntervalDomainPaper3MainlineActualLinear22ThinFrontierData.toCurrent
    {p : CM2Params} {M0 uBar vLower : ℝ}
    {locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop}
    {neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop}
    (h : IntervalDomainPaper3MainlineActualLinear22ThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound)
    (ha_pos : 0 < p.a) (hchi_pos : 0 < p.χ₀) :
    IntervalDomainPaper3MainlineActualLinear22FrontierData
      p M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) where
  core :=
    { initialContinuity := h.initialContinuity
      theorem22Nonminimal := h.theorem22Nonminimal
      theorem22Minimal := h.theorem22Minimal }
  compactness :=
    (h.compactness.toSupNormData ha_pos h.initialContinuity).toConcrete
  stability := h.stability24.toStability23To25 ha_pos hchi_pos

/-- Mainline target from the thin actual-linear raw-Theorem-2.2 route. -/
theorem intervalDomain_paper3_mainlineTargets_of_actualLinear22ThinFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineActualLinear22ThinFrontierData
        p M0 uBar vLower locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_mainlineTargets_of_actualLinear22FrontierData
    p M0 uBar vLower
    (intervalDomainSupNormCompactnessData
      locallyConverges neumannResolventGradientBound)
    ha hb hχ0 hm hβ hχ (hData.toCurrent ha hχ0)
```

## Checklist against the planned implementation

### Plan item 1: `IntervalDomainPaper3Stability24ActualLinearFrontierData`

Good.  Copy the `global24` and `exp24` types exactly from `IntervalDomainPaper3Stability23To25FrontierData`.  They are parameterized by an arbitrary `C : Paper3Constants intervalDomain p`, so this structure should also take `C`, not hard-code concrete constants.

### Plan item 2: `.toStability23To25`

Good.  Use:

```lean
not_le_of_gt hchi_pos hchi_nonpos
(ne_of_gt ha_pos) ha0
```

rather than relying on `linarith`.  This avoids equality-normalization issues in the `p.a = 0` branches.  `0 ≤ p.β` is not involved in this conversion; do not derive it here.

### Plan item 3: `IntervalDomainPaper3SupNormCompactnessAPosData`

Good.  It should carry only:

```lean
compact
resolvent
```

and `.toSupNormData` should take both:

```lean
(ha_pos : 0 < p.a)
(hcont : IntervalDomainInitialContinuityRaw p)
```

because `initialContinuity` is still needed by `IntervalDomainPaper3SupNormCompactnessRegularizationData`, but should be shared from the thin mainline data.

### Plan item 4: `IntervalDomainPaper3MainlineActualLinear22ThinFrontierData`

Good.  Make sure the raw Theorem 2.2 fields use:

```lean
intervalDomainSectorialStabilityNorms.c1Distance
(intervalDomainSectorialPaper3Constants p M0 uBar vLower).chiCritical
```

not the non-sectorial `intervalDomainPaper3Constants`.

### Plan item 5: `.toCurrent`

Good.  The target type should be exactly:

```lean
IntervalDomainPaper3MainlineActualLinear22FrontierData
  p M0 uBar vLower
  (intervalDomainSupNormCompactnessData
    locallyConverges neumannResolventGradientBound)
```

and the compactness field should be:

```lean
compactness :=
  (h.compactness.toSupNormData ha_pos h.initialContinuity).toConcrete
```

If method notation fails inference, expand it explicitly:

```lean
compactness :=
  (IntervalDomainPaper3SupNormCompactnessAPosData.toSupNormData
    (p := p) (M0 := M0) (uBar := uBar) (vLower := vLower)
    (locallyConverges := locallyConverges)
    (neumannResolventGradientBound := neumannResolventGradientBound)
    h.compactness ha_pos h.initialContinuity).toConcrete
```

### Plan item 6: mainline theorem

Good.  It should call:

```lean
intervalDomain_paper3_mainlineTargets_of_actualLinear22FrontierData
```

with `K := intervalDomainSupNormCompactnessData locallyConverges neumannResolventGradientBound` and pass:

```lean
hData.toCurrent ha hχ0
```

The theorem still needs all existing actual-linear-small hypotheses:

```lean
ha hb hχ0 hm hβ hχ
```

because the underlying `to_linear22Data` call uses them to produce actual-linear persistence.

## Optional extra wrapper

After the mainline theorem compiles, an instance-facing wrapper would be routine:

```lean
theorem intervalDomain_paper3_mainlineTargets_of_actualLinear22ThinFrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineActualLinear22ThinFrontierData
        p M0 uBar vLower locallyConverges neumannResolventGradientBound)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_mainlineTargets_of_actualLinear22ThinFrontierData
    p M0 uBar vLower locallyConverges neumannResolventGradientBound
    ha hb hχ0 hm hβ hχ hData.out
```

## Final assessment

The thinning is non-vacuous and safe.  It removes duplicated `initialContinuity`, the definitional `upperEq`, the impossible positive-`a` minimal-upper branch, and the six impossible Theorem 2.3/2.5 stability branches.  The remaining fields are the real statement-level frontiers:

```text
initialContinuity
theorem22Nonminimal
theorem22Minimal
compact
resolvent
global24
exp24
```

plus proposition-side data outside this mainline package, especially `negativeBound` and Paper2 main theorem targets.
