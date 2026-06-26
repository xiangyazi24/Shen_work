# Q708 / cron1: joint continuity of heat-level chemDiv source

Repo inspected: `xiangyazi24/Shen_work`.  Scratch write target: branch `chatgpt-scratch`.

## Verdict

I did **not** find a completed theorem with the exact target:

```lean
ContinuousOn
  (Function.uncurry
    (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0)))
  (Icc c T ×ˢ Icc (0 : ℝ) 1)
```

or the equivalent uncurried heat-level chemDiv-source statement.

The closest heat-level file is:

```text
ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
```

Inside `level0_chemDiv_envelope_summable`, the desired joint continuity is explicitly described as part of a `sorry` block.  The local subgoal `hSup` only concludes per-slice continuity plus a uniform sup bound:

```lean
have hSup : ∃ (Msup : ℝ), 0 ≤ Msup ∧
    (∀ s ∈ Icc c T,
      ContinuousOn (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s)
        (Icc (0 : ℝ) 1)) ∧
    (∀ s ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s x| ≤ Msup) := by
  -- SORRY: sup bound + continuity of chemDiv source slices (>30 lines).
  ...
  sorry
```

The comments in that block say the uncurried map

```text
(s,x) ↦ chemDivSourceLift p (S(·)u₀) s x
```

should be continuous on `[c,T] × [0,1]`, but the repo does not appear to have a standalone completed theorem for it.

## 1. Search for `coupledChemDivSourceLift.*ContinuousOn` / `continuousOn.*chemDivSource`

Searches run:

```text
coupledChemDivSourceLift ContinuousOn
continuousOn chemDivSource
Function.uncurry coupledChemDivSourceLift ContinuousOn
chemDivSource_joint
jointContinuous chemDivSource
```

### What exists

Several structures and residual bundles carry **per-slice** continuity assumptions such as:

```lean
∀ᶠ s in 𝓝 τ,
  ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)
```

Examples:

```text
ShenWork/PDE/IntervalChemDivOuterCommuteProducer.lean
ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
ShenWork/Paper2/IntervalChemDivWinDischarge.lean
```

These are not uncurried joint-continuity producers.  They either consume the field or include it in an `other`/residual package.

### Useful but not joint source continuity

```text
ShenWork/PDE/IntervalChemDivFluxFACSourceDecay.lean
```

has:

```lean
def chemDivSource_weakH2_of_spatialC2
    (hC2 : ContDiffOn ℝ 2 (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1))
    ... :
    IntervalWeakH2Neumann (coupledChemDivSourceLift p u s)
```

and:

```lean
theorem coupledChemDivSource_zeroCoeff_of_uniformSup
    (hcont : ∀ s, 0 ≤ s →
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1))
    (hsup : ∀ s, 0 ≤ s → ∀ x ∈ Icc (0 : ℝ) 1,
      |coupledChemDivSourceLift p u s x| ≤ Msup) :
    ∀ s, 0 ≤ s →
      |cosineCoeffs (coupledChemDivSourceLift p u s) 0| ≤ 2 * max B Msup
```

Again, this is per-slice continuity/sup-boundedness, not `ContinuousOn (Function.uncurry source)`.

## 2. Joint continuity result for the heat semigroup cosine series

There **is** a heat-series joint-continuity proof pattern, but it is private to EWA joint-regularity files, not exported as a public heat semigroup theorem.

### Global/non-windowed EWA file

```text
ShenWork/Wiener/EWA/SourceJointRegularity.lean
```

has a private theorem:

```lean
private theorem heatValueSeries_jointContinuousOn (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0) :
    ContinuousOn
      (fun q : ℝ × ℝ =>
        ∑' n, Real.exp (-q.1 * unitIntervalCosineEigenvalue n) *
          u₀cos n * cosineMode n q.2)
      (Ioi (0 : ℝ) ×ˢ univ)
```

It proves joint continuity by `continuousOn_tsum` on local boxes `Ioo c (p.1+1) ×ˢ univ`, using the heat-trace majorant

```lean
unitIntervalCosineHeatTrace_single_exp_summable hc
```

and the per-mode continuity of

```lean
(t,x) ↦ exp(-t λ_n) * u₀cos n * cosineMode n x.
```

The same file also has a private time-derivative heat-leg theorem:

```lean
private theorem heatDerivSeries_jointContinuousOn ... :
  ContinuousOn
    (fun q : ℝ × ℝ =>
      ∑' n, -(unitIntervalCosineEigenvalue n) *
        Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n q.2)
    (Ioi (0 : ℝ) ×ˢ univ)
```

### Windowed EWA file

```text
ShenWork/Wiener/EWA/SourceJointRegularityOn.lean
```

reproduces those private heat-leg helpers because the original ones are private:

```lean
private theorem heatValueSeries_jointContinuousOn' ...
private theorem heatDerivSeries_jointContinuousOn' ...
```

The file comments explicitly say:

```text
The heat leg depends only on the initial data bound ... so we reproduce the heat-leg helpers here (they are private in the original).
```

### What this means for the level-0 heat source

For the heat semigroup representative

```lean
fun q : ℝ × ℝ =>
  ∑' k,
    Real.exp (-q.1 * unitIntervalCosineEigenvalue k) * heatCoeff u₀ k * cosineMode k q.2
```

the needed proof pattern already exists.  But because the theorem is `private`, you cannot call it directly outside the file.  You would either refactor/export it or copy the `continuousOn_tsum` local-box proof.

### Heat-slice representation exists separately

```text
ShenWork/Paper2/IntervalPicardIterateRepresentation.lean
```

has the level-0 agreement theorem:

```lean
theorem hagree_zero
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {σ M₀ : ℝ} (hσ : 0 < σ)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ 0 σ))
      (fun x => ∑' k, iterateReprCoeff p u₀ 0 σ k * cosineMode k x)
      (Set.Icc (0 : ℝ) 1)
```

This gives agreement of the physical heat slice with the cosine representative on `[0,1]`, but it is not itself a joint-continuity theorem.

## 3. `BoundedWeightJointSeries` / joint-continuity tools

Yes: the repo has a substantial bounded-weight joint-series API, mainly for the resolver.

```text
ShenWork/PDE/IntervalResolverJointC2Physical.lean
```

defines:

```lean
def boundedWeightJointTerm (c : ℕ → ℝ → ℝ) (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => c n q.1 * cosineMode n q.2
```

```lean
def boundedWeightJointMajorant (Bt : ℕ → ℕ → ℝ) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * Bt i n * valueCosWeight (k - i) n
```

and the key assembler:

```lean
theorem boundedWeightJointSeries_contDiff_two
    {c : ℕ → ℝ → ℝ} {Bt : ℕ → ℕ → ℝ}
    (hc : ∀ n, ContDiff ℝ (2 : ℕ∞) (c n))
    (hBt : ∀ (i n : ℕ) (t : ℝ), i ≤ 2 → ‖iteratedFDeriv ℝ i (c n) t‖ ≤ Bt i n)
    (hsumm : ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant Bt k)) :
    ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' n : ℕ, boundedWeightJointTerm c n q)
```

It also has the gradient analogue:

```lean
theorem boundedWeightJointGradSeries_contDiff_two ... :
    ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' n : ℕ, boundedWeightJointGradTerm c n q)
```

The concrete resolver connector is:

```text
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean
```

It uses those assemblers to prove:

```lean
theorem coupledChemical_jointContDiffAt_two
    (H : PhysicalResolverJointC2Data p u Bt) {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2) (s, x)
```

and:

```lean
theorem coupledChemical_grad_jointContDiffAt_two
    (H : PhysicalResolverJointC2Data p u Bt) {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
      (s, x)
```

These are important upstream facts for proving joint regularity of the flux/source, but they do **not** directly give a closed-slab `ContinuousOn` theorem for the chemDiv source.

## Related EWA joint-continuity infrastructure

The EWA source-form solution has public joint-continuity theorems, but these are for the **solution synthesis** and its time/spatial derivative series, not directly for `coupledChemDivSourceLift`.

```text
ShenWork/Wiener/EWA/SourceJointRegularity.lean
```

exports:

```lean
theorem fullSourceCoeff_jointSolutionClosed ... :
  ContinuousOn
    (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
      ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x))
    (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1)
```

and:

```lean
theorem fullSourceCoeffDot_jointTimeDerivClosed ... :
  ContinuousOn
    (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
      ∑' n, fullSourceCoeffDot p u u₀cos t n * cosineMode n x))
    (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1)
```

```text
ShenWork/Wiener/EWA/SourceSpatialJointRegularity.lean
```

exports spatial-derivative joint continuity of the source-form solution synthesis:

```lean
theorem fullSourceCoeff_jointGradClosed ... :
  ContinuousOn (Function.uncurry (fun t x =>
    deriv (fun y => ∑' n,
      fullSourceCoeff p u u₀cos t n * cosineMode n y) x))
    (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1)
```

and:

```lean
theorem fullSourceCoeff_jointGrad2Closed ...
```

These show the general method for joint spatial regularity of cosine synthesis, but they are not a heat-level chemDiv-source composition theorem.

## Practical conclusion

For the requested heat-semigroup chemDiv source on `[c,T]×[0,1]`, the repo currently seems to have the **components**, not the final packaged theorem:

1. heat cosine series joint-continuity proof pattern via private `heatValueSeries_jointContinuousOn` / `heatValueSeries_jointContinuousOn'`;
2. resolver value/gradient joint `C²` via `boundedWeightJointSeries_contDiff_two` and `boundedWeightJointGradSeries_contDiff_two`;
3. flux/source per-slice regularity infrastructure (`chemDivSource_weakH2_of_spatialC2`, `IntervalChemDivSpatialC2.lean`);
4. an explicit level-0 `sorry` block saying the missing work is to wire heat semigroup smoothness + resolver smoothness + chemDiv composition into joint continuity and compact sup bounds.

So the answer to the main question is:

```text
No, I did not find an existing theorem directly proving ContinuousOn of the uncurried heat-level chemDiv source on [c,T]×[0,1].
```

The closest reusable pieces are the private heat-series joint-continuity lemmas and the bounded-weight resolver joint-`C²` assemblers.
