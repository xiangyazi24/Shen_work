# ANALYSIS: structural audit of positive-time H¹ regularity

Repo: `xiangyazi24/Shen_work`  
Audited HEAD: `62e95422495ba646da2b9eccfdead03370a40a1a`

## Verdict

**Use option (i): add one bundle-level positive-time spatial H¹ field for**

```lean
u = conjugatePicardLimit p u₀ DB.T
```

This is a sound, satisfiable input. It is **not circular with `hF1` / quantitative classical local existence**, provided its producer is the mild-solution parabolic-smoothing / coefficient-bootstrap route and does **not** call the later `IsPaper2ClassicalSolution` result produced by the deepest bundle.

The regularity is analytically available from the already-constructed mild fixed point: the Picard data first give a bounded, nonnegative, continuous-slice mild trajectory; boundedness and continuity give the `H^0 = L²` coefficient seed; the parabolic Duhamel/H^σ engine then upgrades positive-time slices. This is weaker and earlier than classical local existence, so it should sit upstream of the weak negative-part identities.

## Why this is not circular

The current deepest structure carries `DB : ConjugateMildExistenceData p u₀`, `DT`, `Hbridge`, `HmildWeakRegular`, and `Henergy`, but it does **not** carry spatial Sobolev regularity of the mild solution. The `localClassicalSolution` theorem is produced only after those carried hypotheses are supplied. Therefore, proving H¹ by appealing to `localClassicalSolution` would be circular; proving it from `DB` and the mild equation is not.

Concrete tree anchors:

* `PositiveDatumBFormSqDeepestHypotheses` carries `DB`, `DT`, `Hbridge`, `Test`, `HmildWeakRegular`, and `Henergy`, but no field of the form `u(t) ∈ H¹` (`IntervalBFormPositiveDatumLocalExistenceSqDeepest.lean:37-57`).
* `localClassicalSolution` is downstream of the deepest bundle and constructs the classical solution only after `H.directFrontier`, strict positivity, PDE, and Neumann data are available (`IntervalBFormPositiveDatumLocalExistenceSqDeepest.lean:25-58` in the local theorem block).
* `ConjugateMildExistenceData` is only the mild/Picard data; the packaged data obtained from it exposes `hbound`, `hnonneg`, `hcont`, and `hmeas` for `conjugatePicardLimit`, before classicality (`IntervalConjugatePicard.lean:157-170`, `:520-548`).

So the dependency order should be:

```text
DB / mild fixed point
  -> bounded + nonnegative + continuous slices
  -> H⁰ seed + source envelopes
  -> positive-time H¹ smoothing
  -> admissibility of φ = -u_-(t) as an H¹ test
  -> weak identity fields / negative-part energy
  -> localClassicalSolution
```

not:

```text
localClassicalSolution -> H¹ -> weak identities -> localClassicalSolution
```

## (a) Analytic availability for this system

Yes. For this one-dimensional interval system, the singular chemotaxis term is in divergence/B-form mild form, but it is still handled by heat smoothing once the flux slice is bounded/L²:

```text
Q(u) = u · v_x · (1 + v)^(-β)
```

The mild Picard data provide bounded, nonnegative, continuous slices. The resolver-gradient machinery bounds `v_x`, and positivity of the resolver keeps `(1+v)^(-β)` controlled. Thus `Q(u(t))` is bounded, hence L² on `[0,1]`, on each positive-time slice and uniformly on local windows.

The tree already contains the needed ingredients:

* `chemFluxLifted_sup_bound_of_ball` gives a uniform flux bound from bounded, nonnegative, continuous slices; it relies on `resolverGrad_sup_le_of_bounded` (`IntervalConjugateChemFluxIntegrable.lean:54-64`, resolver-gradient call inside that proof).
* `NeumannHeatGradientTMinusHalfBound` has been corrected to require `MemLp f 2`, exactly the right non-vacuous form for gradient smoothing (`IntervalBFormCron2SemigroupWeakDuhamel.lean:22-30` in the definition block).
* The H^σ scale is coefficient-based: `MemHSigma σ a` is summability of `(1+λ_k)^σ a_k²` (`IntervalHSigmaScale.lean:32-39`).

Therefore the mild solution has the standard positive-time smoothing route. No classical PDE identity is needed to state or prove the H¹ input.

## (b) Is the repo's H^σ bootstrap the right mechanism?

Yes, with one important qualification: use the bootstrap as a **producer of the H¹ field**, not as a theorem that has already been fully specialized to `conjugatePicardLimit` in the deepest bundle.

The usable mechanism is already present:

* `memHSigma_zero_of_continuousOn` proves the `H^0` seed from continuity on `[0,1]` (`IntervalChiNegCloseBaseSeed.lean:54-77`).
* `conjugatePicardLimit_hasContinuousSlices` gives the continuity of the mild-limit slices from uniform convergence of Picard iterates (`IntervalConjugatePicard.lean:157-170`).
* `duhamelEnergy_mode_endpoint_uniform` and `duhamelEnergy_endpoint_uniform` give endpoint-uniform parabolic gain (`IntervalUniformBootstrap.lean:98-142`).
* `UniformBootstrapStep` abstracts the per-level map `MemHSigma σ -> MemHSigma (σ+α)`, and `gradientSolution_contDiffOn_two_FINAL` shows how repeated steps reach high regularity (`IntervalUniformBootstrap.lean:174-207`).
* The latest mixed-product file supplies the direct sine-envelope route for the flux: `fluxSineEnvelope_uniform` produces the `hg`/`hg_dom` pair consumed by the bootstrap step, and the verdict says the mixed/signed structure adds no new obstruction (`IntervalMixedProduct.lean:69-86`, `:115-128`).

For the current structural fix, one does **not** need to reach `ContDiffOn ℝ 2`; reaching `MemHSigma 1` is enough for the weak test issue. So the right producer is a smaller specialization of the existing ladder:

```text
continuous slice -> MemHSigma 0
UniformBootstrapStep^n with σ₀ + nα ≥ 1
-> MemHSigma 1 or stronger
```

The input `MemHSigma 0` is available without circularity because it comes from the mild-solution slice continuity, not from classical regularity.

## (c) Concrete fix

Add exactly one regularity field to the deepest bundle, or to the sub-bundle that constructs `NegativePartStandardHeatSemigroupDuhamelFacts`, and derive the negative-part test admissibility from it.

Minimal field shape:

```lean
/-- Positive-time spatial H¹ regularity of the named mild solution.
This is upstream of the weak negative-part identities and must be produced from
DB + the mild equation + the H^σ bootstrap, not from `localClassicalSolution`. -/
u_posTime_memHSigma_one :
  ∀ t, 0 < t → t ≤ DB.T →
    ShenWork.Paper2.HSigmaScale.MemHSigma 1
      (ShenWork.IntervalNeumannFullKernel.cosineCoeffs
        (ShenWork.IntervalDomain.intervalDomainLift
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ DB.T) t)))
```

Recommended immediate derived lemma/consumer shape:

```lean
/-- H¹ admissibility of the negative-part test derived from the H¹ slice.
The proof is the standard Lipschitz Sobolev chain rule for `negativePart`, plus
`negativePartTest u t = -negativePartLift (u t)`. -/
negativePartTest_H1_of_u_posTime_memHSigma_one :
  (∀ t, 0 < t → t ≤ DB.T →
    ShenWork.Paper2.HSigmaScale.MemHSigma 1
      (ShenWork.IntervalNeumannFullKernel.cosineCoeffs
        (ShenWork.IntervalDomain.intervalDomainLift
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ DB.T) t)))) →
  ∀ t, 0 < t → t ≤ DB.T,
    NegativePartTestAdmissibleH1
      (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ DB.T) t
```

`NegativePartTestAdmissibleH1` can be a local predicate matching the exact hypotheses needed by `semigroup_form_identity`, source Duhamel weak differentiation, and chemotaxis Duhamel weak differentiation. The key is that its producer should be the single H¹ field above, not repeated ad hoc regularity assumptions in each weak-identity field.

## Campaign guidance

Do **not** redesign the whole deepest-bundle architecture. The architecture is under-hypothesized, not vacuous. The correct repair is to make the missing positive-time Sobolev regularity explicit once, discharge it from the mild bootstrap, and have all weak-identity producers consume that field.

Do **not** prove the field from the final classical solution. That would be circular. The producer must use only:

* `DB` / `conjugateMildSolutionData_of_data DB` mild fixed-point data;
* base `H^0` from slice continuity;
* bounded flux/logistic source estimates;
* `fluxSineEnvelope_uniform` and the H^σ Duhamel gain engine.

That route is the standard parabolic smoothing route for the mild solution and is independent of `hF1`.
