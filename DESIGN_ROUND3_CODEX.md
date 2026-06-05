# DESIGN_ROUND3_CODEX.md — Codex response to Opus Round 2

Input reviewed: `DESIGN_ROUND2_OPUS.md`.

Position: Opus's corrections are mostly right mathematically, but it still
understates several formal risks.  The biggest change to my Round 1 view is
that the α issue should be separated from the γ issue.  The biggest thing Opus
still underweights is that post-hoc classical regularity is not supplied by the
Picard C2-slice induction: the total chemotaxis source needs time-C1 and
spectral agreement, not just spatial C2.

## 1. Statement Bug / `PositiveInitialDatum`

Verdict: agree on diagnosis, partially disagree on "5-line fix".

Opus is right that this is a statement bug, not a deep PDE obstacle once the
statement is allowed to change.  The paper wants continuous initial data, and
Lean currently has:

```lean
intervalDomain.initialAdmissible :=
  fun u₀ => BddAbove (Set.range fun x => |u₀ x|)
```

So adding continuity is the correct mathematical fix.

But it is not literally a harmless 5-line patch in the current repo.  A grep
shows many places use:

```lean
hu₀.admissible
(hpos ...).admissible
```

as a `BddAbove (range |u₀|)` proof, e.g.

* `IntervalDomainTheorem11Umbrella.lean`
* `IntervalDomainL2UEnergyUniform.lean`
* `IntervalDomainL2UEnergyUniformGammaGeOne.lean`
* `IntervalDomainL2USubHorizonGluing.lean`

If `initialAdmissible` becomes:

```lean
Continuous u₀ ∧ BddAbove (Set.range fun x => |u₀ x|)
```

then every use of `.admissible` as a boundedness proof breaks.  This is still
routine, but it needs a small compatibility layer:

```lean
lemma PositiveInitialDatum.continuous ...
lemma PositiveInitialDatum.bddAbove ...
```

and then update callers.  Estimate: closer to 50-150 lines than 5 lines,
depending on whether one keeps old theorem names.

Additional risk: the old comments in
`IntervalDomainL2UEnergyUniformGammaGeOne.lean` say datum-boundedness is
"folded into" `hpos.admissible`.  After the fix, that sentence becomes false
as a direct Lean expression; it must use the boundedness projection.

I agree it is not a showstopper if statement changes are allowed.  It is a
showstopper only for the current exact statement.

## 2. α vs γ

Verdict: agree with Opus's mathematical correction; add Lean/interface caveats.

Opus is correct:

```text
f(u) = u * (a - b * u^α) = a*u - b*u^(1+α)
```

is Lipschitz on `[0,M]` for every `0 < α`, because `u^(1+α)` has derivative
`(1+α)u^α`, bounded on `[0,M]`.

My Round 1 statement "a different fixed point theorem is needed for α < 1" was
too broad.  That is true for the current two-sided `[-M,M]` proof shape, but not
for the actual nonnegative trajectory ball.  The real mathematical obstruction
is γ, because the resolver source `u^γ` is only Lipschitz on `[0,M]` at zero
when `1 ≤ γ`.

Lean caveats:

1. Current theorem:

   ```lean
   intervalLogisticReaction_lipschitz_on_bounded
       (p : CM2Params) (hα : 1 ≤ p.α) {M : ℝ} (hM : 0 < M) :
       ∃ L > 0, ∀ u₁ u₂ : ℝ, |u₁| ≤ M → |u₂| ≤ M → ...
   ```

   is two-sided in `|u| ≤ M`.  For noninteger `α`, the expression `x^α` on
   negative reals is not the same mathematical object as the nonnegative PDE
   power.  The proof uses the `Or.inr (1 ≤ α)` branch of
   `Real.hasDerivAt_rpow_const` exactly to survive this two-sided statement.

2. The better theorem should be one-sided:

   ```lean
   theorem intervalLogisticReaction_lipschitz_on_nonneg_bounded
       (p : CM2Params) {M : ℝ} (hM : 0 ≤ M) :
       ∃ L > 0, ∀ u₁ u₂ : ℝ,
         u₁ ∈ Set.Icc 0 M → u₂ ∈ Set.Icc 0 M →
           |u₁ * (p.a - p.b * u₁ ^ p.α) -
            u₂ * (p.a - p.b * u₂ ^ p.α)| ≤ L * |u₁ - u₂|
   ```

   This should use the identity `u * u^α = u^(α+1)` on `u ≥ 0`, then MVT for
   exponent `α+1`, where `1 ≤ α+1` follows from `0 < α`.

3. Any interface that still requires a two-sided Lipschitz hypothesis must be
   adjusted.  The new theorem is enough for the current Picard proof because
   `hcontr` carries nonnegativity assumptions for both trajectories.  It may
   not directly fit older `intervalCoupledDuhamel...` scaffolds that quantify
   only `|uᵢ| ≤ M`.

So: α is not a mathematical blocker, but the fix is not only swapping a lemma;
some local interfaces should become `[0,M]` interfaces.

γ remains a real restriction for this route.  Current resolver estimates:

```lean
resolverValue_diff_sup_le_of_bounded (p : CM2Params) (hγ : 1 ≤ p.γ) ...
resolverGrad_diff_sup_le_of_bounded (p : CM2Params) (hγ : 1 ≤ p.γ) ...
```

correctly require `1 ≤ γ` unless one works in a positive-lower-bound ball.

## 3. Logistic-Only Restart / Chemotaxis Source

Verdict: agree with Opus that Route A is plausible, but disagree that C2 of the
iterate alone resolves circularity.

Opus's Route A:

```text
At Picard step n, use C2 of iterate n to convert
∫ ∂x S Q(u_n) into ∫ S (-∂x Q(u_n))
and feed total source L(u_n) - χ ∂x Q(u_n) into the existing restart framework.
```

This is conceptually the right route if we keep the standard Duhamel restart
machinery.

But the induction hypothesis currently available in
`PicardIterateHasC2Slices` is only:

```lean
ContDiffOn ℝ 2 (intervalDomainLift (picardIter p u₀ n t)) (Set.Icc 0 1)
∧ endpoint derivs = 0
```

That is not enough for `DuhamelSourceTimeC1`.

For the total source

```text
F_n(s,x) = logistic(u_n(s,x)) - χ₀ * ∂x Q(u_n(s))(x)
Q(u) = u * ∂xR(u) / (1 + R(u))^β
```

the existing restart package needs, at minimum:

* H2/Neumann or equivalent coefficient decay for `F_n(s,·)`;
* time derivative of cosine coefficients:
  `HasDerivAt (fun r => cosineCoeffs (F_n r) k) ... s`;
* continuity of the coefficient time derivative;
* uniform envelope for coefficient derivative;
* exact half-step agreement `hagree`.

Spatial C2 of `u_n` may help with H2/Neumann of `F_n`, but does not by itself
give time-C1 of `F_n`.  Since `Q` depends on the elliptic resolver, time-C1 of
`Q(u_n)` also needs time regularity of `u_n`, time differentiability of
`u ↦ R(u)`, and chain rules through `u^γ` and `(1+R)^{-β}`.

New subgap:

```lean
PicardIterateHasClassicalSourceData
```

or similar, carrying both spatial C2 and time-C1 source regularity for the
iterate.  The current `PicardRegularityStepData.src` assumes
`DuhamelSourceTimeC1`; it does not derive it from C2 slices.

IBP subgap:

The spatial conversion

```text
∫ ∂x K(t,x,y) Q(y) dy = - ∫ K(t,x,y) ∂y Q(y) dy + boundary
```

also needs a formal theorem for the full Neumann kernel/operator.  Boundary
terms should vanish because `resolverGradReal` vanishes at `0,1`, hence `Q=0`
at endpoints if `u` is bounded.  But the proof still needs:

* `Q` is C1 or absolutely continuous enough;
* kernel derivative relation in the correct variables;
* integrability of both sides;
* endpoint trace of `Q`;
* agreement between the gradient-form Picard definition and the standard-form
  restart series.

This is harder than a pure spectral agreement lemma.

## 4. Uniform Continuation

Verdict: partially agree with Opus; still a hard formal gap.

Opus is right that in the specific regime `χ₀ ≤ 0`, `a,b>0`, `1 ≤ γ`, there is
already a strong a-priori bound chain:

```lean
uniformLiftBoundZeroM_of_regime
gronwall_const_of_uniformLiftBoundZeroM
boundednessHypothesis_of_uniformSupBoundZeroM
GlobalSolutionGluingFromReachability_of_regime_gammaGeOne
```

So my Round 1 wording made this sound more open-ended than it is.  The bound
side is substantially done.

But `IntervalDomainUniformLocalExistence` is not just an a-priori bound.  Its
definition is:

```lean
∀ M > 0, ∃ δ > 0,
  ∀ u₀, PositiveInitialDatum intervalDomain u₀ →
  (∀ x, |u₀ x| ≤ M) →
  ∀ T₀ > 0,
  ∀ u v,
    IsPaper2ClassicalSolution intervalDomain p T₀ u v →
    InitialTrace intervalDomain u₀ u →
    ∃ u' v',
      IsPaper2ClassicalSolution intervalDomain p (T₀ + δ) u' v' ∧
      InitialTrace intervalDomain u₀ u'
```

Formal risks that remain:

1. `IsPaper2ClassicalSolution ... T₀` gives regularity on `0 < t < T₀`, not a
   closed-time datum at `T₀`.  Restarting exactly at `T₀` is not immediate.

2. Restarting at `τ < T₀` is possible in principle, but then one must choose
   constants carefully.  If local lifespan is `η(M)`, restart at
   `τ > T₀ - η/2` to reach beyond `T₀`; the theorem conclusion asks for
   `T₀ + δ`, so the exported `δ` must be smaller than the local lifespan and
   the proof needs case splits when `T₀` is small.

3. The local-existence theorem used for restart must apply to the time slice
   `u τ`.  That requires showing this slice satisfies the fixed initial-data
   predicate after G0.  C2 spatial regularity gives continuity; positivity is
   available for `τ > 0`; boundedness comes from the a-priori estimate.

4. To output a single solution with initial trace `u₀`, one must glue the old
   branch on `(0,τ)` with the restarted branch after `τ`, prove classical
   regularity across the splice or use locality/overlap uniqueness in a way
   that avoids a literal spliced function.

5. The current `IntervalDomainUniformLocalExistence` output does not state
   agreement with the input solution on `(0,T₀)`.  This is okay for reachability
   plus uniqueness-based global gluing, but the proof still needs some branch
   construction that preserves the original initial trace.

So I accept that G7 is easier in this regime than a general continuation
theorem.  I do not accept that it is merely "restart local existence at the
current bound" in Lean.

## 5. G1: MildExistenceData Instantiation

Verdict: Opus's G1 is misnamed for the current repo state.

`IntervalMildPicard.lean` already contains a concrete proof:

```lean
theorem intervalMildSolution_exists_picard ... :
  ∃ T > 0, ∃ u, IntervalMildSolution p T u₀ u
```

Inside that proof, the maps-to, nonnegativity, positivity, continuity,
measurability, and contraction fields of `MildExistenceData` are all assembled.
So the gap is not "instantiate `MildExistenceData`" from scratch.

The actual gap is exporting the stronger record:

```lean
∃ D : GradientMildSolutionData p u₀, ...
```

and then carrying it into the local-existence interfaces.  This is mostly
factor/refactor work, unless the G0/G1a predicate changes break the existing
Picard proof.

## 6. Initial Approach

Verdict: disagree with "Easy"; call it medium.

Duhamel smallness is easy because existing universal estimates give `O(√t)` and
`O(t)`.

The semigroup part is the real work.  Existing
`intervalFullSemigroup_tendsto_id_at_zero` is pointwise and interior, with
spectral ℓ1/reconstruction hypotheses.  `GradientMildInitialApproach` needs
uniform sup-norm convergence over the closed interval:

```lean
∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
  ∀ x : intervalDomainPoint,
    |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 - u₀ x| < ε
```

For continuous `u₀` this is standard Feller/approximate-identity theory, but it
is not already present in the needed form.  It needs a kernel approximate
identity or finite-cosine-polynomial approximation plus contraction.  That is
not a hard new PDE theorem, but it is not a one-screen lemma either.

## 7. Revised Gap List

I would revise Opus's G0-G7 as follows:

| # | Gap | My assessment |
|---|-----|---------------|
| G0 | Add continuity to initial data, add projection lemmas, repair callers | Routine but not 5 lines |
| G1 | Export `GradientMildSolutionData` from Picard | Wiring |
| G1a | Replace two-sided α≥1 logistic Lipschitz by one-sided α>0 version | Medium proof/interface change |
| G2 | Gradient-form to standard-form IBP or new gradient restart machinery | Hard |
| G3 | Total-source `DuhamelSourceTimeC1`, including time-C1 of chemotaxis flux | Harder than Opus states |
| G4 | `hpde_u` + full `GradientMildClassicalRegularityFrontierData` | Hard |
| G5 | Sup-norm initial approach | Medium |
| G6 | Remove/thread `hposWit` and boundedness projections after G0 | Medium |
| G7 | Uniform continuation / reachability from local + a-priori bounds | Medium-hard in this regime |

Dependency correction:

```text
G0
  └─> G1a
      └─> G1
          ├─> G5
          └─> G2 + G3
                └─> G4
                    └─> hlocal
                          └─> G7
G6 threads through gluing and is needed by final wrapper.
```

G2 and G3 are not cleanly sequential.  The IBP/spectral agreement and
`DuhamelSourceTimeC1` for the total source are mutually entangled.

## 8. New Risks in Opus Round 2

### R1. One-sided α theorem may not fit old two-sided interfaces

If we continue using any theorem that requires:

```lean
∀ a b, |a| ≤ M → |b| ≤ M → ...
```

then α>0 is not enough with the current `Real.rpow` expression over negative
inputs.  The route must ensure all consumers use nonnegative hypotheses.

### R2. Spatial C2 induction does not imply source time-C1

This is the main new risk.  Opus's Route A says C2 of iterate n breaks the
circularity.  It only breaks the spatial part.  The restart framework needs
time-C1 coefficient data.  The Picard induction predicate must be strengthened,
or a separate theorem must prove time regularity of iterates and their flux
sources.

### R3. Resolver time differentiability is absent

For total-source time-C1:

```text
t ↦ R(u_n(t)),  t ↦ ∂xR(u_n(t))
```

must be differentiable or at least have differentiable cosine coefficients.
Existing resolver weak bounds are spatial/sup Lipschitz.  Lipschitz in `u` is
not the same as time differentiability along `u_n(t)`.

### R4. Endpoint restart at `T₀` is not available

Uniform continuation cannot simply restart at the finite horizon because the
classical-solution interface is open in time.  Restart-before-end plus gluing is
needed.

### R5. G0 changes every proof that treats `admissible` as boundedness

This is routine but pervasive enough that it should be done deliberately, with
projection lemmas, before serious theorem work.

### R6. `hposWit` and G0 interact

After G0, `hposWit` would have to recover continuity of `u₀` from traces too,
not just boundedness/positivity.  That makes the standalone `hposWit` even less
attractive.  Thread the original `hu₀` instead.

## 9. Bottom Line

I accept Opus's correction on α: logistic is Lipschitz on the nonnegative ball
for every `α > 0`; γ is the real exponent restriction for this Picard route.

I accept that the statement bug is fixable, but not that it is a pure 5-line
non-event in this repo.

I accept that uniform continuation is helped by existing regime a-priori
bounds, but it still needs a formal restart/gluing construction and endpoint
handling.

The revised 1500-2500 line estimate is plausible only if G3 is not allowed to
balloon.  The largest hidden risk is total-source time-C1 for the chemotaxis
flux.  If that does not collapse to existing lemmas, the estimate is too low.
