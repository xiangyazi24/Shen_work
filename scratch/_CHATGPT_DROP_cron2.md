# Q804 (cron2) — Final handoff priorities for next session

Static repo inspection only; I did not run a Lean build.

## Short answer

Your priority order is basically right, with one important refinement:

```text
1. Close HeatRegularity completely.
2. Wire the heat semigroup joint-C² theorem into Level0 3B.
3. Build the physical resolver/source C² data once, then use it to close 3C/3D/3F/3G.
```

The better phrasing for item 3 is: **do not attack 3C, 3D, 3F, 3G separately**.  Build the one physical data package that the existing lemmas consume, then apply the existing downstream tools.

## Priority 1 — Close the last HeatRegularity sorry

Current main has already closed the old cutoff-derivative-bound sorry.  The remaining heat regularity obstruction is now the heat-term factor bound:

```lean
private theorem heatTerm_iteratedFDeriv_global_bound
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {c : ℝ} (_hc : 0 < c) (j n : ℕ) (q : ℝ × ℝ)
    (hj : (j : ℕ∞) ≤ 2)
    (hq : c / 2 ≤ q.1) :
    ‖iteratedFDeriv ℝ j (heatTerm u₀ n) q‖ ≤
      (1 + unitIntervalCosineEigenvalue n) ^ j * M₀ *
        Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n) := by
  sorry
```

This statement is still too sharp as written.  The Leibniz expansion gives a finite binomial constant:

```text
∑ i≤j C(j,i) · (1+λ)^i · (1+λ)^(j-i)
  = 2^j · (1+λ)^j
```

So the robust fix is to change the bound to include `2 ^ j`, or fold that finite constant into `cutoffHeatMajorant`.

Recommended patch shape:

```lean
‖iteratedFDeriv ℝ j (heatTerm u₀ n) q‖ ≤
  (2 : ℝ) ^ j * ((1 + unitIntervalCosineEigenvalue n) ^ j * M₀ *
    Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n))
```

or define a small finite constant:

```lean
heatTermLeibnizConstant j := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)
```

and use that instead of simplifying to `2 ^ j`.

This is the highest-priority item because `heatSemigroup_jointContDiffAt_two` depends on the `contDiff_tsum` majorant.  Once this is axiom-clean, Level0 can cite heat joint regularity instead of carrying local analytic sorries.

## Priority 2 — Wire `heatSemigroup_jointContDiffAt_two` into Level0 3B

After Priority 1, the theorem to use is:

```lean
heatSemigroup_jointContDiffAt_two
```

from:

```text
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
```

The goal for Level0 3B should be a small wrapper that says, for `s > 0`, the level-0 profile

```lean
fun q : ℝ × ℝ => intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2
```

is `ContDiffAt ℝ 2` at `(s,x)` on the interior, because level 0 is the heat semigroup cosine series and the heat semigroup series is jointly `C²` for positive time.

This should be mostly wiring:

```text
conjugatePicardIter p u₀ 0 = heat semigroup level
heat semigroup cosine representation agrees on [0,1]
heatSemigroup_jointContDiffAt_two gives joint C² at positive time
```

Do not generalize this too much in the next session.  Just make the exact Level0 sub-sorry compile.  That provides the `u`-side joint-C² input needed by the physical chemDiv/resolver pipeline.

## Priority 3 — Build the physical resolver/source C² data package for the heat semigroup

This is the real gate for the remaining Level0 chain:

```text
3C: coupledChemical_jointContDiffAt_two
3D: coupledChemical_grad_jointContDiffAt_two
3F: coupledChemDivFlux_timeBridge_of_physicalJointC2
3G: chemDivMixedTimeDeriv_jointContinuousOn_closed
```

The existing resolver-side target is in:

```text
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean
```

The key structure is:

```lean
structure PhysicalResolverJointC2Data
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Bt : ℕ → ℕ → ℝ) : Prop where
  coeff_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (resolverTimeCoeff p u k)
  coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤ Bt i k
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant Bt m)
  grad_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant Bt m)
```

Once this exists for

```lean
u := conjugatePicardIter p u₀ 0
```

then the already-proven lemmas become available:

```lean
coupledChemical_jointContDiffAt_two
coupledChemical_grad_jointContDiffAt_two
```

and those feed the existing bridge lemmas for the flux/time-derivative path.

This is the highest-leverage move after 3B.  It is better than proving 3C, 3D, 3F, and 3G independently, because the physical data package is the common missing object.

## Better next-session plan

A concrete next-session order:

```text
A. Patch HeatRegularity bound with a finite Leibniz constant.
   Goal: #print axioms heatSemigroup_jointContDiffAt_two is clean.

B. Add a tiny Level0 wrapper using heatSemigroup_jointContDiffAt_two.
   Goal: close sub-sorry 3B only.

C. Build `PhysicalResolverJointC2Data` for level 0.
   Goal: immediately discharge 3C and 3D via existing lemmas.

D. Use the existing time/flux bridges to close 3F and 3G.
   Goal: finish Level0’s physical chemDiv chain.
```

Do **not** prioritize the Tower file yet.  Q800 showed the Tower still needs extra wrappers and endpoint-extension infrastructure; it should remain downstream until Level0 is clean.

## Verdict

Your proposed order is right, but item 3 should be treated as a single data-construction task:

```text
Build PhysicalResolverJointC2Data / PhysicalSourceTimeC2 for level 0 once,
then apply existing 3C–3G tools.
```

That is the shortest path to turning the current decomposed architecture into a sorry-free Level0 pipeline.
