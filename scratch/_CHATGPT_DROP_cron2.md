# Q781 (cron2) — Final session status update

Static status note / handoff only; I did not run a Lean build in this final write.

## Complete sorry landscape

Current remaining proof obligations are concentrated in three places:

```text
HeatRegularity file: 2 sorry
  1. cutoff derivative bound
  2. heat term derivative bound

Level0 file: 10 sub-sorry
  1A
  2A-core
  2A-agree
  3A–3G

Tower file: 5 sorry
  all downstream of Level0 / HeatRegularity closure
```

The session reduced the original coarse landscape of 11 sorry into a well-decomposed architecture with named local targets and clear downstream dependencies.

## Key infrastructure already proven with 0 sorry

The following infrastructure is available/proven and should be treated as the stable base for the next pass:

```text
✓ Quartic decay + eigenvalue L¹ summability
✓ Resolver global positivity
✓ Source eigenvalue summability
    full chain: H2 certs + quartic decay + eigenvalue sum
✓ Heat cutoff approach
    smoothRightCutoff + contDiff_tsum + eventual eq
✓ Leibniz decomposition
    norm_iteratedFDeriv_mul_le applied
```

These remove the main analytic/summability uncertainty. The remaining tasks are local proof assembly, bridge instantiation, and derivative-bound packaging.

## Existing tools identified for Level0 sub-sorry

Use the following already-existing tools for the 3C–3G segment:

```text
3C:
  coupledChemical_jointContDiffAt_two
  needs PhysicalResolverJointC2Data

3D:
  coupledChemical_grad_jointContDiffAt_two
  needs PhysicalResolverJointC2Data

3F:
  coupledChemDivFlux_timeBridge_of_physicalJointC2

3G:
  chemDivMixedTimeDeriv_jointContinuousOn_closed
  needs ChemDivMixedTimeDerivClosedRepr
```

Also available for time-branch splitting:

```text
heatKernel_of_nonpos → S(t) = 0 for t ≤ 0
```

Earlier inspection found the operator-level nonpositive-time semigroup proof already present privately in `IntervalMildPicard.lean`:

```lean
private theorem intervalFullSemigroupOperator_eq_zero_of_nonpos
    {t : ℝ} (ht : t ≤ 0) (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator t f x = 0 := ...
```

If this is needed outside that file, promote/copy it into the full-kernel namespace as a public theorem.

## Suggested next proof order

1. **Promote nonpositive semigroup lemma** if Level0 needs it across files:

```lean
intervalNeumannFullKernel_of_nonpos
intervalFullSemigroupOperator_eq_zero_of_nonpos
```

This handles all `τ ≤ 0` branches by reducing the heat term to zero.

2. **Close HeatRegularity’s two local derivative bounds**:

```text
cutoff derivative bound
heat term derivative bound
```

The cutoff route is already structurally available via `smoothRightCutoff`, `ContDiff`, and eventual equality. The heat term branch should use the nonpositive-time zero lemma plus the positive-time heat regularity path.

3. **Instantiate `PhysicalResolverJointC2Data`** for Level0 3C/3D.

Once this data object is available, the existing joint-C² lemmas should discharge the coupled-chemical value and gradient regularity subgoals.

4. **Use 3F bridge directly**:

```lean
coupledChemDivFlux_timeBridge_of_physicalJointC2
```

This should connect the physical joint-C² data to the desired time-bridge statement.

5. **Close 3G by producing `ChemDivMixedTimeDerivClosedRepr`** and then applying:

```lean
chemDivMixedTimeDeriv_jointContinuousOn_closed
```

6. **Only after Level0 and HeatRegularity close, clear the Tower file**.

The five Tower sorry are downstream; they should be attacked last to avoid reworking assumptions and bridge signatures.

## Final handoff summary

The main proof architecture is now clear:

```text
analytic summability / positivity / cutoff infrastructure: done
Leibniz decomposition: done
nonpositive heat branch: available, needs public packaging if cross-file
HeatRegularity: 2 local derivative bounds remain
Level0: 10 decomposed sub-sorry remain, with tools identified for 3C–3G
Tower: 5 downstream sorry remain
```

The next productive session should focus on turning the identified existing tools into the exact data records/closed representations expected by Level0, rather than searching for new analytic facts.
