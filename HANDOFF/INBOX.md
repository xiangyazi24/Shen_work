# Shen_work — Current Task

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd ~/repos/shen_work && lake build
```

Invariant: BUILD OK (8387 jobs). 1 sorry in IntervalMildPicard.lean.

## Task: Close intervalMildSolution_exists_picard

File: `ShenWork/Paper2/IntervalMildPicard.lean` (line ~364)

### What is proved (0 sorry)

The entire Picard fixed-point theory is done:

```
MildExistenceData → picardIter_ball → picardIter_geometric →
  cauchySeq → pointwise_convergent → tail_bound →
  uniform_convergence → bounded → is_mildSolution →
  intervalMildSolution_of_data
```

All 0 sorry. The conditional theorem `intervalMildSolution_of_data` says:
given suitable constants satisfying MapsTo + contraction + ball bounds,
a mild solution exists.

### What remains (1 sorry)

`intervalMildSolution_exists_picard`: construct `MildExistenceData p u₀`.

Concretely, need to provide:
1. **T** — from `exists_small_contraction_time` (already proved)
2. **M** — from `hu₀_bounded` (e.g., 2B + 1)
3. **K** — contraction constant K(T) = 2|χ₀|·C_grad·C_Q·√T + C_L·T
4. **C₀** — initial correction bound
5. **hbase_ball** — |S(t)u₀(x)| ≤ M (semigroup contraction)
6. **hmapsTo** — from `mapsTo_mildBall` (IntervalMildExistence.lean, proved)
7. **hcontr** — from `contraction_pointwise` (IntervalMildExistence.lean, proved)
8. **hbase_diff** — |Φ(u₀, S·u₀) - S·u₀| ≤ C₀

The HARD part is discharging the integrability/measurability hypotheses
that `gradDuhamel_sup_bound` / `valueDuhamel_sup_bound` /
`gradDuhamel_diff_sup_bound` / `valueDuhamel_diff_sup_bound` require:
- `∀ s, Integrable (q s) (intervalMeasure 1)` — flux slice integrable
- `IntervalIntegrable (fun s => deriv (S(t-s) q(s)) x) volume 0 t`
- `IntervalIntegrable (fun s => S(t-s) r(s) x) volume 0 t`
- Per-(s,z) kernel integrability and spatial differentiability

These are all "bounded on finite measure → integrable" but need
measurability of the resolver, flux, logistic compositions.

### Strategy

1. Prove a generic "bounded measurable source → Duhamel integrable" lemma
2. Prove chemFluxLifted and logisticLifted are bounded measurable for
   bounded trajectories (from existing resolver bounds)
3. Instantiate MildExistenceData with these

### Constraints

- 0 sorry in all files EXCEPT IntervalMildPicard.lean (1 sorry)
- IntervalMildExistence.lean has 2 sorry (Q2 + main) — superseded by Picard approach
- BUILD OK (8387 jobs)
