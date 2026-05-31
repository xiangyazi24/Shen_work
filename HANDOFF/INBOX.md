# Shen_work — Current Task

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd ~/repos/shen_work && lake env lean ShenWork/Paper2/IntervalMildPicard.lean
cd ~/repos/shen_work && lake build
```

Invariant: BUILD OK. IntervalMildPicard.lean has 4 sorry (all pure real analysis).

## Task: Close 4 sorry in IntervalMildPicard.lean

File: `ShenWork/Paper2/IntervalMildPicard.lean`

### Context

T7 Atom E/F is set up as Picard iteration → IntervalMildSolution.
The approach bypasses Q2 (joint continuity / BCF) entirely.

Already proved:
- `picardIter`: Picard iteration definition
- `real_cauchySeq_of_geometric_bound`: |a_{n+1}-a_n| ≤ K^n·C₀ → Cauchy
- `picardIter_pointwise_convergent`: Picard iterates converge at each (t,x)
- `picardLimit`: the pointwise limit trajectory
- `geometric_tail_tendsto_zero`: K^n·C₀/(1-K) → 0
- `picardIter_uniform_convergence`: geometric tail → uniform convergence
  (PROVED, assuming `picardIter_pointwise_tail_bound`)

### 4 sorry to close (priority order)

#### 1. `picardIter_pointwise_tail_bound` (line ~96)
Statement: `|u_n(t,x) - u(t,x)| ≤ K^n · C₀ / (1 - K)`
This is the standard geometric series tail bound. Proof sketch:
- `|u_n(t,x) - u(t,x)| ≤ ∑_{k≥n} |u_{k+1}(t,x) - u_k(t,x)| ≤ ∑_{k≥n} K^k · C₀ = K^n · C₀ / (1-K)`
- Uses `tsum_geometric_of_lt_one` and telescoping
- The limit is `atTop.limUnder (fun n => picardIter ...)` so need to connect it to the Cauchy limit

#### 2. `picardLimit_bounded` (line ~130)
Statement: `|picardLimit p u₀ T t x| ≤ M`
Proof: pointwise limit of M-bounded functions. Use `le_of_tendsto` from Mathlib.

#### 3. `picardLimit_is_mildSolution` (line ~142)
Statement: `IntervalMildSolution p T u₀ (picardLimit p u₀ T)`
Key proof:
```
|Φ(u₀,u)(t,x) - u(t,x)|
  ≤ |Φ(u₀,u) - Φ(u₀,u_n)| + |u_{n+1} - u|
  ≤ K · sup|u - u_n| + |u_{n+1}(t,x) - u(t,x)|
  → 0 as n → ∞
```
Uses: `hcontract` (contraction on any two bounded trajectories), `picardLimit_bounded`,
`picardIter_uniform_convergence`

#### 4. `intervalMildSolution_exists_picard` (line ~172)
Statement: main theorem
Assembly: choose T from `exists_small_contraction_time`, M from `hu₀_bounded`,
prove the geometric bound by induction on n, prove ball membership by induction,
instantiate the contraction from `contraction_pointwise` in IntervalMildExistence.lean,
apply `picardLimit_is_mildSolution`.

### Also in the repo

`IntervalMildExistence.lean` has the BCF approach (2 sorry: Q2 + main theorem).
The Picard approach in `IntervalMildPicard.lean` is strictly better — it avoids Q2.
Once the 4 sorry above are closed, `IntervalMildExistence.lean` can be cleaned up.

### Constraints

- 0 sorry in all files EXCEPT IntervalMildPicard.lean and IntervalMildExistence.lean
- BUILD OK (8387 jobs)
- Run `grep -rn "\bsorry\b" ShenWork --include="*.lean"` after edits
