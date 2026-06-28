# Q1665 (cron3): IBP

## Status

I could not read the local prompt file through the GitHub connector. I searched the repository for `q_cron3_ibp` and found no match. The repository-side IBP material is in:

```text
ShenWork/PDE/IntervalDuhamelClosedC2.lean
```

## Answer

The IBP step is already proved. Use:

```lean
duhamelCoeff_eigenvalue_mul
```

This is the scalar coefficient identity for the Duhamel term. It takes:

```lean
hda       : ∀ s, HasDerivAt a (adot s) s
hadotcont : Continuous adot
```

and proves the integration-by-parts formula for the kernel `Real.exp (-(t - s) * lam)`.

The proof differentiates:

```lean
fun s => a s * Real.exp (-(t - s) * lam)
```

then applies:

```lean
intervalIntegral.integral_eq_sub_of_hasDerivAt
```

and rearranges the two resulting integrals.

## Dependency chain

For weighted Duhamel coefficient summability, the intended theorem is:

```lean
duhamelSpectralCoeff_eigenvalue_summable
```

It applies `duhamelCoeff_eigenvalue_mul` mode-by-mode with:

```lean
lam  := unitIntervalCosineEigenvalue n
a    := fun s => a s n
adot := fun s => src.adot s n
```

The required hypothesis is:

```lean
src : DuhamelSourceTimeC1 a
```

The final closed-C2 consumer is:

```lean
intervalDuhamelTerm_closedC2_of_timeC1_source
```

So the route is:

```text
DuhamelSourceTimeC1 a
  -> duhamelCoeff_eigenvalue_mul
  -> duhamelSpectralCoeff_eigenvalue_summable
  -> intervalDuhamelTerm_closedC2_of_timeC1_source
```

## Minimal check block

```lean
import ShenWork.PDE.IntervalDuhamelClosedC2

open MeasureTheory Filter Topology
open ShenWork.IntervalDuhamelClosedC2

#check duhamelCoeff_eigenvalue_mul
#check duhamelSpectralCoeff_eigenvalue_summable
#check intervalDuhamelTerm_closedC2_of_timeC1_source
```

## Bottom line

Do not reprove the IBP algebra in downstream files. It is landed. The real remaining task is to construct the relevant `DuhamelSourceTimeC1` package for the concrete coefficient family.
