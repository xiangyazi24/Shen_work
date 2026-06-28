# Q1650 (cron3): summability note

## Status

The prompt only exposed a local path, `/tmp/q_cron3_summable.txt`. That path is not a GitHub repository path, and I followed the delivery rule not to use the sandbox or local filesystem. A GitHub repository search for the literal name `q_cron3_summable` returned no matches.

I therefore inspected the relevant repository-side summability file found by searching for `summable`:

```text
ShenWork/Paper2/IntervalChiNegGradSummable.lean
```

That file is on `main`; the `chatgpt-scratch` branch is being used only for this requested drop file.

## Repository-grounded answer

The per-slice gradient summability result is already organized in `IntervalChiNegGradSummable.lean` as four theorems:

```lean
gradSummable_heat
gradSummable_duhamel
gradSummable_slice
gradSummable_slice_consumes
```

The intended consumer-facing theorem is:

```lean
ShenWork.Paper2.IntervalChiNegGradSummable.gradSummable_slice_consumes
```

It proves the downstream hypothesis shape

```lean
Summable (fun n : ℕ =>
  unitIntervalCosineEigenvalue n *
    |cosineCoeffs (intervalDomainLift (u τ)) n|)
```

from the fixed-time assumptions:

```lean
hτ      : 0 < τ
hM0     : ∀ k, |uhat0 k| ≤ M₀
srcChem : DuhamelSourceTimeC1
  (fun s n => Real.sqrt (lam n) * sineCoeffs (conjQ p u s) n)
srcLog  : DuhamelSourceTimeC1
  (fun s n => Real.sqrt (lam n) * conjFl p u n s)
hdecomp : ∀ k, cosineCoeffs (intervalDomainLift (u τ)) k = ...
```

So if a later file is stuck on this summability hypothesis, the intended shape is:

```lean
exact ShenWork.Paper2.IntervalChiNegGradSummable.gradSummable_slice_consumes
  hτ hM0 srcChem srcLog hdecomp
```

If the goal is written with `lam` instead of `unitIntervalCosineEigenvalue`, use `gradSummable_slice` directly, or close the definitional mismatch with `rfl` / `simpa` after unfolding the local notation.

## Why this is the right route

The heat leg is easy. For fixed `τ > 0`, the exponential factor `Real.exp (-(τ * lam k))` beats the eigenvalue weight `lam k`. In Lean this is packaged by:

```lean
heatCoeff_eigenvalue_summable
```

and wrapped by:

```lean
gradSummable_heat
```

The Duhamel leg is the genuine point. It is not proved from the mild decomposition alone. It uses the time-integration-by-parts theorem:

```lean
duhamelSpectralCoeff_eigenvalue_summable
```

through the bridge:

```lean
duhamelEnergyCoeff_eq_duhamelSpectralCoeff_divMode
```

The bridge identifies:

```lean
duhamelEnergyCoeff 1 F τ k
```

with the spectral coefficient for the divergence-weighted source:

```lean
fun s n => Real.sqrt (lam n) * F n s
```

Therefore the real analytic input is the source package:

```lean
DuhamelSourceTimeC1 (fun s n => Real.sqrt (lam n) * F n s)
```

For the slice theorem, there are two such source packages: one for the chemotaxis term and one for the `conjFl` term. Once those packages and the mild decomposition `hdecomp` are supplied, the final assembly is just the triangle inequality plus `Summable.add` and `Summable.mul_left`.

## Minimal import/check block

```lean
import ShenWork.Paper2.IntervalChiNegGradSummable

open MeasureTheory
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (lam)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalDecompTauLift (conjQ conjFl)

#check ShenWork.Paper2.IntervalChiNegGradSummable.gradSummable_heat
#check ShenWork.Paper2.IntervalChiNegGradSummable.gradSummable_duhamel
#check ShenWork.Paper2.IntervalChiNegGradSummable.gradSummable_slice
#check ShenWork.Paper2.IntervalChiNegGradSummable.gradSummable_slice_consumes
```

## Bottom line

Use `gradSummable_slice_consumes` for the downstream reconstruction consumer. The only non-wiring assumptions are the two divergence-weighted `DuhamelSourceTimeC1` source packages and the landed decomposition `hdecomp`. Those are honest analytic inputs, not mechanical simplification obligations.

Because the local prompt file was unavailable through the GitHub connector, I could not verify whether Q1650 asked about a more specific line number or error message.
