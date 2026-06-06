# Phase-0 / M2-uniform spec: iterate C² explicit-bound induction step (χ₀=0)

Target file (NEW, sole writer): ShenWork/Paper2/IntervalPicardIterateC2Bound.lean

## Goal
From M1's landed restart representation (ShenWork/Paper2/
IntervalPicardIterateRestart.lean: picardIterateRestart_cosineIdentity, read
it first) + the quantitative atoms, derive EXPLICIT spatial bounds for the
NEXT iterate slice: under M1's hypotheses (H1)(H2)(H3) at level n, with the
source envelope |a_k(σ)| ≤ Benv/((k:ℝ)*π)^2 (k ≥ 1) and |a_0(σ)| ≤ Benv0 and
half-step coefficient bound |cosineCoeffs(lift(u_{n+1}(t/2))) k| ≤ M₁:

 (i)  sup_{x∈[0,1]} |∂ₓ lift(u_{n+1}(t)) x| ≤
        M₁·sqrtEigExpWeight(t/2) + C₁·Benv      (τ-free Duhamel G1 bound)
 (ii) sup_{x∈[0,1]} |∂ₓ² lift(u_{n+1}(t)) x| ≤
        M₁·eigExpWeight(t/2) + C₂·(t/2)^{1/4}·Benv + (zeroth-mode term)
 with C₁, C₂ the explicit constants of
 ShenWork.IntervalDuhamelQuantGain (duhamelSpectralCoeff_sqrtEigenvalue_tsum_bound,
 duhamelSpectralCoeff_eigenvalue_tsum_tauQuarter_bound) and
 sqrtEigExpWeight/eigExpWeight from ShenWork.IntervalHomogeneousQuantBound.

Route: the restart series' termwise first/second spatial derivatives are
∓(kπ)·sin/(kπ)²·cos times the coefficients; the sup of the derivative series
is ≤ the (√λ / λ)-weighted coefficient ℓ¹ sums, which are EXACTLY what
M-gate-1 + M-gate-2 bound. The termwise-differentiation justification should
REUSE the existing C² series machinery (restartDuhamelCoeffSeries_contDiff_two
/ restartDuhamelFormula_closedC2_of_timeC1_source in
ShenWork/Paper2/IntervalMildRegularityBootstrap.lean and the underlying
cosineCoeffSeries machinery in ShenWork/PDE/IntervalCosineSliceRegularity.lean
or IntervalDuhamelClosedC2.lean — read them; if they expose the derivative
SERIES form, the sup bound is a tsum-triangle-inequality exercise).
If the existing machinery only gives qualitative C² without exposing the
derivative series, prove the quantitative deriv-bound lemma for an abstract
ℓ¹-weighted cosine series first (it is reusable), then apply.

## Constraints
Identical to previous specs (new file only; no lake build; scp+lake env lean
loop on uisai1; explicit constants, no existentials; named satisfiable
hypotheses if needed; commit ONLY your file:
"Phase-0 M2-uniform: explicit C2 bounds for next iterate from restart series",
push with the untracked-copy dance).
