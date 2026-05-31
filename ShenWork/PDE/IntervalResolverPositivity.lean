/-
  ShenWork/PDE/IntervalResolverPositivity.lean

  T7 existence — **O1: resolver positivity** `R(u) ≥ 0` for `u ≥ 0`, the only
  obstruction left for the weak mild fixed point (the flux denominator
  `(1+R)^β ≥ 1` and the `hv_nonneg` conjunct both need it).  It is NOT reachable
  via the elliptic maximum principle for weak ball elements (the `R''` /
  elliptic-identity tools all need `SourceCoeffQuadraticDecay` = source `C²`,
  which an ℓ²-only weak element lacks).  Route: the positivity-preserving
  heat-Laplace representation
  `R(u) = ∫₀^∞ e^{−μt} S(t)(ν u^γ) dt` via a FINITE truncation `R_T` + a
  spectral T→∞ limit + the closed cone `Ici 0`.

  **Route correction (vs the original O1 sketch):** the sketch used the
  zeroth-reflection `intervalSemigroupOperator`, but that two-term kernel is only
  a small-`t` TRUNCATION of the Neumann kernel — it does NOT have the cosine
  spectral form `∑ e^{−tλₖ} âₖ cos` (see `IntervalSemigroupSpectralForm` header),
  so its per-mode Laplace coefficients would NOT match the resolver
  `âₖ/(μ+λₖ)`.  The correct operator is the FULL Neumann propagator
  `intervalFullSemigroupOperator`, which has BOTH: nonnegativity
  (`intervalNeumannFullKernel_nonneg`) AND the cosine spectral identity
  (`intervalFullSemigroupOperator_eq_cosineHeatValue`).

  This file starts with the full-propagator positivity (O1a).

  No `sorry`, no `admit`, no custom `axiom`.  We never assume
  `SourceCoeffQuadraticDecay` / `R''` / `chemDiv` in the weak ball.
-/
import ShenWork.PDE.IntervalFullKernelSupBound

open MeasureTheory
open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalNeumannFullKernel

noncomputable section

namespace ShenWork.IntervalResolverPositivity

/-- **O1a — full Neumann propagator preserves positivity.**  `S(t)f ≥ 0` for
`f ≥ 0` (`t > 0`): the full Neumann kernel is nonnegative
(`intervalNeumannFullKernel_nonneg`), so the kernel integral of a nonnegative
source is nonnegative.  (Full-kernel analogue of the zeroth-reflection
`intervalSemigroupOperator_nonneg`.) -/
theorem intervalFullSemigroupOperator_nonneg {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : ∀ y, 0 ≤ f y) (x : ℝ) :
    0 ≤ intervalFullSemigroupOperator t f x := by
  unfold intervalFullSemigroupOperator
  apply integral_nonneg
  intro y
  exact mul_nonneg (intervalNeumannFullKernel_nonneg ht x y) (hf y)

end ShenWork.IntervalResolverPositivity
