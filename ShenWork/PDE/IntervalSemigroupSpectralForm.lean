/-
# Kernel ↔ spectral form of the unit-interval Neumann heat semigroup

This file analyses the bridge between the two representations of the Neumann
heat propagator on `[0,1]`:

* the **kernel form**
  `intervalSemigroupOperator 1 t f x = ∫_{[0,1]} K t x y * f y`
  with
  `K t x y = normalizedZerothReflectionKernel 1 t x y
           = (1/2) (G_t(x - y) + G_t(x + y))`,
  `G_t` the standard Gaussian heat kernel (`heatKernel`);

* the **spectral form**
  `unitIntervalCosineHeatValue t a x = ∑' n, e^{-t (nπ)²} cos(nπ x) * a n`.

## Honest mathematical status (read this first)

The classical identity that underlies the equivalence is **Poisson summation**
(the Jacobi theta transformation): the genuine Neumann heat kernel on `[0,1]`
is the *fully periodised* method-of-images Gaussian

  `K_full t x y = ∑_{k ∈ ℤ} (G_t(x - y + 2k) + G_t(x + y + 2k))`,

and *that* kernel — summed over **all** reflections — is what Poisson summation
turns into the cosine eigenfunction series.

The kernel actually used in `intervalSemigroupOperator` is
`normalizedZerothReflectionKernel`, which by definition keeps **only the two
zeroth-order image terms** `(1/2)(G_t(x-y) + G_t(x+y))` and drops the lattice
sum `∑_{k≠0}`.  Therefore the literal pointwise identity

  `intervalSemigroupOperator 1 t f x = unitIntervalCosineHeatValue t a x`

is **false in general**: the two-term kernel is the small-`t` truncation of the
true Neumann kernel, not its exact value.  (Equality would require either the
full image sum, or the boundary terms to vanish, which they do not for fixed
`t > 0`.)

What *is* true and *is* the analytic heart of the matter is the
single–Poisson-summation theta identity.  We prove its cleanest fully real
instance below (the `x = 0` diagonal of the period-`1` periodised heat kernel),
directly from Mathlib's `Real.tsum_exp_neg_mul_int_sq`.  This is the exact
lemma that, applied at a complex shift, yields the general kernel↔spectral
bridge.

## Precise reduction of the remaining gap

To upgrade the proved diagonal identity to the full
`K_full t x y = cosine series` bridge one needs, beyond what is below:

1. A repo definition of the *full* image kernel `K_full` (currently absent —
   only the two-term `normalizedZerothReflectionKernel` exists).  Without it
   the target identity in the task statement cannot even be stated truthfully.

2. The **shifted** Poisson summation lemma
   `Complex.tsum_exp_neg_quadratic`
   (`Mathlib/Analysis/SpecialFunctions/Gaussian/PoissonSummation.lean`),
   used at shift `b = x / (something)` and its real part taken, to handle
   `x ≠ 0`.  Mathlib **does** provide this lemma; no Mathlib gap here.

3. Termwise interchange of `∑_{k∈ℤ}` (image sum) and `∫_{[0,1]}` (the operator
   integral) plus folding `∑_{n∈ℤ}` over the period-`1` torus into the
   `∑_{n≥0}` Neumann cosine sum (the `cos((2πn)x)` ↔ `cos((nπ)x)` reindexing
   coming from the even reflection in `CosineParsevalBridge`).

So the bridge does **not** bottom out at a missing Mathlib lemma: the only
genuinely missing piece is repo-side (the full image kernel `K_full` and the
termwise/reindexing bookkeeping (1) & (3)).  The deep analytic input (2) is
already in Mathlib.
-/

import ShenWork.PDE.IntervalDomain
import ShenWork.PDE.HeatSemigroup
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

open MeasureTheory

noncomputable section

namespace ShenWork.IntervalSemigroupSpectralForm

open scoped Real
open ShenWork.IntervalDomain

/-- The Gaussian heat kernel summed over the integer lattice equals the
spectral (dual) Gaussian series.  This is the Poisson–summation / Jacobi-theta
transformation specialised to the heat-kernel normalisation, in its cleanest
fully real form (the `x = 0` diagonal of the period-`1` periodised kernel).

Concretely, with `G_t(z) = (1/√(4πt)) exp(-z²/(4t))`:

  `∑_{n∈ℤ} G_t(n) = ∑_{n∈ℤ} exp(-t (2πn)²)`.

The right-hand side is exactly the spectral side: `exp(-t (2πn)²)` are the
heat multipliers `exp(-t λ_n)` for the period-`1` torus eigenvalues
`λ_n = (2πn)²`, which fold (via even reflection) onto the Neumann eigenvalues
`(nπ)²` of `unitIntervalCosineEigenvalue`.  This is the real analytic core of
the kernel↔spectral identity. -/
theorem heatKernel_lattice_poisson (t : ℝ) (ht : 0 < t) :
    (∑' n : ℤ, heatKernel t (n : ℝ)) =
      ∑' n : ℤ, Real.exp (-t * (2 * Real.pi * (n : ℝ)) ^ 2) := by
  -- Set `a = 1/(4πt)` so that `-π a n² = -n²/(4t)`, matching `heatKernel`.
  set a : ℝ := 1 / (4 * Real.pi * t) with ha_def
  have hpit : 0 < 4 * Real.pi * t := by positivity
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  -- Poisson summation from Mathlib (Gaussian, integer lattice).
  have hpoisson := Real.tsum_exp_neg_mul_int_sq ha_pos
  -- Rewrite the LHS `heatKernel t n` as `(1/√(4πt)) * exp(-π a n²)`.
  have hLHS : (∑' n : ℤ, heatKernel t (n : ℝ)) =
      (1 / Real.sqrt (4 * Real.pi * t)) *
        ∑' n : ℤ, Real.exp (-Real.pi * a * (n : ℝ) ^ 2) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    unfold heatKernel
    congr 1
    rw [ha_def]
    field_simp
  -- Rewrite the dual side `exp(-π/a n²)` as `exp(-t (2πn)²)`.
  have hdual : ∀ n : ℤ,
      Real.exp (-Real.pi / a * (n : ℝ) ^ 2) =
        Real.exp (-t * (2 * Real.pi * (n : ℝ)) ^ 2) := by
    intro n
    congr 1
    rw [ha_def]
    field_simp
    ring
  -- The prefactor `(1/√(4πt)) * (1/a^(1/2))` collapses to `1`.
  have hprefactor : (1 / Real.sqrt (4 * Real.pi * t)) *
      ((1 : ℝ) / a ^ (1 / 2 : ℝ)) = 1 := by
    have harpow : a ^ (1 / 2 : ℝ) = Real.sqrt a := (Real.sqrt_eq_rpow a).symm
    rw [harpow, ha_def]
    rw [show (1 : ℝ) / (4 * Real.pi * t) = (4 * Real.pi * t)⁻¹ by ring]
    rw [Real.sqrt_inv]
    have hsqrt_pos : 0 < Real.sqrt (4 * Real.pi * t) := Real.sqrt_pos.mpr hpit
    field_simp
  -- Assemble.
  rw [hLHS, hpoisson, ← mul_assoc, hprefactor, one_mul]
  exact tsum_congr hdual

/-!
## Statement of the (false-as-literal) target, recorded honestly

We do **not** state `intervalSemigroupOperator 1 t f x =
unitIntervalCosineHeatValue t a x` as a theorem, because — per the file header —
it is false for the two-term `normalizedZerothReflectionKernel`.  The honest
content delivered here is `heatKernel_lattice_poisson`: the genuine Poisson /
theta identity for the (full, period-`1`) periodised Gaussian on its diagonal,
proved with no `sorry`, no `admit`, no custom axiom.

The one piece needed downstream — recognising `intervalSemigroupOperator 1 t f`
as `unitIntervalCosineHeatValue t a` with `a` bounded by `‖f‖` — requires first
replacing `normalizedZerothReflectionKernel` by the full image kernel `K_full`
(repo gap), then the shifted form `Complex.tsum_exp_neg_quadratic` (present in
Mathlib) and the even-reflection reindexing in `CosineParsevalBridge`.
-/

end ShenWork.IntervalSemigroupSpectralForm
