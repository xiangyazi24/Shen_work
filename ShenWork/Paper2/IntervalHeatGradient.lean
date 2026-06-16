/-
  ShenWork/Paper2/IntervalHeatGradient.lean

  **Paper2 Theorem 1.1 (χ₀ < 0 local existence) — Brick 1: the interval-Neumann
  heat-gradient smoothing bound.**

  TARGET (the contraction-facing shape):

    `|∂ₓ S(t) g (x)| ≤ C∇ · t^(−1/2) · ‖g‖∞`,   uniformly in `x`,

  for the interval-Neumann heat semigroup `S(t)` on `[0,1]` and bounded
  measurable data `g` (`|g| ≤ Cg`), with `C∇ = 1/√π`.  Here `S(t) = `
  `intervalFullSemigroupOperator t` is the genuine method-of-images Neumann
  propagator

    `S(t) g (x) = ∫₀¹ K(t,x,y) g(y) dy`,
    `K(t,x,y) = Σ_{k∈ℤ} [ p_t(x−y+2k) + p_t(x+y+2k) ]`   (reflected images),

  on the non-degenerate domain `Ω = [0,1]`.

  This `L∞ → L∞`, `t^(−1/2)` (NOT spectral `t^(−1)`) gradient-smoothing estimate
  is the brick that gives `∫₀ᵗ (t−s)^(−1/2) ds = 2√t → 0`, hence the short-time
  mild-solution contraction for the divergence-form chemotaxis Duhamel term.

  ## Status / provenance

  The estimate is already proved CLEAN (no `sorry`/`admit`/`axiom`/`native_decide`)
  in the committed PDE layer, via the **Gaussian-kernel `L¹` route** — the route
  that yields the clean `t^(−1/2)` rather than the spectral `t^(−1)`:

    * `intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t`
        (`ShenWork/PDE/IntervalFullKernelGradientLinfty.lean`, Step 6.6):
      pointwise `t^(−1/2)` gradient bound, built from the `L¹` tiling bound
      `∫₀¹ |∂ₓ K(t,x,y)| dy ≤ (1/√π) t^(−1/2)`
      (`intervalNeumannFullKernel_deriv_abs_interval_integral_le`) composed with
      differentiation-under-the-integral (`…_hasDerivAt_fst`).

    * `ShenWork.IntervalGradDuhamelBound.gradDuhamel_sup_bound`
        (`ShenWork/PDE/IntervalGradDuhamelBound.lean`, Atom D):
      integrates the per-slice bound against `∫₀ᵗ (t−s)^(−1/2) ds = 2√t`, giving
      the short-time gradient-Duhamel contraction `≤ C∇ · 2√T · Cq`.

    * `…gradDuhamel_diff_sup_bound`: the difference / Lipschitz form
      `≤ C∇ · 2√T · D` (semigroup linearity in the source).

  This file is the **named Paper2 brick surface**: it re-exports those committed
  clean theorems under the names the χ₀<0 local-existence consumer
  (`chemMildLocal` / `…orderBox_exists` chain) reads, in the `L∞→L∞` sup shape,
  and records the `2√t → 0` contraction consequence.  It introduces NO new
  hypotheses and NO new axioms: it is a definitional re-statement of the
  committed bricks.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.PDE.IntervalFullKernelGradientLinfty
import ShenWork.PDE.IntervalGradDuhamelBound

open MeasureTheory
open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.HeatKernelGradientEstimates (heatGradientLinftyLinftyConstant
  heatGradientLinftyLinftyConstant_nonneg)

namespace ShenWork.Paper2

/-- The interval-Neumann heat semigroup `S(t)` on `[0,1]`: the method-of-images
Neumann propagator `S(t) g (x) = ∫₀¹ K(t,x,y) g(y) dy`.  An abbreviation for the
committed full propagator `intervalFullSemigroupOperator`, exposed under the
`S`-name the Paper2 mild-solution / contraction layer uses. -/
noncomputable abbrev intervalNeumannHeatSemigroup (t : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t g x

/-- The interval-Neumann heat-gradient smoothing constant `C∇ = 1/√π`. -/
noncomputable abbrev gradSmoothingConst : ℝ := heatGradientLinftyLinftyConstant

theorem gradSmoothingConst_nonneg : 0 ≤ gradSmoothingConst :=
  heatGradientLinftyLinftyConstant_nonneg

/-- **Brick 1 — interval-Neumann heat-gradient smoothing bound (`L∞ → L∞`,
`t^(−1/2)`).**

For `t > 0` and bounded measurable data `g` (`|g| ≤ Cg`), the spatial gradient of
the Neumann heat semigroup obeys, **uniformly in `x`**,

  `|∂ₓ S(t) g (x)| ≤ C∇ · t^(−1/2) · Cg`,   `C∇ = 1/√π`.

Taking `Cg = ‖g‖∞` this is exactly the sup-norm smoothing estimate
`‖∂ₓ S(t) g‖∞ ≤ C∇ · t^(−1/2) · ‖g‖∞`.  Proved CLEAN via the Gaussian-kernel `L¹`
route (giving the genuine `t^(−1/2)`); re-exported here from the committed
`intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t`. -/
theorem intervalNeumann_heat_gradient_bound {t : ℝ} (ht : 0 < t)
    {g : ℝ → ℝ} (hg_meas : AEStronglyMeasurable g (intervalMeasure 1))
    {Cg : ℝ} (hg : ∀ y, |g y| ≤ Cg) (x : ℝ) :
    |deriv (fun z : ℝ => intervalNeumannHeatSemigroup t g z) x|
      ≤ gradSmoothingConst * t ^ (-(1 / 2) : ℝ) * Cg :=
  ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t
    ht hg_meas hg x

/-- **Brick 1, sup-norm packaging.**  The bound `|∂ₓ S(t) g (x)| ≤ C∇ t^(−1/2) Cg`
holds for EVERY `x`, i.e. it is uniform in `x` — the `‖∂ₓ S(t) g‖∞`-shape the
contraction consumes.  (Stated as the explicit `∀ x` quantification so the
consumer can take it as the sup-norm bound directly.) -/
theorem intervalNeumann_heat_gradient_bound_uniform {t : ℝ} (ht : 0 < t)
    {g : ℝ → ℝ} (hg_meas : AEStronglyMeasurable g (intervalMeasure 1))
    {Cg : ℝ} (hg : ∀ y, |g y| ≤ Cg) :
    ∀ x, |deriv (fun z : ℝ => intervalNeumannHeatSemigroup t g z) x|
      ≤ gradSmoothingConst * t ^ (-(1 / 2) : ℝ) * Cg :=
  fun x => intervalNeumann_heat_gradient_bound ht hg_meas hg x

/-- **Brick 1 consequence — short-time gradient-Duhamel contraction (`2√t → 0`).**

The gradient-Duhamel integral of the chemotaxis source `q` (bounded by `Cq`)
satisfies, for `0 < t ≤ T`,

  `|∫₀ᵗ ∂ₓ S(t−s) q(s) (x) ds| ≤ C∇ · 2√T · Cq`,

with the factor `2√T` coming from `∫₀ᵗ (t−s)^(−1/2) ds = 2√t ≤ 2√T → 0`, which is
the smallness driving the short-time mild-solution contraction.  Re-exported from
the committed `gradDuhamel_sup_bound`. -/
theorem intervalNeumann_gradDuhamel_contraction
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) {q : ℝ → ℝ → ℝ}
    (hq_int : ∀ s, Integrable (q s) (intervalMeasure 1))
    {Cq : ℝ} (hCq : 0 ≤ Cq) (hq_sup : ∀ s y, |q s y| ≤ Cq) (x : ℝ)
    (hg_int : IntervalIntegrable
      (fun s : ℝ => deriv
        (fun z : ℝ => intervalNeumannHeatSemigroup (t - s) (q s) z) x) volume 0 t) :
    |∫ s in (0:ℝ)..t, deriv
        (fun z : ℝ => intervalNeumannHeatSemigroup (t - s) (q s) z) x|
      ≤ gradSmoothingConst * (2 * Real.sqrt T) * Cq :=
  ShenWork.IntervalGradDuhamelBound.gradDuhamel_sup_bound ht htT hq_int hCq hq_sup x hg_int

/-- **Brick 1 consequence — gradient-Duhamel difference Lipschitz.**  By semigroup
linearity in the source, the difference of two gradient-Duhamel images obeys

  `|∫₀ᵗ (∂ₓ S(t−s) q₁ − ∂ₓ S(t−s) q₂)(x) ds| ≤ C∇ · 2√T · D`   when `|q₁ − q₂| ≤ D`,

the Lipschitz estimate that closes the contraction-map fixed point.  Re-exported
from the committed `gradDuhamel_diff_sup_bound`. -/
theorem intervalNeumann_gradDuhamel_diff_contraction
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) {q₁ q₂ : ℝ → ℝ → ℝ}
    {D : ℝ} (hD : 0 ≤ D) (hq_diff : ∀ s y, |q₁ s y - q₂ s y| ≤ D)
    (hq_int_diff : ∀ s, Integrable (fun y => q₁ s y - q₂ s y) (intervalMeasure 1))
    (x : ℝ)
    (hKq₁ : ∀ s z, Integrable
      (fun y => ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel (t - s) z y * q₁ s y)
        (intervalMeasure 1))
    (hKq₂ : ∀ s z, Integrable
      (fun y => ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel (t - s) z y * q₂ s y)
        (intervalMeasure 1))
    (hd₁ : ∀ s, 0 ≤ s → s < t →
      DifferentiableAt ℝ (fun z => intervalNeumannHeatSemigroup (t - s) (q₁ s) z) x)
    (hd₂ : ∀ s, 0 ≤ s → s < t →
      DifferentiableAt ℝ (fun z => intervalNeumannHeatSemigroup (t - s) (q₂ s) z) x)
    (hg_int : IntervalIntegrable
      (fun s : ℝ => deriv
        (fun z : ℝ => intervalNeumannHeatSemigroup (t - s) (fun y => q₁ s y - q₂ s y) z) x)
      volume 0 t) :
    |∫ s in (0:ℝ)..t,
        (deriv (fun z : ℝ => intervalNeumannHeatSemigroup (t - s) (q₁ s) z) x
          - deriv (fun z : ℝ => intervalNeumannHeatSemigroup (t - s) (q₂ s) z) x)|
      ≤ gradSmoothingConst * (2 * Real.sqrt T) * D :=
  ShenWork.IntervalGradDuhamelBound.gradDuhamel_diff_sup_bound ht htT hD hq_diff
    hq_int_diff x hKq₁ hKq₂ hd₁ hd₂ hg_int

end ShenWork.Paper2
