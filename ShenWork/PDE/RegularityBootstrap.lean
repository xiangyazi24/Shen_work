/-
  ShenWork/PDE/RegularityBootstrap.lean

  Local-existence support lemmas for the interval-domain regularity bootstrap.

  This file stays below `IntervalDomainExistence.lean`: it does not import the
  sb-ode local-existence file, so that file can import these lemmas without a
  cycle.  The proved content here is the heat-smoothing part of the bootstrap:
  interval heat terms are spatially differentiable and their gradients satisfy
  the already established H0.2 `Lp` bounds.

  This file also records the spectral heat-flow `C²` in space / `C¹` in time
  certificate for cosine coefficients.  The remaining nonlinear frontier is
  the upper-endpoint differentiation of the Duhamel time integral and the
  maximum-principle/positivity part of `RegularityBootstrap`; neither is hidden
  as an axiom or a theorem field.
-/
import ShenWork.PDE.HeatKernelGradientEstimates
import ShenWork.PDE.GagliardoNirenberg
import ShenWork.Paper2.Statements

open MeasureTheory Set Filter Topology
open scoped ENNReal Interval

noncomputable section

namespace ShenWork.RegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.HeatKernelGradientEstimates

/-! ## Spatial differentiability of interval heat terms -/

/-- The helper Neumann interval heat operator is spatially differentiable for
positive time and `L¹` interval input.  The derivative is expressed via the
averaged full-line heat representation used in the gradient estimates. -/
theorem intervalSemigroupOperator_hasDerivAt
    {L t x : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure L)) :
    HasDerivAt (fun z : ℝ => intervalSemigroupOperator L t f z)
      ((1 / 2 : ℝ) *
          deriv
            (fun z : ℝ =>
              heatSemigroup t (Set.indicator (intervalSet L) f) z) x -
        (1 / 2 : ℝ) *
          deriv
            (fun z : ℝ =>
              heatSemigroup t (Set.indicator (intervalSet L) f) z) (-x)) x := by
  let g : ℝ → ℝ := Set.indicator (intervalSet L) f
  have hg_int : Integrable g volume :=
    interval_indicator_integrable_of_integrable (L := L) (f := f) hf_int
  have hrepr :
      (fun z : ℝ => intervalSemigroupOperator L t f z) =
        fun z : ℝ =>
          (1 / 2 : ℝ) * heatSemigroup t g z +
            (1 / 2 : ℝ) * heatSemigroup t g (-z) := by
    funext z
    exact intervalSemigroupOperator_eq_half_heatSemigroup_add_reflected
      (L := L) (t := t) ht (f := f) hf_int z
  have hleft :=
    (heatSemigroup_hasDerivAt (f := g) ht x hg_int).const_mul
      (1 / 2 : ℝ)
  have hright :=
    (((heatSemigroup_hasDerivAt (f := g) ht (-x) hg_int).comp x
      (hasDerivAt_neg x)).const_mul (1 / 2 : ℝ))
  have hsum := hleft.add hright
  rw [hrepr]
  convert hsum using 1
  rw [deriv_heatSemigroup (f := g) ht x hg_int,
    deriv_heatSemigroup (f := g) ht (-x) hg_int]
  ring

/-- Spatial differentiability of the interval heat operator, with the
derivative written as Lean's `deriv`. -/
theorem intervalSemigroupOperator_hasDerivAt_deriv
    {L t x : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure L)) :
    HasDerivAt (fun z : ℝ => intervalSemigroupOperator L t f z)
      (deriv (fun z : ℝ => intervalSemigroupOperator L t f z) x) x := by
  have h := intervalSemigroupOperator_hasDerivAt
    (L := L) (t := t) (x := x) ht (f := f) hf_int
  simpa [h.deriv] using h

/-- Unit-interval heat smoothing gives the gradient `Lp → Lq` bound for a
single heat term in the form needed by local-existence bootstrap arguments. -/
theorem intervalHeatTerm_grad_Lp_Lq_bound
    {t p q : ℝ} (ht : 0 < t) (hp : 1 ≤ p) (hq : 0 < q)
    {u : intervalDomain.Point → ℝ}
    (hu_mem :
      MemLp (intervalDomainLift u) (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm
        (fun x : ℝ =>
          deriv
            (fun z : ℝ =>
              intervalSemigroupOperator 1 t (intervalDomainLift u) z) x)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      heatGradientL1LinftyFactor t *
        lpNorm (intervalDomainLift u) (ENNReal.ofReal p)
          (intervalMeasure 1) := by
  exact unitIntervalSemigroupOperator_grad_Lp_Lq_lpNorm_bound
    (t := t) (p := p) (q := q) ht hp hq
    (f := intervalDomainLift u) hu_mem

/-- The same heat-gradient smoothing bound for the Duhamel integrand at a
fixed source time `s`, with the positive heat time `t - s` made explicit. -/
theorem intervalDuhamelIntegrand_grad_Lp_Lq_bound
    {t s p q : ℝ} (hst : s < t) (hp : 1 ≤ p) (hq : 0 < q)
    {F : ℝ → intervalDomain.Point → ℝ}
    (hF_mem :
      MemLp (intervalDomainLift (F s)) (ENNReal.ofReal p)
        (intervalMeasure 1)) :
    lpNorm
        (fun x : ℝ =>
          deriv
            (fun z : ℝ =>
              intervalSemigroupOperator 1 (t - s)
                (intervalDomainLift (F s)) z) x)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      heatGradientL1LinftyFactor (t - s) *
        lpNorm (intervalDomainLift (F s)) (ENNReal.ofReal p)
          (intervalMeasure 1) := by
  exact intervalHeatTerm_grad_Lp_Lq_bound
    (t := t - s) (p := p) (q := q)
    (by linarith) hp hq hF_mem

/-- Spatial differentiability of a Duhamel integrand for positive lag. -/
theorem intervalDuhamelIntegrand_hasDerivAt_deriv
    {t s x : ℝ} (hst : s < t)
    {F : ℝ → intervalDomain.Point → ℝ}
    (hF_int : Integrable (intervalDomainLift (F s)) (intervalMeasure 1)) :
    HasDerivAt
      (fun z : ℝ =>
        intervalSemigroupOperator 1 (t - s)
          (intervalDomainLift (F s)) z)
      (deriv
        (fun z : ℝ =>
          intervalSemigroupOperator 1 (t - s)
            (intervalDomainLift (F s)) z) x) x := by
  exact intervalSemigroupOperator_hasDerivAt_deriv
    (L := 1) (t := t - s) (x := x)
    (by linarith) (f := intervalDomainLift (F s)) hF_int

/-! ## Spectral heat-flow `C²`/`C¹` certificates -/

/-- Pointwise coefficient for the spatial Laplacian/time derivative of the
unit-interval cosine heat flow. -/
def unitIntervalCosineHeatLaplacianPointWeight (t x : ℝ) (n : ℕ) : ℝ :=
  -unitIntervalCosineEigenvalue n *
    unitIntervalCosineHeatPointWeight t x n

/-- Cosine-coefficient model for the spatial Laplacian/time derivative of the
unit-interval heat semigroup value at `x`. -/
def unitIntervalCosineHeatLaplacianValue
    (t : ℝ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, unitIntervalCosineHeatLaplacianPointWeight t x n * a n

/-- Squared coefficient controlling point evaluation of the heat-flow
Laplacian. -/
def unitIntervalCosineHeatLaplacianMultiplier (t : ℝ) (n : ℕ) : ℝ :=
  (unitIntervalCosineEigenvalue n) ^ 2 *
    Real.exp (-2 * t * unitIntervalCosineEigenvalue n)

/-- Heat-flow Laplacian trace for the unit-interval cosine model. -/
def unitIntervalCosineHeatLaplacianTrace (t : ℝ) : ℝ :=
  ∑' n, unitIntervalCosineHeatLaplacianMultiplier t n

/-- The squared pointwise Laplacian weight is bounded by the spectral
Laplacian multiplier. -/
lemma unitIntervalCosineHeatLaplacianPointWeight_sq_le_multiplier
    (t x : ℝ) (n : ℕ) :
    (unitIntervalCosineHeatLaplacianPointWeight t x n) ^ 2 ≤
      unitIntervalCosineHeatLaplacianMultiplier t n := by
  let lambda : ℝ := unitIntervalCosineEigenvalue n
  have hcos : (unitIntervalCosineMode n x) ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]
    exact Real.abs_cos_le_one _
  have hcoeff_nonneg :
      0 ≤ lambda ^ 2 * Real.exp (-2 * t * lambda) := by
    positivity
  calc
    (unitIntervalCosineHeatLaplacianPointWeight t x n) ^ 2
        = lambda ^ 2 * Real.exp (-2 * t * lambda) *
            (unitIntervalCosineMode n x) ^ 2 := by
          dsimp [unitIntervalCosineHeatLaplacianPointWeight,
            unitIntervalCosineHeatPointWeight, lambda]
          have hexp :
              Real.exp (-t * unitIntervalCosineEigenvalue n) ^ 2 =
                Real.exp (-2 * t * unitIntervalCosineEigenvalue n) := by
            rw [sq, ← Real.exp_add]
            congr 1
            ring
          rw [show
              (-unitIntervalCosineEigenvalue n *
                  (Real.exp (-t * unitIntervalCosineEigenvalue n) *
                    unitIntervalCosineMode n x)) ^ 2 =
                unitIntervalCosineEigenvalue n ^ 2 *
                  Real.exp (-t * unitIntervalCosineEigenvalue n) ^ 2 *
                    unitIntervalCosineMode n x ^ 2 by
              ring]
          rw [hexp]
    _ ≤ lambda ^ 2 * Real.exp (-2 * t * lambda) * 1 :=
          mul_le_mul_of_nonneg_left hcos hcoeff_nonneg
    _ = unitIntervalCosineHeatLaplacianMultiplier t n := by
          dsimp [unitIntervalCosineHeatLaplacianMultiplier, lambda]
          ring

/-- Positive-time Laplacian multipliers are dominated by a single-exponential
trace, hence summable. -/
lemma unitIntervalCosineHeatLaplacianMultiplier_le_single_exp_majorant
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    unitIntervalCosineHeatLaplacianMultiplier t n ≤
      (4 / t ^ 2) * Real.exp (-t * unitIntervalCosineEigenvalue n) := by
  let lambda : ℝ := unitIntervalCosineEigenvalue n
  have hlambda : 0 ≤ lambda := by
    dsimp [lambda, unitIntervalCosineEigenvalue]
    positivity
  have hz : 0 ≤ t * lambda := by positivity
  have hgauss : (t * lambda) ^ 2 * Real.exp (-(t * lambda)) ≤ 4 :=
    real_sq_mul_exp_neg_le_four hz
  have hscale_nonneg :
      0 ≤ (1 / t ^ 2) * Real.exp (-(t * lambda)) := by
    positivity
  calc
    unitIntervalCosineHeatLaplacianMultiplier t n
        =
          ((1 / t ^ 2) * Real.exp (-(t * lambda))) *
            ((t * lambda) ^ 2 * Real.exp (-(t * lambda))) := by
          dsimp [unitIntervalCosineHeatLaplacianMultiplier, lambda]
          rw [show
            Real.exp (-2 * t * unitIntervalCosineEigenvalue n) =
              Real.exp (-(t * unitIntervalCosineEigenvalue n)) *
                Real.exp (-(t * unitIntervalCosineEigenvalue n)) by
            rw [← Real.exp_add]
            congr 1
            ring]
          field_simp [ne_of_gt ht]
    _ ≤ ((1 / t ^ 2) * Real.exp (-(t * lambda))) * 4 :=
          mul_le_mul_of_nonneg_left hgauss hscale_nonneg
    _ = (4 / t ^ 2) * Real.exp (-t * unitIntervalCosineEigenvalue n) := by
          dsimp [lambda]
          ring_nf

/-- Summability of the heat-flow Laplacian trace at positive time. -/
lemma unitIntervalCosineHeatLaplacianMultiplier_summable
    {t : ℝ} (ht : 0 < t) :
    Summable fun n => unitIntervalCosineHeatLaplacianMultiplier t n := by
  have hnonneg :
      ∀ n, 0 ≤ unitIntervalCosineHeatLaplacianMultiplier t n := by
    intro n
    dsimp [unitIntervalCosineHeatLaplacianMultiplier,
      unitIntervalCosineEigenvalue]
    positivity
  have hdom :
      ∀ n,
        unitIntervalCosineHeatLaplacianMultiplier t n ≤
          (4 / t ^ 2) * Real.exp (-t * unitIntervalCosineEigenvalue n) :=
    unitIntervalCosineHeatLaplacianMultiplier_le_single_exp_majorant ht
  exact Summable.of_nonneg_of_le hnonneg hdom
    ((unitIntervalCosineHeatTrace_single_exp_summable (t := t) ht).mul_left
      (4 / t ^ 2))

/-- Laplacian multipliers decrease as heat time increases. -/
lemma unitIntervalCosineHeatLaplacianMultiplier_anti_mono_time
    {r τ : ℝ} (hrτ : r ≤ τ) (n : ℕ) :
    unitIntervalCosineHeatLaplacianMultiplier τ n ≤
      unitIntervalCosineHeatLaplacianMultiplier r n := by
  let lambda : ℝ := unitIntervalCosineEigenvalue n
  have hlambda : 0 ≤ lambda := by
    dsimp [lambda, unitIntervalCosineEigenvalue]
    positivity
  have hexp :
      Real.exp (-2 * τ * lambda) ≤ Real.exp (-2 * r * lambda) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact mul_le_mul_of_nonneg_left hexp (sq_nonneg lambda)

/-- Differentiating the first spatial derivative of one heat-weighted cosine
mode gives the Laplacian weight. -/
theorem unitIntervalCosineHeatGradientPointWeight_hasDerivAt_laplacian
    (t : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => unitIntervalCosineHeatGradientPointWeight t y n)
      (unitIntervalCosineHeatLaplacianPointWeight t x n) x := by
  let a : ℝ := (n : ℝ) * Real.pi
  have hsin :
      HasDerivAt (fun y : ℝ => Real.sin (a * y))
        (a * Real.cos (a * x)) x := by
    have h :=
      (Real.hasDerivAt_sin (a * x)).comp x
        ((hasDerivAt_id x).const_mul a)
    convert h using 1
    ring
  have h :=
    hsin.const_mul (Real.exp (-t * unitIntervalCosineEigenvalue n) * (-a))
  convert h using 1
  · ext y
    simp [unitIntervalCosineHeatGradientPointWeight, a]
    ring
  · simp [unitIntervalCosineHeatLaplacianPointWeight,
      unitIntervalCosineHeatPointWeight, unitIntervalCosineMode,
      unitIntervalCosineEigenvalue, a]
    ring

/-- Second-spatial derivative formula for one heat-weighted cosine coefficient. -/
theorem unitIntervalCosineHeatGradientTerm_hasDerivAt_laplacian
    (t : ℝ) (a : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => unitIntervalCosineHeatGradientPointWeight t y n * a n)
      (unitIntervalCosineHeatLaplacianPointWeight t x n * a n) x := by
  simpa [mul_assoc] using
    (unitIntervalCosineHeatGradientPointWeight_hasDerivAt_laplacian
      t n x).mul_const (a n)

/-- Time derivative of one heat-weighted cosine mode equals its Laplacian
weight. -/
theorem unitIntervalCosineHeatPointWeight_hasTimeDerivAt_laplacian
    (t x : ℝ) (n : ℕ) :
    HasDerivAt (fun τ : ℝ => unitIntervalCosineHeatPointWeight τ x n)
      (unitIntervalCosineHeatLaplacianPointWeight t x n) t := by
  let lambda : ℝ := unitIntervalCosineEigenvalue n
  have hlin : HasDerivAt (fun τ : ℝ => -(τ * lambda)) (-lambda) t := by
    have hmul : HasDerivAt (fun τ : ℝ => τ * lambda) lambda t :=
      by simpa [id, one_mul] using (hasDerivAt_id t).mul_const lambda
    simpa using hmul.neg
  have hexp := hlin.exp
  have h := hexp.mul_const (unitIntervalCosineMode n x)
  convert h using 1
  · ext τ
    simp [unitIntervalCosineHeatPointWeight, lambda]
  · simp [unitIntervalCosineHeatLaplacianPointWeight,
      unitIntervalCosineHeatPointWeight, unitIntervalCosineMode, lambda]
    ring

/-- Time derivative formula for one heat-weighted cosine coefficient. -/
theorem unitIntervalCosineHeatTerm_hasTimeDerivAt_laplacian
    (t x : ℝ) (a : ℕ → ℝ) (n : ℕ) :
    HasDerivAt
      (fun τ : ℝ => unitIntervalCosineHeatPointWeight τ x n * a n)
      (unitIntervalCosineHeatLaplacianPointWeight t x n * a n) t := by
  simpa [mul_assoc] using
    (unitIntervalCosineHeatPointWeight_hasTimeDerivAt_laplacian
      t x n).mul_const (a n)

/-- Term-by-term differentiation of the gradient cosine series.  This is the
second spatial derivative of the heat-flow cosine model, with an explicit
summable majorant for the Laplacian series. -/
theorem unitIntervalCosineHeatGradientValue_hasDerivAt_of_summable_bound
    {t x x₀ : ℝ} {a : ℕ → ℝ} {u : ℕ → ℝ}
    (hu : Summable u)
    (hbound :
      ∀ n y,
        ‖unitIntervalCosineHeatLaplacianPointWeight t y n * a n‖ ≤ u n)
    (h₀ :
      Summable fun n => unitIntervalCosineHeatGradientPointWeight t x₀ n * a n) :
    HasDerivAt (fun z : ℝ => unitIntervalCosineHeatGradientValue t a z)
      (unitIntervalCosineHeatLaplacianValue t a x) x := by
  simpa [unitIntervalCosineHeatGradientValue,
    unitIntervalCosineHeatLaplacianValue] using
    (hasDerivAt_tsum
      (𝕜 := ℝ) (F := ℝ)
      (u := u)
      (g := fun n z =>
        unitIntervalCosineHeatGradientPointWeight t z n * a n)
      (g' := fun n z =>
        unitIntervalCosineHeatLaplacianPointWeight t z n * a n)
      hu
      (fun n y => by
        simpa using
          unitIntervalCosineHeatGradientTerm_hasDerivAt_laplacian t a n y)
      (fun n y => by
        simpa using hbound n y)
      (by simpa using h₀)
      x)

/-- Derivative form of
`unitIntervalCosineHeatGradientValue_hasDerivAt_of_summable_bound`. -/
theorem unitIntervalCosineHeatGradientValue_deriv_of_summable_bound
    {t x x₀ : ℝ} {a : ℕ → ℝ} {u : ℕ → ℝ}
    (hu : Summable u)
    (hbound :
      ∀ n y,
        ‖unitIntervalCosineHeatLaplacianPointWeight t y n * a n‖ ≤ u n)
    (h₀ :
      Summable fun n => unitIntervalCosineHeatGradientPointWeight t x₀ n * a n) :
    deriv (fun z : ℝ => unitIntervalCosineHeatGradientValue t a z) x =
      unitIntervalCosineHeatLaplacianValue t a x :=
  (unitIntervalCosineHeatGradientValue_hasDerivAt_of_summable_bound
    (t := t) (x := x) (x₀ := x₀) hu hbound h₀).deriv

/-- Term-by-term time differentiation of the cosine heat series. -/
theorem unitIntervalCosineHeatValue_hasTimeDerivAt_of_summable_bound
    {t x t₀ : ℝ} {a : ℕ → ℝ} {u : ℕ → ℝ}
    (hu : Summable u)
    (hbound :
      ∀ n τ,
        ‖unitIntervalCosineHeatLaplacianPointWeight τ x n * a n‖ ≤ u n)
    (h₀ :
      Summable fun n => unitIntervalCosineHeatPointWeight t₀ x n * a n) :
    HasDerivAt (fun τ : ℝ => unitIntervalCosineHeatValue τ a x)
      (unitIntervalCosineHeatLaplacianValue t a x) t := by
  simpa [unitIntervalCosineHeatValue,
    unitIntervalCosineHeatLaplacianValue] using
    (hasDerivAt_tsum
      (𝕜 := ℝ) (F := ℝ)
      (u := u)
      (g := fun n τ =>
        unitIntervalCosineHeatPointWeight τ x n * a n)
      (g' := fun n τ =>
        unitIntervalCosineHeatLaplacianPointWeight τ x n * a n)
      hu
      (fun n τ => by
        simpa using
          unitIntervalCosineHeatTerm_hasTimeDerivAt_laplacian τ x a n)
      (fun n τ => by
        simpa using hbound n τ)
      (by simpa using h₀)
      t)

/-- Local version of term-by-term time differentiation.  The summable
majorant only has to hold on the open positive-time side `Ioi r`, which is the
usable form for heat regularization at `t > 0`. -/
theorem unitIntervalCosineHeatValue_hasTimeDerivAt_of_summable_bound_on_Ioi
    {r t x t₀ : ℝ} {a : ℕ → ℝ} {u : ℕ → ℝ}
    (hrt : r < t) (hr₀ : r < t₀)
    (hu : Summable u)
    (hbound :
      ∀ n τ, τ ∈ Set.Ioi r →
        ‖unitIntervalCosineHeatLaplacianPointWeight τ x n * a n‖ ≤ u n)
    (h₀ :
      Summable fun n => unitIntervalCosineHeatPointWeight t₀ x n * a n) :
    HasDerivAt (fun τ : ℝ => unitIntervalCosineHeatValue τ a x)
      (unitIntervalCosineHeatLaplacianValue t a x) t := by
  simpa [unitIntervalCosineHeatValue,
    unitIntervalCosineHeatLaplacianValue] using
    (hasDerivAt_tsum_of_isPreconnected
      (𝕜 := ℝ) (F := ℝ)
      (u := u)
      (t := Set.Ioi r)
      (g := fun n τ =>
        unitIntervalCosineHeatPointWeight τ x n * a n)
      (g' := fun n τ =>
        unitIntervalCosineHeatLaplacianPointWeight τ x n * a n)
      hu isOpen_Ioi isPreconnected_Ioi
      (fun n τ _hτ => by
        simpa using
          unitIntervalCosineHeatTerm_hasTimeDerivAt_laplacian τ x a n)
      (fun n τ hτ => by
        simpa using hbound n τ hτ)
      (by simpa using hr₀)
      (by simpa using h₀)
      (by simpa using hrt))

/-- `L²` coefficient data gives a summable majorant for the heat-Laplacian
point weights at any positive heat time. -/
lemma unitIntervalCosineHeatLaplacianPointWeight_l2_majorant
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ}
    (ha : Summable fun n => (a n) ^ 2) :
    Summable
        (fun n =>
          Real.sqrt (unitIntervalCosineHeatLaplacianMultiplier t n) *
            |a n|) ∧
      ∀ n x,
        ‖unitIntervalCosineHeatLaplacianPointWeight t x n * a n‖ ≤
          Real.sqrt (unitIntervalCosineHeatLaplacianMultiplier t n) *
            |a n| := by
  let m : ℕ → ℝ := fun n => unitIntervalCosineHeatLaplacianMultiplier t n
  have hm_nonneg : ∀ n, 0 ≤ m n := by
    intro n
    dsimp [m, unitIntervalCosineHeatLaplacianMultiplier]
    positivity
  have hm : Summable m := by
    simpa [m] using unitIntervalCosineHeatLaplacianMultiplier_summable ht
  have hsqrt_sq : Summable fun n => (Real.sqrt (m n)) ^ 2 := by
    refine hm.congr ?_
    intro n
    exact (Real.sq_sqrt (hm_nonneg n)).symm
  have hu_abs :
      Summable fun n => |Real.sqrt (m n) * a n| :=
    real_summable_abs_mul_of_summable_sq hsqrt_sq ha
  have hu :
      Summable fun n => Real.sqrt (m n) * |a n| := by
    simpa [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] using hu_abs
  refine ⟨by simpa [m] using hu, ?_⟩
  intro n x
  have hsq :=
    unitIntervalCosineHeatLaplacianPointWeight_sq_le_multiplier t x n
  have hw_abs :
      |unitIntervalCosineHeatLaplacianPointWeight t x n| ≤
        Real.sqrt (unitIntervalCosineHeatLaplacianMultiplier t n) :=
    Real.abs_le_sqrt hsq
  calc
    ‖unitIntervalCosineHeatLaplacianPointWeight t x n * a n‖
        =
          |unitIntervalCosineHeatLaplacianPointWeight t x n| *
            |a n| := by
          rw [Real.norm_eq_abs, abs_mul]
    _ ≤
          Real.sqrt (unitIntervalCosineHeatLaplacianMultiplier t n) *
            |a n| :=
          mul_le_mul_of_nonneg_right hw_abs (abs_nonneg _)

/-- Positive-time `L²` coefficient data gives `C¹` time differentiability of
the cosine heat model. -/
theorem unitIntervalCosineHeatValue_hasTimeDerivAt_of_l2
    {t x : ℝ} (ht : 0 < t) {a : ℕ → ℝ}
    (ha : Summable fun n => (a n) ^ 2) :
    HasDerivAt (fun τ : ℝ => unitIntervalCosineHeatValue τ a x)
      (unitIntervalCosineHeatLaplacianValue t a x) t := by
  let r : ℝ := t / 2
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  obtain ⟨hu, _hmajor_at_r⟩ :=
    unitIntervalCosineHeatLaplacianPointWeight_l2_majorant
      (t := r) hr_pos (a := a) ha
  have hbound :
      ∀ n τ, τ ∈ Set.Ioi r →
        ‖unitIntervalCosineHeatLaplacianPointWeight τ x n * a n‖ ≤
          Real.sqrt (unitIntervalCosineHeatLaplacianMultiplier r n) *
            |a n| := by
    intro n τ hτ
    have hsq₁ :=
      unitIntervalCosineHeatLaplacianPointWeight_sq_le_multiplier τ x n
    have hmono :
        unitIntervalCosineHeatLaplacianMultiplier τ n ≤
          unitIntervalCosineHeatLaplacianMultiplier r n :=
      unitIntervalCosineHeatLaplacianMultiplier_anti_mono_time
        (r := r) (τ := τ) (le_of_lt hτ) n
    have hsq₂ :
        (unitIntervalCosineHeatLaplacianPointWeight τ x n) ^ 2 ≤
          unitIntervalCosineHeatLaplacianMultiplier r n :=
      hsq₁.trans hmono
    have hw_abs :
        |unitIntervalCosineHeatLaplacianPointWeight τ x n| ≤
          Real.sqrt (unitIntervalCosineHeatLaplacianMultiplier r n) :=
      Real.abs_le_sqrt hsq₂
    calc
      ‖unitIntervalCosineHeatLaplacianPointWeight τ x n * a n‖
          =
            |unitIntervalCosineHeatLaplacianPointWeight τ x n| *
              |a n| := by
            rw [Real.norm_eq_abs, abs_mul]
      _ ≤
            Real.sqrt (unitIntervalCosineHeatLaplacianMultiplier r n) *
              |a n| :=
            mul_le_mul_of_nonneg_right hw_abs (abs_nonneg _)
  have htrace :=
    unitIntervalCosineHeatTrace_summable ht
      unitIntervalCosineReciprocalEigenvalueTerm_summable
  have hpoint :
      Summable fun n => (unitIntervalCosineHeatPointWeight t x n) ^ 2 :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _)
      (fun n => unitIntervalCosineHeatPointWeight_sq_le_traceTerm t x n)
      htrace
  have h₀ :
      Summable fun n => unitIntervalCosineHeatPointWeight t x n * a n :=
    real_summable_mul_of_summable_sq hpoint ha
  exact
    unitIntervalCosineHeatValue_hasTimeDerivAt_of_summable_bound_on_Ioi
      (r := r) (t := t) (x := x) (t₀ := t) (a := a)
      (u := fun n =>
        Real.sqrt (unitIntervalCosineHeatLaplacianMultiplier r n) * |a n|)
      (by dsimp [r]; linarith) (by dsimp [r]; linarith)
      hu hbound h₀

/-- Positive-time `L²` coefficient data gives the second spatial derivative of
the cosine heat model. -/
theorem unitIntervalCosineHeatValue_hasSecondSpatialDerivAt_of_l2
    {t x : ℝ} (ht : 0 < t) {a : ℕ → ℝ}
    (ha : Summable fun n => (a n) ^ 2) :
    HasDerivAt
      (fun z : ℝ => deriv (fun y : ℝ => unitIntervalCosineHeatValue t a y) z)
      (unitIntervalCosineHeatLaplacianValue t a x) x := by
  have hderiv :
      (fun z : ℝ =>
          deriv (fun y : ℝ => unitIntervalCosineHeatValue t a y) z) =
        fun z : ℝ => unitIntervalCosineHeatGradientValue t a z := by
    funext z
    exact unitIntervalCosineHeatValue_deriv_of_l2
      (t := t) (x := z) ht
      unitIntervalCosineReciprocalEigenvalueTerm_summable ha
  rw [hderiv]
  obtain ⟨hu, hbound⟩ :=
    unitIntervalCosineHeatLaplacianPointWeight_l2_majorant
      (t := t) ht (a := a) ha
  have hgrad_trace :=
    unitIntervalCosineHeatGradientTrace_summable ht
      unitIntervalCosineReciprocalEigenvalueTerm_summable
  have hgrad_point :
      Summable fun n =>
        (unitIntervalCosineHeatGradientPointWeight t 0 n) ^ 2 :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _)
      (fun n => unitIntervalCosineHeatGradientPointWeight_sq_le_multiplier t 0 n)
      hgrad_trace
  have hgrad₀ :
      Summable fun n =>
        unitIntervalCosineHeatGradientPointWeight t 0 n * a n :=
    real_summable_mul_of_summable_sq hgrad_point ha
  exact
    unitIntervalCosineHeatGradientValue_hasDerivAt_of_summable_bound
      (t := t) (x := x) (x₀ := 0) hu
      (by simpa using hbound) hgrad₀

/-- Direct positive-time `L²` coefficient certificate: the cosine heat model is
`C¹` in time and `C²` in space, with both derivatives represented by the
Laplacian cosine series. -/
theorem unitIntervalCosineHeatValue_c1_time_c2_space_of_l2
    {t x : ℝ} (ht : 0 < t) {a : ℕ → ℝ}
    (ha : Summable fun n => (a n) ^ 2) :
    HasDerivAt (fun τ : ℝ => unitIntervalCosineHeatValue τ a x)
        (unitIntervalCosineHeatLaplacianValue t a x) t ∧
      HasDerivAt
        (fun z : ℝ =>
          deriv (fun y : ℝ => unitIntervalCosineHeatValue t a y) z)
        (unitIntervalCosineHeatLaplacianValue t a x) x := by
  exact
    ⟨unitIntervalCosineHeatValue_hasTimeDerivAt_of_l2
        (t := t) (x := x) ht ha,
      unitIntervalCosineHeatValue_hasSecondSpatialDerivAt_of_l2
        (t := t) (x := x) ht ha⟩

/-- The cosine heat series is twice spatially differentiable when both the
first- and second-derivative series have summable majorants. -/
theorem unitIntervalCosineHeatValue_hasSecondSpatialDerivAt_of_summable_bound
    {t x x₀ x₁ : ℝ} {a : ℕ → ℝ} {u₁ u₂ : ℕ → ℝ}
    (hu₁ : Summable u₁)
    (hgrad_bound :
      ∀ n y,
        ‖unitIntervalCosineHeatGradientPointWeight t y n * a n‖ ≤ u₁ n)
    (hpoint₀ :
      Summable fun n => unitIntervalCosineHeatPointWeight t x₀ n * a n)
    (hu₂ : Summable u₂)
    (hlap_bound :
      ∀ n y,
        ‖unitIntervalCosineHeatLaplacianPointWeight t y n * a n‖ ≤ u₂ n)
    (hgrad₀ :
      Summable fun n => unitIntervalCosineHeatGradientPointWeight t x₁ n * a n) :
    HasDerivAt
      (fun z : ℝ => deriv (fun y : ℝ => unitIntervalCosineHeatValue t a y) z)
      (unitIntervalCosineHeatLaplacianValue t a x) x := by
  have hderiv :
      (fun z : ℝ =>
          deriv (fun y : ℝ => unitIntervalCosineHeatValue t a y) z) =
        fun z : ℝ => unitIntervalCosineHeatGradientValue t a z := by
    funext z
    exact unitIntervalCosineHeatValue_deriv_of_summable_bound
      (t := t) (x := z) (x₀ := x₀) hu₁ hgrad_bound hpoint₀
  rw [hderiv]
  exact unitIntervalCosineHeatGradientValue_hasDerivAt_of_summable_bound
    (t := t) (x := x) (x₀ := x₁) hu₂ hlap_bound hgrad₀

/-- Pointwise heat-equation regularity certificate for the unit-interval cosine
model: `C¹` in time and `C²` in space, with both derivatives equal to the same
Laplacian cosine series. -/
theorem unitIntervalCosineHeatValue_c1_time_c2_space_certificate
    {t x x₀ x₁ t₀ : ℝ} {a : ℕ → ℝ}
    {u₁ u₂ uT : ℕ → ℝ}
    (hu₁ : Summable u₁)
    (hgrad_bound :
      ∀ n y,
        ‖unitIntervalCosineHeatGradientPointWeight t y n * a n‖ ≤ u₁ n)
    (hpoint₀ :
      Summable fun n => unitIntervalCosineHeatPointWeight t x₀ n * a n)
    (hu₂ : Summable u₂)
    (hlap_space_bound :
      ∀ n y,
        ‖unitIntervalCosineHeatLaplacianPointWeight t y n * a n‖ ≤ u₂ n)
    (hgrad₀ :
      Summable fun n => unitIntervalCosineHeatGradientPointWeight t x₁ n * a n)
    (huT : Summable uT)
    (hlap_time_bound :
      ∀ n τ,
        ‖unitIntervalCosineHeatLaplacianPointWeight τ x n * a n‖ ≤ uT n)
    (htime₀ :
      Summable fun n => unitIntervalCosineHeatPointWeight t₀ x n * a n) :
    HasDerivAt (fun τ : ℝ => unitIntervalCosineHeatValue τ a x)
        (unitIntervalCosineHeatLaplacianValue t a x) t ∧
      HasDerivAt
        (fun z : ℝ =>
          deriv (fun y : ℝ => unitIntervalCosineHeatValue t a y) z)
        (unitIntervalCosineHeatLaplacianValue t a x) x := by
  exact
    ⟨unitIntervalCosineHeatValue_hasTimeDerivAt_of_summable_bound
        (t := t) (x := x) (t₀ := t₀) huT hlap_time_bound htime₀,
      unitIntervalCosineHeatValue_hasSecondSpatialDerivAt_of_summable_bound
        (t := t) (x := x) (x₀ := x₀) (x₁ := x₁)
        hu₁ hgrad_bound hpoint₀ hu₂ hlap_space_bound hgrad₀⟩

/-! ## Sobolev/Gagliardo--Nirenberg bootstrap interfaces -/

/-- Sobolev endpoint used after H0.2 supplies an `L²` gradient bound.  This is
just the interval `H¹ → L∞` theorem restated with unit interval constants. -/
theorem unitInterval_sobolev_H1_Linfty_bound
    {f f' : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_deriv : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hf_mem : MemLp f (2 : ℝ≥0∞)
      (volume.restrict (Ioc (0 : ℝ) 1)))
    (hf'_mem : MemLp f' (2 : ℝ≥0∞)
      (volume.restrict (Ioc (0 : ℝ) 1)))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |f x| ≤
      lpNorm f (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) 1)) +
        lpNorm f' (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hbase :=
    ShenWork.Sobolev.sobolev_H1_Linfty_interval
      (L := 1) (by norm_num : (0 : ℝ) < 1)
      (f := f) (f' := f') hf_cont hf_deriv hf_mem hf'_mem hx
  simpa using hbase

/-- Unit-interval Gagliardo--Nirenberg endpoint used in the bootstrap, with
the constants specialized to `L = 1`. -/
theorem unitInterval_gagliardoNirenberg_bound
    {f f' : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_deriv : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hf_mem : MemLp f (2 : ℝ≥0∞)
      (volume.restrict (Ioc (0 : ℝ) 1)))
    (hf'_mem : MemLp f' (2 : ℝ≥0∞)
      (volume.restrict (Ioc (0 : ℝ) 1))) :
    (lpNorm f (4 : ℝ≥0∞)
        (volume.restrict (Ioc (0 : ℝ) 1))) ^ (2 : ℝ) ≤
      (lpNorm f (2 : ℝ≥0∞)
          (volume.restrict (Ioc (0 : ℝ) 1)) +
        lpNorm f' (2 : ℝ≥0∞)
          (volume.restrict (Ioc (0 : ℝ) 1))) *
        lpNorm f (2 : ℝ≥0∞)
          (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hbase :=
    ShenWork.Sobolev.gagliardoNirenberg_interval
      (L := 1) (by norm_num : (0 : ℝ) < 1)
      (f := f) (f' := f') hf_cont hf_deriv hf_mem hf'_mem
  simpa using hbase

/-! ## Final classical assembly frontier

The theorem below is intentionally only an assembly theorem.  It does not
claim that the Duhamel time integral has already been differentiated twice in
space and once in time.  The preceding lemmas are the proved heat-smoothing
inputs needed for that step; sb-ode can import them and then discharge the
remaining dominated-differentiation and elliptic `v` pieces in its own file.
-/

/-- Assembly target once the Duhamel fixed point has been regularized into the
Paper 2 pointwise equations, boundary condition, maximum-principle regularity,
positivity, and initial trace. -/
theorem intervalClassicalSolution_of_regularized_mild
    (p : CM2Params) {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hreg : intervalDomainClassicalRegularity T u v)
    (hpos :
      ∀ t x, 0 < t → t < T → 0 < u t x)
    (hv_nonneg :
      ∀ t x, 0 < t → t < T → 0 ≤ v t x)
    (hpde_u :
      ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
        intervalDomain.timeDeriv u t x =
          intervalDomain.laplacian (u t) x
            - p.χ₀ * intervalDomain.chemotaxisDiv p (u t) (v t) x
            + u t x * (p.a - p.b * (u t x) ^ p.α))
    (hpde_v :
      ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
        0 = intervalDomain.laplacian (v t) x
          - p.μ * v t x + p.ν * (u t x) ^ p.γ)
    (hneumann :
      ∀ t x, 0 < t → t < T → x ∈ intervalDomain.boundary →
        intervalDomain.normalDeriv (u t) x = 0 ∧
          intervalDomain.normalDeriv (v t) x = 0) :
    IsPaper2ClassicalSolution intervalDomain p T u v :=
  IsPaper2ClassicalSolution.of_components hT hreg hpos hv_nonneg hpde_u hpde_v hneumann

end ShenWork.RegularityBootstrap

end
