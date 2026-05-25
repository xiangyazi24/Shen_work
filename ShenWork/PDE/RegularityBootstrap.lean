/-
  ShenWork/PDE/RegularityBootstrap.lean

  Local-existence support lemmas for the interval-domain regularity bootstrap.

  This file stays below `IntervalDomainExistence.lean`: it does not import the
  sb-ode local-existence file, so that file can import these lemmas without a
  cycle.  The proved content here is the heat-smoothing part of the bootstrap:
  interval heat terms are spatially differentiable and their gradients satisfy
  the already established H0.2 `Lp` bounds.

  The remaining classical upgrade needs differentiating the Duhamel time
  integral once in time and once more in space.  That is exposed as an explicit
  frontier certificate at the end, not hidden as an axiom or a theorem field.
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
      ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside → 0 < u t x)
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
  IsPaper2ClassicalSolution.of_components hT hreg hpos hpde_u hpde_v hneumann

end ShenWork.RegularityBootstrap

end
