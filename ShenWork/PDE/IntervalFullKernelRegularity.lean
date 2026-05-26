/-
# Interior-`C²` and Neumann regularity of the full-kernel semigroup profile

This file threads the *unconditional* full-kernel = cosine-spectral identity
(`IntervalFullKernelInterchange.lean`) into the regularity obligations of the
local-existence chain.

It proves, with no `sorry`/`admit`/custom axiom:

* `unitIntervalCosineHeatGradientValue_eq_zero_at_zero` /
  `..._at_one` — the spatial-gradient series of the cosine heat value vanishes
  at the endpoints `x = 0, 1` (each term carries `sin(nπ·0)=0`, `sin(nπ·1)=0`).
* `unitIntervalCosineHeatValue_deriv_zero_at_endpoint` — hence the spatial
  derivative `deriv (heat value)` is `0` at `{0,1}`: the **exact Neumann
  boundary condition** of the cosine spectral heat value.
* `intervalFullSemigroupProfile_contDiffOn_two` — a function agreeing on `(0,1)`
  with `intervalFullSemigroupOperator t f` (continuous `f`, bounded cosine
  coefficients) is interior-`C²`, via the unconditional identity composed with
  the bootstrap `eqOn` lemma.
* `intervalFullSemigroupProfile_classicalRegularity_third_conjunct` — the exact
  shape of the third conjunct of `intervalDomainClassicalRegularity` for a
  time-indexed family whose `u`/`v` slices agree on `(0,1)` with full-kernel
  semigroup profiles.

## Remaining gap (named precisely)

The localExistence `RegularityBootstrap` requires this interior-`C²` of the
*Duhamel fixed point* `u t`, i.e. `intervalDomainLift (u t)` agreeing on `(0,1)`
with a cosine heat value.  For the pure semigroup term `e^{tΔ_N}u₀` that
agreement is exactly `intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional`.
The outstanding analytic step is the **Duhamel integral term**
`∫₀ᵗ e^{(t-s)Δ_N}F(u(s)) ds`: showing the *time-integral of the C² spatial
family* is itself interior-`C²` (differentiation under the integral sign with a
locally-uniform second-derivative majorant).  We isolate this as the single
named hypothesis `DuhamelTermInteriorC2` below; everything else in the
interior-`C²` conjunct is discharged here.
-/

import ShenWork.PDE.IntervalFullKernelInterchange
import ShenWork.PDE.IntervalDomainRegularityBootstrap

open MeasureTheory
open scoped Real

noncomputable section

namespace ShenWork.IntervalFullKernelRegularity

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalDomainRegularityBootstrap
open ShenWork.IntervalFullKernelInterchange
open ShenWork.HeatKernelGradientEstimates

/-! ## Neumann boundary condition of the cosine spectral heat value -/

/-- Each spatial-gradient term-weight vanishes at `x = 0` (it carries
`sin(nπ·0) = 0`). -/
theorem unitIntervalCosineHeatGradientPointWeight_zero_at_zero (t : ℝ) (n : ℕ) :
    unitIntervalCosineHeatGradientPointWeight t 0 n = 0 := by
  unfold unitIntervalCosineHeatGradientPointWeight
  simp

/-- Each spatial-gradient term-weight vanishes at `x = 1` (it carries
`sin(nπ·1) = sin(nπ) = 0`). -/
theorem unitIntervalCosineHeatGradientPointWeight_zero_at_one (t : ℝ) (n : ℕ) :
    unitIntervalCosineHeatGradientPointWeight t 1 n = 0 := by
  unfold unitIntervalCosineHeatGradientPointWeight
  have hsin : Real.sin ((n : ℝ) * Real.pi * 1) = 0 := by
    rw [mul_one]
    simp [Real.sin_nat_mul_pi n]
  rw [hsin]
  ring

/-- The spatial-gradient *series* of the cosine heat value vanishes at `x = 0`. -/
theorem unitIntervalCosineHeatGradientValue_eq_zero_at_zero (t : ℝ) (a : ℕ → ℝ) :
    unitIntervalCosineHeatGradientValue t a 0 = 0 := by
  unfold unitIntervalCosineHeatGradientValue
  have : (fun n => unitIntervalCosineHeatGradientPointWeight t 0 n * a n)
      = fun _ : ℕ => (0 : ℝ) := by
    funext n
    rw [unitIntervalCosineHeatGradientPointWeight_zero_at_zero t n, zero_mul]
  rw [this, tsum_zero]

/-- The spatial-gradient *series* of the cosine heat value vanishes at `x = 1`. -/
theorem unitIntervalCosineHeatGradientValue_eq_zero_at_one (t : ℝ) (a : ℕ → ℝ) :
    unitIntervalCosineHeatGradientValue t a 1 = 0 := by
  unfold unitIntervalCosineHeatGradientValue
  have : (fun n => unitIntervalCosineHeatGradientPointWeight t 1 n * a n)
      = fun _ : ℕ => (0 : ℝ) := by
    funext n
    rw [unitIntervalCosineHeatGradientPointWeight_zero_at_one t n, zero_mul]
  rw [this, tsum_zero]

/-- The first spatial derivative of the cosine heat value equals the gradient
value everywhere (bounded coefficients, `t > 0`). -/
theorem unitIntervalCosineHeatValue_deriv_eq_gradientValue
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) (x : ℝ) :
    deriv (fun z : ℝ => unitIntervalCosineHeatValue t a z) x =
      unitIntervalCosineHeatGradientValue t a x := by
  -- gradient majorant (reciprocal-cube), reused from the bootstrap derivation
  set Cg : ℝ := 4 / (t ^ 2 * Real.pi ^ 3) with hCg
  have hCg0 : (0 : ℝ) ≤ Cg := by rw [hCg]; positivity
  have hgrad_majorant : Summable (fun n =>
      Cg * unitIntervalCosineReciprocalCubeTerm n * |M|) := by
    have := (unitIntervalCosineReciprocalCubeTerm_summable.mul_left
      Cg).mul_right |M|
    simpa [mul_assoc] using this
  have hgrad_bound : ∀ n y,
      ‖unitIntervalCosineHeatGradientPointWeight t y n * a n‖ ≤
        Cg * unitIntervalCosineReciprocalCubeTerm n * |M| := by
    intro n y
    have hMn : |a n| ≤ |M| := le_trans (hM n) (le_abs_self M)
    rw [Real.norm_eq_abs, abs_mul]
    have hw := unitIntervalCosineHeatGradientPointWeight_abs_le_reciprocal_cube ht y n
    calc |unitIntervalCosineHeatGradientPointWeight t y n| * |a n|
        ≤ (Cg * unitIntervalCosineReciprocalCubeTerm n) * |M| := by
          refine mul_le_mul hw hMn (abs_nonneg _) ?_
          exact mul_nonneg hCg0 (unitIntervalCosineReciprocalCubeTerm_nonneg n)
      _ = _ := by ring
  -- value summability at `x`
  have hval_summable : Summable
      (fun n => unitIntervalCosineHeatPointWeight t x n * a n) := by
    have hbound : ∀ n,
        ‖unitIntervalCosineHeatPointWeight t x n * a n‖ ≤
          Real.exp (-t * unitIntervalCosineEigenvalue n) * |M| := by
      intro n
      have hMn : |a n| ≤ |M| := le_trans (hM n) (le_abs_self M)
      rw [Real.norm_eq_abs, abs_mul]
      have hw : |unitIntervalCosineHeatPointWeight t x n| ≤
          Real.exp (-t * unitIntervalCosineEigenvalue n) := by
        unfold unitIntervalCosineHeatPointWeight
        rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
        have hmode : |unitIntervalCosineMode n x| ≤ 1 := by
          unfold unitIntervalCosineMode; exact Real.abs_cos_le_one _
        calc Real.exp (-t * unitIntervalCosineEigenvalue n) *
              |unitIntervalCosineMode n x|
            ≤ Real.exp (-t * unitIntervalCosineEigenvalue n) * 1 :=
              mul_le_mul_of_nonneg_left hmode (Real.exp_nonneg _)
          _ = Real.exp (-t * unitIntervalCosineEigenvalue n) := by ring
      exact mul_le_mul hw hMn (abs_nonneg _) (Real.exp_nonneg _)
    refine Summable.of_norm_bounded ?_ hbound
    exact (unitIntervalCosineHeatTrace_single_exp_summable ht).mul_right |M|
  exact unitIntervalCosineHeatValue_deriv_of_summable_bound
    (t := t) (x := x) (x₀ := x) hgrad_majorant hgrad_bound hval_summable

/-- **Neumann boundary condition of the cosine spectral heat value.**  For
`t > 0` and bounded cosine coefficients, the spatial derivative of the heat
value is `0` at both endpoints `x = 0` and `x = 1`. -/
theorem unitIntervalCosineHeatValue_deriv_zero_at_endpoint
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) {x : ℝ} (hx : x = 0 ∨ x = 1) :
    deriv (fun z : ℝ => unitIntervalCosineHeatValue t a z) x = 0 := by
  rcases hx with hx | hx
  · subst hx
    rw [unitIntervalCosineHeatValue_deriv_eq_gradientValue ht hM,
      unitIntervalCosineHeatGradientValue_eq_zero_at_zero]
  · subst hx
    rw [unitIntervalCosineHeatValue_deriv_eq_gradientValue ht hM,
      unitIntervalCosineHeatGradientValue_eq_zero_at_one]

/-! ## Interior-`C²` of the full-kernel semigroup profile -/

/-- The full-kernel Neumann semigroup of a continuous `f` agrees, on the open
interior `(0,1)`, with the cosine spectral heat value of its cosine
coefficients.  This is the *unconditional* identity, packaged as `EqOn`. -/
theorem intervalFullSemigroupOperator_eqOn_cosineHeatValue
    (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) (hf : Continuous f)
    (hkernel : ∀ x : ℝ, ∀ y,
      intervalNeumannFullKernel t x y =
        ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
          (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) :
    Set.EqOn (fun x => intervalFullSemigroupOperator t f x)
      (fun x => unitIntervalCosineHeatValue t (cosineCoeffs f) x)
      (Set.Ioo (0 : ℝ) 1) := by
  intro x hx
  exact intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional
    t ht f hf x hx (fun y => hkernel x y)

/-- **Interior-`C²` of the full-kernel semigroup profile.**  If a function
`g : intervalDomainPoint → ℝ` agrees on the interior `(0,1)` (after the
zero-extension lift) with the full-kernel Neumann semigroup `f ↦ S_t f` of a
continuous `f` whose cosine coefficients are bounded by `M`, then its lift is
`ContDiffOn ℝ 2` on `(0,1)`.

This composes:
* the *unconditional* `S_t f = cosine-spectral heat value` identity, and
* the bootstrap interior-`C²` of the cosine heat value
  (`intervalDomainLift_contDiffOn_two_of_eqOn_heatValue`). -/
theorem intervalFullSemigroupProfile_contDiffOn_two
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M)
    {g : intervalDomainPoint → ℝ}
    (hg : Set.EqOn (intervalDomainLift g)
      (fun x => intervalFullSemigroupOperator t f x) (Set.Ioo (0 : ℝ) 1))
    (hkernel : ∀ x : ℝ, ∀ y,
      intervalNeumannFullKernel t x y =
        ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
          (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) :
    ContDiffOn ℝ 2 (intervalDomainLift g) (Set.Ioo (0 : ℝ) 1) := by
  -- chain: lift g = S_t f = cosine heat value on (0,1)
  have heq : Set.EqOn (intervalDomainLift g)
      (fun x => unitIntervalCosineHeatValue t (cosineCoeffs f) x)
      (Set.Ioo (0 : ℝ) 1) :=
    hg.trans (intervalFullSemigroupOperator_eqOn_cosineHeatValue t ht f hf hkernel)
  exact intervalDomainLift_contDiffOn_two_of_eqOn_heatValue ht hM heq

/-! ## The third conjunct of `intervalDomainClassicalRegularity` -/

/-- **The interior-`C²` conjunct of `intervalDomainClassicalRegularity`,
discharged for full-kernel semigroup profiles.**  If for every `t ∈ (0,T)` both
slices `u t`, `v t` lift to functions agreeing on `(0,1)` with full-kernel
semigroup propagators of continuous, bounded-coefficient sources, then the third
conjunct of `intervalDomainClassicalRegularity` holds. -/
theorem intervalFullSemigroupProfile_classicalRegularity_third_conjunct
    {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hu : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∃ f : ℝ → ℝ, Continuous f ∧
      ∃ M : ℝ, (∀ n, |cosineCoeffs f n| ≤ M) ∧
        Set.EqOn (intervalDomainLift (u t))
          (fun x => intervalFullSemigroupOperator t f x) (Set.Ioo (0 : ℝ) 1) ∧
        (∀ x : ℝ, ∀ y, intervalNeumannFullKernel t x y =
          ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
            (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))))
    (hv : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∃ f : ℝ → ℝ, Continuous f ∧
      ∃ M : ℝ, (∀ n, |cosineCoeffs f n| ≤ M) ∧
        Set.EqOn (intervalDomainLift (v t))
          (fun x => intervalFullSemigroupOperator t f x) (Set.Ioo (0 : ℝ) 1) ∧
        (∀ x : ℝ, ∀ y, intervalNeumannFullKernel t x y =
          ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
            (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y)))) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Ioo (0 : ℝ) 1) ∧
        ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Set.Ioo (0 : ℝ) 1) := by
  intro t ht
  have htpos : 0 < t := ht.1
  obtain ⟨fu, hfu_cont, Mu, hMu, hu_eq, hu_ker⟩ := hu t ht
  obtain ⟨fv, hfv_cont, Mv, hMv, hv_eq, hv_ker⟩ := hv t ht
  refine ⟨?_, ?_⟩
  · exact intervalFullSemigroupProfile_contDiffOn_two htpos hfu_cont hMu hu_eq hu_ker
  · exact intervalFullSemigroupProfile_contDiffOn_two htpos hfv_cont hMv hv_eq hv_ker

/-! ## Named remaining gap toward localExistence

The interior-`C²` conjunct above is discharged for any time-slice that is a
*pure* full-kernel semigroup propagator.  The Duhamel fixed point adds the
inhomogeneous term

  `D_t := ∫₀ᵗ e^{(t-s)Δ_N} F(u(s)) ds`,

whose interior-`C²` is the only analytic content not supplied here.  We name it
precisely as a predicate so the localExistence chain can quote exactly this and
nothing more. -/

/-- **The single remaining analytic obligation.**  Spatial interior-`C²` of the
Duhamel time-integral term: the time-integral of a `C²` spatial family is itself
`C²` on the interior.  Concretely, for the Duhamel slice `w t`, its lift is
`ContDiffOn ℝ 2` on `(0,1)`.  Reducing the localExistence regularity obligation
to *this* predicate (plus the pure-semigroup part discharged above) is the
status delivered by this file. -/
def DuhamelTermInteriorC2 (T : ℝ) (w : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
    ContDiffOn ℝ 2 (intervalDomainLift (w t)) (Set.Ioo (0 : ℝ) 1)

end ShenWork.IntervalFullKernelRegularity
