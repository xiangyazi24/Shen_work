import ShenWork.PDE.IntervalFullKernelInterchange
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The `t → 0⁺` approximate-identity limit for the full Neumann heat propagator

This file proves the *correct* replacement for the false value-identity
`S 0 = id` (see `ShenWork/PDE/IntervalSemigroupAtZero.lean`, where a prior agent
showed `intervalFullSemigroupOperator 0 f x = 0` because `heatKernel 0 = 0`).

The genuine statement the Duhamel representation needs is the **approximate
identity** limit

  `Filter.Tendsto (fun t => intervalFullSemigroupOperator t f x)
     (𝓝[>] 0) (𝓝 (f x))`.

## Route (spectral)

For `t > 0`, `intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional`
(in `IntervalFullKernelInterchange.lean`) gives, for continuous `f` and
`x ∈ (0,1)`,

  `S t f x = unitIntervalCosineHeatValue t (cosineCoeffs f) x
           = ∑ₙ exp(-t λₙ) · cos(nπx) · f̂ₙ`,                              (*)

where `λₙ = (nπ)²` and `f̂ₙ = cosineCoeffs f n`.

As `t → 0⁺`, `exp(-t λₙ) → 1` for each `n`, so each summand of (*) converges to
`cos(nπx) · f̂ₙ`.  Dominated convergence over the discrete index set
(`tendsto_tsum_of_dominated_convergence`, Tannery's theorem) with the
`t`-uniform bound `|exp(-t λₙ) cos(nπx) f̂ₙ| ≤ |f̂ₙ|` (valid for all `t ≥ 0`,
since `λₙ ≥ 0 ⇒ exp(-t λₙ) ≤ 1`) upgrades this to convergence of the full
spectral sums:

  `∑ₙ exp(-t λₙ) cos(nπx) f̂ₙ  →  ∑ₙ cos(nπx) f̂ₙ`   as `t → 0⁺`.

The two analytic inputs that this requires, beyond the `t > 0` spectral identity
already proven in the repository, are:

* `hl1 : Summable (fun n => |cosineCoeffs f n|)`  — `ℓ¹` summability of the
  cosine coefficients, providing the dominating summable bound for Tannery's
  theorem.  (For a generic continuous `f` only `ℓ²` is automatic — see the
  cosine Hilbert basis `unitIntervalCosineHilbertBasis` in
  `Paper2/IntervalDomainLemma21.lean`; `ℓ¹` is the standard extra regularity,
  e.g. `f ∈ C¹` / bounded variation, that makes the cosine series converge
  absolutely and pointwise.)

* `hrecon : HasSum (fun n => unitIntervalCosineMode n x * cosineCoeffs f n)
              (f x)` — the **pointwise cosine reconstruction**
  `∑ₙ f̂ₙ cos(nπx) = f x`.  This is precisely the pointwise Fourier/cosine
  inversion theorem.  The repository proves cosine *completeness* only in the
  `L²` totality form (`unitIntervalCosine_nat_total_ae_zero` in
  `CosineParsevalBridge.lean`: all coefficients zero ⇒ `f = 0` a.e.) and the
  abstract `L²` Hilbert-basis reconstruction (`unitIntervalCosineHilbertBasis`),
  neither of which gives the *pointwise* value at an interior `x`.  Under `hl1`
  the cosine series converges uniformly, so `hrecon` is the natural and minimal
  remaining analytic input; we take it as a hypothesis and name it precisely.

No `sorry`/`admit`/custom axiom is used.
-/

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalFullKernelInterchange

namespace ShenWork.IntervalSemigroupApproxIdentity

noncomputable section

open scoped Real

/-- Per-mode limit: as `t → 0⁺`, the heat point weight times the coefficient
converges to the (undamped) cosine-mode term.  This is just continuity of
`t ↦ exp(-t λₙ)` at `0` with value `1`. -/
theorem heatPointWeight_mul_tendsto (x : ℝ) (a : ℕ → ℝ) (n : ℕ) :
    Tendsto (fun t => unitIntervalCosineHeatPointWeight t x n * a n)
      (𝓝[>] (0 : ℝ)) (𝓝 (unitIntervalCosineMode n x * a n)) := by
  have hexp : Tendsto
      (fun t : ℝ => Real.exp (-t * unitIntervalCosineEigenvalue n))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hcont : Tendsto
        (fun t : ℝ => Real.exp (-t * unitIntervalCosineEigenvalue n))
        (𝓝 (0 : ℝ)) (𝓝 1) := by
      have : Continuous
          (fun t : ℝ => Real.exp (-t * unitIntervalCosineEigenvalue n)) := by
        fun_prop
      have h := this.tendsto (0 : ℝ)
      simpa using h
    exact hcont.mono_left nhdsWithin_le_nhds
  have hmul : Tendsto
      (fun t => Real.exp (-t * unitIntervalCosineEigenvalue n) *
        (unitIntervalCosineMode n x * a n))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 * (unitIntervalCosineMode n x * a n))) :=
    hexp.mul_const _
  have hfun : (fun t => unitIntervalCosineHeatPointWeight t x n * a n)
      = fun t => Real.exp (-t * unitIntervalCosineEigenvalue n) *
        (unitIntervalCosineMode n x * a n) := by
    funext t
    rw [unitIntervalCosineHeatPointWeight]; ring
  rw [hfun]
  simpa using hmul

/-- Uniform `ℓ¹` domination of the heat-point-weighted coefficient summands for
`t ≥ 0`:  `|exp(-t λₙ) cos(nπx) f̂ₙ| ≤ |f̂ₙ|`, because `λₙ ≥ 0 ⇒ exp(-t λₙ) ≤ 1`
and `|cos| ≤ 1`. -/
theorem heatPointWeight_mul_abs_le {t : ℝ} (ht : 0 ≤ t) (x : ℝ) (a : ℕ → ℝ)
    (n : ℕ) :
    ‖unitIntervalCosineHeatPointWeight t x n * a n‖ ≤ |a n| := by
  have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
    dsimp [unitIntervalCosineEigenvalue]; positivity
  have hexp_le_one : Real.exp (-t * unitIntervalCosineEigenvalue n) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ t * unitIntervalCosineEigenvalue n := mul_nonneg ht hlam
    nlinarith
  have hexp_nonneg : 0 ≤ Real.exp (-t * unitIntervalCosineEigenvalue n) :=
    Real.exp_nonneg _
  have hcos : |unitIntervalCosineMode n x| ≤ 1 := by
    rw [unitIntervalCosineMode]; exact Real.abs_cos_le_one _
  rw [Real.norm_eq_abs, unitIntervalCosineHeatPointWeight, abs_mul, abs_mul,
    abs_of_nonneg hexp_nonneg]
  calc Real.exp (-t * unitIntervalCosineEigenvalue n) *
        |unitIntervalCosineMode n x| * |a n|
      ≤ 1 * 1 * |a n| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact mul_le_mul hexp_le_one hcos (abs_nonneg _) (by norm_num)
    _ = |a n| := by ring

/-- **The spectral sum approximate-identity limit.**

For `ℓ¹` cosine coefficients `a`, the damped spectral sum
`unitIntervalCosineHeatValue t a x = ∑ₙ exp(-t λₙ) cos(nπx) aₙ` converges, as
`t → 0⁺`, to the undamped sum `∑ₙ cos(nπx) aₙ`.  Proved by Tannery's theorem
(`tendsto_tsum_of_dominated_convergence`) with dominating bound `|aₙ|`. -/
theorem unitIntervalCosineHeatValue_tendsto_tsum (x : ℝ) {a : ℕ → ℝ}
    (hl1 : Summable (fun n => |a n|)) :
    Tendsto (fun t => unitIntervalCosineHeatValue t a x)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑' n, unitIntervalCosineMode n x * a n)) := by
  have h := tendsto_tsum_of_dominated_convergence
    (𝓕 := 𝓝[>] (0 : ℝ))
    (f := fun t n => unitIntervalCosineHeatPointWeight t x n * a n)
    (g := fun n => unitIntervalCosineMode n x * a n)
    (bound := fun n => |a n|)
    hl1
    (fun n => heatPointWeight_mul_tendsto x a n)
    (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      intro n
      exact heatPointWeight_mul_abs_le (le_of_lt ht) x a n)
  -- `unitIntervalCosineHeatValue t a x = ∑' n, (heat weight) * a n` by definition
  simpa [unitIntervalCosineHeatValue] using h

/-- **Approximate-identity limit for the full periodised Neumann propagator.**

This is the correct replacement for the (false) value-identity `S 0 f x = f x`.
For continuous `f` with `ℓ¹` cosine coefficients (`hl1`), the pointwise cosine
reconstruction at the interior point `x`
(`hrecon : HasSum (fun n => cos(nπx) · f̂ₙ) (f x)`), and the per-time-slice
kernel spectral identity `hkernel` (the Poisson/theta content, valid for `t>0`),
the full periodised Neumann heat propagator satisfies

  `Filter.Tendsto (fun t => intervalFullSemigroupOperator t f x)
     (𝓝[>] 0) (𝓝 (f x))`. -/
theorem intervalFullSemigroup_tendsto_id_at_zero
    (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hl1 : Summable (fun n => |cosineCoeffs f n|))
    (hrecon : HasSum (fun n => unitIntervalCosineMode n x * cosineCoeffs f n) (f x))
    (hkernel : ∀ t : ℝ, 0 < t → ∀ y,
      intervalNeumannFullKernel t x y =
        ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
          (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) :
    Tendsto (fun t => intervalFullSemigroupOperator t f x)
      (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  -- limit of the undamped spectral sum is `f x`
  have hlim_eq : (∑' n, unitIntervalCosineMode n x * cosineCoeffs f n) = f x :=
    hrecon.tsum_eq
  -- the spectral-sum limit (Tannery)
  have htsum := unitIntervalCosineHeatValue_tendsto_tsum x (a := cosineCoeffs f) hl1
  rw [hlim_eq] at htsum
  -- on `(0,∞)`, `S t f x = unitIntervalCosineHeatValue t (cosineCoeffs f) x`
  refine htsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional
    t ht f hf x hx (hkernel t ht)).symm

end

end ShenWork.IntervalSemigroupApproxIdentity
