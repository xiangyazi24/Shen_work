/-
  The chemotaxis-flux integration-by-parts lemma and the flux-difference
  pointwise bound, toward the `u`-only parabolic energy inequality
  `E_u' ≤ K · E_u`.

  This file proves, with no `sorry`/`admit`/`axiom`:

  * `intervalFluxByParts` — **(3)** the chemotaxis IBP
    `∫₀¹ φ·F' = − ∫₀¹ φ'·F` for `C¹` `φ` and `F` with the flux `F` vanishing at
    the endpoints (`F 0 = F 1 = 0`, the genuine Neumann content for the
    chemotaxis flux `u·∂ₓv/(1+v)^β`, whose `∂ₓv` factor is `0` at `0,1`).  This
    is the single-IBP cousin of `intervalEnergyByParts`.
-/
import ShenWork.Paper2.IntervalDomainL2UEnergyInequality
import ShenWork.Paper2.IntervalDomainL2StaticVDifference

open MeasureTheory intervalIntegral
open ShenWork.IntervalDomain
open ShenWork.IntervalSolutionCoeffDeriv
open ShenWork.PDE ShenWork.IntervalEllipticCharacterization
open ShenWork.IntervalResolverGradientBridge
open scoped Topology

namespace ShenWork.Paper2

noncomputable section

open ShenWork.Paper2 (IsPaper2ClassicalSolution)

/-! ## deriv↔RGrad bridge: `∂ₓ(lift v) = resolverGradReal` on the interior

The chemotaxis flux reads the genuine spatial derivative `deriv (lift (v t))` of
the solution's `v`.  Step (1) (`solution_v_eq_resolver_pointwise_unconditional`)
plus the resolver value-series form (`resolverR_apply_eq`) identify
`lift (v t)` with the resolver cosine value series on the OPEN interval `(0,1)`;
`solution_resolver_grad_hasDerivAt` differentiates that series to the gradient
series `resolverGradReal`.  Since `deriv` respects local equality on an open
neighbourhood, the two derivatives agree on `(0,1)`. -/

/-- On the open interior `(0,1)`, the genuine spatial derivative of the solution's
`v(·,t)` equals the resolver gradient series `resolverGradReal p (u t)`. -/
theorem solution_lift_v_deriv_eq_resolverGrad
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (intervalDomainLift (v t)) x = resolverGradReal p (u t) x := by
  classical
  -- The resolver cosine value series.
  set S : ℝ → ℝ := fun z : ℝ =>
    ∑' k : ℕ, (intervalNeumannResolverCoeff p (u t) k).re *
      Real.cos ((k : ℝ) * Real.pi * z) with hS
  -- `S` has derivative `resolverGradReal` at `x` (via the gradient bridge).
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  have hSderiv : HasDerivAt S (intervalNeumannResolverRGrad p (u t) ⟨x, hxIcc⟩) x := by
    rw [hS]; exact solution_resolver_grad_hasDerivAt hsol ht hxIcc
  -- `lift (v t)` agrees with `S` on the open `(0,1)` (step (1) + `resolverR_apply_eq`).
  have hEq : ∀ y ∈ Set.Ioo (0 : ℝ) 1, intervalDomainLift (v t) y = S y := by
    intro y hy
    have h1 := solution_v_eq_resolver_pointwise_unconditional hsol ht hy
    rw [resolverR_apply_eq] at h1
    rw [hS]; exact h1.symm
  -- `deriv` is local: agreement on the open nbhd `(0,1)` ⇒ equal derivatives.
  have hloc : intervalDomainLift (v t) =ᶠ[𝓝 x] S := by
    refine Filter.eventuallyEq_of_mem ?_ hEq
    exact IsOpen.mem_nhds isOpen_Ioo hx
  rw [hloc.deriv_eq, hSderiv.deriv, resolverGradReal_eq p (u t) ⟨x, hxIcc⟩]

/-- **(3) Chemotaxis flux integration-by-parts.**

For `φ, F : ℝ → ℝ` both `C¹` up to the closed interval `[0,1]` (`φ` has derivative
`φ'`, `F` has derivative `F'` at every point of `uIcc 0 1`, with both derivatives
interval-integrable), and with the flux `F` vanishing at the endpoints
(`F 0 = 0`, `F 1 = 0` — the genuine Neumann content of the chemotaxis flux, whose
`∂ₓv` factor is `0` at the boundary),

  `∫₀¹ φ(x) · F'(x) dx = − ∫₀¹ φ'(x) · F(x) dx`.

This is the single integration by parts `∫ φ·F' = [φ·F]₀¹ − ∫ φ'·F`, with the
boundary term killed by `F 0 = F 1 = 0`.  Proved by one application of Mathlib's
`integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`. -/
theorem intervalFluxByParts
    {φ φ' F F' : ℝ → ℝ}
    (hφ : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt φ (φ' x) x)
    (hF : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F (F' x) x)
    (hφ'int : IntervalIntegrable φ' MeasureTheory.volume 0 1)
    (hF'int : IntervalIntegrable F' MeasureTheory.volume 0 1)
    (hbc0 : F 0 = 0) (hbc1 : F 1 = 0) :
    (∫ x in (0 : ℝ)..1, φ x * F' x) = - ∫ x in (0 : ℝ)..1, φ' x * F x := by
  classical
  have hφ_cont : ContinuousOn φ (Set.uIcc (0 : ℝ) 1) :=
    fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have hF_cont : ContinuousOn F (Set.uIcc (0 : ℝ) 1) :=
    fun x hx => (hF x hx).continuousAt.continuousWithinAt
  have huIcc : Set.Ioo (min (0:ℝ) 1) (max 0 1) ⊆ Set.uIcc (0:ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1),
      min_eq_left (by norm_num : (0:ℝ) ≤ 1), max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
    exact fun x hx => Set.mem_Icc_of_Ioo hx
  have hφ_io : ∀ x ∈ Set.Ioo (min (0:ℝ) 1) (max 0 1), HasDerivAt φ (φ' x) x :=
    fun x hx => hφ x (huIcc hx)
  have hF_io : ∀ x ∈ Set.Ioo (min (0:ℝ) 1) (max 0 1), HasDerivAt F (F' x) x :=
    fun x hx => hF x (huIcc hx)
  -- IBP:  ∫ φ · F' = φ·F|₀¹ − ∫ φ' · F.
  have hIBP :
      (∫ x in (0:ℝ)..1, φ x * F' x) =
        φ 1 * F 1 - φ 0 * F 0 - ∫ x in (0:ℝ)..1, φ' x * F x :=
    integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hφ_cont hF_cont hφ_io hF_io hφ'int hF'int
  rw [hIBP, hbc0, hbc1]; ring

/-! ## (4) Flux-difference pointwise bound

The chemotaxis flux at a point is `flux = u · g / (1+v)^β` with `g = ∂ₓv`.  For two
solutions we bound `|flux₁ − flux₂|` by a constant times
`|u₁−u₂| + |g₁−g₂| + |v₁−v₂|`, using:

  * `(1+v)^β ≥ 1` (base `≥ 1`, exponent `β ≥ 0`), so `1/(1+v)^β ≤ 1`;
  * uniform L∞ bounds `|uᵢ| ≤ U`, `|gᵢ| ≤ G` on `[0,1]`;
  * the local Lipschitz of `s ↦ (1+s)^β` on the bounded positive range of `v`.

We isolate the pure algebraic estimate here (in terms of abstract bounded reals),
then specialise to the lift values. -/

/-- **(4) Algebraic flux-difference bound.**

Write `flux = a · g · q` where `q = 1/(1+v)^β ∈ (0,1]` (since `1+v ≥ 1`, `β ≥ 0`).
With `|aᵢ| ≤ U`, `|gᵢ| ≤ G`, `0 < qᵢ ≤ 1`, and the quotient `q` Lipschitz in `v`
with constant `Lq` on the relevant range (`|q₁ − q₂| ≤ Lq · |v₁ − v₂|`),

  `|a₁ g₁ q₁ − a₂ g₂ q₂|
     ≤ |a₁ − a₂| + U · |g₁ − g₂| + U·G·Lq · |v₁ − v₂|`.

(Telescoping `a₁g₁q₁ − a₂g₂q₂ = (a₁−a₂)g₁q₁ + a₂(g₁−g₂)q₁ + a₂g₂(q₁−q₂)` and
bounding each factor.) -/
theorem flux_diff_pointwise_bound
    {a₁ a₂ g₁ g₂ q₁ q₂ v₁ v₂ U G Lq : ℝ}
    (ha₁ : |a₁| ≤ U) (ha₂ : |a₂| ≤ U)
    (hg₁ : |g₁| ≤ G) (hg₂ : |g₂| ≤ G)
    (hq₁0 : 0 ≤ q₁) (hq₁1 : q₁ ≤ 1) (hq₂0 : 0 ≤ q₂) (hq₂1 : q₂ ≤ 1)
    (hUnn : 0 ≤ U) (hGnn : 0 ≤ G)
    (hqLip : |q₁ - q₂| ≤ Lq * |v₁ - v₂|) :
    |a₁ * g₁ * q₁ - a₂ * g₂ * q₂|
      ≤ G * |a₁ - a₂| + U * |g₁ - g₂| + U * G * Lq * |v₁ - v₂| := by
  have htel : a₁ * g₁ * q₁ - a₂ * g₂ * q₂
      = (a₁ - a₂) * g₁ * q₁ + a₂ * (g₁ - g₂) * q₁ + a₂ * g₂ * (q₁ - q₂) := by ring
  rw [htel]
  refine (abs_add_three _ _ _).trans ?_
  refine add_le_add (add_le_add ?_ ?_) ?_
  · -- |(a₁−a₂) g₁ q₁| ≤ G·|a₁−a₂|
    rw [abs_mul, abs_mul]
    have h1 : |a₁ - a₂| * |g₁| * |q₁| ≤ |a₁ - a₂| * G * 1 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hg₁ (abs_nonneg _)
      · rw [abs_of_nonneg hq₁0]; exact hq₁1
      · exact abs_nonneg _
      · positivity
    calc |a₁ - a₂| * |g₁| * |q₁| ≤ |a₁ - a₂| * G * 1 := h1
      _ = G * |a₁ - a₂| := by ring
  · -- |a₂ (g₁−g₂) q₁| ≤ U·|g₁−g₂|
    rw [abs_mul, abs_mul]
    have h1 : |a₂| * |g₁ - g₂| * |q₁| ≤ U * |g₁ - g₂| * 1 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right ha₂ (abs_nonneg _)
      · rw [abs_of_nonneg hq₁0]; exact hq₁1
      · exact abs_nonneg _
      · positivity
    calc |a₂| * |g₁ - g₂| * |q₁| ≤ U * |g₁ - g₂| * 1 := h1
      _ = U * |g₁ - g₂| := by ring
  · -- |a₂ g₂ (q₁−q₂)| ≤ U·G·Lq·|v₁−v₂|
    rw [abs_mul, abs_mul]
    calc |a₂| * |g₂| * |q₁ - q₂|
        ≤ U * G * (Lq * |v₁ - v₂|) := by
          apply mul_le_mul
          · exact mul_le_mul ha₂ hg₂ (abs_nonneg _) hUnn
          · exact hqLip
          · exact abs_nonneg _
          · positivity
      _ = U * G * Lq * |v₁ - v₂| := by ring

end

end ShenWork.Paper2
