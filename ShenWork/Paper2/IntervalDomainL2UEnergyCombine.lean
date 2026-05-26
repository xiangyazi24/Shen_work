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

/-- `resolverGradReal p u 0 = 0`: every term carries `sin(kπ·0) = 0`. -/
theorem resolverGradReal_zero (p : CM2Params) (u : intervalDomainPoint → ℝ) :
    resolverGradReal p u 0 = 0 := by
  unfold resolverGradReal
  have : (fun k : ℕ => (intervalNeumannResolverCoeff p u k).re *
      (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * (0:ℝ)))) = fun _ => 0 := by
    funext k; simp
  rw [this, tsum_zero]

/-- `resolverGradReal p u 1 = 0`: every term carries `sin(kπ·1) = sin(kπ) = 0`. -/
theorem resolverGradReal_one (p : CM2Params) (u : intervalDomainPoint → ℝ) :
    resolverGradReal p u 1 = 0 := by
  unfold resolverGradReal
  have : (fun k : ℕ => (intervalNeumannResolverCoeff p u k).re *
      (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * (1:ℝ)))) = fun _ => 0 := by
    funext k
    have hsin : Real.sin ((k : ℝ) * Real.pi * 1) = 0 := by
      rw [mul_one]; exact Real.sin_nat_mul_pi k
    rw [hsin]; ring
  rw [this, tsum_zero]

/-- On the CLOSED interval `[0,1]`, `deriv(lift v) = resolverGradReal p (u t)`.
Interior agreement is `solution_lift_v_deriv_eq_resolverGrad`; at the endpoints both
sides are `0` (Neumann: `deriv(lift v) 0 = deriv(lift v) 1 = 0` from conjunct 7, and
`resolverGradReal` vanishes at `0,1` since every sine term does). -/
theorem solution_lift_v_deriv_eq_resolverGrad_Icc
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    deriv (intervalDomainLift (v t)) x = resolverGradReal p (u t) x := by
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · -- `x = 0`
    subst hx0
    have hbc0 : deriv (intervalDomainLift (v t)) 0 = 0 :=
      (hsol.regularity.2.2.2.2.2.2.1 t ht).2.2.1
    rw [hbc0, resolverGradReal_zero]
  · rcases eq_or_lt_of_le hx.2 with hx1 | hx1
    · -- `x = 1`
      subst hx1
      have hbc1 : deriv (intervalDomainLift (v t)) 1 = 0 :=
        (hsol.regularity.2.2.2.2.2.2.1 t ht).2.2.2
      rw [hbc1, resolverGradReal_one]
    · -- interior
      exact solution_lift_v_deriv_eq_resolverGrad hsol ht ⟨hx0, hx1⟩

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

/-! ## (A) helper bounds for the chemotaxis quotient `q = (1+v)^{-β}`

`q(v) = (1+v)^{-β}` for `v ≥ 0` (the positive solution range gives `lift(v t) ≥ 0`
since `v t` is a positive classical solution, but here we only need `v ≥ 0`,
equivalently `1+v ≥ 1`).  Two facts:

  * `q ∈ (0,1]`: base `1+v ≥ 1`, exponent `−β ≤ 0` ⇒ `(1+v)^{-β} ≤ 1`, and `> 0`;
  * `q` is `β`-Lipschitz in `v` on `v ≥ 0`: derivative `−β(1+v)^{-β-1}` has
    absolute value `β(1+v)^{-β-1} ≤ β` (since `1+v ≥ 1`, `-β-1 ≤ 0`). -/

/-- `(1+v)^{-β} ∈ (0,1]` for `v ≥ 0` and `β ≥ 0`. -/
theorem chemQuotient_mem_Ioc
    {β v : ℝ} (hβ : 0 ≤ β) (hv : 0 ≤ v) :
    0 < (1 + v) ^ (-β) ∧ (1 + v) ^ (-β) ≤ 1 := by
  have hbase : (1 : ℝ) ≤ 1 + v := by linarith
  have hbase_pos : (0 : ℝ) < 1 + v := by linarith
  refine ⟨Real.rpow_pos_of_pos hbase_pos _, ?_⟩
  -- `(1+v)^{-β} ≤ 1^{-β} = 1` since `1+v ≥ 1` and exponent `-β ≤ 0`.
  have := Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < 1) hbase
    (by linarith : -β ≤ 0)
  simpa using this

/-- **(A)-helper (iii): `β`-Lipschitz of `s ↦ (1+s)^{-β}` on `s ≥ 0`.**
For `v₁, v₂ ≥ 0`,
`|(1+v₁)^{-β} − (1+v₂)^{-β}| ≤ β · |v₁ − v₂|`.
MVT on the convex `Icc 0 (max v₁ v₂) ⊆ [0,∞)`; the derivative
`−β·(1+s)^{-β-1}` has norm `β·(1+s)^{-β-1} ≤ β` there (`1+s ≥ 1`, exponent `≤ 0`). -/
theorem chemQuotient_lipschitz
    {β : ℝ} (hβ : 0 ≤ β) {v₁ v₂ : ℝ} (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) :
    |(1 + v₁) ^ (-β) - (1 + v₂) ^ (-β)| ≤ β * |v₁ - v₂| := by
  set M : ℝ := max v₁ v₂ with hM
  have hv₁M : v₁ ∈ Set.Icc (0:ℝ) M := ⟨hv₁, le_max_left _ _⟩
  have hv₂M : v₂ ∈ Set.Icc (0:ℝ) M := ⟨hv₂, le_max_right _ _⟩
  have hconv : Convex ℝ (Set.Icc (0:ℝ) M) := convex_Icc 0 M
  -- derivative on `Icc 0 M`.
  have hderiv : ∀ s ∈ Set.Icc (0:ℝ) M,
      HasDerivWithinAt (fun y : ℝ => (1 + y) ^ (-β))
        (-β * (1 + s) ^ (-β - 1)) (Set.Icc (0:ℝ) M) s := by
    intro s hs
    have hbase_pos : (0:ℝ) < 1 + s := by have := hs.1; linarith
    have hb : HasDerivAt (fun y : ℝ => (1 + y)) (1 : ℝ) s := by
      simpa using (hasDerivAt_id s).const_add (1 : ℝ)
    have hrp : HasDerivAt (fun y : ℝ => (1 + y) ^ (-β))
        ((-β) * (1 + s) ^ (-β - 1) * 1) s :=
      (Real.hasDerivAt_rpow_const (p := -β) (Or.inl (ne_of_gt hbase_pos))).comp s hb
    have : (-β) * (1 + s) ^ (-β - 1) * 1 = -β * (1 + s) ^ (-β - 1) := by ring
    rw [this] at hrp
    exact hrp.hasDerivWithinAt
  -- derivative norm bound `≤ β` on `Icc 0 M`.
  have hbound : ∀ s ∈ Set.Icc (0:ℝ) M, ‖-β * (1 + s) ^ (-β - 1)‖ ≤ β := by
    intro s hs
    have hbase : (1:ℝ) ≤ 1 + s := by have := hs.1; linarith
    have hbase_pos : (0:ℝ) < 1 + s := by linarith
    have hle1 : (1 + s) ^ (-β - 1) ≤ 1 := by
      have := Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < 1) hbase
        (by linarith : -β - 1 ≤ 0)
      simpa using this
    have hpos : (0:ℝ) ≤ (1 + s) ^ (-β - 1) := (Real.rpow_pos_of_pos hbase_pos _).le
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hβ, abs_of_nonneg hpos]
    calc β * (1 + s) ^ (-β - 1) ≤ β * 1 := mul_le_mul_of_nonneg_left hle1 hβ
      _ = β := by ring
  have hmvt := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hv₂M hv₁M
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  exact hmvt

/-! ## (A) uniform L∞ helper bounds on `[0,1]` -/

/-- **(A)-helper (i): `resolverGradReal p (u τ)` is continuous on ℝ** (exported from
the inline argument inside `static_v_grad_L2_le_Eu`).  Uniform-limit of continuous
terms under the summable gradient majorant `∑ₖ |coeffₖ.re|·kπ` from source decay. -/
theorem resolverGradReal_continuous
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    Continuous (fun x : ℝ => resolverGradReal p (u τ) x) := by
  have hdecay := sourceCoeffQuadraticDecay_of_solution hsol hτ
  have hmaj := resolverGrad_majorant_summable_of_sourceDecay hdecay.C_nonneg hdecay.decay
  refine continuous_tsum (fun k => ?_) hmaj (fun k x => ?_)
  · exact continuous_const.mul (continuous_const.mul
      (Real.continuous_sin.comp (by fun_prop)))
  · rw [Real.norm_eq_abs, abs_mul]
    have hsin : |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x))|
        ≤ (k : ℝ) * Real.pi := by
      rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ)),
        abs_of_nonneg Real.pi_pos.le]
      have h1 : |Real.sin ((k : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_sin_le_one _
      nlinarith [mul_nonneg (Nat.cast_nonneg k) Real.pi_pos.le, abs_nonneg
        (Real.sin ((k : ℝ) * Real.pi * x)), h1]
    exact mul_le_mul_of_nonneg_left hsin (abs_nonneg _)

/-- The termwise SECOND-derivative cosine series of the resolver gradient:
`z ↦ ∑ₖ (v̂_k).re · (−(kπ)² · cos(kπ z))`.  This is the derivative of
`resolverGradReal p u` once the gradient `ℓ¹` (second-derivative) majorant
`∑ₖ |(v̂_k).re|·(kπ)²` is summable. -/
noncomputable def resolverGrad2Real (p : CM2Params) (u : intervalDomainPoint → ℝ) (z : ℝ) : ℝ :=
  ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re *
    (-(((k : ℝ) * Real.pi) ^ 2) * Real.cos ((k : ℝ) * Real.pi * z))

/-- **(B)-helper: `resolverGrad2Real p (u τ)` is continuous on ℝ.**  Uniform-limit
of continuous terms under the summable second-derivative majorant
`∑ₖ |(v̂_k).re|·(kπ)²` (from source quadratic decay). -/
theorem resolverGrad2Real_continuous
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    Continuous (fun z : ℝ => resolverGrad2Real p (u τ) z) := by
  have hdecay := sourceCoeffQuadraticDecay_of_solution hsol hτ
  have hmaj :=
    ShenWork.IntervalResolverGradientBridge.resolverGrad2_majorant_summable_of_sourceDecay
      hdecay.C_nonneg hdecay.decay
  refine continuous_tsum (fun k => ?_) hmaj (fun k z => ?_)
  · exact continuous_const.mul (continuous_const.mul
      (Real.continuous_cos.comp (by fun_prop)))
  · rw [Real.norm_eq_abs, abs_mul]
    have hcos : |(-(((k : ℝ) * Real.pi) ^ 2) * Real.cos ((k : ℝ) * Real.pi * z))|
        ≤ ((k : ℝ) * Real.pi) ^ 2 := by
      rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((k:ℝ) * Real.pi) ^ 2)]
      have h1 : |Real.cos ((k : ℝ) * Real.pi * z)| ≤ 1 := Real.abs_cos_le_one _
      nlinarith [sq_nonneg ((k:ℝ) * Real.pi), abs_nonneg (Real.cos ((k : ℝ) * Real.pi * z)), h1]
    exact mul_le_mul_of_nonneg_left hcos (abs_nonneg _)

/-- **(B): `resolverGradReal p (u τ)` has derivative `resolverGrad2Real p (u τ)` at
every real point**, for a positive classical solution.  Via the second-derivative
bridge `resolverGrad_hasDerivAt_grad2` fed the summable `∑ |(v̂_k).re|·(kπ)²` from
source decay.  (`resolverGradReal` is definitionally the sine series.) -/
theorem resolverGradReal_hasDerivAt
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) (z : ℝ) :
    HasDerivAt (fun w : ℝ => resolverGradReal p (u τ) w) (resolverGrad2Real p (u τ) z) z := by
  have hdecay := sourceCoeffQuadraticDecay_of_solution hsol hτ
  have hmaj :=
    ShenWork.IntervalResolverGradientBridge.resolverGrad2_majorant_summable_of_sourceDecay
      hdecay.C_nonneg hdecay.decay
  -- `resolverGradReal p (u τ)` is definitionally the sine series; `resolverGrad2Real`
  -- is the termwise second-derivative cosine series — exactly the bridge conclusion.
  exact ShenWork.IntervalResolverGradientBridge.resolverGrad_hasDerivAt_grad2 hmaj z

/-- **(B): `resolverGradReal p (u τ)` is `C¹` on `Icc 0 1`.**  It is differentiable
everywhere with derivative `resolverGrad2Real p (u τ)` (a uniformly-convergent
continuous series), so by `contDiff_one_iff_deriv` it is `C¹` on all of ℝ, hence on
the closed `[0,1]`.  This is the missing closed-interval input for the flux factor
`∂ₓ(lift v) = resolverGradReal` of `flux_contDiffOn_Icc`. -/
theorem resolverGradReal_contDiffOn_Icc
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    ContDiffOn ℝ 1 (fun x : ℝ => resolverGradReal p (u τ) x) (Set.Icc (0:ℝ) 1) := by
  have hderiv : ∀ z : ℝ,
      HasDerivAt (fun w : ℝ => resolverGradReal p (u τ) w) (resolverGrad2Real p (u τ) z) z :=
    fun z => resolverGradReal_hasDerivAt hsol hτ z
  have hdiff : Differentiable ℝ (fun x : ℝ => resolverGradReal p (u τ) x) :=
    fun z => (hderiv z).differentiableAt
  -- `deriv (resolverGradReal …) = resolverGrad2Real …`, which is continuous.
  have hderiv_eq : deriv (fun w : ℝ => resolverGradReal p (u τ) w)
      = fun z => resolverGrad2Real p (u τ) z := by
    funext z; exact (hderiv z).deriv
  have hcontD : Continuous (deriv (fun w : ℝ => resolverGradReal p (u τ) w)) := by
    rw [hderiv_eq]; exact resolverGrad2Real_continuous hsol hτ
  have hC1 : ContDiff ℝ 1 (fun x : ℝ => resolverGradReal p (u τ) x) :=
    contDiff_one_iff_deriv.2 ⟨hdiff, hcontD⟩
  exact hC1.contDiffOn

/-- **(A)-helper (i): uniform L∞ bound on `resolverGradReal p (u τ)` over `[0,1]`.**
Continuity on the compact `[0,1]`. -/
theorem resolverGradReal_bounded
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    ∃ G : ℝ, 0 ≤ G ∧
      ∀ x ∈ Set.Icc (0:ℝ) 1, |resolverGradReal p (u τ) x| ≤ G := by
  have hcont : Continuous (fun x : ℝ => resolverGradReal p (u τ) x) :=
    resolverGradReal_continuous hsol hτ
  have hne : (Set.Icc (0:ℝ) 1).Nonempty := ⟨0, by constructor <;> norm_num⟩
  obtain ⟨G, hG⟩ :=
    (isCompact_Icc.image_of_continuousOn
      (hcont.continuousOn.abs)).bddAbove
  refine ⟨max G 0, le_max_right _ _, fun x hx => ?_⟩
  exact le_trans (hG ⟨x, hx, rfl⟩) (le_max_left _ _)

/-- **(A)-helper (ii): uniform L∞ bound on `intervalDomainLift (v τ)` over `[0,1]`.**
Conjunct-7 `C²` ⇒ continuous on the compact `[0,1]` ⇒ bounded. -/
theorem lift_v_bounded
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ Set.Icc (0:ℝ) 1, |intervalDomainLift (v τ) x| ≤ M := by
  have hcont : ContinuousOn (intervalDomainLift (v τ)) (Set.Icc (0:ℝ) 1) :=
    ((hsol.regularity.2.2.2.2.2.2.1 τ hτ).2.1).continuousOn
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc.image_of_continuousOn hcont.abs).bddAbove
  refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
  exact le_trans (hM ⟨x, hx, rfl⟩) (le_max_left _ _)

/-- **(A)-helper: uniform L∞ bound on `intervalDomainLift (u τ)` over `[0,1]`.**
(`lift_u_bounded_pos` gives a two-sided positive bound; here we just need the upper
absolute bound.) -/
theorem lift_u_bounded
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    ∃ U : ℝ, 0 ≤ U ∧
      ∀ x ∈ Set.Icc (0:ℝ) 1, |intervalDomainLift (u τ) x| ≤ U := by
  obtain ⟨δ, M, _, hb⟩ := lift_u_bounded_pos hsol hτ
  refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
  have hmem := hb x hx
  have hpos : 0 < intervalDomainLift (u τ) x := solution_lift_pos hsol hτ x hx
  rw [abs_of_pos hpos]
  exact le_trans hmem.2 (le_max_left _ _)

/-! ## (A) The L²-integrated flux-difference bound

The chemotaxis flux at `(τ, y)` is
`fluxᵢ(τ,y) = lift(uᵢ τ) y · deriv(lift(vᵢ τ)) y / (1 + lift(vᵢ τ) y)^β`
(so that `chemDivᵢ = ∂ₓ(fluxᵢ) = intervalDomainChemotaxisDiv p (uᵢ τ) (vᵢ τ)`).  We
prove `∫₀¹ (flux₁ − flux₂)² ≤ C · E_u(τ)`.

The bound needs `1 + lift(vᵢ τ) > 0` on `[0,1]`; we record the (physical-model)
nonnegativity of the chemical concentration `vᵢ ≥ 0` on `[0,1]` as the named
hypotheses `hv₁nn`/`hv₂nn` (it is exactly `q = (1+v)^{-β} ∈ (0,1]`, and the genuine
content of the resolver of a positive source `ν u^γ` under the maximum principle —
a fact not carried by the abstract `IsPaper2ClassicalSolution`).  Everything else is
unconditional. -/

/-- The chemotaxis flux of a solution, as a plain real function on ℝ. -/
def intervalFlux (p : CM2Params) (u v : intervalDomainPoint → ℝ) (y : ℝ) : ℝ :=
  intervalDomainLift u y * deriv (intervalDomainLift v) y /
    (1 + intervalDomainLift v y) ^ p.β

/-- The continuous interior representative of the flux: `deriv(lift v)` replaced by
`resolverGradReal` and the quotient written as a product with `(1+v)^{-β}`.  Equal to
`intervalFlux` on the open interior `(0,1)` (where `deriv(lift v) = resolverGradReal`
and `a/b^β = a·b^{-β}` for `b > 0`). -/
def intervalFluxRepr (p : CM2Params) (u v : intervalDomainPoint → ℝ) (y : ℝ) : ℝ :=
  intervalDomainLift u y * resolverGradReal p u y *
    (1 + intervalDomainLift v y) ^ (-p.β)

/-- **Nonnegativity of the lifted chemical concentration, for free from a solution.**
A paper solution is a positive classical solution: `v ≥ 0` on the closed domain
(`IsPaper2ClassicalSolution.v_nonneg`).  For `x ∈ [0,1]` the lift `intervalDomainLift
(v τ) x` equals `v τ ⟨x, _⟩`, hence `≥ 0`.  This discharges every `hvnn`-style
hypothesis without an extra assumption. -/
theorem solution_lift_v_nonneg_Icc
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ intervalDomainLift (v τ) x := by
  intro x hx
  simp only [intervalDomainLift, hx, dif_pos]
  exact hsol.v_nonneg hτ.1 hτ.2

/-- Interior version of `solution_lift_v_nonneg_Icc` (`x ∈ (0,1) ⊆ [0,1]`). -/
theorem solution_lift_v_nonneg_Ioo
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    ∀ x ∈ Set.Ioo (0:ℝ) 1, 0 ≤ intervalDomainLift (v τ) x :=
  fun x hx => solution_lift_v_nonneg_Icc hsol hτ x (Set.Ioo_subset_Icc_self hx)

/-- On the interior `(0,1)`, the flux equals its continuous representative.  Uses
`solution_lift_v_deriv_eq_resolverGrad` (interior deriv↔RGrad) and
`a / b^β = a · b^{-β}` (valid since `1+v > 0`). -/
theorem intervalFlux_eq_repr_interior
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    (hvnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ intervalDomainLift (v τ) x)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    intervalFlux p (u τ) (v τ) y = intervalFluxRepr p (u τ) (v τ) y := by
  have hyIcc : y ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hy
  have hgrad := solution_lift_v_deriv_eq_resolverGrad hsol hτ hy
  have hbase_pos : (0:ℝ) < 1 + intervalDomainLift (v τ) y := by
    have := hvnn y hyIcc; linarith
  unfold intervalFlux intervalFluxRepr
  rw [hgrad, div_eq_mul_inv, ← Real.rpow_neg hbase_pos.le]

/-- `intervalFluxRepr` is continuous on `[0,1]` (each factor: `lift u` continuous;
`resolverGradReal` continuous; `(1+lift v)^{-β}` continuous since `1+lift v > 0`). -/
theorem intervalFluxRepr_continuousOn
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    (hvnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ intervalDomainLift (v τ) x) :
    ContinuousOn (intervalFluxRepr p (u τ) (v τ)) (Set.Icc (0:ℝ) 1) := by
  have hu : ContinuousOn (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1) :=
    ((hsol.regularity.2.2.2.2.2.2.1 τ hτ).1.1).continuousOn
  have hg : ContinuousOn (fun x => resolverGradReal p (u τ) x) (Set.Icc (0:ℝ) 1) :=
    (resolverGradReal_continuous hsol hτ).continuousOn
  have hv : ContinuousOn (intervalDomainLift (v τ)) (Set.Icc (0:ℝ) 1) :=
    ((hsol.regularity.2.2.2.2.2.2.1 τ hτ).2.1).continuousOn
  have hbase : ContinuousOn (fun x => 1 + intervalDomainLift (v τ) x) (Set.Icc (0:ℝ) 1) :=
    continuousOn_const.add hv
  have hq : ContinuousOn (fun x => (1 + intervalDomainLift (v τ) x) ^ (-p.β))
      (Set.Icc (0:ℝ) 1) :=
    hbase.rpow_const (fun x hx => Or.inl (by have := hvnn x hx; linarith))
  exact (hu.mul hg).mul hq

/-- The `u`-difference integral equals `E_u`: `∫₀¹(lift u₁ − lift u₂)² = E_u(τ)`. -/
theorem lift_u_diff_sq_integral_eq_Eu
    (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) :
    (∫ y in (0:ℝ)..1,
        (intervalDomainLift (u₁ τ) y - intervalDomainLift (u₂ τ) y) ^ 2)
      = intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by
  rw [intervalDomainL2UEnergy_eq_integral]
  refine intervalIntegral.integral_congr (fun y _ => ?_)
  by_cases hy : y ∈ Set.Icc (0:ℝ) 1
  · simp only [intervalDomainLift, hy, dif_pos]
  · simp [intervalDomainLift, hy]

/-- **(A) L²-integrated flux-difference bound.**
For two positive classical solutions and `τ ∈ (0,T₁) ∩ (0,T₂)`, with the chemical
concentrations nonnegative on `[0,1]` (`hv₁nn`/`hv₂nn`),

  `∫₀¹ (flux₁(τ,y) − flux₂(τ,y))² dy ≤ C · E_u(τ)`,

where `fluxᵢ = lift(uᵢ)·∂ₓ(lift vᵢ)/(1+lift vᵢ)^β` and
`E_u(τ) = ∫₀¹ (lift(u₁−u₂))²`.  The constant is
`C = 3·(G² + U²·C_grad + (U·G·β)²·C_val)` with `U,G` the uniform L∞ bounds on
`lift uᵢ` / `resolverGradReal(uᵢ)`, and `C_grad,C_val` from the static `v`-control
lemmas.  Route: square the proved pointwise `flux_diff_pointwise_bound`
(`(X+Y+Z)² ≤ 3(X²+Y²+Z²)`), integrate over the interior, and bound the three
resulting integrals by `static_v_grad_L2_le_Eu`, `static_v_value_L2_le_Eu`, and the
identity `∫(lift u₁−lift u₂)² = E_u`. -/
theorem flux_diff_L2_le_Eu
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {τ : ℝ} (hτ₁ : τ ∈ Set.Ioo (0 : ℝ) T₁) (hτ₂ : τ ∈ Set.Ioo (0 : ℝ) T₂)
    (hv₁nn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ intervalDomainLift (v₁ τ) x)
    (hv₂nn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ intervalDomainLift (v₂ τ) x) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∫ y in (0:ℝ)..1,
        (intervalFlux p (u₁ τ) (v₁ τ) y - intervalFlux p (u₂ τ) (v₂ τ) y) ^ 2)
        ≤ C * intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by
  classical
  set Eu : ℝ := intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ with hEu
  have hEu_nn : 0 ≤ Eu := intervalDomainClassicalL2DifferenceEnergyU_nonneg u₁ u₂ τ
  -- uniform L∞ bounds `U` (on both `lift uᵢ`) and `G` (on both `resolverGradReal`).
  obtain ⟨U₁, hU₁nn, hU₁⟩ := lift_u_bounded hsol₁ hτ₁
  obtain ⟨U₂, hU₂nn, hU₂⟩ := lift_u_bounded hsol₂ hτ₂
  obtain ⟨G₁, hG₁nn, hG₁⟩ := resolverGradReal_bounded hsol₁ hτ₁
  obtain ⟨G₂, hG₂nn, hG₂⟩ := resolverGradReal_bounded hsol₂ hτ₂
  set U : ℝ := max U₁ U₂ with hUdef
  set G : ℝ := max G₁ G₂ with hGdef
  have hUnn : 0 ≤ U := le_trans hU₁nn (le_max_left _ _)
  have hGnn : 0 ≤ G := le_trans hG₁nn (le_max_left _ _)
  have hβnn : 0 ≤ p.β := p.hβ
  -- pointwise bound on the interior `(0,1)` of the (continuous representative) flux.
  have hpt : ∀ y ∈ Set.Ioo (0:ℝ) 1,
      |intervalFluxRepr p (u₁ τ) (v₁ τ) y - intervalFluxRepr p (u₂ τ) (v₂ τ) y|
        ≤ G * |intervalDomainLift (u₁ τ) y - intervalDomainLift (u₂ τ) y|
          + U * |resolverGradReal p (u₁ τ) y - resolverGradReal p (u₂ τ) y|
          + U * G * p.β
              * |intervalDomainLift (v₁ τ) y - intervalDomainLift (v₂ τ) y| := by
    intro y hy
    have hyIcc : y ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hy
    -- factor bounds.
    have ha₁ : |intervalDomainLift (u₁ τ) y| ≤ U :=
      le_trans (hU₁ y hyIcc) (le_max_left _ _)
    have ha₂ : |intervalDomainLift (u₂ τ) y| ≤ U :=
      le_trans (hU₂ y hyIcc) (le_max_right _ _)
    have hg₁ : |resolverGradReal p (u₁ τ) y| ≤ G :=
      le_trans (hG₁ y hyIcc) (le_max_left _ _)
    have hg₂ : |resolverGradReal p (u₂ τ) y| ≤ G :=
      le_trans (hG₂ y hyIcc) (le_max_right _ _)
    have hq₁ := chemQuotient_mem_Ioc hβnn (hv₁nn y hyIcc)
    have hq₂ := chemQuotient_mem_Ioc hβnn (hv₂nn y hyIcc)
    have hqLip := chemQuotient_lipschitz hβnn (hv₁nn y hyIcc) (hv₂nn y hyIcc)
    -- the algebraic flux-difference bound on the representative.
    have := flux_diff_pointwise_bound
      (a₁ := intervalDomainLift (u₁ τ) y) (a₂ := intervalDomainLift (u₂ τ) y)
      (g₁ := resolverGradReal p (u₁ τ) y) (g₂ := resolverGradReal p (u₂ τ) y)
      (q₁ := (1 + intervalDomainLift (v₁ τ) y) ^ (-p.β))
      (q₂ := (1 + intervalDomainLift (v₂ τ) y) ^ (-p.β))
      (v₁ := intervalDomainLift (v₁ τ) y) (v₂ := intervalDomainLift (v₂ τ) y)
      (U := U) (G := G) (Lq := p.β)
      ha₁ ha₂ hg₁ hg₂ hq₁.1.le hq₁.2 hq₂.1.le hq₂.2 hUnn hGnn hqLip
    simpa only [intervalFluxRepr] using this
  -- square the pointwise bound: `(Δflux)² ≤ 3(G²Δa² + U²Δg² + (UGβ)²Δv²)` on `(0,1)`.
  set a := fun y => (intervalDomainLift (u₁ τ) y - intervalDomainLift (u₂ τ) y) with ha
  set gg := fun y => (resolverGradReal p (u₁ τ) y - resolverGradReal p (u₂ τ) y) with hgg
  set vv := fun y => (intervalDomainLift (v₁ τ) y - intervalDomainLift (v₂ τ) y) with hvv
  have hsq : ∀ y ∈ Set.Ioo (0:ℝ) 1,
      (intervalFluxRepr p (u₁ τ) (v₁ τ) y - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2
        ≤ 3 * (G^2 * (a y)^2 + U^2 * (gg y)^2 + (U*G*p.β)^2 * (vv y)^2) := by
    intro y hy
    have hb := hpt y hy
    set X := G * |a y| with hX
    set Y := U * |gg y| with hY
    set Z := U * G * p.β * |vv y| with hZ
    have hXnn : 0 ≤ X := by rw [hX]; positivity
    have hYnn : 0 ≤ Y := by rw [hY]; positivity
    have hZnn : 0 ≤ Z := by rw [hZ]; positivity
    have hb' : |intervalFluxRepr p (u₁ τ) (v₁ τ) y - intervalFluxRepr p (u₂ τ) (v₂ τ) y|
        ≤ X + Y + Z := hb
    have hsq0 : (intervalFluxRepr p (u₁ τ) (v₁ τ) y
          - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2
        ≤ (X + Y + Z) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb' 2
    refine hsq0.trans ?_
    have hexp : (X + Y + Z) ^ 2 ≤ 3 * (X^2 + Y^2 + Z^2) := by nlinarith [sq_nonneg (X-Y), sq_nonneg (Y-Z), sq_nonneg (X-Z)]
    refine hexp.trans ?_
    have hXsq : X^2 = G^2 * (a y)^2 := by rw [hX]; rw [mul_pow, sq_abs]
    have hYsq : Y^2 = U^2 * (gg y)^2 := by rw [hY]; rw [mul_pow, sq_abs]
    have hZsq : Z^2 = (U*G*p.β)^2 * (vv y)^2 := by rw [hZ]; rw [mul_pow, sq_abs]
    rw [hXsq, hYsq, hZsq]
  -- the LHS flux integral equals the representative integral (interior agreement).
  have hflux_eq : (∫ y in (0:ℝ)..1,
        (intervalFlux p (u₁ τ) (v₁ τ) y - intervalFlux p (u₂ τ) (v₂ τ) y) ^ 2)
      = ∫ y in (0:ℝ)..1,
        (intervalFluxRepr p (u₁ τ) (v₁ τ) y - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2 := by
    refine intervalIntegral.integral_congr_ae ?_
    -- equality holds on `Ioo 0 1 = Ι 0 1 \ {1}` (the endpoint `1` is null).
    have hnull : volume ({(1:ℝ)} : Set ℝ) = 0 := Real.volume_singleton
    refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    push_neg at hy
    obtain ⟨hyIoc0, hne⟩ := hy
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hyIoc0
    simp only [Set.mem_singleton_iff]
    by_contra hy1
    have hyIoo : y ∈ Set.Ioo (0:ℝ) 1 := ⟨hyIoc0.1, lt_of_le_of_ne hyIoc0.2 hy1⟩
    exact hne (by rw [intervalFlux_eq_repr_interior hsol₁ hτ₁ hv₁nn hyIoo,
      intervalFlux_eq_repr_interior hsol₂ hτ₂ hv₂nn hyIoo])
  -- integrability of the representative-difference square (continuous on `[0,1]`).
  have hcontR : ContinuousOn
      (fun y => (intervalFluxRepr p (u₁ τ) (v₁ τ) y
        - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2) (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (((intervalFluxRepr_continuousOn hsol₁ hτ₁ hv₁nn).sub
      (intervalFluxRepr_continuousOn hsol₂ hτ₂ hv₂nn)).pow 2)
  have hintR : IntervalIntegrable
      (fun y => (intervalFluxRepr p (u₁ τ) (v₁ τ) y
        - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2) volume 0 1 :=
    hcontR.intervalIntegrable
  -- the three static integrals.
  obtain ⟨Cg, hCgnn, hCg⟩ := static_v_grad_L2_le_Eu hsol₁ hsol₂ hτ₁ hτ₂
  obtain ⟨Cv, hCvnn, hCv⟩ := static_v_value_L2_le_Eu hsol₁ hsol₂ hτ₁ hτ₂
  -- integrability of the three squared difference integrands (continuous on `[0,1]`).
  have hcont_u₁ : ContinuousOn (intervalDomainLift (u₁ τ)) (Set.Icc (0:ℝ) 1) :=
    ((hsol₁.regularity.2.2.2.2.2.2.1 τ hτ₁).1.1).continuousOn
  have hcont_u₂ : ContinuousOn (intervalDomainLift (u₂ τ)) (Set.Icc (0:ℝ) 1) :=
    ((hsol₂.regularity.2.2.2.2.2.2.1 τ hτ₂).1.1).continuousOn
  have hcont_v₁ : ContinuousOn (intervalDomainLift (v₁ τ)) (Set.Icc (0:ℝ) 1) :=
    ((hsol₁.regularity.2.2.2.2.2.2.1 τ hτ₁).2.1).continuousOn
  have hcont_v₂ : ContinuousOn (intervalDomainLift (v₂ τ)) (Set.Icc (0:ℝ) 1) :=
    ((hsol₂.regularity.2.2.2.2.2.2.1 τ hτ₂).2.1).continuousOn
  have hcg₁ := resolverGradReal_continuous hsol₁ hτ₁
  have hcg₂ := resolverGradReal_continuous hsol₂ hτ₂
  have hint_a : IntervalIntegrable (fun y => (a y)^2) volume 0 1 := by
    rw [ha]
    have : ContinuousOn (fun y => (intervalDomainLift (u₁ τ) y
        - intervalDomainLift (u₂ τ) y)^2) (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact (hcont_u₁.sub hcont_u₂).pow 2
    exact this.intervalIntegrable
  have hint_g : IntervalIntegrable (fun y => (gg y)^2) volume 0 1 := by
    rw [hgg]; exact (((hcg₁.sub hcg₂).pow 2)).intervalIntegrable _ _
  have hint_v : IntervalIntegrable (fun y => (vv y)^2) volume 0 1 := by
    rw [hvv]
    have : ContinuousOn (fun y => (intervalDomainLift (v₁ τ) y
        - intervalDomainLift (v₂ τ) y)^2) (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact (hcont_v₁.sub hcont_v₂).pow 2
    exact this.intervalIntegrable
  set RHSfun := fun y => 3 * (G^2 * (a y)^2 + U^2 * (gg y)^2 + (U*G*p.β)^2 * (vv y)^2)
    with hRHSfun
  have hint_RHS : IntervalIntegrable RHSfun volume 0 1 := by
    rw [hRHSfun]
    exact (((hint_a.const_mul (G^2)).add (hint_g.const_mul (U^2))).add
      (hint_v.const_mul ((U*G*p.β)^2))).const_mul 3
  -- integrate the squared pointwise bound on `(0,1)` (= a.e. on `[0,1]`).
  have hmono : (∫ y in (0:ℝ)..1,
        (intervalFluxRepr p (u₁ τ) (v₁ τ) y
          - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2)
      ≤ ∫ y in (0:ℝ)..1, RHSfun y := by
    -- the bound holds on `Ioo 0 1`, which is `Icc 0 1` minus the null endpoints.
    have hae : (fun y => (intervalFluxRepr p (u₁ τ) (v₁ τ) y
          - intervalFluxRepr p (u₂ τ) (v₂ τ) y) ^ 2)
        ≤ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)] RHSfun := by
      have hmeas : MeasurableSet (Set.Icc (0:ℝ) 1) := measurableSet_Icc
      refine (ae_restrict_iff' (μ := volume) hmeas).2 ?_
      have hnull : volume (insert (0:ℝ) ({(1:ℝ)} : Set ℝ)) = 0 :=
        Set.Finite.measure_zero
          ((Set.finite_singleton (1:ℝ)).insert (0:ℝ)) volume
      refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
      intro y hy
      simp only [Set.mem_setOf_eq] at hy
      push_neg at hy
      obtain ⟨hyIcc, hne⟩ := hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra hcon
      push_neg at hcon
      obtain ⟨hy0, hy1⟩ := hcon
      exact absurd (hsq y ⟨lt_of_le_of_ne hyIcc.1 (Ne.symm hy0),
        lt_of_le_of_ne hyIcc.2 hy1⟩) (not_le.mpr hne)
    exact intervalIntegral.integral_mono_ae_restrict (by norm_num) hintR hint_RHS hae
  refine ⟨3 * (G^2 + U^2 * Cg + (U*G*p.β)^2 * Cv), by positivity, ?_⟩
  rw [hflux_eq]
  refine hmono.trans ?_
  -- expand the RHS integral by linearity and bound each piece.
  have hRHSint : (∫ y in (0:ℝ)..1, RHSfun y)
      = 3 * (G^2 * (∫ y in (0:ℝ)..1, (a y)^2)
        + U^2 * (∫ y in (0:ℝ)..1, (gg y)^2)
        + (U*G*p.β)^2 * (∫ y in (0:ℝ)..1, (vv y)^2)) := by
    rw [hRHSfun]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_add
        ((hint_a.const_mul (G^2)).add (hint_g.const_mul (U^2))) (hint_v.const_mul _),
      intervalIntegral.integral_add (hint_a.const_mul (G^2)) (hint_g.const_mul (U^2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hRHSint]
  -- the three integral bounds.
  have hIa : (∫ y in (0:ℝ)..1, (a y)^2) = Eu := by
    rw [ha, hEu]; exact lift_u_diff_sq_integral_eq_Eu u₁ u₂ τ
  have hIg : (∫ y in (0:ℝ)..1, (gg y)^2) ≤ Cg * Eu := by rw [hgg, hEu]; exact hCg
  have hIv : (∫ y in (0:ℝ)..1, (vv y)^2) ≤ Cv * Eu := by rw [hvv, hEu]; exact hCv
  rw [hIa]
  -- assemble: `3(G²·Eu + U²·∫gg² + (UGβ)²·∫vv²) ≤ 3(G² + U²Cg + (UGβ)²Cv)·Eu`.
  have hUGβsq_nn : 0 ≤ (U*G*p.β)^2 := sq_nonneg _
  have hU2nn : 0 ≤ U^2 := sq_nonneg _
  calc 3 * (G^2 * Eu + U^2 * (∫ y in (0:ℝ)..1, (gg y)^2)
        + (U*G*p.β)^2 * (∫ y in (0:ℝ)..1, (vv y)^2))
      ≤ 3 * (G^2 * Eu + U^2 * (Cg * Eu) + (U*G*p.β)^2 * (Cv * Eu)) := by
        have h1 : U^2 * (∫ y in (0:ℝ)..1, (gg y)^2) ≤ U^2 * (Cg * Eu) :=
          mul_le_mul_of_nonneg_left hIg hU2nn
        have h2 : (U*G*p.β)^2 * (∫ y in (0:ℝ)..1, (vv y)^2)
            ≤ (U*G*p.β)^2 * (Cv * Eu) :=
          mul_le_mul_of_nonneg_left hIv hUGβsq_nn
        nlinarith [h1, h2]
    _ = 3 * (G^2 + U^2 * Cg + (U*G*p.β)^2 * Cv) * Eu := by ring

/-- **(A), unconditional for solutions.**  The chemical-concentration
nonnegativity hypotheses of `flux_diff_L2_le_Eu` are supplied for free by the
paper positivity (`v ≥ 0`), via `solution_lift_v_nonneg_Icc`. -/
theorem flux_diff_L2_le_Eu_of_solution
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {τ : ℝ} (hτ₁ : τ ∈ Set.Ioo (0 : ℝ) T₁) (hτ₂ : τ ∈ Set.Ioo (0 : ℝ) T₂) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∫ y in (0:ℝ)..1,
        (intervalFlux p (u₁ τ) (v₁ τ) y - intervalFlux p (u₂ τ) (v₂ τ) y) ^ 2)
        ≤ C * intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ :=
  flux_diff_L2_le_Eu hsol₁ hsol₂ hτ₁ hτ₂
    (solution_lift_v_nonneg_Icc hsol₁ hτ₁) (solution_lift_v_nonneg_Icc hsol₂ hτ₂)

/-! ## (B) flux C¹ regularity + endpoint vanishing -/

/-- **(B) flux endpoint vanishing.**  `fluxᵢ(τ,0) = fluxᵢ(τ,1) = 0` — the genuine
homogeneous-Neumann content (`∂ₓvᵢ = 0` at the endpoints, conjunct 7).  This is the
boundary datum `F 0 = F 1 = 0` consumed by `intervalFluxByParts`. -/
theorem flux_endpoint_zero
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    intervalFlux p (u τ) (v τ) 0 = 0 ∧ intervalFlux p (u τ) (v τ) 1 = 0 := by
  have hreg := (hsol.regularity.2.2.2.2.2.2.1 τ hτ).2
  have hbc0 : deriv (intervalDomainLift (v τ)) 0 = 0 := hreg.2.1
  have hbc1 : deriv (intervalDomainLift (v τ)) 1 = 0 := hreg.2.2
  refine ⟨?_, ?_⟩
  · unfold intervalFlux; rw [hbc0]; simp
  · unfold intervalFlux; rw [hbc1]; simp

/-- **(B) flux C¹ regularity on the interior `(0,1)`.**  Each `fluxᵢ(τ,·)` is `C¹`
on the open interior `(0,1)`: `fluxᵢ = lift(uᵢ)·∂ₓ(lift vᵢ)/(1+lift vᵢ)^β`, where
`lift uᵢ` is `C²` (conjunct 7, so `C¹`), `∂ₓ(lift vᵢ) = deriv(lift vᵢ)` is `C¹`
(`lift vᵢ` is `C²`, so its derivative is `C¹` on the interior), and `(1+lift vᵢ)^{-β}`
is `C¹` (rpow on the positive base `1+v ≥ 1 > 0`, using `hvnn`).  Hence
`chemDivᵢ = ∂ₓ(fluxᵢ)` is well-defined on the interior, which is exactly where the
chemotaxis integration-by-parts integrates. -/
theorem flux_contDiffOn_Ioo
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    (hvnn : ∀ x ∈ Set.Ioo (0:ℝ) 1, 0 ≤ intervalDomainLift (v τ) x) :
    ContDiffOn ℝ 1 (intervalFlux p (u τ) (v τ)) (Set.Ioo (0:ℝ) 1) := by
  have hreg := hsol.regularity.2.2.1 τ hτ
  -- interior `C²` of `lift u` and `lift v`.
  have hCu : ContDiffOn ℝ 2 (intervalDomainLift (u τ)) (Set.Ioo (0:ℝ) 1) := hreg.1
  have hCv : ContDiffOn ℝ 2 (intervalDomainLift (v τ)) (Set.Ioo (0:ℝ) 1) := hreg.2
  -- `lift u` is `C¹` on the interior.
  have hu1 : ContDiffOn ℝ 1 (intervalDomainLift (u τ)) (Set.Ioo (0:ℝ) 1) :=
    hCu.of_le (by norm_num)
  -- `deriv (lift v)` is `C¹` on the open interior (derivative of a `C²` function;
  -- `deriv = derivWithin` on the open set, and `ContDiffOn.deriv_of_isOpen`).
  have hdv1 : ContDiffOn ℝ 1 (deriv (intervalDomainLift (v τ))) (Set.Ioo (0:ℝ) 1) := by
    have hderivWithin : ContDiffOn ℝ 1
        (derivWithin (intervalDomainLift (v τ)) (Set.Ioo (0:ℝ) 1)) (Set.Ioo (0:ℝ) 1) :=
      hCv.derivWithin isOpen_Ioo.uniqueDiffOn (by norm_num)
    refine hderivWithin.congr (fun x hx => ?_)
    exact (derivWithin_of_isOpen isOpen_Ioo hx).symm
  -- `(1+lift v)^{-β}` is `C¹` on the interior (rpow on positives).
  have hbase1 : ContDiffOn ℝ 1 (fun x => 1 + intervalDomainLift (v τ) x)
      (Set.Ioo (0:ℝ) 1) := contDiffOn_const.add (hCv.of_le (by norm_num))
  have hne : ∀ x ∈ Set.Ioo (0:ℝ) 1, (1 + intervalDomainLift (v τ) x) ≠ 0 := by
    intro x hx; have := hvnn x hx; positivity
  have hq1 : ContDiffOn ℝ 1 (fun x => (1 + intervalDomainLift (v τ) x) ^ (-p.β))
      (Set.Ioo (0:ℝ) 1) := hbase1.rpow_const_of_ne hne
  -- assemble: flux = (lift u · deriv(lift v)) · (1+lift v)^{-β} (quotient as product).
  have hprod : ContDiffOn ℝ 1
      (fun x => intervalDomainLift (u τ) x * deriv (intervalDomainLift (v τ)) x
        * (1 + intervalDomainLift (v τ) x) ^ (-p.β)) (Set.Ioo (0:ℝ) 1) :=
    (hu1.mul hdv1).mul hq1
  refine hprod.congr (fun x hx => ?_)
  -- `a·g/(1+v)^β = a·g·(1+v)^{-β}` (base `> 0`).
  have hbase_pos : (0:ℝ) < 1 + intervalDomainLift (v τ) x := by
    have := hvnn x hx; linarith
  unfold intervalFlux
  rw [div_eq_mul_inv, ← Real.rpow_neg hbase_pos.le]

/-- **(B) flux C¹ on the interior, unconditional for solutions.**  The `hvnn`
hypothesis of `flux_contDiffOn_Ioo` is supplied for free by paper positivity
(`v ≥ 0`), via `solution_lift_v_nonneg_Ioo`. -/
theorem flux_contDiffOn_Ioo_of_solution
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    ContDiffOn ℝ 1 (intervalFlux p (u τ) (v τ)) (Set.Ioo (0:ℝ) 1) :=
  flux_contDiffOn_Ioo hsol hτ (solution_lift_v_nonneg_Ioo hsol hτ)

/-- **(B) flux C¹ regularity on the CLOSED interval `[0,1]`, for a positive
classical solution.**  All three factors of `flux = lift(u)·∂ₓ(lift v)/(1+lift v)^β`
are now `C¹` on the *closed* `[0,1]`:

  * `lift u` is `C²` on `Icc 0 1` (regularity conjunct 7), hence `C¹`;
  * `∂ₓ(lift v) = deriv(lift v)` equals `resolverGradReal p (u τ)` on all of `[0,1]`
    (`solution_lift_v_deriv_eq_resolverGrad_Icc`: interior + endpoint vanishing), and
    `resolverGradReal` is `C¹` on `[0,1]` via the second-derivative cosine majorant
    `∑ |(v̂_k).re|·(kπ)² < ∞` (`resolverGradReal_contDiffOn_Icc`);
  * `(1+lift v)^{-β}` is `C¹` (rpow on the positive base `1+v ≥ 1 > 0`, from `v ≥ 0`).

This is the two-sided-endpoint-derivative input that lets `intervalFluxByParts` be
applied on the closed interval `uIcc 0 1`. -/
theorem flux_contDiffOn_Icc
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    ContDiffOn ℝ 1 (intervalFlux p (u τ) (v τ)) (Set.Icc (0:ℝ) 1) := by
  have hvnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ intervalDomainLift (v τ) x :=
    solution_lift_v_nonneg_Icc hsol hτ
  -- closed-Icc C² of `lift u` and `lift v` (conjunct 7).
  have hCu : ContDiffOn ℝ 2 (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1) :=
    (hsol.regularity.2.2.2.2.2.2.1 τ hτ).1.1
  have hCv : ContDiffOn ℝ 2 (intervalDomainLift (v τ)) (Set.Icc (0:ℝ) 1) :=
    (hsol.regularity.2.2.2.2.2.2.1 τ hτ).2.1
  -- `lift u` is `C¹` on `[0,1]`.
  have hu1 : ContDiffOn ℝ 1 (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1) :=
    hCu.of_le (by norm_num)
  -- `deriv (lift v)` is `C¹` on `[0,1]`: it equals `resolverGradReal p (u τ)` there,
  -- and the latter is `C¹` (second-derivative majorant).
  have hdv1 : ContDiffOn ℝ 1 (deriv (intervalDomainLift (v τ))) (Set.Icc (0:ℝ) 1) := by
    refine (resolverGradReal_contDiffOn_Icc hsol hτ).congr (fun x hx => ?_)
    exact solution_lift_v_deriv_eq_resolverGrad_Icc hsol hτ hx
  -- `(1+lift v)^{-β}` is `C¹` on `[0,1]` (rpow on positives).
  have hbase1 : ContDiffOn ℝ 1 (fun x => 1 + intervalDomainLift (v τ) x)
      (Set.Icc (0:ℝ) 1) := contDiffOn_const.add (hCv.of_le (by norm_num))
  have hne : ∀ x ∈ Set.Icc (0:ℝ) 1, (1 + intervalDomainLift (v τ) x) ≠ 0 := by
    intro x hx; have := hvnn x hx; positivity
  have hq1 : ContDiffOn ℝ 1 (fun x => (1 + intervalDomainLift (v τ) x) ^ (-p.β))
      (Set.Icc (0:ℝ) 1) := hbase1.rpow_const_of_ne hne
  -- assemble: flux = (lift u · deriv(lift v)) · (1+lift v)^{-β} on `[0,1]`.
  have hprod : ContDiffOn ℝ 1
      (fun x => intervalDomainLift (u τ) x * deriv (intervalDomainLift (v τ)) x
        * (1 + intervalDomainLift (v τ) x) ^ (-p.β)) (Set.Icc (0:ℝ) 1) :=
    (hu1.mul hdv1).mul hq1
  refine hprod.congr (fun x hx => ?_)
  have hbase_pos : (0:ℝ) < 1 + intervalDomainLift (v τ) x := by
    have := hvnn x hx; linarith
  unfold intervalFlux
  rw [div_eq_mul_inv, ← Real.rpow_neg hbase_pos.le]

end

end ShenWork.Paper2
