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
      (hsol.regularity.2.2.2.2.1 t ht).2.2.1
    rw [hbc0, resolverGradReal_zero]
  · rcases eq_or_lt_of_le hx.2 with hx1 | hx1
    · -- `x = 1`
      subst hx1
      have hbc1 : deriv (intervalDomainLift (v t)) 1 = 0 :=
        (hsol.regularity.2.2.2.2.1 t ht).2.2.2
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
theorem resolverGradReal_continuous_of_sourceDecay
    {p : CM2Params} {w : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p w) :
    Continuous (fun x : ℝ => resolverGradReal p w x) := by
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

/-- Classical-solution corollary of `resolverGradReal_continuous_of_sourceDecay`. -/
theorem resolverGradReal_continuous
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    Continuous (fun x : ℝ => resolverGradReal p (u τ) x) :=
  resolverGradReal_continuous_of_sourceDecay (sourceCoeffQuadraticDecay_of_solution hsol hτ)

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
theorem resolverGrad2Real_continuous_of_sourceDecay
    {p : CM2Params} {w : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p w) :
    Continuous (fun z : ℝ => resolverGrad2Real p w z) := by
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

/-- Classical-solution corollary of `resolverGrad2Real_continuous_of_sourceDecay`. -/
theorem resolverGrad2Real_continuous
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    Continuous (fun z : ℝ => resolverGrad2Real p (u τ) z) :=
  resolverGrad2Real_continuous_of_sourceDecay (sourceCoeffQuadraticDecay_of_solution hsol hτ)

/-- **(B): `resolverGradReal p (u τ)` has derivative `resolverGrad2Real p (u τ)` at
every real point**, for a positive classical solution.  Via the second-derivative
bridge `resolverGrad_hasDerivAt_grad2` fed the summable `∑ |(v̂_k).re|·(kπ)²` from
source decay.  (`resolverGradReal` is definitionally the sine series.) -/
theorem resolverGradReal_hasDerivAt_of_sourceDecay
    {p : CM2Params} {w : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p w) (z : ℝ) :
    HasDerivAt (fun y : ℝ => resolverGradReal p w y) (resolverGrad2Real p w z) z := by
  have hmaj :=
    ShenWork.IntervalResolverGradientBridge.resolverGrad2_majorant_summable_of_sourceDecay
      hdecay.C_nonneg hdecay.decay
  -- `resolverGradReal p w` is definitionally the sine series; `resolverGrad2Real`
  -- is the termwise second-derivative cosine series — exactly the bridge conclusion.
  exact ShenWork.IntervalResolverGradientBridge.resolverGrad_hasDerivAt_grad2 hmaj z

/-- Classical-solution corollary of `resolverGradReal_hasDerivAt_of_sourceDecay`. -/
theorem resolverGradReal_hasDerivAt
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) (z : ℝ) :
    HasDerivAt (fun w : ℝ => resolverGradReal p (u τ) w) (resolverGrad2Real p (u τ) z) z :=
  resolverGradReal_hasDerivAt_of_sourceDecay (sourceCoeffQuadraticDecay_of_solution hsol hτ) z

/-- **(B): `resolverGradReal p (u τ)` is `C¹` on `Icc 0 1`.**  It is differentiable
everywhere with derivative `resolverGrad2Real p (u τ)` (a uniformly-convergent
continuous series), so by `contDiff_one_iff_deriv` it is `C¹` on all of ℝ, hence on
the closed `[0,1]`.  This is the missing closed-interval input for the flux factor
`∂ₓ(lift v) = resolverGradReal` of `flux_contDiffOn_Icc`. -/
theorem resolverGradReal_contDiffOn_Icc_of_sourceDecay
    {p : CM2Params} {w : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p w) :
    ContDiffOn ℝ 1 (fun x : ℝ => resolverGradReal p w x) (Set.Icc (0:ℝ) 1) := by
  have hderiv : ∀ z : ℝ,
      HasDerivAt (fun y : ℝ => resolverGradReal p w y) (resolverGrad2Real p w z) z :=
    fun z => resolverGradReal_hasDerivAt_of_sourceDecay hdecay z
  have hdiff : Differentiable ℝ (fun x : ℝ => resolverGradReal p w x) :=
    fun z => (hderiv z).differentiableAt
  -- `deriv (resolverGradReal …) = resolverGrad2Real …`, which is continuous.
  have hderiv_eq : deriv (fun y : ℝ => resolverGradReal p w y)
      = fun z => resolverGrad2Real p w z := by
    funext z; exact (hderiv z).deriv
  have hcontD : Continuous (deriv (fun y : ℝ => resolverGradReal p w y)) := by
    rw [hderiv_eq]; exact resolverGrad2Real_continuous_of_sourceDecay hdecay
  have hC1 : ContDiff ℝ 1 (fun x : ℝ => resolverGradReal p w x) :=
    contDiff_one_iff_deriv.2 ⟨hdiff, hcontD⟩
  exact hC1.contDiffOn

/-- Classical-solution corollary of `resolverGradReal_contDiffOn_Icc_of_sourceDecay`. -/
theorem resolverGradReal_contDiffOn_Icc
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    ContDiffOn ℝ 1 (fun x : ℝ => resolverGradReal p (u τ) x) (Set.Icc (0:ℝ) 1) :=
  resolverGradReal_contDiffOn_Icc_of_sourceDecay (sourceCoeffQuadraticDecay_of_solution hsol hτ)

/-- **(A)-helper (i): uniform L∞ bound on `resolverGradReal p (u τ)` over `[0,1]`.**
Continuity on the compact `[0,1]`. -/
theorem resolverGradReal_bounded_of_sourceDecay
    {p : CM2Params} {w : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p w) :
    ∃ G : ℝ, 0 ≤ G ∧
      ∀ x ∈ Set.Icc (0:ℝ) 1, |resolverGradReal p w x| ≤ G := by
  have hcont : Continuous (fun x : ℝ => resolverGradReal p w x) :=
    resolverGradReal_continuous_of_sourceDecay hdecay
  obtain ⟨G, hG⟩ :=
    (isCompact_Icc.image_of_continuousOn
      (hcont.continuousOn.abs)).bddAbove
  refine ⟨max G 0, le_max_right _ _, fun x hx => ?_⟩
  exact le_trans (hG ⟨x, hx, rfl⟩) (le_max_left _ _)

/-- Classical-solution corollary of `resolverGradReal_bounded_of_sourceDecay`. -/
theorem resolverGradReal_bounded
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    ∃ G : ℝ, 0 ≤ G ∧
      ∀ x ∈ Set.Icc (0:ℝ) 1, |resolverGradReal p (u τ) x| ≤ G :=
  resolverGradReal_bounded_of_sourceDecay (sourceCoeffQuadraticDecay_of_solution hsol hτ)

/-- **(Gap 1)-helper: uniform L∞ bound on the resolver second derivative
`resolverGrad2Real p (u τ)` over `[0,1]`.**  The second-derivative cosine series is
continuous (`resolverGrad2Real_continuous`), so it is bounded on the compact `[0,1]`. -/
theorem resolverGrad2Real_bounded_of_sourceDecay
    {p : CM2Params} {w : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p w) :
    ∃ G : ℝ, 0 ≤ G ∧
      ∀ x ∈ Set.Icc (0:ℝ) 1, |resolverGrad2Real p w x| ≤ G := by
  have hcont : Continuous (fun x : ℝ => resolverGrad2Real p w x) :=
    resolverGrad2Real_continuous_of_sourceDecay hdecay
  obtain ⟨G, hG⟩ :=
    (isCompact_Icc.image_of_continuousOn (hcont.continuousOn.abs)).bddAbove
  refine ⟨max G 0, le_max_right _ _, fun x hx => ?_⟩
  exact le_trans (hG ⟨x, hx, rfl⟩) (le_max_left _ _)

/-- Classical-solution corollary of `resolverGrad2Real_bounded_of_sourceDecay`. -/
theorem resolverGrad2Real_bounded
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    ∃ G : ℝ, 0 ≤ G ∧
      ∀ x ∈ Set.Icc (0:ℝ) 1, |resolverGrad2Real p (u τ) x| ≤ G :=
  resolverGrad2Real_bounded_of_sourceDecay (sourceCoeffQuadraticDecay_of_solution hsol hτ)

/-- **(Gap 1) `resolverGradReal` is `θ`-Hölder in `x` on `[0,1]`.**

The chemotaxis multiplier's core `V_x = resolverGradReal p (u τ)` is `C¹` on `ℝ`
(`resolverGradReal_hasDerivAt`, derivative `V_xx = resolverGrad2Real p (u τ)`), and
`V_xx` is continuous hence bounded by some `G ≥ 0` on the compact `[0,1]`
(`resolverGrad2Real_bounded`).  The 1-D mean-value inequality on the convex `[0,1]`
(`norm_image_sub_le_of_norm_deriv_le`) then gives `V_x` Lipschitz with constant `G`,
and on `[0,1]` (where `|x−y| ≤ 1`) Lipschitz upgrades to `θ`-Hölder for `0 < θ ≤ 1`
via `|x−y| = |x−y|^1 ≤ |x−y|^θ`.  This supplies the `Hg` modulus (with `Hg = G`)
that `chemFlux_Ctheta` takes as a hypothesis. -/
theorem resolverGradReal_holder_Icc_of_sourceDecay
    {p : CM2Params} {w : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p w)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ Hg : ℝ, 0 ≤ Hg ∧
      ∀ x y, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 →
        |resolverGradReal p w x - resolverGradReal p w y|
          ≤ Hg * |x - y| ^ θ := by
  obtain ⟨G, hGnn, hGb⟩ := resolverGrad2Real_bounded_of_sourceDecay hdecay
  refine ⟨G, hGnn, fun x y hx hy => ?_⟩
  -- `V_x` is differentiable everywhere with derivative `V_xx = resolverGrad2Real`.
  have hderiv : ∀ z : ℝ, HasDerivAt (fun y : ℝ => resolverGradReal p w y)
      (resolverGrad2Real p w z) z := fun z => resolverGradReal_hasDerivAt_of_sourceDecay hdecay z
  have hdiffAt : ∀ z ∈ Set.Icc (0:ℝ) 1,
      DifferentiableAt ℝ (fun y : ℝ => resolverGradReal p w y) z :=
    fun z _ => (hderiv z).differentiableAt
  have hderiv_eq : ∀ z : ℝ,
      deriv (fun y : ℝ => resolverGradReal p w y) z = resolverGrad2Real p w z :=
    fun z => (hderiv z).deriv
  -- bound on `‖deriv V_x‖ = |V_xx| ≤ G` over `[0,1]`.
  have hbound : ∀ z ∈ Set.Icc (0:ℝ) 1,
      ‖deriv (fun y : ℝ => resolverGradReal p w y) z‖ ≤ G := by
    intro z hz; rw [Real.norm_eq_abs, hderiv_eq z]; exact hGb z hz
  -- mean-value Lipschitz on the convex `[0,1]`.
  have hlip : |resolverGradReal p w x - resolverGradReal p w y| ≤ G * |x - y| := by
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun y => resolverGradReal p w y) hdiffAt hbound (convex_Icc 0 1) hx hy
    simp only [Real.norm_eq_abs] at hmv
    rw [abs_sub_comm (resolverGradReal p w x), abs_sub_comm x y]
    exact hmv
  -- `|x−y| ≤ 1` on `[0,1]`, so `|x−y| = |x−y|^1 ≤ |x−y|^θ`.
  have hle1 : |x - y| ≤ 1 := by
    rw [abs_le]; constructor <;> [linarith [hx.1, hy.2]; linarith [hx.2, hy.1]]
  have hupg : |x - y| ≤ |x - y| ^ θ := by
    rcases eq_or_lt_of_le (abs_nonneg (x - y)) with hz | hpos
    · rw [← hz]; simp [Real.zero_rpow (ne_of_gt hθ0)]
    · calc |x - y| = |x - y| ^ (1:ℝ) := (Real.rpow_one _).symm
        _ ≤ |x - y| ^ θ := Real.rpow_le_rpow_of_exponent_ge hpos hle1 hθ1
  calc |resolverGradReal p w x - resolverGradReal p w y|
      ≤ G * |x - y| := hlip
    _ ≤ G * |x - y| ^ θ := mul_le_mul_of_nonneg_left hupg hGnn

/-- Classical-solution corollary of `resolverGradReal_holder_Icc_of_sourceDecay`:
the original `IsPaper2ClassicalSolution` statement, now a thin instantiation. -/
theorem resolverGradReal_holder_Icc
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ Hg : ℝ, 0 ≤ Hg ∧
      ∀ x y, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 →
        |resolverGradReal p (u τ) x - resolverGradReal p (u τ) y|
          ≤ Hg * |x - y| ^ θ :=
  resolverGradReal_holder_Icc_of_sourceDecay
    (sourceCoeffQuadraticDecay_of_solution hsol hτ) hθ0 hθ1

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
    ((hsol.regularity.2.2.2.2.1 τ hτ).2.1).continuousOn
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
    ((hsol.regularity.2.2.2.2.1 τ hτ).1.1).continuousOn
  have hg : ContinuousOn (fun x => resolverGradReal p (u τ) x) (Set.Icc (0:ℝ) 1) :=
    (resolverGradReal_continuous hsol hτ).continuousOn
  have hv : ContinuousOn (intervalDomainLift (v τ)) (Set.Icc (0:ℝ) 1) :=
    ((hsol.regularity.2.2.2.2.1 τ hτ).2.1).continuousOn
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
    ((hsol₁.regularity.2.2.2.2.1 τ hτ₁).1.1).continuousOn
  have hcont_u₂ : ContinuousOn (intervalDomainLift (u₂ τ)) (Set.Icc (0:ℝ) 1) :=
    ((hsol₂.regularity.2.2.2.2.1 τ hτ₂).1.1).continuousOn
  have hcont_v₁ : ContinuousOn (intervalDomainLift (v₁ τ)) (Set.Icc (0:ℝ) 1) :=
    ((hsol₁.regularity.2.2.2.2.1 τ hτ₁).2.1).continuousOn
  have hcont_v₂ : ContinuousOn (intervalDomainLift (v₂ τ)) (Set.Icc (0:ℝ) 1) :=
    ((hsol₂.regularity.2.2.2.2.1 τ hτ₂).2.1).continuousOn
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
  have hreg := (hsol.regularity.2.2.2.2.1 τ hτ).2
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
  have hreg := hsol.regularity.1 τ hτ
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
    (hsol.regularity.2.2.2.2.1 τ hτ).1.1
  have hCv : ContDiffOn ℝ 2 (intervalDomainLift (v τ)) (Set.Icc (0:ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 τ hτ).2.1
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

/-! ## (C) The parabolic `u`-energy differential inequality `Eprime ≤ K·E_u`

The Leibniz half (`intervalDomainL2UEnergy_hasDerivAt_of_slabContinuous`) gives the
derivative `Eprime τ = ∫₀¹ intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ y`, which is
`∫₀¹ 2·(lift w τ)·(∂ₜ lift w τ)`.  We bound it by `K·E_u(τ)`.

Substituting the parabolic `u`-PDE (`pde_u`) for `u₁,u₂` and subtracting, at each
interior point `∂ₜ(lift w) = Δ(lift w) − χ₀·∂ₓ(flux₁−flux₂) + (reaction₁−reaction₂)`,
where `Δ = deriv∘deriv∘lift`, `flux = intervalFlux`, `reaction = intervalLogisticSource`.
Then
  * `∫ (lift w)·Δ(lift w) = −∫ (∂ₓ lift w)² ≤ 0`   (`intervalEnergyByParts`, conj. 7);
  * `∫ (lift w)·∂ₓ(flux₁−flux₂) = −∫ (∂ₓ lift w)·(flux₁−flux₂)` (`intervalFluxByParts`),
    Young-absorbed: `|χ₀·∫…| ≤ ½D + K₂·E_u` with `∫(flux₁−flux₂)² ≤ C·E_u`;
  * `|∫ (lift w)·(react₁−react₂)| ≤ K₁·E_u` (`intervalLogisticSource_lipschitz` + Cauchy-Schwarz).

Combine: `½ Eprime ≤ −D + ½D + K₂E_u + K₁E_u ≤ (K₁+K₂)E_u`, so `Eprime ≤ K·E_u`,
`K = 2(K₁+K₂) ≥ 0`.

This subsection proves the *pointwise* PDE substitution and the integral
dissipation identity; the full Young/Lipschitz integral assembly is
`intervalDomainL2U_energy_diffIneq_bound`. -/

/-- The lift of the `u`-difference as an `ℝ → ℝ` function, equal on `[0,1]` to
`lift(u₁ τ) − lift(u₂ τ)`. -/
theorem intervalDomainLift_uDiff_eq
    (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) (y : ℝ) :
    intervalDomainLift (fun x => u₁ τ x - u₂ τ x) y
      = intervalDomainLift (u₁ τ) y - intervalDomainLift (u₂ τ) y := by
  unfold intervalDomainLift
  by_cases hy : y ∈ Set.Icc (0:ℝ) 1
  · simp [hy]
  · simp [hy]

/-- **Pointwise PDE substitution for the interior time derivative of the lifted
`u`-difference.**  At every interior `y ∈ (0,1)`, with `w = u₁ − u₂`,
`deriv (fun r => lift (u₁ r − u₂ r) y) τ
   = (Δ(lift u₁) − Δ(lift u₂))(y)
     − χ₀·(deriv(flux₁) − deriv(flux₂))(y)
     + (react₁ − react₂)(y)`,
where `Δ = deriv∘deriv∘lift`, `fluxᵢ = intervalFlux p (uᵢ τ)(vᵢ τ)`,
`reactᵢ y = intervalDomainLift (uᵢ τ) y · (p.a − p.b·(lift (uᵢ τ) y)^α)`.
Pure unfolding of `intervalDomain`'s `timeDeriv`/`laplacian`/`chemotaxisDiv` through
the `pde_u` identity for `u₁,u₂`. -/
theorem intervalDomainUEnergy_timeDeriv_pde
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) (min T₁ T₂))
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (fun r => intervalDomainLift (fun x => u₁ r x - u₂ r x) y) τ
      = (deriv (fun z => deriv (intervalDomainLift (u₁ τ)) z) y
          - deriv (fun z => deriv (intervalDomainLift (u₂ τ)) z) y)
        - p.χ₀ * (deriv (intervalFlux p (u₁ τ) (v₁ τ)) y
            - deriv (intervalFlux p (u₂ τ) (v₂ τ)) y)
        + (intervalDomainLift (u₁ τ) y
              * (p.a - p.b * intervalDomainLift (u₁ τ) y ^ p.α)
            - intervalDomainLift (u₂ τ) y
              * (p.a - p.b * intervalDomainLift (u₂ τ) y ^ p.α)) := by
  classical
  have hyIcc : y ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hy
  set x : intervalDomainPoint := ⟨y, hyIcc⟩ with hx
  have hxin : x ∈ intervalDomain.inside := hy
  have hτ₁ : τ ∈ Set.Ioo (0:ℝ) T₁ := ⟨hτ.1, lt_of_lt_of_le hτ.2 (min_le_left _ _)⟩
  have hτ₂ : τ ∈ Set.Ioo (0:ℝ) T₂ := ⟨hτ.1, lt_of_lt_of_le hτ.2 (min_le_right _ _)⟩
  -- the slice deriv equals timeDeriv u₁ - timeDeriv u₂.
  have hslice :
      deriv (fun r => intervalDomainLift (fun z => u₁ r z - u₂ r z) y) τ
        = intervalDomain.timeDeriv u₁ τ x - intervalDomain.timeDeriv u₂ τ x := by
    have hlift : (fun r => intervalDomainLift (fun z => u₁ r z - u₂ r z) y)
        = fun r => u₁ r x - u₂ r x := by
      funext r; simp [intervalDomainLift, hyIcc, hx]
    rw [hlift]
    exact (intervalDomain_difference_hasDerivAt_time hsol₁ hsol₂ hy hτ).deriv
  rw [hslice]
  -- pde_u for each solution.
  have hp1 := hsol₁.pde_u hτ₁.1 hτ₁.2 hxin
  have hp2 := hsol₂.pde_u hτ₂.1 hτ₂.2 hxin
  rw [hp1, hp2]
  -- unfold the abstract spatial operators of `intervalDomain`.
  change _ = _
  simp only [intervalDomain, intervalDomainLaplacian, intervalDomainChemotaxisDiv]
  -- `intervalFlux` is definitionally the chemotaxisDiv integrand.
  have hfluxeq : ∀ (u v : intervalDomainPoint → ℝ),
      (fun yy : ℝ => intervalDomainLift u yy * deriv (intervalDomainLift v) yy
        / (1 + intervalDomainLift v yy) ^ p.β)
        = intervalFlux p u v := by
    intro u v; funext yy; rfl
  rw [hfluxeq (u₁ τ) (v₁ τ), hfluxeq (u₂ τ) (v₂ τ)]
  -- lift values at the interior point `x` are the slice values.
  have hu₁ : intervalDomainLift (u₁ τ) y = u₁ τ x := by simp [intervalDomainLift, hyIcc, hx]
  have hu₂ : intervalDomainLift (u₂ τ) y = u₂ τ x := by simp [intervalDomainLift, hyIcc, hx]
  rw [hu₁, hu₂]
  ring

/-! ### Building blocks for the integral assembly -/

/-- **Open-interior dissipation integration-by-parts.**  The closed-interval IBP
`intervalEnergyByParts` over-requires two-sided `HasDerivAt` of `w` at the
endpoints, which the lift (a zero-extension that jumps at `0,1`) does NOT satisfy.
This variant requires only: continuity of `w` and `w'` on the closed `[0,1]`,
interior `HasDerivAt` of `w` (deriv `w'`) and `w'` (deriv `w''`), the Neumann
endpoint VALUES `w' 0 = w' 1 = 0`, and integrability of `w', w''`.  Conclusion
`∫₀¹ w·w'' = −∫₀¹ (w')²`, via Mathlib's
`integral_mul_deriv_eq_deriv_mul_of_hasDerivAt` (interior `HasDerivAt`). -/
theorem intervalEnergyByParts_open
    {w w' w'' : ℝ → ℝ}
    (hw_cont : ContinuousOn w (Set.uIcc (0 : ℝ) 1))
    (hw'_cont : ContinuousOn w' (Set.uIcc (0 : ℝ) 1))
    (hw : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt w (w' x) x)
    (hw' : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt w' (w'' x) x)
    (hw'int : IntervalIntegrable w' MeasureTheory.volume 0 1)
    (hw''int : IntervalIntegrable w'' MeasureTheory.volume 0 1)
    (hbc0 : w' 0 = 0) (hbc1 : w' 1 = 0) :
    (∫ x in (0 : ℝ)..1, w x * w'' x) = - ∫ x in (0 : ℝ)..1, (w' x) ^ 2 := by
  classical
  have hmm : Set.Ioo (min (0:ℝ) 1) (max 0 1) = Set.Ioo (0:ℝ) 1 := by
    rw [min_eq_left (by norm_num : (0:ℝ) ≤ 1), max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
  have hw_io : ∀ x ∈ Set.Ioo (min (0:ℝ) 1) (max 0 1), HasDerivAt w (w' x) x := by
    rw [hmm]; exact hw
  have hw'_io : ∀ x ∈ Set.Ioo (min (0:ℝ) 1) (max 0 1), HasDerivAt w' (w'' x) x := by
    rw [hmm]; exact hw'
  have hIBP :
      (∫ x in (0:ℝ)..1, w x * w'' x) =
        w 1 * w' 1 - w 0 * w' 0 - ∫ x in (0:ℝ)..1, w' x * w' x :=
    integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hw_cont hw'_cont hw_io hw'_io hw'int hw''int
  rw [hIBP, hbc0, hbc1]
  rw [show (∫ x in (0:ℝ)..1, w' x * w' x) = ∫ x in (0:ℝ)..1, (w' x) ^ 2 from by
    apply integral_congr; intro x _; ring]
  ring

/-- **Continuity of `deriv (lift (u τ))` on the CLOSED `[0,1]`** for a classical
solution.  Interior continuity is from `C²` (conjunct from `.2.2.1`); endpoint
continuity (within `[0,1]`) is the genuine one-sided Neumann limit
`deriv(lift u) → 0` (conjunct 6) glued with the recorded endpoint value
`deriv(lift u) e = 0` (conjunct 7) — both sides agree with the value `0`. -/
theorem solution_deriv_lift_continuousOn_Icc
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousOn (deriv (intervalDomainLift (u τ))) (Set.Icc (0:ℝ) 1) := by
  classical
  have hC1 : ContDiffOn ℝ 2 (intervalDomainLift (u τ)) (Set.Ioo (0:ℝ) 1) :=
    (hsol.regularity.1 τ hτ).1
  have h6 := (hsol.regularity.2.2.2.1 τ hτ).1
  obtain ⟨htend0, htend1⟩ := h6
  have hbc0 : deriv (intervalDomainLift (u τ)) 0 = 0 :=
    (hsol.regularity.2.2.2.2.1 τ hτ).1.2.1
  have hbc1 : deriv (intervalDomainLift (u τ)) 1 = 0 :=
    (hsol.regularity.2.2.2.2.1 τ hτ).1.2.2
  -- interior continuity of `deriv` (C² ⇒ `deriv` continuous on the open interior).
  have hint : ContinuousOn (deriv (intervalDomainLift (u τ))) (Set.Ioo (0:ℝ) 1) :=
    hC1.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  -- now glue continuity at the endpoints.
  intro e he
  rcases eq_or_lt_of_le he.1 with he0 | he0
  · -- e = 0.
    subst he0
    rw [ContinuousWithinAt]
    rw [hbc0, nhdsWithin_Icc_eq_nhdsGE (by norm_num : (0:ℝ) < 1)]
    -- `𝓝[≥] 0 = 𝓝[>] 0 ⊔ pure 0`; tendsto along each.
    have hsplit : 𝓝[Set.Ici (0:ℝ)] 0 = 𝓝[Set.Ioi (0:ℝ)] 0 ⊔ 𝓝[{(0:ℝ)}] 0 := by
      rw [← nhdsWithin_union, Set.Ioi_union_left]
    rw [hsplit, Filter.tendsto_sup]
    refine ⟨htend0, ?_⟩
    rw [nhdsWithin_singleton]
    have := tendsto_pure_nhds (deriv (intervalDomainLift (u τ))) (0:ℝ)
    rwa [hbc0] at this
  · rcases eq_or_lt_of_le he.2 with he1 | he1
    · -- e = 1.
      subst he1
      rw [ContinuousWithinAt]
      rw [hbc1, nhdsWithin_Icc_eq_nhdsLE (by norm_num : (0:ℝ) < 1)]
      have hsplit : 𝓝[Set.Iic (1:ℝ)] 1 = 𝓝[Set.Iio (1:ℝ)] 1 ⊔ 𝓝[{(1:ℝ)}] 1 := by
        rw [← nhdsWithin_union, Set.Iio_union_right]
      rw [hsplit, Filter.tendsto_sup]
      refine ⟨htend1, ?_⟩
      rw [nhdsWithin_singleton]
      have := tendsto_pure_nhds (deriv (intervalDomainLift (u τ))) (1:ℝ)
      rwa [hbc1] at this
    · -- interior.
      have hcw : ContinuousWithinAt (deriv (intervalDomainLift (u τ))) (Set.Ioo (0:ℝ) 1) e :=
        hint e ⟨he0, he1⟩
      exact hcw.mono_of_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds isOpen_Ioo ⟨he0, he1⟩))

/-- Interior `HasDerivAt` of the lift of a `u`-difference (and of its derivative
field) for a classical solution, with the second derivative the abstract Laplacian.
The genuine input is the `C²` interior regularity (`.2.2.1`). -/
theorem lift_hasDerivAt_interior
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt (intervalDomainLift (u τ)) (deriv (intervalDomainLift (u τ)) x) x
      ∧ HasDerivAt (deriv (intervalDomainLift (u τ)))
          (deriv (fun z => deriv (intervalDomainLift (u τ)) z) x) x := by
  have hC1 : ContDiffOn ℝ 2 (intervalDomainLift (u τ)) (Set.Ioo (0:ℝ) 1) :=
    (hsol.regularity.1 τ hτ).1
  have hd1 : DifferentiableAt ℝ (intervalDomainLift (u τ)) x :=
    (hC1.differentiableOn (by norm_num)).differentiableAt (IsOpen.mem_nhds isOpen_Ioo hx)
  have hC1d : ContDiffOn ℝ 1 (deriv (intervalDomainLift (u τ))) (Set.Ioo (0:ℝ) 1) :=
    hC1.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hd2 : DifferentiableAt ℝ (deriv (intervalDomainLift (u τ))) x :=
    (hC1d.differentiableOn (by norm_num)).differentiableAt (IsOpen.mem_nhds isOpen_Ioo hx)
  exact ⟨hd1.hasDerivAt, hd2.hasDerivAt⟩

/-- **Dissipation identity for the `u`-difference.**  With `wL = lift u₁ − lift u₂`,
`dwL = deriv(lift u₁) − deriv(lift u₂)`,
`∫₀¹ wL·(Δ(lift u₁) − Δ(lift u₂)) = − ∫₀¹ (dwL)²`,
where `Δ = deriv∘deriv∘lift`.  Open-interval IBP (`intervalEnergyByParts_open`)
with the Neumann endpoint values `dwL 0 = dwL 1 = 0` (conjunct 7). -/
theorem uDiff_dissipation
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {τ : ℝ} (hτ₁ : τ ∈ Set.Ioo (0 : ℝ) T₁) (hτ₂ : τ ∈ Set.Ioo (0 : ℝ) T₂) :
    (∫ y in (0:ℝ)..1,
        (intervalDomainLift (u₁ τ) y - intervalDomainLift (u₂ τ) y)
          * (deriv (fun z => deriv (intervalDomainLift (u₁ τ)) z) y
              - deriv (fun z => deriv (intervalDomainLift (u₂ τ)) z) y))
      = - ∫ y in (0:ℝ)..1,
          (deriv (intervalDomainLift (u₁ τ)) y - deriv (intervalDomainLift (u₂ τ)) y) ^ 2 := by
  classical
  set wL : ℝ → ℝ := fun y => intervalDomainLift (u₁ τ) y - intervalDomainLift (u₂ τ) y with hwL
  set dwL : ℝ → ℝ := fun y => deriv (intervalDomainLift (u₁ τ)) y
      - deriv (intervalDomainLift (u₂ τ)) y with hdwL
  set ddwL : ℝ → ℝ := fun y => deriv (fun z => deriv (intervalDomainLift (u₁ τ)) z) y
      - deriv (fun z => deriv (intervalDomainLift (u₂ τ)) z) y with hddwL
  -- continuity of `wL` and `dwL` on `[0,1]`.
  have hwLcont : ContinuousOn wL (Set.Icc (0:ℝ) 1) := by
    have h1 : ContinuousOn (intervalDomainLift (u₁ τ)) (Set.Icc (0:ℝ) 1) :=
      ((hsol₁.regularity.2.2.2.2.1 τ hτ₁).1.1).continuousOn
    have h2 : ContinuousOn (intervalDomainLift (u₂ τ)) (Set.Icc (0:ℝ) 1) :=
      ((hsol₂.regularity.2.2.2.2.1 τ hτ₂).1.1).continuousOn
    exact h1.sub h2
  have hdwLcont : ContinuousOn dwL (Set.Icc (0:ℝ) 1) :=
    (solution_deriv_lift_continuousOn_Icc hsol₁ hτ₁).sub
      (solution_deriv_lift_continuousOn_Icc hsol₂ hτ₂)
  -- interior `HasDerivAt wL (dwL x) x` and `HasDerivAt dwL (ddwL x) x`.
  have hwLderiv : ∀ x ∈ Set.Ioo (0:ℝ) 1, HasDerivAt wL (dwL x) x := by
    intro x hx
    exact ((lift_hasDerivAt_interior hsol₁ hτ₁ hx).1).sub
      ((lift_hasDerivAt_interior hsol₂ hτ₂ hx).1)
  have hdwLderiv : ∀ x ∈ Set.Ioo (0:ℝ) 1, HasDerivAt dwL (ddwL x) x := by
    intro x hx
    exact ((lift_hasDerivAt_interior hsol₁ hτ₁ hx).2).sub
      ((lift_hasDerivAt_interior hsol₂ hτ₂ hx).2)
  -- endpoint vanishing of `dwL`.
  have hbc0 : dwL 0 = 0 := by
    show deriv (intervalDomainLift (u₁ τ)) 0 - deriv (intervalDomainLift (u₂ τ)) 0 = 0
    rw [(hsol₁.regularity.2.2.2.2.1 τ hτ₁).1.2.1,
      (hsol₂.regularity.2.2.2.2.1 τ hτ₂).1.2.1, sub_zero]
  have hbc1 : dwL 1 = 0 := by
    show deriv (intervalDomainLift (u₁ τ)) 1 - deriv (intervalDomainLift (u₂ τ)) 1 = 0
    rw [(hsol₁.regularity.2.2.2.2.1 τ hτ₁).1.2.2,
      (hsol₂.regularity.2.2.2.2.1 τ hτ₂).1.2.2, sub_zero]
  -- integrability of `dwL` and `ddwL` (continuous on `[0,1]`).
  have hdwLint : IntervalIntegrable dwL volume 0 1 := by
    have : ContinuousOn dwL (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hdwLcont
    exact this.intervalIntegrable
  -- integrability of `ddwL`: it agrees on the interior with the closed-`Icc`
  -- second derivative `derivWithin (derivWithin (lift u) Icc) Icc`, which is
  -- continuous on the compact `[0,1]` (closed-`Icc` `C²`), hence integrable; the
  -- two endpoints are null, so interval-integrability transports.
  set ddIcc : ℝ → ℝ := fun y =>
      derivWithin (derivWithin (intervalDomainLift (u₁ τ)) (Set.Icc (0:ℝ) 1)) (Set.Icc (0:ℝ) 1) y
        - derivWithin (derivWithin (intervalDomainLift (u₂ τ)) (Set.Icc (0:ℝ) 1))
            (Set.Icc (0:ℝ) 1) y with hddIcc
  have hddIccCont : ContinuousOn ddIcc (Set.Icc (0:ℝ) 1) := by
    have hcont : ∀ (u : ℝ → intervalDomainPoint → ℝ) {Tj : ℝ} {vj : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p Tj u vj → τ ∈ Set.Ioo (0:ℝ) Tj →
        ContinuousOn (derivWithin (derivWithin (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1))
          (Set.Icc (0:ℝ) 1)) (Set.Icc (0:ℝ) 1) := by
      intro u Tj vj hsolj htj
      have hC : ContDiffOn ℝ 2 (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1) :=
        (hsolj.regularity.2.2.2.2.1 τ htj).1.1
      have huniq : UniqueDiffOn ℝ (Set.Icc (0:ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
      have hd1 : ContDiffOn ℝ 1 (derivWithin (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1))
          (Set.Icc (0:ℝ) 1) := hC.derivWithin huniq (by norm_num)
      exact hd1.continuousOn_derivWithin huniq (by norm_num)
    exact (hcont u₁ hsol₁ hτ₁).sub (hcont u₂ hsol₂ hτ₂)
  have hddIccInt : IntervalIntegrable ddIcc volume 0 1 := by
    have : ContinuousOn ddIcc (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hddIccCont
    exact this.intervalIntegrable
  -- `ddwL = ddIcc` on the open interior (deriv = derivWithin on the open set).
  have hddeq : Set.EqOn ddwL ddIcc (Set.Ioo (0:ℝ) 1) := by
    intro y hy
    have hcong : ∀ (u : ℝ → intervalDomainPoint → ℝ) {Tj : ℝ}
        {vj : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p Tj u vj → τ ∈ Set.Ioo (0:ℝ) Tj →
        deriv (fun z => deriv (intervalDomainLift (u τ)) z) y
          = derivWithin (derivWithin (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1))
              (Set.Icc (0:ℝ) 1) y := by
      intro u Tj vj hsolj htj
      have hC : ContDiffOn ℝ 2 (intervalDomainLift (u τ)) (Set.Ioo (0:ℝ) 1) :=
        (hsolj.regularity.1 τ htj).1
      have hCc : ContDiffOn ℝ 2 (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1) :=
        (hsolj.regularity.2.2.2.2.1 τ htj).1.1
      have huniq : UniqueDiffOn ℝ (Set.Icc (0:ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
      -- inner: deriv (lift u) y = derivWithin (lift u) Icc y on the interior.
      have hinner : ∀ z ∈ Set.Ioo (0:ℝ) 1,
          deriv (intervalDomainLift (u τ)) z
            = derivWithin (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1) z := by
        intro z hz
        have hd : DifferentiableAt ℝ (intervalDomainLift (u τ)) z :=
          (hC.differentiableOn (by norm_num)).differentiableAt (IsOpen.mem_nhds isOpen_Ioo hz)
        rw [hd.derivWithin (huniq.uniqueDiffWithinAt (Set.Ioo_subset_Icc_self hz))]
      -- outer: deriv of the (equal-on-interior) functions at the interior point `y`.
      have hO : deriv (fun z => deriv (intervalDomainLift (u τ)) z) y
          = deriv (fun z => derivWithin (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1) z) y := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [IsOpen.mem_nhds isOpen_Ioo hy] with z hz using hinner z hz
      rw [hO]
      -- finally deriv = derivWithin Icc for the (C¹) function `derivWithin (lift u) Icc`.
      have hd1 : ContDiffOn ℝ 1 (derivWithin (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1))
          (Set.Icc (0:ℝ) 1) := hCc.derivWithin huniq (by norm_num)
      have hdd : DifferentiableAt ℝ (derivWithin (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1)) y :=
        (hd1.differentiableOn (by norm_num)).differentiableAt
          (mem_nhds_iff.2 ⟨Set.Ioo (0:ℝ) 1, Set.Ioo_subset_Icc_self, isOpen_Ioo, hy⟩)
      rw [hdd.derivWithin (huniq.uniqueDiffWithinAt (Set.Ioo_subset_Icc_self hy))]
    show deriv (fun z => deriv (intervalDomainLift (u₁ τ)) z) y
        - deriv (fun z => deriv (intervalDomainLift (u₂ τ)) z) y
      = derivWithin (derivWithin (intervalDomainLift (u₁ τ)) (Set.Icc (0:ℝ) 1))
            (Set.Icc (0:ℝ) 1) y
        - derivWithin (derivWithin (intervalDomainLift (u₂ τ)) (Set.Icc (0:ℝ) 1))
            (Set.Icc (0:ℝ) 1) y
    rw [hcong u₁ hsol₁ hτ₁, hcong u₂ hsol₂ hτ₂]
  have hddwLint : IntervalIntegrable ddwL volume 0 1 := by
    refine hddIccInt.congr_ae ?_
    -- `ddIcc = ddwL` a.e. on `Ι 0 1 = Ioc 0 1`: they agree on `Ioo 0 1`, and `{1}` is null.
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    have hnull : volume ({(1:ℝ)} : Set ℝ) = 0 := Real.volume_singleton
    refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    push_neg at hy
    obtain ⟨hyIoc, hne⟩ := hy
    simp only [Set.mem_singleton_iff]
    by_contra hy1
    exact hne ((hddeq ⟨hyIoc.1, lt_of_le_of_ne hyIoc.2 hy1⟩).symm)
  -- IBP.
  have hibp := intervalEnergyByParts_open
    (w := wL) (w' := dwL) (w'' := ddwL)
    (by rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hwLcont)
    (by rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hdwLcont)
    hwLderiv hdwLderiv hdwLint hddwLint hbc0 hbc1
  exact hibp

/-- **Open-interior flux integration-by-parts** (the chemotaxis cousin of
`intervalEnergyByParts_open`).  Requires only continuity of `φ, F` on `[0,1]`,
interior `HasDerivAt`, integrability, and the flux endpoint vanishing
`F 0 = F 1 = 0`.  `∫₀¹ φ·F' = − ∫₀¹ φ'·F`. -/
theorem intervalFluxByParts_open
    {φ φ' F F' : ℝ → ℝ}
    (hφ_cont : ContinuousOn φ (Set.uIcc (0 : ℝ) 1))
    (hF_cont : ContinuousOn F (Set.uIcc (0 : ℝ) 1))
    (hφ : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt φ (φ' x) x)
    (hF : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F (F' x) x)
    (hφ'int : IntervalIntegrable φ' MeasureTheory.volume 0 1)
    (hF'int : IntervalIntegrable F' MeasureTheory.volume 0 1)
    (hbc0 : F 0 = 0) (hbc1 : F 1 = 0) :
    (∫ x in (0 : ℝ)..1, φ x * F' x) = - ∫ x in (0 : ℝ)..1, φ' x * F x := by
  classical
  have hmm : Set.Ioo (min (0:ℝ) 1) (max 0 1) = Set.Ioo (0:ℝ) 1 := by
    rw [min_eq_left (by norm_num : (0:ℝ) ≤ 1), max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
  have hφ_io : ∀ x ∈ Set.Ioo (min (0:ℝ) 1) (max 0 1), HasDerivAt φ (φ' x) x := by
    rw [hmm]; exact hφ
  have hF_io : ∀ x ∈ Set.Ioo (min (0:ℝ) 1) (max 0 1), HasDerivAt F (F' x) x := by
    rw [hmm]; exact hF
  have hIBP :
      (∫ x in (0:ℝ)..1, φ x * F' x) =
        φ 1 * F 1 - φ 0 * F 0 - ∫ x in (0:ℝ)..1, φ' x * F x :=
    integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hφ_cont hF_cont hφ_io hF_io hφ'int hF'int
  rw [hIBP, hbc0, hbc1]; ring

/-- Interval-integrability of `deriv (intervalFlux p (u τ)(v τ))` over `[0,1]`:
the flux is `C¹` on the closed `[0,1]` (`flux_contDiffOn_Icc`), so `derivWithin …
Icc` is continuous on the compact `[0,1]` (integrable), and `deriv = derivWithin`
on the open interior (the two null endpoints don't affect integrability). -/
theorem solution_deriv_flux_intervalIntegrable
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    IntervalIntegrable (deriv (intervalFlux p (u τ) (v τ))) volume 0 1 := by
  classical
  set f : ℝ → ℝ := intervalFlux p (u τ) (v τ) with hfdef
  have hC1c : ContDiffOn ℝ 1 f (Set.Icc (0:ℝ) 1) := flux_contDiffOn_Icc hsol hτ
  have hC1o : ContDiffOn ℝ 1 f (Set.Ioo (0:ℝ) 1) := flux_contDiffOn_Ioo_of_solution hsol hτ
  have huniq : UniqueDiffOn ℝ (Set.Icc (0:ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  -- continuous closed-Icc derivative.
  have hdWcont : ContinuousOn (derivWithin f (Set.Icc (0:ℝ) 1)) (Set.Icc (0:ℝ) 1) :=
    hC1c.continuousOn_derivWithin huniq (by norm_num)
  have hdWint : IntervalIntegrable (derivWithin f (Set.Icc (0:ℝ) 1)) volume 0 1 := by
    have : ContinuousOn (derivWithin f (Set.Icc (0:ℝ) 1)) (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hdWcont
    exact this.intervalIntegrable
  -- `deriv f = derivWithin f Icc` on the open interior.
  have heq : Set.EqOn (deriv f) (derivWithin f (Set.Icc (0:ℝ) 1)) (Set.Ioo (0:ℝ) 1) := by
    intro z hz
    have hd : DifferentiableAt ℝ f z :=
      (hC1o.differentiableOn (by norm_num)).differentiableAt (IsOpen.mem_nhds isOpen_Ioo hz)
    rw [hd.derivWithin (huniq.uniqueDiffWithinAt (Set.Ioo_subset_Icc_self hz))]
  refine hdWint.congr_ae ?_
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
  have hnull : volume ({(1:ℝ)} : Set ℝ) = 0 := Real.volume_singleton
  refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
  intro y hy
  simp only [Set.mem_setOf_eq] at hy
  push_neg at hy
  obtain ⟨hyIoc, hne⟩ := hy
  simp only [Set.mem_singleton_iff]
  by_contra hy1
  exact hne ((heq ⟨hyIoc.1, lt_of_le_of_ne hyIoc.2 hy1⟩).symm)

/-- **Chemotaxis IBP for the `u`-difference.**  With `wL = lift u₁ − lift u₂`,
`dwL = deriv(lift u₁) − deriv(lift u₂)`,
`∫₀¹ wL·(∂ₓflux₁ − ∂ₓflux₂) = − ∫₀¹ dwL·(flux₁ − flux₂)`,
where `∂ₓfluxᵢ = deriv (intervalFlux p (uᵢ τ)(vᵢ τ))`.  Open-interior flux IBP with
the flux endpoint vanishing (`flux_endpoint_zero`) and `C¹` flux (`flux_contDiffOn_Icc`). -/
theorem uDiff_chemotaxis_ibp
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {τ : ℝ} (hτ₁ : τ ∈ Set.Ioo (0 : ℝ) T₁) (hτ₂ : τ ∈ Set.Ioo (0 : ℝ) T₂) :
    (∫ y in (0:ℝ)..1,
        (intervalDomainLift (u₁ τ) y - intervalDomainLift (u₂ τ) y)
          * (deriv (intervalFlux p (u₁ τ) (v₁ τ)) y
              - deriv (intervalFlux p (u₂ τ) (v₂ τ)) y))
      = - ∫ y in (0:ℝ)..1,
          (deriv (intervalDomainLift (u₁ τ)) y - deriv (intervalDomainLift (u₂ τ)) y)
            * (intervalFlux p (u₁ τ) (v₁ τ) y - intervalFlux p (u₂ τ) (v₂ τ) y) := by
  classical
  set wL : ℝ → ℝ := fun y => intervalDomainLift (u₁ τ) y - intervalDomainLift (u₂ τ) y with hwL
  set dwL : ℝ → ℝ := fun y => deriv (intervalDomainLift (u₁ τ)) y
      - deriv (intervalDomainLift (u₂ τ)) y with hdwL
  set F : ℝ → ℝ := fun y => intervalFlux p (u₁ τ) (v₁ τ) y - intervalFlux p (u₂ τ) (v₂ τ) y with hF
  set F' : ℝ → ℝ := fun y => deriv (intervalFlux p (u₁ τ) (v₁ τ)) y
      - deriv (intervalFlux p (u₂ τ) (v₂ τ)) y with hF'
  -- flux `C¹` on closed `[0,1]`.
  have hfC1 : ContDiffOn ℝ 1 (intervalFlux p (u₁ τ) (v₁ τ)) (Set.Icc (0:ℝ) 1) :=
    flux_contDiffOn_Icc hsol₁ hτ₁
  have hfC2 : ContDiffOn ℝ 1 (intervalFlux p (u₂ τ) (v₂ τ)) (Set.Icc (0:ℝ) 1) :=
    flux_contDiffOn_Icc hsol₂ hτ₂
  -- continuity of `wL` on `[0,1]`.
  have hwLcont : ContinuousOn wL (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (((hsol₁.regularity.2.2.2.2.1 τ hτ₁).1.1).continuousOn).sub
      (((hsol₂.regularity.2.2.2.2.1 τ hτ₂).1.1).continuousOn)
  -- continuity of `F` on `[0,1]`.
  have hFcont : ContinuousOn F (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (hfC1.continuousOn).sub (hfC2.continuousOn)
  -- interior `HasDerivAt wL (dwL x) x`.
  have hwLderiv : ∀ x ∈ Set.Ioo (0:ℝ) 1, HasDerivAt wL (dwL x) x := by
    intro x hx
    exact ((lift_hasDerivAt_interior hsol₁ hτ₁ hx).1).sub
      ((lift_hasDerivAt_interior hsol₂ hτ₂ hx).1)
  -- interior `HasDerivAt F (F' x) x` (flux C¹ on interior).
  have hFderiv : ∀ x ∈ Set.Ioo (0:ℝ) 1, HasDerivAt F (F' x) x := by
    intro x hx
    have hf1 : HasDerivAt (intervalFlux p (u₁ τ) (v₁ τ))
        (deriv (intervalFlux p (u₁ τ) (v₁ τ)) x) x := by
      have hd : DifferentiableAt ℝ (intervalFlux p (u₁ τ) (v₁ τ)) x :=
        ((flux_contDiffOn_Ioo_of_solution hsol₁ hτ₁).differentiableOn (by norm_num)).differentiableAt
          (IsOpen.mem_nhds isOpen_Ioo hx)
      exact hd.hasDerivAt
    have hf2 : HasDerivAt (intervalFlux p (u₂ τ) (v₂ τ))
        (deriv (intervalFlux p (u₂ τ) (v₂ τ)) x) x := by
      have hd : DifferentiableAt ℝ (intervalFlux p (u₂ τ) (v₂ τ)) x :=
        ((flux_contDiffOn_Ioo_of_solution hsol₂ hτ₂).differentiableOn (by norm_num)).differentiableAt
          (IsOpen.mem_nhds isOpen_Ioo hx)
      exact hd.hasDerivAt
    exact hf1.sub hf2
  -- integrability of `dwL` (continuous on `[0,1]`).
  have hdwLint : IntervalIntegrable dwL volume 0 1 := by
    have : ContinuousOn dwL (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact (solution_deriv_lift_continuousOn_Icc hsol₁ hτ₁).sub
        (solution_deriv_lift_continuousOn_Icc hsol₂ hτ₂)
    exact this.intervalIntegrable
  -- integrability of `F'` (difference of two integrable flux-derivatives).
  have hF'int : IntervalIntegrable F' volume 0 1 :=
    (solution_deriv_flux_intervalIntegrable hsol₁ hτ₁).sub
      (solution_deriv_flux_intervalIntegrable hsol₂ hτ₂)
  -- endpoint vanishing of `F`.
  have hbc0 : F 0 = 0 := by
    show intervalFlux p (u₁ τ) (v₁ τ) 0 - intervalFlux p (u₂ τ) (v₂ τ) 0 = 0
    rw [(flux_endpoint_zero hsol₁ hτ₁).1, (flux_endpoint_zero hsol₂ hτ₂).1, sub_zero]
  have hbc1 : F 1 = 0 := by
    show intervalFlux p (u₁ τ) (v₁ τ) 1 - intervalFlux p (u₂ τ) (v₂ τ) 1 = 0
    rw [(flux_endpoint_zero hsol₁ hτ₁).2, (flux_endpoint_zero hsol₂ hτ₂).2, sub_zero]
  exact intervalFluxByParts_open hwLcont hFcont hwLderiv hFderiv hdwLint hF'int hbc0 hbc1

/-- Interval-integrability of `deriv (deriv (lift (u τ)))` over `[0,1]` (closed-`Icc`
`C²` ⇒ `derivWithin²` continuous; `deriv² = derivWithin²` on the interior). -/
theorem solution_lap_lift_intervalIntegrable
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    IntervalIntegrable
      (fun y => deriv (fun z => deriv (intervalDomainLift (u τ)) z) y) volume 0 1 := by
  classical
  have hCc : ContDiffOn ℝ 2 (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 τ hτ).1.1
  have hCo : ContDiffOn ℝ 2 (intervalDomainLift (u τ)) (Set.Ioo (0:ℝ) 1) :=
    (hsol.regularity.1 τ hτ).1
  have huniq : UniqueDiffOn ℝ (Set.Icc (0:ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  set ddIcc : ℝ → ℝ := derivWithin (derivWithin (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1))
    (Set.Icc (0:ℝ) 1) with hddIcc
  have hd1 : ContDiffOn ℝ 1 (derivWithin (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1))
      (Set.Icc (0:ℝ) 1) := hCc.derivWithin huniq (by norm_num)
  have hddIccCont : ContinuousOn ddIcc (Set.Icc (0:ℝ) 1) :=
    hd1.continuousOn_derivWithin huniq (by norm_num)
  have hddIccInt : IntervalIntegrable ddIcc volume 0 1 := by
    have : ContinuousOn ddIcc (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hddIccCont
    exact this.intervalIntegrable
  have heq : Set.EqOn (fun y => deriv (fun z => deriv (intervalDomainLift (u τ)) z) y)
      ddIcc (Set.Ioo (0:ℝ) 1) := by
    intro y hy
    have hinner : ∀ z ∈ Set.Ioo (0:ℝ) 1,
        deriv (intervalDomainLift (u τ)) z
          = derivWithin (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1) z := by
      intro z hz
      have hd : DifferentiableAt ℝ (intervalDomainLift (u τ)) z :=
        (hCo.differentiableOn (by norm_num)).differentiableAt (IsOpen.mem_nhds isOpen_Ioo hz)
      rw [hd.derivWithin (huniq.uniqueDiffWithinAt (Set.Ioo_subset_Icc_self hz))]
    have hO : deriv (fun z => deriv (intervalDomainLift (u τ)) z) y
        = deriv (derivWithin (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1)) y := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [IsOpen.mem_nhds isOpen_Ioo hy] with z hz using hinner z hz
    have hdd : DifferentiableAt ℝ (derivWithin (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1)) y :=
      (hd1.differentiableOn (by norm_num)).differentiableAt
        (mem_nhds_iff.2 ⟨Set.Ioo (0:ℝ) 1, Set.Ioo_subset_Icc_self, isOpen_Ioo, hy⟩)
    show deriv (fun z => deriv (intervalDomainLift (u τ)) z) y = ddIcc y
    rw [hO, hddIcc, hdd.derivWithin (huniq.uniqueDiffWithinAt (Set.Ioo_subset_Icc_self hy))]
  refine hddIccInt.congr_ae ?_
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
  have hnull : volume ({(1:ℝ)} : Set ℝ) = 0 := Real.volume_singleton
  refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
  intro y hy
  simp only [Set.mem_setOf_eq] at hy
  push_neg at hy
  obtain ⟨hyIoc, hne⟩ := hy
  simp only [Set.mem_singleton_iff]
  by_contra hy1
  exact hne ((heq ⟨hyIoc.1, lt_of_le_of_ne hyIoc.2 hy1⟩).symm)

/-! ### The main parabolic energy differential inequality `Eprime ≤ K·E_u` -/

/-- **The `u`-energy differential inequality (integral form).**  For two positive
classical solutions sharing the overlap horizon,
`∫₀¹ intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ ≤ K · E_u(τ)` with `K ≥ 0`.
This is the `Eprime τ ≤ K·E_u τ` half of the frontier's `diffIneq` (the
`Eprime τ` is exactly `∫₀¹ intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ`, produced
by the Leibniz half).  PDE substitution + Neumann IBP dissipation
(`uDiff_dissipation`) + chemotaxis IBP (`uDiff_chemotaxis_ibp`) + Young absorption
with `flux_diff_L2_le_Eu_of_solution` + reaction Lipschitz
(`intervalLogisticSource_lipschitz`).  Young split: `|χ₀|·|∫ dwL·g|
≤ ½∫(dwL)² + ½χ₀²∫g²`, dropping `−½∫(dwL)² ≤ 0`. -/
theorem intervalDomainL2U_energy_diffIneq_bound
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) (min T₁ T₂)) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∫ y in (0:ℝ)..1, intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ y)
        ≤ K * intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ := by
  classical
  have hτ₁ : τ ∈ Set.Ioo (0:ℝ) T₁ := ⟨hτ.1, lt_of_lt_of_le hτ.2 (min_le_left _ _)⟩
  have hτ₂ : τ ∈ Set.Ioo (0:ℝ) T₂ := ⟨hτ.1, lt_of_lt_of_le hτ.2 (min_le_right _ _)⟩
  set Eu : ℝ := intervalDomainClassicalL2DifferenceEnergyU u₁ u₂ τ with hEu
  have hEu_nn : 0 ≤ Eu := intervalDomainClassicalL2DifferenceEnergyU_nonneg u₁ u₂ τ
  -- abbreviations.
  set wL : ℝ → ℝ := fun y => intervalDomainLift (u₁ τ) y - intervalDomainLift (u₂ τ) y with hwL
  set dwL : ℝ → ℝ := fun y => deriv (intervalDomainLift (u₁ τ)) y
      - deriv (intervalDomainLift (u₂ τ)) y with hdwL
  set Lap : ℝ → ℝ := fun y => deriv (fun z => deriv (intervalDomainLift (u₁ τ)) z) y
      - deriv (fun z => deriv (intervalDomainLift (u₂ τ)) z) y with hLap
  set Fd : ℝ → ℝ := fun y => deriv (intervalFlux p (u₁ τ) (v₁ τ)) y
      - deriv (intervalFlux p (u₂ τ) (v₂ τ)) y with hFd
  set Flx : ℝ → ℝ := fun y => intervalFlux p (u₁ τ) (v₁ τ) y - intervalFlux p (u₂ τ) (v₂ τ) y
    with hFlx
  set Rx : ℝ → ℝ := fun y => intervalDomainLift (u₁ τ) y
        * (p.a - p.b * intervalDomainLift (u₁ τ) y ^ p.α)
      - intervalDomainLift (u₂ τ) y * (p.a - p.b * intervalDomainLift (u₂ τ) y ^ p.α) with hRx
  -- (1) the Leibniz integrand equals `2·wL·(Lap − χ₀·Fd + Rx)` on the interior.
  have hintegrand : Set.EqOn (intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ)
      (fun y => 2 * wL y * (Lap y - p.χ₀ * Fd y + Rx y)) (Set.Ioo (0:ℝ) 1) := by
    intro y hy
    unfold intervalDomainUEnergyIntegrandDeriv
    rw [intervalDomainLift_uDiff_eq u₁ u₂ τ y,
      intervalDomainUEnergy_timeDeriv_pde hsol₁ hsol₂ hτ hy]
  -- continuity / integrability building blocks.
  have hwLcont : ContinuousOn wL (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (((hsol₁.regularity.2.2.2.2.1 τ hτ₁).1.1).continuousOn).sub
      (((hsol₂.regularity.2.2.2.2.1 τ hτ₂).1.1).continuousOn)
  have hwLcontI : ContinuousOn wL (Set.Icc (0:ℝ) 1) := by
    rw [← Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hwLcont
  have hdwLint : IntervalIntegrable dwL volume 0 1 := by
    have : ContinuousOn dwL (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact (solution_deriv_lift_continuousOn_Icc hsol₁ hτ₁).sub
        (solution_deriv_lift_continuousOn_Icc hsol₂ hτ₂)
    exact this.intervalIntegrable
  have hLapint : IntervalIntegrable Lap volume 0 1 :=
    (solution_lap_lift_intervalIntegrable hsol₁ hτ₁).sub
      (solution_lap_lift_intervalIntegrable hsol₂ hτ₂)
  have hFdint : IntervalIntegrable Fd volume 0 1 :=
    (solution_deriv_flux_intervalIntegrable hsol₁ hτ₁).sub
      (solution_deriv_flux_intervalIntegrable hsol₂ hτ₂)
  -- `Rx` continuous on `[0,1]` (products/powers of the continuous lift).
  have hRxcont : ContinuousOn Rx (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    have hcu : ∀ (u : ℝ → intervalDomainPoint → ℝ) {Tj : ℝ}
        {vj : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p Tj u vj → τ ∈ Set.Ioo (0:ℝ) Tj →
        ContinuousOn (fun y => intervalDomainLift (u τ) y
          * (p.a - p.b * intervalDomainLift (u τ) y ^ p.α)) (Set.Icc (0:ℝ) 1) := by
      intro u Tj vj hsolj htj
      have hc : ContinuousOn (intervalDomainLift (u τ)) (Set.Icc (0:ℝ) 1) :=
        ((hsolj.regularity.2.2.2.2.1 τ htj).1.1).continuousOn
      have hpow : ContinuousOn (fun y => intervalDomainLift (u τ) y ^ p.α) (Set.Icc (0:ℝ) 1) :=
        hc.rpow_const (fun y hy => Or.inl (ne_of_gt (solution_lift_pos hsolj htj y hy)))
      exact hc.mul (continuousOn_const.sub (continuousOn_const.mul hpow))
    exact (hcu u₁ hsol₁ hτ₁).sub (hcu u₂ hsol₂ hτ₂)
  -- products integrable.
  have hwLLap : IntervalIntegrable (fun y => wL y * Lap y) volume 0 1 :=
    hLapint.continuousOn_mul hwLcont
  have hwLFd : IntervalIntegrable (fun y => wL y * Fd y) volume 0 1 :=
    hFdint.continuousOn_mul hwLcont
  have hwLRx : IntervalIntegrable (fun y => wL y * Rx y) volume 0 1 := by
    have hRxint : IntervalIntegrable Rx volume 0 1 := hRxcont.intervalIntegrable
    exact hRxint.continuousOn_mul hwLcont
  -- (2) integral of the Leibniz integrand = integral of the substituted form (a.e. interior).
  have hIeq : (∫ y in (0:ℝ)..1, intervalDomainUEnergyIntegrandDeriv u₁ u₂ τ y)
      = ∫ y in (0:ℝ)..1, 2 * wL y * (Lap y - p.χ₀ * Fd y + Rx y) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hnull : volume ({(1:ℝ)} : Set ℝ) = 0 := Real.volume_singleton
    refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    push_neg at hy
    obtain ⟨hyIoc0, hne⟩ := hy
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hyIoc0
    simp only [Set.mem_singleton_iff]
    by_contra hy1
    exact hne (hintegrand ⟨hyIoc0.1, lt_of_le_of_ne hyIoc0.2 hy1⟩)
  -- (3) split by linearity:  2∫wL·Lap − 2χ₀∫wL·Fd + 2∫wL·Rx.
  have hsplit : (∫ y in (0:ℝ)..1, 2 * wL y * (Lap y - p.χ₀ * Fd y + Rx y))
      = 2 * (∫ y in (0:ℝ)..1, wL y * Lap y)
        - 2 * p.χ₀ * (∫ y in (0:ℝ)..1, wL y * Fd y)
        + 2 * (∫ y in (0:ℝ)..1, wL y * Rx y) := by
    have hcongr : (fun y => 2 * wL y * (Lap y - p.χ₀ * Fd y + Rx y))
        = fun y => 2 * (wL y * Lap y) + (- (2 * p.χ₀)) * (wL y * Fd y)
            + 2 * (wL y * Rx y) := by
      funext y; ring
    rw [hcongr]
    rw [intervalIntegral.integral_add
        ((hwLLap.const_mul 2).add (hwLFd.const_mul (-(2*p.χ₀)))) (hwLRx.const_mul 2),
      intervalIntegral.integral_add (hwLLap.const_mul 2) (hwLFd.const_mul (-(2*p.χ₀))),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    ring
  -- (4) substitute the two IBP identities.
  have hdiss := uDiff_dissipation hsol₁ hsol₂ hτ₁ hτ₂
  have hchem := uDiff_chemotaxis_ibp hsol₁ hsol₂ hτ₁ hτ₂
  set D : ℝ := ∫ y in (0:ℝ)..1, (dwL y) ^ 2 with hD
  have hD_nn : 0 ≤ D := by
    rw [hD]; refine intervalIntegral.integral_nonneg (by norm_num) (fun y _ => by positivity)
  -- `∫ wL·Lap = −D`.
  have hwLLap_eq : (∫ y in (0:ℝ)..1, wL y * Lap y) = - D := by
    rw [hD]; exact hdiss
  -- `∫ wL·Fd = − ∫ dwL·Flx`.
  have hwLFd_eq : (∫ y in (0:ℝ)..1, wL y * Fd y)
      = - ∫ y in (0:ℝ)..1, dwL y * Flx y := hchem
  -- (5) the flux L² bound + reaction Lipschitz bound.
  obtain ⟨Cflux, hCflux_nn, hCflux⟩ := flux_diff_L2_le_Eu_of_solution hsol₁ hsol₂ hτ₁ hτ₂
  -- `∫ Flx² ≤ Cflux·Eu`.
  set Sflx : ℝ := ∫ y in (0:ℝ)..1, (Flx y) ^ 2 with hSflx
  have hSflx_eq : Sflx ≤ Cflux * Eu := by rw [hSflx, hEu, hFlx]; exact hCflux
  have hSflx_nn : 0 ≤ Sflx := by
    rw [hSflx]; refine intervalIntegral.integral_nonneg (by norm_num) (fun y _ => by positivity)
  -- integrability of `dwL·Flx`, `dwL²`, `Flx²`.
  have hFlxcont : ContinuousOn Flx (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ((flux_contDiffOn_Icc hsol₁ hτ₁).continuousOn).sub
      ((flux_contDiffOn_Icc hsol₂ hτ₂).continuousOn)
  have hdwLcont : ContinuousOn dwL (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (solution_deriv_lift_continuousOn_Icc hsol₁ hτ₁).sub
      (solution_deriv_lift_continuousOn_Icc hsol₂ hτ₂)
  have hdwLFxint : IntervalIntegrable (fun y => dwL y * Flx y) volume 0 1 :=
    (hdwLint.mul_continuousOn hFlxcont)
  have hdwLsqint : IntervalIntegrable (fun y => (dwL y) ^ 2) volume 0 1 := by
    have : ContinuousOn (fun y => (dwL y) ^ 2) (Set.uIcc (0:ℝ) 1) := hdwLcont.pow 2
    exact this.intervalIntegrable
  have hFlxsqint : IntervalIntegrable (fun y => (Flx y) ^ 2) volume 0 1 := by
    have : ContinuousOn (fun y => (Flx y) ^ 2) (Set.uIcc (0:ℝ) 1) := hFlxcont.pow 2
    exact this.intervalIntegrable
  -- Young pointwise:  2·χ₀·(dwL·Flx) ≤ dwL² + χ₀²·Flx².  So
  -- `2·χ₀·∫dwL·Flx ≤ D + χ₀²·Sflx`.
  have hYoung : 2 * p.χ₀ * (∫ y in (0:ℝ)..1, dwL y * Flx y) ≤ D + p.χ₀ ^ 2 * Sflx := by
    have hptw : ∀ y, 2 * p.χ₀ * (dwL y * Flx y) ≤ (dwL y) ^ 2 + p.χ₀ ^ 2 * (Flx y) ^ 2 := by
      intro y; nlinarith [sq_nonneg (dwL y - p.χ₀ * Flx y)]
    have hmono : (∫ y in (0:ℝ)..1, 2 * p.χ₀ * (dwL y * Flx y))
        ≤ ∫ y in (0:ℝ)..1, ((dwL y) ^ 2 + p.χ₀ ^ 2 * (Flx y) ^ 2) := by
      refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ (fun y _ => hptw y)
      · exact hdwLFxint.const_mul _
      · exact hdwLsqint.add (hFlxsqint.const_mul _)
    rw [intervalIntegral.integral_const_mul] at hmono
    rw [intervalIntegral.integral_add hdwLsqint (hFlxsqint.const_mul _),
      intervalIntegral.integral_const_mul] at hmono
    rw [hD, hSflx]; linarith
  -- reaction Lipschitz:  `|∫ wL·Rx| ≤ ∫ |wL·Rx| ≤ L·∫wL² = L·Eu`.
  obtain ⟨M, hMnn, hMu₁⟩ := lift_u_bounded hsol₁ hτ₁
  obtain ⟨M₂, hM₂nn, hMu₂⟩ := lift_u_bounded hsol₂ hτ₂
  set Mm : ℝ := max M M₂ + 1 with hMm
  have hMm_pos : 0 < Mm := by rw [hMm]; positivity
  obtain ⟨L, hLpos, hLip⟩ :=
    ShenWork.IntervalDomainExistence.intervalLogisticSource_lipschitz p hMm_pos
  -- `∫ wL·Rx ≤ L·Eu`  and  `−L·Eu ≤ ∫ wL·Rx` (via `|wL·Rx| ≤ L·wL²` pointwise).
  have hwL2int : IntervalIntegrable (fun y => wL y ^ 2) volume 0 1 := by
    have : ContinuousOn (fun y => wL y ^ 2) (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hwLcontI.pow 2
    exact this.intervalIntegrable
  have hwL2_eq_Eu : (∫ y in (0:ℝ)..1, wL y ^ 2) = Eu := by
    rw [hEu, ← lift_u_diff_sq_integral_eq_Eu u₁ u₂ τ]
  -- pointwise `wL·Rx ≤ L·wL²` and `−L·wL² ≤ wL·Rx` on `[0,1]`.
  have hRxbound : ∀ y ∈ Set.Icc (0:ℝ) 1, |Rx y| ≤ L * |wL y| := by
    intro y hy
    have ha₁ : |intervalDomainLift (u₁ τ) y| ≤ Mm := by
      rw [hMm]; exact le_trans (hMu₁ y hy) (by have := le_max_left M M₂; linarith)
    have ha₂ : |intervalDomainLift (u₂ τ) y| ≤ Mm := by
      rw [hMm]; exact le_trans (hMu₂ y hy) (by have := le_max_right M M₂; linarith)
    have := hLip (intervalDomainLift (u₁ τ) y) (intervalDomainLift (u₂ τ) y) ha₁ ha₂
    rw [hRx, hwL]; exact this
  have hptwRx : ∀ y ∈ Set.Icc (0:ℝ) 1, wL y * Rx y ≤ L * wL y ^ 2 := by
    intro y hy
    have h1 : wL y * Rx y ≤ |wL y * Rx y| := le_abs_self _
    have h2 : |wL y * Rx y| ≤ L * wL y ^ 2 := by
      rw [abs_mul]
      calc |wL y| * |Rx y| ≤ |wL y| * (L * |wL y|) :=
            mul_le_mul_of_nonneg_left (hRxbound y hy) (abs_nonneg _)
        _ = L * (|wL y| * |wL y|) := by ring
        _ = L * wL y ^ 2 := by rw [abs_mul_abs_self]; ring
    exact le_trans h1 h2
  have hLwL2int : IntervalIntegrable (fun y => L * wL y ^ 2) volume 0 1 := hwL2int.const_mul L
  have hwLRx_le : (∫ y in (0:ℝ)..1, wL y * Rx y) ≤ L * Eu := by
    have hmono := intervalIntegral.integral_mono_on (by norm_num) hwLRx hLwL2int hptwRx
    rw [intervalIntegral.integral_const_mul, hwL2_eq_Eu] at hmono
    exact hmono
  -- assemble:  I = 2·(−D) − 2χ₀·(−∫dwL·Flx) + 2·∫wL·Rx
  --              = −2D + 2χ₀·∫dwL·Flx + 2·∫wL·Rx
  --              ≤ −2D + (D + χ₀²·Sflx) + 2·(L·Eu)   [Young, drop nothing here]
  --              = −D + χ₀²·Sflx + 2L·Eu ≤ χ₀²·Cflux·Eu + 2L·Eu  (drop −D ≤ 0).
  refine ⟨p.χ₀ ^ 2 * Cflux + 2 * L, by positivity, ?_⟩
  rw [hIeq, hsplit, hwLLap_eq, hwLFd_eq]
  -- LHS = 2·(−D) − 2χ₀·(−∫dwL·Flx) + 2·∫wL·Rx.
  have hkey : 2 * (-D) - 2 * p.χ₀ * (- ∫ y in (0:ℝ)..1, dwL y * Flx y)
      + 2 * (∫ y in (0:ℝ)..1, wL y * Rx y)
      ≤ (p.χ₀ ^ 2 * Cflux + 2 * L) * Eu := by
    have h1 : 2 * p.χ₀ * (∫ y in (0:ℝ)..1, dwL y * Flx y) ≤ D + p.χ₀ ^ 2 * Sflx := hYoung
    have h2 : (∫ y in (0:ℝ)..1, wL y * Rx y) ≤ L * Eu := hwLRx_le
    have h3 : p.χ₀ ^ 2 * Sflx ≤ p.χ₀ ^ 2 * (Cflux * Eu) :=
      mul_le_mul_of_nonneg_left hSflx_eq (by positivity)
    nlinarith [hD_nn, h1, h2, h3]
  exact hkey

/-! ### Closed-slab joint continuity of the `u`-energy integrand time-derivative

For GENERAL positive classical solutions (not merely time-constant), the integrand
time-derivative field `(s,y) ↦ 2·(lift(u₁s−u₂s)y)·∂ₛ(lift(u₁s−u₂s)y)` is jointly
continuous on a closed slab `Icc(τ−δ,τ+δ) ×ˢ Icc 0 1 ⊆ Ioo 0 (min T₁ T₂) ×ˢ Icc 0 1`,
from regularity conjuncts (8) (`∂ₜ`-field continuity) and (9) (solution-field
continuity), once `∂ₛ` of the difference is rewritten as the difference of the two
`∂ₛ` fields (valid on the open-time interior, where both slices are differentiable). -/
theorem intervalDomainUEnergyIntegrandDeriv_continuousOn_closedSlab
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {τ δ : ℝ} (hδ : 0 < δ)
    (hslab : Set.Icc (τ - δ) (τ + δ) ⊆ Set.Ioo (0:ℝ) (min T₁ T₂)) :
    ContinuousOn
      (Function.uncurry (intervalDomainUEnergyIntegrandDeriv u₁ u₂))
      (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  classical
  -- conjunct (9): joint continuity of the solution fields on `Ioo 0 Tⱼ ×ˢ Icc 0 1`.
  have hfield₁ := (hsol₁.regularity.2.2.2.2.2.2).1
  have hfield₂ := (hsol₂.regularity.2.2.2.2.2.2).1
  -- conjunct (8): joint continuity of the `∂ₜ` fields on `Ioo 0 Tⱼ ×ˢ Icc 0 1`.
  have hdt₁ := (hsol₁.regularity.2.2.2.2.2.1).1
  have hdt₂ := (hsol₂.regularity.2.2.2.2.2.1).1
  -- the slab is `⊆ Ioo 0 Tⱼ ×ˢ Icc 0 1` for each `j`.
  have hsub₁ : Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0:ℝ) 1
      ⊆ Set.Ioo (0:ℝ) T₁ ×ˢ Set.Icc (0:ℝ) 1 := by
    rintro ⟨s, y⟩ ⟨hs, hy⟩
    exact ⟨⟨(hslab hs).1, lt_of_lt_of_le (hslab hs).2 (min_le_left _ _)⟩, hy⟩
  have hsub₂ : Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0:ℝ) 1
      ⊆ Set.Ioo (0:ℝ) T₂ ×ˢ Set.Icc (0:ℝ) 1 := by
    rintro ⟨s, y⟩ ⟨hs, hy⟩
    exact ⟨⟨(hslab hs).1, lt_of_lt_of_le (hslab hs).2 (min_le_right _ _)⟩, hy⟩
  -- continuity of the solution field difference factor `A(s,y) = lift(u₁s−u₂s)y`.
  have hA : ContinuousOn (fun q : ℝ × ℝ =>
      intervalDomainLift (fun x => u₁ q.1 x - u₂ q.1 x) q.2)
      (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0:ℝ) 1) := by
    have h1 : ContinuousOn (fun q : ℝ × ℝ => intervalDomainLift (u₁ q.1) q.2)
        (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0:ℝ) 1) := hfield₁.mono hsub₁
    have h2 : ContinuousOn (fun q : ℝ × ℝ => intervalDomainLift (u₂ q.1) q.2)
        (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0:ℝ) 1) := hfield₂.mono hsub₂
    refine (h1.sub h2).congr (fun q hq => ?_)
    exact intervalDomainLift_uDiff_eq u₁ u₂ q.1 q.2
  -- continuity of the `∂ₛ` difference factor `B(s,y) = ∂ₛ(lift(u₁s−u₂s)y)`.
  have hB : ContinuousOn (fun q : ℝ × ℝ =>
      deriv (fun r => intervalDomainLift (fun x => u₁ r x - u₂ r x) q.2) q.1)
      (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0:ℝ) 1) := by
    have h1 : ContinuousOn (fun q : ℝ × ℝ =>
        deriv (fun r => intervalDomainLift (u₁ r) q.2) q.1)
        (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0:ℝ) 1) := hdt₁.mono hsub₁
    have h2 : ContinuousOn (fun q : ℝ × ℝ =>
        deriv (fun r => intervalDomainLift (u₂ r) q.2) q.1)
        (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0:ℝ) 1) := hdt₂.mono hsub₂
    refine (h1.sub h2).congr (fun q hq => ?_)
    obtain ⟨hs, hy⟩ := hq
    -- `∂ₛ(lift(u₁−u₂)y) = ∂ₛ lift(u₁)y − ∂ₛ lift(u₂)y` at interior times.
    have hsIoo₁ : q.1 ∈ Set.Ioo (0:ℝ) T₁ := (hsub₁ ⟨hs, hy⟩).1
    have hsIoo₂ : q.1 ∈ Set.Ioo (0:ℝ) T₂ := (hsub₂ ⟨hs, hy⟩).1
    by_cases hyIcc : q.2 ∈ Set.Icc (0:ℝ) 1
    · set x : intervalDomainPoint := ⟨q.2, hyIcc⟩ with hx
      have heq : (fun r => intervalDomainLift (fun z => u₁ r z - u₂ r z) q.2)
          = fun r => u₁ r x - u₂ r x := by
        funext r; simp [intervalDomainLift, hyIcc, hx]
      have heq1 : (fun r => intervalDomainLift (u₁ r) q.2) = fun r => u₁ r x := by
        funext r; simp [intervalDomainLift, hyIcc, hx]
      have heq2 : (fun r => intervalDomainLift (u₂ r) q.2) = fun r => u₂ r x := by
        funext r; simp [intervalDomainLift, hyIcc, hx]
      -- differentiability of the time slices at `x`: conjunct (4) is now
      -- UNCONDITIONAL in `x` (closed-domain time `C¹`), so it covers the open
      -- interior AND the two Neumann endpoints `{0,1}` directly — no separate
      -- boundary hypothesis is needed.
      have hdd : DifferentiableAt ℝ (fun r => u₁ r x) q.1
          ∧ DifferentiableAt ℝ (fun r => u₂ r x) q.1 :=
        ⟨(hsol₁.regularity.2.1 x q.1 hsIoo₁).1.1,
          (hsol₂.regularity.2.1 x q.1 hsIoo₂).1.1⟩
      -- the slices, as functions of `r`, are `u₁ · x − u₂ · x` etc; use `HasDerivAt`.
      have hH1 : HasDerivAt (fun r => intervalDomainLift (u₁ r) q.2)
          (deriv (fun r => u₁ r x) q.1) q.1 := by
        rw [heq1]; exact hdd.1.hasDerivAt
      have hH2 : HasDerivAt (fun r => intervalDomainLift (u₂ r) q.2)
          (deriv (fun r => u₂ r x) q.1) q.1 := by
        rw [heq2]; exact hdd.2.hasDerivAt
      have hHd : HasDerivAt (fun r => intervalDomainLift (fun z => u₁ r z - u₂ r z) q.2)
          (deriv (fun r => u₁ r x) q.1 - deriv (fun r => u₂ r x) q.1) q.1 := by
        rw [heq]; exact (hdd.1.hasDerivAt).sub (hdd.2.hasDerivAt)
      show deriv (fun r => intervalDomainLift (fun z => u₁ r z - u₂ r z) q.2) q.1
        = deriv (fun r => intervalDomainLift (u₁ r) q.2) q.1
          - deriv (fun r => intervalDomainLift (u₂ r) q.2) q.1
      rw [hHd.deriv, hH1.deriv, hH2.deriv]
    · -- `y ∉ [0,1]`: every lift is `0`, so all three derivatives are `0`.
      have hz : ∀ (u : ℝ → intervalDomainPoint → ℝ),
          (fun r => intervalDomainLift (u r) q.2) = fun _ => (0:ℝ) := by
        intro u; funext r; simp [intervalDomainLift, hyIcc]
      have hzd : (fun r => intervalDomainLift (fun z => u₁ r z - u₂ r z) q.2)
          = fun _ => (0:ℝ) := by funext r; simp [intervalDomainLift, hyIcc]
      rw [hzd, hz u₁, hz u₂]; simp
  -- the integrand-deriv is `2·A·B`.
  have hform : Function.uncurry (intervalDomainUEnergyIntegrandDeriv u₁ u₂)
      = fun q : ℝ × ℝ => 2 * (intervalDomainLift (fun x => u₁ q.1 x - u₂ q.1 x) q.2)
          * deriv (fun r => intervalDomainLift (fun x => u₁ r x - u₂ r x) q.2) q.1 := by
    funext q; obtain ⟨s, y⟩ := q; rfl
  rw [hform]
  exact (continuousOn_const.mul hA).mul hB

end

end ShenWork.Paper2

#print axioms ShenWork.Paper2.resolverGradReal_holder_Icc
