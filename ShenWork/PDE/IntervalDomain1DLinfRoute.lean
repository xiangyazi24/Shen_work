import ShenWork.PDE.IntervalAgmonInterpolation
import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
import ShenWork.Paper2.IntervalDomainCrossDiffusionBootstrap
import ShenWork.Paper2.IntervalDomainLpMonotonicity

/-!
# 1D L∞ route to Proposition 2.5 via Sobolev embedding

In 1D (the concrete `intervalDomain` = [0,1]), the L∞ bound does NOT
require Moser iteration. Instead:

1. **Energy + Gronwall → L² bound** (pointwise in time)
2. **1D Sobolev** (Agmon for g = u^{p/2}) → pointwise `u(x)^p ≤ C(∫u^p + ∫|∇(u^{p/2})|²)`
3. **Gradient bound** from the energy identity → `∫|∇(u^{p/2})|²(t) ≤ C'` (pointwise in time)
4. **Combining 2+3**: `‖u(t)‖∞^p ≤ C(M_p + G_p)` → L∞ bound
5. **L∞ → all Lp**: `∫u^r ≤ ‖u‖∞^{r-1} ∫u` → all Lp bounds → Prop 2.5

## Key difference from higher dimensions

In N ≥ 2, the Gagliardo-Nirenberg critical exponent matches the Moser
gradient, so `RelativeMoserInterpolationBefore` holds with a LINEAR
lower-order term. In N = 1, the Sobolev embedding gives H¹ → L∞ (any
exponent), but the interpolation is SUPERLINEAR:
  `∫u^{p+ρ} ≤ ε·∫|∇(u^{p/2})|² + C_ε·(∫u^p)^{p/(p-ρ)}`

The superlinear term breaks the threshold plan's first-crossing argument.
The direct Sobolev route avoids this entirely.

## Parameter condition

The L² energy estimate closes (Gronwall gives global bound) under the
paper's subcritical condition: the logistic damping `a - bu^m` with
`m > 1` beats the chemotaxis growth (α > ρ in the abstract framework).
-/

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.IntervalDomain1DLinfRoute

/-! ### Step 1: L^p energy → integrated dissipation bound

From `LpBootstrapEnergyInequality` at exponent p:
  `(1/p) Y'(t) + A·G(t) + B·Y(t) ≤ K·Z(t) + L`

where Y = ∫u^p, G = ∫|∇(u^{p/2})|², Z = ∫u^{p+ρ}.

Under the parameter condition (α > ρ), absorb Z using the logistic:
  `Z = ∫u^{p+ρ} ≤ ε·∫u^{p+α} + C_ε·∫u^p` (Young for powers, α > ρ)

The logistic damping gives `-b·∫u^{p+α}` in the energy, absorbing the Z term.

After absorption: `Y'(t) + c·G(t) ≤ C₁·Y(t) + C₂`

Gronwall → Y(t) bounded → integrated G bounded.
-/

theorem intervalDomain_Lp_energy_and_dissipation_of_regularity
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u
        (params.N : ℝ) T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hlogistic_dominates : rho < params.α)
    {pExp : ℝ} (hpExp : p0 ≤ pExp) :
    ∃ M_Lp M_diss : ℝ,
      0 ≤ M_Lp ∧ 0 ≤ M_diss ∧
      (∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x => (u t x) ^ pExp) ≤ M_Lp) ∧
      (∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) ≤ M_diss) := by
  sorry

/-! ### Step 2: Pointwise L∞ from Lp + gradient via 1D Sobolev

From `intervalDomainLift_rpow_agmon_bound` (proved Agmon for g = u^{p/2}):
  `u(x)^p ≤ 2·∫u^p + 2·√(∫u^p)·√(∫|∇(u^{p/2})|²)`

With ∫u^p ≤ M_Lp and ∫|∇(u^{p/2})|² ≤ M_diss:
  `‖u(t)‖∞^p ≤ 2·M_Lp + 2·√M_Lp·√M_diss`
-/

theorem intervalDomain_Linf_of_Lp_and_gradient
    {params : CM2Params} {T pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hpExp : 2 ≤ pExp)
    {M_Lp M_diss : ℝ}
    (hMLp : 0 ≤ M_Lp)
    (hMdiss : 0 ≤ M_diss)
    (hLp_bound : ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x => (u t x) ^ pExp) ≤ M_Lp)
    (hgrad_bound : ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x =>
        (intervalDomain.gradNorm
          (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) ≤ M_diss) :
    ∀ t, 0 < t → t < T →
      ∀ x : intervalDomain.Point,
        (u t x) ^ pExp ≤
          2 * M_Lp + 2 * Real.sqrt M_Lp * Real.sqrt M_diss := by
  intro t ht0 htT x
  have hf_pos : ∀ z : intervalDomain.Point, 0 < u t z :=
    fun z => hsol.u_pos' ht0 htT
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hC2 : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hagmon := intervalDomainLift_rpow_agmon_bound (q := pExp) hf_pos hC2 x.2
  have hlift : intervalDomainLift (u t) x.1 = u t x := by
    simp [intervalDomainLift, x.2]
  rw [hlift] at hagmon
  have hchain :=
    intervalDomain_moser_gradient_integral_eq_weighted_of_regularity
      (params := params) (T := T) (pExp := pExp) (u := u) (v := v)
      hsol ht0 htT
  sorry

/-! ### Step 3: L∞ → all Lp bounds

With `‖u(t)‖∞ ≤ M_inf` and `∫u ≤ M_mass`:
  `∫u^r ≤ ‖u‖∞^{r-1} · ∫u ≤ M_inf^{r-1} · M_mass`
-/

theorem intervalDomain_all_Lp_of_Linf
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    {M_inf : ℝ} (hMinf : 0 ≤ M_inf)
    (hLinf : ∀ t, 0 < t → t < T →
      ∀ x : intervalDomain.Point, u t x ≤ M_inf) :
    ∀ r, 1 < r → LpPowerBoundedBefore intervalDomain r T u := by
  sorry

/-! ### Step 4: Assembly → Proposition 2.5

Chain: energy + Gronwall → Lp + dissipation bounds → 1D Sobolev → L∞ → all Lp
→ Proposition 2.5 (with quantitative endpoint).
-/

theorem intervalDomain_Proposition_2_5_1d
    (params : CM2Params)
    (hlogistic_dominates : 2 * params.γ < params.α)
    (hEndpoint :
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
      ∀ {T : ℝ}, 0 < T →
      ∀ {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        InitialTrace intervalDomain u₀ u →
      ∀ pExp,
        max (params.N : ℝ)
            (max (params.m * (params.N : ℝ)) (params.γ * (params.N : ℝ))) <
          pExp →
        LpPowerBoundedBefore intervalDomain pExp T u →
          ∃ pSeq rootBound : ℕ → ℝ,
            (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
              IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    Proposition_2_5 intervalDomain params := by
  sorry

#check intervalDomain_Lp_energy_and_dissipation_of_regularity
#check intervalDomain_Linf_of_Lp_and_gradient
#check intervalDomain_all_Lp_of_Linf
#check intervalDomain_Proposition_2_5_1d

end ShenWork.IntervalDomainExistence.IntervalDomain1DLinfRoute

end
