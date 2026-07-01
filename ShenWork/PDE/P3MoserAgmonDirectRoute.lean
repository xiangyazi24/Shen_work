import ShenWork.PDE.IntervalAgmonInterpolation
import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
import ShenWork.Paper2.IntervalDomainChain

/-!
# GN-absorbed interpolation from Agmon → Moser iteration (1D)

This file produces the GN-absorbed interpolation inequality
  `∫u^{p+ρ} ≤ ε·∫|∇(u^{p/2})|² + C_ε`
for positive classical solutions on `intervalDomain = [0,1]`, using:

1. The proved **Agmon inequality** for `w = u^{p/2}`:
     `‖w‖∞² ≤ C(∫w² + ∫|w'|²)` (pointwise 1D Sobolev)
2. **Hölder interpolation** with the SEED norm:
     `∫u^{p+ρ} = ∫w^{p₁} ≤ ‖w‖∞^{p₁-q₁} · ∫w^{q₁}`
   where `p₁ = 2(p+ρ)/p`, `q₁ = 2p₀/p`, and `∫w^{q₁} = ∫u^{p₀} ≤ M₀` (seed bound)
3. **Young's inequality** to absorb the gradient:
     `(A + G)^α ≤ εG + C_ε`  for `α = (p+ρ-p₀)/p < 1`

The key insight (from the paper's Lemma 2.6): the lower-order term uses the
SEED L^{p₀} norm (bounded by hypothesis), not the CURRENT L^p norm. This
gives a CONSTANT lower-order term, which is stronger than
`RelativeMoserInterpolationBefore` and feeds `moser_iteration_chain` directly.

Combined with `LpBootstrapEnergyInequality` (proved from regularity), this
yields all Lp bounds via `moser_iteration_chain`, and then L∞ via the proved
Agmon/GN → Proposition 2.5.
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

namespace ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute

/-! ### Step 1: Hölder interpolation with seed norm

For `w = u^{p/2}`, `p₁ = 2(p+ρ)/p`, `q₁ = 2p₀/p`:
  `∫w^{p₁} ≤ ‖w‖∞^{p₁-q₁} · ∫w^{q₁}`

i.e., `∫u^{p+ρ} ≤ ‖u^{p/2}‖∞^{2(p+ρ-p₀)/p} · ∫u^{p₀}`
-/

theorem intervalDomain_higher_Lp_le_Linf_rpow_mul_seed
    {f : intervalDomain.Point → ℝ}
    (hf_nonneg : ∀ x, 0 ≤ f x)
    {pExp p0 rho : ℝ}
    (hp0_le : p0 ≤ pExp) (hrho : 0 < rho) :
    intervalDomain.integral (fun x => f x ^ (pExp + rho)) ≤
      (intervalDomainSupNorm f) ^ rho *
        intervalDomain.integral (fun x => f x ^ pExp) := by
  sorry

/-! ### Step 2: Agmon bound for w = u^{p/2}

From `intervalDomainLift_rpow_agmon_bound` (proved):
  `u(x)^p ≤ 2·∫u^p + 2·√(∫u^p)·√((p²/4)·∫u^{p-2}|∇u|²)`
  = `2·∫u^p + 2·√(∫u^p)·√(∫|∇(u^{p/2})|²)` (by chain rule equality)

So: `‖u^{p/2}‖∞² = ‖u‖∞^p ≤ 2·∫u^p + 2·√(∫u^p)·√(∫|∇(u^{p/2})|²)`
-/

theorem intervalDomain_supNorm_rpow_le_energy_plus_gradient
    {params : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hpExp : 2 ≤ pExp) :
    (intervalDomainSupNorm (u t)) ^ pExp ≤
      2 * intervalDomain.integral (fun x => (u t x) ^ pExp) +
      2 * Real.sqrt (intervalDomain.integral (fun x => (u t x) ^ pExp)) *
        Real.sqrt (intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)) := by
  sorry

/-! ### Step 3: GN-absorbed interpolation (the main lemma)

Combining Steps 1 and 2:
  `∫u^{p+ρ} ≤ ‖u‖∞^ρ · ∫u^p ≤ C(∫u^p + ∫|∇(u^{p/2})|²)^{ρ/p} · ∫u^p`

But with the SEED norm trick (Hölder with q₁ = 2p₀/p):
  `∫u^{p+ρ} ≤ ‖u^{p/2}‖∞^{2(p+ρ-p₀)/p} · ∫u^{p₀}`
  ≤ `C(∫u^p + G)^{(p+ρ-p₀)/p} · M₀`

With α = (p+ρ-p₀)/p < 1 (since p₀ > ρ):
  `C(A+G)^α ≤ C(A^α + G^α) ≤ C(1+A+εG+C_ε)` (sub-additivity + Young on G^α)
  `≤ εG + C(1+A+C_ε)`

For the energy identity: the `A = ∫u^p` is absorbed by the `B·∫u^p` on the LHS.
The net result: `K·∫u^{p+ρ} ≤ A_orig·G + C_absorbed`
which is `∫u^{p+ρ} ≤ ε·G + Ceps` (constant lower-order term).
-/

theorem intervalDomain_gn_absorbed_interpolation_of_agmon
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hrho : 0 < rho)
    (hp0_gt_rho : rho < p0)
    {pExp : ℝ} (hpExp : p0 ≤ pExp) :
    ∀ eps > 0, ∃ Ceps : ℝ, ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) ≤
        eps * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
        Ceps := by
  sorry

/-! ### Step 4: Feed into moser_iteration_chain

The GN-absorbed interpolation + `LpBootstrapEnergyInequality` provide the
`hstep` input to `moser_iteration_chain`, yielding all Lp bounds.
-/

theorem intervalDomain_all_Lp_of_agmon_bootstrap
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hrho : 0 < rho)
    (hp0_gt_rho : rho < p0) :
    ∀ n : ℕ, LpPowerBoundedBefore intervalDomain (p0 + n * rho) T u := by
  sorry

/-! ### Step 5: Corollary 2.1 and Proposition 2.5

All Lp bounds + Lp monotonicity → ∀ r > 1, LpPowerBoundedBefore r T u.
Plus quantitative endpoint → Proposition 2.5.
-/

theorem intervalDomain_Corollary_2_1_of_agmon
    (params : CM2Params) :
    Corollary_2_1 intervalDomain params := by
  sorry

theorem intervalDomain_Proposition_2_5_of_agmon
    (params : CM2Params)
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

end ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute

end
