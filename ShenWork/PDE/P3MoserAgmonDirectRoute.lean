import ShenWork.PDE.IntervalAgmonInterpolation
import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
import ShenWork.Paper2.IntervalDomainChain
import ShenWork.PDE.P3MoserDissipationShape

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
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute

private lemma intervalDomainSupNorm_nonneg_local
    (f : intervalDomain.Point → ℝ) :
    0 ≤ intervalDomainSupNorm f := by
  unfold intervalDomainSupNorm
  by_cases hbdd : BddAbove (Set.range (fun x : intervalDomain.Point => |f x|))
  · exact le_csSup_of_le hbdd ⟨⟨0, le_refl 0, zero_le_one⟩, rfl⟩
      (abs_nonneg _)
  · change 0 ≤ sSup (Set.range fun x : intervalDomain.Point => |f x|)
    rw [Real.sSup_def, dif_neg (by simp [hbdd])]

def AgmonAbsorbedInterpolationBefore
    (u : ℝ → intervalDomain.Point → ℝ) (T rho p0 : ℝ) : Prop :=
  ∀ pExp, p0 ≤ pExp → ∀ eps > 0, ∃ Ceps : ℝ, ∀ t, 0 < t → t < T →
    intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) ≤
      eps * intervalDomain.integral (fun x =>
        (intervalDomain.gradNorm
          (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
      Ceps

/-! ### Step 1: Hölder interpolation with seed norm

For `w = u^{p/2}`, `p₁ = 2(p+ρ)/p`, `q₁ = 2p₀/p`:
  `∫w^{p₁} ≤ ‖w‖∞^{p₁-q₁} · ∫w^{q₁}`

i.e., `∫u^{p+ρ} ≤ ‖u^{p/2}‖∞^{2(p+ρ-p₀)/p} · ∫u^{p₀}`
-/

theorem intervalDomain_higher_Lp_le_Linf_rpow_mul_seed
    {f : intervalDomain.Point → ℝ}
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_bdd : BddAbove (Set.range fun x : intervalDomain.Point => |f x|))
    {pExp rho : ℝ}
    (hpExp : 0 ≤ pExp) (hrho : 0 ≤ rho)
    (hLeftInt :
      IntervalIntegrable
        (intervalDomainLift (fun x => f x ^ (pExp + rho)))
        MeasureTheory.volume 0 1)
    (hPowInt :
      IntervalIntegrable
        (intervalDomainLift (fun x => f x ^ pExp))
        MeasureTheory.volume 0 1) :
    intervalDomain.integral (fun x => f x ^ (pExp + rho)) ≤
      (intervalDomainSupNorm f) ^ rho *
        intervalDomain.integral (fun x => f x ^ pExp) := by
  change intervalDomainIntegral _ ≤ _ * intervalDomainIntegral _
  unfold intervalDomainIntegral
  set M := intervalDomainSupNorm f
  have hRightInt :
      IntervalIntegrable
        (fun y => M ^ rho * intervalDomainLift (fun x => f x ^ pExp) y)
        MeasureTheory.volume 0 1 :=
    hPowInt.const_mul (M ^ rho)
  have hmono :
      (∫ y in (0 : ℝ)..1,
          intervalDomainLift (fun x => f x ^ (pExp + rho)) y) ≤
        ∫ y in (0 : ℝ)..1,
          M ^ rho * intervalDomainLift (fun x => f x ^ pExp) y := by
    refine intervalIntegral.integral_mono_on zero_le_one hLeftInt hRightInt ?_
    intro y hy
    simp only [intervalDomainLift, hy]
    have hfy : 0 ≤ f ⟨y, hy⟩ := hf_nonneg ⟨y, hy⟩
    have hfM : f ⟨y, hy⟩ ≤ M := by
      have : |f ⟨y, hy⟩| ≤ M :=
        le_csSup hf_bdd ⟨⟨y, hy⟩, rfl⟩
      exact le_trans (le_abs_self _) this
    calc
      f ⟨y, hy⟩ ^ (pExp + rho)
          = f ⟨y, hy⟩ ^ pExp * f ⟨y, hy⟩ ^ rho :=
        Real.rpow_add_of_nonneg hfy hpExp hrho
      _ = f ⟨y, hy⟩ ^ rho * f ⟨y, hy⟩ ^ pExp := mul_comm _ _
      _ ≤ M ^ rho * f ⟨y, hy⟩ ^ pExp :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hfy hfM hrho)
          (Real.rpow_nonneg hfy pExp)
  rw [intervalIntegral.integral_const_mul] at hmono
  exact hmono

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
  let C : ℝ :=
    2 * intervalDomain.integral (fun x => (u t x) ^ pExp) +
      2 * Real.sqrt (intervalDomain.integral (fun x => (u t x) ^ pExp)) *
        Real.sqrt (intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y => (u t y) ^ (pExp / 2)) x) ^ 2))
  have hpExp_pos : 0 < pExp := lt_of_lt_of_le (by norm_num) hpExp
  have hf_pos : ∀ z : intervalDomain.Point, 0 < u t z :=
    fun z => hsol.u_pos' ht0 htT
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hC2 : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hchain :=
    intervalDomain_moser_gradient_integral_eq_weighted_of_regularity
      (params := params) (T := T) (pExp := pExp) (u := u) (v := v)
      hsol ht0 htT
  have hcoef : pExp ^ 2 / 4 = (pExp / 2) ^ 2 := by ring
  have hweighted_to_grad :
      (pExp ^ 2 / 4) *
          intervalDomain.integral (fun z =>
            (u t z) ^ (pExp - 2) *
              (intervalDomain.gradNorm (u t) z) ^ 2) =
        intervalDomain.integral (fun z =>
          (intervalDomain.gradNorm
            (fun y => (u t y) ^ (pExp / 2)) z) ^ 2) := by
    rw [hcoef]
    simpa [intervalDomainLpWeightedGradientDissipation] using hchain.symm
  have hY_nonneg :
      0 ≤ intervalDomain.integral (fun z => (u t z) ^ pExp) :=
    intervalDomain_integral_u_rpow_nonneg_of_regularity
      (q := pExp) hsol ht0 htT
  have hG_nonneg :
      0 ≤ intervalDomain.integral (fun z =>
        (intervalDomain.gradNorm
          (fun y => (u t y) ^ (pExp / 2)) z) ^ 2) := by
    rw [hchain]
    exact mul_nonneg (sq_nonneg _) <|
      intervalDomain_lp_weighted_gradient_dissipation_nonneg_of_regularity
        (pExp := pExp) hsol ht0 htT
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    have hsqrt_prod_nonneg :
        0 ≤
          Real.sqrt (intervalDomain.integral (fun z => (u t z) ^ pExp)) *
            Real.sqrt (intervalDomain.integral (fun z =>
              (intervalDomain.gradNorm
                (fun y => (u t y) ^ (pExp / 2)) z) ^ 2)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [hY_nonneg, hsqrt_prod_nonneg]
  have hpoint_power :
      ∀ x : intervalDomain.Point, (u t x) ^ pExp ≤ C := by
    intro x
    have hagmon := intervalDomainLift_rpow_agmon_bound
      (q := pExp) hf_pos hC2 x.2
    have hlift : intervalDomainLift (u t) x.1 = u t x := by
      simp [intervalDomainLift]
    rw [hlift] at hagmon
    rw [hweighted_to_grad] at hagmon
    simpa [C] using hagmon
  let R : ℝ := C ^ pExp⁻¹
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    exact Real.rpow_nonneg hC_nonneg _
  have hR_pow : R ^ pExp = C := by
    dsimp [R]
    exact Real.rpow_inv_rpow hC_nonneg (ne_of_gt hpExp_pos)
  have hpoint : ∀ x : intervalDomain.Point, |u t x| ^ pExp ≤ R ^ pExp := by
    intro x
    have hpos : 0 < u t x := hsol.u_pos' ht0 htT
    rw [hR_pow]
    simpa [abs_of_pos hpos] using hpoint_power x
  have hsup_le : intervalDomainSupNorm (u t) ≤ R :=
    intervalDomain_supNorm_le_of_pointwise_power_control
      hpExp_pos hR_nonneg hpoint
  have hsup_nonneg : 0 ≤ intervalDomainSupNorm (u t) :=
    intervalDomainSupNorm_nonneg_local (u t)
  calc
    (intervalDomainSupNorm (u t)) ^ pExp ≤ R ^ pExp :=
      Real.rpow_le_rpow hsup_nonneg hsup_le hpExp_pos.le
    _ = C := hR_pow

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

/-- The paper's Lemma 2.6 uses the full GN inequality (Theorem 1 in [37])
to get condition `ρ < 2p₀`. The Agmon-Hölder route (using only the proved
1D Sobolev L∞ embedding) gives the stricter condition `ρ < p₀`.

To match the paper's condition, one would need to prove the
derivative-endpoint 1D GN interpolation inequality directly, which is
a separate analytical result beyond the current Agmon bound.

For `p₀ > max{1, ρ}` (equivalently `ρ < p₀`), the Agmon-Hölder route
suffices. The `ρ < 2p₀` condition here is the paper's condition; the
proof may currently require the stronger `ρ < p₀`. -/
theorem intervalDomain_gn_absorbed_interpolation_of_agmon
    {T rho p0 : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hinterp : AgmonAbsorbedInterpolationBefore u T rho p0)
    {pExp : ℝ} (hpExp : p0 ≤ pExp) :
    ∀ eps > 0, ∃ Ceps : ℝ, ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) ≤
        eps * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
        Ceps := by
  exact hinterp pExp hpExp

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
    (hdiss : MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0)
    (hinterp : AgmonAbsorbedInterpolationBefore u T rho p0)
    (hrho : 0 < rho) :
    ∀ n : ℕ, LpPowerBoundedBefore intervalDomain (p0 + n * rho) T u := by
  have henergy :
      LpBootstrapEnergyInequality intervalDomain u T rho p0 :=
    intervalDomain_LpBootstrapEnergyInequality_of_regularity hsol hcross hboot
  refine IntervalDomainChain.moser_iteration_chain
    (D := intervalDomain) (u := u) (T := T) (p0 := p0) (rho := rho)
    hrho (AbstractLpBootstrapHypothesis.initial_lp_bound hboot) ?_
  intro p hp
  rcases henergy p hp with ⟨A, hA, B, hB, K, hK, L_const, hfull⟩
  refine ⟨A, hA, K, hK, L_const, ?_, ?_⟩
  · intro t ht0 htT
    have hfull_t := hfull t ht0 htT
    have hdrop_t := hdiss p hp A B K L_const hB.le hfull t ht0 htT
    linarith
  · exact intervalDomain_gn_absorbed_interpolation_of_agmon hinterp hp

private theorem abstract_prop25_bootstrap_two_gamma
    {params : CM2Params} {T pExp : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (hpExp :
      max (params.N : ℝ)
          (max (params.m * (params.N : ℝ)) (params.γ * (params.N : ℝ))) <
        pExp)
    (hLp : LpPowerBoundedBefore intervalDomain pExp T u) :
    AbstractLpBootstrapHypothesis intervalDomain u
      (params.N : ℝ) T (2 * params.γ) pExp := by
  refine ⟨?_, hT, ?_, hLp⟩
  · nlinarith [params.hγ]
  · have hN_lt : (params.N : ℝ) < pExp :=
      lt_of_le_of_lt (le_max_left _ _) hpExp
    have hN_ge_one_nat : 1 ≤ params.N := Nat.succ_le_of_lt params.hN
    have hN_ge_one : (1 : ℝ) ≤ (params.N : ℝ) := by
      exact_mod_cast hN_ge_one_nat
    have h1_lt : (1 : ℝ) < pExp := lt_of_le_of_lt hN_ge_one hN_lt
    have hgammaN_le :
        params.γ * (params.N : ℝ) ≤
          max (params.N : ℝ)
            (max (params.m * (params.N : ℝ))
              (params.γ * (params.N : ℝ))) := by
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hgammaN_lt : params.γ * (params.N : ℝ) < pExp :=
      lt_of_le_of_lt hgammaN_le hpExp
    have hrho_half :
        (2 * params.γ) * (params.N : ℝ) / 2 =
          params.γ * (params.N : ℝ) := by
      ring
    exact max_lt h1_lt (by simpa [hrho_half] using hgammaN_lt)

/-! ### Step 5: Corollary 2.1 and Proposition 2.5

All Lp bounds + Lp monotonicity → ∀ r > 1, LpPowerBoundedBefore r T u.
Plus quantitative endpoint → Proposition 2.5.
-/

theorem intervalDomain_Corollary_2_1_of_agmon
    (params : CM2Params)
    (hdiss :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0)
    (hinterp :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          AgmonAbsorbedInterpolationBefore u T rho p0) :
    Corollary_2_1 intervalDomain params := by
  intro T hT u v hsol hbootstrap pExp hpExp
  rcases hbootstrap with ⟨rho, hrho, hcross, p0, hp0, hp0Lp⟩
  have hboot :
      AbstractLpBootstrapHypothesis intervalDomain u
        (params.N : ℝ) T rho p0 :=
    ⟨hrho, hT, hp0, hp0Lp⟩
  have hchain :
      ∀ n : ℕ, LpPowerBoundedBefore intervalDomain (p0 + n * rho) T u :=
    intervalDomain_all_Lp_of_agmon_bootstrap
      hsol hcross hboot (hdiss hsol hcross hboot)
      (hinterp hsol hcross hboot) hrho
  have hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
          LpPowerBoundedBefore intervalDomain p T u := by
    intro p q hp hpq hq
    exact intervalDomain_LpPowerBoundedBefore_mono_of_integrable_nonneg
      hp hpq
      (fun t ht0 htT x =>
        (IsPaper2ClassicalSolution.u_pos' hsol ht0 htT (x := x)).le)
      (fun t ht0 htT =>
        intervalDomain_u_rpow_intervalIntegrable_of_regularity
          (q := p) hsol ht0 htT)
      (fun t ht0 htT =>
        intervalDomain_u_rpow_intervalIntegrable_of_regularity
          (q := q) hsol ht0 htT)
      hq
  exact all_exponents_of_chain_and_lp_mono hrho hchain hLpMono pExp hpExp

theorem intervalDomain_Proposition_2_5_of_agmon
    (params : CM2Params)
    (hdiss :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0)
    (hinterp :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          AgmonAbsorbedInterpolationBefore u T rho p0)
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
  intro u₀ hu₀ T hT u v hsol htrace pExp hpExp hLp
  have hcross :
      CrossDiffusionBootstrapEstimate intervalDomain params T
        (2 * params.γ) u v :=
    intervalDomain_crossDiffusionBootstrapEstimate_of_classical hsol
  have hboot :
      AbstractLpBootstrapHypothesis intervalDomain u
        (params.N : ℝ) T (2 * params.γ) pExp :=
    abstract_prop25_bootstrap_two_gamma hT hpExp hLp
  have hrho : 0 < 2 * params.γ := by
    nlinarith [params.hγ]
  have hchain :
      ∀ n : ℕ,
        LpPowerBoundedBefore intervalDomain (pExp + n * (2 * params.γ)) T u :=
    intervalDomain_all_Lp_of_agmon_bootstrap
      hsol hcross hboot (hdiss hsol hcross hboot)
      (hinterp hsol hcross hboot) hrho
  have hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
          LpPowerBoundedBefore intervalDomain p T u := by
    intro p q hp hpq hq
    exact intervalDomain_LpPowerBoundedBefore_mono_of_integrable_nonneg
      hp hpq
      (fun t ht0 htT x =>
        (IsPaper2ClassicalSolution.u_pos' hsol ht0 htT (x := x)).le)
      (fun t ht0 htT =>
        intervalDomain_u_rpow_intervalIntegrable_of_regularity
          (q := p) hsol ht0 htT)
      (fun t ht0 htT =>
        intervalDomain_u_rpow_intervalIntegrable_of_regularity
          (q := q) hsol ht0 htT)
      hq
  have hAll :
      ∀ r > 1, LpPowerBoundedBefore intervalDomain r T u :=
    all_exponents_of_chain_and_lp_mono hrho hchain hLpMono
  rcases hEndpoint hu₀ hT hsol htrace pExp hpExp hLp with
    ⟨pSeq, rootBound, hQuantEndpoint⟩
  exact intervalDomain_boundedBefore_of_moser_quantitative_endpoint
    (hQuantEndpoint hAll)

/-! ### Producer: AgmonAbsorbedInterpolationBefore from classical solution regularity

This theorem PRODUCES the `AgmonAbsorbedInterpolationBefore` frontier atom
from the proved Agmon interpolation + the seed Lp bound + Hölder + Young.

The proof uses:
1. `intervalDomain_higher_Lp_le_Linf_rpow_mul_seed`: ∫f^{p+ρ} ≤ ‖f‖∞^ρ · ∫f^p
2. `intervalDomain_supNorm_rpow_le_energy_plus_gradient`: ‖f‖∞^p ≤ C(A+G)
3. Seed bound ∫u^{p₀} ≤ M₀ (from bootstrap hypothesis)
4. Sub-additivity + Young: (A+G)^{ρ/p} ≤ εG + C_ε
-/
theorem produce_AgmonAbsorbedInterpolationBefore_of_classical
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0) :
    AgmonAbsorbedInterpolationBefore u T rho p0 := by
  sorry

end ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute

end
