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
    (_hpExp : 0 < pExp)
    {M_Lp M_diss : ℝ}
    (_hMLp : 0 ≤ M_Lp)
    (_hMdiss : 0 ≤ M_diss)
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
    simp [intervalDomainLift]
  rw [hlift] at hagmon
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
  rw [hweighted_to_grad] at hagmon
  set Y : ℝ := intervalDomain.integral (fun z => (u t z) ^ pExp) with hY_def
  set G : ℝ := intervalDomain.integral (fun z =>
    (intervalDomain.gradNorm (fun y => (u t y) ^ (pExp / 2)) z) ^ 2) with hG_def
  have hY_nonneg : 0 ≤ Y := by
    rw [hY_def]
    exact intervalDomain_integral_u_rpow_nonneg_of_regularity
      (q := pExp) hsol ht0 htT
  have hG_nonneg : 0 ≤ G := by
    rw [hchain]
    exact mul_nonneg (sq_nonneg _) <|
      intervalDomain_lp_weighted_gradient_dissipation_nonneg_of_regularity
        (pExp := pExp) hsol ht0 htT
  have hY_le : Y ≤ M_Lp := by
    rw [hY_def]
    exact hLp_bound t ht0 htT
  have hG_le : G ≤ M_diss := by
    rw [hG_def]
    exact hgrad_bound t ht0 htT
  have hsqrtY_le : Real.sqrt Y ≤ Real.sqrt M_Lp :=
    Real.sqrt_le_sqrt hY_le
  have hsqrtG_le : Real.sqrt G ≤ Real.sqrt M_diss :=
    Real.sqrt_le_sqrt hG_le
  have hsqrt_prod :
      Real.sqrt Y * Real.sqrt G ≤
        Real.sqrt M_Lp * Real.sqrt M_diss :=
    mul_le_mul hsqrtY_le hsqrtG_le
      (Real.sqrt_nonneg G) (Real.sqrt_nonneg M_Lp)
  have hfirst : 2 * Y ≤ 2 * M_Lp :=
    mul_le_mul_of_nonneg_left hY_le (by norm_num)
  have hsecond :
      2 * Real.sqrt Y * Real.sqrt G ≤
        2 * Real.sqrt M_Lp * Real.sqrt M_diss := by
    calc
      2 * Real.sqrt Y * Real.sqrt G
          = 2 * (Real.sqrt Y * Real.sqrt G) := by ring
      _ ≤ 2 * (Real.sqrt M_Lp * Real.sqrt M_diss) :=
          mul_le_mul_of_nonneg_left hsqrt_prod (by norm_num)
      _ = 2 * Real.sqrt M_Lp * Real.sqrt M_diss := by ring
  refine le_trans ?_ (add_le_add hfirst hsecond)
  simpa [Y, G] using hagmon

/-! ### Step 3: L∞ → all Lp bounds

With `‖u(t)‖∞ ≤ M_inf` and `∫u ≤ M_mass`:
  `∫u^r ≤ ‖u‖∞^{r-1} · ∫u ≤ M_inf^{r-1} · M_mass`
-/

theorem intervalDomain_all_Lp_of_Linf
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    {M_inf : ℝ} (_hMinf : 0 ≤ M_inf)
    (hLinf : ∀ t, 0 < t → t < T →
      ∀ x : intervalDomain.Point, u t x ≤ M_inf) :
    ∀ r, 1 < r → LpPowerBoundedBefore intervalDomain r T u := by
  intro r hr
  refine ⟨M_inf ^ r, ?_⟩
  intro t ht0 htT
  have hr_nonneg : 0 ≤ r := le_trans zero_le_one hr.le
  have hpow_int :
      IntervalIntegrable
        (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ r))
        MeasureTheory.volume 0 1 :=
    intervalDomain_u_rpow_intervalIntegrable_of_regularity
      (q := r) hsol ht0 htT
  have hpoint :
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ r) y ≤
          M_inf ^ r := by
    intro y hy
    have hu_nonneg : 0 ≤ u t (⟨y, hy⟩ : intervalDomain.Point) :=
      (hsol.u_pos' ht0 htT).le
    have hu_le : u t (⟨y, hy⟩ : intervalDomain.Point) ≤ M_inf :=
      hLinf t ht0 htT ⟨y, hy⟩
    simpa [intervalDomainLift, hy] using
      Real.rpow_le_rpow hu_nonneg hu_le hr_nonneg
  have hmono :
      (∫ y in (0 : ℝ)..1,
          intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ r) y) ≤
        ∫ _y in (0 : ℝ)..1, M_inf ^ r :=
    intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      hpow_int intervalIntegrable_const hpoint
  change
    (∫ y in (0 : ℝ)..1,
        intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ r) y) ≤
      M_inf ^ r
  calc
    (∫ y in (0 : ℝ)..1,
        intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ r) y)
        ≤ ∫ _y in (0 : ℝ)..1, M_inf ^ r := hmono
    _ = M_inf ^ r := by
      rw [intervalIntegral.integral_const]
      norm_num [smul_eq_mul]

/-! ### Step 4: Assembly → Proposition 2.5

Chain: energy + Gronwall → Lp + dissipation bounds → 1D Sobolev → L∞ → all Lp
→ Proposition 2.5 (with quantitative endpoint).
-/

theorem intervalDomain_Proposition_2_5_1d
    (params : CM2Params)
    (hlogistic_dominates : 2 * params.γ < params.α)
    (_hEndpoint :
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
  have hpExp_pos : 0 < pExp := by
    have hN_lt : (params.N : ℝ) < pExp :=
      lt_of_le_of_lt (le_max_left _ _) hpExp
    have hN_ge_one_nat : 1 ≤ params.N := Nat.succ_le_of_lt params.hN
    have hN_ge_one : (1 : ℝ) ≤ (params.N : ℝ) := by
      exact_mod_cast hN_ge_one_nat
    linarith
  have hcross :
      CrossDiffusionBootstrapEstimate intervalDomain params T
        (2 * params.γ) u v :=
    intervalDomain_crossDiffusionBootstrapEstimate_of_classical hsol
  have hboot :
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
  have henergy :
      LpBootstrapEnergyInequality intervalDomain u T
        (2 * params.γ) pExp :=
    intervalDomain_LpBootstrapEnergyInequality_of_regularity hsol hcross hboot
  rcases intervalDomain_Lp_energy_and_dissipation_of_regularity
      (params := params) (T := T) (rho := 2 * params.γ)
      (p0 := pExp) (u := u) (v := v)
      hsol hcross hboot henergy hlogistic_dominates
      (pExp := pExp) le_rfl with
    ⟨M_Lp, M_diss, hMLp, hMdiss, hLp_bound, hgrad_bound⟩
  let C : ℝ := 2 * M_Lp + 2 * Real.sqrt M_Lp * Real.sqrt M_diss
  have hpower :
      ∀ t, 0 < t → t < T →
        ∀ x : intervalDomain.Point, (u t x) ^ pExp ≤ C :=
    intervalDomain_Linf_of_Lp_and_gradient
      (params := params) (T := T) (pExp := pExp) (u := u) (v := v)
      hsol hpExp_pos hMLp hMdiss hLp_bound hgrad_bound
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    have hsqrt_prod_nonneg :
        0 ≤ Real.sqrt M_Lp * Real.sqrt M_diss :=
      mul_nonneg (Real.sqrt_nonneg M_Lp) (Real.sqrt_nonneg M_diss)
    nlinarith [hMLp, hsqrt_prod_nonneg]
  let R : ℝ := C ^ pExp⁻¹
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    exact Real.rpow_nonneg hC_nonneg _
  have hR_pow : R ^ pExp = C := by
    dsimp [R]
    exact Real.rpow_inv_rpow hC_nonneg (ne_of_gt hpExp_pos)
  have hpoint : IntervalDomainMoserPointwisePowerControlBefore u T pExp R := by
    intro t ht0 htT x
    have hpos : 0 < u t x := hsol.u_pos' ht0 htT
    have hpow : (u t x) ^ pExp ≤ C := hpower t ht0 htT x
    rw [hR_pow]
    simpa [abs_of_pos hpos] using hpow
  exact intervalDomain_boundedBefore_of_pointwise_power_control
    hpExp_pos hR_nonneg hpoint

#check intervalDomain_Lp_energy_and_dissipation_of_regularity
#check intervalDomain_Linf_of_Lp_and_gradient
#check intervalDomain_all_Lp_of_Linf
#check intervalDomain_Proposition_2_5_1d

end ShenWork.IntervalDomainExistence.IntervalDomain1DLinfRoute

end
