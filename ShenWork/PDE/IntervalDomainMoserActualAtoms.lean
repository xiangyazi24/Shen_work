import ShenWork.PDE.IntervalDomainAPrioriGlobal
import ShenWork.Paper2.IntervalDomainEnergyStep
import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open ShenWork.Paper2.IntervalDomainMoserClosure
open scoped BigOperators

noncomputable section

namespace ShenWork.IntervalDomainExistence

/-! ### Finite dyadic root tower -/

theorem dyadic_inv_sum_Icc_le_one (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, ((1 / 2 : ℝ) ^ k)) ≤ 1 := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  have h :=
    geom_sum_Ico_le_of_lt_one (m := 1) (n := n + 1)
      (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hhalf :
      ((1 / 2 : ℝ) ^ (1 : ℕ)) / (1 - (1 / 2 : ℝ)) = 1 := by
    norm_num
  rw [hhalf] at h
  simpa [one_div] using h

theorem dyadic_k_inv_sum_Icc_eq (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, (k : ℝ) * ((1 / 2 : ℝ) ^ k)) =
      2 - (n + 2 : ℝ) * ((1 / 2 : ℝ) ^ n) := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (a := 1) (b := n)
        (f := fun k : ℕ => (k : ℝ) * ((1 / 2 : ℝ) ^ k)) (by omega)]
      rw [ih]
      rw [pow_succ]
      push_cast
      ring

theorem dyadic_k_inv_sum_Icc_le_two (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, (k : ℝ) * ((1 / 2 : ℝ) ^ k)) ≤ 2 := by
  rw [dyadic_k_inv_sum_Icc_eq n]
  have hnonneg :
      0 ≤ (n + 2 : ℝ) * ((1 / 2 : ℝ) ^ n) := by
    positivity
  linarith

def dyadicMoserFactor (C : ℝ) (k : ℕ) : ℝ :=
  (C * (2 : ℝ) ^ k) ^ ((1 / 2 : ℝ) ^ k)

theorem dyadic_moser_factor_prod_split
    (n : ℕ) {C : ℝ} (hC : 1 ≤ C) :
    (∏ k ∈ Finset.Icc 1 n, dyadicMoserFactor C k) =
      (∏ k ∈ Finset.Icc 1 n,
        C ^ ((1 / 2 : ℝ) ^ k) *
          (2 : ℝ) ^ ((k : ℝ) * ((1 / 2 : ℝ) ^ k))) := by
  apply Finset.prod_congr rfl
  intro k _hk
  unfold dyadicMoserFactor
  rw [Real.mul_rpow (le_trans zero_le_one hC) (by positivity :
    0 ≤ (2 : ℝ) ^ k)]
  rw [← Real.rpow_natCast_mul (x := (2 : ℝ)) (by norm_num) k
    ((1 / 2 : ℝ) ^ k)]

theorem dyadic_root_tower_product_bound
    (n : ℕ) {C : ℝ} (hC : 1 ≤ C) :
    (∏ k ∈ Finset.Icc 1 n, dyadicMoserFactor C k) ≤ 4 * C := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  rw [dyadic_moser_factor_prod_split n hC]
  rw [Finset.prod_mul_distrib]
  rw [← Real.rpow_sum_of_pos hCpos
    (fun k : ℕ => ((1 / 2 : ℝ) ^ k)) (Finset.Icc 1 n)]
  rw [← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)
    (fun k : ℕ => (k : ℝ) * ((1 / 2 : ℝ) ^ k)) (Finset.Icc 1 n)]
  have hCp :
      C ^ (∑ k ∈ Finset.Icc 1 n, ((1 / 2 : ℝ) ^ k)) ≤ C := by
    have h := Real.rpow_le_rpow_of_exponent_le hC
      (dyadic_inv_sum_Icc_le_one n)
    simpa using h
  have h2p :
      (2 : ℝ) ^
          (∑ k ∈ Finset.Icc 1 n, (k : ℝ) * ((1 / 2 : ℝ) ^ k)) ≤
        4 := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (dyadic_k_inv_sum_Icc_le_two n)
    norm_num at h
    exact h
  have hprod :=
    mul_le_mul hCp h2p
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (∑ k ∈ Finset.Icc 1 n, (k : ℝ) * ((1 / 2 : ℝ) ^ k)))
      hCpos.le
  nlinarith

theorem dyadic_root_tower_iterate_bound
    {C : ℝ} {M : ℕ → ℝ} (hC : 1 ≤ C)
    (hrec :
      ∀ k, 1 ≤ k →
        M (k + 1) ≤ dyadicMoserFactor C k * M k) :
    ∀ n,
      M (n + 1) ≤
        (∏ k ∈ Finset.Icc 1 n, dyadicMoserFactor C k) * M 1 := by
  intro n
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      have hfac_nonneg : 0 ≤ dyadicMoserFactor C (n + 1) := by
        unfold dyadicMoserFactor
        exact Real.rpow_nonneg
          (mul_nonneg (le_trans zero_le_one hC) (by positivity)) _
      have hstep :
          M (n + 1 + 1) ≤ dyadicMoserFactor C (n + 1) * M (n + 1) :=
        hrec (n + 1) (by omega)
      have hmul :
          dyadicMoserFactor C (n + 1) * M (n + 1) ≤
            dyadicMoserFactor C (n + 1) *
              ((∏ k ∈ Finset.Icc 1 n, dyadicMoserFactor C k) * M 1) :=
        mul_le_mul_of_nonneg_left ih hfac_nonneg
      calc
        M (n + 1 + 1)
            ≤ dyadicMoserFactor C (n + 1) * M (n + 1) := hstep
        _ ≤ dyadicMoserFactor C (n + 1) *
              ((∏ k ∈ Finset.Icc 1 n, dyadicMoserFactor C k) * M 1) := hmul
        _ =
            (∏ k ∈ Finset.Icc 1 (n + 1), dyadicMoserFactor C k) * M 1 := by
              rw [Finset.prod_Icc_succ_top (a := 1) (b := n)
                (f := dyadicMoserFactor C) (by omega)]
              ring

theorem dyadic_root_tower_bound
    {C : ℝ} {M : ℕ → ℝ} (hC : 1 ≤ C) (hM1 : 0 ≤ M 1)
    (hrec :
      ∀ k, 1 ≤ k →
        M (k + 1) ≤ dyadicMoserFactor C k * M k) :
    ∀ n, M (n + 1) ≤ 4 * C * M 1 := by
  intro n
  have hiter := dyadic_root_tower_iterate_bound hC hrec n
  have hprod := dyadic_root_tower_product_bound n hC
  have hscaled :
      (∏ k ∈ Finset.Icc 1 n, dyadicMoserFactor C k) * M 1 ≤
        (4 * C) * M 1 :=
    mul_le_mul_of_nonneg_right hprod hM1
  nlinarith

/-! ### Closed-time L² seed bridge -/

structure IntervalDomainClosedL2SeedBridge
    (T : ℝ) (u : ℝ → intervalDomain.Point → ℝ) where
  energyContinuous :
    ContinuousOn (fun t => intervalDomainLpAbsEnergy 2 u t)
      (Set.Icc (0 : ℝ) T)
  energyHasDerivWithin :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt
        (fun τ => intervalDomainLpAbsEnergy 2 u τ)
        (deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) t)
        (Set.Ici t) t
  initialBound :
    ∃ δ0, 0 ≤ δ0 ∧ intervalDomainLpAbsEnergy 2 u 0 ≤ δ0
  derivativeAlignment :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      deriv (fun τ => intervalDomainLpAbsEnergy 2 u τ) t =
        2 * deriv (fun τ => intervalDomainL2HalfEnergy u τ) t

def IntervalDomainClosedL2SeedBridge.to_frontier
    {T : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (h : IntervalDomainClosedL2SeedBridge T u) :
    IntervalDomainL2SeedRegularityFrontier T u where
  energyContinuous := h.energyContinuous
  energyHasDerivWithin := h.energyHasDerivWithin
  initialBound := h.initialBound
  derivativeAlignment := h.derivativeAlignment

/-! ### Atom 2: all finite Lp from the actual relative Moser step -/

theorem intervalDomain_allLpBoundFromBootstrap_of_relative_moser_step
    {params : CM2Params}
    (hdiss :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          MoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          RelativeMoserInterpolationBefore intervalDomain u T rho p0) :
    Corollary_2_1 intervalDomain params := by
  intro T hT u v hsol hbootstrap pExp hpExp
  rcases hbootstrap with ⟨rho, hrho, hcross, p0, hp0, hp0Lp⟩
  have hboot :
      AbstractLpBootstrapHypothesis intervalDomain u
        (params.N : ℝ) T rho p0 :=
    ⟨hrho, hT, hp0, hp0Lp⟩
  exact
    intervalDomain_all_exponents_of_energy_dissipation_relative_interpolation_inside_nonneg
      hboot
      (intervalDomain_LpBootstrapEnergyInequality_of_regularity hsol hcross hboot)
      (hdiss hsol hcross hboot)
      (hrel hsol hcross hboot)
      (fun t ht0 htT x _hx =>
        (IsPaper2ClassicalSolution.u_pos' hsol ht0 htT (x := x)).le)
      (fun r _hr t ht0 htT =>
        intervalDomain_u_rpow_intervalIntegrable_of_regularity
          (q := r) hsol ht0 htT)
      pExp hpExp

theorem intervalDomain_allLpBoundFromBootstrap_of_regularity_moser_step
    {params : CM2Params}
    (hdiss :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          MoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          RelativeMoserInterpolationBefore intervalDomain u T rho p0) :
    Corollary_2_1 intervalDomain params :=
  intervalDomain_allLpBoundFromBootstrap_of_relative_moser_step hdiss hrel

/-! ### Atom 3: Lp to Linfty through the quantitative endpoint/root tower -/

private theorem abstract_prop25_bootstrap
    {params : CM2Params} {T pExp : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (hpExp :
      max (params.N : ℝ)
          (max (params.m * (params.N : ℝ)) (params.γ * (params.N : ℝ))) <
        pExp)
    (hLp : LpPowerBoundedBefore intervalDomain pExp T u) :
    AbstractLpBootstrapHypothesis intervalDomain u
      (params.N : ℝ) T 1 pExp := by
  refine ⟨one_pos, hT, ?_, hLp⟩
  have hN_lt : (params.N : ℝ) < pExp :=
    lt_of_le_of_lt (le_max_left _ _) hpExp
  have hN_ge_one_nat : 1 ≤ params.N := Nat.succ_le_of_lt params.hN
  have hN_ge_one : (1 : ℝ) ≤ (params.N : ℝ) := by
    exact_mod_cast hN_ge_one_nat
  have h1_lt : (1 : ℝ) < pExp := lt_of_le_of_lt hN_ge_one hN_lt
  have hhalf_lt : 1 * (params.N : ℝ) / 2 < pExp := by
    nlinarith
  exact max_lt h1_lt hhalf_lt

theorem intervalDomain_endpointBoundFromLp_of_quantitative_root_tower
    {params : CM2Params}
    (hcross :
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
          CrossDiffusionBootstrapEstimate intervalDomain params T 1 u v)
    (hdiss :
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
          MoserDissipationDropBefore intervalDomain u T 1 pExp)
    (hrel :
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
          RelativeMoserInterpolationBefore intervalDomain u T 1 pExp)
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
  have hboot :
      AbstractLpBootstrapHypothesis intervalDomain u
        (params.N : ℝ) T 1 pExp :=
    abstract_prop25_bootstrap hT hpExp hLp
  rcases hEndpoint hu₀ hT hsol htrace pExp hpExp hLp with
    ⟨pSeq, rootBound, hQuantEndpoint⟩
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
  exact
    intervalDomain_boundedBefore_of_energy_dissipation_relative_interpolation
      hboot
      (intervalDomain_LpBootstrapEnergyInequality_of_regularity hsol
        (hcross hu₀ hT hsol htrace pExp hpExp hLp) hboot)
      (hdiss hu₀ hT hsol htrace pExp hpExp hLp)
      (hrel hu₀ hT hsol htrace pExp hpExp hLp)
      hLpMono
      hQuantEndpoint

end ShenWork.IntervalDomainExistence

end
