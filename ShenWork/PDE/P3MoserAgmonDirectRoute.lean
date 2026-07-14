import ShenWork.PDE.IntervalAgmonInterpolation
import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
import ShenWork.Paper2.IntervalDomainLpTimeLeibniz

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
SEED L^{p₀} norm (bounded by hypothesis), not the CURRENT L^p norm.  Combined
with `LpBootstrapEnergyInequality`, this yields a scalar linear damping
inequality and hence terminal-window bounds at every finite exponent.
-/

open MeasureTheory Set Filter Topology
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

private lemma intervalDomainSupNorm_nonneg_local
    (f : intervalDomain.Point → ℝ) :
    0 ≤ intervalDomainSupNorm f := by
  unfold intervalDomainSupNorm
  by_cases hbdd : BddAbove (Set.range (fun x : intervalDomain.Point => |f x|))
  · exact le_csSup_of_le hbdd ⟨⟨0, le_refl 0, zero_le_one⟩, rfl⟩
      (abs_nonneg _)
  · change 0 ≤ sSup (Set.range fun x : intervalDomain.Point => |f x|)
    rw [Real.sSup_def, dif_neg (by simp [hbdd])]

private theorem solution_slice_abs_bddAbove_local
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|)) := by
  classical
  have hcont : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    ((hsol.regularity.2.2.2.2.1 t ht).1.1).continuousOn
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc.image_of_continuousOn hcont.abs).bddAbove
  refine ⟨M, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hMx := hM ⟨x.1, x.2, rfl⟩
  have hlift : intervalDomainLift (u t) x.1 = u t x := by
    simp [intervalDomainLift]
  simpa [hlift] using hMx

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
    (hpExp : 0 < pExp) :
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
  have hpExp_pos : 0 < pExp := hpExp
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

def scalarSeedAgmonAbsorbConstant
    (M p p0 rho eps : ℝ) : ℝ :=
  let theta : ℝ := (p - p0) / p
  let alpha : ℝ := (p + rho - p0) / p
  let eta : ℝ := (theta + alpha) / 2
  let c2 : ℝ := 2 * Real.sqrt (M * (M / eps))
  let c : ℝ := 2 * M + c2
  let B0 : ℝ := (4 * c / 1 + 1) ^ (1 / (1 - eta))
  let B : ℝ := max 1 B0
  M * B ^ alpha

private lemma sqrt_seed_product_eq
    {M eps S theta alpha : ℝ}
    (hM : 0 ≤ M) (heps : 0 < eps) (hS : 0 < S) :
    2 * Real.sqrt (M * S ^ theta) *
        Real.sqrt ((M / eps) * S ^ alpha) =
      2 * Real.sqrt (M * (M / eps)) * S ^ ((theta + alpha) / 2) := by
  have hMeps : 0 ≤ M / eps := div_nonneg hM heps.le
  have hSnn : 0 ≤ S := hS.le
  have hsqrt_theta : Real.sqrt (S ^ theta) = S ^ (theta / 2) := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hSnn]
    congr 1
    ring
  have hsqrt_alpha : Real.sqrt (S ^ alpha) = S ^ (alpha / 2) := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hSnn]
    congr 1
    ring
  calc
    2 * Real.sqrt (M * S ^ theta) * Real.sqrt ((M / eps) * S ^ alpha)
        = 2 * (Real.sqrt M * Real.sqrt (S ^ theta)) *
            (Real.sqrt (M / eps) * Real.sqrt (S ^ alpha)) := by
          rw [Real.sqrt_mul hM (S ^ theta), Real.sqrt_mul hMeps (S ^ alpha)]
    _ = 2 * (Real.sqrt M * S ^ (theta / 2)) *
            (Real.sqrt (M / eps) * S ^ (alpha / 2)) := by
          rw [hsqrt_theta, hsqrt_alpha]
    _ = 2 * (Real.sqrt M * Real.sqrt (M / eps)) *
            (S ^ (theta / 2) * S ^ (alpha / 2)) := by ring
    _ = 2 * Real.sqrt (M * (M / eps)) *
            (S ^ (theta / 2) * S ^ (alpha / 2)) := by
          rw [Real.sqrt_mul hM (M / eps)]
    _ = 2 * Real.sqrt (M * (M / eps)) *
            S ^ ((theta + alpha) / 2) := by
          rw [← Real.rpow_add hS]
          congr 2
          ring

lemma scalar_seed_agmon_absorb
    {M S G p p0 rho eps : ℝ}
    (hM : 0 ≤ M) (hS : 0 ≤ S) (hG : 0 ≤ G)
    (hp0 : 0 < p0) (hp : p0 ≤ p)
    (hrho : 0 < rho) (hrho_lt : rho < 2 * p0)
    (heps : 0 < eps)
    (hSineq :
      S ≤ 2 * M * S ^ ((p - p0) / p) +
        2 * Real.sqrt (M * S ^ ((p - p0) / p)) * Real.sqrt G) :
    M * S ^ ((p + rho - p0) / p) ≤
      eps * G + scalarSeedAgmonAbsorbConstant M p p0 rho eps := by
  let theta : ℝ := (p - p0) / p
  let alpha : ℝ := (p + rho - p0) / p
  let eta : ℝ := (theta + alpha) / 2
  have hp_pos : 0 < p := lt_of_lt_of_le hp0 hp
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have htheta_nonneg : 0 ≤ theta := by
    dsimp [theta]
    exact div_nonneg (sub_nonneg.mpr hp) hp_pos.le
  have halpha_pos : 0 < alpha := by
    dsimp [alpha]
    exact div_pos (by linarith) hp_pos
  have halpha_nonneg : 0 ≤ alpha := halpha_pos.le
  have htheta_le_alpha : theta ≤ alpha := by
    dsimp [theta, alpha]
    rw [div_le_div_iff_of_pos_right hp_pos]
    linarith
  have htheta_le_eta : theta ≤ eta := by
    dsimp [eta]
    linarith
  have heta_nonneg : 0 ≤ eta := by
    dsimp [eta]
    linarith
  have heta_lt_one : eta < 1 := by
    dsimp [eta, theta, alpha]
    field_simp [hp_ne]
    nlinarith
  let c2 : ℝ := 2 * Real.sqrt (M * (M / eps))
  let c : ℝ := 2 * M + c2
  let B0 : ℝ := (4 * c / 1 + 1) ^ (1 / (1 - eta))
  let B : ℝ := max 1 B0
  have hc2_nonneg : 0 ≤ c2 := by
    dsimp [c2]
    positivity
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    nlinarith
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact le_trans zero_le_one (le_max_left _ _)
  have hC_nonneg : 0 ≤ M * B ^ alpha :=
    mul_nonneg hM (Real.rpow_nonneg hB_nonneg alpha)
  change M * S ^ alpha ≤ eps * G + M * B ^ alpha
  by_cases hlarge : M * S ^ alpha ≤ eps * G
  · have hEG_nonneg : 0 ≤ eps * G := mul_nonneg heps.le hG
    linarith
  · have hS_le_B : S ≤ B := by
      by_cases hSle_one : S ≤ 1
      · exact le_trans hSle_one (le_max_left _ _)
      · have hS_gt_one : 1 < S := lt_of_not_ge hSle_one
        have hS_pos : 0 < S := lt_trans zero_lt_one hS_gt_one
        have hnot : eps * G < M * S ^ alpha := not_le.mp hlarge
        have hG_lt : G < (M * S ^ alpha) / eps := by
          rw [lt_div_iff₀ heps]
          simpa [mul_comm] using hnot
        have hG_le : G ≤ (M / eps) * S ^ alpha := by
          have hEq : (M * S ^ alpha) / eps = (M / eps) * S ^ alpha := by ring
          rw [hEq] at hG_lt
          exact le_of_lt hG_lt
        have hsqrtG_le :
            Real.sqrt G ≤ Real.sqrt ((M / eps) * S ^ alpha) :=
          Real.sqrt_le_sqrt hG_le
        have hcoef_nonneg : 0 ≤ 2 * Real.sqrt (M * S ^ theta) := by
          positivity
        have hterm_le₁ :
            2 * Real.sqrt (M * S ^ theta) * Real.sqrt G ≤
              2 * Real.sqrt (M * S ^ theta) *
                Real.sqrt ((M / eps) * S ^ alpha) := by
          exact mul_le_mul_of_nonneg_left hsqrtG_le hcoef_nonneg
        have hterm_eq :
            2 * Real.sqrt (M * S ^ theta) *
                Real.sqrt ((M / eps) * S ^ alpha) =
              c2 * S ^ eta := by
          dsimp [c2, eta]
          exact sqrt_seed_product_eq hM heps hS_pos
        have htheta_pow_le : S ^ theta ≤ S ^ eta :=
          Real.rpow_le_rpow_of_exponent_le hS_gt_one.le htheta_le_eta
        have hterm_le :
            2 * Real.sqrt (M * S ^ theta) * Real.sqrt G ≤
              c2 * S ^ eta := by
          calc
            2 * Real.sqrt (M * S ^ theta) * Real.sqrt G
                ≤ 2 * Real.sqrt (M * S ^ theta) *
                    Real.sqrt ((M / eps) * S ^ alpha) := hterm_le₁
            _ = c2 * S ^ eta := hterm_eq
        have hfirst_le : 2 * M * S ^ theta ≤ 2 * M * S ^ eta := by
          exact mul_le_mul_of_nonneg_left htheta_pow_le (by nlinarith [hM])
        have hS_sub : S ≤ c * S ^ eta := by
          calc
            S ≤ 2 * M * S ^ theta +
                2 * Real.sqrt (M * S ^ theta) * Real.sqrt G := by
                  simpa [theta] using hSineq
            _ ≤ 2 * M * S ^ eta + c2 * S ^ eta := by
                  exact add_le_add hfirst_le hterm_le
            _ = c * S ^ eta := by
                  dsimp [c]
                  ring
        have hS_bound0 : S ≤ B0 := by
          have hsub :=
            ShenWork.Paper2.IntervalDomainBootstrap.sublinear_algebraic_bound
              (A := 1) (c := c) (d := 0) (e := 0) (x := S) (θ := eta)
              (by norm_num) hc_nonneg (by norm_num) (by norm_num) hS
              heta_nonneg heta_lt_one ?_
          · dsimp [B0]
            simpa using hsub
          · simpa [zero_add, one_mul, add_zero] using hS_sub
        exact le_trans hS_bound0 (le_max_right _ _)
    have hpow_le : S ^ alpha ≤ B ^ alpha :=
      Real.rpow_le_rpow hS hS_le_B halpha_nonneg
    have hleft_le : M * S ^ alpha ≤ M * B ^ alpha :=
      mul_le_mul_of_nonneg_left hpow_le hM
    have hEG_nonneg : 0 ≤ eps * G := mul_nonneg heps.le hG
    exact le_trans hleft_le (by linarith)

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
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0) :
    AgmonAbsorbedInterpolationBefore u T rho p0 := by
  unfold AgmonAbsorbedInterpolationBefore
  intro pExp hpExp eps heps
  rcases AbstractLpBootstrapHypothesis.initial_lp_bound hboot with ⟨C0, hC0⟩
  let M0 : ℝ := max C0 0
  have hM0_nonneg : 0 ≤ M0 := by
    dsimp [M0]
    exact le_max_right C0 0
  have hseed_bound :
      ∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x => (u t x) ^ p0) ≤ M0 := by
    intro t ht0 htT
    exact le_trans (hC0 t ht0 htT) (le_max_left C0 0)
  have hrho : 0 < rho :=
    AbstractLpBootstrapHypothesis.rho_pos hboot
  have hp0_gt_one : 1 < p0 := by
    have hthreshold := AbstractLpBootstrapHypothesis.p0_gt_threshold hboot
    have hone_le :
        (1 : ℝ) ≤ max 1 (rho * (params.N : ℝ) / 2) :=
      le_max_left _ _
    linarith
  have hp0_pos : 0 < p0 := lt_trans zero_lt_one hp0_gt_one
  have hpExp_pos : 0 < pExp := lt_of_lt_of_le hp0_pos hpExp
  have hrho_lt_two_p0 : rho < 2 * p0 := by
    have hthreshold := AbstractLpBootstrapHypothesis.p0_gt_threshold hboot
    have hrhoN_lt : rho * (params.N : ℝ) / 2 < p0 :=
      lt_of_le_of_lt (le_max_right _ _) hthreshold
    have hN_ge_one_nat : 1 ≤ params.N := Nat.succ_le_of_lt params.hN
    have hN_ge_one : (1 : ℝ) ≤ (params.N : ℝ) := by
      exact_mod_cast hN_ge_one_nat
    have hhalf_le : rho / 2 ≤ rho * (params.N : ℝ) / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hN_ge_one hrho.le]
    nlinarith
  refine ⟨scalarSeedAgmonAbsorbConstant M0 pExp p0 rho eps, ?_⟩
  intro t ht0 htT
  let U : ℝ := intervalDomainSupNorm (u t)
  let S : ℝ := U ^ pExp
  let Y : ℝ := intervalDomain.integral (fun x => (u t x) ^ pExp)
  let G : ℝ := intervalDomain.integral (fun x =>
    (intervalDomain.gradNorm
      (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)
  let seed : ℝ := intervalDomain.integral (fun x => (u t x) ^ p0)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hf_nonneg : ∀ x : intervalDomain.Point, 0 ≤ u t x :=
    fun x => (hsol.u_pos' ht0 htT (x := x)).le
  have hf_bdd :
      BddAbove (Set.range fun x : intervalDomain.Point => |u t x|) :=
    solution_slice_abs_bddAbove_local hsol ht
  have hp0_nonneg : 0 ≤ p0 := hp0_pos.le
  have hp_minus_nonneg : 0 ≤ pExp - p0 := sub_nonneg.mpr hpExp
  have hhigh_minus_nonneg : 0 ≤ pExp + rho - p0 := by
    linarith [hp_minus_nonneg, hrho.le]
  have hseed_int :
      IntervalIntegrable
        (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ p0))
        MeasureTheory.volume 0 1 :=
    intervalDomain_u_rpow_intervalIntegrable_of_regularity
      (q := p0) hsol ht0 htT
  have hY_int :
      IntervalIntegrable
        (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
        MeasureTheory.volume 0 1 :=
    intervalDomain_u_rpow_intervalIntegrable_of_regularity
      (q := pExp) hsol ht0 htT
  have hhigh_int :
      IntervalIntegrable
        (intervalDomainLift
          (fun x : intervalDomain.Point => (u t x) ^ (pExp + rho)))
        MeasureTheory.volume 0 1 :=
    intervalDomain_u_rpow_intervalIntegrable_of_regularity
      (q := pExp + rho) hsol ht0 htT
  have hY_left_int :
      IntervalIntegrable
        (intervalDomainLift
          (fun x : intervalDomain.Point => (u t x) ^ (p0 + (pExp - p0))))
        MeasureTheory.volume 0 1 := by
    have hpow : p0 + (pExp - p0) = pExp := by ring
    simpa [hpow] using hY_int
  have hhigh_left_int :
      IntervalIntegrable
        (intervalDomainLift
          (fun x : intervalDomain.Point =>
            (u t x) ^ (p0 + (pExp + rho - p0))))
        MeasureTheory.volume 0 1 := by
    have hpow : p0 + (pExp + rho - p0) = pExp + rho := by ring
    simpa [hpow] using hhigh_int
  have hU_nonneg : 0 ≤ U := by
    dsimp [U]
    exact intervalDomainSupNorm_nonneg_local (u t)
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Real.rpow_nonneg hU_nonneg pExp
  have hY_nonneg : 0 ≤ Y := by
    dsimp [Y]
    exact intervalDomain_integral_u_rpow_nonneg_of_regularity
      (q := pExp) hsol ht0 htT
  have hchain :=
    intervalDomain_moser_gradient_integral_eq_weighted_of_regularity
      (params := params) (T := T) (pExp := pExp) (u := u) (v := v)
      hsol ht0 htT
  have hG_nonneg : 0 ≤ G := by
    dsimp [G]
    rw [hchain]
    exact mul_nonneg (sq_nonneg _) <|
      intervalDomain_lp_weighted_gradient_dissipation_nonneg_of_regularity
        (pExp := pExp) hsol ht0 htT
  have hY_raw :=
    intervalDomain_higher_Lp_le_Linf_rpow_mul_seed
      (f := u t) hf_nonneg hf_bdd
      (pExp := p0) (rho := pExp - p0)
      hp0_nonneg hp_minus_nonneg hY_left_int hseed_int
  have hY_seed :
      Y ≤ U ^ (pExp - p0) * seed := by
    have hpow : p0 + (pExp - p0) = pExp := by ring
    simpa [Y, U, seed, hpow] using hY_raw
  have hU_theta :
      U ^ (pExp - p0) = S ^ ((pExp - p0) / pExp) := by
    have hmul : pExp * ((pExp - p0) / pExp) = pExp - p0 := by
      field_simp [ne_of_gt hpExp_pos]
    calc
      U ^ (pExp - p0) = U ^ (pExp * ((pExp - p0) / pExp)) := by
          rw [hmul]
      _ = (U ^ pExp) ^ ((pExp - p0) / pExp) := by
          rw [Real.rpow_mul hU_nonneg]
      _ = S ^ ((pExp - p0) / pExp) := by
          rfl
  have hY_le_seed :
      Y ≤ M0 * S ^ ((pExp - p0) / pExp) := by
    have hseed_t : seed ≤ M0 := by
      dsimp [seed]
      exact hseed_bound t ht0 htT
    have hcoef_nonneg : 0 ≤ U ^ (pExp - p0) :=
      Real.rpow_nonneg hU_nonneg _
    calc
      Y ≤ U ^ (pExp - p0) * seed := hY_seed
      _ ≤ U ^ (pExp - p0) * M0 :=
          mul_le_mul_of_nonneg_left hseed_t hcoef_nonneg
      _ = M0 * S ^ ((pExp - p0) / pExp) := by
          rw [hU_theta]
          ring
  have hsup_step :
      S ≤ 2 * Y + 2 * Real.sqrt Y * Real.sqrt G := by
    have hstep :=
      intervalDomain_supNorm_rpow_le_energy_plus_gradient
        (params := params) (T := T) (t := t) (pExp := pExp)
        (u := u) (v := v) hsol ht0 htT hpExp_pos
    simpa [S, U, Y, G] using hstep
  have hsqrtY_le :
      Real.sqrt Y ≤
        Real.sqrt (M0 * S ^ ((pExp - p0) / pExp)) :=
    Real.sqrt_le_sqrt hY_le_seed
  have hYterm_le :
      2 * Y ≤ 2 * (M0 * S ^ ((pExp - p0) / pExp)) :=
    mul_le_mul_of_nonneg_left hY_le_seed (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrtterm_le :
      2 * Real.sqrt Y * Real.sqrt G ≤
        2 * Real.sqrt (M0 * S ^ ((pExp - p0) / pExp)) *
          Real.sqrt G := by
    have hmul :=
      mul_le_mul_of_nonneg_right hsqrtY_le (Real.sqrt_nonneg G)
    nlinarith
  have hSineq :
      S ≤ 2 * M0 * S ^ ((pExp - p0) / pExp) +
        2 * Real.sqrt (M0 * S ^ ((pExp - p0) / pExp)) *
          Real.sqrt G := by
    calc
      S ≤ 2 * Y + 2 * Real.sqrt Y * Real.sqrt G := hsup_step
      _ ≤
          2 * (M0 * S ^ ((pExp - p0) / pExp)) +
            2 * Real.sqrt (M0 * S ^ ((pExp - p0) / pExp)) *
              Real.sqrt G := add_le_add hYterm_le hsqrtterm_le
      _ =
          2 * M0 * S ^ ((pExp - p0) / pExp) +
            2 * Real.sqrt (M0 * S ^ ((pExp - p0) / pExp)) *
              Real.sqrt G := by ring
  have hhigh_raw :=
    intervalDomain_higher_Lp_le_Linf_rpow_mul_seed
      (f := u t) hf_nonneg hf_bdd
      (pExp := p0) (rho := pExp + rho - p0)
      hp0_nonneg hhigh_minus_nonneg hhigh_left_int hseed_int
  have hhigh_seed :
      intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) ≤
        U ^ (pExp + rho - p0) * seed := by
    have hpow : p0 + (pExp + rho - p0) = pExp + rho := by ring
    simpa [U, seed, hpow] using hhigh_raw
  have hU_alpha :
      U ^ (pExp + rho - p0) =
        S ^ ((pExp + rho - p0) / pExp) := by
    have hmul :
        pExp * ((pExp + rho - p0) / pExp) =
          pExp + rho - p0 := by
      field_simp [ne_of_gt hpExp_pos]
    calc
      U ^ (pExp + rho - p0) =
          U ^ (pExp * ((pExp + rho - p0) / pExp)) := by
            rw [hmul]
      _ = (U ^ pExp) ^ ((pExp + rho - p0) / pExp) := by
            rw [Real.rpow_mul hU_nonneg]
      _ = S ^ ((pExp + rho - p0) / pExp) := by
            rfl
  have hhigh_le_seed :
      intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) ≤
        M0 * S ^ ((pExp + rho - p0) / pExp) := by
    have hseed_t : seed ≤ M0 := by
      dsimp [seed]
      exact hseed_bound t ht0 htT
    have hcoef_nonneg : 0 ≤ U ^ (pExp + rho - p0) :=
      Real.rpow_nonneg hU_nonneg _
    calc
      intervalDomain.integral (fun x => (u t x) ^ (pExp + rho))
          ≤ U ^ (pExp + rho - p0) * seed := hhigh_seed
      _ ≤ U ^ (pExp + rho - p0) * M0 :=
          mul_le_mul_of_nonneg_left hseed_t hcoef_nonneg
      _ = M0 * S ^ ((pExp + rho - p0) / pExp) := by
          rw [hU_alpha]
          ring
  have hscalar :
      M0 * S ^ ((pExp + rho - p0) / pExp) ≤
        eps * G + scalarSeedAgmonAbsorbConstant M0 pExp p0 rho eps :=
    scalar_seed_agmon_absorb hM0_nonneg hS_nonneg hG_nonneg
      hp0_pos hpExp hrho hrho_lt_two_p0 heps hSineq
  exact le_trans hhigh_le_seed (by simpa [G] using hscalar)

/-! ### Faithful positive-time conclusion of the abstract bootstrap

The printed statement of Lemma 2.6 asks for a bound on the whole open time
interval.  That conclusion additionally needs control of every higher power
at the initial endpoint.  Corollary 2.1 only uses the terminal-time conclusion:
after any fixed positive anchor time, the scalar damping inequality bounds the
power uniformly up to the terminal horizon.  The following predicate records
exactly that conclusion and does not smuggle an initial trace into the
abstract energy hypothesis. -/

/-- Uniform power control after every fixed positive anchor time. -/
def LpPowerBoundedOnTerminalWindow
    (D : BoundedDomainData) (pExp T : ℝ)
    (u : ℝ → D.Point → ℝ) : Prop :=
  ∀ s, 0 < s → s < T → ∃ C,
    ∀ t, s ≤ t → t < T →
      D.integral (fun x => (u t x) ^ pExp) ≤ C

/-- A before-horizon bound restricts to a terminal subwindow. -/
theorem lpPowerBoundedOnTerminalWindow_of_boundedBefore
    {D : BoundedDomainData} {pExp T : ℝ}
    {u : ℝ → D.Point → ℝ}
    (h : LpPowerBoundedBefore D pExp T u) :
    LpPowerBoundedOnTerminalWindow D pExp T u := by
  rcases h with ⟨C, hC⟩
  intro s hs0 _hsT
  refine ⟨C, ?_⟩
  intro t ht htT
  exact hC t (lt_of_lt_of_le hs0 ht) htT

/-- Agmon absorption turns the abstract bootstrap energy inequality into a
scalar linear damping inequality at every exponent above the seed. -/
theorem intervalDomain_bootstrap_linear_damping_of_energy
    {params : CM2Params} {T rho p0 pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u
      (params.N : ℝ) T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hpExp : p0 ≤ pExp) :
    ∃ B > 0, ∃ D, ∀ t, 0 < t → t < T →
      (1 / pExp) *
          deriv (fun τ =>
            intervalDomain.integral (fun x => (u τ x) ^ pExp)) t +
        B * intervalDomain.integral (fun x => (u t x) ^ pExp) ≤ D := by
  have hinterp :=
    produce_AgmonAbsorbedInterpolationBefore_of_classical hsol hboot
  obtain ⟨A, hA, B, hB, K, hK, L, hfull⟩ := henergy pExp hpExp
  let eps : ℝ := A / (2 * K)
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  obtain ⟨Ceps, hCeps⟩ := hinterp pExp hpExp eps heps
  refine ⟨B, hB, K * Ceps + L, ?_⟩
  intro t ht0 htT
  let G : ℝ := intervalDomain.integral (fun x =>
    (intervalDomain.gradNorm
      (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)
  let Z : ℝ := intervalDomain.integral (fun x => (u t x) ^ (pExp + rho))
  have hfull_t := hfull t ht0 htT
  have hinterp_t : Z ≤ eps * G + Ceps := by
    simpa [Z, G] using hCeps t ht0 htT
  have hG : 0 ≤ G := by
    dsimp [G]
    rw [intervalDomain_moser_gradient_integral_eq_weighted_of_regularity
      (params := params) (T := T) (pExp := pExp)
      (u := u) (v := v) hsol ht0 htT]
    exact mul_nonneg (sq_nonneg _) <|
      intervalDomain_lp_weighted_gradient_dissipation_nonneg_of_regularity
        (pExp := pExp) hsol ht0 htT
  have hscaled : K * Z ≤ K * (eps * G + Ceps) :=
    mul_le_mul_of_nonneg_left hinterp_t hK.le
  have hKe : K * eps = A / 2 := by
    dsimp [eps]
    field_simp [ne_of_gt hK]
  have hscaled' : K * Z ≤ (A / 2) * G + K * Ceps := by
    calc
      K * Z ≤ K * (eps * G + Ceps) := hscaled
      _ = (A / 2) * G + K * Ceps := by
        rw [mul_add, ← mul_assoc, hKe]
  dsimp [G, Z] at hfull_t hscaled' ⊢
  nlinarith

/-- A linear damping inequality bounds one terminal time window.  No initial
trace is needed: the positive anchor slice is a finite classical slice. -/
theorem intervalDomain_lp_power_bounded_on_terminal_window_of_linear_damping
    {params : CM2Params} {T pExp B D : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hp : 1 < pExp) (hB : 0 < B)
    (hdamp : ∀ t, 0 < t → t < T →
      (1 / pExp) *
          deriv (fun τ =>
            intervalDomain.integral (fun x => (u τ x) ^ pExp)) t +
        B * intervalDomain.integral (fun x => (u t x) ^ pExp) ≤ D) :
    LpPowerBoundedOnTerminalWindow intervalDomain pExp T u := by
  let E : ℝ → ℝ := fun s =>
    intervalDomain.integral (fun x => (u s x) ^ pExp)
  let K : ℝ := max 0 (D / B)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact le_max_left _ _
  have hDK : D ≤ B * K := by
    have hdiv : D / B ≤ K := by
      dsimp [K]
      exact le_max_right _ _
    have hmul := mul_le_mul_of_nonneg_left hdiv hB.le
    have hcancel : B * (D / B) = D := by
      field_simp [ne_of_gt hB]
    rwa [hcancel] at hmul
  have hEderivAt : ∀ s, 0 < s → s < T →
      HasDerivAt E (deriv E s) s := by
    intro s hs0 hsT
    have hpow := intervalDomainPowerEnergy_hasDerivAt
      (q := pExp) hsol ⟨hs0, hsT⟩
    have hEq : E = fun r => intervalDomainPowerEnergy pExp u r := by
      funext r
      dsimp [E, intervalDomainPowerEnergy]
      exact intervalDomain_integral_rpow_eq_lift_integral
    rw [hEq]
    exact hpow.differentiableAt.hasDerivAt
  have hEcont : ContinuousOn E (Set.Ioo (0 : ℝ) T) := by
    intro s hs
    exact (hEderivAt s hs.1 hs.2).continuousAt.continuousWithinAt
  have hEderiv : ∀ s ∈ Set.Ioo (0 : ℝ) T, K < E s →
      ∃ d : ℝ, d ≤ 0 ∧ HasDerivAt E d s := by
    intro s hs hKs
    have hDamp := hdamp s hs.1 hs.2
    have hp0 : 0 < pExp := lt_trans zero_lt_one hp
    refine ⟨deriv E s, ?_, hEderivAt s hs.1 hs.2⟩
    have hinv : 0 < 1 / pExp := one_div_pos.mpr hp0
    have hBE : B * K < B * E s := mul_lt_mul_of_pos_left hKs hB
    change (1 / pExp) * deriv E s + B * E s ≤ D at hDamp
    nlinarith
  intro anchor hanchor0 hanchorT
  let C : ℝ := max K (E anchor)
  refine ⟨C, ?_⟩
  intro t hat htT
  have hEt : E t ≤ C := by
    by_cases hle : E t ≤ K
    · exact hle.trans (le_max_left _ _)
    · push Not at hle
      by_cases heq : t = anchor
      · subst t
        exact le_max_right _ _
      · have hat_lt : anchor < t :=
          lt_of_le_of_ne hat (Ne.symm heq)
        have habove : ∀ s ∈ Set.Ioc (0 : ℝ) t, K < E s :=
          threshold_persists_below_of_hasDerivAt_nonpos
            (lt_of_lt_of_le hanchor0 hat) htT hEcont hEderiv hle
        have hsubIoo : Set.Icc anchor t ⊆ Set.Ioo (0 : ℝ) T := fun z hz =>
          ⟨lt_of_lt_of_le hanchor0 hz.1, lt_of_le_of_lt hz.2 htT⟩
        have hsubIoc : Set.Ioo anchor t ⊆ Set.Ioc (0 : ℝ) t := fun z hz =>
          ⟨lt_trans hanchor0 hz.1, hz.2.le⟩
        have hanti : AntitoneOn E (Set.Icc anchor t) := by
          apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
            (hEcont.mono hsubIoo)
          · intro z hz
            rw [interior_Icc] at hz
            exact ((hEderivAt z
              (lt_trans hanchor0 hz.1) (lt_trans hz.2 htT)).differentiableAt
                ).differentiableWithinAt
          · intro z hz
            rw [interior_Icc] at hz
            have hzIoo : z ∈ Set.Ioo (0 : ℝ) T :=
              ⟨lt_trans hanchor0 hz.1, lt_trans hz.2 htT⟩
            obtain ⟨d, hd, hD⟩ := hEderiv z hzIoo (habove z (hsubIoc hz))
            rw [hD.deriv]
            exact hd
        have hEtEa : E t ≤ E anchor :=
          hanti (Set.left_mem_Icc.mpr hat_lt.le)
            (Set.right_mem_Icc.mpr hat_lt.le) hat_lt.le
        exact hEtEa.trans (le_max_right _ _)
  simpa [E] using hEt

/-- Correct positive-time form of the abstract Lemma 2.6 bootstrap on the
unit interval: every exponent is uniformly bounded on a terminal subwindow.
For exponents below the seed this follows from finite-measure monotonicity;
for exponents above it, Agmon absorption and scalar damping apply directly. -/
theorem intervalDomain_abstractLpBootstrap_terminal
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u
      (params.N : ℝ) T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0) :
    ∀ pExp > 1,
      LpPowerBoundedOnTerminalWindow intervalDomain pExp T u := by
  intro pExp hpExp
  by_cases hp : p0 ≤ pExp
  · obtain ⟨B, hB, D, hdamp⟩ :=
      intervalDomain_bootstrap_linear_damping_of_energy
        hsol hboot henergy hp
    exact intervalDomain_lp_power_bounded_on_terminal_window_of_linear_damping
      hsol hpExp hB hdamp
  · have hp_le : pExp ≤ p0 := le_of_lt (lt_of_not_ge hp)
    have hLp : LpPowerBoundedBefore intervalDomain pExp T u :=
      intervalDomain_LpPowerBoundedBefore_mono_of_integrable_nonneg
        hpExp hp_le
        (fun t ht0 htT x => (hsol.u_pos' ht0 htT (x := x)).le)
        (fun t ht0 htT =>
          intervalDomain_u_rpow_intervalIntegrable_of_regularity
            (q := pExp) hsol ht0 htT)
        (fun t ht0 htT =>
          intervalDomain_u_rpow_intervalIntegrable_of_regularity
            (q := p0) hsol ht0 htT)
        (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)
    exact lpPowerBoundedOnTerminalWindow_of_boundedBefore hLp

/-! ### Axiom audit -/

#print axioms produce_AgmonAbsorbedInterpolationBefore_of_classical
#print axioms intervalDomain_abstractLpBootstrap_terminal

end ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute

end
