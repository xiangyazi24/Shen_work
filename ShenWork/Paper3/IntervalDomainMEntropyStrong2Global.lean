import ShenWork.Paper3.IntervalDomainMEntropyStrong1Global
import ShenWork.Paper3.IntervalDomainEntropyStrong2
import ShenWork.Paper3.IntervalDomainEntropyStrong2Dynamics
import ShenWork.Paper3.IntervalDomainPersistenceGeneralMPart3
import ShenWork.Paper3.IntervalDomainModelLinearizationAudit

/-!
# Unconditional second-branch global stability for the faithful general-`m` equation

The second strong-logistic branch improves the chemotactic weight through an
eventual signal floor.  For `m = 1` the committed legacy persistence supplies
the floor at `vABLowerFormula` itself (transported through the `m = 1` model
bridge proved below); for `m > 1` the committed faithful Theorem 2.1(3)
persistence supplies a liminf signal bound that dominates `vABLowerFormula`
non-strictly.  Because the strict-threshold inequality
`χ₀ < chiStrong2Formula` has slack, the dissipation coefficient stays positive
for a floor slightly *below* `vABLowerFormula`, which the liminf bound does
reach eventually.  This closes the branch with no `p.m = 1` hypothesis.
-/

namespace ShenWork.Paper3

open Filter Topology Set
open ShenWork.IntervalDomain ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep

noncomputable section

/-- A faithful `intervalDomainM` classical solution is a legacy
`intervalDomain` classical solution on the explicit `m = 1` slice — the
converse of `isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one`. -/
theorem isPaper2ClassicalSolution_of_intervalDomainM_of_m_eq_one
    (p : CM2Params) (hm : p.m = 1) {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution
      intervalDomainM p T u v) :
    ShenWork.Paper2.IsPaper2ClassicalSolution
      intervalDomain p T u v := by
  open ShenWork.Paper2 in
  refine IsPaper2ClassicalSolution.of_components
    hsol.T_pos ?_ ?_ ?_ ?_ ?_ ?_
  · exact hsol.regularity
  · intro t x ht0 htT
    exact hsol.u_pos' ht0 htT
  · intro t x ht0 htT
    exact hsol.v_nonneg ht0 htT
  · intro t x ht0 htT hx
    have h := hsol.pde_u ht0 htT hx
    change
      intervalDomainM.timeDeriv u t x =
        intervalDomainM.laplacian (u t) x -
          p.χ₀ * intervalDomainM.chemotaxisDiv p (u t) (v t) x +
            u t x * (p.a - p.b * u t x ^ p.α) at h
    change
      intervalDomain.timeDeriv u t x =
        intervalDomain.laplacian (u t) x -
          p.χ₀ * intervalDomain.chemotaxisDiv p (u t) (v t) x +
            u t x * (p.a - p.b * u t x ^ p.α)
    change
      deriv (fun s : ℝ => u s x) t =
        intervalDomainLaplacian (u t) x -
          p.χ₀ * intervalDomainChemotaxisDiv p (u t) (v t) x +
            u t x * (p.a - p.b * u t x ^ p.α)
    rw [← intervalDomainChemotaxisDivM_eq_of_m_eq_one p hm]
    exact h
  · intro t x ht0 htT hx
    exact hsol.pde_v ht0 htT hx
  · intro t x ht0 htT hx
    exact hsol.neumann ht0 htT hx

/-- Positive bounded global faithful orbits transfer to the legacy domain on
the `m = 1` slice. -/
theorem positiveGlobalBoundedSolution_of_intervalDomainM_of_m_eq_one
    (p : CM2Params) (hm : p.m = 1)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    PositiveGlobalBoundedSolution intervalDomain p u v := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    exact isPaper2ClassicalSolution_of_intervalDomainM_of_m_eq_one
      p hm (huv.classical T hT)
  · exact huv.bounded
  · exact fun t x ht hx => huv.pos (t := t) (x := x) ht hx

/-- For `m > 1` under the half-logistic `chiBar` threshold, the faithful
Theorem 2.1(3) signal level dominates `vABLowerFormula` (non-strictly; the two
coincide when `a ≥ 2b` saturates both clamps). -/
theorem vABLowerFormula_le_part3Signal
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    (hmgt : 1 < p.m) (hβ : 1 ≤ p.β)
    (hχpos : 0 < p.χ₀)
    (hχbar : p.χ₀ < chiBarFormula p) :
    vABLowerFormula p ≤
      p.ν / p.μ * theorem21Part3LowerU p ^ p.γ := by
  have hm_ne : p.m ≠ 1 := ne_of_gt hmgt
  have htheta : 0 < Theta_beta (p.β - 1) :=
    Theta_beta_pos_of_nonneg (by linarith)
  have hχμθ : p.χ₀ * p.μ * Theta_beta (p.β - 1) < p.b := by
    unfold chiBarFormula at hχbar
    rw [if_neg hm_ne] at hχbar
    have hden : 0 < p.μ * Theta_beta (p.β - 1) := mul_pos p.hμ htheta
    have hmul := (lt_div_iff₀ hden).mp hχbar
    calc p.χ₀ * p.μ * Theta_beta (p.β - 1) =
        p.χ₀ * (p.μ * Theta_beta (p.β - 1)) := by ring
      _ < p.b := hmul
  have hdenX : 0 < p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1) := by
    have : 0 < p.χ₀ * p.μ * Theta_beta (p.β - 1) :=
      mul_pos (mul_pos hχpos p.hμ) htheta
    linarith
  have hYpos : 0 < p.a / (2 * p.b) := div_pos ha (by linarith)
  have hYX : p.a / (2 * p.b) ≤
      p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1)) :=
    div_le_div_of_nonneg_left ha.le hdenX (by linarith)
  have hEpos : 0 < max (1 / (p.m - 1)) (1 / p.α) :=
    lt_of_lt_of_le (div_pos one_pos p.hα) (le_max_right _ _)
  have hinner :
      min 1 ((p.a / (2 * p.b)) ^ max (1 / (p.m - 1)) (1 / p.α)) ≤
        (min 1 (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1)))) ^
          max (1 / (p.m - 1)) (1 / p.α) := by
    rcases le_or_gt 1 (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1)))
      with hX1 | hX1
    · rw [min_eq_left hX1, Real.one_rpow]
      exact min_le_left _ _
    · rw [min_eq_right hX1.le]
      calc
        min 1 ((p.a / (2 * p.b)) ^ max (1 / (p.m - 1)) (1 / p.α)) ≤
            (p.a / (2 * p.b)) ^ max (1 / (p.m - 1)) (1 / p.α) :=
          min_le_right _ _
        _ ≤ (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
              max (1 / (p.m - 1)) (1 / p.α) :=
          Real.rpow_le_rpow hYpos.le hYX hEpos.le
  have hminNonneg :
      0 ≤ min 1 ((p.a / (2 * p.b)) ^ max (1 / (p.m - 1)) (1 / p.α)) :=
    le_min (by norm_num) (Real.rpow_nonneg hYpos.le _)
  unfold vABLowerFormula theorem21Part3LowerU
  rw [if_neg hm_ne]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hminNonneg hinner p.hγ.le)
    (div_nonneg p.hν.le p.hμ.le)

/-- Nonnegativity of the faithful elliptic signal supplies the
lower-boundedness input for the liminf API. -/
theorem intervalDomainM_infValue_v_isBoundedUnder
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    IsBoundedUnder GE.ge atTop
      (fun t => intervalDomainM.infValue (v t)) := by
  have hfloor : ∀ᶠ t in atTop, 0 ≤ intervalDomainM.infValue (v t) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have hT : 0 < t + 1 := by linarith
    have hsol := huv.classical (t + 1) hT
    change 0 ≤ sInf (Set.range (v t))
    apply le_csInf
    · exact ⟨v t ⟨0, ⟨by norm_num, by norm_num⟩⟩,
        ⟨⟨0, ⟨by norm_num, by norm_num⟩⟩, rfl⟩⟩
    · rintro y ⟨x, rfl⟩
      exact hsol.v_nonneg ht0 (by linarith) (x := x)
  exact isBoundedUnder_of_eventually_ge hfloor

/-- Eventual pointwise signal floor for faithful general-`m` orbits: any level
strictly below `vABLowerFormula` (or any nonpositive level) is eventually a
pointwise lower barrier for the signal.  The `m = 1` slice goes through the
model bridge and the committed legacy persistence; the `m > 1` slice uses the
committed faithful Theorem 2.1(3). -/
theorem intervalDomainM_strong2_eventually_floor
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β)
    (hχpos : 0 < p.χ₀)
    (hχbar : p.χ₀ < chiBarFormula p)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    {floor : ℝ}
    (hfloorlt : floor ≤ 0 ∨ floor < vABLowerFormula p) :
    ∀ᶠ t in atTop, ∀ x : intervalDomainPoint, floor ≤ v t x := by
  by_cases hf0 : floor ≤ 0
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht x
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
    have hsol := huv.classical (t + 1) (by linarith)
    exact hf0.trans (hsol.v_nonneg ht0 (by linarith))
  have hflt : floor < vABLowerFormula p := by
    rcases hfloorlt with h | h
    · exact absurd h hf0
    · exact h
  rcases eq_or_lt_of_le hm with hm1 | hmgt
  · have huv' := positiveGlobalBoundedSolution_of_intervalDomainM_of_m_eq_one
      p hm1.symm huv
    have hev := intervalDomain_eventually_vABLower_of_chi_lt_chiBar
      p hm1.symm ha hb hβ hχpos hχbar huv'
    filter_upwards [hev] with t ht x
    exact hflt.le.trans (ht x)
  · have hpart3 := intervalDomainM_part3_liminfUV_proven
      ha hb hχpos hmgt hβ huv (T0 := 1) one_pos
    have hsig := vABLowerFormula_le_part3Signal p ha hb hmgt hβ hχpos hχbar
    have hlim : floor < liminfInfValue intervalDomainM v :=
      lt_of_lt_of_le hflt (hsig.trans hpart3.2)
    have hevInf : ∀ᶠ t in atTop,
        floor < intervalDomainM.infValue (v t) :=
      eventually_lt_of_lt_liminf hlim
        (intervalDomainM_infValue_v_isBoundedUnder huv)
    filter_upwards [hevInf, eventually_ge_atTop (1 : ℝ)] with t htInf ht x
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
    have hsol := huv.classical (t + 1) (by linarith)
    have hBdd : BddBelow (Set.range (v t)) := by
      refine ⟨0, ?_⟩
      rintro y ⟨z, rfl⟩
      exact hsol.v_nonneg ht0 (by linarith)
    have hle : intervalDomainM.infValue (v t) ≤ v t x :=
      csInf_le hBdd ⟨x, rfl⟩
    linarith

/-- Exact entropy-production coefficient of the general-`m` second strong
branch at an arbitrary signal floor. -/
def strong2MFloorCoefficient
    (p : CM2Params) (uStar floor : ℝ) : ℝ :=
  p.b -
    p.χ₀ ^ 2 * p.ν ^ 2 * (2 * p.m - 1) * CAlphaGamma p.α p.γ *
        uStar ^ (2 * p.γ - p.α + 2 * p.m - 2) /
      (16 * p.μ * (1 + floor) ^ (2 * p.β))

/-- General-`m` entropy dissipation inequality at every slice on which a
nonnegative signal floor is available. -/
theorem intervalDomainM_entropySlope_le_strong2MFloorCoefficient
    {p : CM2Params} {T t uStar vStar floor : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hrel : 2 * p.γ ≤ p.α + 1)
    (hfloor : 0 ≤ floor)
    (hVfloor : ∀ x : intervalDomainPoint, floor ≤ v t x) :
    intervalDomain.integral (fun x =>
        chemotaxisEntropyIntegrand p.m uStar (u t x) *
          intervalDomain.timeDeriv u t x) ≤
      -strong2MFloorCoefficient p uStar floor *
        chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
  set c : ℝ := (2 * p.m - 1) * uStar ^ (2 * p.m - 1) with hcdef
  have hc : 0 ≤ c := by
    have h2m : (0 : ℝ) < 2 * p.m - 1 := by linarith
    exact mul_nonneg h2m.le (Real.rpow_pos_of_pos heq.u_pos _).le
  have hid := intervalDomainM_entropySlope_le_of_classical
    hm hsol ht0 htT heq
  have hyoung := intervalDomainM_entropyDiffusionChemotaxis_young
    (c := c) hc hsol ht0 htT
  have hell := intervalDomain_persistentWeightedElliptic_gradient_estimate
    hsol ht0 htT heq hfloor hVfloor
  have hpower := intervalDomain_powerDifference_integral_le_theta
    hsol ht0 htT heq.u_pos hrel
  have hbase : (0 : ℝ) < 1 + floor := by linarith
  have hscale : 0 ≤ p.χ₀ ^ 2 * c / 4 :=
    div_nonneg (mul_nonneg (sq_nonneg _) hc) (by norm_num)
  have hell' := mul_le_mul_of_nonneg_left hell hscale
  have hpowerScale : 0 ≤
      p.χ₀ ^ 2 * c / 4 *
        (p.ν ^ 2 / (4 * p.μ * (1 + floor) ^ (2 * p.β))) := by
    have hden4 : 0 < 4 * p.μ * (1 + floor) ^ (2 * p.β) :=
      mul_pos (mul_pos (by norm_num) p.hμ)
        (Real.rpow_pos_of_pos hbase _)
    exact mul_nonneg hscale (div_nonneg (sq_nonneg _) hden4.le)
  calc
    intervalDomain.integral (fun x =>
        chemotaxisEntropyIntegrand p.m uStar (u t x) *
          intervalDomain.timeDeriv u t x) ≤
        -c * intervalDomainLpWeightedGradientDissipation (2 - 2 * p.m) u t +
          p.χ₀ * c *
            ShenWork.Paper2.IntervalDomainM.lpSignedCrossIntegralM
              p (2 - 2 * p.m) u v t -
          p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
      rw [hcdef]
      exact hid
    _ ≤ p.χ₀ ^ 2 * c / 4 *
          (∫ y in (0 : ℝ)..1,
            (deriv (intervalDomainLift (v t)) y) ^ 2 *
              (1 + intervalDomainLift (v t) y) ^ (-2 * p.β)) -
        p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
      linarith
    _ ≤ p.χ₀ ^ 2 * c / 4 *
          (p.ν ^ 2 / (4 * p.μ * (1 + floor) ^ (2 * p.β)) *
            (∫ y in (0 : ℝ)..1,
              (intervalDomainLift (u t) y ^ p.γ - uStar ^ p.γ) ^ 2)) -
        p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
      linarith
    _ ≤ p.χ₀ ^ 2 * c / 4 *
          (p.ν ^ 2 / (4 * p.μ * (1 + floor) ^ (2 * p.β)) *
            (CAlphaGamma p.α p.γ * uStar ^ (2 * p.γ - p.α - 1) *
              chemotaxisThetaDissipation intervalDomain uStar p.α (u t))) -
        p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
      apply sub_le_sub_right
      calc
        p.χ₀ ^ 2 * c / 4 *
              (p.ν ^ 2 / (4 * p.μ * (1 + floor) ^ (2 * p.β)) *
                (∫ y in (0 : ℝ)..1,
                  (intervalDomainLift (u t) y ^ p.γ - uStar ^ p.γ) ^ 2)) =
            (p.χ₀ ^ 2 * c / 4 *
              (p.ν ^ 2 / (4 * p.μ * (1 + floor) ^ (2 * p.β)))) *
              (∫ y in (0 : ℝ)..1,
                (intervalDomainLift (u t) y ^ p.γ - uStar ^ p.γ) ^ 2) := by
          ring
        _ ≤ (p.χ₀ ^ 2 * c / 4 *
              (p.ν ^ 2 / (4 * p.μ * (1 + floor) ^ (2 * p.β)))) *
              (CAlphaGamma p.α p.γ * uStar ^ (2 * p.γ - p.α - 1) *
                chemotaxisThetaDissipation intervalDomain uStar p.α (u t)) :=
          mul_le_mul_of_nonneg_left hpower hpowerScale
        _ = p.χ₀ ^ 2 * c / 4 *
              (p.ν ^ 2 / (4 * p.μ * (1 + floor) ^ (2 * p.β)) *
                (CAlphaGamma p.α p.γ * uStar ^ (2 * p.γ - p.α - 1) *
                  chemotaxisThetaDissipation intervalDomain uStar p.α (u t))) := by
          ring
    _ = -strong2MFloorCoefficient p uStar floor *
        chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
      have huPow :
          uStar ^ (2 * p.m - 1) * uStar ^ (2 * p.γ - p.α - 1) =
            uStar ^ (2 * p.γ - p.α + 2 * p.m - 2) := by
        rw [← Real.rpow_add heq.u_pos]
        congr 1
        ring
      unfold strong2MFloorCoefficient
      rw [hcdef, ← huPow]
      field_simp [p.hμ.ne', (Real.rpow_pos_of_pos hbase (2 * p.β)).ne']
      ring

/-- Slack extraction from the strict second-branch threshold: some floor
strictly below `vABLowerFormula` (or zero) keeps the dissipation coefficient
positive. -/
theorem strong2MFloorCoefficient_exists_floor
    (p : CM2Params) {uStar : ℝ}
    (hb : 0 < p.b) (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β)
    (huStar : 0 < uStar)
    (hvAB : 0 ≤ vABLowerFormula p)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong2Formula p uStar) :
    ∃ floor, 0 ≤ floor ∧ (floor ≤ 0 ∨ floor < vABLowerFormula p) ∧
      0 < strong2MFloorCoefficient p uStar floor := by
  have h2β : (0 : ℝ) < 2 * p.β := by linarith
  set N : ℝ := p.χ₀ ^ 2 * p.ν ^ 2 * (2 * p.m - 1) * CAlphaGamma p.α p.γ *
    uStar ^ (2 * p.γ - p.α + 2 * p.m - 2) with hNdef
  set B : ℝ := 16 * p.μ * p.b with hBdef
  have h2m : (0 : ℝ) < 2 * p.m - 1 := by linarith
  have hN0 : 0 ≤ N := by
    rw [hNdef]
    have hC := CAlphaGamma_pos p.hα p.hγ
    have hupow := Real.rpow_pos_of_pos huStar (2 * p.γ - p.α + 2 * p.m - 2)
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)) h2m.le) hC.le) hupow.le
  have hB : 0 < B := by
    rw [hBdef]
    exact mul_pos (mul_pos (by norm_num) p.hμ) hb
  have hcoeff_of : ∀ floor : ℝ, 0 ≤ floor →
      N < B * (1 + floor) ^ (2 * p.β) →
      0 < strong2MFloorCoefficient p uStar floor := by
    intro floor hfloor hlt
    have hbase : (0 : ℝ) < 1 + floor := by linarith
    have hden : 0 < 16 * p.μ * (1 + floor) ^ (2 * p.β) :=
      mul_pos (mul_pos (by norm_num) p.hμ)
        (Real.rpow_pos_of_pos hbase _)
    unfold strong2MFloorCoefficient
    rw [sub_pos, div_lt_iff₀ hden]
    calc p.χ₀ ^ 2 * p.ν ^ 2 * (2 * p.m - 1) * CAlphaGamma p.α p.γ *
          uStar ^ (2 * p.γ - p.α + 2 * p.m - 2) = N := by rw [hNdef]
      _ < B * (1 + floor) ^ (2 * p.β) := hlt
      _ = p.b * (16 * p.μ * (1 + floor) ^ (2 * p.β)) := by
          rw [hBdef]; ring
  have hχsqrt : p.χ₀ < Real.sqrt
      (p.b * (16 * (1 + vABLowerFormula p) ^ (2 * p.β) * p.μ /
        ((2 * p.m - 1) * p.ν ^ 2 * CAlphaGamma p.α p.γ *
          uStar ^ (2 * p.γ - p.α + 2 * p.m - 2)))) := by
    unfold chiStrong2Formula at hχ
    exact (lt_min_iff.mp hχ).2
  have hsource : 0 < (2 * p.m - 1) * p.ν ^ 2 * CAlphaGamma p.α p.γ *
      uStar ^ (2 * p.γ - p.α + 2 * p.m - 2) := by
    have hC := CAlphaGamma_pos p.hα p.hγ
    have hupow := Real.rpow_pos_of_pos huStar (2 * p.γ - p.α + 2 * p.m - 2)
    exact mul_pos (mul_pos (mul_pos h2m (sq_pos_of_pos p.hν)) hC) hupow
  have hvABbase : (0 : ℝ) < 1 + vABLowerFormula p := by linarith
  have hscale : 0 < 16 * (1 + vABLowerFormula p) ^ (2 * p.β) * p.μ :=
    mul_pos (mul_pos (by norm_num)
      (Real.rpow_pos_of_pos hvABbase _)) p.hμ
  have hR : 0 < p.b *
      (16 * (1 + vABLowerFormula p) ^ (2 * p.β) * p.μ /
        ((2 * p.m - 1) * p.ν ^ 2 * CAlphaGamma p.α p.γ *
          uStar ^ (2 * p.γ - p.α + 2 * p.m - 2))) :=
    mul_pos hb (div_pos hscale hsource)
  have hχsq : p.χ₀ ^ 2 < p.b *
      (16 * (1 + vABLowerFormula p) ^ (2 * p.β) * p.μ /
        ((2 * p.m - 1) * p.ν ^ 2 * CAlphaGamma p.α p.γ *
          uStar ^ (2 * p.γ - p.α + 2 * p.m - 2))) := by
    have hsq := Real.sq_sqrt hR.le
    nlinarith [Real.sqrt_nonneg (p.b *
      (16 * (1 + vABLowerFormula p) ^ (2 * p.β) * p.μ /
        ((2 * p.m - 1) * p.ν ^ 2 * CAlphaGamma p.α p.γ *
          uStar ^ (2 * p.γ - p.α + 2 * p.m - 2))))]
  have hNvAB : N < B * (1 + vABLowerFormula p) ^ (2 * p.β) := by
    have h3 : p.χ₀ ^ 2 <
        p.b * (16 * (1 + vABLowerFormula p) ^ (2 * p.β) * p.μ) /
          ((2 * p.m - 1) * p.ν ^ 2 * CAlphaGamma p.α p.γ *
            uStar ^ (2 * p.γ - p.α + 2 * p.m - 2)) := by
      rw [mul_div_assoc]
      exact hχsq
    have hmul := (lt_div_iff₀ hsource).mp h3
    calc N = p.χ₀ ^ 2 *
          ((2 * p.m - 1) * p.ν ^ 2 * CAlphaGamma p.α p.γ *
            uStar ^ (2 * p.γ - p.α + 2 * p.m - 2)) := by
            rw [hNdef]; ring
      _ < p.b * (16 * (1 + vABLowerFormula p) ^ (2 * p.β) * p.μ) := hmul
      _ = B * (1 + vABLowerFormula p) ^ (2 * p.β) := by
            rw [hBdef]; ring
  by_cases hNB : N < B
  · refine ⟨0, le_rfl, Or.inl le_rfl, hcoeff_of 0 le_rfl ?_⟩
    have : ((1 : ℝ) + 0) ^ (2 * p.β) = 1 := by
      norm_num
    rw [this, mul_one]
    exact hNB
  · push_neg at hNB
    have hvABpos : 0 < vABLowerFormula p := by
      by_contra hnot
      push_neg at hnot
      have hvAB0 : vABLowerFormula p = 0 := le_antisymm hnot hvAB
      rw [hvAB0] at hNvAB
      have : ((1 : ℝ) + 0) ^ (2 * p.β) = 1 := by norm_num
      rw [this, mul_one] at hNvAB
      exact absurd hNvAB (not_lt.mpr hNB)
    set W : ℝ := (N / B) ^ (2 * p.β)⁻¹ with hWdef
    have hNB1 : 1 ≤ N / B := (one_le_div hB).mpr hNB
    have hW1 : 1 ≤ W := by
      calc (1 : ℝ) = 1 ^ (2 * p.β)⁻¹ := (Real.one_rpow _).symm
        _ ≤ (N / B) ^ (2 * p.β)⁻¹ :=
          Real.rpow_le_rpow (by norm_num) hNB1 (by positivity)
    have hWpow : W ^ (2 * p.β) = N / B := by
      rw [hWdef, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N / B),
        inv_mul_cancel₀ h2β.ne', Real.rpow_one]
    have hWlt : W < 1 + vABLowerFormula p := by
      by_contra hnot
      push_neg at hnot
      have hpow : (1 + vABLowerFormula p) ^ (2 * p.β) ≤ W ^ (2 * p.β) :=
        Real.rpow_le_rpow hvABbase.le hnot h2β.le
      rw [hWpow] at hpow
      have : B * (1 + vABLowerFormula p) ^ (2 * p.β) ≤ N := by
        calc B * (1 + vABLowerFormula p) ^ (2 * p.β) ≤ B * (N / B) :=
            mul_le_mul_of_nonneg_left hpow hB.le
          _ = N := by field_simp
      exact absurd hNvAB (not_lt.mpr this)
    refine ⟨(W - 1 + vABLowerFormula p) / 2, ?_, ?_, ?_⟩
    · have : 0 ≤ W - 1 := by linarith
      linarith [hvABpos]
    · refine Or.inr ?_
      linarith
    · refine hcoeff_of _ (by linarith) ?_
      have hgt : W < 1 + (W - 1 + vABLowerFormula p) / 2 := by linarith
      have hWpos : (0 : ℝ) < W := lt_of_lt_of_le one_pos hW1
      have hpow : W ^ (2 * p.β) <
          (1 + (W - 1 + vABLowerFormula p) / 2) ^ (2 * p.β) :=
        Real.rpow_lt_rpow hWpos.le hgt h2β
      rw [hWpow] at hpow
      calc N = B * (N / B) := by field_simp
        _ < B * (1 + (W - 1 + vABLowerFormula p) / 2) ^ (2 * p.β) :=
          mul_lt_mul_of_pos_left hpow hB

/-- Every positive bounded global faithful orbit in branch two has arbitrarily
late small theta-dissipation slices. -/
theorem intervalDomainM_strong2_exists_late_thetaDissipation_lt
    (p : CM2Params)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β)
    (hrel : 2 * p.γ ≤ p.α + 1)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong2Formula p
      (positiveEquilibrium p ⟨ha, hb⟩).1)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    {T q : ℝ} (hq : 0 < q) :
    ∃ t, T ≤ t ∧
      chemotaxisThetaDissipation intervalDomain
        (positiveEquilibrium p ⟨ha, hb⟩).1 p.α (u t) < q := by
  set uStar := (positiveEquilibrium p ⟨ha, hb⟩).1 with huStarDef
  set vStar := (positiveEquilibrium p ⟨ha, hb⟩).2 with hvStarDef
  have heq : Paper3ConstantEquilibrium p uStar vStar := by
    simpa [huStarDef, hvStarDef] using
      paper3ConstantEquilibrium_positive p ha hb
  obtain ⟨floor, hfloor0, hfloorlt, hcpos⟩ :=
    strong2MFloorCoefficient_exists_floor p hb hm hβ heq.u_pos
      (vABLowerFormula_pos p ha hb hm).le hχpos hχ
  have hevFloor := intervalDomainM_strong2_eventually_floor
    p ha hb hm hβ hχpos
    (chi_lt_chiBarFormula_of_lt_chiStrong2Formula p hχ) huv hfloorlt
  rcases eventually_atTop.1 hevFloor with ⟨Tv, hTv⟩
  set Tbase : ℝ := max (max T Tv) 1 with hTbaseDef
  have hTbase : 0 < Tbase :=
    lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hTle : T ≤ Tbase :=
    (le_max_left T Tv).trans (le_max_left (max T Tv) 1)
  have hTvle : Tv ≤ Tbase :=
    (le_max_right T Tv).trans (le_max_left (max T Tv) 1)
  obtain ⟨t, htbase, htSmall⟩ :=
    exists_late_dissipation_lt_of_nonnegative_energy_on_Ici
      (E := fun s => chemotaxisEntropyFunctional intervalDomain p.m uStar u s)
      (D := fun s => chemotaxisThetaDissipation intervalDomain uStar p.α (u s))
      (slope := fun s => intervalDomain.integral (fun x =>
        chemotaxisEntropyIntegrand p.m uStar (u s x) *
          intervalDomain.timeDeriv u s x))
      hcpos hTbase hq
      (fun s hs =>
        intervalDomain_chemotaxisEntropyFunctional_nonneg_of_inside_pos
          (by linarith : (1 / 2 : ℝ) ≤ p.m) heq.u_pos
          (fun x hx => huv.pos (t := s) (x := x) hs hx))
      (intervalDomainM_strongMEntropy_hasDerivAt p heq huv)
      (fun s hs => by
        have hs0 : 0 < s := lt_of_lt_of_le hTbase hs
        have hH : 0 < s + 1 := by linarith
        exact intervalDomainM_entropySlope_le_strong2MFloorCoefficient
          hm (huv.classical (s + 1) hH) hs0 (by linarith) heq hrel
          hfloor0 (hTv s (hTvle.trans hs)))
  exact ⟨t, hTle.trans htbase, htSmall⟩

/-- Unconditional second formula branch of faithful eventual Theorem 2.4 on
the general-`m` unit-interval equation.  No `p.m = 1` hypothesis. -/
theorem intervalDomainM_eventuallyGloballyExponentiallyStableNonminimal_strong2
    (p : CM2Params)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hmge : 1 ≤ p.m) (hβ : 1 ≤ p.β)
    (hrel : 2 * p.γ ≤ p.α + 1)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong2Formula p
      (positiveEquilibrium p ⟨ha, hb⟩).1) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    EventuallyGloballyExponentiallyStableNonminimal intervalDomainM p
      intervalDomainMSectorialStabilityNorms eq.1 eq.2 := by
  let eq := positiveEquilibrium p ⟨ha, hb⟩
  have heq : Paper3ConstantEquilibrium p eq.1 eq.2 := by
    simpa [eq] using paper3ConstantEquilibrium_positive p ha hb
  have hcond : NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 0 :=
    Or.inr (Or.inl ⟨hmge, hβ, hrel, hχpos, by simpa [eq] using hχ⟩)
  have hstable : LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
    simpa [eq] using hcond.linearlyStable_unitInterval p ha hb
  have hproduce : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      PositiveGlobalBoundedSolution intervalDomainM p u v →
      ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
        EventualExponentialC1ConvergenceWith intervalDomainM
          intervalDomainMSectorialStabilityNorms u v eq.1 eq.2 C rate t₀ := by
    intro u v huv
    refine intervalDomainM_eventualC1_of_lateSupClose p ha heq hstable huv ?_
    intro eps heps
    refine intervalDomainM_exists_late_supClose_of_thetaDissipation
      p heq.u_pos huv ?_ 1 heps
    intro T' q _hT' hq
    exact intervalDomainM_strong2_exists_late_thetaDissipation_lt
      p ha hb hmge hβ hrel hχpos (by simpa [eq] using hχ) huv hq
  refine ⟨?_, hproduce⟩
  intro u v huv
  obtain ⟨C, hC, rate, hrate, t₀, ht₀, hbound⟩ := hproduce u v huv
  exact intervalDomainM_uniformConvergesInSup_of_eventualExponentialC1
    hrate hbound

#print axioms isPaper2ClassicalSolution_of_intervalDomainM_of_m_eq_one
#print axioms positiveGlobalBoundedSolution_of_intervalDomainM_of_m_eq_one
#print axioms vABLowerFormula_le_part3Signal
#print axioms intervalDomainM_strong2_eventually_floor
#print axioms intervalDomainM_entropySlope_le_strong2MFloorCoefficient
#print axioms strong2MFloorCoefficient_exists_floor
#print axioms intervalDomainM_strong2_exists_late_thetaDissipation_lt
#print axioms
  intervalDomainM_eventuallyGloballyExponentiallyStableNonminimal_strong2

end

end ShenWork.Paper3
