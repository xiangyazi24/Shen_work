import ShenWork.Paper3.IntervalDomainMinimalPowerDifference
import ShenWork.Paper3.IntervalDomainEntropyBasinEntry

/-!
# Minimal-model entropy dissipation on the unit interval

This file implements Section 8.1 after the orbit-independent eventual box is
available.  The mass constraint converts the half diffusion left by Young's
inequality into an `L²` distance, while the signal floor and the local
power-difference slope control the chemotactic term.
-/

open Filter MeasureTheory Set Topology
open scoped Topology Interval

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainEnergyStep

noncomputable section

/-- On a positive mass-constrained slice lying below `uBar`, the entropy
gradient controls the squared `L²` distance to the conserved mean. -/
theorem intervalDomain_minimal_weightedGradient_ge_l2
    {p : CM2Params} {T t uStar uBar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (huBar : 0 < uBar)
    (hmass : intervalDomain.integral (u t) = uStar)
    (hupper : ∀ x : intervalDomainPoint, u t x ≤ uBar) :
    uBar ^ (-2 : ℝ) *
        (∫ y in (0 : ℝ)..1,
          (intervalDomainLift (u t) y - uStar) ^ 2) ≤
      intervalDomainLpWeightedGradientDissipation 0 u t := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let Ux : ℝ → ℝ := deriv U
  let g : ℝ → ℝ := fun y => U y ^ (-2 : ℝ) * Ux y ^ 2
  have ht : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hU2 : ContDiffOn ℝ 2 U (Icc (0 : ℝ) 1) := by
    simpa [U] using (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hUcont : ContinuousOn U (Icc (0 : ℝ) 1) := hU2.continuousOn
  have hUxcont : ContinuousOn Ux (Icc (0 : ℝ) 1) := by
    dsimp [Ux]
    exact (deriv_lift_contDiffOn_one_Icc hU2
      (derivWithin_left_zero hsol ht0 htT u (Or.inl rfl))
      (derivWithin_right_zero hsol ht0 htT u (Or.inl rfl))).continuousOn
  have hUpos : ∀ y ∈ Icc (0 : ℝ) 1, 0 < U y := by
    intro y hy
    simpa [U] using solution_lift_pos_Icc hsol ht y hy
  have hUupper : ∀ y ∈ Icc (0 : ℝ) 1, U y ≤ uBar := by
    intro y hy
    simpa [U, intervalDomainLift, hy] using
      hupper (⟨y, hy⟩ : intervalDomainPoint)
  have hUxSqInt : IntervalIntegrable (fun y => Ux y ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le zero_le_one] using hUxcont.pow 2
  have hgcont : ContinuousOn g (Icc (0 : ℝ) 1) := by
    dsimp [g]
    exact (hUcont.rpow_const
      (fun y hy => Or.inl (ne_of_gt (hUpos y hy)))).mul (hUxcont.pow 2)
  have hgint : IntervalIntegrable g volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le zero_le_one] using hgcont
  have hcoeff : 0 ≤ uBar ^ (-2 : ℝ) :=
    Real.rpow_nonneg huBar.le _
  have hpoincare := intervalDomain_classicalSlice_poincare
    hsol ht0 htT hmass
  have hweight : ∀ y ∈ Icc (0 : ℝ) 1,
      uBar ^ (-2 : ℝ) * Ux y ^ 2 ≤ g y := by
    intro y hy
    have hpow : uBar ^ (-2 : ℝ) ≤ U y ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (hUpos y hy) (hUupper y hy) (by norm_num)
    exact mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
  have hG := intervalDomain_lpGradient_zero_eq_integral hsol ht0 htT
  calc
    uBar ^ (-2 : ℝ) *
          (∫ y in (0 : ℝ)..1, (U y - uStar) ^ 2) ≤
        uBar ^ (-2 : ℝ) *
          (∫ y in (0 : ℝ)..1, Ux y ^ 2) :=
      mul_le_mul_of_nonneg_left (by simpa [U, Ux] using hpoincare) hcoeff
    _ = ∫ y in (0 : ℝ)..1, uBar ^ (-2 : ℝ) * Ux y ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ y in (0 : ℝ)..1, g y := by
      exact intervalIntegral.integral_mono_on (by norm_num)
        (hUxSqInt.const_mul _) hgint hweight
    _ = intervalDomainLpWeightedGradientDissipation 0 u t := by
      simpa [g, U, Ux] using hG.symm

/-- The exact positive coefficient left in the Section 8.1 entropy estimate
after Poincare, the elliptic multiplier, and the power-difference bound. -/
def minimal1EntropyCoefficient
    (p : CM2Params) (uStar uBar vLower : ℝ) : ℝ :=
  uStar / 2 *
    (uBar ^ (-2 : ℝ) -
      p.χ₀ ^ 2 * p.ν ^ 2 * minimalPowerSlope p uStar uBar ^ 2 /
        (4 * p.μ * ((1 + vLower) ^ p.β) ^ 2))

/-- The third entry in `chiMinimal1Formula` makes the concrete entropy
coefficient strictly positive. -/
theorem minimal1EntropyCoefficient_pos_of_chi_lt
    (p : CM2Params) {uStar uBar vLower : ℝ}
    (huStar : 0 < uStar) (huBar : 0 < uBar) (hvLower : 0 ≤ vLower)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiMinimal1Formula p 1 uStar uBar vLower) :
    0 < minimal1EntropyCoefficient p uStar uBar vLower := by
  let S : ℝ := minimalPowerSlope p uStar uBar
  let B : ℝ := (1 + vLower) ^ p.β
  have hS : 0 < S := by
    simpa [S] using minimalPowerSlope_pos p huStar huBar
  have hbase : 0 < 1 + vLower := by linarith
  have hB : 0 < B := Real.rpow_pos_of_pos hbase _
  have hGamma : GammaMinimalFormula p.γ uStar uBar = S * uBar := by
    simpa [S] using GammaMinimalFormula_eq_slope_mul p huBar
  have hsqrt : 0 < Real.sqrt p.μ := Real.sqrt_pos.mpr p.hμ
  have hden : 0 < p.ν * (S * uBar) :=
    mul_pos p.hν (mul_pos hS huBar)
  have hthird :
      p.χ₀ < 2 * Real.sqrt p.μ * B / (p.ν * (S * uBar)) := by
    have := hχ.trans_le (min_le_right
      (min (chiBeta p / 2) (Real.sqrt (chiBeta p)))
      (2 * Real.sqrt (p.μ * 1) * (1 + vLower) ^ p.β /
        (p.ν * GammaMinimalFormula p.γ uStar uBar)))
    simpa [chiMinimal1Formula, B, hGamma] using this
  have hmul :
      p.χ₀ * (p.ν * (S * uBar)) < 2 * Real.sqrt p.μ * B :=
    (lt_div_iff₀ hden).mp hthird
  have hleft : 0 < p.χ₀ * (p.ν * (S * uBar)) :=
    mul_pos hχpos hden
  have hright : 0 < 2 * Real.sqrt p.μ * B :=
    mul_pos (mul_pos (by norm_num) hsqrt) hB
  have hsqrtSq : (Real.sqrt p.μ) ^ 2 = p.μ := Real.sq_sqrt p.hμ.le
  have hsq :
      p.χ₀ ^ 2 * p.ν ^ 2 * S ^ 2 * uBar ^ 2 <
        4 * p.μ * B ^ 2 := by
    have hsquare :
        (p.χ₀ * (p.ν * (S * uBar))) ^ 2 <
          (2 * Real.sqrt p.μ * B) ^ 2 := by
      nlinarith [sq_nonneg
        (2 * Real.sqrt p.μ * B - p.χ₀ * (p.ν * (S * uBar)))]
    nlinarith [hsqrtSq]
  have hD : 0 < 4 * p.μ * B ^ 2 :=
    mul_pos (mul_pos (by norm_num) p.hμ) (sq_pos_of_pos hB)
  have huSq : 0 < uBar ^ 2 := sq_pos_of_pos huBar
  have hquot :
      p.χ₀ ^ 2 * p.ν ^ 2 * S ^ 2 / (4 * p.μ * B ^ 2) <
        1 / uBar ^ 2 := by
    exact (div_lt_div_iff₀ hD huSq).2 (by simpa using hsq)
  have huNegTwo : uBar ^ (-2 : ℝ) = 1 / uBar ^ 2 := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
      Real.rpow_neg huBar.le, Real.rpow_two]
    rw [one_div]
  unfold minimal1EntropyCoefficient
  rw [huNegTwo]
  dsimp [S, B] at hquot ⊢
  exact mul_pos (div_pos huStar (by norm_num)) (sub_pos.mpr hquot)

/-- Concrete Section 8.1 entropy slope on every classical slice belonging to
the eventual upper/lower box and carrying the conserved physical mass. -/
theorem intervalDomain_entropySlope_le_minimal1Coefficient
    {p : CM2Params} {T t uStar vStar uBar vLower : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : p.m = 1) (hb0 : p.b = 0)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (huBar : 0 < uBar) (huStarBar : uStar ≤ uBar)
    (hmass : intervalDomain.integral (u t) = uStar)
    (hupper : ∀ x : intervalDomainPoint, u t x ≤ uBar)
    (hvLower : 0 ≤ vLower)
    (hVfloor : ∀ x : intervalDomainPoint, vLower ≤ v t x) :
    intervalDomain.integral (fun x =>
        (1 - uStar / u t x) * intervalDomain.timeDeriv u t x) ≤
      -minimal1EntropyCoefficient p uStar uBar vLower *
        (∫ y in (0 : ℝ)..1,
          (intervalDomainLift (u t) y - uStar) ^ 2) := by
  let hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one p hm hsol
  let L2 : ℝ := ∫ y in (0 : ℝ)..1,
    (intervalDomainLift (u t) y - uStar) ^ 2
  let G : ℝ := intervalDomainLpWeightedGradientDissipation 0 u t
  let W : ℝ := ∫ y in (0 : ℝ)..1,
    (deriv (intervalDomainLift (v t)) y) ^ 2 *
      (1 + intervalDomainLift (v t) y) ^ (-2 * p.β)
  let P : ℝ := ∫ y in (0 : ℝ)..1,
    (intervalDomainLift (u t) y ^ p.γ - uStar ^ p.γ) ^ 2
  let S : ℝ := minimalPowerSlope p uStar uBar
  have hid := intervalDomain_entropySlope_identity
    hm hsol ht0 htT heq
  have hyoung := intervalDomain_entropyDiffusionChemotaxis_half_young
    hm hsolM ht0 htT heq.u_pos
  have hgradient := intervalDomain_minimal_weightedGradient_ge_l2
    hsolM ht0 htT huBar hmass hupper
  have hell := intervalDomain_persistentWeightedElliptic_gradient_estimate
    hsolM ht0 htT heq hvLower hVfloor
  have hpower := intervalDomain_minimal_powerDifference_integral_le
    hsol ht0 htT heq.u_pos huStarBar hupper
  change uBar ^ (-2 : ℝ) * L2 ≤ G at hgradient
  change W ≤
    p.ν ^ 2 / (4 * p.μ * (1 + vLower) ^ (2 * p.β)) * P at hell
  change P ≤ S ^ 2 * L2 at hpower
  have hneg := mul_le_mul_of_nonpos_left hgradient
    (show -(uStar / 2) ≤ 0 by linarith [heq.u_pos])
  have hchemScale : 0 ≤ p.χ₀ ^ 2 * uStar / 2 :=
    div_nonneg (mul_nonneg (sq_nonneg _) heq.u_pos.le) (by norm_num)
  have hellScaled := mul_le_mul_of_nonneg_left hell hchemScale
  have hellCoeff : 0 ≤
      p.χ₀ ^ 2 * uStar / 2 *
        (p.ν ^ 2 / (4 * p.μ * (1 + vLower) ^ (2 * p.β))) := by
    have hden : 0 < 4 * p.μ * (1 + vLower) ^ (2 * p.β) :=
      mul_pos (mul_pos (by norm_num) p.hμ)
        (Real.rpow_pos_of_pos (by linarith : 0 < 1 + vLower) _)
    exact mul_nonneg hchemScale (div_nonneg (sq_nonneg _) hden.le)
  have hpowerScaled := mul_le_mul_of_nonneg_left hpower hellCoeff
  have hbase : 0 ≤ 1 + vLower := by linarith
  have hB2 :
      (1 + vLower) ^ (2 * p.β) = ((1 + vLower) ^ p.β) ^ 2 := by
    rw [← Real.rpow_mul_natCast hbase p.β 2]
    congr 1
    ring
  calc
    intervalDomain.integral (fun x =>
        (1 - uStar / u t x) * intervalDomain.timeDeriv u t x) =
        -uStar * G + p.χ₀ * uStar *
            ShenWork.Paper2.IntervalDomainM.lpSignedCrossIntegralM p 0 u v t -
          p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
      simpa [G] using hid
    _ ≤ -(uStar / 2) * G + p.χ₀ ^ 2 * uStar / 2 * W := by
      rw [hb0]
      simpa [G, W] using hyoung
    _ ≤ -(uStar / 2) * (uBar ^ (-2 : ℝ) * L2) +
          p.χ₀ ^ 2 * uStar / 2 * W := by
      have h := add_le_add_right hneg (p.χ₀ ^ 2 * uStar / 2 * W)
      simpa [add_comm] using h
    _ ≤ -(uStar / 2) * (uBar ^ (-2 : ℝ) * L2) +
          p.χ₀ ^ 2 * uStar / 2 *
            (p.ν ^ 2 /
              (4 * p.μ * (1 + vLower) ^ (2 * p.β)) * P) :=
      by
        have h := add_le_add_left hellScaled
          (-(uStar / 2) * (uBar ^ (-2 : ℝ) * L2))
        simpa [mul_assoc, add_comm] using h
    _ ≤ -(uStar / 2) * (uBar ^ (-2 : ℝ) * L2) +
          p.χ₀ ^ 2 * uStar / 2 *
            (p.ν ^ 2 /
              (4 * p.μ * (1 + vLower) ^ (2 * p.β)) *
                (S ^ 2 * L2)) := by
      have h := add_le_add_left hpowerScaled
        (-(uStar / 2) * (uBar ^ (-2 : ℝ) * L2))
      simpa [mul_assoc, add_comm] using h
    _ = -minimal1EntropyCoefficient p uStar uBar vLower * L2 := by
      rw [hB2]
      unfold minimal1EntropyCoefficient
      dsimp [S]
      ring

/-- Every bounded physical-mass orbit satisfying the concrete eventual box
has arbitrarily late slices with small squared `L²` distance to its mean. -/
theorem intervalDomain_minimal1_exists_late_l2_lt
    (p : CM2Params) (hm : p.m = 1) (hb0 : p.b = 0)
    {uStar vStar uBar vLower : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (huBar : 0 < uBar) (hvLower : 0 ≤ vLower)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiMinimal1Formula p 1 uStar uBar vLower)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
    (hupper : ∀ᶠ t : ℝ in atTop,
      intervalDomain.supNorm (u t) ≤ uBar)
    (hfloor : ∀ᶠ t : ℝ in atTop,
      ∀ x : intervalDomainPoint, vLower ≤ v t x)
    {T q : ℝ} (hq : 0 < q) :
    ∃ t, T ≤ t ∧
      (∫ y in (0 : ℝ)..1,
        (intervalDomainLift (u t) y - uStar) ^ 2) < q := by
  let c := minimal1EntropyCoefficient p uStar uBar vLower
  have hc : 0 < c := by
    simpa [c] using minimal1EntropyCoefficient_pos_of_chi_lt
      p heq.u_pos huBar hvLower hχpos hχ
  rcases eventually_atTop.1 hupper with ⟨Tu, hTu⟩
  rcases eventually_atTop.1 hfloor with ⟨Tv, hTv⟩
  let Tbase : ℝ := max (max Tu Tv) (max T 1)
  have hTbase : 0 < Tbase :=
    lt_of_lt_of_le zero_lt_one
      ((le_max_right T 1).trans (le_max_right (max Tu Tv) (max T 1)))
  have hTle : T ≤ Tbase :=
    (le_max_left T 1).trans (le_max_right (max Tu Tv) (max T 1))
  have hTuLe : Tu ≤ Tbase :=
    (le_max_left Tu Tv).trans (le_max_left (max Tu Tv) (max T 1))
  have hTvLe : Tv ≤ Tbase :=
    (le_max_right Tu Tv).trans (le_max_left (max Tu Tv) (max T 1))
  obtain ⟨t, htbase, htSmall⟩ :=
    exists_late_dissipation_lt_of_nonnegative_energy_on_Ici
      (E := fun s => chemotaxisEntropyFunctional intervalDomain 1 uStar u s)
      (D := fun s => ∫ y in (0 : ℝ)..1,
        (intervalDomainLift (u s) y - uStar) ^ 2)
      (slope := fun s => intervalDomain.integral (fun x =>
        (1 - uStar / u s x) * intervalDomain.timeDeriv u s x))
      hc hTbase hq
      (fun s hs =>
        intervalDomain_chemotaxisEntropyFunctional_nonneg_of_positiveGlobalBoundedSolution
          (by norm_num) heq.u_pos huv hs)
      (intervalDomain_strong1Entropy_hasDerivAt p heq huv)
      (fun s hs => by
        have hs0 : 0 < s := lt_of_lt_of_le hTbase hs
        have hH : 0 < s + 1 := by linarith
        have hsH : s < s + 1 := by linarith
        let hsol := huv.classical (s + 1) hH
        have hsup : intervalDomain.supNorm (u s) ≤ uBar :=
          hTu s (hTuLe.trans hs)
        have hVfloor : ∀ x : intervalDomainPoint, vLower ≤ v s x :=
          hTv s (hTvLe.trans hs)
        have hmassS : intervalDomain.integral (u s) = uStar := by
          simpa [intervalDomain] using hmass s hs0
        have huStarBar : uStar ≤ uBar := by
          have hmassSup := intervalDomain_classicalSolution_mass_le_supNorm
            hsol (⟨hs0, hsH⟩ : s ∈ Ioo (0 : ℝ) (s + 1))
          rw [hmassS] at hmassSup
          exact hmassSup.trans hsup
        have hpointUpper : ∀ x : intervalDomainPoint, u s x ≤ uBar := by
          intro x
          have hx :=
            IntervalChiNegH1PhysicalResolverSupProducer.intervalDomainLift_le_supNorm_of_classical
              hsol (⟨hs0, hsH⟩ : s ∈ Ioo (0 : ℝ) (s + 1)) x.property
          have hx' : u s x ≤ intervalDomain.supNorm (u s) := by
            simpa [intervalDomainLift, x.property] using hx
          exact hx'.trans hsup
        exact intervalDomain_entropySlope_le_minimal1Coefficient
          hm hb0 hsol hs0 hsH heq huBar huStarBar hmassS
            hpointUpper hvLower hVfloor)
  exact ⟨t, hTle.trans htbase, htSmall⟩

/-- The entropy slices from the first minimal formula branch enter every weak
supremum neighborhood at arbitrarily late positive times. -/
theorem intervalDomain_minimal1_exists_late_supClose
    (p : CM2Params) (hm : p.m = 1) (hb0 : p.b = 0)
    {uStar vStar uBar vLower : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (huBar : 0 < uBar) (hvLower : 0 ≤ vLower)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiMinimal1Formula p 1 uStar uBar vLower)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
    (hupper : ∀ᶠ t : ℝ in atTop,
      intervalDomain.supNorm (u t) ≤ uBar)
    (hfloor : ∀ᶠ t : ℝ in atTop,
      ∀ x : intervalDomainPoint, vLower ≤ v t x)
    {T eps : ℝ} (heps : 0 < eps) :
    ∃ t, T ≤ t ∧
      SupCloseToConstant intervalDomain (u t) uStar eps := by
  have hlate : ∀ {T q : ℝ}, 0 < q →
      ∃ t, T ≤ t ∧
        chemotaxisThetaDissipation intervalDomain uStar 1 (u t) < q := by
    intro T q hq
    obtain ⟨t, ht, hsmall⟩ := intervalDomain_minimal1_exists_late_l2_lt
      p hm hb0 heq huBar hvLower hχpos hχ huv hmass hupper hfloor hq
    refine ⟨t, ht, ?_⟩
    unfold chemotaxisThetaDissipation
    simp only [Real.rpow_one]
    change intervalDomainIntegral
      (fun x => (u t x - uStar) * (u t x - uStar)) < q
    unfold intervalDomainIntegral
    calc
      (∫ y in (0 : ℝ)..1,
          intervalDomainLift
            (fun x => (u t x - uStar) * (u t x - uStar)) y) =
          ∫ y in (0 : ℝ)..1,
            (intervalDomainLift (u t) y - uStar) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
        simp [intervalDomainLift, hy, pow_two]
      _ < q := hsmall
  exact intervalDomain_exists_late_supClose_of_thetaDissipation_slices
    p hm heq.u_pos (by norm_num) huv hlate heps

#print axioms intervalDomain_minimal_weightedGradient_ge_l2
#print axioms minimal1EntropyCoefficient_pos_of_chi_lt
#print axioms intervalDomain_entropySlope_le_minimal1Coefficient
#print axioms intervalDomain_minimal1_exists_late_l2_lt
#print axioms intervalDomain_minimal1_exists_late_supClose

end

end ShenWork.Paper3
