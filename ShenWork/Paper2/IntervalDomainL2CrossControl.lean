/-
# Chemotaxis cross-diffusion control (`hCrossControl`) — discharged

This file closes the `hCrossControl` frontier of the L² energy differential
inequality for a classical solution.  Concretely it proves, **unconditionally for
any `IsPaper2ClassicalSolution` at an interior time**, the cross-term bound

  `-χ₀ · ∫₀¹ u·chemDiv(u,v)  ≤  |χ₀| · ∫₀¹ u·|∂ₓu|·|∂ₓv|/(1+v)^β`,

i.e. `-χ₀ · intervalDomainL2ChemotaxisIntegral ≤ |χ₀| · crossDiffusionEnergyTerm 2`.

## Mathematical content

The chemotaxis integral is, by definition, `∫₀¹ u·∂ₓ(flux)` with the flux
`flux = u·∂ₓv/(1+v)^β` (`intervalFlux`).  Integration by parts on the open
interior (`intervalFluxByParts_open`), with the flux vanishing at both endpoints
(`flux_endpoint_zero`, the genuine `v`-Neumann data), moves the derivative:

  `∫₀¹ u·∂ₓ(flux) = - ∫₀¹ ∂ₓu·flux = - ∫₀¹ ∂ₓu·u·∂ₓv/(1+v)^β`.

Hence `-χ₀·(chemotaxis integral) = ∫₀¹ χ₀·∂ₓu·u·∂ₓv/(1+v)^β`, and pointwise

  `χ₀·∂ₓu·u·∂ₓv/(1+v)^β ≤ |χ₀|·u·|∂ₓu|·|∂ₓv|/(1+v)^β`

because `u ≥ 0`, `(1+v)^β > 0`, and `χ₀·a·b ≤ |χ₀|·|a|·|b|` (`le_abs_self`).
Integral monotonicity (`integral_mono_on`) delivers the claim; the right-hand
integrand is interval-integrable because it agrees a.e. with the continuous
`derivWithin` representative.

No `sorry`/`admit`/custom `axiom`.
-/

import ShenWork.Paper2.IntervalDomainL2HalfEnergyTimeLeibniz
import ShenWork.Paper2.IntervalDomainL2UEnergyCombine

open MeasureTheory
open scoped Topology

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
open ShenWork.PDE ShenWork.IntervalEllipticCharacterization
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpMonotonicity

/-- **Chemotaxis cross-diffusion control, unconditional from regularity.**
For any classical solution at an interior time `t ∈ (0,T)`,

  `-χ₀ · intervalDomainL2ChemotaxisIntegral ≤ |χ₀| · crossDiffusionEnergyTerm 2`.

This discharges the `hCrossControl` hypothesis of the L² energy inequality with
`chiBound := |χ₀|`. -/
theorem intervalDomain_l2_crossControl_of_regularity
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    -params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t ≤
      |params.χ₀| *
        intervalDomain.crossDiffusionEnergyTerm params 2 (u t) (v t) := by
  classical
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  -- Abbreviations for the lifts and the flux.
  set lu : ℝ → ℝ := intervalDomainLift (u t) with hlu
  set lv : ℝ → ℝ := intervalDomainLift (v t) with hlv
  set F : ℝ → ℝ := intervalFlux params (u t) (v t) with hFdef
  -- conjunct (7): closed-`[0,1]` `C²` of the `u`- and `v`-lifts.
  have hCu : ContDiffOn ℝ 2 lu (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.2.2.1 t ht).1.1
  have hCv : ContDiffOn ℝ 2 lv (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.2.2.1 t ht).2.1
  -- conjunct (3): interior `C²`.
  have hCuI : ContDiffOn ℝ 2 lu (Set.Ioo (0 : ℝ) 1) := (hsol.regularity.2.2.1 t ht).1
  -- ## Step 1.  The IBP identity for the chemotaxis integral.
  -- continuity on the closed interval.
  have hlu_cont : ContinuousOn lu (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hCu.continuousOn
  have hF_cont : ContinuousOn F (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (flux_contDiffOn_Icc hsol ht).continuousOn
  -- interior derivatives.
  have hφ : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt lu (deriv lu x) x := by
    intro x hx
    exact ((hCuI.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hFderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F (deriv F x) x := by
    intro x hx
    exact (((flux_contDiffOn_Ioo_of_solution hsol ht).differentiableOn
      (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  -- integrability of the two derivatives.
  have hdu_int : IntervalIntegrable (deriv lu) volume 0 1 :=
    intervalIntegrable_deriv_of_contDiffOn_two hCu
  have hdF_int : IntervalIntegrable (deriv F) volume 0 1 :=
    solution_deriv_flux_intervalIntegrable hsol ht
  -- endpoint vanishing of the flux.
  obtain ⟨hbc0, hbc1⟩ := flux_endpoint_zero hsol ht
  -- the IBP.
  have hIBP : (∫ y in (0:ℝ)..1, lu y * deriv F y)
      = - ∫ y in (0:ℝ)..1, deriv lu y * F y :=
    intervalFluxByParts_open hlu_cont hF_cont hφ hFderiv hdu_int hdF_int hbc0 hbc1
  -- chemotaxis integral equals `∫ lu·deriv F`.
  have hchem_eq : intervalDomainL2ChemotaxisIntegral params u v t
      = ∫ y in (0:ℝ)..1, lu y * deriv F y := by
    rw [intervalDomainL2ChemotaxisIntegral]
    show intervalDomainIntegral
      (fun x => u t x * intervalDomain.chemotaxisDiv params (u t) (v t) x) = _
    rw [intervalDomainIntegral]
    refine intervalIntegral.integral_congr ?_
    intro y hy
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hy
    rw [intervalDomainLift_mul]
    have hchem : intervalDomainLift
        (intervalDomain.chemotaxisDiv params (u t) (v t)) y = deriv F y := by
      simp only [intervalDomainLift, hy, dif_pos]
      rw [hFdef]; rfl
    rw [hchem]
  -- ## Step 2.  Right-hand integrand integrability via a continuous representative.
  set rhsCross : ℝ → ℝ := fun y =>
    lu y * |deriv lu y| * |deriv lv y| / (1 + lv y) ^ params.β with hrhsCross
  -- continuous representative using closed-`Icc` `derivWithin`.
  set rhsCont : ℝ → ℝ := fun y =>
    lu y * |derivWithin lu (Set.Icc (0:ℝ) 1) y| * |derivWithin lv (Set.Icc (0:ℝ) 1) y|
      / (1 + lv y) ^ params.β with hrhsCont
  have hvnn : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ lv x := solution_lift_v_nonneg_Icc hsol ht
  have hbase_pos : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < 1 + lv x := by
    intro x hx; have := hvnn x hx; linarith
  -- continuity of `rhsCont` on `uIcc`.
  have hrhsCont_cont : ContinuousOn rhsCont (Set.uIcc (0:ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    have hlu_c : ContinuousOn lu (Set.Icc (0:ℝ) 1) := hCu.continuousOn
    have hdwu_c : ContinuousOn (fun y => |derivWithin lu (Set.Icc (0:ℝ) 1) y|)
        (Set.Icc (0:ℝ) 1) :=
      (continuousOn_derivWithin_of_contDiffOn_two hCu).abs
    have hdwv_c : ContinuousOn (fun y => |derivWithin lv (Set.Icc (0:ℝ) 1) y|)
        (Set.Icc (0:ℝ) 1) :=
      (continuousOn_derivWithin_of_contDiffOn_two hCv).abs
    have hnum_c : ContinuousOn
        (fun y => lu y * |derivWithin lu (Set.Icc (0:ℝ) 1) y|
          * |derivWithin lv (Set.Icc (0:ℝ) 1) y|) (Set.Icc (0:ℝ) 1) :=
      (hlu_c.mul hdwu_c).mul hdwv_c
    have hden_c : ContinuousOn (fun y => (1 + lv y) ^ params.β) (Set.Icc (0:ℝ) 1) := by
      apply ContinuousOn.rpow_const (contDiffOn_const.add hCv).continuousOn
      intro x hx; exact Or.inl (ne_of_gt (hbase_pos x hx))
    have hden_ne : ∀ x ∈ Set.Icc (0:ℝ) 1, (1 + lv x) ^ params.β ≠ 0 :=
      fun x hx => ne_of_gt (Real.rpow_pos_of_pos (hbase_pos x hx) _)
    exact hnum_c.div hden_c hden_ne
  -- `rhsCross =ᵃᵉ rhsCont` on `Ioc` (they differ only where `deriv ≠ derivWithin`,
  -- i.e. at the endpoint `1`).
  have hrhsCross_int : IntervalIntegrable rhsCross volume 0 1 := by
    have hcontII : IntervalIntegrable rhsCont volume 0 1 := hrhsCont_cont.intervalIntegrable
    refine hcontII.congr_ae ?_
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    have hnull : volume ({(1:ℝ)} : Set ℝ) = 0 := by simp
    refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    push_neg at hy
    obtain ⟨hyIoc, hne⟩ := hy
    simp only [Set.mem_singleton_iff]
    by_contra hy1
    have hyIoo : y ∈ Set.Ioo (0:ℝ) 1 := ⟨hyIoc.1, lt_of_le_of_ne hyIoc.2 hy1⟩
    apply hne
    -- `rhsCont y = rhsCross y` since `deriv = derivWithin` on the interior.
    have hdu_eq : derivWithin lu (Set.Icc (0:ℝ) 1) y = deriv lu y :=
      (deriv_eq_derivWithin_interior hyIoo).symm
    have hdv_eq : derivWithin lv (Set.Icc (0:ℝ) 1) y = deriv lv y :=
      (deriv_eq_derivWithin_interior hyIoo).symm
    simp only [hrhsCont, hrhsCross, hdu_eq, hdv_eq]
  -- ## Step 3.  The LHS integrand `χ₀·(deriv lu · F)` is interval-integrable.
  have hlhs_int : IntervalIntegrable
      (fun y => params.χ₀ * (deriv lu y * F y)) volume 0 1 :=
    (hdu_int.mul_continuousOn hF_cont).const_mul params.χ₀
  -- `|χ₀|·rhsCross` is interval-integrable.
  have hrhs_int : IntervalIntegrable
      (fun y => |params.χ₀| * rhsCross y) volume 0 1 :=
    hrhsCross_int.const_mul _
  -- ## Step 4.  Pointwise bound on `[0,1]`.
  have hptw : ∀ y ∈ Set.Icc (0:ℝ) 1,
      params.χ₀ * (deriv lu y * F y) ≤ |params.χ₀| * rhsCross y := by
    intro y hy
    -- `lu y ≥ 0` (strict positivity of `u`).
    have hluy : 0 ≤ lu y := by
      have : lu y = u t ⟨y, hy⟩ := by simp [hlu, intervalDomainLift, hy]
      rw [this]; exact (hsol.u_pos' ht0 htT).le
    have hDpos : 0 < (1 + lv y) ^ params.β := Real.rpow_pos_of_pos (hbase_pos y hy) _
    -- common nonneg factor `c = lu y / (1+lv y)^β`.
    have hc : 0 ≤ lu y / (1 + lv y) ^ params.β := div_nonneg hluy hDpos.le
    -- the scalar abs inequality.
    have habs : params.χ₀ * deriv lu y * deriv lv y
        ≤ |params.χ₀| * |deriv lu y| * |deriv lv y| := by
      have h := le_abs_self (params.χ₀ * deriv lu y * deriv lv y)
      rwa [abs_mul, abs_mul] at h
    -- factor both sides as `c · (…)`.
    have hL : params.χ₀ * (deriv lu y * F y)
        = (lu y / (1 + lv y) ^ params.β)
          * (params.χ₀ * deriv lu y * deriv lv y) := by
      rw [hFdef]; simp only [intervalFlux]; ring
    have hR : |params.χ₀| * rhsCross y
        = (lu y / (1 + lv y) ^ params.β)
          * (|params.χ₀| * |deriv lu y| * |deriv lv y|) := by
      simp only [hrhsCross]; ring
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_left habs hc
  -- ## Step 5.  Assemble via integral monotonicity.
  calc -params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t
      = ∫ y in (0:ℝ)..1, params.χ₀ * (deriv lu y * F y) := by
        rw [hchem_eq, hIBP, intervalIntegral.integral_const_mul]; ring
    _ ≤ ∫ y in (0:ℝ)..1, |params.χ₀| * rhsCross y :=
        intervalIntegral.integral_mono_on (by norm_num) hlhs_int hrhs_int hptw
    _ = |params.χ₀| * intervalDomain.crossDiffusionEnergyTerm params 2 (u t) (v t) := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        show (∫ y in (0:ℝ)..1, rhsCross y)
          = intervalDomainCrossDiffusionEnergyTerm params 2 (u t) (v t)
        rw [intervalDomainCrossDiffusionEnergyTerm]
        refine intervalIntegral.integral_congr ?_
        intro y _
        simp only [hrhsCross, hlu, hlv]
        rw [show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one]

/-- **Full-solution L² energy inequality — both remaining gates discharged but
`hrepIoo`.**  Strengthens `…_of_cosineProfile_full` by also discharging the
cross-diffusion control `hCrossControl` via
`intervalDomain_l2_crossControl_of_regularity` (T5-s), with `chiBound := |χ₀|`.
The **only** remaining input is the OPEN-`(0,1)` cosine representation `hrepIoo`
(`DuhamelHeatValueRepresentation` body, the Fubini/parabolic-gain step).  Every
other hypothesis of the energy differential inequality is now a theorem about an
arbitrary classical solution. -/
theorem intervalDomain_l2_half_energy_inequality_of_cosineProfile_full_final
    {params : CM2Params} {T rho eps t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (heps : 0 < eps)
    (ht0 : 0 < t) (htT : t < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    {τ : ℝ} (hτ : 0 < τ) {b : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |b n| ≤ M)
    (hrepIoo : Set.EqOn (intervalDomainLift (u t))
      (fun x => unitIntervalCosineHeatValue τ b x) (Set.Ioo (0 : ℝ) 1)) :
    ∃ Ceps,
      deriv (fun τ' => intervalDomainL2HalfEnergy u τ') t +
          intervalDomainL2DiffusionDissipation u t ≤
        |params.χ₀| *
            (eps * intervalDomainLpWeightedGradientDissipation 2 u t +
              Ceps *
                intervalDomain.integral (fun x => (u t x) ^ (2 + rho))) +
          intervalDomainL2LogisticIntegral params u t :=
  intervalDomain_l2_half_energy_inequality_of_cosineProfile_full
    heps (abs_nonneg _) ht0 htT hsol hcross hτ hM hrepIoo
    (intervalDomain_l2_crossControl_of_regularity hsol ht0 htT)

end ShenWork.Paper2
