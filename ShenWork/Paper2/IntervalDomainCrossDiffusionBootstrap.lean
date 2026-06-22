import ShenWork.Paper2.IntervalDomainL2UEnergyCombine
import ShenWork.Paper2.IntervalDomainResolverSupQuantitative

open MeasureTheory intervalIntegral Filter
open ShenWork.IntervalDomain
open ShenWork.PDE ShenWork.IntervalEllipticCharacterization
open scoped Topology BigOperators

namespace ShenWork.Paper2

noncomputable section

/-- On the unit interval, a positive continuous function has monotone power
moments: lower moments are controlled by higher moments. -/
theorem unitInterval_power_moment_le
    {f : ℝ → ℝ} {a q : ℝ}
    (hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hfpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < f x)
    (ha : 0 < a) (haq : a < q) :
    ∫ x in (0 : ℝ)..1, f x ^ a ≤
      (∫ x in (0 : ℝ)..1, f x ^ q) ^ (a / q) := by
  classical
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hq : 0 < q := lt_trans ha haq
  set pH : ℝ := q / a with hpH_def
  set rH : ℝ := q / (q - a) with hrH_def
  have hpH_gt : 1 < pH := by
    rw [hpH_def, one_lt_div ha]
    exact haq
  have hpq : pH.HolderConjugate rH := by
    rw [Real.holderConjugate_iff]
    constructor
    · exact hpH_gt
    · rw [hpH_def, hrH_def]
      have hqa : 0 < q - a := sub_pos.mpr haq
      field_simp [ne_of_gt ha, ne_of_gt hq, ne_of_gt hqa]
      ring
  have hfa_cont : ContinuousOn (fun x => f x ^ a) (Set.Icc (0 : ℝ) 1) :=
    hfcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hfpos x hx)))
  have hfa_meas : AEStronglyMeasurable (fun x => f x ^ a) μ := by
    dsimp [μ]
    exact hfa_cont.aestronglyMeasurable_of_subset_isCompact isCompact_Icc measurableSet_Ioc
      (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  obtain ⟨Ca, hCa⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hfa_cont
  have hfa_bound : ∀ᵐ x ∂μ, ‖f x ^ a‖ ≤ Ca := by
    dsimp [μ]
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun x hx => hCa x ⟨le_of_lt hx.1, hx.2⟩
  have hfa_mem : MemLp (fun x => f x ^ a) (ENNReal.ofReal pH) μ :=
    MemLp.of_bound hfa_meas Ca hfa_bound
  have hone_mem : MemLp (fun _x : ℝ => (1 : ℝ)) (ENNReal.ofReal rH) μ := memLp_const 1
  have hfa_nn : 0 ≤ᵐ[μ] fun x => f x ^ a := by
    change ∀ᵐ x ∂μ, 0 ≤ f x ^ a
    dsimp [μ]
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun x hx =>
      Real.rpow_nonneg (hfpos x ⟨le_of_lt hx.1, hx.2⟩).le a
  have hone_nn : 0 ≤ᵐ[μ] fun _x : ℝ => (1 : ℝ) := by
    change ∀ᵐ _x ∂μ, 0 ≤ (1 : ℝ)
    exact Eventually.of_forall fun _ => zero_le_one
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
    hfa_nn hone_nn hfa_mem hone_mem
  have hleft_mul : (∫ x, f x ^ a * (1 : ℝ) ∂μ) = ∫ x, f x ^ a ∂μ := by
    simp
  have hpa : a * pH = q := by
    rw [hpH_def]
    field_simp [ne_of_gt ha]
  have hp_inv : 1 / pH = a / q := by
    rw [hpH_def]
    field_simp [ne_of_gt ha, ne_of_gt hq]
  have hfa_pow_eq : (∫ x, (f x ^ a) ^ pH ∂μ) = ∫ x, f x ^ q ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
    have hpow : f x ^ (a * pH) = (f x ^ a) ^ pH :=
      Real.rpow_mul (hfpos x ⟨le_of_lt hx.1, hx.2⟩).le a pH
    have hpowq : f x ^ (a * pH) = f x ^ q := by rw [hpa]
    exact hpow.symm.trans hpowq
  have hμuniv : μ Set.univ = 1 := by
    dsimp [μ]
    rw [Measure.restrict_apply_univ]
    simp [Real.volume_Ioc]
  have hμreal : μ.real Set.univ = 1 := by
    rw [Measure.real, hμuniv]
    norm_num
  have hone_pow_eq : (∫ x, ((1 : ℝ)) ^ rH ∂μ) = 1 := by
    rw [show (fun x : ℝ => (1 : ℝ) ^ rH) = fun _ => (1 : ℝ) by
      funext x
      simp]
    rw [MeasureTheory.integral_const]
    simp [hμreal]
  have hright :
      (∫ x, (f x ^ a) ^ pH ∂μ) ^ (1 / pH) *
        (∫ x, ((1 : ℝ)) ^ rH ∂μ) ^ (1 / rH) =
      (∫ x, f x ^ q ∂μ) ^ (a / q) := by
    rw [hfa_pow_eq, hone_pow_eq, hp_inv]
    simp
  rw [hleft_mul, hright] at hholder
  have hμa : (∫ x in (0 : ℝ)..1, f x ^ a) = ∫ x, f x ^ a ∂μ := by
    simp [μ, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  have hμq : (∫ x in (0 : ℝ)..1, f x ^ q) = ∫ x, f x ^ q ∂μ := by
    simp [μ, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  rwa [hμa, hμq]

/-- Product form of power-moment monotonicity on the unit interval. -/
theorem unitInterval_power_moment_mul_le
    {f : ℝ → ℝ} {a b : ℝ}
    (hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hfpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < f x)
    (ha : 0 < a) (hb : 0 < b) :
    (∫ x in (0 : ℝ)..1, f x ^ a) * (∫ x in (0 : ℝ)..1, f x ^ b) ≤
      ∫ x in (0 : ℝ)..1, f x ^ (a + b) := by
  set I : ℝ := ∫ x in (0 : ℝ)..1, f x ^ (a+b) with hI
  have hsum : 0 < a + b := add_pos ha hb
  have ha_lt : a < a + b := lt_add_of_pos_right a hb
  have hb_lt : b < a + b := lt_add_of_pos_left b ha
  have hA := unitInterval_power_moment_le hfcont hfpos ha ha_lt
  have hB := unitInterval_power_moment_le hfcont hfpos hb hb_lt
  have hA' : ∫ x in (0 : ℝ)..1, f x ^ a ≤ I ^ (a / (a+b)) := by
    simpa [hI] using hA
  have hB' : ∫ x in (0 : ℝ)..1, f x ^ b ≤ I ^ (b / (a+b)) := by
    simpa [hI] using hB
  have hB_nn : 0 ≤ ∫ x in (0 : ℝ)..1, f x ^ b :=
    intervalIntegral.integral_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
      (fun x hx => Real.rpow_nonneg (hfpos x hx).le b)
  have hI_nn : 0 ≤ I := by
    rw [hI]
    exact intervalIntegral.integral_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
      (fun x hx => Real.rpow_nonneg (hfpos x hx).le (a+b))
  have hIa_nn : 0 ≤ I ^ (a/(a+b)) := Real.rpow_nonneg hI_nn _
  have hmul := mul_le_mul hA' hB' hB_nn hIa_nn
  refine hmul.trans_eq ?_
  have ha_frac : 0 ≤ a / (a+b) := div_nonneg ha.le hsum.le
  have hb_frac : 0 ≤ b / (a+b) := div_nonneg hb.le hsum.le
  have habsum : a / (a+b) + b / (a+b) = 1 := by
    field_simp [ne_of_gt hsum]
  rw [← Real.rpow_add_of_nonneg hI_nn ha_frac hb_frac, habsum, Real.rpow_one]

/-- The elliptic source `L²` mass times a `p`-moment is absorbed by the
`p+2γ` moment. -/
theorem intervalDomain_sourceL2_mul_power_le
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t pExp : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) (hpExp : 1 < pExp) :
    (∫ x in (0 : ℝ)..1,
        ‖((p.ν * intervalDomainLift (u t) x ^ p.γ : ℝ) : ℂ)‖ ^ 2) *
      (∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ pExp) ≤
      p.ν ^ 2 *
        ∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ (pExp + 2 * p.γ) := by
  classical
  set lu : ℝ → ℝ := intervalDomainLift (u t) with hlu
  have hCu : ContDiffOn ℝ 2 lu (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hlu_cont : ContinuousOn lu (Set.Icc (0 : ℝ) 1) := hCu.continuousOn
  have hlu_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < lu x := by
    intro x hx
    rw [hlu]
    exact solution_lift_pos hsol ht x hx
  have h2γ_pos : 0 < 2 * p.γ := by nlinarith [p.hγ]
  have hpExp_pos : 0 < pExp := lt_trans zero_lt_one hpExp
  have hprod := unitInterval_power_moment_mul_le hlu_cont hlu_pos h2γ_pos hpExp_pos
  have hsrc_eq :
      (∫ x in (0 : ℝ)..1, ‖((p.ν * lu x ^ p.γ : ℝ) : ℂ)‖ ^ 2)
        = p.ν ^ 2 * ∫ x in (0 : ℝ)..1, lu x ^ (2 * p.γ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    change ‖((p.ν * lu x ^ p.γ : ℝ) : ℂ)‖ ^ 2 = p.ν ^ 2 * lu x ^ (2 * p.γ)
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hx
      exact hx
    have hpow : (lu x ^ p.γ) ^ 2 = lu x ^ (p.γ * (2 : ℝ)) := by
      simpa using (Real.rpow_mul_natCast (hlu_pos x hxIcc).le p.γ 2).symm
    rw [hpow]
    ring_nf
  rw [hlu, hsrc_eq]
  calc
    (p.ν ^ 2 * ∫ x in (0 : ℝ)..1, lu x ^ (2 * p.γ)) *
        (∫ x in (0 : ℝ)..1, lu x ^ pExp)
        = p.ν ^ 2 * ((∫ x in (0 : ℝ)..1, lu x ^ (2 * p.γ)) *
            (∫ x in (0 : ℝ)..1, lu x ^ pExp)) := by ring
    _ ≤ p.ν ^ 2 * ∫ x in (0 : ℝ)..1, lu x ^ ((2 * p.γ) + pExp) := by
        exact mul_le_mul_of_nonneg_left hprod (sq_nonneg p.ν)
    _ = p.ν ^ 2 * ∫ x in (0 : ℝ)..1, lu x ^ (pExp + 2 * p.γ) := by
        congr 1
        apply intervalIntegral.integral_congr
        intro x hx
        ring_nf

/-- Convert an interval-domain power integral to the raw lift integral. -/
theorem intervalDomain_integral_power_lift
    {f : intervalDomainPoint → ℝ} {a : ℝ} :
    intervalDomain.integral (fun x => f x ^ a) =
      ∫ y in (0 : ℝ)..1, intervalDomainLift f y ^ a := by
  change intervalDomainIntegral (fun x => f x ^ a) =
    ∫ y in (0 : ℝ)..1, intervalDomainLift f y ^ a
  rw [intervalDomainIntegral]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hy
  simp [intervalDomainLift, hy]

/-- Convert the abstract weighted-gradient integral to the raw lift expression. -/
theorem intervalDomain_weightedGradient_integral_lift
    {f : intervalDomainPoint → ℝ} {pExp : ℝ} :
    intervalDomain.integral
        (fun x => f x ^ (pExp - 2) * (intervalDomain.gradNorm f x) ^ 2) =
      ∫ y in (0 : ℝ)..1,
        intervalDomainLift f y ^ (pExp - 2) *
          |deriv (intervalDomainLift f) y| ^ 2 := by
  change intervalDomainIntegral
      (fun x => f x ^ (pExp - 2) * (intervalDomainGradNorm f x) ^ 2) =
    ∫ y in (0 : ℝ)..1,
      intervalDomainLift f y ^ (pExp - 2) *
        |deriv (intervalDomainLift f) y| ^ 2
  rw [intervalDomainIntegral]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hy
  simp [intervalDomainLift, intervalDomainGradNorm, hy]

/-- Pointwise weighted Young inequality used for the cross-diffusion term. -/
theorem crossDiffusion_pointwise_young
    {u ux bq G eps pExp : ℝ}
    (hu : 0 < u) (hbq : bq ≤ G) (heps : 0 < eps) :
    u ^ (pExp - 1) * |ux| * bq ≤
      eps * (u ^ (pExp - 2) * |ux| ^ 2) +
        (G ^ 2 / (4 * eps)) * u ^ pExp := by
  let A := u ^ ((pExp - 2) / 2) * |ux|
  let B := G * u ^ (pExp / 2)
  have hden : 0 < 4 * eps := by positivity
  have hyoung : A * B ≤ eps * A ^ 2 + B ^ 2 / (4 * eps) := by
    have hmul : (4 * eps) * (A * B) ≤
        (4 * eps) * (eps * A ^ 2 + B ^ 2 / (4 * eps)) := by
      field_simp [ne_of_gt hden]
      nlinarith [sq_nonneg (2 * eps * A - B)]
    exact le_of_mul_le_mul_left hmul hden
  have hbqG : u ^ (pExp - 1) * |ux| * bq ≤ u ^ (pExp - 1) * |ux| * G := by
    have hcoef : 0 ≤ u ^ (pExp - 1) * |ux| :=
      mul_nonneg (Real.rpow_nonneg hu.le _) (abs_nonneg _)
    exact mul_le_mul_of_nonneg_left hbq hcoef
  have hprod_eq :
      u ^ (pExp - 1) * |ux| * G = A * B := by
    dsimp [A, B]
    calc
      u ^ (pExp - 1) * |ux| * G
          = (u ^ (((pExp - 2) / 2) + (pExp / 2))) * |ux| * G := by ring_nf
      _ = (u ^ ((pExp - 2) / 2) * u ^ (pExp / 2)) * |ux| * G := by
          rw [Real.rpow_add hu]
      _ = (u ^ ((pExp - 2) / 2) * |ux|) * (G * u ^ (pExp / 2)) := by ring
  have hsquareA : A ^ 2 = u ^ (pExp - 2) * |ux| ^ 2 := by
    dsimp [A]
    rw [mul_pow, ← Real.rpow_mul_natCast hu.le ((pExp - 2) / 2) 2]
    ring_nf
  have hsquareB : B ^ 2 / (4 * eps) =
      (G ^ 2 / (4 * eps)) * u ^ pExp := by
    dsimp [B]
    rw [mul_pow, ← Real.rpow_mul_natCast hu.le (pExp / 2) 2]
    ring_nf
  calc
    u ^ (pExp - 1) * |ux| * bq ≤ u ^ (pExp - 1) * |ux| * G := hbqG
    _ = A * B := hprod_eq
    _ ≤ eps * A ^ 2 + B ^ 2 / (4 * eps) := hyoung
    _ = eps * (u ^ (pExp - 2) * |ux| ^ 2) +
          (G ^ 2 / (4 * eps)) * u ^ pExp := by rw [hsquareA, hsquareB]

/-- Pointwise Young inequality with the chemotactic denominator included. -/
theorem crossDiffusion_pointwise_young_div
    {u ux vx denom G eps pExp : ℝ}
    (hu : 0 < u) (hvx : |vx| ≤ G) (hden : 1 ≤ denom) (heps : 0 < eps) :
    u ^ (pExp - 1) * |ux| * |vx| / denom ≤
      eps * (u ^ (pExp - 2) * |ux| ^ 2) +
        (G ^ 2 / (4 * eps)) * u ^ pExp := by
  have hden_pos : 0 < denom := lt_of_lt_of_le zero_lt_one hden
  have hGnn : 0 ≤ G := le_trans (abs_nonneg vx) hvx
  have hGle : G ≤ G * denom := by
    calc
      G = G * 1 := by ring
      _ ≤ G * denom := mul_le_mul_of_nonneg_left hden hGnn
  have hbq : |vx| / denom ≤ G := by
    rw [div_le_iff₀ hden_pos]
    exact hvx.trans hGle
  have h := crossDiffusion_pointwise_young (u := u) (ux := ux)
    (bq := |vx| / denom) (G := G) (eps := eps) (pExp := pExp) hu hbq heps
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- Integral Young estimate for the cross-diffusion energy, with the elliptic
resolver gradient controlled by the actual source `L²` norm. -/
theorem intervalDomain_crossDiffusionEnergyTerm_young_sourceL2
    {p : CM2Params} {T t eps pExp : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) (heps : 0 < eps) :
    intervalDomain.crossDiffusionEnergyTerm p pExp (u t) (v t) ≤
      eps *
          intervalDomain.integral
            (fun x => (u t x) ^ (pExp - 2) *
              (intervalDomain.gradNorm (u t) x) ^ 2) +
        (((Real.sqrt
            (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)) *
              (2 * Real.sqrt
                (∫ y in (0 : ℝ)..1,
                  ‖((p.ν * intervalDomainLift (u t) y ^ p.γ : ℝ) : ℂ)‖ ^ 2))) ^ 2 /
            (4 * eps)) *
          intervalDomain.integral (fun x => (u t x) ^ pExp) := by
  classical
  set lu : ℝ → ℝ := intervalDomainLift (u t) with hlu
  set lv : ℝ → ℝ := intervalDomainLift (v t) with hlv
  set Ssrc : ℝ :=
    ∫ y in (0 : ℝ)..1,
      ‖((p.ν * intervalDomainLift (u t) y ^ p.γ : ℝ) : ℂ)‖ ^ 2 with hSsrc
  set G : ℝ :=
    Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
      (2 * Real.sqrt Ssrc) with hG
  set K : ℝ := G ^ 2 / (4 * eps) with hK
  set rhsCross : ℝ → ℝ := fun y =>
    lu y ^ (pExp - 1) * |deriv lu y| * |deriv lv y| /
      (1 + lv y) ^ p.β with hrhsCross
  set rhsGrad : ℝ → ℝ := fun y =>
    lu y ^ (pExp - 2) * |deriv lu y| ^ 2 with hrhsGrad
  set rhsPow : ℝ → ℝ := fun y => lu y ^ pExp with hrhsPow
  have hCu : ContDiffOn ℝ 2 lu (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hCv : ContDiffOn ℝ 2 lv (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hlu_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < lu x := by
    intro x hx
    rw [hlu]
    exact solution_lift_pos hsol ht x hx
  have hvnn : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ lv x := by
    intro x hx
    rw [hlv]
    exact solution_lift_v_nonneg_Icc hsol ht x hx
  have hbase_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + lv x := by
    intro x hx
    have := hvnn x hx
    linarith
  set rhsCrossCont : ℝ → ℝ := fun y =>
    lu y ^ (pExp - 1) *
      |derivWithin lu (Set.Icc (0 : ℝ) 1) y| *
        |derivWithin lv (Set.Icc (0 : ℝ) 1) y| /
      (1 + lv y) ^ p.β with hrhsCrossCont
  have hrhsCrossCont_cont : ContinuousOn rhsCrossCont (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    have hlu_pow_c : ContinuousOn (fun y => lu y ^ (pExp - 1))
        (Set.Icc (0 : ℝ) 1) :=
      hCu.continuousOn.rpow_const
        (fun y hy => Or.inl (ne_of_gt (hlu_pos y hy)))
    have hdwu_c :
        ContinuousOn (fun y => |derivWithin lu (Set.Icc (0 : ℝ) 1) y|)
          (Set.Icc (0 : ℝ) 1) :=
      (continuousOn_derivWithin_of_contDiffOn_two hCu).abs
    have hdwv_c :
        ContinuousOn (fun y => |derivWithin lv (Set.Icc (0 : ℝ) 1) y|)
          (Set.Icc (0 : ℝ) 1) :=
      (continuousOn_derivWithin_of_contDiffOn_two hCv).abs
    have hnum_c : ContinuousOn
        (fun y =>
          lu y ^ (pExp - 1) *
            |derivWithin lu (Set.Icc (0 : ℝ) 1) y| *
              |derivWithin lv (Set.Icc (0 : ℝ) 1) y|)
        (Set.Icc (0 : ℝ) 1) :=
      (hlu_pow_c.mul hdwu_c).mul hdwv_c
    have hden_c : ContinuousOn
        (fun y => (1 + lv y) ^ p.β) (Set.Icc (0 : ℝ) 1) := by
      apply ContinuousOn.rpow_const (contDiffOn_const.add hCv).continuousOn
      intro x hx
      exact Or.inl (ne_of_gt (hbase_pos x hx))
    have hden_ne : ∀ x ∈ Set.Icc (0 : ℝ) 1, (1 + lv x) ^ p.β ≠ 0 :=
      fun x hx => ne_of_gt (Real.rpow_pos_of_pos (hbase_pos x hx) _)
    exact hnum_c.div hden_c hden_ne
  have hrhsCross_int : IntervalIntegrable rhsCross volume 0 1 := by
    have hcontII : IntervalIntegrable rhsCrossCont volume 0 1 :=
      hrhsCrossCont_cont.intervalIntegrable
    refine hcontII.congr_ae ?_
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    have hnull : volume ({(1 : ℝ)} : Set ℝ) = 0 := by simp
    refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    push Not at hy
    obtain ⟨hyIoc, hne⟩ := hy
    simp only [Set.mem_singleton_iff]
    by_contra hy1
    have hyIoo : y ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨hyIoc.1, lt_of_le_of_ne hyIoc.2 hy1⟩
    apply hne
    have hdu_eq : derivWithin lu (Set.Icc (0 : ℝ) 1) y = deriv lu y :=
      (deriv_eq_derivWithin_interior hyIoo).symm
    have hdv_eq : derivWithin lv (Set.Icc (0 : ℝ) 1) y = deriv lv y :=
      (deriv_eq_derivWithin_interior hyIoo).symm
    simp only [hrhsCrossCont, hrhsCross, hdu_eq, hdv_eq]
  set rhsGradCont : ℝ → ℝ := fun y =>
    lu y ^ (pExp - 2) *
      |derivWithin lu (Set.Icc (0 : ℝ) 1) y| ^ 2 with hrhsGradCont
  have hrhsGradCont_cont : ContinuousOn rhsGradCont (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    have hlu_pow_c : ContinuousOn (fun y => lu y ^ (pExp - 2))
        (Set.Icc (0 : ℝ) 1) :=
      hCu.continuousOn.rpow_const
        (fun y hy => Or.inl (ne_of_gt (hlu_pos y hy)))
    have hdwu_c :
        ContinuousOn (fun y => |derivWithin lu (Set.Icc (0 : ℝ) 1) y|)
          (Set.Icc (0 : ℝ) 1) :=
      (continuousOn_derivWithin_of_contDiffOn_two hCu).abs
    exact hlu_pow_c.mul (hdwu_c.pow 2)
  have hrhsGrad_int : IntervalIntegrable rhsGrad volume 0 1 := by
    have hcontII : IntervalIntegrable rhsGradCont volume 0 1 :=
      hrhsGradCont_cont.intervalIntegrable
    refine hcontII.congr_ae ?_
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    have hnull : volume ({(1 : ℝ)} : Set ℝ) = 0 := by simp
    refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    push Not at hy
    obtain ⟨hyIoc, hne⟩ := hy
    simp only [Set.mem_singleton_iff]
    by_contra hy1
    have hyIoo : y ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨hyIoc.1, lt_of_le_of_ne hyIoc.2 hy1⟩
    apply hne
    have hdu_eq : derivWithin lu (Set.Icc (0 : ℝ) 1) y = deriv lu y :=
      (deriv_eq_derivWithin_interior hyIoo).symm
    simp only [hrhsGradCont, hrhsGrad, hdu_eq]
  have hrhsPow_cont : ContinuousOn rhsPow (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact hCu.continuousOn.rpow_const
      (fun y hy => Or.inl (ne_of_gt (hlu_pos y hy)))
  have hrhsPow_int : IntervalIntegrable rhsPow volume 0 1 :=
    hrhsPow_cont.intervalIntegrable
  have hright_int : IntervalIntegrable
      (fun y => eps * rhsGrad y + K * rhsPow y) volume 0 1 :=
    (hrhsGrad_int.const_mul eps).add (hrhsPow_int.const_mul K)
  have hptw : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      rhsCross y ≤ eps * rhsGrad y + K * rhsPow y := by
    intro y hy
    have hvx : |deriv lv y| ≤ G := by
      have hv_eq : deriv lv y = resolverGradReal p (u t) y := by
        rw [hlv]
        exact solution_lift_v_deriv_eq_resolverGrad_Icc hsol ht hy
      rw [hv_eq]
      simpa [G, Ssrc, hG, hSsrc] using resolverGrad_sup_le_sourceL2 hsol ht hy
    have hden : 1 ≤ (1 + lv y) ^ p.β := by
      have hbase : 1 ≤ 1 + lv y := by
        have := hvnn y hy
        linarith
      exact Real.one_le_rpow hbase p.hβ
    have hyoung := crossDiffusion_pointwise_young_div
      (u := lu y) (ux := deriv lu y) (vx := deriv lv y)
      (denom := (1 + lv y) ^ p.β) (G := G) (eps := eps) (pExp := pExp)
      (hlu_pos y hy) hvx hden heps
    simpa [rhsCross, rhsGrad, rhsPow, K, hrhsCross, hrhsGrad, hrhsPow, hK] using hyoung
  have hraw :
      (∫ y in (0 : ℝ)..1, rhsCross y) ≤
        eps * (∫ y in (0 : ℝ)..1, rhsGrad y) +
          K * (∫ y in (0 : ℝ)..1, rhsPow y) := by
    calc
      (∫ y in (0 : ℝ)..1, rhsCross y)
          ≤ ∫ y in (0 : ℝ)..1, eps * rhsGrad y + K * rhsPow y :=
        intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
          hrhsCross_int hright_int hptw
      _ = eps * (∫ y in (0 : ℝ)..1, rhsGrad y) +
            K * (∫ y in (0 : ℝ)..1, rhsPow y) := by
          rw [intervalIntegral.integral_add (hf := hrhsGrad_int.const_mul eps)
              (hg := hrhsPow_int.const_mul K),
            intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const_mul]
  have hcross_eq :
      intervalDomain.crossDiffusionEnergyTerm p pExp (u t) (v t) =
        ∫ y in (0 : ℝ)..1, rhsCross y := by
    change intervalDomainCrossDiffusionEnergyTerm p pExp (u t) (v t) =
      ∫ y in (0 : ℝ)..1, rhsCross y
    rw [intervalDomainCrossDiffusionEnergyTerm]
  have hgrad_eq :
      (∫ y in (0 : ℝ)..1, rhsGrad y) =
        intervalDomain.integral
          (fun x => (u t x) ^ (pExp - 2) *
            (intervalDomain.gradNorm (u t) x) ^ 2) := by
    rw [intervalDomain_weightedGradient_integral_lift]
  have hpow_eq :
      (∫ y in (0 : ℝ)..1, rhsPow y) =
        intervalDomain.integral (fun x => (u t x) ^ pExp) := by
    rw [intervalDomain_integral_power_lift]
  calc
    intervalDomain.crossDiffusionEnergyTerm p pExp (u t) (v t)
        = ∫ y in (0 : ℝ)..1, rhsCross y := hcross_eq
    _ ≤ eps * (∫ y in (0 : ℝ)..1, rhsGrad y) +
          K * (∫ y in (0 : ℝ)..1, rhsPow y) := hraw
    _ = eps *
          intervalDomain.integral
            (fun x => (u t x) ^ (pExp - 2) *
              (intervalDomain.gradNorm (u t) x) ^ 2) +
        (((Real.sqrt
            (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)) *
              (2 * Real.sqrt
                (∫ y in (0 : ℝ)..1,
                  ‖((p.ν * intervalDomainLift (u t) y ^ p.γ : ℝ) : ℂ)‖ ^ 2))) ^ 2 /
            (4 * eps)) *
          intervalDomain.integral (fun x => (u t x) ^ pExp) := by
        rw [hgrad_eq, hpow_eq, hK, hG, hSsrc]

/-- Cross-diffusion bootstrap estimate at a fixed time, after absorbing the
elliptic source `L²` factor into the `p+2γ` moment. -/
theorem intervalDomain_crossDiffusionEnergyTerm_bootstrap_bound
    {p : CM2Params} {T t eps pExp : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) (heps : 0 < eps) (hpExp : 1 < pExp) :
    intervalDomain.crossDiffusionEnergyTerm p pExp (u t) (v t) ≤
      eps *
          intervalDomain.integral
            (fun x => (u t x) ^ (pExp - 2) *
              (intervalDomain.gradNorm (u t) x) ^ 2) +
        (((∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) / eps) *
            p.ν ^ 2) *
          intervalDomain.integral (fun x => (u t x) ^ (pExp + 2 * p.γ)) := by
  classical
  set W2 : ℝ := ∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2 with hW2
  set Ssrc : ℝ :=
    ∫ y in (0 : ℝ)..1,
      ‖((p.ν * intervalDomainLift (u t) y ^ p.γ : ℝ) : ℂ)‖ ^ 2 with hSsrc
  set G : ℝ := Real.sqrt W2 * (2 * Real.sqrt Ssrc) with hG
  set Grad : ℝ :=
    intervalDomain.integral
      (fun x => (u t x) ^ (pExp - 2) *
        (intervalDomain.gradNorm (u t) x) ^ 2) with hGrad
  set Pmom : ℝ := intervalDomain.integral (fun x => (u t x) ^ pExp) with hPmom
  set Qmom : ℝ :=
    intervalDomain.integral (fun x => (u t x) ^ (pExp + 2 * p.γ)) with hQmom
  have hpre :
      intervalDomain.crossDiffusionEnergyTerm p pExp (u t) (v t) ≤
        eps * Grad + (G ^ 2 / (4 * eps)) * Pmom := by
    simpa [W2, Ssrc, G, Grad, Pmom, hW2, hSsrc, hG, hGrad, hPmom] using
      intervalDomain_crossDiffusionEnergyTerm_young_sourceL2
        (p := p) (T := T) (t := t) (eps := eps) (pExp := pExp)
        (u := u) (v := v) hsol ht heps
  set Praw : ℝ :=
    ∫ y in (0 : ℝ)..1, intervalDomainLift (u t) y ^ pExp with hPraw
  set Qraw : ℝ :=
    ∫ y in (0 : ℝ)..1,
      intervalDomainLift (u t) y ^ (pExp + 2 * p.γ) with hQraw
  have hPmom_raw : Pmom = Praw := by
    rw [hPmom, hPraw, intervalDomain_integral_power_lift]
  have hQmom_raw : Qmom = Qraw := by
    rw [hQmom, hQraw, intervalDomain_integral_power_lift]
  have hprod : Ssrc * Praw ≤ p.ν ^ 2 * Qraw := by
    simpa [Ssrc, Praw, Qraw, hSsrc, hPraw, hQraw] using
      intervalDomain_sourceL2_mul_power_le
        (p := p) (T := T) (u := u) (v := v) hsol ht hpExp
  have hcoef :
      (G ^ 2 / (4 * eps)) * Pmom ≤
        ((W2 / eps) * p.ν ^ 2) * Qmom := by
    rw [hPmom_raw, hQmom_raw]
    have hW2nn : 0 ≤ W2 := by
      rw [hW2]
      exact tsum_nonneg (fun k => sq_nonneg _)
    have hSnn : 0 ≤ Ssrc := by
      rw [hSsrc]
      exact intervalIntegral.integral_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
        (fun y hy => sq_nonneg _)
    have hcoef_nn : 0 ≤ W2 / eps := div_nonneg hW2nn heps.le
    calc
      (G ^ 2 / (4 * eps)) * Praw = (W2 / eps) * (Ssrc * Praw) := by
        rw [hG, mul_pow, mul_pow, Real.sq_sqrt hW2nn, Real.sq_sqrt hSnn]
        field_simp [ne_of_gt heps]
        ring
      _ ≤ (W2 / eps) * (p.ν ^ 2 * Qraw) :=
        mul_le_mul_of_nonneg_left hprod hcoef_nn
      _ = ((W2 / eps) * p.ν ^ 2) * Qraw := by ring
  calc
    intervalDomain.crossDiffusionEnergyTerm p pExp (u t) (v t)
        ≤ eps * Grad + (G ^ 2 / (4 * eps)) * Pmom := hpre
    _ ≤ eps * Grad + ((W2 / eps) * p.ν ^ 2) * Qmom :=
        by simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hcoef (eps * Grad)
    _ = eps *
          intervalDomain.integral
            (fun x => (u t x) ^ (pExp - 2) *
              (intervalDomain.gradNorm (u t) x) ^ 2) +
        (((∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) / eps) *
            p.ν ^ 2) *
          intervalDomain.integral (fun x => (u t x) ^ (pExp + 2 * p.γ)) := by
        rw [hGrad, hQmom, hW2]

/-- Classical interval solutions satisfy the abstract cross-diffusion bootstrap
with exponent `rho = 2γ`. -/
theorem intervalDomain_crossDiffusionBootstrapEstimate_of_classical
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v) :
    CrossDiffusionBootstrapEstimate intervalDomain p T (2 * p.γ) u v := by
  intro eps heps pExp hpExp
  refine ⟨((∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) / eps) *
    p.ν ^ 2, ?_⟩
  intro t ht0 htT
  simpa [add_comm, add_left_comm, add_assoc] using
    intervalDomain_crossDiffusionEnergyTerm_bootstrap_bound
      (p := p) (T := T) (t := t) (eps := eps) (pExp := pExp)
      (u := u) (v := v) hsol ⟨ht0, htT⟩ heps hpExp

end

end ShenWork.Paper2
