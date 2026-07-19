import ShenWork.Paper1.WavePositivePlateauTrapHeight
import ShenWork.Paper1.WholeLineWeightedRegularityLateH1WindowNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalScaledTrapNatural
import ShenWork.Paper1.WholeLineWeightedRegularityScaledTrapWindowNatural
import ShenWork.Paper1.WholeLineWeightedRegularityWeightedConvergenceChiPosNatural

open Filter Function MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# A late positive-sensitivity plateau window

The positive ceiling is only attained with slack.  We therefore choose a
height `Q = MChi p + r` inside the open operator budget
`p.χ * Q ^ p.γ < 1`.  Weighted convergence and a uniform late `H¹` bound then
put every sufficiently late canonical closed window in the *scaled* trap
`InTimeWaveTrapSet (kappa c) Q`.  This is the predicate actually available at
finite time; for `Q > 1` its slices need not belong to the unscaled
`InWaveTrapSet (kappa c) Q`.
-/

/-- A sign-free form of the uniform late `H¹` window producer.  The sign in
the older wrapper is used only to manufacture the ceiling regime and the
inclusion `MChi p ≤ wholeLineCauchyGlobalClamp p u₀`; both are explicit here. -/
theorem exists_eventual_common_weighted_H1_restart_window_of_ceiling
    (p : CMParams) (hceiling : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hMChi : MChi p ≤ wholeLineCauchyGlobalClamp p u₀)
    {Blog eta c D E Kflux FD B : ℝ}
    (hBlog : 0 ≤ Blog) (heta : 0 < eta) (heta_one : eta < 1)
    {Uw Vw : ℝ → ℝ}
    (hTW : IsTravelingWave p c Uw Vw)
    (hbound : HasWaveUpperTailBound p c Uw)
    (hreg : TravelingWaveRegularity p c Uw Vw)
    (hlog : ∀ y, |deriv Uw y / Uw y| ≤ Blog)
    (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hB : 0 ≤ B)
    (hUd : ∀ y, |deriv Uw y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv Uw) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv Uw)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p Uw Vw y| ≤ Kflux)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p Uw Vw) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p Uw Vw)
      (deriv (wholeLineTravelingWaveFlux p Uw Vw) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p Uw Vw)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p Uw y| ≤ B)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p Uw))
    (hgrad_int : ∀ q, 0 < q → ∀ x, IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p Uw Vw) x) volume 0 q)
    (hconv : CoMovingWeightedL2Convergence eta c
      (wholeLineCauchyGlobalU p u₀) Uw) :
    ∃ N : ℕ, ∃ F G : ℝ, 0 ≤ F ∧ 0 ≤ G ∧
      ∀ n : ℕ, N ≤ n →
        let datum := wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c n
        let Traj := wholeLineCauchyBUCMildFixedPoint p
          (wholeLineCauchyGlobalClamp_pos p u₀).le
          (wholeLineCauchyGlobalSegmentTime_pos p u₀).le datum
          (wholeLineCauchyGlobalSegmentTime_rate p u₀)
        let u : ℝ → ℝ → ℝ := fun s x =>
          (wholeLineBUCTrajectoryExtend
            (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj s).1 x
        (∀ s ∈ Set.Icc (0 : ℝ) (wholeLineCauchyGlobalSegmentTime p u₀),
          Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
            |u s (x + c * s) - Uw x| ^ 2) ∧
          (∫ x : ℝ, Real.exp (2 * eta * x) *
            |u s (x + c * s) - Uw x| ^ 2) ≤ F ^ 2) ∧
        (∀ s ∈ Set.Icc (wholeLineCauchyGlobalStep p u₀)
            (wholeLineCauchyGlobalSegmentTime p u₀),
          Integrable (fun x : ℝ =>
            paper5WeightedPopulationX eta (coMovingPath c u) Uw s x ^ 2) ∧
          (∫ x : ℝ,
            paper5WeightedPopulationX eta (coMovingPath c u) Uw s x ^ 2) ≤
              G ^ 2) := by
  let M := wholeLineCauchyGlobalClamp p u₀
  let T := wholeLineCauchyGlobalSegmentTime p u₀
  let a := wholeLineCauchyGlobalStep p u₀
  have hM : 0 ≤ M := by
    simpa only [M] using (wholeLineCauchyGlobalClamp_pos p u₀).le
  have hT : 0 ≤ T := by
    simpa only [T] using (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
  have ha : 0 < a := by
    simpa only [a] using wholeLineCauchyGlobalStep_pos p u₀
  have hevent := eventually_translatedDatumIndex_fullWeightedL2_le_one
    p hceiling u₀ hu₀ hconv
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  let ι := {n : ℕ // N ≤ n}
  let datum : ι → WholeLineBUC := fun n =>
    wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c n.1
  have hdata_full : ∀ i : ι, Integrable (fun y : ℝ =>
      Real.exp (2 * eta * y) * |(datum i).1 y - Uw y| ^ 2) := by
    intro i
    exact (hN i.1 i.2).1
  have hdata_energy : ∀ i : ι, (∫ y : ℝ,
      Real.exp (2 * eta * y) * |(datum i).1 y - Uw y| ^ 2) ≤ (1 : ℝ) ^ 2 := by
    intro i
    simpa only [one_pow] using (hN i.1 i.2).2
  have hstrip : ∀ i : ι, ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT (datum i)
        (wholeLineCauchyGlobalSegmentTime_rate p u₀) z).1 x ∈
        Set.Icc (0 : ℝ) M := by
    intro i z x
    let d : ℝ := c * ((i.1 : ℝ) * a)
    have htranslate : datum i = wholeLineBUCTranslate d
        (wholeLineCauchyGlobalDatum p u₀ i.1) := by
      rfl
    have hfp := wholeLineCauchyBUCMildFixedPoint_spatialTranslate
      (d := d) p hM hT (wholeLineCauchyGlobalDatum p u₀ i.1)
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
    have heq : wholeLineCauchyBUCMildFixedPoint p hM hT (datum i)
        (wholeLineCauchyGlobalSegmentTime_rate p u₀) =
      wholeLineBUCTrajectorySpatialTranslate hT d
        (wholeLineCauchyGlobalSegment p u₀ i.1) := by
      rw [htranslate]
      simpa only [wholeLineCauchyGlobalSegment, M, T] using hfp
    rw [heq]
    simpa only [wholeLineBUCTrajectorySpatialTranslate_apply, M, T] using
      (wholeLineCauchyGlobalDatum_segment_bounds
        p hceiling u₀ hu₀ i.1).2.1 z (x + d)
  obtain ⟨F, hF, hfull⟩ :=
    exists_common_fullWeighted_mildFixedPoint_wave_value_inputs_family
      (M := M) (T := T) (eta := eta) (c := c) (B₀ := 1)
      (D := D) (E := E) (Kflux := Kflux) (FD := FD) (B := B)
      p hT heta heta_one (by norm_num) datum
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
        hTW hbound hreg (by simpa only [M] using hMChi) hD hFD hB hUd hUdd
        hUddcont hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont
        hgrad_int hdata_full hdata_energy
  obtain ⟨G, hG, hgrad⟩ :=
    exists_common_uniform_window_weightedPopulationX_data_mildFixedPoint_wave_family
      (M := M) (T := T) (a := a) (b := T) (Blog := Blog)
      (eta := eta) (c := c) (F := F)
      (D := D) (E := E) (Kflux := Kflux) (FD := FD) (B := B)
      p hM hT ha le_rfl hBlog heta heta_one hF datum
        (wholeLineCauchyGlobalSegmentTime_rate p u₀) hstrip
        hTW hbound hreg (by simpa only [M] using hMChi) hlog hD hFD hB hUd
        hUdd hUddcont hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont
        hgrad_int hfull
  refine ⟨N, F, G, hF, hG, ?_⟩
  intro n hn
  let i : ι := ⟨n, hn⟩
  have hfull_i := hfull i
  have hgrad_i := hgrad i
  simpa only [datum, i, M, T, a] using And.intro hfull_i hgrad_i

/-- At a sufficiently late canonical seam, every following closed restart
window belongs to the scaled trap of height `Q = MChi p + r`, with `r > 0`
chosen inside the sharp positive constant-plateau budget. -/
theorem wholeLineCauchyGlobal_exists_chiPos_plateau_window
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : 0 < p.χ) (hchi_half : p.χ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1)
    {c eta : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hroot : paper531RootMinus c
      (paper531ConcreteStabilityBudget p hregime).A
      (paper531ConcreteStabilityBudget p hregime).B < eta)
    (hetaCap : eta < stabilityWeightCap p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U) :
    ∃ r : ℝ, 0 < r ∧
      let Q := MChi p + r
      MChi p < Q ∧ 1 < Q ∧ p.χ * Q ^ p.γ < 1 ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        InTimeWaveTrapSet (kappa c) Q
          (wholeLineCauchyGlobalStep p u₀)
          (fun s x => wholeLineCauchyGlobalU p u₀
            (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + s)
            (x + c * (((n : ℝ) + 1) *
              wholeLineCauchyGlobalStep p u₀ + s))) := by
  have hchi_one : p.χ < 1 := by linarith
  have hceiling : WholeLineCauchyCeilingRegime p :=
    hregime.toWholeLineCauchyCeilingRegime
  have hbranch := hregime.positive_branch_of_chi_nonneg hchi.le
  have hMChiClamp : MChi p ≤ wholeLineCauchyGlobalClamp p u₀ := by
    have hparam : wholeLineCauchyParameterCeiling p = MChi p := by
      unfold wholeLineCauchyParameterCeiling
      rw [if_neg (not_lt.mpr (le_of_eq hbranch.2))]
    have hle : MChi p ≤ wholeLineCauchyStableCeiling p u₀ := by
      rw [← hparam]
      exact le_max_right _ _
    unfold wholeLineCauchyGlobalClamp
    linarith
  have hMChi_pos : 0 < MChi p := MChi_pos_of_chi_lt_one p hchi_one
  have hbaseTrap : p.χ * (MChi p) ^ p.γ < 1 :=
    chiPos_trap_condition_of_chi_lt_half p hchi.le hchi_half hcritical
  obtain ⟨r, hr, hrTrap⟩ :=
    exists_trap_height_above_of_chi_mul_rpow_lt_one
      p hMChi_pos hchi.le hbaseTrap
  let Q : ℝ := MChi p + r
  have hMChiQ : MChi p < Q := by dsimp [Q]; linarith
  have hMChi_one : 1 ≤ MChi p :=
    one_le_MChi_of_chi_nonneg_lt_one p hchi.le hchi_one
  have hQone : 1 < Q := hMChi_one.trans_lt hMChiQ
  have hQpos : 0 < Q := zero_lt_one.trans hQone
  have hQTrap : p.χ * Q ^ p.γ < 1 := by simpa only [Q] using hrTrap
  have hbaseline : stabilitySpeedBaseline p ≤
      paper5CorrectedCStarStar p p.χ :=
    paper5CorrectedCStarStar_baseline_le p
  have hc_two : 2 < c :=
    two_lt_of_stabilitySpeedBaseline_lt hbaseline hc
  have hkappa : 0 < kappa c := kappa_pos_of_two_lt hc_two
  have heta : 0 < eta :=
    ((paper531ConcreteStabilityBudget p hregime).rootMinus_pos hc).trans hroot
  have heta_one : eta < 1 := by
    have hcap_one : stabilityWeightCap p ≤ 1 := by
      unfold stabilityWeightCap
      rw [div_le_one (by positivity)]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)
    exact hetaCap.trans_le hcap_one
  have hkappa_eta : kappa c ≤ eta :=
    ((paper531ConcreteStabilityBudget p hregime).kappa_le_rootMinus hc).trans
      hroot.le
  have hs : Paper5WaveStaticNaturalData p c U V :=
    paper5WaveStaticNaturalData_of_wave p (ne_of_gt hchi) hc hTW hbound hreg
  have hconv : CoMovingWeightedL2Convergence eta c
      (wholeLineCauchyGlobalU p u₀) U :=
    wholeLineCauchyGlobal_coMovingWeightedL2Convergence_chi_pos_natural
      p hregime hchi hc hTW hbound hreg hroot hetaCap u₀ hu₀ hinitial
  obtain ⟨Ngrad, _Fcoarse, G, _hFcoarse, hG, hgrad⟩ :=
    exists_eventual_common_weighted_H1_restart_window_of_ceiling
      (Blog := 1) (D := paper5ConcreteLu p)
      (E := paper5WaveSecondDerivativeBound p c)
      (Kflux := paper5WaveFluxBound p)
      (FD := paper5WaveFluxDerivativeBound p)
      (B := paper5WaveShiftedReactionBound p)
      p hceiling u₀ hu₀ hMChiClamp hs.hBlog heta heta_one
        hTW hbound hreg hs.hlog hs.hD hs.hFD hs.hB hs.hUd hs.hUdd
        hs.hUddcont hs.hflux hs.hfluxd hs.hflux_has hs.hfluxd_cont
        hs.hreact hs.hreact_cont hs.hgrad_int hconv
  let gap : ℝ := Q - 1
  have hgap : 0 < gap := by dsimp [gap]; linarith
  let Fsmall : ℝ := min 1 (gap ^ 2 / (4 * (1 + G)))
  have hFsmall : 0 < Fsmall := by
    dsimp [Fsmall]
    exact lt_min zero_lt_one (div_pos (sq_pos_of_pos hgap) (by positivity))
  have hFsmall_one : Fsmall ≤ 1 := by
    dsimp [Fsmall]
    exact min_le_left _ _
  have hFsmall_budget :
      Fsmall ≤ gap ^ 2 / (4 * (1 + G)) := by
    dsimp [Fsmall]
    exact min_le_right _ _
  let Cenv : ℝ := Real.sqrt (2 * Fsmall ^ 2 + 2 * Fsmall * G)
  have hinside : 0 ≤ 2 * Fsmall ^ 2 + 2 * Fsmall * G := by positivity
  have hCenv_gap : Cenv ≤ gap := by
    have hprod := mul_le_mul_of_nonneg_right hFsmall_budget
      (show 0 ≤ 2 * (1 + G) by positivity)
    have hden : 0 < 1 + G := by positivity
    have hboundInside :
        2 * Fsmall ^ 2 + 2 * Fsmall * G ≤ gap ^ 2 := by
      have hFsum : Fsmall + G ≤ 1 + G := by
        simpa only [add_comm] using add_le_add_right hFsmall_one G
      have hmul := mul_le_mul_of_nonneg_left hFsum
        (show 0 ≤ 2 * Fsmall by positivity)
      have hbudget' : 2 * Fsmall * (1 + G) ≤ gap ^ 2 := by
        calc
          2 * Fsmall * (1 + G) ≤
              2 * (gap ^ 2 / (4 * (1 + G))) * (1 + G) := by
                gcongr
          _ = gap ^ 2 / 2 := by field_simp [ne_of_gt hden]; ring
          _ ≤ gap ^ 2 := by nlinarith [sq_nonneg gap]
      nlinarith
    have hsq : Cenv ^ 2 ≤ gap ^ 2 := by
      dsimp only [Cenv]
      rw [Real.sq_sqrt hinside]
      exact hboundInside
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) hgap.le).1 hsq
  have henergySmall : ∀ᶠ t : ℝ in atTop,
      coMovingWeightedL2Energy eta c
        (wholeLineCauchyGlobalU p u₀) U t < Fsmall ^ 2 :=
    (tendsto_order.1 hconv.2).2 _ (sq_pos_of_pos hFsmall)
  obtain ⟨Tenergy, hTenergy⟩ := eventually_atTop.1
    (hconv.1.and henergySmall)
  have hlimsup := wholeLineCauchyGlobal_uniformLimsupLe_MChi_of_chi_pos
    p hchi hchi_one hcritical hceiling u₀ hu₀
  obtain ⟨Tupper, hTupper⟩ := eventually_atTop.1
    (hlimsup (Q - MChi p) (sub_pos.mpr hMChiQ))
  let step := wholeLineCauchyGlobalStep p u₀
  have hstep : 0 < step := by
    simpa only [step] using wholeLineCauchyGlobalStep_pos p u₀
  obtain ⟨Ntime, hNtime⟩ :
      ∃ Ntime : ℕ, max Tenergy Tupper ≤ ((Ntime : ℝ) + 1) * step := by
    obtain ⟨Ntime, hNtime⟩ := exists_nat_ge (max Tenergy Tupper / step)
    refine ⟨Ntime, ?_⟩
    have := (div_le_iff₀ hstep).1 hNtime
    nlinarith
  let N := max Ngrad Ntime
  refine ⟨r, hr, ?_⟩
  dsimp only
  refine ⟨hMChiQ, hQone, hQTrap, N, ?_⟩
  intro n hn t ht
  have hnGrad : Ngrad ≤ n := (le_max_left Ngrad Ntime).trans hn
  have hnTime : Ntime ≤ n := (le_max_right Ngrad Ntime).trans hn
  have htimeBase : max Tenergy Tupper ≤ ((n : ℝ) + 1) * step := by
    have hcast : (Ntime : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnTime
    exact hNtime.trans (mul_le_mul_of_nonneg_right (by linarith) hstep.le)
  have hphysEnergy : Tenergy ≤ ((n : ℝ) + 1) * step + t := by
    exact (le_max_left Tenergy Tupper).trans
      (htimeBase.trans (le_add_of_nonneg_right ht.1))
  have hphysUpper : Tupper ≤ ((n : ℝ) + 1) * step + t := by
    exact (le_max_right Tenergy Tupper).trans
      (htimeBase.trans (le_add_of_nonneg_right ht.1))
  let datum := wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c n
  let Traj := wholeLineCauchyBUCMildFixedPoint p
    (wholeLineCauchyGlobalClamp_pos p u₀).le
    (wholeLineCauchyGlobalSegmentTime_pos p u₀).le datum
    (wholeLineCauchyGlobalSegmentTime_rate p u₀)
  let q : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj s).1 (x + c * s)
  let s := step + t
  have hs : s ∈ Set.Icc step (wholeLineCauchyGlobalSegmentTime p u₀) := by
    have ht_upper : t ≤ step := by
      simpa only [step] using ht.2
    constructor
    · dsimp only [s]
      exact le_add_of_nonneg_right ht.1
    · rw [wholeLineCauchyGlobalSegmentTime_eq_two_step]
      change step + t ≤ 2 * step
      linarith
  have hbudget := hgrad n hnGrad
  have hgradSliceRaw := hbudget.2 s (by simpa only [step] using hs)
  have hgradSlice : Integrable (fun x =>
        paper5WeightedPopulationX eta q U s x ^ 2) ∧
      (∫ x, paper5WeightedPopulationX eta q U s x ^ 2) ≤ G ^ 2 := by
    simpa only [q, coMovingPath, datum, Traj] using hgradSliceRaw
  have hglobal :
      (fun x => wholeLineCauchyGlobalU p u₀
        (((n : ℝ) + 1) * step + t)
        (x + c * (((n : ℝ) + 1) * step + t))) = q s := by
    simpa only [q, datum, Traj, s, step] using
      wholeLineCauchyGlobal_coMoving_eq_translatedSegment_second_half_closed
        p hceiling u₀ hu₀ c n ht.1 ht.2
  have hq2 : ContDiff ℝ 2 (q s) := by
    have habspos : 0 < ((n : ℝ) + 1) * step + t := by
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have : 0 < ((n : ℝ) + 1) * step := mul_pos (by linarith) hstep
      linarith [ht.1]
    have hslice := wholeLineCauchyGlobalU_coMoving_contDiff_two_positive
      p hceiling u₀ hu₀ habspos (c := c)
    change ContDiff ℝ 2 (fun x => wholeLineCauchyGlobalU p u₀
      (((n : ℝ) + 1) * step + t)
      (x + c * (((n : ℝ) + 1) * step + t))) at hslice
    rw [hglobal] at hslice
    exact hslice
  have henergy := hTenergy (((n : ℝ) + 1) * step + t) hphysEnergy
  have hWfield : (fun x => paper5WeightedPopulation eta q U s x ^ 2) =
      fun x => Real.exp (2 * eta * x) * |q s x - U x| ^ 2 := by
    funext x
    exact paper5WeightedPopulation_sq_eq_weighted_difference
  have hWint : Integrable (fun x =>
      paper5WeightedPopulation eta q U s x ^ 2) := by
    rw [hWfield]
    rw [← hglobal]
    simpa only [coMovingWeightedL2Energy] using henergy.1
  have hWle : (∫ x, paper5WeightedPopulation eta q U s x ^ 2) ≤
      Fsmall ^ 2 := by
    rw [hWfield]
    rw [← hglobal]
    have := henergy.2
    simpa only [coMovingWeightedL2Energy] using this.le
  have henv := weightedDifference_pointwise_envelope_of_H1_budgets
    hFsmall.le hG hq2 (hreg.U_contDiff_two hTW) hWint hWle
      hgradSlice.1 hgradSlice.2
  refine ⟨?_, ?_⟩
  · simpa only [coMovingPath, step] using
      wholeLineCauchyGlobal_coMoving_slice_isCUnifBdd p u₀ c
        (((n : ℝ) + 1) * step + t)
  · intro x
    constructor
    · have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have htime0 : 0 ≤ ((n : ℝ) + 1) * step + t := by
        exact add_nonneg (mul_nonneg (by linarith) hstep.le) ht.1
      have hnonneg := wholeLineCauchyGlobal_nonnegative
        p hceiling u₀ hu₀
          htime0
          (x + c * (((n : ℝ) + 1) * step + t))
      simpa only [step] using hnonneg
    · apply le_min
      · have huQ := hTupper (((n : ℝ) + 1) * step + t) hphysUpper
          (x + c * (((n : ℝ) + 1) * step + t))
        have huQ' : wholeLineCauchyGlobalU p u₀
            (((n : ℝ) + 1) * step + t)
            (x + c * (((n : ℝ) + 1) * step + t)) ≤ Q := by
          linarith
        simpa only [step, Q] using huQ'
      · by_cases hx : x ≤ 0
        · have hexpOne : 1 ≤ Real.exp (-(kappa c) * x) := by
            rw [← Real.exp_zero]
            exact Real.exp_le_exp.mpr
              (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hkappa.le) hx)
          have hQle : Q ≤ Q * Real.exp (-(kappa c) * x) := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hexpOne hQpos.le
          have huQ := hTupper (((n : ℝ) + 1) * step + t) hphysUpper
            (x + c * (((n : ℝ) + 1) * step + t))
          have huQ' : wholeLineCauchyGlobalU p u₀
              (((n : ℝ) + 1) * step + t)
              (x + c * (((n : ℝ) + 1) * step + t)) ≤ Q := by
            linarith
          have := huQ'.trans hQle
          simpa only [step, Q] using this
        · have hx0 : 0 ≤ x := le_of_not_ge hx
          have hetaExp : Real.exp (-eta * x) ≤
              Real.exp (-(kappa c) * x) := by
            exact Real.exp_le_exp.mpr
              (mul_le_mul_of_nonneg_right (neg_le_neg hkappa_eta) hx0)
          have herr := (le_abs_self _).trans (henv x)
          have hUexp := hbound.le_exp x
          have hCexp :
              Real.sqrt (2 * Fsmall ^ 2 + 2 * Fsmall * G) *
                  Real.exp (-eta * x) ≤
                Real.sqrt (2 * Fsmall ^ 2 + 2 * Fsmall * G) *
                  Real.exp (-(kappa c) * x) :=
            mul_le_mul_of_nonneg_left hetaExp (Real.sqrt_nonneg _)
          have hcoef : 1 + Cenv ≤ Q := by
            dsimp only [gap] at hCenv_gap
            linarith
          have hcoefExp := mul_le_mul_of_nonneg_right hcoef
            (Real.exp_nonneg (-(kappa c) * x))
          have hqtail : q s x ≤ Q * Real.exp (-(kappa c) * x) := by
            dsimp only [Cenv] at hCexp hcoefExp
            linarith
          rw [← congrFun hglobal x] at hqtail
          simpa only [step, Q] using hqtail

section AxiomAudit

#print axioms exists_eventual_common_weighted_H1_restart_window_of_ceiling
#print axioms wholeLineCauchyGlobal_exists_chiPos_plateau_window

end AxiomAudit

end ShenWork.Paper1
