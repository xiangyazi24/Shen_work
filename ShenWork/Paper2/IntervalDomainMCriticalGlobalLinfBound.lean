import ShenWork.Paper2.IntervalDomainMCriticalGlobalLpBootstrap
import ShenWork.Paper2.IntervalDomainMCriticalLinfBound

/-!
# Global critical sup bound by a fixed backward restart window

The finite-horizon endpoint uses the horizon itself as the Duhamel integration
length.  Here the absolute restart time and the positive lag floor are split:
the former may move with the observation time, while the latter is fixed.  A
maximum on the whole past slab is then estimated by restarting one unit before
the maximizing time, so every coefficient is horizon-independent.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

/-- Critical restart estimate with separate absolute base time `b`, lag floor
`delta`, and integration-length majorant `W`. -/
theorem solutionSlice_le_of_restart_critical_lp_slab_guard_window
    {p : CM2Params} {T b h delta W r pExp C M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hb : 0 < b) (hh : 0 ≤ h) (hbhT : b + h < T)
    (hdelta : 0 < delta) (hdeltar : delta ≤ r)
    (hrh : r ≤ h) (hrW : r ≤ W)
    (hm : p.m = 1) (hp : 1 < pExp) (hγp : p.γ ≤ pExp)
    (hpower : ∀ τ, 0 < τ → τ < T →
      intervalDomainM.integral (fun z => (u τ z) ^ pExp) ≤ C)
    (hM : 0 ≤ M)
    (hslab : ∀ τ ∈ Icc b (b + h), ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u τ) y ≤ M)
    (hL : 0 ≤ L)
    (hsource : ∀ z ≥ 0, z * (p.a - p.b * z ^ p.α) ≤ L) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u (b + r)) x ≤
        fixedHeatKernelBound delta * (C + 1) +
          |p.χ₀| * (criticalChemCoefficient p W delta C *
            (M + 1) ^ (4 / 5 : ℝ)) + h * L := by
  have hr : 0 < r := hdelta.trans_le hdeltar
  have hbT : b < T := lt_of_lt_of_le (by linarith : b < b + r)
    (lt_of_le_of_lt (by linarith) hbhT).le
  have hC1 : 0 ≤ C + 1 := by
    have hγ := solution_gamma_integral_le_of_lp hsol hb hbT hγp
      (hpower b hb hbT)
    have hγnonneg : 0 ≤ ∫ y in (0 : ℝ)..1,
        intervalDomainLift (u b) y ^ p.γ :=
      intervalIntegral.integral_nonneg (by norm_num) (fun y hy =>
        Real.rpow_nonneg
          (solution_lift_pos_Icc hsol ⟨hb, hbT⟩ y (by
            simpa [Set.uIcc_of_le zero_le_one] using hy)).le _)
    linarith
  let G : ℝ := 2 * p.ν * (C + 1)
  let Q₁ : ℝ := (C + 1) * G
  let Cspec : ℝ :=
    ShenWork.HeatKernelGradientEstimates.unitIntervalCosineGradientL1LinftyConstant
  let Cg : ℝ :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
  let Achem : ℝ := Cspec * Q₁
  let Dchem : ℝ := 2 * Cg * G
  let ε : ℝ := criticalTerminalWidth delta M
  have hG : 0 ≤ G := by
    dsimp [G]
    exact mul_nonneg (mul_nonneg (by norm_num) p.hν.le) hC1
  have hQ₁ : 0 ≤ Q₁ := mul_nonneg hC1 hG
  have hCspec : 0 ≤ Cspec := by
    dsimp [Cspec]
    exact ShenWork.HeatKernelGradientEstimates.unitIntervalCosineGradientL1LinftyConstant_nonneg
  have hCg : 0 ≤ Cg := by
    dsimp [Cg]
    exact ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  have hAchem : 0 ≤ Achem := mul_nonneg hCspec hQ₁
  have hDchem : 0 ≤ Dchem := by dsimp [Dchem]; positivity
  have hε : 0 < ε := by
    simpa [ε] using criticalTerminalWidth_pos hdelta hM
  have hεr : ε ≤ r := by
    have hεdelta : ε ≤ delta := by
      simpa [ε] using criticalTerminalWidth_le hdelta hM
    exact hεdelta.trans hdeltar
  have hhom : ∀ x,
      |ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator r
          (intervalDomainLift (u b)) x| ≤
        fixedHeatKernelBound delta * (C + 1) := by
    intro x
    have hbound := restartHomM_abs_le_of_lp hsol hb hbT hr hp
      (hpower b hb hbT) x
    exact hbound.trans <| mul_le_mul_of_nonneg_right
      (fixedHeatKernelBound_anti hdelta hdeltar) hC1
  have hchem : ∀ x, |restartChemDuhamelM p b h u v r x| ≤
      criticalChemCoefficient p W delta C *
        (M + 1) ^ (4 / 5 : ℝ) := by
    intro x
    have hbound := restartChemDuhamelM_two_scale_abs_le
      hsol hb hh hbhT hm hp.le hγp hpower hM hslab hε hεr x
    have hscale := critical_two_scale_terms_le
      hdelta hM hdeltar hrW hAchem hDchem
    calc
      |restartChemDuhamelM p b h u v r x| ≤
          (r - ε) * ((Cspec / ε ^ 2) * Q₁) +
            Cg * (2 * Real.sqrt ε) * (M * G) := by
              simpa [Cspec, Q₁, Cg, G] using hbound
      _ = (r - ε) * (Achem / ε ^ 2) +
          Dchem * (M * Real.sqrt ε) := by
            dsimp [Achem, Dchem]
            field_simp [ne_of_gt hε]
      _ ≤ (W * (Achem / delta ^ 2) + Dchem * Real.sqrt delta) *
          (M + 1) ^ (4 / 5 : ℝ) := by
            simpa [ε] using hscale
      _ = criticalChemCoefficient p W delta C *
          (M + 1) ^ (4 / 5 : ℝ) := by
            simp only [criticalChemCoefficient]
            dsimp [G, Q₁, Achem, Dchem, Cspec, Cg]
  have hlog : ∀ x, restartLogisticDuhamelM p b h u r x ≤ h * L := by
    intro x
    exact (restartLogisticDuhamelM_le_of_guard
      hsol hb hh hbhT hr hsource x).trans
        (mul_le_mul_of_nonneg_right hrh hL)
  let R : ℝ := fixedHeatKernelBound delta * (C + 1) +
    |p.χ₀| * (criticalChemCoefficient p W delta C *
      (M + 1) ^ (4 / 5 : ℝ)) + h * L
  have hcand : ∀ x, faithfulRestartDuhamelM p b h u v r x ≤ R := by
    intro x
    unfold faithfulRestartDuhamelM
    dsimp [R]
    have hχ : 0 ≤ |p.χ₀| := abs_nonneg _
    have hchemMul : -p.χ₀ * restartChemDuhamelM p b h u v r x ≤
        |p.χ₀| * |restartChemDuhamelM p b h u v r x| := by
      calc
        -p.χ₀ * restartChemDuhamelM p b h u v r x ≤
            |-p.χ₀ * restartChemDuhamelM p b h u v r x| := le_abs_self _
        _ = |p.χ₀| * |restartChemDuhamelM p b h u v r x| := by
          rw [abs_mul, abs_neg]
    nlinarith [le_abs_self
      (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator r
        (intervalDomainLift (u b)) x),
      mul_le_mul_of_nonneg_left (hchem x) hχ, hhom x, hlog x]
  have haeEq := faithfulRestartDuhamelM_ae_eq_solution
    hsol hb hh hbhT hr hrh
  have haeLe : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      intervalDomainLift (u (b + r)) x ≤ R := by
    filter_upwards [haeEq] with x hx
    rw [← hx]
    exact hcand x
  have hbr0 : 0 < b + r := by linarith
  have hbrT : b + r < T :=
    lt_of_le_of_lt (by simpa [add_comm] using add_le_add_left hrh b) hbhT
  have hcont := solution_lift_continuousOn_Icc hsol ⟨hbr0, hbrT⟩
  simpa [R] using continuousOn_le_of_ae_le_Ioc hcont haeLe

/-- Complete eventual boundedness in the positive-sensitivity critical
branch.  The maximum is restarted one unit before its maximizing time, so the
coefficient is independent of the observation horizon. -/
theorem critical_bounded_global_positive
    {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbeta : 1 ≤ p.β) (hm : p.m = 1)
    (hchi : 0 < p.χ₀) (hthreshold : p.χ₀ < chiBeta p) :
    IsPaper2Bounded intervalDomainM u := by
  obtain ⟨pExp, hpExp, C, hpower⟩ := exists_critical_lp_above_gamma_global
    hguard hu₀ hglobal htrace hbeta hm hchi hthreshold
  have hp : 1 < pExp := lt_of_le_of_lt (le_max_left _ _) hpExp
  have hγp : p.γ ≤ pExp := (le_max_right (1 : ℝ) p.γ).trans hpExp.le
  have hsol3 : IsPaper2ClassicalSolution intervalDomainM p 3 u v :=
    hglobal.classical (by norm_num)
  obtain ⟨E, hearly⟩ := critical_bounded_before_positive
    hguard hu₀ hsol3 htrace hbeta hm hchi hthreshold
  obtain ⟨L, hL, hsource⟩ := exists_logistic_source_upper_of_guard p hguard
  have hC1 : 0 ≤ C + 1 := by
    have hγ := solution_gamma_integral_le_of_lp hsol3
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 3) hγp
      (hpower 1 (by norm_num))
    have hγnonneg : 0 ≤ ∫ y in (0 : ℝ)..1,
        intervalDomainLift (u 1) y ^ p.γ :=
      intervalIntegral.integral_nonneg (by norm_num) (fun y hy =>
        Real.rpow_nonneg
          (solution_lift_pos_Icc hsol3 ⟨by norm_num, by norm_num⟩ y (by
            simpa [Set.uIcc_of_le zero_le_one] using hy)).le _)
    linarith
  have hKchem : 0 ≤ criticalChemCoefficient p 1 1 C := by
    let G : ℝ := 2 * p.ν * (C + 1)
    let Q₁ : ℝ := (C + 1) * G
    let Achem : ℝ :=
      ShenWork.HeatKernelGradientEstimates.unitIntervalCosineGradientL1LinftyConstant * Q₁
    let Dchem : ℝ :=
      2 * ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant * G
    have hG : 0 ≤ G := by
      dsimp [G]
      exact mul_nonneg (mul_nonneg (by norm_num) p.hν.le) hC1
    have hQ₁ : 0 ≤ Q₁ := mul_nonneg hC1 hG
    have hAchem : 0 ≤ Achem := by
      dsimp [Achem]
      exact mul_nonneg
        ShenWork.HeatKernelGradientEstimates.unitIntervalCosineGradientL1LinftyConstant_nonneg
        hQ₁
    have hDchem : 0 ≤ Dchem := by
      dsimp [Dchem]
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg)
        hG
    simp only [criticalChemCoefficient]
    exact add_nonneg (by simpa using hAchem) (by simpa using hDchem)
  let A : ℝ := fixedHeatKernelBound 1 * (C + 1) + L
  let B : ℝ := |p.χ₀| * criticalChemCoefficient p 1 1 C
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg
      (mul_nonneg (fixedHeatKernelBound_nonneg 1) hC1) hL
  have hB : 0 ≤ B := mul_nonneg (abs_nonneg _) hKchem
  obtain ⟨R, hR, hscalar⟩ :=
    exists_uniform_bound_of_sublinear_inequality
      (m := (4 / 5 : ℝ)) (A := A + 1) (B := B)
      (by norm_num) (by norm_num) (by linarith) hB
  apply IsPaper2Bounded.of_forall_ge_supNorm_le (T := (1 : ℝ))
  intro t ht1
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  let T : ℝ := t + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have htT : t < T := by dsimp [T]; linarith
  have hsol : IsPaper2ClassicalSolution intervalDomainM p T u v :=
    hglobal.classical hT
  let h : ℝ := t - 1
  have hh : 0 ≤ h := by dsimp [h]; linarith
  have h1h : 1 + h = t := by dsimp [h]; ring
  have h1hT : 1 + h < T := by simpa [h1h] using htT
  let Kset : Set (ℝ × ℝ) := Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) 1
  let F : ℝ × ℝ → ℝ := fun z => restartField 1 h u z.1 z.2
  have hKcompact : IsCompact Kset := isCompact_Icc.prod isCompact_Icc
  have hKne : Kset.Nonempty :=
    ⟨(0, 0), ⟨⟨le_rfl, hh⟩, ⟨le_rfl, zero_le_one⟩⟩⟩
  have hFcont : ContinuousOn F Kset :=
    (restartField_continuous hsol (by norm_num) hh h1hT u (Or.inl rfl)).continuousOn
  obtain ⟨z, hz, hzmax⟩ := hKcompact.exists_isMaxOn hKne hFcont
  let M : ℝ := F z
  have hztime0 : 0 < 1 + z.1 := by linarith [hz.1.1]
  have hztimeT : 1 + z.1 < T := by
    have hzle : 1 + z.1 ≤ 1 + h := by
      simpa [add_comm] using add_le_add_left hz.1.2 1
    exact hzle.trans_lt h1hT
  have hM : 0 ≤ M := by
    have hpos := u_pos hsol hztime0 hztimeT
      (⟨z.2, hz.2⟩ : intervalDomainPoint)
    have heq := restartField_eq_physical
      (a := 1) (h := h) (w := u) hz.1 hz.2
    dsimp [M, F]
    rw [heq]
    simpa [intervalDomainLift, hz.2] using hpos.le
  have hslabGlobal : ∀ τ ∈ Icc (1 : ℝ) t, ∀ q ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u τ) q ≤ M := by
    intro τ hτ q hq
    have hrange : τ - 1 ∈ Icc (0 : ℝ) h := by
      constructor <;> dsimp [h] <;> linarith [hτ.1, hτ.2]
    have hmz := hzmax (show (τ - 1, q) ∈ Kset from ⟨hrange, hq⟩)
    have heq := restartField_eq_physical
      (a := 1) (h := h) (w := u) hrange hq
    dsimp [M, F] at hmz
    rw [heq, show 1 + (τ - 1) = τ by ring] at hmz
    exact hmz
  have hutM : ∀ x : intervalDomainPoint, u t x ≤ M := by
    intro x
    have hmz := hzmax (show (h, x.1) ∈ Kset from
      ⟨Set.right_mem_Icc.mpr hh, x.property⟩)
    have heq := restartField_eq_physical
      (a := 1) (h := h) (w := u) (Set.right_mem_Icc.mpr hh) x.property
    dsimp [M, F] at hmz
    rw [heq, h1h] at hmz
    simpa [intervalDomainLift, x.property] using hmz
  have hMbound : M ≤ max E R := by
    by_cases hzEarly : z.1 < 1
    · have htimeEarly : 1 + z.1 < 3 := by linarith
      have hME := hearly (1 + z.1) hztime0 htimeEarly
      have hbdd := solution_slice_abs_bddAbove hsol ⟨hztime0, hztimeT⟩
      have hpointSup :
          |u (1 + z.1) (⟨z.2, hz.2⟩ : intervalDomainPoint)| ≤
            intervalDomainSupNorm (u (1 + z.1)) := by
        unfold intervalDomainSupNorm
        exact le_csSup hbdd ⟨(⟨z.2, hz.2⟩ : intervalDomainPoint), rfl⟩
      have hpointE :
          |u (1 + z.1) (⟨z.2, hz.2⟩ : intervalDomainPoint)| ≤ E :=
        hpointSup.trans (by simpa [intervalDomainM, intervalDomain] using hME)
      have heq := restartField_eq_physical
        (a := 1) (h := h) (w := u) hz.1 hz.2
      have hME' : M ≤ E := by
        dsimp [M, F]
        rw [heq]
        have hpos := u_pos hsol hztime0 hztimeT
          (⟨z.2, hz.2⟩ : intervalDomainPoint)
        simpa [intervalDomainLift, hz.2, abs_of_pos hpos] using hpointE
      exact hME'.trans (le_max_left _ _)
    · have hzOne : 1 ≤ z.1 := le_of_not_gt hzEarly
      let b : ℝ := z.1
      have hb : 0 < b := lt_of_lt_of_le zero_lt_one hzOne
      have hb1T : b + 1 < T := by dsimp [b]; simpa [add_comm] using hztimeT
      have hslab : ∀ τ ∈ Icc b (b + 1), ∀ q ∈ Icc (0 : ℝ) 1,
          intervalDomainLift (u τ) q ≤ M := by
        intro τ hτ q hq
        apply hslabGlobal τ
        · constructor
          · exact le_trans hzOne hτ.1
          · have hzle : 1 + z.1 ≤ t := by
              have := hz.1.2
              dsimp [h] at this
              linarith
            dsimp [b] at hτ
            exact hτ.2.trans (by simpa [add_comm] using hzle)
        · exact hq
      have hslice := solutionSlice_le_of_restart_critical_lp_slab_guard_window
        (b := b) (h := 1) (delta := 1) (W := 1) (r := 1)
        hsol hb (by norm_num) hb1T (by norm_num) le_rfl le_rfl le_rfl
        hm hp hγp (fun τ hτ0 _hτT => hpower τ hτ0) hM hslab hL hsource
        z.2 hz.2
      have heq := restartField_eq_physical
        (a := 1) (h := h) (w := u) hz.1 hz.2
      have hraw : M ≤ fixedHeatKernelBound 1 * (C + 1) +
          |p.χ₀| * (criticalChemCoefficient p 1 1 C *
            (M + 1) ^ (4 / 5 : ℝ)) + L := by
        have hMeq : M = intervalDomainLift (u (b + 1)) z.2 := by
          dsimp [M, F, b]
          rw [heq]
          congr 2
          ring
        calc
          M = intervalDomainLift (u (b + 1)) z.2 := hMeq
          _ ≤ _ := by simpa using hslice
      have hrewrite : |p.χ₀| * (criticalChemCoefficient p 1 1 C *
          (M + 1) ^ (4 / 5 : ℝ)) =
          B * (M + 1) ^ (4 / 5 : ℝ) := by
        dsimp [B]
        ring
      rw [hrewrite] at hraw
      have hineq : M + 1 ≤
          (A + 1) + B * (M + 1) ^ (4 / 5 : ℝ) := by
        dsimp [A]
        linarith
      have hMR : M ≤ R := by
        have hMR1 := hscalar (M + 1) (by linarith) hineq
        linarith
      exact hMR.trans (le_max_right _ _)
  change intervalDomainSupNorm (u t) ≤ max E R
  unfold intervalDomainSupNorm
  apply csSup_le
  · let x₀ : intervalDomainPoint := ⟨0, ⟨le_rfl, zero_le_one⟩⟩
    exact ⟨|u t x₀|, ⟨x₀, rfl⟩⟩
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  change |u t x| ≤ max E R
  rw [abs_of_pos (u_pos hsol ht0 htT x)]
  exact (hutM x).trans hMbound

/-- At `m = 1`, a legacy global classical solution is also a faithful global
classical solution. -/
theorem globalClassicalSolution_intervalDomainM_of_m_eq_one
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (hm : p.m = 1)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v) :
    IsPaper2GlobalClassicalSolution intervalDomainM p u v := by
  intro T hT
  simpa [IsPaper2ClassicalSolution, intervalDomainM, intervalDomain,
    intervalDomainChemotaxisDivM, intervalDomainChemotaxisDiv, hm] using
      hglobal.classical hT

/-- Legacy-domain form of the positive critical global bound.  This is the
exact boundedness half consumed by the Theorem 1.2 critical branch. -/
theorem critical_bounded_global_positive_intervalDomain
    {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hbeta : 1 ≤ p.β) (hm : p.m = 1)
    (hchi : 0 < p.χ₀) (hthreshold : p.χ₀ < chiBeta p) :
    IsPaper2Bounded intervalDomain u := by
  have hu₀M : PositiveInitialDatum intervalDomainM u₀ := by
    simpa [intervalDomainM, intervalDomain] using hu₀
  have htraceM : InitialTrace intervalDomainM u₀ u := by
    simpa [intervalDomainM, intervalDomain] using htrace
  have hboundedM : IsPaper2Bounded intervalDomainM u :=
    critical_bounded_global_positive hguard hu₀M
      (globalClassicalSolution_intervalDomainM_of_m_eq_one hm hglobal)
      htraceM hbeta hm hchi hthreshold
  simpa [IsPaper2Bounded, intervalDomainM, intervalDomain] using hboundedM

#print axioms solutionSlice_le_of_restart_critical_lp_slab_guard_window
#print axioms critical_bounded_global_positive
#print axioms critical_bounded_global_positive_intervalDomain

end ShenWork.Paper2.IntervalDomainM

end
