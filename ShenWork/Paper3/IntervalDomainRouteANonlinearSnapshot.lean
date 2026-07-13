/- Actual positive-time route-(a) Nemytskii estimate on one strong slice. -/
import ShenWork.Paper3.IntervalDomainFullNonlinearRouteA
import ShenWork.Paper3.IntervalDomainPhysicalFluxDerivativeRouteA
import ShenWork.Paper3.IntervalDomainLogisticRemainderCoeffs
import ShenWork.Paper3.IntervalDomainSignalStrongBounds

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel

noncomputable section

/-- The physical full nonlinear remainder at a positive classical slice
inhabits the route-(a) `L²` package.  The radius hypotheses are explicit:
`hu_near` is the positivity ball needed by the real-power Taylor estimates,
and `M ≤ 1` is the local strong ball. -/
theorem exists_fullNonlinearRemainderRouteAData_of_strong_slice
    {p : CM2Params} {T t uStar vStar M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution
      intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hm : p.m = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (Hsplit : IntervalSolutionSignalSplitData p uStar (u t))
    (Hlin : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticLinearProfile p uStar (u t)))
    (Hquad : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticRemainderProfile p uStar (u t)))
    (hM0 : 0 ≤ M) (hM1 : M ≤ 1)
    (hu_near : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u t) x ∈ Set.Icc (uStar / 2) (3 * uStar / 2))
    (hphi : MemLp (paper3IntervalPerturbationProfile uStar (u t)) 2
      (intervalMeasure 1))
    (hphi_sup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationProfile uStar (u t) x| ≤ M)
    (hphi_l2 : intervalL2Size
      (paper3IntervalPerturbationProfile uStar (u t)) ≤ M)
    (hphiInt : IntervalIntegrable
      (paper3IntervalPerturbationProfile uStar (u t)) volume 0 1)
    (hreact : IntervalIntegrable
      (fun x => paper3LogisticReaction p (intervalDomainLift (u t) x))
      volume 0 1)
    (hlog_meas : AEStronglyMeasurable
      (paper3IntervalLogisticRemainderProfile p uStar (u t))
      (intervalMeasure 1))
    (hwx : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |deriv (intervalDomainLift (u t)) x| ≤ M)
    (hfluxDerivInt : IntervalIntegrable
      (deriv (paper3ChemFluxRemainderProfileM
        p uStar vStar (u t) (v t))) volume 0 1) :
    ∃ H : FullNonlinearRemainderRouteAData
        (paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v t),
      H.flux.bounds.M = M ∧ H.flux.bounds.L = M := by
  have hlin_meas := Hlin.profile_aestronglyMeasurable
  have hquad_meas := Hquad.profile_aestronglyMeasurable
  obtain ⟨C, hC, hsignal⟩ := paper3SignalComponents_strong_bounds
    p heq.u_pos hM0 (u t) hu_near hphi hlin_meas hquad_meas
      hphi_sup hphi_l2
  obtain ⟨Klog, hKlog, hlogQuad⟩ :=
    paper3LogisticReaction_quadratic_remainder p heq
  let U : ℝ := uStar + 1
  let B : EliminatedFluxDerivativeRouteABounds :=
    { M := M
      L := M
      U := U
      Cz1x := C
      Cz2x := C
      Cq := 2 * p.β * C
      Cqx := 2 * p.β * C
      Czx := 2 * C
      M_nonneg := hM0
      M_le_one := hM1
      L_nonneg := hM0
      L_le_M := le_rfl
      U_nonneg := by dsimp [U]; linarith [heq.u_pos]
      Cz1x_nonneg := hC.le
      Cz2x_nonneg := hC.le
      Cq_nonneg := mul_nonneg (mul_nonneg (by norm_num) p.hβ) hC.le
      Cqx_nonneg := mul_nonneg (mul_nonneg (by norm_num) p.hβ) hC.le
      Czx_nonneg := by positivity }
  let z1xx : ℝ → ℝ := paper3LinearSignalLaplacian p uStar (u t)
  let z2xx : ℝ → ℝ := paper3QuadraticSignalLaplacian p uStar (u t)
  let zxx : ℝ → ℝ := fun x => z1xx x + z2xx x
  let fluxDeriv : ℝ → ℝ :=
    deriv (paper3ChemFluxRemainderProfileM p uStar vStar (u t) (v t))
  have hM_sq_le : M ^ 2 ≤ M := by nlinarith
  have hz1xx_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |z1xx x| ≤ C * M := by
    intro x hx
    exact (hsignal x hx).2.2.1
  have hz2xx_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |z2xx x| ≤ C * M ^ 2 := by
    intro x hx
    exact (hsignal x hx).2.2.2.2.2
  have hzxx_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |zxx x| ≤ (2 * C) * M := by
    intro x hx
    dsimp [zxx]
    calc
      |z1xx x + z2xx x| ≤ |z1xx x| + |z2xx x| := abs_add_le _ _
      _ ≤ C * M + C * M ^ 2 :=
        add_le_add (hz1xx_bound x hx) (hz2xx_bound x hx)
      _ ≤ (2 * C) * M := by
        nlinarith [mul_nonneg hC.le hM0]
  have hz1xx_mem : MemLp z1xx 2 (intervalMeasure 1) := by
    apply memLp_two_of_hasDerivAt_Ioo_and_abs_bound_Icc
      (mul_nonneg hC.le hM0)
    · intro x hx
      exact paper3LinearSignalGradient_hasDerivAt_laplacian
        p uStar (u t) Hlin hx
    · exact hz1xx_bound
  have hz2xx_mem : MemLp z2xx 2 (intervalMeasure 1) := by
    apply memLp_two_of_hasDerivAt_Ioo_and_abs_bound_Icc
      (mul_nonneg hC.le (sq_nonneg M))
    · intro x hx
      exact paper3QuadraticSignalGradient_hasDerivAt_laplacian
        p uStar (u t) Hquad hx
    · exact hz2xx_bound
  have hzxx_mem : MemLp zxx 2 (intervalMeasure 1) := by
    simpa [zxx] using hz1xx_mem.add hz2xx_mem
  have hz1xx_l2 : intervalL2Size z1xx ≤ C * M :=
    intervalL2Size_le_of_pointwise_abs_bound
      (mul_nonneg hC.le hM0) hz1xx_mem
      (fun x hx => hz1xx_bound x (Set.Ioo_subset_Icc_self hx))
  have hz2xx_l2 : intervalL2Size z2xx ≤ C * M * M := by
    have h := intervalL2Size_le_of_pointwise_abs_bound
      (mul_nonneg hC.le (sq_nonneg M)) hz2xx_mem
      (fun x hx => hz2xx_bound x (Set.Ioo_subset_Icc_self hx))
    simpa [pow_two, mul_assoc] using h
  have hzxx_l2 : intervalL2Size zxx ≤ (2 * C) * M :=
    intervalL2Size_le_of_pointwise_abs_bound
      (mul_nonneg (by positivity) hM0) hzxx_mem
      (fun x hx => hzxx_bound x (Set.Ioo_subset_Icc_self hx))
  have hU : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |uStar + (intervalDomainLift (u t) x - uStar)| ≤ U := by
    intro x hx
    have hp := hphi_sup x (Set.Ioo_subset_Icc_self hx)
    dsimp [paper3IntervalPerturbationProfile] at hp
    dsimp [U]
    calc
      |uStar + (intervalDomainLift (u t) x - uStar)| ≤
          |uStar| + |intervalDomainLift (u t) x - uStar| := abs_add_le _ _
      _ ≤ uStar + M := by
        rw [abs_of_pos heq.u_pos]
        gcongr
      _ ≤ uStar + 1 := by linarith
  have hz1x : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |paper3LinearSignalGradient p uStar (u t) x| ≤ C * M := by
    intro x hx
    exact (hsignal x (Set.Ioo_subset_Icc_self hx)).2.1
  have hz2x : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |paper3QuadraticSignalGradient p uStar (u t) x| ≤ C * M * M := by
    intro x hx
    simpa [pow_two, mul_assoc] using
      (hsignal x (Set.Ioo_subset_Icc_self hx)).2.2.2.2.1
  have hzx : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |paper3LinearSignalGradient p uStar (u t) x +
          paper3QuadraticSignalGradient p uStar (u t) x| ≤
        (2 * C) * M := by
    intro x hx
    calc
      _ ≤ |paper3LinearSignalGradient p uStar (u t) x| +
          |paper3QuadraticSignalGradient p uStar (u t) x| := abs_add_le _ _
      _ ≤ C * M + C * M * M := add_le_add (hz1x x hx) (hz2x x hx)
      _ ≤ (2 * C) * M := by
        nlinarith [mul_nonneg hC.le hM0]
  have hqDiff : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |paper3SensitivityFactor p.β (intervalDomainLift (v t) x) -
          paper3SensitivityFactor p.β vStar| ≤
        (2 * p.β * C) * M := by
    intro x hx
    have hv0 := ShenWork.Paper2.solution_lift_v_nonneg_Icc
      hsol ht x (Set.Ioo_subset_Icc_self hx)
    have hsens := paper3SensitivityFactor_sub_abs_le
      p.hβ hv0 heq.v_nonneg
    have hsplit := solution_lift_v_sub_eq_signalComponents
      hsol ht heq Hsplit hx
    calc
      _ ≤ p.β * |intervalDomainLift (v t) x - vStar| := hsens
      _ = p.β * |paper3LinearSignalValue p uStar (u t) x +
          paper3QuadraticSignalValue p uStar (u t) x| := by rw [hsplit]
      _ ≤ p.β * (|paper3LinearSignalValue p uStar (u t) x| +
          |paper3QuadraticSignalValue p uStar (u t) x|) := by
        exact mul_le_mul_of_nonneg_left (abs_add_le _ _) p.hβ
      _ ≤ p.β * (C * M + C * M ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add
            (hsignal x (Set.Ioo_subset_Icc_self hx)).1
            (hsignal x (Set.Ioo_subset_Icc_self hx)).2.2.2.1) p.hβ
      _ ≤ (2 * p.β * C) * M := by
        nlinarith [mul_nonneg p.hβ hC.le, mul_nonneg hC.le hM0]
  have hqx : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |paper3SensitivityDerivativeValue p.β
          (intervalDomainLift (v t) x)
          (deriv (intervalDomainLift (v t)) x)| ≤
        (2 * p.β * C) * M := by
    intro x hx
    have hv0 := ShenWork.Paper2.solution_lift_v_nonneg_Icc
      hsol ht x (Set.Ioo_subset_Icc_self hx)
    have hsens := paper3SensitivityDerivativeValue_abs_le
      (vx := deriv (intervalDomainLift (v t)) x) p.hβ hv0
    have hgrad := solution_lift_v_deriv_eq_signalGradientComponents
      hsol ht heq Hsplit (Set.Ioo_subset_Icc_self hx)
    calc
      _ ≤ p.β * |deriv (intervalDomainLift (v t)) x| := hsens
      _ = p.β * |paper3LinearSignalGradient p uStar (u t) x +
          paper3QuadraticSignalGradient p uStar (u t) x| := by rw [hgrad]
      _ ≤ p.β * ((2 * C) * M) :=
        mul_le_mul_of_nonneg_left (hzx x hx) p.hβ
      _ = (2 * p.β * C) * M := by ring
  have hfluxBound : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |fluxDeriv x| ≤
        eliminatedFluxDerivativeRouteAConstant B
            (paper3SensitivityFactor p.β vStar) * B.M * B.L +
          |paper3SensitivityFactor p.β vStar| * B.M * |z1xx x| +
          B.U * |paper3SensitivityFactor p.β vStar| * |z2xx x| +
          B.U * B.Cq * B.L * |zxx x| := by
    intro x hx
    have hder := solution_paper3ChemFluxRemainderProfileM_hasDerivAt_routeA
      hsol ht hm heq Hsplit Hlin Hquad hx
    rw [show fluxDeriv x =
        paper3EliminatedFluxRemainderDerivativeValue
          uStar (paper3SensitivityFactor p.β vStar)
          (intervalDomainLift (u t) x - uStar)
          (deriv (intervalDomainLift (u t)) x)
          (paper3LinearSignalGradient p uStar (u t) x) (z1xx x)
          (paper3QuadraticSignalGradient p uStar (u t) x) (z2xx x)
          (paper3SensitivityFactor p.β (intervalDomainLift (v t) x) -
            paper3SensitivityFactor p.β vStar)
          (paper3SensitivityDerivativeValue p.β
            (intervalDomainLift (v t) x)
            (deriv (intervalDomainLift (v t)) x))
          (paper3LinearSignalGradient p uStar (u t) x +
            paper3QuadraticSignalGradient p uStar (u t) x)
          (zxx x) by simpa [fluxDeriv, z1xx, z2xx, zxx] using hder.deriv]
    apply paper3EliminatedFluxRemainderDerivativeValue_routeA B
    · exact hphi_sup x (Set.Ioo_subset_Icc_self hx)
    · exact hwx x hx
    · exact hU x hx
    · simpa [B] using hz1x x hx
    · simpa [B] using hz2x x hx
    · simpa [B] using hqDiff x hx
    · simpa [B] using hqx x hx
    · simpa [B] using hzx x hx
  let f0 : ℝ → ℝ := fun _x =>
    eliminatedFluxDerivativeRouteAConstant B
      (paper3SensitivityFactor p.β vStar) * B.M * B.L
  let f1 : ℝ → ℝ := fun x =>
    |paper3SensitivityFactor p.β vStar| * B.M * |z1xx x|
  let f2 : ℝ → ℝ := fun x =>
    B.U * |paper3SensitivityFactor p.β vStar| * |z2xx x|
  let f3 : ℝ → ℝ := fun x => B.U * B.Cq * B.L * |zxx x|
  let majorant : ℝ → ℝ := fun x => ((f0 x + f1 x) + f2 x) + f3 x
  have hmajorant_mem : MemLp majorant 2 (intervalMeasure 1) := by
    have hf0 : MemLp f0 2 (intervalMeasure 1) := memLp_const _
    have hf1 : MemLp f1 2 (intervalMeasure 1) := by
      have hz := hz1xx_mem.abs.const_mul
        (|paper3SensitivityFactor p.β vStar| * B.M)
      simpa [f1] using hz
    have hf2 : MemLp f2 2 (intervalMeasure 1) := by
      have hz := hz2xx_mem.abs.const_mul
        (B.U * |paper3SensitivityFactor p.β vStar|)
      simpa [f2] using hz
    have hf3 : MemLp f3 2 (intervalMeasure 1) := by
      have hz := hzxx_mem.abs.const_mul (B.U * B.Cq * B.L)
      simpa [f3] using hz
    simpa [majorant] using ((hf0.add hf1).add hf2).add hf3
  have hmajorant_nonneg : ∀ x, 0 ≤ majorant x := by
    intro x
    dsimp [majorant, f0, f1, f2, f3]
    have hK := eliminatedFluxDerivativeRouteAConstant_nonneg B
      (paper3SensitivityFactor p.β vStar)
    have h0 : 0 ≤ eliminatedFluxDerivativeRouteAConstant B
        (paper3SensitivityFactor p.β vStar) * B.M * B.L :=
      mul_nonneg (mul_nonneg hK B.M_nonneg) B.L_nonneg
    have h1 : 0 ≤ |paper3SensitivityFactor p.β vStar| * B.M *
        |z1xx x| :=
      mul_nonneg (mul_nonneg (abs_nonneg _) B.M_nonneg) (abs_nonneg _)
    have h2 : 0 ≤ B.U * |paper3SensitivityFactor p.β vStar| *
        |z2xx x| :=
      mul_nonneg (mul_nonneg B.U_nonneg (abs_nonneg _)) (abs_nonneg _)
    have h3 : 0 ≤ B.U * B.Cq * B.L * |zxx x| :=
      mul_nonneg (mul_nonneg (mul_nonneg B.U_nonneg B.Cq_nonneg)
        B.L_nonneg) (abs_nonneg _)
    exact add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3
  have hflux_mem : MemLp fluxDeriv 2 (intervalMeasure 1) := by
    apply memLp_two_of_pointwise_mul_Ioo (B := 1) (by norm_num)
      (measurable_deriv _).aestronglyMeasurable hmajorant_mem
    intro x hx
    rw [one_mul, abs_of_nonneg (hmajorant_nonneg x)]
    exact hfluxBound x hx
  have hlogPoint : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |paper3IntervalLogisticRemainderProfile p uStar (u t) x| ≤
        (Klog * M) * |paper3IntervalPerturbationProfile uStar (u t) x| := by
    intro x hx
    have hq := hlogQuad (intervalDomainLift (u t) x)
      (hu_near x (Set.Ioo_subset_Icc_self hx))
    have hs := hphi_sup x (Set.Ioo_subset_Icc_self hx)
    dsimp [paper3IntervalLogisticRemainderProfile,
      paper3IntervalPerturbationProfile, paper3LogisticRemainder] at hq ⊢
    calc
      _ ≤ Klog * |intervalDomainLift (u t) x - uStar| ^ 2 := hq
      _ ≤ (Klog * M) * |intervalDomainLift (u t) x - uStar| := by
        have hnonneg : 0 ≤ |intervalDomainLift (u t) x - uStar| := abs_nonneg _
        have hprod : 0 ≤ Klog * |intervalDomainLift (u t) x - uStar| *
            (M - |intervalDomainLift (u t) x - uStar|) :=
          mul_nonneg (mul_nonneg hKlog.le hnonneg) (sub_nonneg.mpr hs)
        nlinarith
  have hlog_mem : MemLp
      (paper3IntervalLogisticRemainderProfile p uStar (u t)) 2
      (intervalMeasure 1) :=
    memLp_two_of_pointwise_mul_Ioo
      (mul_nonneg hKlog.le hM0) hlog_meas hphi hlogPoint
  have hlog_l2 : intervalL2Size
      (paper3IntervalLogisticRemainderProfile p uStar (u t)) ≤
        Klog * M * M := by
    have hmul := intervalL2Size_le_of_pointwise_mul
      (mul_nonneg hKlog.le hM0) hlog_mem hphi hlogPoint
    calc
      _ ≤ (Klog * M) * intervalL2Size
          (paper3IntervalPerturbationProfile uStar (u t)) := hmul
      _ ≤ (Klog * M) * M :=
        mul_le_mul_of_nonneg_left hphi_l2 (mul_nonneg hKlog.le hM0)
  let Hflux : EliminatedFluxDerivativeRouteAL2Data :=
    { bounds := B
      qStar := paper3SensitivityFactor p.β vStar
      Cz1xx := C
      Cz2xx := C
      Czxx := 2 * C
      profile := fluxDeriv
      z1xx := z1xx
      z2xx := z2xx
      zxx := zxx
      Cz1xx_nonneg := hC.le
      Cz2xx_nonneg := hC.le
      Czxx_nonneg := by positivity
      profile_memLp := hflux_mem
      z1xx_memLp := hz1xx_mem
      z2xx_memLp := hz2xx_mem
      zxx_memLp := hzxx_mem
      profile_bound := hfluxBound
      z1xx_l2 := by simpa [B] using hz1xx_l2
      z2xx_l2 := by simpa [B] using hz2xx_l2
      zxx_l2 := by simpa [B] using hzxx_l2 }
  let Hfull : FullNonlinearRemainderRouteAData
      (paper3FullModeNonlinearRemainderCoeffM
        p uStar vStar u v t) :=
    { chi := p.χ₀
      flux := Hflux
      Klog := Klog
      logProfile := paper3IntervalLogisticRemainderProfile p uStar (u t)
      Klog_nonneg := hKlog.le
      log_memLp := hlog_mem
      log_l2 := by simpa [Hflux, B] using hlog_l2
      coeff_eq := by
        intro n
        rw [paper3FullModeNonlinearRemainderCoeffM_eq_parts,
          paper3ChemotaxisRemainderCoeffM_eq_routeA_cosine
            hsol ht hm heq Hsplit Hlin Hquad hfluxDerivInt n,
          paper3LogisticRemainderCoeffM_eq_cosine
            p uStar u t n hreact hphiInt] }
  refine ⟨Hfull, ?_, ?_⟩ <;> rfl

#print axioms exists_fullNonlinearRemainderRouteAData_of_strong_slice

end

end ShenWork.Paper3
