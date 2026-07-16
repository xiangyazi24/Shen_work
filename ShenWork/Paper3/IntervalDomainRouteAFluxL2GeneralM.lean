/- Route-A `L²` flux-remainder data for the faithful general-`m` model. -/
import ShenWork.Paper3.IntervalDomainRouteANonlinearSnapshot
import ShenWork.Paper3.IntervalDomainPhysicalFluxDerivativeRouteAGeneralM
import ShenWork.Paper3.IntervalDomainRouteAPowerBoundsGeneralM
import ShenWork.Paper3.IntervalDomainSignalStrongBounds

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2

noncomputable section

/-- The trajectory-independent Route-A flux constant for the faithful
general-`m` power.  The only change from the `m = 1` expression is the fixed
positive-strip ceiling for `u ^ m`. -/
def paper3RouteAFluxL2ConstantGeneralM
    (p : CM2Params) (uStar vStar C : ℝ) : ℝ :=
  let U := paper3RouteAPowerCeiling p uStar
  let qStar := paper3SensitivityFactor p.β vStar
  let Cq := 2 * p.β * C
  let K0 := |qStar| * C + |qStar| * C +
    Cq * (2 * C) + U * Cq * (2 * C)
  Real.sqrt 2 *
    (Real.sqrt 2 *
      (Real.sqrt 2 * (K0 + |qStar| * C) + U * |qStar| * C) +
        U * Cq * (2 * C))

/-- On a faithful positive classical slice, the differentiated general-`m`
chemotaxis remainder inhabits the existing Route-A `L²` package.  The strong
radius is scaled by the fixed power factor, while the weak/signal radius stays
equal to `M`. -/
theorem exists_routeAFluxL2Data_of_strong_slice_generalM
    {p : CM2Params} {T t uStar vStar M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (Hsplit : IntervalSolutionSignalSplitData p uStar (u t))
    (Hlin : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticLinearProfile p uStar (u t)))
    (Hquad : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticRemainderProfile p uStar (u t)))
    (C : ℝ) (hC : 0 < C)
    (hsignal : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3LinearSignalValue p uStar (u t) x| ≤ C * M ∧
      |paper3LinearSignalGradient p uStar (u t) x| ≤ C * M ∧
      |paper3LinearSignalLaplacian p uStar (u t) x| ≤ C * M ∧
      |paper3QuadraticSignalValue p uStar (u t) x| ≤ C * M ^ 2 ∧
      |paper3QuadraticSignalGradient p uStar (u t) x| ≤ C * M ^ 2 ∧
      |paper3QuadraticSignalLaplacian p uStar (u t) x| ≤ C * M ^ 2)
    (hM0 : 0 ≤ M)
    (hscaledM1 : paper3RouteAPowerFactor p uStar * M ≤ 1)
    (hu_near : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u t) x ∈ Set.Icc (uStar / 2) (3 * uStar / 2))
    (hphi_sup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationProfile uStar (u t) x| ≤ M)
    (hwx : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |deriv (intervalDomainLift (u t)) x| ≤ M) :
    ∃ H : EliminatedFluxDerivativeRouteAL2Data,
      H.bounds.M = paper3RouteAPowerFactor p uStar * M ∧
        H.bounds.L = M ∧
        H.profile = deriv (paper3ChemFluxRemainderProfileM
          p uStar vStar (u t) (v t)) ∧
        H.z1xx = paper3LinearSignalLaplacian p uStar (u t) ∧
        H.l2Constant =
          paper3RouteAFluxL2ConstantGeneralM p uStar vStar C := by
  let P : ℝ := paper3RouteAPowerFactor p uStar
  let U : ℝ := paper3RouteAPowerCeiling p uStar
  let B : EliminatedFluxDerivativeRouteABounds :=
    { M := P * M
      L := M
      U := U
      Cz1x := C
      Cz2x := C
      Cq := 2 * p.β * C
      Cqx := 2 * p.β * C
      Czx := 2 * C
      M_nonneg := mul_nonneg (paper3RouteAPowerFactor_nonneg p uStar) hM0
      M_le_one := by simpa [P] using hscaledM1
      L_nonneg := hM0
      L_le_M := by
        have hP := paper3RouteAPowerFactor_one_le p uStar
        dsimp [P]
        nlinarith [mul_nonneg (sub_nonneg.mpr hP) hM0]
      U_nonneg := (paper3RouteAPowerCeiling_pos p heq.u_pos).le
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
  have hP1 : 1 ≤ P := by
    simpa [P] using paper3RouteAPowerFactor_one_le p uStar
  have hM_le_scaled : M ≤ P * M := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hP1) hM0]
  have hM1 : M ≤ 1 := hM_le_scaled.trans (by simpa [P] using hscaledM1)
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
  have hz2xx_l2_raw : intervalL2Size z2xx ≤ C * M * M := by
    have h := intervalL2Size_le_of_pointwise_abs_bound
      (mul_nonneg hC.le (sq_nonneg M)) hz2xx_mem
      (fun x hx => hz2xx_bound x (Set.Ioo_subset_Icc_self hx))
    simpa [pow_two, mul_assoc] using h
  have hz2xx_l2 : intervalL2Size z2xx ≤ C * (P * M) * M := by
    calc
      intervalL2Size z2xx ≤ C * M * M := hz2xx_l2_raw
      _ ≤ C * (P * M) * M := by
        nlinarith [mul_nonneg hC.le hM0,
          mul_nonneg (mul_nonneg hC.le hM0) hM0,
          mul_nonneg (sub_nonneg.mpr hP1) (sq_nonneg M)]
  have hzxx_l2 : intervalL2Size zxx ≤ (2 * C) * M :=
    intervalL2Size_le_of_pointwise_abs_bound
      (mul_nonneg (by positivity) hM0) hzxx_mem
      (fun x hx => hzxx_bound x (Set.Ioo_subset_Icc_self hx))
  have hpowDiff : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |(intervalDomainLift (u t) x) ^ p.m - uStar ^ p.m| ≤ P * M := by
    intro x hx
    simpa [P] using paper3RouteAPower_sub_le_factor_mul p heq.u_pos
      (hu_near x (Set.Ioo_subset_Icc_self hx))
      (hphi_sup x (Set.Ioo_subset_Icc_self hx))
  have hpowDeriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |p.m * (intervalDomainLift (u t) x) ^ (p.m - 1) *
          deriv (intervalDomainLift (u t)) x| ≤ P * M := by
    intro x hx
    simpa [P] using paper3RouteAPower_derivative_le_factor_mul p heq.u_pos
      (hu_near x (Set.Ioo_subset_Icc_self hx)) (hwx x hx)
  have hpowValue : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |(intervalDomainLift (u t) x) ^ p.m| ≤ U := by
    intro x hx
    simpa [U] using paper3RouteAPower_abs_le_ceiling p heq.u_pos
      (hu_near x (Set.Ioo_subset_Icc_self hx))
  have hz1x : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |paper3LinearSignalGradient p uStar (u t) x| ≤ C * M := by
    intro x hx
    exact (hsignal x (Set.Ioo_subset_Icc_self hx)).2.1
  have hz2x_raw : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |paper3QuadraticSignalGradient p uStar (u t) x| ≤ C * M * M := by
    intro x hx
    simpa [pow_two, mul_assoc] using
      (hsignal x (Set.Ioo_subset_Icc_self hx)).2.2.2.2.1
  have hz2x : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |paper3QuadraticSignalGradient p uStar (u t) x| ≤
        C * (P * M) * M := by
    intro x hx
    exact (hz2x_raw x hx).trans (by
      nlinarith [mul_nonneg hC.le hM0,
        mul_nonneg (sub_nonneg.mpr hP1) (sq_nonneg M)])
  have hzx : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |paper3LinearSignalGradient p uStar (u t) x +
          paper3QuadraticSignalGradient p uStar (u t) x| ≤
        (2 * C) * M := by
    intro x hx
    calc
      _ ≤ |paper3LinearSignalGradient p uStar (u t) x| +
          |paper3QuadraticSignalGradient p uStar (u t) x| := abs_add_le _ _
      _ ≤ C * M + C * M * M := add_le_add (hz1x x hx) (hz2x_raw x hx)
      _ ≤ (2 * C) * M := by
        nlinarith [mul_nonneg hC.le hM0]
  have hqDiff : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |paper3SensitivityFactor p.β (intervalDomainLift (v t) x) -
          paper3SensitivityFactor p.β vStar| ≤
        (2 * p.β * C) * M := by
    intro x hx
    have hv0 := IntervalDomainM.lift_v_nonneg_Icc
      hsol ht.1 ht.2 x (Set.Ioo_subset_Icc_self hx)
    have hsens := paper3SensitivityFactor_sub_abs_le
      p.hβ hv0 heq.v_nonneg
    have hsplit := solution_lift_v_sub_eq_signalComponents_generalM
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
    have hv0 := IntervalDomainM.lift_v_nonneg_Icc
      hsol ht.1 ht.2 x (Set.Ioo_subset_Icc_self hx)
    have hsens := paper3SensitivityDerivativeValue_abs_le
      (vx := deriv (intervalDomainLift (v t)) x) p.hβ hv0
    have hgrad := solution_lift_v_deriv_eq_signalGradientComponents_generalM
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
    have hder := solution_paper3ChemFluxRemainderProfileM_hasDerivAt_routeA_generalM
      hsol ht heq Hsplit Hlin Hquad hx
    rw [show fluxDeriv x =
        paper3EliminatedFluxRemainderDerivativeValue
          (uStar ^ p.m) (paper3SensitivityFactor p.β vStar)
          ((intervalDomainLift (u t) x) ^ p.m - uStar ^ p.m)
          (p.m * (intervalDomainLift (u t) x) ^ (p.m - 1) *
            deriv (intervalDomainLift (u t)) x)
          (paper3LinearSignalGradient p uStar (u t) x) (z1xx x)
          (paper3QuadraticSignalGradient p uStar (u t) x) (z2xx x)
          (paper3SensitivityFactor p.β (intervalDomainLift (v t) x) -
            paper3SensitivityFactor p.β vStar)
          (paper3SensitivityDerivativeValue p.β
            (intervalDomainLift (v t) x)
            (deriv (intervalDomainLift (v t)) x))
          (paper3LinearSignalGradient p uStar (u t) x +
            paper3QuadraticSignalGradient p uStar (u t) x)
          (zxx x) by
        simpa [fluxDeriv, z1xx, z2xx, zxx] using hder.deriv]
    apply paper3EliminatedFluxRemainderDerivativeValue_routeA B
    · exact hpowDiff x hx
    · exact hpowDeriv x hx
    · simpa [B] using hpowValue x hx
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
  refine ⟨Hflux, rfl, rfl, rfl, rfl, ?_⟩
  simp only [Hflux, EliminatedFluxDerivativeRouteAL2Data.l2Constant, B,
    eliminatedFluxDerivativeRouteAConstant,
    paper3RouteAFluxL2ConstantGeneralM, U]

#print axioms paper3RouteAFluxL2ConstantGeneralM
#print axioms exists_routeAFluxL2Data_of_strong_slice_generalM

end

end ShenWork.Paper3
