import ShenWork.Paper1.WholeLineWeightedRegularityForcingWindowNatural
import ShenWork.Paper1.WholeLineWeightedRegularityBoundedDriftRestart
import ShenWork.Paper1.WholeLineWeightedRegularityForcingHolder

open Filter MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Natural pointwise data on a positive canonical window

This file collects the pointwise and measurability data used by the exact
weighted generator restart.  In particular, joint measurability is derived
from the already proved uniform-in-space time modulus and spatial
continuity; it is not carried as an independent analytic hypothesis.
-/

/-- A scalar family which is measurable in space and locally Holder in time,
uniformly in space, remains jointly measurable after clamping time to a
closed interval. -/
theorem measurable_uncurry_projIcc_of_local_rpow_holder
    {a b alpha H : ℝ} (hab : a ≤ b) (halpha : 0 < alpha) (hH : 0 ≤ H)
    {f : ℝ → ℝ → ℝ}
    (hf_meas : ∀ q ∈ Set.Icc a b, Measurable (f q))
    (hf_holder : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      ∀ x : ℝ, |s - t| ≤ 1 →
        |f s x - f t x| ≤ H * |s - t| ^ alpha) :
    Measurable (Function.uncurry (fun q =>
      f ((Set.projIcc a b hab q : Set.Icc a b).1))) := by
  apply measurable_uncurry_of_continuous_of_measurable
  · intro x
    apply continuous_of_local_rpow_holder halpha
    intro s t hst
    let ps : ℝ := (Set.projIcc a b hab s : Set.Icc a b).1
    let pt : ℝ := (Set.projIcc a b hab t : Set.Icc a b).1
    have hps : ps ∈ Set.Icc a b := (Set.projIcc a b hab s).2
    have hpt : pt ∈ Set.Icc a b := (Set.projIcc a b hab t).2
    have hproj : |ps - pt| ≤ |s - t| := by
      have hraw := (LipschitzWith.projIcc hab).dist_le_mul s t
      simpa only [NNReal.coe_one, one_mul, Real.dist_eq, ps, pt] using hraw
    have hpow : |ps - pt| ^ alpha ≤ |s - t| ^ alpha :=
      Real.rpow_le_rpow (abs_nonneg _) hproj halpha.le
    rw [Real.norm_eq_abs]
    calc
      |f ps x - f pt x| ≤ H * |ps - pt| ^ alpha :=
        hf_holder ps hps pt hpt x (hproj.trans hst)
      _ ≤ H * |s - t| ^ alpha := mul_le_mul_of_nonneg_left hpow hH
  · intro q
    exact hf_meas _ (Set.projIcc a b hab q).2

/-- The genuine weighted generator forcing is a continuous spatial function
on every classical `C²` slice.  The proof uses the physical product-rule
representative, so no continuity of a formal `deriv` is assumed. -/
theorem paper5WeightedGeneratorForcing_continuous_of_classical_slices
    (p : CMParams) {T eta c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V) :
    Continuous (paper5WeightedGeneratorForcing p eta
      (coMovingPath c u) (coMovingPath c v) U V t) := by
  let physical : ℝ → ℝ := fun x =>
    (-p.χ) * (Real.exp (eta * x) *
      ((p.m * (coMovingPath c u t x) ^ (p.m - 1) *
            deriv (coMovingPath c u t) x * deriv (coMovingPath c v t) x +
          (coMovingPath c u t x) ^ p.m *
            (coMovingPath c v t x - (coMovingPath c u t x) ^ p.γ)) -
        (p.m * (U x) ^ (p.m - 1) * deriv U x * deriv V x +
          (U x) ^ p.m * (V x - (U x) ^ p.γ)))) +
      Real.exp (eta * x) *
        (reactionFun p.α (coMovingPath c u t x) - reactionFun p.α (U x))
  have hphysical : Continuous physical := by
    have hexp : Continuous (fun x : ℝ => Real.exp (eta * x)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hu : Continuous (coMovingPath c u t) := hu2.continuous
    have hv : Continuous (coMovingPath c v t) := hv2.continuous
    have hUc : Continuous U := hU2.continuous
    have hVc : Continuous V := hV2.continuous
    have hux : Continuous (deriv (coMovingPath c u t)) :=
      hu2.continuous_deriv (by norm_num)
    have hvx : Continuous (deriv (coMovingPath c v t)) :=
      hv2.continuous_deriv (by norm_num)
    have hUx : Continuous (deriv U) := hU2.continuous_deriv (by norm_num)
    have hVx : Continuous (deriv V) := hV2.continuous_deriv (by norm_num)
    have hm0 : 0 ≤ p.m := zero_le_one.trans p.hm
    have hm10 : 0 ≤ p.m - 1 := sub_nonneg.mpr p.hm
    have hgamma0 : 0 ≤ p.γ := zero_le_one.trans p.hγ
    have hupowm : Continuous (fun x => (coMovingPath c u t x) ^ p.m) :=
      (Real.continuous_rpow_const hm0).comp hu
    have hupowm1 : Continuous
        (fun x => (coMovingPath c u t x) ^ (p.m - 1)) :=
      (Real.continuous_rpow_const hm10).comp hu
    have hupowgamma : Continuous
        (fun x => (coMovingPath c u t x) ^ p.γ) :=
      (Real.continuous_rpow_const hgamma0).comp hu
    have hUpowm : Continuous (fun x => (U x) ^ p.m) :=
      (Real.continuous_rpow_const hm0).comp hUc
    have hUpowm1 : Continuous (fun x => (U x) ^ (p.m - 1)) :=
      (Real.continuous_rpow_const hm10).comp hUc
    have hUpowgamma : Continuous (fun x => (U x) ^ p.γ) :=
      (Real.continuous_rpow_const hgamma0).comp hUc
    have hdynamic : Continuous (fun x =>
        p.m * (coMovingPath c u t x) ^ (p.m - 1) *
            deriv (coMovingPath c u t) x * deriv (coMovingPath c v t) x +
          (coMovingPath c u t x) ^ p.m *
            (coMovingPath c v t x - (coMovingPath c u t x) ^ p.γ)) :=
      (((continuous_const.mul hupowm1).mul hux).mul hvx).add
        (hupowm.mul (hv.sub hupowgamma))
    have hwave : Continuous (fun x =>
        p.m * (U x) ^ (p.m - 1) * deriv U x * deriv V x +
          (U x) ^ p.m * (V x - (U x) ^ p.γ)) :=
      (((continuous_const.mul hUpowm1).mul hUx).mul hVx).add
        (hUpowm.mul (hVc.sub hUpowgamma))
    have hflux : Continuous (fun x =>
        (-p.χ) * (Real.exp (eta * x) *
          ((p.m * (coMovingPath c u t x) ^ (p.m - 1) *
                deriv (coMovingPath c u t) x *
                deriv (coMovingPath c v t) x +
              (coMovingPath c u t x) ^ p.m *
                (coMovingPath c v t x - (coMovingPath c u t x) ^ p.γ)) -
            (p.m * (U x) ^ (p.m - 1) * deriv U x * deriv V x +
              (U x) ^ p.m * (V x - (U x) ^ p.γ))))) :=
      continuous_const.mul (hexp.mul (hdynamic.sub hwave))
    have hreact : Continuous (fun x =>
        Real.exp (eta * x) *
          (reactionFun p.α (coMovingPath c u t x) - reactionFun p.α (U x))) :=
      hexp.mul
        (((continuous_reactionFun (zero_le_one.trans p.hα)).comp hu).sub
          ((continuous_reactionFun (zero_le_one.trans p.hα)).comp hUc))
    exact hflux.add hreact
  apply hphysical.congr
  intro x
  dsimp only [physical]
  unfold paper5WeightedGeneratorForcing
  rw [paper5CoMovingFluxDerivative_realization_of_classical
      p hsol ht0 htT (hu2.of_le (by norm_num)) hv2,
    paper5WaveFluxDerivative_realization p hTW
      (hU2.of_le (by norm_num)) hV2]
  ring

/-- The canonical mild fixed point supplies the population strip and the
`C²` population/signal slices uniformly on every closed positive window. -/
theorem wholeLineCauchyBUCMildFixedPoint_positive_window_slice_data
    (p : CMParams) {M T a b c : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let u : ℝ → ℝ → ℝ := fun s x =>
      (wholeLineBUCTrajectoryExtend hT Traj s).1 x
    let v : ℝ → ℝ → ℝ := fun s => frozenElliptic p (u s)
    IsClassicalSolution p T u v ∧
      (∀ s ∈ Set.Icc a b, ∀ x,
        coMovingPath c u s x ∈ Set.Icc (0 : ℝ) M) ∧
      (∀ s ∈ Set.Icc a b, ContDiff ℝ 2 (coMovingPath c u s)) ∧
      ∀ s ∈ Set.Icc a b, ContDiff ℝ 2 (coMovingPath c v s) := by
  dsimp only
  let Traj : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let u : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend hT Traj s).1 x
  let v : ℝ → ℝ → ℝ := fun s => frozenElliptic p (u s)
  have hTpos : 0 < T := ha.trans_le (hab.trans hbT.le)
  have hsol : IsClassicalSolution p T u v := by
    simpa only [u, v, Traj] using
      (wholeLineCauchyBUCMildFixedPoint_isClassicalSolution
        p (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
          hM hTpos u₀ hsmall
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) hstrip)
  have huM : ∀ s ∈ Set.Icc a b, ∀ x,
      coMovingPath c u s x ∈ Set.Icc (0 : ℝ) M := by
    intro s hs x
    let zs : Set.Icc (0 : ℝ) T :=
      ⟨s, ha.le.trans hs.1, hs.2.trans hbT.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT Traj s = Traj zs :=
      wholeLineBUCTrajectoryExtend_eq hT Traj zs.2
    simpa only [coMovingPath, u, hext] using hstrip zs (x + c * s)
  have hu2 : ∀ s ∈ Set.Icc a b,
      ContDiff ℝ 2 (coMovingPath c u s) := by
    intro s hs
    have hs0 : 0 < s := ha.trans_le hs.1
    have hsT : s ≤ T := hs.2.trans hbT.le
    let zs : Set.Icc (0 : ℝ) T := ⟨s, hs0.le, hsT⟩
    have hwindow : ∀ r ∈ Set.Icc (s / 2) s, ∀ x,
        (wholeLineBUCTrajectoryExtend hT Traj r).1 x ∈
          Set.Icc (0 : ℝ) M := by
      intro r hr x
      have hrT : r ∈ Set.Icc (0 : ℝ) T :=
        ⟨(half_pos hs0).le.trans hr.1, hr.2.trans hsT⟩
      rw [wholeLineBUCTrajectoryExtend_eq hT Traj hrT]
      exact hstrip ⟨r, hrT⟩ x
    have hslice : ContDiff ℝ 2 (fun x => (Traj zs).1 x) := by
      simpa only [Traj] using
        (wholeLineCauchyBUCMildFixedPoint_slice_contDiff_two_positive
          (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
          p hM hT u₀ hsmall zs hs0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) hwindow)
    have hext : wholeLineBUCTrajectoryExtend hT Traj s = Traj zs :=
      wholeLineBUCTrajectoryExtend_eq hT Traj zs.2
    change ContDiff ℝ 2
      (fun x => (wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s))
    rw [hext]
    exact ContDiff.two_shift hslice (c * s)
  have hv2 : ∀ s ∈ Set.Icc a b,
      ContDiff ℝ 2 (coMovingPath c v s) := by
    intro s hs
    have huCphys : IsCUnifBdd (u s) := by
      dsimp only [u]
      exact WholeLineBUC.isCUnifBdd
        (wholeLineBUCTrajectoryExtend hT Traj s)
    have hu0phys : ∀ x, 0 ≤ u s x := by
      intro x
      have hsT : s ∈ Set.Icc (0 : ℝ) T :=
        ⟨ha.le.trans hs.1, hs.2.trans hbT.le⟩
      have hext := wholeLineBUCTrajectoryExtend_eq hT Traj hsT
      simpa only [u, hext] using (hstrip ⟨s, hsT⟩ x).1
    have hvEq : coMovingPath c v s =
        frozenElliptic p (coMovingPath c u s) := by
      change (fun x => frozenElliptic p (u s) (x + c * s)) =
        frozenElliptic p (fun x => u s (x + c * s))
      exact (frozenElliptic_comp_add_const_fun p huCphys hu0phys (c * s)).symm
    rw [hvEq]
    have huC : IsCUnifBdd (coMovingPath c u s) := by
      simpa only [coMovingPath] using
        isCUnifBdd_comp_add_const huCphys (c * s)
    exact frozenElliptic_contDiff_two_of_cunifBdd_nonneg
      p huC (fun x => (huM s hs x).1)
  exact ⟨hsol, huM, hu2, hv2⟩

/-- The canonical raw generator source with its time variable clamped to a
closed positive window. -/
def paper5CanonicalGeneratorForcingRawPositiveWindowClamped
    (p : CMParams) (c : ℝ) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (Traj : WholeLineBUCTrajectory T) (U V : ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b) (s x : ℝ) : ℝ :=
  paper5CanonicalGeneratorForcingRaw p c hM hT Traj U V
    (Set.projIcc a b hab s) x

/-- Exact exponential conjugation of the clamped canonical raw source. -/
def paper5WeightedGeneratorForcingPositiveWindowClamped
    (p : CMParams) (eta c : ℝ) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (Traj : WholeLineBUCTrajectory T) (U V : ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b) (s x : ℝ) : ℝ :=
  Real.exp (eta * x) *
    paper5CanonicalGeneratorForcingRawPositiveWindowClamped
      p c hM hT Traj U V hab s x

/-- Natural raw/weighted forcing data on a closed positive canonical
window.  The theorem exports one time exponent, one raw ceiling, spatial
continuity of every slice, and joint measurability of both clamped scalar
representatives. -/
theorem exists_paper5CanonicalGeneratorForcingRaw_positive_window_natural_data
    (p : CMParams) {M T a b eta c FD : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hMChi : MChi p ≤ M)
    (hFD : 0 ≤ FD)
    (hwaveFlux : ∀ x,
      |deriv (fun y => U y ^ p.m * deriv V y) x| ≤ FD) :
    let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let u : ℝ → ℝ → ℝ := fun s x =>
      (wholeLineBUCTrajectoryExtend hT Traj s).1 x
    let v : ℝ → ℝ → ℝ := fun s => frozenElliptic p (u s)
    ∃ alpha H D : ℝ,
      0 < alpha ∧ alpha ≤ 1 ∧ 0 ≤ H ∧ 0 ≤ D ∧
      (∀ s ∈ Set.Icc a b,
        Continuous (paper5CanonicalGeneratorForcingRaw
          p c hM hT Traj U V s)) ∧
      (∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x : ℝ,
        |s - t| ≤ 1 →
        |paper5CanonicalGeneratorForcingRaw p c hM hT Traj U V s x -
            paper5CanonicalGeneratorForcingRaw p c hM hT Traj U V t x| ≤
          H * |s - t| ^ alpha) ∧
      (∀ s ∈ Set.Icc a b, ∀ x,
        |paper5CanonicalGeneratorForcingRaw
          p c hM hT Traj U V s x| ≤ D) ∧
      Measurable (Function.uncurry
        (paper5CanonicalGeneratorForcingRawPositiveWindowClamped
          p c hM hT Traj U V hab)) ∧
      Measurable (Function.uncurry
        (paper5WeightedGeneratorForcingPositiveWindowClamped
          p eta c hM hT Traj U V hab)) ∧
      ∀ s ∈ Set.Icc a b, ∀ x,
        paper5WeightedGeneratorForcingPositiveWindowClamped
            p eta c hM hT Traj U V hab s x =
          paper5WeightedGeneratorForcing p eta
            (coMovingPath c u) (coMovingPath c v) U V s x := by
  dsimp only
  let Traj : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let u : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend hT Traj s).1 x
  let v : ℝ → ℝ → ℝ := fun s => frozenElliptic p (u s)
  obtain ⟨hsol, huM, hu2, hv2⟩ :=
    wholeLineCauchyBUCMildFixedPoint_positive_window_slice_data
      (c := c) p hM hT ha hab hbT u₀ hsmall hstrip
  have hU2 : ContDiff ℝ 2 U := hreg.U_contDiff_two hTW
  have hV2 : ContDiff ℝ 2 V := hreg.V_contDiff_two hTW
  have hUwM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M := by
    intro x
    exact ⟨(hbound.pos x).le, (hbound.le_MChi x).trans hMChi⟩
  have hstripWindow : ∀ s ∈ Set.Icc a b, ∀ x,
      (wholeLineBUCTrajectoryExtend hT Traj s).1 x ∈
        Set.Icc (0 : ℝ) M := by
    intro s hs x
    have hsT : s ∈ Set.Icc (0 : ℝ) T :=
      ⟨ha.le.trans hs.1, hs.2.trans hbT.le⟩
    rw [wholeLineBUCTrajectoryExtend_eq hT Traj hsT]
    exact hstrip ⟨s, hsT⟩ x
  obtain ⟨alpha, H, halpha, halpha1, hH, hholderRaw⟩ :=
    exists_paper5CanonicalGeneratorForcingRaw_time_holder_positive_window
      p c hM hT ha hab hbT.le u₀ hsmall
        (theta := (1 / 2 : ℝ)) (zeta := (1 / 4 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hstrip U V
  obtain ⟨D, hD, hrawBound⟩ :=
    exists_paper5CanonicalGeneratorForcingRaw_uniform_bound_positive_window
      p c hM hT ha hab hbT.le u₀ hsmall
        (theta := (1 / 2 : ℝ)) (zeta := (1 / 4 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hstrip U V hUwM hFD hwaveFlux
  have hrawCont : ∀ s ∈ Set.Icc a b,
      Continuous (paper5CanonicalGeneratorForcingRaw
        p c hM hT Traj U V s) := by
    intro s hs
    have hs0 : 0 < s := ha.trans_le hs.1
    have hsT : s < T := hs.2.trans_lt hbT
    have hF0 := paper5WeightedGeneratorForcing_continuous_of_classical_slices
      p (eta := (0 : ℝ)) hsol hs0 hsT hTW (hu2 s hs) (hv2 s hs) hU2 hV2
    apply hF0.congr
    intro x
    have hfactor := paper5CanonicalGeneratorForcingRaw_exp_eq_weighted
      (eta := (0 : ℝ)) (c := c) p hM hT Traj U V
        (hstripWindow s hs) x
    simpa only [zero_mul, Real.exp_zero, one_mul, u, v, Traj] using hfactor.symm
  have hholder : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x : ℝ,
      |s - t| ≤ 1 →
      |paper5CanonicalGeneratorForcingRaw p c hM hT Traj U V s x -
          paper5CanonicalGeneratorForcingRaw p c hM hT Traj U V t x| ≤
        H * |s - t| ^ alpha := by
    intro s hs t ht x hst
    have hraw := hholderRaw s hs t ht x (by simpa [abs_sub_comm] using hst)
    simpa only [Traj, abs_sub_comm] using hraw
  have hrawJoint : Measurable (Function.uncurry
      (paper5CanonicalGeneratorForcingRawPositiveWindowClamped
        p c hM hT Traj U V hab)) := by
    simpa only [paper5CanonicalGeneratorForcingRawPositiveWindowClamped] using
      (measurable_uncurry_projIcc_of_local_rpow_holder
        hab halpha hH (fun q hq => (hrawCont q hq).measurable) hholder)
  have hweightedJoint : Measurable (Function.uncurry
      (paper5WeightedGeneratorForcingPositiveWindowClamped
        p eta c hM hT Traj U V hab)) := by
    have hexp : Measurable (fun z : ℝ × ℝ => Real.exp (eta * z.2)) := by
      fun_prop
    exact hexp.mul hrawJoint
  refine ⟨alpha, H, D, halpha, halpha1, hH, hD, hrawCont, hholder,
    ?_, hrawJoint, hweightedJoint, ?_⟩
  · intro s hs x
    simpa only [Traj] using hrawBound s hs x
  · intro s hs x
    simp only [paper5WeightedGeneratorForcingPositiveWindowClamped,
      paper5CanonicalGeneratorForcingRawPositiveWindowClamped,
      Set.projIcc_of_mem hab hs]
    simpa only [u, v, Traj] using
      (paper5CanonicalGeneratorForcingRaw_exp_eq_weighted
        (eta := eta) (c := c) p hM hT Traj U V
          (hstripWindow s hs) x)

/-- Canonical pointwise data needed by the local exact-generator energy
consumer.  Besides the classical slices, this packages joint measurability
of the weighted population, slice measurability of the physical forcing,
and the ordinary material-time derivative at every point of the closed
positive window. -/
theorem wholeLineCauchyBUCMildFixedPoint_positive_window_pointwise_data
    (p : CMParams) {M T a b eta c : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V) :
    let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let u : ℝ → ℝ → ℝ := fun s x =>
      (wholeLineBUCTrajectoryExtend hT Traj s).1 x
    let v : ℝ → ℝ → ℝ := fun s => frozenElliptic p (u s)
    IsClassicalSolution p T u v ∧
      (∀ s ∈ Set.Icc a b, ∀ x,
        coMovingPath c u s x ∈ Set.Icc (0 : ℝ) M) ∧
      (∀ s ∈ Set.Icc a b, ContDiff ℝ 2 (coMovingPath c u s)) ∧
      (∀ s ∈ Set.Icc a b, ContDiff ℝ 2 (coMovingPath c v s)) ∧
      Measurable (Function.uncurry
        (paper5WeightedPopulation eta (coMovingPath c u) U)) ∧
      (∀ s ∈ Set.Icc a b,
        AEStronglyMeasurable
          (paper5WeightedPopulation eta (coMovingPath c u) U s) volume) ∧
      (∀ s ∈ Set.Icc a b,
        AEStronglyMeasurable
          (paper5WeightedGeneratorForcing p eta
            (coMovingPath c u) (coMovingPath c v) U V s) volume) ∧
      ∀ s ∈ Set.Icc a b, ∀ x,
        HasDerivAt
          (fun q => paper5WeightedPopulation eta (coMovingPath c u) U q x)
          (paper5WeightedPopulationT eta
            (paper5CoMovingMaterialTime c u) s x) s := by
  dsimp only
  let Traj : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let u : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend hT Traj s).1 x
  let v : ℝ → ℝ → ℝ := fun s => frozenElliptic p (u s)
  obtain ⟨hsol, huM, hu2, hv2⟩ :=
    wholeLineCauchyBUCMildFixedPoint_positive_window_slice_data
      (c := c) p hM hT ha hab hbT u₀ hsmall hstrip
  have hU2 : ContDiff ℝ 2 U := hreg.U_contDiff_two hTW
  have hV2 : ContDiff ℝ 2 V := hreg.V_contDiff_two hTW
  have hWjointCont : Continuous (fun z : ℝ × ℝ =>
      paper5WeightedPopulation eta (coMovingPath c u) U z.1 z.2) := by
    have heval : Continuous (fun q : WholeLineBUC × ℝ => q.1.1 q.2) := by
      fun_prop
    have hdynamic : Continuous (fun z : ℝ × ℝ =>
        (wholeLineBUCTrajectoryExtend hT Traj z.1).1
          (z.2 + c * z.1)) := by
      exact heval.comp (Continuous.prodMk
        ((wholeLineBUCTrajectoryExtend_continuous hT Traj).comp continuous_fst)
        (continuous_snd.add (continuous_const.mul continuous_fst)))
    have hwave : Continuous (fun z : ℝ × ℝ => U z.2) :=
      hreg.U_cont.comp continuous_snd
    have hexp : Continuous (fun z : ℝ × ℝ => Real.exp (eta * z.2)) := by
      fun_prop
    simpa only [paper5WeightedPopulation, coMovingPath, u] using
      hexp.mul (hdynamic.sub hwave)
  have hWjoint : Measurable (Function.uncurry
      (paper5WeightedPopulation eta (coMovingPath c u) U)) := by
    simpa only [Function.uncurry_apply_pair] using hWjointCont.measurable
  have hWmeas : ∀ s ∈ Set.Icc a b,
      AEStronglyMeasurable
        (paper5WeightedPopulation eta (coMovingPath c u) U s) volume := by
    intro s hs
    exact hWjoint.of_uncurry_left.aestronglyMeasurable
  have hFmeas : ∀ s ∈ Set.Icc a b,
      AEStronglyMeasurable
        (paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V s) volume := by
    intro s hs
    exact (paper5WeightedGeneratorForcing_continuous_of_classical_slices
      p hsol (ha.trans_le hs.1) (hs.2.trans_lt hbT) hTW
        (hu2 s hs) (hv2 s hs) hU2 hV2).aestronglyMeasurable
  have hpoint : ∀ s ∈ Set.Icc a b, ∀ x,
      HasDerivAt
        (fun q => paper5WeightedPopulation eta (coMovingPath c u) U q x)
        (paper5WeightedPopulationT eta
          (paper5CoMovingMaterialTime c u) s x) s := by
    intro s hs x
    have hs0 : 0 < s := ha.trans_le hs.1
    have hsT : s < T := hs.2.trans_lt hbT
    let zs : Set.Icc (0 : ℝ) T := ⟨s, hs0.le, hsT.le⟩
    have hjoint := wholeLineCauchyBUCMildFixedPoint_joint_hasFDerivAt_positive
      p hM hT u₀ hsmall zs hs0 hsT
        (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hstrip (x + c * s)
    apply paper5WeightedPopulation_time_hasDerivAt_of_joint
      (η := eta) (c := c) (u := u) (U := U)
    simpa only [u, Traj] using hjoint
  exact ⟨hsol, huM, hu2, hv2, hWjoint, hWmeas, hFmeas, hpoint⟩

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.measurable_uncurry_projIcc_of_local_rpow_holder
#print axioms
  ShenWork.Paper1.paper5WeightedGeneratorForcing_continuous_of_classical_slices
#print axioms
  ShenWork.Paper1.wholeLineCauchyBUCMildFixedPoint_positive_window_slice_data
#print axioms
  ShenWork.Paper1.exists_paper5CanonicalGeneratorForcingRaw_positive_window_natural_data
#print axioms
  ShenWork.Paper1.wholeLineCauchyBUCMildFixedPoint_positive_window_pointwise_data
