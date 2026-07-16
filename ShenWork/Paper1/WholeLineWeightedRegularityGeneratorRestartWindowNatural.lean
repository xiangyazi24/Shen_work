import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorRestartActual
import ShenWork.Paper1.WholeLineWeightedRegularitySemigroupHistoryNatural
import ShenWork.Paper1.WholeLineWeightedRegularityForcingContinuityNatural
import ShenWork.Paper1.WholeLineWeightedRegularityBoundedDriftRestart
import ShenWork.Paper1.WholeLineWeightedRegularityRawDQProfile

open Filter MeasureTheory Set Topology
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Natural positive-window generator restart

This file removes the artificial ambient forcing window, its numerical
forcing bound, every terminal heat-history measurability premise, and the
damped `Z + F` Bochner-integrability premise from the actual-state damping
removal theorem.  Continuity of the genuine exact-weight forcing supplies
all forcing histories.  Continuity of the actual state on the restart
window supplies the remaining damped history after clamping that state to
the window.

No spatial derivative of the state or forcing is used here.
-/

/-- Exponential conjugation of the undamped moving heat flow.  Unlike the
modified-semigroup identity, no residual `exp (-t)` factor remains. -/
theorem exp_mul_wholeLineDriftHeatOp_eq_weightedMovingHeatEta
    {eta c t : ℝ} (ht : 0 < t) (f : ℝ → ℝ) (x : ℝ) :
    Real.exp (eta * x) * wholeLineDriftHeatOp c t f x =
      weightedMovingHeatEta eta c t
        (fun y => Real.exp (eta * y) * f y) x := by
  have hbase := exp_mul_movingFrameHeatOp_eq_weightedMovingHeatEta
    ht f x (eta := eta) (c := c)
  unfold wholeLineDriftHeatOp wholeLineCauchyMovingHeatOp
  unfold paper5MovingFrameHeatOp at hbase
  rw [show Real.exp (eta * x) *
      (Real.exp t * wholeLineCauchyHeatOp t f (x + c * t)) =
      Real.exp t *
        (Real.exp (eta * x) *
          wholeLineCauchyHeatOp t f (x + c * t)) by ring,
    hbase]
  rw [← mul_assoc, ← Real.exp_add]
  simp

/-- The stationary wave satisfies an undamped moving-heat restart.  This is
the bounded-joint theorem applied to the constant-in-time wave orbit; the
source is kept as `-U_xx-c U_x`, so no differentiated nonlinear flux is
introduced. -/
theorem IsTravelingWave.stationary_drift_restart_identity
    (p : CMParams) {a b c x D E : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hab : a < b) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hUd : ∀ y, |deriv U y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv U) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv U))) :
    U x = wholeLineDriftHeatOp c (b - a) U x +
      ∫ s in a..b, wholeLineDriftHeatOp c (b - s)
        (fun y => -deriv (deriv U) y - c * deriv U y) x := by
  have hMChi : 0 ≤ MChi p :=
    (hbound.pos 0).le.trans (hbound.le_MChi 0)
  have hUbound : ∀ y, |U y| ≤ MChi p := by
    intro y
    rw [abs_of_pos (hbound.pos y)]
    exact hbound.le_MChi y
  let Ubuc : WholeLineBUC := wholeLineBUCOfUniformBound U
    (travelingWave_U_uniformContinuous hTW hreg.U_cont) (MChi p) hUbound
  let W : ℝ → WholeLineBUC := fun _ => Ubuc
  let Wt : ℝ → ℝ → ℝ := fun _ _ => 0
  let Wx : ℝ → ℝ → ℝ := fun _ y => deriv U y
  let Wxx : ℝ → ℝ → ℝ := fun _ y => deriv (deriv U) y
  have hleft : Tendsto W
      (nhdsWithin a (Set.Ioi a)) (nhds (W a)) := by
    exact tendsto_const_nhds
  have hright : Tendsto W (nhdsWithin b (Set.Iio b)) (nhds (W b)) := by
    exact tendsto_const_nhds
  have hWbound : ∀ r ∈ Set.Ioo a b, ∀ y,
      |(W r).1 y| ≤ MChi p := by
    intro r hr y
    simpa [W, Ubuc, wholeLineBUCOfUniformBound_apply] using hUbound y
  have hWtbound : ∀ r ∈ Set.Ioo a b, ∀ y,
      |Wt r y| ≤ 0 := by
    simp [Wt]
  have hWxbound : ∀ r ∈ Set.Ioo a b, ∀ y,
      |Wx r y| ≤ D := by
    intro r hr y
    exact hUd y
  have hWxxbound : ∀ r ∈ Set.Ioo a b, ∀ y,
      |Wxx r y| ≤ E := by
    intro r hr y
    exact hUdd y
  have hWtcont : ∀ r ∈ Set.Ioo a b, Continuous (Wt r) := by
    intro r hr
    exact continuous_const
  have hWxcont : ∀ r ∈ Set.Ioo a b, Continuous (Wx r) := by
    intro r hr
    simpa [Wx] using hreg.deriv_U_cont
  have hWxxcont : ∀ r ∈ Set.Ioo a b, Continuous (Wxx r) := by
    intro r hr
    simpa [Wxx] using hUddcont
  have hspace1 : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasDerivAt (W r).1 (Wx r y) y := by
    intro r hr y
    change HasDerivAt U (deriv U y) y
    exact (hreg.U_diff y).hasDerivAt
  have hspace2 : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasDerivAt (Wx r) (Wxx r y) y := by
    intro r hr y
    simpa [Wx, Wxx] using (hreg.deriv_U_diff y).hasDerivAt
  have hjoint : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasFDerivAt
        (fun q : ℝ × ℝ => (W q.1).1 q.2)
        (Wt r y • ContinuousLinearMap.fst ℝ ℝ ℝ +
          Wx r y • ContinuousLinearMap.snd ℝ ℝ ℝ)
        (r, y) := by
    intro r hr y
    have hsnd : HasFDerivAt (fun q : ℝ × ℝ => U q.2)
        (deriv U y • ContinuousLinearMap.snd ℝ ℝ ℝ) (r, y) :=
      (hreg.U_diff y).hasDerivAt.comp_hasFDerivAt (r, y)
        (hasFDerivAt_snd (𝕜 := ℝ) (p := (r, y)))
    change HasFDerivAt (fun q : ℝ × ℝ => U q.2)
      (0 • ContinuousLinearMap.fst ℝ ℝ ℝ +
        deriv U y • ContinuousLinearMap.snd ℝ ℝ ℝ) (r, y)
    simpa using hsnd
  have hraw := wholeLineDrift_restart_identity_of_bounded_joint_auto
    (a := a) (b := b) (d := c) (x := x)
    (W := W) (Wt := Wt) (Wx := Wx) (Wxx := Wxx)
    hab hleft hright hMChi (by norm_num) hD hE hWbound hWtbound
      hWxbound hWxxbound hWtcont hWxcont hWxxcont hspace1 hspace2 hjoint
  simpa [W, Wt, Wx, Wxx, Ubuc, wholeLineBUCOfUniformBound_apply]
    using hraw

/-- Canonical co-moving perturbation restart with the physical generator as
a value source.  The proof applies the bounded-joint drift theorem directly
to `u(t,x+ct)-U(x)`.  Thus no integration by parts in the nonlinear flux and
no weighted spatial derivative of the solution is used. -/
theorem wholeLineCauchyBUCMildFixedPoint_coMoving_wavePerturbation_drift_restart
    (p : CMParams) {M T a b theta zeta c D E : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a < b) (hbT : b < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (hrel : zeta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 y ∈
        Set.Icc (0 : ℝ) M)
    {Uw Vw : ℝ → ℝ}
    (hTW : IsTravelingWave p c Uw Vw)
    (hbound : HasWaveUpperTailBound p c Uw)
    (hreg : TravelingWaveRegularity p c Uw Vw)
    (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hUd : ∀ y, |deriv Uw y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv Uw) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv Uw))) (x : ℝ) :
    let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let Ext := wholeLineBUCTrajectoryExtend hT Traj
    (Ext b).1 (x + c * b) - Uw x =
      wholeLineDriftHeatOp c (b - a)
        (fun y => (Ext a).1 (y + c * a) - Uw y) x +
      ∫ s in a..b, wholeLineDriftHeatOp c (b - s)
        (paper5CanonicalGeneratorForcingRaw p c hM hT
          Traj Uw Vw s) x := by
  dsimp only
  let Traj : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let Ext : ℝ → WholeLineBUC := wholeLineBUCTrajectoryExtend hT Traj
  let Ec : ℝ → WholeLineBUC := fun r =>
    wholeLineBUCTranslate (c * r) (Ext r)
  have hMChi : 0 ≤ MChi p :=
    (hbound.pos 0).le.trans (hbound.le_MChi 0)
  have hUwBound : ∀ y, |Uw y| ≤ MChi p := by
    intro y
    rw [abs_of_pos (hbound.pos y)]
    exact hbound.le_MChi y
  let UwBUC : WholeLineBUC := wholeLineBUCOfUniformBound Uw
    (travelingWave_U_uniformContinuous hTW hreg.U_cont) (MChi p) hUwBound
  let W : ℝ → WholeLineBUC := fun r =>
    wholeLineBUCPointwiseSub (Ec r) UwBUC
  let e : ℝ → ℝ → ℝ := fun r y => (Ext r).1 y
  let Wt : ℝ → ℝ → ℝ := fun r y =>
    paper5CoMovingMaterialTime c e r y
  let Wx : ℝ → ℝ → ℝ := fun r y =>
    deriv (e r) (y + c * r) - deriv Uw y
  let Wxx : ℝ → ℝ → ℝ := fun r y =>
    deriv (deriv (e r)) (y + c * r) - deriv (deriv Uw) y
  let Flux : ℝ → WholeLineBUC :=
    wholeLineCauchyFluxSourceTrajectory p hM hT Traj
  let React : ℝ → WholeLineBUC :=
    wholeLineCauchyReactionSourceTrajectory p hM hT Traj
  have hstripHalf : ∀ s ∈ Set.Icc (a / 2) b, ∀ y,
      (Ext s).1 y ∈ Set.Icc (0 : ℝ) M := by
    intro s hs y
    have hs0 : 0 ≤ s := (half_pos ha).le.trans hs.1
    have hsT : s ≤ T := hs.2.trans hbT.le
    let zs : Set.Icc (0 : ℝ) T := ⟨s, hs0, hsT⟩
    rw [show Ext s = Traj zs by
      exact wholeLineBUCTrajectoryExtend_eq hT Traj zs.2]
    exact hstrip zs y
  have hstripWindow : ∀ s ∈ Set.Icc a b, ∀ y,
      (Ext s).1 y ∈ Set.Icc (0 : ℝ) M := by
    intro s hs y
    exact hstripHalf s
      ⟨(div_le_self ha.le (by norm_num)).trans hs.1, hs.2⟩ y
  rcases wholeLineCauchyBUCMildFixedPoint_spatial_deriv_bounded_positive_window
      p hM hT ha hab.le hbT.le u₀ hsmall htheta0 htheta1
        hzeta0 hzeta1 hrel (by simpa [Ext, Traj] using hstripWindow) with
    ⟨Bx, hBx, hxBound⟩
  rcases wholeLineCauchyBUCMildFixedPoint_spatial_second_bounded_positive_window
      p hM hT ha hab.le hbT.le u₀ hsmall htheta0 htheta1
        hzeta0 hzeta1 hrel (by simpa [Ext, Traj] using hstripHalf) with
    ⟨Bxx, hBxx, hxxBound⟩
  rcases wholeLineCauchyBUCMildFixedPoint_time_deriv_bounded_positive_window
      p hM hT ha hab.le hbT u₀ hsmall htheta0 htheta1
        hzeta0 hzeta1 hrel hstrip with
    ⟨Bt, hBt, htBound⟩
  rcases wholeLineCauchyFluxSourceTrajectory_deriv_holder_positive_window
      p hM hT ha hab.le hbT.le u₀ hsmall htheta0 htheta1
        hzeta0 hzeta1 hrel (by simpa [Ext, Traj] using hstripWindow) with
    ⟨rho, HF, hrho, _hrho1, hHF, hfluxHolder⟩
  have hExtcont : Continuous Ext := by
    simpa [Ext] using wholeLineBUCTrajectoryExtend_continuous hT Traj
  have hEccont : Continuous Ec := by
    exact wholeLineBUCTranslate_joint_continuous.comp
      ((continuous_const.mul continuous_id).prodMk hExtcont)
  have hWcont : Continuous W := by
    rw [← continuousOn_univ]
    exact wholeLineBUCPointwiseSub_continuousOn
      hEccont.continuousOn continuous_const.continuousOn
  have hWleft : Tendsto W (nhdsWithin a (Set.Ioi a)) (nhds (W a)) :=
    hWcont.continuousAt.mono_left nhdsWithin_le_nhds
  have hWright : Tendsto W (nhdsWithin b (Set.Iio b)) (nhds (W b)) :=
    hWcont.continuousAt.mono_left nhdsWithin_le_nhds
  have hvalue : ∀ r ∈ Set.Ioo a b, ∀ y,
      |(W r).1 y| ≤ M + MChi p := by
    intro r hr y
    have hdyn := hstripWindow r ⟨hr.1.le, hr.2.le⟩ (y + c * r)
    change |(Ext r).1 (y + c * r) - Uw y| ≤ M + MChi p
    exact (abs_sub _ _).trans
      (add_le_add (by simpa [abs_of_nonneg hdyn.1] using hdyn.2) (hUwBound y))
  have htbound : ∀ r ∈ Set.Ioo a b, ∀ y,
      |Wt r y| ≤ Bt + |c| * Bx := by
    intro r hr y
    have ht := htBound r ⟨hr.1.le, hr.2.le⟩ (y + c * r)
    have hx := hxBound r ⟨hr.1.le, hr.2.le⟩ (y + c * r)
    unfold Wt paper5CoMovingMaterialTime coMovingPath
    rw [deriv_comp_add_const]
    calc
      |deriv (fun s => e s (y + c * r)) r +
          c * deriv (e r) (y + c * r)| ≤
          |deriv (fun s => e s (y + c * r)) r| +
            |c| * |deriv (e r) (y + c * r)| := by
              simpa only [abs_mul] using
                abs_add_le
                  (deriv (fun s => e s (y + c * r)) r)
                  (c * deriv (e r) (y + c * r))
      _ ≤ Bt + |c| * Bx := by
        exact add_le_add (by simpa [e, Ext, Traj] using ht)
          (mul_le_mul_of_nonneg_left
            (by simpa [e, Ext, Traj] using hx) (abs_nonneg c))
  have hxbound : ∀ r ∈ Set.Ioo a b, ∀ y,
      |Wx r y| ≤ Bx + D := by
    intro r hr y
    exact (abs_sub _ _).trans (add_le_add
      (by simpa [Wx, e, Ext, Traj] using
        hxBound r ⟨hr.1.le, hr.2.le⟩ (y + c * r)) (hUd y))
  have hxxbound : ∀ r ∈ Set.Ioo a b, ∀ y,
      |Wxx r y| ≤ Bxx + E := by
    intro r hr y
    exact (abs_sub _ _).trans (add_le_add
      (by simpa [Wxx, e, Ext, Traj] using
        hxxBound r ⟨hr.1.le, hr.2.le⟩ (y + c * r)) (hUdd y))
  have hspace1 : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasDerivAt (W r).1 (Wx r y) y := by
    intro r hr y
    let zr : Set.Icc (0 : ℝ) T :=
      ⟨r, (ha.trans hr.1).le, (hr.2.trans hbT).le⟩
    have hext : Ext r = Traj zr :=
      wholeLineBUCTrajectoryExtend_eq hT Traj zr.2
    have hs := wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
      p hM hT u₀ hsmall zr (ha.trans hr.1) (y + c * r)
    have hs' : HasDerivAt (e r)
        (deriv (e r) (y + c * r)) (y + c * r) := by
      simpa [e, Ext, Traj, hext] using
        hs.differentiableAt.hasDerivAt
    have hshift : HasDerivAt (fun z : ℝ => e r (z + c * r))
        (deriv (e r) (y + c * r)) y := by
      simpa [Function.comp_def] using
        hs'.comp y ((hasDerivAt_id y).add_const (c * r))
    have hwave := (hreg.U_diff y).hasDerivAt
    change HasDerivAt (fun z => e r (z + c * r) - Uw z)
      (deriv (e r) (y + c * r) - deriv Uw y) y
    exact hshift.sub hwave
  have hspace2 : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasDerivAt (Wx r) (Wxx r y) y := by
    intro r hr y
    let zr : Set.Icc (0 : ℝ) T :=
      ⟨r, (ha.trans hr.1).le, (hr.2.trans hbT).le⟩
    have hext : Ext r = Traj zr :=
      wholeLineBUCTrajectoryExtend_eq hT Traj zr.2
    have hstripR : ∀ s ∈ Set.Icc (r / 2) r, ∀ q,
        (Ext s).1 q ∈ Set.Icc (0 : ℝ) M := by
      intro s hs q
      have hs0 : 0 ≤ s := (half_pos (ha.trans hr.1)).le.trans hs.1
      have hsT : s ≤ T := hs.2.trans (hr.2.trans hbT).le
      let zs : Set.Icc (0 : ℝ) T := ⟨s, hs0, hsT⟩
      rw [show Ext s = Traj zs by
        exact wholeLineBUCTrajectoryExtend_eq hT Traj zs.2]
      exact hstrip zs q
    have hs :=
      wholeLineCauchyBUCMildFixedPoint_spatial_second_hasDerivAt_positive
        p hM hT u₀ hsmall zr (ha.trans hr.1) htheta0 htheta1
          hzeta0 hzeta1 hrel (by simpa [Ext, Traj] using hstripR)
          (y + c * r)
    have hs' : HasDerivAt (deriv (e r))
        (deriv (deriv (e r)) (y + c * r)) (y + c * r) := by
      simpa [e, Ext, Traj, hext] using
        hs.differentiableAt.hasDerivAt
    have hshift : HasDerivAt
        (fun z : ℝ => deriv (e r) (z + c * r))
        (deriv (deriv (e r)) (y + c * r)) y := by
      simpa [Function.comp_def] using
        hs'.comp y ((hasDerivAt_id y).add_const (c * r))
    have hwave := (hreg.deriv_U_diff y).hasDerivAt
    change HasDerivAt
      (fun z => deriv (e r) (z + c * r) - deriv Uw z)
      (deriv (deriv (e r)) (y + c * r) - deriv (deriv Uw) y) y
    exact hshift.sub hwave
  have hxcont : ∀ r ∈ Set.Ioo a b, Continuous (Wx r) := by
    intro r hr
    rw [continuous_iff_continuousAt]
    intro y
    exact (hspace2 r hr y).continuousAt
  have hxxcont : ∀ r ∈ Set.Ioo a b, Continuous (Wxx r) := by
    intro r hr
    let zr : Set.Icc (0 : ℝ) T :=
      ⟨r, (ha.trans hr.1).le, (hr.2.trans hbT).le⟩
    have hext : Ext r = Traj zr :=
      wholeLineBUCTrajectoryExtend_eq hT Traj zr.2
    have hstripR : ∀ s ∈ Set.Icc (r / 2) r, ∀ q,
        (Ext s).1 q ∈ Set.Icc (0 : ℝ) M := by
      intro s hs q
      have hs0 : 0 ≤ s := (half_pos (ha.trans hr.1)).le.trans hs.1
      have hsT : s ≤ T := hs.2.trans (hr.2.trans hbT).le
      let zs : Set.Icc (0 : ℝ) T := ⟨s, hs0, hsT⟩
      rw [show Ext s = Traj zs by
        exact wholeLineBUCTrajectoryExtend_eq hT Traj zs.2]
      exact hstrip zs q
    have hc := wholeLineCauchyBUCMildFixedPoint_spatial_second_continuous_positive
      p hM hT u₀ hsmall zr (ha.trans hr.1) htheta0 htheta1
        hzeta0 hzeta1 hrel (by simpa [Ext, Traj] using hstripR)
    have hcanonXX : Continuous (deriv (deriv (e r))) := by
      simpa [e, Ext, hext] using hc
    exact (hcanonXX.comp
      (continuous_id.add continuous_const)).sub hUddcont
  have htcont : ∀ r ∈ Set.Ioo a b, Continuous (Wt r) := by
    intro r hr
    have hfluxCont : Continuous (fun y => deriv (Flux r).1 y) :=
      wholeLineContinuous_of_holder hrho hHF
        (fun y q => hfluxHolder r ⟨hr.1.le, hr.2.le⟩ y q)
    have hcanonXX : Continuous (deriv (deriv (e r))) := by
      let zr : Set.Icc (0 : ℝ) T :=
        ⟨r, (ha.trans hr.1).le, (hr.2.trans hbT).le⟩
      have hext : Ext r = Traj zr :=
        wholeLineBUCTrajectoryExtend_eq hT Traj zr.2
      have hstripR : ∀ s ∈ Set.Icc (r / 2) r, ∀ q,
          (Ext s).1 q ∈ Set.Icc (0 : ℝ) M := by
        intro s hs q
        have hs0 : 0 ≤ s := (half_pos (ha.trans hr.1)).le.trans hs.1
        have hsT : s ≤ T := hs.2.trans (hr.2.trans hbT).le
        let zs : Set.Icc (0 : ℝ) T := ⟨s, hs0, hsT⟩
        rw [show Ext s = Traj zs by
          exact wholeLineBUCTrajectoryExtend_eq hT Traj zs.2]
        exact hstrip zs q
      have hc := wholeLineCauchyBUCMildFixedPoint_spatial_second_continuous_positive
        p hM hT u₀ hsmall zr (ha.trans hr.1) htheta0 htheta1
          hzeta0 hzeta1 hrel (by simpa [Ext, Traj] using hstripR)
      simpa [e, Ext, hext] using hc
    have hformula : Wt r = fun y =>
        deriv (deriv (e r)) (y + c * r) - e r (y + c * r) +
          (-p.χ) * deriv (Flux r).1 (y + c * r) +
          (React r).1 (y + c * r) +
          c * deriv (e r) (y + c * r) := by
      funext y
      have htderiv :=
        wholeLineCauchyBUCMildFixedPoint_time_hasDerivAt_positive
          p hM hT u₀ hsmall (ha.trans hr.1) (hr.2.trans hbT)
            htheta0 htheta1 hzeta0 hzeta1 hrel hstrip (y + c * r)
      have heq := htderiv.deriv
      unfold Wt paper5CoMovingMaterialTime coMovingPath
      rw [deriv_comp_add_const]
      have heq' : deriv (fun s => e s (y + c * r)) r =
          deriv (deriv (e r)) (y + c * r) - e r (y + c * r) +
            (-p.χ) * deriv (Flux r).1 (y + c * r) +
            (React r).1 (y + c * r) := by
        simpa [e, Ext, Traj, Flux, React] using heq
      rw [heq']
    rw [hformula]
    have hcanonXShift : Continuous
        (fun y => deriv (e r) (y + c * r)) := by
      have hsum := (hxcont r hr).add hreg.deriv_U_cont
      have heq : (fun y => deriv (e r) (y + c * r)) =
          Wx r + deriv Uw := by
        funext y
        simp only [Pi.add_apply, Wx, sub_add_cancel]
      rw [heq]
      exact hsum
    have hshift : Continuous (fun y : ℝ => y + c * r) :=
      continuous_id.add continuous_const
    exact ((((hcanonXX.comp hshift).sub
      ((Ext r).1.continuous.comp hshift)).add
      (continuous_const.mul (hfluxCont.comp hshift))).add
      ((React r).1.continuous.comp hshift)).add
      (continuous_const.mul hcanonXShift)
  have hjoint : ∀ r ∈ Set.Ioo a b, ∀ y,
      HasFDerivAt
        (fun q : ℝ × ℝ => (W q.1).1 q.2)
        (Wt r y • ContinuousLinearMap.fst ℝ ℝ ℝ +
          Wx r y • ContinuousLinearMap.snd ℝ ℝ ℝ)
        (r, y) := by
    intro r hr y
    let zr : Set.Icc (0 : ℝ) T :=
      ⟨r, (ha.trans hr.1).le, (hr.2.trans hbT).le⟩
    have hcjoint := wholeLineCauchyBUCMildFixedPoint_joint_hasFDerivAt_positive
      p hM hT u₀ hsmall zr (ha.trans hr.1) (hr.2.trans hbT)
        htheta0 htheta1 hzeta0 hzeta1 hrel hstrip (y + c * r)
    have htimeCore := paper5CoMovingPath_hasDerivAt_of_joint
      (c := c) (t := r) (x := y) (u := e) (by
        simpa [e, Ext, Traj] using hcjoint)
    have htime : HasDerivAt (fun s => (W s).1 y) (Wt r y) r := by
      have hsub := htimeCore.sub_const (Uw y)
      simpa [W, Ec, UwBUC, e, Wt, coMovingPath,
        wholeLineBUCOfUniformBound_apply] using hsub
    have hspace : ∀ᶠ s in nhds r, ∀ z,
        HasDerivAt (W s).1 (Wx s z) z := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
      exact hspace1 s hs
    have hcanonDx :=
      wholeLineCauchyBUCMildFixedPoint_spatial_deriv_jointContinuousAt_positive
        p hM hT u₀ hsmall zr (ha.trans hr.1) (hr.2.trans hbT)
          htheta0 htheta1 hzeta0 hzeta1 hrel (y + c * r)
    have hphi : ContinuousAt (fun q : ℝ × ℝ =>
        (q.1, q.2 + c * q.1)) (r, y) := by fun_prop
    have hfx : ContinuousAt (fun q : ℝ × ℝ => Wx q.1 q.2)
        (r, y) := by
      have hcanonShift := hcanonDx.comp
        (f := fun q : ℝ × ℝ => (q.1, q.2 + c * q.1)) hphi
      have hwaveShift : ContinuousAt
          (fun q : ℝ × ℝ => deriv Uw q.2) (r, y) :=
        (hreg.deriv_U_cont.comp continuous_snd).continuousAt
      simpa only [Wx, Function.comp_apply] using hcanonShift.sub hwaveShift
    exact hasFDerivAt_prod_of_time_slice_of_spatial_continuousAt
      htime hspace hfx
  have hrestart := wholeLineDrift_restart_identity_of_bounded_joint_auto
    (a := a) (b := b) (d := c) (x := x)
    (W := W) (Wt := Wt) (Wx := Wx) (Wxx := Wxx)
    hab hWleft hWright (add_nonneg hM hMChi) (add_nonneg hBt
      (mul_nonneg (abs_nonneg c) hBx)) (add_nonneg hBx hD)
      (add_nonneg hBxx hE)
      hvalue htbound hxbound hxxbound htcont hxcont hxxcont
      hspace1 hspace2 hjoint
  have hsource : ∀ s ∈ Set.Ioo a b, ∀ y,
      Wt s y - Wxx s y - c * Wx s y =
        paper5CanonicalGeneratorForcingRaw p c hM hT
          Traj Uw Vw s y := by
    intro s hs y
    have htderiv := wholeLineCauchyBUCMildFixedPoint_time_hasDerivAt_positive
      p hM hT u₀ hsmall (ha.trans hs.1) (hs.2.trans hbT)
        htheta0 htheta1 hzeta0 hzeta1 hrel hstrip (y + c * s)
    have htimeEq : deriv (fun r => e r (y + c * s)) s =
        deriv (deriv (e s)) (y + c * s) - e s (y + c * s) +
          (-p.χ) * deriv (Flux s).1 (y + c * s) +
          (React s).1 (y + c * s) := by
      simpa [e, Ext, Traj, Flux, React] using htderiv.deriv
    have hreactEq : (React s).1 (y + c * s) =
        e s (y + c * s) + reactionFun p.α (e s (y + c * s)) := by
      have hraw := congrFun
        (wholeLineCauchyCoMovingReactionSource_eq_genuineReaction_of_strip
          p c hM hT Traj hstrip s) y
      simpa [React, e, Ext, wholeLineCauchyCoMovingReactionSource,
        wholeLineCauchyShiftedReaction, wholeLineLogisticSource] using hraw
    have hwave := wholeLineTravelingWave_movingGenerator_balance
      p hTW (x := y)
    have hwaveEq : deriv (deriv Uw) y + c * deriv Uw y =
        p.χ * deriv (fun z => Uw z ^ p.m * deriv Vw z) y -
          reactionFun p.α (Uw y) := by
      unfold wholeLineTravelingWaveShiftedSource wholeLineTravelingWaveFlux
        wholeLineCauchyShiftedReaction wholeLineLogisticSource at hwave
      linarith
    unfold Wt paper5CoMovingMaterialTime coMovingPath Wxx Wx
    rw [deriv_comp_add_const, htimeEq, hreactEq]
    unfold paper5CanonicalGeneratorForcingRaw
    linarith [hwaveEq]
  have hintegral :
      (∫ s in a..b, wholeLineDriftHeatOp c (b - s)
          (fun y => Wt s y - Wxx s y - c * Wx s y) x) =
        ∫ s in a..b, wholeLineDriftHeatOp c (b - s)
          (paper5CanonicalGeneratorForcingRaw p c hM hT
            Traj Uw Vw s) x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume a, Measure.ae_ne volume b]
      with s hsa hsb hsI
    rw [Set.uIoc_of_le hab.le] at hsI
    have hs : s ∈ Set.Ioo a b :=
      ⟨hsI.1, lt_of_le_of_ne hsI.2 hsb⟩
    rw [show (fun y => Wt s y - Wxx s y - c * Wx s y) =
        paper5CanonicalGeneratorForcingRaw p c hM hT Traj Uw Vw s by
      funext y
      exact hsource s hs y]
  rw [hintegral] at hrestart
  simpa [W, Ec, UwBUC, e, Ext, Traj,
    wholeLineBUCOfUniformBound_apply] using hrestart

/-- Exponential conjugation of the canonical co-moving drift restart gives
the exact-weight full-generator restart.  The source is the physical
chemotaxis/reaction forcing itself; no damping term and no differentiated
weighted flux are introduced. -/
theorem wholeLineCauchyBUCMildFixedPoint_weighted_generator_restart
    (p : CMParams) {M T a b theta zeta eta c D E : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a < b) (hbT : b < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (hrel : zeta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 y ∈
        Set.Icc (0 : ℝ) M)
    {Uw Vw : ℝ → ℝ}
    (hTW : IsTravelingWave p c Uw Vw)
    (hbound : HasWaveUpperTailBound p c Uw)
    (hreg : TravelingWaveRegularity p c Uw Vw)
    (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hUd : ∀ y, |deriv Uw y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv Uw) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv Uw))) (x : ℝ) :
    let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let u : ℝ → ℝ → ℝ := fun s y =>
      (wholeLineBUCTrajectoryExtend hT Traj s).1 y
    let v : ℝ → ℝ → ℝ := fun s => frozenElliptic p (u s)
    paper5WeightedPopulation eta (coMovingPath c u) Uw b x =
      weightedMovingHeatEta eta c (b - a)
          (paper5WeightedPopulation eta (coMovingPath c u) Uw a) x +
        ∫ s in a..b, weightedMovingHeatEta eta c (b - s)
          (paper5WeightedGeneratorForcing p eta
            (coMovingPath c u) (coMovingPath c v) Uw Vw s) x := by
  dsimp only
  let Traj : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let Ext : ℝ → WholeLineBUC := wholeLineBUCTrajectoryExtend hT Traj
  let u : ℝ → ℝ → ℝ := fun s y => (Ext s).1 y
  let v : ℝ → ℝ → ℝ := fun s => frozenElliptic p (u s)
  have hraw :=
    wholeLineCauchyBUCMildFixedPoint_coMoving_wavePerturbation_drift_restart
      p hM hT ha hab hbT u₀ hsmall htheta0 htheta1 hzeta0 hzeta1 hrel
        hstrip hTW hbound hreg hD hE hUd hUdd hUddcont x
  have hhom := exp_mul_wholeLineDriftHeatOp_eq_weightedMovingHeatEta
    (eta := eta) (c := c) (t := b - a) (sub_pos.mpr hab)
      (fun y => (Ext a).1 (y + c * a) - Uw y) x
  change Real.exp (eta * x) * ((Ext b).1 (x + c * b) - Uw x) = _
  rw [show (Ext b).1 (x + c * b) - Uw x =
      wholeLineDriftHeatOp c (b - a)
          (fun y => (Ext a).1 (y + c * a) - Uw y) x +
        ∫ s in a..b, wholeLineDriftHeatOp c (b - s)
          (paper5CanonicalGeneratorForcingRaw p c hM hT
            Traj Uw Vw s) x by
      simpa [Traj, Ext] using hraw,
    mul_add, hhom]
  change weightedMovingHeatEta eta c (b - a)
      (paper5WeightedPopulation eta (coMovingPath c u) Uw a) x +
      Real.exp (eta * x) *
        ∫ s in a..b, wholeLineDriftHeatOp c (b - s)
          (paper5CanonicalGeneratorForcingRaw p c hM hT
            Traj Uw Vw s) x = _
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume b] with s hsb hsI
  rw [Set.uIoc_of_le hab.le] at hsI
  have hsb' : s < b := lt_of_le_of_ne hsI.2 hsb
  have hs0 : 0 ≤ s := ha.le.trans hsI.1.le
  have hsT : s ≤ T := hsI.2.trans hbT.le
  let zs : Set.Icc (0 : ℝ) T := ⟨s, hs0, hsT⟩
  have hstripS : ∀ y, (Ext s).1 y ∈ Set.Icc (0 : ℝ) M := by
    intro y
    rw [show Ext s = Traj zs by
      exact wholeLineBUCTrajectoryExtend_eq hT Traj zs.2]
    exact hstrip zs y
  have hconj := exp_mul_wholeLineDriftHeatOp_eq_weightedMovingHeatEta
    (eta := eta) (c := c) (t := b - s) (sub_pos.mpr hsb')
      (paper5CanonicalGeneratorForcingRaw p c hM hT Traj Uw Vw s) x
  rw [hconj]
  congr 2
  funext y
  simpa [u, v, Ext, Traj] using
    (paper5CanonicalGeneratorForcingRaw_exp_eq_weighted
      (eta := eta) (c := c) (s := s)
      p hM hT Traj Uw Vw hstripS y)

/-- Joint measurability of a scalar source gives joint measurability of its
moving weighted-heat history.  This is the only measurability input needed
by the local Fubini step; the Gaussian convolution is assembled here. -/
theorem weightedMovingHeatEta_history_aestronglyMeasurable_of_joint_measurable
    {eta c tau : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) :
    StronglyMeasurable
      (fun z : ℝ × ℝ =>
        weightedMovingHeatEta eta c (tau - z.1) (f z.1) z.2) := by
  let raw : (ℝ × ℝ) × ℝ → ℝ := fun z =>
    weightedMovingHeatMarkovKernel eta c (tau - z.1.1) z.1.2 z.2 *
      f z.1.1 z.2
  have hraw : StronglyMeasurable raw := by
    apply Measurable.stronglyMeasurable
    dsimp only [raw, weightedMovingHeatMarkovKernel, heatKernel]
    fun_prop
  have hint : StronglyMeasurable
      (fun z : ℝ × ℝ => ∫ y : ℝ, raw (z, y)) :=
    hraw.integral_prod_right'
  have hgrowth : Continuous (fun z : ℝ × ℝ =>
      weightedMovingHeatGrowth eta c (tau - z.1)) := by
    dsimp only [weightedMovingHeatGrowth]
    fun_prop
  have hprod := hgrowth.stronglyMeasurable.mul hint
  simpa only [raw, weightedMovingHeatEta] using hprod

/-- A continuous forcing and a state continuous on one compact restart
window automatically supply the damped `Z + F` histories used by the
pointwise-to-`L²` restart lift. -/
theorem weightedMovingHeat_actualState_damped_history_intervalIntegrable_of_continuous
    {eta c a r : ℝ} (har : a ≤ r)
    {Z F : ℝ → WholeLineRealL2}
    (hZ : ContinuousOn Z (Set.Icc a r))
    (hF : Continuous F) :
    ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q))
      volume a t := by
  let Zc : ℝ → WholeLineRealL2 := fun q =>
    Z (Set.projIcc a r har q)
  let G : ℝ → WholeLineRealL2 := fun q => Zc q + F q
  have hZc : Continuous Zc := by
    exact hZ.comp_continuous
      (continuous_subtype_val.comp continuous_projIcc)
      (fun q => (Set.projIcc a r har q).property)
  have hG : Continuous G := hZc.add hF
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hG.continuousOn.norm
  let K : ℝ := max B 0
  have hK : 0 ≤ K := le_max_right _ _
  have hGbound : ∀ q ∈ Set.Icc a r, ‖G q‖ ≤ K := by
    intro q hq
    exact (hB (Set.mem_image_of_mem _ hq)).trans (le_max_left _ _)
  intro t ht
  have hhist : AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (G q))
      (volume.restrict (Set.Icc a t)) :=
    (weightedMovingHeatL2Semigroup_terminal_history_aestronglyMeasurable
      (eta := eta) (c := c) (tau := t) hG).mono_measure
        Measure.restrict_le_self
  have hGI : ∀ q ∈ Set.Icc a t, ‖G q‖ ≤ K := by
    intro q hq
    exact hGbound q ⟨hq.1, hq.2.trans ht.2⟩
  have hraw :=
    (weightedMovingHeat_damped_histories_intervalIntegrable_of_uniform_norm_bound
      (eta := eta) (c := c) ht.1 hK hGI hhist).1
  apply hraw.congr
  intro q hq
  have hqIcc : q ∈ Set.Icc a r := by
    rw [Set.uIoc_of_le ht.1] at hq
    exact ⟨hq.1.le, hq.2.trans ht.2⟩
  have hproj : ((Set.projIcc a r har q : Set.Icc a r) : ℝ) = q := by
    simpa using congrArg Subtype.val (Set.projIcc_of_mem har hqIcc)
  simp only [G, Zc, hproj]

/-- Local scalar Fubini data are automatic when both scalar summands have
continuous `L²` realizations and their sum is jointly measurable.  The
damping is absorbed into the source before applying the uniform-square
history theorem, so no product-space domination premise remains. -/
theorem weightedMovingHeatEta_damped_history_local_prod_integrable_of_continuous_representatives
    {eta c a r : ℝ} (har : a ≤ r)
    {z f : ℝ → ℝ → ℝ} {Z F : ℝ → WholeLineRealL2}
    (hz_meas : ∀ q ∈ Set.Icc a r, AEStronglyMeasurable (z q) volume)
    (hz_sq : ∀ q ∈ Set.Icc a r,
      Integrable (fun x : ℝ => z q x ^ 2) volume)
    (hf_meas : ∀ q ∈ Set.Icc a r, AEStronglyMeasurable (f q) volume)
    (hf_sq : ∀ q ∈ Set.Icc a r,
      Integrable (fun x : ℝ => f q x ^ 2) volume)
    (hZrep : ∀ q ∈ Set.Icc a r,
      (((Z q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] z q))
    (hFrep : ∀ q ∈ Set.Icc a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q))
    (hZcont : ContinuousOn Z (Set.Icc a r))
    (hFcont : Continuous F)
    (hjoint : Measurable (Function.uncurry (fun q x => z q x + f q x))) :
    ∀ t ∈ Set.Ioc a r, ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun w : ℝ × ℝ => A.indicator
          (fun x => Real.exp (-(t - w.1)) *
            weightedMovingHeatEta eta c (t - w.1)
              (fun y => z w.1 y + f w.1 y) x) w.2)
        ((volume.restrict (Set.Ioc a t)).prod volume) := by
  let Zc : ℝ → WholeLineRealL2 := fun q =>
    Z (Set.projIcc a r har q)
  let G : ℝ → WholeLineRealL2 := fun q => Zc q + F q
  have hZc : Continuous Zc := by
    exact hZcont.comp_continuous
      (continuous_subtype_val.comp continuous_projIcc)
      (fun q => (Set.projIcc a r har q).property)
  have hG : Continuous G := hZc.add hFcont
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hG.continuousOn.norm
  let K : ℝ := max B 0
  have hK : 0 ≤ K := le_max_right _ _
  have hGbound : ∀ q ∈ Set.Icc a r, ‖G q‖ ≤ K := by
    intro q hq
    exact (hB (Set.mem_image_of_mem _ hq)).trans (le_max_left _ _)
  let g : ℝ → ℝ → ℝ := fun q x => z q x + f q x
  have hg_meas : ∀ q ∈ Set.Icc a r, AEStronglyMeasurable (g q) volume := by
    intro q hq
    exact (hz_meas q hq).add (hf_meas q hq)
  have hg_sq : ∀ q ∈ Set.Icc a r,
      Integrable (fun x : ℝ => g q x ^ 2) volume := by
    intro q hq
    have hzLp : MemLp (z q) 2 volume :=
      (memLp_two_iff_integrable_sq (hz_meas q hq)).2 (hz_sq q hq)
    have hfLp : MemLp (f q) 2 volume :=
      (memLp_two_iff_integrable_sq (hf_meas q hq)).2 (hf_sq q hq)
    exact (memLp_two_iff_integrable_sq (hg_meas q hq)).1 (hzLp.add hfLp)
  have htotal : ∀ q ∈ Set.Icc a r,
      wholeLineRealL2Total (g q) = Z q + F q := by
    intro q hq
    apply Lp.ext
    filter_upwards [wholeLineRealL2Total_coe_ae _ (hg_meas q hq)
        (hg_sq q hq), Lp.coeFn_add (Z q) (F q), hZrep q hq, hFrep q hq]
      with x htotalx hadd hxz hxf
    rw [htotalx, hadd]
    simp only [Pi.add_apply]
    rw [hxz, hxf]
  have hg_le : ∀ q ∈ Set.Icc a r,
      (∫ x : ℝ, g q x ^ 2) ≤ K ^ 2 := by
    intro q hq
    rw [← wholeLineRealL2Total_norm_sq_eq_integral
      (hg_meas q hq) (hg_sq q hq), htotal q hq]
    have hproj : ((Set.projIcc a r har q : Set.Icc a r) : ℝ) = q := by
      simpa using congrArg Subtype.val (Set.projIcc_of_mem har hq)
    have hnorm : ‖Z q + F q‖ ≤ K := by
      simpa only [G, Zc, hproj] using hGbound q hq
    exact (sq_le_sq₀ (norm_nonneg _) hK).2 hnorm
  intro t ht A hA hAfin
  let gt : ℝ → ℝ → ℝ := fun q x => Real.exp (-(t - q)) * g q x
  let Gt : ℝ → WholeLineRealL2 := fun q =>
    Real.exp (-(t - q)) • G q
  have hGt : Continuous Gt := by
    exact (by fun_prop : Continuous (fun q : ℝ => Real.exp (-(t - q)))).smul hG
  have hgt_meas : ∀ q ∈ Set.Icc a t,
      AEStronglyMeasurable (gt q) volume := by
    intro q hq
    exact (hg_meas q ⟨hq.1, hq.2.trans ht.2⟩).const_mul _
  have hgt_sq : ∀ q ∈ Set.Icc a t,
      Integrable (fun x : ℝ => gt q x ^ 2) volume := by
    intro q hq
    have hbase := hg_sq q ⟨hq.1, hq.2.trans ht.2⟩
    simpa only [gt, mul_pow] using hbase.const_mul (Real.exp (-(t - q)) ^ 2)
  have hgt_le : ∀ q ∈ Set.Icc a t,
      (∫ x : ℝ, gt q x ^ 2) ≤ K ^ 2 := by
    intro q hq
    have hqR : q ∈ Set.Icc a r := ⟨hq.1, hq.2.trans ht.2⟩
    have hexp : Real.exp (-(t - q)) ^ 2 ≤ 1 := by
      have he : Real.exp (-(t - q)) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (neg_nonpos.mpr (sub_nonneg.mpr hq.2))
      nlinarith [Real.exp_pos (-(t - q))]
    calc
      (∫ x : ℝ, gt q x ^ 2) =
          Real.exp (-(t - q)) ^ 2 * ∫ x : ℝ, g q x ^ 2 := by
        simp only [gt, mul_pow]
        rw [MeasureTheory.integral_const_mul]
      _ ≤ 1 * ∫ x : ℝ, g q x ^ 2 := by
        gcongr
      _ ≤ K ^ 2 := by simpa using hg_le q hqR
  have hgt_total : ∀ q ∈ Set.Icc a t,
      wholeLineRealL2Total (gt q) = Gt q := by
    intro q hq
    have hqR : q ∈ Set.Icc a r := ⟨hq.1, hq.2.trans ht.2⟩
    apply Lp.ext
    filter_upwards [wholeLineRealL2Total_coe_ae _ (hgt_meas q hq)
        (hgt_sq q hq), wholeLineRealL2Total_coe_ae _ (hg_meas q hqR)
        (hg_sq q hqR), htotal q hqR ▸
          Lp.coeFn_smul (Real.exp (-(t - q))) (wholeLineRealL2Total (g q))]
      with x htotalx hgrep hsmul
    have hproj : ((Set.projIcc a r har q : Set.Icc a r) : ℝ) = q := by
      simpa using congrArg Subtype.val (Set.projIcc_of_mem har hqR)
    have hGq : G q = Z q + F q := by
      simp only [G, Zc, hproj]
    rw [htotalx]
    change gt q x = (((Real.exp (-(t - q)) • G q : WholeLineRealL2) :
      ℝ → ℝ) x)
    rw [hGq, hsmul]
    simp only [gt, Pi.smul_apply, smul_eq_mul]
    rw [← htotal q hqR, hgrep]
  have hhist : AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q)
        (wholeLineRealL2Total (gt q)))
      (volume.restrict (Set.Icc a t)) := by
    have hbase : AEStronglyMeasurable
        (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (Gt q))
        (volume.restrict (Set.Icc a t)) :=
      (weightedMovingHeatL2Semigroup_terminal_history_aestronglyMeasurable
        (eta := eta) (c := c) (tau := t) hGt).mono_measure
          (Measure.restrict_le_self (μ := volume) (s := Set.Icc a t))
    exact hbase.congr (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with q hq
      rw [hgt_total q hq])
  have hgt_joint : Measurable (Function.uncurry gt) := by
    dsimp only [gt, g, Function.uncurry]
    fun_prop
  have hjointHeat : AEStronglyMeasurable
      (fun w : ℝ × ℝ =>
        weightedMovingHeatEta eta c (t - w.1) (gt w.1) w.2)
      ((volume.restrict (Set.Ioc a t)).prod volume) :=
    (weightedMovingHeatEta_history_aestronglyMeasurable_of_joint_measurable
      (eta := eta) (c := c) (tau := t) hgt_joint).aestronglyMeasurable
  have hdata := weightedMovingHeat_generatorRestart_data_of_uniform_square_bound
    (eta := eta) (c := c) ht.1.le (sq_nonneg K) hgt_meas hgt_sq hgt_le
      hhist hjointHeat
  have hraw := hdata.2 A hA hAfin
  apply hraw.congr
  filter_upwards with w
  by_cases hwA : w.2 ∈ A
  · simp only [Set.indicator, hwA, if_pos, gt, g]
    unfold weightedMovingHeatEta
    have hint :
        (∫ y : ℝ, weightedMovingHeatMarkovKernel eta c (t - w.1) w.2 y *
            (Real.exp (-(t - w.1)) * (z w.1 y + f w.1 y))) =
          Real.exp (-(t - w.1)) *
            ∫ y : ℝ, weightedMovingHeatMarkovKernel eta c (t - w.1) w.2 y *
              (z w.1 y + f w.1 y) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      ring
    rw [hint]
    ring
  · simp [Set.indicator, hwA]

/-- Actual-state damping removal on a compact positive window with a
continuous genuine forcing.  Compactness chooses the ambient forcing bound,
the natural heat-history theorem supplies every terminal history, and the
preceding theorem constructs the damped state history. -/
theorem paper5WeightedPopulation_eq_fullGeneratorCandidate_of_damped_pointwise_on_window_continuous_forcing
    {eta c a r : ℝ}
    {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {f : ℝ → ℝ → ℝ} {F : ℝ → WholeLineRealL2}
    (har : a ≤ r)
    (hFcont : Continuous F)
    (hWcont : ContinuousOn
      (fun q => wholeLineRealL2Total
        (paper5WeightedPopulation eta u U q)) (Set.Icc a r))
    (hW_meas : ∀ q ∈ Set.Icc a r,
      AEStronglyMeasurable (paper5WeightedPopulation eta u U q) volume)
    (hW_sq : ∀ q ∈ Set.Icc a r, Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta u U q x ^ 2) volume)
    (hFrep : ∀ q ∈ Set.Ioc a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q))
    (hlocal : ∀ t ∈ Set.Ioc a r, ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun w : ℝ × ℝ => A.indicator
          (fun x => Real.exp (-(t - w.1)) *
            weightedMovingHeatEta eta c (t - w.1)
              (fun y => paper5WeightedPopulation eta u U w.1 y +
                f w.1 y) x) w.2)
        ((volume.restrict (Set.Ioc a t)).prod volume))
    (hpoint : ∀ t ∈ Set.Ioc a r, ∀ᵐ x ∂volume,
      paper5WeightedPopulation eta u U t x =
        Real.exp (-(t - a)) *
          weightedMovingHeatEta eta c (t - a)
            (paper5WeightedPopulation eta u U a) x +
        ∫ q in a..t, Real.exp (-(t - q)) *
          weightedMovingHeatEta eta c (t - q)
            (fun y => paper5WeightedPopulation eta u U q y + f q y) x)
    (hshort :
      Real.exp (|eta ^ 2 - c * eta| * (r - a)) * (r - a) < 1) :
    ∀ t ∈ Set.Icc a r,
      wholeLineRealL2Total (paper5WeightedPopulation eta u U t) =
        weightedMovingHeatFullGeneratorCandidate eta c a
          (wholeLineRealL2Total (paper5WeightedPopulation eta u U a)) F t := by
  let L : ℝ := a - 1
  let R : ℝ := r + 1
  have hLa : L < a := by dsimp only [L]; linarith
  have hrR : r < R := by dsimp only [R]; linarith
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hFcont.continuousOn.norm
  let K : ℝ := max B 0
  have hK : 0 ≤ K := le_max_right _ _
  have hFbound : ∀ q ∈ Set.Icc L R, ‖F q‖ ≤ K := by
    intro q hq
    exact (hB (Set.mem_image_of_mem _ hq)).trans (le_max_left _ _)
  have hhist : ∀ t : ℝ, AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      (volume.restrict (Set.uIoc L R)) := by
    intro t
    exact
      (weightedMovingHeatL2Semigroup_terminal_history_aestronglyMeasurable
        (eta := eta) (c := c) (tau := t) hFcont).mono_measure
          Measure.restrict_le_self
  have hDint : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          (wholeLineRealL2Total
              (paper5WeightedPopulation eta u U q) + F q))
      volume a t :=
    weightedMovingHeat_actualState_damped_history_intervalIntegrable_of_continuous
      (eta := eta) (c := c) har hWcont hFcont
  exact
    paper5WeightedPopulation_eq_fullGeneratorCandidate_of_damped_pointwise_on_window
      (eta := eta) (c := c) (u := u) (U := U) (f := f) (F := F)
      hLa har hrR hK hFbound hhist hWcont hW_meas hW_sq hFrep hDint
      hlocal hpoint hshort

/-- The preceding restart with the canonical natural `L²` realization of
the physical generator forcing.  Its almost-everywhere representative is
now constructed internally, so downstream users cannot accidentally pair
the scalar restart with an unrelated Hilbert forcing. -/
theorem paper5WeightedPopulation_eq_fullGeneratorCandidate_of_damped_pointwise_on_window_natural_forcing
    (p : CMParams) {eta c a r : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (har : a ≤ r)
    (hF_meas : ∀ q ∈ Set.Icc a r,
      AEStronglyMeasurable
        (paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q) volume)
    (hF_sq : ∀ q ∈ Set.Icc a r,
      Integrable (fun x : ℝ =>
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q x ^ 2) volume)
    (hFcont : Continuous
      (paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
        p eta c u v U V har))
    (hWcont : ContinuousOn
      (fun q => wholeLineRealL2Total
        (paper5WeightedPopulation eta (coMovingPath c u) U q))
      (Set.Icc a r))
    (hW_meas : ∀ q ∈ Set.Icc a r,
      AEStronglyMeasurable
        (paper5WeightedPopulation eta (coMovingPath c u) U q) volume)
    (hW_sq : ∀ q ∈ Set.Icc a r, Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta (coMovingPath c u) U q x ^ 2) volume)
    (hjoint : Measurable (Function.uncurry (fun q x =>
      paper5WeightedPopulation eta (coMovingPath c u) U q x +
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q x)))
    (hpoint : ∀ t ∈ Set.Ioc a r, ∀ᵐ x ∂volume,
      paper5WeightedPopulation eta (coMovingPath c u) U t x =
        Real.exp (-(t - a)) *
          weightedMovingHeatEta eta c (t - a)
            (paper5WeightedPopulation eta (coMovingPath c u) U a) x +
        ∫ q in a..t, Real.exp (-(t - q)) *
          weightedMovingHeatEta eta c (t - q)
            (fun y =>
              paper5WeightedPopulation eta (coMovingPath c u) U q y +
              paper5WeightedGeneratorForcing p eta
                (coMovingPath c u) (coMovingPath c v) U V q y) x)
    (hshort :
      Real.exp (|eta ^ 2 - c * eta| * (r - a)) * (r - a) < 1) :
    ∀ t ∈ Set.Icc a r,
      wholeLineRealL2Total
          (paper5WeightedPopulation eta (coMovingPath c u) U t) =
        weightedMovingHeatFullGeneratorCandidate eta c a
          (wholeLineRealL2Total
            (paper5WeightedPopulation eta (coMovingPath c u) U a))
          (paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
            p eta c u v U V har) t := by
  have hFrepIcc : ∀ q ∈ Set.Icc a r,
      ((((paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
            p eta c u v U V har) q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q) := by
    intro q hq
    exact
      paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_coe_ae
        p eta c u v U V har hF_meas hF_sq hq
  have hWrep : ∀ q ∈ Set.Icc a r,
      ((wholeLineRealL2Total
          (paper5WeightedPopulation eta (coMovingPath c u) U q) :
            WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedPopulation eta (coMovingPath c u) U q := by
    intro q hq
    exact wholeLineRealL2Total_coe_ae _ (hW_meas q hq) (hW_sq q hq)
  have hlocal : ∀ t ∈ Set.Ioc a r, ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun w : ℝ × ℝ => A.indicator
          (fun x => Real.exp (-(t - w.1)) *
            weightedMovingHeatEta eta c (t - w.1)
              (fun y =>
                paper5WeightedPopulation eta (coMovingPath c u) U w.1 y +
                paper5WeightedGeneratorForcing p eta
                  (coMovingPath c u) (coMovingPath c v) U V w.1 y) x) w.2)
        ((volume.restrict (Set.Ioc a t)).prod volume) := by
    exact
      weightedMovingHeatEta_damped_history_local_prod_integrable_of_continuous_representatives
        (eta := eta) (c := c) har hW_meas hW_sq hF_meas hF_sq hWrep
          hFrepIcc hWcont hFcont hjoint
  have hFrep : ∀ q ∈ Set.Ioc a r,
      ((((paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
            p eta c u v U V har) q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q) := by
    intro q hq
    exact hFrepIcc q ⟨hq.1.le, hq.2⟩
  exact
    paper5WeightedPopulation_eq_fullGeneratorCandidate_of_damped_pointwise_on_window_continuous_forcing
      (eta := eta) (c := c) (u := coMovingPath c u) (U := U)
      (f := paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V)
      (F := paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
        p eta c u v U V har)
      har hFcont hWcont hW_meas hW_sq hFrep hlocal hpoint hshort


end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.exp_mul_wholeLineDriftHeatOp_eq_weightedMovingHeatEta
#print axioms
  ShenWork.Paper1.IsTravelingWave.stationary_drift_restart_identity
#print axioms
  ShenWork.Paper1.wholeLineCauchyBUCMildFixedPoint_coMoving_wavePerturbation_drift_restart
#print axioms
  ShenWork.Paper1.wholeLineCauchyBUCMildFixedPoint_weighted_generator_restart
#print axioms
  ShenWork.Paper1.weightedMovingHeat_actualState_damped_history_intervalIntegrable_of_continuous
#print axioms
  ShenWork.Paper1.paper5WeightedPopulation_eq_fullGeneratorCandidate_of_damped_pointwise_on_window_continuous_forcing
#print axioms
  ShenWork.Paper1.paper5WeightedPopulation_eq_fullGeneratorCandidate_of_damped_pointwise_on_window_natural_forcing
