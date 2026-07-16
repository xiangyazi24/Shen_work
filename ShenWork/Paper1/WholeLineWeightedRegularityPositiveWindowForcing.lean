import ShenWork.Paper1.WholeLineWeightedRegularityForcingL2Trajectory
import ShenWork.Paper1.WholeLineWeightedRegularityTimeIntegralClosure

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Exact-weight forcing trajectories on positive time windows

The physical solution is only available on its positive classical interval.
For a compact positive-time window, the construction below clamps time to the
window before taking the canonical `L²(ℝ)` realization.  Consequently no
measurability, square-integrability, or continuity premise is imposed at
negative times or past the classical horizon.
-/

/-- The canonical whole-line `L²` realization of a scalar trajectory after
clamping time to a closed window. -/
def wholeLineRealL2PositiveWindowTrajectory
    {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ → ℝ) (s : ℝ) : WholeLineRealL2 :=
  wholeLineRealL2Total (g (Set.projIcc a b hab s))

/-- The clamped canonical trajectory represents the scalar field at the
clamped time.  The hypotheses are required only on the closed window. -/
theorem wholeLineRealL2PositiveWindowTrajectory_coe_ae
    {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ → ℝ}
    (hg_meas : ∀ q ∈ Set.Icc a b,
      AEStronglyMeasurable (g q) volume)
    (hg_sq : ∀ q ∈ Set.Icc a b,
      Integrable (fun x : ℝ => g q x ^ 2) volume)
    (s : ℝ) :
    (((wholeLineRealL2PositiveWindowTrajectory hab g s : WholeLineRealL2) :
        ℝ → ℝ) =ᵐ[volume]
      g (Set.projIcc a b hab s)) := by
  exact wholeLineRealL2Total_coe_ae _
    (hg_meas _ (Set.projIcc a b hab s).2)
    (hg_sq _ (Set.projIcc a b hab s).2)

/-- On the physical window the time clamp is the identity. -/
theorem wholeLineRealL2PositiveWindowTrajectory_coe_ae_of_mem
    {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ → ℝ}
    (hg_meas : ∀ q ∈ Set.Icc a b,
      AEStronglyMeasurable (g q) volume)
    (hg_sq : ∀ q ∈ Set.Icc a b,
      Integrable (fun x : ℝ => g q x ^ 2) volume)
    {s : ℝ} (hs : s ∈ Set.Icc a b) :
    (((wholeLineRealL2PositiveWindowTrajectory hab g s : WholeLineRealL2) :
        ℝ → ℝ) =ᵐ[volume] g s) := by
  simpa only [Set.projIcc_of_mem hab hs] using
    wholeLineRealL2PositiveWindowTrajectory_coe_ae
      hab hg_meas hg_sq s

/-- Restricted scalar strong-`L²` continuity on the closed window yields a
globally continuous clamped Hilbert trajectory.  This is the positive-time
replacement for an all-real-time `L²` section. -/
theorem wholeLineRealL2PositiveWindowTrajectory_continuous
    {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ → ℝ}
    (hg_meas : ∀ q ∈ Set.Icc a b,
      AEStronglyMeasurable (g q) volume)
    (hg_sq : ∀ q ∈ Set.Icc a b,
      Integrable (fun x : ℝ => g q x ^ 2) volume)
    (hstrong : ∀ q ∈ Set.Icc a b,
      Tendsto (fun r => ∫ x : ℝ, (g r x - g q x) ^ 2)
        (nhdsWithin q (Set.Icc a b)) (nhds 0)) :
    Continuous (wholeLineRealL2PositiveWindowTrajectory hab g) := by
  let tau : ℝ → ℝ := fun s => (Set.projIcc a b hab s : ℝ)
  let gc : ℝ → ℝ → ℝ := fun s => g (tau s)
  have htau_mem : ∀ s, tau s ∈ Set.Icc a b := by
    intro s
    exact (Set.projIcc a b hab s).2
  have hgc_meas : ∀ s, AEStronglyMeasurable (gc s) volume := by
    intro s
    exact hg_meas (tau s) (htau_mem s)
  have hgc_sq : ∀ s, Integrable (fun x : ℝ => gc s x ^ 2) volume := by
    intro s
    exact hg_sq (tau s) (htau_mem s)
  have htau_cont : Continuous tau := by
    dsimp only [tau]
    fun_prop
  have hgc_strong : ∀ t, Tendsto
      (fun s => ∫ x : ℝ, (gc s x - gc t x) ^ 2)
      (nhds t) (nhds 0) := by
    intro t
    have htau : Tendsto tau (nhds t)
        (nhdsWithin (tau t) (Set.Icc a b)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨htau_cont.continuousAt,
          Eventually.of_forall (fun s => htau_mem s)⟩
    exact (hstrong (tau t) (htau_mem t)).comp htau
  have hsection : Continuous
      (wholeLineRealL2Section gc hgc_meas hgc_sq) :=
    wholeLineRealL2Section_continuous_of_integral_sub_sq_tendsto_zero
      hgc_meas hgc_sq hgc_strong
  have heq : wholeLineRealL2PositiveWindowTrajectory hab g =
      wholeLineRealL2Section gc hgc_meas hgc_sq := by
    funext s
    rw [wholeLineRealL2PositiveWindowTrajectory, wholeLineRealL2Total,
      dif_pos ⟨hgc_meas s, hgc_sq s⟩]
    rfl
  rw [heq]
  exact hsection

/-- The clamped positive-window trajectory is Bochner integrable on every
finite oriented time interval. -/
theorem wholeLineRealL2PositiveWindowTrajectory_intervalIntegrable
    {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ → ℝ}
    (hg_meas : ∀ q ∈ Set.Icc a b,
      AEStronglyMeasurable (g q) volume)
    (hg_sq : ∀ q ∈ Set.Icc a b,
      Integrable (fun x : ℝ => g q x ^ 2) volume)
    (hstrong : ∀ q ∈ Set.Icc a b,
      Tendsto (fun r => ∫ x : ℝ, (g r x - g q x) ^ 2)
        (nhdsWithin q (Set.Icc a b)) (nhds 0))
    (s t : ℝ) :
    IntervalIntegrable
      (wholeLineRealL2PositiveWindowTrajectory hab g) volume s t :=
  (wholeLineRealL2PositiveWindowTrajectory_continuous
    hab hg_meas hg_sq hstrong).intervalIntegrable s t

/-- The exact expanded forcing evaluated on the actual weighted fields. -/
def paper5WeightedGeneratorForcingExpandedActualTrajectory
    (p : CMParams) (eta c : ℝ)
    (u v : ℝ → ℝ → ℝ) (U V : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  paper5WeightedGeneratorForcingExpandedTrajectory p eta
    (coMovingPath c u) (coMovingPath c v) U
    (paper5WeightedPopulation eta (coMovingPath c u) U)
    (paper5WeightedPopulationX eta (coMovingPath c u) U)
    (paper5WeightedSignal eta (coMovingPath c v) V)
    (paper5WeightedSignalX eta (coMovingPath c v) V)

/-- Canonical exact-weight forcing trajectory with time clamped to a
positive closed window. -/
def paper5WeightedGeneratorForcingPositiveWindowL2Trajectory
    (p : CMParams) (eta c : ℝ)
    (u v : ℝ → ℝ → ℝ) (U V : ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b) : ℝ → WholeLineRealL2 :=
  wholeLineRealL2PositiveWindowTrajectory hab
    (paper5WeightedGeneratorForcingExpandedActualTrajectory
      p eta c u v U V)

/-- Local strong `L²` data for the expanded exact-weight forcing produce a
continuous positive-window forcing trajectory, with no assumptions outside
the window. -/
theorem paper5WeightedGeneratorForcingPositiveWindowL2Trajectory_continuous
    (p : CMParams) (eta c : ℝ)
    (u v : ℝ → ℝ → ℝ) (U V : ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b)
    (hF_meas : ∀ q ∈ Set.Icc a b,
      AEStronglyMeasurable
        (paper5WeightedGeneratorForcingExpandedActualTrajectory
          p eta c u v U V q) volume)
    (hF_sq : ∀ q ∈ Set.Icc a b,
      Integrable (fun x : ℝ =>
        paper5WeightedGeneratorForcingExpandedActualTrajectory
          p eta c u v U V q x ^ 2) volume)
    (hF_strong : ∀ q ∈ Set.Icc a b,
      Tendsto (fun r => ∫ x : ℝ,
        (paper5WeightedGeneratorForcingExpandedActualTrajectory
              p eta c u v U V r x -
            paper5WeightedGeneratorForcingExpandedActualTrajectory
              p eta c u v U V q x) ^ 2)
        (nhdsWithin q (Set.Icc a b)) (nhds 0)) :
    Continuous
      (paper5WeightedGeneratorForcingPositiveWindowL2Trajectory
        p eta c u v U V hab) := by
  exact wholeLineRealL2PositiveWindowTrajectory_continuous
    hab hF_meas hF_sq hF_strong

/-- The exact expanded forcing trajectory is Bochner integrable on every
finite oriented interval after positive-window clamping. -/
theorem paper5WeightedGeneratorForcingPositiveWindowL2Trajectory_intervalIntegrable
    (p : CMParams) (eta c : ℝ)
    (u v : ℝ → ℝ → ℝ) (U V : ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b)
    (hF_meas : ∀ q ∈ Set.Icc a b,
      AEStronglyMeasurable
        (paper5WeightedGeneratorForcingExpandedActualTrajectory
          p eta c u v U V q) volume)
    (hF_sq : ∀ q ∈ Set.Icc a b,
      Integrable (fun x : ℝ =>
        paper5WeightedGeneratorForcingExpandedActualTrajectory
          p eta c u v U V q x ^ 2) volume)
    (hF_strong : ∀ q ∈ Set.Icc a b,
      Tendsto (fun r => ∫ x : ℝ,
        (paper5WeightedGeneratorForcingExpandedActualTrajectory
              p eta c u v U V r x -
            paper5WeightedGeneratorForcingExpandedActualTrajectory
              p eta c u v U V q x) ^ 2)
        (nhdsWithin q (Set.Icc a b)) (nhds 0))
    (s t : ℝ) :
    IntervalIntegrable
      (paper5WeightedGeneratorForcingPositiveWindowL2Trajectory
        p eta c u v U V hab) volume s t :=
  (paper5WeightedGeneratorForcingPositiveWindowL2Trajectory_continuous
    p eta c u v U V hab hF_meas hF_sq hF_strong).intervalIntegrable s t

/-- Positive-window forcing closure for the weighted half-energy derivative.

`A` is the continuous `L²` trajectory of the spatial generator.  The
expanded nonlinear forcing is constructed canonically from local data on
`[a,b]` and clamped outside that window.  At the target time, the classical
PDE identifies their sum with the weighted material derivative, so the only
remaining time-evolution input is the concrete local Bochner increment
identity. -/
theorem paper5WeightedHalfEnergy_hasDerivAt_of_positiveWindowForcing_and_increment
    (p : CMParams) {T eta c t a b : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hab : a ≤ b) (htwin : t ∈ Set.Icc a b)
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu : ∀ x, 0 ≤ coMovingPath c u t x)
    (hu1 : ContDiff ℝ 1 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU1 : ContDiff ℝ 1 U) (hV2 : ContDiff ℝ 2 V)
    (hW_meas : ∀ᶠ s in nhds t,
      AEStronglyMeasurable
        (paper5WeightedPopulation eta (coMovingPath c u) U s) volume)
    (hclose : ∀ᶠ s in nhds t, Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) *
        |coMovingPath c u s x - U x| ^ 2) volume)
    (hWt_meas : AEStronglyMeasurable
      (paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u) t) volume)
    (hgenerator_sq : Integrable (fun x : ℝ =>
      (paper5WeightedPopulationXX eta (coMovingPath c u) U t x +
        (c - 2 * eta) *
          paper5WeightedPopulationX eta (coMovingPath c u) U t x +
        (eta ^ 2 - c * eta) *
          paper5WeightedPopulation eta (coMovingPath c u) U t x) ^ 2)
      volume)
    (hF_meas : ∀ q ∈ Set.Icc a b,
      AEStronglyMeasurable
        (paper5WeightedGeneratorForcingExpandedActualTrajectory
          p eta c u v U V q) volume)
    (hF_sq : ∀ q ∈ Set.Icc a b,
      Integrable (fun x : ℝ =>
        paper5WeightedGeneratorForcingExpandedActualTrajectory
          p eta c u v U V q x ^ 2) volume)
    (hF_strong : ∀ q ∈ Set.Icc a b,
      Tendsto (fun r => ∫ x : ℝ,
        (paper5WeightedGeneratorForcingExpandedActualTrajectory
              p eta c u v U V r x -
            paper5WeightedGeneratorForcingExpandedActualTrajectory
              p eta c u v U V q x) ^ 2)
        (nhdsWithin q (Set.Icc a b)) (nhds 0))
    {A : ℝ → WholeLineRealL2}
    (hA : Continuous A)
    (hAt : (((A t : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      fun x =>
        paper5WeightedPopulationXX eta (coMovingPath c u) U t x +
          (c - 2 * eta) *
            paper5WeightedPopulationX eta (coMovingPath c u) U t x +
          (eta ^ 2 - c * eta) *
            paper5WeightedPopulation eta (coMovingPath c u) U t x))
    (hinc :
      (fun s => wholeLineRealL2Total
        (paper5WeightedPopulation eta (coMovingPath c u) U s)) =ᶠ[nhds t]
      fun s =>
        wholeLineRealL2Total
            (paper5WeightedPopulation eta (coMovingPath c u) U t) +
          ∫ r in t..s,
            (A r +
              paper5WeightedGeneratorForcingPositiveWindowL2Trajectory
                p eta c u v U V hab r)) :
    HasDerivAt (paper5WeightedHalfEnergy eta c u U)
      (∫ x : ℝ,
        paper5WeightedPopulation eta (coMovingPath c u) U t x *
          paper5WeightedPopulationT eta
            (paper5CoMovingMaterialTime c u) t x) t := by
  let F : ℝ → ℝ → ℝ :=
    paper5WeightedGeneratorForcingExpandedActualTrajectory
      p eta c u v U V
  let GF : ℝ → WholeLineRealL2 :=
    paper5WeightedGeneratorForcingPositiveWindowL2Trajectory
      p eta c u v U V hab
  let G : ℝ → WholeLineRealL2 := fun s => A s + GF s
  have hFfun : F t =
      paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V t := by
    simpa only [F, paper5WeightedGeneratorForcingExpandedActualTrajectory]
      using
        paper5WeightedGeneratorForcingExpandedTrajectory_fun_eq_generatorForcing
          p hsol ht0 htT hTW hu hu1 hv2 hU1 hV2
  have hforcing_sq : Integrable (fun x : ℝ =>
      paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V t x ^ 2) volume := by
    simpa only [← hFfun, F] using hF_sq t htwin
  have hWt_sq :=
    paper5WeightedPopulationT_sq_integrable_of_generatorForcing
      p hsol ht0 htT hTW hu hu1 hv2 hU1 hV2 hWt_meas
        hgenerator_sq hforcing_sq
  have hGFcont : Continuous GF := by
    exact paper5WeightedGeneratorForcingPositiveWindowL2Trajectory_continuous
      p eta c u v U V hab hF_meas hF_sq hF_strong
  have hGcont : Continuous G := by
    exact hA.add hGFcont
  have hGFrep : (((GF t : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] F t) := by
    simpa only [GF,
      paper5WeightedGeneratorForcingPositiveWindowL2Trajectory, F] using
      wholeLineRealL2PositiveWindowTrajectory_coe_ae_of_mem
        hab hF_meas hF_sq htwin
  have hGFphys : (((GF t : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V t) := by
    exact hGFrep.trans (Eventually.of_forall fun x => congrFun hFfun x)
  have hWtrep :
      (((wholeLineRealL2Total
          (paper5WeightedPopulationT eta
            (paper5CoMovingMaterialTime c u) t) : WholeLineRealL2) :
          ℝ → ℝ) =ᵐ[volume]
        paper5WeightedPopulationT eta
          (paper5CoMovingMaterialTime c u) t) :=
    wholeLineRealL2Total_coe_ae _ hWt_meas hWt_sq
  have hGt : G t = wholeLineRealL2Total
      (paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u) t) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (A t) (GF t), hAt, hGFphys, hWtrep]
      with x hadd hgen hforcing hwt
    rw [hadd]
    simp only [Pi.add_apply]
    rw [hgen, hforcing, hwt]
    exact
      (paper5WeightedPopulationT_eq_spatialGenerator_add_generatorForcing
        p hsol ht0 htT hTW (hu x) hu1 hv2 hU1 hV2).symm
  apply paper5WeightedHalfEnergy_hasDerivAt_of_generatorForcing_and_increment
    p hsol ht0 htT hTW hu hu1 hv2 hU1 hV2 hW_meas hclose
      hWt_meas hgenerator_sq hforcing_sq hGcont
  · simpa only [G, GF] using hinc
  · exact hGt

section AxiomAudit

#print axioms wholeLineRealL2PositiveWindowTrajectory_coe_ae
#print axioms wholeLineRealL2PositiveWindowTrajectory_coe_ae_of_mem
#print axioms wholeLineRealL2PositiveWindowTrajectory_continuous
#print axioms wholeLineRealL2PositiveWindowTrajectory_intervalIntegrable
#print axioms
  paper5WeightedGeneratorForcingPositiveWindowL2Trajectory_continuous
#print axioms
  paper5WeightedGeneratorForcingPositiveWindowL2Trajectory_intervalIntegrable
#print axioms
  paper5WeightedHalfEnergy_hasDerivAt_of_positiveWindowForcing_and_increment

end AxiomAudit

end ShenWork.Paper1
