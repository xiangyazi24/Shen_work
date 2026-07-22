import ShenWork.Paper1.WholeLineChiLargeFiniteStage1
import ShenWork.Paper1.WholeLineChiLargeStage1Reduction
import ShenWork.Paper1.WholeLinePhysicalMildUniqueness

/-!
# Stage 1 on arbitrary maximal whole-line BUC orbits

The maximal-orbit interface stores only finite-horizon continuity,
classicality, the original mild equation, and nonnegativity.  On each compact
subhorizon these data give a physical truncated fixed point.  Short-window
Volterra uniqueness then provides canonical restart charts at every positive
time.  The nonnegative local-energy identity transfers through those charts,
yielding the horizon-independent damping inequality required by Stage 1.
-/

open Filter MeasureTheory Real Set Topology Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-- The nonnegative canonical energy identity supplies the maximal-orbit
damping statement. -/
theorem wholeLineLargeChiMaximalEnergyDamping_nonnegative
    (p : CMParams) {P κ : ℝ}
    (hP : 1 < P) (hPtwo : 2 ≤ P)
    (hκ : 0 < κ) (hκhalf : κ < 1 / 2)
    (hχ : 0 ≤ p.χ)
    (hcritical : p.α = p.m + p.γ - 1)
    (habsorption : 0 < wholeLineLocalMomentAbsorption p P κ) :
    WholeLineLargeChiMaximalEnergyDamping p P κ := by
  intro u₀ hu₀ Tmax U horbit T hT hTmax x₀
  obtain ⟨_hTmaxPos, _hdatum, _htrace, hcont, _hclass, hmild,
    hnonnegative, _hblowup⟩ := horbit
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  have hcontT := hcont T hT.le hTmax
  let Traj : WholeLineBUCTrajectory T :=
    ⟨fun z => U z.1, hcontT.restrict⟩
  have hnormCont : ContinuousOn (fun s : ℝ => ‖U s‖)
      (Set.Icc (0 : ℝ) T) := hcontT.norm
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) T)).bddAbove_image hnormCont
  let M : ℝ := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hTrajNorm : ∀ z : Set.Icc (0 : ℝ) T, ‖Traj z‖ ≤ M := by
    intro z
    have hzB : ‖U z.1‖ ≤ B :=
      hB (Set.mem_image_of_mem (fun s => ‖U s‖) z.2)
    exact hzB.trans (le_max_left _ _)
  have hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (Traj z).1 x ∈ Set.Icc (0 : ℝ) M := by
    intro z x
    have hzmax : (z.1 : WithTop ℝ) < Tmax :=
      lt_of_le_of_lt (WithTop.coe_le_coe.mpr z.2.2) hTmax
    constructor
    · exact hnonnegative z.1 x z.2.1 hzmax
    · exact (WholeLineBUC.apply_le_norm (Traj z) x).trans (hTrajNorm z)
  have hmildTraj : ∀ z : Set.Icc (0 : ℝ) T, ∀ x : ℝ,
      (Traj z).1 x = wholeLineCauchyMildMap p w.1
        (fun q y => (wholeLineBUCTrajectoryExtend hT.le Traj q).1 y)
        z.1 x := by
    intro z x
    have hzmax : (z.1 : WithTop ℝ) < Tmax :=
      lt_of_le_of_lt (WithTop.coe_le_coe.mpr z.2.2) hTmax
    have hraw := hmild T hT hTmax z.1 z.2 x
    have hagree : ∀ s ∈ Set.Icc (0 : ℝ) z.1,
        (fun q y => (U q).1 y) s =
          (fun q y => (wholeLineBUCTrajectoryExtend hT.le Traj q).1 y) s := by
      intro s hs
      have hsT : s ∈ Set.Icc (0 : ℝ) T :=
        ⟨hs.1, hs.2.trans z.2.2⟩
      funext y
      change (U s).1 y =
        (wholeLineBUCTrajectoryExtend hT.le Traj s).1 y
      rw [wholeLineBUCTrajectoryExtend_eq hT.le Traj hsT]
      rfl
    have hcongr := wholeLineCauchyMildMap_congr_on_Icc
      p u₀ z.2.1 hagree x
    calc
      (Traj z).1 x = (U z.1).1 x := rfl
      _ = wholeLineCauchyMildMap p u₀
          (fun q y => (U q).1 y) z.1 x := hraw
      _ = wholeLineCauchyMildMap p u₀
          (fun q y => (wholeLineBUCTrajectoryExtend hT.le Traj q).1 y)
            z.1 x := hcongr
      _ = wholeLineCauchyMildMap p w.1
          (fun q y => (wholeLineBUCTrajectoryExtend hT.le Traj q).1 y)
            z.1 x := by rfl
  have hfixed : IsFixedPt
      (wholeLineCauchyBUCMildMap p hM hT.le w) Traj :=
    wholeLinePhysicalOriginalMild_isFixedPt
      p hM hT.le w Traj hstrip hmildTraj
  let u : ℝ → ℝ → ℝ := fun s x => (U s).1 x
  let ue : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend hT.le Traj s).1 x
  let E : ℝ → ℝ := fun s => wholeLineLocalLpEnergy P κ u s x₀
  let Ee : ℝ → ℝ := fun s => wholeLineLocalLpEnergy P κ ue s x₀
  have hcontEe : Continuous Ee := by
    simpa [Ee, ue] using
      wholeLineBUCTrajectory_localLpEnergy_continuous
        hM hT.le (by linarith : 0 ≤ P) hκ Traj hstrip x₀
  have hEeq : ∀ s ∈ Set.Icc (0 : ℝ) T, E s = Ee s := by
    intro s hs
    have hext := wholeLineBUCTrajectoryExtend_eq hT.le Traj hs
    simp only [E, Ee, u, ue, wholeLineLocalLpEnergy,
      wholeLineLocalLpMoment]
    congr 2
    funext x
    rw [hext]
    rfl
  constructor
  · change ContinuousOn E (Set.Icc (0 : ℝ) T)
    exact hcontEe.continuousOn.congr (fun s hs => hEeq s hs)
  · intro t ht
    rcases wholeLinePhysicalFixedPoint_exists_canonical_chart
        p hM hT w Traj hfixed hstrip t ht with
      ⟨a, h, q, ha, hh, hq, hah, htime, hsmall, hchart⟩
    let za : Set.Icc (0 : ℝ) T :=
      ⟨a, ha.le, (le_add_of_nonneg_right hh.le).trans hah⟩
    let datum : WholeLineBUC := Traj za
    let Canon : WholeLineBUCTrajectory h :=
      wholeLineCauchyBUCMildFixedPoint p hM hh.le datum hsmall
    let ul : ℝ → ℝ → ℝ := fun s x =>
      (wholeLineBUCTrajectoryExtend hh.le Canon s).1 x
    let vl : ℝ → ℝ → ℝ := fun s => frozenElliptic p (ul s)
    let El : ℝ → ℝ := fun s => wholeLineLocalLpEnergy P κ ul s x₀
    have hstripCanon : ∀ z : Set.Icc (0 : ℝ) h, ∀ x,
        (Canon z).1 x ∈ Set.Icc (0 : ℝ) M := by
      intro z x
      have happ := congrArg
        (fun Q : WholeLineBUCTrajectory h => Q z) hchart
      have hzT : a + z.1 ∈ Set.Icc (0 : ℝ) T :=
        ⟨add_nonneg ha.le z.2.1, by linarith [z.2.2, hah]⟩
      have happ' : Canon z = Traj ⟨a + z.1, hzT⟩ := by
        simpa [Canon, datum, za, wholeLineBUCTrajectoryShift] using happ.symm
      rw [happ']
      exact hstrip ⟨a + z.1, hzT⟩ x
    let H :=
      wholeLineCauchyBUCMildFixedPoint_localMomentNonnegativeEnergyData
        p (M := M) (T := h) (P := P) (κ := κ) (t := q) (x₀ := x₀)
        hM hh.le hP hPtwo hκ hq.1 hq.2 datum hsmall
          (by simpa [Canon] using hstripCanon)
    have hulC : IsCUnifBdd (ul q) :=
      WholeLineBUC.isCUnifBdd
        (wholeLineBUCTrajectoryExtend hh.le Canon q)
    have hul0 : ∀ x, 0 ≤ ul q x := by
      intro x
      dsimp [ul, wholeLineBUCTrajectoryExtend]
      exact (hstripCanon (Set.projIcc 0 h hh.le q) x).1
    have hdampLocal : deriv El q + El q ≤
        wholeLineLocalMomentDampingRhs p P κ := by
      have hd := H.critical_energy_damping hχ hκhalf hcritical
        habsorption hulC hul0 rfl
      simpa [H, El, ul, vl, Canon] using hd
    have htmem : t ∈ Set.Ioo a (a + h) := by
      rw [htime]
      exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
    have hlocalEq : Filter.EventuallyEq (nhds t) E (fun s => El (s - a)) := by
      filter_upwards [isOpen_Ioo.mem_nhds htmem] with s hs
      have hr : s - a ∈ Set.Icc (0 : ℝ) h :=
        ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hsT : s ∈ Set.Icc (0 : ℝ) T :=
        ⟨by linarith [ha, hs.1], by linarith [hs.2, hah]⟩
      have happ := congrArg
        (fun Q : WholeLineBUCTrajectory h => Q ⟨s - a, hr⟩) hchart
      have hext := wholeLineBUCTrajectoryExtend_eq hh.le Canon hr
      have hslice : u s = ul (s - a) := by
        funext x
        change (U s).1 x =
          (wholeLineBUCTrajectoryExtend hh.le Canon (s - a)).1 x
        rw [hext]
        change (Traj ⟨s, hsT⟩).1 x = (Canon ⟨s - a, hr⟩).1 x
        have heq := congrArg (fun W : WholeLineBUC => W.1 x) happ
        simpa [Canon, datum, za, wholeLineBUCTrajectoryShift] using heq
      simp only [E, El, wholeLineLocalLpEnergy,
        wholeLineLocalLpMoment]
      rw [hslice]
    have htimeSub : t - a = q := by rw [htime]; ring
    have hlocalDeriv : HasDerivAt El (deriv El q) q := by
      have hd := H.energy_hasDerivAt
      have hd' := hd.congr_deriv hd.deriv.symm
      simpa [H, El, ul, Canon] using hd'
    have hlocalAtSub : HasDerivAt El (deriv El q) (t - a) := by
      simpa [htimeSub] using hlocalDeriv
    have htranslated := hlocalAtSub.comp t
      ((hasDerivAt_id t).sub_const a)
    have htranslated' : HasDerivAt (fun s => El (s - a))
        (deriv El q) t := by
      simpa [mul_one] using htranslated
    have hglobalDeriv := htranslated'.congr_of_eventuallyEq hlocalEq
    have hvalue : E t = El q := by
      have := hlocalEq.self_of_nhds
      simpa [htimeSub] using this
    refine ⟨hglobalDeriv.congr_deriv hglobalDeriv.deriv.symm, ?_⟩
    change deriv E t + E t ≤ wholeLineLocalMomentDampingRhs p P κ
    rw [hglobalDeriv.deriv, hvalue]
    exact hdampLocal

/-- The exact critical Stage-1 producer in the nonnegative maximal-orbit
interface. -/
theorem wholeLineLargeChiCriticalStage1Producer_nonnegative
    (p : CMParams) (hχ : 0 ≤ p.χ)
    (hcritical : p.α = p.m + p.γ - 1) :
    WholeLineLargeChiCriticalStage1Producer p := by
  apply wholeLineLargeChiCriticalStage1Producer_of_energyDamping p
  intro P κ hP _hPupper _hadmissible hκ hκhalf habsorption
  have hPone : 1 < P := by
    have hm2 : 1 ≤ 2 * p.m := by linarith [p.hm]
    exact lt_of_le_of_lt
      (hm2.trans (le_max_left (2 * p.m) p.γ)) hP
  have hPtwo : 2 ≤ P := by
    have htwoM : 2 ≤ 2 * p.m := by linarith [p.hm]
    exact htwoM.trans
      ((le_max_left (2 * p.m) p.γ).trans hP.le)
  exact wholeLineLargeChiMaximalEnergyDamping_nonnegative
    p hPone hPtwo hκ hκhalf hχ hcritical habsorption

section AxiomAudit

#print axioms wholeLineLargeChiMaximalEnergyDamping_nonnegative
#print axioms wholeLineLargeChiCriticalStage1Producer_nonnegative

end AxiomAudit

end ShenWork.Paper1
