import ShenWork.Paper1.WholeLineChiPosPhysicalSegmentStrictPositivity
import ShenWork.Paper1.WholeLineChiLargeFiniteStage1
import ShenWork.Paper1.WholeLineChiLargeStage1Reduction
import ShenWork.Paper1.WholeLineLocalMomentEnergyProducer

/-!
# Subquadratic local moments on maximal orbits with a left plateau

For arbitrary nonnegative data the regularized energy producer currently asks
for `2 ≤ P`.  A datum with a positive left-hand floor generates a strictly
positive physical orbit, so the original positive energy identity applies for
every `1 < P`.  This is the exponent range needed by the normalized
`m = gamma = 1`, `chi < 4` problem.
-/

open Filter MeasureTheory Real Set Topology Function

noncomputable section

namespace ShenWork.Paper1

/-- Maximal-orbit energy damping restricted to data with a positive
left-hand floor. -/
def WholeLineLargeChiMaximalEnergyDampingAtLeft
    (p : CMParams) (P κ : ℝ) : Prop :=
  ∀ (u₀ : ℝ → ℝ), PaperNonnegativeInitialDatum u₀ →
    StrictlyPositiveAtLeft u₀ →
    ∀ (Tmax : WithTop ℝ) (U : ℝ → WholeLineBUC),
      IsWholeLineMaximalBUCOrbit p u₀ Tmax U →
      ∀ T : ℝ, 0 < T → (T : WithTop ℝ) < Tmax → ∀ x₀ : ℝ,
        let u : ℝ → ℝ → ℝ := fun t x => (U t).1 x
        let E : ℝ → ℝ := fun t => wholeLineLocalLpEnergy P κ u t x₀
        ContinuousOn E (Icc 0 T) ∧
          ∀ t ∈ Ioo (0 : ℝ) T,
            HasDerivAt E (deriv E t) t ∧
              deriv E t + E t ≤ wholeLineLocalMomentDampingRhs p P κ

/-- The strictly-positive energy producer supplies damping on every maximal
physical orbit issued from a datum with a positive left-hand floor. -/
theorem wholeLineLargeChiMaximalEnergyDampingAtLeft
    (p : CMParams) {P κ : ℝ}
    (hP : 1 < P)
    (hκ : 0 < κ) (hκhalf : κ < 1 / 2)
    (hχ : 0 ≤ p.χ)
    (hcritical : p.α = p.m + p.γ - 1)
    (habsorption : 0 < wholeLineLocalMomentAbsorption p P κ) :
    WholeLineLargeChiMaximalEnergyDampingAtLeft p P κ := by
  intro u₀ hu₀ hleft Tmax U horbit T hT hTmax x₀
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
  have hleftw : StrictlyPositiveAtLeft w.1 := by
    simpa [w] using hleft
  have hpositive := wholeLinePhysicalFixedPoint_pos_and_left_of_posAtBot
    p hM hT w hleftw Traj hfixed hstrip
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
    have hposCanon : ∀ z : Set.Icc (0 : ℝ) h, 0 < z.1 → ∀ x,
        0 < (Canon z).1 x := by
      intro z hz x
      have happ := congrArg
        (fun Q : WholeLineBUCTrajectory h => Q z) hchart
      have hzT : a + z.1 ∈ Set.Icc (0 : ℝ) T :=
        ⟨add_nonneg ha.le z.2.1, by linarith [z.2.2, hah]⟩
      have happ' : Canon z = Traj ⟨a + z.1, hzT⟩ := by
        simpa [Canon, datum, za, wholeLineBUCTrajectoryShift] using happ.symm
      rw [happ']
      exact hpositive.1 ⟨a + z.1, hzT⟩ (add_pos ha hz) x
    let H := wholeLineCauchyBUCMildFixedPoint_localMomentEnergyData
      p (M := M) (T := h) (P := P) (κ := κ) (t := q) (x₀ := x₀)
      hM hh.le hP hκ hq.1 hq.2 datum hsmall
        (by simpa [Canon] using hstripCanon)
        (by simpa [Canon] using hposCanon)
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
    have hlocalEq : Filter.EventuallyEq (nhds t) E
        (fun s => El (s - a)) := by
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

/-- Maximal local-moment bound restricted to data with a positive left-hand
floor. -/
def WholeLineLargeChiMaximalLocalMomentBoundAtLeft
    (p : CMParams) (P κ : ℝ) : Prop :=
  ∀ (u₀ : ℝ → ℝ), PaperNonnegativeInitialDatum u₀ →
    StrictlyPositiveAtLeft u₀ →
    ∀ (Tmax : WithTop ℝ) (U : ℝ → WholeLineBUC),
      IsWholeLineMaximalBUCOrbit p u₀ Tmax U →
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ t : ℝ, 0 < t → (t : WithTop ℝ) < Tmax → ∀ x : ℝ,
          (∫ y : ℝ, ((U t).1 y) ^ P *
            localizingWeightAt κ x y) ≤ K

/-- Positive-time damping closes to a time- and translate-uniform local
moment bound exactly as in the unrestricted Stage-1 reduction. -/
theorem wholeLineLargeChiMaximalLocalMomentBoundAtLeft_of_energyDamping
    (p : CMParams) {P κ : ℝ}
    (hP : 1 < P) (hκ : 0 < κ)
    (habsorption : 0 < wholeLineLocalMomentAbsorption p P κ)
    (Hdamping : WholeLineLargeChiMaximalEnergyDampingAtLeft p P κ) :
    WholeLineLargeChiMaximalLocalMomentBoundAtLeft p P κ := by
  intro u₀ hu₀ hleft Tmax U horbit
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  let A : ℝ := (‖w‖ ^ P * (2 / κ)) / P
  let R : ℝ := wholeLineLocalMomentDampingRhs p P κ
  let K : ℝ := P * max A R
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hR : 0 < R := by
    have hrem := wholeLineLocalMomentYoungRemainder_pos
      p hP hκ habsorption
    dsimp [R, wholeLineLocalMomentDampingRhs]
    exact mul_pos hrem (div_pos (by norm_num) hκ)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg hP0.le (hA.trans (le_max_left A R))
  refine ⟨K, hK, ?_⟩
  intro T hT hTmax x₀
  let u : ℝ → ℝ → ℝ := fun t x => (U t).1 x
  let E : ℝ → ℝ := fun t => wholeLineLocalLpEnergy P κ u t x₀
  have hdata := Hdamping u₀ hu₀ hleft Tmax U horbit T hT hTmax x₀
  change ContinuousOn E (Icc 0 T) ∧
    (∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt E (deriv E t) t ∧
        deriv E t + E t ≤ wholeLineLocalMomentDampingRhs p P κ) at hdata
  obtain ⟨hcont, hdamping⟩ := hdata
  have hscalar : E T ≤ max (E 0) R := by
    have hraw := scalarEnergy_uniform_bound_of_positive_time_damping
      (E := E) (T := T) (lam := 1)
      (K := wholeLineLocalMomentDampingRhs p P κ)
      hT.le one_pos hcont
      (fun t ht => (hdamping t ht).1)
      (fun t ht => by simpa only [one_mul] using (hdamping t ht).2)
      T ⟨hT.le, le_rfl⟩
    simpa [R] using hraw
  obtain ⟨_hTmaxPos, hdatum, _htrace, _hcontOrbit, _hclass,
    _hmild, _hnonnegative, _hblowup⟩ := horbit
  have hUzero : U 0 = w := by
    apply Subtype.ext
    apply BoundedContinuousFunction.ext
    intro x
    simpa [w] using hdatum x
  have hmoment0 : wholeLineLocalLpMoment P κ u 0 x₀ ≤
      ‖w‖ ^ P * (2 / κ) := by
    apply wholeLineLocalLpMoment_le_two_mul_div
      hP0.le hκ (norm_nonneg w)
    · simpa [u, hUzero] using (WholeLineBUC.isCUnifBdd w).1
    · intro x
      simpa [u, hUzero] using hu₀.2 x
    · intro x
      simpa [u, hUzero] using WholeLineBUC.apply_le_norm w x
  have hEzero : E 0 ≤ A := by
    change (1 / P) * wholeLineLocalLpMoment P κ u 0 x₀ ≤
      (‖w‖ ^ P * (2 / κ)) / P
    have hscaled := mul_le_mul_of_nonneg_left hmoment0
      (one_div_nonneg.mpr hP0.le)
    convert hscaled using 1
    all_goals field_simp [hP0.ne']
  have hE : E T ≤ max A R :=
    hscalar.trans (max_le_max hEzero le_rfl)
  have hscaled := mul_le_mul_of_nonneg_left hE hP0.le
  have hmomentEq : wholeLineLocalLpMoment P κ u T x₀ = P * E T := by
    dsimp [E, wholeLineLocalLpEnergy]
    field_simp [hP0.ne']
  change wholeLineLocalLpMoment P κ u T x₀ ≤ K
  rw [hmomentEq]
  simpa [K] using hscaled

/-- The concrete strict-positive Stage 1, valid for every exponent `P > 1`. -/
theorem wholeLineLargeChiMaximalLocalMomentBoundAtLeft_strict
    (p : CMParams) {P κ : ℝ}
    (hP : 1 < P)
    (hκ : 0 < κ) (hκhalf : κ < 1 / 2)
    (hχ : 0 ≤ p.χ)
    (hcritical : p.α = p.m + p.γ - 1)
    (habsorption : 0 < wholeLineLocalMomentAbsorption p P κ) :
    WholeLineLargeChiMaximalLocalMomentBoundAtLeft p P κ :=
  wholeLineLargeChiMaximalLocalMomentBoundAtLeft_of_energyDamping
    p hP hκ habsorption
      (wholeLineLargeChiMaximalEnergyDampingAtLeft
        p hP hκ hκhalf hχ hcritical habsorption)

section AxiomAudit

#print axioms wholeLineLargeChiMaximalEnergyDampingAtLeft
#print axioms
  wholeLineLargeChiMaximalLocalMomentBoundAtLeft_of_energyDamping
#print axioms wholeLineLargeChiMaximalLocalMomentBoundAtLeft_strict

end AxiomAudit

end ShenWork.Paper1
