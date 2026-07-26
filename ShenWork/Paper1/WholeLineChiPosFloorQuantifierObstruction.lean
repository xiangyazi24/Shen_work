import ShenWork.Paper1.WholeLineChiPosDeepHoleRefill
import ShenWork.Paper1.WholeLineChiPosEntropyFarLeftNormalFamily
import ShenWork.Paper1.WholeLineChiPosHalfLineSeedMGTOne
import ShenWork.Paper1.WholeLineChiPosPhysicalSegmentStrictPositivity
import ShenWork.Paper1.WholeLineMaximalBUCImport
import ShenWork.Paper1.WholeLinePhysicalMildSegments

/-!
# Convective escape and the far-left floor quantifier obstruction

The canonical positivity theory preserves `StrictlyPositiveAtLeft` on every
fixed co-moving time slice.  This gives

`∀ t ≥ 0, ∃ ell_t > 0, ∃ R_t, ∀ z ≤ R_t, ell_t ≤ q(t,z)`.

The persistent floor needed by `EventualCoMovingLeftBand` reverses the first
three quantifiers: one needs a single `ell`, `T`, and `R` for every `t ≥ T`.

The earlier version of this module used the artificial smooth family

`q(t,z) = 1 / (1 + exp (z+t))`

to record the quantifier mismatch.  Here it is superseded by the exact
convective-escape family from an arbitrary traveling-wave profile.  If `U`
connects `1` at `-∞` to `0` at `+∞`, has laboratory speed `s`, and is observed
in a faster frame `c > s`, then

`q(t,z) = U (z + (c-s)t)`.

Every fixed slice tends to `1` at the left endpoint, but at every fixed
co-moving point it tends to `0` as time tends to infinity.  Thus no positive
uniform far-left floor exists.  For an `IsTravelingWave`, the laboratory orbit
is a genuine solution of the chemotaxis--logistic system; the remaining
theorems below wire this exact solution to the quantifier obstruction.
-/

open Filter Function Set Topology

noncomputable section

namespace ShenWork.Paper1

/-- `StrictlyPositiveAtLeft` gives an explicit positive floor on one left
half-line.  Both witnesses may depend on the profile. -/
theorem StrictlyPositiveAtLeft.exists_leftHalfLine_floor
    {u : ℝ → ℝ} (h : StrictlyPositiveAtLeft u) :
    ∃ ell R : ℝ, 0 < ell ∧ ∀ x, x ≤ R → ell ≤ u x := by
  rcases h with ⟨ell, hell, hevent⟩
  obtain ⟨R, hR⟩ := eventually_atBot.1 hevent
  exact ⟨ell, R, hell, hR⟩

/-- The currently landed canonical positivity result gives a floor on every
fixed co-moving time slice, with time-dependent height and cut. -/
theorem wholeLineCauchyGlobal_exists_timeSlice_coMoving_left_floor
    (p : CMParams) (hceiling : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1) (c : ℝ) :
    ∀ t, 0 ≤ t →
      ∃ ell R : ℝ, 0 < ell ∧
        ∀ z, z ≤ R →
          ell ≤ coMovingPath c (wholeLineCauchyGlobalU p u₀) t z := by
  intro t ht
  exact
    (wholeLineCauchyGlobal_coMoving_strictlyPositiveAtLeft
      p hceiling u₀ hu₀ hleft c ht).exists_leftHalfLine_floor

/-- Every slice of a global physical maximal BUC orbit retains
`StrictlyPositiveAtLeft`.  Unlike the canonical result above, this statement
does not require `WholeLineCauchyCeilingRegime`. -/
theorem wholeLineGlobalMaximalBUCOrbit_strictlyPositiveAtLeft
    (p : CMParams) (u₀ : ℝ → ℝ)
    (hu₀ : PaperNonnegativeInitialDatum u₀)
    (hleft : StrictlyPositiveAtLeft u₀)
    {U : ℝ → WholeLineBUC}
    (horbit : IsWholeLineMaximalBUCOrbit p u₀ (⊤ : WithTop ℝ) U)
    {t : ℝ} (ht : 0 ≤ t) :
    StrictlyPositiveAtLeft (U t).1 := by
  obtain ⟨_horizon, _hdatum, _htrace, hcont, _hclassical, hmild,
    hnonnegative, _hcontinuation⟩ := horbit
  let T : ℝ := t + 1
  have hT : 0 < T := by
    dsimp only [T]
    linarith
  have hcontT : ContinuousOn U (Set.Icc (0 : ℝ) T) :=
    hcont T hT.le (WithTop.coe_lt_top T)
  let Traj : WholeLineBUCTrajectory T :=
    ⟨fun z => U z.1, hcontT.restrict⟩
  have hnormCont : ContinuousOn (fun s : ℝ => ‖U s‖)
      (Set.Icc (0 : ℝ) T) :=
    hcontT.norm
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
    constructor
    · exact hnonnegative z.1 x z.2.1 (WithTop.coe_lt_top z.1)
    · exact (WholeLineBUC.apply_le_norm (Traj z) x).trans (hTrajNorm z)
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  have hmildTraj : ∀ z : Set.Icc (0 : ℝ) T, ∀ x : ℝ,
      (Traj z).1 x = wholeLineCauchyMildMap p w.1
        (fun q y => (wholeLineBUCTrajectoryExtend hT.le Traj q).1 y)
        z.1 x := by
    intro z x
    have hraw :=
      hmild T hT (WithTop.coe_lt_top T) z.1 z.2 x
    have hagree : ∀ s ∈ Set.Icc (0 : ℝ) z.1,
        (fun q y => (U q).1 y) s =
          (fun q y =>
            (wholeLineBUCTrajectoryExtend hT.le Traj q).1 y) s := by
      intro s hs
      have hsT : s ∈ Set.Icc (0 : ℝ) T :=
        ⟨hs.1, hs.2.trans z.2.2⟩
      funext y
      change (U s).1 y =
        (wholeLineBUCTrajectoryExtend hT.le Traj s).1 y
      rw [wholeLineBUCTrajectoryExtend_eq hT.le Traj hsT]
      rfl
    have hcongr := wholeLineCauchyMildMap_congr_on_Icc_segments
      p u₀ z.2.1 hagree x
    calc
      (Traj z).1 x = (U z.1).1 x := rfl
      _ = wholeLineCauchyMildMap p u₀
          (fun q y => (U q).1 y) z.1 x := hraw
      _ = wholeLineCauchyMildMap p u₀
          (fun q y =>
            (wholeLineBUCTrajectoryExtend hT.le Traj q).1 y)
          z.1 x := hcongr
      _ = wholeLineCauchyMildMap p w.1
          (fun q y =>
            (wholeLineBUCTrajectoryExtend hT.le Traj q).1 y)
          z.1 x := by rfl
  have hfixed : IsFixedPt
      (wholeLineCauchyBUCMildMap p hM hT.le w) Traj :=
    wholeLinePhysicalOriginalMild_isFixedPt
      p hM hT.le w Traj hstrip hmildTraj
  have hleftw : StrictlyPositiveAtLeft w.1 := by
    simpa only [w] using hleft
  have hpositive :=
    wholeLinePhysicalFixedPoint_pos_and_left_of_posAtBot
      p hM hT w hleftw Traj hfixed hstrip
  let zt : Set.Icc (0 : ℝ) T :=
    ⟨t, ht, by dsimp only [T]; linarith⟩
  simpa only [Traj, zt] using hpositive.2 zt

/-- Consequently, every fixed co-moving slice of a global physical maximal
orbit has a positive left-half-line floor.  Its witnesses still depend on
time. -/
theorem wholeLineGlobalMaximalBUCOrbit_exists_timeSlice_coMoving_left_floor
    (p : CMParams) (u₀ : ℝ → ℝ)
    (hu₀ : PaperNonnegativeInitialDatum u₀)
    (hleft : StrictlyPositiveAtLeft u₀)
    {U : ℝ → WholeLineBUC}
    (horbit : IsWholeLineMaximalBUCOrbit p u₀ (⊤ : WithTop ℝ) U)
    (c : ℝ) :
    ∀ t, 0 ≤ t →
      ∃ ell R : ℝ, 0 < ell ∧
        ∀ z, z ≤ R →
          ell ≤ coMovingPath c (fun s x => (U s).1 x) t z := by
  intro t ht
  have hslice :
      StrictlyPositiveAtLeft
        (coMovingPath c (fun s x => (U s).1 x) t) := by
    simpa only [coMovingPath] using
      (wholeLineGlobalMaximalBUCOrbit_strictlyPositiveAtLeft
        p u₀ hu₀ hleft horbit ht).shift (c * t)
  exact hslice.exists_leftHalfLine_floor

/-- A profile of laboratory speed `s`, viewed in the faster frame of speed
`c`.  Its transition moves to the left with speed `c-s`. -/
def convectiveEscapeProfile
    (U : ℝ → ℝ) (s c t z : ℝ) : ℝ :=
  U (z + (c - s) * t)

/-- The laboratory-coordinate traveling profile with speed `s`. -/
def travelingWaveLaboratoryProfile
    (s : ℝ) (U : ℝ → ℝ) (t x : ℝ) : ℝ :=
  U (x - s * t)

/-- Observing a laboratory traveling profile in the frame of speed `c`
produces exactly `convectiveEscapeProfile`. -/
@[simp] theorem coMovingPath_travelingWaveLaboratoryProfile
    (U : ℝ → ℝ) (s c t z : ℝ) :
    coMovingPath c (travelingWaveLaboratoryProfile s U) t z =
      convectiveEscapeProfile U s c t z := by
  simp only [coMovingPath, travelingWaveLaboratoryProfile,
    convectiveEscapeProfile]
  congr 1
  ring

/-- Every fixed time slice retains the left endpoint limit of the profile. -/
theorem convectiveEscapeProfile_tendsto_atBot
    {U : ℝ → ℝ} (hleft : Tendsto U atBot (𝓝 1))
    (s c t : ℝ) :
    Tendsto (convectiveEscapeProfile U s c t) atBot (𝓝 1) := by
  simpa only [convectiveEscapeProfile] using
    hleft.comp
      (tendsto_atBot_add_const_right atBot ((c - s) * t) tendsto_id)

/-- In particular, convergence to `1` at the left endpoint gives the
`StrictlyPositiveAtLeft` property on every fixed slice. -/
theorem convectiveEscapeProfile_strictlyPositiveAtLeft
    {U : ℝ → ℝ} (hleft : Tendsto U atBot (𝓝 1))
    (s c t : ℝ) :
    StrictlyPositiveAtLeft (convectiveEscapeProfile U s c t) := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  have hnhds : Set.Ioi (1 / 2 : ℝ) ∈ 𝓝 (1 : ℝ) :=
    Ioi_mem_nhds (by norm_num)
  filter_upwards
      [(convectiveEscapeProfile_tendsto_atBot hleft s c t) hnhds] with z hz
  exact hz.le

/-- At every fixed point of a strictly faster frame, the profile samples the
right endpoint and therefore converges to zero in time. -/
theorem convectiveEscapeProfile_tendsto_atTop_time
    {U : ℝ → ℝ} (hright : Tendsto U atTop (𝓝 0))
    {s c : ℝ} (hsc : s < c) (z : ℝ) :
    Tendsto (fun t => convectiveEscapeProfile U s c t z) atTop (𝓝 0) := by
  apply hright.comp
  have hrate : 0 < c - s := sub_pos.mpr hsc
  apply tendsto_atTop_add_const_left
  exact (tendsto_const_mul_atTop_of_pos hrate).2 tendsto_id

/-- Pure quantifier obstruction: for every proposed positive height, start
time, and left cut, a later point in that fixed half-line lies below the
height.  The witness is the boundary point `z = -R`. -/
theorem convectiveEscapeProfile_exists_late_left_lt
    {U : ℝ → ℝ} (hright : Tendsto U atTop (𝓝 0))
    {s c ell : ℝ} (hsc : s < c) (hell : 0 < ell) (T R : ℝ) :
    ∃ t z : ℝ, T ≤ t ∧ z ≤ -R ∧
      convectiveEscapeProfile U s c t z < ell := by
  have hsmall : ∀ᶠ t in atTop,
      convectiveEscapeProfile U s c t (-R) < ell :=
    (tendsto_order.1
      (convectiveEscapeProfile_tendsto_atTop_time hright hsc (-R))).2
        ell hell
  obtain ⟨t, ht, hlt⟩ :=
    ((eventually_ge_atTop T).and hsmall).exists
  exact ⟨t, -R, ht, le_rfl, hlt⟩

/-- Equivalently, no positive lower floor can be uniform in all late times
and all points of one fixed left half-line. -/
theorem convectiveEscapeProfile_no_uniform_left_floor
    {U : ℝ → ℝ} (hright : Tendsto U atTop (𝓝 0))
    {s c : ℝ} (hsc : s < c) :
    ¬ ∃ ell T R : ℝ, 0 < ell ∧
      ∀ t, T ≤ t → ∀ z, z ≤ -R →
        ell ≤ convectiveEscapeProfile U s c t z := by
  rintro ⟨ell, T, R, hell, hfloor⟩
  obtain ⟨t, z, ht, hz, hlt⟩ :=
    convectiveEscapeProfile_exists_late_left_lt
      hright hsc hell T R
  exact (not_lt_of_ge (hfloor t ht z hz)) hlt

/-- The same obstruction in the repository's physical-orbit interface:
a laboratory wave of speed `s` has no positive
`EventualCoMovingLeftBand` in any faster frame `c`. -/
theorem travelingWaveLaboratoryProfile_not_eventualCoMovingLeftBand
    {U : ℝ → ℝ} (hright : Tendsto U atTop (𝓝 0))
    {s c ell M : ℝ} (hsc : s < c) (hell : 0 < ell) :
    ¬ EventualCoMovingLeftBand c ell M
      (travelingWaveLaboratoryProfile s U) := by
  rintro ⟨T, cut, hband⟩
  have hsmall : ∀ᶠ t in atTop,
      convectiveEscapeProfile U s c t cut < ell :=
    (tendsto_order.1
      (convectiveEscapeProfile_tendsto_atTop_time hright hsc cut)).2
        ell hell
  obtain ⟨t, ht, hlt⟩ :=
    ((eventually_ge_atTop T).and hsmall).exists
  have hlower := (hband t ht cut le_rfl).1
  rw [coMovingPath_travelingWaveLaboratoryProfile] at hlower
  exact (not_lt_of_ge hlower) hlt

/-- For every genuine traveling-wave profile, slice positivity and failure of
the uniform floor coexist whenever the observation frame is faster than the
wave. -/
theorem IsTravelingWave.convectiveEscape_quantifier_obstruction
    {p : CMParams} {s c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p s U V) (hsc : s < c) :
    (∀ t, Tendsto (convectiveEscapeProfile U s c t) atBot (𝓝 1)) ∧
    (∀ t, StrictlyPositiveAtLeft (convectiveEscapeProfile U s c t)) ∧
    (∀ ell, 0 < ell → ∀ T R,
      ∃ t z : ℝ, T ≤ t ∧ z ≤ -R ∧
        convectiveEscapeProfile U s c t z < ell) ∧
    (∀ ell M, 0 < ell →
      ¬ EventualCoMovingLeftBand c ell M
        (travelingWaveLaboratoryProfile s U)) := by
  refine ⟨fun t =>
      convectiveEscapeProfile_tendsto_atBot hTW.lim_neg_inf.1 s c t,
    fun t =>
      convectiveEscapeProfile_strictlyPositiveAtLeft
        hTW.lim_neg_inf.1 s c t, ?_, ?_⟩
  · intro ell hell T R
    exact convectiveEscapeProfile_exists_late_left_lt
      hTW.lim_pos_inf.1 hsc hell T R
  · intro ell M hell
    exact travelingWaveLaboratoryProfile_not_eventualCoMovingLeftBand
      hTW.lim_pos_inf.1 hsc hell

section AxiomAudit

#print axioms StrictlyPositiveAtLeft.exists_leftHalfLine_floor
#print axioms wholeLineCauchyGlobal_exists_timeSlice_coMoving_left_floor
#print axioms wholeLineGlobalMaximalBUCOrbit_strictlyPositiveAtLeft
#print axioms
  wholeLineGlobalMaximalBUCOrbit_exists_timeSlice_coMoving_left_floor
#print axioms coMovingPath_travelingWaveLaboratoryProfile
#print axioms convectiveEscapeProfile_tendsto_atBot
#print axioms convectiveEscapeProfile_strictlyPositiveAtLeft
#print axioms convectiveEscapeProfile_tendsto_atTop_time
#print axioms convectiveEscapeProfile_exists_late_left_lt
#print axioms convectiveEscapeProfile_no_uniform_left_floor
#print axioms
  travelingWaveLaboratoryProfile_not_eventualCoMovingLeftBand
#print axioms IsTravelingWave.convectiveEscape_quantifier_obstruction

end AxiomAudit

end ShenWork.Paper1
