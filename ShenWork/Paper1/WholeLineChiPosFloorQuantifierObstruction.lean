import ShenWork.Paper1.WholeLineChiPosDeepHoleRefill
import ShenWork.Paper1.WholeLineChiPosEntropyFarLeftNormalFamily
import ShenWork.Paper1.WholeLineChiPosHalfLineSeedMGTOne
import ShenWork.Paper1.WholeLineChiPosPhysicalSegmentStrictPositivity
import ShenWork.Paper1.WholeLineMaximalBUCImport
import ShenWork.Paper1.WholeLinePhysicalMildSegments

/-!
# The quantifier obstruction in the positive-sensitivity far-left floor

The canonical positivity theory preserves `StrictlyPositiveAtLeft` on every
fixed co-moving time slice.  This gives

`∀ t ≥ 0, ∃ ell_t > 0, ∃ R_t, ∀ z ≤ R_t, ell_t ≤ q(t,z)`.

The persistent floor needed by `EventualCoMovingLeftBand` reverses the first
three quantifiers: one needs a single `ell`, `T`, and `R` for every `t ≥ T`.

The explicit smooth family

`q(t,z) = 1 / (1 + exp (z+t))`

records why slice positivity and an interior-minimum refill certificate do not
by themselves justify that reversal.  Every slice has the fixed height `1/2`
on `z ≤ -t`, but the cut retreats to `-∞`, so there is no eventual positive
floor on any fixed left half-line.  Moreover every slice is strictly
decreasing and has no spatial local minimum.  Thus a refill result whose
hypotheses begin at an interior minimum, such as
`deepHole_minimum_refill_of_local_ceiling`, cannot see this escape mode.

This is a logical obstruction only, not a counterexample to the
chemotaxis--logistic PDE.  Closing the PDE floor requires an additional
anti-escape estimate that uniformly controls the location of the left
plateau (or an equivalent boundary/nondegeneracy estimate).
-/

open Filter Function Set

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

/-- A smooth positive plateau whose transition point retreats linearly to
the left. -/
def retreatingLogisticPlateau (t z : ℝ) : ℝ :=
  1 / (1 + Real.exp (z + t))

/-- At time `t`, the retreating plateau still has height at least `1/2` on
the time-dependent half-line `z ≤ -t`. -/
theorem retreatingLogisticPlateau_ge_half
    (t : ℝ) {z : ℝ} (hz : z ≤ -t) :
    1 / 2 ≤ retreatingLogisticPlateau t z := by
  have hexp : Real.exp (z + t) ≤ 1 := by
    calc
      Real.exp (z + t) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hden : 0 < 1 + Real.exp (z + t) := by positivity
  rw [retreatingLogisticPlateau]
  apply (le_div_iff₀ hden).2
  nlinarith

/-- Every fixed time slice of the retreating plateau is strictly positive at
the left end. -/
theorem retreatingLogisticPlateau_strictlyPositiveAtLeft (t : ℝ) :
    StrictlyPositiveAtLeft (retreatingLogisticPlateau t) := by
  refine ⟨1 / 2, by norm_num, eventually_atBot.2 ⟨-t, ?_⟩⟩
  intro z hz
  exact retreatingLogisticPlateau_ge_half t hz

/-- Exact spatial derivative of the retreating plateau. -/
theorem retreatingLogisticPlateau_hasDerivAt (t z : ℝ) :
    HasDerivAt (retreatingLogisticPlateau t)
      (-Real.exp (z + t) / (1 + Real.exp (z + t)) ^ 2) z := by
  have hlin : HasDerivAt (fun y : ℝ => y + t) 1 z := by
    simpa using (hasDerivAt_id z).add_const t
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (y + t))
      (Real.exp (z + t)) z := by
    simpa only [Function.comp_apply, mul_one] using
      (Real.hasDerivAt_exp (z + t)).comp z hlin
  have hden : HasDerivAt (fun y : ℝ => 1 + Real.exp (y + t))
      (Real.exp (z + t)) z := by
    simpa only [zero_add] using
      (hasDerivAt_const z (1 : ℝ)).add hexp
  have hraw := (hasDerivAt_const z (1 : ℝ)).div hden
    (by positivity : 1 + Real.exp (z + t) ≠ 0)
  simpa only [retreatingLogisticPlateau, zero_mul, one_mul, zero_sub] using hraw

/-- Every spatial slice is strictly decreasing. -/
theorem retreatingLogisticPlateau_deriv_neg (t z : ℝ) :
    deriv (retreatingLogisticPlateau t) z < 0 := by
  rw [(retreatingLogisticPlateau_hasDerivAt t z).deriv]
  exact div_neg_of_neg_of_pos
    (neg_neg_iff_pos.mpr (Real.exp_pos _))
    (sq_pos_of_pos (by positivity))

/-- In particular, the retreating plateau has no spatial local minimum, so
an interior-minimum refill lemma is vacuous on this escape mode. -/
theorem retreatingLogisticPlateau_not_isLocalMin (t z : ℝ) :
    ¬ IsLocalMin (retreatingLogisticPlateau t) z := by
  intro hmin
  have hzero :=
    hmin.hasDerivAt_eq_zero
      (retreatingLogisticPlateau_hasDerivAt t z)
  have hneg : -Real.exp (z + t) /
      (1 + Real.exp (z + t)) ^ 2 < 0 :=
    div_neg_of_neg_of_pos
      (neg_neg_iff_pos.mpr (Real.exp_pos _))
      (sq_pos_of_pos (by positivity))
  linarith

/-- At every proposed start time and fixed cut, the retreating plateau
eventually falls below any prescribed positive height. -/
theorem exists_late_retreatingLogisticPlateau_lt
    {ell : ℝ} (hell : 0 < ell) (start cut : ℝ) :
    ∃ t : ℝ, start ≤ t ∧ retreatingLogisticPlateau t cut < ell := by
  let t : ℝ := max start (Real.log (1 / ell) - cut + 1)
  have hstart : start ≤ t := by
    exact le_max_left _ _
  have hlog_lt : Real.log (1 / ell) < cut + t := by
    have ht : Real.log (1 / ell) - cut + 1 ≤ t := le_max_right _ _
    linarith
  have hinvpos : 0 < 1 / ell := one_div_pos.mpr hell
  have hexp : 1 / ell < Real.exp (cut + t) := by
    calc
      1 / ell = Real.exp (Real.log (1 / ell)) :=
        (Real.exp_log hinvpos).symm
      _ < Real.exp (cut + t) := Real.exp_lt_exp.mpr hlog_lt
  have hden : 0 < 1 + Real.exp (cut + t) := by positivity
  refine ⟨t, hstart, ?_⟩
  rw [retreatingLogisticPlateau]
  apply (div_lt_iff₀ hden).2
  have hscaled := mul_lt_mul_of_pos_left hexp hell
  have hcancel : ell * (1 / ell) = 1 := by
    field_simp
  rw [hcancel] at hscaled
  nlinarith

/-- Slice-by-slice left positivity does not imply a persistent lower band:
the smooth retreating plateau has no positive
`EventualCoMovingLeftBand` even in the stationary frame. -/
theorem retreatingLogisticPlateau_not_eventualCoMovingLeftBand
    {ell M : ℝ} (hell : 0 < ell) :
    ¬ EventualCoMovingLeftBand 0 ell M retreatingLogisticPlateau := by
  rintro ⟨start, cut, hband⟩
  obtain ⟨t, ht, hsmall⟩ :=
    exists_late_retreatingLogisticPlateau_lt hell start cut
  have hlower := (hband t ht cut le_rfl).1
  simp only [coMovingPath, zero_mul, add_zero] at hlower
  exact (not_lt_of_ge hlower) hsmall

/-- Combined quantifier counterexample: every slice has a positive left
plateau and no spatial local minimum, yet no fixed positive eventual band
exists. -/
theorem
    exists_strictlyPositiveAtLeft_slices_without_eventualCoMovingLeftBand :
    ∃ orbit : ℝ → ℝ → ℝ,
      (∀ t, StrictlyPositiveAtLeft (orbit t)) ∧
      (∀ t z, ¬ IsLocalMin (orbit t) z) ∧
      ∀ ell M, 0 < ell →
        ¬ EventualCoMovingLeftBand 0 ell M orbit := by
  exact ⟨retreatingLogisticPlateau,
    retreatingLogisticPlateau_strictlyPositiveAtLeft,
    retreatingLogisticPlateau_not_isLocalMin,
    fun _ell _M hell =>
      retreatingLogisticPlateau_not_eventualCoMovingLeftBand hell⟩

section AxiomAudit

#print axioms StrictlyPositiveAtLeft.exists_leftHalfLine_floor
#print axioms wholeLineCauchyGlobal_exists_timeSlice_coMoving_left_floor
#print axioms wholeLineGlobalMaximalBUCOrbit_strictlyPositiveAtLeft
#print axioms
  wholeLineGlobalMaximalBUCOrbit_exists_timeSlice_coMoving_left_floor
#print axioms retreatingLogisticPlateau_ge_half
#print axioms retreatingLogisticPlateau_strictlyPositiveAtLeft
#print axioms retreatingLogisticPlateau_hasDerivAt
#print axioms retreatingLogisticPlateau_deriv_neg
#print axioms retreatingLogisticPlateau_not_isLocalMin
#print axioms exists_late_retreatingLogisticPlateau_lt
#print axioms retreatingLogisticPlateau_not_eventualCoMovingLeftBand
#print axioms
  exists_strictlyPositiveAtLeft_slices_without_eventualCoMovingLeftBand

end AxiomAudit

end ShenWork.Paper1
