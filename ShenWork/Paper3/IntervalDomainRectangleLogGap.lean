import ShenWork.Paper3.IntervalDomainRectangleExtremumSlopes
import ShenWork.Paper3.CompactExtremumDini
import ShenWork.Paper2.IntervalDomainSliceMinPos

/-!
# Clamped logarithmic gap for the interval rectangle argument

The upper and lower population envelopes are clamped at the positive logistic
equilibrium.  A single compact choice space records both extrema: each factor
chooses either the equilibrium or a physical point of the closed interval.
Maximizing the logarithmic difference on the product therefore selects the
clamped maximum and minimum simultaneously.  This is the correct input for one
right-upper Dini estimate; two separate `Frequently` conclusions could not be
intersected.
-/

open Filter Set Topology
open ShenWork.IntervalDomain ShenWork.Paper2
open ShenWork.MinPersistenceAtoms ShenWork.MaxPrincipleAtoms

namespace ShenWork.Paper3

noncomputable section

/-- One clamped-envelope choice: the equilibrium or a physical interval point. -/
abbrev intervalRectangleEnvelopeChoice := Unit ⊕ intervalDomainPoint

/-- The compact pair selecting the upper and lower clamped envelopes. -/
abbrev intervalRectangleGapChoice :=
  intervalRectangleEnvelopeChoice × intervalRectangleEnvelopeChoice

/-- Evaluate one envelope choice against a population orbit. -/
def intervalDomain_equilibriumChoiceValue
    (uStar : ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) : intervalRectangleEnvelopeChoice → ℝ
  | Sum.inl _ => uStar
  | Sum.inr x => u t x

/-- Logarithmic spread associated with one simultaneous upper/lower choice. -/
def intervalDomain_rectangleLogGapChoice
    (uStar : ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) (q : intervalRectangleGapChoice) : ℝ :=
  Real.log (intervalDomain_equilibriumChoiceValue uStar u t q.1) -
    Real.log (intervalDomain_equilibriumChoiceValue uStar u t q.2)

/-- Population maximum clamped from below at the positive equilibrium. -/
def intervalDomain_clampedUpper
    (uStar : ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) : ℝ :=
  max uStar
    (sSup (intervalDomainLift (u t) '' Icc (0 : ℝ) 1))

/-- Population minimum clamped from above at the positive equilibrium. -/
def intervalDomain_clampedLower
    (uStar : ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) : ℝ :=
  min uStar
    (sInf (intervalDomainLift (u t) '' Icc (0 : ℝ) 1))

/-- The clamped logarithmic oscillation used in the rectangle proof. -/
def intervalDomain_rectangleLogGap
    (uStar : ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) : ℝ :=
  Real.log (intervalDomain_clampedUpper uStar u t) -
    Real.log (intervalDomain_clampedLower uStar u t)

@[simp] theorem intervalDomain_equilibriumChoiceValue_inl
    (uStar : ℝ) (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ)
    (z : Unit) :
    intervalDomain_equilibriumChoiceValue uStar u t (Sum.inl z) = uStar :=
  rfl

@[simp] theorem intervalDomain_equilibriumChoiceValue_inr
    (uStar : ℝ) (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ)
    (x : intervalDomainPoint) :
    intervalDomain_equilibriumChoiceValue uStar u t (Sum.inr x) = u t x :=
  rfl

/-- Every envelope choice is positive at a positive classical time. -/
theorem intervalDomain_equilibriumChoiceValue_pos
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huStar : 0 < uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    ∀ q : intervalRectangleEnvelopeChoice,
      0 < intervalDomain_equilibriumChoiceValue uStar u t q := by
  rintro (z | x)
  · simpa using huStar
  · simpa using hsol.u_pos' ht.1 ht.2

/-- The clamped lower envelope stays strictly positive on every classical
positive-time slice. -/
theorem intervalDomain_clampedLower_pos
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huStar : 0 < uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    0 < intervalDomain_clampedLower uStar u t := by
  rw [intervalDomain_clampedLower]
  exact lt_min huStar (sliceMin_pos_of_solution hsol ht.1 ht.2)

/-- The equilibrium lies between the two clamped envelopes. -/
theorem intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
    (uStar : ℝ) (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) :
    intervalDomain_clampedLower uStar u t ≤ uStar ∧
      uStar ≤ intervalDomain_clampedUpper uStar u t := by
  exact ⟨min_le_left _ _, le_max_left _ _⟩

/-- The clamped logarithmic gap is nonnegative on a positive classical slice. -/
theorem intervalDomain_rectangleLogGap_nonneg
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huStar : 0 < uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    0 ≤ intervalDomain_rectangleLogGap uStar u t := by
  have hlo : 0 < intervalDomain_clampedLower uStar u t :=
    intervalDomain_clampedLower_pos huStar hsol ht
  have horder : intervalDomain_clampedLower uStar u t ≤
      intervalDomain_clampedUpper uStar u t :=
    (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
      uStar u t).1.trans
      (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
        uStar u t).2
  have hlog := Real.log_le_log hlo horder
  simpa [intervalDomain_rectangleLogGap] using sub_nonneg.mpr hlog

/-- Every equilibrium/spatial choice lies between the clamped envelopes. -/
theorem intervalDomain_equilibriumChoiceValue_mem_clamped
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    ∀ q : intervalRectangleEnvelopeChoice,
      intervalDomain_clampedLower uStar u t ≤
          intervalDomain_equilibriumChoiceValue uStar u t q ∧
        intervalDomain_equilibriumChoiceValue uStar u t q ≤
          intervalDomain_clampedUpper uStar u t := by
  obtain ⟨_, _, _, _, hclosed, _, _⟩ := hsol.regularity
  have hslice : ContinuousOn (intervalDomainLift (u t)) (Icc (0 : ℝ) 1) :=
    (hclosed t ht).1.1.continuousOn
  have himg : IsCompact
      (intervalDomainLift (u t) '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hslice
  rintro (z | x)
  · exact intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
      uStar u t
  · have hmem : intervalDomainLift (u t) x.1 ∈
        intervalDomainLift (u t) '' Icc (0 : ℝ) 1 :=
      Set.mem_image_of_mem _ x.2
    have hlift : intervalDomainLift (u t) x.1 = u t x := by
      simp [intervalDomainLift]
    constructor
    · exact (min_le_right uStar _).trans
        (by simpa [hlift] using csInf_le himg.bddBelow hmem)
    · have hle : u t x ≤
          sSup (intervalDomainLift (u t) '' Icc (0 : ℝ) 1) := by
        simpa [hlift] using le_csSup himg.bddAbove hmem
      exact hle.trans (le_max_right uStar _)

/-- The clamped upper envelope is realized by one compact envelope choice. -/
theorem intervalDomain_exists_choiceValue_eq_clampedUpper
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    ∃ q : intervalRectangleEnvelopeChoice,
      intervalDomain_equilibriumChoiceValue uStar u t q =
        intervalDomain_clampedUpper uStar u t := by
  obtain ⟨_, _, _, _, hclosed, _, _⟩ := hsol.regularity
  have hslice : ContinuousOn (intervalDomainLift (u t)) (Icc (0 : ℝ) 1) :=
    (hclosed t ht).1.1.continuousOn
  have himg : IsCompact
      (intervalDomainLift (u t) '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hslice
  have hne : (intervalDomainLift (u t) '' Icc (0 : ℝ) 1).Nonempty :=
    (nonempty_Icc.mpr zero_le_one).image _
  by_cases hle : uStar ≤ sSup (intervalDomainLift (u t) '' Icc (0 : ℝ) 1)
  · obtain ⟨y, hy, hyeq⟩ := himg.sSup_mem hne
    let x : intervalDomainPoint := ⟨y, hy⟩
    refine ⟨Sum.inr x, ?_⟩
    rw [intervalDomain_equilibriumChoiceValue_inr,
      intervalDomain_clampedUpper, max_eq_right hle]
    simpa [x, intervalDomainLift, hy] using hyeq
  · refine ⟨Sum.inl (), ?_⟩
    rw [intervalDomain_equilibriumChoiceValue_inl,
      intervalDomain_clampedUpper,
      max_eq_left (le_of_not_ge hle)]

/-- The clamped lower envelope is realized by one compact envelope choice. -/
theorem intervalDomain_exists_choiceValue_eq_clampedLower
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    ∃ q : intervalRectangleEnvelopeChoice,
      intervalDomain_equilibriumChoiceValue uStar u t q =
        intervalDomain_clampedLower uStar u t := by
  obtain ⟨_, _, _, _, hclosed, _, _⟩ := hsol.regularity
  have hslice : ContinuousOn (intervalDomainLift (u t)) (Icc (0 : ℝ) 1) :=
    (hclosed t ht).1.1.continuousOn
  have himg : IsCompact
      (intervalDomainLift (u t) '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hslice
  have hne : (intervalDomainLift (u t) '' Icc (0 : ℝ) 1).Nonempty :=
    (nonempty_Icc.mpr zero_le_one).image _
  by_cases hle : sInf (intervalDomainLift (u t) '' Icc (0 : ℝ) 1) ≤ uStar
  · obtain ⟨y, hy, hyeq⟩ := himg.sInf_mem hne
    let x : intervalDomainPoint := ⟨y, hy⟩
    refine ⟨Sum.inr x, ?_⟩
    rw [intervalDomain_equilibriumChoiceValue_inr,
      intervalDomain_clampedLower, min_eq_right hle]
    simpa [x, intervalDomainLift, hy] using hyeq
  · refine ⟨Sum.inl (), ?_⟩
    rw [intervalDomain_equilibriumChoiceValue_inl,
      intervalDomain_clampedLower,
      min_eq_left (le_of_not_ge hle)]

/-- The compact-choice maximum is exactly the clamped logarithmic gap. -/
theorem intervalDomain_rectangleLogGapChoice_sSup_eq
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huStar : 0 < uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    sSup (intervalDomain_rectangleLogGapChoice uStar u t ''
        (Set.univ : Set intervalRectangleGapChoice)) =
      intervalDomain_rectangleLogGap uStar u t := by
  obtain ⟨qhi, hqhi⟩ :=
    intervalDomain_exists_choiceValue_eq_clampedUpper
      (uStar := uStar) hsol ht
  obtain ⟨qlo, hqlo⟩ :=
    intervalDomain_exists_choiceValue_eq_clampedLower
      (uStar := uStar) hsol ht
  let qstar : intervalRectangleGapChoice := (qhi, qlo)
  have hqstar : intervalDomain_rectangleLogGapChoice uStar u t qstar =
      intervalDomain_rectangleLogGap uStar u t := by
    simp [qstar, intervalDomain_rectangleLogGapChoice,
      intervalDomain_rectangleLogGap, hqhi, hqlo]
  have hall : ∀ q : intervalRectangleGapChoice,
      intervalDomain_rectangleLogGapChoice uStar u t q ≤
        intervalDomain_rectangleLogGap uStar u t := by
    intro q
    have hbhi := (intervalDomain_equilibriumChoiceValue_mem_clamped
      (uStar := uStar) hsol ht q.1).2
    have hblo := (intervalDomain_equilibriumChoiceValue_mem_clamped
      (uStar := uStar) hsol ht q.2).1
    have hvhi := intervalDomain_equilibriumChoiceValue_pos huStar hsol ht q.1
    have hlo := intervalDomain_clampedLower_pos huStar hsol ht
    have hloghi := Real.log_le_log hvhi hbhi
    have hloglo := Real.log_le_log hlo hblo
    simp only [intervalDomain_rectangleLogGapChoice,
      intervalDomain_rectangleLogGap]
    linarith
  have hmem : intervalDomain_rectangleLogGapChoice uStar u t qstar ∈
      intervalDomain_rectangleLogGapChoice uStar u t ''
        (Set.univ : Set intervalRectangleGapChoice) :=
    Set.mem_image_of_mem _ (Set.mem_univ qstar)
  have hbdd : BddAbove
      (intervalDomain_rectangleLogGapChoice uStar u t ''
        (Set.univ : Set intervalRectangleGapChoice)) :=
    ⟨intervalDomain_rectangleLogGap uStar u t, by
      rintro _ ⟨q, _, rfl⟩
      exact hall q⟩
  apply le_antisymm
  · apply csSup_le ⟨_, hmem⟩
    rintro _ ⟨q, _, rfl⟩
    exact hall q
  · rw [← hqstar]
    exact le_csSup hbdd hmem

/-- Joint continuity of the compact-choice logarithmic spread on a closed
positive-time slab. -/
theorem intervalDomain_rectangleLogGapChoice_jointContinuousOn
    {p : CM2Params} {T a b uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huStar : 0 < uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hab : Icc a b ⊆ Ioo (0 : ℝ) T) :
    ContinuousOn
      (Function.uncurry (intervalDomain_rectangleLogGapChoice uStar u))
      (Icc a b ×ˢ (Set.univ : Set intervalRectangleGapChoice)) := by
  let Time := {t : ℝ // t ∈ Icc a b}
  obtain ⟨_, _, _, _, _, _, hjoint⟩ := hsol.regularity
  have hU : Continuous (fun z : Time × intervalDomainPoint =>
      u z.1.1 z.2) := by
    have hbase := continuousOn_iff_continuous_restrict.mp
      (hjoint.1.mono (Set.prod_mono hab (le_refl _)))
    have hmap : Continuous (fun z : Time × intervalDomainPoint =>
        (⟨(z.1.1, z.2.1), ⟨z.1.2, z.2.2⟩⟩ :
          ↑(Icc a b ×ˢ Icc (0 : ℝ) 1))) := by
      exact Continuous.subtype_mk
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)) _
    have hc := hbase.comp hmap
    change Continuous (fun z : Time × intervalDomainPoint =>
      intervalDomainLift (u z.1.1) z.2.1) at hc
    convert hc using 1
    funext z
    simp [intervalDomainLift]
  let leftValue : Time × Unit → ℝ := fun _ => uStar
  let rightValue : Time × intervalDomainPoint → ℝ :=
    fun z => u z.1.1 z.2
  let value : Time × intervalRectangleEnvelopeChoice → ℝ :=
    fun z => intervalDomain_equilibriumChoiceValue uStar u z.1.1 z.2
  have hvalue : Continuous value := by
    have hsum : Continuous (Sum.elim leftValue rightValue) :=
      Continuous.sumElim continuous_const hU
    let e : Time × (Unit ⊕ intervalDomainPoint) ≃ₜ
        (Time × Unit) ⊕ (Time × intervalDomainPoint) :=
      Homeomorph.prodSumDistrib
    have heq : value =
        (Sum.elim leftValue rightValue) ∘ e := by
      funext z
      rcases z with ⟨t, q⟩
      rcases q with z | x <;> rfl
    rw [heq]
    exact hsum.comp e.continuous
  have hgap : Continuous (fun z : Time × intervalRectangleGapChoice =>
      intervalDomain_rectangleLogGapChoice uStar u z.1.1 z.2) := by
    have htop : Continuous (fun z : Time × intervalRectangleGapChoice =>
        value (z.1, z.2.1)) := hvalue.comp (by fun_prop)
    have hbot : Continuous (fun z : Time × intervalRectangleGapChoice =>
        value (z.1, z.2.2)) := hvalue.comp (by fun_prop)
    have htopLog := htop.log (fun z => by
      exact ne_of_gt (intervalDomain_equilibriumChoiceValue_pos huStar hsol
        (hab z.1.2) z.2.1))
    have hbotLog := hbot.log (fun z => by
      exact ne_of_gt (intervalDomain_equilibriumChoiceValue_pos huStar hsol
        (hab z.1.2) z.2.2))
    simpa [value, intervalDomain_rectangleLogGapChoice] using
      htopLog.sub hbotLog
  rw [continuousOn_iff_continuous_restrict]
  have hmap : Continuous
      (fun z : ↑(Icc a b ×ˢ (Set.univ : Set intervalRectangleGapChoice)) =>
        ((⟨z.1.1, z.2.1⟩ : Time), z.1.2)) := by
    fun_prop
  simpa [Function.uncurry] using hgap.comp hmap

#print axioms intervalDomain_equilibriumChoiceValue_pos
#print axioms intervalDomain_clampedLower_pos
#print axioms intervalDomain_rectangleLogGap_nonneg
#print axioms intervalDomain_equilibriumChoiceValue_mem_clamped
#print axioms intervalDomain_rectangleLogGapChoice_sSup_eq
#print axioms intervalDomain_rectangleLogGapChoice_jointContinuousOn

end

end ShenWork.Paper3
