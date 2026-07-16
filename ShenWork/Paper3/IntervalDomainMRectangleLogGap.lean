import ShenWork.Paper3.IntervalDomainMRectangleExtremumSlopes
import ShenWork.Paper3.IntervalDomainRectangleLogGap
import ShenWork.Paper3.CompactExtremumDini
import ShenWork.Paper2.IntervalDomainSliceMinPos

/-!
# Clamped logarithmic gap for the faithful general-`m` rectangle argument

`intervalDomainM` counterpart of `IntervalDomainRectangleLogGap`.  The clamped
envelope / choice structural definitions are domain-free and reused from the
`m = 1` file; only the log-slope bound fields change, gaining a `U^(m-1)`
(resp. `L^(m-1)`) chemotaxis prefactor inherited from the `u^m` extremum slope
bounds.  Every regularity-only lemma is the byte-identical proof with the
solution predicate typed at `intervalDomainM`.
-/

open Filter Set Topology
open ShenWork.IntervalDomain ShenWork.Paper2
open ShenWork.MinPersistenceAtoms ShenWork.MaxPrincipleAtoms

namespace ShenWork.Paper3

noncomputable section

/-- General-`m` slice-minimum positivity (the `sliceMin_pos_of_solution`
analogue for the faithful equation; regularity-only). -/
theorem intervalDomainM_sliceMin_pos_of_solution
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    0 < sInf (intervalDomainLift (u t) '' Set.Icc (0:ℝ) 1) := by
  have hslice_cont : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0:ℝ) 1) := by
    obtain ⟨_, _, _, _, h7, _, _⟩ := hsol.regularity
    exact (h7 t ⟨ht0, htT⟩).1.1.continuousOn
  have himg : IsCompact (intervalDomainLift (u t) '' Set.Icc (0:ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hslice_cont
  have hne : (intervalDomainLift (u t) '' Set.Icc (0:ℝ) 1).Nonempty :=
    ⟨intervalDomainLift (u t) 0,
      Set.mem_image_of_mem _ (Set.left_mem_Icc.mpr zero_le_one)⟩
  obtain ⟨x0, hx0_mem, hx0_eq⟩ := himg.sInf_mem hne
  rw [← hx0_eq, intervalDomainLift, dif_pos hx0_mem]
  exact hsol.u_pos' ht0 htT

/-- Upper general-`m` logarithmic rectangle vector field (with `U^(m-1)`). -/
def intervalDomainM_rectangleUpperLogSlopeBound
    (p : CM2Params) (uStar : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) : ℝ :=
  let U := intervalDomain_clampedUpper uStar u t
  let L := intervalDomain_clampedLower uStar u t
  p.a - p.b * U ^ p.α +
    p.χ₀ * U ^ (p.m - 1) * (p.ν * (U ^ p.γ - L ^ p.γ) +
      p.β * (unitIntervalResolverGradientOscillationConstant p *
        (p.ν * (U ^ p.γ - L ^ p.γ))) ^ 2)

/-- Lower general-`m` logarithmic rectangle vector field (with `L^(m-1)`). -/
def intervalDomainM_rectangleLowerLogSlopeBound
    (p : CM2Params) (uStar : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) : ℝ :=
  let U := intervalDomain_clampedUpper uStar u t
  let L := intervalDomain_clampedLower uStar u t
  (-p.χ₀) * L ^ (p.m - 1) * p.ν * (U ^ p.γ - L ^ p.γ) +
    p.a - p.b * L ^ p.α

/-- Combined general-`m` scalar right-hand side for the clamped log gap. -/
def intervalDomainM_rectangleLogGapSlopeBound
    (p : CM2Params) (uStar : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) : ℝ :=
  intervalDomainM_rectangleUpperLogSlopeBound p uStar u t -
    intervalDomainM_rectangleLowerLogSlopeBound p uStar u t

/-- Weighted upper general-`m` logarithmic rectangle vector field. -/
def intervalDomainM_rectangleUpperLogSlopeBound_with_weight
    (p : CM2Params) (q uStar : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) : ℝ :=
  let U := intervalDomain_clampedUpper uStar u t
  let L := intervalDomain_clampedLower uStar u t
  p.a - p.b * U ^ p.α +
    p.χ₀ * q * U ^ (p.m - 1) * (p.ν * (U ^ p.γ - L ^ p.γ) +
      p.β * (unitIntervalResolverGradientOscillationConstant p *
        (p.ν * (U ^ p.γ - L ^ p.γ))) ^ 2)

/-- Weighted lower general-`m` logarithmic rectangle vector field. -/
def intervalDomainM_rectangleLowerLogSlopeBound_with_weight
    (p : CM2Params) (q uStar : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) : ℝ :=
  let U := intervalDomain_clampedUpper uStar u t
  let L := intervalDomain_clampedLower uStar u t
  (-p.χ₀ * q) * L ^ (p.m - 1) * p.ν * (U ^ p.γ - L ^ p.γ) +
    p.a - p.b * L ^ p.α

/-- Combined weighted general-`m` log-gap vector field. -/
def intervalDomainM_rectangleLogGapSlopeBound_with_weight
    (p : CM2Params) (q uStar : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) : ℝ :=
  intervalDomainM_rectangleUpperLogSlopeBound_with_weight p q uStar u t -
    intervalDomainM_rectangleLowerLogSlopeBound_with_weight p q uStar u t

/-- Every envelope choice is positive at a positive classical time. -/
theorem intervalDomainM_equilibriumChoiceValue_pos
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huStar : 0 < uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    ∀ q : intervalRectangleEnvelopeChoice,
      0 < intervalDomain_equilibriumChoiceValue uStar u t q := by
  rintro (z | x)
  · simpa using huStar
  · simpa using hsol.u_pos' ht.1 ht.2

/-- The clamped lower envelope stays strictly positive on every classical
positive-time slice. -/
theorem intervalDomainM_clampedLower_pos
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huStar : 0 < uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    0 < intervalDomain_clampedLower uStar u t := by
  rw [intervalDomain_clampedLower]
  exact lt_min huStar (intervalDomainM_sliceMin_pos_of_solution hsol ht.1 ht.2)

/-- The clamped logarithmic gap is nonnegative on a positive classical slice. -/
theorem intervalDomainM_rectangleLogGap_nonneg
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huStar : 0 < uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    0 ≤ intervalDomain_rectangleLogGap uStar u t := by
  have hlo : 0 < intervalDomain_clampedLower uStar u t :=
    intervalDomainM_clampedLower_pos huStar hsol ht
  have horder : intervalDomain_clampedLower uStar u t ≤
      intervalDomain_clampedUpper uStar u t :=
    (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
      uStar u t).1.trans
      (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
        uStar u t).2
  have hlog := Real.log_le_log hlo horder
  simpa [intervalDomain_rectangleLogGap] using sub_nonneg.mpr hlog

/-- Every equilibrium/spatial choice lies between the clamped envelopes. -/
theorem intervalDomainM_equilibriumChoiceValue_mem_clamped
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
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
theorem intervalDomainM_exists_choiceValue_eq_clampedUpper
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
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
theorem intervalDomainM_exists_choiceValue_eq_clampedLower
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
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
theorem intervalDomainM_rectangleLogGapChoice_sSup_eq
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huStar : 0 < uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    sSup (intervalDomain_rectangleLogGapChoice uStar u t ''
        (Set.univ : Set intervalRectangleGapChoice)) =
      intervalDomain_rectangleLogGap uStar u t := by
  obtain ⟨qhi, hqhi⟩ :=
    intervalDomainM_exists_choiceValue_eq_clampedUpper
      (uStar := uStar) hsol ht
  obtain ⟨qlo, hqlo⟩ :=
    intervalDomainM_exists_choiceValue_eq_clampedLower
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
    have hbhi := (intervalDomainM_equilibriumChoiceValue_mem_clamped
      (uStar := uStar) hsol ht q.1).2
    have hblo := (intervalDomainM_equilibriumChoiceValue_mem_clamped
      (uStar := uStar) hsol ht q.2).1
    have hvhi := intervalDomainM_equilibriumChoiceValue_pos huStar hsol ht q.1
    have hlo := intervalDomainM_clampedLower_pos huStar hsol ht
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

/-- An exact maximizer of the logarithmic choice spread realizes both clamped
envelopes separately. -/
theorem intervalDomainM_rectangleLogGapChoice_argmax_values
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huStar : 0 < uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (q : intervalRectangleGapChoice)
    (harg : intervalDomain_rectangleLogGapChoice uStar u t q =
      sSup (intervalDomain_rectangleLogGapChoice uStar u t ''
        (Set.univ : Set intervalRectangleGapChoice))) :
    intervalDomain_equilibriumChoiceValue uStar u t q.1 =
        intervalDomain_clampedUpper uStar u t ∧
      intervalDomain_equilibriumChoiceValue uStar u t q.2 =
        intervalDomain_clampedLower uStar u t := by
  rw [intervalDomainM_rectangleLogGapChoice_sSup_eq huStar hsol ht] at harg
  have htopBound := (intervalDomainM_equilibriumChoiceValue_mem_clamped
    (uStar := uStar) hsol ht q.1).2
  have hbotBound := (intervalDomainM_equilibriumChoiceValue_mem_clamped
    (uStar := uStar) hsol ht q.2).1
  have htopPos := intervalDomainM_equilibriumChoiceValue_pos
    huStar hsol ht q.1
  have hbotPos := intervalDomainM_equilibriumChoiceValue_pos
    huStar hsol ht q.2
  have hloPos := intervalDomainM_clampedLower_pos huStar hsol ht
  have hhiPos : 0 < intervalDomain_clampedUpper uStar u t :=
    huStar.trans_le
      (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
        uStar u t).2
  have htopLog : Real.log
        (intervalDomain_equilibriumChoiceValue uStar u t q.1) ≤
      Real.log (intervalDomain_clampedUpper uStar u t) :=
    Real.log_le_log htopPos htopBound
  have hbotLog : Real.log (intervalDomain_clampedLower uStar u t) ≤
      Real.log (intervalDomain_equilibriumChoiceValue uStar u t q.2) :=
    Real.log_le_log hloPos hbotBound
  have htopLogEq : Real.log
        (intervalDomain_equilibriumChoiceValue uStar u t q.1) =
      Real.log (intervalDomain_clampedUpper uStar u t) := by
    unfold intervalDomain_rectangleLogGapChoice
      intervalDomain_rectangleLogGap at harg
    linarith
  have hbotLogEq : Real.log
        (intervalDomain_equilibriumChoiceValue uStar u t q.2) =
      Real.log (intervalDomain_clampedLower uStar u t) := by
    unfold intervalDomain_rectangleLogGapChoice
      intervalDomain_rectangleLogGap at harg
    linarith
  constructor
  · have he := congrArg Real.exp htopLogEq
    simpa [Real.exp_log htopPos, Real.exp_log hhiPos] using he
  · have he := congrArg Real.exp hbotLogEq
    simpa [Real.exp_log hbotPos, Real.exp_log hloPos] using he

/-- An upper choice realizing the clamped maximum obeys the concrete upper
rectangle logarithmic slope bound. -/
theorem intervalDomainM_rectangle_clampedUpper_logSlope
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ : 0 ≤ p.χ₀) (huStar : 0 < uStar)
    (heq : p.a - p.b * uStar ^ p.α = 0)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (q : intervalRectangleEnvelopeChoice)
    (hq : intervalDomain_equilibriumChoiceValue uStar u t q =
      intervalDomain_clampedUpper uStar u t) :
    intervalDomain_equilibriumChoiceSlope u t q /
        intervalDomain_equilibriumChoiceValue uStar u t q ≤
      intervalDomainM_rectangleUpperLogSlopeBound p uStar u t := by
  let U := intervalDomain_clampedUpper uStar u t
  let L := intervalDomain_clampedLower uStar u t
  have hLpos : 0 < L := intervalDomainM_clampedLower_pos huStar hsol ht
  have hUpos : 0 < U := huStar.trans_le
    (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
      uStar u t).2
  have hLU : L ≤ U :=
    (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
      uStar u t).1.trans
      (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
        uStar u t).2
  have hpow : L ^ p.γ ≤ U ^ p.γ :=
    Real.rpow_le_rpow hLpos.le hLU p.hγ.le
  have hD : 0 ≤ p.ν * (U ^ p.γ - L ^ p.γ) :=
    mul_nonneg p.hν.le (sub_nonneg.mpr hpow)
  have hUmp : 0 ≤ U ^ (p.m - 1) := (Real.rpow_pos_of_pos hUpos _).le
  have hUpow : U * U ^ (p.m - 1) = U ^ p.m := by
    have hh := Real.rpow_add hUpos 1 (p.m - 1)
    rw [Real.rpow_one] at hh
    rw [← hh]; congr 1; ring
  rcases q with z | x
  · have hUeq : uStar = U := by simpa [U] using hq
    simp only [intervalDomain_equilibriumChoiceSlope,
      intervalDomain_equilibriumChoiceValue, zero_div]
    rw [intervalDomainM_rectangleUpperLogSlopeBound]
    change 0 ≤ p.a - p.b * U ^ p.α +
      p.χ₀ * U ^ (p.m - 1) * (p.ν * (U ^ p.γ - L ^ p.γ) +
        p.β * (unitIntervalResolverGradientOscillationConstant p *
          (p.ν * (U ^ p.γ - L ^ p.γ))) ^ 2)
    have hreactU : p.a - p.b * U ^ p.α = 0 := by
      rw [← hUeq]
      exact heq
    rw [hreactU]
    have hchem : 0 ≤ p.ν * (U ^ p.γ - L ^ p.γ) +
        p.β * (unitIntervalResolverGradientOscillationConstant p *
          (p.ν * (U ^ p.γ - L ^ p.γ))) ^ 2 :=
      add_nonneg hD (mul_nonneg p.hβ (sq_nonneg _))
    have := mul_nonneg (mul_nonneg hχ hUmp) hchem
    linarith
  · have hxU : u t x = U := by simpa [U] using hq
    have hmax : ∀ y, u t y ≤ u t x := by
      intro y
      have hy := (intervalDomainM_equilibriumChoiceValue_mem_clamped
        (uStar := uStar) hsol ht (Sum.inr y)).2
      simpa [U, hxU] using hy
    have hlo : ∀ y ∈ Icc (0 : ℝ) 1,
        L ≤ intervalDomainLift (u t) y := by
      intro y hy
      let yp : intervalDomainPoint := ⟨y, hy⟩
      have hb := (intervalDomainM_equilibriumChoiceValue_mem_clamped
        (uStar := uStar) hsol ht (Sum.inr yp)).1
      simpa [L, yp, intervalDomainLift, hy] using hb
    have hslope := intervalDomainM_rectangle_max_slope_of_argmax
      hχ hsol ht hLpos.le hmax hlo
    have hxLift : intervalDomainLift (u t) x.1 = U := by
      simpa [intervalDomainLift, hxU]
    rw [hxLift] at hslope
    have hslope' : deriv (fun s => u s x) t ≤
        U * (p.a - p.b * U ^ p.α +
          p.χ₀ * U ^ (p.m - 1) * (p.ν * (U ^ p.γ - L ^ p.γ) +
            p.β * (unitIntervalResolverGradientOscillationConstant p *
              (p.ν * (U ^ p.γ - L ^ p.γ))) ^ 2)) := by
      have h : intervalDomainM.timeDeriv u t x ≤ _ := hslope
      refine h.trans_eq ?_
      rw [← hUpow]; ring
    simp only [intervalDomain_equilibriumChoiceSlope,
      intervalDomain_equilibriumChoiceValue]
    rw [hxU]
    rw [intervalDomainM_rectangleUpperLogSlopeBound]
    change deriv (fun s => u s x) t / U ≤
      p.a - p.b * U ^ p.α +
        p.χ₀ * U ^ (p.m - 1) * (p.ν * (U ^ p.γ - L ^ p.γ) +
          p.β * (unitIntervalResolverGradientOscillationConstant p *
            (p.ν * (U ^ p.γ - L ^ p.γ))) ^ 2)
    rw [div_le_iff₀ hUpos]
    simpa [mul_comm] using hslope'

/-- A lower choice realizing the clamped minimum obeys the concrete lower
rectangle logarithmic slope bound. -/
theorem intervalDomainM_rectangle_clampedLower_logSlope
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ : 0 ≤ p.χ₀) (huStar : 0 < uStar)
    (heq : p.a - p.b * uStar ^ p.α = 0)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (q : intervalRectangleEnvelopeChoice)
    (hq : intervalDomain_equilibriumChoiceValue uStar u t q =
      intervalDomain_clampedLower uStar u t) :
    intervalDomainM_rectangleLowerLogSlopeBound p uStar u t ≤
      intervalDomain_equilibriumChoiceSlope u t q /
        intervalDomain_equilibriumChoiceValue uStar u t q := by
  let U := intervalDomain_clampedUpper uStar u t
  let L := intervalDomain_clampedLower uStar u t
  have hLpos : 0 < L := intervalDomainM_clampedLower_pos huStar hsol ht
  have hUpos : 0 < U := huStar.trans_le
    (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
      uStar u t).2
  have hLU : L ≤ U :=
    (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
      uStar u t).1.trans
      (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
        uStar u t).2
  have hpow : L ^ p.γ ≤ U ^ p.γ :=
    Real.rpow_le_rpow hLpos.le hLU p.hγ.le
  have hD : 0 ≤ p.ν * (U ^ p.γ - L ^ p.γ) :=
    mul_nonneg p.hν.le (sub_nonneg.mpr hpow)
  have hLmp : 0 ≤ L ^ (p.m - 1) := (Real.rpow_pos_of_pos hLpos _).le
  have hLpow : L * L ^ (p.m - 1) = L ^ p.m := by
    have hh := Real.rpow_add hLpos 1 (p.m - 1)
    rw [Real.rpow_one] at hh
    rw [← hh]; congr 1; ring
  rcases q with z | x
  · have hLeq : uStar = L := by simpa [L] using hq
    simp only [intervalDomain_equilibriumChoiceSlope,
      intervalDomain_equilibriumChoiceValue, zero_div]
    rw [intervalDomainM_rectangleLowerLogSlopeBound]
    change (-p.χ₀) * L ^ (p.m - 1) * p.ν * (U ^ p.γ - L ^ p.γ) +
      p.a - p.b * L ^ p.α ≤ 0
    have hreactL : p.a - p.b * L ^ p.α = 0 := by
      rw [← hLeq]
      exact heq
    have hneg : (-p.χ₀) * L ^ (p.m - 1) *
        (p.ν * (U ^ p.γ - L ^ p.γ)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hχ) hLmp) hD
    nlinarith [hreactL, hneg]
  · have hxL : u t x = L := by simpa [L] using hq
    have hmin : ∀ y, u t x ≤ u t y := by
      intro y
      have hy := (intervalDomainM_equilibriumChoiceValue_mem_clamped
        (uStar := uStar) hsol ht (Sum.inr y)).1
      simpa [L, hxL] using hy
    have hhi : ∀ y ∈ Icc (0 : ℝ) 1,
        intervalDomainLift (u t) y ≤ U := by
      intro y hy
      let yp : intervalDomainPoint := ⟨y, hy⟩
      have hb := (intervalDomainM_equilibriumChoiceValue_mem_clamped
        (uStar := uStar) hsol ht (Sum.inr yp)).2
      simpa [U, yp, intervalDomainLift, hy] using hb
    have hslope := intervalDomainM_rectangle_min_slope_of_argmin
      hχ hsol ht hmin hhi
    have hxLift : intervalDomainLift (u t) x.1 = L := by
      simpa [intervalDomainLift, hxL]
    rw [hxLift] at hslope
    have hslope' :
        L * ((-p.χ₀) * L ^ (p.m - 1) * p.ν * (U ^ p.γ - L ^ p.γ) +
          p.a - p.b * L ^ p.α) ≤ deriv (fun s => u s x) t := by
      have h : _ ≤ intervalDomainM.timeDeriv u t x := hslope
      refine h.trans_eq' ?_
      rw [← hLpow]; ring
    simp only [intervalDomain_equilibriumChoiceSlope,
      intervalDomain_equilibriumChoiceValue]
    rw [hxL]
    rw [intervalDomainM_rectangleLowerLogSlopeBound]
    change (-p.χ₀) * L ^ (p.m - 1) * p.ν * (U ^ p.γ - L ^ p.γ) +
        p.a - p.b * L ^ p.α ≤ deriv (fun s => u s x) t / L
    rw [le_div_iff₀ hLpos]
    simpa [mul_comm] using hslope'

/-- A clamped upper maximizer obeys the weighted logarithmic rectangle
field whenever both signal sensitivity weights are uniformly bounded by
`q` on the slice. -/
theorem intervalDomainM_rectangle_clampedUpper_logSlope_with_weight
    {p : CM2Params} {T t q uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hq : 0 ≤ q)
    (hweight : ∀ y ∈ Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (v t) y) ^ (-p.β) ≤ q)
    (hweightOne : ∀ y ∈ Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (v t) y) ^ (-p.β - 1) ≤ q)
    (hχ : 0 ≤ p.χ₀) (huStar : 0 < uStar)
    (heq : p.a - p.b * uStar ^ p.α = 0)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (choice : intervalRectangleEnvelopeChoice)
    (hchoice : intervalDomain_equilibriumChoiceValue uStar u t choice =
      intervalDomain_clampedUpper uStar u t) :
    intervalDomain_equilibriumChoiceSlope u t choice /
        intervalDomain_equilibriumChoiceValue uStar u t choice ≤
      intervalDomainM_rectangleUpperLogSlopeBound_with_weight
        p q uStar u t := by
  let U := intervalDomain_clampedUpper uStar u t
  let L := intervalDomain_clampedLower uStar u t
  have hLpos : 0 < L := intervalDomainM_clampedLower_pos huStar hsol ht
  have hUpos : 0 < U := huStar.trans_le
    (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
      uStar u t).2
  have hLU : L ≤ U :=
    (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
      uStar u t).1.trans
      (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
        uStar u t).2
  have hpow : L ^ p.γ ≤ U ^ p.γ :=
    Real.rpow_le_rpow hLpos.le hLU p.hγ.le
  have hD : 0 ≤ p.ν * (U ^ p.γ - L ^ p.γ) :=
    mul_nonneg p.hν.le (sub_nonneg.mpr hpow)
  have hUmp : 0 ≤ U ^ (p.m - 1) := (Real.rpow_pos_of_pos hUpos _).le
  have hUpow : U * U ^ (p.m - 1) = U ^ p.m := by
    have hh := Real.rpow_add hUpos 1 (p.m - 1)
    rw [Real.rpow_one] at hh
    rw [← hh]; congr 1; ring
  rcases choice with z | x
  · have hUeq : uStar = U := by simpa [U] using hchoice
    simp only [intervalDomain_equilibriumChoiceSlope,
      intervalDomain_equilibriumChoiceValue, zero_div]
    rw [intervalDomainM_rectangleUpperLogSlopeBound_with_weight]
    change 0 ≤ p.a - p.b * U ^ p.α +
      p.χ₀ * q * U ^ (p.m - 1) * (p.ν * (U ^ p.γ - L ^ p.γ) +
        p.β * (unitIntervalResolverGradientOscillationConstant p *
          (p.ν * (U ^ p.γ - L ^ p.γ))) ^ 2)
    have hreactU : p.a - p.b * U ^ p.α = 0 := by
      rw [← hUeq]
      exact heq
    rw [hreactU]
    have hchem : 0 ≤ p.ν * (U ^ p.γ - L ^ p.γ) +
        p.β * (unitIntervalResolverGradientOscillationConstant p *
          (p.ν * (U ^ p.γ - L ^ p.γ))) ^ 2 :=
      add_nonneg hD (mul_nonneg p.hβ (sq_nonneg _))
    have := mul_nonneg (mul_nonneg (mul_nonneg hχ hq) hUmp) hchem
    linarith
  · have hxU : u t x = U := by simpa [U] using hchoice
    have hmax : ∀ y, u t y ≤ u t x := by
      intro y
      have hy := (intervalDomainM_equilibriumChoiceValue_mem_clamped
        (uStar := uStar) hsol ht (Sum.inr y)).2
      simpa [U, hxU] using hy
    have hlo : ∀ y ∈ Icc (0 : ℝ) 1,
        L ≤ intervalDomainLift (u t) y := by
      intro y hy
      let yp : intervalDomainPoint := ⟨y, hy⟩
      have hb := (intervalDomainM_equilibriumChoiceValue_mem_clamped
        (uStar := uStar) hsol ht (Sum.inr yp)).1
      simpa [L, yp, intervalDomainLift, hy] using hb
    have hslope := intervalDomainM_rectangle_max_slope_of_argmax_with_weight
      q hq hweight hweightOne hχ hsol ht hLpos.le hmax hlo
    have hxLift : intervalDomainLift (u t) x.1 = U := by
      simpa [intervalDomainLift, hxU]
    rw [hxLift] at hslope
    have hslope' : deriv (fun s => u s x) t ≤
        U * (p.a - p.b * U ^ p.α +
          p.χ₀ * q * U ^ (p.m - 1) * (p.ν * (U ^ p.γ - L ^ p.γ) +
            p.β * (unitIntervalResolverGradientOscillationConstant p *
              (p.ν * (U ^ p.γ - L ^ p.γ))) ^ 2)) := by
      have h : intervalDomainM.timeDeriv u t x ≤ _ := hslope
      refine h.trans_eq ?_
      rw [← hUpow]; ring
    simp only [intervalDomain_equilibriumChoiceSlope,
      intervalDomain_equilibriumChoiceValue]
    rw [hxU]
    rw [intervalDomainM_rectangleUpperLogSlopeBound_with_weight]
    change deriv (fun s => u s x) t / U ≤
      p.a - p.b * U ^ p.α +
        p.χ₀ * q * U ^ (p.m - 1) * (p.ν * (U ^ p.γ - L ^ p.γ) +
          p.β * (unitIntervalResolverGradientOscillationConstant p *
            (p.ν * (U ^ p.γ - L ^ p.γ))) ^ 2)
    rw [div_le_iff₀ hUpos]
    simpa [mul_comm] using hslope'

/-- A clamped lower minimizer obeys the weighted logarithmic rectangle
field under the same sensitivity-weight bound. -/
theorem intervalDomainM_rectangle_clampedLower_logSlope_with_weight
    {p : CM2Params} {T t q uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hq : 0 ≤ q)
    (hweight : ∀ y ∈ Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (v t) y) ^ (-p.β) ≤ q)
    (hχ : 0 ≤ p.χ₀) (huStar : 0 < uStar)
    (heq : p.a - p.b * uStar ^ p.α = 0)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (choice : intervalRectangleEnvelopeChoice)
    (hchoice : intervalDomain_equilibriumChoiceValue uStar u t choice =
      intervalDomain_clampedLower uStar u t) :
    intervalDomainM_rectangleLowerLogSlopeBound_with_weight p q uStar u t ≤
      intervalDomain_equilibriumChoiceSlope u t choice /
        intervalDomain_equilibriumChoiceValue uStar u t choice := by
  let U := intervalDomain_clampedUpper uStar u t
  let L := intervalDomain_clampedLower uStar u t
  have hLpos : 0 < L := intervalDomainM_clampedLower_pos huStar hsol ht
  have hUpos : 0 < U := huStar.trans_le
    (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
      uStar u t).2
  have hLU : L ≤ U :=
    (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
      uStar u t).1.trans
      (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
        uStar u t).2
  have hpow : L ^ p.γ ≤ U ^ p.γ :=
    Real.rpow_le_rpow hLpos.le hLU p.hγ.le
  have hD : 0 ≤ p.ν * (U ^ p.γ - L ^ p.γ) :=
    mul_nonneg p.hν.le (sub_nonneg.mpr hpow)
  have hLmp : 0 ≤ L ^ (p.m - 1) := (Real.rpow_pos_of_pos hLpos _).le
  have hLpow : L * L ^ (p.m - 1) = L ^ p.m := by
    have hh := Real.rpow_add hLpos 1 (p.m - 1)
    rw [Real.rpow_one] at hh
    rw [← hh]; congr 1; ring
  rcases choice with z | x
  · have hLeq : uStar = L := by simpa [L] using hchoice
    simp only [intervalDomain_equilibriumChoiceSlope,
      intervalDomain_equilibriumChoiceValue, zero_div]
    rw [intervalDomainM_rectangleLowerLogSlopeBound_with_weight]
    change (-p.χ₀ * q) * L ^ (p.m - 1) * p.ν * (U ^ p.γ - L ^ p.γ) +
      p.a - p.b * L ^ p.α ≤ 0
    have hreactL : p.a - p.b * L ^ p.α = 0 := by
      rw [← hLeq]
      exact heq
    have hneg : (-p.χ₀ * q) * L ^ (p.m - 1) *
        (p.ν * (U ^ p.γ - L ^ p.γ)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hχ) hq) hLmp) hD
    nlinarith [hreactL, hneg]
  · have hxL : u t x = L := by simpa [L] using hchoice
    have hmin : ∀ y, u t x ≤ u t y := by
      intro y
      have hy := (intervalDomainM_equilibriumChoiceValue_mem_clamped
        (uStar := uStar) hsol ht (Sum.inr y)).1
      simpa [L, hxL] using hy
    have hhi : ∀ y ∈ Icc (0 : ℝ) 1,
        intervalDomainLift (u t) y ≤ U := by
      intro y hy
      let yp : intervalDomainPoint := ⟨y, hy⟩
      have hb := (intervalDomainM_equilibriumChoiceValue_mem_clamped
        (uStar := uStar) hsol ht (Sum.inr yp)).2
      simpa [U, yp, intervalDomainLift, hy] using hb
    have hslope := intervalDomainM_rectangle_min_slope_of_argmin_with_weight
      q hq hweight hχ hsol ht hmin hhi
    have hxLift : intervalDomainLift (u t) x.1 = L := by
      simpa [intervalDomainLift, hxL]
    rw [hxLift] at hslope
    have hslope' :
        L * ((-p.χ₀ * q) * L ^ (p.m - 1) * p.ν * (U ^ p.γ - L ^ p.γ) +
          p.a - p.b * L ^ p.α) ≤ deriv (fun s => u s x) t := by
      have h : _ ≤ intervalDomainM.timeDeriv u t x := hslope
      refine h.trans_eq' ?_
      rw [← hLpow]; ring
    simp only [intervalDomain_equilibriumChoiceSlope,
      intervalDomain_equilibriumChoiceValue]
    rw [hxL]
    rw [intervalDomainM_rectangleLowerLogSlopeBound_with_weight]
    change (-p.χ₀ * q) * L ^ (p.m - 1) * p.ν * (U ^ p.γ - L ^ p.γ) +
        p.a - p.b * L ^ p.α ≤ deriv (fun s => u s x) t / L
    rw [le_div_iff₀ hLpos]
    simpa [mul_comm] using hslope'

/-- Expanded physical form of the combined general-`m` log-gap vector field. -/
theorem intervalDomainM_rectangleLogGapSlopeBound_eq
    (p : CM2Params) (uStar : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) :
    intervalDomainM_rectangleLogGapSlopeBound p uStar u t =
      let U := intervalDomain_clampedUpper uStar u t
      let L := intervalDomain_clampedLower uStar u t
      p.χ₀ * p.ν * (U ^ p.γ - L ^ p.γ) *
          (U ^ (p.m - 1) + L ^ (p.m - 1)) +
        p.χ₀ * p.β * U ^ (p.m - 1) *
          (unitIntervalResolverGradientOscillationConstant p *
            (p.ν * (U ^ p.γ - L ^ p.γ))) ^ 2 -
        p.b * (U ^ p.α - L ^ p.α) := by
  unfold intervalDomainM_rectangleLogGapSlopeBound
    intervalDomainM_rectangleUpperLogSlopeBound
    intervalDomainM_rectangleLowerLogSlopeBound
  ring

/-- Expanded physical form of the weighted general-`m` log-gap vector field. -/
theorem intervalDomainM_rectangleLogGapSlopeBound_with_weight_eq
    (p : CM2Params) (q uStar : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) :
    intervalDomainM_rectangleLogGapSlopeBound_with_weight p q uStar u t =
      let U := intervalDomain_clampedUpper uStar u t
      let L := intervalDomain_clampedLower uStar u t
      p.χ₀ * q * p.ν * (U ^ p.γ - L ^ p.γ) *
          (U ^ (p.m - 1) + L ^ (p.m - 1)) +
        p.χ₀ * q * p.β * U ^ (p.m - 1) *
          (unitIntervalResolverGradientOscillationConstant p *
            (p.ν * (U ^ p.γ - L ^ p.γ))) ^ 2 -
        p.b * (U ^ p.α - L ^ p.α) := by
  unfold intervalDomainM_rectangleLogGapSlopeBound_with_weight
    intervalDomainM_rectangleUpperLogSlopeBound_with_weight
    intervalDomainM_rectangleLowerLogSlopeBound_with_weight
  ring

/-- Joint continuity of one equilibrium/spatial choice on a closed
positive-time slab. -/
theorem intervalDomainM_equilibriumChoiceValue_jointContinuousOn
    {p : CM2Params} {T a b uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hab : Icc a b ⊆ Ioo (0 : ℝ) T) :
    ContinuousOn
      (Function.uncurry (intervalDomain_equilibriumChoiceValue uStar u))
      (Icc a b ×ˢ (Set.univ : Set intervalRectangleEnvelopeChoice)) := by
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
  rw [continuousOn_iff_continuous_restrict]
  have hmap : Continuous
      (fun z : ↑(Icc a b ×ˢ
          (Set.univ : Set intervalRectangleEnvelopeChoice)) =>
        ((⟨z.1.1, z.2.1⟩ : Time), z.1.2)) := by
    fun_prop
  simpa [Function.uncurry, value] using hvalue.comp hmap

/-- Joint continuity of the compact-choice logarithmic spread on a closed
positive-time slab. -/
theorem intervalDomainM_rectangleLogGapChoice_jointContinuousOn
    {p : CM2Params} {T a b uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huStar : 0 < uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hab : Icc a b ⊆ Ioo (0 : ℝ) T) :
    ContinuousOn
      (Function.uncurry (intervalDomain_rectangleLogGapChoice uStar u))
      (Icc a b ×ˢ (Set.univ : Set intervalRectangleGapChoice)) := by
  let S : Set (ℝ × intervalRectangleGapChoice) :=
    Icc a b ×ˢ (Set.univ : Set intervalRectangleGapChoice)
  have hv := intervalDomainM_equilibriumChoiceValue_jointContinuousOn
    (uStar := uStar) hsol hab
  have hmapTop : ContinuousOn
      (fun z : ℝ × intervalRectangleGapChoice => (z.1, z.2.1)) S :=
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn
  have hmapBot : ContinuousOn
      (fun z : ℝ × intervalRectangleGapChoice => (z.1, z.2.2)) S :=
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd)).continuousOn
  have htop : ContinuousOn
      (fun z : ℝ × intervalRectangleGapChoice =>
        intervalDomain_equilibriumChoiceValue uStar u z.1 z.2.1) S := by
    apply hv.comp hmapTop
    intro z hz
    change z.1 ∈ Icc a b ∧ z.2 ∈ Set.univ at hz
    exact ⟨hz.1, Set.mem_univ _⟩
  have hbot : ContinuousOn
      (fun z : ℝ × intervalRectangleGapChoice =>
        intervalDomain_equilibriumChoiceValue uStar u z.1 z.2.2) S := by
    apply hv.comp hmapBot
    intro z hz
    change z.1 ∈ Icc a b ∧ z.2 ∈ Set.univ at hz
    exact ⟨hz.1, Set.mem_univ _⟩
  have htopLog := htop.log (fun z hz => ne_of_gt
    (intervalDomainM_equilibriumChoiceValue_pos huStar hsol
      (hab hz.1) z.2.1))
  have hbotLog := hbot.log (fun z hz => ne_of_gt
    (intervalDomainM_equilibriumChoiceValue_pos huStar hsol
      (hab hz.1) z.2.2))
  simpa [S, Function.uncurry, intervalDomain_rectangleLogGapChoice] using
    htopLog.sub hbotLog

/-- Continuity of the clamped logarithmic gap on every closed positive-time
window. -/
theorem intervalDomainM_rectangleLogGap_continuousOn
    {p : CM2Params} {T a b uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huStar : 0 < uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hab : Icc a b ⊆ Ioo (0 : ℝ) T) :
    ContinuousOn (intervalDomain_rectangleLogGap uStar u) (Icc a b) := by
  obtain ⟨_, _, _, _, _, _, hjoint⟩ := hsol.regularity
  have hFab : ContinuousOn
      (Function.uncurry (fun t y => intervalDomainLift (u t) y))
      (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    hjoint.1.mono (Set.prod_mono hab (le_refl _))
  have hmax : ContinuousOn
      (fun t => sSup (intervalDomainLift (u t) '' Icc (0 : ℝ) 1))
      (Icc a b) := sliceMax_continuousOn hFab
  have hmin : ContinuousOn
      (fun t => sInf (intervalDomainLift (u t) '' Icc (0 : ℝ) 1))
      (Icc a b) := sliceMin_continuousOn hFab
  have hupper : ContinuousOn (intervalDomain_clampedUpper uStar u)
      (Icc a b) := by
    intro t ht
    simpa [intervalDomain_clampedUpper] using
      (continuousWithinAt_const.max (hmax t ht))
  have hlower : ContinuousOn (intervalDomain_clampedLower uStar u)
      (Icc a b) := by
    intro t ht
    simpa [intervalDomain_clampedLower] using
      (continuousWithinAt_const.min (hmin t ht))
  have hupperLog := hupper.log (fun t ht => ne_of_gt
    (huStar.trans_le
      (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
        uStar u t).2))
  have hlowerLog := hlower.log (fun t ht => ne_of_gt
    (intervalDomainM_clampedLower_pos huStar hsol (hab ht)))
  simpa [intervalDomain_rectangleLogGap] using hupperLog.sub hlowerLog

/-- Exact derivative of one equilibrium/spatial envelope choice. -/
theorem intervalDomainM_equilibriumChoiceValue_hasDerivAt
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    ∀ q : intervalRectangleEnvelopeChoice,
      HasDerivAt
        (fun s => intervalDomain_equilibriumChoiceValue uStar u s q)
        (intervalDomain_equilibriumChoiceSlope u t q) t := by
  obtain ⟨_, htime, _, _, _, _, _⟩ := hsol.regularity
  rintro (z | x)
  · simpa [intervalDomain_equilibriumChoiceValue,
      intervalDomain_equilibriumChoiceSlope] using
      (hasDerivAt_const (x := t) (c := uStar))
  · simpa [intervalDomain_equilibriumChoiceValue,
      intervalDomain_equilibriumChoiceSlope] using
      ((htime x t ht).1.1.hasDerivAt)

/-- Exact derivative of the logarithmic choice spread. -/
theorem intervalDomainM_rectangleLogGapChoice_hasDerivAt
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huStar : 0 < uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (q : intervalRectangleGapChoice) :
    HasDerivAt
      (fun s => intervalDomain_rectangleLogGapChoice uStar u s q)
      (intervalDomain_rectangleLogGapChoiceSlope uStar u t q) t := by
  have htop := intervalDomainM_equilibriumChoiceValue_hasDerivAt
    (uStar := uStar) hsol ht q.1
  have hbot := intervalDomainM_equilibriumChoiceValue_hasDerivAt
    (uStar := uStar) hsol ht q.2
  have htop0 := ne_of_gt
    (intervalDomainM_equilibriumChoiceValue_pos huStar hsol ht q.1)
  have hbot0 := ne_of_gt
    (intervalDomainM_equilibriumChoiceValue_pos huStar hsol ht q.2)
  simpa [intervalDomain_rectangleLogGapChoice,
    intervalDomain_rectangleLogGapChoiceSlope] using
    (htop.log htop0).sub (hbot.log hbot0)

/-- The `deriv` selected by Lean is the explicit logarithmic choice slope. -/
theorem intervalDomainM_rectangleLogGapChoice_deriv_eq
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huStar : 0 < uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (q : intervalRectangleGapChoice) :
    deriv (fun s => intervalDomain_rectangleLogGapChoice uStar u s q) t =
      intervalDomain_rectangleLogGapChoiceSlope uStar u t q :=
  (intervalDomainM_rectangleLogGapChoice_hasDerivAt
    huStar hsol ht q).deriv

/-- Every exact compact-choice maximizer obeys the combined concrete
logarithmic-gap slope bound. -/
theorem intervalDomainM_rectangleLogGapChoice_argmax_slope
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ : 0 ≤ p.χ₀) (huStar : 0 < uStar)
    (heq : p.a - p.b * uStar ^ p.α = 0)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (q : intervalRectangleGapChoice)
    (harg : intervalDomain_rectangleLogGapChoice uStar u t q =
      sSup (intervalDomain_rectangleLogGapChoice uStar u t ''
        (Set.univ : Set intervalRectangleGapChoice))) :
    deriv (fun s => intervalDomain_rectangleLogGapChoice uStar u s q) t ≤
      intervalDomainM_rectangleLogGapSlopeBound p uStar u t := by
  have hvals := intervalDomainM_rectangleLogGapChoice_argmax_values
    huStar hsol ht q harg
  have htop := intervalDomainM_rectangle_clampedUpper_logSlope
    hχ huStar heq hsol ht q.1 hvals.1
  have hbot := intervalDomainM_rectangle_clampedLower_logSlope
    hχ huStar heq hsol ht q.2 hvals.2
  rw [intervalDomainM_rectangleLogGapChoice_deriv_eq huStar hsol ht q]
  unfold intervalDomain_rectangleLogGapChoiceSlope
    intervalDomainM_rectangleLogGapSlopeBound
  linarith

/-- Every exact compact-choice maximizer obeys the weighted combined
logarithmic-gap slope bound. -/
theorem intervalDomainM_rectangleLogGapChoice_argmax_slope_with_weight
    {p : CM2Params} {T t q uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hq : 0 ≤ q)
    (hweight : ∀ y ∈ Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (v t) y) ^ (-p.β) ≤ q)
    (hweightOne : ∀ y ∈ Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (v t) y) ^ (-p.β - 1) ≤ q)
    (hχ : 0 ≤ p.χ₀) (huStar : 0 < uStar)
    (heq : p.a - p.b * uStar ^ p.α = 0)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (choice : intervalRectangleGapChoice)
    (harg : intervalDomain_rectangleLogGapChoice uStar u t choice =
      sSup (intervalDomain_rectangleLogGapChoice uStar u t ''
        (Set.univ : Set intervalRectangleGapChoice))) :
    deriv (fun s => intervalDomain_rectangleLogGapChoice
        uStar u s choice) t ≤
      intervalDomainM_rectangleLogGapSlopeBound_with_weight
        p q uStar u t := by
  have hvals := intervalDomainM_rectangleLogGapChoice_argmax_values
    huStar hsol ht choice harg
  have htop := intervalDomainM_rectangle_clampedUpper_logSlope_with_weight
    hq hweight hweightOne hχ huStar heq hsol ht choice.1 hvals.1
  have hbot := intervalDomainM_rectangle_clampedLower_logSlope_with_weight
    hq hweight hχ huStar heq hsol ht choice.2 hvals.2
  rw [intervalDomainM_rectangleLogGapChoice_deriv_eq
    huStar hsol ht choice]
  unfold intervalDomain_rectangleLogGapChoiceSlope
    intervalDomainM_rectangleLogGapSlopeBound_with_weight
  linarith

/-- Joint continuity of the exact envelope-choice slope on a closed
positive-time slab. -/
theorem intervalDomainM_equilibriumChoiceSlope_jointContinuousOn
    {p : CM2Params} {T a b : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hab : Icc a b ⊆ Ioo (0 : ℝ) T) :
    ContinuousOn
      (Function.uncurry (intervalDomain_equilibriumChoiceSlope u))
      (Icc a b ×ˢ (Set.univ : Set intervalRectangleEnvelopeChoice)) := by
  let Time := {t : ℝ // t ∈ Icc a b}
  obtain ⟨_, _, _, _, _, hderivJoint, _⟩ := hsol.regularity
  have hUt : Continuous (fun z : Time × intervalDomainPoint =>
      deriv (fun s => u s z.2) z.1.1) := by
    have hbase := continuousOn_iff_continuous_restrict.mp
      (hderivJoint.1.mono (Set.prod_mono hab (le_refl _)))
    have hmap : Continuous (fun z : Time × intervalDomainPoint =>
        (⟨(z.1.1, z.2.1), ⟨z.1.2, z.2.2⟩⟩ :
          ↑(Icc a b ×ˢ Icc (0 : ℝ) 1))) := by
      exact Continuous.subtype_mk
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)) _
    have hc := hbase.comp hmap
    change Continuous (fun z : Time × intervalDomainPoint =>
      deriv (fun s => intervalDomainLift (u s) z.2.1) z.1.1) at hc
    have heq : (fun z : Time × intervalDomainPoint =>
        deriv (fun s => intervalDomainLift (u s) z.2.1) z.1.1) =
        fun z => deriv (fun s => u s z.2) z.1.1 := by
      funext z
      congr 1
      funext s
      simp [intervalDomainLift]
    rw [heq] at hc
    exact hc
  let leftSlope : Time × Unit → ℝ := fun _ => 0
  let rightSlope : Time × intervalDomainPoint → ℝ :=
    fun z => deriv (fun s => u s z.2) z.1.1
  let slope : Time × intervalRectangleEnvelopeChoice → ℝ :=
    fun z => intervalDomain_equilibriumChoiceSlope u z.1.1 z.2
  have hslope : Continuous slope := by
    have hsum : Continuous (Sum.elim leftSlope rightSlope) :=
      Continuous.sumElim continuous_const hUt
    let e : Time × (Unit ⊕ intervalDomainPoint) ≃ₜ
        (Time × Unit) ⊕ (Time × intervalDomainPoint) :=
      Homeomorph.prodSumDistrib
    have heq : slope = (Sum.elim leftSlope rightSlope) ∘ e := by
      funext z
      rcases z with ⟨t, q⟩
      rcases q with z | x <;> rfl
    rw [heq]
    exact hsum.comp e.continuous
  rw [continuousOn_iff_continuous_restrict]
  have hmap : Continuous
      (fun z : ↑(Icc a b ×ˢ
          (Set.univ : Set intervalRectangleEnvelopeChoice)) =>
        ((⟨z.1.1, z.2.1⟩ : Time), z.1.2)) := by
    fun_prop
  simpa [Function.uncurry, slope] using hslope.comp hmap

/-- Joint continuity of the explicit logarithmic choice slope. -/
theorem intervalDomainM_rectangleLogGapChoiceSlope_jointContinuousOn
    {p : CM2Params} {T a b uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huStar : 0 < uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hab : Icc a b ⊆ Ioo (0 : ℝ) T) :
    ContinuousOn
      (Function.uncurry (intervalDomain_rectangleLogGapChoiceSlope uStar u))
      (Icc a b ×ˢ (Set.univ : Set intervalRectangleGapChoice)) := by
  let S : Set (ℝ × intervalRectangleGapChoice) :=
    Icc a b ×ˢ (Set.univ : Set intervalRectangleGapChoice)
  have hv := intervalDomainM_equilibriumChoiceValue_jointContinuousOn
    (uStar := uStar) hsol hab
  have hs := intervalDomainM_equilibriumChoiceSlope_jointContinuousOn hsol hab
  have hmapTop : ContinuousOn
      (fun z : ℝ × intervalRectangleGapChoice => (z.1, z.2.1)) S :=
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn
  have hmapBot : ContinuousOn
      (fun z : ℝ × intervalRectangleGapChoice => (z.1, z.2.2)) S :=
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd)).continuousOn
  have hmapsTop : MapsTo
      (fun z : ℝ × intervalRectangleGapChoice => (z.1, z.2.1)) S
      (Icc a b ×ˢ (Set.univ : Set intervalRectangleEnvelopeChoice)) := by
    intro z hz
    change z.1 ∈ Icc a b ∧ z.2 ∈ Set.univ at hz
    exact ⟨hz.1, Set.mem_univ _⟩
  have hmapsBot : MapsTo
      (fun z : ℝ × intervalRectangleGapChoice => (z.1, z.2.2)) S
      (Icc a b ×ˢ (Set.univ : Set intervalRectangleEnvelopeChoice)) := by
    intro z hz
    change z.1 ∈ Icc a b ∧ z.2 ∈ Set.univ at hz
    exact ⟨hz.1, Set.mem_univ _⟩
  have hvTop := hv.comp hmapTop hmapsTop
  have hvBot := hv.comp hmapBot hmapsBot
  have hsTop := hs.comp hmapTop hmapsTop
  have hsBot := hs.comp hmapBot hmapsBot
  have htop := hsTop.div hvTop (fun z hz => ne_of_gt
    (intervalDomainM_equilibriumChoiceValue_pos huStar hsol
      (hab hz.1) z.2.1))
  have hbot := hsBot.div hvBot (fun z hz => ne_of_gt
    (intervalDomainM_equilibriumChoiceValue_pos huStar hsol
      (hab hz.1) z.2.2))
  simpa [S, Function.uncurry,
    intervalDomain_rectangleLogGapChoiceSlope] using htop.sub hbot

/-- The actual `deriv` field required by compact Danskin is jointly continuous. -/
theorem intervalDomainM_rectangleLogGapChoice_deriv_jointContinuousOn
    {p : CM2Params} {T a b uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huStar : 0 < uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hab : Icc a b ⊆ Ioo (0 : ℝ) T) :
    ContinuousOn
      (Function.uncurry (fun s q =>
        deriv (fun r => intervalDomain_rectangleLogGapChoice uStar u r q) s))
      (Icc a b ×ˢ (Set.univ : Set intervalRectangleGapChoice)) := by
  have hs := intervalDomainM_rectangleLogGapChoiceSlope_jointContinuousOn
    huStar hsol hab
  apply hs.congr
  intro z hz
  exact (intervalDomainM_rectangleLogGapChoice_deriv_eq
    huStar hsol (hab hz.1) z.2)

set_option maxHeartbeats 4000000 in
/-- Generic right-upper Dini inequality for the clamped logarithmic gap,
given a bound for every exact compact-choice maximizer. -/
theorem intervalDomainM_rectangleLogGap_dini_of_argmax_slope_bound
    {p : CM2Params} {T a b uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (g : ℝ → ℝ) (huStar : 0 < uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hab : Icc a b ⊆ Ioo (0 : ℝ) T)
    (hargmax : ∀ s ∈ Icc a b, ∀ choice : intervalRectangleGapChoice,
      intervalDomain_rectangleLogGapChoice uStar u s choice =
          sSup (intervalDomain_rectangleLogGapChoice uStar u s ''
            (Set.univ : Set intervalRectangleGapChoice)) →
        deriv (fun r => intervalDomain_rectangleLogGapChoice
            uStar u r choice) s ≤ g s) :
    ∀ x ∈ Ico a b, ∀ r : ℝ,
      g x < r →
        ∃ᶠ z in nhdsWithin x (Ioi x),
          (z - x)⁻¹ *
            (intervalDomain_rectangleLogGap uStar u z -
              intervalDomain_rectangleLogGap uStar u x) < r := by
  let xzero : intervalDomainPoint :=
    ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩
  letI : MetricSpace intervalDomainPoint := by
    change MetricSpace (Subtype (Icc (0 : ℝ) 1))
    infer_instance
  letI : MetricSpace Bool := TopologicalSpace.metrizableSpaceMetric _
  letI : CompactSpace intervalDomainPoint :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : Nonempty intervalDomainPoint := ⟨xzero⟩
  letI hcompactEnvelope : CompactSpace intervalRectangleEnvelopeParameter :=
    inferInstance
  letI hcompactGap : CompactSpace intervalRectangleGapParameter := inferInstance
  have hdecode : Continuous intervalRectangleEnvelopeParameterChoice := by
    have hs : IsClopen
        {q : intervalRectangleEnvelopeParameter | q.1 = true} :=
      (isClopen_discrete ({true} : Set Bool)).preimage continuous_fst
    unfold intervalRectangleEnvelopeParameterChoice
    apply Continuous.if
    · intro q hq
      rw [hs.frontier_eq] at hq
      simp at hq
    · exact continuous_const
    · exact continuous_inr.comp continuous_snd
  have hdecodePair : Continuous intervalRectangleGapParameterChoice := by
    exact (hdecode.comp continuous_fst).prodMk
      (hdecode.comp continuous_snd)
  have hdecode_surjective :
      Function.Surjective intervalRectangleEnvelopeParameterChoice := by
    intro q
    rcases q with z | x
    · exact ⟨(true, xzero), by
        simp [intervalRectangleEnvelopeParameterChoice]⟩
    · exact ⟨(false, x), by
        simp [intervalRectangleEnvelopeParameterChoice]⟩
  have hdecodePair_surjective :
      Function.Surjective intervalRectangleGapParameterChoice := by
    rintro ⟨qhi, qlo⟩
    obtain ⟨phi, hphi⟩ := hdecode_surjective qhi
    obtain ⟨plo, hplo⟩ := hdecode_surjective qlo
    refine ⟨(phi, plo), ?_⟩
    simp [intervalRectangleGapParameterChoice, hphi, hplo]
  let F : ℝ → intervalRectangleGapParameter → ℝ :=
    fun s q => intervalDomain_rectangleLogGapChoice uStar u s
      (intervalRectangleGapParameterChoice q)
  have himage : ∀ s : ℝ,
      F s '' (Set.univ : Set intervalRectangleGapParameter) =
        intervalDomain_rectangleLogGapChoice uStar u s ''
          (Set.univ : Set intervalRectangleGapChoice) := by
    intro s
    apply Set.Subset.antisymm
    · rintro y ⟨q, -, rfl⟩
      exact ⟨intervalRectangleGapParameterChoice q, Set.mem_univ _, rfl⟩
    · rintro y ⟨q, -, rfl⟩
      obtain ⟨r, hr⟩ := hdecodePair_surjective q
      refine ⟨r, Set.mem_univ _, ?_⟩
      simp only [F]
      rw [hr]
  have hFbase := intervalDomainM_rectangleLogGapChoice_jointContinuousOn
    huStar hsol hab
  have hparameterMap : Continuous
      (fun z : ℝ × intervalRectangleGapParameter =>
        (z.1, intervalRectangleGapParameterChoice z.2)) :=
    continuous_fst.prodMk (hdecodePair.comp continuous_snd)
  have hparameterMapsTo : MapsTo
      (fun z : ℝ × intervalRectangleGapParameter =>
        (z.1, intervalRectangleGapParameterChoice z.2))
      (Icc a b ×ˢ (Set.univ : Set intervalRectangleGapParameter))
      (Icc a b ×ˢ (Set.univ : Set intervalRectangleGapChoice)) := by
    intro z hz
    exact ⟨hz.1, Set.mem_univ _⟩
  have hF : ContinuousOn (Function.uncurry F)
      (Icc a b ×ˢ (Set.univ : Set intervalRectangleGapParameter)) := by
    have hc := hFbase.comp hparameterMap.continuousOn hparameterMapsTo
    simpa [F, Function.uncurry] using hc
  have hsliceCont : ∀ q : intervalRectangleGapParameter,
      ContinuousOn (fun s => F s q) (Icc a b) := by
    intro q
    exact hF.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, Set.mem_univ q⟩)
  have hsliceDiff : ∀ q : intervalRectangleGapParameter, ∀ s ∈ Ioo a b,
      HasDerivAt (fun r => F r q) (deriv (fun r => F r q) s) s := by
    intro q s hs
    have hst : s ∈ Ioo (0 : ℝ) T := hab (Ioo_subset_Icc_self hs)
    have hderiv : deriv (fun r => F r q) s =
        intervalDomain_rectangleLogGapChoiceSlope uStar u s
          (intervalRectangleGapParameterChoice q) := by
      simpa [F] using intervalDomainM_rectangleLogGapChoice_deriv_eq
        huStar hsol hst (intervalRectangleGapParameterChoice q)
    rw [hderiv]
    simpa [F] using intervalDomainM_rectangleLogGapChoice_hasDerivAt
      huStar hsol hst (intervalRectangleGapParameterChoice q)
  have hM : ContinuousOn
      (fun s => sSup (F s ''
        (Set.univ : Set intervalRectangleGapParameter))) (Icc a b) := by
    have hg := intervalDomainM_rectangleLogGap_continuousOn huStar hsol hab
    apply hg.congr
    intro s hs
    change sSup (F s '' (Set.univ : Set intervalRectangleGapParameter)) = _
    rw [himage s]
    exact intervalDomainM_rectangleLogGapChoice_sSup_eq
      huStar hsol (hab hs)
  have hdFbase := intervalDomainM_rectangleLogGapChoice_deriv_jointContinuousOn
    huStar hsol hab
  have hdF : ContinuousOn
      (Function.uncurry (fun (s : ℝ) (q : intervalRectangleGapParameter) =>
        deriv (fun r => F r q) s))
      (Icc a b ×ˢ (Set.univ : Set intervalRectangleGapParameter)) := by
    have hc := hdFbase.comp hparameterMap.continuousOn hparameterMapsTo
    simpa [F, Function.uncurry] using hc
  have hbnd : ∀ s ∈ Icc a b, ∀ q : intervalRectangleGapParameter,
      F s q = sSup (F s ''
          (Set.univ : Set intervalRectangleGapParameter)) →
        deriv (fun r => F r q) s ≤ g s := by
    intro s hs q harg
    rw [himage s] at harg
    have hbase := hargmax s hs
      (intervalRectangleGapParameterChoice q) harg
    simpa [F] using hbase
  have hraw := @compactMax_dini_of_argmax_upperBound
    intervalRectangleGapParameter
    (inferInstance : PseudoMetricSpace intervalRectangleGapParameter)
    hcompactGap
    (inferInstance : Nonempty intervalRectangleGapParameter)
    F g a b
    hF hsliceCont hsliceDiff hM hdF hbnd
  intro x hx r hr
  have hfreq := hraw x hx r hr
  have hxIcc : x ∈ Icc a b := Ico_subset_Icc_self hx
  have hev : ∀ᶠ z in nhdsWithin x (Ioi x), z ∈ Icc a b := by
    have hmem : Ioo x b ∈ nhdsWithin x (Ioi x) := by
      rw [← Ioi_inter_Iio]
      exact inter_mem_nhdsWithin _ (Iio_mem_nhds hx.2)
    filter_upwards [hmem] with z hz
    exact ⟨le_trans hx.1 hz.1.le, hz.2.le⟩
  refine (hfreq.and_eventually hev).mono ?_
  rintro z ⟨hz, hzmem⟩
  rw [himage z, intervalDomainM_rectangleLogGapChoice_sSup_eq
      huStar hsol (hab hzmem),
    himage x, intervalDomainM_rectangleLogGapChoice_sSup_eq
      huStar hsol (hab hxIcc)] at hz
  exact hz

set_option maxHeartbeats 4000000 in
/-- Concrete right-upper Dini inequality for the clamped logarithmic gap. -/
theorem intervalDomainM_rectangleLogGap_dini
    {p : CM2Params} {T a b uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hχ : 0 ≤ p.χ₀) (huStar : 0 < uStar)
    (heq : p.a - p.b * uStar ^ p.α = 0)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hab : Icc a b ⊆ Ioo (0 : ℝ) T) :
    ∀ x ∈ Ico a b, ∀ r : ℝ,
      intervalDomainM_rectangleLogGapSlopeBound p uStar u x < r →
        ∃ᶠ z in nhdsWithin x (Ioi x),
          (z - x)⁻¹ *
            (intervalDomain_rectangleLogGap uStar u z -
              intervalDomain_rectangleLogGap uStar u x) < r := by
  apply intervalDomainM_rectangleLogGap_dini_of_argmax_slope_bound
    (p := p) (g := intervalDomainM_rectangleLogGapSlopeBound p uStar u)
      huStar hsol hab
  intro s hs choice harg
  exact intervalDomainM_rectangleLogGapChoice_argmax_slope
    hχ huStar heq hsol (hab hs) choice harg

set_option maxHeartbeats 4000000 in
/-- Weighted right-upper Dini inequality on a window where both sensitivity
weights admit the same uniform factor `q`. -/
theorem intervalDomainM_rectangleLogGap_dini_with_weight
    {p : CM2Params} {T a b q uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hq : 0 ≤ q)
    (hweight : ∀ s ∈ Icc a b, ∀ y ∈ Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (v s) y) ^ (-p.β) ≤ q)
    (hweightOne : ∀ s ∈ Icc a b, ∀ y ∈ Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (v s) y) ^ (-p.β - 1) ≤ q)
    (hχ : 0 ≤ p.χ₀) (huStar : 0 < uStar)
    (heq : p.a - p.b * uStar ^ p.α = 0)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hab : Icc a b ⊆ Ioo (0 : ℝ) T) :
    ∀ x ∈ Ico a b, ∀ r : ℝ,
      intervalDomainM_rectangleLogGapSlopeBound_with_weight
          p q uStar u x < r →
        ∃ᶠ z in nhdsWithin x (Ioi x),
          (z - x)⁻¹ *
            (intervalDomain_rectangleLogGap uStar u z -
              intervalDomain_rectangleLogGap uStar u x) < r := by
  apply intervalDomainM_rectangleLogGap_dini_of_argmax_slope_bound
    (p := p)
      (g := intervalDomainM_rectangleLogGapSlopeBound_with_weight
        p q uStar u) huStar hsol hab
  intro s hs choice harg
  exact intervalDomainM_rectangleLogGapChoice_argmax_slope_with_weight
    hq (hweight s hs) (hweightOne s hs) hχ huStar heq hsol
      (hab hs) choice harg


#print axioms intervalDomainM_equilibriumChoiceValue_pos
#print axioms intervalDomainM_clampedLower_pos
#print axioms intervalDomainM_rectangleLogGap_nonneg
#print axioms intervalDomainM_equilibriumChoiceValue_mem_clamped
#print axioms intervalDomainM_rectangleLogGapChoice_sSup_eq
#print axioms intervalDomainM_rectangle_clampedUpper_logSlope
#print axioms intervalDomainM_rectangle_clampedLower_logSlope
#print axioms intervalDomainM_rectangleLogGapChoice_argmax_slope
#print axioms intervalDomainM_rectangle_clampedUpper_logSlope_with_weight
#print axioms intervalDomainM_rectangle_clampedLower_logSlope_with_weight
#print axioms intervalDomainM_rectangleLogGapChoice_argmax_slope_with_weight
#print axioms intervalDomainM_rectangleLogGap_dini_of_argmax_slope_bound
#print axioms intervalDomainM_rectangleLogGap_dini
#print axioms intervalDomainM_rectangleLogGap_dini_with_weight

end

end ShenWork.Paper3
