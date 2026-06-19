import ShenWork.PaperOne.WaveResidualWired9

/-!
  Last two residual fields for the whole-line Paper 1 assembly.

  The long-time uniform tail is proved by a sequential Dini argument.  The only
  additional named data is the parameter compactness/continuity needed to make
  the finite-cover step uniform over the whole trap; the theorem does not carry
  `LongTimeMapUniformTail` itself.

  The fixed-point flat-left field is wired through the existing parabolic tail
  bridge from `WholeLineLeftTailDischarge`.
-/

open Filter Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-- Sequential compactness of the parameter-window space used by the uniform
Dini argument.  Any trapped profiles and points in a fixed compact window have a
subsequence converging locally uniformly in the profile and ordinarily in the
point variable. -/
def WaveTrapWindowSequentialCompactness (κ κt D : ℝ) : Prop :=
  ∀ R, 0 < R →
    ∀ seq : ℕ → ℝ → ℝ, (∀ n, seq n ∈ WaveTrap κ κt D) →
      ∀ xs : ℕ → ℝ, (∀ n, xs n ∈ Icc (-R) R) →
        ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
          ∃ U x,
            U ∈ WaveTrap κ κt D ∧
              x ∈ Icc (-R) R ∧
                ShenWork.Paper1.LocallyUniformConverges
                  (fun n => seq (subseq n)) U ∧
                  Tendsto (fun n => xs (subseq n)) atTop (𝓝 x)

/-- Parameter continuity of the long-time image map in the local-uniform
topology.  This is the continuity input for the Dini compactness argument and is
kept separate from the spatial continuity field `LongTimeMapImageContinuity`. -/
def LongTimeMapImageParameterContinuity (κ κt D : ℝ)
    (w : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop :=
  ShenWork.Paper1.LocalUniformContinuousOn
    (fun U : ℝ → ℝ => U ∈ WaveTrap κ κt D) (longTimeMap w)

/-- The named parameter-side data needed to make the pointwise Dini convergence
uniform over all trapped profiles. -/
structure LongTimeUniformDiniParameterData (κ κt D : ℝ)
    (w : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  trap_window_compactness : WaveTrapWindowSequentialCompactness κ κt D
  image_parameter_continuity : LongTimeMapImageParameterContinuity κ κt D w

/-- A locally-uniformly convergent sequence can be evaluated along a convergent
sequence of points, provided all points stay in the same compact window and the
limit profile is continuous. -/
theorem tendsto_eval_of_locallyUniformConverges
    {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {xs : ℕ → ℝ} {x R : ℝ}
    (hR : 0 < R)
    (hxs_window : ∀ n, xs n ∈ Icc (-R) R)
    (hconv : ShenWork.Paper1.LocallyUniformConverges fs f)
    (hf : Continuous f)
    (hxs : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun n => fs n (xs n)) atTop (𝓝 (f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hconv_ev :
      ∀ᶠ n in atTop, |fs n (xs n) - f (xs n)| < ε / 2 := by
    filter_upwards [hconv R hR (ε / 2) hε2] with n hn
    exact hn (xs n) (hxs_window n)
  have hcont_ev :
      ∀ᶠ n in atTop, |f (xs n) - f x| < ε / 2 := by
    rcases (Metric.continuousAt_iff.mp hf.continuousAt (ε / 2) hε2) with
      ⟨δ, hδ, hδprop⟩
    filter_upwards [Metric.tendsto_nhds.mp hxs δ hδ] with n hn
    simpa [Real.dist_eq] using hδprop hn
  rcases eventually_atTop.1 (hconv_ev.and hcont_ev) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hnN
  rcases hN n hnN with ⟨hn, hcontn⟩
  have htri :
      |fs n (xs n) - f x| ≤
        |fs n (xs n) - f (xs n)| + |f (xs n) - f x| := by
    calc
      |fs n (xs n) - f x|
          =
            |(fs n (xs n) - f (xs n)) + (f (xs n) - f x)| := by
              ring_nf
      _ ≤ |fs n (xs n) - f (xs n)| + |f (xs n) - f x| :=
            abs_add_le _ _
  have hlt : |fs n (xs n) - f x| < ε := by
    nlinarith [htri, hn, hcontn]
  simpa [Real.dist_eq] using hlt

/-- The long-time infimum is below every finite-time slice. -/
theorem longTimeMap_le_time
    {κ κt D : ℝ} {w : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    (hlower : ∀ U, U ∈ WaveTrap κ κt D →
      ∀ t x, lowerBarrier κ κt D x ≤ w U t x)
    {U : ℝ → ℝ} (hU : U ∈ WaveTrap κ κt D) (t x : ℝ) :
    longTimeMap w U x ≤ w U t x := by
  simpa [longTimeMap, wholeLineLongTimeLimit] using
    (ciInf_le_of_le
      (wholeLine_longTime_bddBelow
        (κ := κ) (κt := κt) (D := D) (w := w U)
        (hlower U hU) x)
      t (le_rfl : w U t x ≤ w U t x))

/-- Uniform Dini tail for the long-time map.

The proof uses time antitonicity to compare a bad late time with one fixed
finite time, compactness to pass to a limit profile/window point, and the
finite-time plus image parameter-continuity inputs to pass that comparison to
the limit. -/
theorem longTime_uniform_tail_discharge
    {κ κt D : ℝ} {w : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    (hlower : ∀ U, U ∈ WaveTrap κ κt D →
      ∀ t x, lowerBarrier κ κt D x ≤ w U t x)
    (htime : ∀ U, U ∈ WaveTrap κ κt D →
      ∀ x, Antitone fun t : ℝ => w U t x)
    (hslice : ∀ U, U ∈ WaveTrap κ κt D → ∀ t, Continuous (w U t))
    (hfinite : LongTimeMapFiniteTimeContinuity κ κt D w)
    (himage : LongTimeMapImageContinuity κ κt D w)
    (Hdini : LongTimeUniformDiniParameterData κ κt D w) :
    LongTimeMapUniformTail κ κt D w := by
  intro R hR ε hε
  by_contra hno
  have hbad :
      ∀ N : ℕ, ∃ U : ℝ → ℝ, U ∈ WaveTrap κ κt D ∧
        ∃ x : ℝ, x ∈ Icc (-R) R ∧
          ε ≤ |w U (N : ℝ) x - longTimeMap w U x| := by
    intro N
    have hN :
        ¬ ∀ U, U ∈ WaveTrap κ κt D →
          ∀ x : ℝ, x ∈ Icc (-R) R →
            |w U (N : ℝ) x - longTimeMap w U x| < ε := by
      intro hN
      exact hno ⟨(N : ℝ), hN⟩
    push Not at hN
    rcases hN with ⟨U, hU, x, hx, hbadx⟩
    exact ⟨U, hU, x, hx, hbadx⟩
  classical
  let Ubad : ℕ → ℝ → ℝ := fun N => Classical.choose (hbad N)
  have hUbad : ∀ N, Ubad N ∈ WaveTrap κ κt D := by
    intro N
    exact (Classical.choose_spec (hbad N)).1
  let xbad : ℕ → ℝ := fun N =>
    Classical.choose (Classical.choose_spec (hbad N)).2
  have hxbad : ∀ N, xbad N ∈ Icc (-R) R := by
    intro N
    exact (Classical.choose_spec (Classical.choose_spec (hbad N)).2).1
  have hbad_eval :
      ∀ N, ε ≤
        |w (Ubad N) (N : ℝ) (xbad N) -
          longTimeMap w (Ubad N) (xbad N)| := by
    intro N
    exact (Classical.choose_spec (Classical.choose_spec (hbad N)).2).2
  rcases Hdini.trap_window_compactness R hR Ubad hUbad xbad hxbad with
    ⟨subseq, hsubseq, Uinf, xinf, hUinf, hxinf, hUconv, hxconv⟩
  have hε3 : 0 < ε / 3 := by linarith
  have hlimit_tendsto :
      Tendsto (fun t : ℝ => w Uinf t xinf) atTop
        (𝓝 (longTimeMap w Uinf xinf)) := by
    simpa [longTimeMap] using
      (wholeLine_longTime_limit_tendsto
        (κ := κ) (κt := κt) (D := D) (w := w Uinf)
        (htime Uinf hUinf) (hlower Uinf hUinf) xinf)
  rcases Metric.tendsto_atTop.mp hlimit_tendsto (ε / 3) hε3 with
    ⟨T0, hT0⟩
  obtain ⟨N0, hN0_gt⟩ := exists_nat_gt T0
  have hN0_ge : T0 ≤ (N0 : ℝ) := le_of_lt hN0_gt
  have hlimit_close :
      |w Uinf (N0 : ℝ) xinf - longTimeMap w Uinf xinf| < ε / 3 := by
    have hdist := hT0 (N0 : ℝ) hN0_ge
    simpa [Real.dist_eq] using hdist
  have hfinite_conv :
      ShenWork.Paper1.LocallyUniformConverges
        (fun n => w (Ubad (subseq n)) (N0 : ℝ)) (w Uinf (N0 : ℝ)) :=
    hfinite (N0 : ℝ) (fun n => Ubad (subseq n)) Uinf
      (fun n => hUbad (subseq n)) hUinf hUconv
  have hw_eval_tend :
      Tendsto
        (fun n => w (Ubad (subseq n)) (N0 : ℝ) (xbad (subseq n)))
        atTop (𝓝 (w Uinf (N0 : ℝ) xinf)) :=
    tendsto_eval_of_locallyUniformConverges
      (R := R) hR (fun n => hxbad (subseq n)) hfinite_conv
      (hslice Uinf hUinf (N0 : ℝ)) hxconv
  have himage_conv :
      ShenWork.Paper1.LocallyUniformConverges
        (fun n => longTimeMap w (Ubad (subseq n))) (longTimeMap w Uinf) :=
    Hdini.image_parameter_continuity (fun n => Ubad (subseq n)) Uinf
      (fun n => hUbad (subseq n)) hUinf hUconv
  have hL_eval_tend :
      Tendsto
        (fun n => longTimeMap w (Ubad (subseq n)) (xbad (subseq n)))
        atTop (𝓝 (longTimeMap w Uinf xinf)) :=
    tendsto_eval_of_locallyUniformConverges
      (R := R) hR (fun n => hxbad (subseq n)) himage_conv
      (himage Uinf hUinf) hxconv
  have hdiff_tend :
      Tendsto
        (fun n =>
          w (Ubad (subseq n)) (N0 : ℝ) (xbad (subseq n)) -
            longTimeMap w (Ubad (subseq n)) (xbad (subseq n)))
        atTop
        (𝓝 (w Uinf (N0 : ℝ) xinf - longTimeMap w Uinf xinf)) :=
    hw_eval_tend.sub hL_eval_tend
  have hdiff_event :
      ∀ᶠ n in atTop,
        |(w (Ubad (subseq n)) (N0 : ℝ) (xbad (subseq n)) -
            longTimeMap w (Ubad (subseq n)) (xbad (subseq n))) -
          (w Uinf (N0 : ℝ) xinf - longTimeMap w Uinf xinf)| < ε / 3 := by
    rcases Metric.tendsto_atTop.mp hdiff_tend (ε / 3) hε3 with
      ⟨N, hN⟩
    exact eventually_atTop.2
      ⟨N, fun n hn => by
        have hn' := hN n hn
        rw [Real.dist_eq] at hn'
        convert hn' using 1⟩
  have hsubseq_ge :
      ∀ᶠ n in atTop, N0 ≤ subseq n :=
    hsubseq.tendsto_atTop.eventually (Filter.eventually_ge_atTop N0)
  rcases eventually_atTop.1 (hsubseq_ge.and hdiff_event) with ⟨n1, hn1⟩
  have hn := hn1 n1 (le_refl n1)
  have hNle_nat : N0 ≤ subseq n1 := hn.1
  have hdiff_close := hn.2
  let Ub := Ubad (subseq n1)
  let xb := xbad (subseq n1)
  have hUb : Ub ∈ WaveTrap κ κt D := hUbad (subseq n1)
  have hLle_late :
      longTimeMap w Ub xb ≤ w Ub (subseq n1 : ℝ) xb :=
    longTimeMap_le_time hlower hUb (subseq n1 : ℝ) xb
  have hbad_noabs :
      ε ≤ w Ub (subseq n1 : ℝ) xb - longTimeMap w Ub xb := by
    have hnonneg :
        0 ≤ w Ub (subseq n1 : ℝ) xb - longTimeMap w Ub xb :=
      sub_nonneg.mpr hLle_late
    simpa [Ub, xb, abs_of_nonneg hnonneg] using hbad_eval (subseq n1)
  have htime_le :
      w Ub (subseq n1 : ℝ) xb ≤ w Ub (N0 : ℝ) xb :=
    (htime Ub hUb xb) (by exact_mod_cast hNle_nat)
  have hbad_fixed :
      ε ≤ w Ub (N0 : ℝ) xb - longTimeMap w Ub xb := by
    linarith
  have hfixed_lt :
      w Ub (N0 : ℝ) xb - longTimeMap w Ub xb < ε := by
    have hdiff_upper :
        (w Ub (N0 : ℝ) xb - longTimeMap w Ub xb) -
            (w Uinf (N0 : ℝ) xinf - longTimeMap w Uinf xinf) < ε / 3 :=
      (abs_lt.mp (by simpa [Ub, xb] using hdiff_close)).2
    have hlimit_upper :
        w Uinf (N0 : ℝ) xinf - longTimeMap w Uinf xinf < ε / 3 :=
      (abs_lt.mp hlimit_close).2
    linarith
  exact not_lt_of_ge hbad_fixed hfixed_lt

/-- Spatial continuity of each long-time image from the derivative bridge. -/
theorem longTime_image_continuity_of_derivative_bridge
    {p : CMParams} {c κ κt D Λ : ℝ}
    {raw_w raw_wx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    (Himage :
      WholeLineLongTimeImageDerivativeBridgeData p c κ κt D Λ raw_w raw_wx) :
    LongTimeMapImageContinuity κ κt D
      (wholeLineForwardOrbitExtension κ raw_w) := by
  intro U hU
  let seq : ℕ → ℝ → ℝ := fun _ => U
  have hseq : ∀ n, seq n ∈ WaveTrap κ κt D := fun _ => hU
  have hdiff := Himage.image_differentiable seq hseq 0
  simpa [seq] using hdiff.continuous

/-- The `fixedPoint_flat_left` residual field from the named parabolic
left-tail bridge. -/
theorem fixedPoint_flat_left_discharge
    {p : CMParams} {c κt D : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    (hflat :
      FixedPointFlatLeftParabolicTailFromMonotoneLimit p c κt D Haux) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) U = U →
        ShenWork.Paper1.FrozenStationaryFlatAtLeft p U :=
  fixedPoint_flat_left_of_waveTrap hflat

/-- `WaveResidualWired9` with the last two fields supplied by the Dini discharge
and the parabolic left-tail bridge. -/
def wholeLineWaveExistenceConsolidatedResidualData_lastTwo
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    {w0 : ℝ → ℝ → ℝ} {V0 Vx0 : ℝ → ℝ}
    (Hparams : WholeLineOrbitTrappingData p c κt D w0 V0 Vx0)
    (hχ : p.χ ≤ 0) (hχ0 : p3.χ₀ = p.χ)
    (Horbit : WholeLineOrbitPropertiesData p c κt D Haux.raw_w)
    (Hduhamel :
      ∀ t,
        ShenWork.Paper1.LocalUniformContinuousOn
          (fun U : ℝ → ℝ => U ∈ WaveTrap (waveExponent c) κt D)
          (residualAuxDuhamelOnTrap p c Haux.raw_w Haux.raw_wx t))
    (Hslice : WholeLineAuxiliaryMildSliceContinuityData p c κt D Haux)
    (Htime :
      WholeLineTimeMonotonicityFamilyData (waveExponent c) κt D
        Haux.raw_w
        (concreteLongTimeAuxiliaryWt p c (waveExponent c)
          Haux.raw_w Haux.raw_wx wxx)
        Haux.raw_wx wxx)
    (Hdini :
      LongTimeUniformDiniParameterData (waveExponent c) κt D
        (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w))
    (Himage :
      WholeLineLongTimeImageDerivativeBridgeData p c (waveExponent c) κt D Λ
        Haux.raw_w Haux.raw_wx)
    (Hderiv :
      ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
        WholeLineParabolicDerivativeConvergence
          (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U)
          (concreteLongTimeAuxiliaryWt p c (waveExponent c)
            Haux.raw_w Haux.raw_wx wxx U)
          (Haux.raw_wx U) (wxx U)
          (wholeLineLongTimeLimit
            (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U)))
    (Hprofile :
      ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
        longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w)
            U = U →
          ∃ Ux Uxx : ℝ → ℝ,
            WholeLineProfileRegularityData p U (frozenSignal p.γ U) Ux Uxx)
    (Hflat :
      FixedPointFlatLeftParabolicTailFromMonotoneLimit p c κt D Haux)
    (Hid : TranslateLimitIdentificationParabolicData p c p3) :
    WholeLineWaveExistenceConsolidatedResidualData p c κt D Λ Haux
      (concreteLongTimeAuxiliaryWt p c (waveExponent c)
        Haux.raw_w Haux.raw_wx wxx)
      wxx p3 :=
  wholeLineWaveExistenceConsolidatedResidualData_wired9
    Hparams hχ hχ0 Horbit Hduhamel Hslice Htime
    (longTime_uniform_tail_discharge
      (κ := waveExponent c) (κt := κt) (D := D)
      (w := wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w)
      (wholeLine_orbit_lower_bound Horbit)
      (waveResidualWired9_longTime_time_antitone Horbit Htime)
      (waveResidualWired9_finite_time_slice_continuity Hslice)
      (longTime_finite_time_continuity_of_mildmap
        (κ := waveExponent c) (κt := κt) (D := D) (χ := p.χ)
        (w := wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w)
        (semigroupTerm := residualAuxSemigroupTerm c (waveExponent c))
        (chemDuhamel := residualAuxChemDuhamel)
        (reactionDuhamel :=
          residualAuxReactionDuhamel p c (waveExponent c) κt D
            Haux.raw_w Haux.raw_wx)
        (by
          intro t U x
          exact
            WholeLineWaveExistenceConsolidatedResidualData.mild_decomp
              (p := p) (c := c) (κt := κt) (D := D)
              (Haux := Haux) t U x)
        (fun _ =>
          localUniformContinuousOn_zero
            (fun U : ℝ → ℝ => U ∈ WaveTrap (waveExponent c) κt D))
        (fun t =>
          residualAuxReactionDuhamel_continuity
            (Hduhamel t)))
      (longTime_image_continuity_of_derivative_bridge Himage)
      Hdini)
    Himage Hderiv Hprofile
    (fixedPoint_flat_left_discharge Hflat)
    Hid

section AxiomAudit

#print axioms WaveTrapWindowSequentialCompactness
#print axioms LongTimeMapImageParameterContinuity
#print axioms LongTimeUniformDiniParameterData
#print axioms tendsto_eval_of_locallyUniformConverges
#print axioms longTimeMap_le_time
#print axioms longTime_uniform_tail_discharge
#print axioms longTime_image_continuity_of_derivative_bridge
#print axioms fixedPoint_flat_left_discharge
#print axioms wholeLineWaveExistenceConsolidatedResidualData_lastTwo

end AxiomAudit

end ShenWork.PaperOne
