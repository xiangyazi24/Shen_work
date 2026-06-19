import ShenWork.PaperOne.WaveResidualLastTwo
import ShenWork.PaperOne.WholeLineProfileRegularityFromWeak
import ShenWork.PaperOne.WholeLineFlowWeakFormDischarge
import ShenWork.Paper1.InMonotoneWaveTrapSchauderPrinciple
import Mathlib.Tactic

open Filter MeasureTheory Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

abbrev assembledForwardOrbit
    {p : CMParams} {c κt D : ℝ}
    (Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D)
    (U : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w U

abbrev assembledConcreteWt
    {p : CMParams} {c κt D : ℝ}
    (Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D)
    (wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (U : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  concreteLongTimeAuxiliaryWt p c (waveExponent c)
    Haux.raw_w Haux.raw_wx wxx U

private theorem abs_sub_le_of_deriv_abs_le
    {f : ℝ → ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hdiff : Differentiable ℝ f) (hderiv : ∀ x, |deriv f x| ≤ Λ) :
    ∀ x y, |f x - f y| ≤ Λ * |x - y| := by
  intro x y
  have hLip := ShenWork.Paper1.crossImplicitStep_lipschitz hΛ hdiff hderiv
  have hdist := hLip.dist_le_mul x y
  simpa [Real.dist_eq, Real.coe_toNNReal _ hΛ] using hdist

private theorem inConstantBarrierTrap_one_of_bounds
    {f : ℝ → ℝ}
    (hcont : Continuous f)
    (hnonneg : ∀ x, 0 ≤ f x)
    (hle_one : ∀ x, f x ≤ 1) :
    ShenWork.Paper1.InConstantBarrierTrap 1 f := by
  refine ⟨⟨hcont, ⟨1, ?_⟩⟩, fun x => ⟨hnonneg x, hle_one x⟩⟩
  intro x
  rw [abs_of_nonneg (hnonneg x)]
  exact hle_one x

private theorem longTimeLimit_lipschitz_of_image_bridge
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    (Himage :
      WholeLineLongTimeImageDerivativeBridgeData p c (waveExponent c) κt D Λ
        Haux.raw_w Haux.raw_wx)
    {U : ℝ → ℝ} (hU : U ∈ WaveTrap (waveExponent c) κt D) :
    ∀ x y,
      |wholeLineLongTimeLimit (assembledForwardOrbit Haux U) x -
          wholeLineLongTimeLimit (assembledForwardOrbit Haux U) y|
        ≤ Λ * |x - y| := by
  let seq : ℕ → ℝ → ℝ := fun _ => U
  have hseq : ∀ n, seq n ∈ WaveTrap (waveExponent c) κt D := fun _ => hU
  have hdiff :
      Differentiable ℝ
        (longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) U) := by
    simpa [seq] using Himage.image_differentiable seq hseq 0
  have hderiv :
      ∀ x,
        |deriv
          (longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) U) x|
            ≤ Λ := by
    intro x
    simpa [seq] using Himage.image_deriv_bound seq hseq 0 x
  intro x y
  simpa [longTimeMap, assembledForwardOrbit] using
    abs_sub_le_of_deriv_abs_le Himage.lambda_nonneg hdiff hderiv x y

private theorem finite_slice_inConstantBarrierTrap_one
    {p : CMParams} {c κt D : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    (Horbit : WholeLineOrbitPropertiesData p c κt D Haux.raw_w)
    (Hslice : WholeLineAuxiliaryMildSliceContinuityData p c κt D Haux)
    {U : ℝ → ℝ} (hU : U ∈ WaveTrap (waveExponent c) κt D)
    (n : ℕ) :
    ShenWork.Paper1.InConstantBarrierTrap 1
      (fun x => assembledForwardOrbit Haux U (n : ℝ) x) := by
  have hcont :
      Continuous (fun x => assembledForwardOrbit Haux U (n : ℝ) x) := by
    simpa [assembledForwardOrbit] using
      waveResidualWired9_finite_time_slice_continuity Hslice U hU (n : ℝ)
  refine inConstantBarrierTrap_one_of_bounds hcont ?_ ?_
  · intro x
    exact le_trans
      (lowerBarrier_nonneg (waveExponent c) κt D x)
      (wholeLine_orbit_lower_bound Horbit U hU (n : ℝ) x)
  · intro x
    exact le_trans
      (wholeLine_orbit_upper_bound Horbit U hU (n : ℝ) x)
      (upperBarrier_le_one (waveExponent c) x)

private theorem longTimeLimit_inConstantBarrierTrap_one
    {p : CMParams} {c κt D Λ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    (Horbit : WholeLineOrbitPropertiesData p c κt D Haux.raw_w)
    (Himage :
      WholeLineLongTimeImageDerivativeBridgeData p c (waveExponent c) κt D Λ
        Haux.raw_w Haux.raw_wx)
    {U : ℝ → ℝ} (hU : U ∈ WaveTrap (waveExponent c) κt D) :
    ShenWork.Paper1.InConstantBarrierTrap 1
      (wholeLineLongTimeLimit (assembledForwardOrbit Haux U)) := by
  let seq : ℕ → ℝ → ℝ := fun _ => U
  have hseq : ∀ n, seq n ∈ WaveTrap (waveExponent c) κt D := fun _ => hU
  have hcont :
      Continuous (wholeLineLongTimeLimit (assembledForwardOrbit Haux U)) := by
    have hdiff :=
      Himage.image_differentiable seq hseq 0
    simpa [seq, longTimeMap, assembledForwardOrbit] using hdiff.continuous
  refine inConstantBarrierTrap_one_of_bounds hcont ?_ ?_
  · intro x
    exact le_trans
      (lowerBarrier_nonneg (waveExponent c) κt D x)
      (wholeLine_longTime_limit_lowerBarrier
        (κ := waveExponent c) (κt := κt) (D := D)
        (w := assembledForwardOrbit Haux U)
        (wholeLine_orbit_lower_bound Horbit U hU) x)
  · intro x
    exact le_trans
      (wholeLine_longTime_limit_upperBarrier
        (κ := waveExponent c) (κt := κt) (D := D)
        (w := assembledForwardOrbit Haux U)
        (wholeLine_orbit_lower_bound Horbit U hU)
        (wholeLine_orbit_upper_bound Horbit U hU) x)
      (upperBarrier_le_one (waveExponent c) x)

theorem banked_inMonotone_schauder_for_height_one {c : ℝ} :
    ShenWork.Paper1.LocalUniformSchauderFixedPointPrinciple
      (ShenWork.Paper1.InMonotoneWaveTrapSet (waveExponent c) 1) :=
  ShenWork.Paper1.inMonotoneWaveTrap_schauderPrinciple (by norm_num)

theorem fixedPoint_profile_regularity_from_banked_weak
    {p : CMParams} {c κt D Λ τ : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    (Horbit : WholeLineOrbitPropertiesData p c κt D Haux.raw_w)
    (Hslice : WholeLineAuxiliaryMildSliceContinuityData p c κt D Haux)
    (Htime :
      WholeLineTimeMonotonicityFamilyData (waveExponent c) κt D
        Haux.raw_w (assembledConcreteWt Haux wxx) Haux.raw_wx wxx)
    (Himage :
      WholeLineLongTimeImageDerivativeBridgeData p c (waveExponent c) κt D Λ
        Haux.raw_w Haux.raw_wx)
    (hτ_pos : 0 < τ)
    (Hflow_lip :
      ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
        ∀ t x y,
          |assembledForwardOrbit Haux U t x -
              assembledForwardOrbit Haux U t y| ≤ Λ * |x - y|)
    (Hclassical :
      ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
        ∀ T > 0,
          IsAuxiliaryClassicalSolutionOn p c
            (frozenSignal p.γ U)
            (fun x => deriv (frozenSignal p.γ U) x)
            T
            (assembledForwardOrbit Haux U)
            (Haux.raw_wx U) (wxx U)
            (assembledConcreteWt Haux wxx U))
    (Hweak :
      ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
        WholeLineClassicalWeakFormData p c τ
          (frozenSignal p.γ U)
          (fun x => deriv (frozenSignal p.γ U) x)
          (assembledForwardOrbit Haux U)
          (Haux.raw_wx U) (wxx U)
          (assembledConcreteWt Haux wxx U))
    (Htest_l1 : ∀ Φ : WholeLineWeakTestFunction, Integrable Φ.phi)
    (HwindowDCT :
      ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
        ∀
          (_orbit_locunif :
            ShenWork.Paper1.LocallyUniformConverges
              (fun n x => assembledForwardOrbit Haux U (n : ℝ) x)
              (wholeLineLongTimeLimit (assembledForwardOrbit Haux U)))
          (_shift_locunif :
            ∀ R > 0, ∀ ε > 0,
              ∀ᶠ n : ℕ in atTop,
                ∀ s : ℝ, s ∈ Icc (0 : ℝ) τ →
                  ∀ x : ℝ, x ∈ Icc (-R) R →
                    |assembledForwardOrbit Haux U ((n : ℝ) + s) x -
                        wholeLineLongTimeLimit (assembledForwardOrbit Haux U) x| < ε)
          (_flux_locunif :
            ShenWork.Paper1.LocallyUniformConverges
              (fun n x =>
                wholeLineFlux p
                  (fun y => assembledForwardOrbit Haux U (n : ℝ) y) x)
              (wholeLineFlux p
                (wholeLineLongTimeLimit (assembledForwardOrbit Haux U))))
          (_reaction_locunif :
            ShenWork.Paper1.LocallyUniformConverges
              (fun n x =>
                wholeLineReaction p
                  (fun y => assembledForwardOrbit Haux U (n : ℝ) y) x)
              (wholeLineReaction p
                (wholeLineLongTimeLimit (assembledForwardOrbit Haux U))))
          (Φ : WholeLineWeakTestFunction),
            WholeLineTimeWindowDCTData p c
              (assembledForwardOrbit Haux U)
              (wholeLineLongTimeLimit (assembledForwardOrbit Haux U)) τ Φ) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w)
          U = U →
        ∃ Ux Uxx : ℝ → ℝ,
          WholeLineProfileRegularityData p U (frozenSignal p.γ U) Ux Uxx := by
  intro U hU hfixed
  have htimeU :
      ∀ x, Antitone fun t : ℝ => assembledForwardOrbit Haux U t x := by
    simpa [assembledForwardOrbit] using
      waveResidualWired9_longTime_time_antitone
        (Haux := Haux) (wxx := wxx) Horbit Htime U hU
  have hlowerU :
      ∀ t x,
        lowerBarrier (waveExponent c) κt D x ≤
          assembledForwardOrbit Haux U t x := by
    simpa [assembledForwardOrbit] using
      wholeLine_orbit_lower_bound Horbit U hU
  have hU_lip :
      ∀ x y,
        |wholeLineLongTimeLimit (assembledForwardOrbit Haux U) x -
            wholeLineLongTimeLimit (assembledForwardOrbit Haux U) y|
          ≤ Λ * |x - y| :=
    longTimeLimit_lipschitz_of_image_bridge Himage hU
  have horbit_locunif :
      ShenWork.Paper1.LocallyUniformConverges
        (fun n x => assembledForwardOrbit Haux U (n : ℝ) x)
        (wholeLineLongTimeLimit (assembledForwardOrbit Haux U)) :=
    longtime_limit_locallyUniform
      (κ := waveExponent c) (κt := κt) (D := D) (Λ := Λ)
      (w := assembledForwardOrbit Haux U)
      htimeU hlowerU Himage.lambda_nonneg (Hflow_lip U hU) hU_lip
  have hshift_locunif :
      ∀ R > 0, ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop,
          ∀ s : ℝ, s ∈ Icc (0 : ℝ) τ →
            ∀ x : ℝ, x ∈ Icc (-R) R →
              |assembledForwardOrbit Haux U ((n : ℝ) + s) x -
                  wholeLineLongTimeLimit (assembledForwardOrbit Haux U) x| < ε :=
    time_shift_locallyUniform
      (κ := waveExponent c) (κt := κt) (D := D) (τ := τ)
      (w := assembledForwardOrbit Haux U)
      htimeU hlowerU horbit_locunif
  have hinc :
      WholeLineWeakIncrementVanishes (assembledForwardOrbit Haux U) τ :=
    wholeLineWeakIncrementVanishes_of_locUnifLimit
      hτ_pos.le horbit_locunif hshift_locunif Htest_l1
  have hweak_flow :
      WholeLineFlowWeakForm p c (assembledForwardOrbit Haux U) τ :=
    wholeLineFlowWeakForm_of_classical
      (p := p) (c := c) (τ := τ)
      (V := frozenSignal p.γ U)
      (Vx := fun x => deriv (frozenSignal p.γ U) x)
      (w := assembledForwardOrbit Haux U)
      (wx := Haux.raw_wx U) (wxx := wxx U)
      (wt := assembledConcreteWt Haux wxx U)
      (Hclassical U hU) (Hweak U hU)
  have hDCT :
      WholeLineTimeIntegratedWeakDCT p c
        (assembledForwardOrbit Haux U)
        (wholeLineLongTimeLimit (assembledForwardOrbit Haux U)) τ :=
    wholeLineTimeIntegratedWeakDCT_of_bounds
      (p := p) (c := c) (w := assembledForwardOrbit Haux U)
      (U := wholeLineLongTimeLimit (assembledForwardOrbit Haux U))
      (τ := τ) hτ_pos
      (HwindowDCT U hU)
  have hseq_trap :
      ∀ n : ℕ,
        ShenWork.Paper1.InConstantBarrierTrap 1
          (fun x => assembledForwardOrbit Haux U (n : ℝ) x) :=
    finite_slice_inConstantBarrierTrap_one Horbit Hslice hU
  have hlimit_trap :
      ShenWork.Paper1.InConstantBarrierTrap 1
        (wholeLineLongTimeLimit (assembledForwardOrbit Haux U)) :=
    longTimeLimit_inConstantBarrierTrap_one Horbit Himage hU
  have hweak_stationary_limit :
      WholeLineWeakStationary p c
        (wholeLineLongTimeLimit (assembledForwardOrbit Haux U)) :=
    wholeLine_longTime_weak_stationary
      (p := p) (c := c) (τ := τ) (κ := waveExponent c)
      (κt := κt) (D := D) (Λ := Λ) (M := 1)
      (w := assembledForwardOrbit Haux U)
      (ne_of_gt hτ_pos) htimeU hlowerU Himage.lambda_nonneg
      (Hflow_lip U hU) hU_lip (by norm_num) hseq_trap hlimit_trap
      hweak_flow hinc hDCT
  have hlimit_eq :
      wholeLineLongTimeLimit (assembledForwardOrbit Haux U) = U := by
    simpa [assembledForwardOrbit, longTimeMap] using hfixed
  have hweak_stationary_U : WholeLineWeakStationary p c U := by
    simpa [hlimit_eq] using hweak_stationary_limit
  have hU_const_trap : ShenWork.Paper1.InConstantBarrierTrap 1 U := by
    simpa [hlimit_eq] using hlimit_trap
  exact fixedPoint_profile_regularity_from_weak
    (p := p) (c := c) (M := 1) hU_const_trap hweak_stationary_U

theorem wholeLine_travelingWave_exists_assembled
    (p : CMParams)
    (hχ : p.χ ≤ 0) (hα : p.α ≤ p.m + p.γ - 1)
    {c κt D Λ τ : ℝ}
    (hc : 2 < c)
    (hκt : waveExponent c < κt) (hD : 1 ≤ D)
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (hχ0 : p3.χ₀ = p.χ)
    (Hschauder_waveTrap :
      ShenWork.Paper1.LocalUniformSchauderFixedPointPrinciple
        (fun U : ℝ → ℝ => U ∈ WaveTrap (waveExponent c) κt D))
    (Horbit : WholeLineOrbitPropertiesData p c κt D Haux.raw_w)
    (Hduhamel :
      ∀ t,
        ShenWork.Paper1.LocalUniformContinuousOn
          (fun U : ℝ → ℝ => U ∈ WaveTrap (waveExponent c) κt D)
          (residualAuxDuhamelOnTrap p c Haux.raw_w Haux.raw_wx t))
    (Hslice : WholeLineAuxiliaryMildSliceContinuityData p c κt D Haux)
    (Htime :
      WholeLineTimeMonotonicityFamilyData (waveExponent c) κt D
        Haux.raw_w (assembledConcreteWt Haux wxx) Haux.raw_wx wxx)
    (Hdini :
      LongTimeUniformDiniParameterData (waveExponent c) κt D
        (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w))
    (Himage :
      WholeLineLongTimeImageDerivativeBridgeData p c (waveExponent c) κt D Λ
        Haux.raw_w Haux.raw_wx)
    (Hderiv :
      ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
        WholeLineParabolicDerivativeConvergence
          (assembledForwardOrbit Haux U)
          (assembledConcreteWt Haux wxx U)
          (Haux.raw_wx U) (wxx U)
          (wholeLineLongTimeLimit (assembledForwardOrbit Haux U)))
    (Hflat :
      FixedPointFlatLeftParabolicTailFromMonotoneLimit p c κt D Haux)
    (Hid : TranslateLimitIdentificationParabolicData p c p3)
    (hτ_pos : 0 < τ)
    (Hflow_lip :
      ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
        ∀ t x y,
          |assembledForwardOrbit Haux U t x -
              assembledForwardOrbit Haux U t y| ≤ Λ * |x - y|)
    (Hclassical :
      ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
        ∀ T > 0,
          IsAuxiliaryClassicalSolutionOn p c
            (frozenSignal p.γ U)
            (fun x => deriv (frozenSignal p.γ U) x)
            T
            (assembledForwardOrbit Haux U)
            (Haux.raw_wx U) (wxx U)
            (assembledConcreteWt Haux wxx U))
    (Hweak :
      ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
        WholeLineClassicalWeakFormData p c τ
          (frozenSignal p.γ U)
          (fun x => deriv (frozenSignal p.γ U) x)
          (assembledForwardOrbit Haux U)
          (Haux.raw_wx U) (wxx U)
          (assembledConcreteWt Haux wxx U))
    (Htest_l1 : ∀ Φ : WholeLineWeakTestFunction, Integrable Φ.phi)
    (HwindowDCT :
      ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
        ∀
          (_orbit_locunif :
            ShenWork.Paper1.LocallyUniformConverges
              (fun n x => assembledForwardOrbit Haux U (n : ℝ) x)
              (wholeLineLongTimeLimit (assembledForwardOrbit Haux U)))
          (_shift_locunif :
            ∀ R > 0, ∀ ε > 0,
              ∀ᶠ n : ℕ in atTop,
                ∀ s : ℝ, s ∈ Icc (0 : ℝ) τ →
                  ∀ x : ℝ, x ∈ Icc (-R) R →
                    |assembledForwardOrbit Haux U ((n : ℝ) + s) x -
                        wholeLineLongTimeLimit (assembledForwardOrbit Haux U) x| < ε)
          (_flux_locunif :
            ShenWork.Paper1.LocallyUniformConverges
              (fun n x =>
                wholeLineFlux p
                  (fun y => assembledForwardOrbit Haux U (n : ℝ) y) x)
              (wholeLineFlux p
                (wholeLineLongTimeLimit (assembledForwardOrbit Haux U))))
          (_reaction_locunif :
            ShenWork.Paper1.LocallyUniformConverges
              (fun n x =>
                wholeLineReaction p
                  (fun y => assembledForwardOrbit Haux U (n : ℝ) y) x)
              (wholeLineReaction p
                (wholeLineLongTimeLimit (assembledForwardOrbit Haux U))))
          (Φ : WholeLineWeakTestFunction),
            WholeLineTimeWindowDCTData p c
              (assembledForwardOrbit Haux U)
              (wholeLineLongTimeLimit (assembledForwardOrbit Haux U)) τ Φ) :
    ∃ Ustar Vstar : ℝ → ℝ,
      WholeLineTravelingWaveProfile p c (waveExponent c) Ustar Vstar := by
  have hupper_mem :
      upperBarrier (waveExponent c) ∈ WaveTrap (waveExponent c) κt D :=
    waveTrap_upper_mem (waveExponent_pos (le_of_lt hc)) hκt hD
  let Hparams :
      WholeLineOrbitTrappingData p c κt D
        (Haux.raw_w (upperBarrier (waveExponent c)))
        (frozenSignal p.γ (upperBarrier (waveExponent c)))
        (fun x => deriv (frozenSignal p.γ (upperBarrier (waveExponent c))) x) :=
    Horbit.trapping (upperBarrier (waveExponent c)) hupper_mem
  refine
    wholeLine_travelingWave_exists_consolidated
      (p := p) hχ hα (c := c) (κt := κt) (D := D) (Λ := Λ)
      (hc := hc) (Haux := Haux)
      (wt := assembledConcreteWt Haux wxx) (wxx := wxx) (p3 := p3)
      Hschauder_waveTrap ?_
  exact
    wholeLineWaveExistenceConsolidatedResidualData_lastTwo
      (p := p) (c := c) (κt := κt) (D := D) (Λ := Λ)
      (Haux := Haux) (wxx := wxx) (p3 := p3)
      Hparams hχ hχ0 Horbit Hduhamel Hslice Htime Hdini Himage Hderiv
      (fixedPoint_profile_regularity_from_banked_weak
        (p := p) (c := c) (κt := κt) (D := D) (Λ := Λ) (τ := τ)
        (Haux := Haux) (wxx := wxx)
        Horbit Hslice Htime Himage hτ_pos
        Hflow_lip Hclassical Hweak Htest_l1 HwindowDCT)
      Hflat Hid

#print axioms banked_inMonotone_schauder_for_height_one
#print axioms fixedPoint_profile_regularity_from_banked_weak
#print axioms wholeLine_travelingWave_exists_assembled

end ShenWork.PaperOne
