import ShenWork.PaperOne.WholeLineTravelingWaveDataBuilder
import ShenWork.PaperOne.WholeLineAuxiliaryExistence
import ShenWork.PaperOne.WholeLineTranslateCompactness
import Mathlib.Tactic

open Filter Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/--
PaperOne's frozen signal is the same whole-line resolvent as the older
Paper1 `frozenElliptic` interface.
-/
theorem frozenSignal_eq_frozenElliptic (p : CMParams) (U : ℝ → ℝ) :
    frozenSignal p.γ U = ShenWork.Paper1.frozenElliptic p U := by
  funext x
  simp [frozenSignal, ShenWork.Paper1.frozenElliptic, wholeLineResolvent_eq_Psi]

theorem wholeLineDivergenceStationaryOperator_eq_frozenWaveOperator
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) (x : ℝ) :
    wholeLineDivergenceStationaryOperator p c U x =
      ShenWork.Paper1.frozenWaveOperator p c U U x := by
  unfold wholeLineDivergenceStationaryOperator
    ShenWork.Paper1.frozenWaveOperator wholeLineReaction
  rw [frozenSignal_eq_frozenElliptic p U]

private theorem differentiableAt_deriv_of_contDiff_two_reduced
    {V : ℝ → ℝ} (hV : ContDiff ℝ 2 V) :
    ∀ x, DifferentiableAt ℝ (deriv V) x := by
  have hD : Differentiable ℝ (iteratedDeriv 1 V) :=
    hV.differentiable_iteratedDeriv 1 (by norm_num)
  intro x
  simpa [iteratedDeriv_one] using hD x

theorem translate_equicontinuousOn_of_uniform_deriv_bound
    {U : ℝ → ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hdiff : Differentiable ℝ U)
    (hderiv : ∀ x, |deriv U x| ≤ Λ) :
    ∀ K : Set ℝ, IsCompact K →
      EquicontinuousOn
        (fun (n : ℕ) (x : ℝ) => U (x + (-(n : ℝ)))) K := by
  intro K _hK
  refine equicontinuousOn_of_uniform_deriv_bound (Λ := Λ) hΛ ?_ ?_ K
  · intro n
    exact hdiff.comp
      (differentiable_id.add (differentiable_const (c := -((n : ℕ) : ℝ))))
  · intro n x
    let a : ℝ := -((n : ℕ) : ℝ)
    have hshift : HasDerivAt (fun z : ℝ => z + a) 1 x := by
      simpa using (hasDerivAt_id x).add_const a
    have hcomp :
        HasDerivAt (fun z : ℝ => U (z + a)) (deriv U (x + a)) x :=
      by
        simpa [Function.comp] using
          (hdiff (x + a)).hasDerivAt.comp x hshift
    have hderiv_eq :
        deriv (fun z : ℝ => U (z + a)) x = deriv U (x + a) :=
      hcomp.deriv
    simpa [a, hderiv_eq] using hderiv (x + a)

theorem localUniformContinuousOn_zero
    (trap : (ℝ → ℝ) → Prop) :
    ShenWork.Paper1.LocalUniformContinuousOn trap
      (fun (_U : ℝ → ℝ) (_x : ℝ) => 0) := by
  intro _seq _u _hseq _hu _hconv R hR ε hε
  exact Eventually.of_forall fun _n x _hx => by
    simpa using hε

/-- Semigroup leg for the all-time forward extension. -/
def residualAuxSemigroupTerm (c κ : ℝ) (t x : ℝ) : ℝ :=
  if 0 ≤ t then movingFrameHeatOp c t (upperBarrier κ) x else upperBarrier κ x

/-- The residual chem leg is unused for the aggregate auxiliary Duhamel split. -/
def residualAuxChemDuhamel (_t : ℝ) (_U : ℝ → ℝ) (_x : ℝ) : ℝ :=
  0

/-- Aggregate auxiliary Duhamel leg on the trapped domain. -/
def residualAuxDuhamelOnTrap
    (p : CMParams) (c : ℝ)
    (raw_w wx : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (t : ℝ) (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 ≤ t then
    auxiliaryDuhamel p c (raw_w U) (wx U)
      (frozenSignal p.γ U)
      (fun y => deriv (frozenSignal p.γ U) y) t x
  else 0

/--
Reaction leg used by the residual interface.  On the trapped domain this is
the aggregate auxiliary Duhamel term; off the trapped domain it is only the
extension needed because the old residual decomposition has no trap premise.
-/
def residualAuxReactionDuhamel
    (p : CMParams) (c κ κt D : ℝ)
    (raw_w wx : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (t : ℝ) (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  by
    classical
    exact
      if U ∈ WaveTrap κ κt D then
        residualAuxDuhamelOnTrap p c raw_w wx t U x
      else
        wholeLineForwardOrbitExtension κ raw_w U t x -
          residualAuxSemigroupTerm c κ t x

theorem residualAuxReactionDuhamel_continuity
    {p : CMParams} {c κ κt D : ℝ}
    {raw_w wx : (ℝ → ℝ) → ℝ → ℝ → ℝ} {t : ℝ}
    (hcont :
      ShenWork.Paper1.LocalUniformContinuousOn
        (fun U : ℝ → ℝ => U ∈ WaveTrap κ κt D)
        (residualAuxDuhamelOnTrap p c raw_w wx t)) :
    ShenWork.Paper1.LocalUniformContinuousOn
      (fun U : ℝ → ℝ => U ∈ WaveTrap κ κt D)
      (residualAuxReactionDuhamel p c κ κt D raw_w wx t) := by
  intro seq u hseq hu hconv
  classical
  intro R hR ε hε
  filter_upwards [hcont seq u hseq hu hconv R hR ε hε] with n hn
  intro x hx
  simpa [residualAuxReactionDuhamel, hu, hseq n] using hn x hx

/--
The reduced core left after wiring the banked auxiliary mild solution,
parabolic equicontinuity, stationarity, and translate compactness into
`WholeLineTravelingWaveResidualData`.
-/
structure WholeLineTravelingWaveCoreData
    (p : CMParams) (c κt D Λ : ℝ)
    (raw_w wt wx wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (p3 : CM2Params) where
  kappa_lt_kappat : waveExponent c < κt
  D_ge_one : 1 ≤ D
  paper3_chi_nonpos : p3.χ₀ ≤ 0
  orbit_properties : WholeLineOrbitPropertiesData p c κt D raw_w
  auxiliary_solution :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      ∀ T > 0,
        AuxiliaryMildSolutionOn p c
          (upperBarrier (waveExponent c))
          (frozenSignal p.γ U)
          (fun x => deriv (frozenSignal p.γ U) x)
          (waveExponent c) κt D T
          (raw_w U) (wx U)
  auxiliaryDuhamel_continuity :
    ∀ t,
      ShenWork.Paper1.LocalUniformContinuousOn
        (fun U : ℝ → ℝ => U ∈ WaveTrap (waveExponent c) κt D)
        (residualAuxDuhamelOnTrap p c raw_w wx t)
  finite_time_slice_continuity :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      ∀ t, Continuous
        (wholeLineForwardOrbitExtension (waveExponent c) raw_w U t)
  longTime_uniform_tail :
    LongTimeMapUniformTail (waveExponent c) κt D
      (wholeLineForwardOrbitExtension (waveExponent c) raw_w)
  longTime_deriv_bound_nonneg : 0 ≤ Λ
  longTime_image_differentiable :
    ∀ seq : ℕ → ℝ → ℝ,
      (∀ n, seq n ∈ WaveTrap (waveExponent c) κt D) →
        ∀ n, Differentiable ℝ
          (longTimeMap
            (wholeLineForwardOrbitExtension (waveExponent c) raw_w)
            (seq n))
  longTime_image_deriv_bound :
    ∀ seq : ℕ → ℝ → ℝ,
      (∀ n, seq n ∈ WaveTrap (waveExponent c) κt D) →
        ∀ n x,
          |deriv
            (longTimeMap
              (wholeLineForwardOrbitExtension (waveExponent c) raw_w)
              (seq n)) x| ≤ Λ
  longTime_time_antitone :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      ∀ x, Antitone fun t : ℝ =>
        wholeLineForwardOrbitExtension (waveExponent c) raw_w U t x
  longTime_derivative_convergence :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      WholeLineParabolicDerivativeConvergence
        (wholeLineForwardOrbitExtension (waveExponent c) raw_w U)
        (wt U) (wx U) (wxx U)
        (wholeLineLongTimeLimit
          (wholeLineForwardOrbitExtension (waveExponent c) raw_w U))
  longTime_evolution_eq :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      ∀ t x,
        wt U t x =
          wxx U t x + c * wx U t x +
            auxiliaryFrozenNonlinearity p
              (wholeLineForwardOrbitExtension (waveExponent c) raw_w U t)
              (wx U t)
              (frozenSignal p.γ U)
              (fun y => deriv (frozenSignal p.γ U) y) x
  fixedPoint_profile_contDiff2 :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) raw_w) U = U →
        ContDiff ℝ 2 U
  fixedPoint_signal_contDiff2 :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) raw_w) U = U →
        ContDiff ℝ 2 (frozenSignal p.γ U)
  fixedPoint_flat_left :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) raw_w) U = U →
        ShenWork.Paper1.FrozenStationaryFlatAtLeft p U
  translate_limit_identification :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) raw_w) U = U →
        ∀ L : ℝ,
          ShenWork.Paper1.WholeLineLeftTail.TranslateCompactnessStationaryLimit
            p c U L →
          ShenWork.Paper1.WholeLineLeftTail.Paper3T10PositiveLimitIdentification
            p3 L

namespace WholeLineTravelingWaveCoreData

def longTimeStationarity
    {p : CMParams} {c κt D Λ : ℝ}
    {raw_w wt wx wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineTravelingWaveCoreData p c κt D Λ raw_w wt wx wxx p3) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      WholeLineLongTimeStationarityData p c
        (wholeLineForwardOrbitExtension (waveExponent c) raw_w U)
        (wt U) (wx U) (wxx U)
        (wholeLineLongTimeLimit
          (wholeLineForwardOrbitExtension (waveExponent c) raw_w U))
        (frozenSignal p.γ U)
        (fun x => deriv (frozenSignal p.γ U) x) := by
  intro U hU
  exact
    longTime_stationarity_of_convergence
      (p := p) (c := c) (κ := waveExponent c) (κt := κt) (D := D)
      (w := wholeLineForwardOrbitExtension (waveExponent c) raw_w U)
      (wt := wt U) (wx := wx U) (wxx := wxx U)
      (V := frozenSignal p.γ U)
      (Vx := fun x => deriv (frozenSignal p.γ U) x)
      (H.longTime_time_antitone U hU)
      ((wholeLine_orbit_fields H.orbit_properties).1 U hU)
      (H.longTime_derivative_convergence U hU)
      (H.longTime_evolution_eq U hU)

theorem fixedPoint_differentiable
    {p : CMParams} {c κt D Λ : ℝ}
    {raw_w wt wx wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineTravelingWaveCoreData p c κt D Λ raw_w wt wx wxx p3)
    {U : ℝ → ℝ}
    (hU : U ∈ WaveTrap (waveExponent c) κt D)
    (hfixed :
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) raw_w) U = U) :
    Differentiable ℝ U := by
  let seq : ℕ → ℝ → ℝ := fun _ => U
  have hseq : ∀ n, seq n ∈ WaveTrap (waveExponent c) κt D := fun _ => hU
  have hdiff := H.longTime_image_differentiable seq hseq 0
  simpa [seq, hfixed] using hdiff

theorem fixedPoint_deriv_bound
    {p : CMParams} {c κt D Λ : ℝ}
    {raw_w wt wx wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineTravelingWaveCoreData p c κt D Λ raw_w wt wx wxx p3)
    {U : ℝ → ℝ}
    (hU : U ∈ WaveTrap (waveExponent c) κt D)
    (hfixed :
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) raw_w) U = U) :
    ∀ x, |deriv U x| ≤ Λ := by
  intro x
  let seq : ℕ → ℝ → ℝ := fun _ => U
  have hseq : ∀ n, seq n ∈ WaveTrap (waveExponent c) κt D := fun _ => hU
  have hbound := H.longTime_image_deriv_bound seq hseq 0 x
  simpa [seq, hfixed] using hbound

theorem fixedPoint_frozenWaveOperator_zero
    {p : CMParams} {c κt D Λ : ℝ}
    {raw_w wt wx wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineTravelingWaveCoreData p c κt D Λ raw_w wt wx wxx p3)
    {U : ℝ → ℝ}
    (hU : U ∈ WaveTrap (waveExponent c) κt D)
    (hfixed :
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) raw_w) U = U) :
    ∀ x, ShenWork.Paper1.frozenWaveOperator p c U U x = 0 := by
  let wU : ℝ → ℝ → ℝ :=
    wholeLineForwardOrbitExtension (waveExponent c) raw_w U
  have hlim_eq : wholeLineLongTimeLimit wU = U := by
    simpa [wU, longTimeMap] using hfixed
  have hstat :=
    wholeLine_longTime_stationary
      (p := p) (c := c) (u := U)
      (w := wU) (wt := wt U) (wx := wx U) (wxx := wxx U)
      (H.longTimeStationarity U hU)
  have haux : wholeLineAuxStationaryEquation p c U := by
    intro x
    rw [wholeLine_aux_operator_eq_residual p c U x]
    simpa [hlim_eq] using hstat x
  have hU_contDiff : ContDiff ℝ 2 U :=
    H.fixedPoint_profile_contDiff2 U hU hfixed
  have hV_contDiff : ContDiff ℝ 2 (frozenSignal p.γ U) :=
    H.fixedPoint_signal_contDiff2 U hU hfixed
  have hU_bdd : IsCUnifBdd U :=
    ⟨hU_contDiff.continuous, waveTrap_bounded hU⟩
  have hU_nonneg : ∀ x, 0 ≤ U x :=
    fun x => waveTrap_mem_nonneg hU x
  have hU_diff : ∀ x, DifferentiableAt ℝ U x := by
    intro x
    exact hU_contDiff.differentiable two_ne_zero x
  have hV_deriv_diff :
      ∀ x, DifferentiableAt ℝ (deriv (frozenSignal p.γ U)) x :=
    differentiableAt_deriv_of_contDiff_two_reduced hV_contDiff
  have hdiv : wholeLineDivergenceStationaryEquation p c U :=
    (wholeLine_diagonal_stationary p hU_bdd hU_nonneg hU_diff hV_deriv_diff).mp haux
  intro x
  rw [← wholeLineDivergenceStationaryOperator_eq_frozenWaveOperator p c U x]
  exact hdiv x

def translate_compactness
    {p : CMParams} {c κt D Λ : ℝ}
    {raw_w wt wx wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineTravelingWaveCoreData p c κt D Λ raw_w wt wx wxx p3) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) raw_w) U = U →
        ∀ L : ℝ, Tendsto U atBot (𝓝 L) → L < 1 →
          ShenWork.Paper1.WholeLineLeftTail.TranslateCompactnessStationaryLimit
            p c U L := by
  intro U hU hfixed L hlim _hL_lt_one
  have hκ : 0 < waveExponent c :=
    waveExponent_pos ((H.orbit_properties.trapping U hU).speed_ge)
  have hcont : Continuous U :=
    (H.fixedPoint_profile_contDiff2 U hU hfixed).continuous
  have hdiff : Differentiable ℝ U :=
    H.fixedPoint_differentiable hU hfixed
  have hderiv : ∀ x, |deriv U x| ≤ Λ :=
    H.fixedPoint_deriv_bound hU hfixed
  have hequi :
      ∀ K : Set ℝ, IsCompact K →
        EquicontinuousOn
          (fun (n : ℕ) (x : ℝ) => U (x + (-(n : ℝ)))) K :=
    translate_equicontinuousOn_of_uniform_deriv_bound
      H.longTime_deriv_bound_nonneg hdiff hderiv
  exact
    translate_compactness_of_equicontinuity
      (p := p) (c := c) (κ := waveExponent c) (κt := κt) (D := D)
      (U := U) (L := L)
      hκ H.kappa_lt_kappat H.D_ge_one hU hcont hequi hlim
      (H.fixedPoint_frozenWaveOperator_zero hU hfixed)
      (H.fixedPoint_flat_left U hU hfixed)

theorem mild_decomp
    {p : CMParams} {c κt D Λ : ℝ}
    {raw_w wt wx wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineTravelingWaveCoreData p c κt D Λ raw_w wt wx wxx p3) :
    ∀ t U x,
      wholeLineForwardOrbitExtension (waveExponent c) raw_w U t x =
        residualAuxSemigroupTerm c (waveExponent c) t x +
          (-p.χ) * residualAuxChemDuhamel t U x +
            residualAuxReactionDuhamel p c (waveExponent c) κt D raw_w wx t U x := by
  intro t U x
  by_cases hU : U ∈ WaveTrap (waveExponent c) κt D
  · by_cases ht : 0 ≤ t
    · have hT : 0 < t + 1 := by linarith
      have ht_mem : t ∈ Set.Icc (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
      have hsol := H.auxiliary_solution U hU (t + 1) hT
      have hmild :=
        hsol.2.1 t ht_mem x
      rw [wholeLineForwardOrbitExtension, if_pos ht, hmild]
      simp [residualAuxSemigroupTerm, residualAuxChemDuhamel,
        residualAuxReactionDuhamel, residualAuxDuhamelOnTrap, hU, ht,
        auxiliaryMildMap]
    · simp [wholeLineForwardOrbitExtension, residualAuxSemigroupTerm,
        residualAuxChemDuhamel, residualAuxReactionDuhamel,
        residualAuxDuhamelOnTrap, hU, ht]
  · simp [residualAuxSemigroupTerm, residualAuxChemDuhamel,
      residualAuxReactionDuhamel, hU]

end WholeLineTravelingWaveCoreData

/--
Constructor from the reduced core to the previous residual record.
-/
def wholeLineTravelingWaveResidualData_of_core
    {p : CMParams} {c κt D Λ : ℝ}
    {raw_w wt wx wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {p3 : CM2Params}
    (H : WholeLineTravelingWaveCoreData p c κt D Λ raw_w wt wx wxx p3) :
    WholeLineTravelingWaveResidualData p c κt D Λ raw_w wt wx wxx p3 where
  kappa_lt_kappat := H.kappa_lt_kappat
  D_ge_one := H.D_ge_one
  paper3_chi_nonpos := H.paper3_chi_nonpos
  orbit_properties := H.orbit_properties
  longTime_deriv_bound_nonneg := H.longTime_deriv_bound_nonneg
  longTime_image_differentiable := H.longTime_image_differentiable
  longTime_image_deriv_bound := H.longTime_image_deriv_bound
  semigroupTerm := residualAuxSemigroupTerm c (waveExponent c)
  chemDuhamel := residualAuxChemDuhamel
  reactionDuhamel :=
    residualAuxReactionDuhamel p c (waveExponent c) κt D raw_w wx
  mild_decomp := H.mild_decomp
  chemDuhamel_continuity := fun _ =>
    localUniformContinuousOn_zero
      (fun U : ℝ → ℝ => U ∈ WaveTrap (waveExponent c) κt D)
  reactionDuhamel_continuity := fun t =>
    residualAuxReactionDuhamel_continuity
      (H.auxiliaryDuhamel_continuity t)
  finite_time_slice_continuity := H.finite_time_slice_continuity
  longTime_uniform_tail := H.longTime_uniform_tail
  longTime_stationarity := H.longTimeStationarity
  fixedPoint_profile_contDiff2 := H.fixedPoint_profile_contDiff2
  fixedPoint_signal_contDiff2 := H.fixedPoint_signal_contDiff2
  translate_compactness := H.translate_compactness
  translate_limit_identification := H.translate_limit_identification

#print axioms frozenSignal_eq_frozenElliptic
#print axioms wholeLineDivergenceStationaryOperator_eq_frozenWaveOperator
#print axioms translate_equicontinuousOn_of_uniform_deriv_bound
#print axioms localUniformContinuousOn_zero
#print axioms WholeLineTravelingWaveCoreData
#print axioms WholeLineTravelingWaveCoreData.longTimeStationarity
#print axioms WholeLineTravelingWaveCoreData.fixedPoint_frozenWaveOperator_zero
#print axioms WholeLineTravelingWaveCoreData.translate_compactness
#print axioms WholeLineTravelingWaveCoreData.mild_decomp
#print axioms wholeLineTravelingWaveResidualData_of_core

end ShenWork.PaperOne
