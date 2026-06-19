import ShenWork.PaperOne.WholeLineWaveExistenceReduced

/-!
  Paper 1 whole-line left-tail discharge.

  The monotone-bounded part is closed directly from `WaveTrap`.  The actual
  `FrozenStationaryFlatAtLeft` field contains derivative tails, so the
  remaining parabolic tail bridge is named explicitly instead of being hidden.
-/

open Filter Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-- A PaperOne `WaveTrap` profile has a finite left limit in `[0,1]`.
This is the part that follows only from antitonicity and boundedness. -/
theorem waveTrap_left_limit_exists
    {κ κt D : ℝ} {U : ℝ → ℝ}
    (hU : U ∈ WaveTrap κ κt D) :
    ∃ L : ℝ, Tendsto U atBot (𝓝 L) ∧ 0 ≤ L ∧ L ≤ 1 := by
  rcases
      ShenWork.Paper1.WholeLineLeftTail.antitone_isBddFun_tendsto_atBot
        hU.2 (waveTrap_bounded hU) with
    ⟨L, hL⟩
  have hnonneg : 0 ≤ L := by
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hL
      (Eventually.of_forall (fun x => waveTrap_mem_nonneg hU x))
  have hle_one : L ≤ 1 := by
    exact le_of_tendsto_of_tendsto hL tendsto_const_nhds
      (Eventually.of_forall (fun x => waveTrap_mem_le_one hU x))
  exact ⟨L, hL, hnonneg, hle_one⟩

/-- Named parabolic tail bridge needed to turn the monotone left limit into the
`FrozenStationaryFlatAtLeft` derivative-tail statement required by the residual
record.  This is stronger than monotone boundedness and is not derived here. -/
def FixedPointFlatLeftParabolicTailFromMonotoneLimit
    (p : CMParams) (c κt D : ℝ)
    (Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D) : Prop :=
  ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
    longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) U = U →
      ∀ L : ℝ, Tendsto U atBot (𝓝 L) → 0 ≤ L → L ≤ 1 →
        ShenWork.Paper1.FrozenStationaryFlatAtLeft p U

/-- The `fixedPoint_flat_left` residual field, reduced to the closed
monotone-left-limit fact plus the named parabolic derivative-tail bridge. -/
theorem fixedPoint_flat_left_of_waveTrap
    {p : CMParams} {c κt D : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    (hflat :
      FixedPointFlatLeftParabolicTailFromMonotoneLimit p c κt D Haux) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) U = U →
        ShenWork.Paper1.FrozenStationaryFlatAtLeft p U := by
  intro U hU hfixed
  rcases waveTrap_left_limit_exists hU with ⟨L, hL, hL_nonneg, hL_le_one⟩
  exact hflat U hU hfixed L hL hL_nonneg hL_le_one

/-- Named compactness-to-Paper3 identification bridge for a positive constant
translate limit.  T10 is then applied by the banked left-tail theorem. -/
structure TranslateLimitIdentificationParabolicData
    (p : CMParams) (c : ℝ) (p3 : CM2Params) : Prop where
  ha : 0 < p3.a
  hb : 0 < p3.b
  hab_eq : p3.a = p3.b
  stable_identifies :
    ∀ {U : ℝ → ℝ} {L : ℝ},
      ShenWork.Paper1.WholeLineLeftTail.TranslateCompactnessStationaryLimit
        p c U L →
        ShenWork.Paper3.LinearlyStable
          ShenWork.Paper3.unitIntervalNeumannSpectrum p3
          (ShenWork.Paper3.positiveEquilibrium p3 ⟨ha, hb⟩).1
          (ShenWork.Paper3.positiveEquilibrium p3 ⟨ha, hb⟩).2 →
          L = (ShenWork.Paper3.positiveEquilibrium p3 ⟨ha, hb⟩).1

/-- Package the named compactness-to-Paper3 bridge in the exact structure
consumed by `WholeLineLeftTail.wholeLine_travelingWave_leftLimit`. -/
theorem paper3_limit_identification_of_translate_compactness
    {p : CMParams} {c : ℝ} {p3 : CM2Params}
    (Hid : TranslateLimitIdentificationParabolicData p c p3)
    {U : ℝ → ℝ} {L : ℝ}
    (hcompact :
      ShenWork.Paper1.WholeLineLeftTail.TranslateCompactnessStationaryLimit
        p c U L) :
    ShenWork.Paper1.WholeLineLeftTail.Paper3T10PositiveLimitIdentification
      p3 L where
  ha := Hid.ha
  hb := Hid.hb
  hab_eq := Hid.hab_eq
  stable_identifies := by
    intro hstable
    exact Hid.stable_identifies hcompact hstable

/-- The `translate_limit_identification` residual field from the named
compactness-to-Paper3 bridge. -/
theorem translate_limit_identification_of_T10
    {p : CMParams} {c κt D : ℝ}
    {Haux : WholeLineAuxiliaryGlobalFamilyData p c κt D}
    {p3 : CM2Params}
    (Hid : TranslateLimitIdentificationParabolicData p c p3) :
    ∀ U, U ∈ WaveTrap (waveExponent c) κt D →
      longTimeMap (wholeLineForwardOrbitExtension (waveExponent c) Haux.raw_w) U = U →
        ∀ L : ℝ,
          ShenWork.Paper1.WholeLineLeftTail.TranslateCompactnessStationaryLimit
            p c U L →
          ShenWork.Paper1.WholeLineLeftTail.Paper3T10PositiveLimitIdentification
            p3 L := by
  intro U _hU _hfixed L hcompact
  exact paper3_limit_identification_of_translate_compactness Hid hcompact

/-- Consuming the banked Paper3 T10 wiring: a compact positive constant
translate limit identified by the bridge is equal to `1` in the nonpositive
sensitivity regime. -/
theorem translate_limit_eq_one_of_T10_chi_nonpos
    {p : CMParams} {c : ℝ} {p3 : CM2Params}
    (hχ : p3.χ₀ ≤ 0)
    (Hid : TranslateLimitIdentificationParabolicData p c p3)
    {U : ℝ → ℝ} {L : ℝ}
    (hcompact :
      ShenWork.Paper1.WholeLineLeftTail.TranslateCompactnessStationaryLimit
        p c U L) :
    L = 1 := by
  exact
    ShenWork.Paper1.WholeLineLeftTail.left_limit_eq_one_of_translate_limit_and_T10
      (ShenWork.Paper1.WholeLineLeftTail.paper3_T10_positiveEquilibriumStable_of_chi_nonpos
        p3 hχ)
      (paper3_limit_identification_of_translate_compactness Hid hcompact)

#print axioms waveTrap_left_limit_exists
#print axioms FixedPointFlatLeftParabolicTailFromMonotoneLimit
#print axioms fixedPoint_flat_left_of_waveTrap
#print axioms TranslateLimitIdentificationParabolicData
#print axioms paper3_limit_identification_of_translate_compactness
#print axioms translate_limit_identification_of_T10
#print axioms translate_limit_eq_one_of_T10_chi_nonpos

end ShenWork.PaperOne

