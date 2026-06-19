import ShenWork.Paper1.Statements
import ShenWork.Paper3.CriticalSensitivityExactValue

/-!
  Paper 1, avenue-c BRICK 16.

  The analytic translate-compactness step is carried as explicit data.  This
  file only wires the monotone left limit, the contradiction step, and the
  Paper3 positive-equilibrium linear-stability input (T10).
-/

open Filter Topology

namespace ShenWork.Paper1

noncomputable section

namespace WholeLineLeftTail

/-- A bounded antitone whole-line profile has a finite left limit. -/
theorem antitone_isBddFun_tendsto_atBot
    {U : ℝ → ℝ} (hmono : Antitone U) (hbdd : IsBddFun U) :
    ∃ L : ℝ, Tendsto U atBot (𝓝 L) := by
  rcases tendsto_atBot_of_antitone (f := U) hmono with htop | hfin
  · exfalso
    rcases hbdd with ⟨B, hB⟩
    have hupper : ∀ x, U x ≤ B := by
      intro x
      exact le_trans (le_abs_self _) (hB x)
    have hev : ∀ᶠ x in atBot, B + 1 < U x :=
      htop (Ioi_mem_atTop (B + 1))
    have hboth : ∀ᶠ x in atBot, B + 1 < U x ∧ U x ≤ B :=
      hev.and (Eventually.of_forall hupper)
    rcases hboth.exists with ⟨_x, hxlt, hxle⟩
    linarith
  · exact hfin

/-- The monotone trap gives the left limit in `[0,M]`. -/
theorem monotoneTrap_left_limit_exists
    {κ M : ℝ} {U : ℝ → ℝ}
    (hU : InMonotoneWaveTrapSet κ M U) :
    ∃ L : ℝ, Tendsto U atBot (𝓝 L) ∧ 0 ≤ L ∧ L ≤ M := by
  rcases antitone_isBddFun_tendsto_atBot hU.antitone hU.trap.cunif_bdd.2 with
    ⟨L, hL⟩
  have hnonneg : 0 ≤ L := by
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hL
      (Eventually.of_forall hU.nonneg)
  have hleM : L ≤ M := by
    exact le_of_tendsto_of_tendsto hL tendsto_const_nhds
      (Eventually.of_forall hU.le_M)
  exact ⟨L, hL, hnonneg, hleM⟩

/-- Paper3 T10, in the positive-equilibrium linearly-stable form consumed by
the left-tail contradiction. -/
def Paper3T10PositiveEquilibriumStable
    (p3 : CM2Params) : Prop :=
  ∀ (ha : 0 < p3.a) (hb : 0 < p3.b),
    ShenWork.Paper3.LinearlyStable ShenWork.Paper3.unitIntervalNeumannSpectrum p3
      (ShenWork.Paper3.positiveEquilibrium p3 ⟨ha, hb⟩).1
      (ShenWork.Paper3.positiveEquilibrium p3 ⟨ha, hb⟩).2

/-- T10 wired from Paper3: the nonpositive-sensitivity positive equilibrium is
linearly stable on the unit interval. -/
theorem paper3_T10_positiveEquilibriumStable_of_chi_nonpos
    (p3 : CM2Params) (hχ : p3.χ₀ ≤ 0) :
    Paper3T10PositiveEquilibriumStable p3 := by
  intro ha hb
  exact ShenWork.Paper3.unitInterval_positiveEquilibrium_linearlyStable_of_chi_nonpos
    p3 hχ ha hb

/-- The explicit first-mode T10 dichotomy at the positive equilibrium, wired
from Paper3's exact-threshold theorem. -/
def Paper3T10PositiveEquilibriumDichotomy
    (p3 : CM2Params) : Prop :=
  ∀ (ha : 0 < p3.a) (hb : 0 < p3.b),
    (p3.χ₀ <
        ShenWork.Paper3.sigmaCriticalChiPaperFormula p3
          (ShenWork.Paper3.positiveEquilibrium p3 ⟨ha, hb⟩).1
          (ShenWork.Paper3.positiveEquilibrium p3 ⟨ha, hb⟩).2
          (ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue 1) →
        ShenWork.Paper3.LinearlyStable
          ShenWork.Paper3.unitIntervalNeumannSpectrum p3
          (ShenWork.Paper3.positiveEquilibrium p3 ⟨ha, hb⟩).1
          (ShenWork.Paper3.positiveEquilibrium p3 ⟨ha, hb⟩).2) ∧
      (ShenWork.Paper3.sigmaCriticalChiPaperFormula p3
          (ShenWork.Paper3.positiveEquilibrium p3 ⟨ha, hb⟩).1
          (ShenWork.Paper3.positiveEquilibrium p3 ⟨ha, hb⟩).2
          (ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue 1) <
            p3.χ₀ →
        ShenWork.Paper3.LinearlyUnstable
          ShenWork.Paper3.unitIntervalNeumannSpectrum p3
          (ShenWork.Paper3.positiveEquilibrium p3 ⟨ha, hb⟩).1
          (ShenWork.Paper3.positiveEquilibrium p3 ⟨ha, hb⟩).2)

/-- T10 wired from Paper3's exact first-mode positive-equilibrium dichotomy. -/
theorem paper3_T10_positiveEquilibriumDichotomy_unitInterval
    (p3 : CM2Params)
    (hregime : p3.a * p3.α * p3.μ ≤ (Real.pi ^ 2) ^ 2) :
    Paper3T10PositiveEquilibriumDichotomy p3 := by
  intro ha hb
  exact
    ShenWork.Paper3.positiveEquilibrium_linearStability_dichotomy_of_firstMode_dominant
      ShenWork.Paper3.unitIntervalNeumannSpectrum p3
      ShenWork.Paper3.unitIntervalNeumannSpectrum_hasNeumannSpectrum
      ha hb
      (by simp [ShenWork.Paper3.unitIntervalNeumannSpectrum])
      (by simpa [ShenWork.Paper3.unitIntervalNeumannSpectrum] using hregime)

/-- The exact-threshold T10 stable branch, packaged in the form consumed by
`wholeLine_travelingWave_leftLimit`. -/
theorem paper3_T10_positiveEquilibriumStable_of_dichotomy
    {p3 : CM2Params}
    (hT10 : Paper3T10PositiveEquilibriumDichotomy p3)
    (hχ :
      ∀ (ha : 0 < p3.a) (hb : 0 < p3.b),
        p3.χ₀ <
          ShenWork.Paper3.sigmaCriticalChiPaperFormula p3
            (ShenWork.Paper3.positiveEquilibrium p3 ⟨ha, hb⟩).1
            (ShenWork.Paper3.positiveEquilibrium p3 ⟨ha, hb⟩).2
            (ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue 1)) :
    Paper3T10PositiveEquilibriumStable p3 := by
  intro ha hb
  exact (hT10 ha hb).1 (hχ ha hb)

/-- Carried analytic output of the translate-compactness argument.  The limit
profile is positive, stationary, and constant with value `L`; the local-uniform
compactness itself is represented here by the translated pointwise convergence
field plus the named stationary limit field. -/
structure TranslateCompactnessStationaryLimit
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) (L : ℝ) where
  Ulim : ℝ → ℝ
  shifts : ℕ → ℝ
  shifts_atBot : Tendsto shifts atTop atBot
  translated_pointwise :
    ∀ x : ℝ, Tendsto (fun n : ℕ => U (x + shifts n)) atTop (𝓝 (Ulim x))
  constant_profile : ∀ x : ℝ, Ulim x = L
  positive_profile : ∀ x : ℝ, 0 < Ulim x
  stationary_profile : ∀ x : ℝ, frozenWaveOperator p c Ulim Ulim x = 0

/-- The carried T10 consequence matching the compactness limit to Paper3's
positive equilibrium.  The premise is deliberately the Paper3 linear-stability
conclusion, so the main theorem must actually apply the wired T10 theorem. -/
structure Paper3T10PositiveLimitIdentification
    (p3 : CM2Params) (L : ℝ) : Prop where
  ha : 0 < p3.a
  hb : 0 < p3.b
  hab_eq : p3.a = p3.b
  stable_identifies :
    ShenWork.Paper3.LinearlyStable ShenWork.Paper3.unitIntervalNeumannSpectrum p3
      (ShenWork.Paper3.positiveEquilibrium p3 ⟨ha, hb⟩).1
      (ShenWork.Paper3.positiveEquilibrium p3 ⟨ha, hb⟩).2 →
    L = (ShenWork.Paper3.positiveEquilibrium p3 ⟨ha, hb⟩).1

/-- T10 application to a carried positive stationary constant translate-limit:
the limit value must be `1`. -/
theorem left_limit_eq_one_of_translate_limit_and_T10
    {p3 : CM2Params} {L : ℝ}
    (hT10 : Paper3T10PositiveEquilibriumStable p3)
    (hId : Paper3T10PositiveLimitIdentification p3 L) :
    L = 1 := by
  have hstable := hT10 hId.ha hId.hb
  have hL_eq := hId.stable_identifies hstable
  have hpeq_one :
      (ShenWork.Paper3.positiveEquilibrium p3 ⟨hId.ha, hId.hb⟩).1 = 1 :=
    ShenWork.Paper3.positiveEquilibrium_fst_eq_one p3
      ⟨hId.ha, hId.hb⟩ hId.hab_eq
  exact hL_eq.trans hpeq_one

/-- Whole-line left tail: antitone trap gives a left limit in `[0,1]`; if that
limit were `< 1`, the carried translate-compactness stationary limit and Paper3
T10 identify it with the positive equilibrium `1`, a contradiction. -/
theorem wholeLine_travelingWave_leftLimit
    {p : CMParams} {c κ : ℝ} {U : ℝ → ℝ}
    {p3 : CM2Params}
    (hU : InMonotoneWaveTrapSet κ 1 U)
    (htranslate :
      ∀ L : ℝ, Tendsto U atBot (𝓝 L) → L < 1 →
        TranslateCompactnessStationaryLimit p c U L)
    (hT10 : Paper3T10PositiveEquilibriumStable p3)
    (hlimit_to_T10 :
      ∀ L : ℝ, TranslateCompactnessStationaryLimit p c U L →
        Paper3T10PositiveLimitIdentification p3 L) :
    Tendsto U atBot (𝓝 1) := by
  rcases monotoneTrap_left_limit_exists hU with ⟨L, hL, _hL_nonneg, hL_le_one⟩
  have hL_eq_one : L = 1 := by
    by_cases hlt : L < 1
    · have hcompact : TranslateCompactnessStationaryLimit p c U L :=
        htranslate L hL hlt
      have hId : Paper3T10PositiveLimitIdentification p3 L :=
        hlimit_to_T10 L hcompact
      have hEq := left_limit_eq_one_of_translate_limit_and_T10 hT10 hId
      exact hEq
    · exact le_antisymm hL_le_one (le_of_not_gt hlt)
  simpa [hL_eq_one] using hL

end WholeLineLeftTail

end

end ShenWork.Paper1

#print axioms ShenWork.Paper1.WholeLineLeftTail.paper3_T10_positiveEquilibriumStable_of_chi_nonpos
#print axioms ShenWork.Paper1.WholeLineLeftTail.paper3_T10_positiveEquilibriumDichotomy_unitInterval
#print axioms ShenWork.Paper1.WholeLineLeftTail.left_limit_eq_one_of_translate_limit_and_T10
#print axioms ShenWork.Paper1.WholeLineLeftTail.wholeLine_travelingWave_leftLimit
