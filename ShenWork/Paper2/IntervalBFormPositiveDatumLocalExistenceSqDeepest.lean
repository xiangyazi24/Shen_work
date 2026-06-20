import ShenWork.Paper2.IntervalBFormPositiveDatumLocalExistenceSqBankedConcrete
import ShenWork.Paper2.IntervalBFormCron2MildToWeak

open Set Filter Topology MeasureTheory

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit
   conjugateMildSolutionData_of_data)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1)
open ShenWork.PDE
  (intervalNeumannResolverSourceCoeff)
open ShenWork.Paper2
open ShenWork.Paper2.BFormPositiveDatumNegPart
open scoped Topology BigOperators

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumLocalSq

/-- The deepest currently honest per-datum B-form inputs.

The B_N step is represented by `TruncatedMildToWeakRegularData`, whose
constructor uses the proved regular theorem `bN_duality_regular` at the actual
tested lags.  The energy field is the existing negative-part energy core: it is
the repository's current package for the cancellation/Gronwall argument and its
Sobolev plumbing.
-/
structure PositiveDatumBFormSqDeepestHypotheses
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  bank :
    ShenWork.Paper2.BFormDirectClassical.BFormBankedInputs p DB
  hTimeNhd :
    HasTimeNeighborhoodSpectralAgreement DB.T
      (conjugatePicardLimit p u₀ DB.T)
  hResolverCoeffTimeC1 :
    ∀ t₀, 0 < t₀ → t₀ < DB.T →
      ∃ (aC : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC1 aC) (W : Set ℝ),
        W ∈ 𝓝 t₀ ∧
        (∀ s ∈ W, ∀ k,
          aC s k =
            (intervalNeumannResolverSourceCoeff p
              ((conjugatePicardLimit p u₀ DB.T) s) k).re)
  DT : TruncatedConjugateMildExistenceData p u₀
  Hbridge : TruncatedConjugateLimitBridge p DB DT
  Test : (ℝ → ℝ) → Prop
  HmildWeakRegular : TruncatedMildToWeakRegularData p DB Test
  Henergy : NegativePartEnergyCoreData p DB
  A : ℝ
  Dbar : ℝ
  M : ℝ
  hM_nonneg : 0 ≤ M
  hM : A ^ 2 / 2 + Dbar ≤ M
  drift : ℝ → ℝ → ℝ
  react : ℝ → ℝ → ℝ
  hstrip :
    ∀ τ, 0 < τ → τ < DB.T →
      NeumannLinearDriftCoefficientsRegular (DB.T - τ)
        (restartTimeShift τ drift) (restartTimeShift τ react) ∧
      IsClassicalNeumannLinearDriftSuperSolution (DB.T - τ)
        (restartTimeShift τ drift) (restartTimeShift τ react)
        (restartTimeShift τ (bformConjugatePicardLift p DB)) ∧
      (∀ s x, 0 < s → s < DB.T - τ →
        x ∈ Set.Ioo (0 : ℝ) 1 → |drift (τ + s) x| ≤ A) ∧
      (∀ s x, 0 < s → s < DB.T - τ →
        x ∈ Set.Ioo (0 : ℝ) 1 → -react (τ + s) x ≤ Dbar)

def PositiveDatumBFormSqDeepestHypotheses.hResolverData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (H : PositiveDatumBFormSqDeepestHypotheses p DB) :
    ShenWork.IntervalResolverDirectTimeRegularity.HasResolverDirectSpectralData
      DB.T
      (mildChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T)) p :=
  ShenWork.Paper2.RegularityFrontierAssembly.hasResolverDirectSpectralData_of_clamped_perT0
    (p := p) (T := DB.T) (u := conjugatePicardLimit p u₀ DB.T)
    H.hResolverCoeffTimeC1

def PositiveDatumBFormSqDeepestHypotheses.directFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (H : PositiveDatumBFormSqDeepestHypotheses p DB) :
    ShenWork.Paper2.BFormDirectClassical.BFormDirectFrontier p DB where
  bank := H.bank
  hTimeNhd := H.hTimeNhd
  hResolverData := H.hResolverData
  hVpos := bform_mildChemicalConcentration_pos_of_conjugate_data p DB

/-- The B-form spectral PDE field is discharged from the PID-unconditional
spectral provider through the existing banked inputs. -/
def PositiveDatumBFormSqDeepestHypotheses.Hpde
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (H : PositiveDatumBFormSqDeepestHypotheses p DB) :
    ShenWork.IntervalBFormSpectral.HasBFormSpectralPdeAgreement p DB.T
      (conjugatePicardLimit p u₀ DB.T) :=
  hpde_of_BFormBankedInputs H.bank

/-- The truncated Picard construction, plus the explicit bridge, gives the
truncated mild fixed point for the named conjugate Picard limit. -/
def PositiveDatumBFormSqDeepestHypotheses.truncatedMild
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (H : PositiveDatumBFormSqDeepestHypotheses p DB) :
    TruncatedConjugateMildSolution p DB.T u₀
      (conjugatePicardLimit p u₀ DB.T) :=
  truncatedConjugateMildSolution_conjugatePicardLimit_of_data
    DB H.DT H.Hbridge

/-- Mild-to-weak on the carried test class.  The lagwise B_N identities inside
this theorem are exactly the proved `bN_duality_regular` specialization. -/
def PositiveDatumBFormSqDeepestHypotheses.weakOn
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (H : PositiveDatumBFormSqDeepestHypotheses p DB) :
    TruncatedWeakLocalPDEOn p DB.T
      (conjugatePicardLimit p u₀ DB.T) H.Test :=
  truncatedWeakLocalPDEOn_of_regularData
    H.HmildWeakRegular H.truncatedMild

def PositiveDatumBFormSqDeepestHypotheses.strictPos
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (H : PositiveDatumBFormSqDeepestHypotheses p DB) :
    ∀ t x, 0 < t → t < DB.T →
      0 < conjugatePicardLimit p u₀ DB.T t x :=
  bform_strictPos_closed
    (p := p) (u₀ := u₀) (DB := DB)
    (A := H.A) (D := H.Dbar) (M := H.M)
    (drift := H.drift) (react := H.react)
    H.bank.huPaper H.bank.Hinf H.bank.hsmall
    H.hM_nonneg H.hM H.hstrip

theorem PositiveDatumBFormSqDeepestHypotheses.localClassicalSolution
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (H : PositiveDatumBFormSqDeepestHypotheses p DB) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u₀ u := by
  let F := H.directFrontier
  let hsol :=
    ShenWork.Paper2.BFormDirectClassical.intervalConjugatePicardLimit_isClassicalSolution_direct F
  refine ⟨DB.T, DB.hT,
    conjugatePicardLimit p u₀ DB.T,
    mildChemicalConcentration p (conjugatePicardLimit p u₀ DB.T), ?_⟩
  refine ⟨?_, ?_⟩
  · refine IsPaper2ClassicalSolution.of_components DB.hT
      (ShenWork.Paper2.BFormDirectClassical.intervalConjugatePicardLimit_classicalRegularity_direct F)
      H.strictPos ?_
      (ShenWork.IntervalConjugatePicard.intervalConjugateMildSolution_pde_u_from_picard_data_and_spectral
        DB H.Hpde)
      ?_ ?_
    · intro t x ht htT
      exact ShenWork.IntervalMildToClassical.mildChemical_nonneg
        (T := DB.T) p
        (u := conjugatePicardLimit p u₀ DB.T)
        (conjugateMildSolutionData_of_data DB).hnonneg
        (conjugateMildSolutionData_of_data DB).hcont
        ht (le_of_lt htT) x
    · intro t x ht htT hx
      exact hsol.pde_v ht htT hx
    · intro t x ht htT hx
      exact hsol.neumann ht htT hx
  · exact
      ShenWork.Paper2.BFormInitialTrace.conjugatePicardLimit_initialTrace_of_conjugate_data
        p (PaperPositiveInitialDatum.admissible H.bank.huPaper).2 DB

def PositiveDatumBFormLocalHypSqDeepest (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomainPoint → ℝ,
    PaperPositiveInitialDatum intervalDomain u₀ →
      ∃ DB : ConjugateMildExistenceData p u₀,
        Nonempty (PositiveDatumBFormSqDeepestHypotheses p DB)

theorem positiveDatum_localExistence_of_BFormSq_deepest
    {p : CM2Params}
    (hdeepest : PositiveDatumBFormLocalHypSqDeepest p) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  rcases hdeepest u₀ hu₀ with ⟨DB, ⟨H⟩⟩
  exact H.localClassicalSolution

/-- The requested deep banked local-existence wrapper.  This is the honest
version of `hbanked_concrete_of_deep_hypotheses`: it uses the regular lagwise
B_N data exposed by `IntervalBFormCron2MildToWeak`. -/
theorem hbanked_concrete_of_deepest
    {p : CM2Params}
    (hdeepest : PositiveDatumBFormLocalHypSqDeepest p) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u :=
  positiveDatum_localExistence_of_BFormSq_deepest hdeepest

theorem reachableArbitrarilyLong_of_BFormSq_deepest_uniform
    {p : CM2Params}
    (hdeepest : PositiveDatumBFormLocalHypSqDeepest p)
    (hUniform : IntervalDomainUniformLocalExistence p)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀paper : PaperPositiveInitialDatum intervalDomain u₀) :
    ShenWork.IntervalDomainExistence.ReachableArbitrarilyLong p u₀ := by
  intro T hT
  have hu₀ : PositiveInitialDatum intervalDomain u₀ := hu₀paper.toPositive
  obtain ⟨M₀, hM₀⟩ := hu₀.admissible.1
  let M : ℝ := max M₀ 1
  have hM_pos : 0 < M :=
    lt_of_lt_of_le zero_lt_one (le_max_right M₀ 1)
  have hM_bound : ∀ x : intervalDomainPoint, |u₀ x| ≤ M := by
    intro x
    exact (hM₀ ⟨x, rfl⟩).trans (le_max_left M₀ 1)
  obtain ⟨δ, hδ_pos, hExtend⟩ := hUniform M hM_pos
  obtain ⟨T₀, hT₀_pos, u₀sol, v₀sol, hsol₀, htrace₀⟩ :=
    positiveDatum_localExistence_of_BFormSq_deepest hdeepest u₀ hu₀paper
  suffices h :
      ∀ n : ℕ, ∃ u v : ℝ → intervalDomainPoint → ℝ,
        IsPaper2ClassicalSolution intervalDomain p (T₀ + n * δ) u v ∧
        InitialTrace intervalDomain u₀ u by
    have hn : ∃ n : ℕ, T ≤ T₀ + n * δ := by
      use ⌈(T - T₀) / δ⌉₊
      have hle : (T - T₀) / δ ≤ ↑⌈(T - T₀) / δ⌉₊ := Nat.le_ceil _
      have hmul := mul_le_mul_of_nonneg_right hle hδ_pos.le
      rw [div_mul_cancel₀ (T - T₀) (ne_of_gt hδ_pos)] at hmul
      linarith
    obtain ⟨n, hn⟩ := hn
    obtain ⟨un, vn, hsoln, htracen⟩ := h n
    exact ⟨hT, un, vn, hsoln.restrict_horizon hT (by linarith), htracen⟩
  intro n
  induction n with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, add_zero]
      exact ⟨u₀sol, v₀sol, hsol₀, htrace₀⟩
  | succ n ih =>
      obtain ⟨un, vn, hsoln, htracen⟩ := ih
      have hTn_pos : 0 < T₀ + ↑n * δ := by positivity
      obtain ⟨u', v', hsol', htrace'⟩ :=
        hExtend hu₀ hM_bound hTn_pos hsoln htracen
      refine ⟨u', v', ?_, htrace'⟩
      convert hsol' using 1
      push_cast
      ring

/-- General-χ Theorem 1.1 through the deepest B-form squared-barrier inputs.

The only global continuation input is F1, packaged here as
`IntervalDomainUniformLocalExistence`.  The per-datum local input is precisely
`PositiveDatumBFormLocalHypSqDeepest`.
-/
theorem paper2_theorem_1_1_general_chi_bformSq_of_deepest
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hdeepest : PositiveDatumBFormLocalHypSqDeepest p)
    (hF1 : IntervalDomainUniformLocalExistence p) :
    Theorem_1_1 intervalDomain p := by
  intro _hχ
  constructor
  · intro _ha _hb u₀ hu₀paper
    have hu₀ : PositiveInitialDatum intervalDomain u₀ := hu₀paper.toPositive
    have hreach :
        ShenWork.IntervalDomainExistence.ReachableArbitrarilyLong p u₀ :=
      reachableArbitrarilyLong_of_BFormSq_deepest_uniform
        hdeepest hF1 hu₀paper
    have hglue :
        ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p :=
      GlobalSolutionGluingFromReachability_of_regime_gammaGeOne
        p hχ ha hb hγ_ge_one
    obtain ⟨u, v, hglobal, htrace⟩ := hglue u₀ hu₀ hreach
    have hT : (0 : ℝ) < 1 := by norm_num
    have hsol : IsPaper2ClassicalSolution intervalDomain p 1 u v :=
      hglobal.classical hT
    have happroach :
        ∀ ε > 0, ∃ δ > 0, δ ≤ (1 : ℝ) ∧ ∀ t, 0 < t → t < δ →
          intervalDomain.supNorm (u t) ≤ intervalDomain.supNorm u₀ + ε := by
      intro ε hε
      exact ShenWork.IntervalDomainExistence.initialSupNormApproach_intervalDomain
        p u₀ hu₀ hu₀.admissible.1 hT hsol htrace hε
    refine ⟨1, hT, u, v, hsol, htrace, ?_, fun _hm => hglobal⟩
    exact
      ShenWork.Paper2.IntervalDomainGlobalWellposed.nonminimal_supNorm_bound_of_corrected_initial_approach
        p hχ ha hb hT hsol happroach
  · intro ha_zero _hb_zero
    exact False.elim ((ne_of_gt ha) ha_zero)

end ShenWork.Paper2.BFormPositiveDatumLocalSq
