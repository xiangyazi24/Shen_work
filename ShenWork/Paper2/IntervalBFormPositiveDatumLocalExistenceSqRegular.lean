import ShenWork.Paper2.IntervalBFormTruncatedBridgeProducerData
import ShenWork.Paper2.IntervalBFormPdeUProducer
import ShenWork.Paper2.IntervalBFormSpectralPdeAgreementStandardFacts
import ShenWork.Paper2.IntervalBFormNeumannDischarge
import ShenWork.Paper2.IntervalBFormHpdeVDischarge
import ShenWork.Paper2.IntervalBFormStrictPosClosed
import ShenWork.Paper2.IntervalBFormRegularityDischarge
import ShenWork.Paper2.IntervalBFormPositiveDatumLocalExistenceSqBankedConcrete
import ShenWork.Paper2.IntervalDomainGlobalWellposed

open Filter Topology Set

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint
   intervalDomainClassicalRegularity)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData ConjugatePicardInfThresholdData
   conjugateMildSolutionData_of_data conjugatePicardLimit paperPositiveFloor)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant)
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainGlobalWellposed

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumLocalSq

open ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Corrected per-datum B-form package for the squared-barrier route.  The
negative-part step is the regular flux/test chain: the concrete test is
`-u_-`, and the B_N identity is obtained from bounded measurable data on
`[0,1]`. -/
structure PositiveDatumBFormLocalComponentsSqRegular
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) where
  DB : ConjugateMildExistenceData p u₀
  huPaper : PaperPositiveInitialDatum intervalDomain u₀
  Hinf : ConjugatePicardInfThresholdData p u₀ DB.T
  hsmall :
    |p.χ₀| * (heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt DB.T) * Hinf.CQ)
      + DB.T * Hinf.CL ≤ paperPositiveFloor huPaper / 2
  HpdeFacts :
    ShenWork.IntervalBFormSpectral.BFormSpectralPdeAgreementStandardFacts p DB.T
      (conjugatePicardLimit p u₀ DB.T)
  DT : TruncatedConjugateMildExistenceData p u₀
  HbridgeT : DT.T = DB.T
  HtruncatedEnergy : TruncatedNegativePartEnergyCoreRegularData p DT
  htruncatedM_le_DBM : DT.M ≤ DB.M
  hLinearStripCore :
    ∀ τ, 0 < τ → τ < DB.T →
      NeumannLinearDriftCoefficientsRegular (DB.T - τ)
        (restartTimeShift τ (bformConcreteDrift p DB))
        (restartTimeShift τ (bformConcreteReact p DB)) ∧
      IsClassicalNeumannLinearDriftSuperSolution (DB.T - τ)
        (restartTimeShift τ (bformConcreteDrift p DB))
        (restartTimeShift τ (bformConcreteReact p DB))
        (restartTimeShift τ (bformConjugatePicardLift p DB))
  regularityFrontier :
    ShenWork.Paper2.BFormDirectClassical.BFormDirectFrontier p DB
  neumannFacts :
    BFormNeumannStandardFacts p DB.T u₀
      (conjugatePicardLimit p u₀ DB.T)
  initialTrace :
    InitialTrace intervalDomain u₀
      (conjugatePicardLimit p u₀ DB.T)

def PositiveDatumBFormLocalComponentsSqRegular.regularity
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSqRegular p u₀) :
    intervalDomain.classicalRegularity K.DB.T
      (conjugatePicardLimit p u₀ K.DB.T)
      (mildChemicalConcentration p
        (conjugatePicardLimit p u₀ K.DB.T)) :=
  bForm_classicalRegularity_of_direct_frontier K.regularityFrontier

def PositiveDatumBFormLocalComponentsSqRegular.boundedClassicalRegularity
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSqRegular p u₀) :
    ShenWork.IntervalBFormSpectral.BFormBoundedClassicalRegularity p K.DB.T
      (conjugatePicardLimit p u₀ K.DB.T) := by
  refine ⟨K.regularity, ?_⟩
  refine ⟨(conjugateMildSolutionData_of_data K.DB).M,
    (conjugateMildSolutionData_of_data K.DB).hM.le, ?_⟩
  intro t ht htT x
  exact (conjugateMildSolutionData_of_data K.DB).hbound t ht htT x

def PositiveDatumBFormLocalComponentsSqRegular.Hpde
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSqRegular p u₀) :
    ShenWork.IntervalBFormSpectral.HasBFormSpectralPdeAgreement p K.DB.T
      (conjugatePicardLimit p u₀ K.DB.T) :=
  ShenWork.IntervalBFormSpectral.hasBFormSpectralPdeAgreement_of_standardFacts
    (conjugateMildSolutionData_of_data K.DB).hmild
    K.boundedClassicalRegularity K.HpdeFacts

def PositiveDatumBFormLocalComponentsSqRegular.bridgeData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSqRegular p u₀) :
    TruncatedConjugateLimitBridgeProducerData p K.DB K.DT :=
  truncatedConjugateLimitBridgeProducerData_of_cores
    K.HbridgeT K.HtruncatedEnergy K.htruncatedM_le_DBM

def PositiveDatumBFormLocalComponentsSqRegular.bridge
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSqRegular p u₀) :
    TruncatedConjugateLimitBridge p K.DB K.DT :=
  truncatedConjugateLimitBridge_of_faithful_truncation K.bridgeData

def PositiveDatumBFormLocalComponentsSqRegular.negativePart_zero
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSqRegular p u₀) :
    ∀ t, 0 < t → t ≤ K.DB.T → ∀ x : intervalDomainPoint,
      negativePart (conjugatePicardLimit p u₀ K.DB.T t x) = 0 := by
  intro t ht htT x
  have Hbridge := K.bridge
  have htDT : t ≤ K.DT.T := by
    simpa [K.HbridgeT] using htT
  have hnonneg :
      0 ≤ truncatedConjugatePicardLimit p u₀ K.DT.T t x :=
    K.bridgeData.truncated_nonneg t ht htDT x
  have heq :
      conjugatePicardLimit p u₀ K.DB.T t x
        = truncatedConjugatePicardLimit p u₀ K.DT.T t x :=
    Hbridge.2 t ht htT x
  rw [heq]
  exact negativePart_eq_zero_of_nonneg hnonneg

def PositiveDatumBFormLocalComponentsSqRegular.hstrip
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSqRegular p u₀) :
    ∀ τ, 0 < τ → τ < K.DB.T →
      NeumannLinearDriftCoefficientsRegular (K.DB.T - τ)
        (restartTimeShift τ (bformConcreteDrift p K.DB))
        (restartTimeShift τ (bformConcreteReact p K.DB)) ∧
      IsClassicalNeumannLinearDriftSuperSolution (K.DB.T - τ)
        (restartTimeShift τ (bformConcreteDrift p K.DB))
        (restartTimeShift τ (bformConcreteReact p K.DB))
        (restartTimeShift τ (bformConjugatePicardLift p K.DB)) ∧
      (∀ s x, 0 < s → s < K.DB.T - τ →
        x ∈ Set.Ioo (0 : ℝ) 1 →
          |bformConcreteDrift p K.DB (τ + s) x| ≤
            bformConcreteDriftA p K.DB) ∧
      (∀ s x, 0 < s → s < K.DB.T - τ →
        x ∈ Set.Ioo (0 : ℝ) 1 →
          -bformConcreteReact p K.DB (τ + s) x ≤
            bformConcreteDbar p K.DB) := by
  intro τ hτ hτT
  obtain ⟨hcoeff, hsuper⟩ := K.hLinearStripCore τ hτ hτT
  exact ⟨hcoeff, hsuper,
    bformConcreteDrift_bound_restart p K.DB τ hτ hτT,
    bformConcreteReact_bound_restart p K.DB τ hτ hτT⟩

def PositiveDatumBFormLocalComponentsSqRegular.strictPos
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSqRegular p u₀) :
    ∀ t x, 0 < t → t < K.DB.T →
      0 < conjugatePicardLimit p u₀ K.DB.T t x :=
  bform_strictPos_closed
    (p := p) (u₀ := u₀) (DB := K.DB)
    (A := bformConcreteDriftA p K.DB)
    (D := bformConcreteDbar p K.DB)
    (M := bformConcreteM p K.DB)
    (drift := bformConcreteDrift p K.DB)
    (react := bformConcreteReact p K.DB)
    K.huPaper K.Hinf K.hsmall
    (bformConcreteM_nonneg p K.DB)
    (bformConcreteM_closes p K.DB)
    K.hstrip

def PositiveDatumBFormLocalComponentsSqRegular.hpde_u
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSqRegular p u₀) :
    ∀ t x, 0 < t → t < K.DB.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv (conjugatePicardLimit p u₀ K.DB.T) t x =
        intervalDomain.laplacian
            ((conjugatePicardLimit p u₀ K.DB.T) t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p
              ((conjugatePicardLimit p u₀ K.DB.T) t)
              (mildChemicalConcentration p
                (conjugatePicardLimit p u₀ K.DB.T) t) x
          + (conjugatePicardLimit p u₀ K.DB.T) t x
            * (p.a - p.b *
              ((conjugatePicardLimit p u₀ K.DB.T) t x) ^ p.α) :=
  ShenWork.IntervalConjugatePicard.intervalConjugateMildSolution_pde_u_from_picard_data_and_spectral
    K.DB K.Hpde

def PositiveDatumBFormLocalComponentsSqRegular.route
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSqRegular p u₀) :
    BFormNegativePartPositivityRoute p K.DB where
  datum := K.huPaper.toPositive
  negativePart_zero := K.negativePart_zero
  strictPos := K.strictPos
  hpde_u := K.hpde_u

def PositiveDatumBFormLocalComponentsSqRegular.neumann
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSqRegular p u₀) :
    ∀ t x, 0 < t → t < K.DB.T → x ∈ intervalDomain.boundary →
      intervalDomain.normalDeriv
          ((conjugatePicardLimit p u₀ K.DB.T) t) x = 0 ∧
        intervalDomain.normalDeriv
          ((mildChemicalConcentration p
            (conjugatePicardLimit p u₀ K.DB.T)) t) x = 0 :=
  bForm_neumann_of_standardFacts K.neumannFacts

theorem PositiveDatumBFormLocalComponentsSqRegular.isClassicalSolution
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSqRegular p u₀) :
    IsPaper2ClassicalSolution intervalDomain p K.DB.T
      (conjugatePicardLimit p u₀ K.DB.T)
      (mildChemicalConcentration p
        (conjugatePicardLimit p u₀ K.DB.T)) := by
  let R := K.route
  have hreg :
      intervalDomainClassicalRegularity K.DB.T
        (conjugatePicardLimit p u₀ K.DB.T)
        (mildChemicalConcentration p
          (conjugatePicardLimit p u₀ K.DB.T)) := by
    simpa [intervalDomain] using K.regularity
  have hpdeV :
      ∀ t x, 0 < t → t < K.DB.T → x ∈ intervalDomain.inside →
        0 = intervalDomain.laplacian
              ((mildChemicalConcentration p
                (conjugatePicardLimit p u₀ K.DB.T)) t) x
            - p.μ *
              (mildChemicalConcentration p
                (conjugatePicardLimit p u₀ K.DB.T)) t x
            + p.ν *
              ((conjugatePicardLimit p u₀ K.DB.T) t x) ^ p.γ :=
    bForm_mildChemical_hpde_v_of_resolver_standardFacts
      K.neumannFacts.resolver_source_decay hreg R.strictPos
  refine IsPaper2ClassicalSolution.of_components K.DB.hT
    K.regularity R.strictPos ?_ R.hpde_u hpdeV K.neumann
  intro t x ht htT
  exact ShenWork.IntervalMildToClassical.mildChemical_nonneg
    (T := K.DB.T) p
    (u := conjugatePicardLimit p u₀ K.DB.T)
    (conjugateMildSolutionData_of_data K.DB).hnonneg
    (conjugateMildSolutionData_of_data K.DB).hcont
    ht (le_of_lt htT) x

theorem PositiveDatumBFormLocalComponentsSqRegular.localClassicalSolution
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSqRegular p u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u₀ u := by
  refine ⟨K.DB.T, K.DB.hT,
    conjugatePicardLimit p u₀ K.DB.T,
    mildChemicalConcentration p (conjugatePicardLimit p u₀ K.DB.T), ?_⟩
  exact ⟨K.isClassicalSolution, K.initialTrace⟩

def PositiveDatumBFormLocalHypSqRegular (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomainPoint → ℝ,
    PaperPositiveInitialDatum intervalDomain u₀ →
      Nonempty (PositiveDatumBFormLocalComponentsSqRegular p u₀)

theorem positiveDatum_localExistence_of_BFormSqRegular
    {p : CM2Params}
    (hBForm : PositiveDatumBFormLocalHypSqRegular p) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨K⟩ := hBForm u₀ hu₀
  exact K.localClassicalSolution

theorem reachableArbitrarilyLong_of_BFormSqRegular_uniform
    {p : CM2Params}
    (hBForm : PositiveDatumBFormLocalHypSqRegular p)
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
    positiveDatum_localExistence_of_BFormSqRegular hBForm u₀ hu₀paper
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

theorem paper2_theorem_1_1_general_chi_bformSq_regular
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHypSqRegular p)
    (hUniform : IntervalDomainUniformLocalExistence p) :
    Theorem_1_1 intervalDomain p := by
  intro _hχ
  constructor
  · intro _ha _hb u₀ hu₀paper
    have hu₀ : PositiveInitialDatum intervalDomain u₀ := hu₀paper.toPositive
    have hreach :
        ShenWork.IntervalDomainExistence.ReachableArbitrarilyLong p u₀ :=
      reachableArbitrarilyLong_of_BFormSqRegular_uniform hBForm hUniform hu₀paper
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
      nonminimal_supNorm_bound_of_corrected_initial_approach
        p hχ ha hb hT hsol happroach
  · intro ha_zero _hb_zero
    exact False.elim ((ne_of_gt ha) ha_zero)

end ShenWork.Paper2.BFormPositiveDatumLocalSq
