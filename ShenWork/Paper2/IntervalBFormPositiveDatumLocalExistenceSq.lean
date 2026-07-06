import ShenWork.Paper2.IntervalBFormCron2NegativePartEnergy
import ShenWork.Paper2.IntervalBFormPdeUProducer
import ShenWork.Paper2.IntervalBFormStrictPosClosed
import ShenWork.Paper2.IntervalBFormDirectClassical
import ShenWork.Paper2.IntervalDomainGlobalWellposed

open Filter Topology Set

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint)
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

/-- Per-datum B-form package using the squared-barrier strict-positivity
route.

The strict positivity field is not carried as an assumption and no linear heat
lower barrier appears.  It is derived from `bform_strictPos_closed`, i.e. from
the constant seed `sqrt(c₀)/2`, positive-time restart, the discharged drift
comparison, and the satisfiable restarted strip data below. -/
structure PositiveDatumBFormLocalComponentsSq
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) where
  DB : ConjugateMildExistenceData p u₀
  huPaper : PaperPositiveInitialDatum intervalDomain u₀
  Hinf : ConjugatePicardInfThresholdData p u₀ DB.T
  hsmall :
    |p.χ₀| * (heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt DB.T) * Hinf.CQ)
      + DB.T * Hinf.CL ≤ paperPositiveFloor huPaper / 2
  hpde_u :
    ∀ t x, 0 < t → t < DB.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv (conjugatePicardLimit p u₀ DB.T) t x =
        intervalDomain.laplacian
            ((conjugatePicardLimit p u₀ DB.T) t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p
              ((conjugatePicardLimit p u₀ DB.T) t)
              (mildChemicalConcentration p
                (conjugatePicardLimit p u₀ DB.T) t) x
          + (conjugatePicardLimit p u₀ DB.T) t x
            * (p.a - p.b *
              ((conjugatePicardLimit p u₀ DB.T) t x) ^ p.α)
  DT : TruncatedConjugateMildExistenceData p u₀
  Hbridge : TruncatedConjugateLimitBridge p DB DT
  HmildWeak : TruncatedMildToWeakAvailable p DB
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
  regularity :
    intervalDomain.classicalRegularity DB.T
      (conjugatePicardLimit p u₀ DB.T)
      (mildChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T))
  hpde_v :
    ∀ t x, 0 < t → t < DB.T → x ∈ intervalDomain.inside →
      0 = intervalDomain.laplacian
            ((mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T)) t) x
          - p.μ *
            (mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T)) t x
          + p.ν *
            ((conjugatePicardLimit p u₀ DB.T) t x) ^ p.γ
  neumann :
    ∀ t x, 0 < t → t < DB.T → x ∈ intervalDomain.boundary →
      intervalDomain.normalDeriv
          ((conjugatePicardLimit p u₀ DB.T) t) x = 0 ∧
        intervalDomain.normalDeriv
          ((mildChemicalConcentration p
            (conjugatePicardLimit p u₀ DB.T)) t) x = 0

def PositiveDatumBFormLocalComponentsSq.negativePart_zero
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSq p u₀) :
    ∀ t, 0 < t → t ≤ K.DB.T → ∀ x : intervalDomainPoint,
      negativePart (conjugatePicardLimit p u₀ K.DB.T t x) = 0 :=
  bform_negativePart_zero_of_concrete_truncated_energyCore
    K.DT K.Hbridge K.HmildWeak K.Henergy

def PositiveDatumBFormLocalComponentsSq.strictPos
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSq p u₀) :
    ∀ t x, 0 < t → t < K.DB.T →
      0 < conjugatePicardLimit p u₀ K.DB.T t x :=
  bform_strictPos_closed
    (p := p) (u₀ := u₀) (DB := K.DB)
    (A := K.A) (D := K.Dbar) (M := K.M)
    (drift := K.drift) (react := K.react)
    K.huPaper K.Hinf K.hsmall K.hM_nonneg K.hM K.hstrip

def PositiveDatumBFormLocalComponentsSq.route
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSq p u₀) :
    BFormNegativePartPositivityRoute p K.DB where
  datum := K.huPaper.toPositive
  negativePart_zero := K.negativePart_zero
  strictPos := K.strictPos
  hpde_u := K.hpde_u

theorem PositiveDatumBFormLocalComponentsSq.isClassicalSolution
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSq p u₀) :
    IsPaper2ClassicalSolution intervalDomain p K.DB.T
      (conjugatePicardLimit p u₀ K.DB.T)
      (mildChemicalConcentration p
        (conjugatePicardLimit p u₀ K.DB.T)) := by
  let R := K.route
  refine IsPaper2ClassicalSolution.of_components K.DB.hT
    K.regularity R.strictPos ?_ R.hpde_u K.hpde_v K.neumann
  intro t x ht htT
  exact ShenWork.IntervalMildToClassical.mildChemical_nonneg
    (T := K.DB.T) p
    (u := conjugatePicardLimit p u₀ K.DB.T)
    (conjugateMildSolutionData_of_data K.DB).hnonneg
    (conjugateMildSolutionData_of_data K.DB).hcont
    ht (le_of_lt htT) x

/-- A squared-barrier component package builds the negative-part classical
frontier record, keeping the datum class paper-positive. -/
theorem PositiveDatumBFormLocalComponentsSq.toBFormPositiveClassicalFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSq p u₀) :
    BFormPositiveClassicalFrontier p K.DB := by
  refine
    { route := K.route
      regularity := K.regularity
      v_nonneg := ?_
      hpde_v := K.hpde_v
      neumann := K.neumann }
  intro t x ht htT
  exact ShenWork.IntervalMildToClassical.mildChemical_nonneg
    (T := K.DB.T) p
    (u := conjugatePicardLimit p u₀ K.DB.T)
    (conjugateMildSolutionData_of_data K.DB).hnonneg
    (conjugateMildSolutionData_of_data K.DB).hcont
    ht (le_of_lt htT) x

theorem PositiveDatumBFormLocalComponentsSq.localClassicalSolution
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (K : PositiveDatumBFormLocalComponentsSq p u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u₀ u := by
  refine ⟨K.DB.T, K.DB.hT,
    conjugatePicardLimit p u₀ K.DB.T,
    mildChemicalConcentration p (conjugatePicardLimit p u₀ K.DB.T), ?_⟩
  exact ⟨K.isClassicalSolution,
    ShenWork.Paper2.BFormInitialTrace.conjugatePicardLimit_initialTrace_of_conjugate_data
      p (PaperPositiveInitialDatum.admissible K.huPaper).2 K.DB⟩

/-- Per-datum squared-barrier B-form local hypothesis.  The seed used by the
constructor is the paper-positive floor seed, so the datum class is the
paper-faithful one with a closed-domain positive lower bound. -/
def PositiveDatumBFormLocalHypSq (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomainPoint → ℝ,
    PaperPositiveInitialDatum intervalDomain u₀ →
      Nonempty (PositiveDatumBFormLocalComponentsSq p u₀)

/-- The squared-barrier paper-positive component package produces the
paper-positive negative-part B-form frontier. -/
theorem bFormPaperPositiveLocalFrontier_of_sq
    {p : CM2Params}
    (hBForm : PositiveDatumBFormLocalHypSq p) :
    BFormPaperPositiveLocalFrontier p := by
  intro u₀ hu₀paper
  obtain ⟨K⟩ := hBForm u₀ hu₀paper
  exact ⟨K.DB, ⟨K.toBFormPositiveClassicalFrontier⟩⟩

/-- Local classical existence for paper-positive data from the squared-barrier
B-form component package. -/
theorem positiveDatum_localExistence_of_BFormSq
    {p : CM2Params}
    (hBForm : PositiveDatumBFormLocalHypSq p) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨K⟩ := hBForm u₀ hu₀
  exact K.localClassicalSolution

theorem reachableArbitrarilyLong_of_BFormSq_uniform
    {p : CM2Params}
    (hBForm : PositiveDatumBFormLocalHypSq p)
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
    positiveDatum_localExistence_of_BFormSq hBForm u₀ hu₀paper
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

/-- General-χ B-form headline with `hlocal` discharged for the paper-positive
initial data appearing in `Theorem_1_1`, using the squared-barrier component
package and the F1 uniform continuation input. -/
theorem paper2_theorem_1_1_general_chi_bformSq
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hBForm : PositiveDatumBFormLocalHypSq p)
    (hUniform : IntervalDomainUniformLocalExistence p) :
    Theorem_1_1 intervalDomain p := by
  intro _hχ
  constructor
  · intro _ha _hb u₀ hu₀paper
    have hu₀ : PositiveInitialDatum intervalDomain u₀ := hu₀paper.toPositive
    have hreach :
        ShenWork.IntervalDomainExistence.ReachableArbitrarilyLong p u₀ :=
      reachableArbitrarilyLong_of_BFormSq_uniform hBForm hUniform hu₀paper
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
