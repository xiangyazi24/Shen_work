/- Small-data global existence near a linearly stable positive equilibrium. -/
import ShenWork.Paper2.IntervalDomainL2USubHorizonGluing
import ShenWork.Paper2.IntervalConjugatePicardFloorCoreInhabit
import ShenWork.Paper2.IntervalBFormInitialTrace
import ShenWork.Paper2.IntervalConjugateMildJointTimeDerivativeInterior
import ShenWork.Paper2.IntervalConjugateMildClassicalRegularityFromJointUT
import ShenWork.Paper2.IntervalDuhamelIntegrability
import ShenWork.PDE.IntervalCoupledClassicalCoreDischarge
import ShenWork.PDE.P3MoserEnergyContinuity
import ShenWork.Paper3.IntervalDomainWeakSupBasinEntry
import ShenWork.Paper3.IntervalDomainFiniteStrongBootstrap

namespace ShenWork.Paper3

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.IntervalDomainExistence
open ShenWork.PDE
open ShenWork.PDE.SectorialOperator
open ShenWork.IntervalConjugatePicard
open ShenWork.IntervalCoupledRegularityBootstrap

noncomputable section

local instance : TopologicalSpace intervalDomain.Point :=
  inferInstanceAs (TopologicalSpace intervalDomainPoint)

/-! ### Unconditional local Cauchy producer

The Paper-2 all-exponent local theorem imports a much larger theorem-level
assembly.  The small-data continuation only needs its already-proved local
ingredients, so we expose the same direct reduced-core route here without any
global or stability hypothesis. -/

/-- Direct joint-value/time-derivative package for a positive-floor conjugate
mild solution. -/
def paper3ConjugateMildResolverTimeData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ S.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1)) :
    ShenWork.Paper2.ResolverTimeFromJointUTData S.T S.u
      (ShenWork.Paper2.conjugateMildTimeDerivJointRep S) where
  jointValue :=
    ShenWork.Paper2.conjugateMild_jointValue_u S hu₀_bound hu₀_meas
  jointTimeDeriv :=
    ShenWork.Paper2.conjugateMildTimeDerivJointRep_jointContinuousOn
      S hu₀_cont hu₀_bound hu₀_meas
  positive := by
    intro t ht x hx
    simpa [intervalDomainLift, hx] using S.hpos t ht.1 ht.2.le ⟨x, hx⟩
  hasTimeDeriv := by
    intro t ht x hx
    exact ShenWork.Paper2.conjugateMild_intervalDomainLift_hasDerivAt_time_Icc
      S hu₀_cont hu₀_bound hu₀_meas ht.1 ht.2 hx

/-- The reduced classical core for an arbitrary positive-floor conjugate mild
solution, assembled only from the direct local regularity producers. -/
theorem paper3ConjugateMild_reducedClassicalCore
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ S.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    (htrace : InitialTrace intervalDomain u₀ S.u) :
    CoupledDuhamelReducedClassicalCore p S.T u₀ S.u :=
  ShenWork.Paper2.conjugateMild_reducedClassicalCore_of_jointUT
    S hu₀_cont hu₀_bound hu₀_meas
      (paper3ConjugateMildResolverTimeData
        S hu₀_cont hu₀_bound hu₀_meas)
      htrace

/-- Upgrade an inhabited positive-floor Picard datum to a classical solution
at its explicit horizon, for every exponent allowed by `CM2Params`. -/
theorem paper3ClassicalSolution_of_floorData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (D : ConjugateMildExistenceFloorData p u₀) :
    let S : ConjugateMildSolutionData p u₀ :=
      conjugateMildSolutionData_of_floorData D
    ∃ v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p D.T S.u v ∧
      InitialTrace intervalDomain u₀ S.u := by
  let S : ConjugateMildSolutionData p u₀ :=
    conjugateMildSolutionData_of_floorData D
  have htrace : InitialTrace intervalDomain u₀ S.u :=
    ShenWork.Paper2.BFormInitialTrace.conjugateMildSolutionData_initialTrace
      p hu₀.admissible.2 S
  have hu₀_bound_lift : ∀ y, |intervalDomainLift u₀ y| ≤ S.M := by
    intro y
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · have hsemigroup :=
        ShenWork.IntervalPicardIterateInitialApproach.semigroup_initialApproach
      simp only [S, conjugateMildSolutionData_of_floorData,
        intervalDomainLift, dif_pos hy]
      by_contra hnot
      push Not at hnot
      obtain ⟨delta, hdelta, hclose⟩ := hsemigroup p hu₀.admissible.2
        ((|u₀ ⟨y, hy⟩| - D.M) / 2) (by linarith)
      let t := min D.T delta / 2
      have hmin : 0 < min D.T delta := lt_min D.hT hdelta
      have ht : 0 < t := by dsimp [t]; linarith
      have htT : t ≤ D.T := by
        dsimp [t]
        linarith [min_le_left D.T delta]
      have htdelta : t < delta := by
        dsimp [t]
        linarith [min_le_right D.T delta]
      have hb := D.hbase_ball t ht htT ⟨y, hy⟩
      have hclose' := hclose t ht htdelta ⟨y, hy⟩
      simp only [conjugatePicardIter] at hb
      have htri : |u₀ ⟨y, hy⟩| ≤
          |ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
            (intervalDomainLift u₀) y - u₀ ⟨y, hy⟩| +
          |ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
            (intervalDomainLift u₀) y| := by
        have h := abs_add_le
          (u₀ ⟨y, hy⟩ -
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
              (intervalDomainLift u₀) y)
          (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
            (intervalDomainLift u₀) y)
        rw [sub_add_cancel] at h
        simpa [abs_sub_comm, add_comm] using h
      linarith
    · simp [S, conjugateMildSolutionData_of_floorData,
        intervalDomainLift, hy, D.hM.le]
  have hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.intervalDomainLift_aestronglyMeasurable_of_continuous
      hu₀.admissible.2
  have hcore := paper3ConjugateMild_reducedClassicalCore
    S hu₀.admissible.2 hu₀_bound_lift hu₀_meas htrace
  have hreg :=
    ShenWork.IntervalCoupledRegularityBootstrap.regularityBootstrap_of_coupledDuhamel_reducedClassicalCore
      p hcore
  obtain ⟨v, hpos, hvnn, hpde_u, hpde_v, hbc, hclassreg, htrace'⟩ := hreg
  exact ⟨v,
    IsPaper2ClassicalSolution.of_components S.hT hclassreg hpos hvnn
      hpde_u hpde_v hbc,
    htrace'⟩

/-- Uniform local classical existence on a positive strip.  This is the
continuation factory used below; its lifespan is fixed before the datum. -/
theorem paper3ThresholdLocalExistence_positiveStrip
    (p : CM2Params) :
    ∀ M c : ℝ, 0 < M → 0 < c → ∃ delta : ℝ, 0 < delta ∧
      ∀ w : intervalDomainPoint → ℝ,
        PositiveInitialDatum intervalDomain w →
        (∀ x, |w x| ≤ M) →
        (∀ x, c ≤ w x) →
        ∃ uw vw,
          IsPaper2ClassicalSolution intervalDomain p delta uw vw ∧
          InitialTrace intervalDomain w uw := by
  intro M c hM hc
  obtain ⟨delta, hdelta, hfactory⟩ :=
    conjugateMildExistenceFloorData_exists_uniform p M c hc
  refine ⟨delta, hdelta, ?_⟩
  intro w hw hbound hfloor
  have hwPaper : PaperPositiveInitialDatum intervalDomain w :=
    ⟨hw.admissible, ⟨c, hc, hfloor⟩⟩
  obtain ⟨D, hDdelta⟩ := hfactory w hw.admissible.2 hbound hfloor
  let S : ConjugateMildSolutionData p w :=
    conjugateMildSolutionData_of_floorData D
  obtain ⟨v, hsol, htrace⟩ := paper3ClassicalSolution_of_floorData p hwPaper D
  subst delta
  exact ⟨S.u, v, hsol, htrace⟩

/-- Sup-small positive data around a positive equilibrium lie in one fixed
paper-positive strip. -/
theorem paper3SupClose_initial_positiveStrip
    {uStar delta : ℝ} {u₀ : intervalDomainPoint → ℝ}
    (huStar : 0 < uStar) (hdelta : delta ≤ uStar / 16)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hclose : SupCloseToConstant intervalDomain u₀ uStar delta) :
    PaperPositiveInitialDatum intervalDomain u₀ ∧
      (∀ x, |u₀ x| ≤ 2 * uStar + 1) ∧
      (∀ x, uStar / 4 ≤ u₀ x) := by
  have hconstBdd : BddAbove
      (Set.range (fun _x : intervalDomainPoint => |uStar|)) :=
    ⟨|uStar|, by rintro _ ⟨x, rfl⟩; exact le_rfl⟩
  have hdiffBdd : BddAbove
      (Set.range (fun x : intervalDomainPoint => |u₀ x - uStar|)) :=
    ShenWork.Paper2.BFormPositiveDatumNegPart.bddAbove_abs_sub_of_bddAbove_abs_restart
      hu₀.admissible.1 hconstBdd
  have hpoint : ∀ x : intervalDomainPoint, |u₀ x - uStar| < delta :=
    ShenWork.Paper2.BFormPositiveDatumNegPart.intervalDomain_pointwise_abs_lt_of_supNorm_lt_restart
      hdiffBdd hclose.lt
  have hfloor : ∀ x : intervalDomainPoint, uStar / 4 ≤ u₀ x := by
    intro x
    have hlo := (abs_lt.mp (hpoint x)).1
    linarith
  have hbound : ∀ x : intervalDomainPoint, |u₀ x| ≤ 2 * uStar + 1 := by
    intro x
    have htri : |u₀ x| ≤ |u₀ x - uStar| + |uStar| := by
      calc
        |u₀ x| = |(u₀ x - uStar) + uStar| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    rw [abs_of_pos huStar] at htri
    exact htri.trans (by linarith [hpoint x])
  exact ⟨⟨hu₀.admissible, ⟨uStar / 4, by linarith, hfloor⟩⟩,
    hbound, hfloor⟩

/-- Membership in the explicit strong bootstrap ball gives the same fixed
positive strip pointwise. -/
theorem intervalDomainStrongBootstrapRadius_positiveStrip
    {p : CM2Params} {T t sigma uStar vStar gap : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hm : p.m = 1) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hdist : intervalDomainX2SigmaDistance sigma uStar (u t) ≤
      intervalDomainStrongBootstrapRadius
        p sigma uStar vStar gap heq) :
    (∀ x, |u t x| ≤ 2 * uStar + 1) ∧
      (∀ x, uStar / 4 ≤ u t x) := by
  have hmem := intervalDomainX2SigmaPerturbation_of_classical_positive
    (uStar := uStar) hsol ht hsigma1.le
  let hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
    p hm hsol
  have hcont : Continuous (u t) := solutionSlice_continuous hsolM ht
  have hreal := intervalDomainX2SigmaRealizationBounds_of_continuous
    hsigmaStrong hcont hmem
  let Ctrace := intervalDomainX2SigmaValueTrace sigma
  let d := intervalDomainX2SigmaDistance sigma uStar (u t)
  have hCtrace : 0 ≤ Ctrace := by
    simpa [Ctrace] using intervalDomainX2SigmaValueTrace_nonneg sigma
  have hd : 0 ≤ d := by dsimp [d]; exact Real.sqrt_nonneg _
  have hlocal : d ≤ intervalDomainX2SigmaLocalNemytskiiRadius sigma uStar :=
    hdist.trans (intervalDomainStrongBootstrapRadius_le_positivity
      p sigma uStar vStar gap heq)
  have hposRadius : d ≤
      uStar / (2 * (1 + Ctrace)) := by
    exact hlocal.trans (by
      unfold intervalDomainX2SigmaLocalNemytskiiRadius
        intervalDomainX2SigmaPositivityRadius
      simpa [Ctrace] using min_le_left
        (uStar / (2 * (1 + intervalDomainX2SigmaValueTrace sigma)))
        (1 / intervalDomainX2SigmaC1Envelope sigma))
  have hden : 0 < 2 * (1 + Ctrace) := by positivity
  have hratio : Ctrace * (uStar / (2 * (1 + Ctrace))) ≤ uStar / 2 := by
    rw [show Ctrace * (uStar / (2 * (1 + Ctrace))) =
      (Ctrace * uStar) / (2 * (1 + Ctrace)) by ring]
    apply (div_le_iff₀ hden).2
    nlinarith [heq.u_pos, hCtrace]
  have hvalue : ∀ x, |u t x - uStar| ≤ uStar / 2 := by
    intro x
    calc
      |u t x - uStar| ≤ Ctrace * d := by
        simpa [Ctrace, d] using hreal.value_bound x
      _ ≤ Ctrace * (uStar / (2 * (1 + Ctrace))) :=
        mul_le_mul_of_nonneg_left hposRadius hCtrace
      _ ≤ uStar / 2 := hratio
  constructor
  · intro x
    have htri : |u t x| ≤ |u t x - uStar| + |uStar| := by
      calc
        |u t x| = |(u t x - uStar) + uStar| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    rw [abs_of_pos heq.u_pos] at htri
    calc
      |u t x| ≤ |u t x - uStar| + uStar := htri
      _ ≤ uStar / 2 + uStar := add_le_add (hvalue x) le_rfl
      _ ≤ 2 * uStar + 1 := by nlinarith [heq.u_pos]
  · intro x
    have hlo := neg_le_of_abs_le (hvalue x)
    nlinarith [heq.u_pos]

/-- A finite stable solution issued from the chosen sup-small ball extends
strictly past its current horizon.  The proof first enters the strong ball on
the fixed weak window, then uses the finite-horizon strong bootstrap to keep
every later restart slice in one positive strip. -/
theorem paper3_reachablePast_of_finite_stable_bootstrap
    (p : CM2Params)
    {sigma uStar vStar gap deltaLoc T CL H : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
    (hm : p.m = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    (hdeltaLoc : 0 < deltaLoc)
    (hfactory : ∀ w : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain w →
      (∀ x, |w x| ≤ 2 * uStar + 1) →
      (∀ x, uStar / 4 ≤ w x) →
      ∃ uw vw,
        IsPaper2ClassicalSolution intervalDomain p deltaLoc uw vw ∧
        InitialTrace intervalDomain w uw)
    (hoverlap : ∀ {w : intervalDomainPoint → ℝ},
      PaperPositiveInitialDatum intervalDomain w →
        IntervalClassicalSolutionOverlapUniqueAt p w)
    (hT : 0 < T) (hThalf : T < deltaLoc / 2)
    (hTsmall : 5 * T / 4 < deltaLoc)
    (hCL : 0 < CL)
    (hCLlip : ∀ r s : ℝ,
      |r| ≤ intervalDomainWeakSupConeCeiling uStar →
      |s| ≤ intervalDomainWeakSupConeCeiling uStar →
      |r * (p.a - p.b * r ^ p.α) -
        s * (p.a - p.b * s ^ p.α)| ≤ CL * |r - s|)
    (hcontract :
      intervalDomainWeakSupContractionCoefficient p uStar CL T < 1 / 4)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hclose : SupCloseToConstant intervalDomain u₀ uStar
      (paper3WeakSupBasinDelta p sigma uStar vStar T gap heq))
    (hdeltaLocH : deltaLoc ≤ H)
    (hsol : IsPaper2ClassicalSolution intervalDomain p H u v)
    (htrace : InitialTrace intervalDomain u₀ u) :
    ReachablePast p u₀ H := by
  have hHT : 5 * T / 4 < H := lt_of_lt_of_le hTsmall hdeltaLocH
  have hTH : T < H := by linarith [hTsmall, hdeltaLocH]
  have hentry := intervalDomainSupToStrongBasinEntry_of_contraction_of_solution
    p hsigmaStrong hsigma1 hm heq hgap hT hCL hCLlip hcontract
      hu₀ hclose hsol hHT htrace
  have hdecay := intervalDomainX2SigmaDistance_restart_exponential_bound_before
    hsol hm hT hTH heq hgap hsigmaStrong hsigma1 hentry.2
  have hR : 0 < intervalDomainStrongBootstrapRadius
      p sigma uStar vStar gap heq :=
    intervalDomainStrongBootstrapRadius_pos p heq hgap.1
      (by linarith) hsigma1
  have horbitStrip : ∀ s, T ≤ s → s < H →
      (∀ x, |u s x| ≤ 2 * uStar + 1) ∧
        (∀ x, uStar / 4 ≤ u s x) := by
    intro s hsT hsH
    let tau := s - T
    have htau : 0 ≤ tau := by dsimp [tau]; linarith
    have htime : T + tau = s := by dsimp [tau]; ring
    have hd := hdecay tau htau (by simpa [htime] using hsH)
    have hexp : Real.exp (-(gap / 4) * tau) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith [hgap.1]
    have hdR : intervalDomainX2SigmaDistance sigma uStar (u s) ≤
        intervalDomainStrongBootstrapRadius
          p sigma uStar vStar gap heq := by
      rw [htime] at hd
      exact hd.trans (by
        simpa using mul_le_mul_of_nonneg_left hexp hR.le)
    exact intervalDomainStrongBootstrapRadius_positiveStrip
      hsol hm ⟨lt_of_lt_of_le hT hsT, hsH⟩
        hsigmaStrong hsigma1 heq hdR
  have hinitial := paper3SupClose_initial_positiveStrip
    heq.u_pos
    (paper3WeakSupBasinDelta_le_equilibrium
      p sigma uStar vStar T gap heq)
    hu₀ hclose
  by_cases hsmall : H ≤ deltaLoc / 2
  · obtain ⟨uw, vw, hsolw, htracew⟩ :=
      hfactory u₀ hu₀ hinitial.2.1 hinitial.2.2
    refine ⟨deltaLoc, by linarith, hdeltaLoc, uw, vw, hsolw, htracew⟩
  · push Not at hsmall
    let tau : ℝ := H - deltaLoc / 4
    have htau0 : 0 < tau := by dsimp [tau]; linarith
    have htauH : tau < H := by dsimp [tau]; linarith
    have hTtau : T ≤ tau := by
      dsimp [tau]
      linarith [hThalf, hdeltaLocH]
    have htauMem : tau ∈ Set.Ioo (0 : ℝ) H := ⟨htau0, htauH⟩
    have htauPaper : PaperPositiveInitialDatum intervalDomain (u tau) :=
      UniformContinuation.classicalSolution_slice_paperPositiveInitialDatum
        hsol htauMem
    have htauStrip := horbitStrip tau hTtau htauH
    obtain ⟨w, z, hsolw, htracew⟩ :=
      hfactory (u tau) htauPaper.toPositive htauStrip.1 htauStrip.2
    have hshift : IsPaper2ClassicalSolution intervalDomain p (H - tau)
        (fun t x => u (t + tau) x) (fun t x => v (t + tau) x) :=
      TimeShift.classicalSolution_timeShift TimeShift.regularityTimeShiftWorks
        hsol htau0 htauH
    have hshiftTrace : InitialTrace intervalDomain (u tau)
        (fun t x => u (t + tau) x) :=
      GlueExtension.timeShiftInitialTraceWorks hsol htau0 htauH
    have huniq : IntervalClassicalSolutionOverlapUniqueAt p (u tau) :=
      hoverlap htauPaper
    have hmin : min (H - tau) deltaLoc = H - tau := by
      rw [min_eq_left]
      dsimp [tau]
      linarith
    have hoverU : ∀ s, tau < s → s < H → ∀ x,
        u s x = w (s - tau) x := by
      intro s hstau hsH x
      have hs := huniq
        { T_pos := by dsimp [tau]; linarith
          u := fun t x => u (t + tau) x
          v := fun t x => v (t + tau) x
          sol := hshift, trace := hshiftTrace }
        { T_pos := hdeltaLoc, u := w, v := z, sol := hsolw, trace := htracew }
        (s - tau) (by linarith) (by rw [hmin]; linarith) x
      simpa using hs.1
    have hoverV : ∀ s, tau < s → s < H → ∀ x,
        v s x = z (s - tau) x := by
      intro s hstau hsH x
      have hs := huniq
        { T_pos := by dsimp [tau]; linarith
          u := fun t x => u (t + tau) x
          v := fun t x => v (t + tau) x
          sol := hshift, trace := hshiftTrace }
        { T_pos := hdeltaLoc, u := w, v := z, sol := hsolw, trace := htracew }
        (s - tau) (by linarith) (by rw [hmin]; linarith) x
      simpa using hs.2
    let H' : ℝ := H + deltaLoc / 2
    have hH' : 0 < H' := by dsimp [H']; linarith [hsol.T_pos]
    have hH'le : H' ≤ tau + deltaLoc := by
      dsimp [H', tau]
      linarith
    have hsol' := PiecewiseClassical.piecewiseClassicalWorks p
      hsol.T_pos hdeltaLoc htau0 htauH hsol hsolw hoverU hoverV
        H' hH' hH'le
    have htrace' : InitialTrace intervalDomain u₀
        (fun t x => if t < H then u t x else w (t - tau) x) := by
      intro eps heps
      obtain ⟨d, hd, htr⟩ := htrace eps heps
      refine ⟨min d H, lt_min hd hsol.T_pos, ?_⟩
      intro t ht0 htd
      have htH : t < H := lt_of_lt_of_le htd (min_le_right _ _)
      have htd' : t < d := lt_of_lt_of_le htd (min_le_left _ _)
      have heqfun :
          (fun x => (if t < H then u t x else w (t - tau) x) - u₀ x) =
            (fun x => u t x - u₀ x) := by
        funext x
        rw [if_pos htH]
      change intervalDomainSupNorm
        (fun x => (if t < H then u t x else w (t - tau) x) - u₀ x) < eps
      rw [heqfun]
      exact htr t ht0 htd'
    refine ⟨H', by dsimp [H']; linarith, hH', _, _, hsol', htrace'⟩

/-- A finite classical solution with a bounded initial trace is uniformly
bounded on every closed half-horizon `(0,t]`, with `t` strictly below its
classical horizon.  The short-time leg comes from the initial trace and the
remaining compact slab from joint continuity. -/
theorem intervalDomain_solution_lift_uniform_abs_on_halfHorizon
    {p : CM2Params} {T t : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hbdd₀ : BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)))
    (ht0 : 0 < t) (htT : t < T) :
    ∃ M : ℝ, ∀ τ, 0 < τ → τ ≤ t →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |intervalDomainLift (u τ) x| ≤ M := by
  obtain ⟨eta, heta, _hetaT, hnear⟩ :=
    initialSupNormApproach_intervalDomain p u₀ hu₀ hbdd₀ hsol.T_pos
      hsol htrace (by norm_num : (0 : ℝ) < 1)
  let a := min (eta / 2) (t / 2)
  have ha : 0 < a := by
    dsimp [a]
    exact lt_min (by linarith) (by linarith)
  have hat : a ≤ t := by
    have : a ≤ t / 2 := by dsimp [a]; exact min_le_right _ _
    linarith
  have haeta : a < eta := by
    have : a ≤ eta / 2 := by dsimp [a]; exact min_le_left _ _
    linarith
  let slab := Set.Icc a t ×ˢ Set.Icc (0 : ℝ) 1
  have hslabCompact : IsCompact slab := by
    dsimp [slab]
    exact isCompact_Icc.prod isCompact_Icc
  have hslabSub : slab ⊆
      Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 := by
    dsimp [slab]
    exact Set.prod_mono (Set.Icc_subset_Ioo ha htT) Subset.rfl
  have hjoint :=
    ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity.intervalDomain_solution_jointContinuousOn
      hsol
  have habsCont : ContinuousOn
      (fun tx : ℝ × ℝ =>
        |intervalDomainLift (u tx.1) tx.2|) slab :=
    continuous_abs.comp_continuousOn (hjoint.mono hslabSub)
  have hslabNonempty : slab.Nonempty := by
    refine ⟨(a, 0), ?_⟩
    exact ⟨⟨le_rfl, hat⟩, by norm_num⟩
  obtain ⟨txmax, _htxmax, hmax⟩ :=
    hslabCompact.exists_isMaxOn hslabNonempty habsCont
  let Mcompact := |intervalDomainLift (u txmax.1) txmax.2|
  let Mnear := intervalDomain.supNorm u₀ + 1
  let M := max Mnear Mcompact
  refine ⟨M, ?_⟩
  intro τ hτ hτt x hx
  by_cases hτa : τ < a
  · have hτT : τ < T := lt_of_le_of_lt hτt htT
    have habs := abs_lift_le_supNorm hsol ⟨hτ, hτT⟩ hx
    have hsup : intervalDomain.supNorm (u τ) ≤ Mnear := by
      dsimp [Mnear]
      exact hnear τ hτ (lt_trans hτa haeta)
    exact habs.trans (hsup.trans (by dsimp [M]; exact le_max_left _ _))
  · have hτmem : (τ, x) ∈ slab := by
      dsimp [slab]
      exact ⟨⟨le_of_not_gt hτa, hτt⟩, hx⟩
    have hcompact : |intervalDomainLift (u τ) x| ≤ Mcompact := by
      simpa [Mcompact] using hmax hτmem
    exact hcompact.trans (by dsimp [M]; exact le_max_right _ _)

/-- Parameter-independent overlap uniqueness for the paper's uniformly
positive initial data.  Stability is not used: on each strict sub-horizon,
positivity and compact boundedness supply the two-sided strip needed by the
existing L2 energy argument. -/
def intervalDomainPaperPositiveOverlapUniqueAt
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    IntervalClassicalSolutionOverlapUniqueAt p u₀ := by
  intro T₁ T₂ d₁ d₂ t ht0 htmin x
  refine intervalDomain_classicalSolution_overlap_unique_of_subHorizonBound
    d₁.sol d₂.sol d₁.trace d₂.trace hu₀.admissible.1 ?_ t ht0 htmin x
  intro T' hT' hT'min
  have hT'₁ : T' < T₁ := hT'min.trans_le (min_le_left _ _)
  have hT'₂ : T' < T₂ := hT'min.trans_le (min_le_right _ _)
  obtain ⟨delta₁, hdelta₁, hlo₁⟩ := lift_u_uniformPositive_on_halfHorizon
    d₁.sol d₁.trace hu₀.floor hu₀.admissible hT' hT'₁
  obtain ⟨delta₂, hdelta₂, hlo₂⟩ := lift_u_uniformPositive_on_halfHorizon
    d₂.sol d₂.trace hu₀.floor hu₀.admissible hT' hT'₂
  obtain ⟨M₁, hM₁⟩ := intervalDomain_solution_lift_uniform_abs_on_halfHorizon
    d₁.sol d₁.trace hu₀.toPositive hu₀.admissible.1 hT' hT'₁
  obtain ⟨M₂, hM₂⟩ := intervalDomain_solution_lift_uniform_abs_on_halfHorizon
    d₂.sol d₂.trace hu₀.toPositive hu₀.admissible.1 hT' hT'₂
  refine ⟨min delta₁ delta₂, max M₁ M₂, lt_min hdelta₁ hdelta₂, ?_⟩
  intro τ hτ hτT'
  constructor
  · intro y hy
    exact ⟨(min_le_left _ _).trans (hlo₁ τ hτ hτT' y hy),
      (le_abs_self _).trans
        ((hM₁ τ hτ hτT' y hy).trans (le_max_left _ _))⟩
  · intro y hy
    exact ⟨(min_le_right _ _).trans (hlo₂ τ hτ hτT' y hy),
      (le_abs_self _).trans
        ((hM₂ τ hτ hτT' y hy).trans (le_max_right _ _))⟩

/-- Genuine small-data global-existence producer near a linearly stable
positive equilibrium.  No global solution is assumed: local solutions are
glued up to the maximal reachable horizon, and the finite stable bootstrap
contradicts finiteness of that horizon. -/
theorem intervalDomain_smallDataGlobalExistence_of_linearlyStable
    (p : CM2Params) {uStar vStar : ℝ}
    (hm : p.m = 1) (ha : 0 < p.a)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hstable : LinearlyStable unitIntervalNeumannSpectrum p uStar vStar) :
    ∃ delta > 0,
      SmallDataGlobalExistence intervalDomain p uStar delta := by
  obtain ⟨gap, hgap0, hgap⟩ :=
    unitIntervalLinearSpectralGap_of_linearlyStable_of_a_pos
      p heq hstable ha
  let sigma : ℝ := 7 / 8
  have hsigmaStrong : 3 / 4 < sigma := by norm_num [sigma]
  have hsigma1 : sigma < 1 := by norm_num [sigma]
  let M : ℝ := 2 * uStar + 1
  let c : ℝ := uStar / 4
  have hM : 0 < M := by dsimp [M]; linarith [heq.u_pos]
  have hc : 0 < c := by dsimp [c]; linarith [heq.u_pos]
  obtain ⟨deltaLoc, hdeltaLoc, hfactoryRaw⟩ :=
    paper3ThresholdLocalExistence_positiveStrip p M c hM hc
  have hfactory : ∀ w : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain w →
      (∀ x, |w x| ≤ 2 * uStar + 1) →
      (∀ x, uStar / 4 ≤ w x) →
      ∃ uw vw,
        IsPaper2ClassicalSolution intervalDomain p deltaLoc uw vw ∧
        InitialTrace intervalDomain w uw := by
    simpa [M, c] using hfactoryRaw
  obtain ⟨T, hT, hTquarter, CL, hCL, hCLlip, hcontract⟩ :=
    exists_intervalDomainWeakSupContractionWindow_lt
      p heq.u_pos (by positivity : 0 < deltaLoc / 4)
  have hThalf : T < deltaLoc / 2 := by linarith
  have hTsmall : 5 * T / 4 < deltaLoc := by linarith
  let delta := paper3WeakSupBasinDelta
    p sigma uStar vStar T gap heq
  have hdelta : 0 < delta := by
    simpa [delta] using paper3WeakSupBasinDelta_pos
      p hsigmaStrong hsigma1 heq hgap hT
  refine ⟨delta, hdelta, ?_⟩
  intro u₀ hu₀ hclose
  have hinitial := paper3SupClose_initial_positiveStrip
    heq.u_pos
    (paper3WeakSupBasinDelta_le_equilibrium
      p sigma uStar vStar T gap heq)
    hu₀ (by simpa [delta] using hclose)
  obtain ⟨u₁, v₁, hsol₁, htrace₁⟩ :=
    hfactory u₀ hu₀ hinitial.2.1 hinitial.2.2
  have hreach₁ : ReachableClassicalHorizon p u₀ deltaLoc :=
    ⟨hdeltaLoc, u₁, v₁, hsol₁, htrace₁⟩
  have huniq : IntervalClassicalSolutionOverlapUniqueAt p u₀ :=
    intervalDomainPaperPositiveOverlapUniqueAt p hinitial.1
  have hreach : ReachableArbitrarilyLong p u₀ := by
    by_cases hbdd : BddAbove (reachableClassicalHorizonSet p u₀)
    · have hne : (reachableClassicalHorizonSet p u₀).Nonempty :=
        ⟨deltaLoc, hreach₁⟩
      have hdeltaLocMax : deltaLoc ≤ finiteMaximalReachableHorizon p u₀ :=
        reachable_le_finiteMaximalReachableHorizon hbdd hreach₁
      have hTmax : 0 < finiteMaximalReachableHorizon p u₀ :=
        hdeltaLoc.trans_le hdeltaLocMax
      let u := boundedReachableGluedU hbdd hne
      let v := boundedReachableGluedV hbdd hne
      have hsol : IsPaper2ClassicalSolution intervalDomain p
          (finiteMaximalReachableHorizon p u₀) u v :=
        boundedReachableGlued_isPaper2ClassicalSolution_of_overlapUnique
          huniq hu₀ hbdd hne hTmax
      have htrace : InitialTrace intervalDomain u₀ u :=
        boundedReachableGlued_initialTrace_of_overlapUnique
          huniq hu₀ hbdd hne
      have hpast : ReachablePast p u₀
          (finiteMaximalReachableHorizon p u₀) :=
        paper3_reachablePast_of_finite_stable_bootstrap
          p hsigmaStrong hsigma1 hm heq hgap hdeltaLoc hfactory
            (fun {_w} hw => intervalDomainPaperPositiveOverlapUniqueAt p hw)
            hT hThalf hTsmall hCL hCLlip hcontract hu₀
            (by simpa [delta] using hclose) hdeltaLocMax hsol htrace
      exact False.elim
        (not_reachablePast_finiteMaximalReachableHorizon hbdd hpast)
    · exact reachableArbitrarilyLong_of_not_bddAbove hbdd
  obtain ⟨u, v, hglobal, htrace⟩ :=
    globalSolution_of_reachableArbitrarilyLong_of_overlapUniqueAt
      huniq hu₀ hreach
  exact ⟨u, v, hglobal, htrace⟩

#print axioms paper3ConjugateMildResolverTimeData
#print axioms paper3ConjugateMild_reducedClassicalCore
#print axioms paper3ClassicalSolution_of_floorData
#print axioms paper3ThresholdLocalExistence_positiveStrip
#print axioms paper3SupClose_initial_positiveStrip
#print axioms intervalDomainStrongBootstrapRadius_positiveStrip
#print axioms paper3_reachablePast_of_finite_stable_bootstrap
#print axioms intervalDomain_solution_lift_uniform_abs_on_halfHorizon
#print axioms intervalDomainPaperPositiveOverlapUniqueAt
#print axioms intervalDomain_smallDataGlobalExistence_of_linearlyStable

end

end ShenWork.Paper3
