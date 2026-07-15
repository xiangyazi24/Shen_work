import ShenWork.Paper3.IntervalDomainSmallDataGlobalExistence
import ShenWork.Paper3.IntervalDomainMinimalFiniteWeakSupBasinEntry
import ShenWork.Paper3.IntervalDomainMinimalFiniteStrongBootstrap
import ShenWork.Paper3.IntervalDomainUniformSpectralGap
import ShenWork.Paper3.IntervalDomainTailReactionCoercivity

/-!
# Small-data global existence for the mass-constrained minimal model
-/

namespace ShenWork.Paper3

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2
open ShenWork.PDE
open ShenWork.PDE.SectorialOperator
open ShenWork.Paper2.IntervalDomainM

noncomputable section

/-- A finite stable solution issued from the chosen sup-small ball extends
strictly past its current horizon.  The proof first enters the strong ball on
the fixed weak window, then uses the finite-horizon strong bootstrap to keep
every later restart slice in one positive strip. -/
theorem paper3_mass_reachablePast_of_finite_stable_bootstrap
    (p : CM2Params)
    {sigma uStar vStar gap deltaLoc T CL H : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
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
    (htrace : InitialTrace intervalDomain u₀ u)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar) :
    ReachablePast p u₀ H := by
  have hHT : 5 * T / 4 < H := lt_of_lt_of_le hTsmall hdeltaLocH
  have hTH : T < H := by linarith [hTsmall, hdeltaLocH]
  have hentry := intervalDomainMassSupToStrongBasinEntry_of_contraction_of_solution
    p hsigmaStrong hsigma1 hm ha0 hb0 heq hgap hT hCL hCLlip hcontract
      hu₀ hclose hsol hHT htrace hmass
  have hdecay := intervalDomainMassX2SigmaDistance_restart_exponential_bound_before
    hsol hm ha0 hb0 hT hTH heq hgap hsigmaStrong hsigma1 hmass hentry.2
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

/-- In the minimal model the exact mass ODE and the initial trace identify the
positive-time mass of every finite classical solution with the datum mass. -/
theorem intervalDomain_minimal_mass_eq_initial_before
    (p : CM2Params) {H t : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain p H u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (ht0 : 0 < t) (htH : t < H) :
    intervalDomain.integral (u t) = intervalDomain.integral u₀ := by
  have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one p hm hsol
  apply le_antisymm
  · exact mass_le_initial_of_a_eq_b_eq_zero
      ha0 hb0 hu₀ hsolM htrace ht0 htH
  · let M : ℝ → ℝ := fun s => intervalDomain.integral (u s)
    have hdiff : DifferentiableOn ℝ M (Set.Ioo (0 : ℝ) H) := by
      intro s hs
      exact (mass_hasDerivAt hsolM hs.1 hs.2).differentiableAt.differentiableWithinAt
    have hzero : ∀ s ∈ Set.Ioo (0 : ℝ) H, deriv M s = 0 := by
      intro s hs
      simpa [M, ha0, hb0] using mass_derivative_eq_logistic hsolM hs.1 hs.2
    have hconst : ∀ s₁ ∈ Set.Ioo (0 : ℝ) H, ∀ s₂ ∈ Set.Ioo (0 : ℝ) H,
        M s₁ = M s₂ := fun s₁ hs₁ s₂ hs₂ =>
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hdiff hzero hs₁ hs₂
    have hinit := mass_tendsto_initial hu₀ hsolM htrace
    by_contra hnot
    push Not at hnot
    let eps : ℝ := intervalDomain.integral u₀ - M t
    have heps : 0 < eps := by dsimp [eps]; linarith
    obtain ⟨δ, hδ, hnear⟩ := hinit (eps / 2) (by linarith)
    let s := min (δ / 2) (H / 2)
    have hs0 : 0 < s := lt_min (by linarith) (by linarith [hsol.T_pos])
    have hsδ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hsH : s < H :=
      lt_of_le_of_lt (min_le_right _ _) (by linarith [hsol.T_pos])
    have habs := hnear s hs0 hsδ hsH
    have hts : intervalDomain.integral (u t) =
        intervalDomain.integral (u s) := by
      simpa [M] using hconst t ⟨ht0, htH⟩ s ⟨hs0, hsH⟩
    rw [← hts] at habs
    rw [abs_of_neg (by linarith)] at habs
    dsimp [eps] at habs
    linarith

/-- A linearly stable minimal equilibrium has a genuine mass-constrained
small-data global solution.  The construction uses only finite-horizon
classical solutions until maximal-horizon finiteness has been contradicted. -/
theorem
intervalDomain_massConstrainedSmallDataGlobalExistence_of_linearlyStable
    (p : CM2Params) {uStar vStar : ℝ}
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hstable : LinearlyStable unitIntervalNeumannSpectrum p uStar vStar) :
    ∃ delta > 0,
      MassConstrainedSmallDataGlobalExistence
        intervalDomain p uStar delta := by
  obtain ⟨gap, hgap0, hgap⟩ :=
    unitIntervalLinearMassSpectralGap_of_linearlyStable p heq hstable
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
  obtain ⟨T, hT, _hTquarter, CL, hCL, hCLlip, hcontract⟩ :=
    exists_intervalDomainWeakSupContractionWindow_lt
      p heq.u_pos (by positivity : 0 < deltaLoc / 4)
  have hThalf : T < deltaLoc / 2 := by linarith
  have hTsmall : 5 * T / 4 < deltaLoc := by linarith
  let delta := paper3WeakSupBasinDelta
    p sigma uStar vStar T gap heq
  have hdelta : 0 < delta := by
    simpa [delta] using paper3WeakSupBasinDelta_pos_of_gap_pos
      p hsigmaStrong hsigma1 heq hgap.1 hT
  refine ⟨delta, hdelta, ?_⟩
  intro u₀ hu₀ hclose hmass₀
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
      let Hmax := finiteMaximalReachableHorizon p u₀
      let u := boundedReachableGluedU hbdd hne
      let v := boundedReachableGluedV hbdd hne
      have hsol : IsPaper2ClassicalSolution intervalDomain p Hmax u v := by
        simpa [Hmax] using
          boundedReachableGlued_isPaper2ClassicalSolution_of_overlapUnique
            huniq hu₀ hbdd hne hTmax
      have htrace : InitialTrace intervalDomain u₀ u :=
        boundedReachableGlued_initialTrace_of_overlapUnique
          huniq hu₀ hbdd hne
      let ue : ℝ → intervalDomainPoint → ℝ :=
        fun t x => if t < Hmax then u t x else uStar
      let ve : ℝ → intervalDomainPoint → ℝ :=
        fun t x => if t < Hmax then v t x else vStar
      have hsole : IsPaper2ClassicalSolution intervalDomain p Hmax ue ve := by
        apply classicalSolutionLocalityUnderIooAgreement_intervalDomain
          p hsol.T_pos hsol
        intro t ht0 htH x
        simp [ue, ve, htH]
      have htracee : InitialTrace intervalDomain u₀ ue := by
        intro eps heps
        obtain ⟨d, hd, htr⟩ := htrace eps heps
        refine ⟨min d Hmax, lt_min hd hsol.T_pos, ?_⟩
        intro t ht0 htd
        have htd' : t < d := lt_of_lt_of_le htd (min_le_left _ _)
        have htH : t < Hmax := lt_of_lt_of_le htd (min_le_right _ _)
        simpa [ue, htH] using htr t ht0 htd'
      have hmassBefore : ∀ t, 0 < t → t < Hmax →
          intervalDomain.integral (u t) = uStar := by
        intro t ht0 htH
        rw [intervalDomain_minimal_mass_eq_initial_before
          p hm ha0 hb0 hu₀ hsol htrace ht0 htH, hmass₀]
        simp [intervalDomain]
      have hmasse : HasEquilibriumMassOnPositiveTimes
          intervalDomain ue uStar := by
        intro t ht0
        by_cases htH : t < Hmax
        · simpa [ue, htH, intervalDomain] using hmassBefore t ht0 htH
        · simpa [ue, htH, intervalDomain] using
            intervalDomain_integral_const uStar
      have hpast : ReachablePast p u₀ Hmax :=
        paper3_mass_reachablePast_of_finite_stable_bootstrap
          p hsigmaStrong hsigma1 hm ha0 hb0 heq hgap hdeltaLoc hfactory
            (fun {_w} hw => intervalDomainPaperPositiveOverlapUniqueAt p hw)
            hT hThalf hTsmall hCL hCLlip hcontract hu₀
            (by simpa [delta] using hclose)
            (by simpa [Hmax] using hdeltaLocMax) hsole htracee hmasse
      exact False.elim
        (not_reachablePast_finiteMaximalReachableHorizon hbdd
          (by simpa [Hmax] using hpast))
    · exact reachableArbitrarilyLong_of_not_bddAbove hbdd
  obtain ⟨u, v, hglobal, htrace⟩ :=
    globalSolution_of_reachableArbitrarilyLong_of_overlapUniqueAt
      huniq hu₀ hreach
  exact ⟨u, v, hglobal, htrace⟩


#print axioms paper3_mass_reachablePast_of_finite_stable_bootstrap
#print axioms intervalDomain_minimal_mass_eq_initial_before
#print axioms
  intervalDomain_massConstrainedSmallDataGlobalExistence_of_linearlyStable

end

end ShenWork.Paper3
