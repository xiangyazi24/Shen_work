/- Small-data global existence for the mass-constrained faithful general-`m`
minimal model.

This is the `intervalDomainM` counterpart of
`IntervalDomainMinimalSmallDataGlobalExistence.lean`.  Mass conservation is
the faithful mass ODE (valid for every exponent `m`), the stable trapping is
the mass-projected weak-window basin entry plus the finite mass bootstrap,
and continuation is the faithful bounded-plus-floor criterion.  No
`p.m = 1` hypothesis appears. -/
import ShenWork.Paper3.IntervalDomainMSmallDataGlobalExistence
import ShenWork.Paper3.IntervalDomainMMinimalWeakSupBasinEntry
import ShenWork.Paper3.IntervalDomainTailReactionCoercivity

namespace ShenWork.Paper3

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainMContinuation
open ShenWork.PDE
open ShenWork.PDE.SectorialOperator

noncomputable section

/-- The faithful minimal-model mass is constant before the classical horizon:
the datum mass propagates to every positive time.  Valid for every exponent
`m > 0`, because the flux is in divergence form with Neumann boundary. -/
theorem intervalDomainM_minimal_mass_eq_initial_before
    (p : CM2Params) {H t : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p H u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (ht0 : 0 < t) (htH : t < H) :
    intervalDomain.integral (u t) = intervalDomain.integral u₀ := by
  apply le_antisymm
  · exact mass_le_initial_of_a_eq_b_eq_zero
      ha0 hb0 hu₀ hsol htrace ht0 htH
  · let M : ℝ → ℝ := fun s => intervalDomain.integral (u s)
    have hdiff : DifferentiableOn ℝ M (Set.Ioo (0 : ℝ) H) := by
      intro s hs
      exact (mass_hasDerivAt hsol hs.1 hs.2).differentiableAt.differentiableWithinAt
    have hzero : ∀ s ∈ Set.Ioo (0 : ℝ) H, deriv M s = 0 := by
      intro s hs
      simpa [M, ha0, hb0] using mass_derivative_eq_logistic hsol hs.1 hs.2
    have hconst : ∀ s₁ ∈ Set.Ioo (0 : ℝ) H, ∀ s₂ ∈ Set.Ioo (0 : ℝ) H,
        M s₁ = M s₂ := fun s₁ hs₁ s₂ hs₂ =>
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hdiff hzero hs₁ hs₂
    have hinit := mass_tendsto_initial hu₀ hsol htrace
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

/-- A finite mass-constrained faithful stable branch issued from the weak
basin extends strictly past its current horizon: bounded-plus-floor
continuation against the mass-projected trapping strip. -/
theorem paper3_mass_reachablePastM_of_finite_stable_bootstrap
    (p : CM2Params)
    {sigma uStar vStar gap T CL H : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
    (ha0 : p.a = 0) (hb0 : p.b = 0)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hT : 0 < T) (hCL : 0 < CL)
    (hCLlip : ∀ r s : ℝ,
      |r| ≤ intervalDomainMWeakSupConeCeiling uStar →
      |s| ≤ intervalDomainMWeakSupConeCeiling uStar →
      |r * (p.a - p.b * r ^ p.α) -
        s * (p.a - p.b * s ^ p.α)| ≤ CL * |r - s|)
    (hcontract :
      intervalDomainMWeakSupContractionCoefficient p uStar CL T < 1 / 4)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hclose : SupCloseToConstant intervalDomainM u₀ uStar
      (paper3WeakSupBasinDeltaGeneralM p sigma uStar vStar T gap heq))
    (hHT : 5 * T / 4 < H)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p H u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar) :
    ReachablePastM p u₀ H := by
  have hTH : T < H := by linarith
  have hentry :=
    intervalDomainMassSupToStrongBasinEntry_of_contraction_of_solution_generalM
      p hsigmaStrong hsigma1 ha0 hb0 heq hgap hT hCL hCLlip hcontract
        hu₀ hclose hsol hHT htrace hmass
  have hdecay :=
    intervalDomainMassX2SigmaDistance_restart_exponential_bound_before_generalM
      hsol ha0 hb0 hT hTH heq hgap hsigmaStrong hsigma1 hmass hentry.2
  have hR : 0 < intervalDomainStrongBootstrapRadiusGeneralM
      p sigma uStar vStar gap heq :=
    intervalDomainStrongBootstrapRadiusGeneralM_pos p heq hgap.1
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
        intervalDomainStrongBootstrapRadiusGeneralM
          p sigma uStar vStar gap heq := by
      rw [htime] at hd
      exact hd.trans (by
        simpa using mul_le_mul_of_nonneg_left hexp hR.le)
    exact intervalDomainStrongBootstrapRadiusGeneralM_positiveStrip
      hsol ⟨lt_of_lt_of_le hT hsT, hsH⟩
        hsigmaStrong hsigma1 heq hdR
  have hinitial := paper3SupClose_initial_positiveStrip_generalM
    heq.u_pos
    (paper3WeakSupBasinDeltaGeneralM_le_equilibrium
      p sigma uStar vStar T gap heq)
    hu₀ hclose
  have hu₀Bdd : BddAbove
      (Set.range (fun x : intervalDomainPoint => |u₀ x|)) := by
    simpa [intervalDomainM] using hu₀.admissible.1
  obtain ⟨Bear, cear, hcear, hearly⟩ :=
    intervalDomainM_solution_strip_on_initial_window
      hsol htrace hu₀Bdd hinitial.2.1
      (show 0 < uStar / 4 by linarith [heq.u_pos])
      hinitial.2.2 hT hTH
  have hbdd : IsPaper2BoundedBefore intervalDomainM H u := by
    refine ⟨max Bear (2 * uStar + 1), ?_⟩
    intro t ht0 htH'
    have hpt : ∀ x : intervalDomainPoint,
        |u t x| ≤ max Bear (2 * uStar + 1) := by
      intro x
      by_cases htT : t ≤ T
      · exact ((hearly t ht0 htT x).1).trans (le_max_left _ _)
      · push Not at htT
        exact ((horbitStrip t htT.le htH').1 x).trans (le_max_right _ _)
    change intervalDomainSupNorm (u t) ≤ max Bear (2 * uStar + 1)
    unfold intervalDomainSupNorm
    apply csSup_le
    · exact ⟨|u t ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩|,
        ⟨⟨0, Set.left_mem_Icc.mpr zero_le_one⟩, rfl⟩⟩
    · rintro _ ⟨x, rfl⟩
      exact hpt x
  have hfloor : ∃ c : ℝ, 0 < c ∧
      ∀ t, 0 < t → t < H → ∀ x, c ≤ u t x := by
    refine ⟨min cear (uStar / 4),
      lt_min hcear (by linarith [heq.u_pos]), ?_⟩
    intro t ht0 htH' x
    by_cases htT : t ≤ T
    · exact le_trans (min_le_left _ _) (hearly t ht0 htT x).2
    · push Not at htT
      exact le_trans (min_le_right _ _) ((horbitStrip t htT.le htH').2 x)
  exact reachablePastM_of_bounded_and_uniform_floor
    p hinitial.1 (lt_trans (by linarith) hHT) hsol htrace hbdd hfloor

/-- Mass-constrained small-data global existence for the faithful
general-`m` minimal model near a linearly stable neutral equilibrium.
No `p.m = 1` hypothesis. -/
theorem intervalDomainM_massConstrainedSmallDataGlobalExistence_of_linearlyStable
    (p : CM2Params) {uStar vStar : ℝ}
    (ha0 : p.a = 0) (hb0 : p.b = 0)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hstable : LinearlyStable unitIntervalNeumannSpectrum p uStar vStar) :
    ∃ delta > 0,
      MassConstrainedSmallDataGlobalExistence
        intervalDomainM p uStar delta := by
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
    intervalDomainM_thresholdLocalExistence_positiveStrip_allExponents
      p M c hM hc
  have hfactory : ∀ w : intervalDomainPoint → ℝ,
      Continuous w →
      (∀ x, |w x| ≤ 2 * uStar + 1) →
      (∀ x, uStar / 4 ≤ w x) →
      ∃ uw vw,
        IsPaper2ClassicalSolution intervalDomainM p deltaLoc uw vw ∧
        InitialTrace intervalDomainM w uw := by
    simpa [M, c] using hfactoryRaw
  obtain ⟨T, hT, hTquarter, CL, hCL, hCLlip, hcontract⟩ :=
    exists_intervalDomainMWeakSupContractionWindow_lt
      p heq.u_pos (by positivity : 0 < deltaLoc / 4)
  let delta := paper3WeakSupBasinDeltaGeneralM
    p sigma uStar vStar T gap heq
  have hdelta : 0 < delta := by
    simpa [delta] using paper3WeakSupBasinDeltaGeneralM_pos_of_gap_pos
      p hsigmaStrong hsigma1 heq hgap.1 hT
  refine ⟨delta, hdelta, ?_⟩
  intro u₀ hu₀ hclose hmass₀
  have hinitial := paper3SupClose_initial_positiveStrip_generalM
    heq.u_pos
    (paper3WeakSupBasinDeltaGeneralM_le_equilibrium
      p sigma uStar vStar T gap heq)
    hu₀ (by simpa [delta] using hclose)
  obtain ⟨u₁, v₁, hsol₁, htrace₁⟩ :=
    hfactory u₀ hu₀.admissible.2 hinitial.2.1 hinitial.2.2
  have hreach₁ : ReachableClassicalHorizonM p u₀ deltaLoc :=
    ⟨hdeltaLoc, u₁, v₁, hsol₁, htrace₁⟩
  have huniq : IntervalMClassicalSolutionOverlapUniqueAt p u₀ :=
    intervalMClassicalSolutionOverlapUniqueAt_of_paperPositive hinitial.1
  have hreach : ReachableArbitrarilyLongM p u₀ := by
    by_cases hbdd : BddAbove (reachableClassicalHorizonSetM p u₀)
    · exfalso
      have hne : (reachableClassicalHorizonSetM p u₀).Nonempty :=
        ⟨deltaLoc, hreach₁⟩
      have hdeltaLocMax : deltaLoc ≤ finiteMaximalReachableHorizonM p u₀ :=
        reachable_le_finiteMaximalReachableHorizonM hbdd hreach₁
      let Hmax := finiteMaximalReachableHorizonM p u₀
      have hHmax : 0 < Hmax := hdeltaLoc.trans_le hdeltaLocMax
      obtain ⟨gu, gv, hgsol, hgtrace⟩ :=
        realize_at_finiteMaximalReachableHorizonM_of_overlapUnique
          huniq hbdd hne
      -- Extend by the constant equilibrium after the maximal horizon so the
      -- physical mass interface holds at every positive time.
      let ue : ℝ → intervalDomainPoint → ℝ :=
        fun t x => if t < Hmax then gu t x else uStar
      let ve : ℝ → intervalDomainPoint → ℝ :=
        fun t x => if t < Hmax then gv t x else vStar
      have hsole : IsPaper2ClassicalSolution intervalDomainM p Hmax ue ve := by
        apply classicalSolutionLocalityUnderIooAgreement_intervalDomainM
          p hHmax (by simpa [Hmax] using hgsol)
        intro t ht0 htH x
        simp [ue, ve, htH]
      have htracee : InitialTrace intervalDomainM u₀ ue := by
        intro eps heps
        obtain ⟨d, hd, htr⟩ := hgtrace eps heps
        refine ⟨min d Hmax, lt_min hd hHmax, ?_⟩
        intro t ht0 htd
        have htd' : t < d := lt_of_lt_of_le htd (min_le_left _ _)
        have htH : t < Hmax := lt_of_lt_of_le htd (min_le_right _ _)
        have heqfun :
            (fun x => ue t x - u₀ x) = (fun x => gu t x - u₀ x) := by
          funext x
          simp [ue, htH]
        change intervalDomainSupNorm (fun x => ue t x - u₀ x) < eps
        rw [heqfun]
        exact htr t ht0 htd'
      have hmass₀' : intervalDomain.integral u₀ = uStar := by
        simpa [intervalDomain, intervalDomainM] using hmass₀
      have hmassBefore : ∀ t, 0 < t → t < Hmax →
          intervalDomain.integral (ue t) = uStar := by
        intro t ht0 htH
        have heqfun : ue t = gu t := by
          funext x
          simp [ue, htH]
        rw [heqfun,
          intervalDomainM_minimal_mass_eq_initial_before
            p ha0 hb0 hu₀ (by simpa [Hmax] using hgsol) hgtrace ht0 htH,
          hmass₀']
      have hmasse : HasEquilibriumMassOnPositiveTimes
          intervalDomainM ue uStar := by
        intro t ht0
        by_cases htH : t < Hmax
        · have h := hmassBefore t ht0 htH
          change intervalDomainM.integral (ue t) =
            intervalDomainM.volume * uStar
          simpa [intervalDomain, intervalDomainM] using h
        · have heqfun : ue t = fun _ => uStar := by
            funext x
            simp [ue, htH]
          change intervalDomainM.integral (ue t) =
            intervalDomainM.volume * uStar
          rw [heqfun]
          have h := intervalDomain_integral_const uStar
          simpa [intervalDomain, intervalDomainM] using h
      have hHT : 5 * T / 4 < Hmax := by
        have h1 : 5 * T / 4 < 5 * (deltaLoc / 4) / 4 := by linarith
        have h2 : 5 * (deltaLoc / 4) / 4 < deltaLoc := by linarith
        exact lt_of_lt_of_le (lt_trans h1 h2)
          (by simpa [Hmax] using hdeltaLocMax)
      have hpast : ReachablePastM p u₀ Hmax :=
        paper3_mass_reachablePastM_of_finite_stable_bootstrap
          p hsigmaStrong hsigma1 ha0 hb0 heq hgap hT hCL hCLlip hcontract
            hu₀ (by simpa [delta] using hclose) hHT hsole htracee hmasse
      exact not_reachablePast_finiteMaximalReachableHorizonM hbdd
        (by simpa [Hmax] using hpast)
    · exact reachableArbitrarilyLongM_of_not_bddAbove hbdd
  obtain ⟨u, v, hglobal, htrace⟩ :=
    globalSolutionM_of_reachableArbitrarilyLong_of_overlapUniqueAt
      huniq hreach
  exact ⟨u, v, hglobal, htrace⟩

#print axioms intervalDomainM_minimal_mass_eq_initial_before
#print axioms paper3_mass_reachablePastM_of_finite_stable_bootstrap
#print axioms
  intervalDomainM_massConstrainedSmallDataGlobalExistence_of_linearlyStable

end

end ShenWork.Paper3
