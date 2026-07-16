/- Small-data global existence near a linearly stable positive equilibrium
for the faithful general-`m` interval domain.

This is the `intervalDomainM` counterpart of
`IntervalDomainSmallDataGlobalExistence.lean`.  The local Cauchy factory and
the maximal-continuation framework are the faithful all-exponent Paper-2
theories; the stable trapping is supplied by the faithful weak-window basin
entry and the general-`m` finite strong bootstrap.  No `p.m = 1` hypothesis
appears anywhere. -/
import ShenWork.Paper2.IntervalDomainMLocalExistenceAllExponents
import ShenWork.Paper2.IntervalDomainMMaximalContinuationAlternative
import ShenWork.Paper3.IntervalDomainMWeakSupBasinEntry
import ShenWork.Paper3.IntervalDomainMStrongPositiveStrip
import ShenWork.Paper3.IntervalDomainFiniteStrongBootstrapGeneralM
import ShenWork.Paper3.IntervalDomainUniformSpectralGap

namespace ShenWork.Paper3

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainMContinuation
open ShenWork.PDE
open ShenWork.PDE.SectorialOperator

noncomputable section

/-- Joint continuity of the faithful general-`m` solution field on interior
time slabs.  This is conjunct (9) of the shared classical-regularity package,
projected exactly as in the legacy `intervalDomain` extraction. -/
theorem intervalDomainM_solution_jointContinuousOn
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v) :
    ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  hsol.2.1.2.2.2.2.2.2.1

/-- A faithful finite-horizon solution with a two-sided initial strip stays in
an explicit two-sided strip on every initial window `(0, tmid]` with
`tmid` strictly below the horizon.  Near `t = 0` the strip comes from the
initial trace; the remaining compact slab is handled by joint continuity and
closed-domain positivity. -/
theorem intervalDomainM_solution_strip_on_initial_window
    {p : CM2Params} {H tmid B₀ c₀ : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p H u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hu₀Bdd : BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)))
    (hbound₀ : ∀ x, |u₀ x| ≤ B₀)
    (hc₀ : 0 < c₀)
    (hfloor₀ : ∀ x, c₀ ≤ u₀ x)
    (ht0 : 0 < tmid) (htH : tmid < H) :
    ∃ B c : ℝ, 0 < c ∧
      ∀ t, 0 < t → t ≤ tmid → ∀ x : intervalDomainPoint,
        |u t x| ≤ B ∧ c ≤ u t x := by
  obtain ⟨eta, heta, hnear⟩ :=
    intervalDomainM_initialTrace_pointwise_abs_lt_of_classical
      hsol htrace hu₀Bdd (show 0 < c₀ / 2 by linarith)
  let a : ℝ := min (eta / 2) (tmid / 2)
  have ha : 0 < a := lt_min (by linarith) (by linarith)
  have hat : a ≤ tmid := by
    have : a ≤ tmid / 2 := min_le_right _ _
    linarith
  have haeta : a < eta := by
    have : a ≤ eta / 2 := min_le_left _ _
    linarith
  let slab := Set.Icc a tmid ×ˢ Set.Icc (0 : ℝ) 1
  have hslabCompact : IsCompact slab := isCompact_Icc.prod isCompact_Icc
  have hslabSub : slab ⊆ Set.Ioo (0 : ℝ) H ×ˢ Set.Icc (0 : ℝ) 1 :=
    Set.prod_mono (Set.Icc_subset_Ioo ha htH) Subset.rfl
  have hslabNonempty : slab.Nonempty :=
    ⟨(a, 0), ⟨le_rfl, hat⟩, by norm_num⟩
  have hjointOn : ContinuousOn
      (fun tx : ℝ × ℝ => intervalDomainLift (u tx.1) tx.2) slab :=
    (intervalDomainM_solution_jointContinuousOn hsol).mono hslabSub
  have habsCont : ContinuousOn
      (fun tx : ℝ × ℝ => |intervalDomainLift (u tx.1) tx.2|) slab :=
    continuous_abs.comp_continuousOn hjointOn
  obtain ⟨txmax, _htxmaxMem, hmax⟩ :=
    hslabCompact.exists_isMaxOn hslabNonempty habsCont
  obtain ⟨txmin, htxminMem, hmin⟩ :=
    hslabCompact.exists_isMinOn hslabNonempty hjointOn
  have htxminT : txmin.1 ∈ Set.Ioo (0 : ℝ) H :=
    (hslabSub htxminMem).1
  have hminPos : 0 < intervalDomainLift (u txmin.1) txmin.2 :=
    solution_lift_pos_Icc hsol htxminT txmin.2 (htxminMem.2)
  let Bslab : ℝ := |intervalDomainLift (u txmax.1) txmax.2|
  let cslab : ℝ := intervalDomainLift (u txmin.1) txmin.2
  let B : ℝ := max (B₀ + c₀ / 2) Bslab
  let c : ℝ := min (c₀ / 2) cslab
  have hc : 0 < c := lt_min (by linarith) hminPos
  refine ⟨B, c, hc, ?_⟩
  intro t ht0' httmid x
  by_cases hta : t < a
  · have hnearx := hnear t ht0' (lt_trans hta haeta) x
    have habs := abs_lt.mp hnearx
    constructor
    · have : |u t x| ≤ |u₀ x| + c₀ / 2 := by
        have htri : |u t x| ≤ |u t x - u₀ x| + |u₀ x| := by
          calc
            |u t x| = |(u t x - u₀ x) + u₀ x| := by ring_nf
            _ ≤ _ := abs_add_le _ _
        linarith [hnearx]
      exact this.trans (le_trans (by linarith [hbound₀ x])
        (le_max_left _ _))
    · have hfloor : c₀ / 2 ≤ u t x := by
        have := hfloor₀ x
        linarith [habs.1]
      exact le_trans (min_le_left _ _) hfloor
  · push Not at hta
    have hx1 : x.1 ∈ Set.Icc (0 : ℝ) 1 := x.2
    have hmem : ((t, x.1)) ∈ slab :=
      ⟨⟨hta, httmid⟩, hx1⟩
    have hliftEq : intervalDomainLift (u t) x.1 = u t x := by
      simp only [intervalDomainLift, dif_pos hx1]
      rfl
    constructor
    · have hb : |intervalDomainLift (u t) x.1| ≤ Bslab := hmax hmem
      rw [hliftEq] at hb
      exact hb.trans (le_max_right _ _)
    · have hf : cslab ≤ intervalDomainLift (u t) x.1 := hmin hmem
      rw [hliftEq] at hf
      exact le_trans (min_le_right _ _) hf

/-- A finite faithful stable branch issued from the general-`m` weak basin
extends strictly past its current horizon.  The initial window is trapped by
the trace and a compact slab; from the fixed weak window onwards the strong
bootstrap ball keeps every slice inside one positive strip; continuation is
the faithful bounded-plus-floor criterion, valid for every exponent
`p.m > 0`. -/
theorem paper3_reachablePastM_of_finite_stable_bootstrap
    (p : CM2Params)
    {sigma uStar vStar gap T CL H : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
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
    (htrace : InitialTrace intervalDomainM u₀ u) :
    ReachablePastM p u₀ H := by
  have hTH : T < H := by linarith
  have hentry := intervalDomainMSupToStrongBasinEntry_of_contraction_of_solution
    p hsigmaStrong hsigma1 heq hgap hT hCL hCLlip hcontract
      hu₀ hclose hsol hHT htrace
  have hdecay := intervalDomainX2SigmaDistance_restart_exponential_bound_before_generalM
    hsol hT hTH heq hgap hsigmaStrong hsigma1 hentry.2
  have hR : 0 < intervalDomainStrongBootstrapRadiusGeneralM
      p sigma uStar vStar gap heq :=
    intervalDomainStrongBootstrapRadiusGeneralM_pos p heq hgap.1
      (by linarith) hsigma1
  -- Strong-ball strip from the weak window onwards.
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
  -- Initial strip for the datum.
  have hinitial := paper3SupClose_initial_positiveStrip_generalM
    heq.u_pos
    (paper3WeakSupBasinDeltaGeneralM_le_equilibrium
      p sigma uStar vStar T gap heq)
    hu₀ hclose
  have hu₀Bdd : BddAbove
      (Set.range (fun x : intervalDomainPoint => |u₀ x|)) := by
    simpa [intervalDomainM] using hu₀.admissible.1
  have huStar : 0 < uStar := heq.u_pos
  -- Early-window strip up to the weak window time.
  obtain ⟨Bear, cear, hcear, hearly⟩ :=
    intervalDomainM_solution_strip_on_initial_window
      hsol htrace hu₀Bdd hinitial.2.1
      (show 0 < uStar / 4 by linarith)
      hinitial.2.2 hT hTH
  -- Uniform bound before the horizon.
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
  -- Uniform floor before the horizon.
  have hfloor : ∃ c : ℝ, 0 < c ∧
      ∀ t, 0 < t → t < H → ∀ x, c ≤ u t x := by
    refine ⟨min cear (uStar / 4), lt_min hcear (by linarith), ?_⟩
    intro t ht0 htH' x
    by_cases htT : t ≤ T
    · exact le_trans (min_le_left _ _) (hearly t ht0 htT x).2
    · push Not at htT
      exact le_trans (min_le_right _ _) ((horbitStrip t htT.le htH').2 x)
  exact reachablePastM_of_bounded_and_uniform_floor
    p hinitial.1 (lt_trans (by linarith) hHT) hsol htrace hbdd hfloor

/-- Small-data global existence for the faithful general-`m` interval model
near a linearly stable positive-logistic equilibrium.  The radius is the
faithful weak basin delta; globality is maximal continuation against the
stable trapping strip.  No `p.m = 1` hypothesis. -/
theorem intervalDomainM_smallDataGlobalExistence_of_linearlyStable
    (p : CM2Params) {uStar vStar : ℝ}
    (ha : 0 < p.a)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hstable : LinearlyStable unitIntervalNeumannSpectrum p uStar vStar) :
    ∃ delta > 0,
      SmallDataGlobalExistence intervalDomainM p uStar delta := by
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
    simpa [delta] using paper3WeakSupBasinDeltaGeneralM_pos
      p hsigmaStrong hsigma1 heq hgap hT
  refine ⟨delta, hdelta, ?_⟩
  intro u₀ hu₀ hclose
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
      obtain ⟨gu, gv, hgsol, hgtrace⟩ :=
        realize_at_finiteMaximalReachableHorizonM_of_overlapUnique
          huniq hbdd hne
      have hHT : 5 * T / 4 <
          finiteMaximalReachableHorizonM p u₀ := by
        have h1 : 5 * T / 4 < 5 * (deltaLoc / 4) / 4 := by linarith
        have h2 : 5 * (deltaLoc / 4) / 4 < deltaLoc := by linarith
        linarith [hdeltaLocMax]
      have hpast : ReachablePastM p u₀
          (finiteMaximalReachableHorizonM p u₀) :=
        paper3_reachablePastM_of_finite_stable_bootstrap
          p hsigmaStrong hsigma1 heq hgap hT hCL hCLlip hcontract
            hu₀ (by simpa [delta] using hclose) hHT hgsol hgtrace
      exact not_reachablePast_finiteMaximalReachableHorizonM hbdd hpast
    · exact reachableArbitrarilyLongM_of_not_bddAbove hbdd
  obtain ⟨u, v, hglobal, htrace⟩ :=
    globalSolutionM_of_reachableArbitrarilyLong_of_overlapUniqueAt
      huniq hreach
  exact ⟨u, v, hglobal, htrace⟩

#print axioms intervalDomainM_solution_jointContinuousOn
#print axioms intervalDomainM_solution_strip_on_initial_window
#print axioms paper3_reachablePastM_of_finite_stable_bootstrap
#print axioms intervalDomainM_smallDataGlobalExistence_of_linearlyStable

end

end ShenWork.Paper3
