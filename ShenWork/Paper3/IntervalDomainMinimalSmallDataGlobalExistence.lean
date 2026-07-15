import ShenWork.Paper3.IntervalDomainSmallDataGlobalExistence
import ShenWork.Paper3.IntervalDomainMinimalFiniteWeakSupBasinEntry
import ShenWork.Paper3.IntervalDomainMinimalFiniteStrongBootstrap

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


#print axioms paper3_mass_reachablePast_of_finite_stable_bootstrap

end

end ShenWork.Paper3
