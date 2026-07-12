import ShenWork.Wiener.EWA.ChemDivAdot
import ShenWork.Paper2.IntervalConjugatePicard

/-!
# Chem-div source time-C¹ package on a positive conjugate window

This is the conditional assembly requested for the chi-negative branch.  The
value-side `ℓ¹` envelope is supplied explicitly (the ladder/Green estimate
output), and the flux time-regularity is supplied by the committed local
chain-rule package plus joint continuity/uniform bound for the canonical
chem-div coefficient derivative.  The implementation below is fully checked.
-/

open Set
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalConjugatePicard (ConjugateMildSolutionData)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
  (cosineCoeffs_continuousOn_of_jointContinuousOn_Icc)

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- Conditional chem-div `DuhamelSourceTimeC1On` on a positive window.

The hypotheses are exactly the two analytic inputs not manufactured here:

* `henv`/`henv_sum`: the ladder/Green `ℓ¹` envelope for the source coefficients;
* `hchain`, `hflux_cont`, `hMdot`: the flux time-regularity package for the
  canonical derivative `coupledChemDivAdot`.
-/
noncomputable def chemDivSource_duhamelSourceTimeC1On_of_timeRegularFlux
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    {c T' : ℝ} (_hc : 0 < c) (_hT' : T' < S.T)
    (envelope : ℕ → ℝ) (henv_sum : Summable envelope)
    (henv : ∀ s ∈ Set.Icc c T', ∀ k,
      |coupledChemDivSourceCoeffs p S.u s k| ≤ envelope k)
    (hchain : CoupledChemDivLocalChainRule p S.u)
    (hflux_cont : ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p S.u))
      (Set.Icc c T' ×ˢ Set.Icc (0 : ℝ) 1))
    (Mdot : ℝ)
    (hMdot : ∀ s ∈ Set.Icc c T', ∀ k,
      |coupledChemDivAdot p S.u s k| ≤ Mdot) :
    DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p S.u) c T' where
  adot := coupledChemDivAdot p S.u
  hderiv := by
    intro s _hs k
    have hAt : HasDerivAt
        (fun r => coupledChemDivSourceCoeffs p S.u r k)
        (coupledChemDivAdot p S.u s k) s := by
      simpa only [coupledChemDivSourceCoeffs] using
        coupledChemDivCoeff_hasDerivAt_of_chainRule hchain s k
    exact hAt.hasDerivWithinAt
  hadotcont := by
    intro k
    simpa only [coupledChemDivAdot] using
      cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
        (f := coupledChemDivTimeDerivativeLift p S.u) (c := c) (T := T') k
        hflux_cont
  envelope := envelope
  henv_summable := henv_sum
  henv_bound := henv
  derivBound := Mdot
  hderivBound := hMdot

end ShenWork.IntervalCoupledRegularityBootstrap

#print axioms
  ShenWork.IntervalCoupledRegularityBootstrap.chemDivSource_duhamelSourceTimeC1On_of_timeRegularFlux
