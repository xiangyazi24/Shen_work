import ShenWork.Paper3.IntervalDomainNegativeSensitivityMassConvergence
import ShenWork.Paper3.EventualGlobalStability

/-!
# Unconditional positive branch of eventual Theorem 2.3 on the unit interval

This file removes the former qualitative-global-attractor premise from the
`chi0 <= 0` positive-logistic branch.  The currently implemented physical
equation has `m = 1`; that scope restriction remains explicit.
-/

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

/-- Concrete global sup attraction for every bounded positive orbit in the
repulsive positive-logistic interval model. -/
theorem intervalDomain_chiNonpos_globallyAsymptoticallyStableNonminimal
    (p : CM2Params) (hm : p.m = 1) (hχ : p.χ₀ ≤ 0)
    (ha : 0 < p.a) (hb : 0 < p.b) :
    GloballyAsymptoticallyStableNonminimal intervalDomain p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  intro u v huv
  exact intervalDomain_chiNonpos_uniform_u_converges p hm hχ ha hb huv

/-- Unconditional faithful eventual-exponential positive branch of Paper 3
Theorem 2.3 for the implemented one-dimensional `m = 1` equation. -/
theorem intervalDomain_Theorem_2_3_positiveEventual
    (p : CM2Params) (hm : p.m = 1) (hχ : p.χ₀ ≤ 0) :
    ∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      EventuallyGloballyExponentiallyStableNonminimal
        intervalDomain p intervalDomainSectorialStabilityNorms
          eq.1 eq.2 := by
  intro ha hb
  dsimp
  exact intervalDomain_eventuallyGloballyExponentiallyStableNonminimal_of_global
    p hm ha (paper3ConstantEquilibrium_positive p ha hb)
    (unitInterval_positiveEquilibrium_linearlyStable_of_chi_nonpos p hχ ha hb)
    (intervalDomain_chiNonpos_globallyAsymptoticallyStableNonminimal
      p hm hχ ha hb)

#print axioms
  intervalDomain_chiNonpos_globallyAsymptoticallyStableNonminimal
#print axioms intervalDomain_Theorem_2_3_positiveEventual

end

end ShenWork.Paper3
