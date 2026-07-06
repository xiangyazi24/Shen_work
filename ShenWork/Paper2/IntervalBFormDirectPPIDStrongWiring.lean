/-
  ShenWork/Paper2/IntervalBFormDirectPPIDStrongWiring.lean

  Direct B-form wrappers through the PPID-typed strong path.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalBFormDirectClassical
import ShenWork.Paper2.IntervalDomainTheorem11StrongPath

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.BFormDirectClassical

noncomputable section

namespace ShenWork.Paper2.BFormDirectClassical

/-- Direct B-form headline through the PPID-typed strong path.

This avoids the older all-positive local-existence umbrella and consumes the
paper-positive local-existence producer supplied by the direct B-form frontier. -/
theorem paper2_theorem_1_1_general_chi_bformDirect_from_ppid_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hPerDatum : BFormPaperLocalFrontier p)
    (hQuant : ShenWork.Paper2.StrongPath.ChiNegDatumUniformConstructionPPID p) :
    Theorem_1_1 intervalDomain p :=
  ShenWork.Paper2.StrongPath.Theorem_1_1_intervalDomain_of_ppid_local_and_quant
    p hχ ha hb hγ_ge_one
    (paperPositive_localExistence_of_BFormDirect hPerDatum)
    hQuant

#print axioms paper2_theorem_1_1_general_chi_bformDirect_from_ppid_quant

end ShenWork.Paper2.BFormDirectClassical
