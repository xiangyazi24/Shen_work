/-
  ShenWork/Paper2/IntervalDomainChiZeroHeadline.lean

  Route-facing chi-zero headline alias for the current preferred tower/cone
  proof.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalPicardTowerSupply

open ShenWork.IntervalDomain (intervalDomain)
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.ConeQuantBridge

/-- Route-facing chi-zero headline theorem, routed through the strengthened cone
and tower supply.  This is the current preferred entry point; it avoids the old
vacuous ledger route and the intermediate source-spectral surfaces. -/
theorem paper2_theorem_1_1_chiZero_headline
    (p : CM2Params) (hchi0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (halpha : 1 ≤ p.α) (hgamma : 1 ≤ p.γ) :
    Theorem_1_1 intervalDomain p :=
  ShenWork.IntervalPicardTowerSupply.from_cone_construction
    p hchi0 ha hb halpha hgamma

#print axioms paper2_theorem_1_1_chiZero_headline

end ShenWork.Paper2.ConeQuantBridge
