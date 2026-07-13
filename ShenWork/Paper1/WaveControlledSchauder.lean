import ShenWork.Paper1.WaveControlledModulusTrap
import ShenWork.Paper1.CompactConvexProfileSchauder

namespace ShenWork.Paper1

noncomputable section

namespace InControlledLowerPinnedMonotoneTrap

variable {κ M L sigma aL C : ℝ} {φ : ℝ → ℝ}

/-- The controlled parameter trap satisfies the exact hypotheses of the
compact-open Schauder--Tychonoff construction. -/
theorem boundedConvexProfileTrapData
    (hne : ∃ u,
      InControlledLowerPinnedMonotoneTrap κ M L sigma aL C φ u) :
    BoundedConvexProfileTrapData
      (InControlledLowerPinnedMonotoneTrap κ M L sigma aL C φ) M := by
  refine
    { nonempty := hne
      convex := set_convex κ M L sigma aL C φ
      continuous := ?_
      abs_le := ?_ }
  · intro u hu
    exact hu.bare.trap.cunif_bdd.1
  · intro u hu x
    rw [abs_of_nonneg (hu.bare.nonneg x)]
    exact hu.bare.le_M x

/-- Schauder--Tychonoff on the corrected compact convex parameter trap, with
no finite-cube approximation package left as a hypothesis. -/
theorem schauderPrinciple
    (hne : ∃ u,
      InControlledLowerPinnedMonotoneTrap κ M L sigma aL C φ u) :
    LocalUniformSchauderFixedPointPrinciple
      (InControlledLowerPinnedMonotoneTrap κ M L sigma aL C φ) :=
  (boundedConvexProfileTrapData hne).schauderPrinciple

end InControlledLowerPinnedMonotoneTrap

section AxiomAudit

#print axioms InControlledLowerPinnedMonotoneTrap.boundedConvexProfileTrapData
#print axioms InControlledLowerPinnedMonotoneTrap.schauderPrinciple

end AxiomAudit

end

end ShenWork.Paper1
