import ShenWork.Paper3.IntervalDomainPersistenceGeneralMPart1Corrected
import ShenWork.Paper3.IntervalDomainPersistenceActualLinearPart2Faithful
import ShenWork.Paper3.IntervalDomainPersistenceGeneralMPart3
import ShenWork.Paper3.IntervalDomainPersistenceMinimalPhysicalMass

/-!
# Corrected full Paper 3 Theorem 2.1 on the faithful interval

The printed Part 1 omits its reaction guard, and the repository's stored
zero-time slice is not tied to the classical positive-time orbit needed by
Part 4.  The corrected headline records exactly the proof-supported Part 1
guard and the physical positive-time mass interface for Part 4.
-/

namespace ShenWork.Paper3

open ShenWork.IntervalDomain

noncomputable section

def Theorem_2_1_corrected
    (D : BoundedDomainData) (p : CM2Params) (C : Paper3Constants D p) : Prop :=
  Theorem_2_1_part1_corrected D p ∧
    Theorem_2_1_part2 D p ∧
    Theorem_2_1_part3 D p ∧
    Theorem_2_1_part4_physicalMass D p C

/-- Unconditional, non-vacuous, paper-faithful full persistence theorem for
the physical unit interval with the general `u^m` flux. -/
theorem Theorem_2_1_corrected_intervalDomainM
    (p : CM2Params) :
    Theorem_2_1_corrected intervalDomainM p
      (intervalDomainMPhysicalPart4Constants p) := by
  exact
    ⟨Theorem_2_1_part1_corrected_intervalDomainM p,
      Theorem_2_1_part2_intervalDomainM_proven p,
      Theorem_2_1_part3_intervalDomainM_proven p,
      Theorem_2_1_part4_intervalDomainM_physicalMass_proven p⟩

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.Theorem_2_1_corrected_intervalDomainM
