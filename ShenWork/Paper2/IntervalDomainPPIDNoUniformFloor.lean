/-
  ShenWork/Paper2/IntervalDomainPPIDNoUniformFloor.lean

  A small datum-class obstruction for the strict chi-negative uniform route:
  the family of interval-domain paper-positive initial data with sup bound `1`
  has no common positive lower floor.  Each datum has its own paper floor, but
  the floor can tend to zero along positive constant datums.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.PDE.IntervalDomain
import ShenWork.Paper2.Statements

open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint)
open ShenWork.Paper2 (PaperPositiveInitialDatum)

namespace ShenWork.Paper2

/-- Positive constant interval datums are paper-positive initial data. -/
theorem intervalDomain_const_paperPositive {a : ℝ} (ha : 0 < a) :
    PaperPositiveInitialDatum intervalDomain (fun _ : intervalDomainPoint => a) := by
  constructor
  · constructor
    · refine ⟨|a|, ?_⟩
      rintro _ ⟨x, rfl⟩
      rfl
    · exact continuous_const
  · exact ⟨a, ha, fun _ => le_rfl⟩

/-- The bounded interval PPID class with `|u₀| ≤ 1` has no common positive
closed-domain floor. -/
theorem intervalDomain_paperPositive_bounded_one_no_uniform_floor :
    ¬ ∃ fm : ℝ, 0 < fm ∧
      ∀ {u0p : intervalDomainPoint → ℝ},
        PaperPositiveInitialDatum intervalDomain u0p →
        (∀ x, |u0p x| ≤ (1 : ℝ)) →
        ∀ x, fm ≤ u0p x := by
  rintro ⟨fm, hfm, hcommon⟩
  let a : ℝ := min (fm / 2) (1 / 2)
  have ha_pos : 0 < a := by
    dsimp [a]
    exact lt_min (by linarith) (by norm_num)
  have ha_le_one : a ≤ 1 := by
    dsimp [a]
    have hmin : min (fm / 2) (1 / 2) ≤ 1 / 2 :=
      min_le_right _ _
    linarith
  have ha_lt_fm : a < fm := by
    dsimp [a]
    have hmin : min (fm / 2) (1 / 2) ≤ fm / 2 :=
      min_le_left _ _
    linarith
  have hppid : PaperPositiveInitialDatum intervalDomain
      (fun _ : intervalDomainPoint => a) :=
    intervalDomain_const_paperPositive ha_pos
  have hbd : ∀ x : intervalDomainPoint, |(fun _ : intervalDomainPoint => a) x| ≤
      (1 : ℝ) := by
    intro x
    rw [abs_of_pos ha_pos]
    exact ha_le_one
  let x0 : intervalDomainPoint := ⟨0, by constructor <;> norm_num⟩
  have hle : fm ≤ a := hcommon hppid hbd x0
  linarith

end ShenWork.Paper2

#print axioms ShenWork.Paper2.intervalDomain_paperPositive_bounded_one_no_uniform_floor
