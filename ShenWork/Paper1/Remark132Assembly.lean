/-
  Assembly of Paper-1 `Remark_1_3_2` (right-vanishing traveling-wave existence).

  This file wires the two halves of the headline together and isolates the one
  remaining analytic residual precisely.

  * The LEFT FLOOR is fully proven (axiom-clean) in `LeftFloorProducer`:
    `strictlyPositiveAtLeft_of_coercive_anchor` discharges `positive_at_left`
    from the maximum principle + Paper-1 coercivity + an anchor, with the
    geometric producer closed (no carried geometric brick).

  * The EXISTENCE half is the Schauder/Rothe construction.  The Schauder
    fixed-point principle itself is unconditional on canonical
    (`inMonotoneWaveTrap_schauderPrinciple`, and the lower-pinned cube data
    `lowerPinnedRawWaveCubeApproxData`).  What remains carried is the analytic
    PDE layer of the construction:
      - `PaperGreenStepInput` (= `PaperPerStepParabolicFloor`): the per-step
        implicit parabolic solver producing the next Rothe iterate;
      - `hstationary`: the Rothe limit solves the frozen stationary equation;
      - `StationaryStrongMaxPrinciple` and `FrozenStationaryFlatAtLeft`:
        nontriviality/strong-max-principle and left flatness of the limit.
    These are the genuine residuals of `b1_chiPos_existence_paper_of_cubeApproxData`.

  We package the existence as a single `RightVanishingWaveExistence` hypothesis
  and assemble `Remark_1_3_2` from it, so the remaining obligation is named and
  machine-checked.
-/
import ShenWork.Paper1.LeftFloorProducer
import ShenWork.Paper1.WaveLemma42G1Discharge

namespace ShenWork.Paper1

noncomputable section

open Filter Topology

/-- The right-vanishing wave existence statement in the extended
positive-sensitivity regime, phrased exactly as the `construction` hypothesis of
`Remark_1_3_2.of_frozen_right_vanishing_profile_existence`.  This is the single
remaining analytic residual: a `FrozenRightVanishingWaveProfile` for every
admissible parameter tuple. -/
def RightVanishingWaveExistence : Prop :=
  ∀ p : CMParams,
    p.α = p.m + p.γ - 1 →
    (1 / 2 : ℝ) < positiveSensitivityExtendedThreshold p →
    (1 / 2 : ℝ) ≤ p.χ →
    p.χ < min (positiveSensitivityExtendedThreshold p) 1 →
    ∀ c : ℝ, 2 < c →
      ∃ U : ℝ → ℝ, FrozenRightVanishingWaveProfile p c U

/-- `Remark_1_3_2` follows from `RightVanishingWaveExistence`.  Pure repackaging
of the canonical bridge, recorded here so the residual carries a single name. -/
theorem remark_1_3_2_of_rightVanishingWaveExistence
    (h : RightVanishingWaveExistence) : Remark_1_3_2 :=
  Remark_1_3_2.of_frozen_right_vanishing_profile_existence h

/-- The frozen-stationary existence chain (Schauder principle already
discharged by the unconditional cube data) feeds the right-vanishing existence:
a `FrozenStationaryWaveProfile` for the tuple gives a
`FrozenRightVanishingWaveProfile` via the canonical weakening, so the residual is
exactly the carried analytic data of
`b1_chiPos_existence_paper_of_cubeApproxData`. -/
theorem rightVanishingWaveExistence_of_frozenStationaryExistence
    (hstat : ∀ p : CMParams,
      p.α = p.m + p.γ - 1 →
      (1 / 2 : ℝ) < positiveSensitivityExtendedThreshold p →
      (1 / 2 : ℝ) ≤ p.χ →
      p.χ < min (positiveSensitivityExtendedThreshold p) 1 →
      ∀ c : ℝ, 2 < c →
        ∃ U : ℝ → ℝ, FrozenStationaryWaveProfile p c U) :
    RightVanishingWaveExistence := by
  intro p hα hext hχ_ge hχ_lt c hc
  obtain ⟨U, hU⟩ := hstat p hα hext hχ_ge hχ_lt c hc
  exact ⟨U, hU.to_rightVanishingProfile⟩

/-- End-to-end reduction of `Remark_1_3_2` to the frozen-stationary existence
(the carried PDE residual). -/
theorem remark_1_3_2_of_frozenStationaryExistence
    (hstat : ∀ p : CMParams,
      p.α = p.m + p.γ - 1 →
      (1 / 2 : ℝ) < positiveSensitivityExtendedThreshold p →
      (1 / 2 : ℝ) ≤ p.χ →
      p.χ < min (positiveSensitivityExtendedThreshold p) 1 →
      ∀ c : ℝ, 2 < c →
        ∃ U : ℝ → ℝ, FrozenStationaryWaveProfile p c U) :
    Remark_1_3_2 :=
  remark_1_3_2_of_rightVanishingWaveExistence
    (rightVanishingWaveExistence_of_frozenStationaryExistence hstat)

section Remark132AssemblyAxiomAudit
#print axioms remark_1_3_2_of_rightVanishingWaveExistence
#print axioms rightVanishingWaveExistence_of_frozenStationaryExistence
#print axioms remark_1_3_2_of_frozenStationaryExistence
end Remark132AssemblyAxiomAudit

end

end ShenWork.Paper1
