/-
  Q1 final wiring: hQuant for the χ₀ = 0 sub-regime from the
  cone-uniform Picard data — NO inf-threshold, NO minimum-principle
  hypothesis.

  ## Chain

  `coneGradientMildSolutionData_exists` (cone-invariance construction)
  gives, per `M`, ONE horizon `δ(p, M) > 0` and, per PID bounded by `M`,
  packaged Picard data `D` with `D.T = δ` and `D.u = picardLimit`.
  The abstract restart frontier for PICARD-LIMIT-valued data
  (`PicardLimitRestartFrontier`, the F2/S-construction target) upgrades
  to a classical solution at the explicit horizon
  (`ThresholdQuantBridge.classicalSolution_at_horizon`, with the
  initial approach discharged generically).

  ## Residual

  Only `PicardLimitRestartFrontier p` — restart source + frontier core
  for the canonical Picard-limit solutions.  This subsumes the earlier
  `PicardRestartFrontier` shape (`gradientMildSolutionData_of_data E`
  satisfies `D.u = picardLimit p u₀ D.T` definitionally), so ONE
  S-construction discharge closes both the threshold (general χ₀ ≤ 0)
  and the cone (χ₀ = 0) routes.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalMildPicardConeData
import ShenWork.Paper2.IntervalDomainThresholdQuantBridge

open MeasureTheory Set Filter
open ShenWork.IntervalDomain (intervalDomain intervalDomainLift
  intervalDomainPoint intervalMeasure)
open ShenWork.IntervalMildToClassical
open ShenWork.IntervalMildToLocalExistence
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardThreshold
open ShenWork.IntervalMildPicardConeData
open ShenWork.IntervalMildRegularityBootstrap
open ShenWork.Paper2
open ShenWork.Paper2.ThresholdQuantBridge

noncomputable section

namespace ShenWork.Paper2.ConeQuantBridge

/-! ## PID facts -/

/-- A positive initial datum is nonnegative on the CLOSED interval: the
interior positivity extends to the boundary by continuity (via the
clipped extension, which is continuous on `ℝ`). -/
theorem positiveInitialDatum_nonneg
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀) :
    ∀ x, 0 ≤ u₀ x := by
  have hcont : Continuous u₀ := hu₀.admissible.2
  set f₀ : ℝ → ℝ := fun y => u₀ (unitClip y) with hf₀_def
  have hf₀_cont : Continuous f₀ := hcont.comp unitClip_continuous
  have hf₀_pos : ∀ y ∈ Set.Ioo (0:ℝ) 1, 0 < f₀ y := by
    intro y hy
    have hy' : y ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hy
    rw [hf₀_def]
    simp only [unitClip_of_mem hy']
    exact hu₀.pos (by exact hy)
  -- Nonempty within-filters at the endpoints (so the limits are honest).
  haveI hne0 : (nhdsWithin (0:ℝ) (Set.Ioo (0:ℝ) 1)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by
      rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
      exact Set.left_mem_Icc.mpr (by norm_num))
  haveI hne1 : (nhdsWithin (1:ℝ) (Set.Ioo (0:ℝ) 1)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by
      rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
      exact Set.right_mem_Icc.mpr (by norm_num))
  -- Endpoint nonnegativity by one-sided limits.
  have h0 : 0 ≤ f₀ 0 := by
    have htend : Filter.Tendsto f₀ (nhdsWithin 0 (Set.Ioo (0:ℝ) 1))
        (nhds (f₀ 0)) :=
      (hf₀_cont.tendsto 0).mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto htend
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hf₀_pos y hy).le
  have h1 : 0 ≤ f₀ 1 := by
    have htend : Filter.Tendsto f₀ (nhdsWithin 1 (Set.Ioo (0:ℝ) 1))
        (nhds (f₀ 1)) :=
      (hf₀_cont.tendsto 1).mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto htend
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hf₀_pos y hy).le
  -- Trichotomy on the coordinate.
  intro x
  have hx_eq : u₀ x = f₀ x.1 := by
    simp only [hf₀_def, unitClip_of_mem x.2]
    rfl
  rw [hx_eq]
  rcases lt_or_eq_of_le x.2.1 with h0x | h0x
  · rcases lt_or_eq_of_le x.2.2 with hx1 | hx1
    · exact (hf₀_pos x.1 ⟨h0x, hx1⟩).le
    · rw [hx1]; exact h1
  · rw [← h0x]; exact h0

/-- A positive initial datum is positive somewhere (e.g. at `1/2`). -/
theorem positiveInitialDatum_pos_somewhere
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀) :
    ∃ x₀, 0 < u₀ x₀ := by
  have hmem : ((1:ℝ)/2) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hins : (⟨1/2, hmem⟩ : intervalDomainPoint) ∈ intervalDomain.inside := by
    show ((1:ℝ)/2) ∈ Set.Ioo (0:ℝ) 1
    constructor <;> norm_num
  exact ⟨⟨1/2, hmem⟩, hu₀.pos hins⟩

/-! ## The Picard-limit restart frontier (unified residual) -/

/-- **Residual frontier, unified form**: the abstract restart package for
every packaged mild solution whose trajectory IS the canonical Picard
limit.  Both `gradientMildSolutionData_of_data E` (threshold route) and
the cone-construction record (χ₀ = 0 route) satisfy
`D.u = picardLimit p u₀ D.T` definitionally, so one S-construction
discharge closes both routes. -/
def PicardLimitRestartFrontier (p : CM2Params) : Prop :=
  ∀ (u₀ : intervalDomainPoint → ℝ),
    PositiveInitialDatum intervalDomain u₀ →
  ∀ (D : GradientMildSolutionData p u₀),
    D.u = picardLimit p u₀ D.T →
    ∃ _R : GradientMildHalfStepRestartData D,
      GradientMildClassicalFrontierCoreData p D

/-- The unified frontier discharges the threshold-route residual. -/
theorem picardRestartFrontier_of_picardLimitFrontier
    {p : CM2Params} (h : PicardLimitRestartFrontier p) :
    PicardRestartFrontier p := by
  intro u₀ hu₀ E
  exact h u₀ hu₀ (gradientMildSolutionData_of_data E) rfl

/-! ## hQuant for χ₀ = 0 -/

/-- **Quantitative local existence for χ₀ = 0** — the hQuant statement,
with the Picard-contraction core AND the positivity both proved
(cone invariance); the only residual is the restart frontier. -/
theorem quantitativeLocalExistence_chiZero
    (p : CM2Params) (hχ : p.χ₀ = 0) (hα_ge : 1 ≤ p.α)
    (hPLF : PicardLimitRestartFrontier p) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro M hM
  obtain ⟨δ, hδ, h⟩ := coneGradientMildSolutionData_exists p hχ hM hα_ge
  refine ⟨δ, hδ, ?_⟩
  intro u₀ hu₀ hbound
  obtain ⟨D, hDT, hDu⟩ := h u₀ hu₀.admissible.2 hbound
    (positiveInitialDatum_nonneg hu₀)
    (positiveInitialDatum_pos_somewhere hu₀)
  obtain ⟨R, hcore⟩ := hPLF u₀ hu₀ D (by rw [hDu, hDT])
  obtain ⟨v, hsol, htrace⟩ :=
    ThresholdQuantBridge.classicalSolution_at_horizon p D R
      (gradientMildSolutionData_initialApproach p hu₀.admissible.2 D) hcore
  exact ⟨D.u, v, hsol.restrict_horizon hδ (le_of_eq hDT.symm), htrace⟩

/-- **Paper 2 Theorem 1.1 for the χ₀ = 0 sub-regime** from
`PicardLimitRestartFrontier` + `hlocal`: the hQuant input of the final
wiring is now PROVED (modulo the shared restart frontier), with no
threshold and no minimum-principle hypothesis. -/
theorem paper2_theorem_1_1_chiZero_of_frontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : PicardLimitRestartFrontier p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  RestartLocalWiring.paper2_theorem_1_1_from_quant_and_hlocal
    p (le_of_eq hχ) ha hb hγ_ge_one
    (quantitativeLocalExistence_chiZero p hχ hα_ge hPLF)
    hlocal

end ShenWork.Paper2.ConeQuantBridge
