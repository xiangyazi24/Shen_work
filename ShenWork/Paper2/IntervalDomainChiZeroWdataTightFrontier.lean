/-
  ShenWork/Paper2/IntervalDomainChiZeroWdataTightFrontier.lean

  χ₀ = 0 Wdata/datum capstone wrappers routed through the tight local ledger.

  The hypotheses are intentionally the same as the existing Wdata/datum capstones
  in `IntervalDomainThm11ChiZeroCoreProvider`; the difference is proof-path
  visibility: the restart/core package is assembled by
  `restartAndFrontierCore_of_wdata_tight`, so the final wrappers consume
  `LedgerSweep.TightLimitRegularityInputs` rather than the older reduced-ledger
  helper.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainThm11ChiZeroCoreProvider

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint)
open ShenWork.IntervalMildPicard
  (GradientMildSolutionData HasContinuousSlices picardIter picardLimit)
open ShenWork.IntervalMildPicardThreshold (gradientMildSolutionData_initialApproach)
open ShenWork.IntervalMildPicardConeData (coneGradientMildSolutionData_exists_with_data)
open ShenWork.Paper2 (PositiveInitialDatum Theorem_1_1)
open ShenWork.Paper2.HresWiring (WdataProvider)

noncomputable section

namespace ShenWork.Paper2.Thm11ChiZeroCoreProvider

/-- Quantitative local existence for χ₀ = 0 from the Wdata-only surface, routed
through the tight `hpde_u`/`Hu`-free local ledger. -/
theorem quantitativeLocalExistence_chiZero_wdata_tightLedger
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b) (hα_ge : 1 ≤ p.α)
    (Hiter : IterCoeffTimeContProvider p)
    (HWdata : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = picardLimit p u₀ D.T → WdataProvider p u₀ D) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro M hM
  obtain ⟨δ, hδ, h⟩ := coneGradientMildSolutionData_exists_with_data p hχ0 hM hα_ge
  refine ⟨δ, hδ, ?_⟩
  intro u₀ hu₀ hbound
  obtain ⟨D, hDT, hDu, hcont_iter, hFacts_ex, _hpos_iter⟩ :=
    h u₀ hu₀.admissible.2 hbound
      (ShenWork.Paper2.ConeQuantBridge.positiveInitialDatum_nonneg hu₀)
      (ShenWork.Paper2.ConeQuantBridge.positiveInitialDatum_pos_somewhere hu₀)
  have hDu' : D.u = picardLimit p u₀ D.T := by rw [hDT]; exact hDu
  obtain ⟨hFacts, hFactsT⟩ := hFacts_ex
  have hFacts_T : hFacts.T = D.T := by rw [hFactsT, hDT]
  obtain ⟨R, hCore⟩ :=
    restartAndFrontierCore_of_wdata_tight p hχ0 ha hb hα_ge u₀ hu₀ D hDu'
      hcont_iter hFacts hFacts_T (Hiter u₀ hu₀ D hDu') (HWdata u₀ hu₀ D hDu')
  obtain ⟨v, hsol, htrace⟩ :=
    ShenWork.Paper2.ThresholdQuantBridge.classicalSolution_at_horizon p D R
      (gradientMildSolutionData_initialApproach p hu₀.admissible.2 D) hCore
  exact ⟨D.u, v, hsol.restrict_horizon hδ (le_of_eq hDT.symm), htrace⟩

/-- Local existence for χ₀ = 0 from the Wdata-only surface, routed through the
tight `hpde_u`/`Hu`-free local ledger. -/
theorem hMildLocal_chi0_zero_of_wdata_tightLedger
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b) (hα_ge : 1 ≤ p.α)
    (Hiter : IterCoeffTimeContProvider p)
    (HWdata : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = picardLimit p u₀ D.T → WdataProvider p u₀ D) :
    RestartLocalWiring.IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData p := by
  intro u₀ hu₀
  obtain ⟨B, hB⟩ := hu₀.admissible.1
  set M := max B 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right B 1)
  have hbound : ∀ x, |u₀ x| ≤ M := fun x =>
    le_trans (hB (Set.mem_range_self x)) (le_max_left B 1)
  obtain ⟨δ, _hδ, hD⟩ := coneGradientMildSolutionData_exists_with_data p hχ0 hM hα_ge
  obtain ⟨D, hDT, hDu, hcont_iter, hFacts_ex, _hpos_iter⟩ :=
    hD u₀ hu₀.admissible.2 hbound
      (ShenWork.Paper2.ConeQuantBridge.positiveInitialDatum_nonneg hu₀)
      (ShenWork.Paper2.ConeQuantBridge.positiveInitialDatum_pos_somewhere hu₀)
  have hDu' : D.u = picardLimit p u₀ D.T := by rw [hDT]; exact hDu
  obtain ⟨hFacts, hFactsT⟩ := hFacts_ex
  have hFacts_T : hFacts.T = D.T := by rw [hFactsT, hDT]
  obtain ⟨R, hCore⟩ :=
    restartAndFrontierCore_of_wdata_tight p hχ0 ha hb hα_ge u₀ hu₀ D hDu'
      hcont_iter hFacts hFacts_T (Hiter u₀ hu₀ D hDu') (HWdata u₀ hu₀ D hDu')
  exact ⟨D, R, gradientMildSolutionData_initialApproach p hu₀.admissible.2 D, hCore⟩

/-- χ₀ = 0 Wdata capstone with the local side routed through
`LedgerSweep.TightLimitRegularityInputs`. -/
theorem paper2_theorem_1_1_chiZero_wdata_tightLedger
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (Hiter : IterCoeffTimeContProvider p)
    (HWdata : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = picardLimit p u₀ D.T →
        WdataProvider p u₀ D) :
    Theorem_1_1 intervalDomain p :=
  RestartLocalWiring.paper2_theorem_1_1_from_quant_and_hlocal
    p (le_of_eq hχ0) ha hb hγ
    (quantitativeLocalExistence_chiZero_wdata_tightLedger p hχ0 ha hb hα Hiter HWdata)
    (RestartLocalWiring.localExistence_of_gradientMildHalfStepRestartFrontierCoreLocalData
      p (hMildLocal_chi0_zero_of_wdata_tightLedger p hχ0 ha hb hα Hiter HWdata))

/-- Quantitative local existence from the narrowed datum-owned supply, routed
through the tight `hpde_u`/`Hu`-free local ledger. -/
theorem quantitativeLocalExistence_chiZero_datum_tightLedger
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b) (hα_ge : 1 ≤ p.α)
    (Hsupply : DatumProviderSupply p) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro M hM
  obtain ⟨δ, hδ, h⟩ := Hsupply M hM
  refine ⟨δ, hδ, ?_⟩
  intro u₀ hu₀ hbound
  obtain ⟨D, hDT, hDu, hcont_iter, hFacts_ex, hWdata, hiter_cont⟩ := h u₀ hu₀ hbound
  have hDu' : D.u = picardLimit p u₀ D.T := by rw [hDT]; exact hDu
  obtain ⟨hFacts, hFactsT⟩ := hFacts_ex
  have hFacts_T : hFacts.T = D.T := by rw [hFactsT, hDT]
  obtain ⟨R, hCore⟩ :=
    restartAndFrontierCore_of_wdata_tight p hχ0 ha hb hα_ge u₀ hu₀ D hDu'
      hcont_iter hFacts hFacts_T hiter_cont hWdata
  obtain ⟨v, hsol, htrace⟩ :=
    ShenWork.Paper2.ThresholdQuantBridge.classicalSolution_at_horizon p D R
      (gradientMildSolutionData_initialApproach p hu₀.admissible.2 D) hCore
  exact ⟨D.u, v, hsol.restrict_horizon hδ (le_of_eq hDT.symm), htrace⟩

/-- Local existence from the narrowed datum-owned supply, routed through the
tight `hpde_u`/`Hu`-free local ledger. -/
theorem hMildLocal_chi0_zero_of_datum_tightLedger
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b) (hα_ge : 1 ≤ p.α)
    (Hsupply : DatumProviderSupply p) :
    RestartLocalWiring.IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData p := by
  intro u₀ hu₀
  obtain ⟨B, hB⟩ := hu₀.admissible.1
  set M := max B 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right B 1)
  have hbound : ∀ x, |u₀ x| ≤ M := fun x =>
    le_trans (hB (Set.mem_range_self x)) (le_max_left B 1)
  obtain ⟨δ, _hδ, h⟩ := Hsupply M hM
  obtain ⟨D, hDT, hDu, hcont_iter, hFacts_ex, hWdata, hiter_cont⟩ := h u₀ hu₀ hbound
  have hDu' : D.u = picardLimit p u₀ D.T := by rw [hDT]; exact hDu
  obtain ⟨hFacts, hFactsT⟩ := hFacts_ex
  have hFacts_T : hFacts.T = D.T := by rw [hFactsT, hDT]
  obtain ⟨R, hCore⟩ :=
    restartAndFrontierCore_of_wdata_tight p hχ0 ha hb hα_ge u₀ hu₀ D hDu'
      hcont_iter hFacts hFacts_T hiter_cont hWdata
  exact ⟨D, R, gradientMildSolutionData_initialApproach p hu₀.admissible.2 D, hCore⟩

/-- χ₀ = 0 datum-owned capstone with the local side routed through
`LedgerSweep.TightLimitRegularityInputs`. -/
theorem paper2_theorem_1_1_chiZero_of_datumProviders_tightLedger
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (Hsupply : DatumProviderSupply p) :
    Theorem_1_1 intervalDomain p :=
  RestartLocalWiring.paper2_theorem_1_1_from_quant_and_hlocal
    p (le_of_eq hχ0) ha hb hγ
    (quantitativeLocalExistence_chiZero_datum_tightLedger p hχ0 ha hb hα Hsupply)
    (RestartLocalWiring.localExistence_of_gradientMildHalfStepRestartFrontierCoreLocalData
      p (hMildLocal_chi0_zero_of_datum_tightLedger p hχ0 ha hb hα Hsupply))

#print axioms paper2_theorem_1_1_chiZero_wdata_tightLedger
#print axioms paper2_theorem_1_1_chiZero_of_datumProviders_tightLedger

end ShenWork.Paper2.Thm11ChiZeroCoreProvider
