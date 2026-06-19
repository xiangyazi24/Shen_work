import ShenWork.Paper2.IntervalPicardTowerSupply

open Set
open ShenWork.IntervalDomain (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalMildPicard
  (GradientMildSolutionData HasContinuousSlices picardIter picardLimit)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalPicardIterateUniform (GateCondition)

noncomputable section

namespace ShenWork.Paper2

/-- The strengthened χ₀=0 cone/tower supply, packaged at the local-existence level. -/
def chiZeroDatumProviderSupply
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α) :
    Thm11ChiZeroCoreProvider.DatumProviderSupply p :=
  fun _M hM =>
    let C :=
      ShenWork.IntervalMildPicardConeData.coneGradientMildSolutionData_exists_with_gate_data'
        p hχ0 hM hα
    let δ := C.choose
    let A₂ := C.choose_spec.choose
    have hδ : 0 < δ := C.choose_spec.choose_spec.1
    have hA₂nn : 0 ≤ A₂ := C.choose_spec.choose_spec.2.1
    have hbody := C.choose_spec.choose_spec.2.2
    ⟨δ, hδ, fun u₀ hu₀ hbound =>
      let E := hbody u₀ hu₀.admissible.2 hbound
        (ConeQuantBridge.positiveInitialDatum_nonneg hu₀)
        (ConeQuantBridge.positiveInitialDatum_pos_somewhere hu₀)
      let D := E.choose
      have hspec := E.choose_spec
      have hDT : D.T = δ := hspec.1
      have hDu : D.u = picardLimit p u₀ δ := hspec.2.1
      have hgate : GateCondition p D.M A₂ D.T := hspec.2.2.1
      have hcontSlice : ∀ n, HasContinuousSlices D.T (picardIter p u₀ n) :=
        hspec.2.2.2.1
      have hF :
          ∃ F : ShenWork.IntervalPicardLimitCoeffConv.PicardConvFacts p u₀,
            F.T = δ :=
        hspec.2.2.2.2.1
      have hpos :
          ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T →
            ∀ x ∈ Set.Icc (0 : ℝ) 1,
              0 < intervalDomainLift (picardIter p u₀ n σ) x :=
        fun n σ hσ hσT x hx =>
          hspec.2.2.2.2.2.1 n σ hσ (hσT.trans hDT.le) x hx
      have hT1 : D.T ≤ 1 := hspec.2.2.2.2.2.2.1
      have hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ D.M :=
        hspec.2.2.2.2.2.2.2.1
      have hball :
          ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T →
            ∀ y : intervalDomainPoint, |picardIter p u₀ n σ y| ≤ D.M :=
        hspec.2.2.2.2.2.2.2.2
      let R : ShenWork.IntervalPicardTowerSupply.ResidualAtDatum p u₀ D :=
        { hT1 := hT1, hu₀_bound := hu₀_bound, hball := hball }
      ⟨D, hDT, hDu, hcontSlice, hF,
        ShenWork.IntervalPicardTowerSupply.datumIterLegs_of_cone
          p hχ0 hα ha.le hb.le u₀ hu₀ D hA₂nn hgate
          hu₀.admissible.2 hpos hcontSlice R⟩⟩

/-- χ₀=0 interval-domain local existence with no analytic-frontier hypothesis. -/
theorem intervalDomain_localExistence_chiZero_unconditional
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α) (_hγ : 1 ≤ p.γ)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
        InitialTrace intervalDomain u₀ u := by
  exact
    RestartLocalWiring.localExistence_of_gradientMildHalfStepRestartFrontierCoreLocalData
      p
      (Thm11ChiZeroCoreProvider.hMildLocal_chi0_zero_of_datum
        p hχ0 ha hb hα (chiZeroDatumProviderSupply p hχ0 ha hb hα))
      u₀ hu₀

#print axioms intervalDomain_localExistence_chiZero_unconditional

end ShenWork.Paper2
