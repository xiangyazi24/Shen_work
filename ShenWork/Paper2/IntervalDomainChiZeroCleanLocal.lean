import ShenWork.Paper2.IntervalDomainChiZeroUnconditionalLocalExistence

open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint)

noncomputable section

namespace ShenWork.Paper2

/-- Chi-zero quantitative local existence with the datum supply already plugged in.
This removes the explicit `Hsupply : DatumProviderSupply p` argument from
`Thm11ChiZeroCoreProvider.quantitativeLocalExistence_chiZero_datum`. -/
theorem quantitativeLocalExistence_chiZero_unconditional_clean
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  Thm11ChiZeroCoreProvider.quantitativeLocalExistence_chiZero_datum
    p hχ0 ha hb hα (chiZeroDatumProviderSupply p hχ0 ha hb hα)

/-- Chi-zero `hMildLocal` with the datum supply already plugged in.  This removes
the explicit `Hsupply : DatumProviderSupply p` argument from
`Thm11ChiZeroCoreProvider.hMildLocal_chi0_zero_of_datum`. -/
theorem hMildLocal_chi0_zero_unconditional_clean
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) :
    RestartLocalWiring.IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData p :=
  Thm11ChiZeroCoreProvider.hMildLocal_chi0_zero_of_datum
    p hχ0 ha hb hα (chiZeroDatumProviderSupply p hχ0 ha hb hα)

/-- Chi-zero local existence with no `γ ≥ 1` hypothesis.  The existing theorem
`intervalDomain_localExistence_chiZero_unconditional` carries an unused `_hγ`; this
version exposes the sharper local-existence interface directly from `hMildLocal`. -/
theorem intervalDomain_localExistence_chiZero_unconditional_noGamma
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
        InitialTrace intervalDomain u₀ u :=
  RestartLocalWiring.localExistence_of_gradientMildHalfStepRestartFrontierCoreLocalData
    p (hMildLocal_chi0_zero_unconditional_clean p hχ0 ha hb hα) u₀ hu₀

end ShenWork.Paper2
