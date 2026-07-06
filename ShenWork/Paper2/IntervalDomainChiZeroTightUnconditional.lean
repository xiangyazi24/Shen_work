/-
  ShenWork/Paper2/IntervalDomainChiZeroTightUnconditional.lean

  χ₀ = 0 unconditional wrappers routed through the tight local ledger.

  This plugs the committed datum supply `chiZeroDatumProviderSupply` into the
  Task248 tight-ledger capstones.  The resulting headline has the same external
  hypotheses as the existing χ₀ = 0 unconditional theorem, but the proof path now
  visibly consumes `LedgerSweep.TightLimitRegularityInputs`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainChiZeroUnconditionalLocalExistence
import ShenWork.Paper2.IntervalDomainChiZeroWdataTightFrontier

open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint)

noncomputable section

namespace ShenWork.Paper2

/-- χ₀ = 0 quantitative local existence with the committed datum supply plugged
into the tight-ledger datum capstone. -/
theorem quantitativeLocalExistence_chiZero_unconditional_tightLedger
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  Thm11ChiZeroCoreProvider.quantitativeLocalExistence_chiZero_datum_tightLedger
    p hχ0 ha hb hα (chiZeroDatumProviderSupply p hχ0 ha hb hα)

/-- χ₀ = 0 local existence frontier with the committed datum supply plugged into
the tight-ledger datum capstone. -/
theorem hMildLocal_chi0_zero_unconditional_tightLedger
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) :
    RestartLocalWiring.IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData p :=
  Thm11ChiZeroCoreProvider.hMildLocal_chi0_zero_of_datum_tightLedger
    p hχ0 ha hb hα (chiZeroDatumProviderSupply p hχ0 ha hb hα)

/-- χ₀ = 0 local existence with no analytic-frontier hypothesis, routed through
the tight local ledger and with no `γ ≥ 1` hypothesis. -/
theorem intervalDomain_localExistence_chiZero_unconditional_tightLedger
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
        InitialTrace intervalDomain u₀ u :=
  RestartLocalWiring.localExistence_of_gradientMildHalfStepRestartFrontierCoreLocalData
    p (hMildLocal_chi0_zero_unconditional_tightLedger p hχ0 ha hb hα) u₀ hu₀

/-- Paper 2 Theorem 1.1 on the interval domain, unconditionally for χ₀ = 0,
with both the local and quantitative branches routed through the tight ledger. -/
theorem intervalDomain_theorem_1_1_chiZero_unconditional_tightLedger
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    Theorem_1_1 intervalDomain p :=
  Thm11ChiZeroCoreProvider.paper2_theorem_1_1_chiZero_of_datumProviders_tightLedger
    p hχ0 ha hb hα hγ (chiZeroDatumProviderSupply p hχ0 ha hb hα)

#print axioms intervalDomain_theorem_1_1_chiZero_unconditional_tightLedger

end ShenWork.Paper2
