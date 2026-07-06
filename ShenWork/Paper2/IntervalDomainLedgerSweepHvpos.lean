import ShenWork.Paper2.IntervalDomainLedgerSweep
import ShenWork.Paper2.IntervalResolverStrictPositivity

/-!
# χ₀ = 0 ledger sweep: discharging `Hvpos`

This downstream module removes the explicit `Hvpos` field from the reduced
ledger interface by asking callers for a builder of the reduced ledger after an
`Hvpos` argument has been supplied.  The argument is then filled internally by
the strict resolver-positivity producer.
-/

open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)

noncomputable section

namespace ShenWork.Paper2.LedgerSweep

/-- Reduced ledger builder with `Hvpos` left as the final supplied argument.

`ReducedLimitRegularityInputs` has already removed `Hu`; this type asks callers
for all remaining reduced-ledger fields except `Hvpos`. -/
abbrev ReducedLimitRegularityInputsNoHvpos
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) : Type :=
  ∀ _Hvpos : ∀ t, 0 < t → t < D.T → ∀ x : intervalDomainPoint,
      0 < mildChemicalConcentration p D.u t x,
    ReducedLimitRegularityInputs p u₀ D

/-- Fill the deleted `Hvpos` field using strict resolver positivity. -/
def reducedLimitRegularityInputs_of_noHvpos
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (I : ReducedLimitRegularityInputsNoHvpos p u₀ D) :
    ReducedLimitRegularityInputs p u₀ D :=
  I (ShenWork.IntervalResolverStrictPositivity.mildChemicalConcentration_pos p D)

/-- `hMildLocal` from the reduced ledger with both `Hu` and `Hvpos` removed.

`Hu` is reconstructed by `hMildLocal_chi0_zero_of_reduced_inputs`; `Hvpos` is
reconstructed here from strict resolver positivity. -/
theorem hMildLocal_chi0_zero_of_reduced_noHvpos_inputs
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (hα_ge : 1 ≤ p.α)
    (H : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = ShenWork.IntervalMildPicard.picardLimit p u₀ D.T →
        ReducedLimitRegularityInputsNoHvpos p u₀ D) :
    RestartLocalWiring.IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData p :=
  hMildLocal_chi0_zero_of_reduced_inputs p hχ0 hα_ge
    (fun u₀ hu₀ D hDu =>
      reducedLimitRegularityInputs_of_noHvpos (H u₀ hu₀ D hDu))

/-- Paper 2 Theorem 1.1, χ₀ = 0, from the reduced ledger with both `Hu` and
`Hvpos` removed. -/
theorem paper2_theorem_1_1_chiZero_of_reduced_noHvpos_inputs
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (H : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = ShenWork.IntervalMildPicard.picardLimit p u₀ D.T →
        ReducedLimitRegularityInputsNoHvpos p u₀ D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_reduced_inputs
    p hχ0 ha hb hα_ge hγ_ge_one hPLF
    (fun u₀ hu₀ D hDu =>
      reducedLimitRegularityInputs_of_noHvpos (H u₀ hu₀ D hDu))

end ShenWork.Paper2.LedgerSweep
