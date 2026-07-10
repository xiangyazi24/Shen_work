import ShenWork.Paper2.IntervalDomainLedgerSweep
import ShenWork.Paper2.IntervalDomainLedgerSweepHvpos

/-!
# χ₀ = 0 ledger sweep: tight ledger without `Hvpos`

This downstream module composes two existing reductions:

* `TightLimitRegularityInputs` removes `hpde_u` and `Hu`.
* `ReducedLimitRegularityInputsNoHvpos` fills `Hvpos` from strict resolver
  positivity.

The result is a caller-facing tight ledger builder that carries none of
`hpde_u`, `Hu`, or `Hvpos`.  The remaining assumptions are still conditional
ledger fields, especially `Hvsrc` and the source/representation/K1-K2 supply.
-/

open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)

noncomputable section

namespace ShenWork.Paper2.LedgerSweep

/-- The tight ledger with `Hvpos` deleted.

`TightLimitRegularityInputs` has already removed `hpde_u` and `Hu`; this builder
asks callers for the remaining tight-ledger fields after an `Hvpos` witness has
been supplied. -/
abbrev TightLimitRegularityInputsNoHvpos
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) : Type :=
  ∀ _Hvpos : ∀ t, 0 < t → t < D.T → ∀ x : intervalDomainPoint,
      0 < mildChemicalConcentration p D.u t x,
    TightLimitRegularityInputs p u₀ D

/-- Fill the deleted `Hvpos` field using strict resolver positivity. -/
def tightLimitRegularityInputs_of_noHvpos
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (I : TightLimitRegularityInputsNoHvpos p u₀ D) :
    TightLimitRegularityInputs p u₀ D :=
  I (ShenWork.IntervalResolverStrictPositivity.mildChemicalConcentration_pos p D)

/-- Convert the tight no-`Hvpos` builder into Task224's reduced no-`Hvpos`
builder. -/
def reducedNoHvpos_of_tightNoHvpos
    {p : CM2Params} (hχ0 : p.χ₀ = 0) {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (I : TightLimitRegularityInputsNoHvpos p u₀ D) :
    ReducedLimitRegularityInputsNoHvpos p u₀ D :=
  fun Hvpos => reducedLimitRegularityInputs_of_tight hχ0 (I Hvpos)

/-- Direct reduced ledger from the tight ledger with `Hvpos` deleted. -/
def reducedLimitRegularityInputs_of_tight_noHvpos
    {p : CM2Params} (hχ0 : p.χ₀ = 0) {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (I : TightLimitRegularityInputsNoHvpos p u₀ D) :
    ReducedLimitRegularityInputs p u₀ D :=
  reducedLimitRegularityInputs_of_noHvpos
    (reducedNoHvpos_of_tightNoHvpos hχ0 I)

/-- Conditional χ₀=0 `hMildLocal` from the tight ledger with `Hvpos` deleted.

This is still conditional: the caller must supply all fields of the tight
ledger except `Hvpos`.  Internally, `hpde_u` and `Hu` are reconstructed by the
tight-ledger path, and `Hvpos` is reconstructed from strict resolver positivity.
-/
theorem hMildLocal_chi0_zero_of_tight_noHvpos_inputs
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (hα_ge : 1 ≤ p.α)
    (H : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = ShenWork.IntervalMildPicard.picardLimit p u₀ D.T →
        TightLimitRegularityInputsNoHvpos p u₀ D) :
    RestartLocalWiring.IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData p :=
  hMildLocal_chi0_zero_of_reduced_noHvpos_inputs p hχ0 hα_ge
    (fun u₀ hu₀ D hDu =>
      reducedNoHvpos_of_tightNoHvpos hχ0 (H u₀ hu₀ D hDu))

/-- Conditional Paper 2 χ₀=0 theorem from the tight ledger with `Hvpos` deleted.

This is not a headline closure: it still assumes the remaining tight-ledger
fields and the quantitative-side `PicardLimitRestartFrontier`. -/
theorem paper2_theorem_1_1_chiZero_of_tight_noHvpos_inputs
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (H : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = ShenWork.IntervalMildPicard.picardLimit p u₀ D.T →
        TightLimitRegularityInputsNoHvpos p u₀ D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_reduced_noHvpos_inputs
    p hχ0 ha hb hα_ge hγ_ge_one hPLF
    (fun u₀ hu₀ D hDu =>
      reducedNoHvpos_of_tightNoHvpos hχ0 (H u₀ hu₀ D hDu))

end ShenWork.Paper2.LedgerSweep
