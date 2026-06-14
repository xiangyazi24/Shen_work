import ShenWork.Wiener.EWA.ChemDivAdot

/-!
# EWA brick — the `hGcont` discharge for the chemDiv FINAL/uncond theorem

`chemDiv_eigenvalueSummableOn_uncond` (`ChemDivUncond.lean`) and its R2 core
`chemDiv_eigenvalueSummableOn_viaR2` (`ChemDivViaR2.lean`) both carry the per-mode
**time-continuity** input

  `hGcont : ∀ n, Continuous (fun s => coupledChemDivSourceCoeffs p u s n)`,

used there only to obtain `Continuous (f n)` (hence interval-integrability of the
Duhamel kernel times the coefficient) for the split-integral estimate.

This file DISCHARGES `hGcont` from the SAME committed time-smoothness package the
`adot`/`h_deriv` legs already consume — `CoupledChemDivLocalChainRule p u`
(`IntervalChemDivTimeDerivative.lean:78`).  It is therefore **NOT** an extra
assumption beyond the committed solution time-regularity.

## Route (no new analysis)

`coupledChemDivSourceCoeffs p u s n = cosineCoeffs (coupledChemDivSourceLift p u s) n`
DEFINITIONALLY (`IntervalCoupledSourceTimeC1.lean:24`).  The committed
`coupledChemDivCoeff_hasDerivAt_of_chainRule` (`ChemDivAdot.lean:79`) gives, for
EVERY `s` and `n`, a *global* `HasDerivAt` of `fun r => cosineCoeffs (lift r) n` at
`s`.  Differentiability at every point of `ℝ` implies continuity everywhere
(`HasDerivAt.continuousAt` + `continuous_iff_continuousAt`).  Hence the coefficient
map is globally `Continuous` in time — exactly `hGcont`.

No window restriction, no joint-continuity-of-the-source-lift datum, and in
particular no extra `Mdot`/`A⁰` input: pointwise time-differentiability of the
coefficient (committed via the chain-rule slab) already forces `C⁰` time-continuity.

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalCoupledRegularityBootstrap

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- **Per-mode global time-continuity of the chemDiv source coefficient, for one
mode**, from the committed local chain-rule package.

For every `n`, the time map `s ↦ coupledChemDivSourceCoeffs p u s n` is continuous on
all of `ℝ`.  Proof: the committed `coupledChemDivCoeff_hasDerivAt_of_chainRule`
supplies a `HasDerivAt` of `fun r => cosineCoeffs (coupledChemDivSourceLift p u r) n`
at *every* `s`, and a function differentiable at every point is continuous.  The
coefficient family is *definitionally* this cosine coefficient. -/
theorem chemDiv_coeff_continuous_of_chainRule
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) (n : ℕ) :
    Continuous (fun s => coupledChemDivSourceCoeffs p u s n) := by
  have hcoeff : Continuous
      (fun s => cosineCoeffs (coupledChemDivSourceLift p u s) n) := by
    refine continuous_iff_continuousAt.mpr (fun s => ?_)
    exact (coupledChemDivCoeff_hasDerivAt_of_chainRule hchain s n).continuousAt
  -- `coupledChemDivSourceCoeffs p u s n = cosineCoeffs (coupledChemDivSourceLift p u s) n`.
  simpa only [coupledChemDivSourceCoeffs] using hcoeff

/-- **`hGcont` fully discharged** — per-mode time-continuity of the chemotaxis
-divergence source coefficient family for the committed solution, from the same
local chain-rule time-smoothness package the `adot`/`h_deriv` legs already use.

This is exactly the `∀ n, Continuous (fun s => coupledChemDivSourceCoeffs p u s n)`
input consumed by `chemDiv_eigenvalueSummableOn_viaR2` /
`chemDiv_eigenvalueSummableOn_uncond`.  It is **not** an extra hypothesis beyond the
committed time-regularity: `CoupledChemDivLocalChainRule p u` is the documented
analytic input (pointwise chain rule + dominated-convergence slab) already carried by
the FINAL theorem's `adot` legs (`chemDivAdot_hasDerivWithinAt_of_chainRule`). -/
theorem chemDiv_coeff_timeContinuous
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) :
    ∀ n, Continuous (fun s => coupledChemDivSourceCoeffs p u s n) :=
  fun n => chemDiv_coeff_continuous_of_chainRule hchain n

end ShenWork.IntervalCoupledRegularityBootstrap

#print axioms ShenWork.IntervalCoupledRegularityBootstrap.chemDiv_coeff_timeContinuous
