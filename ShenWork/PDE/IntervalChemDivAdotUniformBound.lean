import ShenWork.PDE.IntervalChemDivTimeDerivative

/-!
# Uniform-in-mode bound on the chemotaxis-divergence source time-derivative coefficients

`coupledChemDivSource_timeC1_of_factorJointC2Inputs` needs
`MchemDot : ℝ` with `∀ s, 0 ≤ s → ∀ n, |coupledChemDivAdot p u s n| ≤ MchemDot` — a
single mode-uniform bound on the time-derivative cosine coefficients.  `ChemDivAdot.lean`
supplies per-mode continuity but not this uniform bound.

**Key simplification.**  `coupledChemDivAdot p u s n = cosineCoeffs (∂ₜsource) n`, and for a
function `f` continuous and bounded by `B` on `[0,1]`, `|cosineCoeffs f n| ≤ 2·B` for
**every** `n` (`cosineCoeffs_abs_le_of_continuous_bounded`).  A *uniform* (as opposed to
*summable*) bound — which is exactly what `hMdot` requires — therefore needs only the
mode-0-style sup bound applied at all modes: no `O(k⁻²)` decay, no weak-`H²` witness.
`Mdot := 2·B_sup`.

The carried input is the source-time-derivative's continuity + uniform sup bound on
`[0,1]` (uniform in `s ≥ 0`) — the `∂ₜ`-source regularity hypothesis.  It is strictly
weaker than the decay route (`chemDivAdot_Mdot_of_spatial_H2`), which the summable
envelope needs elsewhere but which `hMdot` does not.
-/

namespace ShenWork.PDE.IntervalChemDivAdotUniformBound

open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalDomain

/-- **Mode-uniform bound on `coupledChemDivAdot`** (the `MchemDot`/`hMdot` supplier),
from continuity + a uniform sup bound `B_sup` on the source time-derivative lift.
`Mdot := 2·B_sup`; the bound holds at every mode `n` and every `s ≥ 0`. -/
theorem chemDivAdot_uniform_bound
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {B_sup : ℝ} (hBs : 0 ≤ B_sup)
    (hcont : ∀ s, 0 ≤ s →
      ContinuousOn (coupledChemDivTimeDerivativeLift p u s) (Set.Icc (0 : ℝ) 1))
    (hbd : ∀ s, 0 ≤ s → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |coupledChemDivTimeDerivativeLift p u s x| ≤ B_sup) :
    ∃ Mdot : ℝ, ∀ s, 0 ≤ s → ∀ n, |coupledChemDivAdot p u s n| ≤ Mdot := by
  refine ⟨2 * B_sup, fun s hs n => ?_⟩
  simpa [coupledChemDivAdot] using
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      (hcont s hs) hBs (hbd s hs) n

end ShenWork.PDE.IntervalChemDivAdotUniformBound
