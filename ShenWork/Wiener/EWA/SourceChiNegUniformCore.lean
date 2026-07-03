/-
  ShenWork/Wiener/EWA/SourceChiNegUniformCore.lean

  **Wiener lifting packaging + per-datum Core bridge.**

  Bundles the Wiener algebra data needed by `chiNeg_EWA_core_of_datum` into a
  structure `WienerLifting`, and wraps the per-datum Core construction to use it.

  The uniform construction (`ChiNegDatumUniformCore`) requires two ingredients
  beyond what this file provides:
  1. **Wiener membership for PPID datums** — continuous bounded functions are
     NOT necessarily in the Wiener algebra. Regularity strengthening (H² or C²)
     would close this gap.
  2. **Prescribed-T FP or T-monotonicity** — to use a UNIFORM lifespan δ
     (from `exists_uniform_EWA_lifespan`) instead of per-datum T, either:
     (a) factor the clean FP to accept T as input, or
     (b) prove T ≥ δ from constant monotonicity, then use `Core.restrict`.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceChiNegPerDatumV6

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.EWA

/-- Wiener algebra lifting data for a PPID datum on `[0,1]`.

A `WienerLifting` provides the cosine-series infrastructure needed by the
EWA fixed-point machinery: an extension to ℝ, ℓ¹ summability of cosine
coefficients, MemW 1 membership, and pointwise reconstruction. -/
structure WienerLifting (u₀p : intervalDomainPoint → ℝ) where
  u₀ : ℝ → ℝ
  hu₀ : Continuous u₀
  floor : ℝ
  hfloor_pos : 0 < floor
  hfloor : ∀ y, floor ≤ u₀ y
  hsumc : Summable (fun k => |cosineCoeffs u₀ k|)
  hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀))
  coeff_bound : ℝ
  hcoeff_bound : ∀ n, |cosineCoeffs u₀ n| ≤ coeff_bound
  hrecon : ∀ x : intervalDomainPoint,
    u₀p x = ∑' n, cosineCoeffs u₀ n * cosineMode n x.1

def WienerLifting.wienerNorm {u₀p : intervalDomainPoint → ℝ} (W : WienerLifting u₀p) : ℝ :=
  ‖(⟨ofCosineCoeffs (cosineCoeffs W.u₀), W.hmem⟩ : WA 1)‖

/-- **Per-datum Core from Wiener lifting.**

Packages `chiNeg_EWA_core_of_datum` with a `WienerLifting` input. Returns
`∃ T > 0, ∃ u, Core p T u₀p u` (EWA existentially abstracted away). -/
theorem core_of_wienerLifting (p : CM2Params)
    {u₀p : intervalDomainPoint → ℝ}
    (W : WienerLifting u₀p)
    (hβpos : 0 < p.β) (hαnn : 0 ≤ p.α) (hμle1 : p.μ ≤ 1) :
    ∃ (T : ℝ), 0 < T ∧ ∃ u : ℝ → intervalDomainPoint → ℝ,
      CoupledDuhamelReducedClassicalCore p T u₀p u := by
  obtain ⟨T, hTpos, u_star, hCore⟩ :=
    chiNeg_EWA_core_of_datum p W.u₀ W.hu₀ W.hfloor_pos W.hfloor W.hsumc W.hmem
      W.hcoeff_bound u₀p W.hrecon hβpos hαnn hμle1
  exact ⟨T, hTpos, realSlice u_star, hCore⟩

end ShenWork.EWA
