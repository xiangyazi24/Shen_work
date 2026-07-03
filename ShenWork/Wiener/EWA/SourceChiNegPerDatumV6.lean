/-
  ShenWork/Wiener/EWA/SourceChiNegPerDatumV6.lean

  **Per-datum EWA core construction from the clean EvenReal fixed point.**

  Combines `picardEWA_clean_fixedPoint_evenReal` (SourceFixedPointEvenReal.lean)
  with `realSlice_reducedCore_of_evenReal` (SourceReducedCoreWireV6EvenReal.lean)
  to produce `CoupledDuhamelReducedClassicalCore` from clean datum data.

  The ball floor η = δ₀/2 (half the datum floor) is derived automatically from
  `uniformFloor_on_ball`, and passed to the v6 theorem as a generic floor
  parameter — no constraint tying the floor value to the lifespan T.

  Hypotheses:
  - Continuous u₀ : ℝ → ℝ with global floor δ₀ > 0
  - ℓ¹ summability and MemW 1 of cosine coefficients (the Wiener membership gap)
  - Uniform bound on cosine coefficients
  - Reconstruction: u₀p on [0,1] equals its cosine series

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceFixedPointEvenReal
import ShenWork.Wiener.EWA.SourceReducedCoreWireV6EvenReal

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.EWA

theorem chiNeg_EWA_core_of_datum (p : CM2Params)
    (u₀ : ℝ → ℝ) (hu₀ : Continuous u₀)
    {δ₀ : ℝ} (hδ₀pos : 0 < δ₀) (hfloor₀ : ∀ y, δ₀ ≤ u₀ y)
    (hsumc : Summable (fun k => |cosineCoeffs u₀ k|))
    (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀)))
    {Mu0 : ℝ} (hu0bd : ∀ n, |cosineCoeffs u₀ n| ≤ Mu0)
    (u₀p : intervalDomainPoint → ℝ)
    (hrecon : ∀ x : intervalDomainPoint,
      u₀p x = ∑' n, cosineCoeffs u₀ n * cosineMode n x.1)
    (hβpos : 0 < p.β) (hαnn : 0 ≤ p.α) (hμle1 : p.μ ≤ 1) :
    ∃ (T : ℝ) (_ : 0 < T),
      ∃ u_star : EWA T 1,
        CoupledDuhamelReducedClassicalCore p T u₀p (realSlice u_star) := by
  have hνpos : 0 ≤ p.ν := le_of_lt p.hν
  -- Step 1: clean EvenReal fixed point.
  obtain ⟨T, hTpos, u_star, hu_ball, hER, hfix⟩ :=
    picardEWA_clean_fixedPoint_evenReal u₀ hu₀ hδ₀pos hfloor₀ hsumc hmem hβpos hνpos
  refine ⟨T, hTpos, u_star, ?_⟩
  -- Step 2: heat floor and ball floor.
  set u₀E : WA 1 := ⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩
  have hheat : UniformFloor (heatEWA (T := T) u₀E) δ₀ :=
    heatEWA_uniformFloor (T := T) hu₀ hfloor₀ hsumc hmem
  have hballFloor : UniformFloor u_star (δ₀ - δ₀ / 2) :=
    uniformFloor_on_ball hheat hu_ball
  have hδ₀half_pos : 0 < δ₀ - δ₀ / 2 := by linarith
  have hδρ : 0 < δ₀ - δ₀ / 2 := by linarith
  -- Step 3: v6 reduced core.
  exact realSlice_reducedCore_of_evenReal p u_star u₀p (cosineCoeffs u₀)
    hu0bd hδρ hheat hu_ball hsumc hmem hTpos.le hTpos hfix hER
    hβpos hαnn hμle1 hδ₀half_pos hballFloor hrecon

end ShenWork.EWA

#print axioms ShenWork.EWA.chiNeg_EWA_core_of_datum
