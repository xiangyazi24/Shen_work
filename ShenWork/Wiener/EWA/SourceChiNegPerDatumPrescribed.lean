/-
  ShenWork/Wiener/EWA/SourceChiNegPerDatumPrescribed.lean

  **Per-datum Core at a PRESCRIBED time T, from prescribed-T FP + v6.**

  Combines:
  - `picardEWA_clean_fixedPoint_evenReal_prescribedT` → fixed point at T
  - `realSlice_reducedCore_of_evenReal` (v6) → Core at T

  Output: `∃ u_star : EWA T 1, Core p T u₀p (realSlice u_star)`
  at a GIVEN T (not existential). This is the key piece for the uniform
  construction: all datums get Core at the SAME T.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceFixedPointEvenRealPrescribed
import ShenWork.Wiener.EWA.SourceReducedCoreWireV6EvenReal

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.EWA

/-- **Per-datum Core at a PRESCRIBED time T.**

Same as `chiNeg_EWA_core_of_datum` but T is provided externally. The
conditions on T (contraction + self-map) use `normBound ≥ ‖u₀E‖`,
enabling the uniform construction where normBound = WM is shared. -/
theorem chiNeg_EWA_core_of_datum_prescribedT (p : CM2Params)
    (u₀ : ℝ → ℝ) (hu₀ : Continuous u₀)
    {δ₀ : ℝ} (hδ₀pos : 0 < δ₀) (hfloor₀ : ∀ y, δ₀ ≤ u₀ y)
    (hsumc : Summable (fun k => |cosineCoeffs u₀ k|))
    (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀)))
    {Mu0 : ℝ} (hu0bd : ∀ n, |cosineCoeffs u₀ n| ≤ Mu0)
    (u₀p : intervalDomainPoint → ℝ)
    (hrecon : ∀ x : intervalDomainPoint,
      u₀p x = ∑' n, cosineCoeffs u₀ n * cosineMode n x.1)
    (hβpos : 0 < p.β) (hαnn : 0 ≤ p.α) (hμle1 : p.μ ≤ 1)
    {normBound : ℝ} (hnormBound : 0 ≤ normBound)
    (hnorm : ‖(⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)‖ ≤ normBound)
    (T : ℝ) (hTpos : 0 < T)
    (hKlt : |p.χ₀| * C₀ * CleanFPConst.L_Q p normBound δ₀ * Real.sqrt T
        + CleanFPConst.L_G p normBound δ₀ * T < 1)
    (hsmall : |p.χ₀| * C₀ * CleanFPConst.M_Q p normBound δ₀ * Real.sqrt T
        + CleanFPConst.M_G p normBound δ₀ * T ≤ δ₀ / 2) :
    ∃ u_star : EWA T 1,
      CoupledDuhamelReducedClassicalCore p T u₀p (realSlice u_star) := by
  have hνpos : 0 ≤ p.ν := le_of_lt p.hν
  -- Step 1: prescribed-T clean EvenReal fixed point.
  obtain ⟨u_star, hu_ball, hER, hfix⟩ :=
    picardEWA_clean_fixedPoint_evenReal_prescribedT p u₀ hu₀ hδ₀pos hfloor₀
      hsumc hmem hβpos hνpos hnormBound hnorm T hTpos hKlt hsmall
  -- Step 2: heat floor and ball floor.
  set u₀E : WA 1 := ⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩
  have hheat : UniformFloor (heatEWA (T := T) u₀E) δ₀ :=
    heatEWA_uniformFloor (T := T) hu₀ hfloor₀ hsumc hmem
  have hballFloor : UniformFloor u_star (δ₀ - δ₀ / 2) :=
    uniformFloor_on_ball hheat hu_ball
  have hδ₀half_pos : 0 < δ₀ - δ₀ / 2 := by linarith
  -- Step 3: v6 reduced core.
  exact ⟨u_star, realSlice_reducedCore_of_evenReal p u_star u₀p (cosineCoeffs u₀)
    hu0bd hδ₀half_pos hheat hu_ball hsumc hmem hTpos.le hTpos hfix hER
    hβpos hαnn hμle1 hδ₀half_pos hballFloor hrecon⟩

end ShenWork.EWA
