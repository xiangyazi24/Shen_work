import ShenWork.Wiener.EWA.SourceCenterFloorHeat

/-!
# EWA capstone (χ₀<0 Route A′) — the fixed point with NO carried positivity hypothesis

`picardEWA_abs_fixedPoint_vdDischarged` (`SourceVdFloorDischarge.lean`) produces the χ₀<0
fixed point but carries the center floor `hcenter` and the heat floor `hheat`.
`vdEWA_center_floor_heat` (`SourceCenterFloorHeat.lean`) discharges `hcenter` from standard
u₀ data + the single ℓ¹ atom `hsource`; `heatEWA_uniformFloor` discharges `hheat`.

This file composes the two: the χ₀<0 source-form fixed point holds with NO carried floor
hypothesis — only standard u₀ data (`hu₀`/`hδpos`/`hfloor`/`hνpos`/`hsumc`/`hmem`), the single
ℓ¹ resolver-source atom `hsource` (the framework-wide carried analytic input, same kind χ₀=0
carries), the smallness `hsmall`, and the standard brick-1 side-data / self-map / contraction
that the small-time chooser supplies.
-/

open scoped BigOperators
open Set Metric
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- **THE χ₀<0 SOURCE-FORM FIXED POINT — NO CARRIED POSITIVITY HYPOTHESIS.**

Composes `vdEWA_center_floor_heat` (the unconditional heat-center floor, modulo the single
ℓ¹ atom `hsource`) and `heatEWA_uniformFloor` (the heat floor) into
`picardEWA_abs_fixedPoint_vdDischarged`.  The χ₀<0 Picard map `picardEWA` has a fixed point
`u* ∈ closedBall (heatEWA u₀E) ρ` with the positivity content fully discharged: the only
analytic input beyond the standard u₀ datum is `hsource`, the realized-source ℓ¹ summability
that the framework carries everywhere (including the χ₀=0 track). -/
theorem picardEWA_uncond_fixedPoint (p : CM2Params) (u₀ : ℝ → ℝ) (hu₀ : Continuous u₀)
    {δ ρ δv Md Mdv R L_Q L_G : ℝ}
    (hT : 0 ≤ T) (hδpos : 0 < δ) (hfloor : ∀ y, δ ≤ u₀ y) (hνpos : 0 ≤ p.ν)
    (hsumc : Summable (fun k => |cosineCoeffs u₀ k|))
    (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀)))
    (uR : ℝ → intervalDomainPoint → ℝ)
    (huR : uR = fun t pt => unitIntervalCosineHeatValue t (cosineCoeffs u₀) (pt.1))
    (hsource : ∀ τ : TimeDom T, ResolverSourceSummable p (uR τ.1))
    (hρ : 0 ≤ ρ) (hMd : 0 ≤ Md) (hMdv : 0 ≤ Mdv) (hR : 0 ≤ R)
    (hδρpos : 0 < δ - ρ) (hδvpos : 0 < δv)
    (hMD : ∀ u ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)) ρ, ‖GWA.gDeriv u‖ ≤ Md)
    (hRad : ∀ u ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)) ρ, ‖u‖ ≤ R)
    (hVdD : ∀ u ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)) ρ,
      ‖GWA.gDeriv (vdEWA p.μ p.ν p.γ p.hμ u)‖ ≤ Mdv)
    (hcenterMD : ‖GWA.gDeriv (heatEWA (T := T)
        (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1))‖ ≤ Md)
    (hcenterR : ‖heatEWA (T := T)
        (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)‖ ≤ R)
    (hsmall : (GWA.resolverGainConst p.μ * (|p.ν| *
          ((Nat.floor p.γ + 1 : ℝ) * R ^ ((Nat.floor p.γ + 1) - 1)
              * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md
            + R ^ (Nat.floor p.γ + 1)
              * negLipConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))) * ρ
        ≤ 1 - δv)
    (hLQ : L_Q = (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
              (R ^ (Nat.floor p.γ + 1)
                * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))))
            * negNormConst p.β δv Mdv * 1
          + R * negNormConst p.β δv Mdv
            * (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
              ((Nat.floor p.γ + 1 : ℝ) * R ^ ((Nat.floor p.γ + 1) - 1)
                  * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md
                + R ^ (Nat.floor p.γ + 1)
                  * negLipConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))))
          + R * (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
              (R ^ (Nat.floor p.γ + 1)
                * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))))
            * (negLipConst p.β δv Mdv * (GWA.resolverGainConst p.μ * (|p.ν| *
                ((Nat.floor p.γ + 1 : ℝ) * R ^ ((Nat.floor p.γ + 1) - 1)
                    * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md
                  + R ^ (Nat.floor p.γ + 1)
                    * negLipConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md)))))
    (hLG : L_G = R * (|p.b| * ((Nat.floor p.α + 1 : ℝ) * R ^ ((Nat.floor p.α + 1) - 1)
              * negNormConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md
            + R ^ (Nat.floor p.α + 1)
              * negLipConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md))
          + (|p.a| * ‖(1 : EWA T 1)‖ + |p.b| *
              (R ^ (Nat.floor p.α + 1)
                * negNormConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md)))
    (hβ : 0 < p.β) (hα : 0 ≤ p.α)
    (hself : MapsTo (picardEWA p p.μ p.ν p.γ p.hμ hT
        (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1))
      (Metric.closedBall (heatEWA (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)) ρ)
      (Metric.closedBall (heatEWA (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)) ρ))
    (hKnn : (0 : ℝ) ≤ |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T)
    (hK : |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T < 1) :
    ∃ u_star ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)) ρ,
      u_star = picardEWA p p.μ p.ν p.γ p.hμ hT
        (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1) u_star := by
  -- the heat floor and the (now unconditional) center floor, both from u₀ data.
  have hheat : UniformFloor (heatEWA (T := T)
      (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)) δ :=
    heatEWA_uniformFloor hu₀ hfloor hsumc hmem
  have hcenter : UniformFloor (1 + vdEWA p.μ p.ν p.γ p.hμ
      (heatEWA (T := T) (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1))) 1 :=
    vdEWA_center_floor_heat p u₀ hu₀ hδpos hfloor hνpos hsumc hmem uR huR hsource
  exact picardEWA_abs_fixedPoint_vdDischarged hT
    (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1) hρ hMd hMdv hR hδρpos hδvpos hheat
    hMD hRad hVdD hcenterMD hcenterR hcenter hsmall hLQ hLG hβ hα hself hKnn hK

end ShenWork.EWA
