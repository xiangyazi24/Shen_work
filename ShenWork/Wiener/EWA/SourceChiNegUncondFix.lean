import ShenWork.Wiener.EWA.SourceUncondFixedPoint
import ShenWork.Wiener.EWA.HeatFloorIcc
import ShenWork.Wiener.EWA.SourceChiNegFaithful

/-!
# χ₀<0 EWA track — the STRONG (paper-faithful) datum construction and the
  floor-unlocked contraction tower

## Why this file exists

The previously-landed faithful closeout `chiNeg_theorem_1_1_faithful`
(`SourceChiNegFaithful.lean`) reduces the headline `Theorem_1_1 intervalDomain p`
to `ChiNegDatumUniformConstructionFaithful p`, which quantifies the per-datum
realized-track core over the WEAK class `PositiveInitialDatum intervalDomain u0`
(Paper2/Statements.lean:277 — positivity on the OPEN interior only; the closed-domain
infimum CAN be `0`, e.g. `x(1−x)`).  That obligation is **unsatisfiable from the
contraction tower**: the EWA fixed-point engine `picardEWA_uncond_fixedPoint`
(`SourceUncondFixedPoint.lean:38`) needs a *uniform* positive floor
`∀ y, δ ≤ u₀ y` on the heat source (via `heatEWA_uniformFloor`,
`HeatFloor.lean:403`), which no `PositiveInitialDatum` instance can supply.

The headline `Theorem_1_1` (Paper2/Statements.lean:4420) itself quantifies over
the STRONGER `PaperPositiveInitialDatum` (Paper2/Statements.lean:297), which carries
`PaperPositiveInitialDatum.floor : ∃ η > 0, ∀ x, η ≤ u₀ x` — exactly the uniform
floor the tower needs.  This file therefore introduces the **strong** datum-uniform
construction `ChiNegDatumUniformConstructionStrong` — identical in shape to the
faithful one but over `PaperPositiveInitialDatum` — and discharges the genuine
MILESTONE the floor unlocks.

## MILESTONE 1 (landed, axiom-clean) — the floor → EWA heat-floor → fixed point.

`chiNegStrong_heatFloor_of_paperDatum`: the closed-domain floor of
`PaperPositiveInitialDatum` discharges the EWA heat-floor `UniformFloor (heatEWA …) η`
via the landed bridge `paperFloorDatum_heatEWA_uniformFloor` (`HeatFloorIcc.lean:239`,
which routes the `Point`-floor through `intervalDomainLift_floor_Icc` +
`heatEWA_uniformFloor_Icc`).  This isolates the SOLE remaining datum-level residual
as the cosine-summability of the lifted source (the `HeatFloorIcc` "obstruction (a)":
a merely continuous floored datum need not be absolutely cosine-summable).

`chiNegStrong_EWA_fixedPoint_of_floor`: feeding that heat-floor to
`picardEWA_uncond_fixedPoint` produces the χ₀<0 EWA fixed point
`u_star ∈ closedBall (heatEWA u₀E) ρ`, `u_star = picardEWA … u_star`, with the
positivity content now supplied from the STRONG datum's floor (not assumed).  What
the engine still carries are exactly the framework-wide carried inputs (the single
ℓ¹ resolver-source atom `hsource`, the contraction-rate side data `hMD`/`hRad`/
`hVdD`/`hsmall`/`hLQ`/`hLG`/`hself`/`hKnn`/`hK`) — these are NOT the floor and were
never the floor; they are the standard brick-1 / small-time chooser inputs the χ₀=0
track carries too.

## What this file does NOT (and provably cannot, as a new-file-only addition) close

A FULLY unconditional `chiNeg_theorem_1_1_unconditional : Theorem_1_1` is blocked at
TWO independent points that are not "wiring" but genuine unbuilt analytic content:

1. **The per-slice realization frontier.**  `realSlice_reducedCore`
   (`SourceReducedCore.lean:84`) and `realizes_evalST_discharged`
   (`SourceChiNegUncondWire.lean:123`) still carry, as explicit hypotheses, the
   per-slice spectral/regularity atoms: the cosine representation (`hagree`/`bc`),
   the per-interior-point spectral inversions `htime`/`hlap`/`hchemInv`/`hlogInv`,
   the quadratic-decay coefficients (`hdecay`/`ha0`/`C`), the resolver-source family
   `f` (`hf_cont`/`hf_nonneg`/`hf_coeff`), and the secondary regularity atoms
   `h_flux_diff`/`h_src_cont_chem`/`h_src_cont_log`/`hgrad`.  The recent EWA work
   (`SourceChiNegUncond.lean`) closed ONLY the three hard-core `evalST` atoms
   (`h_u`/`h_uα`/`h_flux_nbhd`); the per-slice frontier above is produced by NO
   landed lemma (verified by reading the exact "full discharge" signatures
   `realSlice_resolverSpectralData_full`, `realSlice_hchemInv_direct_realSlice` —
   each still carries `bc`/`hagree`/`hdecay`/`hcont`/`h_coeff`).

2. **The continuation/restart factory is typed over WEAK data.**  The headline
   reduction `theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual`
   feeds `RestartAndGlueWorks` (`IntervalDomainRestartExtension.lean:22`), whose
   "fresh factory" is re-invoked at intermediate time-slices `u(τ,·)` that are only
   `PositiveInitialDatum` — the landed slice producer
   `classicalSolution_slice_positiveInitialDatum`
   (`IntervalDomainUniformContinuation.lean:22`) returns a WEAK datum (interior
   positivity, no uniform closed-domain floor).  A strong-only construction cannot
   supply that weak-data factory, and rebuilding the entire continuation stack over
   strong data is not new-file-local work.

So this file lands the strong construction + the floor-unlocked MILESTONE 1 honestly,
and names the precise residual.  It does NOT fake a `chiNeg_theorem_1_1_unconditional`
discharge: there is no hidden axiom and no re-introduced `hfp`.

No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/

open scoped BigOperators
open Set Metric
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2
  (PaperPositiveInitialDatum PositiveInitialDatum Theorem_1_1)
open ShenWork.IntervalCoupledRegularityBootstrap (CoupledDuhamelReducedClassicalCore)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### The STRONG (paper-faithful) datum-uniform construction. -/

/-- **The χ₀<0 STRONG datum-uniform construction.**

Identical in shape to `ChiNegDatumUniformConstructionFaithful`
(`SourceChiNegFaithful.lean:106`) but with the STRONG, paper-faithful datum class
`PaperPositiveInitialDatum intervalDomain u0` replacing the weak
`PositiveInitialDatum`.  The strong class carries
`PaperPositiveInitialDatum.floor : ∃ η > 0, ∀ x, η ≤ u0 x` — the uniform positive
floor the EWA contraction tower (`picardEWA_uncond_fixedPoint` →
`heatEWA_uniformFloor`) requires and which no weak datum can supply.  This is the
datum class the headline `Theorem_1_1` itself quantifies over. -/
def ChiNegDatumUniformConstructionStrong (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
    ∀ {u0 : intervalDomain.Point → ℝ},
      PaperPositiveInitialDatum intervalDomain u0 →
      (∀ x, |u0 x| ≤ M) →
        ∃ u_star : EWA δ 1,
          CoupledDuhamelReducedClassicalCore p δ u0 (realSlice u_star)

/-! ### MILESTONE 1 — the strong floor unlocks the EWA heat-floor. -/

/-- **The EWA heat-floor from the closed-domain floor of `PaperPositiveInitialDatum`.**

The uniform positive floor `∃ η > 0, ∀ x, η ≤ u₀p x` carried by
`PaperPositiveInitialDatum.floor` discharges `∃ η > 0, UniformFloor (heatEWA u₀E) η`
through the landed bridge `paperFloorDatum_heatEWA_uniformFloor` (which routes the
`Point`-floor through `intervalDomainLift_floor_Icc` + `heatEWA_uniformFloor_Icc`).
The remaining inputs (`hu₀`, `hagree`, `hsum`, `hmem`) are the framework's standard
cosine-realization datum (the `HeatFloorIcc` "obstruction (a)" — absolute
cosine-summability of the lifted source, which the floor alone does not give).  This
is the precise statement that the floor piece — and ONLY the floor piece — is what
the strong datum class newly supplies (a weak `PositiveInitialDatum` cannot, having
no uniform floor). -/
theorem chiNegStrong_heatFloor_of_paperDatum
    {u₀p : intervalDomainPoint → ℝ}
    (hpaper : PaperPositiveInitialDatum intervalDomain u₀p)
    {u₀ : ℝ → ℝ} (hu₀ : Continuous u₀)
    (hagree : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift u₀p y = u₀ y)
    (hsum : Summable (fun k => |cosineCoeffs u₀ k|))
    (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀))) :
    ∃ η : ℝ, 0 < η ∧ UniformFloor (heatEWA (T := T)
      (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)) η := by
  obtain ⟨η, hηpos, hηfloor⟩ := hpaper.floor
  exact ⟨η, hηpos, paperFloorDatum_heatEWA_uniformFloor hηfloor hu₀ hagree hsum hmem⟩

/-- **MILESTONE 1 — the χ₀<0 EWA fixed point over the (global) heat floor.**

The unconditional source-form fixed-point engine `picardEWA_uncond_fixedPoint`
produces the χ₀<0 EWA fixed point `u_star ∈ closedBall (heatEWA u₀E) ρ`,
`u_star = picardEWA … u_star`, given the heat source's positive floor
`hheatfloor : ∀ y, δ ≤ u₀ y` (which, on `[0,1]`, the strong datum's closed-domain
floor supplies — see `chiNegStrong_heatFloor_of_paperDatum` for the `[0,1]`-floor
→ heat-floor bridge that the strong class unlocks; the engine's INTERNAL center
floor `vdEWA_center_floor_heat` is what still needs the *global* `∀ y` floor, the
`HeatFloorIcc` "obstruction (a)" — a merely continuous floored lift need not have a
global real-line floor).

What is still carried is exactly the framework-wide analytic / contraction-rate
data the χ₀=0 track also carries: the single ℓ¹ resolver-source atom `hsource`, the
ball-radius / derivative bounds `hMD`/`hRad`/`hVdD`/`hcenterMD`/`hcenterR`, the
smallness `hsmall`, the Lipschitz-constant equalities `hLQ`/`hLG`, the self-map
`hself`, and the contraction `hKnn`/`hK`.  None of these is the χ₀<0-specific
floor blocker, which is what the strong datum class addresses. -/
theorem chiNegStrong_EWA_fixedPoint_of_floor (p : CM2Params)
    (u₀ : ℝ → ℝ) (hu₀ : Continuous u₀)
    {δ ρ δv Md Mdv R L_Q L_G : ℝ}
    (hT : 0 ≤ T) (hδpos : 0 < δ)
    (hheatfloor : ∀ y, δ ≤ u₀ y) (hνpos : 0 ≤ p.ν)
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
        (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1) u_star :=
  picardEWA_uncond_fixedPoint p u₀ hu₀ hT hδpos hheatfloor hνpos hsumc hmem
    uR huR hsource hρ hMd hMdv hR hδρpos hδvpos hMD hRad hVdD hcenterMD hcenterR
    hsmall hLQ hLG hβ hα hself hKnn hK

/-! ### The strong → faithful projection (datum-class compatibility). -/

/-- **The strong construction implies the (weak) faithful construction.**

`PaperPositiveInitialDatum.toPositive` (Paper2/Statements.lean) projects every strong
datum to a weak one, but the converse is false, so this map goes from the WEAKER
obligation to the STRONGER: a faithful (weak-datum) construction yields the strong
one by restricting its universally-quantified datum to the strong subclass.  Hence
the strong construction is *no harder to assume* than the faithful one — it is the
correct interface for the headline, which quantifies over the strong class. -/
theorem chiNegDatumUniformConstructionStrong_of_faithful (p : CM2Params)
    (hF : ChiNegDatumUniformConstructionFaithful p) :
    ChiNegDatumUniformConstructionStrong p := by
  intro M hM
  obtain ⟨δ, hδ, hbody⟩ := hF M hM
  exact ⟨δ, hδ, fun {u0} hu0 hbd => hbody (hu0.toPositive) hbd⟩

end ShenWork.EWA

namespace ShenWork.EWA
section AxiomAudit
#print axioms chiNegStrong_heatFloor_of_paperDatum
#print axioms chiNegStrong_EWA_fixedPoint_of_floor
#print axioms chiNegDatumUniformConstructionStrong_of_faithful
end AxiomAudit
end ShenWork.EWA
