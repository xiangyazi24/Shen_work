import ShenWork.PDE.IntervalChemDivFACCommuteDischarge

/-!
# Closed-slab joint continuity of the chem-div mixed time-derivative lift

This file discharges the `htime_cont` regularity field of the χ₀<0 FAC chain:

  `ContinuousOn (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
     (Icc (τ-δ) (τ+δ) ×ˢ Icc 0 1)`.

`coupledChemDivTimeDerivativeLift = ∂ₓ` of the flux time-derivative lift, which on
`[0,1]` is a finite algebraic combination of the bounded-weight Neumann
cosine/sine series for `u`, `∂ₜu`, `v`, `∂ₓv`, `∂ₓ∂ₜv`, and `(1+v)^{-β}`.  Each
spatial-gradient factor is `-∑ (nπ)·coeffₙ·sin(nπx)`, which is continuous on the
**closed** `Icc 0 1` (sin entire) and converges uniformly under the bounded-weight
summability `∑ (nπ)|coeffₙ| < ∞`.  Hence the combination is jointly continuous on
the closed slab.

The honest analytic input isolated here is a single globally-jointly-continuous
spectral representative `Gmix : ℝ × ℝ → ℝ` of the mixed time-derivative that
agrees with the lift on the closed spatial domain inside a time window — exactly
the boundary-extension datum the bounded-weight sin/cos series provide.  Given
that representative, the closed-slab continuity is transferred by the committed
frontier `congr_of_eventuallyEq` technique (mirroring
`mildSolution_timeDeriv_jointContinuousOn_closed`).
-/

open ShenWork.IntervalDomain
open ShenWork.IntervalResolverJointC2PhysicalConcrete
open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- **Closed-slab spectral representative of the mixed time-derivative.**

`Gmix` is the globally jointly continuous flux mixed time-derivative built from
the bounded-weight sin/cos series; `agree` records that it equals the committed
`coupledChemDivTimeDerivativeLift` lift on the closed spatial domain throughout
the time window `Ioo (τ-δ) (τ+δ)`.  No outer-commute atom, no resolver `C²`
field, and no FAC conclusion is assumed. -/
def ChemDivMixedTimeDerivClosedRepr
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) : Prop :=
  ∃ Gmix : ℝ × ℝ → ℝ, Continuous Gmix ∧
    ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
      coupledChemDivTimeDerivativeLift p u t x = Gmix (t, x)

/-- **`htime_cont` from the closed-slab spectral representative.**

The committed frontier technique: the mixed time-derivative agrees with the
globally continuous `Gmix` on `Ioo (τ-δ) (τ+δ) ×ˢ Icc 0 1`, so it inherits joint
`ContinuousOn` on that closed slab; restrict to the compact `Icc`. -/
theorem chemDivMixedTimeDeriv_jointContinuousOn_closed
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (H : ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨Gmix, hGmix_cont, hagree⟩ := H
  set S := Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1 with hS
  intro q hq
  -- On `S`, the mixed time-derivative agrees with the continuous `Gmix`.
  have hagree_on : ∀ r ∈ S,
      Function.uncurry (coupledChemDivTimeDerivativeLift p u) r = Gmix r := by
    intro ⟨t, x⟩ hr
    obtain ⟨htr, hxr⟩ := mem_prod.1 hr
    simpa [Function.uncurry] using hagree t htr x hxr
  have hGwithin : ContinuousWithinAt Gmix S q :=
    hGmix_cont.continuousWithinAt
  have heq : (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      =ᶠ[𝓝[S] q] Gmix := by
    filter_upwards [self_mem_nhdsWithin] with r hr using hagree_on r hr
  exact (hGwithin.congr_of_eventuallyEq heq (hagree_on q hq))

/-- **χ₀<0 FAC factor inputs with `htime_cont` discharged.**

Assembles the full FAC factor joint-`C²` inputs from the resolver physical joint
`C²` data, the `u`-side positivity/continuity, the source/Picard-`C²` slab data,
and — in place of the previously-open `htime_cont` field — the closed-slab
spectral representative `ChemDivMixedTimeDerivClosedRepr`.  The mixed
time-derivative continuity is now produced internally by
`chemDivMixedTimeDeriv_jointContinuousOn_closed`, so `htime_cont` is no longer a
slab hypothesis. -/
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt)
    (hu_cont : ∀ s : ℝ, Continuous (u s))
    (hu_nonneg : ∀ s : ℝ, ∀ x : intervalDomainPoint, 0 ≤ u s x)
    (other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
      (∀ᶠ s in 𝓝 τ,
        ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
        ContDiffAt ℝ 2 (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)) ∧
      ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    CoupledChemDivFluxFactorJointC2Inputs p u :=
  coupledChemDivFluxFactorJointC2Inputs_of_physical_commuteDischarged
    H hu_cont hu_nonneg (fun τ => by
      rcases other τ with ⟨δ, hδ, hsrc, hu_c2, hrepr⟩
      exact ⟨δ, hδ, hsrc, hu_c2,
        chemDivMixedTimeDeriv_jointContinuousOn_closed hrepr⟩)

end ShenWork.IntervalCoupledRegularityBootstrap
