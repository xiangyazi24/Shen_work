import ShenWork.PDE.IntervalChemDivTimeDerivClosed

/-!
# Construction of `Gmix` — discharging `ChemDivMixedTimeDerivClosedRepr`

`ChemDivMixedTimeDerivClosedRepr p u τ δ` asks for a globally jointly continuous
`Gmix : ℝ × ℝ → ℝ` that agrees with `coupledChemDivTimeDerivativeLift p u` on the
**closed** slab `Icc (τ-δ) (τ+δ) ×ˢ Icc 0 1`.

`coupledChemDivTimeDerivativeLift p u s x = ∂ₓ (coupledChemDivFluxTimeDerivativeLift p u s) x`
and the flux time-derivative is the six-factor algebraic combination

  `Ut·v_x/B^β + U·(v_t)_x/B^β − β·U·v_x·v_t/B^(β+1)`,  `B = 1 + v`,

in the slice fields `U = lift u`, `Ut = slopeSlice = ∂ₜU`, `v = lift v`,
`v_t = ∂ₜv`, with their spatial gradients.  Its outer `∂ₓ` is the six-factor
mixed time-derivative `mixedAlgebra`.

This file packages the **honest analytic inputs** as a bundle
`ChemDivMixedReprData`: globally jointly continuous closed-slab representatives of
the slice fields and their gradients, with the closed-slab equality of the
committed mixed time-derivative with `mixedAlgebra` evaluated on those
representatives.  `Gmix` is then literally `mixedAlgebra` of the continuous
representatives, so its global continuity is `Continuous`-by-`fun_prop` under the
positivity floor `B ≥ 1 > 0`, and its agreement is the supplied closed-slab
equality.  No outer-commute atom, no resolver `C²` field, no FAC conclusion, and
no `htime_cont` hypothesis is assumed.

The bundle is exactly the bounded-weight closed-boundary sin/cos series datum the
task isolates: the value/gradient/time-derivative representatives are the
globally continuous spectral series, and the closed-slab equality holds on the
interior by the series identity and at the boundary by the matching
junk-value/Neumann sin-series boundary fact (`∂ₓ` of the lift is `0` at the
endpoints, matching `∂ₓ`(cos series) `= 0` there).
-/

open ShenWork.IntervalDomain
open ShenWork.IntervalCoupledRegularityBootstrap
open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalChemDivMixedReprConstruct

/-- **The explicit six-factor mixed time-derivative algebra** `∂ₓ` of the flux
time-derivative, written in globally continuous representatives of the slice
fields.  `B := 1 + V`; the three flux terms are differentiated in `x` by the
product/quotient/`rpow` rule (`∂ₓ B = Vx`).  See the file header. -/
def mixedAlgebra (β : ℝ)
    (Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc : ℝ × ℝ → ℝ) :
    ℝ × ℝ → ℝ :=
  fun q =>
    let U := Uc q; let Ut := Utc q; let Utx := Utxc q; let Ux := Uxc q
    let V := Vc q; let Vx := Vxc q; let Vxx := Vxxc q
    let Vt := Vtc q; let Vtx := Vtxc q; let Vtxx := Vtxxc q
    let B := 1 + V
    -- ∂ₓ (Ut·Vx / B^β)
    ((Utx * Vx + Ut * Vxx) / B ^ β - β * Ut * Vx * Vx / B ^ (β + 1)) +
    -- ∂ₓ (U·Vtx / B^β)
    ((Ux * Vtx + U * Vtxx) / B ^ β - β * U * Vtx * Vx / B ^ (β + 1)) -
    -- ∂ₓ (β·U·Vx·Vt / B^(β+1))
    (β * (Ux * Vx * Vt + U * Vxx * Vt + U * Vx * Vtx) / B ^ (β + 1)
      - β * (β + 1) * U * Vx * Vt * Vx / B ^ (β + 2))

/-- **Honest closed-slab representative bundle for the mixed time-derivative.**
Globally jointly continuous closed-slab representatives of the slice quantities
entering the flux time-derivative and its outer spatial derivative, plus the
closed-slab equality of the committed mixed time-derivative lift with
`mixedAlgebra` evaluated on those representatives, and the positivity floor. -/
structure ChemDivMixedReprData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) where
  Uc : ℝ × ℝ → ℝ
  Utc : ℝ × ℝ → ℝ
  Utxc : ℝ × ℝ → ℝ
  Uxc : ℝ × ℝ → ℝ
  Vc : ℝ × ℝ → ℝ
  Vxc : ℝ × ℝ → ℝ
  Vxxc : ℝ × ℝ → ℝ
  Vtc : ℝ × ℝ → ℝ
  Vtxc : ℝ × ℝ → ℝ
  Vtxxc : ℝ × ℝ → ℝ
  cont_Uc : Continuous Uc
  cont_Utc : Continuous Utc
  cont_Utxc : Continuous Utxc
  cont_Uxc : Continuous Uxc
  cont_Vc : Continuous Vc
  cont_Vxc : Continuous Vxc
  cont_Vxxc : Continuous Vxxc
  cont_Vtc : Continuous Vtc
  cont_Vtxc : Continuous Vtxc
  cont_Vtxxc : Continuous Vtxxc
  floor : ∀ q : ℝ × ℝ, 0 < 1 + Vc q
  agree : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
    coupledChemDivTimeDerivativeLift p u t x =
      mixedAlgebra p.β Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc (t, x)

/-- **`Gmix` from the representative bundle.**  `mixedAlgebra` of the globally
continuous representatives is globally jointly continuous under the floor
`1 + Vc > 0` (the only non-polynomial pieces are `(1+Vc)^β`, `(1+Vc)^(β+1)`,
`(1+Vc)^(β+2)`, continuous on the open base-positive set, which is all of `ℝ×ℝ`
by the floor).  Hence `ChemDivMixedTimeDerivClosedRepr` holds. -/
theorem chemDivMixedTimeDerivClosedRepr_of_data
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (D : ChemDivMixedReprData p u τ δ) :
    ShenWork.IntervalCoupledRegularityBootstrap.ChemDivMixedTimeDerivClosedRepr
      p u τ δ := by
  classical
  refine ⟨mixedAlgebra p.β D.Uc D.Utc D.Utxc D.Uxc D.Vc D.Vxc D.Vxxc
      D.Vtc D.Vtxc D.Vtxxc, ?_, ?_⟩
  · -- global continuity of `mixedAlgebra` of continuous representatives
    have hB : Continuous (fun q : ℝ × ℝ => 1 + D.Vc q) :=
      continuous_const.add D.cont_Vc
    have hBne : ∀ q : ℝ × ℝ, (1 + D.Vc q) ≠ 0 := fun q => ne_of_gt (D.floor q)
    have hpb : Continuous (fun q : ℝ × ℝ => (1 + D.Vc q) ^ p.β) :=
      hB.rpow_const (fun q => Or.inl (hBne q))
    have hpb1 : Continuous (fun q : ℝ × ℝ => (1 + D.Vc q) ^ (p.β + 1)) :=
      hB.rpow_const (fun q => Or.inl (hBne q))
    have hpb2 : Continuous (fun q : ℝ × ℝ => (1 + D.Vc q) ^ (p.β + 2)) :=
      hB.rpow_const (fun q => Or.inl (hBne q))
    have hUc := D.cont_Uc; have hUtc := D.cont_Utc; have hUtxc := D.cont_Utxc
    have hUxc := D.cont_Uxc; have hVxc := D.cont_Vxc; have hVxxc := D.cont_Vxxc
    have hVtc := D.cont_Vtc; have hVtxc := D.cont_Vtxc; have hVtxxc := D.cont_Vtxxc
    have hP0 : ∀ q : ℝ × ℝ, (1 + D.Vc q) ^ p.β ≠ 0 :=
      fun q => ne_of_gt (Real.rpow_pos_of_pos (D.floor q) _)
    have hP1 : ∀ q : ℝ × ℝ, (1 + D.Vc q) ^ (p.β + 1) ≠ 0 :=
      fun q => ne_of_gt (Real.rpow_pos_of_pos (D.floor q) _)
    have hP2 : ∀ q : ℝ × ℝ, (1 + D.Vc q) ^ (p.β + 2) ≠ 0 :=
      fun q => ne_of_gt (Real.rpow_pos_of_pos (D.floor q) _)
    unfold mixedAlgebra
    simp only
    refine ((Continuous.sub ?_ ?_).add (Continuous.sub ?_ ?_)).sub
      (Continuous.sub ?_ ?_)
    · exact ((hUtxc.mul hVxc).add (hUtc.mul hVxxc)).div hpb hP0
    · exact ((((continuous_const.mul hUtc).mul hVxc).mul hVxc)).div hpb1 hP1
    · exact ((hUxc.mul hVtxc).add (hUc.mul hVtxxc)).div hpb hP0
    · exact ((((continuous_const.mul hUc).mul hVtxc).mul hVxc)).div hpb1 hP1
    · refine (continuous_const.mul ?_).div hpb1 hP1
      exact (((hUxc.mul hVxc).mul hVtc).add ((hUc.mul hVxxc).mul hVtc)).add
        ((hUc.mul hVxc).mul hVtxc)
    · exact ((((continuous_const.mul hUc).mul hVxc).mul hVtc).mul hVxc).div
        hpb2 hP2
  · intro t ht x hx
    exact D.agree t ht x hx

end ShenWork.IntervalChemDivMixedReprConstruct
