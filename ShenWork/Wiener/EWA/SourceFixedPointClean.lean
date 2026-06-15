import ShenWork.Wiener.EWA.SourceFixedPointAbs
import ShenWork.Wiener.EWA.HeatFloor
import ShenWork.PDE.IntervalChemFluxLipschitz

/-!
# EWA brick (χ₀<0 Route A′) — THE TRULY-CLEAN χ₀<0 ABSOLUTE FIXED POINT on STANDARD DATA

This file assembles `picardEWA_clean_fixedPoint`: the χ₀<0 source-form fixed point
conditional **only on standard datum facts** (`u₀` continuous, `u₀ ≥ δ > 0`, summable
cosine coefficients, `CM2Params` positivity, small `T`), discharging *all* the carried
hypotheses of `picardEWA_abs_fixedPoint` (`SourceFixedPointAbs.lean`) via the committed
bricks:

* `heatEWA_uniformFloor` (`HeatFloor.lean`) discharges the heat floor `hheat`;
* the brick-1 norm lemmas (`vxEWA_norm_le`, `qFactor_norm_le`, `growthFactor_norm_le`,
  `vFieldEWA_norm_le`, `norm_gDeriv_apply_le`, `norm_incl_apply_le`) furnish the uniform
  side-data `Md`, `Mdv`, `M_Q`, `M_G` on the ball `B = closedBall (heatEWA u₀E) ρ`;
* `picardEWA_mapsTo` (`SourceSelfMap.lean`) discharges `hself` from the smallness
  `|χ₀|·C₀√T·M_Q + T·M_G ≤ ρ`;
* `exists_small_contraction_time` (`IntervalChemFluxLipschitz.lean`) chooses `T` small
  enough for BOTH the contraction `|χ₀|·C₀√T·L_Q + L_G·T < 1` and the self-map smallness;
* the brick-1 Lipschitz discharge of `hLipQ`/`hLipG` lives inside `picardEWA_abs_fixedPoint`.

## The one honest carried hypothesis

The `1+v` positivity floor `UniformFloor (1 + vdEWA μ ν γ hμ u) δv` — the EWA analogue
of the heat floor for the resolved chemo-signal — is NOT committed at the EWA level.  At
the real-space level the resolver positivity `R(u) ≥ 0` (hence `1+R ≥ 1`) IS proved
(`IntervalResolverPositivity.lean`, O1), but its transfer to the EWA element `vdEWA`
needs the resolver eval bridge (the `vFieldEWA` analogue of `heatEWA_evalST_eq_cosineHeatValue`),
which is not in the tree.  We therefore carry it as the single NAMED hypothesis `hVdFloor`,
exactly as `hheat` was carried before `HeatFloor.lean` closed it.  Everything else collapses
to the standard datum facts.
-/

open scoped BigOperators
open Set Metric
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalNeumannFullKernel

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### The unit norm is `T`-independent (`= 1`). -/

/-- `‖(1 : EWA T 1)‖ = 1` for `0 ≤ T`.  The unit is `gOne` (`1` at `n=0`, else `0`), so its
weighted Wiener norm is `gWeight 1 0 · ‖(1 : CT T)‖ = 1 · 1 = 1` (`gWeight 1 0 = 1` and the
sup norm of the constant `1` on the nonempty compact `[0,T]` is `1`). -/
theorem norm_one_EWA {T : ℝ} (hT : 0 ≤ T) : ‖(1 : EWA T 1)‖ = 1 := by
  haveI : Nonempty (TimeDom T) := ⟨⟨0, Set.mem_Icc.mpr ⟨le_refl 0, hT⟩⟩⟩
  rw [GWA.norm_def, GWA.gNorm]
  rw [tsum_eq_single (0 : ℤ)]
  · have hone : ((1 : EWA T 1).toFun 0) = (1 : CT T) := by
      change GWA.gOne (0 : ℤ) = (1 : CT T); simp [GWA.gOne]
    rw [hone, norm_one, GWA.gWeight, mul_one]
    norm_num
  · intro n hn
    have hzero : ((1 : EWA T 1).toFun n) = (0 : CT T) := by
      change GWA.gOne n = (0 : CT T); rw [GWA.gOne, if_neg hn]
    rw [hzero, norm_zero, mul_zero]

/-! ### Nonnegativity of the Γ-combination constants. -/

/-- `0 ≤ negNormConst s δ Md` for `s,δ > 0`, `Md ≥ 0`.  All Γ-factors are positive
(`Real.Gamma_pos_of_pos`) and the remaining factors are nonnegative powers / squares. -/
theorem negNormConst_nonneg {s δ Md : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hMd : 0 ≤ Md) :
    0 ≤ negNormConst s δ Md := by
  rw [negNormConst]
  have h0 : 0 < Real.Gamma s := Real.Gamma_pos_of_pos hs
  have h1 : 0 < Real.Gamma (s + 1) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : 0 < Real.Gamma (s + 2) := Real.Gamma_pos_of_pos (by linarith)
  have hδi : 0 < 1 / δ := by positivity
  positivity

/-- `0 ≤ negLipConst s δ Md` for `s,δ > 0`, `Md ≥ 0` (Γ-factors `Γ(s+1),Γ(s+2),Γ(s+3)`). -/
theorem negLipConst_nonneg {s δ Md : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hMd : 0 ≤ Md) :
    0 ≤ negLipConst s δ Md := by
  rw [negLipConst]
  have h0 : 0 < Real.Gamma s := Real.Gamma_pos_of_pos hs
  have h1 : 0 < Real.Gamma (s + 1) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : 0 < Real.Gamma (s + 2) := Real.Gamma_pos_of_pos (by linarith)
  have h3 : 0 < Real.Gamma (s + 3) := Real.Gamma_pos_of_pos (by linarith)
  have hδi : 0 < 1 / δ := by positivity
  positivity

/-! ### Side-data norm lemmas composed from the committed brick-1 bounds. -/

/-- Uniform `gDeriv` bound on the ball: `‖gDeriv (vdEWA u)‖ ≤ π · ‖vFieldEWA u‖`, via the
`gDeriv` (`π`) and `incl` (`≤1`) operator norms.  Composed with `vFieldEWA_norm_le` this
gives the `Mdv` side-data. -/
theorem vdEWA_gDeriv_norm_le {μ ν γ δ Md R : ℝ} (hμ : 0 < μ) {u : EWA T 1} (hγ : 0 ≤ γ)
    (hδpos : 0 < δ) (hMd : 0 ≤ Md) (hu_floor : UniformFloor u δ)
    (huD : ‖GWA.gDeriv u‖ ≤ Md) (huR : ‖u‖ ≤ R) (hR : 0 ≤ R) :
    ‖GWA.gDeriv (vdEWA μ ν γ hμ u)‖
      ≤ Real.pi * (GWA.resolverGainConst μ * (|ν| *
          (R ^ (Nat.floor γ + 1) * negNormConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md))) := by
  refine le_trans (norm_gDeriv_apply_le _) ?_
  rw [vdEWA]
  refine mul_le_mul_of_nonneg_left ?_ Real.pi_nonneg
  refine le_trans (norm_incl_apply_le _ _) ?_
  exact vFieldEWA_norm_le hμ hγ hδpos hMd hu_floor huD huR hR

/-- **`chemFluxEWA` norm bound** on the positive ball, composed from the triple-product
factor norms `‖u‖ ≤ R`, `‖vxEWA u‖ ≤ Mb`, `‖qFactor β (vd)‖ ≤ Mc`:
`‖Q(u)‖ ≤ R · Mb · Mc`. -/
theorem chemFluxEWA_norm_le {μ ν β γ δ δv Md Mdv R : ℝ} (hμ : 0 < μ) {u : EWA T 1}
    (hγ : 0 ≤ γ) (hβ : 0 < β) (hδpos : 0 < δ) (hδvpos : 0 < δv) (hMd : 0 ≤ Md)
    (hMdv : 0 ≤ Mdv) (hu_floor : UniformFloor u δ) (huD : ‖GWA.gDeriv u‖ ≤ Md)
    (huR : ‖u‖ ≤ R) (hR : 0 ≤ R) (hvdu_floor : UniformFloor (1 + vdEWA μ ν γ hμ u) δv)
    (hvduD : ‖GWA.gDeriv (vdEWA μ ν γ hμ u)‖ ≤ Mdv) :
    ‖chemFluxEWA μ ν β γ hμ u‖
      ≤ R * (Real.pi * (GWA.resolverGainConst μ * (|ν| *
            (R ^ (Nat.floor γ + 1) * negNormConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md))))
          * negNormConst β δv Mdv := by
  have hfu : chemFluxEWA μ ν β γ hμ u
      = u * vxEWA μ ν γ hμ u * qFactor β (vdEWA μ ν γ hμ u) := rfl
  rw [hfu]
  set Mb : ℝ := Real.pi * (GWA.resolverGainConst μ * (|ν| *
      (R ^ (Nat.floor γ + 1) * negNormConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md))) with hMb_def
  set Mc : ℝ := negNormConst β δv Mdv with hMc_def
  have hb : ‖vxEWA μ ν γ hμ u‖ ≤ Mb := by
    rw [hMb_def]; exact vxEWA_norm_le hμ hγ hδpos hMd hu_floor huD huR hR
  have hc : ‖qFactor β (vdEWA μ ν γ hμ u)‖ ≤ Mc :=
    qFactor_norm_le hβ hδvpos hMdv hvdu_floor hvduD
  have hMbnn : (0 : ℝ) ≤ Mb := le_trans (norm_nonneg _) hb
  have hMcnn : (0 : ℝ) ≤ Mc := le_trans (norm_nonneg _) hc
  refine le_trans (norm_mul_le _ _) ?_
  refine le_trans (mul_le_mul (le_trans (norm_mul_le _ _)
    (mul_le_mul huR hb (norm_nonneg _) hR)) hc (norm_nonneg _)
    (mul_nonneg hR hMbnn)) ?_
  apply le_of_eq; ring

/-- **`growthEWA` norm bound** on the ball `‖u‖ ≤ R`, from `‖P(u)‖` (the logistic factor
norm) and `‖u‖ ≤ R`: `‖G(u)‖ ≤ R · (|a|·‖1‖ + |b|·R^m·negNormConst s)`. -/
theorem growthEWA_norm_le {α a b δ Md R : ℝ} {u : EWA T 1} (hα : 0 ≤ α)
    (hδpos : 0 < δ) (hMd : 0 ≤ Md) (hu_floor : UniformFloor u δ)
    (huD : ‖GWA.gDeriv u‖ ≤ Md) (huR : ‖u‖ ≤ R) (hR : 0 ≤ R) :
    ‖growthEWA α a b u‖
      ≤ R * (|a| * ‖(1 : EWA T 1)‖ + |b| *
          (R ^ (Nat.floor α + 1) * negNormConst ((Nat.floor α + 1 : ℝ) - α) δ Md)) := by
  rw [growthEWA]
  set Mp : ℝ := |a| * ‖(1 : EWA T 1)‖ + |b| *
      (R ^ (Nat.floor α + 1) * negNormConst ((Nat.floor α + 1 : ℝ) - α) δ Md) with hMp_def
  have hp : ‖(a : ℂ) • (1 : EWA T 1) - (b : ℂ) • realPowEWA u α‖ ≤ Mp :=
    growthFactor_norm_le hα hδpos hMd hu_floor huD huR hR
  refine le_trans (norm_mul_le _ _) ?_
  exact mul_le_mul huR hp (norm_nonneg _) hR

/-! ### The two-smallness time chooser. -/

/-- **Two smallness conditions, one time.**  For `A,B ≥ 0` (contraction constants) and
`A',B' ≥ 0` with `ρ > 0` (self-map constants), there is a single `T > 0` making BOTH
`A·√T + B·T < 1` (the contraction) AND `A'·√T + B'·T ≤ ρ` (the self-map smallness).
Take `T` = the minimum of the two times from `exists_small_contraction_time`. -/
theorem exists_small_two_conditions {A B A' B' ρ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hA' : 0 ≤ A') (hB' : 0 ≤ B') (hρ : 0 < ρ) :
    ∃ T : ℝ, 0 < T ∧ A * Real.sqrt T + B * T < 1 ∧ A' * Real.sqrt T + B' * T ≤ ρ := by
  obtain ⟨T₁, hT₁, hlt₁⟩ :=
    ShenWork.IntervalChemFluxLipschitz.exists_small_contraction_time hA hB
  obtain ⟨T₂, hT₂, hlt₂⟩ := exists_small_contraction_time_target hA' hB' hρ
  refine ⟨min T₁ T₂, lt_min hT₁ hT₂, ?_, ?_⟩
  · -- on `min ≤ T₁` the contraction holds (monotone in `T` for `A,B ≥ 0`).
    have hmin : min T₁ T₂ ≤ T₁ := min_le_left _ _
    have hsqrt : Real.sqrt (min T₁ T₂) ≤ Real.sqrt T₁ := Real.sqrt_le_sqrt hmin
    have h1 : A * Real.sqrt (min T₁ T₂) ≤ A * Real.sqrt T₁ :=
      mul_le_mul_of_nonneg_left hsqrt hA
    have h2 : B * min T₁ T₂ ≤ B * T₁ := mul_le_mul_of_nonneg_left hmin hB
    linarith
  · -- on `min ≤ T₂` the self-map smallness holds.
    have hmin : min T₁ T₂ ≤ T₂ := min_le_right _ _
    have hsqrt : Real.sqrt (min T₁ T₂) ≤ Real.sqrt T₂ := Real.sqrt_le_sqrt hmin
    have h1 : A' * Real.sqrt (min T₁ T₂) ≤ A' * Real.sqrt T₂ :=
      mul_le_mul_of_nonneg_left hsqrt hA'
    have h2 : B' * min T₁ T₂ ≤ B' * T₂ := mul_le_mul_of_nonneg_left hmin hB'
    linarith

/-! ### THE TRULY-CLEAN χ₀<0 ABSOLUTE FIXED POINT. -/

/-- **THE TRULY-CLEAN χ₀<0 SOURCE-FORM ABSOLUTE FIXED POINT (standard data).**

From a continuous real source `u₀ : ℝ → ℝ` with floor `u₀ ≥ δ > 0` and absolutely
summable cosine coefficients, the `MemW` membership of the cosine embedding, `CM2Params`
positivity (and `0 < p.β`), choosing the ball radius `ρ := δ/2` internally and the time
`T > 0` small via the two-smallness chooser, the χ₀<0 Picard map `picardEWA` has a fixed
point `u* ∈ closedBall (heatEWA u₀E) ρ`.

ALL of `hheat`/`hself`/`hLipQ`/`hLipG` and the side-data `Md`/`Mdv`/`M_Q`/`M_G`/radius are
discharged from the standard datum facts and the committed norm bricks; the SINGLE carried
hypothesis is the EWA resolver-positivity floor `hVdFloor`
(`UniformFloor (1 + vdEWA …) δv`, the `1+v ≥ δv` signal floor — the EWA analogue of the heat
floor, genuinely uncommitted at the EWA level; the time `T` is the chooser's, so the floor
is quantified over all `T ≥ 0`).  χ₀<0 enters through `picardEWA`; the result holds for any
`p.χ₀`, in particular `p.χ₀ < 0`. -/
theorem picardEWA_clean_fixedPoint {p : CM2Params} {δ δv : ℝ}
    (u₀ : ℝ → ℝ) (hu₀ : Continuous u₀) (hδpos : 0 < δ) (hfloor : ∀ y, δ ≤ u₀ y)
    (hsum : Summable (fun k => |cosineCoeffs u₀ k|))
    (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀)))
    (hβpos : 0 < p.β) (hδvpos : 0 < δv)
    (hVdFloor : ∀ (T : ℝ), 0 ≤ T → ∀ u ∈ Metric.closedBall
        (heatEWA (T := T) (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)) (δ / 2),
      UniformFloor (1 + vdEWA p.μ p.ν p.γ p.hμ u) δv) :
    ∃ (T : ℝ) (hT : 0 ≤ T), ∃ u_star ∈ Metric.closedBall
        (heatEWA (T := T) (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)) (δ / 2),
      u_star = picardEWA p p.μ p.ν p.γ p.hμ hT
        (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1) u_star := by
  classical
  -- abbreviations for the realized datum and the `T`-independent radius / floors.
  set u₀E : WA 1 := ⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ with hu₀E
  set ρ : ℝ := δ / 2 with hρ_def
  have hρpos : 0 < ρ := by rw [hρ_def]; linarith
  have hρnn : 0 ≤ ρ := hρpos.le
  have hδρpos : 0 < δ - ρ := by rw [hρ_def]; linarith
  -- the `T`-independent radius `R = ‖u₀E‖ + ρ` (dominates `‖heatEWA u₀E‖ + ρ` for every T).
  set R : ℝ := ‖u₀E‖ + ρ with hR_def
  have hRnn : 0 ≤ R := by rw [hR_def]; positivity
  -- the `T`-independent derivative bounds `Md = π·R`, `Mdv = π·(C_μ·|ν|·R^m·negNormConst)`.
  set Md : ℝ := Real.pi * R with hMd_def
  have hMdnn : 0 ≤ Md := by rw [hMd_def]; positivity
  set Mdv : ℝ := Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
      (R ^ (Nat.floor p.γ + 1)
        * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))) with hMdv_def
  have hCμnn : (0 : ℝ) ≤ GWA.resolverGainConst p.μ := by
    unfold GWA.resolverGainConst; have := p.hμ; positivity
  have hγnn : 0 ≤ p.γ := p.hγ.le
  have hαnn : 0 ≤ p.α := p.hα.le
  -- the `T`-independent flux/growth norm constants `M_Q`, `M_G`.
  set M_Q : ℝ := R * (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
        (R ^ (Nat.floor p.γ + 1)
          * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))))
      * negNormConst p.β δv Mdv with hMQ_def
  set M_G : ℝ := R * (|p.a| * 1 + |p.b| *
      (R ^ (Nat.floor p.α + 1)
        * negNormConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md)) with hMG_def
  -- the `T`-independent Lipschitz constants `L_Q`, `L_G` (exactly as pinned in `_abs_`).
  set L_Q : ℝ := (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
              (R ^ (Nat.floor p.γ + 1)
                * negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md))))
            * negNormConst p.β δv Mdv * 1
          + R * negNormConst p.β δv Mdv * (Real.pi * (GWA.resolverGainConst p.μ * (|p.ν| *
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
                    * negLipConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md)))) with hLQ_def
  set L_G : ℝ := R * (|p.b| * ((Nat.floor p.α + 1 : ℝ) * R ^ ((Nat.floor p.α + 1) - 1)
              * negNormConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md
            + R ^ (Nat.floor p.α + 1)
              * negLipConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md))
          + (|p.a| * 1 + |p.b| *
              (R ^ (Nat.floor p.α + 1)
                * negNormConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md)) with hLG_def
  -- the two power-floor exponents are strictly positive.
  have hsγ : 0 < (Nat.floor p.γ + 1 : ℝ) - p.γ := by
    have := Nat.lt_floor_add_one p.γ; linarith
  have hsα : 0 < (Nat.floor p.α + 1 : ℝ) - p.α := by
    have := Nat.lt_floor_add_one p.α; linarith
  -- nonnegativity of all four Γ-combination constants (positive Γ-factors).
  have hnegNγ : (0 : ℝ) ≤ negNormConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md :=
    negNormConst_nonneg hsγ hδρpos hMdnn
  have hnegLγ : (0 : ℝ) ≤ negLipConst ((Nat.floor p.γ + 1 : ℝ) - p.γ) (δ - ρ) Md :=
    negLipConst_nonneg hsγ hδρpos hMdnn
  have hnegNα : (0 : ℝ) ≤ negNormConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md :=
    negNormConst_nonneg hsα hδρpos hMdnn
  have hnegLα : (0 : ℝ) ≤ negLipConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md :=
    negLipConst_nonneg hsα hδρpos hMdnn
  have hMdvnn : 0 ≤ Mdv := by rw [hMdv_def]; positivity
  have hnegNv : (0 : ℝ) ≤ negNormConst p.β δv Mdv := negNormConst_nonneg hβpos hδvpos hMdvnn
  have hnegLv : (0 : ℝ) ≤ negLipConst p.β δv Mdv := negLipConst_nonneg hβpos hδvpos hMdvnn
  have hMQnn : 0 ≤ M_Q := by rw [hMQ_def]; positivity
  have hMGnn : 0 ≤ M_G := by rw [hMG_def]; positivity
  have hLQnn : 0 ≤ L_Q := by rw [hLQ_def]; positivity
  have hLGnn : 0 ≤ L_G := by rw [hLG_def]; positivity
  -- choose `T > 0` small for BOTH the contraction (`hK`) and the self-map smallness.
  obtain ⟨T, hTpos, hKlt, hsmall⟩ :=
    exists_small_two_conditions (A := |p.χ₀| * C₀ * L_Q) (B := L_G)
      (A' := |p.χ₀| * C₀ * M_Q) (B' := M_G)
      (by have := C₀_nonneg; positivity) hLGnn
      (by have := C₀_nonneg; positivity) hMGnn hρpos
  have hT : (0 : ℝ) ≤ T := hTpos.le
  refine ⟨T, hT, ?_⟩
  -- the heat-floor `hheat` from the standard datum (HeatFloor brick).
  have hheat : UniformFloor (heatEWA (T := T) u₀E) δ := by
    rw [hu₀E]; exact heatEWA_uniformFloor (T := T) hu₀ hfloor hsum hmem
  -- the `T`-independent ball side-data, uniform on `B = closedBall (heatEWA u₀E) ρ`.
  have hball_norm : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ, ‖u‖ ≤ R := by
    intro u hu
    rw [Metric.mem_closedBall, dist_eq_norm] at hu
    have htri : ‖u‖ ≤ ‖u - heatEWA (T := T) u₀E‖ + ‖heatEWA (T := T) u₀E‖ := by
      have := norm_add_le (u - heatEWA (T := T) u₀E) (heatEWA (T := T) u₀E); simpa using this
    have hhle : ‖heatEWA (T := T) u₀E‖ ≤ ‖u₀E‖ := heatEWA_norm_le u₀E
    rw [hR_def]; linarith
  have hball_floor : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      UniformFloor u (δ - ρ) := fun u hu => uniformFloor_on_ball hheat hu
  have hMD : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ, ‖GWA.gDeriv u‖ ≤ Md := by
    intro u hu
    refine le_trans (norm_gDeriv_apply_le u) ?_
    rw [hMd_def]; exact mul_le_mul_of_nonneg_left (hball_norm u hu) Real.pi_nonneg
  have hVdD : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ‖GWA.gDeriv (vdEWA p.μ p.ν p.γ p.hμ u)‖ ≤ Mdv := by
    intro u hu
    rw [hMdv_def]
    exact vdEWA_gDeriv_norm_le p.hμ hγnn hδρpos hMdnn (hball_floor u hu) (hMD u hu)
      (hball_norm u hu) hRnn
  have hVdF : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      UniformFloor (1 + vdEWA p.μ p.ν p.γ p.hμ u) δv := by
    intro u hu; exact hVdFloor T hT u hu
  -- the flux/growth norm bounds `M_Q`, `M_G` on the ball (composed bricks).
  have hMQ : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ‖chemFluxEWA p.μ p.ν p.β p.γ p.hμ u‖ ≤ M_Q := by
    intro u hu
    rw [hMQ_def]
    exact chemFluxEWA_norm_le p.hμ hγnn hβpos hδρpos hδvpos hMdnn hMdvnn
      (hball_floor u hu) (hMD u hu) (hball_norm u hu) hRnn (hVdF u hu) (hVdD u hu)
  have hone : ‖(1 : EWA T 1)‖ = 1 := norm_one_EWA hT
  have hMG : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ‖growthEWA p.α p.a p.b u‖ ≤ M_G := by
    intro u hu
    rw [hMG_def]
    have h := growthEWA_norm_le (α := p.α) (a := p.a) (b := p.b) (u := u)
      hαnn hδρpos hMdnn (hball_floor u hu) (hMD u hu) (hball_norm u hu) hRnn
    rw [hone] at h; exact h
  -- the self-map `hself` from `picardEWA_mapsTo` + the small-time smallness.
  have hsmall' : |p.χ₀| * (C₀ * Real.sqrt T) * M_Q + T * M_G ≤ ρ := by
    have heq : |p.χ₀| * C₀ * M_Q * Real.sqrt T + M_G * T
        = |p.χ₀| * (C₀ * Real.sqrt T) * M_Q + T * M_G := by ring
    rw [heq] at hsmall; exact hsmall
  have hself : MapsTo (picardEWA p p.μ p.ν p.γ p.hμ hT u₀E)
      (Metric.closedBall (heatEWA u₀E) ρ) (Metric.closedBall (heatEWA u₀E) ρ) :=
    picardEWA_mapsTo p.hμ hT u₀E hMQ hMG hsmall'
  -- the contraction smallness `hK`, `hKnn`.
  have hKnn : (0 : ℝ) ≤ |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T := by
    have := C₀_nonneg; have hsq : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T; positivity
  have hK : |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T < 1 := by
    have heq : |p.χ₀| * C₀ * L_Q * Real.sqrt T + L_G * T
        = |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T := by ring
    rw [heq] at hKlt; exact hKlt
  -- the `hLG` pinning expected by `_abs_` carries `‖(1:EWA T 1)‖`; rewrite it to `1 = L_G`.
  have hLG_pin : L_G = R * (|p.b| * ((Nat.floor p.α + 1 : ℝ) * R ^ ((Nat.floor p.α + 1) - 1)
              * negNormConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md
            + R ^ (Nat.floor p.α + 1)
              * negLipConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md))
          + (|p.a| * ‖(1 : EWA T 1)‖ + |p.b| *
              (R ^ (Nat.floor p.α + 1)
                * negNormConst ((Nat.floor p.α + 1 : ℝ) - p.α) (δ - ρ) Md)) := by
    rw [hLG_def, hone]
  -- assemble via the absolute fixed point with all side-data discharged.
  exact picardEWA_abs_fixedPoint p.hμ hT u₀E hρnn hγnn
    hMdnn hMdvnn hRnn hδρpos hδvpos hheat hMD hball_norm hVdF hVdD hLQ_def hLG_pin hβpos hαnn
    hself hKnn hK

end ShenWork.EWA

#print axioms ShenWork.EWA.norm_one_EWA
#print axioms ShenWork.EWA.chemFluxEWA_norm_le
#print axioms ShenWork.EWA.growthEWA_norm_le
#print axioms ShenWork.EWA.exists_small_two_conditions
#print axioms ShenWork.EWA.picardEWA_clean_fixedPoint
