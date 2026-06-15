import ShenWork.Wiener.EWA.SourceVdFloorDischarge
import ShenWork.Wiener.EWA.WLEvenReal
import ShenWork.Wiener.EWA.FluxRealizeEmbed

/-!
# EWA brick (χ₀<0 Route A′) — UNCONDITIONAL center floor for the HEAT center

`vdEWA_center_floor` (`SourceVdFloorDischarge.lean`) proves
`UniformFloor (1 + vdEWA p.μ p.ν p.γ p.hμ (heatEWA u₀E)) 1` but CARRIES the eight
heat-realization sub-inputs `uR`/`hsum`/`hWslice`/`f`/`hf_cont`/`hf_nonneg`/`hf_coeff`/`hâ`.

This file DISCHARGES all eight for the heat center, from the standard real-space datum
`u₀ : ℝ → ℝ` (continuous, floor `δ>0`) plus `ν ≥ 0` and the SINGLE genuine analytic
summability of the realized resolver source `ν·V^γ` (the cosine-coefficient ℓ¹ summability
`hsource` of the nonlinear heat-source; NOT reducible to the linear `c₀` summability, carried
as one named hypothesis).  The ℓ² summability `hâ` is DERIVED from `hsource`, not carried.

## The realized track

* `c₀ := cosineCoeffs u₀`, `u₀E := ⟨ofCosineCoeffs c₀, hmem⟩`.
* the per-τ heat realization `uR t := fun pt => unitIntervalCosineHeatValue t c₀ pt.1`.
* the per-τ real source `f t := fun y => p.ν · unitIntervalCosineHeatValue t c₀ y ^ p.γ`.

**Even-real** of the heat element (`heatEWA_evenReal`): its slice is `ofCosineCoeffs` of a
real family (`heatEWA_slice_eq_ofCosineCoeffs`), even+real by `ofCosineCoeffs_neg` /
`ofCosineCoeffs_im`.  Through `realPowEWA_evenReal FnegEWA_evenReal_Hyp_proved` + `.smul_real`
+ `.incl` this gives `hER` for `incl (ν • realPowEWA (heat) γ)`.

**`hRealize`** chains `realPowEWA_eval` (with `hfloor := heatEWA_uniformFloor`, `hreal` from
`heatEWA_evalST_eq_cosineHeatValue`) + the `ν•` smul-commute, landing
`ν·(lift (uR τ.1) x)^γ`; `slice_smul_realPow_eq_source` then gives `hWslice`.

**`hf_coeff`** matches `f τ.1` to `ν·(lift (uR τ.1) ·)^γ` on `[0,1]` via
`cosineCoeffs_congr_on_Icc` + `resolverSourceReCoeff_eq_cosineCoeffs`.

No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/

open scoped BigOperators
open Set
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.PDE (intervalNeumannResolverSourceCoeff)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### The heat element is even-real. -/

/-- **The heat element `heatEWA u₀E` is even-real.**  Its slice at every `τ` is
`ofCosineCoeffs (k ↦ exp(−τ(kπ)²)·c₀ k)` (`heatEWA_slice_eq_ofCosineCoeffs`), a real
cosine embedding — even by `ofCosineCoeffs_neg`, real by `ofCosineCoeffs_im`. -/
theorem heatEWA_evenReal (c₀ : ℕ → ℝ) (hmem : MemW 1 (ofCosineCoeffs c₀)) :
    EvenRealEWA (heatEWA (T := T) (⟨ofCosineCoeffs c₀, hmem⟩ : WA 1)) where
  even τ n := by
    rw [coeff_sliceWA, coeff_sliceWA,
      heatEWA_slice_eq_ofCosineCoeffs (T := T) c₀ τ hmem (-n),
      heatEWA_slice_eq_ofCosineCoeffs (T := T) c₀ τ hmem n, ofCosineCoeffs_neg]
  real τ n := by
    rw [coeff_sliceWA, heatEWA_slice_eq_ofCosineCoeffs (T := T) c₀ τ hmem n,
      ofCosineCoeffs_im]

/-! ### THE UNCONDITIONAL CENTER FLOOR. -/

/-- **THE UNCONDITIONAL χ₀<0 CENTER FLOOR (heat center).**

`UniformFloor (1 + vdEWA p.μ p.ν p.γ p.hμ (heatEWA u₀E)) 1` for the heat center
`u₀E = ⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩`, with ALL eight heat-realization
sub-inputs of `vdEWA_center_floor` DISCHARGED from the standard datum.

The single carried `hsource` is the genuine analytic ℓ¹ summability of the cosine
coefficients of the realized nonlinear resolver source `ν·V^γ` (V = heat value); it is NOT
the linear-`c₀` summability and has no committed discharge in the framework.  The ℓ²
summability `hâ` is DERIVED from `hsource` (bounded-tail argument), not carried. -/
theorem vdEWA_center_floor_heat (p : CM2Params) (u₀ : ℝ → ℝ) (hu₀ : Continuous u₀)
    {δ : ℝ} (hδpos : 0 < δ) (hfloor : ∀ y, δ ≤ u₀ y) (hνpos : 0 ≤ p.ν)
    (hsumc : Summable (fun k => |cosineCoeffs u₀ k|))
    (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀)))
    -- the per-τ realization data:
    (uR : ℝ → intervalDomainPoint → ℝ)
    (huR : uR = fun t pt =>
      unitIntervalCosineHeatValue t (cosineCoeffs u₀) (pt.1))
    -- the genuine analytic summability of the realized source `ν·V^γ` (ℓ¹; ℓ² is derived):
    (hsource : ∀ τ : TimeDom T, ResolverSourceSummable p (uR τ.1)) :
    UniformFloor (1 + vdEWA p.μ p.ν p.γ p.hμ
      (heatEWA (T := T) (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1))) 1 := by
  set c₀ : ℕ → ℝ := cosineCoeffs u₀ with hc₀
  set u₀E : WA 1 := ⟨ofCosineCoeffs c₀, hmem⟩ with hu₀E
  set f : ℝ → ℝ → ℝ :=
    fun t y => p.ν * unitIntervalCosineHeatValue t c₀ y ^ p.γ with hf_def
  -- The heat element is even-real, hence so is `incl (ν • realPowEWA (heat) γ)`.
  have hheatER : EvenRealEWA (heatEWA (T := T) u₀E) := heatEWA_evenReal c₀ hmem
  have hER : EvenRealEWA (GWA.incl (by omega : (0 : ℕ) ≤ 1)
      ((p.ν : ℂ) • realPowEWA (heatEWA (T := T) u₀E) p.γ)) :=
    ((realPowEWA_evenReal FnegEWA_evenReal_Hyp_proved hheatER p.γ).smul_real p.ν).incl
      (by omega)
  -- The heat floor on the element (feeds `realPowEWA_eval`).
  have hheatFloor : UniformFloor (heatEWA (T := T) u₀E) δ :=
    heatEWA_uniformFloor hu₀ hfloor hsumc hmem
  -- `(evalST τ x (incl heat)).im = 0` for every circle point (feeds `realPowEWA_eval`).
  have hheatReal : ∀ (τ : TimeDom T) (x : WA.Circ),
      (evalST τ x (GWA.incl (by omega : (0 : ℕ) ≤ 1) (heatEWA (T := T) u₀E))).im = 0 := by
    intro τ x
    induction x using QuotientAddGroup.induction_on with
    | _ x =>
      rw [heatEWA_evalST_eq_cosineHeatValue c₀ hsumc hmem τ x, Complex.ofReal_im]
  -- The real heat value equals the lift of `uR τ.1` on `[0,1]`.
  have hlift : ∀ (t : ℝ) (y : ℝ), y ∈ Set.Icc (0 : ℝ) 1 →
      intervalDomainLift (uR t) y = unitIntervalCosineHeatValue t c₀ y := by
    intro t y hy
    rw [intervalDomainLift, dif_pos hy, huR]
  -- `hRealize`: the synthesis of `incl (ν • realPowEWA (heat) γ)` realizes `ν·(lift)^γ`.
  have hRealize : ∀ τ : TimeDom T, ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
          ((p.ν : ℂ) • realPowEWA (heatEWA (T := T) u₀E) p.γ))
        = ((p.ν * intervalDomainLift (uR τ.1) x ^ p.γ : ℝ) : ℂ) := by
    intro τ x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    -- `incl (c • W) = c • incl W`.
    have hincl_smul : GWA.incl (by omega : (0 : ℕ) ≤ 1)
          ((p.ν : ℂ) • realPowEWA (heatEWA (T := T) u₀E) p.γ)
        = (p.ν : ℂ) • GWA.incl (by omega : (0 : ℕ) ≤ 1)
            (realPowEWA (heatEWA (T := T) u₀E) p.γ) := by
      rw [← GWA.gIncl_apply, map_smul, GWA.gIncl_apply]
    rw [hincl_smul, evalST_smul]
    -- `realPowEWA_eval`: the power synthesis is `(Re evalST(incl heat))^γ`.
    rw [realPowEWA_eval p.hγ.le hδpos hheatFloor hheatReal τ (x : WA.Circ)]
    -- `Re evalST(incl heat) = unitIntervalCosineHeatValue τ.1 c₀ x`.
    rw [heatEWA_evalST_eq_cosineHeatValue c₀ hsumc hmem τ x, Complex.ofReal_re]
    rw [hlift (τ : ℝ) x hxIcc]
    push_cast
    ring
  -- `hWslice`: the crux slice-coefficient identity (from `slice_smul_realPow_eq_source`).
  have hWslice : ∀ τ : TimeDom T, (sliceWA τ (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        ((p.ν : ℂ) • realPowEWA (heatEWA (T := T) u₀E) p.γ))).toFun
      = ofCosineCoeffs (resolverSourceReCoeff p (uR τ.1)) := by
    intro τ
    exact slice_smul_realPow_eq_source p uR (heatEWA (T := T) u₀E) τ hER (hRealize τ)
  -- The source `f` is continuous, nonneg, and its cosine coeffs match the resolver source.
  have hf_cont : ∀ τ : TimeDom T, Continuous (f τ.1) := by
    intro τ
    have hcontV : Continuous (fun y => unitIntervalCosineHeatValue (τ : ℝ) c₀ y) :=
      cosineHeatValue_continuous hsumc τ.2.1
    have hVpos : ∀ y, 0 < unitIntervalCosineHeatValue (τ : ℝ) c₀ y := fun y =>
      lt_of_lt_of_le hδpos (cosineHeatValue_ge_floor_all τ.2.1 hu₀ hfloor hsumc y)
    rw [hf_def]
    exact continuous_const.mul
      (hcontV.rpow_const (fun y => Or.inl (ne_of_gt (hVpos y))))
  have hf_nonneg : ∀ (τ : TimeDom T) (y : ℝ), 0 ≤ f τ.1 y := by
    intro τ y
    rw [hf_def]
    have hV : 0 ≤ unitIntervalCosineHeatValue (τ : ℝ) c₀ y :=
      le_trans hδpos.le (cosineHeatValue_ge_floor_all τ.2.1 hu₀ hfloor hsumc y)
    exact mul_nonneg hνpos (Real.rpow_nonneg hV p.γ)
  have hf_coeff : ∀ (τ : TimeDom T) (k : ℕ),
      cosineCoeffs (f τ.1) k = (intervalNeumannResolverSourceCoeff p (uR τ.1) k).re := by
    intro τ k
    have hcongr : cosineCoeffs (f τ.1) k
        = cosineCoeffs (fun y => p.ν * intervalDomainLift (uR τ.1) y ^ p.γ) k := by
      refine cosineCoeffs_congr_on_Icc (fun y hy => ?_) k
      rw [hf_def, hlift (τ : ℝ) y hy]
    rw [hcongr]
    have hre : (intervalNeumannResolverSourceCoeff p (uR τ.1) k).re
        = resolverSourceReCoeff p (uR τ.1) k := rfl
    rw [hre, resolverSourceReCoeff_eq_cosineCoeffs]
  -- `hâ` (ℓ²) is DERIVED from `hsource` (ℓ¹): the coeffs equal `resolverSourceReCoeff`,
  -- and an absolutely-summable real family is square-summable (terms → 0, eventually
  -- `a² ≤ |a|`).
  have hâ : ∀ τ : TimeDom T, Summable (fun k => (cosineCoeffs (f τ.1) k) ^ 2) := by
    intro τ
    have hcoeff : (fun k => (cosineCoeffs (f τ.1) k) ^ 2)
        = fun k => (resolverSourceReCoeff p (uR τ.1) k) ^ 2 := by
      funext k
      have hre : (intervalNeumannResolverSourceCoeff p (uR τ.1) k).re
          = resolverSourceReCoeff p (uR τ.1) k := rfl
      rw [hf_coeff τ k, hre]
    rw [hcoeff]
    set a : ℕ → ℝ := fun k => resolverSourceReCoeff p (uR τ.1) k with ha
    have hℓ1 : Summable (fun k => |a k|) := hsource τ
    -- terms tend to 0, so for `k ≥ N` we have `|a k| ≤ 1`, hence `(a k)^2 ≤ |a k|`.
    have htend : Filter.Tendsto (fun k => |a k|) Filter.atTop (nhds 0) :=
      hℓ1.tendsto_atTop_zero
    have hev : ∀ᶠ k in Filter.atTop, |a k| < 1 := by
      have := htend.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
      simpa using this
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    -- square-summability of the shifted tail, then `summable_nat_add_iff`.
    have htail : Summable (fun k => (a (k + N)) ^ 2) := by
      refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
        ((summable_nat_add_iff N).mpr hℓ1)
      have hk : |a (k + N)| < 1 := hN (k + N) (by omega)
      have hsq : (a (k + N)) ^ 2 = |a (k + N)| * |a (k + N)| := by
        rw [← sq_abs, sq]
      rw [hsq]
      nlinarith [abs_nonneg (a (k + N)), hk.le]
    exact (summable_nat_add_iff N).mp htail
  -- Assemble: feed all eight discharged inputs into the carried center floor.
  exact vdEWA_center_floor p u₀E uR hsource hWslice f hf_cont hf_nonneg hf_coeff hâ

end ShenWork.EWA

#print axioms ShenWork.EWA.vdEWA_center_floor_heat
