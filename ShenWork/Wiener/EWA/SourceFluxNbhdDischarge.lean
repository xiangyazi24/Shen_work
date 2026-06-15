import ShenWork.Wiener.EWA.FluxRealizeEmbed
import ShenWork.Wiener.EWA.SourceResolverFloor
import ShenWork.Wiener.EWA.SourceCenterFloorHeat
import ShenWork.Wiener.EWA.SourceDuhamelSynthesis

/-!
# EWA brick (χ₀<0) — DISCHARGING the flux-neighborhood atom for `embedEWA u`

`flux_nbhd_of_embed` (`FluxRealizeEmbed.lean:326`) proves the chemotaxis flux value
realization
`evalST τ x (incl (chemFluxEWA …U)) = (chemFluxLifted p (u τ.1) x : ℂ)` for
`U := embedEWA u …`, but TAKES a stack of sub-atoms `hER`/`hRealize`/`hqfloor`/`hqreal`/
`h_floor` (plus the genuinely-irreducible `hsum`/`hgrad`/embed data).

This file's `flux_nbhd_of_embed_discharged` applies `flux_nbhd_of_embed` with FOUR of
those sub-atoms PROVED from committed machinery, carrying only the genuinely-irreducible
ones.

## DISCHARGED vs CARRIED

DISCHARGED:
* `hER`     — `embedEWA_evenReal` ⇒ `EvenRealEWA U`, then
  `(realPowEWA_evenReal FnegEWA_evenReal_Hyp_proved · p.γ).smul_real p.ν |>.incl`.
* `hRealize`— `realPowEWA_eval` + the `ν•`-smul commute + `embedEWA_realizes` for the
  `Re`-value (mirrors `vdEWA_center_floor_heat`).  REALITY of `evalST(incl U)` is free
  (`evalST_eq_cosineSynthesis_of_even_real` ⇒ real cast).  Uses the carried
  `UniformFloor U δ`/`hδpos` (no committed embed floor — `embedEWA u` of a generic
  solution `u` has no a-priori positive floor).
* `hqreal`  — `1 + incl(1≤3)(vFieldEWA …U)` is even-real (`vFieldEWA_evenReal` + `.incl`
  + `.one`/`.add`), so its `evalST` is a real cast ⇒ `im = 0`.
* `hqfloor` / `h_floor` — `vdEWA_uniformFloor` / `resolverSynthesis_nonneg_Icc` from the
  carried nonneg continuous source data (`f`/`hf_cont`/`hf_nonneg`/`hf_coeff`/`hâ`) and
  `p.μ ≤ 1`.  The crux slice identity feeding them is `slice_smul_realPow_eq_source`
  (from the discharged `hER`/`hRealize`).

CARRIED (genuinely irreducible — see the report):
`hsum`, `hgrad`, the embed data (`hBv`/`hBvnn`/`hBvsum`/`hcont`/`hsummable`/`hcos_series`),
the embed floor `hUfloor`/`hδpos`, the parameter constraint `hμle1`, and the nonneg
continuous resolver-source data `f`/`hf_cont`/`hf_nonneg`/`hf_coeff`/`hâ`.

No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.PDE (intervalNeumannResolverR intervalNeumannResolverCoeff
  intervalNeumannResolverSourceCoeff)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- **`flux_nbhd_of_embed_discharged`.**  The flux value realization for
`U := embedEWA u …`, with the parity/realization/reality sub-atoms of
`flux_nbhd_of_embed` DISCHARGED from committed machinery, carrying only the genuinely
irreducible inputs (the resolver-source summability `hsum`, the resolver gradient
majorant `hgrad`, the embed data, the embed floor `hUfloor`/`hδpos`, the parameter
constraint `hμle1`, and the nonneg continuous resolver-source data). -/
theorem flux_nbhd_of_embed_discharged
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    {Bv : ℕ → ℝ}
    (hBv : ∀ t k, |cosineCoeffs (intervalDomainLift (u t)) k| ≤ Bv k)
    (hBvnn : ∀ k, 0 ≤ Bv k)
    (hBvsum : Summable (fun k : ℕ => (1 + (k : ℝ)) * Bv k))
    (hcont : ∀ n : ℤ, Continuous (embedModeFun u n))
    (hsummable : ∀ t, Summable (fun k => |cosineCoeffs (intervalDomainLift (u t)) k|))
    (hcos_series : ∀ t y, y ∈ Set.Icc (0 : ℝ) 1 →
      intervalDomainLift (u t) y
        = ∑' k : ℕ, cosineCoeffs (intervalDomainLift (u t)) k * cosineMode k y)
    (hβpos : 0 < p.β)
    (τ : TimeDom T) (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hxIcc : x ∈ Set.Icc (0 : ℝ) 1)
    -- genuinely-irreducible analytic inputs (the floor needs the source summability at
    -- EVERY time `σ`, since the slice source `u σ.1` is `σ`-dependent):
    (hsum : ∀ σ : TimeDom T, ResolverSourceSummable p (u σ.1))
    (hgrad : Summable fun k : ℕ =>
      |(intervalNeumannResolverCoeff p (u τ.1) k).re| * ((k : ℝ) * Real.pi))
    -- the embed floor (no committed embed floor) + the spectral-floor constraint `μ ≤ 1`:
    {δ : ℝ} (hδpos : 0 < δ)
    (hUfloor : UniformFloor (embedEWA (T := T) u hBv hBvnn hBvsum hcont) δ)
    (hμle1 : p.μ ≤ 1)
    -- the nonneg continuous resolver-source data (per-slice O1 positivity input):
    (f : ℝ → ℝ → ℝ) (hf_cont : ∀ σ : TimeDom T, Continuous (f σ.1))
    (hf_nonneg : ∀ (σ : TimeDom T) (y : ℝ), 0 ≤ f σ.1 y)
    (hf_coeff : ∀ (σ : TimeDom T) (k : ℕ),
      cosineCoeffs (f σ.1) k = (intervalNeumannResolverSourceCoeff p (u σ.1) k).re)
    (hâ : ∀ σ : TimeDom T, Summable (fun k => (cosineCoeffs (f σ.1) k) ^ 2)) :
    evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (chemFluxEWA p.μ p.ν p.β p.γ p.hμ (embedEWA u hBv hBvnn hBvsum hcont)))
      = ((chemFluxLifted p (u τ.1) x : ℝ) : ℂ) := by
  set U : EWA T 1 := embedEWA u hBv hBvnn hBvsum hcont with hUeq
  -- `U` is even-real (committed `embedEWA_evenReal`).
  have hU_even : EvenRealEWA U := embedEWA_evenReal u hBv hBvnn hBvsum hcont
  -- `hER`: `incl (ν • realPowEWA U γ)` is even-real.
  have hER : EvenRealEWA (GWA.incl (by omega : (0 : ℕ) ≤ 1)
      ((p.ν : ℂ) • realPowEWA U p.γ)) :=
    ((realPowEWA_evenReal FnegEWA_evenReal_Hyp_proved hU_even p.γ).smul_real p.ν).incl
      (by omega)
  -- Reality of `evalST (incl U)` for every circle point (even-real ⇒ real cast).
  have hUreal : ∀ (σ : TimeDom T) (y : WA.Circ),
      (evalST σ y (GWA.incl (by omega : (0 : ℕ) ≤ 1) U)).im = 0 := by
    intro σ y
    have hERU : EvenRealEWA (GWA.incl (by omega : (0 : ℕ) ≤ 1) U) := hU_even.incl (by omega)
    induction y using QuotientAddGroup.induction_on with
    | _ y =>
      rw [evalST_eq_cosineSynthesis_of_even_real (fun n => hERU.even σ n)
        (fun n => hERU.real σ n) y, Complex.ofReal_im]
  -- `hRealize`: `incl (ν • realPowEWA U γ)` realizes `ν · (lift (u τ.1))^γ` on `(0,1)`.
  have hRealize : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (y : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
          ((p.ν : ℂ) • realPowEWA U p.γ))
        = ((p.ν * intervalDomainLift (u τ.1) y ^ p.γ : ℝ) : ℂ) := by
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2.le⟩
    have hincl_smul : GWA.incl (by omega : (0 : ℕ) ≤ 1)
          ((p.ν : ℂ) • realPowEWA U p.γ)
        = (p.ν : ℂ) • GWA.incl (by omega : (0 : ℕ) ≤ 1) (realPowEWA U p.γ) := by
      rw [← GWA.gIncl_apply, map_smul, GWA.gIncl_apply]
    rw [hincl_smul, evalST_smul,
      realPowEWA_eval p.hγ.le hδpos hUfloor hUreal τ (y : WA.Circ)]
    -- `Re (evalST (incl U)) = lift (u τ.1) y` (committed `embedEWA_realizes`).
    rw [embedEWA_realizes u hBv hBvnn hBvsum hcont hsummable hcos_series τ y hyIcc,
      Complex.ofReal_re]
    push_cast; ring
  -- `hqreal`: `1 + incl(1≤3)(vFieldEWA …U)` is even-real, so `evalST(incl ·)` is real.
  have hqreal : ∀ (σ : TimeDom T) (y : WA.Circ),
      (evalST σ y (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (1 + GWA.incl (by omega : (1 : ℕ) ≤ 3)
          (vFieldEWA p.μ p.ν p.γ p.hμ U)))).im = 0 := by
    intro σ y
    have hvER : EvenRealEWA (1 + GWA.incl (by omega : (1 : ℕ) ≤ 3)
        (vFieldEWA p.μ p.ν p.γ p.hμ U)) :=
      EvenRealEWA.one.add
        ((vFieldEWA_evenReal FnegEWA_evenReal_Hyp_proved p.hμ hU_even).incl (by omega))
    have hER0 : EvenRealEWA (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (1 + GWA.incl (by omega : (1 : ℕ) ≤ 3) (vFieldEWA p.μ p.ν p.γ p.hμ U))) :=
      hvER.incl (by omega)
    induction y using QuotientAddGroup.induction_on with
    | _ y =>
      rw [evalST_eq_cosineSynthesis_of_even_real (fun n => hER0.even σ n)
        (fun n => hER0.real σ n) y, Complex.ofReal_im]
  -- The crux slice identity (feeds the resolver-floor and the value bridge).
  have hWslice : ∀ σ : TimeDom T, (sliceWA σ (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        ((p.ν : ℂ) • realPowEWA U p.γ))).toFun
      = ofCosineCoeffs (resolverSourceReCoeff p (u σ.1)) := by
    intro σ
    exact slice_smul_realPow_eq_source p u U σ
      (((realPowEWA_evenReal FnegEWA_evenReal_Hyp_proved hU_even p.γ).smul_real p.ν).incl
        (by omega))
      (by
        intro y hy
        have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2.le⟩
        have hincl_smul : GWA.incl (by omega : (0 : ℕ) ≤ 1)
              ((p.ν : ℂ) • realPowEWA U p.γ)
            = (p.ν : ℂ) • GWA.incl (by omega : (0 : ℕ) ≤ 1) (realPowEWA U p.γ) := by
          rw [← GWA.gIncl_apply, map_smul, GWA.gIncl_apply]
        rw [hincl_smul, evalST_smul,
          realPowEWA_eval p.hγ.le hδpos hUfloor hUreal σ (y : WA.Circ),
          embedEWA_realizes u hBv hBvnn hBvsum hcont hsummable hcos_series σ y hyIcc,
          Complex.ofReal_re]
        push_cast; ring)
  -- `hqfloor`: per-σ resolver synthesis (source datum `u σ.1` is σ-dependent), `≥ 1 ≥ μ`.
  have hqfloor : UniformFloor (1 + GWA.incl (by omega : (1 : ℕ) ≤ 3)
      (vFieldEWA p.μ p.ν p.γ p.hμ U)) p.μ := by
    intro σ y
    induction y using QuotientAddGroup.induction_on with
    | _ y =>
      have hincl_one : GWA.incl (by omega : (0 : ℕ) ≤ 1) (1 : EWA T 1) = 1 := by
        rw [← GWA.gIncl_apply, map_one]
      have hincl_add : GWA.incl (by omega : (0 : ℕ) ≤ 1)
            (1 + GWA.incl (by omega : (1 : ℕ) ≤ 3) (vFieldEWA p.μ p.ν p.γ p.hμ U))
          = GWA.incl (by omega : (0 : ℕ) ≤ 1) (1 : EWA T 1)
            + GWA.incl (by omega : (0 : ℕ) ≤ 1)
                (GWA.incl (by omega : (1 : ℕ) ≤ 3) (vFieldEWA p.μ p.ν p.γ p.hμ U)) := by
        rw [← GWA.gIncl_apply, map_add, GWA.gIncl_apply, GWA.gIncl_apply]
      have hvd : evalST σ (y : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
            (GWA.incl (by omega : (1 : ℕ) ≤ 3)
              (GWA.gResolver p.μ p.hμ ((p.ν : ℂ) • realPowEWA U p.γ))))
          = ((∑' k : ℕ, (intervalNeumannResolverCoeff p (u σ.1) k).re * cosineMode k y : ℝ)
              : ℂ) :=
        evalST_gResolver_eq_resolverSynthesis_all p (u σ.1)
          ((p.ν : ℂ) • realPowEWA U p.γ) σ y (hsum σ) (hWslice σ)
      rw [hincl_add, (evalST σ (y : WA.Circ)).map_add, hincl_one,
        (evalST σ (y : WA.Circ)).map_one]
      rw [show vFieldEWA p.μ p.ν p.γ p.hμ U
          = GWA.gResolver p.μ p.hμ ((p.ν : ℂ) • realPowEWA U p.γ) from rfl, hvd]
      rw [Complex.add_re, Complex.one_re, Complex.ofReal_re]
      have hR : 0 ≤ ∑' k : ℕ,
          (intervalNeumannResolverCoeff p (u σ.1) k).re * cosineMode k y :=
        resolverSynthesis_nonneg_all p (u σ.1) (hf_cont σ) (hf_nonneg σ) (hf_coeff σ) (hâ σ) y
      linarith
  -- `h_floor`: `0 < 1 + R`.  `R ≥ 0` via O1 positivity of the nonneg source `f τ`.
  have h_floor : 0 < 1 + intervalNeumannResolverR p (u τ.1) ⟨x, hxIcc⟩ := by
    have hR : 0 ≤ ∑' k : ℕ,
        (intervalNeumannResolverCoeff p (u τ.1) k).re * cosineMode k x :=
      resolverSynthesis_nonneg_Icc p (u τ.1) (hf_cont τ) (hf_nonneg τ) (hf_coeff τ)
        (hâ τ) hxIcc
    rw [resolverSynthesis_eq_resolverR p (u τ.1) hxIcc] at hR
    linarith
  -- Assemble via `flux_nbhd_of_embed`.
  exact flux_nbhd_of_embed p u hBv hBvnn hBvsum hcont hsummable hcos_series hβpos τ x hx hxIcc
    U hUeq (hsum τ) hER hRealize hgrad hqfloor hqreal h_floor

end ShenWork.EWA

#print axioms ShenWork.EWA.flux_nbhd_of_embed_discharged
