import ShenWork.Wiener.EWA.SourceFluxNbhdDischarge
import ShenWork.Wiener.EWA.SourceFixedPointParity

/-!
# χ₀<0 EWA track — the realization atoms PRODUCED for the Picard fixed point

A prior closeout (`SourceChiNegNegUnconditional.lean`) carried the per-datum
`evalST`-realization atoms

* `h_u`         : `evalST τ x (incl u_star) = (lift (realSlice u_star τ.1) x : ℂ)`,
* `h_uα`        : `evalST τ x (incl (realPowEWA u_star p.α)) = (lift (realSlice …)^α : ℂ)`,
* `h_flux_nbhd` : `evalST τ y (incl (chemFluxEWA … u_star)) = (chemFluxLifted … y : ℂ)`,

as an OPEN frontier, claiming the only producers (`embedEWA_realizes`,
`flux_nbhd_of_embed_discharged`) require an **embed-form** `u_star = embedEWA u …`
and that no `picardEWA → embedEWA` bridge exists.

That claim is **structurally false**: the producers `flux_nbhd_of_realized`
(`FluxRealizeEmbed.lean`) and `slice_smul_realPow_eq_source` (same file) take the
field `U : EWA T 1` **abstract** — the embed form is used by the `*_of_embed`
specializations ONLY to discharge the single base realization
`Re (evalST τ x (incl U)) = lift uR x` (via `embedEWA_realizes`).  For the Picard
fixed point that base realization is **true by DEFINITION** of `realSlice`
(`realSlice u_star t x := (evalST ⟨t,_⟩ ↑x (incl u_star)).re`): with
`uR := realSlice u_star τ.1`, `lift uR x = uR ⟨x,_⟩ = (evalST τ ↑x (incl u_star)).re`
on `[0,1]`.

So this file PRODUCES all three atoms for the abstract fixed point, replaying the
exact discharge skeleton of `flux_nbhd_of_embed_discharged` but with
`embedEWA_realizes` replaced by the definitional `realSlice` unfolding, and the
parity input `EvenRealEWA u_star` supplied by `picardEWA_evenReal_fixedPoint`.

Inputs are exactly the standard fixed-point datum: `EvenRealEWA u_star`, the heat
floor + ball membership (`UniformFloor u_star (δ-ρ)` via `uniformFloor_of_ball`),
the framework-wide resolver-source summability `hsum`, the resolver-gradient ℓ¹
majorant `hgrad`, and the nonneg continuous resolver-source data (the same O1
positivity input the embed track carries) — NO embed form, NO `hfp`.

## Status

The three CORE realization atoms (`h_u`, `h_uα`, `h_flux_nbhd`) are now PRODUCED for
the abstract Picard fixed point as the named lemmas `realSlice_evalST_realizes`,
`realSlice_realPow_realizes`, `realSlice_flux_realizes` (all axiom-clean).  These
are exactly the atoms `realizes_clean` / `realSlice_realizes_of_atoms` consume to
deliver the slab `hrealizes`; from there `realSlice_reducedCore` is fed.

What is NOT yet produced (the remaining residual for a fully unconditional headline):
the secondary regularity side-atoms still carried by `realizes_clean` /
`realSlice_reducedCore` and not produced anywhere in the tree — `h_flux_diff`
(`DifferentiableAt … (chemFluxLifted …)`), `h_src_cont_chem`/`h_src_cont_log`
(continuity of `wChem`/`wLog`), the eigenvalue-ℓ¹ summabilities and
`DuhamelSourceTimeC1` packages, and the `htime`/`hlap`/inversion/trace inputs —
together with the per-datum contraction estimates that select the fixed point.

No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/

open scoped BigOperators
open Set Metric
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.PDE
  (intervalNeumannResolverR intervalNeumannResolverCoeff
    intervalNeumannResolverSourceCoeff)
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### The base realization `h_u` for the fixed point — definitional. -/

/-- **The base realization for `realSlice`.**  For ANY `u_star : EWA T 1` the
Wiener point-evaluation of `incl u_star` realizes the lift of its own real slice
on `[0,1]`, PROVIDED `evalST` is real there (`(evalST …).im = 0`).  This is the
no-embed replacement for `embedEWA_realizes`: `realSlice u_star τ.1 ⟨x,_⟩` is by
definition the real part, so the identity is `z = (z.re : ℂ)` under `z.im = 0`. -/
theorem realSlice_evalST_realizes (u_star : EWA T 1) (τ : TimeDom T) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hreal : (evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)).im = 0) :
    evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)
      = (intervalDomainLift (realSlice u_star τ.1) x : ℂ) := by
  -- `lift (realSlice …) x = realSlice … ⟨x,hx⟩ = (evalST ⟨τ.1,_⟩ ↑x …).re`.
  have hτ : (⟨τ.1, τ.2⟩ : TimeDom T) = τ := Subtype.ext rfl
  have hlift : intervalDomainLift (realSlice u_star τ.1) x
      = (evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)).re := by
    rw [intervalDomainLift, dif_pos hx, realSlice, dif_pos τ.2, hτ]
  rw [hlift]
  apply Complex.ext
  · rw [Complex.ofReal_re]
  · rw [Complex.ofReal_im, hreal]

/-- Full-circle reality of `evalST (incl u_star)` from `EvenRealEWA u_star`. -/
theorem evalST_incl_im_zero_of_evenReal {u_star : EWA T 1}
    (hER : EvenRealEWA u_star) (τ : TimeDom T) (y : WA.Circ) :
    (evalST τ y (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)).im = 0 := by
  have hER0 : EvenRealEWA (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star) := hER.incl (by omega)
  induction y using QuotientAddGroup.induction_on with
  | _ y =>
    rw [evalST_eq_cosineSynthesis_of_even_real (fun n => hER0.even τ n)
      (fun n => hER0.real τ n) y, Complex.ofReal_im]

/-! ### `h_uα` for the fixed point — `realPowEWA_eval` + reality + floor. -/

/-- **`h_uα` PRODUCED for the fixed point.**  Under `EvenRealEWA u_star` and the
uniform floor `UniformFloor u_star δ`, the Wiener synthesis of `incl (realPowEWA
u_star p.α)` realizes `(lift (realSlice u_star τ.1) x)^α` on `[0,1]`. -/
theorem realSlice_realPow_realizes (p : CM2Params) (u_star : EWA T 1)
    {δ : ℝ} (hδpos : 0 < δ) (hER : EvenRealEWA u_star)
    (hfloor : UniformFloor u_star δ) (hα : 0 ≤ p.α)
    (τ : TimeDom T) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1) (realPowEWA u_star p.α))
      = ((intervalDomainLift (realSlice u_star τ.1) x ^ p.α : ℝ) : ℂ) := by
  have hreal := evalST_incl_im_zero_of_evenReal hER
  rw [realPowEWA_eval hα hδpos hfloor hreal τ (x : WA.Circ)]
  -- `Re (evalST (incl u_star)) = lift (realSlice u_star τ.1) x`.
  have hbase := realSlice_evalST_realizes u_star τ x hx (hreal τ (x : WA.Circ))
  rw [hbase, Complex.ofReal_re]

/-! ### `h_flux_nbhd` for the fixed point — `flux_nbhd_of_realized` (abstract `U`). -/

/-- **`h_flux_nbhd` PRODUCED for the fixed point.**  Replays the discharge skeleton
of `flux_nbhd_of_embed_discharged`, but with the abstract producer
`flux_nbhd_of_realized` (so NO embed form), the base realization supplied
definitionally for `realSlice`, and the parity input from `EvenRealEWA u_star`.

The carried analytic inputs are exactly the no-embed fixed-point datum: the
uniform floor `UniformFloor u_star δ`, the resolver-source summability `hsum`, the
resolver-gradient ℓ¹ majorant `hgrad`, the spectral-floor constraint `p.μ ≤ 1`,
and the nonneg continuous resolver-source data (the O1 positivity input). -/
theorem realSlice_flux_realizes (p : CM2Params) (u_star : EWA T 1)
    {δ : ℝ} (hδpos : 0 < δ) (hβpos : 0 < p.β) (hER : EvenRealEWA u_star)
    (hfloor : UniformFloor u_star δ)
    (τ : TimeDom T) (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : ∀ σ : TimeDom T, ResolverSourceSummable p (realSlice u_star σ.1))
    (hgrad : Summable fun k : ℕ =>
      |(intervalNeumannResolverCoeff p (realSlice u_star τ.1) k).re| * ((k : ℝ) * Real.pi))
    (hμle1 : p.μ ≤ 1)
    (f : ℝ → ℝ → ℝ) (hf_cont : ∀ σ : TimeDom T, Continuous (f σ.1))
    (hf_nonneg : ∀ (σ : TimeDom T) (y : ℝ), 0 ≤ f σ.1 y)
    (hf_coeff : ∀ (σ : TimeDom T) (k : ℕ),
      cosineCoeffs (f σ.1) k = (intervalNeumannResolverSourceCoeff p (realSlice u_star σ.1) k).re)
    (hâ : ∀ σ : TimeDom T, Summable (fun k => (cosineCoeffs (f σ.1) k) ^ 2)) :
    evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (chemFluxEWA p.μ p.ν p.β p.γ p.hμ u_star))
      = ((chemFluxLifted p (realSlice u_star τ.1) x : ℝ) : ℂ) := by
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  -- reality of `evalST (incl u_star)` (full circle).
  have hUreal := evalST_incl_im_zero_of_evenReal hER
  -- the base realization `h_u` (definitional for `realSlice`).
  have h_u : evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)
      = (intervalDomainLift (realSlice u_star τ.1) x : ℂ) :=
    realSlice_evalST_realizes u_star τ x hxIcc (hUreal τ (x : WA.Circ))
  -- `incl (ν • realPowEWA u_star γ)` is even-real.
  have hERsmul : EvenRealEWA (GWA.incl (by omega : (0 : ℕ) ≤ 1)
      ((p.ν : ℂ) • realPowEWA u_star p.γ)) :=
    ((realPowEWA_evenReal FnegEWA_evenReal_Hyp_proved hER p.γ).smul_real p.ν).incl (by omega)
  -- `hRealize`: `incl (ν • realPowEWA u_star γ)` realizes `ν · (lift)^γ` on (0,1).
  have hRealize : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (y : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
          ((p.ν : ℂ) • realPowEWA u_star p.γ))
        = ((p.ν * intervalDomainLift (realSlice u_star τ.1) y ^ p.γ : ℝ) : ℂ) := by
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2.le⟩
    have hincl_smul : GWA.incl (by omega : (0 : ℕ) ≤ 1)
          ((p.ν : ℂ) • realPowEWA u_star p.γ)
        = (p.ν : ℂ) • GWA.incl (by omega : (0 : ℕ) ≤ 1) (realPowEWA u_star p.γ) := by
      rw [← GWA.gIncl_apply, map_smul, GWA.gIncl_apply]
    rw [hincl_smul, evalST_smul,
      realPowEWA_eval p.hγ.le hδpos hfloor hUreal τ (y : WA.Circ)]
    rw [(realSlice_evalST_realizes u_star τ y hyIcc (hUreal τ (y : WA.Circ))),
      Complex.ofReal_re]
    push_cast; ring
  -- `hWslice`: the crux slice-coefficient identity.
  have hWslice : (sliceWA τ (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        ((p.ν : ℂ) • realPowEWA u_star p.γ))).toFun
      = ofCosineCoeffs (resolverSourceReCoeff p (realSlice u_star τ.1)) :=
    slice_smul_realPow_eq_source p (fun s => realSlice u_star s) u_star τ hERsmul hRealize
  -- `hqreal`: `1 + incl(1≤3)(vFieldEWA … u_star)` is even-real ⇒ real.
  have hqreal : ∀ (σ : TimeDom T) (y : WA.Circ),
      (evalST σ y (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (1 + GWA.incl (by omega : (1 : ℕ) ≤ 3)
          (vFieldEWA p.μ p.ν p.γ p.hμ u_star)))).im = 0 := by
    intro σ y
    have hvER : EvenRealEWA (1 + GWA.incl (by omega : (1 : ℕ) ≤ 3)
        (vFieldEWA p.μ p.ν p.γ p.hμ u_star)) :=
      EvenRealEWA.one.add
        ((vFieldEWA_evenReal FnegEWA_evenReal_Hyp_proved p.hμ hER).incl (by omega))
    have hER0 : EvenRealEWA (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (1 + GWA.incl (by omega : (1 : ℕ) ≤ 3) (vFieldEWA p.μ p.ν p.γ p.hμ u_star))) :=
      hvER.incl (by omega)
    induction y using QuotientAddGroup.induction_on with
    | _ y =>
      rw [evalST_eq_cosineSynthesis_of_even_real (fun n => hER0.even σ n)
        (fun n => hER0.real σ n) y, Complex.ofReal_im]
  -- `hqfloor`: per-σ resolver synthesis `≥ 1 ≥ μ`.
  have hqfloor : UniformFloor (1 + GWA.incl (by omega : (1 : ℕ) ≤ 3)
      (vFieldEWA p.μ p.ν p.γ p.hμ u_star)) p.μ := by
    intro σ y
    induction y using QuotientAddGroup.induction_on with
    | _ y =>
      have hincl_one : GWA.incl (by omega : (0 : ℕ) ≤ 1) (1 : EWA T 1) = 1 := by
        rw [← GWA.gIncl_apply, map_one]
      have hincl_add : GWA.incl (by omega : (0 : ℕ) ≤ 1)
            (1 + GWA.incl (by omega : (1 : ℕ) ≤ 3) (vFieldEWA p.μ p.ν p.γ p.hμ u_star))
          = GWA.incl (by omega : (0 : ℕ) ≤ 1) (1 : EWA T 1)
            + GWA.incl (by omega : (0 : ℕ) ≤ 1) (GWA.incl (by omega : (1 : ℕ) ≤ 3)
                (vFieldEWA p.μ p.ν p.γ p.hμ u_star)) := by
        rw [← GWA.gIncl_apply, map_add, GWA.gIncl_apply, GWA.gIncl_apply]
      -- the crux slice identity at `σ` (rebuilt; `hWslice` above is at `τ` only).
      have hWsliceσ : (sliceWA σ (GWA.incl (by omega : (0 : ℕ) ≤ 1)
            ((p.ν : ℂ) • realPowEWA u_star p.γ))).toFun
          = ofCosineCoeffs (resolverSourceReCoeff p (realSlice u_star σ.1)) :=
        slice_smul_realPow_eq_source p (fun s => realSlice u_star s) u_star σ hERsmul
          (by
            intro z hz
            have hzIcc : z ∈ Set.Icc (0 : ℝ) 1 := ⟨hz.1.le, hz.2.le⟩
            have hincl_smul : GWA.incl (by omega : (0 : ℕ) ≤ 1)
                  ((p.ν : ℂ) • realPowEWA u_star p.γ)
                = (p.ν : ℂ) • GWA.incl (by omega : (0 : ℕ) ≤ 1)
                  (realPowEWA u_star p.γ) := by
              rw [← GWA.gIncl_apply, map_smul, GWA.gIncl_apply]
            rw [hincl_smul, evalST_smul,
              realPowEWA_eval p.hγ.le hδpos hfloor hUreal σ (z : WA.Circ),
              (realSlice_evalST_realizes u_star σ z hzIcc (hUreal σ (z : WA.Circ))),
              Complex.ofReal_re]
            push_cast; ring)
      have hvd : evalST σ (y : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
            (GWA.incl (by omega : (1 : ℕ) ≤ 3)
              (GWA.gResolver p.μ p.hμ ((p.ν : ℂ) • realPowEWA u_star p.γ))))
          = ((∑' k : ℕ,
              (intervalNeumannResolverCoeff p (realSlice u_star σ.1) k).re * cosineMode k y : ℝ)
              : ℂ) :=
        evalST_gResolver_eq_resolverSynthesis_all p (realSlice u_star σ.1)
          ((p.ν : ℂ) • realPowEWA u_star p.γ) σ y (hsum σ) hWsliceσ
      rw [hincl_add, (evalST σ (y : WA.Circ)).map_add, hincl_one,
        (evalST σ (y : WA.Circ)).map_one]
      rw [show vFieldEWA p.μ p.ν p.γ p.hμ u_star
          = GWA.gResolver p.μ p.hμ ((p.ν : ℂ) • realPowEWA u_star p.γ) from rfl, hvd]
      rw [Complex.add_re, Complex.one_re, Complex.ofReal_re]
      have hR : 0 ≤ ∑' k : ℕ,
          (intervalNeumannResolverCoeff p (realSlice u_star σ.1) k).re * cosineMode k y :=
        resolverSynthesis_nonneg_all p (realSlice u_star σ.1) (hf_cont σ) (hf_nonneg σ)
          (hf_coeff σ) (hâ σ) y
      linarith
  -- `h_floor`: `0 < 1 + R`.
  have h_floor : 0 < 1 + intervalNeumannResolverR p (realSlice u_star τ.1) ⟨x, hxIcc⟩ := by
    have hR : 0 ≤ ∑' k : ℕ,
        (intervalNeumannResolverCoeff p (realSlice u_star τ.1) k).re * cosineMode k x :=
      resolverSynthesis_nonneg_Icc p (realSlice u_star τ.1) (hf_cont τ) (hf_nonneg τ)
        (hf_coeff τ) (hâ τ) hxIcc
    rw [resolverSynthesis_eq_resolverR p (realSlice u_star τ.1) hxIcc] at hR
    linarith
  -- assemble via the ABSTRACT flux producer (no embed form).
  exact flux_nbhd_of_realized p u_star (realSlice u_star τ.1) hβpos τ x hx hxIcc
    h_u (hsum τ) hWslice hgrad hqfloor hqreal h_floor

end ShenWork.EWA
