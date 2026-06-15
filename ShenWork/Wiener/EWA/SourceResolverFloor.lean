import ShenWork.Wiener.EWA.FluxRealizeEmbed
import ShenWork.Wiener.EWA.FluxLipschitzGraded
import ShenWork.Wiener.EWA.HeatFloor
import ShenWork.PDE.IntervalResolverPositivity

/-!
# EWA brick (χ₀<0 Route A′) — THE EWA RESOLVER-FLOOR `UniformFloor (1 + vdEWA u) δv`

This file discharges the single named gap `hVdFloor` of `picardEWA_clean_fixedPoint`
(`SourceFixedPointClean.lean`): the **uniform spectral floor of the resolved chemo-signal**
`UniformFloor (1 + vdEWA μ ν γ hμ u) δv` from the committed resolver EVAL bridge
(`evalC_gResolver_eq_intervalNeumannResolverR` / `resolver_value_of_slice`) and the
committed O1 resolver positivity (`intervalNeumannResolverR_nonneg_of_nonneg_source`).

It **mirrors** `HeatFloor.lean` (eval bridge + floor):

* `heatEWA_evalST_eq_cosineHeatValue`  ↔  `evalST_vdEWA_eq_resolverSynthesis` (A);
* `cosineHeatValue_ge_floor_all`        ↔  `resolverSynthesis_nonneg_all` (E);
* `heatEWA_uniformFloor`                ↔  `vdEWA_uniformFloor` (F).

## (A) THE RESOLVER EVAL BRIDGE — full circle

`vdEWA u = incl(1≤3)(vFieldEWA u)` and `vFieldEWA u = gResolver μ hμ (ν•realPowEWA u γ)`
(`Flux.lean`).  The committed `resolver_value_of_slice` evaluates the *interior* value of
`evalST (incl (incl (vFieldEWA …)))` as `(intervalNeumannResolverR p uR ⟨x,_⟩ : ℂ)` from
the crux slice-coefficient realization `hWslice`.  Mirroring `heatEWA_evalST_eq_…`, we
re-derive the **full-circle synthesis** form
`evalST τ x (incl (vdEWA u)) = (∑' k, d_k · cosineMode k x : ℂ)` for EVERY real `x`,
with `d_k = (intervalNeumannResolverCoeff p uR k).re` the resolved cosine coefficients —
via the committed full-circle synthesis `evalC_ofCosineCoeffs_all` (the SAME engine
HeatFloor used).  This is the resolver analogue of the diagonal heat synthesis: the
gResolver is a `scalarMultiplier`, so slicing/evaluation is term-by-term.

## (B) THE RESOLVER POSITIVITY → FLOOR

Through the committed O1 positivity `intervalNeumannResolverR_nonneg_of_nonneg_source`
(the `[0,1]` Neumann resolver of a *nonneg* real source is `≥ 0`, the `T→∞` limit of
nonnegative heat truncations), the cosine synthesis `∑' k d_k · cosineMode k x` is `≥ 0`
on `[0,1]`; period-2 evenness reduces ALL real `x` to a representative in `[0,1]` (exactly
as HeatFloor's `_all`).  Hence `Re(evalST(incl(1+vd))) = 1 + R ≥ 1 ≥ δv` (for `0<δv≤1`),
uniformly in `τ` and `x` (no interior restriction: `R ≥ 0` everywhere).

The realization sub-inputs (the crux slice-coefficient identity `hWslice`, the resolver
source summability `hsum`, and the nonneg real source `f` realizing the source coeffs) are
carried as hypotheses — exactly the documented "floor + per-slice realization sub-inputs"
of the brick contract, identical in spirit to `flux_nbhd_of_realized`'s `hWslice`.

No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.PDE (intervalNeumannResolverR intervalNeumannResolverCoeff
  intervalNeumannResolverSourceCoeff)
open ShenWork.IntervalResolverPositivity (intervalNeumannResolverR_nonneg_of_nonneg_source)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### (A) THE RESOLVER EVAL BRIDGE — full-circle synthesis form. -/

/-- The resolved cosine-coefficient family `d_k = (v̂_k).re`, summable from `hsum`
(`|d_k| ≤ |source_k|/μ`, exactly as in `evalC_gResolver_eq_intervalNeumannResolverR`). -/
theorem resolverResolvedCoeff_summable (p : CM2Params) (uR : intervalDomainPoint → ℝ)
    (hsum : ResolverSourceSummable p uR) :
    Summable (fun k => |(intervalNeumannResolverCoeff p uR k).re|) := by
  have hcsum : Summable (fun k => |resolverSourceReCoeff p uR k|) := hsum
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _)
    (fun k => ?_) (hcsum.div_const p.μ)
  have heq := resolverOutputCoeff_eq_resolverCoeff_re p uR k
  have hden_pos : 0 < p.μ + ((k : ℝ) * Real.pi) ^ 2 := by
    have : (0 : ℝ) ≤ ((k : ℝ) * Real.pi) ^ 2 := sq_nonneg _
    linarith [p.hμ]
  rw [← heq, abs_div, abs_of_pos hden_pos]
  apply div_le_div_of_nonneg_left (abs_nonneg _) p.hμ
  have : (0 : ℝ) ≤ ((k : ℝ) * Real.pi) ^ 2 := sq_nonneg _
  linarith

/-- **THE RESOLVER EVAL BRIDGE (A) — full circle.**  For a resolver argument
`W : EWA T 1` whose slice at `τ` is the even embedding of the resolver source
coefficients `resolverSourceReCoeff p uR` (hypothesis `hWslice`), the Wiener synthesis of
the doubly-included resolved field, sliced at `τ` and evaluated at EVERY real `x`, equals
the cosine synthesis `(∑' k, (v̂_k).re · cosineMode k x : ℂ)` of the resolved coefficients.

This is the resolver analogue of `heatEWA_evalST_eq_cosineHeatValue` (full circle, all `x`):
`gResolver` is a `scalarMultiplier`, so slicing commutes coefficientwise; the sliced field's
`toFun` is `ofCosineCoeffs d`, to which the committed full-circle synthesis
`evalC_ofCosineCoeffs_all` applies. -/
theorem evalST_gResolver_eq_resolverSynthesis_all
    (p : CM2Params) (uR : intervalDomainPoint → ℝ) (W : EWA T 1)
    (τ : TimeDom T) (x : ℝ)
    (hsum : ResolverSourceSummable p uR)
    (hWslice : (sliceWA τ (GWA.incl (by omega : (0 : ℕ) ≤ 1) W)).toFun
      = ofCosineCoeffs (resolverSourceReCoeff p uR)) :
    evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (GWA.incl (by omega : (1 : ℕ) ≤ 3) (GWA.gResolver p.μ p.hμ W)))
      = ((∑' k : ℕ, (intervalNeumannResolverCoeff p uR k).re * cosineMode k x : ℝ)
          : ℂ) := by
  -- The resolved coefficient family `d` and its summability.
  set d : ℕ → ℝ := fun k => (intervalNeumannResolverCoeff p uR k).re with hd_def
  have hdsum : Summable (fun k => |d k|) := resolverResolvedCoeff_summable p uR hsum
  -- The static source `s : GWA ℂ 0`, built from the slice (cheap `MemW 0 → GMemW 0`).
  set sl : WA 0 := sliceWA τ (GWA.incl (by omega : (0 : ℕ) ≤ 1) W) with hsl
  set s : GWA ℂ 0 := ⟨sl.toFun, gmemW_zero_of_wMem sl.mem⟩ with hs
  have hs_eq : s.toFun = ofCosineCoeffs (resolverSourceReCoeff p uR) := by
    change sl.toFun = _; rw [hsl]; exact hWslice
  -- Reduce `evalST` to `WA.evalC` of the sliced double-inclusion `WA 0` element.
  rw [evalST_apply, WA.evalAt_apply, ← WA.evalC_apply]
  -- The static gResolver output `(gResolver p.μ p.hμ s).toFun = ofCosineCoeffs d`
  -- (committed coefficient bridge + the source/multiplier match).
  have hcG : Summable (fun k : ℕ => (1 + (k : ℝ)) ^ (0 : ℕ)
      * |resolverSourceReCoeff p uR k|) := by simpa using (hsum : ResolverSourceSummable p uR)
  have hs_cosG : s = cosG 0 (resolverSourceReCoeff p uR) hcG := by
    apply GWA.ext; rw [hs_eq, cosG_toFun]
  have hgr := gResolver_ofCosineCoeffs (r := 0) (c := resolverSourceReCoeff p uR) p.μ p.hμ hcG
  have hsout : (GWA.gResolver (K := ℂ) p.μ p.hμ s).toFun = ofCosineCoeffs d := by
    rw [hs_cosG, hgr]
    refine congrArg ofCosineCoeffs (funext (fun k => ?_))
    exact resolverOutputCoeff_eq_resolverCoeff_re p uR k
  -- The sliced field's `toFun` equals `(gResolver p.μ p.hμ s).toFun` (scalarMultiplier
  -- commutes with slicing coefficientwise).
  have htoFun :
      (sliceWA τ (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (GWA.incl (by omega : (1 : ℕ) ≤ 3) (GWA.gResolver p.μ p.hμ W)))).toFun
      = ofCosineCoeffs d := by
    rw [← hsout]
    funext n
    rw [coeff_sliceWA, GWA.incl_toFun, GWA.incl_toFun]
    change ((GWA.gResolver p.μ p.hμ W).toFun n) τ
        = (GWA.gResolver (K := ℂ) p.μ p.hμ s).toFun n
    rw [GWA.gResolver, GWA.scalarMultiplier_toFun, GWA.gResolver, GWA.scalarMultiplier_toFun,
      ContinuousMap.smul_apply]
    have hWn : (W.toFun n) τ = s.toFun n := by
      change (W.toFun n) τ = sl.toFun n; rw [hsl, coeff_sliceWA, GWA.incl_toFun]
    rw [hWn]
  -- Apply the committed full-circle synthesis to the `ofCosineCoeffs d` element: the sliced
  -- field and `⟨ofCosineCoeffs d, _⟩` share the same `toFun` (`htoFun`), and `evalC` depends
  -- only on `toFun`.
  refine Eq.trans (congrArg (fun a : WA 0 => WA.evalC a (x : WA.Circ)) ?_)
    (evalC_ofCosineCoeffs_all d hdsum x)
  exact WA.ext htoFun

/-! ### (B) NONNEGATIVITY of the resolver synthesis for all real `x`. -/

/-- The resolver cosine synthesis equals the committed `intervalNeumannResolverR` on the
fundamental domain `[0,1]` (basis match `cosineMode = unitIntervalCosineMode`). -/
theorem resolverSynthesis_eq_resolverR (p : CM2Params) (uR : intervalDomainPoint → ℝ)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∑' k : ℕ, (intervalNeumannResolverCoeff p uR k).re * cosineMode k x)
      = intervalNeumannResolverR p uR ⟨x, hx⟩ := by
  rw [intervalNeumannResolverR]
  exact tsum_congr (fun k => by rw [unitIntervalCosineMode_eq_cosineMode])

/-- **Nonnegativity on `[0,1]`.**  The resolver synthesis is `≥ 0` on the fundamental
domain, from the committed O1 positivity of a nonneg real source. -/
theorem resolverSynthesis_nonneg_Icc (p : CM2Params) (uR : intervalDomainPoint → ℝ)
    {f : ℝ → ℝ} (hf_cont : Continuous f) (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_coeff : ∀ k, cosineCoeffs f k = (intervalNeumannResolverSourceCoeff p uR k).re)
    (hâ : Summable (fun k => (cosineCoeffs f k) ^ 2))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ ∑' k : ℕ, (intervalNeumannResolverCoeff p uR k).re * cosineMode k x := by
  rw [resolverSynthesis_eq_resolverR p uR hx]
  exact intervalNeumannResolverR_nonneg_of_nonneg_source hf_cont hf_nonneg hf_coeff hâ ⟨x, hx⟩

/-- **Nonnegativity for ALL real `x`.**  Period-2 evenness reduces an arbitrary `x` to a
representative in `[0,1]` (exactly as `cosineHeatValue_ge_floor_all`), where O1 applies. -/
theorem resolverSynthesis_nonneg_all (p : CM2Params) (uR : intervalDomainPoint → ℝ)
    {f : ℝ → ℝ} (hf_cont : Continuous f) (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_coeff : ∀ k, cosineCoeffs f k = (intervalNeumannResolverSourceCoeff p uR k).re)
    (hâ : Summable (fun k => (cosineCoeffs f k) ^ 2)) (x : ℝ) :
    0 ≤ ∑' k : ℕ, (intervalNeumannResolverCoeff p uR k).re * cosineMode k x := by
  set d : ℕ → ℝ := fun k => (intervalNeumannResolverCoeff p uR k).re with hd_def
  -- `y = x - 2·round(x/2) ∈ [-1,1]`, and the synthesis is period-2 (integer shift) + even.
  set m : ℤ := round (x / 2) with hm
  set y : ℝ := x - 2 * m with hy
  have hVxy : (∑' k : ℕ, d k * cosineMode k x) = ∑' k : ℕ, d k * cosineMode k y := by
    refine tsum_congr (fun k => ?_)
    rw [show x = y + 2 * (m : ℝ) from by rw [hy]; ring, cosineMode_add_int_two]
  have hyabs : |y| ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨abs_nonneg _, ?_⟩
    have hround : |x / 2 - (m : ℝ)| ≤ 1 / 2 := by rw [hm]; exact abs_sub_round (x / 2)
    rw [hy, show x - 2 * (m : ℝ) = 2 * (x / 2 - (m : ℝ)) from by ring, abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith [hround]
  have hVy : (∑' k : ℕ, d k * cosineMode k y) = ∑' k : ℕ, d k * cosineMode k |y| := by
    rcases abs_choice y with h | h
    · rw [h]
    · rw [h]; exact tsum_congr (fun k => by rw [cosineMode_neg])
  rw [hVxy, hVy]
  exact resolverSynthesis_nonneg_Icc p uR hf_cont hf_nonneg hf_coeff hâ hyabs

/-! ### (F) THE FINAL `UniformFloor` — assembling the eval bridge with the resolver floor. -/

/-- **THE EWA RESOLVER-FLOOR (F).**  For a resolver argument `u : EWA T 1` whose slice at
every time realizes the resolver source of a *nonneg continuous* real source `f` (the
documented per-slice realization sub-inputs `hWslice`/`hsum`/`hf_*`), the resolved field
`vdEWA μ ν γ hμ u = incl(1≤3)(gResolver μ hμ (ν•realPowEWA u γ))` satisfies the uniform
spectral floor `UniformFloor (1 + vdEWA μ ν γ hμ u) δv` for any `0 < δv ≤ 1`.

This discharges the `hVdFloor` gap of `picardEWA_clean_fixedPoint`: at every time `τ` and
circle point `x`, the included `1 + vd` symbol has real part `1 + R(uR)(x') ≥ 1 ≥ δv`.  Via
the resolver eval bridge (A) the resolved value is the real cast `∑' k (v̂_k).re·cosineMode`,
whose real part is itself; the O1 floor (B) — `R ≥ 0` on all real `x` — closes it.

The resolver argument is supplied as `W` with `vFieldEWA μ ν γ hμ u = gResolver μ hμ W`
(definitionally `W = (ν:ℂ)•realPowEWA u γ`); the slice realization `hWslice` is the crux
identity (committed `slice_smul_realPow_eq_source`). -/
theorem vdEWA_uniformFloor
    (p : CM2Params) (uR : intervalDomainPoint → ℝ) {δv : ℝ}
    (u : EWA T 1)
    (hsum : ResolverSourceSummable p uR)
    (hWslice : ∀ τ : TimeDom T, (sliceWA τ (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        ((p.ν : ℂ) • realPowEWA u p.γ))).toFun
      = ofCosineCoeffs (resolverSourceReCoeff p uR))
    {f : ℝ → ℝ} (hf_cont : Continuous f) (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_coeff : ∀ k, cosineCoeffs f k = (intervalNeumannResolverSourceCoeff p uR k).re)
    (hâ : Summable (fun k => (cosineCoeffs f k) ^ 2))
    (_hδv_pos : 0 < δv) (hδv_le : δv ≤ 1) :
    UniformFloor (1 + vdEWA p.μ p.ν p.γ p.hμ u) δv := by
  intro τ x
  -- lift the circle point `x : WA.Circ = AddCircle 2` to a real representative.
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
    -- `evalST(incl(1+vd)) = 1 + evalST(incl(vd))` (ring-hom structure of `evalST ∘ incl`).
    have hincl_one : GWA.incl (by omega : (0:ℕ) ≤ 1) (1 : EWA T 1) = 1 := by
      rw [← GWA.gIncl_apply, map_one]
    have hincl_add : GWA.incl (by omega : (0:ℕ) ≤ 1) (1 + vdEWA p.μ p.ν p.γ p.hμ u)
        = GWA.incl (by omega : (0:ℕ) ≤ 1) (1 : EWA T 1)
          + GWA.incl (by omega : (0:ℕ) ≤ 1) (vdEWA p.μ p.ν p.γ p.hμ u) := by
      rw [← GWA.gIncl_apply, map_add, GWA.gIncl_apply, GWA.gIncl_apply]
    -- the resolver value at `x` via the eval bridge (A).
    have hvd : evalST τ (x : WA.Circ)
          (GWA.incl (by omega : (0:ℕ) ≤ 1) (vdEWA p.μ p.ν p.γ p.hμ u))
        = ((∑' k : ℕ, (intervalNeumannResolverCoeff p uR k).re * cosineMode k x : ℝ)
            : ℂ) := by
      rw [vdEWA, vFieldEWA]
      exact evalST_gResolver_eq_resolverSynthesis_all p uR
        ((p.ν : ℂ) • realPowEWA u p.γ) τ x hsum (hWslice τ)
    rw [hincl_add, (evalST τ (x : WA.Circ)).map_add, hincl_one,
      (evalST τ (x : WA.Circ)).map_one, hvd]
    -- `Re(1 + (R : ℂ)) = 1 + R ≥ 1 ≥ δv`.
    rw [Complex.add_re, Complex.one_re, Complex.ofReal_re]
    have hR : 0 ≤ ∑' k : ℕ, (intervalNeumannResolverCoeff p uR k).re * cosineMode k x :=
      resolverSynthesis_nonneg_all p uR hf_cont hf_nonneg hf_coeff hâ x
    linarith

end ShenWork.EWA

#print axioms ShenWork.EWA.evalST_gResolver_eq_resolverSynthesis_all
#print axioms ShenWork.EWA.vdEWA_uniformFloor
