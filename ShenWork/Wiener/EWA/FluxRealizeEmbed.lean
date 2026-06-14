import ShenWork.Wiener.EWA.FluxEvalBridge
import ShenWork.Wiener.EWA.ResolverEvalBridge
import ShenWork.Wiener.EWA.ResolverGradEvalBridge
import ShenWork.Wiener.EWA.EmbedEWA
import ShenWork.Wiener.EWA.NonCircularCoeffBridge
import ShenWork.Wiener.EWA.EvenRealClosure
import ShenWork.PDE.IntervalCoupledRegularityBootstrap

/-!
# EWA brick — discharging `h_flux_nbhd` for the embedded element `embedEWA u`

This file composes the committed eval bridges down the operator stack to discharge
the chemotaxis flux value-realization (`h_flux_nbhd`) for the embedded solution
`U := embedEWA u …`.  The result `flux_nbhd_of_embed` shrinks the FINAL theorem's
conditionality: where the downstream `evalST_chemDivEWA_eq_coupledChemDivSourceLift`
carries `h_flux_nbhd` as a hypothesis, here we PROVE it from the realization chain.

## The composition

`evalST_chemFluxEWA_eq_chemFluxLifted` (FluxEvalBridge) takes three factor
realizations `h_u`/`h_v`/`h_vx` plus the `qFactor` floor/reality + `hβpos`.  We feed:

* **h_u** — `embedEWA_realizes` directly (the base realization on `[0,1]`).
* **h_v** — the resolver VALUE realization
  `evalST τ x (incl (incl (vFieldEWA …))) = (intervalNeumannResolverR p (u τ.1) ⟨x,_⟩ : ℂ)`,
  proved here by `resolver_value_of_slice`: slice the resolver (a `scalarMultiplier`,
  so it commutes with slicing coefficientwise), reduce to the static resolver bridge
  `evalC_gResolver_eq_intervalNeumannResolverR` on the source slice, whose source-coeff
  hypothesis is the crux identity
  `(sliceWA τ (ν • realPowEWA U γ)).toFun = ofCosineCoeffs (resolverSourceReCoeff p (u τ.1))`.
* **h_vx** — the gradient leg, DISCHARGED via the relaxed gradient bridge
  `evalC_gDeriv_vField_eq_resolverGradReal` (per-slice `hreal`) fed the SAME slice-level
  resolver-value realization (`resolver_value_of_slice` + `evalST_inclincl_eq_evalC_toZero`)
  plus the resolver gradient ℓ¹ majorant `hgrad`.

`flux_nbhd_of_realized` states this for an abstract realized `U`; `flux_nbhd_of_embed`
specializes to `U := embedEWA u …` (naming `U` via a single equation `hUeq` so the giant
`embedEWA`/`realPowEWA` term stays out of the heavy floor/parity binders — writing it out
explicitly there triggers a Lean `whnf` blow-up, not a math gap).

## The crux source-coefficient identity (`slice_smul_realPow_eq_source`)

`ν • realPowEWA U γ` is even-real (parity closure `realPowEWA_evenReal` + `smul_real`,
modulo the documented Wiener–Lévy parity hypothesis `FnegEWA_evenReal_Hyp`) and
realizes `ν · (lift u τ.1)^γ` on `(0,1)` (from `realPowEWA_eval` + `embedEWA_realizes`
+ the floor/reality of `embedEWA U`).  So by `slice_eq_ofCosineCoeffs_of_even_real` its
slice is `ofCosineCoeffs (ewaCosCoeffAt …)`, and by
`ewaCosCoeffAt_eq_cosineCoeffs_of_even_real` that extractor equals
`cosineCoeffs (ν · (lift u τ.1)^γ) = resolverSourceReCoeff p (u τ.1)`
(the committed `(intervalNeumannResolverSourceCoeff …).re = cosineCoeffs (ν · lift^γ)`).

The genuinely-open analytic inputs (the Wiener–Lévy parity, the uniform spectral
floor + reality of `embedEWA U`, and the resolver-source / gradient summabilities) are
carried as hypotheses — exactly the documented "floor + per-slice regularity /
realization sub-inputs" of the brick contract.

No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.PDE (intervalNeumannResolverR intervalNeumannResolverCoeff
  intervalNeumannResolverSourceCoeff)
open ShenWork.Paper2 (resolverGradReal cosineCoeffs_congr_on_Icc)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

set_option maxHeartbeats 1000000

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### 1. The crux: the slice of `ν • realPowEWA U γ` is the resolver source embedding. -/

/-- The committed identity (from `IntervalCoupledRegularityBootstrap`):
`resolverSourceReCoeff p u k = cosineCoeffs (fun y => p.ν · (lift u) y ^ p.γ) k`. -/
theorem resolverSourceReCoeff_eq_cosineCoeffs
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (k : ℕ) :
    resolverSourceReCoeff p u k
      = cosineCoeffs (fun y => p.ν * intervalDomainLift u y ^ p.γ) k := by
  simp only [resolverSourceReCoeff, intervalNeumannResolverSourceCoeff, cosineCoeffs,
    Complex.ofReal_re]

/-- **The crux source-coefficient identity.**  For the embedded element
`U := embedEWA u …`, the slice of `(ν:ℂ) • realPowEWA U γ` at time `τ` is the even
embedding of the resolver source coefficient family, with `ν = p.ν`, `γ = p.γ`.

Inputs (carried as hypotheses — the documented realization sub-inputs):
* `hER` — `ν • realPowEWA U γ` is even-real (parity closure modulo Wiener–Lévy);
* `hRealize` — its space-time synthesis realizes `p.ν · (lift u τ.1)^γ` on `(0,1)`. -/
theorem slice_smul_realPow_eq_source
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (U : EWA T 1)
    (τ : TimeDom T)
    (hER : EvenRealEWA (GWA.incl (by omega : (0 : ℕ) ≤ 1) ((p.ν : ℂ) • realPowEWA U p.γ)))
    (hRealize : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
          ((p.ν : ℂ) • realPowEWA U p.γ))
        = ((p.ν * intervalDomainLift (u τ.1) x ^ p.γ : ℝ) : ℂ)) :
    (sliceWA τ (GWA.incl (by omega : (0 : ℕ) ≤ 1) ((p.ν : ℂ) • realPowEWA U p.γ))).toFun
      = ofCosineCoeffs (resolverSourceReCoeff p (u τ.1)) := by
  set F : EWA T 0 := GWA.incl (by omega : (0 : ℕ) ≤ 1) ((p.ν : ℂ) • realPowEWA U p.γ)
    with hF
  set f : ℝ → ℝ := fun y => p.ν * intervalDomainLift (u τ.1) y ^ p.γ with hf
  -- The slice IS `ofCosineCoeffs (ewaCosCoeffAt F τ)` (parity crux).
  have hslice : (sliceWA τ F).toFun = ofCosineCoeffs (ewaCosCoeffAt F τ) :=
    slice_eq_ofCosineCoeffs_of_even_real (fun n => hER.even τ n) (fun n => hER.real τ n)
  rw [hslice]
  -- The extractor `ewaCosCoeffAt F τ` equals `cosineCoeffs f` (non-circular bridge).
  have hcoeff : ∀ k, ewaCosCoeffAt F τ k = cosineCoeffs f k :=
    fun k => ewaCosCoeffAt_eq_cosineCoeffs_of_even_real τ
      (fun n => hER.even τ n) (fun n => hER.real τ n) hRealize k
  -- `cosineCoeffs f = resolverSourceReCoeff p (u τ.1)`.
  have hsrc : ∀ k, ewaCosCoeffAt F τ k = resolverSourceReCoeff p (u τ.1) k := by
    intro k
    rw [hcoeff k, hf, resolverSourceReCoeff_eq_cosineCoeffs]
  exact congrArg ofCosineCoeffs (funext hsrc)

/-- Convert a static `WA 0` membership to a `GWA ℂ 0` membership cheaply: at `r = 0`
both weights collapse to `1`, so the witness is a pointwise `Summable.congr` (avoiding
the deep `MemW 0 = GMemW 0` defeq that would force `whnf` on a giant slice term). -/
theorem gmemW_zero_of_wMem {a : ℤ → ℂ} (h : ShenWork.Wiener.MemW 0 a) :
    GMemW (K := ℂ) 0 a := by
  rw [GMemW]
  rw [ShenWork.Wiener.MemW] at h
  refine h.congr (fun n => ?_)
  rw [GWA.gWeight, ShenWork.Wiener.wWeight]

/-! ### 2. The resolver VALUE realization (`h_v`) for the embedded element. -/

/-- **The resolver value bridge (abstract source).**  For ANY resolver argument
`W : EWA T 1` whose slice at `τ` is the even embedding of the resolver source
coefficients `resolverSourceReCoeff p (u τ.1)` (hypothesis `hWslice`), the Wiener
synthesis of the doubly included resolved field `incl (incl (gResolver p.μ p.hμ W))`,
sliced at `τ` and evaluated at an interior point `x ∈ (0,1)`, realizes the committed
real-space Neumann resolver `intervalNeumannResolverR p (u τ.1) ⟨x,_⟩`.

Since `gResolver` is a `scalarMultiplier`, slicing commutes with it coefficientwise, so
the sliced field matches the static `gResolver p.μ p.hμ s` with `s` the slice of `W`
viewed in `GWA ℂ 0`; `hWslice` makes `s`'s coefficients exactly
`ofCosineCoeffs (resolverSourceReCoeff …)`, so the static resolver bridge
`evalC_gResolver_eq_intervalNeumannResolverR` applies.  The argument `W` is kept
abstract (not unfolded to `ν • realPowEWA …`) so elaboration never reduces the stuck
`Nat.floor p.γ` inside `realPowEWA`. -/
theorem resolver_value_of_slice
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (W : EWA T 1)
    (τ : TimeDom T) (x : ℝ) (hxIcc : x ∈ Set.Icc (0 : ℝ) 1)
    (hsum : ResolverSourceSummable p (u τ.1))
    (hWslice : (sliceWA τ (GWA.incl (by omega : (0 : ℕ) ≤ 1) W)).toFun
      = ofCosineCoeffs (resolverSourceReCoeff p (u τ.1))) :
    evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (GWA.incl (by omega : (1 : ℕ) ≤ 3) (GWA.gResolver p.μ p.hμ W)))
      = ((intervalNeumannResolverR p (u τ.1) ⟨x, hxIcc⟩ : ℝ) : ℂ) := by
  -- The static source element `s : GWA ℂ 0`, built from the slice's `toFun` + `mem`
  -- (cheap `MemW 0 → GMemW 0` to avoid the deep defeq `whnf`).
  set sl : WA 0 := sliceWA τ (GWA.incl (by omega : (0 : ℕ) ≤ 1) W) with hsl
  set s : GWA ℂ 0 := ⟨sl.toFun, gmemW_zero_of_wMem sl.mem⟩ with hs
  -- Its coefficients are the resolver source embedding (crux identity, supplied).
  have hs_eq : s.toFun = ofCosineCoeffs (resolverSourceReCoeff p (u τ.1)) := by
    show sl.toFun = _
    rw [hsl]; exact hWslice
  -- Reduce `evalST` to `WA.evalC` of the sliced double-inclusion `WA 0` element.
  rw [evalST_apply, WA.evalAt_apply, ← WA.evalC_apply]
  -- The committed resolver bridge, on the static source `s`.
  have hbridge := evalC_gResolver_eq_intervalNeumannResolverR p (u τ.1) hsum s hs_eq x hxIcc
  -- The goal's sliced `WA 0` argument has the SAME `toFun` as the bridge's bundled
  -- element (both read `m n • s.toFun n`); `WA.evalC` depends only on `toFun`, so we
  -- reduce to that `toFun` equality via `WA.ext` (no `WA.mem0` defeq is forced).
  refine Eq.trans (congrArg (fun a : WA 0 => WA.evalC a (x : WA.Circ)) ?_) hbridge
  apply WA.ext
  funext n
  -- LHS coefficient: slice commutes with both inclusions (identity coeffs).
  rw [coeff_sliceWA, GWA.incl_toFun, GWA.incl_toFun]
  -- `gResolver` is a scalarMultiplier: the coefficient is `m n • W_n`.
  show ((GWA.gResolver p.μ p.hμ W).toFun n) τ = (GWA.gResolver (K := ℂ) p.μ p.hμ s).toFun n
  rw [GWA.gResolver, GWA.scalarMultiplier_toFun,
    GWA.gResolver, GWA.scalarMultiplier_toFun]
  rw [ContinuousMap.smul_apply]
  -- `(W.toFun n) τ = (sliceWA τ (incl W)).toFun n = s.toFun n`.
  have hWn : (W.toFun n) τ = s.toFun n := by
    show (W.toFun n) τ = sl.toFun n
    rw [hsl, coeff_sliceWA, GWA.incl_toFun]
  rw [hWn]

/-- **The resolver value bridge for `embedEWA`** (specialization to the chemotaxis
field).  `vFieldEWA p.μ p.ν p.γ p.hμ U = gResolver p.μ p.hμ ((p.ν:ℂ) • realPowEWA U p.γ)`,
so this is `resolver_value_of_slice` with `W := (p.ν:ℂ) • realPowEWA U p.γ` and the
slice-coefficient identity supplied by `slice_smul_realPow_eq_source`. -/
theorem resolver_value_of_embed
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (U : EWA T 1)
    (τ : TimeDom T) (x : ℝ) (hxIcc : x ∈ Set.Icc (0 : ℝ) 1)
    (hsum : ResolverSourceSummable p (u τ.1))
    (hER : EvenRealEWA (GWA.incl (by omega : (0 : ℕ) ≤ 1) ((p.ν : ℂ) • realPowEWA U p.γ)))
    (hRealize : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (y : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
          ((p.ν : ℂ) • realPowEWA U p.γ))
        = ((p.ν * intervalDomainLift (u τ.1) y ^ p.γ : ℝ) : ℂ)) :
    evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (GWA.incl (by omega : (1 : ℕ) ≤ 3) (vFieldEWA p.μ p.ν p.γ p.hμ U)))
      = ((intervalNeumannResolverR p (u τ.1) ⟨x, hxIcc⟩ : ℝ) : ℂ) := by
  have hWslice := slice_smul_realPow_eq_source p u U τ hER hRealize
  exact resolver_value_of_slice p u ((p.ν : ℂ) • realPowEWA U p.γ) τ x hxIcc hsum hWslice

/-- **The `evalST = evalC ∘ toZero ∘ sliceWA` link through a double inclusion.**
For `D : EWA T m` (with `1 ≤ m`), the Wiener synthesis of the doubly-included
`incl (0≤1) (incl (h:1≤m) D)`, sliced at `τ` and evaluated at `x`, equals the
slice-level `evalC (toZero (sliceWA τ D)) ↑x`.  Both inclusions preserve `toFun`
coefficientwise (`coeff_sliceWA_incl`), so the sliced `WA 0` element and
`toZero (sliceWA τ D)` share the same `toFun`, and `evalC` depends only on `toFun`.
This is the bridge between the `h_v`/`h_vx` `evalST`-form realizations carried/derived
here and the `evalC (toZero (sliceWA τ ·))` form the gradient bridge consumes/produces. -/
theorem evalST_inclincl_eq_evalC_toZero {m : ℕ} (h : 1 ≤ m) (D : EWA T m)
    (τ : TimeDom T) (x : ℝ) :
    evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1) (GWA.incl h D))
      = (WA.evalC (WA.toZero (sliceWA τ D)) (x : WA.Circ) : ℂ) := by
  rw [evalST_apply, WA.evalAt_apply, ← WA.evalC_apply]
  refine congrArg (fun a : WA 0 => WA.evalC a (x : WA.Circ)) ?_
  apply WA.ext
  funext n
  rw [WA.toZero_toFun, coeff_sliceWA_incl, coeff_sliceWA_incl]

/-! ### 3. The flux value-realization (`h_flux_nbhd`) for the embedded element. -/

/-- **`flux_nbhd_of_realized` — the discharged flux value bridge (abstract `U`).**

For ANY field `U : EWA T 1` realizing the slice `uR` (hypothesis `h_u`), the Wiener
synthesis of the EWA chemotaxis flux `chemFluxEWA p.μ p.ν p.β p.γ p.hμ U`, sliced at `τ`
and evaluated at an interior point `x ∈ (0,1)`, equals the committed real-space lifted
flux `chemFluxLifted p uR x`, cast to `ℂ`.

The resolver value leg `h_v` is DISCHARGED here from the committed resolver bridge
(`resolver_value_of_slice` + the crux source-coeff identity carried as `hWslice`).  The
gradient leg `h_vx` is now ALSO DISCHARGED: the relaxed gradient bridge
`evalC_gDeriv_vField_eq_resolverGradReal` (whose `hreal` is per-slice, not `∀σ`) is fed
the SAME resolver-value realization — taken at the slice level via `resolver_value_of_slice`
+ `evalST_inclincl_eq_evalC_toZero` for every `y ∈ [0,1]` — together with the resolver
gradient ℓ¹ majorant `hgrad`.  Only the base realization `h_u` remains a factor hypothesis.
Keeping `U` abstract (no `embedEWA`/`realPowEWA` giant term in the binders) keeps
elaboration `whnf`-free. -/
theorem flux_nbhd_of_realized
    (p : CM2Params) (U : EWA T 1) (uR : intervalDomainPoint → ℝ)
    (hβpos : 0 < p.β)
    (τ : TimeDom T) (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hxIcc : x ∈ Set.Icc (0 : ℝ) 1)
    -- base realization (h_u):
    (h_u : evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1) U)
      = (intervalDomainLift uR x : ℂ))
    -- resolver source summability + the crux slice-coefficient identity:
    (hsum : ResolverSourceSummable p uR)
    (hWslice : (sliceWA τ (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        ((p.ν : ℂ) • realPowEWA U p.γ))).toFun
      = ofCosineCoeffs (resolverSourceReCoeff p uR))
    -- resolver gradient ℓ¹ majorant (feeds the relaxed gradient bridge for h_vx):
    (hgrad : Summable fun k : ℕ =>
      |(intervalNeumannResolverCoeff p uR k).re| * ((k : ℝ) * Real.pi))
    -- qFactor floor + reality, and the resolver floor:
    (hqfloor : UniformFloor (1 + GWA.incl (by omega : (1 : ℕ) ≤ 3)
        (vFieldEWA p.μ p.ν p.γ p.hμ U)) p.μ)
    (hqreal : ∀ (σ : TimeDom T) (y : WA.Circ),
      (evalST σ y (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (1 + GWA.incl (by omega : (1 : ℕ) ≤ 3) (vFieldEWA p.μ p.ν p.γ p.hμ U)))).im = 0)
    (h_floor : 0 < 1 + intervalNeumannResolverR p uR ⟨x, hxIcc⟩) :
    evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (chemFluxEWA p.μ p.ν p.β p.γ p.hμ U))
      = ((chemFluxLifted p uR x : ℝ) : ℂ) := by
  -- h_v : the resolver value realization (resolver_value_of_slice + the crux identity).
  have h_v : evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (GWA.incl (by omega : (1 : ℕ) ≤ 3) (vFieldEWA p.μ p.ν p.γ p.hμ U)))
      = (intervalNeumannResolverR p uR ⟨x, hxIcc⟩ : ℂ) := by
    -- `vFieldEWA = gResolver p.μ p.hμ (ν • realPowEWA U γ)` definitionally.
    rw [vFieldEWA]
    exact resolver_value_of_slice p (fun _ => uR) ((p.ν : ℂ) • realPowEWA U p.γ)
      τ x hxIcc hsum hWslice
  -- The slice-level resolver-value realization (the relaxed bridge's per-slice `hreal`):
  -- ∀ `y ∈ [0,1]`, `evalC (toZero (sliceWA τ (vFieldEWA … U))) ↑y = R p uR ⟨y,_⟩`.
  have hreal : ∀ (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1),
      (WA.evalC (WA.toZero (sliceWA τ (vFieldEWA p.μ p.ν p.γ p.hμ U))) (y : WA.Circ) : ℂ)
        = ((intervalNeumannResolverR p uR ⟨y, hy⟩ : ℝ) : ℂ) := by
    intro y hy
    rw [← evalST_inclincl_eq_evalC_toZero (by omega : (1 : ℕ) ≤ 3)
      (vFieldEWA p.μ p.ν p.γ p.hμ U) τ y]
    rw [vFieldEWA]
    exact resolver_value_of_slice p (fun _ => uR) ((p.ν : ℂ) • realPowEWA U p.γ)
      τ y hy hsum hWslice
  -- h_vx : DISCHARGED from the relaxed gradient bridge (per-slice `hreal` + `hgrad`).
  have h_vx : evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (GWA.incl (by omega : (1 : ℕ) ≤ 2)
          (GWA.gDeriv (vFieldEWA p.μ p.ν p.γ p.hμ U))))
      = (resolverGradReal p uR x : ℂ) := by
    rw [evalST_inclincl_eq_evalC_toZero (by omega : (1 : ℕ) ≤ 2)
      (GWA.gDeriv (vFieldEWA p.μ p.ν p.γ p.hμ U)) τ x]
    exact evalC_gDeriv_vField_eq_resolverGradReal p uR (vFieldEWA p.μ p.ν p.γ p.hμ U)
      τ hreal hgrad x hx
  -- Compose the three factor realizations through the committed FluxEvalBridge.
  exact evalST_chemFluxEWA_eq_chemFluxLifted p.μ p.ν p.γ p.hμ p U uR τ x hx hxIcc
    h_u h_vx h_v hqfloor hqreal hβpos h_floor

/-- **`flux_nbhd_of_embed` — the discharged flux value bridge for `embedEWA u`.**

The specialization of `flux_nbhd_of_realized` to the embedded solution
`U := embedEWA u …`: `h_u` is `embedEWA_realizes`, and the crux slice-coefficient
identity `hWslice` is `slice_smul_realPow_eq_source` (the intricate resolver-source
link).  The realPow even-real (`hER`) + realization (`hRealize`) inputs that feed
`slice_smul_realPow_eq_source` are the documented per-slice realization hypotheses.

The embedded field is named via the single small equation `hUeq : U = embedEWA u …`
so the giant `embedEWA`/`realPowEWA` term never appears inside the heavy floor/parity
binders (which forced a `whnf` blow-up when written out explicitly).

## The gradient leg `h_vx` is now DISCHARGED

The committed gradient bridge `evalC_gDeriv_vField_eq_resolverGradReal` was relaxed so its
value realization `hreal` is per-slice (at the theorem's `τ`), not `∀σ` with a single fixed
`uR`.  The embedded field realizes the resolver of the slice `u τ.1` at `τ`, which is
exactly that per-slice `hreal` — so `flux_nbhd_of_realized` discharges `h_vx` internally
(relaxed gradient bridge + the resolver-value realization at the slice + the gradient ℓ¹
majorant `hgrad`).  No `h_vx` hypothesis is carried any more; only the resolver gradient
majorant `hgrad` is added.

The embedded field is named via the single small equation `hUeq : U = embedEWA u …`
so the giant `embedEWA`/`realPowEWA` term never appears inside the heavy floor/parity
binders (which forced a `whnf` blow-up when written out explicitly). -/
theorem flux_nbhd_of_embed
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
    -- the embedded field, named abstractly to keep the giant term out of the binders:
    (U : EWA T 1) (hUeq : U = embedEWA u hBv hBvnn hBvsum hcont)
    (hsum : ResolverSourceSummable p (u τ.1))
    (hER : EvenRealEWA (GWA.incl (by omega : (0 : ℕ) ≤ 1) ((p.ν : ℂ) • realPowEWA U p.γ)))
    (hRealize : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (y : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
          ((p.ν : ℂ) • realPowEWA U p.γ))
        = ((p.ν * intervalDomainLift (u τ.1) y ^ p.γ : ℝ) : ℂ))
    -- resolver gradient ℓ¹ majorant (feeds the relaxed gradient bridge for h_vx):
    (hgrad : Summable fun k : ℕ =>
      |(intervalNeumannResolverCoeff p (u τ.1) k).re| * ((k : ℝ) * Real.pi))
    (hqfloor : UniformFloor (1 + GWA.incl (by omega : (1 : ℕ) ≤ 3)
        (vFieldEWA p.μ p.ν p.γ p.hμ U)) p.μ)
    (hqreal : ∀ (σ : TimeDom T) (y : WA.Circ),
      (evalST σ y (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (1 + GWA.incl (by omega : (1 : ℕ) ≤ 3) (vFieldEWA p.μ p.ν p.γ p.hμ U)))).im = 0)
    (h_floor : 0 < 1 + intervalNeumannResolverR p (u τ.1) ⟨x, hxIcc⟩) :
    evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (chemFluxEWA p.μ p.ν p.β p.γ p.hμ U))
      = ((chemFluxLifted p (u τ.1) x : ℝ) : ℂ) := by
  -- `h_u` from `embedEWA_realizes`, transported across `hUeq`.
  have h_u : evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1) U)
      = (intervalDomainLift (u τ.1) x : ℂ) := by
    rw [hUeq]
    exact embedEWA_realizes u hBv hBvnn hBvsum hcont hsummable hcos_series τ x hxIcc
  -- the crux slice-coefficient identity (the intricate resolver-source link).
  have hWslice := slice_smul_realPow_eq_source p u U τ hER hRealize
  exact flux_nbhd_of_realized p U (u τ.1) hβpos τ x hx hxIcc
    h_u hsum hWslice hgrad hqfloor hqreal h_floor

end ShenWork.EWA

#print axioms ShenWork.EWA.resolver_value_of_slice
#print axioms ShenWork.EWA.flux_nbhd_of_realized
#print axioms ShenWork.EWA.flux_nbhd_of_embed
