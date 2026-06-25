# Q380 / cron1: `picardEWA` vs `embedEWA`, and the three evalST realization atoms

## Executive verdict

Reading current `main`, the premise that the three atoms

```lean
h_flux_nbhd
h_u
h_uα
```

are still an irreducible core is **stale / no longer true in the current tree**.

The old diagnosis was reasonable for an earlier state of the EWA route: the embed-form producers

```lean
embedEWA_realizes
flux_nbhd_of_embed_discharged
```

only work for elements explicitly of the form

```lean
embedEWA u hBv hBvnn hBvsum hcont
```

and there is still no theorem literally saying

```lean
u_star = embedEWA (realSlice u_star) ...
```

for a `picardEWA` fixed point.

But the current repo has a **no-embed direct route** in:

```text
ShenWork/Wiener/EWA/SourceChiNegUncond.lean
ShenWork/Wiener/EWA/SourceChiNegUncondWire.lean
```

It proves the three atoms for an abstract Picard fixed point by using `realSlice` directly:

```lean
realSlice_evalST_realizes   -- h_u, pointwise
realSlice_realPow_realizes  -- h_uα, pointwise
realSlice_flux_realizes     -- h_flux_nbhd, pointwise

realSlice_h_u_slab          -- h_u, slab-shaped
realSlice_h_uα_slab         -- h_uα, slab-shaped
realSlice_h_flux_slab       -- h_flux_nbhd, slab-shaped

realizes_evalST_discharged  -- consumes these internally to remove the three hypotheses
```

So the better current summary is:

```text
picardEWA → embedEWA bridge: still not present as equality.
But it is no longer needed for h_u/h_uα/h_flux_nbhd: these are now produced directly for picardEWA/realSlice.
```

The remaining residuals are secondary analytic side-atoms, not these three evalST realization atoms: for example `h_flux_diff`, source continuity, eigenvalue-summability / source-time-C¹ packages, PDE time/laplacian/inversion/trace inputs, and per-datum contraction setup.

---

## (1) What is `picardEWA` vs `embedEWA`?

### `picardEWA`

`picardEWA` is **not itself “the fixed point”**.  It is the **source-form Picard map** on the EWA algebra.  A Picard fixed point is a value `u_star : EWA T 1` satisfying

```lean
u_star = picardEWA p μ ν γ hμ hT u₀E u_star
```

The definition is in `ShenWork/Wiener/EWA/SourceFixedPoint.lean`.

```lean
import ShenWork.Wiener.EWA.FluxLipschitzGraded
import ShenWork.Wiener.EWA.HeatFlow
import ShenWork.Paper2.Defs
import Mathlib.Topology.MetricSpace.Contracting

open scoped BigOperators NNReal ENNReal
open MeasureTheory Set Real Metric Filter Topology
open ShenWork.GWA ShenWork.Wiener

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- **The source-form Picard map** on `EWA T 1`:
`Φ(u) = heatEWA u₀E + (−χ₀)•𝒟(Q(u)) + 𝒱(G(u))`, with `Q = chemFluxEWA`, `G = growthEWA`,
`𝒟 = divDuhamelEWA` (the `C₀√T` divergence-Duhamel) and `𝒱 = valDuhamelEWA` (the `T`
value-Duhamel).  The chemotactic and growth nonlinearities live at grade 1. -/
def picardEWA (p : CM2Params) (μ ν γ : ℝ) (hμ : 0 < μ) (hT : 0 ≤ T)
    (u₀E : WA 1) (u : EWA T 1) : EWA T 1 :=
  heatEWA u₀E
    + ((-p.χ₀ : ℝ) : ℂ) • divDuhamelEWA hT (chemFluxEWA μ ν p.β γ hμ u)
    + valDuhamelEWA hT (growthEWA p.α p.a p.b u)
```

The fixed point theorem is:

```lean
/-- **BRICKS 2–4 assembled (conditional on the carried self-map + Lipschitz data).**
On the good ball `B = closedBall (heatEWA u₀E) ρ`, if

* `hself` : `Φ` maps `B` into `B` (BRICK-2 positivity / floor preservation), and
* `hLipQ` / `hLipG` : the BRICK-1 flux/growth Lipschitz bounds hold for every pair in `B`,
* `hK` : the contraction constant `K = |χ₀|·C₀√T·L_Q + L_G·T < 1` (BRICK-3 small-time),
* `hKnn` : `0 ≤ K`,

then `Φ` has a fixed point in `B`:  `∃ u* ∈ B, u* = Φ(u*)`. -/
theorem picardEWA_exists_fixedPoint {p : CM2Params} {μ ν γ ρ L_Q L_G : ℝ}
    (hμ : 0 < μ) (hT : 0 ≤ T) (u₀E : WA 1) (hρ : 0 ≤ ρ)
    (hself : MapsTo (picardEWA p μ ν γ hμ hT u₀E)
      (Metric.closedBall (heatEWA u₀E) ρ) (Metric.closedBall (heatEWA u₀E) ρ))
    (hLipQ : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ∀ w ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ‖chemFluxEWA μ ν p.β γ hμ u - chemFluxEWA μ ν p.β γ hμ w‖ ≤ L_Q * ‖u - w‖)
    (hLipG : ∀ u ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ∀ w ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      ‖growthEWA p.α p.a p.b u - growthEWA p.α p.a p.b w‖ ≤ L_G * ‖u - w‖)
    (hKnn : (0 : ℝ) ≤ |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T)
    (hK : |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T < 1) :
    ∃ u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ,
      u_star = picardEWA p μ ν γ hμ hT u₀E u_star
```

So yes: `picardEWA` is the Banach-contraction Picard operator in the EWA algebra; `u_star` is the abstract fixed point of that operator.

### `embedEWA`

`embedEWA` is a **function-to-EWA embedding**.  It takes a known real trajectory

```lean
u : ℝ → intervalDomainPoint → ℝ
```

and packages its per-time cosine coefficients into an element of `EWA T 1`.  It is not obtained from a fixed-point theorem; it is built directly from the function’s slice coefficients, with continuity and weighted-ℓ¹ envelope hypotheses.

The definition is in `ShenWork/Wiener/EWA/EmbedEWA.lean`.

```lean
import Mathlib
import ShenWork.Wiener.EWA.CoeffBridge
import ShenWork.Wiener.EWA.EvenRealClosure
import ShenWork.Wiener.WeightedL1CosineAdapter
import ShenWork.PDE.IntervalNeumannFullKernel
import ShenWork.PDE.IntervalDomain
import ShenWork.PDE.CosineSpectrum

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalNeumannFullKernel ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- The underlying `ℝ → ℂ` per-mode coefficient
`t ↦ ofCosineCoeffs (cosineCoeffs (intervalDomainLift (u t))) n`. -/
def embedModeFun (u : ℝ → intervalDomainPoint → ℝ) (n : ℤ) (t : ℝ) : ℂ :=
  ofCosineCoeffs (fun k => cosineCoeffs (intervalDomainLift (u t)) k) n

/-- **The embed construction** `embedEWA u … : EWA T 1`, with `n`-th
time-coefficient `t ↦ ofCosineCoeffs (cosineCoeffs (lift (u t))) n`. -/
def embedEWA (u : ℝ → intervalDomainPoint → ℝ)
    {Bv : ℕ → ℝ} (hBv : ∀ t k, |cosineCoeffs (intervalDomainLift (u t)) k| ≤ Bv k)
    (hBvnn : ∀ k, 0 ≤ Bv k)
    (hBvsum : Summable (fun k : ℕ => (1 + (k : ℝ)) * Bv k))
    (hcont : ∀ n : ℤ, Continuous (embedModeFun u n)) : EWA T 1 :=
  ⟨fun n => embedModeCT u n (hcont n), embedEWA_mem u hBv hBvnn hBvsum hcont⟩
```

And it comes with the key realization theorem:

```lean
/-- **`embedEWA` realizes `u`.**  Given the committed Neumann cosine-series property
of the solution slice (`hcos_series`: `lift (u t)` IS its cosine series on `[0,1]`),
the space-time synthesis of `embedEWA u …` reproduces `lift (u τ.1) x` for every
`τ` and `x ∈ [0,1]`. -/
theorem embedEWA_realizes (u : ℝ → intervalDomainPoint → ℝ)
    {Bv : ℕ → ℝ} (hBv : ∀ t k, |cosineCoeffs (intervalDomainLift (u t)) k| ≤ Bv k)
    (hBvnn : ∀ k, 0 ≤ Bv k)
    (hBvsum : Summable (fun k : ℕ => (1 + (k : ℝ)) * Bv k))
    (hcont : ∀ n : ℤ, Continuous (embedModeFun u n))
    (hsummable : ∀ t, Summable (fun k => |cosineCoeffs (intervalDomainLift (u t)) k|))
    (hcos_series : ∀ t x, x ∈ Set.Icc (0:ℝ) 1 →
      intervalDomainLift (u t) x
        = ∑' k : ℕ, cosineCoeffs (intervalDomainLift (u t)) k * cosineMode k x)
    (τ : TimeDom T) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    evalST τ (x : WA.Circ)
        (GWA.incl (by omega : (0:ℕ) ≤ 1) (embedEWA u hBv hBvnn hBvsum hcont))
      = (intervalDomainLift (u τ.1) x : ℂ)
```

So yes: `embedEWA` is a packaging/embedding construction for a known physical function, while `picardEWA` is the nonlinear EWA Picard operator whose fixed point is abstract until interpreted by `realSlice`.

---

## (2) Does `h_u` fail for `picardEWA`?  What is the real issue?

The atom is:

```lean
h_u : ∀ (τ : TimeDom T), ∀ x ∈ Set.Icc (0 : ℝ) 1,
  evalST τ x (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)
    = (intervalDomainLift (realSlice u_star τ.1) x : ℂ)
```

For an arbitrary `u_star : EWA T 1`, the **real-valued** physical slice is defined by the real part of `evalST`:

```lean
import ShenWork.Wiener.EWA.SourceStrongSolution
import ShenWork.Wiener.EWA.SourceFixedPointAbs
import ShenWork.Wiener.EWA.HeatFloor
import ShenWork.Wiener.EWA.ChemDivEval
import ShenWork.Wiener.EWA.FluxEvalBridge
import ShenWork.Wiener.EWA.GrowthEvalBridge

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff DuhamelSourceTimeC1)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledChemDivSourceLift coupledLogisticSourceCoeffs)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.PDE (intervalNeumannResolverCoeff)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- **The realized real-space slice of an `EWA T 1` element.** -/
def realSlice (u_star : EWA T 1) : ℝ → intervalDomainPoint → ℝ :=
  fun t x =>
    if h : t ∈ Set.Icc (0 : ℝ) T then
      (evalST (⟨t, h⟩ : TimeDom T) ((x.1 : ℝ) : WA.Circ)
        (GWA.incl (by omega : (0:ℕ) ≤ 1) u_star)).re
    else 0
```

This means `h_u` is **almost definitional**, but not entirely: it is a complex equality

```lean
evalST ... = (real number : ℂ)
```

and `realSlice` only stores the **real part**.  Therefore we also need the imaginary part of the evaluation to vanish.

The current repo proves exactly this:

```lean
import ShenWork.Wiener.EWA.SourceFluxNbhdDischarge
import ShenWork.Wiener.EWA.SourceFixedPointParity

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

/-- **The base realization for `realSlice`.**  For ANY `u_star : EWA T 1` the
Wiener point-evaluation of `incl u_star` realizes the lift of its own real slice
on `[0,1]`, PROVIDED `evalST` is real there (`(evalST …).im = 0`). -/
theorem realSlice_evalST_realizes (u_star : EWA T 1) (τ : TimeDom T) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hreal : (evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)).im = 0) :
    evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)
      = (intervalDomainLift (realSlice u_star τ.1) x : ℂ)

/-- Full-circle reality of `evalST (incl u_star)` from `EvenRealEWA u_star`. -/
theorem evalST_incl_im_zero_of_evenReal {u_star : EWA T 1}
    (hER : EvenRealEWA u_star) (τ : TimeDom T) (y : WA.Circ) :
    (evalST τ y (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)).im = 0
```

And for a Picard fixed point, the repo proves `EvenRealEWA u_star` from the contraction/fixed-point data:

```lean
/-- **THE DISCHARGE — `EvenRealEWA u_star`.** ... -/
theorem picardEWA_evenReal_fixedPoint (p : CM2Params) {μ ν γ ρ L_Q L_G : ℝ}
    (hμ : 0 < μ) (hT : (0 : ℝ) ≤ T) (u₀cos : ℕ → ℝ) (hmem : MemW 1 (ofCosineCoeffs u₀cos))
    (hρ : 0 ≤ ρ)
    (hself : MapsTo (picardEWA p μ ν γ hμ hT (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1))
      (Metric.closedBall (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ)
      (Metric.closedBall (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ))
    (hLipQ : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ‖chemFluxEWA μ ν p.β γ hμ a - chemFluxEWA μ ν p.β γ hμ b‖ ≤ L_Q * ‖a - b‖)
    (hLipG : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ‖growthEWA p.α p.a p.b a - growthEWA p.α p.a p.b b‖ ≤ L_G * ‖a - b‖)
    (hKnn : (0 : ℝ) ≤ |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T)
    (hK : |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T < 1)
    (u_star : EWA T 1)
    (hmem_star : u_star ∈ Metric.closedBall (heatEWA (T := T)
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ)
    (hfix : u_star = picardEWA p μ ν γ hμ hT (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1) u_star) :
    EvenRealEWA u_star
```

So the current answer to “why doesn’t `h_u` hold for `picardEWA`?” is:

```text
It DOES hold in the current repo, provided the fixed point's even-real parity is supplied/proved.
The old issue was that a bare abstract EWA fixed point does not automatically expose a physical lift
unless you define `realSlice` and prove the evaluation is real.  That is now done.
```

The slab theorem is:

```lean
/-- **`h_u` slab — DISCHARGED.** -/
theorem realSlice_h_u_slab {u_star : EWA T 1} (hER : EvenRealEWA u_star) :
    ∀ (τ : TimeDom T), ∀ x ∈ Set.Icc (0 : ℝ) 1,
      evalST τ x (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)
        = (intervalDomainLift (realSlice u_star τ.1) x : ℂ)
```

---

## (3) What would a `picardEWA → embedEWA` bridge look like?

A literal bridge would be something like:

```lean
theorem picardEWA_eq_embed_realSlice
    (p : CM2Params) ...
    (u_star : EWA T 1)
    (hfix : u_star = picardEWA p p.μ p.ν p.γ p.hμ hT u₀E u_star)
    (hER : EvenRealEWA u_star)
    -- continuity/envelope/summability needed to construct embedEWA (realSlice u_star)
    {Bv : ℕ → ℝ}
    (hBv : ∀ t k, |cosineCoeffs (intervalDomainLift (realSlice u_star t)) k| ≤ Bv k)
    (hBvnn : ∀ k, 0 ≤ Bv k)
    (hBvsum : Summable (fun k : ℕ => (1 + (k : ℝ)) * Bv k))
    (hcont : ∀ n : ℤ, Continuous (embedModeFun (realSlice u_star) n)) :
    u_star = embedEWA (realSlice u_star) hBv hBvnn hBvsum hcont
```

But this is stronger than what the three evalST atoms require.  It is an equality of EWA coefficient objects, not merely equality of their values on `[0,1]`.

The actual proof would likely proceed by extensionality on EWA coefficients.  A more useful intermediate theorem would be a coefficient-extractor statement:

```lean
∀ τ k,
  ewaCosCoeffAt (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star) τ k
    = cosineCoeffs (intervalDomainLift (realSlice u_star τ.1)) k
```

For even-real EWA elements, the repo already has exactly the kind of non-circular bridge needed to get such coefficient identities from an `evalST` identity:

```lean
ewaCosCoeffAt_eq_cosineCoeffs_of_even_real
slice_eq_ofCosineCoeffs_of_even_real
```

These are used repeatedly in `SourceRealizesRecords.lean` and `FluxRealizeEmbed.lean`.

However, a full equality

```lean
u_star = embedEWA (realSlice u_star) ...
```

also needs all the data needed to construct the RHS `embedEWA`, namely the uniform A¹ envelope and time-continuity of embedded coefficients.  Those are not automatic from an arbitrary `EWA T 1` fixed point unless one proves them separately.

So yes, conceptually the bridge would say:

```text
The Picard fixed point is the EWA embedding of its own physical realization.
```

But it is best viewed as a **coefficient uniqueness / characterization theorem**, and it is stronger than necessary.  The current tree avoids it by proving the evalST atoms directly for `realSlice u_star`.

---

## (4) Is there a simpler route by induction on Picard iterates?

Conceptually yes, but it is not the route the current tree uses, and it would likely be heavier.

The induction route would look like:

```text
1. Define Picard iterates U₀ = heatEWA u₀E, Uₙ₊₁ = picardEWA ... Uₙ.
2. Prove h_u / h_uα / h_flux_nbhd for every Uₙ.
3. Prove Uₙ → u_star in EWA norm via contraction.
4. Prove evalST is continuous enough to pass the atoms to the limit.
```

This is plausible because `evalST` is continuous on Wiener algebras and because the parity proof already uses a version of “iterate then pass to the closed limit.”  In fact, `picardEWA_evenReal_fixedPoint` proves even-real parity by showing each Banach iterate is even-real and then using closedness of `EvenRealEWA`.

But for the three evalST atoms, the current repo has an even simpler route:

1. Define the physical realization by `realSlice`.
2. Prove `evalST(incl u_star)` is real from `EvenRealEWA u_star`.
3. Then `h_u` follows by unfolding `realSlice`.
4. Prove `h_uα` from `realPowEWA_eval`, the uniform floor, and `h_u`.
5. Prove `h_flux_nbhd` using the abstract theorem `flux_nbhd_of_realized`, not the embed specialization.

The core direct producers are:

```lean
/-- **The base realization for `realSlice`.** -/
theorem realSlice_evalST_realizes (u_star : EWA T 1) (τ : TimeDom T) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hreal : (evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)).im = 0) :
    evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)
      = (intervalDomainLift (realSlice u_star τ.1) x : ℂ)

/-- **`h_uα` PRODUCED for the fixed point.** -/
theorem realSlice_realPow_realizes (p : CM2Params) (u_star : EWA T 1)
    {δ : ℝ} (hδpos : 0 < δ) (hER : EvenRealEWA u_star)
    (hfloor : UniformFloor u_star δ) (hα : 0 ≤ p.α)
    (τ : TimeDom T) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1) (realPowEWA u_star p.α))
      = ((intervalDomainLift (realSlice u_star τ.1) x ^ p.α : ℝ) : ℂ)

/-- **`h_flux_nbhd` PRODUCED for the fixed point.** -/
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
      = ((chemFluxLifted p (realSlice u_star τ.1) x : ℝ) : ℂ)
```

And the slab packaging is:

```lean
/-- **`h_u` slab — DISCHARGED.** -/
theorem realSlice_h_u_slab {u_star : EWA T 1} (hER : EvenRealEWA u_star) :
    ∀ (τ : TimeDom T), ∀ x ∈ Set.Icc (0 : ℝ) 1,
      evalST τ x (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)
        = (intervalDomainLift (realSlice u_star τ.1) x : ℂ)

/-- **`h_uα` slab — DISCHARGED.** -/
theorem realSlice_h_uα_slab (p : CM2Params) {u_star : EWA T 1} {δ : ℝ}
    (hδpos : 0 < δ) (hER : EvenRealEWA u_star) (hfloor : UniformFloor u_star δ)
    (hα : 0 ≤ p.α) :
    ∀ (τ : TimeDom T), ∀ x ∈ Set.Icc (0 : ℝ) 1,
      evalST τ x (GWA.incl (by omega : (0 : ℕ) ≤ 1) (realPowEWA u_star p.α))
        = ((intervalDomainLift (realSlice u_star τ.1) x ^ p.α : ℝ) : ℂ)

/-- **`h_flux_nbhd` slab — DISCHARGED.** -/
theorem realSlice_h_flux_slab (p : CM2Params) {u_star : EWA T 1} {δ : ℝ}
    (hδpos : 0 < δ) (hβpos : 0 < p.β) (hER : EvenRealEWA u_star)
    (hfloor : UniformFloor u_star δ)
    (hsum : ∀ σ : TimeDom T, ResolverSourceSummable p (realSlice u_star σ.1))
    (hgrad : ∀ (τ : TimeDom T),
      Summable fun k : ℕ =>
        |(intervalNeumannResolverCoeff p (realSlice u_star τ.1) k).re| * ((k : ℝ) * Real.pi))
    (hμle1 : p.μ ≤ 1)
    (f : ℝ → ℝ → ℝ) (hf_cont : ∀ σ : TimeDom T, Continuous (f σ.1))
    (hf_nonneg : ∀ (σ : TimeDom T) (y : ℝ), 0 ≤ f σ.1 y)
    (hf_coeff : ∀ (σ : TimeDom T) (k : ℕ),
      cosineCoeffs (f σ.1) k = (intervalNeumannResolverSourceCoeff p (realSlice u_star σ.1) k).re)
    (hâ : ∀ σ : TimeDom T, Summable (fun k => (cosineCoeffs (f σ.1) k) ^ 2)) :
    ∀ (τ : TimeDom T), ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (y : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (chemFluxEWA p.μ p.ν p.β p.γ p.hμ u_star))
        = ((chemFluxLifted p (realSlice u_star τ.1) y : ℝ) : ℂ)
```

Finally, the direct consumer that no longer carries these three hard atoms is:

```lean
/-- **The χ₀<0 `realizes` slab — three hard-core evalST atoms DISCHARGED.** -/
theorem realizes_evalST_discharged (p : CM2Params) (u₀cos : ℕ → ℝ)
    (hsumc : Summable (fun k => |u₀cos k|)) (hmem : MemW 1 (ofCosineCoeffs u₀cos))
    (hT : (0 : ℝ) ≤ T)
    {ρ L_Q L_G δ : ℝ} (hδpos : 0 < δ) (u_star : EWA T 1)
    (hfix : u_star = picardEWA p p.μ p.ν p.γ p.hμ hT
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1) u_star)
    ...
    (t : ℝ) (htlo : 0 < t) (hthi : t ≤ T) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x
```

The proof derives `EvenRealEWA u_star`, builds `h_u`, `h_uα`, and `h_flux` internally, then calls `realizes_clean`.

---

## Existing partial/full bridge work: theorem inventory

### Embed route

```lean
embedEWA
embedEWA_evenReal
embedEWA_realizes
flux_nbhd_of_embed
flux_nbhd_of_embed_discharged
```

Meaning: works when the EWA element is literally built by embedding a known function’s cosine coefficients.

### Abstract/no-embed route

```lean
flux_nbhd_of_realized
resolver_value_of_slice
slice_smul_realPow_eq_source
```

Meaning: `flux_nbhd_of_realized` already abstracts away from `embedEWA`; it only needs the base realization `h_u` and the source/resolver sub-atoms.  This is the key reason the no-embed route works.

### Picard fixed-point parity / reality

```lean
picardEWA_evenReal
isClosed_evenReal
picardEWA_evenReal_fixedPoint
evalST_incl_im_zero_of_evenReal
```

Meaning: the Picard fixed point is even-real, hence its `evalST` values are real casts.

### Direct Picard/realSlice atom producers

```lean
realSlice_evalST_realizes
realSlice_realPow_realizes
realSlice_flux_realizes
```

Meaning: pointwise `h_u`, `h_uα`, and `h_flux_nbhd` for abstract `u_star`, without an embed equality.

### Slab packagers and final discharge

```lean
realSlice_h_u_slab
realSlice_h_uα_slab
realSlice_h_flux_slab
realizes_evalST_discharged
```

Meaning: the exact slab-shaped hypotheses consumed by `realizes_clean` are now produced internally.

---

## Bottom line

Answers to the four questions:

1. **Yes, with a nuance:** `picardEWA` is the EWA Picard **operator**; a fixed point is `u_star = picardEWA ... u_star`.  `embedEWA` is a known-function embedding into EWA via time-dependent cosine coefficients.

2. **It actually does hold now.**  For arbitrary `u_star`, `h_u` needs eval-reality because `realSlice` stores only the real part.  For a Picard fixed point, `picardEWA_evenReal_fixedPoint` gives `EvenRealEWA`, `evalST_incl_im_zero_of_evenReal` gives reality, and `realSlice_evalST_realizes` gives `h_u`.

3. **A literal bridge would be** `u_star = embedEWA (realSlice u_star) ...`, but that is stronger than needed and would require coefficient extensionality plus the envelope/continuity data needed to construct the RHS.  A coefficient characterization theorem would be the more surgical version.

4. **Induction on Picard iterates is conceptually possible but not needed.**  The current tree has a simpler direct route through `realSlice`, even-real parity, `realPowEWA_eval`, and `flux_nbhd_of_realized`.  There is no need to prove `picardEWA = embedEWA (realSlice picardEWA)` just to discharge the three evalST atoms.
