import Mathlib
import ShenWork.Wiener.EWA.OpCoeffBridge
import ShenWork.Wiener.EWA.CoeffBridge
import ShenWork.Wiener.WeightedL1CosineEval
import ShenWork.PDE.IntervalNeumannEllipticResolverR
import ShenWork.PDE.HeatKernelLpEstimates

/-!
# EWA brick — the resolver EVAL bridge (Phase C source eval-bridge, source-form target)

This file proves the **EVAL bridge for the elliptic resolver**: the Wiener synthesis
(`WA.evalC`) of the EWA resolver `gResolver` applied to a realized source element
equals the committed real-space Neumann resolver `intervalNeumannResolverR`,
evaluated pointwise on `[0,1]`.

## Setup

The source element is the even cosine embedding `cosG 0 c hc` of the *real-part*
source-coefficient family `c k = (intervalNeumannResolverSourceCoeff p u k).re`
(the realization hypothesis `hs : s.toFun = ofCosineCoeffs c` is exactly what the
upstream B5 `EWARealizesOn` discharge provides at the coefficient level).  Applying
the operator `gResolver μ hμ : GWA ℂ 0 →L[ℂ] GWA ℂ 2`, the committed coefficient
bridge `gResolver_ofCosineCoeffs` gives the output coefficients
`ofCosineCoeffs (fun k => c k / (μ + (kπ)²))`.

## The two committed matchings (the crux)

1. **Source/multiplier match (elliptic identity).**  By the committed
   `intervalNeumannResolverCoeff_elliptic` — `(μ + λ_k) · v̂_k = â_k` — and the
   reality of the source coefficient `â_k`, the gResolver output coefficient
   `c k / (μ + (kπ)²)` equals `(intervalNeumannResolverCoeff p u k).re`.  We use
   `unitIntervalNeumannSpectrum.eigenvalue k = (k:ℝ)²·π² = ((k:ℝ)·π)²` (rfl/`ring`),
   matching the `gResolver` multiplier denominator `μ + (kπ)²`.

2. **Basis match (`cosineMode = unitIntervalCosineMode`).**  The committed
   `evalC_ofCosineCoeffs_all` synthesizes the cosine series with `cosineMode k x`,
   while `intervalNeumannResolverR` uses `unitIntervalCosineMode k x.1`.  These are
   definitionally the same (`Real.cos (kπx)`), bridged by the committed
   `unitIntervalCosineMode_eq_cosineMode`.

No realization of `s` against `ν·u^γ` is proved here (that is upstream); this is a
pure coefficient/synthesis bridge.
-/

open scoped BigOperators

noncomputable section

namespace ShenWork.EWA

open ShenWork.Wiener ShenWork.GWA ShenWork.GWA.GWA
open ShenWork.PDE ShenWork.CosineSpectrum ShenWork.IntervalDomain ShenWork.Paper3

/-- The real-part source-coefficient family of the elliptic resolver, as a real
cosine-coefficient sequence `c k = (â_k).re`. -/
def resolverSourceReCoeff (p : CM2Params) (u : intervalDomainPoint → ℝ) (k : ℕ) : ℝ :=
  (intervalNeumannResolverSourceCoeff p u k).re

/-- The gResolver output coefficient `c k / (μ + (kπ)²)` equals the real part of the
committed resolver coefficient `intervalNeumannResolverCoeff p u k`.

This is the **source/multiplier match**: it routes the gResolver Fourier multiplier
`1/(μ+(kπ)²)` through the committed coefficient-form elliptic identity
`intervalNeumannResolverCoeff_elliptic`, using that the source coefficient is real. -/
theorem resolverOutputCoeff_eq_resolverCoeff_re
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (k : ℕ) :
    resolverSourceReCoeff p u k / (p.μ + ((k : ℝ) * Real.pi) ^ 2)
      = (intervalNeumannResolverCoeff p u k).re := by
  -- `λ_k = (k:ℝ)² π² = ((k:ℝ)π)²`.
  have hlam : unitIntervalNeumannSpectrum.eigenvalue k = ((k : ℝ) * Real.pi) ^ 2 := by
    show (k : ℝ) ^ 2 * Real.pi ^ 2 = ((k : ℝ) * Real.pi) ^ 2
    ring
  -- Real-part of the committed elliptic identity `(μ + λ_k) · v̂_k = â_k`.
  have hell := intervalNeumannResolverCoeff_elliptic p u k
  have hcast :
      ((p.μ : ℂ) + (unitIntervalNeumannSpectrum.eigenvalue k : ℂ)) =
        (((p.μ + unitIntervalNeumannSpectrum.eigenvalue k : ℝ)) : ℂ) := by
    push_cast; ring
  have hRe :
      (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) *
          (intervalNeumannResolverCoeff p u k).re
        = resolverSourceReCoeff p u k := by
    have hk := congrArg Complex.re hell
    rw [hcast, Complex.re_ofReal_mul] at hk
    exact hk
  -- Denominator positive, hence solve for `(v̂_k).re`.
  have hden_pos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue k :=
    intervalNeumannResolver_denom_pos p k
  have hden_ne : (p.μ + ((k : ℝ) * Real.pi) ^ 2) ≠ 0 := by
    rw [← hlam]; exact ne_of_gt hden_pos
  rw [eq_comm, eq_div_iff hden_ne, mul_comm]
  rw [hlam] at hRe
  exact hRe

/-- The real source-coefficient family is absolutely summable.

(The summability hypothesis is needed to build the `WA 0` element and to invoke
`evalC_ofCosineCoeffs_all`; it is supplied upstream alongside the realization.) -/
def ResolverSourceSummable (p : CM2Params) (u : intervalDomainPoint → ℝ) : Prop :=
  Summable (fun k => |resolverSourceReCoeff p u k|)

/-- **The resolver eval bridge.**  For a source element `s : GWA ℂ 0` whose
coefficients realize the resolver source (real-part) coefficients, the Wiener
synthesis of `gResolver μ hμ s` equals (cast to `ℂ`) the committed real-space
Neumann resolver `intervalNeumannResolverR p u ⟨x, hx⟩`.

* `hs` is the coefficient-form realization hypothesis (B5's `EWARealizesOn`
  discharge).
* `hsum` is the absolute summability of the source coefficient family.

The proof: rewrite the gResolver output coefficients via the committed
`gResolver_ofCosineCoeffs`, identify them with `(intervalNeumannResolverCoeff …).re`
via `resolverOutputCoeff_eq_resolverCoeff_re`, synthesize the cosine series with the
committed `evalC_ofCosineCoeffs_all`, and match `cosineMode ↔ unitIntervalCosineMode`
via `unitIntervalCosineMode_eq_cosineMode`. -/
theorem evalC_gResolver_eq_intervalNeumannResolverR
    (p : CM2Params) (u : intervalDomainPoint → ℝ)
    (hsum : ResolverSourceSummable p u)
    (s : GWA ℂ 0)
    (hs : s.toFun = ofCosineCoeffs (resolverSourceReCoeff p u))
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    WA.evalC
        (⟨(gResolver (K := ℂ) p.μ p.hμ s).toFun,
          WA.mem0
            (⟨(gResolver (K := ℂ) p.μ p.hμ s).toFun,
              (gResolver (K := ℂ) p.μ p.hμ s).mem⟩ : WA 2)⟩ : WA 0)
        (x : WA.Circ)
      = ((intervalNeumannResolverR p u ⟨x, hx⟩ : ℝ) : ℂ) := by
  -- Abbreviations.
  set c : ℕ → ℝ := resolverSourceReCoeff p u with hc_def
  have hcsum : Summable (fun k => |c k|) := hsum
  -- The source `s` is the cosine embedding of `c`.
  have hcG : Summable (fun k : ℕ => (1 + (k : ℝ)) ^ (0 : ℕ) * |c k|) := by
    simpa using hcsum
  -- `gResolver` output coefficients via the committed coefficient bridge.
  -- First, rewrite `s` as `cosG 0 c hcG` (same `toFun`, same element by `ext`).
  have hs_eq : s = cosG 0 c hcG := by
    apply GWA.ext
    rw [hs, cosG_toFun]
  have hgr := gResolver_ofCosineCoeffs (r := 0) (c := c) p.μ p.hμ hcG
  -- The gResolver output `toFun = ofCosineCoeffs (k ↦ c k/(μ+(kπ)²))`.
  have hout : (gResolver (K := ℂ) p.μ p.hμ s).toFun
      = ofCosineCoeffs (fun k => c k / (p.μ + ((k : ℝ) * Real.pi) ^ 2)) := by
    rw [hs_eq]; exact hgr
  -- That coefficient family equals `k ↦ (intervalNeumannResolverCoeff p u k).re`.
  have hcoeff_eq : (fun k => c k / (p.μ + ((k : ℝ) * Real.pi) ^ 2))
      = (fun k => (intervalNeumannResolverCoeff p u k).re) := by
    funext k
    exact resolverOutputCoeff_eq_resolverCoeff_re p u k
  -- Summability of the resolved-coefficient family `(v̂_k).re`.
  have hressum : Summable (fun k => |(intervalNeumannResolverCoeff p u k).re|) := by
    have hbound : ∀ k, |(intervalNeumannResolverCoeff p u k).re|
        ≤ |c k| / p.μ := by
      intro k
      have heq := resolverOutputCoeff_eq_resolverCoeff_re p u k
      have hden_pos : 0 < p.μ + ((k : ℝ) * Real.pi) ^ 2 := by
        have : (0 : ℝ) ≤ ((k : ℝ) * Real.pi) ^ 2 := sq_nonneg _
        linarith [p.hμ]
      rw [← heq, abs_div, abs_of_pos hden_pos]
      apply div_le_div_of_nonneg_left (abs_nonneg _) p.hμ
      have : (0 : ℝ) ≤ ((k : ℝ) * Real.pi) ^ 2 := sq_nonneg _
      linarith
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) hbound ?_
    exact hcsum.div_const p.μ
  -- Rewrite the synthesized `WA 0` so its coefficients are `ofCosineCoeffs (v̂.re)`.
  set d : ℕ → ℝ := fun k => (intervalNeumannResolverCoeff p u k).re with hd_def
  have hdsum : Summable (fun k => |d k|) := hressum
  have houtd : (gResolver (K := ℂ) p.μ p.hμ s).toFun = ofCosineCoeffs d := by
    rw [hout, hcoeff_eq]
  -- The synthesized WA 0 element equals `⟨ofCosineCoeffs d, _⟩`, so apply the
  -- committed full-circle synthesis identity.
  have hWAeq :
      (⟨(gResolver (K := ℂ) p.μ p.hμ s).toFun,
          WA.mem0
            (⟨(gResolver (K := ℂ) p.μ p.hμ s).toFun,
              (gResolver (K := ℂ) p.μ p.hμ s).mem⟩ : WA 2)⟩ : WA 0)
        = (⟨ofCosineCoeffs d,
            memW_ofCosineCoeffs (r := 0) (by simpa using hdsum)⟩ : WA 0) := by
    apply WA.ext
    exact houtd
  rw [hWAeq, evalC_ofCosineCoeffs_all d hdsum x]
  -- Now match the two cosine series: `cosineMode = unitIntervalCosineMode`.
  -- Reduce to the real-valued equality of the two cosine series.
  have hreal : (∑' k : ℕ, d k * cosineMode k x)
      = intervalNeumannResolverR p u ⟨x, hx⟩ := by
    rw [intervalNeumannResolverR]
    refine tsum_congr (fun k => ?_)
    rw [unitIntervalCosineMode_eq_cosineMode]
  rw [hreal]

end ShenWork.EWA
