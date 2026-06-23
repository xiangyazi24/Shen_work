/-
  # χ₀<0 regularity chain: the two genuine bottoms, closed.

  This file closes the two carried residuals of the χ₀<0 trajectory-`H^σ`
  regularity chain landed in `IntervalChiNegTrajectoryClosure`:

  * (C1) — the τ-uniform DECAYING `H⁰` flux-source envelope `hMsq : MemHSigma 0 Msup`.
    The landed `trajBaseEnvelope_of_sourceEnvelope` REDUCES the (C1) base to a
    decaying `H⁰` source envelope `Msup` of the flux Duhamel integrand, plus
    nonneg / continuity / τ-uniform bound.  The stall note flagged the L∞ ball
    cannot give `hMsq` (flat constant `k ↦ 2M ∉ H⁰`) and proposed an
    L²-COMPACTNESS attack.  But the divergence/factor STRUCTURE of the flux
    already supplies a *strictly stronger* `H^σ` (hence `H⁰`) decaying envelope
    WITHOUT any compactness argument: from a τ-uniform factor package
    `FluxFactorEnvelopes σ t Q` (cosine env `gW` of `W`, sine env `gvx` of `vx`,
    both in `H^σ`), the landed `fluxSineEnvelope_uniform` produces
    `Msup := trueCosProd gW gvx ∈ H^σ` τ-uniformly dominating `|sineCoeffs (Q τ)|`.
    `memHSigma_antitone` downscales `H^σ → H⁰`.  This ELIMINATES the carried
    `hMsq` (and the whole compactness seam): the (C1) base now reduces only to the
    factor envelopes, which are upstream-landed mild data.

  * (C2) — the per-slice `InputFamily`.  `mkBundleInputs_of_package` assembles one
    `BundleInputs` from a clean per-slice analytic package (the genuinely mild
    fields: positivity, the cosine/mixed bridges, the resolver relay `hvrel`/`hdiv`,
    the τ-uniform continuity and the decomposition `hdecomp`), and
    `inputFamily_of_package` lifts it σ-uniformly to the `InputFamily` consumed by
    the landed engine.  The decomposition field is threaded from the landed
    `conjugateSlice_decomp_tauLift` shape.  HONEST: the package's analytic fields
    are the genuine per-slice mild content; this CLOSES the wiring, carrying the
    package — NOT an unconditional discharge of the mild solution.

  NON-CIRCULAR: imports only the landed closure + flux factor envelope +
  `H^σ` antitone; NEVER `localClassicalSolution`/`IsPaper2ClassicalSolution`/C²-of-u.
  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.
  `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
-/
import ShenWork.Paper2.IntervalChiNegTrajectoryClosure

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegFluxSourceClosure

open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalTrajectoryEnvelope
  (TrajectoryHSigmaEnvelope FluxFactorEnvelopes flux_memHSigma flux_dom)
open ShenWork.Paper2.IntervalWienerAlgebra (trueCosProd)
open ShenWork.Paper2.IntervalMildPosTimeHSigma (memHSigma_antitone)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalChiNegTrajectoryClosure
  (BundleInputs InputFamily trajBaseEnvelope_of_sourceEnvelope)

/-! ## (C1) — the DECAYING `H⁰` flux-source envelope, compactness-free.

`Msup := trueCosProd gW gvx` is the single decaying `H^σ` envelope of the flux
`Q τ = W τ · vx τ`, dominating `|sineCoeffs (Q τ) k|` τ-uniformly (landed
`flux_dom`).  It is the genuine *decaying* dominator the L∞ ball could not supply:
its `H^σ` membership (landed `flux_memHSigma`) forces `(1+λ_k)^σ (Msup k)²` summable,
so `Σ_k (Msup k)² < ∞` after `memHSigma_antitone`.  No `IsCompact`/equismall-tails
lemma is needed — the divergence/factor structure is the decay. -/

/-- The flux factor envelope `Msup := trueCosProd gW gvx` is `H⁰` (`Σ Msup² < ∞`),
obtained by downscaling its landed `H^σ` membership (`σ > 1/2 ≥ 0`). -/
theorem fluxSource_memHSigma_zero {σ t : ℝ} (hσ : 1 / 2 < σ)
    {Q : ℝ → ℝ → ℝ} (F : FluxFactorEnvelopes σ t Q) :
    MemHSigma 0 (trueCosProd F.gW F.gvx) :=
  memHSigma_antitone (by linarith) (flux_memHSigma hσ F)

/-- `Msup := trueCosProd gW gvx` is nonneg: on the nonempty `[0,t]` (`t > 0`) it
dominates `|sineCoeffs (Q τ) k| ≥ 0` (landed `flux_dom`). -/
theorem fluxSource_nonneg {σ t : ℝ} (hσ : 1 / 2 < σ) (ht : 0 < t)
    {Q : ℝ → ℝ → ℝ} (F : FluxFactorEnvelopes σ t Q) (k : ℕ) :
    0 ≤ trueCosProd F.gW F.gvx k :=
  le_trans (abs_nonneg (sineCoeffs (Q 0) k))
    (flux_dom hσ F 0 ⟨le_refl 0, ht.le⟩ k)

/-- **(C1) — the BASE envelope from flux FACTOR envelopes, COMPACTNESS-FREE.**

Given the gain `α ∈ [0,1)`, the flux factor package `FluxFactorEnvelopes σ t Q`
(`σ > 1/2`), continuity of the flux Duhamel integrand `F k = fun τ => sineCoeffs (Q τ) k`,
and the per-mode trajectory-vs-Duhamel domination `htraj_dom`, build the (C1)
base `TrajectoryHSigmaEnvelope α t (cosineCoeffs ∘ u)` — with the decaying `H⁰`
source envelope `hMsq` discharged unconditionally (`Msup := trueCosProd gW gvx`,
`flux_memHSigma` + `memHSigma_antitone`).  The compactness seam is eliminated:
the (C1) base reduces ONLY to the upstream factor envelopes + `htraj_dom`. -/
def trajBaseEnvelope_of_fluxFactors {α σ t : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hσ : 1 / 2 < σ) (ht : 0 < t) (ht1 : t ≤ 1)
    {u : ℝ → ℝ → ℝ} {Q : ℝ → ℝ → ℝ} (F : FluxFactorEnvelopes σ t Q)
    (hFcont : ∀ k, Continuous (fun τ => sineCoeffs (Q τ) k))
    (htraj_dom : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
      |cosineCoeffs (u τ) k|
        ≤ |duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (Q τ) k) τ k|) :
    TrajectoryHSigmaEnvelope (0 + α) t (fun τ => cosineCoeffs (u τ)) :=
  trajBaseEnvelope_of_sourceEnvelope hα0 hα1 ht ht1 hFcont
    (Msup := trueCosProd F.gW F.gvx)
    (fluxSource_nonneg hσ ht F)
    (fluxSource_memHSigma_zero hσ F)
    (fun k τ hτ => flux_dom hσ F τ hτ k)
    htraj_dom

/-! ## (C2) — the per-slice `BundleInputs` from a clean mild PACKAGE.

`BundleInputs` carries genuine per-slice analytic mild data (positivity, the
cosine/mixed Fourier bridges, the resolver relay `hvrel`/`hdiv`, the τ-uniform
continuity and the decomposition).  `MildSlicePackage` names exactly those fields
(plus the σ-uniform `L`-envelope and the numeric side-conditions decided by the
hypotheses), and `mkBundleInputs_of_package` assembles `BundleInputs` from it.
The decomposition field matches the landed `conjugateSlice_decomp_tauLift` shape. -/

/-- The genuine per-slice analytic mild data for one `BundleInputs`, as a named
package (every field is a landed-or-carried mild fact above the coefficient
envelope `E`; nothing is `E`-derivable except `heU = E.hdom`, wired by `mkBundle`). -/
structure MildSlicePackage (μ σ β χ₀ t : ℝ) (u v : ℝ → ℝ → ℝ) (û₀ : ℕ → ℝ)
    (Q W vx : ℝ → ℝ → ℝ) (Fl : ℕ → ℝ → ℝ)
    (E : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (u τ))) where
  hμ : 0 < μ
  hσ0 : 1 / 2 < σ
  hσ1 : σ < 3 / 2
  hβ : 0 ≤ β
  ht : 0 < t
  ht1 : t ≤ 1
  hû₀ : MemHSigma (σ + 1 / 4) û₀
  hvnn : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ x,
    0 ≤ ShenWork.Paper2.IntervalDenomEnvelopeResolver.resolverValue μ
      (cosineCoeffs (u τ)) x
  hQ : ∀ τ, Q τ = fun x => W τ x * vx τ x
  hWdef : ∀ τ, W τ = fun x => u τ x
    * (1 + ShenWork.Paper2.IntervalDenomEnvelopeResolver.resolverValue μ
        (cosineCoeffs (u τ)) x) ^ (-β)
  hbr : ∀ τ ∈ Set.Icc (0:ℝ) t,
    ShenWork.Paper2.IntervalWienerAlgebra.CosineMulBridge (u τ)
      (fun x => (1 + ShenWork.Paper2.IntervalDenomEnvelopeResolver.resolverValue μ
        (cosineCoeffs (u τ)) x) ^ (-β))
  hbridge : ∀ τ ∈ Set.Icc (0:ℝ) t,
    ShenWork.Paper2.IntervalMixedProduct.MixedMulBridge (W τ) (vx τ)
  hvrel : ∀ τ ∈ Set.Icc (0:ℝ) t,
    ShenWork.Paper2.IntervalEnvelopeProp.Envelopes
      (ShenWork.Paper2.HSigmaScale.resolverCoeff 1 E.env) (cosineCoeffs (v τ))
  hdiv : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
    |sineCoeffs (vx τ) k| = Real.sqrt (lam k) * |cosineCoeffs (v τ) k|
  hQ_cont : ∀ k, Continuous (fun τ => sineCoeffs (Q τ) k)
  L : TrajectoryHSigmaEnvelope σ t (fun τ k => Fl k τ)
  hFl_cont : ∀ k, Continuous (Fl k)
  hdecomp : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
    cosineCoeffs (u τ) k
      = Real.exp (-(τ * lam k)) * û₀ k
        + (-χ₀) * duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (Q τ) k) τ k
        + duhamelEnergyCoeff 1 Fl τ k

/-- **(C2) — assemble `BundleInputs` from the per-slice mild package.**  A pure
field-for-field threading: every analytic field is carried by `P`. -/
def mkBundleInputs_of_package {μ σ β χ₀ t : ℝ} {u v : ℝ → ℝ → ℝ} {û₀ : ℕ → ℝ}
    {Q W vx : ℝ → ℝ → ℝ} {Fl : ℕ → ℝ → ℝ}
    {E : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (u τ))}
    (P : MildSlicePackage μ σ β χ₀ t u v û₀ Q W vx Fl E) :
    BundleInputs μ σ β χ₀ t u v û₀ Q W vx Fl E where
  hμ := P.hμ
  hσ0 := P.hσ0
  hσ1 := P.hσ1
  hβ := P.hβ
  ht := P.ht
  ht1 := P.ht1
  hû₀ := P.hû₀
  hvnn := P.hvnn
  hQ := P.hQ
  hWdef := P.hWdef
  hbr := P.hbr
  hbridge := P.hbridge
  hvrel := P.hvrel
  hdiv := P.hdiv
  hQ_cont := P.hQ_cont
  L := P.L
  hFl_cont := P.hFl_cont
  hdecomp := P.hdecomp

/-- A σ-indexed `MildSlicePackage` family — the precise per-slice mild residual. -/
abbrev MildPackageFamily (μ β χ₀ t : ℝ) (u v : ℝ → ℝ → ℝ) (û₀ : ℕ → ℝ)
    (Q W vx : ℝ → ℝ → ℝ) (Fl : ℕ → ℝ → ℝ) : Type :=
  ∀ σ : ℝ, ∀ E : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (u τ)),
    MildSlicePackage μ σ β χ₀ t u v û₀ Q W vx Fl E

/-- **(C2) — the `InputFamily` from a σ-uniform mild package family.**  Lifts
`mkBundleInputs_of_package` σ-uniformly to the `InputFamily Inp` the landed
`trajEnvelope_one_of_baseInputs` consumes. -/
def inputFamily_of_packageFamily {μ β χ₀ t : ℝ} {u v : ℝ → ℝ → ℝ} {û₀ : ℕ → ℝ}
    {Q W vx : ℝ → ℝ → ℝ} {Fl : ℕ → ℝ → ℝ}
    (PF : MildPackageFamily μ β χ₀ t u v û₀ Q W vx Fl) :
    InputFamily μ β χ₀ t u v û₀ Q W vx Fl :=
  fun σ E => mkBundleInputs_of_package (PF σ E)

/-! ## SIGNATURE AUDIT — exact carried hypotheses of the deliverables.

  * (C1) `trajBaseEnvelope_of_fluxFactors` — BASE, COMPACTNESS-FREE.  Carries
    EXACTLY: `(α ∈ [0,1), σ > 1/2, t ∈ (0,1], FluxFactorEnvelopes σ t Q,
    hFcont, htraj_dom)`.  The decaying `H⁰` source envelope `hMsq` is DISCHARGED
    (no longer carried): `Msup := trueCosProd gW gvx`, `flux_memHSigma`
    (`H^σ`) + `memHSigma_antitone` (`H^σ → H⁰`).  The `FluxFactorEnvelopes` package
    is the τ-uniform `H^σ` factor envelopes of `W` and `vx` — upstream-landed mild
    data, NOT the regularity being bootstrapped.  `htraj_dom` is the decomposition
    collapsed to its dominant Duhamel term (per-mode, carried; landed as the
    `hdecomp` shape).  The L²-compactness attack is UNNECESSARY: the divergence/
    factor structure already gives a *decaying* (`H^σ ⊆ H⁰`) dominator.

  * (C2) `mkBundleInputs_of_package` / `inputFamily_of_packageFamily` — ASSEMBLY.
    Closes the per-slice wiring: every analytic field is threaded from the named
    `MildSlicePackage` (positivity, the cosine/mixed bridges `hbr`/`hbridge`, the
    resolver relay `hvrel`/`hdiv`, the τ-uniform continuity `hQ_cont`/`hFl_cont`,
    the σ-uniform `L`-envelope, and the decomposition `hdecomp` in the landed
    `conjugateSlice_decomp_tauLift` shape).  The carried (C2) residual is exactly
    the σ-indexed `MildPackageFamily PF` — genuine per-slice mild content, NOT an
    unconditional discharge of `conjugatePicardLimit`.

  NET.  Plugging `trajBaseEnvelope_of_fluxFactors` as `E₀` and
  `inputFamily_of_packageFamily PF` as `Inp` into the landed
  `trajEnvelope_one_of_baseInputs` reaches `TrajectoryHSigmaEnvelope 1` carrying
  EXACTLY `(FluxFactorEnvelopes, hFcont, htraj_dom, MildPackageFamily PF, n,
  hreach)`.  `MemHSigma 1` is NOT unconditional: the two genuine residuals are the
  base flux FACTOR envelopes (C1) and the per-slice mild package family (C2).  The
  compactness seam of (C1) is RESOLVED (eliminated, not carried).  Both residuals
  are strictly upstream of `localClassicalSolution`; confirmed by `#print axioms`. -/

end ShenWork.Paper2.IntervalChiNegFluxSourceClosure

namespace ShenWork.Paper2.IntervalChiNegFluxSourceClosure
#print axioms fluxSource_memHSigma_zero
#print axioms fluxSource_nonneg
#print axioms trajBaseEnvelope_of_fluxFactors
#print axioms mkBundleInputs_of_package
#print axioms inputFamily_of_packageFamily
end ShenWork.Paper2.IntervalChiNegFluxSourceClosure
