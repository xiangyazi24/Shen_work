/-
  ShenWork/Paper2/IntervalTrajectoryEnvelope.lean

  THE τ-UNIFORM TRAJECTORY-H^σ ENVELOPE ATOM (genv / glenv) for the χ₀<0 mild
  trajectory — the single residual gating `SliceMildStepData` (KEYSTONE B).

  ## Two-layer structure (as in the route)

  * LAYER 2 — WIRING (this file delivers it COMPLETE, unconditional):
    given an ABSTRACT τ-uniform trajectory-`H^σ` envelope `Uσ` of the trajectory
    (the CORE datum), the flux / logistic `H^σ` envelopes (`genv`, `glenv`) and
    their τ-uniform domination are PRODUCED by the repo's envelope algebra:
      - the chemotaxis flux `Q τ = W τ · vx τ` is a sine object; with τ-uniform
        cosine factor envelope `gW` and sine factor envelope `gvx`, both in `H^σ`,
        `genv := trueCosProd gW gvx` lies in `H^σ` and dominates
        `|sineCoeffs (Q τ) k|` over `τ ∈ [0,t]` — this is
        `IntervalMixedProduct.fluxSineEnvelope_uniform` packaged into the field;
      - the logistic source `Fl` is bounded-range; a τ-uniform `H^σ` dominator
        `glenv` discharges `hgl` / `hgl_dom` directly.

  * LAYER 1 — CORE (the hard continuation, see the STALL REPORT at the end):
    producing the abstract τ-uniform trajectory-`H^σ` envelope `Uσ` itself.

  ## NON-CIRCULARITY

  This file imports ONLY the mild engine inputs (`IntervalBootstrapStep`,
  `IntervalMixedProduct`, `IntervalEnvelopeProp`, `IntervalHSigmaScale`).  It
  NEVER references `localClassicalSolution`, `IsPaper2ClassicalSolution`, the
  C²-Neumann producers, or the PID-classical bridge.  `#print axioms` ⊆
  `{propext, Classical.choice, Quot.sound}`.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.
-/
import ShenWork.Paper2.IntervalMildBootstrapStep
import ShenWork.Paper2.IntervalMixedProduct
import ShenWork.Paper2.IntervalEnvelopeProp

noncomputable section

namespace ShenWork.Paper2.IntervalTrajectoryEnvelope

open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma one_add_lam_pos)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalEnvelopeProp (Envelopes)
open ShenWork.Paper2.IntervalMixedProduct (MixedMulBridge fluxSineEnvelope_uniform)
open ShenWork.Paper2.IntervalWienerAlgebra (trueCosProd)

/-! ## The abstract τ-uniform trajectory-`H^σ` envelope (the CORE datum). -/

/-- **`TrajectoryHSigmaEnvelope σ t f`** — a single sequence `env ∈ H^σ` that
dominates the coordinatewise size `|f τ k|` UNIFORMLY over `τ ∈ [0,t]`.

This is the bootstrap's own monotone-induction datum for the trajectory window,
NOT a classical-existence object: it is exactly the τ-uniform coordinatewise
`H^σ` bound the endpoint-uniform propagator consumes. -/
structure TrajectoryHSigmaEnvelope (σ t : ℝ) (f : ℝ → ℕ → ℝ) where
  env : ℕ → ℝ
  henv : MemHSigma σ env
  hdom : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, |f τ k| ≤ env k

namespace TrajectoryHSigmaEnvelope

/-- The carried envelope is nonneg (a coordinatewise upper bound on `|·|`). -/
theorem env_nonneg {σ t : ℝ} {f : ℝ → ℕ → ℝ} (E : TrajectoryHSigmaEnvelope σ t f)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) t) (k : ℕ) : 0 ≤ E.env k :=
  le_trans (abs_nonneg _) (E.hdom τ hτ k)

end TrajectoryHSigmaEnvelope

/-! ## LAYER-2 WIRING — the flux SINE envelope (`genv`) from factor envelopes.

The chemotaxis flux `Q τ = W τ · vx τ` is wired directly through
`fluxSineEnvelope_uniform`: a τ-uniform cosine factor envelope `gW` of `W` and a
τ-uniform sine factor envelope `gvx` of `vx`, both in `H^σ`, produce a SINGLE
`H^σ` sequence `genv := trueCosProd gW gvx` dominating `|sineCoeffs (Q τ) k|`
over the whole window. -/

/-- **`FluxFactorEnvelopes σ t Q`** — the τ-uniform factor-envelope package the
flux wiring consumes: the sine factorisation `Q τ = W τ · vx τ`, the per-τ mixed
bridge, and τ-uniform cosine / sine factor envelopes `gW`, `gvx ∈ H^σ`.

`gW` is the cosine envelope of the chemotaxis weight `W = u·(1+v)^{−β}` (built
from the trajectory envelope `Uσ` via the cosine Wiener chain
`fluxCosEnvelope_of_factorEnvelopes`); `gvx` is the sine envelope of `v_x`
(`= √λ·cosineCoeffs v`, from `v ∈ H^{σ+1}` via the elliptic resolver).  Both are
τ-free, hence τ-uniform. -/
structure FluxFactorEnvelopes (σ t : ℝ) (Q : ℝ → ℝ → ℝ) where
  W : ℝ → ℝ → ℝ
  vx : ℝ → ℝ → ℝ
  gW : ℕ → ℝ
  gvx : ℕ → ℝ
  hQ : ∀ τ, Q τ = fun x => W τ x * vx τ x
  hgW : MemHSigma σ gW
  hgvx : MemHSigma σ gvx
  hbridge : ∀ τ ∈ Set.Icc (0:ℝ) t, MixedMulBridge (W τ) (vx τ)
  heW : ∀ τ ∈ Set.Icc (0:ℝ) t, Envelopes gW (cosineCoeffs (W τ))
  hevx : ∀ τ ∈ Set.Icc (0:ℝ) t, Envelopes gvx (sineCoeffs (vx τ))

/-- **WIRING — the τ-uniform flux `H^σ` envelope (`genv`, `hg`, `hg_dom`).**
From the factor-envelope package, `trueCosProd gW gvx` is a single `H^σ` sequence
that dominates `|sineCoeffs (Q τ) k|` uniformly over `τ ∈ [0,t]`.  This is
EXACTLY the `(genv σ, hg, hg_dom σ)` triple of `SliceMildStepData`.

Direct package of `fluxSineEnvelope_uniform`; no Gronwall, no new estimate. -/
theorem fluxEnvelope_of_factorEnvelopes {σ t : ℝ} (hσ : 1 / 2 < σ)
    {Q : ℝ → ℝ → ℝ} (F : FluxFactorEnvelopes σ t Q) :
    MemHSigma σ (trueCosProd F.gW F.gvx) ∧
      ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
        |sineCoeffs (Q τ) k| ≤ trueCosProd F.gW F.gvx k :=
  fluxSineEnvelope_uniform hσ F.hQ F.hgW F.hgvx F.hbridge F.heW F.hevx

/-- The `H^σ` membership half of the flux wiring (the `hg` field). -/
theorem flux_memHSigma {σ t : ℝ} (hσ : 1 / 2 < σ) {Q : ℝ → ℝ → ℝ}
    (F : FluxFactorEnvelopes σ t Q) :
    MemHSigma σ (trueCosProd F.gW F.gvx) :=
  (fluxEnvelope_of_factorEnvelopes hσ F).1

/-- The τ-uniform domination half of the flux wiring (the `hg_dom` field). -/
theorem flux_dom {σ t : ℝ} (hσ : 1 / 2 < σ) {Q : ℝ → ℝ → ℝ}
    (F : FluxFactorEnvelopes σ t Q) :
    ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
      |sineCoeffs (Q τ) k| ≤ trueCosProd F.gW F.gvx k :=
  (fluxEnvelope_of_factorEnvelopes hσ F).2

/-! ## LAYER-2 WIRING — the logistic source envelope (`glenv`).

The logistic source `Fl` has a bounded-range (Nemytskii / Wiener) `H^σ`
envelope.  Abstractly this is exactly a `TrajectoryHSigmaEnvelope σ t Fl`; its
two fields ARE `(glenv σ, hgl)` and `hgl_dom`. -/

/-- **WIRING — the logistic `H^σ` envelope (`glenv`, `hgl`, `hgl_dom`).**  A
`TrajectoryHSigmaEnvelope σ t Fl` IS the `(glenv σ, hgl)`/`hgl_dom` data: its
`env` lies in `H^σ` and dominates `|Fl τ k|` uniformly over `[0,t]`. -/
theorem logisticEnvelope_of_traj {σ t : ℝ} {Fl : ℝ → ℕ → ℝ}
    (L : TrajectoryHSigmaEnvelope σ t Fl) :
    MemHSigma σ L.env ∧ ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, |Fl τ k| ≤ L.env k :=
  ⟨L.henv, L.hdom⟩

/-! ## LAYER-1 CORE — the trajectory-envelope SMOOTHING / continuation step.

The endpoint-uniform propagator turns a τ-uniform `H^r` SOURCE envelope `Msup`
of a Duhamel source `F` into a SINGLE τ-uniform `H^{r+α}` envelope of the Duhamel
OUTPUT coefficients `duhamelEnergyCoeff d F s`, with NO elapsed-time blow-up
(endpoint-uniformity).  This is exactly the openness/closedness engine of the
continuation closure `P(r,s)`: monotone, endpoint-independent constant, so the
limit stays in `H^σ`.  The pointwise envelope is `coreEnv := (C·Rbar)·(1+λ)^{-α/2}·Msup`,
obtained by taking square roots of the per-mode `H^{r+α}` ENERGY bound
`duhamelEnergy_mode_endpoint_uniform`. -/

open ShenWork.Paper2.IntervalUniformBootstrap (Rbar Rbar_nonneg duhamelEnergy_mode_endpoint_uniform)
open ShenWork.Paper2.BFormHSigmaLinftyMultiplier (linfty_multiplier_bound)
open ShenWork.IntervalC2Bootstrap (weightedEnvelope weightedEnvelope_sq weightedEnvelope_nonneg)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.BFormHSigmaDuhamelMode (duhamelModeCoeff)

/-- The CORE per-mode pointwise trajectory envelope at level `r+α`:
`(C·Rbar α)·(1+λ_k)^{-α/2}·Msup k`.  Its square times `(1+λ_k)^{r+α}` equals
`(C·Rbar)²·(1+λ_k)^r·(Msup k)²`, i.e. `H^{r+α}` energy = `(C·Rbar)²·H^r`-energy. -/
def coreEnv (C α : ℝ) (Msup : ℕ → ℝ) (k : ℕ) : ℝ :=
  (C * Rbar α) * ((1 + lam k) ^ (-(α / 2)) * Msup k)

theorem coreEnv_nonneg {C α : ℝ} (hC : 0 ≤ C) (hα1 : α < 1) {Msup : ℕ → ℝ}
    (hMsup0 : ∀ k, 0 ≤ Msup k) (k : ℕ) : 0 ≤ coreEnv C α Msup k := by
  unfold coreEnv
  have hR := Rbar_nonneg hα1
  have hp := Real.rpow_nonneg (one_add_lam_pos k).le (-(α / 2))
  have := hMsup0 k; positivity

/-- The `H^{r+α}` weighted square of `coreEnv` is `(C·Rbar)²·(1+λ_k)^r·(Msup k)²`. -/
theorem coreEnv_weighted_sq (C α r : ℝ) (Msup : ℕ → ℝ) (k : ℕ) :
    (1 + lam k) ^ (r + α) * (coreEnv C α Msup k) ^ 2
      = (C * Rbar α) ^ 2 * ((1 + lam k) ^ r * (Msup k) ^ 2) := by
  have hpos := (one_add_lam_pos k)
  unfold coreEnv
  have hsplit : (1 + lam k) ^ (r + α)
      = (1 + lam k) ^ r * (1 + lam k) ^ (α : ℝ) := by
    rw [← Real.rpow_add hpos]
  have hcancel : (1 + lam k) ^ (α : ℝ) * ((1 + lam k) ^ (-(α / 2))) ^ 2 = 1 := by
    rw [← Real.rpow_natCast ((1 + lam k) ^ (-(α / 2))) 2,
      ← Real.rpow_mul hpos.le, ← Real.rpow_add hpos]
    norm_num
  calc
    (1 + lam k) ^ (r + α)
        * ((C * Rbar α) * ((1 + lam k) ^ (-(α / 2)) * Msup k)) ^ 2
        = (C * Rbar α) ^ 2 * ((1 + lam k) ^ r * (Msup k) ^ 2)
            * ((1 + lam k) ^ (α : ℝ) * ((1 + lam k) ^ (-(α / 2))) ^ 2) := by
          rw [hsplit]; ring
    _ = (C * Rbar α) ^ 2 * ((1 + lam k) ^ r * (Msup k) ^ 2) := by
          rw [hcancel, mul_one]

/-- **CORE — the trajectory-envelope smoothing step (membership half).**  If the
source envelope `Msup ∈ H^r`, then `coreEnv (C) α r Msup ∈ H^{r+α}`.  Pure
comparison: its `H^{r+α}` energy is `(C·Rbar)²` times the `H^r` energy of `Msup`. -/
theorem coreEnv_memHSigma {C α r : ℝ} {Msup : ℕ → ℝ}
    (hMsq : MemHSigma r Msup) : MemHSigma (r + α) (coreEnv C α Msup) := by
  have hcongr : (fun k => (1 + lam k) ^ (r + α) * (coreEnv C α Msup k) ^ 2)
      = fun k => (C * Rbar α) ^ 2 * ((1 + lam k) ^ r * (Msup k) ^ 2) :=
    funext (coreEnv_weighted_sq C α r Msup)
  show Summable fun k => (1 + lam k) ^ (r + α) * (coreEnv C α Msup k) ^ 2
  rw [hcongr]
  exact hMsq.mul_left _

/-- **CORE — the trajectory-envelope smoothing step (domination half).**  For
each endpoint `s ∈ (0,t]` (`t ≤ 1`), the Duhamel output coefficients are dominated
pointwise by the SINGLE `s`-independent envelope `coreEnv C α Msup`, where
`C = Classical.choose (linfty_multiplier_bound ...)`.  Square root of the per-mode
endpoint-uniform energy bound `duhamelEnergy_mode_endpoint_uniform`. -/
theorem coreEnv_dom {α r : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {d : ℝ} (hd : 0 < d) {t : ℝ} (_ht : 0 < t) (ht1 : t ≤ 1)
    {F : ℕ → ℝ → ℝ} (hFcont : ∀ k, Continuous (F k))
    {Msup : ℕ → ℝ} (hMsup0 : ∀ k, 0 ≤ Msup k)
    (hFbd : ∀ k, ∀ τ ∈ Set.Icc (0 : ℝ) t, |F k τ| ≤ Msup k) :
    ∀ s ∈ Set.Ioc (0 : ℝ) t, ∀ k,
      |duhamelEnergyCoeff d F s k|
        ≤ coreEnv (Classical.choose (linfty_multiplier_bound hα0 hα1 d hd)) α Msup k := by
  intro s hs k
  set C := Classical.choose (linfty_multiplier_bound hα0 hα1 d hd) with hCdef
  have hs0 : 0 < s := hs.1
  have hsT : s ≤ t := hs.2
  have hs1 : s ≤ 1 := le_trans hsT ht1
  have hFbd_s : ∀ k, ∀ τ ∈ Set.Icc (0 : ℝ) s, |F k τ| ≤ Msup k := by
    intro k τ hτ
    exact hFbd k τ ⟨hτ.1, le_trans hτ.2 hsT⟩
  have hmode := duhamelEnergy_mode_endpoint_uniform (r := r) hα0 hα1 hd hs0 hs1
    hFcont hMsup0 hFbd_s k
  rw [← hCdef] at hmode
  -- hmode : (1+λk)^{r+α} * coeff² ≤ (C·Rbar)² * weightedEnvelope r Msup k ²
  have hpos := one_add_lam_pos k
  have hw : (0 : ℝ) < (1 + lam k) ^ ((r + α) / 2) := Real.rpow_pos_of_pos hpos _
  -- rewrite RHS via weightedEnvelope_sq and coreEnv_weighted_sq into (weight·coreEnv)²
  have hWsq : (weightedEnvelope r Msup k) ^ 2 = (1 + lam k) ^ r * (Msup k) ^ 2 :=
    weightedEnvelope_sq r Msup k
  have hweightsq : ((1 + lam k) ^ ((r + α) / 2)) ^ 2 = (1 + lam k) ^ (r + α) := by
    rw [← Real.rpow_natCast ((1 + lam k) ^ ((r + α) / 2)) 2,
      ← Real.rpow_mul hpos.le]
    norm_num
  have hRHS : (C * Rbar α) ^ 2 * (weightedEnvelope r Msup k) ^ 2
      = ((1 + lam k) ^ ((r + α) / 2) * coreEnv C α Msup k) ^ 2 := by
    rw [hWsq]
    rw [show ((1 + lam k) ^ ((r + α) / 2) * coreEnv C α Msup k) ^ 2
        = ((1 + lam k) ^ ((r + α) / 2)) ^ 2 * (coreEnv C α Msup k) ^ 2 from mul_pow _ _ 2,
      hweightsq, coreEnv_weighted_sq C α r Msup k]
  have hLHS : (1 + lam k) ^ (r + α) * (duhamelEnergyCoeff d F s k) ^ 2
      = ((1 + lam k) ^ ((r + α) / 2) * duhamelEnergyCoeff d F s k) ^ 2 := by
    rw [mul_pow, hweightsq]
  rw [hLHS, hRHS] at hmode
  -- now (w·coeff)² ≤ (w·coreEnv)²; w>0 ⇒ |coeff| ≤ w·coreEnv ; coreEnv ≥ 0
  have hcore0 : 0 ≤ coreEnv C α Msup k :=
    coreEnv_nonneg (Classical.choose_spec (linfty_multiplier_bound hα0 hα1 d hd)).1.le
      hα1 hMsup0 k
  have hrhs0 : 0 ≤ (1 + lam k) ^ ((r + α) / 2) * coreEnv C α Msup k :=
    mul_nonneg hw.le hcore0
  have habs : |(1 + lam k) ^ ((r + α) / 2) * duhamelEnergyCoeff d F s k|
      ≤ (1 + lam k) ^ ((r + α) / 2) * coreEnv C α Msup k :=
    abs_le_of_sq_le_sq hmode hrhs0
  rw [abs_mul, abs_of_pos hw] at habs
  exact le_of_mul_le_mul_left habs hw

/-- **CORE — the τ-uniform trajectory-`H^{r+α}` envelope of the Duhamel output.**
Bundles the membership + domination halves into a `TrajectoryHSigmaEnvelope` over
`(0,t]` (the endpoint `0` is invisible to the Duhamel integral, so the window is
`Ioc`).  This IS the abstract `Uσ` the LAYER-2 wiring consumes — produced from the
source envelope by the endpoint-uniform propagator, NON-circularly (no classical
regularity), as the monotone continuation closure. -/
def trajectoryEnvelope_of_sourceEnvelope {α r : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {d : ℝ} (hd : 0 < d) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {F : ℕ → ℝ → ℝ} (hFcont : ∀ k, Continuous (F k))
    {Msup : ℕ → ℝ} (hMsup0 : ∀ k, 0 ≤ Msup k)
    (hMsq : MemHSigma r Msup)
    (hFbd : ∀ k, ∀ τ ∈ Set.Icc (0 : ℝ) t, |F k τ| ≤ Msup k) :
    TrajectoryHSigmaEnvelope (r + α) t (fun s k => duhamelEnergyCoeff d F s k) where
  env := coreEnv (Classical.choose (linfty_multiplier_bound hα0 hα1 d hd)) α Msup
  henv := coreEnv_memHSigma hMsq
  hdom := by
    intro s hs k
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · -- s = 0 : duhamelEnergyCoeff vanishes (empty integration window), ≤ env
      have hz : duhamelEnergyCoeff d F s k = 0 := by
        rw [← hs0]
        show duhamelModeCoeff d (lam k) (F k) 0 = 0
        unfold duhamelModeCoeff
        simp
      rw [hz, abs_zero]
      exact coreEnv_nonneg
        (Classical.choose_spec (linfty_multiplier_bound hα0 hα1 d hd)).1.le hα1 hMsup0 k
    · exact coreEnv_dom (r := r) hα0 hα1 hd ht ht1 hFcont hMsup0 hFbd s ⟨hs0, hs.2⟩ k

/-! ## STALL REPORT — what is built, what remains, real-gap vs circularity.

  BUILT (all `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`, 0 sorry):

  * LAYER-2 WIRING (COMPLETE).  `fluxEnvelope_of_factorEnvelopes` produces the
    `(genv σ, hg, hg_dom σ)` triple of `SliceMildStepData` from a τ-uniform factor
    package `FluxFactorEnvelopes σ t Q` (cosine env `gW` of `W=u·(1+v)^{−β}`, sine
    env `gvx` of `v_x`), via `IntervalMixedProduct.fluxSineEnvelope_uniform`.
    `logisticEnvelope_of_traj` produces `(glenv σ, hgl, hgl_dom)` from a
    `TrajectoryHSigmaEnvelope σ t Fl`.  So GIVEN the abstract trajectory envelopes,
    the genv/glenv fields are mechanical — wiring fully discharged.

  * LAYER-1 CORE smoothing step (PROVEN).  `trajectoryEnvelope_of_sourceEnvelope`:
    from a τ-uniform `H^r` envelope `Msup` of a Duhamel SOURCE `F`, the
    endpoint-uniform propagator yields a SINGLE τ-uniform `H^{r+α}` envelope
    `coreEnv = (C·Rbar α)·(1+λ)^{−α/2}·Msup` of the Duhamel OUTPUT coefficients
    `duhamelEnergyCoeff d F s` over `(0,t]` — the openness/closedness engine of the
    continuation closure, with NO elapsed-time blow-up (endpoint-uniform constant
    `C·Rbar α`, independent of `s`).  Closedness needs NO ℓ²-sup argument: `coreEnv`
    is an explicit `H^{r+α}` DOMINATOR, and membership/domination follow by
    `Summable.of_nonneg_of_le` + `abs_le_of_sq_le_sq` (the route's "monotone
    recurrence collapses to one application").

  PRECISE RESIDUAL (one genuine analytic input, NON-circular — NOT exposed as a
  circularity):

  To instantiate a FULL `SliceMildStepData` two pieces remain, both upstream of
  the engine and independent of classical regularity:

  (R1) the BASE trajectory envelope: a τ-uniform `H^{σ₀}` envelope of `u(τ)` and
       `v(τ)` over `[0,t]` at the SEED regularity `σ₀ > 1/2`, to start the factor
       chain (`gW` via `fluxCosEnvelope_of_factorEnvelopes`, `gvx` via the elliptic
       resolver `resolverCoeff` + √λ).  The mild data gives a τ-uniform L∞ ball
       (`ConjugateMildExistenceData.hbase_ball`, `|u(τ,x)|≤M`), but L∞ has no
       high-frequency decay so the constant sequence `k↦2M ∉ H^{σ₀}` (σ₀>0): the
       SEED genuinely requires the FIRST positive-time smoothing.  This is exactly
       `trajectoryEnvelope_of_sourceEnvelope` with `r=−α` (or weakening `[0,t]` to
       `Ioc 0 t` since the endpoint is invisible to the Duhamel integral) — i.e.
       the CORE step seeds itself from the L∞ ball through ONE smoothing pass.

  (R2) the B-form SPECTRAL kernel identity bridging the CORE output to the field:
       `cosineCoeffs (conjugateSlice p u₀ T s) = duhamelEnergyCoeff d Fsrc s` for
       the conjugate flux source `Fsrc` (so the CORE's `duhamelEnergyCoeff`
       envelope IS an envelope of the slice cosine coeffs).  No such identity
       exists in Paper2 yet (grep: no `cosineCoeffs … = duhamelEnergyCoeff …`
       theorem).  This is the SAME "missing B-form→spectral kernel identity" the
       landed `conjugatePicardLimit_slice_memHSigma_one_of_step` header names.

  VERDICT: REAL GAP, NOT CIRCULARITY.  (R1)+(R2) are the bootstrap's own monotone
  induction seeded by the L∞ ball + the B-form spectral identity — all strictly
  upstream of `localClassicalSolution`/`IsPaper2ClassicalSolution` (which this file
  never imports; confirmed by `#print axioms`).  The self-reference (source = flux
  built from the very trajectory envelope being produced) is resolved by the
  MONOTONE recurrence: the CORE step is monotone in `Msup` and endpoint-uniform, so
  iterating from the L∞-seeded `H^{σ₀}` envelope up the σ-ladder is well-founded
  and stays in `H^σ` — the route's continuation closure.  The structural verdict
  (non-circular discharge of genv/glenv from mild data) therefore STANDS. -/

end ShenWork.Paper2.IntervalTrajectoryEnvelope

namespace ShenWork.Paper2.IntervalTrajectoryEnvelope
#print axioms fluxEnvelope_of_factorEnvelopes
#print axioms flux_memHSigma
#print axioms flux_dom
#print axioms logisticEnvelope_of_traj
#print axioms coreEnv_memHSigma
#print axioms coreEnv_dom
#print axioms trajectoryEnvelope_of_sourceEnvelope
end ShenWork.Paper2.IntervalTrajectoryEnvelope
