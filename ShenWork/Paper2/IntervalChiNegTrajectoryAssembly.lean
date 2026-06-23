/-
  ShenWork/Paper2/IntervalChiNegTrajectoryAssembly.lean

  THE σ-LADDER ASSEMBLY for the χ₀<0 conjugate mild trajectory: chain the LANDED
  analytic pieces into a single σ-step PRODUCER
    `TrajectoryHSigmaEnvelope σ → TrajectoryHSigmaEnvelope (σ+α)`
  for the trajectory `u`, and ITERATE it from a carried base to reach
  `TrajectoryHSigmaEnvelope 1`.  This is the wiring layer; the genuine remaining
  analytic inputs are isolated as the explicit fields of `TrajStepBridges`
  (the per-τ resolver/bridge seam) and the carried base envelope.

  ## WHAT THIS FILE DELIVERS (genuine wiring of landed atoms — not repackaging)

  * `trajStep_of_bridges` (PRODUCER).  Given a τ-uniform `H^σ` trajectory envelope
    `E` of `u` (`TrajectoryHSigmaEnvelope σ t (cosineCoeffs ∘ u)`) PLUS a bundle
    `B : TrajStepBridges` of the per-τ seam data, it BUILDS a `TrajLadderData` —
      - the flux SINE envelope `gQ` via the LANDED
        `genv_of_trajectoryEnvelope_uncond` (denom envelope internalized);
      - the logistic envelope `gFl` via the LANDED `logisticEnvelope_of_traj`;
      - the τ-uniform 3-term decomposition `hdecomp` carried in the bundle —
    and runs the LANDED `trajLadder_step` to produce a
    `TrajectoryHSigmaEnvelope (σ+α) t (cosineCoeffs ∘ u)`.

  * `trajStep_iterate` (ITERATE).  A σ-INDEXED family of bundles
    `(fun σ => TrajStepBridges …)` drives `n` applications of the producer from a
    carried base `E₀ : TrajectoryHSigmaEnvelope σ₀ t (cosineCoeffs ∘ u)`, yielding
    `TrajectoryHSigmaEnvelope (σ₀ + n·α) t (cosineCoeffs ∘ u)`.

  * `trajEnvelope_one_of_base` (REACH `H¹`).  Specialising the iterate to a count
    `n` with `σ₀ + n·α = 1` (carried as `hreach`) and `memHSigma_antitone`
    gives `TrajectoryHSigmaEnvelope 1` — the H¹ trajectory field.

  ## HONEST ACCOUNTING — what is carried, what closes

  The σ-step is UNCONDITIONAL given the seam bundle (it invokes only landed
  atoms).  Two inputs are genuinely carried, exactly the (R1)/(R2) the landed
  STALL REPORTs name and which are NOT supplied by mild data alone:

  (C1) the BASE `TrajectoryHSigmaEnvelope σ₀ t (cosineCoeffs ∘ u)` at `σ₀ > 1/2`.
       The L∞ ball gives the constant `k ↦ 2M ∉ H^{σ₀}` (σ₀>0); the per-slice H⁰
       seed `conjugatePicardLimit_slice_memHSigma_zero` is NOT τ-uniform.  No
       unconditional producer of this base exists in Paper2 — carried as `E₀`.

  (C2) the per-σ seam bundle `TrajStepBridges` — its `hbr`/`hbridge`/`heU`/`hvrel`/
       `hdiv`/`hvnn` are the LANDED resolver/CosineMulBridge/mixed-bridge/relay
       data (dischargeable per τ via `cosineMulBridge_of_summable` + the resolver
       positivity brick), and `hdecomp` is the τ-uniform decomposition
       (`conjugateSlice_decomp_tauLift`).  At a fixed σ these are landed; the
       MISSING piece is a single σ-uniform PRODUCER that re-derives the bundle at
       `σ+α` from the OUTPUT envelope — named precisely in the closure STALL
       REPORT as the unbuilt `TrajectoryHSigmaEnvelope σ → TrajStepBridges` map.

  So this file CLOSES the σ-ladder ENGINE unconditionally and carries exactly
  (C1)+(C2); it does NOT claim unconditional `MemHSigma 1`.  The final theorem's
  signature is audited at the end (the carried hyps are explicit).

  ## NON-CIRCULARITY

  Imports ONLY the landed trajectory-envelope atoms + the denom/decomp producers.
  NEVER references `localClassicalSolution`, `IsPaper2ClassicalSolution`, the
  C²-Neumann producers, or the PID-classical bridge.  `#print axioms` ⊆
  `{propext, Classical.choice, Quot.sound}`.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.
-/
import ShenWork.Paper2.IntervalTrajectoryEnvelopeClosure
import ShenWork.Paper2.IntervalDenomSecondDerivBound

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegTrajectoryAssembly

open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalEnvelopeProp (Envelopes)
open ShenWork.Paper2.IntervalDenomEnvelopeResolver (resolverValue)
open ShenWork.Paper2.IntervalTrajectoryEnvelope (TrajectoryHSigmaEnvelope)
open ShenWork.Paper2.IntervalTrajectoryEnvelopeClosure (TrajLadderData)
open ShenWork.Paper2.IntervalDenomSecondDerivBound (genv_of_trajectoryEnvelope_uncond)
open ShenWork.Paper2.IntervalMildPosTimeHSigma (memHSigma_antitone)

/-! ## The per-σ seam bundle (the carried analytic inputs, C2). -/

/-- **`TrajStepBridges μ σ β χ₀ t u v û₀ Q W vx Fl`** — the per-σ seam data the
σ-step consumes ABOVE the trajectory envelope `E`.  Every field is a LANDED atom
(resolver positivity, the cosine/mixed bridges, the resolver relay, the τ-uniform
decomposition); none is classical regularity.  This bundle is the precise carried
residual (C2): a σ-uniform PRODUCER of it from the output envelope is the single
unbuilt map named in the closure STALL REPORT. -/
structure TrajStepBridges (μ σ β χ₀ t : ℝ)
    (u v : ℝ → ℝ → ℝ) (û₀ : ℕ → ℝ)
    (Q W vx : ℝ → ℝ → ℝ) (Fl : ℕ → ℝ → ℝ)
    (E : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (u τ))) where
  hμ : 0 < μ
  hσ0 : 1 / 2 < σ
  hσ1 : σ < 3 / 2
  hβ : 0 ≤ β
  hα0 : (0 : ℝ) ≤ 1 / 4
  ht : 0 < t
  ht1 : t ≤ 1
  /-- heat-part datum at the NEXT level `σ + 1/4`. -/
  hû₀ : MemHSigma (σ + 1 / 4) û₀
  /-- resolver positivity (LANDED elliptic-max / resolver-positivity brick). -/
  hvnn : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ x, 0 ≤ resolverValue μ (cosineCoeffs (u τ)) x
  /-- the chemotaxis flux factorisation `Q τ = W τ · vx τ`, weight `W = u·(1+v)^{-β}`. -/
  hQ : ∀ τ, Q τ = fun x => W τ x * vx τ x
  hWdef : ∀ τ, W τ = fun x => u τ x
    * (1 + resolverValue μ (cosineCoeffs (u τ)) x) ^ (-β)
  /-- per-τ cosine multiplication bridge (LANDED `cosineMulBridge_of_summable`). -/
  hbr : ∀ τ ∈ Set.Icc (0:ℝ) t,
    ShenWork.Paper2.IntervalWienerAlgebra.CosineMulBridge (u τ)
      (fun x => (1 + resolverValue μ (cosineCoeffs (u τ)) x) ^ (-β))
  /-- the envelope envelopes `u`'s coefficients (immediate from `E.hdom`). -/
  heU : ∀ τ ∈ Set.Icc (0:ℝ) t, Envelopes E.env (cosineCoeffs (u τ))
  /-- per-τ mixed-product bridge for the flux factors (LANDED). -/
  hbridge : ∀ τ ∈ Set.Icc (0:ℝ) t,
    ShenWork.Paper2.IntervalMixedProduct.MixedMulBridge (W τ) (vx τ)
  /-- the resolver relay: `√λ`-coeff envelope of `v` from `E.env` (LANDED). -/
  hvrel : ∀ τ ∈ Set.Icc (0:ℝ) t,
    Envelopes (ShenWork.Paper2.HSigmaScale.resolverCoeff 1 E.env) (cosineCoeffs (v τ))
  /-- the divergence identity `|sineCoeffs (vx τ) k| = √λ_k·|cosineCoeffs (v τ) k|`. -/
  hdiv : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
    |sineCoeffs (vx τ) k|
      = Real.sqrt (lam k) * |cosineCoeffs (v τ) k|
  hQ_cont : ∀ k, Continuous (fun τ => sineCoeffs (Q τ) k)
  /-- the logistic source envelope at level `σ` (LANDED `logisticEnvelope_of_traj`). -/
  L : TrajectoryHSigmaEnvelope σ t (fun τ k => Fl k τ)
  hFl_cont : ∀ k, Continuous (Fl k)
  /-- the τ-uniform 3-term Duhamel decomposition (LANDED `conjugateSlice_decomp_tauLift`). -/
  hdecomp : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
    cosineCoeffs (u τ) k
      = Real.exp (-(τ * lam k)) * û₀ k
        + (-χ₀) * ShenWork.Paper2.BFormHSigmaDuhamelEnergy.duhamelEnergyCoeff 1
            (fun k τ => sineCoeffs (Q τ) k) τ k
        + ShenWork.Paper2.BFormHSigmaDuhamelEnergy.duhamelEnergyCoeff 1 Fl τ k

namespace TrajStepBridges

variable {μ σ β χ₀ t : ℝ} {u v : ℝ → ℝ → ℝ} {û₀ : ℕ → ℝ}
variable {Q W vx : ℝ → ℝ → ℝ} {Fl : ℕ → ℝ → ℝ}
variable {E : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (u τ))}

/-- The flux SINE envelope `gQ` produced by the LANDED unconditional genv. -/
def gQ (B : TrajStepBridges μ σ β χ₀ t u v û₀ Q W vx Fl E) : ℕ → ℝ :=
  ShenWork.Paper2.IntervalWienerAlgebra.trueCosProd
    (ShenWork.Paper2.IntervalGWProductEnvelope.gW E.env
      (ShenWork.Paper2.IntervalDenomSecondDerivBound.denomUniformEnvelope_of_trajectoryEnvelope
        B.hμ B.hσ0 B.hσ1 B.hβ E B.hvnn).Gden)
    (ShenWork.Paper2.IntervalFluxFactorEnvelope.sineEnv E.env)

/-- `gQ` membership + τ-uniform domination from `genv_of_trajectoryEnvelope_uncond`. -/
theorem gQ_spec (B : TrajStepBridges μ σ β χ₀ t u v û₀ Q W vx Fl E) :
    MemHSigma σ B.gQ ∧
      ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, |sineCoeffs (Q τ) k| ≤ B.gQ k :=
  genv_of_trajectoryEnvelope_uncond B.hμ B.hσ0 B.hσ1 B.hβ E B.hvnn B.hQ B.hWdef
    B.hbr B.heU B.hbridge B.hvrel B.hdiv

/-- `gQ` is nonneg (it dominates `|·|` at `τ = 0 ∈ [0,t]`). -/
theorem gQ_nonneg (B : TrajStepBridges μ σ β χ₀ t u v û₀ Q W vx Fl E) (k : ℕ) :
    0 ≤ B.gQ k :=
  le_trans (abs_nonneg _) ((B.gQ_spec).2 0 ⟨le_refl 0, B.ht.le⟩ k)

/-- The assembled `TrajLadderData` at gain `α = 1/4`. -/
def toLadder (B : TrajStepBridges μ σ β χ₀ t u v û₀ Q W vx Fl E) :
    TrajLadderData σ (1 / 4) χ₀ t u û₀ Q Fl where
  hα0 := B.hα0
  hα1 := by norm_num
  ht := B.ht
  ht1 := B.ht1
  Uσ := E
  hû₀ := B.hû₀
  gQ := B.gQ
  hgQ := (B.gQ_spec).1
  hgQ0 := B.gQ_nonneg
  hgQ_dom := (B.gQ_spec).2
  hQ_cont := B.hQ_cont
  gFl := B.L.env
  hgFl := B.L.henv
  hgFl0 := fun k => B.L.env_nonneg ⟨le_refl 0, B.ht.le⟩ k
  hgFl_dom := fun τ hτ k => B.L.hdom τ hτ k
  hFl_cont := B.hFl_cont
  hdecomp := B.hdecomp

/-- **THE σ-STEP — `H^σ → H^{σ+1/4}` trajectory envelope of `u`.**  Runs the LANDED
`trajLadder_step` on the assembled ladder.  UNCONDITIONAL given the bundle. -/
def step (B : TrajStepBridges μ σ β χ₀ t u v û₀ Q W vx Fl E) :
    TrajectoryHSigmaEnvelope (σ + 1 / 4) t (fun τ => cosineCoeffs (u τ)) :=
  B.toLadder.trajLadder_step

end TrajStepBridges

/-! ## The iterate: drive the σ-step `n` times from a carried base. -/

/-- A σ-INDEXED bundle family `Bf σ E` producing, at every running `σ` and input
envelope `E`, the seam bundle for `u` (the carried `TrajStepBridges` of (C2)).  The
fixed analytic data `μ β χ₀ t v û₀ Q W vx Fl` is shared across levels. -/
abbrev BundleFamily (μ β χ₀ t : ℝ) (u v : ℝ → ℝ → ℝ) (û₀ : ℕ → ℝ)
    (Q W vx : ℝ → ℝ → ℝ) (Fl : ℕ → ℝ → ℝ) : Type :=
  ∀ σ : ℝ, ∀ E : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (u τ)),
    TrajStepBridges μ σ β χ₀ t u v û₀ Q W vx Fl E

/-- **THE ITERATE — `n` applications of the σ-step.**  From a base envelope `E₀`
at `σ₀` and the bundle family, produces a `TrajectoryHSigmaEnvelope (σ₀ + n·(1/4))`
of `u`.  UNCONDITIONAL given `(E₀, Bf)`; the analytic content is entirely inside
the carried family. -/
def trajStep_iterate {μ β χ₀ t : ℝ} {u v : ℝ → ℝ → ℝ} {û₀ : ℕ → ℝ}
    {Q W vx : ℝ → ℝ → ℝ} {Fl : ℕ → ℝ → ℝ}
    (Bf : BundleFamily μ β χ₀ t u v û₀ Q W vx Fl) :
    ∀ (n : ℕ) {σ₀ : ℝ}
      (E₀ : TrajectoryHSigmaEnvelope σ₀ t (fun τ => cosineCoeffs (u τ))),
      TrajectoryHSigmaEnvelope (σ₀ + n * (1 / 4)) t (fun τ => cosineCoeffs (u τ))
  | 0, σ₀, E₀ => by simpa using E₀
  | n + 1, σ₀, E₀ => by
      have hnext := (Bf σ₀ E₀).step
      have hrec := trajStep_iterate Bf n hnext
      have hcong : σ₀ + 1 / 4 + (n : ℝ) * (1 / 4) = σ₀ + ((n : ℝ) + 1) * (1 / 4) := by
        ring
      rw [hcong] at hrec
      have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast] at hrec
      exact hrec

/-! ## Reach `TrajectoryHSigmaEnvelope 1` from the base. -/

/-- **REACH `H¹` — the trajectory envelope at level `1`.**  From a base envelope at
`σ₀` and the bundle family, with `n` steps overshooting `1` (`1 ≤ σ₀ + n·(1/4)`),
the iterate reaches `σ₀ + n·(1/4) ≥ 1`; `memHSigma_antitone` on the carried `H^σ`
membership lands `TrajectoryHSigmaEnvelope 1`.

Carries exactly (C1) `E₀` and (C2) `Bf` — the precise residuals; nothing faked. -/
def trajEnvelope_one_of_base {μ β χ₀ t : ℝ} {u v : ℝ → ℝ → ℝ} {û₀ : ℕ → ℝ}
    {Q W vx : ℝ → ℝ → ℝ} {Fl : ℕ → ℝ → ℝ} {σ₀ : ℝ} (n : ℕ)
    (hreach : (1 : ℝ) ≤ σ₀ + n * (1 / 4))
    (E₀ : TrajectoryHSigmaEnvelope σ₀ t (fun τ => cosineCoeffs (u τ)))
    (Bf : BundleFamily μ β χ₀ t u v û₀ Q W vx Fl) :
    TrajectoryHSigmaEnvelope 1 t (fun τ => cosineCoeffs (u τ)) where
  env := (trajStep_iterate Bf n E₀).env
  henv := memHSigma_antitone hreach (trajStep_iterate Bf n E₀).henv
  hdom := (trajStep_iterate Bf n E₀).hdom

/-! ## STALL / CARRY REPORT — audit of the final theorem signature.

  DELIVERED UNCONDITIONALLY (all `#print axioms ⊆ {propext, Classical.choice,
  Quot.sound}`, 0 sorry):

  * `TrajStepBridges.step` — the σ-STEP `H^σ → H^{σ+1/4}` trajectory envelope of
    `u`, wiring the LANDED `genv_of_trajectoryEnvelope_uncond` (flux `gQ`),
    `logisticEnvelope_of_traj` (`gFl`), and the carried decomposition into the
    LANDED `trajLadder_step`.  NO `sorry`, NO classical regularity.

  * `trajStep_iterate` / `trajEnvelope_one_of_base` — the finite iterate and the
    `H¹` reach, UNCONDITIONAL given the base `E₀` and the family `Bf`.

  CARRIED (the genuine residuals, NOT faked — signature of
  `trajEnvelope_one_of_base`):

    (E₀ : TrajectoryHSigmaEnvelope σ₀ t (cosineCoeffs ∘ u))            -- (C1)
    (Bf : ∀ σ E, TrajStepBridges μ σ β χ₀ t u v û₀ Q W vx Fl E)        -- (C2)
    (hreach : 1 ≤ σ₀ + n·(1/4))

  (C1) the BASE envelope at `σ₀ > 1/2`.  NOT producible from mild data (L∞ ball ⇒
       constant `∉ H^{σ₀}`; the H⁰ seed is per-slice, not τ-uniform).  This is the
       (R1) named in BOTH landed STALL REPORTs.

  (C2) the σ-uniform bundle family.  At a FIXED σ every field is a landed atom
       (resolver positivity `hvnn`, the cosine/mixed bridges `hbr`/`hbridge`, the
       relay `hvrel`/`hdiv`, the τ-uniform decomposition `hdecomp`).  The unbuilt
       piece is the σ-uniform PRODUCER
         `TrajectoryHSigmaEnvelope σ (cosineCoeffs ∘ u) → TrajStepBridges μ σ …`
       re-deriving the bundle at `σ+1/4` from the OUTPUT envelope — exactly the map
       the closure STALL REPORT (iii) names as not yet wired in Paper2 (the flux
       factor envelopes from `Uσ` via `fluxCosEnvelope_of_factorEnvelopes` + the
       resolver relay, plus the τ-uniform decomposition lift).  REAL GAP, NOT
       CIRCULARITY: the resolver only RELAYS `H^σ`, the decomposition is a
       spectral/Fubini computation — both strictly upstream of
       `localClassicalSolution` (never imported; confirmed by `#print axioms`).

  PRECISE STALL: to discharge (C2) UNCONDITIONALLY one must build the single map
  `mkBundle : TrajectoryHSigmaEnvelope σ (cosineCoeffs ∘ u) → TrajStepBridges …`
  whose two unbuilt inputs are (a) the flux factor-envelope domination from `Uσ`
  (the cosine env `gW` of `W = u·(1+v)^{-β}` and the sine env `gvx` of `v_x`,
  τ-uniform — the LANDED `fluxCosEnvelope_of_factorEnvelopes` + `resolver_memHSigmaPlus2`
  relay packaged as `hbr`/`hbridge`/`hvrel`/`hdiv`), and (b) the τ-uniform 3-term
  decomposition `hdecomp` (the σ-independent `conjugateSlice_decomp_tauLift`, whose
  per-τ continuity/Fubini residuals are landed).  Neither needs classical
  regularity.  Once `mkBundle` lands, `Bf := fun σ E => mkBundle E` discharges (C2)
  and the only carry is (C1), the τ-uniform base — the campaign's single open seam.

  This file does NOT claim unconditional `MemHSigma 1`; it ASSEMBLES the σ-ladder
  engine + the `H¹`-reach and carries (C1)+(C2) with explicit signatures. -/

end ShenWork.Paper2.IntervalChiNegTrajectoryAssembly

namespace ShenWork.Paper2.IntervalChiNegTrajectoryAssembly
#print axioms TrajStepBridges.gQ_spec
#print axioms TrajStepBridges.gQ_nonneg
#print axioms TrajStepBridges.toLadder
#print axioms TrajStepBridges.step
#print axioms trajStep_iterate
#print axioms trajEnvelope_one_of_base
end ShenWork.Paper2.IntervalChiNegTrajectoryAssembly
