/-
  ShenWork/Paper2/IntervalTrajectoryEnvelopeClosure.lean

  THE σ-LADDER CONTINUATION CLOSURE STEP for the χ₀<0 mild-trajectory H^σ
  envelope (R1) — built ON the landed propagator
  (`trajectoryEnvelope_of_sourceEnvelope`) + the landed envelope algebra
  (`fluxSineEnvelope_uniform`, `memHSigma_add`/`memHSigma_smul`), NON-CIRCULARLY.

  ## What this file delivers

  * (i) THE σ-LADDER STEP (`trajLadder_step`, UNCONDITIONAL given the ladder
    bundle).  From a τ-uniform `H^σ` trajectory envelope `Uσ` for `u` over `[0,t]`
    (a `TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (u τ))`), together with
    the τ-uniform 3-term Duhamel decomposition of `cosineCoeffs (u τ)` (heat +
    chemotaxis-flux Duhamel + logistic-source Duhamel) and the σ-level flux/source
    envelopes (the flux SINE envelope `gQ` from `fluxSineEnvelope_uniform`, the
    logistic envelope `gFl`, both `∈ H^σ`, both built from `Uσ`), the file PRODUCES
    a τ-uniform `H^{σ+α}` trajectory envelope `Uσ₊α` for the SAME `u`.

    Mechanism (the route's openness/closedness engine, no ℓ²-sup, no Gronwall):
      - feed the flux SINE source `Fc τ k = sineCoeffs (Q τ) k` (dominated by
        `gQ ∈ H^σ`) to the landed propagator → chemotaxis OUTPUT envelope
        `coreEnv … ∈ H^{σ+α}` (gain α), τ-uniform via endpoint-uniformity;
      - feed the logistic source `Fl` (dominated by `gFl ∈ H^σ`) to the propagator
        → logistic OUTPUT envelope `∈ H^{σ+α}`;
      - the HEAT part `exp(-τλ_k)·û₀_k` is dominated by `|û₀_k|` (since `0 ≤ τ` ⇒
        `exp(-τλ_k) ≤ 1`), requiring only `û₀ ∈ H^{σ+α}` (the datum's base
        regularity, NOT a flux estimate);
      - SUM the three `H^{σ+α}` envelopes (closed by `memHSigma_add`/`memHSigma_smul`)
        and dominate `|cosineCoeffs (u τ) k|` by the τ-uniform 3-term decomposition.

  ## NON-CIRCULARITY (tested by compilation)

  Imports ONLY the landed propagator + the envelope algebra
  (`IntervalTrajectoryEnvelope`) and the Duhamel coefficient.  NEVER references
  `localClassicalSolution`, `IsPaper2ClassicalSolution`, the C²-Neumann producers,
  or the PID-classical bridge.  `#print axioms` ⊆ {propext, Classical.choice,
  Quot.sound}.  The self-reference (the flux source is built from the very `u`
  whose envelope is produced) is resolved by the MONOTONE recurrence: the step is
  monotone in `Uσ` and endpoint-uniform, so it is `H^σ → H^{σ+α}` with no elapsed-
  time blow-up — the route's continuation closure.

  ## THE PRECISE RESIDUAL (stall, see report at the end)

  (ii) the BASE `TrajectoryHSigmaEnvelope σ₀ t u` and (iii) iterating (i) to σ>1/2
  are NOT closed unconditionally here.  Both reduce to one genuine analytic input
  that is upstream of classical regularity but NOT supplied by mild data alone (the
  τ-uniform 3-term decomposition `hdecomp` of the bundle, and the τ-uniform flux/
  source envelope domination), exactly as the landed STALL REPORT (R1)+(R2) names.
  The ladder bundle isolates them as explicit fields, so (i) is the maximally
  useful self-contained partial; (ii)/(iii) are reported precisely, NOT faked.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.
-/
import ShenWork.Paper2.IntervalTrajectoryEnvelope

noncomputable section

namespace ShenWork.Paper2.IntervalTrajectoryEnvelopeClosure

open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (lam lam_nonneg MemHSigma)
open ShenWork.Paper2.IntervalWienerAlgebra (memHSigma_add memHSigma_smul)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.BFormHSigmaLinftyMultiplier (linfty_multiplier_bound)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalTrajectoryEnvelope
  (TrajectoryHSigmaEnvelope coreEnv coreEnv_nonneg coreEnv_memHSigma
   trajectoryEnvelope_of_sourceEnvelope)

/-! ## The σ-ladder bundle. -/

/-- **`TrajLadderData σ α χ₀ t u û₀ Q Fl`** — the data the σ-ladder step consumes
at running regularity `σ`, to gain `α`.  Every field is upstream of classical
regularity; the genuine residual analytic inputs are exactly `hdecomp` (the
τ-uniform 3-term Duhamel decomposition of `cosineCoeffs (u τ)`) together with the
flux/source envelope dominations `hgQ_dom`/`hgFl_dom`. -/
structure TrajLadderData (σ α χ₀ t : ℝ) (u : ℝ → ℝ → ℝ) (û₀ : ℕ → ℝ)
    (Q : ℝ → ℝ → ℝ) (Fl : ℕ → ℝ → ℝ) where
  hα0 : 0 ≤ α
  hα1 : α < 1
  ht : 0 < t
  ht1 : t ≤ 1
  /-- the input τ-uniform `H^σ` trajectory envelope `Uσ` for `u` (the recurrence
  datum that drives the flux/source envelopes). -/
  Uσ : TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (u τ))
  /-- heat-part datum at the NEXT level `σ+α` (the base regularity of `û₀`). -/
  hû₀ : MemHSigma (σ + α) û₀
  /-- σ-level flux SINE envelope `gQ ∈ H^σ` (from `Uσ` via `fluxSineEnvelope_uniform`). -/
  gQ : ℕ → ℝ
  hgQ : MemHSigma σ gQ
  hgQ0 : ∀ k, 0 ≤ gQ k
  hgQ_dom : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, |sineCoeffs (Q τ) k| ≤ gQ k
  hQ_cont : ∀ k, Continuous (fun τ => sineCoeffs (Q τ) k)
  /-- σ-level logistic source envelope `gFl ∈ H^σ` (from `Uσ`). -/
  gFl : ℕ → ℝ
  hgFl : MemHSigma σ gFl
  hgFl0 : ∀ k, 0 ≤ gFl k
  hgFl_dom : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, |Fl k τ| ≤ gFl k
  hFl_cont : ∀ k, Continuous (Fl k)
  /-- the τ-UNIFORM 3-term Duhamel decomposition of the trajectory coefficients. -/
  hdecomp : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
    cosineCoeffs (u τ) k
      = Real.exp (-(τ * lam k)) * û₀ k
        + (-χ₀) * duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (Q τ) k) τ k
        + duhamelEnergyCoeff 1 Fl τ k

namespace TrajLadderData

variable {σ α χ₀ t : ℝ} {u : ℝ → ℝ → ℝ} {û₀ : ℕ → ℝ} {Q : ℝ → ℝ → ℝ} {Fl : ℕ → ℝ → ℝ}

/-- The chemotaxis OUTPUT envelope at level `σ+α`: the propagator applied to the
flux SINE source, dominated τ-uniformly over `(0,t]`.  `H^{σ+α}` by gain `α`. -/
def chemOut (D : TrajLadderData σ α χ₀ t u û₀ Q Fl) :
    TrajectoryHSigmaEnvelope (σ + α) t
      (fun s k => duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (Q τ) k) s k) :=
  trajectoryEnvelope_of_sourceEnvelope (r := σ) D.hα0 D.hα1 (d := 1) one_pos D.ht D.ht1
    (F := fun k τ => sineCoeffs (Q τ) k) D.hQ_cont (Msup := D.gQ) D.hgQ0 D.hgQ
    (fun k τ hτ => D.hgQ_dom τ hτ k)

/-- The logistic OUTPUT envelope at level `σ+α`: the propagator applied to the
logistic source, dominated τ-uniformly over `(0,t]`.  `H^{σ+α}` by gain `α`. -/
def logOut (D : TrajLadderData σ α χ₀ t u û₀ Q Fl) :
    TrajectoryHSigmaEnvelope (σ + α) t
      (fun s k => duhamelEnergyCoeff 1 Fl s k) :=
  trajectoryEnvelope_of_sourceEnvelope (r := σ) D.hα0 D.hα1 (d := 1) one_pos D.ht D.ht1
    (F := Fl) D.hFl_cont (Msup := D.gFl) D.hgFl0 D.hgFl
    (fun k τ hτ => D.hgFl_dom τ hτ k)

/-- The summed `H^{σ+α}` envelope sequence: `|û₀| + |χ₀|·chemEnv + logEnv`. -/
def ladderEnv (D : TrajLadderData σ α χ₀ t u û₀ Q Fl) (k : ℕ) : ℝ :=
  |û₀ k| + (|χ₀| * D.chemOut.env k + D.logOut.env k)

theorem ladderEnv_memHSigma (D : TrajLadderData σ α χ₀ t u û₀ Q Fl) :
    MemHSigma (σ + α) D.ladderEnv := by
  have habs : MemHSigma (σ + α) (fun k => |û₀ k|) := by
    have : (fun k => |û₀ k|) = fun k => |1 * û₀ k| := by funext k; rw [one_mul]
    unfold MemHSigma
    refine D.hû₀.congr (fun k => ?_)
    rw [sq_abs]
  exact memHSigma_add habs
    (memHSigma_add (memHSigma_smul |χ₀| D.chemOut.henv) D.logOut.henv)

/-- **(i) THE σ-LADDER STEP — PROVEN.**  From the ladder bundle at level `σ`, the
trajectory of `u` has a τ-uniform `H^{σ+α}` envelope: the sum of the heat
envelope `|û₀|`, the chemotaxis propagator output (gain `α`), and the logistic
propagator output (gain `α`).  Domination uses the τ-uniform 3-term decomposition;
membership is `H^{σ+α}` closure under sum/scalar.  No ℓ²-sup, no Gronwall. -/
def trajLadder_step (D : TrajLadderData σ α χ₀ t u û₀ Q Fl) :
    TrajectoryHSigmaEnvelope (σ + α) t (fun τ => cosineCoeffs (u τ)) where
  env := D.ladderEnv
  henv := D.ladderEnv_memHSigma
  hdom := by
    intro τ hτ k
    have hdec := D.hdecomp τ hτ k
    -- heat term: |exp(-τλk)·û₀ k| ≤ |û₀ k|
    have hτ0 : (0:ℝ) ≤ τ := hτ.1
    have hexp1 : Real.exp (-(τ * lam k)) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      have hl := lam_nonneg k
      have : 0 ≤ τ * lam k := mul_nonneg hτ0 hl
      linarith
    have hexp0 : 0 ≤ Real.exp (-(τ * lam k)) := (Real.exp_pos _).le
    have hheat : |Real.exp (-(τ * lam k)) * û₀ k| ≤ |û₀ k| := by
      rw [abs_mul, abs_of_nonneg hexp0]
      calc Real.exp (-(τ * lam k)) * |û₀ k| ≤ 1 * |û₀ k| :=
            mul_le_mul_of_nonneg_right hexp1 (abs_nonneg _)
        _ = |û₀ k| := one_mul _
    -- chemotaxis term: |(-χ₀)·chemCoeff| ≤ |χ₀|·chemEnv
    have hchem : |(-χ₀) * duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (Q τ) k) τ k|
        ≤ |χ₀| * D.chemOut.env k := by
      rw [abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (D.chemOut.hdom τ hτ k) (abs_nonneg _)
    -- logistic term
    have hlog : |duhamelEnergyCoeff 1 Fl τ k| ≤ D.logOut.env k := D.logOut.hdom τ hτ k
    -- assemble: bound the heat term and the (chem + log) tail separately
    set H := Real.exp (-(τ * lam k)) * û₀ k with hH
    set Ch := (-χ₀) * duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (Q τ) k) τ k with hCh
    set Lg := duhamelEnergyCoeff 1 Fl τ k with hLg
    rw [hdec]
    unfold ladderEnv
    have htail : |Ch + Lg| ≤ |χ₀| * D.chemOut.env k + D.logOut.env k :=
      (abs_add_le _ _).trans (add_le_add hchem hlog)
    have hassoc : H + Ch + Lg = H + (Ch + Lg) := by ring
    rw [hassoc]
    exact (abs_add_le _ _).trans (add_le_add hheat htail)

end TrajLadderData

/-! ## (ii)/(iii) — the BASE and the iterate: PRECISE STALL, not faked.

  (i) is delivered UNCONDITIONALLY given the bundle `TrajLadderData σ α χ₀ t u û₀ Q
  Fl` (the bundle's residual fields are named below).  (ii) and (iii) are NOT
  closed here; the precise account follows.

  ── (ii) THE BASE `TrajLadderData σ₀ α χ₀ t u û₀ Q Fl` for small `σ₀` ──

  To instantiate the bundle at the SEED level `σ₀` requires, all upstream of
  classical regularity:

  * `Uσ : TrajectoryHSigmaEnvelope σ₀ t (cosineCoeffs ∘ u)`.  The H⁰ seed
    `conjugatePicardLimit_slice_memHSigma_zero` (LANDED, IntervalMildPosTimeHSigma)
    gives, FOR EACH FIXED τ, `MemHSigma 0 (cosineCoeffs (u τ))` from slice
    continuity.  But a τ-UNIFORM coordinatewise envelope `env k` with
    `∀τ∈[0,t]∀k, |cosineCoeffs (u τ) k| ≤ env k` AND `env ∈ H^{σ₀}` (σ₀>0) is NOT a
    pointwise consequence: the mild data gives a τ-uniform L∞ ball
    (`|u(τ,x)| ≤ M`), and the constant sequence `k ↦ 2M ∉ H^{σ₀}` for σ₀>0 (no
    high-frequency decay).  The seed genuinely needs the FIRST positive-time
    smoothing — i.e. `trajLadder_step` itself with `σ = -α` (or `Ioc 0 t`,
    endpoint invisible to Duhamel), which in turn needs an `H^{-α}` source envelope
    — bottoming out at the SAME residual.

  * `gQ`, `gFl` with their τ-uniform domination.  These are the flux SINE / logistic
    envelopes; their MEMBERSHIP at σ₀ follows from `Uσ` by `fluxSineEnvelope_uniform`
    + the resolver/√λ relay (LANDED algebra), but their DOMINATION over `[0,t]`
    needs `Uσ` (the very base envelope being sought) plus the (1+v)^{-β} and v_x
    factor envelopes — a fixed-point, not a single pass.

  * `hdecomp` — the τ-uniform 3-term Duhamel decomposition.  `IntervalBootstrapDecomp`
    LANDS this decomposition for a FIXED slice's endpoint t (a single
    `cosineCoeffs ut k = …`), carrying `hmap`/`hswap_chem`/`hpt_chem`/`hswap_log`/
    `hpt_log` for that t.  Promoting it to ALL τ∈[0,t] simultaneously (`hdecomp`) is
    the τ-uniform spectral identity — present per-slice, NOT yet as one ∀τ statement
    in Paper2 (grep: no τ-indexed `cosineCoeffs (u τ) = … duhamelEnergyCoeff …`).

  ── (iii) ITERATE (i) FROM (ii) TO σ>1/2 ──

  GIVEN a base bundle at `σ₀` and the ability to RE-BUILD the bundle at `σ₀+α`
  (i.e. produce `gQ`/`gFl`/`hdecomp` at the new level from the OUTPUT envelope
  `trajLadder_step D : TrajectoryHSigmaEnvelope (σ₀+α) t (cosineCoeffs∘u)`), the
  iterate is a finite induction (`n` steps with `n·α ≥ σ_target`).  `trajLadder_step`
  supplies the OUTPUT trajectory envelope `Uσ₊α` directly, so the `Uσ` field of the
  next bundle is discharged.  What is NOT mechanical: re-deriving `gQ`/`gFl`/`hdecomp`
  AT `σ₀+α` from `Uσ₊α` — i.e. a PRODUCER `TrajectoryHSigmaEnvelope σ t (cosineCoeffs∘u)
  → TrajLadderData σ α χ₀ t u û₀ Q Fl`.  Building that producer needs:
    - the flux factor envelopes (cosine env `gW` of `W=u·(1+v)^{-β}`, sine env `gvx`
      of `v_x`) from `Uσ` — `gW` via `fluxCosEnvelope_of_factorEnvelopes` needs an
      `H^σ` envelope of `(1+v)^{-β}` and of `u`; `gvx = √λ·cosineCoeffs(v)` needs
      `v ∈ H^{σ+1}`, i.e. `v_x ∈ H^σ` from `u ∈ H^{σ-1}` (the elliptic relay
      `-v''+v=u` is one-degree smoothing, LANDED as `resolver_memHSigmaPlus2`);
    - the τ-uniform `hdecomp` at `σ+α` (same spectral identity as in (ii)).
  These do NOT need classical regularity (the resolver only RELAYS H^σ; the
  decomposition is a spectral/Fubini computation on the mild fixed point), so the
  iterate is non-circular — but the PRODUCER is not yet wired in Paper2, so (iii)
  is CONDITIONAL on it.

  VERDICT: REAL GAP, NOT CIRCULARITY.  (i) closes UNCONDITIONALLY given the bundle
  (the propagator + envelope algebra + sum closure, all axiom-clean).  (ii)+(iii)
  are CONDITIONAL on a single non-circular producer
  `TrajectoryHSigmaEnvelope σ t (cosineCoeffs∘u) → TrajLadderData …` whose two
  unbuilt pieces are (a) the τ-uniform flux/source factor-envelope domination from
  `Uσ` (the FIXED-POINT/bootstrap, well-founded by the monotone endpoint-uniform
  recurrence `trajLadder_step` realizes), and (b) the τ-uniform 3-term Duhamel
  decomposition `hdecomp` (the τ-indexed lift of the LANDED per-endpoint
  `IntervalBootstrapDecomp` identity).  Both are strictly upstream of
  `localClassicalSolution`/`IsPaper2ClassicalSolution` (never imported here;
  confirmed by `#print axioms`).  The σ-ladder STEP — the most self-contained atom
  — is therefore PROVEN; the BASE/iterate are precisely located, not overclaimed. -/

end ShenWork.Paper2.IntervalTrajectoryEnvelopeClosure

namespace ShenWork.Paper2.IntervalTrajectoryEnvelopeClosure
#print axioms TrajLadderData.chemOut
#print axioms TrajLadderData.logOut
#print axioms TrajLadderData.ladderEnv_memHSigma
#print axioms TrajLadderData.trajLadder_step
end ShenWork.Paper2.IntervalTrajectoryEnvelopeClosure
