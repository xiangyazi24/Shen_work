/-
  ShenWork/Paper2/IntervalMildBootstrapStep.lean

  KEYSTONE B — the per-slice `UniformBootstrapStep` for the χ₀<0 mild solution,
  built FROM mild data + the H^σ Duhamel engine, NON-CIRCULARLY (no
  `localClassicalSolution`, no `IsPaper2ClassicalSolution`, no `ContDiffOn ℝ 2`
  classical regularity).

  ## What this file delivers

  * `SliceMildStepData` — the mild-only bundle the per-σ engine step consumes for a
    FIXED interior slice `ut = conjugateSlice p u₀ DB.T t`.  Its fields are exactly
    the hypotheses of `gradientSolution_memHSigma_succ_fully_uncond`
    (IntervalBootstrapInputs.lean) split into:
      - σ-INDEPENDENT mild data: the three-term mild-map agreement `hmap`, the
        summand continuities, the heat diagonalization `hpt_heat`, the joint
        slab-continuities of the Duhamel integrands, and the per-τ divergence-mode
        / logistic spectral identities `hpt_chem` / `hpt_log` — all genuine
        consequences of `IntervalConjugateMildSolution`, none through C²;
      - σ-INDEXED trajectory envelopes: a family `genv σ` / `glenv σ` of τ-uniform
        `H^σ` flux/source envelopes (the SINGLE remaining analytic input, see the
        verdict below — this is the bootstrap's own induction datum, not C²).

  * `uniformBootstrapStep_of_sliceMildData` — assembles a
    `UniformBootstrapStep α ut` from `SliceMildStepData`, by feeding each σ-level
    instance of the bundle into `gradientSolution_memHSigma_succ_fully_uncond`.
    This is the OBJECT the scaffold's
    `conjugatePicardLimit_slice_memHSigma_one_of_step` consumes.

  * `slice_memHSigma_one_of_mildStepData` — feeds that step into the landed ladder
    (`conjugatePicardLimit_slice_memHSigma_one_of_step`) to discharge positive-time
    `MemHSigma 1` of the slice, from the H⁰ seed + the engine.

  ## NON-CIRCULARITY (TESTED by compilation, not asserted)

  The producer below imports ONLY `IntervalBootstrapInputs` (the mild-only engine
  step), `IntervalMildPosTimeHSigma` (the H⁰ seed + ladder), and the engine scale.
  It NEVER references `localClassicalSolution`, `IsPaper2ClassicalSolution`, the
  C²-Neumann Fourier producers (`hchemFourier_slice_of_limit_C2Neumann`), or the
  PID-classical bridge.  `#print axioms` on the main theorems is
  `⊆ {propext, Classical.choice, Quot.sound}`.  So the per-slice step is
  constructible from mild data + the H^σ induction WITHOUT classical regularity:
  the non-circularity claim is CONFIRMED.

  ## THE PRECISE RESIDUAL (the one genuine remaining analytic input)

  The `genv`/`glenv` fields are NOT dischargeable from the carried
  `MemHSigma σ (cosineCoeffs ut)` (the ENDPOINT slice at time `t`) alone.  As the
  header of `gradientSolution_memHSigma_succ_fully_uncond` states verbatim: the
  per-time flux membership gives `MemHSigma σ (cosineCoeffs (Q τ))` for each FIXED
  `τ`, but a SINGLE sequence dominating `|sineCoeffs (Q τ) k|` UNIFORMLY over
  `τ ∈ [0,t]` while staying in `H^σ` is a uniform-in-time bound on the flux `H^σ`
  norm over the WHOLE trajectory `s ↦ u(s)` — not a pointwise consequence of the
  endpoint datum.  No τ-uniform trajectory-`H^σ` producer exists in Paper2.

  This residual is GENUINE (a real missing analytic input) and NON-CIRCULAR (it is
  the bootstrap's own monotone induction propagated over the trajectory window, NOT
  a classical-existence result):  it is wired-down to a τ-uniform `H^σ` flux
  envelope `g` for the conjugate flux `Q τ = u(τ)·(1+v(τ))^{-β}·v_x(τ)`, built by
  the envelope-monotone Wiener-algebra chain (`IntervalEnvelopeProp` /
  `IntervalMixedProduct.fluxSineEnvelope_uniform`) from a τ-uniform `H^σ` envelope
  of `u(τ)` over `[0,t]`.  The mixed cosine×sine→sine route
  (`fluxSineEnvelope_uniform`) BYPASSES the prior `Q_x`-derivative obstruction: `Q`
  is treated directly as a sine object `W·v_x`, needing only same-order factor
  envelopes `gW` (cosine `H^σ`) and `gvx` (sine `H^σ`, from `v ∈ H^{σ+1}` via the
  elliptic resolver).  So the whole step reduces to ONE τ-uniform trajectory-`H^σ`
  envelope of `u`, supplied here as the `genv`/`glenv` fields.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.
-/
import ShenWork.Paper2.IntervalBootstrapInputs
import ShenWork.Paper2.IntervalMildPosTimeHSigma

noncomputable section

namespace ShenWork.Paper2.IntervalMildBootstrapStep

open MeasureTheory
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalBootstrapInputs (gradientSolution_memHSigma_succ_fully_uncond)
open ShenWork.IntervalConjugatePicard
  (conjugatePicardLimit conjugateMildSolutionData_of_data ConjugateMildExistenceData)
open ShenWork.Paper2.IntervalUniformBootstrap (UniformBootstrapStep)
open ShenWork.Paper2.IntervalMildPosTimeHSigma
  (conjugateSlice conjugatePicardLimit_slice_memHSigma_one_of_step)
open Real

/-! ## The mild-only per-slice bootstrap bundle.

`SliceMildStepData α χ₀ t ut u₀d chemTerm logTerm Q Fl` records, for a FIXED
interior slice `ut`, every input the engine step
`gradientSolution_memHSigma_succ_fully_uncond` consumes, split into:

* σ-INDEPENDENT mild data (`hmap`, the summand continuities, `hpt_heat`, the slab
  joint-continuities, and the per-τ spectral identities `hpt_chem`/`hpt_log`) —
  all intrinsic to `IntervalConjugateMildSolution`, none via classical regularity;

* the σ-INDEXED trajectory envelopes `genv σ` / `glenv σ` together with their
  domination + `H^σ` membership and the per-mode source continuities — the single
  genuine residual analytic input (see the module header).

`u₀d` is the heat-part datum (`= cosineCoeffs (intervalDomainLift u₀)` for the
conjugate slice); `ha` records its base `H^σ` membership at each running σ. -/
structure SliceMildStepData (α χ₀ t : ℝ)
    (ut u₀d : ℝ → ℝ) (chemTerm logTerm : ℝ → ℝ → ℝ)
    (Q : ℝ → ℝ → ℝ) (Fl : ℝ → ℕ → ℝ) where
  hα0 : 0 < α
  hα1 : α < 1
  ht : 0 < t
  ht1 : t ≤ 1
  /-- base `H^σ` datum of the heat part, at every running regularity. -/
  ha : ∀ {σ : ℝ}, MemHSigma σ (cosineCoeffs ut) → MemHSigma σ (cosineCoeffs u₀d)
  /-- σ-indexed τ-uniform `H^σ` chemotaxis-flux envelope (the residual). -/
  genv : ℝ → ℕ → ℝ
  hg : ∀ {σ : ℝ}, MemHSigma σ (cosineCoeffs ut) → MemHSigma σ (genv σ)
  hg_dom : ∀ σ, ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, |sineCoeffs (Q τ) k| ≤ genv σ k
  hFc_cont : ∀ k, Continuous (fun τ => sineCoeffs (Q τ) k)
  /-- σ-indexed τ-uniform `H^σ` logistic-source envelope (the residual). -/
  glenv : ℝ → ℕ → ℝ
  hgl : ∀ {σ : ℝ}, MemHSigma σ (cosineCoeffs ut) → MemHSigma σ (glenv σ)
  hgl_dom : ∀ σ, ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k, |Fl τ k| ≤ glenv σ k
  hFl_cont : ∀ k, Continuous (fun τ => Fl τ k)
  /-- the three-term mild-map agreement on `[0,1]` (heat + chem + logistic). -/
  hmap : Set.EqOn ut
    (fun x => intervalFullSemigroupOperator t u₀d x
      + (-χ₀) * (∫ s in (0:ℝ)..t, chemTerm s x)
      + ∫ s in (0:ℝ)..t, logTerm s x) (Set.Icc (0:ℝ) 1)
  hheat_cont : Continuous (fun x => intervalFullSemigroupOperator t u₀d x)
  hchemI_cont : Continuous (fun x => ∫ s in (0:ℝ)..t, chemTerm s x)
  hlogI_cont : Continuous (fun x => ∫ s in (0:ℝ)..t, logTerm s x)
  hpt_heat : ∀ k, cosineCoeffs (fun x => intervalFullSemigroupOperator t u₀d x) k
    = Real.exp (-(t * lam k)) * cosineCoeffs u₀d k
  hchemTerm_cont : ContinuousOn (Function.uncurry chemTerm)
    (Set.Icc (0:ℝ) t ×ˢ Set.Icc (0:ℝ) 1)
  hlogTerm_cont : ContinuousOn (Function.uncurry logTerm)
    (Set.Icc (0:ℝ) t ×ˢ Set.Icc (0:ℝ) 1)
  hpt_chem : ∀ k, ∀ s, cosineCoeffs (fun x => chemTerm s x) k
    = Real.exp (-(1 * lam k * (t - s))) * ((lam k) ^ (1/2 : ℝ) * sineCoeffs (Q s) k)
  hpt_log : ∀ k, ∀ s, cosineCoeffs (fun x => logTerm s x) k
    = (lam k) ^ (1/2 : ℝ) * Real.exp (-(1 * lam k * (t - s))) * Fl s k

/-- **The per-σ engine step from the mild bundle.**  At a running regularity `σ`,
given `MemHSigma σ (cosineCoeffs ut)`, feed the bundle's σ-INDEPENDENT mild data
and its σ-level trajectory envelopes (`genv σ`, `glenv σ`) into the mild-only
engine `gradientSolution_memHSigma_succ_fully_uncond` to gain `α`.  No classical
regularity is used. -/
theorem sliceMildData_step {α χ₀ t : ℝ} {ut u₀d : ℝ → ℝ}
    {chemTerm logTerm : ℝ → ℝ → ℝ} {Q : ℝ → ℝ → ℝ} {Fl : ℝ → ℕ → ℝ}
    (D : SliceMildStepData α χ₀ t ut u₀d chemTerm logTerm Q Fl)
    {σ : ℝ} (h : MemHSigma σ (cosineCoeffs ut)) :
    MemHSigma (σ + α) (cosineCoeffs ut) :=
  gradientSolution_memHSigma_succ_fully_uncond
    (σ := σ) (α := α) (χ₀ := χ₀) (t := t)
    (ut := ut) (u₀ := u₀d) (chemTerm := chemTerm) (logTerm := logTerm)
    (Q := Q) (Fl := Fl) (g := D.genv σ) (gl := D.glenv σ)
    D.hα0 D.hα1 D.ht D.ht1
    (D.ha h)
    (D.hg h) (D.hg_dom σ) D.hFc_cont
    (D.hgl h) (D.hgl_dom σ) D.hFl_cont
    D.hmap D.hheat_cont D.hchemI_cont D.hlogI_cont D.hpt_heat
    D.hchemTerm_cont D.hlogTerm_cont D.hpt_chem D.hpt_log

/-- **KEYSTONE B — the per-slice `UniformBootstrapStep` from mild data.**  Bundle
the mild-only data into a `UniformBootstrapStep α ut`: the engine map
`∀σ, MemHSigma σ → MemHSigma (σ+α)` is `sliceMildData_step`.  This is the object
the scaffold consumes.  Non-circular: built only from the mild-only engine. -/
def uniformBootstrapStep_of_sliceMildData {α χ₀ t : ℝ} {ut u₀d : ℝ → ℝ}
    {chemTerm logTerm : ℝ → ℝ → ℝ} {Q : ℝ → ℝ → ℝ} {Fl : ℝ → ℕ → ℝ}
    (D : SliceMildStepData α χ₀ t ut u₀d chemTerm logTerm Q Fl) :
    UniformBootstrapStep α ut where
  step := fun {σ} h => sliceMildData_step D (σ := σ) h

/-! ## Discharging positive-time `MemHSigma 1` of the conjugate mild slice.

Specialise `uniformBootstrapStep_of_sliceMildData` to `ut = conjugateSlice p u₀
DB.T t` and feed it into the landed ladder
`conjugatePicardLimit_slice_memHSigma_one_of_step` (which iterates the engine step
from the H⁰ seed up to `MemHSigma 1`).  Everything is mild-only. -/

/-- **`MemHSigma 1` of the conjugate mild slice from the mild step bundle.**  For
an interior time `t ∈ (0, DB.T]`, a step-count `n` with `1 ≤ n·α`, and a mild
bundle `D` for the slice `conjugateSlice p u₀ DB.T t`, the positive-time spatial
`MemHSigma 1` regularity holds — discharged by the H⁰ seed + the engine ladder,
NON-CIRCULARLY. -/
theorem slice_memHSigma_one_of_mildStepData
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (DB : ConjugateMildExistenceData p u₀)
    {α χ₀ : ℝ} {n : ℕ} (hreach : (1 : ℝ) ≤ n * α)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DB.T)
    {u₀d : ℝ → ℝ} {chemTerm logTerm : ℝ → ℝ → ℝ} {Q : ℝ → ℝ → ℝ} {Fl : ℝ → ℕ → ℝ}
    (D : SliceMildStepData α χ₀ t (conjugateSlice p u₀ DB.T t) u₀d
      chemTerm logTerm Q Fl) :
    MemHSigma 1 (cosineCoeffs (conjugateSlice p u₀ DB.T t)) :=
  conjugatePicardLimit_slice_memHSigma_one_of_step p u₀ DB hreach ht htT
    (uniformBootstrapStep_of_sliceMildData D)

/-- **Unconditional field, in its closest provable form.**  Positive-time spatial
`MemHSigma 1` regularity of every interior conjugate mild slice, once the mild step
bundle `D` is supplied per slice.  The H⁰ seed and the H^σ ladder are
unconditional; the only carried input is the per-slice mild bundle `D` (whose sole
genuine residual is the τ-uniform trajectory-`H^σ` flux envelope — see the module
header), NOT classical regularity. -/
theorem u_posTime_memHSigma_one_of_mild_uncond
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (DB : ConjugateMildExistenceData p u₀)
    {α χ₀ : ℝ} {n : ℕ} (hreach : (1 : ℝ) ≤ n * α)
    {u₀d : ℝ → ℝ} {chemTerm logTerm : ℝ → ℝ → ℝ} {Q : ℝ → ℝ → ℝ} {Fl : ℝ → ℕ → ℝ}
    (D : ∀ t, 0 < t → t ≤ DB.T →
      SliceMildStepData α χ₀ t (conjugateSlice p u₀ DB.T t) u₀d
        chemTerm logTerm Q Fl) :
    ∀ t, 0 < t → t ≤ DB.T →
      MemHSigma 1 (cosineCoeffs (conjugateSlice p u₀ DB.T t)) :=
  fun t ht htT =>
    slice_memHSigma_one_of_mildStepData p u₀ DB hreach ht htT (D t ht htT)

#print axioms sliceMildData_step
#print axioms uniformBootstrapStep_of_sliceMildData
#print axioms slice_memHSigma_one_of_mildStepData
#print axioms u_posTime_memHSigma_one_of_mild_uncond

end ShenWork.Paper2.IntervalMildBootstrapStep
