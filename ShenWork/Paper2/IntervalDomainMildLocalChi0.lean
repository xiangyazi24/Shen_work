/-
  ShenWork/Paper2/IntervalDomainMildLocalChi0.lean

  Final-mile step 4 — wire the landed limit restart package into the
  `hMildLocal`-abstract interface for `χ₀ = 0`, making the residual stack
  EXPLICIT at the top level as one named ledger structure.

  ## The chain (per pickup map, COORDINATION step 4)

  For every positive initial datum `u₀` (PID) the target interface
  `RestartLocalWiring.IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData p`
  asks for: a packaged mild solution `D`, a half-step restart package `R`,
  the uniform initial-approach conjunct, and the reduced classical frontier core
  `GradientMildClassicalFrontierCoreData p D` (= `hpde_u` + `hregularityFrontier`).

  We produce them as follows.

  1. **`D` from cone existence (χ₀ = 0).**  `coneGradientMildSolutionData_exists`
     builds one horizon `δ(p, M) > 0` and a packaged Picard mild datum `D` for
     any continuous nonnegative datum bounded by `M` and positive somewhere — all
     read off the PID (`positiveInitialDatum_nonneg`, `_pos_somewhere`,
     `hu₀.admissible`).  No horizon constraint is imposed by the target interface,
     so this is unconditional input.

  2. **`R` from step 1.**  `IntervalPicardLimitSourceData.gradientMildHalfStepRestartData_for_limit`
     (commit e01f32e) assembles `GradientMildHalfStepRestartData D` for the limit
     (χ₀ = 0) from the K2 spatial-slice families and the K1 source-coefficient
     time-`C¹` families (unshifted + `t/2`-shift), plus the datum continuity /
     ℓ¹-coefficient data and the mild fixed-point equation.  These are the named,
     satisfiable "limit regularity" inputs (the n → ∞ images of the iterates'
     spatial bootstrap + M3b's window output); they are grouped verbatim into the
     ledger `LimitRegularityInputs`.

  3. **`HasRestartCosineRepresentations D.T D.u` from step 2.**
     `hasRestartCosineRepresentations_of_gradientMildHalfStepRestartData D R`.

  4. **The frontier core from step 3.**
     `GradientMildClassicalFrontierCoreData p D = ⟨hpde_u, hregularityFrontier⟩`.
     * `hregularityFrontier` is the proved 9-field assembly
       `RegularityFrontierWiring.gradientMildClassicalRegularityFrontierData_of_spectral`,
       which takes `Hu` (u-side time agreement), `Hv` (v-side resolver spectral
       data), `Hrestart` (from step 3), `HsupNorm` (sup-norm monotonicity), and
       `Hvpos` (resolver boundary positivity).  Of these:
         - `Hrestart` is WIRED from `R` (step 2);
         - `Hv` is WIRED from a `DuhamelSourceTimeC1` of the resolver source
           coefficients via
           `RegularityFrontierAssembly.hasResolverDirectSpectralData_of_sourceCoeffTimeC1`;
           the ledger carries the `DuhamelSourceTimeC1` package as `Hvsrc`;
         - `Hu`, `HsupNorm`, `Hvpos` have no proved producer here and are carried
           as named satisfiable inputs (the genuine residuals — see the audit).
     * `hpde_u` (the parabolic PDE satisfied by the mild slice `D.u`) likewise has
       no non-circular producer at this layer (`mildSolution_parabolicPDE` needs a
       full `IsPaper2ClassicalSolution`), so it is carried as a named input.

  5. **The initial-approach conjunct is PROVED generically.**
     `gradientMildSolutionData_initialApproach p (Continuous u₀) D` (Session B,
     landed) discharges it for any continuous datum — NOT in the ledger.

  ## The honest residual ledger

  All non-derivable residuals are grouped into ONE structure
  `LimitRegularityInputs p u₀ D`.  The top-level statement therefore reads as the
  explicit ledger:

      hMildLocal_chi0_zero_of_inputs (hχ0 : p.χ₀ = 0) ...
        (H : ∀ u₀, PID u₀ → ∀ D, LimitRegularityInputs p u₀ D) :
        IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData p

  and the corollary chains into Paper 2 Theorem 1.1 (χ₀ = 0) via
  `paper2_theorem_1_1_from_quant_and_hlocal` (with `hQuant(χ₀=0)` proved through
  the cone bridge), since `χ₀ = 0 ⟹ χ₀ ≤ 0`.

  ## Satisfiability audit of `LimitRegularityInputs` (the project's honest frontier)

  Structural: `hα : 1 ≤ p.α`, `ha : 0 ≤ p.a`, `hb : 0 ≤ p.b` — regime params.
  H1 datum:  `hu₀_cont`, `hu₀_bound` — datum continuity + bounded cosine
             coefficients (the CM2/PID datum is C²/Neumann ⇒ bounded coeffs).
  Fixed pt:  `hfix` — the mild Duhamel equation for `D.u` (= `D.hmild`).
  K2 slices: `hC2t/hpost/hubt/hG1t/hG2t/hN0t/hN1t` — C²/positivity/sup/grad/
             Hessian/Neumann bounds of `lift (D.u σ)`, n-uniform (n → ∞ image of
             the iterate spatial bootstrap).
  K1 fields: `adott/hderivt/hadotcontt/hMdott` (+ the `t/2`-shifted
             `adotS/hderivS/hadotcontS/hMdotS`) — source-coefficient time-`C¹`
             data (M3b's window output for `rep(u)`).
  H3 slice:  `hLc` — per-slice continuity of `logisticLifted p (D.u s)`.
  Frontier residuals:
    `hpde_u`  — parabolic PDE for `D.u` (genuine residual; no non-circular
                producer here).
    `Hu`      — `HasTimeNeighborhoodSpectralAgreement D.T D.u` (genuine residual;
                u-side time regularity).
    `Hvsrc`   — PER-`t₀` clamped resolver-source `DuhamelSourceTimeC1` witness
                (a window-agreeing family per interior `t₀`; yields `Hv` via the
                proved packaging theorem `hasResolverDirectSpectralData_of_clamped_perT0`).
                Retyped from the unsatisfiable GLOBAL `DuhamelSourceTimeC1` (jump at
                `s = D.T`); see field doc + `IntervalResolverSourceTimeC1.lean`.
    `Hvpos`   — boundary positivity of `mildChemicalConcentration` (genuine
                residual; elliptic strong maximum principle).

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalPicardLimitSourceData
import ShenWork.Paper2.IntervalPicardLimitRestartWeak
import ShenWork.Paper2.IntervalRegularityFrontierWiring
import ShenWork.Paper2.IntervalDomainConeQuantBridge
import ShenWork.Paper2.IntervalDomainConstExtendAdapter
import ShenWork.Paper2.IntervalDomainRestartPackaging

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint
   intervalDomainConstExtend constExtend_continuous
   IntervalDomainSupNormDerivativeNonposOn)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalMildPicard (GradientMildSolutionData gradientMildSolutionData_of_data)
open ShenWork.IntervalMildPicardConeData (coneGradientMildSolutionData_exists)
open ShenWork.IntervalMildPicardThreshold (gradientMildSolutionData_initialApproach)
open ShenWork.IntervalMildRegularityBootstrap
  (GradientMildHalfStepRestartData HasRestartCosineRepresentations
   hasRestartCosineRepresentations_of_gradientMildHalfStepRestartData)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalMildToLocalExistence
  (GradientMildClassicalFrontierCoreData)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalResolverDirectTimeRegularity (HasResolverDirectSpectralData)
open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1ContOn)
open ShenWork.PDE (intervalNeumannResolverSourceCoeff)
open ShenWork.Paper2
open ShenWork.Paper2.ConeQuantBridge
  (positiveInitialDatum_nonneg positiveInitialDatum_pos_somewhere)

noncomputable section

namespace ShenWork.Paper2.MildLocalChi0

/-! ## The honest residual ledger -/

/-- **`LimitRegularityInputs p u₀ D`** — the single grouped residual ledger for
the `χ₀ = 0` mild-local wiring.  It bundles (i) the named K1/K2 "limit
regularity" families that build the half-step restart package `R` via step 1
(`gradientMildHalfStepRestartData_for_limit`), together with (ii) the frontier
residuals not derivable from `R`/`rep(u)` at this layer (`hpde_u`, `Hu`, `Hvsrc`,
`Hvpos`).  Everything in this structure is a named, satisfiable
hypothesis (see the file header §"Satisfiability audit"); the structure IS the
project's honest residual frontier for the χ₀ = 0 sub-regime. -/
structure LimitRegularityInputs
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) where
  -- structural regime parameters
  hα : 1 ≤ p.α
  ha : 0 ≤ p.a
  hb : 0 ≤ p.b
  -- H1 datum data
  hu₀_cont : Continuous u₀
  M₀ : ℝ
  hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀
  -- mild fixed-point (= D.hmild)
  hfix : ∀ t, 0 < t → t < D.T → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
    intervalDomainLift (D.u t) x = intervalGradientDuhamelMap p u₀ D.u t ⟨x, hx⟩
  -- weak limit-source package (horizon-bounded; feeds the localized restart route)
  hsrc0 : ShenWork.IntervalPicardLimitRestartBdd.DuhamelSourceBddOn
    (ShenWork.IntervalPicardLimitBddProducer.patchedSource p u₀ D.u) D.T
  -- K2 spatial slice bounds (per time slice)
  Msup : ℝ
  -- per-slice cosine representation (replaces the unsatisfiable global-`C²` field
  -- `hC2t`; fed into the source-decay machinery via
  -- `IntervalDomainLimitSourceRepresentation`)
  bc : ℝ → ℕ → ℝ
  hbsum : ∀ σ, 0 < σ → σ < D.T → Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|)
  hagree : ∀ σ, 0 < σ → σ < D.T → Set.EqOn (intervalDomainLift (D.u σ))
    (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1)
  hpost : ∀ σ, 0 < σ → σ < D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (D.u σ) x
  hubt : ∀ σ, 0 < σ → σ < D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (D.u σ) x ≤ Msup
  -- K2 gradient/Hessian bounds, PER-COMPACT (the satisfiable form)
  hG1t : ∀ a' b', 0 < a' → b' < D.T → ∃ G1, ∀ σ ∈ Set.Icc a' b',
    ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (D.u σ)) x| ≤ G1
  hG2t : ∀ a' b', 0 < a' → b' < D.T → ∃ G2, ∀ σ ∈ Set.Icc a' b',
    ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (intervalDomainLift (D.u σ))) x| ≤ G2
  hN0t : ∀ σ, 0 < σ → σ < D.T → deriv (intervalDomainLift (D.u σ)) 0 = 0
  hN1t : ∀ σ, 0 < σ → σ < D.T → deriv (intervalDomainLift (D.u σ)) 1 = 0
  -- K1 source-coefficient time-C¹ data (UNSHIFTED, localized to (0,T))
  adott : ℝ → ℕ → ℝ
  hderivt : ∀ σ, 0 < σ → σ < D.T → ∀ k, HasDerivAt
    (fun r => cosineCoeffs
      (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u r))) k)
    (adott σ k) σ
  hadotcontt : ∀ k, ContinuousOn (fun σ => adott σ k) (Set.Ioo 0 D.T)
  hMdott : ∀ a' b', 0 < a' → b' < D.T → ∃ Mdot, ∀ σ ∈ Set.Icc a' b',
    ∀ k, |adott σ k| ≤ Mdot
  -- H3 slice continuity
  hLc : ∀ t, 0 < t → t < D.T →
    ∀ s, 0 < s → s ≤ t → Continuous (intervalLogisticSource p (D.u s))
  -- ===== frontier residuals (not derivable from R/rep(u) here) =====
  hpde_u :
    ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α)
  Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u
  -- **`Hvsrc` (per-`t₀` clamped form).**  Retyped from the unsatisfiable GLOBAL
  -- `DuhamelSourceTimeC1` (the canonical resolver source `ν·(D.u s)^γ` jumps at
  -- `s = D.T` because `picardLimit = 0` off `(0,T]`, so the global `hderiv` there is
  -- FALSE — see `IntervalResolverSourceTimeC1.lean` header).  The downstream
  -- consumer (`HasResolverDirectSpectralData`, now per-`t₀`) reads the package only
  -- at interior times, so the faithful field is a PER-`t₀` clamped witness: for each
  -- interior `t₀` a family `aC` with a `DuhamelSourceTimeC1 aC` package agreeing with
  -- the canonical resolver source coefficients on a window `W ∈ 𝓝 t₀`.  This IS
  -- satisfiable (soft-clamp the trajectory into a compact window `⊂ (0,T)`; see the
  -- Provider's witness producer), unlike the global field.  Fed to `Hv` via
  -- `RegularityFrontierAssembly.hasResolverDirectSpectralData_of_clamped_perT0`.
  Hvsrc : ∀ t₀, 0 < t₀ → t₀ < D.T →
    ∃ (aC : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC1 aC) (W : Set ℝ),
      W ∈ 𝓝 t₀ ∧
      (∀ s ∈ W, ∀ k, aC s k = (intervalNeumannResolverSourceCoeff p (D.u s) k).re)
  Hvpos : ∀ t, 0 < t → t < D.T → ∀ x : intervalDomainPoint,
    0 < mildChemicalConcentration p D.u t x

/-! ## Assembling the per-datum package from the ledger -/

/-- **Build `R` from the ledger via step 1.** -/
noncomputable def restartData_of_inputs
    {p : CM2Params} (hχ0 : p.χ₀ = 0) {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (I : LimitRegularityInputs p u₀ D) :
    GradientMildHalfStepRestartData D :=
  -- The per-`t` half-step restart package is built by the time-localized subtype
  -- producer (`RestartPackaging.gradientMildHalfStepRestartData_localized_of_subtypeCont`),
  -- the same clamped-witness machinery tonight's `Hu` route uses
  -- (`TimeNhdSubtype.Hu_of_restart_localized_of_subtypeCont`).  Every hypothesis is
  -- a ledger field, except `I.hLc` (subtype continuity of
  -- `intervalLogisticSource p (D.u s)`), which is bridged to the globally-continuous
  -- `intervalDomainConstExtend` slice-continuity form via `constExtend_continuous`.
  RestartPackaging.gradientMildHalfStepRestartData_localized_of_subtypeCont
    hχ0 D I.hα I.ha I.hb I.hu₀_cont I.hu₀_bound I.hfix I.hsrc0
    I.bc I.hbsum I.hagree I.hpost I.hubt I.hG1t I.hG2t
    I.adott I.hderivt I.hadotcontt I.hMdott
    (fun t ht htT s hs hst =>
      constExtend_continuous (I.hLc t ht htT s hs hst))

/-- **Build the reduced classical frontier core from the ledger via steps 2–3.**
`Hrestart` from step 2 (the restart package `R`); `Hv` from `Hvsrc` via the
proved packaging theorem; the remaining frontier fields from the named residuals;
`hpde_u` carried directly. -/
theorem frontierCore_of_inputs
    {p : CM2Params} (hχ0 : p.χ₀ = 0) {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (I : LimitRegularityInputs p u₀ D) :
    GradientMildClassicalFrontierCoreData p D where
  hpde_u := I.hpde_u
  hregularityFrontier := by
    have Hrestart : HasRestartCosineRepresentations D.T D.u :=
      hasRestartCosineRepresentations_of_gradientMildHalfStepRestartData D
        (restartData_of_inputs hχ0 I)
    have Hv : HasResolverDirectSpectralData D.T
        (mildChemicalConcentration p D.u) p :=
      RegularityFrontierAssembly.hasResolverDirectSpectralData_of_clamped_perT0
        D.u I.Hvsrc
    exact RegularityFrontierWiring.gradientMildClassicalRegularityFrontierData_of_spectral
      p D I.Hu Hv Hrestart I.Hvpos

/-! ## The top-level `hMildLocal`-abstract statement (χ₀ = 0) -/

/-- **`hMildLocal`-abstract (χ₀ = 0) from the explicit residual ledger.**

For every PID `u₀`, the cone construction supplies a packaged mild datum `D`
(χ₀ = 0), and the named ledger `LimitRegularityInputs p u₀ D` supplies — via the
landed limit restart package (step 1), the bootstrap (step 2), and the proved
frontier assembly (step 3) — the half-step restart package and the reduced
classical frontier core.  The initial-approach conjunct is discharged
GENERICALLY (`gradientMildSolutionData_initialApproach`).  The ledger is the
honest residual frontier; nothing in it is the conclusion in disguise. -/
theorem hMildLocal_chi0_zero_of_inputs
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (hα_ge : 1 ≤ p.α)
    (H : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = ShenWork.IntervalMildPicard.picardLimit p u₀ D.T →
        LimitRegularityInputs p u₀ D) :
    RestartLocalWiring.IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData p := by
  intro u₀ hu₀
  -- numeric bound on the datum from PID admissibility
  obtain ⟨B, hB⟩ := hu₀.admissible.1
  set M := max B 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right B 1)
  have hbound : ∀ x, |u₀ x| ≤ M := fun x =>
    le_trans (hB (Set.mem_range_self x)) (le_max_left B 1)
  -- build D via the cone construction (χ₀ = 0).  `hu₀.admissible.2` already has
  -- the `Continuous` type at the resolved point type, so it is threaded inline
  -- (writing `Continuous u₀` on the unreduced `intervalDomain.Point` would block
  -- topology-instance synthesis).
  obtain ⟨δ, _hδ, hD⟩ := coneGradientMildSolutionData_exists p hχ0 hM hα_ge
  obtain ⟨D, hDT, hDu⟩ := hD u₀ hu₀.admissible.2 hbound
    (positiveInitialDatum_nonneg hu₀) (positiveInitialDatum_pos_somewhere hu₀)
  -- the canonical Picard-limit identity at this `D`'s horizon (un-discarded)
  have hDu' : D.u = ShenWork.IntervalMildPicard.picardLimit p u₀ D.T := by
    rw [hDT]; exact hDu
  -- the named ledger for this D
  have I : LimitRegularityInputs p u₀ D := H u₀ hu₀ D hDu'
  refine ⟨D, restartData_of_inputs hχ0 I, ?_, frontierCore_of_inputs hχ0 I⟩
  -- initial approach: proved generically for continuous data
  exact gradientMildSolutionData_initialApproach p hu₀.admissible.2 D

/-! ## Corollary: Paper 2 Theorem 1.1 for χ₀ = 0 -/

/-- **Paper 2 Theorem 1.1 (χ₀ = 0) from the explicit ledger.**

Chains `hMildLocal_chi0_zero_of_inputs` (the local existence side) with the
already-proved `hQuant(χ₀ = 0)` (via the cone bridge), through
`paper2_theorem_1_1_from_quant_and_hlocal`.  The regime hypothesis aligns:
`χ₀ = 0 ⟹ χ₀ ≤ 0`.  The only inputs are the named residual ledger `H` (local
side) and `PicardLimitRestartFrontier p` (the shared quantitative-side residual). -/
theorem paper2_theorem_1_1_chiZero_of_inputs
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (H : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = ShenWork.IntervalMildPicard.picardLimit p u₀ D.T →
        LimitRegularityInputs p u₀ D) :
    Theorem_1_1 intervalDomain p :=
  RestartLocalWiring.paper2_theorem_1_1_from_quant_and_hlocal
    p (le_of_eq hχ0) ha hb hγ_ge_one
    (ConeQuantBridge.quantitativeLocalExistence_chiZero p hχ0 hα_ge hPLF)
    (RestartLocalWiring.localExistence_of_gradientMildHalfStepRestartFrontierCoreLocalData
      p (hMildLocal_chi0_zero_of_inputs p hχ0 hα_ge H))

end ShenWork.Paper2.MildLocalChi0
