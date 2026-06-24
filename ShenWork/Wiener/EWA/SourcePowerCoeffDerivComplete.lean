/-
  ShenWork/Wiener/EWA/SourcePowerCoeffDerivComplete.lean

  **χ₀<0 — completing the power-source `ν·u^γ` time-`C¹` quadruple and wiring it to
  the resolver direct spectral datum `Hv`, past the same `whnf`/`isDefEq` wall that
  K1(i) cracked.**

  The banked file `SourcePowerCoeffDeriv.lean` proved K1(i)
  (`realSlice_powerCoeff_hasDerivAt`, with `adotPow` and the opaque engine lemma
  `hasDerivAt_powerCoeff_of_inputs`).  This file completes the quadruple:

  * **K1(ii)** `powerCoeff_continuousOn_of_inputs` — continuity in `σ` of the per-mode
    derivative coefficient `σ ↦ adotPow p v vdotL σ k`, on a closed window, over the
    OPAQUE abstract `v`.
  * **K1(iii)** `powerCoeff_bound_of_inputs` — a window-uniform bound on `|adotPow …|`,
    over the OPAQUE abstract `v`.

  and then assembles the quadruple into the EXACT `adotP/Mdot/hderivP/hadotcontP/hMdotP`
  shapes carried by `realSlice_resolverSpectralData_of_windowedPowerSource`
  (`SourceResolverTimeC1Discharge.lean`), producing

      realSlice_resolverSpectralData_full :
        HasResolverDirectSpectralData T (mildChemicalConcentration p (realSlice u_star)) p

  — the `Hv` field of `realSlice_reducedCore`.

  ## The structural wall and how this file blocks it (same as K1(i))

  The EWA weighted-Wiener point evaluation `realSlice u_star` never `whnf`-terminates,
  so the cosine-coefficient continuity/bound engines blow up if they ever try to reduce
  it.  As in the banked K1(i):

  1. `attribute [local irreducible] realSlice` forbids residual unfolding.
  2. K1(ii)/K1(iii) are proved over an ABSTRACT `v : ℝ → intervalDomainPoint → ℝ` with
     every analytic input (joint slab continuity of the chain-rule integrand, per-slice
     continuity, positivity, the per-slice time-derivative) supplied as an explicit
     hypothesis ABOUT `v`; the engines never see the EWA structure.  `v` is instantiated
     to `realSlice u_star` only at the very end.
  3. `change`/`show` pin every goal so elaboration matches syntactically.
  4. The power chain rule reuses `hasDerivAt_powerLiftSlice` (positivity branch,
     exponent explicit) from the banked file.

  The K1(ii)/K1(iii) proofs MIRROR the canonical-Picard power-source spine
  `ShenWork.Paper2.ResolverPowerK1` (`IntervalResolverPowerK1.lean`): K1(ii) via the
  dominated-continuity route
  `intervalIntegral.continuousAt_of_dominated_interval` + `cosineCoeffs_eq_factor_mul_integral`,
  K1(iii) via `cosineCoeffs_abs_le_of_continuous_bounded` over the compact window — the
  only change being that the joint slab continuity is an INPUT about `v` rather than a
  fact extracted from the `LocalRestartWeak` engine.

  ## What `realSlice_resolverSpectralData_full` genuinely carries

  `realSlice_classicalRegularity` carries NO time-differentiability atom for the
  `u`-slice source.  So the engine inputs threaded here — the per-slice power-source
  time-derivative `hslice`, the per-slice positivity `hposW`, per-slice continuity
  `hf_cont`, and the joint slab continuity `hslabcont` of the chain-rule integrand
  `ν·γ·(lift (v σ))^{γ−1}·vdotL σ` — together with the cosine-rep / positivity /
  quadratic-decay inputs (`bc`/`hbsum`/`hagree`/`hpos`/`C`/`hC`/`hdecay`/`ha0`) are the
  genuine χ₀<0 resolver-source TIME-`C¹` frontier, threaded — not asserted.  These are
  exactly the data the canonical-Picard side discharges from its `LocalRestartWeak`
  subtype-continuity engine; for the abstract EWA fixed-point slice they are the precise
  remaining frontier.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourcePowerCoeffDeriv
import ShenWork.Wiener.EWA.SourceResolverTimeC1Discharge

open Set Filter Topology MeasureTheory
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalResolverDirectTimeRegularity (HasResolverDirectSpectralData)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_eq_factor_mul_integral cosineCoeffs_abs_le_of_continuous_bounded)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

-- BLOCK the whnf/isDefEq wall: `realSlice` must never unfold inside this section.
attribute [local irreducible] realSlice

/-! ### The power-source chain-rule integrand slice (opaque `v`).

`gPow p v vdotL σ x = ν·γ·(lift (v σ) x)^{γ−1} · vdotL σ x` is the spatial slice
whose cosine coefficients ARE the K1 derivative coefficients
`adotPow p v vdotL σ k = cosineCoeffs (gPow p v vdotL σ) k`. -/
def gPow (p : CM2Params) (v : ℝ → intervalDomainPoint → ℝ)
    (vdotL : ℝ → ℝ → ℝ) (σ x : ℝ) : ℝ :=
  p.ν * p.γ * (intervalDomainLift (v σ) x) ^ (p.γ - 1) * vdotL σ x

/-- `adotPow` is the cosine coefficient family of `gPow` (definitional).  Proved
BEFORE `gPow` is made irreducible, so the `rfl` still fires. -/
theorem adotPow_eq_cosineCoeffs_gPow {p : CM2Params}
    {v : ℝ → intervalDomainPoint → ℝ} {vdotL : ℝ → ℝ → ℝ} (σ : ℝ) (k : ℕ) :
    adotPow p v vdotL σ k = cosineCoeffs (gPow p v vdotL σ) k := rfl

/-- Uncurried unfold of `gPow` (definitional).  Proved BEFORE `gPow` is made
irreducible; used at the K1(i) feed to convert the banked engine's explicit-lambda
chain-rule field into `gPow` form (and back). -/
theorem gPow_uncurry_eq {p : CM2Params}
    {v : ℝ → intervalDomainPoint → ℝ} {vdotL : ℝ → ℝ → ℝ} :
    Function.uncurry (gPow p v vdotL)
      = Function.uncurry (fun s x => p.ν * p.γ
          * (intervalDomainLift (v s) x) ^ (p.γ - 1) * vdotL s x) := rfl

-- BLOCK the whnf/isDefEq wall: `gPow` (the rpow-bearing chain-rule integrand) must
-- never unfold inside the continuity/bound engines; they consume it only through the
-- abstract joint-continuity hypothesis `hslabcont`.
attribute [local irreducible] gPow

/-! ### K1(ii) over the OPAQUE `v` — continuity of `σ ↦ adotPow … σ k`.

From the joint continuity of the chain-rule integrand `gPow` on a window
`I ×ˢ [0,1]`, the dominated-continuity route gives `ContinuousOn (adotPow … · k) I`.
This is the `gPow`/opaque-`v` clone of the canonical
`ShenWork.Paper2.ResolverPowerK1.powerK1_quadruple_of_subtypeCont`'s `hcont` leg. -/
theorem powerCoeff_continuousOn_of_inputs {p : CM2Params}
    {v : ℝ → intervalDomainPoint → ℝ} {vdotL : ℝ → ℝ → ℝ} {a' b' : ℝ} (k : ℕ)
    (hslabcont : ContinuousOn (Function.uncurry (gPow p v vdotL))
      (Set.Icc a' b' ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun σ => adotPow p v vdotL σ k) (Set.Icc a' b') := by
  intro σ₀ hσ₀
  set I : Set ℝ := Set.Icc a' b' with hIdef
  -- weighted integrand `F σ x = cos(kπx)·gPow σ x`.
  set F : ℝ → ℝ → ℝ := fun σ x =>
    Real.cos ((k : ℝ) * Real.pi * x) * gPow p v vdotL σ x with hFdef
  have hcos_cont : Continuous (fun x : ℝ => Real.cos ((k : ℝ) * Real.pi * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id')
  have hFcont : ContinuousOn (Function.uncurry F) (I ×ˢ Set.Icc (0 : ℝ) 1) :=
    (hcos_cont.comp continuous_snd).continuousOn.mul hslabcont
  have hKcompact : IsCompact (I ×ˢ Set.Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hKcompact.bddAbove_image hFcont.norm
  set B' := max B 0 with hB'def
  have hB'nn : 0 ≤ B' := le_max_right _ _
  have hFbd : ∀ σ ∈ I, ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖F σ x‖ ≤ B' := by
    intro σ hσ x hx
    have : ‖Function.uncurry F (σ, x)‖ ≤ B :=
      hB (Set.mem_image_of_mem _ (Set.mem_prod.mpr ⟨hσ, hx⟩))
    exact le_trans this (le_max_left _ _)
  have hsec_cont : ∀ σ ∈ I, ContinuousOn (F σ) (Set.Icc (0 : ℝ) 1) := by
    intro σ hσ
    have hsslice : ContinuousOn (gPow p v vdotL σ) (Set.Icc (0 : ℝ) 1) :=
      hslabcont.comp (continuousOn_const.prodMk continuousOn_id)
        (fun x hx => Set.mem_prod.mpr ⟨hσ, hx⟩)
    exact hcos_cont.continuousOn.mul hsslice
  have hInhds : I ∈ 𝓝[I] σ₀ := self_mem_nhdsWithin
  -- continuity of `σ ↦ ∫₀¹ F σ x dx` within `I` at `σ₀` via dominated convergence.
  have hint_cont : ContinuousWithinAt (fun σ => ∫ x in (0 : ℝ)..1, F σ x) I σ₀ := by
    refine intervalIntegral.continuousWithinAt_of_dominated_interval
      (bound := fun _ => B') ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [hInhds] with σ hσ
      have : ContinuousOn (F σ) (Set.uIcc (0 : ℝ) 1) := by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact hsec_cont σ hσ
      exact (this.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · filter_upwards [hInhds] with σ hσ
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      exact hFbd σ hσ x ⟨hx.1.le, hx.2⟩
    · refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      have := (hFcont.comp (continuousOn_id.prodMk continuousOn_const)
        (fun σ hσ => Set.mem_prod.mpr ⟨hσ, hxIcc⟩)).continuousWithinAt hσ₀
      simpa [Function.uncurry] using this
  -- transport through the `cosineCoeffs = factor · integral` formula.
  have hadeq : ∀ σ, adotPow p v vdotL σ k =
      (if k = 0 then (1 : ℝ) else 2) * ∫ x in (0 : ℝ)..1, F σ x := by
    intro σ
    rw [adotPow_eq_cosineCoeffs_gPow, cosineCoeffs_eq_factor_mul_integral]
  have hfun : (fun σ => adotPow p v vdotL σ k)
      = (fun σ => (if k = 0 then (1 : ℝ) else 2) * ∫ x in (0 : ℝ)..1, F σ x) :=
    funext hadeq
  rw [hfun]
  exact hint_cont.const_mul _

/-! ### K1(iii) over the OPAQUE `v` — window-uniform bound.

From the joint continuity of `gPow` on the compact window `[a',b'] ×ˢ [0,1]`, a
uniform bound on the integrand yields a uniform bound on every cosine coefficient via
`cosineCoeffs_abs_le_of_continuous_bounded`.  The `gPow`/opaque-`v` clone of the
canonical `hbound` leg. -/
theorem powerCoeff_bound_of_inputs {p : CM2Params}
    {v : ℝ → intervalDomainPoint → ℝ} {vdotL : ℝ → ℝ → ℝ} {a' b' : ℝ}
    (hslabcont : ContinuousOn (Function.uncurry (gPow p v vdotL))
      (Set.Icc a' b' ×ˢ Set.Icc (0 : ℝ) 1)) :
    ∃ Mdot, ∀ σ ∈ Set.Icc a' b', ∀ k, |adotPow p v vdotL σ k| ≤ Mdot := by
  set K := Set.Icc a' b' ×ˢ Set.Icc (0 : ℝ) 1 with hKdef
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hKcompact.bddAbove_image hslabcont.norm
  set B' := max B 0 with hB'def
  have hB'nn : 0 ≤ B' := le_max_right _ _
  have hbd : ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |gPow p v vdotL σ x| ≤ B' := by
    intro σ hσ x hx
    have hmem : (σ, x) ∈ K := Set.mem_prod.mpr ⟨hσ, hx⟩
    have : ‖Function.uncurry (gPow p v vdotL) (σ, x)‖ ≤ B :=
      hB (Set.mem_image_of_mem _ hmem)
    simp only [Function.uncurry, Real.norm_eq_abs] at this
    exact le_trans this (le_max_left _ _)
  refine ⟨2 * B', fun σ hσ k => ?_⟩
  have hsec : ContinuousOn (gPow p v vdotL σ) (Set.Icc (0 : ℝ) 1) := by
    have hmaps : Set.MapsTo (fun x : ℝ => ((σ, x) : ℝ × ℝ)) (Set.Icc (0 : ℝ) 1) K :=
      fun x hx => Set.mem_prod.mpr ⟨hσ, hx⟩
    exact hslabcont.comp (continuousOn_const.prodMk continuousOn_id) hmaps
  rw [adotPow_eq_cosineCoeffs_gPow]
  exact cosineCoeffs_abs_le_of_continuous_bounded hsec hB'nn (fun x hx => hbd σ hσ x hx) k

/-! ### `Hv` for the EWA slice, fully wired from the engine inputs.

`realSlice_resolverSpectralData_full` discharges the power-source K1 quadruple
(`adotP/Mdot/hderivP/hadotcontP/hMdotP` carried by
`realSlice_resolverSpectralData_of_windowedPowerSource`) from the per-`t₀` windowed
engine inputs about `realSlice u_star`:

* `hf_cont`/`hslice`/`hposK1`/`hderivcont` — the four K1(i) engine inputs (eventual
  per-slice continuity, per-slice time-derivative on the ball, per-slice positivity,
  joint slab continuity of the chain-rule integrand), feeding the banked
  `realSlice_powerCoeff_hasDerivAt` for `hderivP`;
* `hslabcont` — the joint continuity of the chain-rule integrand `gPow` on each clamp
  window, feeding `powerCoeff_continuousOn_of_inputs` (K1(ii)) and
  `powerCoeff_bound_of_inputs` (K1(iii)).

Setting `adotP t₀ σ n := adotPow p (realSlice u_star) vdotL σ n` (t₀-independent), the
quadruple is assembled and chained into
`realSlice_resolverSpectralData_of_windowedPowerSource`, producing the `Hv` datum

    HasResolverDirectSpectralData T (mildChemicalConcentration p (realSlice u_star)) p

with no residual quadruple left open.  The conclusion is `Prop`-valued, so this is a
`theorem`. -/
theorem realSlice_resolverSpectralData_full
    (p : CM2Params) (u_star : EWA T 1)
    (vdotL : ℝ → ℝ → ℝ)
    -- cosine representation + per-slice positivity (for the clamped producer).
    (bc : ℝ → ℝ → ℕ → ℝ)
    (hbsum : ∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc t₀ σ n|))
    (hagree : ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      Set.EqOn (intervalDomainLift (realSlice u_star σ))
        (fun x => ∑' n, bc t₀ σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (realSlice u_star σ) x)
    -- power-source quadratic decay (for the clamped producer).
    (C : ℝ → ℝ) (hC : ∀ t₀, 0 ≤ C t₀)
    (hdecay : ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4), ∀ k : ℕ, 1 ≤ k →
        |cosineCoeffs (fun x => p.ν * intervalDomainLift (realSlice u_star σ) x ^ p.γ) k|
          ≤ C t₀ / ((k : ℝ) * Real.pi) ^ 2)
    (ha0 : ∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      |cosineCoeffs (fun x => p.ν * intervalDomainLift (realSlice u_star σ) x ^ p.γ) 0|
        ≤ C t₀)
    -- K1(i) engine inputs, per interior σ (for the per-slice `HasDerivAt`).
    (hK1 : ∀ σ ∈ Set.Ioo (0 : ℝ) T, ∃ δ > 0,
      (∀ᶠ s in 𝓝 σ,
          ContinuousOn
            (fun x => p.ν * (intervalDomainLift (realSlice u_star s) x) ^ p.γ)
            (Set.Icc (0 : ℝ) 1))
        ∧ (∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball σ δ,
            HasDerivAt (fun r => intervalDomainLift (realSlice u_star r) x)
              (vdotL s x) s)
        ∧ (∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball σ δ,
            0 < intervalDomainLift (realSlice u_star s) x)
        ∧ ContinuousOn (Function.uncurry (gPow p (realSlice u_star) vdotL))
            (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1))
    -- joint continuity of the chain-rule integrand on each clamp window (K1(ii)/(iii)).
    (hslabcont : ∀ t₀, 0 < t₀ → t₀ < T →
      ContinuousOn (Function.uncurry (gPow p (realSlice u_star) vdotL))
        (Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4) ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasResolverDirectSpectralData T
      (mildChemicalConcentration p (realSlice u_star)) p := by
  classical
  -- K1(i): per-mode HasDerivAt of the coefficient family, from the banked engine.
  -- (`gPow` is definitionally the explicit chain-rule lambda the banked engine wants.)
  have hδ : ∀ σ ∈ Set.Ioo (0 : ℝ) T, ∃ δ > 0,
      (∀ᶠ s in 𝓝 σ,
          ContinuousOn
            (fun x => p.ν * (intervalDomainLift (realSlice u_star s) x) ^ p.γ)
            (Set.Icc (0 : ℝ) 1))
        ∧ (∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball σ δ,
            HasDerivAt (fun r => intervalDomainLift (realSlice u_star r) x)
              (vdotL s x) s)
        ∧ (∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball σ δ,
            0 < intervalDomainLift (realSlice u_star s) x)
        ∧ ContinuousOn
            (Function.uncurry
              (fun s x => p.ν * p.γ
                * (intervalDomainLift (realSlice u_star s) x) ^ (p.γ - 1)
                * vdotL s x))
            (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro σ hσ
    obtain ⟨δ, hδpos, hfc, hsl, hpc, hslab⟩ := hK1 σ hσ
    -- convert the `gPow`-form slab continuity into the banked engine's lambda form.
    rw [gPow_uncurry_eq (p := p) (v := realSlice u_star) (vdotL := vdotL)] at hslab
    exact ⟨δ, hδpos, hfc, hsl, hpc, hslab⟩
  have hderivAll : ∀ σ ∈ Set.Ioo (0 : ℝ) T, ∀ k : ℕ,
      HasDerivAt
        (fun r => cosineCoeffs
          (fun x => p.ν * (intervalDomainLift (realSlice u_star r) x) ^ p.γ) k)
        (adotPow p (realSlice u_star) vdotL σ k) σ :=
    realSlice_powerCoeff_hasDerivAt (p := p) u_star (vdotL := vdotL) hδ
  -- K1(iii): per-`t₀` window-uniform bound; `Mdot t₀` chosen from the bound existential
  -- on the clamp window (under `0<t₀<T`; an arbitrary value otherwise — never read).
  let Mdot : ℝ → ℝ := fun t₀ =>
    if h : 0 < t₀ ∧ t₀ < T then
      Classical.choose (powerCoeff_bound_of_inputs (p := p) (v := realSlice u_star)
        (vdotL := vdotL) (a' := t₀ / 4) (b' := (t₀ + 3 * T) / 4) (hslabcont t₀ h.1 h.2))
    else 0
  have hMdotspec : ∀ t₀ (h1 : 0 < t₀) (h2 : t₀ < T),
      ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4), ∀ k,
        |adotPow p (realSlice u_star) vdotL σ k| ≤ Mdot t₀ := by
    intro t₀ h1 h2
    have hpick := Classical.choose_spec (powerCoeff_bound_of_inputs (p := p)
      (v := realSlice u_star) (vdotL := vdotL) (a' := t₀ / 4) (b' := (t₀ + 3 * T) / 4)
      (hslabcont t₀ h1 h2))
    have hval : Mdot t₀ = Classical.choose (powerCoeff_bound_of_inputs (p := p)
        (v := realSlice u_star) (vdotL := vdotL) (a' := t₀ / 4) (b' := (t₀ + 3 * T) / 4)
        (hslabcont t₀ h1 h2)) := dif_pos ⟨h1, h2⟩
    rw [hval]; exact hpick
  -- assemble the quadruple in the windowed shapes (`adotP` is t₀-independent).
  refine realSlice_resolverSpectralData_of_windowedPowerSource p u_star bc hbsum hagree
    hpos C hC hdecay ha0
    (fun _ σ n => adotPow p (realSlice u_star) vdotL σ n) Mdot ?_ ?_ ?_
  · -- hderivP: per-window `HasDerivAt` from the global K1(i) datum (window ⊂ Ioo 0 T).
    intro t₀ ht₀ ht₀T σ hσ n
    have hσInt : σ ∈ Set.Ioo (0 : ℝ) T := by
      refine ⟨lt_of_lt_of_le (by linarith) hσ.1, lt_of_le_of_lt hσ.2 (by linarith)⟩
    exact hderivAll σ hσInt n
  · -- hadotcontP: K1(ii) continuity on the clamp window via the joint slab continuity.
    intro t₀ ht₀ ht₀T n
    exact powerCoeff_continuousOn_of_inputs (p := p) (v := realSlice u_star)
      (vdotL := vdotL) (a' := t₀ / 4) (b' := (t₀ + 3 * T) / 4) n (hslabcont t₀ ht₀ ht₀T)
  · -- hMdotP: the chosen per-`t₀` uniform bound.
    intro t₀ ht₀ ht₀T σ hσ n
    exact hMdotspec t₀ ht₀ ht₀T σ hσ n

end ShenWork.EWA
