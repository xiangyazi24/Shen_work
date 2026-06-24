/-
  ShenWork/Wiener/EWA/SourceResolverTimeC1Discharge.lean

  **χ₀<0 capstone — discharging the resolver-source TIME-`C¹` `Hclamp` residual of
  `realSlice_resolverSpectralData` (SourceResolverSpectralDischarge.lean:275) for the
  EWA Duhamel fixed-point slice `u := realSlice u_star`.**

  `realSlice_resolverSpectralData` consumes a per-`t₀` clamped resolver-source witness

      Hclamp : ∀ t₀, 0 < t₀ → t₀ < T →
        ∃ (aC : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC1 aC) (W : Set ℝ),
          W ∈ 𝓝 t₀ ∧ (∀ s ∈ W, ∀ k, aC s k =
            (intervalNeumannResolverSourceCoeff p (realSlice u_star s) k).re)

  and feeds it to `hasResolverDirectSpectralData_of_clamped_perT0` to produce
  `Hv : HasResolverDirectSpectralData T (mildChemicalConcentration p (realSlice u_star)) p`.

  This file PRODUCES that `Hclamp`.  The resolver source `ν·u^γ` is another power-of-`u`
  term in the same EWA (weighted-Wiener) algebra as the chemDiv and logistic sources, so
  the construction MIRRORS the canonical-Picard `Hvsrc` block of
  `Thm11ChiZeroCoreProvider` (lines 595–711) verbatim, swapping the canonical `D.u`
  trajectory for `realSlice u_star`:

  * For each interior `t₀` pick the soft-clamp window `[c',d'] = [t₀/4, (t₀+3T)/4] ⊂ (0,T)`
    with active id-zone `[c,d] = [t₀/2, (t₀+T)/2]` (a neighborhood of `t₀`).
  * Build the clamped resolver-source `DuhamelSourceTimeC1` via
    `ResolverSourceClampedWitness.clampedResolverSource_duhamelSourceTimeC1` (the `ν·u^γ`
    mirror of the logistic clamped source), feeding the WINDOWED power-source data.
  * Take `W := Ioo c d ∈ 𝓝 t₀`; on `W` the clamp is the identity (`φ_eq_id_on`), so the
    clamped family AGREES with the canonical resolver-source coefficients
    (`clampedResolverFamily_eq_on`).

  ## What is genuinely carried (the honest χ₀<0 frontier)

  `realSlice_classicalRegularity` carries only spatial-regularity and per-slice positivity
  atoms; it carries NO time-differentiability datum for the `u`-slice source.  Hence the
  WINDOWED power-source data the clamped producer consumes — the per-slice cosine
  representation (`bc`/`hbsum`/`hagree`), per-slice positivity (`hpos`), the power-source
  quadratic-decay constant `C` (`hdecay`/`ha0`), and the power-source K1 time-`C¹`
  quadruple (`adotP`/`hderivP`/`hadotcontP`/`hMdotP`) — is carried here as NAMED
  hypotheses.  These are exactly the inputs the canonical-Picard side discharges from its
  subtype-continuity engine (`powerSource_window_uniform_decay` /
  `powerK1_quadruple_of_subtypeCont`); for the abstract EWA fixed-point slice they are the
  precise remaining frontier, threaded — not asserted.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceResolverSpectralDischarge
import ShenWork.Paper2.IntervalResolverSourceClampedWitness

noncomputable section

namespace ShenWork.EWA

open Set Filter Topology
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalResolverDirectTimeRegularity (HasResolverDirectSpectralData)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.PDE (intervalNeumannResolverSourceCoeff)

variable {T : ℝ}

/-- **The per-`t₀` clamped resolver-source witness `Hclamp`, for the EWA slice
`realSlice u_star`.**

For each interior `t₀ ∈ (0,T)`, build the `DuhamelSourceTimeC1` package of a clamped
resolver-source coefficient family that agrees with the canonical resolver-source
coefficients `s ↦ (intervalNeumannResolverSourceCoeff p (realSlice u_star s) k).re` on a
neighborhood `W ∈ 𝓝 t₀`.

The construction is the `realSlice u_star` clone of the canonical-Picard `Hvsrc` block:
the soft-clamp window `[t₀/4, (t₀+3T)/4] ⊂ (0,T)` with id-zone `[t₀/2, (t₀+T)/2]`, fed to
`clampedResolverSource_duhamelSourceTimeC1`.

The WINDOWED power-source data the clamped producer consumes is carried as the hypotheses
`bc`/`hbsum`/`hagree`/`hpos` (cosine representation + per-slice positivity), `C`/`hC`/
`hdecay`/`ha0` (power-source quadratic decay), and `adotP`/`Mdot`/`hderivP`/`hadotcontP`/
`hMdotP` (the power-source K1 time-`C¹` quadruple) — each provided per `t₀` on its own
clamp window `[t₀/4, (t₀+3T)/4]`.  These are the genuine χ₀<0 resolver-source TIME-`C¹`
frontier (not derivable from the atoms `realSlice_classicalRegularity` carries).

The result is a `theorem` (its conclusion is the `Prop`-valued per-`t₀` existential), even
though it internally builds the `Type`-valued `DuhamelSourceTimeC1` structure. -/
theorem realSlice_resolverSource_clampedWitness
    (p : CM2Params) (u_star : EWA T 1)
    (bc : ℝ → ℝ → ℕ → ℝ)
    (hbsum : ∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc t₀ σ n|))
    (hagree : ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      Set.EqOn (intervalDomainLift (realSlice u_star σ))
        (fun x => ∑' n, bc t₀ σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (realSlice u_star σ) x)
    (C : ℝ → ℝ) (hC : ∀ t₀, 0 ≤ C t₀)
    (hdecay : ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4), ∀ k : ℕ, 1 ≤ k →
        |cosineCoeffs (fun x => p.ν * intervalDomainLift (realSlice u_star σ) x ^ p.γ) k|
          ≤ C t₀ / ((k : ℝ) * Real.pi) ^ 2)
    (ha0 : ∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      |cosineCoeffs (fun x => p.ν * intervalDomainLift (realSlice u_star σ) x ^ p.γ) 0|
        ≤ C t₀)
    (adotP : ℝ → ℝ → ℕ → ℝ) (Mdot : ℝ → ℝ)
    (hderivP : ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4), ∀ n, HasDerivAt
        (fun r => cosineCoeffs
          (fun x => p.ν * intervalDomainLift (realSlice u_star r) x ^ p.γ) n)
        (adotP t₀ σ n) σ)
    (hadotcontP : ∀ t₀, 0 < t₀ → t₀ < T → ∀ n,
      ContinuousOn (fun σ => adotP t₀ σ n) (Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4)))
    (hMdotP : ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4), ∀ n, |adotP t₀ σ n| ≤ Mdot t₀) :
    ∀ t₀, 0 < t₀ → t₀ < T →
      ∃ (aC : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC1 aC) (W : Set ℝ),
        W ∈ 𝓝 t₀ ∧
        (∀ s ∈ W, ∀ k, aC s k =
          (intervalNeumannResolverSourceCoeff p (realSlice u_star s) k).re) := by
  intro t₀ ht₀ ht₀T
  -- clamp window and id-zone around t₀, both ⊂ (0, T).
  set c' : ℝ := t₀ / 4 with hc'def
  set c : ℝ := t₀ / 2 with hcdef
  set d : ℝ := (t₀ + T) / 2 with hddef
  set d' : ℝ := (t₀ + 3 * T) / 4 with hd'def
  have hc'c : c' < c := by rw [hc'def, hcdef]; linarith
  have hcd : c ≤ d := by rw [hcdef, hddef]; linarith
  have hdd' : d < d' := by rw [hddef, hd'def]; linarith
  -- the windowed power-source data, specialized at this t₀.
  have hbsumW := hbsum t₀ ht₀ ht₀T
  have hagreeW := hagree t₀ ht₀ ht₀T
  have hposW := hpos t₀ ht₀ ht₀T
  have hdecayW := hdecay t₀ ht₀ ht₀T
  have ha0W := ha0 t₀ ht₀ ht₀T
  have hderivW := hderivP t₀ ht₀ ht₀T
  have hadotcontW := hadotcontP t₀ ht₀ ht₀T
  have hMdotW := hMdotP t₀ ht₀ ht₀T
  -- Build the clamped resolver-source `DuhamelSourceTimeC1` (τ = 0 ⇒ Φ = φ).
  refine ⟨fun σ k => (intervalNeumannResolverSourceCoeff p
      (realSlice u_star (ShenWork.IntervalTimeSoftClamp.φ c' c d d' (0 + σ))) k).re,
    ?_, Set.Ioo c d, ?_, ?_⟩
  · exact ShenWork.Paper2.ResolverSourceClampedWitness.clampedResolverSource_duhamelSourceTimeC1
      p (realSlice u_star) hc'c hcd hdd' (bc t₀) hbsumW hagreeW hposW (hC t₀) hdecayW ha0W
      (adotP t₀) hderivW hadotcontW hMdotW
  · -- W = Ioo c d ∈ 𝓝 t₀  (c = t₀/2 < t₀ < (t₀+T)/2 = d)
    refine isOpen_Ioo.mem_nhds ⟨?_, ?_⟩
    · rw [hcdef]; linarith
    · rw [hddef]; linarith
  · -- agreement on W: on Ioo c d ⊂ Icc c d the clamp is the identity (φ = id).
    intro s hs k
    have hsId : (0 : ℝ) + s ∈ Set.Icc c d :=
      ⟨by simpa using le_of_lt hs.1, by simpa using le_of_lt hs.2⟩
    have heq := ShenWork.Paper2.ResolverSourceClampedWitness.clampedResolverFamily_eq_on
      p (realSlice u_star) hc'c hdd' hsId k
    simpa using heq

/-- **`Hv` for the EWA slice, fully wired from the windowed power-source data.**

Chaining `realSlice_resolverSource_clampedWitness` (which builds the per-`t₀` clamped
witness `Hclamp`) into `realSlice_resolverSpectralData`
(`SourceResolverSpectralDischarge.lean:275`) produces the resolver direct spectral datum

    HasResolverDirectSpectralData T (mildChemicalConcentration p (realSlice u_star)) p

— i.e. the `Hv` carried hypothesis of `realSlice_reducedCore`
(`SourceReducedCore.lean:143`) — directly from the windowed power-source inputs, with no
residual `Hclamp` left open.  This is the consumer-facing endpoint: it converts the
genuine χ₀<0 resolver-source TIME-`C¹` frontier (the named windowed power-source
hypotheses) into the spectral datum the reduced core needs. -/
theorem realSlice_resolverSpectralData_of_windowedPowerSource
    (p : CM2Params) (u_star : EWA T 1)
    (bc : ℝ → ℝ → ℕ → ℝ)
    (hbsum : ∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc t₀ σ n|))
    (hagree : ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      Set.EqOn (intervalDomainLift (realSlice u_star σ))
        (fun x => ∑' n, bc t₀ σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (realSlice u_star σ) x)
    (C : ℝ → ℝ) (hC : ∀ t₀, 0 ≤ C t₀)
    (hdecay : ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4), ∀ k : ℕ, 1 ≤ k →
        |cosineCoeffs (fun x => p.ν * intervalDomainLift (realSlice u_star σ) x ^ p.γ) k|
          ≤ C t₀ / ((k : ℝ) * Real.pi) ^ 2)
    (ha0 : ∀ t₀, 0 < t₀ → t₀ < T → ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4),
      |cosineCoeffs (fun x => p.ν * intervalDomainLift (realSlice u_star σ) x ^ p.γ) 0|
        ≤ C t₀)
    (adotP : ℝ → ℝ → ℕ → ℝ) (Mdot : ℝ → ℝ)
    (hderivP : ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4), ∀ n, HasDerivAt
        (fun r => cosineCoeffs
          (fun x => p.ν * intervalDomainLift (realSlice u_star r) x ^ p.γ) n)
        (adotP t₀ σ n) σ)
    (hadotcontP : ∀ t₀, 0 < t₀ → t₀ < T → ∀ n,
      ContinuousOn (fun σ => adotP t₀ σ n) (Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4)))
    (hMdotP : ∀ t₀, 0 < t₀ → t₀ < T →
      ∀ σ ∈ Set.Icc (t₀ / 4) ((t₀ + 3 * T) / 4), ∀ n, |adotP t₀ σ n| ≤ Mdot t₀) :
    HasResolverDirectSpectralData T
      (mildChemicalConcentration p (realSlice u_star)) p :=
  realSlice_resolverSpectralData p u_star
    (realSlice_resolverSource_clampedWitness p u_star bc hbsum hagree hpos C hC hdecay ha0
      adotP Mdot hderivP hadotcontP hMdotP)

end ShenWork.EWA
