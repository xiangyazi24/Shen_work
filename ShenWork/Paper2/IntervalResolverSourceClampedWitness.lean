/-
  ShenWork/Paper2/IntervalResolverSourceClampedWitness.lean

  **Clamped, time-shifted resolver power-source `DuhamelSourceTimeC1` witness —
  the per-`t₀` filler of the (retyped) ledger `Hvsrc` field.**

  The ledger field `Hvsrc` was retyped (this campaign) from the unsatisfiable GLOBAL
  `DuhamelSourceTimeC1 (fun s k => (resolverSourceCoeff p (D.u s) k).re)` to the
  per-`t₀` clamped form

      ∀ t₀, 0 < t₀ → t₀ < D.T →
        ∃ aC, ∃ _ : DuhamelSourceTimeC1 aC, ∃ W ∈ 𝓝 t₀,
          ∀ s ∈ W, ∀ k, aC s k = (resolverSourceCoeff p (D.u s) k).re

  (see `IntervalDomainMildLocalChi0.Hvsrc` field doc).  This file produces exactly
  that witness from WINDOWED power-source data, exactly mirroring the logistic
  `ClampedSourceRepresentation.clampedSource_duhamelSourceTimeC1` trick:

  Compose the slice index with the C¹ soft clamp `Φ σ := φ c' c d d' (τ + σ)`
  (`ShenWork.IntervalTimeSoftClamp`), so every slice index lands in the compact
  window `[c', d'] ⊂ (0, T)` (`φ_mem_range`).  The reindexed trajectory
  `wc σ := w (Φ σ)` then satisfies the GLOBAL hypotheses of the resolver-source
  representation producer
  `IntervalDomainLogisticWeakH2Adapter.resolverSource_duhamelSourceTimeC1_of_representation`
  (its slice index always lies in the window), and the time-`C¹` data transfers by
  the chain rule (`Φ' = ψ (τ + σ)`, `hasDerivAt_φ`, `ψ ∈ [0,1]`).  On the active
  window `τ + σ ∈ [c, d]` the clamp is the identity (`φ_eq_id_on`), so the clamped
  resolver-source coefficient family AGREES there with the genuine
  `(resolverSourceCoeff p (w (τ + σ)) k).re` family.

  No `sorry`/`admit`/custom `axiom`/`native_decide` in this file.
-/
import ShenWork.Paper2.IntervalDomainLogisticWeakH2Adapter
import ShenWork.PDE.IntervalTimeSoftClamp

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalDomainLogisticWeakH2Adapter
  (resolverSource_duhamelSourceTimeC1_of_representation
   resolverSourceCoeff_re_eq_cosineCoeffs)

noncomputable section

namespace ShenWork.Paper2.ResolverSourceClampedWitness

open ShenWork.IntervalTimeSoftClamp

/-- **Clamped, time-shifted resolver power-source `DuhamelSourceTimeC1`.**

For a trajectory `w` whose per-slice cosine representation / positivity / power-source
quadratic decay / time-`C¹` coefficient data for `ν·u^γ` are known ONLY on the
compact window `[c', d'] ⊂ (0, T)`, this produces the `DuhamelSourceTimeC1` package
for the CLAMPED resolver-source family

    `σ ↦ k ↦ (resolverSourceCoeff p (w (φ c' c d d' (τ + σ))) k).re`,

whose slice index `Φ σ := φ c' c d d' (τ + σ)` always lies in `[c', d']`
(`φ_mem_range`).  The composed trajectory `wc σ := w (Φ σ)` satisfies the GLOBAL
hypotheses of `resolverSource_duhamelSourceTimeC1_of_representation`, and the
time-`C¹` data transfers by the chain rule (inner derivative `ψ (τ + σ)`). -/
noncomputable def clampedResolverSource_duhamelSourceTimeC1
    (p : CM2Params) (w : ℝ → intervalDomainPoint → ℝ)
    -- clamp parameters
    {τ c' c d d' : ℝ} (hc' : c' < c) (hcd : c ≤ d) (hd' : d < d')
    -- per-slice cosine representation, required ONLY on the window
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ ∈ Set.Icc c' d',
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ ∈ Set.Icc c' d', Set.EqOn (intervalDomainLift (w σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (w σ) x)
    -- power-source quadratic decay on the window
    {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ σ ∈ Set.Icc c' d', ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (fun x => p.ν * intervalDomainLift (w σ) x ^ p.γ) k|
        ≤ C / ((k : ℝ) * Real.pi) ^ 2)
    (ha0 : ∀ σ ∈ Set.Icc c' d',
      |cosineCoeffs (fun x => p.ν * intervalDomainLift (w σ) x ^ p.γ) 0| ≤ C)
    -- K1 power-source time-C¹ data on the window
    (adot : ℝ → ℕ → ℝ)
    (hderiv : ∀ σ ∈ Set.Icc c' d', ∀ n, HasDerivAt
      (fun r => cosineCoeffs (fun x => p.ν * intervalDomainLift (w r) x ^ p.γ) n)
      (adot σ n) σ)
    (hadotcont : ∀ n, ContinuousOn (fun σ => adot σ n) (Set.Icc c' d'))
    {Mdot : ℝ} (hMdot : ∀ σ ∈ Set.Icc c' d', ∀ n, |adot σ n| ≤ Mdot) :
    DuhamelSourceTimeC1
      (fun σ k => (ShenWork.PDE.intervalNeumannResolverSourceCoeff p
        (w (ShenWork.IntervalTimeSoftClamp.φ c' c d d' (τ + σ))) k).re) := by
  -- The clamped slice index and the composed trajectory.
  set Φ : ℝ → ℝ := fun σ => φ c' c d d' (τ + σ) with hΦ
  have hΦmem : ∀ σ, Φ σ ∈ Set.Icc c' d' := fun σ => φ_mem_range hc' hcd hd' (τ + σ)
  set wc : ℝ → intervalDomainPoint → ℝ := fun σ => w (Φ σ) with hwc
  -- Inner derivative of `Φ`: `Φ' σ = ψ (τ + σ)` (clamp FTC ∘ affine shift).
  have hΦderiv : ∀ σ, HasDerivAt Φ (ψ c' c d d' (τ + σ)) σ := by
    intro σ
    have hshift : HasDerivAt (fun s : ℝ => τ + s) 1 σ := (hasDerivAt_id σ).const_add τ
    have h := (hasDerivAt_φ (c' := c') (c := c) (d := d) (d' := d') (τ + σ)).comp σ hshift
    simpa [Φ, hΦ, Function.comp, mul_one] using h
  -- Composed time derivative of each coefficient: `adot (Φ σ) k · ψ (τ + σ)`.
  set adotc : ℝ → ℕ → ℝ := fun σ k => adot (Φ σ) k * ψ c' c d d' (τ + σ) with hadotc
  -- `Mdot ≥ 0` (window nonempty: `c' ∈ [c', d']`).
  have hc'mem : c' ∈ Set.Icc c' d' := ⟨le_rfl, by linarith [hc'.le, hd'.le]⟩
  have hMdot_nn : 0 ≤ Mdot := le_trans (abs_nonneg _) (hMdot c' hc'mem 0)
  -- Globalized hypotheses for the composed trajectory `wc`.
  have hbsum' : ∀ σ, Summable (fun n => unitIntervalCosineEigenvalue n * |bc (Φ σ) n|) :=
    fun σ => hbsum (Φ σ) (hΦmem σ)
  have hagree' : ∀ σ, Set.EqOn (intervalDomainLift (wc σ))
      (fun x => ∑' n, bc (Φ σ) n * cosineMode n x) (Set.Icc (0 : ℝ) 1) :=
    fun σ => hagree (Φ σ) (hΦmem σ)
  have hpos' : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (wc σ) x :=
    fun σ => hpos (Φ σ) (hΦmem σ)
  have hdecay' : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (fun x => p.ν * intervalDomainLift (wc σ) x ^ p.γ) k|
        ≤ C / ((k : ℝ) * Real.pi) ^ 2 :=
    fun σ _ => hdecay (Φ σ) (hΦmem σ)
  have ha0' : ∀ σ, 0 ≤ σ →
      |cosineCoeffs (fun x => p.ν * intervalDomainLift (wc σ) x ^ p.γ) 0| ≤ C :=
    fun σ _ => ha0 (Φ σ) (hΦmem σ)
  -- Composed time-`C¹` derivative via the chain rule.
  have hderiv' : ∀ σ n, HasDerivAt
      (fun r => cosineCoeffs (fun x => p.ν * intervalDomainLift (wc r) x ^ p.γ) n)
      (adotc σ n) σ := by
    intro σ n
    have houter := hderiv (Φ σ) (hΦmem σ) n
    have h := houter.comp σ (hΦderiv σ)
    have hfun : (fun r => cosineCoeffs
        (fun x => p.ν * intervalDomainLift (wc r) x ^ p.γ) n)
        = (fun s => cosineCoeffs
            (fun x => p.ν * intervalDomainLift (w s) x ^ p.γ) n) ∘ Φ := by
      funext r; simp [wc, Function.comp]
    rw [hfun]
    simpa [adotc, hadotc] using h
  -- Continuity of the composed derivative coefficients.
  have hΦcont : Continuous Φ :=
    φ_continuous.comp (continuous_const.add continuous_id)
  have hadotcont' : ∀ n, Continuous (fun σ => adotc σ n) := by
    intro n
    have h1 : Continuous (fun σ => adot (Φ σ) n) :=
      (hadotcont n).comp_continuous hΦcont (fun σ => hΦmem σ)
    have h2 : Continuous (fun σ => ψ c' c d d' (τ + σ)) :=
      ψ_continuous.comp (continuous_const.add continuous_id)
    simpa [adotc, hadotc] using h1.mul h2
  -- Uniform bound on the composed derivative coefficients (`|adot · ψ| ≤ Mdot · 1`).
  have hMdot' : ∀ σ, 0 ≤ σ → ∀ n, |adotc σ n| ≤ Mdot := by
    intro σ _ n
    rw [hadotc]
    rw [abs_mul, abs_of_nonneg (ψ_nonneg (τ + σ))]
    calc |adot (Φ σ) n| * ψ c' c d d' (τ + σ)
        ≤ Mdot * 1 := by
          apply mul_le_mul (hMdot (Φ σ) (hΦmem σ) n) (ψ_le_one (τ + σ))
            (ψ_nonneg (τ + σ)) hMdot_nn
      _ = Mdot := mul_one _
  -- Assemble through the resolver-source representation producer for `wc`.
  have hpkg := resolverSource_duhamelSourceTimeC1_of_representation
    p (w := wc) (fun σ => bc (Φ σ)) hbsum' hagree' hpos'
    hC hdecay' ha0' (adot := adotc) hderiv' hadotcont' hMdot'
  -- The producer's output family is exactly the clamped resolver-source family.
  simpa [wc, hwc, Φ, hΦ] using hpkg

/-- **Agreement on the active window.**  Where `τ + σ ∈ [c, d]` the clamp is the
identity (`φ_eq_id_on`), so the clamped resolver-source coefficient family agrees
(in `k`) with the genuine `w (τ + σ)` resolver-source coefficient family. -/
theorem clampedResolverFamily_eq_on
    (p : CM2Params) (w : ℝ → intervalDomainPoint → ℝ)
    {τ c' c d d' : ℝ} (hc' : c' < c) (hd' : d < d')
    {σ : ℝ} (hσ : τ + σ ∈ Set.Icc c d) (k : ℕ) :
    (ShenWork.PDE.intervalNeumannResolverSourceCoeff p
        (w (ShenWork.IntervalTimeSoftClamp.φ c' c d d' (τ + σ))) k).re
      = (ShenWork.PDE.intervalNeumannResolverSourceCoeff p (w (τ + σ)) k).re := by
  rw [ShenWork.IntervalTimeSoftClamp.φ_eq_id_on hc' hd' hσ]

end ShenWork.Paper2.ResolverSourceClampedWitness
