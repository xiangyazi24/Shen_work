/-
  ShenWork/Paper2/IntervalResolverSourceWitnessFrontier.lean

  Producer-facing window data for the resolver-source witness consumed by the
  PPID restart-core frontier.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalResolverSourceClampedWitness
import ShenWork.Paper2.IntervalMildRegularityFrontierAssembly

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.PDE (intervalNeumannResolverSourceCoeff)

noncomputable section

namespace ShenWork.Paper2.ResolverSourceWitnessFrontier

/-- The raw resolver-source witness field used in the current PPID residual. -/
def ResolverSourceWitness
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∀ t₀, 0 < t₀ → t₀ < D.T →
    ∃ (aC : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC1 aC) (W : Set ℝ),
      W ∈ 𝓝 t₀ ∧
      (∀ s ∈ W, ∀ k,
        aC s k = (intervalNeumannResolverSourceCoeff p (D.u s) k).re)

/-- Windowed power-source data that existing clamped resolver-source machinery can
consume.  This is a producer-friendly replacement for the raw
`ResolverSourceWitness`.  It remains a real residual, but it is lower-level and
non-circular. -/
def ResolverSourceWindowData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∀ t₀, 0 < t₀ → t₀ < D.T →
    ∃ (c' c d d' : ℝ) (bc : ℝ → ℕ → ℝ) (C : ℝ)
      (adot : ℝ → ℕ → ℝ) (Mdot : ℝ),
      c' < c ∧ c < t₀ ∧ t₀ < d ∧ d < d' ∧
      0 ≤ C ∧
      (∀ σ ∈ Set.Icc c' d',
        Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|)) ∧
      (∀ σ ∈ Set.Icc c' d',
        Set.EqOn (intervalDomainLift (D.u σ))
          (fun x => ∑' n, bc σ n * cosineMode n x)
          (Set.Icc (0 : ℝ) 1)) ∧
      (∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
        0 < intervalDomainLift (D.u σ) x) ∧
      (∀ σ ∈ Set.Icc c' d', ∀ k : ℕ, 1 ≤ k →
        |cosineCoeffs (fun x => p.ν * intervalDomainLift (D.u σ) x ^ p.γ) k|
          ≤ C / ((k : ℝ) * Real.pi) ^ 2) ∧
      (∀ σ ∈ Set.Icc c' d',
        |cosineCoeffs (fun x => p.ν * intervalDomainLift (D.u σ) x ^ p.γ) 0|
          ≤ C) ∧
      (∀ σ ∈ Set.Icc c' d', ∀ n,
        HasDerivAt
          (fun r => cosineCoeffs
            (fun x => p.ν * intervalDomainLift (D.u r) x ^ p.γ) n)
          (adot σ n) σ) ∧
      (∀ n, ContinuousOn (fun σ => adot σ n) (Set.Icc c' d')) ∧
      (∀ σ ∈ Set.Icc c' d', ∀ n, |adot σ n| ≤ Mdot)

/-- Existing clamped resolver-source machinery turns windowed power-source data
into the raw per-`t₀` witness field. -/
theorem resolverSourceWitness_of_windowData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (H : ResolverSourceWindowData p D) :
    ResolverSourceWitness p D := by
  intro t₀ ht₀ ht₀T
  obtain ⟨c', c, d, d', bc, C, adot, Mdot,
    hc'c, hct₀, ht₀d, hdd', hC,
    hbsum, hagree, hpos, hdecay, ha0, hderiv, hadotcont, hMdot⟩ :=
    H t₀ ht₀ ht₀T
  refine ⟨fun s k =>
      (intervalNeumannResolverSourceCoeff p
        (D.u (ShenWork.IntervalTimeSoftClamp.φ c' c d d' ((0 : ℝ) + s))) k).re,
    ?_, Set.Ioo c d, ?_, ?_⟩
  · exact
      ShenWork.Paper2.ResolverSourceClampedWitness.clampedResolverSource_duhamelSourceTimeC1
        p D.u (τ := 0) hc'c (le_of_lt (lt_trans hct₀ ht₀d)) hdd'
        bc hbsum hagree hpos hC hdecay ha0 adot hderiv hadotcont hMdot
  · exact isOpen_Ioo.mem_nhds ⟨hct₀, ht₀d⟩
  · intro s hs k
    have hsIcc : (0 : ℝ) + s ∈ Set.Icc c d :=
      ⟨by simpa using le_of_lt hs.1, by simpa using le_of_lt hs.2⟩
    simpa using
      ShenWork.Paper2.ResolverSourceClampedWitness.clampedResolverFamily_eq_on
        p D.u (τ := 0) hc'c hdd' hsIcc k

/-- The raw witness produced above immediately gives resolver direct spectral
data. -/
theorem resolverDirectSpectralData_of_windowData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (H : ResolverSourceWindowData p D) :
    ShenWork.IntervalResolverDirectTimeRegularity.HasResolverDirectSpectralData
      D.T (ShenWork.IntervalMildToClassical.mildChemicalConcentration p D.u) p :=
  ShenWork.Paper2.RegularityFrontierAssembly.hasResolverDirectSpectralData_of_clamped_perT0
    D.u (resolverSourceWitness_of_windowData H)

end ShenWork.Paper2.ResolverSourceWitnessFrontier
