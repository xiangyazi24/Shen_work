/-
  ShenWork/Paper2/IntervalResolverSourceWindowDecayFrontier.lean

  Decay-lowered resolver-source window data.

  This module uses the existing `powerSource_window_uniform_decay` theorem to
  replace the explicit power-source quadratic decay fields in
  `ResolverSourceWindowData` by spatial K2 window bounds and positive lower /
  upper bounds.  It leaves the power-source K1 time-derivative data as an
  explicit residual.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalResolverSourceWitnessFrontier
import ShenWork.Paper2.IntervalResolverPowerDecay

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)

noncomputable section

namespace ShenWork.Paper2.ResolverSourceWitnessFrontier

/-- A lower-level window package for the resolver source.  Compared with
`ResolverSourceWindowData`, the explicit `ν * u^γ` cosine-decay fields are
replaced by spatial K2 data plus a positive lower bound and an upper bound on
the lifted solution.  The K1 time-derivative data is still carried explicitly. -/
def ResolverSourceWindowSpatialK1Data
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∀ t₀, 0 < t₀ → t₀ < D.T →
    ∃ (c' c d d' : ℝ) (bc : ℝ → ℕ → ℝ) (m M G1 G2 : ℝ)
      (adot : ℝ → ℕ → ℝ) (Mdot : ℝ),
      c' < c ∧ c < t₀ ∧ t₀ < d ∧ d < d' ∧ 0 < m ∧
      (∀ σ ∈ Set.Icc c' d',
        Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|)) ∧
      (∀ σ ∈ Set.Icc c' d',
        Set.EqOn (intervalDomainLift (D.u σ))
          (fun x => ∑' n, bc σ n * cosineMode n x)
          (Set.Icc (0 : ℝ) 1)) ∧
      (∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
        m ≤ intervalDomainLift (D.u σ) x) ∧
      (∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift (D.u σ) x ≤ M) ∧
      (∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (intervalDomainLift (D.u σ)) x| ≤ G1) ∧
      (∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (deriv (intervalDomainLift (D.u σ))) x| ≤ G2) ∧
      (∀ σ ∈ Set.Icc c' d', ∀ n,
        HasDerivAt
          (fun r => cosineCoeffs
            (fun x => p.ν * intervalDomainLift (D.u r) x ^ p.γ) n)
          (adot σ n) σ) ∧
      (∀ n, ContinuousOn (fun σ => adot σ n) (Set.Icc c' d')) ∧
      (∀ σ ∈ Set.Icc c' d', ∀ n, |adot σ n| ≤ Mdot)

/-- Spatial K2 window data produces the explicit resolver-source window data by
the already-proved power-source quadratic decay estimate. -/
theorem windowData_of_spatialK1Data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (H : ResolverSourceWindowSpatialK1Data p D) :
    ResolverSourceWindowData p D := by
  intro t₀ ht₀ ht₀T
  obtain ⟨c', c, d, d', bc, m, M, G1, G2, adot, Mdot,
    hc'c, hct₀, ht₀d, hdd', hm, hbsum, hagree, hlb, hub, hG1, hG2,
    hderiv, hadotcont, hMdot⟩ := H t₀ ht₀ ht₀T
  have hcd' : c' ≤ d' := by
    linarith
  obtain ⟨C, hC, hdecay, ha0⟩ :=
    ShenWork.Paper2.ResolverPowerDecay.powerSource_window_uniform_decay
      (ν := p.ν) (γ := p.γ) (M := M) (m := m)
      p.hν.le p.hγ hm hcd' bc hbsum hagree hlb hub hG1 hG2
  refine ⟨c', c, d, d', bc, C, adot, Mdot,
    hc'c, hct₀, ht₀d, hdd', hC, hbsum, hagree, ?_, hdecay, ha0,
    hderiv, hadotcont, hMdot⟩
  intro σ hσ x hx
  exact lt_of_lt_of_le hm (hlb σ hσ x hx)

/-- Spatial K2 window data also directly produces the raw clamped witness. -/
theorem resolverSourceWitness_of_spatialK1Data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (H : ResolverSourceWindowSpatialK1Data p D) :
    ResolverSourceWitness p D :=
  resolverSourceWitness_of_windowData (windowData_of_spatialK1Data H)

end ShenWork.Paper2.ResolverSourceWitnessFrontier
