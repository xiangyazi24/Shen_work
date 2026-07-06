/-
  ShenWork/Paper2/IntervalResolverSourceWindowInputs.lean

  Global/per-compact producer-side inputs for the resolver-source window data.

  This module replaces the awkward per-`t₀` existential window shape of
  `ResolverSourceWindowData` by a standard primitive ledger: one global cosine
  representation family, per-compact lower/upper/K2 bounds, and power-source K1
  time-derivative data.  The per-window decay constant is produced by
  `ResolverPowerDecay.powerSource_window_uniform_decay`.

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

namespace ShenWork.Paper2.ResolverSourceWindowInput

/-- Primitive producer-side inputs for the resolver-source window field.

This is intentionally different from `ResolverSourceWindowData`: it carries
global/per-compact representation, bounds, and power-K1 data.  The per-window
decay constant `C` is produced from these fields. -/
structure ResolverSourceWindowInputs
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) where
  bc : ℝ → ℕ → ℝ
  hbsum : ∀ σ, 0 < σ → σ < D.T →
    Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|)
  hagree : ∀ σ, 0 < σ → σ < D.T →
    Set.EqOn (intervalDomainLift (D.u σ))
      (fun x => ∑' n, bc σ n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1)
  hpos : ∀ σ, 0 < σ → σ < D.T →
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (D.u σ) x
  Msup : ℝ
  hub : ∀ σ, 0 < σ → σ < D.T →
    ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (D.u σ) x ≤ Msup
  /-- Window-uniform positive lower bound, the non-`χ₀ = 0` replacement for
  the current χ0-specific compact positivity producer. -/
  hlower : ∀ a b, 0 < a → b < D.T → a ≤ b →
    ∃ m : ℝ, 0 < m ∧
      ∀ σ ∈ Set.Icc a b, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        m ≤ intervalDomainLift (D.u σ) x
  hG1 : ∀ a b, 0 < a → b < D.T →
    ∃ G1, ∀ σ ∈ Set.Icc a b, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (D.u σ)) x| ≤ G1
  hG2 : ∀ a b, 0 < a → b < D.T →
    ∃ G2, ∀ σ ∈ Set.Icc a b, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (D.u σ))) x| ≤ G2
  adotPow : ℝ → ℕ → ℝ
  hderivPow : ∀ σ, 0 < σ → σ < D.T → ∀ n,
    HasDerivAt
      (fun r => cosineCoeffs
        (fun x => p.ν * intervalDomainLift (D.u r) x ^ p.γ) n)
      (adotPow σ n) σ
  hadotPowCont : ∀ n, ContinuousOn (fun σ => adotPow σ n) (Set.Ioo 0 D.T)
  hMdotPow : ∀ a b, 0 < a → b < D.T →
    ∃ Mdot, ∀ σ ∈ Set.Icc a b, ∀ n, |adotPow σ n| ≤ Mdot

/-- Primitive producer-side resolver-source inputs produce the Task246 window
data. -/
theorem resolverSourceWindowData_of_inputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (H : ResolverSourceWindowInputs p D) :
    ShenWork.Paper2.ResolverSourceWitnessFrontier.ResolverSourceWindowData p D := by
  intro t₀ ht₀ ht₀T
  set c' : ℝ := t₀ / 4 with hc'def
  set c : ℝ := t₀ / 2 with hcdef
  set d : ℝ := (t₀ + D.T) / 2 with hddef
  set d' : ℝ := (t₀ + 3 * D.T) / 4 with hd'def
  have hc'c : c' < c := by
    rw [hc'def, hcdef]
    linarith
  have hct₀ : c < t₀ := by
    rw [hcdef]
    linarith
  have ht₀d : t₀ < d := by
    rw [hddef]
    linarith
  have hdd' : d < d' := by
    rw [hddef, hd'def]
    linarith
  have hc'pos : 0 < c' := by
    rw [hc'def]
    linarith
  have hd'T : d' < D.T := by
    rw [hd'def]
    linarith
  have hcd' : c' ≤ d' := le_of_lt (lt_trans hc'c (lt_trans hct₀ (lt_trans ht₀d hdd')))
  have hwin_open : ∀ σ ∈ Set.Icc c' d', 0 < σ ∧ σ < D.T := by
    intro σ hσ
    exact ⟨lt_of_lt_of_le hc'pos hσ.1, lt_of_le_of_lt hσ.2 hd'T⟩
  obtain ⟨m, hm, hlbW⟩ := H.hlower c' d' hc'pos hd'T hcd'
  obtain ⟨G1, hG1W⟩ := H.hG1 c' d' hc'pos hd'T
  obtain ⟨G2, hG2W⟩ := H.hG2 c' d' hc'pos hd'T
  have hbsumW : ∀ σ ∈ Set.Icc c' d',
      Summable (fun n => unitIntervalCosineEigenvalue n * |H.bc σ n|) := by
    intro σ hσ
    exact H.hbsum σ (hwin_open σ hσ).1 (hwin_open σ hσ).2
  have hagreeW : ∀ σ ∈ Set.Icc c' d',
      Set.EqOn (intervalDomainLift (D.u σ))
        (fun x => ∑' n, H.bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1) := by
    intro σ hσ
    exact H.hagree σ (hwin_open σ hσ).1 (hwin_open σ hσ).2
  have hposW : ∀ σ ∈ Set.Icc c' d',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (D.u σ) x := by
    intro σ hσ
    exact H.hpos σ (hwin_open σ hσ).1 (hwin_open σ hσ).2
  have hubW : ∀ σ ∈ Set.Icc c' d',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (D.u σ) x ≤ H.Msup := by
    intro σ hσ
    exact H.hub σ (hwin_open σ hσ).1 (hwin_open σ hσ).2
  obtain ⟨C, hC, hdecay, ha0⟩ :=
    ShenWork.Paper2.ResolverPowerDecay.powerSource_window_uniform_decay
      (ν := p.ν) (γ := p.γ) (M := H.Msup) (m := m)
      p.hν.le p.hγ hm hcd' H.bc hbsumW hagreeW hlbW hubW hG1W hG2W
  obtain ⟨Mdot, hMdotW⟩ := H.hMdotPow c' d' hc'pos hd'T
  have hderivW : ∀ σ ∈ Set.Icc c' d', ∀ n,
      HasDerivAt
        (fun r => cosineCoeffs
          (fun x => p.ν * intervalDomainLift (D.u r) x ^ p.γ) n)
        (H.adotPow σ n) σ := by
    intro σ hσ n
    exact H.hderivPow σ (hwin_open σ hσ).1 (hwin_open σ hσ).2 n
  have hadotcontW : ∀ n, ContinuousOn (fun σ => H.adotPow σ n) (Set.Icc c' d') := by
    intro n
    exact (H.hadotPowCont n).mono (fun σ hσ => hwin_open σ hσ)
  refine ⟨c', c, d, d', H.bc, C, H.adotPow, Mdot,
    hc'c, hct₀, ht₀d, hdd', hC, hbsumW, hagreeW, hposW,
    hdecay, ha0, hderivW, hadotcontW, hMdotW⟩

/-- Primitive inputs also directly produce the raw clamped resolver-source
witness. -/
theorem resolverSourceWitness_of_inputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (H : ResolverSourceWindowInputs p D) :
    ShenWork.Paper2.ResolverSourceWitnessFrontier.ResolverSourceWitness p D :=
  ShenWork.Paper2.ResolverSourceWitnessFrontier.resolverSourceWitness_of_windowData
    (resolverSourceWindowData_of_inputs H)

end ShenWork.Paper2.ResolverSourceWindowInput
