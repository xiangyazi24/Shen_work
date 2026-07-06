/-
  ShenWork/Paper2/IntervalResolverSourceWindowInputsNoLower.lean

  Resolver-source primitive inputs with the compact lower-bound field discharged
  from the u-side time-neighborhood spectral agreement.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalResolverSourceWindowInputs
import ShenWork.PDE.IntervalMildFrontierFromSpectral

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)

noncomputable section

namespace ShenWork.Paper2.ResolverSourceWindowInput

/-- Primitive resolver-source inputs with the compact positive lower bound
removed.  That field is derivable from the sibling u-side
`HasTimeNeighborhoodSpectralAgreement` plus pointwise positivity. -/
structure ResolverSourceWindowInputsNoLower
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

/-- Compact lower bounds follow from u-side spectral neighborhood agreement,
which gives joint continuity of the lift on the open-time closed-space slab, and
strict positivity on that slab. -/
theorem compactLower_of_timeNeighborhoodSpectral
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u)
    (hpos : ∀ σ, 0 < σ → σ < D.T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (D.u σ) x) :
    ∀ a b, 0 < a → b < D.T → a ≤ b →
      ∃ m : ℝ, 0 < m ∧
        ∀ σ ∈ Set.Icc a b, ∀ x ∈ Set.Icc (0 : ℝ) 1,
          m ≤ intervalDomainLift (D.u σ) x := by
  intro a b ha hb hab
  classical
  have hjoint : ContinuousOn
      (Function.uncurry
        (fun (σ : ℝ) (x : ℝ) => intervalDomainLift (D.u σ) x))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) :=
    ShenWork.IntervalMildFrontierFromSpectral.mildSolution_jointContinuousOn_closed Hu
  have hKcompact : IsCompact (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hKne : (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1).Nonempty :=
    ⟨(a, 0), ⟨Set.left_mem_Icc.mpr hab, by constructor <;> norm_num⟩⟩
  have hsub : Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1 ⊆
      Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1 := by
    rintro ⟨σ, x⟩ ⟨hσ, hx⟩
    exact ⟨⟨lt_of_lt_of_le ha hσ.1, lt_of_le_of_lt hσ.2 hb⟩, hx⟩
  have hcontK : ContinuousOn
      (Function.uncurry
        (fun (σ : ℝ) (x : ℝ) => intervalDomainLift (D.u σ) x))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    hjoint.mono hsub
  obtain ⟨q₀, hq₀_mem, hq₀_min⟩ :=
    hKcompact.exists_isMinOn hKne hcontK
  obtain ⟨σ₀, x₀⟩ := q₀
  obtain ⟨hσ₀_mem, hx₀_mem⟩ := Set.mem_prod.mp hq₀_mem
  have hσ₀_open : 0 < σ₀ ∧ σ₀ < D.T :=
    ⟨lt_of_lt_of_le ha hσ₀_mem.1, lt_of_le_of_lt hσ₀_mem.2 hb⟩
  have hmin_pos : 0 < intervalDomainLift (D.u σ₀) x₀ :=
    hpos σ₀ hσ₀_open.1 hσ₀_open.2 x₀ hx₀_mem
  refine ⟨intervalDomainLift (D.u σ₀) x₀, hmin_pos, ?_⟩
  intro σ hσ x hx
  exact isMinOn_iff.mp hq₀_min (σ, x) (Set.mem_prod.mpr ⟨hσ, hx⟩)

/-- Add the derived compact lower-bound field to a no-lower primitive input
package. -/
def resolverSourceWindowInputs_of_noLower
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u)
    (H : ResolverSourceWindowInputsNoLower p D) :
    ResolverSourceWindowInputs p D where
  bc := H.bc
  hbsum := H.hbsum
  hagree := H.hagree
  hpos := H.hpos
  Msup := H.Msup
  hub := H.hub
  hlower := compactLower_of_timeNeighborhoodSpectral Hu H.hpos
  hG1 := H.hG1
  hG2 := H.hG2
  adotPow := H.adotPow
  hderivPow := H.hderivPow
  hadotPowCont := H.hadotPowCont
  hMdotPow := H.hMdotPow

/-- No-lower primitive inputs, together with the u-side spectral agreement,
produce the Task246 window data. -/
theorem resolverSourceWindowData_of_noLower
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u)
    (H : ResolverSourceWindowInputsNoLower p D) :
    ShenWork.Paper2.ResolverSourceWitnessFrontier.ResolverSourceWindowData p D :=
  resolverSourceWindowData_of_inputs
    (resolverSourceWindowInputs_of_noLower Hu H)

/-- No-lower primitive inputs also produce the raw clamped resolver-source
witness. -/
theorem resolverSourceWitness_of_noLower
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u)
    (H : ResolverSourceWindowInputsNoLower p D) :
    ShenWork.Paper2.ResolverSourceWitnessFrontier.ResolverSourceWitness p D :=
  resolverSourceWitness_of_inputs
    (resolverSourceWindowInputs_of_noLower Hu H)

end ShenWork.Paper2.ResolverSourceWindowInput
