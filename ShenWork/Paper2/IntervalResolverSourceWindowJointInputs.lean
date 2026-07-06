/-
  ShenWork/Paper2/IntervalResolverSourceWindowJointInputs.lean

  Resolver-source primitive inputs with the elementary positivity, upper-bound,
  and compact lower-bound fields discharged from `GradientMildSolutionData` plus
  joint continuity of the lifted solution.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalResolverSourceWindowInputs

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)

noncomputable section

namespace ShenWork.Paper2.ResolverSourceWindowInput

/-- Resolver-source primitive inputs with the easy fields projected out.

Compared with `ResolverSourceWindowInputs`, this package replaces `hpos`,
`Msup`/`hub`, and `hlower` by joint continuity of the lifted solution on the
open-time, closed-space slab.  The pointwise positivity and upper bound then
come from `GradientMildSolutionData`, and the compact lower bound comes from
compactness. -/
structure ResolverSourceWindowJointInputs
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) where
  bc : ℝ → ℕ → ℝ
  hbsum : ∀ σ, 0 < σ → σ < D.T →
    Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|)
  hagree : ∀ σ, 0 < σ → σ < D.T →
    Set.EqOn (intervalDomainLift (D.u σ))
      (fun x => ∑' n, bc σ n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1)
  hliftCont :
    ContinuousOn
      (Function.uncurry
        (fun (σ : ℝ) (x : ℝ) => intervalDomainLift (D.u σ) x))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1)
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

/-- Joint continuity plus `GradientMildSolutionData.hpos` gives the compact
window positive lower bound required by `ResolverSourceWindowInputs`. -/
theorem compactLower_of_jointContinuous
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (hliftCont :
      ContinuousOn
        (Function.uncurry
          (fun (σ : ℝ) (x : ℝ) => intervalDomainLift (D.u σ) x))
        (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ∀ a b, 0 < a → b < D.T → a ≤ b →
      ∃ m : ℝ, 0 < m ∧
        ∀ σ ∈ Set.Icc a b, ∀ x ∈ Set.Icc (0 : ℝ) 1,
          m ≤ intervalDomainLift (D.u σ) x := by
  intro a b ha hb hab
  classical
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
    hliftCont.mono hsub
  obtain ⟨q₀, hq₀_mem, hq₀_min⟩ :=
    hKcompact.exists_isMinOn hKne hcontK
  obtain ⟨σ₀, x₀⟩ := q₀
  obtain ⟨hσ₀_mem, hx₀_mem⟩ := Set.mem_prod.mp hq₀_mem
  have hσ₀_open : 0 < σ₀ ∧ σ₀ < D.T :=
    ⟨lt_of_lt_of_le ha hσ₀_mem.1, lt_of_le_of_lt hσ₀_mem.2 hb⟩
  have hmin_pos : 0 < intervalDomainLift (D.u σ₀) x₀ := by
    simp only [intervalDomainLift, dif_pos hx₀_mem]
    exact D.hpos σ₀ hσ₀_open.1 (le_of_lt hσ₀_open.2) ⟨x₀, hx₀_mem⟩
  refine ⟨intervalDomainLift (D.u σ₀) x₀, hmin_pos, ?_⟩
  intro σ hσ x hx
  exact isMinOn_iff.mp hq₀_min (σ, x) (Set.mem_prod.mpr ⟨hσ, hx⟩)

/-- Joint-continuity primitive inputs produce the Task255 primitive inputs. -/
def resolverSourceWindowInputs_of_jointInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (H : ResolverSourceWindowJointInputs p D) :
    ResolverSourceWindowInputs p D where
  bc := H.bc
  hbsum := H.hbsum
  hagree := H.hagree
  hpos := by
    intro σ hσ hσT x hx
    simp only [intervalDomainLift, dif_pos hx]
    exact D.hpos σ hσ (le_of_lt hσT) ⟨x, hx⟩
  Msup := D.M
  hub := by
    intro σ hσ hσT x hx
    simp only [intervalDomainLift, dif_pos hx]
    exact le_trans (le_abs_self _) (D.hbound σ hσ (le_of_lt hσT) ⟨x, hx⟩)
  hlower := compactLower_of_jointContinuous H.hliftCont
  hG1 := H.hG1
  hG2 := H.hG2
  adotPow := H.adotPow
  hderivPow := H.hderivPow
  hadotPowCont := H.hadotPowCont
  hMdotPow := H.hMdotPow

/-- Joint-continuity primitive inputs produce the Task246 window data. -/
theorem resolverSourceWindowData_of_jointInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (H : ResolverSourceWindowJointInputs p D) :
    ShenWork.Paper2.ResolverSourceWitnessFrontier.ResolverSourceWindowData p D :=
  resolverSourceWindowData_of_inputs
    (resolverSourceWindowInputs_of_jointInputs H)

/-- Joint-continuity primitive inputs also produce the raw clamped
resolver-source witness. -/
theorem resolverSourceWitness_of_jointInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (H : ResolverSourceWindowJointInputs p D) :
    ShenWork.Paper2.ResolverSourceWitnessFrontier.ResolverSourceWitness p D :=
  resolverSourceWitness_of_inputs
    (resolverSourceWindowInputs_of_jointInputs H)

end ShenWork.Paper2.ResolverSourceWindowInput
