/-
  ShenWork/Paper2/IntervalResolverSourceWindowEnvelopeInputs.lean

  Resolver-source primitive inputs with spatial K2 fields discharged from a
  per-compact eigenvalue envelope for the chosen cosine coefficients.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalResolverSourceWindowJointInputs
import ShenWork.Paper2.IntervalCompactSliceGradientBounds

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)

noncomputable section

namespace ShenWork.Paper2.ResolverSourceWindowInput

/-- Joint-continuity resolver-source inputs with the spatial K2 bounds replaced
by a compact-window eigenvalue envelope for the chosen cosine coefficients. -/
structure ResolverSourceWindowEnvelopeInputs
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
  henv : ∀ a b, 0 < a → b < D.T → a ≤ b →
    ∃ E : ℕ → ℝ,
      Summable E ∧
      (∀ n, 0 ≤ E n) ∧
      (∀ σ ∈ Set.Icc a b, ∀ n,
        unitIntervalCosineEigenvalue n * |bc σ n| ≤ E n)
  adotPow : ℝ → ℕ → ℝ
  hderivPow : ∀ σ, 0 < σ → σ < D.T → ∀ n,
    HasDerivAt
      (fun r => cosineCoeffs
        (fun x => p.ν * intervalDomainLift (D.u r) x ^ p.γ) n)
      (adotPow σ n) σ
  hadotPowCont : ∀ n, ContinuousOn (fun σ => adotPow σ n) (Set.Ioo 0 D.T)
  hMdotPow : ∀ a b, 0 < a → b < D.T →
    ∃ Mdot, ∀ σ ∈ Set.Icc a b, ∀ n, |adotPow σ n| ≤ Mdot

/-- A compact-window eigenvalue envelope gives the first spatial derivative
bound required by `ResolverSourceWindowJointInputs`. -/
theorem hG1_of_envelope
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < D.T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < D.T →
      Set.EqOn (intervalDomainLift (D.u σ))
        (fun x => ∑' n, bc σ n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (henv : ∀ a b, 0 < a → b < D.T → a ≤ b →
      ∃ E : ℕ → ℝ,
        Summable E ∧
        (∀ n, 0 ≤ E n) ∧
        (∀ σ ∈ Set.Icc a b, ∀ n,
          unitIntervalCosineEigenvalue n * |bc σ n| ≤ E n)) :
    ∀ a b, 0 < a → b < D.T →
      ∃ G1, ∀ σ ∈ Set.Icc a b, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (intervalDomainLift (D.u σ)) x| ≤ G1 := by
  intro a b ha hb
  by_cases hab : a ≤ b
  · obtain ⟨E, hEsum, hEnn, hdom⟩ := henv a b ha hb hab
    refine ⟨∑' n, E n, ?_⟩
    intro σ hσ x hx
    have hσpos : 0 < σ := lt_of_lt_of_le ha hσ.1
    have hσT : σ < D.T := lt_of_le_of_lt hσ.2 hb
    have hGnn : 0 ≤ ∑' n, E n := tsum_nonneg hEnn
    have hgrad_bound :
        |∑' n, bc σ n * (-((n : ℝ) * Real.pi) *
            Real.sin ((n : ℝ) * Real.pi * x))| ≤ ∑' n, E n :=
      ShenWork.Paper2.CompactSliceGradientBounds.grad_series_abs_le
        (fun n => bc σ n) E x hEsum (hdom σ hσ)
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    · have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
        Set.left_mem_Icc.mpr zero_le_one
      have hval : 0 < intervalDomainLift (D.u σ) 0 := by
        simpa [intervalDomainLift, h0] using
          D.hpos σ hσpos hσT.le ⟨0, h0⟩
      have hnd : ¬ DifferentiableAt ℝ (intervalDomainLift (D.u σ)) x := by
        rw [← hx0]
        exact ShenWork.Paper2.CompactSliceGradientBounds.not_differentiableAt_lift_left
          D.u σ hval
      rw [deriv_zero_of_not_differentiableAt hnd, abs_zero]
      exact hGnn
    · rcases eq_or_lt_of_le hx.2 with hx1 | hx1
      · have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
          Set.right_mem_Icc.mpr zero_le_one
        have hval : 0 < intervalDomainLift (D.u σ) 1 := by
          simpa [intervalDomainLift, h1] using
            D.hpos σ hσpos hσT.le ⟨1, h1⟩
        have hnd : ¬ DifferentiableAt ℝ (intervalDomainLift (D.u σ)) x := by
          rw [hx1]
          exact ShenWork.Paper2.CompactSliceGradientBounds.not_differentiableAt_lift_right
            D.u σ hval
        rw [deriv_zero_of_not_differentiableAt hnd, abs_zero]
        exact hGnn
      · have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
        have hEq : intervalDomainLift (D.u σ) =ᶠ[nhds x]
            (fun y => ∑' n, bc σ n * cosineMode n y) := by
          have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhds x := isOpen_Ioo.mem_nhds hxIoo
          filter_upwards [hmem] with y hy
          exact hagree σ hσpos hσT (Set.Ioo_subset_Icc_self hy)
        rw [hEq.deriv_eq,
          (ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_grad_hasDerivAt
            (hbsum σ hσpos hσT) x).deriv]
        exact hgrad_bound
  · refine ⟨0, ?_⟩
    intro σ hσ
    exact False.elim (hab (le_trans hσ.1 hσ.2))

/-- A compact-window eigenvalue envelope gives the second spatial derivative
bound required by `ResolverSourceWindowJointInputs`. -/
theorem hG2_of_envelope
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < D.T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < D.T →
      Set.EqOn (intervalDomainLift (D.u σ))
        (fun x => ∑' n, bc σ n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (henv : ∀ a b, 0 < a → b < D.T → a ≤ b →
      ∃ E : ℕ → ℝ,
        Summable E ∧
        (∀ n, 0 ≤ E n) ∧
        (∀ σ ∈ Set.Icc a b, ∀ n,
          unitIntervalCosineEigenvalue n * |bc σ n| ≤ E n)) :
    ∀ a b, 0 < a → b < D.T →
      ∃ G2, ∀ σ ∈ Set.Icc a b, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (deriv (intervalDomainLift (D.u σ))) x| ≤ G2 := by
  intro a b ha hb
  by_cases hab : a ≤ b
  · obtain ⟨E, hEsum, hEnn, hdom⟩ := henv a b ha hb hab
    refine ⟨∑' n, E n, ?_⟩
    intro σ hσ x hx
    have hσpos : 0 < σ := lt_of_lt_of_le ha hσ.1
    have hσT : σ < D.T := lt_of_le_of_lt hσ.2 hb
    have hGnn : 0 ≤ ∑' n, E n := tsum_nonneg hEnn
    have hgrad2_bound :
        |∑' n, bc σ n * (-(((n : ℝ) * Real.pi) ^ 2) *
            Real.cos ((n : ℝ) * Real.pi * x))| ≤ ∑' n, E n :=
      ShenWork.Paper2.CompactSliceGradientBounds.grad2_series_abs_le
        (fun n => bc σ n) E x hEsum (hdom σ hσ)
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    · rw [← hx0,
        ShenWork.Paper2.CompactSliceGradientBounds.deriv2_lift_eq_zero_left D.u σ,
        abs_zero]
      exact hGnn
    · rcases eq_or_lt_of_le hx.2 with hx1 | hx1
      · rw [hx1,
          ShenWork.Paper2.CompactSliceGradientBounds.deriv2_lift_eq_zero_right D.u σ,
          abs_zero]
        exact hGnn
      · have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
        have hEq : intervalDomainLift (D.u σ) =ᶠ[nhds x]
            (fun y => ∑' n, bc σ n * cosineMode n y) := by
          have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhds x := isOpen_Ioo.mem_nhds hxIoo
          filter_upwards [hmem] with y hy
          exact hagree σ hσpos hσT (Set.Ioo_subset_Icc_self hy)
        have hderiv_eq : deriv (intervalDomainLift (D.u σ)) =ᶠ[nhds x]
            deriv (fun y => ∑' n, bc σ n * cosineMode n y) :=
          hEq.deriv
        rw [hderiv_eq.deriv_eq,
          ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv2_eq
            (hbsum σ hσpos hσT) x]
        exact hgrad2_bound
  · refine ⟨0, ?_⟩
    intro σ hσ
    exact False.elim (hab (le_trans hσ.1 hσ.2))

/-- Envelope primitive inputs produce the Task259 joint-continuity primitive
inputs. -/
def resolverSourceWindowJointInputs_of_envelopeInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (H : ResolverSourceWindowEnvelopeInputs p D) :
    ResolverSourceWindowJointInputs p D where
  bc := H.bc
  hbsum := H.hbsum
  hagree := H.hagree
  hliftCont := H.hliftCont
  hG1 := hG1_of_envelope H.bc H.hbsum H.hagree H.henv
  hG2 := hG2_of_envelope H.bc H.hbsum H.hagree H.henv
  adotPow := H.adotPow
  hderivPow := H.hderivPow
  hadotPowCont := H.hadotPowCont
  hMdotPow := H.hMdotPow

/-- Envelope primitive inputs produce the Task255 primitive inputs. -/
def resolverSourceWindowInputs_of_envelopeInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (H : ResolverSourceWindowEnvelopeInputs p D) :
    ResolverSourceWindowInputs p D :=
  resolverSourceWindowInputs_of_jointInputs
    (resolverSourceWindowJointInputs_of_envelopeInputs H)

/-- Envelope primitive inputs produce the Task246 window data. -/
theorem resolverSourceWindowData_of_envelopeInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (H : ResolverSourceWindowEnvelopeInputs p D) :
    ShenWork.Paper2.ResolverSourceWitnessFrontier.ResolverSourceWindowData p D :=
  resolverSourceWindowData_of_jointInputs
    (resolverSourceWindowJointInputs_of_envelopeInputs H)

/-- Envelope primitive inputs also produce the raw clamped resolver-source
witness. -/
theorem resolverSourceWitness_of_envelopeInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (H : ResolverSourceWindowEnvelopeInputs p D) :
    ShenWork.Paper2.ResolverSourceWitnessFrontier.ResolverSourceWitness p D :=
  resolverSourceWitness_of_jointInputs
    (resolverSourceWindowJointInputs_of_envelopeInputs H)

end ShenWork.Paper2.ResolverSourceWindowInput
