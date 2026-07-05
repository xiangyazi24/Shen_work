import ShenWork.Paper2.IntervalChiNegH1WindowWiring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# H¹ average wiring from a scalar differential inequality

This file is scalar analysis only.  It converts a carried differential
inequality for `H1energy` into the averaged input consumed by the restricted
H¹-window assembly.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1WindowWiring
open ShenWork.IntervalDomainExistence.P3Moser1DBypassAssembly

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1AverageWiring

/-- Scalar H¹ differential inequality data on the time slab `(0,T)`.

The endpoint `τ = 1` starts at `0`, so continuity and integrability are stated
on closed windows with nonnegative left endpoint.  The derivative inequality is
only used on open interiors. -/
structure H1ScalarDIOnBefore
    (u : ℝ → intervalDomainPoint → ℝ) (T A B : ℝ) : Prop where
  hA : 0 ≤ A
  hB : 0 ≤ B
  hcont : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
    ContinuousOn (H1energy u) (Set.Icc a b)
  hderivInt : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
    IntervalIntegrable (fun r => deriv (H1energy u) r) volume a b
  hhasDerivRight : ∀ {a b r : ℝ}, 0 ≤ a → a ≤ b → b < T →
    r ∈ Set.Ioo a b →
      HasDerivWithinAt (H1energy u)
        (deriv (H1energy u) r) (Set.Ioi r) r
  hDI : ∀ r, 0 < r → r < T →
    deriv (H1energy u) r ≤ A * H1energy u r + B

/-- A nonnegative H¹ subwindow is bounded by the full one-unit window. -/
theorem H1Window_subinterval_le
    {u : ℝ → intervalDomainPoint → ℝ} {τ σ : ℝ}
    (hσ : σ ∈ Set.Icc (τ - 1) τ)
    (hcont : ContinuousOn (H1energy u) (Set.Icc (τ - 1) τ)) :
    (∫ r in σ..τ, H1energy u r) ≤ H1Window u τ := by
  have hleft_int :
      IntervalIntegrable (fun r => H1energy u r) volume (τ - 1) σ := by
    have hcont_left :
        ContinuousOn (H1energy u) (Set.Icc (τ - 1) σ) :=
      hcont.mono (fun r hr => ⟨hr.1, le_trans hr.2 hσ.2⟩)
    exact hcont_left.intervalIntegrable_of_Icc hσ.1
  have hright_int :
      IntervalIntegrable (fun r => H1energy u r) volume σ τ := by
    have hcont_right :
        ContinuousOn (H1energy u) (Set.Icc σ τ) :=
      hcont.mono (fun r hr => ⟨le_trans hσ.1 hr.1, hr.2⟩)
    exact hcont_right.intervalIntegrable_of_Icc hσ.2
  have hleft_nonneg :
      0 ≤ ∫ r in (τ - 1)..σ, H1energy u r :=
    intervalIntegral.integral_nonneg hσ.1
      (fun r _hr => H1energy_nonneg u r)
  have hsplit :
      (∫ r in (τ - 1)..σ, H1energy u r) +
          ∫ r in σ..τ, H1energy u r =
        H1Window u τ := by
    simpa [H1Window] using
      (intervalIntegral.integral_add_adjacent_intervals
        hleft_int hright_int)
  linarith

/-- Integrate the scalar H¹ differential inequality from `σ` to `τ` and bound
the result by the full one-unit window. -/
theorem H1_backward_bound_of_scalarDI_before
    {u : ℝ → intervalDomainPoint → ℝ} {T A B τ σ : ℝ}
    (hDI : H1ScalarDIOnBefore u T A B)
    (hτ1 : 1 ≤ τ) (hτT : τ < T)
    (hσ : σ ∈ Set.Icc (τ - 1) τ) :
    H1energy u τ ≤ H1energy u σ + (A * H1Window u τ + B) := by
  have hσ0 : 0 ≤ σ := by linarith [hτ1, hσ.1]
  have hστ : σ ≤ τ := hσ.2
  have hcontστ : ContinuousOn (H1energy u) (Set.Icc σ τ) :=
    hDI.hcont hσ0 hστ hτT
  have hH1int :
      IntervalIntegrable (fun r => H1energy u r) volume σ τ :=
    hcontστ.intervalIntegrable_of_Icc hστ
  have hderivInt :
      IntervalIntegrable (fun r => deriv (H1energy u) r) volume σ τ :=
    hDI.hderivInt hσ0 hστ hτT
  have hFTC :
      (∫ r in σ..τ, deriv (H1energy u) r) =
        H1energy u τ - H1energy u σ := by
    exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      hστ hcontστ (fun r hr => hDI.hhasDerivRight hσ0 hστ hτT hr)
      hderivInt
  have hrhsInt :
      IntervalIntegrable (fun r => A * H1energy u r + B) volume σ τ :=
    (hH1int.const_mul A).add intervalIntegral.intervalIntegrable_const
  have hmono :
      (∫ r in σ..τ, deriv (H1energy u) r) ≤
        ∫ r in σ..τ, A * H1energy u r + B :=
    intervalIntegral.integral_mono_on_of_le_Ioo hστ hderivInt hrhsInt
      (fun r hr => by
        have hr0 : 0 < r := lt_of_le_of_lt hσ0 hr.1
        have hrT : r < T := lt_trans hr.2 hτT
        exact hDI.hDI r hr0 hrT)
  have hrhs_eval :
      (∫ r in σ..τ, A * H1energy u r + B) =
        A * (∫ r in σ..τ, H1energy u r) + B * (τ - σ) := by
    rw [intervalIntegral.integral_add
      (hH1int.const_mul A) intervalIntegral.intervalIntegrable_const]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp [smul_eq_mul]
    ring_nf
  have hfull_cont :
      ContinuousOn (H1energy u) (Set.Icc (τ - 1) τ) :=
    hDI.hcont (by linarith [hτ1]) (by linarith) hτT
  have hsub :
      (∫ r in σ..τ, H1energy u r) ≤ H1Window u τ :=
    H1Window_subinterval_le hσ hfull_cont
  have hA_sub :
      A * (∫ r in σ..τ, H1energy u r) ≤ A * H1Window u τ :=
    mul_le_mul_of_nonneg_left hsub hDI.hA
  have hB_len : B * (τ - σ) ≤ B := by
    have hlen : τ - σ ≤ 1 := by linarith [hσ.1]
    have hlen_nonneg : 0 ≤ τ - σ := by linarith [hσ.2]
    nlinarith [mul_le_mul_of_nonneg_left hlen hDI.hB, hlen_nonneg]
  have hmain :
      H1energy u τ - H1energy u σ ≤ A * H1Window u τ + B := by
    calc
      H1energy u τ - H1energy u σ
          = ∫ r in σ..τ, deriv (H1energy u) r := hFTC.symm
      _ ≤ ∫ r in σ..τ, A * H1energy u r + B := hmono
      _ = A * (∫ r in σ..τ, H1energy u r) + B * (τ - σ) := hrhs_eval
      _ ≤ A * H1Window u τ + B := by linarith
  linarith

/-- Average the backward-in-time bound over the one-unit window to produce the
exact `havg` shape consumed by `chiNeg_H1_norm_bound_before`. -/
theorem H1_avg_of_backwards_bound
    {u : ℝ → intervalDomainPoint → ℝ} {A B τ : ℝ}
    (hcont : ContinuousOn (H1energy u) (Set.Icc (τ - 1) τ))
    (hback : ∀ σ, σ ∈ Set.Icc (τ - 1) τ →
      H1energy u τ ≤ H1energy u σ + (A * H1Window u τ + B)) :
    1 * H1energy u τ ≤
      H1Window u τ + 1 * (A * H1Window u τ + B * 1) := by
  have hab : τ - 1 ≤ τ := by linarith
  have hH1int :
      IntervalIntegrable (fun s => H1energy u s) volume (τ - 1) τ :=
    hcont.intervalIntegrable_of_Icc hab
  exact H1_avg_of_pointwise_window_bound
    (u := u) (τ := τ) (A := A) (B := B)
    (fun s hs => hback s ⟨le_of_lt hs.1, le_of_lt hs.2⟩)
    hH1int

/-- Task 41B reducer: a scoped scalar H¹ differential inequality produces the
`havg` input for the restricted H¹-window assembly. -/
theorem H1_avg_of_scalarDI_before
    {u : ℝ → intervalDomainPoint → ℝ} {T A B : ℝ}
    (hDI : H1ScalarDIOnBefore u T A B) :
    ∀ τ, 1 ≤ τ → τ < T →
      1 * H1energy u τ ≤
        H1Window u τ + 1 * (A * H1Window u τ + B * 1) := by
  intro τ hτ1 hτT
  have hcont : ContinuousOn (H1energy u) (Set.Icc (τ - 1) τ) :=
    hDI.hcont (by linarith [hτ1]) (by linarith) hτT
  exact H1_avg_of_backwards_bound hcont
    (fun σ hσ => H1_backward_bound_of_scalarDI_before hDI hτ1 hτT hσ)

/-- Bridge from `H1ScalarDIOnBefore` to the paper-positive H¹-local-average bypass
assembler. -/
theorem intervalDomain_boundedBefore_of_paperPositive_H1scalarDI_local
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {A B Ylocal : ℝ}
    (hDI : H1ScalarDIOnBefore u T A B)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have havg : ∀ τ, 1 ≤ τ → τ < T →
      1 * H1energy u τ ≤
        (∫ s in (τ - 1)..τ, H1energy u s) +
          1 * (A * (∫ s in (τ - 1)..τ, H1energy u s) + B * 1) := by
    intro τ hτ1 hτT
    simpa [H1Window] using H1_avg_of_scalarDI_before hDI τ hτ1 hτT
  exact intervalDomain_boundedBefore_of_paperPositive_H1local_average
    hbounded ha hu₀ hT hsol htrace hfrontier hDI.hA hlocal havg

#print axioms H1Window_subinterval_le
#print axioms H1_backward_bound_of_scalarDI_before
#print axioms H1_avg_of_backwards_bound
#print axioms H1_avg_of_scalarDI_before
#print axioms intervalDomain_boundedBefore_of_paperPositive_H1scalarDI_local

end ShenWork.Paper2.IntervalChiNegH1AverageWiring
