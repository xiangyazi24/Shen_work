import ShenWork.PDE.P3Moser1DBypassAssembly
import ShenWork.Paper2.IntervalSingleSolutionL2Window

/-!
# H¹ sliding-window wiring on the interval domain

This file removes the carried H¹ window input from the 1D bounded-before route:
the window is supplied by `singleSolution_H1_window_bound`.  The local H¹ start
and averaged H¹ differential inequality remain explicit.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalSingleSolutionL2Window
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3Moser1DBypassAssembly

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1WindowWiring

/-- The one-unit sliding window of the H¹ seminorm energy. -/
def H1Window (u : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) : ℝ :=
  ∫ s in (τ - 1)..τ, H1energy u s

/-- The H¹ window is nonnegative for windows oriented from `τ - 1` to `τ`. -/
theorem H1Window_nonneg
    {u : ℝ → intervalDomainPoint → ℝ} {τ : ℝ} :
    0 ≤ H1Window u τ := by
  unfold H1Window
  exact intervalIntegral.integral_nonneg (by linarith)
    (fun s _hs => H1energy_nonneg u s)

/-- The landed single-solution L² window theorem, rewritten using `H1Window`. -/
theorem H1Window_bound_of_singleSolution_H1_window_bound
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (habsorbing :
      IntervalDomainL2AbsorbingDifferentialInequalityResult p T u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {Y_L2 : ℝ}
    (hL2 : ∀ τ, 0 < τ → τ < T → L2energy u τ ≤ Y_L2) :
    ∃ C, 0 ≤ C ∧ ∀ τ, 1 ≤ τ → τ < T → H1Window u τ ≤ C := by
  rcases singleSolution_H1_window_bound hsol habsorbing hfrontier hL2 with
    ⟨C, hC, hwin⟩
  refine ⟨C, hC, ?_⟩
  intro τ hτ1 hτT
  simpa [H1Window] using hwin τ hτ1 hτT

/-- Restricted-time version of `chiNeg_H1_norm_bound`.

This is the same averaging proof, but all carried inputs are scoped to the
classical solution interval `0 < τ < T`. -/
theorem chiNeg_H1_norm_bound_before
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (_hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {A B C Ylocal : ℝ} (hA : 0 ≤ A) {W : ℝ → ℝ}
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal)
    (havg : ∀ τ, 1 ≤ τ → τ < T →
      1 * H1energy u τ ≤ W τ + 1 * (A * W τ + B * 1))
    (hwin : ∀ τ, 1 ≤ τ → τ < T → W τ ≤ C)
    (hWnn : ∀ τ, 1 ≤ τ → τ < T → 0 ≤ W τ) :
    ∀ τ, 0 < τ → τ < T →
      H1energy u τ ≤ max Ylocal ((1 + A) * C + B) := by
  intro τ hτ0 hτT
  rcases le_or_gt τ 1 with hτ1 | hτ1
  · exact le_trans (hlocal τ ⟨hτ0, hτ1⟩ hτT) (le_max_left _ _)
  · have h1 := uniform_bound_of_window_le
      (ytR := H1energy u τ) (W := W τ)
      (A := A) (B := B) (R := 1) (C := C)
      one_pos hA (hWnn τ hτ1.le hτT)
      (hwin τ hτ1.le hτT) (havg τ hτ1.le hτT)
    have hsimp : C / 1 + A * C + B * 1 = (1 + A) * C + B := by
      ring
    rw [hsimp] at h1
    exact le_trans h1 (le_max_right _ _)

/-- H¹ bound on `(0,T)` after replacing the carried window input by the landed
single-solution L² window theorem.

Remaining carried H¹ inputs are exactly the local start and averaged
differential inequality. -/
theorem H1_bound_before_of_singleSolution_window
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (habsorbing :
      IntervalDomainL2AbsorbingDifferentialInequalityResult p T u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {Y_L2 : ℝ}
    (hL2 : ∀ τ, 0 < τ → τ < T → L2energy u τ ≤ Y_L2)
    {A B Ylocal : ℝ} (hA : 0 ≤ A)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal)
    (havg : ∀ τ, 1 ≤ τ → τ < T →
      1 * H1energy u τ ≤
        H1Window u τ + 1 * (A * H1Window u τ + B * 1)) :
    ∃ Y₁, 0 ≤ Y₁ ∧
      ∀ τ, 0 < τ → τ < T → H1energy u τ ≤ Y₁ := by
  rcases H1Window_bound_of_singleSolution_H1_window_bound
      hsol habsorbing hfrontier hL2 with
    ⟨C, _hC, hwin⟩
  let Yraw : ℝ := max Ylocal ((1 + A) * C + B)
  refine ⟨max 0 Yraw, le_max_left _ _, ?_⟩
  have hWnn : ∀ τ, 1 ≤ τ → τ < T → 0 ≤ H1Window u τ := by
    intro τ _hτ1 _hτT
    exact H1Window_nonneg
  have hbefore := chiNeg_H1_norm_bound_before
    (p := p) (T := T) (u := u) (v := v)
    hsol hA (W := H1Window u)
    hlocal havg hwin hWnn
  intro τ hτ0 hτT
  exact le_trans (hbefore τ hτ0 hτT) (le_max_right _ _)

/-- Averaging bridge for the H¹ route.

If every interior start point `s ∈ (τ - 1, τ)` gives the pointwise integrated
bound `y τ ≤ y s + A * W + B`, then averaging in `s` gives exactly the `havg`
input used by the window wiring. -/
theorem H1_avg_of_pointwise_window_bound
    {u : ℝ → intervalDomainPoint → ℝ} {τ A B : ℝ}
    (hpoint : ∀ s, s ∈ Set.Ioo (τ - 1) τ →
      H1energy u τ ≤ H1energy u s + (A * H1Window u τ + B))
    (hH1int :
      IntervalIntegrable (fun s => H1energy u s) MeasureTheory.volume
        (τ - 1) τ) :
    1 * H1energy u τ ≤
      H1Window u τ + 1 * (A * H1Window u τ + B * 1) := by
  let K : ℝ := A * H1Window u τ + B
  have hab : τ - 1 ≤ τ := by linarith
  have hleft_int :
      IntervalIntegrable (fun _s : ℝ => H1energy u τ)
        MeasureTheory.volume (τ - 1) τ :=
    intervalIntegral.intervalIntegrable_const
  have hright_int :
      IntervalIntegrable (fun s => H1energy u s + K)
        MeasureTheory.volume (τ - 1) τ :=
    hH1int.add intervalIntegral.intervalIntegrable_const
  have hmono :
      (∫ s in (τ - 1)..τ, H1energy u τ) ≤
        ∫ s in (τ - 1)..τ, H1energy u s + K :=
    intervalIntegral.integral_mono_on_of_le_Ioo
      hab hleft_int hright_int (fun s hs => by
        simpa [K] using hpoint s hs)
  have hleft_eq :
      (∫ s in (τ - 1)..τ, H1energy u τ) = H1energy u τ := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  have hright_eq :
      (∫ s in (τ - 1)..τ, H1energy u s + K) = H1Window u τ + K := by
    rw [intervalIntegral.integral_add hH1int intervalIntegral.intervalIntegrable_const]
    rw [intervalIntegral.integral_const]
    simp [H1Window, smul_eq_mul]
  have hmain : H1energy u τ ≤ H1Window u τ + K := by
    simpa [hleft_eq, hright_eq] using hmono
  dsimp [K] at hmain
  linarith

/-- Task-41-facing composition: use the landed window theorem to discharge the
H¹-window carry, then close bounded-before through the 1D bypass. -/
theorem intervalDomain_boundedBefore_of_L2Window_H1local_H1avg_and_Lp2
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hlogistic : 2 * p.γ < p.α)
    (habsorbing :
      IntervalDomainL2AbsorbingDifferentialInequalityResult p T u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {Y_L2 : ℝ}
    (hL2 : ∀ τ, 0 < τ → τ < T → L2energy u τ ≤ Y_L2)
    {A B Ylocal : ℝ} (hA : 0 ≤ A)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal)
    (havg : ∀ τ, 1 ≤ τ → τ < T →
      1 * H1energy u τ ≤
        H1Window u τ + 1 * (A * H1Window u τ + B * 1))
    (hLp2 : LpPowerBoundedBefore intervalDomain 2 T u) :
    IsPaper2BoundedBefore intervalDomain T u := by
  rcases H1_bound_before_of_singleSolution_window
      hsol habsorbing hfrontier hL2 hA hlocal havg with
    ⟨Y₁, hY₁, hH1bnd⟩
  exact intervalDomain_boundedBefore_of_H1bound_and_L2seed_logistic
    hsol hlogistic hY₁ hH1bnd hLp2

#print axioms H1Window_nonneg
#print axioms H1Window_bound_of_singleSolution_H1_window_bound
#print axioms chiNeg_H1_norm_bound_before
#print axioms H1_bound_before_of_singleSolution_window
#print axioms H1_avg_of_pointwise_window_bound
#print axioms intervalDomain_boundedBefore_of_L2Window_H1local_H1avg_and_Lp2

end ShenWork.Paper2.IntervalChiNegH1WindowWiring
