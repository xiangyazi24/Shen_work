import ShenWork.Paper2.IntervalChiNegH1WindowWiring
import Mathlib.Analysis.ODE.Gronwall
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

/-- The scalar H¹ differential inequality supplies the restricted local H¹
seed needed before the one-unit averaged estimate starts.

The proof avoids needing a right derivative at `0`: first bound the energy on
`[0, T/2]` by compactness, then apply Mathlib's Gronwall estimate only on
windows `[T/2, τ]`, obtaining the derivative at the left endpoint from the
larger positive-time window `[0, τ]`. -/
theorem exists_H1_localSeed_of_scalarDI_before
    {u : ℝ → intervalDomainPoint → ℝ} {T A B : ℝ}
    (hT : 0 < T)
    (hDI : H1ScalarDIOnBefore u T A B) :
    ∃ Ylocal : ℝ,
      ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
        H1energy u τ ≤ Ylocal := by
  let δ : ℝ := T / 2
  have hδ0 : 0 < δ := by
    dsimp [δ]
    linarith
  have hδT : δ < T := by
    dsimp [δ]
    linarith
  have h0δ : (0 : ℝ) ≤ δ := le_of_lt hδ0
  have hcont0δ : ContinuousOn (H1energy u) (Set.Icc (0 : ℝ) δ) :=
    hDI.hcont (by norm_num) h0δ hδT
  have hbdd : BddAbove ((H1energy u) '' Set.Icc (0 : ℝ) δ) :=
    isCompact_Icc.bddAbove_image hcont0δ
  obtain ⟨M0, hM0_image⟩ := hbdd
  have hM0 : ∀ t, t ∈ Set.Icc (0 : ℝ) δ → H1energy u t ≤ M0 := by
    intro t ht
    exact hM0_image (Set.mem_image_of_mem (H1energy u) ht)
  refine ⟨max M0 (gronwallBound (H1energy u δ) A B 1), ?_⟩
  intro τ hτ hτT
  by_cases hτδ : τ ≤ δ
  · have hτIcc : τ ∈ Set.Icc (0 : ℝ) δ := ⟨le_of_lt hτ.1, hτδ⟩
    exact (hM0 τ hτIcc).trans (le_max_left _ _)
  · have hδτ : δ < τ := lt_of_not_ge hτδ
    have hδτ_le : δ ≤ τ := le_of_lt hδτ
    have hcontδτ : ContinuousOn (H1energy u) (Set.Icc δ τ) :=
      hDI.hcont h0δ hδτ_le hτT
    have hgr :
        H1energy u τ ≤ gronwallBound (H1energy u δ) A B (τ - δ) := by
      have hpoint :=
        le_gronwallBound_of_liminf_deriv_right_le
          (f := H1energy u)
          (f' := fun t => deriv (H1energy u) t)
          (δ := H1energy u δ) (K := A) (ε := B)
          (a := δ) (b := τ)
          hcontδτ
          (fun t ht r hr => by
            have ht0 : 0 < t := lt_of_lt_of_le hδ0 ht.1
            have htτ : t < τ := ht.2
            have hderiv :
                HasDerivWithinAt (H1energy u)
                  (deriv (H1energy u) t) (Set.Ioi t) t :=
              hDI.hhasDerivRight (a := 0) (b := τ) (r := t)
                (by norm_num) (le_of_lt hτ.1) hτT ⟨ht0, htτ⟩
            exact (hderiv.limsup_slope_le' (lt_irrefl t) hr).frequently.mono
              (fun z hz => by
                simpa [slope_def_field, div_eq_mul_inv, mul_comm, mul_left_comm,
                  mul_assoc] using hz))
          (le_rfl)
          (fun t ht => by
            have ht0 : 0 < t := lt_of_lt_of_le hδ0 ht.1
            have htT : t < T := lt_trans ht.2 hτT
            exact hDI.hDI t ht0 htT)
          τ ⟨hδτ_le, le_rfl⟩
      simpa [sub_self] using hpoint
    have htime_le : τ - δ ≤ 1 := by
      linarith [hτ.2, h0δ]
    have hmono :
        gronwallBound (H1energy u δ) A B (τ - δ) ≤
          gronwallBound (H1energy u δ) A B 1 :=
      (gronwallBound_mono (H1energy_nonneg u δ) hDI.hB hDI.hA) htime_le
    exact (hgr.trans hmono).trans (le_max_right _ _)

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

/-- Restricted-time paper-positive H¹ scalar-DI wrapper.

This uses the windowed 1D bypass directly, so the local H¹ start is only
required on the actual solution interval `τ < T`. -/
theorem intervalDomain_boundedBefore_of_paperPositive_H1scalarDI_local_before
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
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hmass : IntervalDomainLogisticMassBound params T u :=
    intervalDomainLogisticMassBound_of_proposition24
      (ShenWork.Paper2.intervalDomain_Proposition_2_4 params)
      ha hbounded.2.1 hu₀.toPositive hT hsol htrace
  have habsorbing :
      IntervalDomainL2AbsorbingDifferentialInequalityResult params T u :=
    intervalDomain_absorbingDifferentialL2_of_mass hbounded hsol hmass
  have hLp2 : LpPowerBoundedBefore intervalDomain 2 T u :=
    intervalDomainL2PowerBoundedBefore_of_absorbingDifferentialInequality
      hsol habsorbing hfrontier
  rcases intervalDomain_L2energy_bound_of_Lp2 hsol hLp2 with
    ⟨Y_L2, hL2⟩
  exact intervalDomain_boundedBefore_of_L2Window_H1local_H1avg_and_Lp2
    hsol hbounded.2.2.1 habsorbing hfrontier hL2 hDI.hA
    hlocal (H1_avg_of_scalarDI_before hDI) hLp2

/-- Paper-positive H¹ scalar-DI wrapper with the restricted local seed produced
from the scalar differential inequality itself. -/
theorem intervalDomain_boundedBefore_of_paperPositive_H1scalarDI_before
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
    {A B : ℝ}
    (hDI : H1ScalarDIOnBefore u T A B) :
    IsPaper2BoundedBefore intervalDomain T u := by
  rcases exists_H1_localSeed_of_scalarDI_before hT hDI with
    ⟨Ylocal, hlocal⟩
  exact intervalDomain_boundedBefore_of_paperPositive_H1scalarDI_local_before
    hbounded ha hu₀ hT hsol htrace hfrontier hDI hlocal

#print axioms H1Window_subinterval_le
#print axioms H1_backward_bound_of_scalarDI_before
#print axioms H1_avg_of_backwards_bound
#print axioms H1_avg_of_scalarDI_before
#print axioms exists_H1_localSeed_of_scalarDI_before
#print axioms intervalDomain_boundedBefore_of_paperPositive_H1scalarDI_local
#print axioms intervalDomain_boundedBefore_of_paperPositive_H1scalarDI_local_before
#print axioms intervalDomain_boundedBefore_of_paperPositive_H1scalarDI_before

end ShenWork.Paper2.IntervalChiNegH1AverageWiring
