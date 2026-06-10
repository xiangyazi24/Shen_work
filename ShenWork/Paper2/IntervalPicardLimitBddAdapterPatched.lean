/-
  ShenWork/Paper2/IntervalPicardLimitBddAdapterPatched.lean

  **PATCHED-family variants of the BddOn adapter lemmas.**

  `IntervalPicardLimitBddAdapter` states the σ-uniform eigenvalue majorant and
  the K2 gradient/Hessian compact-window bounds against a `DuhamelSourceBddOn`
  package for the CANONICAL source family — which is unfillable at `s = 0`
  (the canonical family reads `u 0`, unconstrained for an arbitrary
  `GradientMildSolutionData`).  The producer
  (`duhamelSourceBddOn_of_mildData`) yields the package for the PATCHED family
  `patchedSource p u₀ u` instead.  This file clones the three adapter lemmas
  against the patched package: `limitCoeff` is first rewritten through
  `limitCoeff_eq_patched` (the canonical and patched Duhamel coefficients agree
  — the families differ only at the measure-null `s ≤ 0`), after which the
  original estimates run verbatim on the patched integrals.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalPicardLimitBddAdapter
import ShenWork.Paper2.IntervalPicardLimitTimeNhdSubtype

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalPicardLimitRestart (limitCoeff)
open ShenWork.IntervalPicardLimitRestartWeak (duhamelSpectralCoeff_general_split_on)
open ShenWork.IntervalPicardLimitRestartBdd
open ShenWork.Paper2.CompactSliceGradientBounds
open ShenWork.IntervalMildRegularityBootstrap (unitIntervalCosineEigenvalue_mul_exp_summable)
open ShenWork.IntervalPicardLimitBddProducer (patchedSource)
open ShenWork.Paper2.TimeNhdSubtype (limitCoeff_eq_patched)
open ShenWork.IntervalPicardLimitBddAdapter (windowEigEnv windowEigEnv_summable)

noncomputable section

namespace ShenWork.Paper2.BddAdapterPatched

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-- **σ-uniform eigenvalue majorant from the PATCHED bounded package.**
Patched clone of `IntervalPicardLimitBddAdapter.eigenvalue_mul_abs_limitCoeff_le_uniform_bdd`. -/
theorem eigenvalue_mul_abs_limitCoeff_le_uniform_patched
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {τ : ℝ}
    (src : DuhamelSourceBddOn (patchedSource p u₀ u) τ)
    {a' : ℝ} (ha' : 0 < a') {σ : ℝ} (hσ : a' ≤ σ) (hστ : σ ≤ τ) (k : ℕ) :
    (λ_ k) * |limitCoeff p u₀ u σ k|
      ≤ windowEigEnv M₀ src.M a' (src.env (a' / 2)) k := by
  have heig_nn : 0 ≤ (λ_ k) := by unfold unitIntervalCosineEigenvalue; positivity
  have hσpos : 0 < σ := lt_of_lt_of_le ha' hσ
  rw [limitCoeff_eq_patched p u₀ u hσpos k]
  -- fixed split point
  set m : ℝ := a' / 2 with hmdef
  have hm : 0 < m := by rw [hmdef]; linarith
  have hmσ : m ≤ σ := le_trans (by rw [hmdef]; linarith) hσ
  have hmτ : m ≤ τ := le_trans hmσ hστ
  have hσmσ : 0 < σ - m := by linarith
  -- the per-mode split at m
  have hsplit : duhamelSpectralCoeff (patchedSource p u₀ u) σ k
      = Real.exp (-(σ - m) * (λ_ k)) * duhamelSpectralCoeff (patchedSource p u₀ u) m k
        + duhamelSpectralCoeff (fun ρ k => patchedSource p u₀ u (m + ρ) k) (σ - m) k :=
    duhamelSpectralCoeff_general_split_on (a := patchedSource p u₀ u) (T := τ) src.hcont hm.le hmσ hστ k
  -- head crude bound
  have hhead : |duhamelSpectralCoeff (patchedSource p u₀ u) m k| ≤ m * src.M :=
    abs_duhamelSpectralCoeff_le_of_bound hm k
      (fun s hs hsm => src.hM s hs (le_trans hsm hmτ) k)
  -- tail: λ_k · |duh(shifted) (σ-m) k| ≤ env m k
  have htail : (λ_ k) * |duhamelSpectralCoeff (fun ρ k => patchedSource p u₀ u (m + ρ) k) (σ - m) k|
      ≤ src.env m k := by
    refine eigenvalue_mul_abs_duhamelSpectralCoeff_le_of_bound hσmσ k ?_ ?_
    · intro ρ hρ hρσm
      exact src.henv_bound m hm (m + ρ) (by linarith) (by linarith) k
    · have hmaps : Set.MapsTo (fun ρ : ℝ => m + ρ) (Set.Icc 0 (σ - m)) (Set.Icc 0 τ) :=
        fun ρ hρ => ⟨by linarith [hρ.1, hm.le], by linarith [hρ.2]⟩
      exact (src.hcont k).comp (continuous_const.add continuous_id).continuousOn hmaps
  -- assemble
  calc (λ_ k) * |Real.exp (-σ * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k
          + duhamelSpectralCoeff (patchedSource p u₀ u) σ k|
      ≤ (λ_ k) * (|Real.exp (-σ * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k|
          + |duhamelSpectralCoeff (patchedSource p u₀ u) σ k|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) heig_nn
    _ = (λ_ k) * |Real.exp (-σ * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k|
          + (λ_ k) * |duhamelSpectralCoeff (patchedSource p u₀ u) σ k| := by ring
    _ ≤ M₀ * ((λ_ k) * Real.exp (-a' * (λ_ k)))
          + ((a' / 2 * src.M) * ((λ_ k) * Real.exp (-(a' / 2) * (λ_ k))) + src.env m k) := by
        apply add_le_add
        · -- homogeneous part, frozen at a' via exp monotonicity
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          have hexp_mono : Real.exp (-σ * (λ_ k)) ≤ Real.exp (-a' * (λ_ k)) :=
            Real.exp_le_exp.mpr (by nlinarith [heig_nn, hσ])
          calc (λ_ k) * (Real.exp (-σ * (λ_ k)) * |cosineCoeffs (intervalDomainLift u₀) k|)
              ≤ (λ_ k) * (Real.exp (-a' * (λ_ k)) * M₀) := by
                apply mul_le_mul_of_nonneg_left _ heig_nn
                exact mul_le_mul hexp_mono (hu₀_bound k) (abs_nonneg _) (Real.exp_pos _).le
            _ = M₀ * ((λ_ k) * Real.exp (-a' * (λ_ k))) := by ring
        · -- Duhamel part, via the split
          rw [hsplit]
          calc (λ_ k) * |Real.exp (-(σ - m) * (λ_ k)) * duhamelSpectralCoeff (patchedSource p u₀ u) m k
                  + duhamelSpectralCoeff (fun ρ k => patchedSource p u₀ u (m + ρ) k) (σ - m) k|
              ≤ (λ_ k) * (|Real.exp (-(σ - m) * (λ_ k)) * duhamelSpectralCoeff (patchedSource p u₀ u) m k|
                  + |duhamelSpectralCoeff (fun ρ k => patchedSource p u₀ u (m + ρ) k) (σ - m) k|) :=
                mul_le_mul_of_nonneg_left (abs_add_le _ _) heig_nn
            _ = (λ_ k) * |Real.exp (-(σ - m) * (λ_ k)) * duhamelSpectralCoeff (patchedSource p u₀ u) m k|
                  + (λ_ k) * |duhamelSpectralCoeff (fun ρ k => patchedSource p u₀ u (m + ρ) k) (σ - m) k| := by
                ring
            _ ≤ (a' / 2 * src.M) * ((λ_ k) * Real.exp (-(a' / 2) * (λ_ k))) + src.env m k := by
                apply add_le_add _ htail
                rw [abs_mul, abs_of_pos (Real.exp_pos _)]
                have hexp_mono : Real.exp (-(σ - m) * (λ_ k)) ≤ Real.exp (-m * (λ_ k)) :=
                  Real.exp_le_exp.mpr (by nlinarith [heig_nn, hmσ])
                calc (λ_ k) * (Real.exp (-(σ - m) * (λ_ k)) * |duhamelSpectralCoeff (patchedSource p u₀ u) m k|)
                    ≤ (λ_ k) * (Real.exp (-m * (λ_ k)) * (m * src.M)) := by
                      apply mul_le_mul_of_nonneg_left _ heig_nn
                      exact mul_le_mul hexp_mono hhead (abs_nonneg _) (Real.exp_pos _).le
                  _ = (a' / 2 * src.M) * ((λ_ k) * Real.exp (-(a' / 2) * (λ_ k))) := by
                      rw [hmdef]; ring
    _ = windowEigEnv M₀ src.M a' (src.env (a' / 2)) k := by
        unfold ShenWork.IntervalPicardLimitBddAdapter.windowEigEnv
        rw [hmdef]; ring

/-- **Gradient bound on a compact window (PATCHED bounded source).** -/
theorem deriv_lift_bound_on_compact_patched
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {τ : ℝ}
    (src : DuhamelSourceBddOn (patchedSource p u₀ u) τ)
    (hbsum : ∀ σ, 0 < σ → σ ≤ τ →
      Summable (fun k => (λ_ k) * |limitCoeff p u₀ u σ k|))
    (hagree : ∀ σ, 0 < σ → σ ≤ τ → Set.EqOn (intervalDomainLift (u σ))
      (fun x => ∑' n, limitCoeff p u₀ u σ n * cosineMode n x) (Set.Icc (0:ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ ≤ τ → ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < intervalDomainLift (u σ) x)
    {a' b' : ℝ} (ha' : 0 < a') (hb'τ : b' ≤ τ) :
    ∃ G1, 0 ≤ G1 ∧ ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0:ℝ) 1,
      |deriv (intervalDomainLift (u σ)) x| ≤ G1 := by
  by_cases hab : a' ≤ b'
  · have hWsum : Summable (windowEigEnv M₀ src.M a' (src.env (a' / 2))) :=
      windowEigEnv_summable ha' (src.henv_summable (a' / 2) (by linarith) (by linarith))
    have hWnn : ∀ k, 0 ≤ windowEigEnv M₀ src.M a' (src.env (a' / 2)) k := by
      intro k
      have h1 : 0 ≤ (λ_ k) := by unfold unitIntervalCosineEigenvalue; positivity
      refine le_trans (mul_nonneg h1 (abs_nonneg (limitCoeff p u₀ u a' k))) ?_
      exact eigenvalue_mul_abs_limitCoeff_le_uniform_patched p u₀ u hM₀ hu₀_bound src
        ha' le_rfl (le_trans hab hb'τ) k
    refine ⟨∑' k, windowEigEnv M₀ src.M a' (src.env (a' / 2)) k,
      tsum_nonneg hWnn, ?_⟩
    intro σ hσ x hx
    obtain ⟨hσa, hσb⟩ := hσ
    have hσpos : 0 < σ := lt_of_lt_of_le ha' hσa
    have hστ : σ ≤ τ := le_trans hσb hb'τ
    have hbsumσ : Summable (fun k => (λ_ k) * |limitCoeff p u₀ u σ k|) :=
      hbsum σ hσpos hστ
    have henvU : ∀ k, (λ_ k) * |limitCoeff p u₀ u σ k|
        ≤ windowEigEnv M₀ src.M a' (src.env (a' / 2)) k :=
      fun k => eigenvalue_mul_abs_limitCoeff_le_uniform_patched p u₀ u hM₀ hu₀_bound src
        ha' hσa hστ k
    have hgrad_bound : |∑' n, limitCoeff p u₀ u σ n
          * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x))|
        ≤ ∑' k, windowEigEnv M₀ src.M a' (src.env (a' / 2)) k :=
      grad_series_abs_le (fun n => limitCoeff p u₀ u σ n)
        (windowEigEnv M₀ src.M a' (src.env (a' / 2))) x hWsum henvU
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    · have hnd : ¬ DifferentiableAt ℝ (intervalDomainLift (u σ)) x := by
        rw [← hx0]
        exact not_differentiableAt_lift_left u σ
          (hpost σ hσpos hστ 0 (Set.left_mem_Icc.mpr zero_le_one))
      rw [deriv_zero_of_not_differentiableAt hnd, abs_zero]
      exact tsum_nonneg hWnn
    · rcases eq_or_lt_of_le hx.2 with hx1 | hx1
      · have hnd : ¬ DifferentiableAt ℝ (intervalDomainLift (u σ)) x := by
          rw [hx1]
          exact not_differentiableAt_lift_right u σ
            (hpost σ hσpos hστ 1 (Set.right_mem_Icc.mpr zero_le_one))
        rw [deriv_zero_of_not_differentiableAt hnd, abs_zero]
        exact tsum_nonneg hWnn
      · have hxIoo : x ∈ Set.Ioo (0:ℝ) 1 := ⟨hx0, hx1⟩
        have hEq : intervalDomainLift (u σ)
            =ᶠ[nhds x] (fun y => ∑' n, limitCoeff p u₀ u σ n * cosineMode n y) := by
          have hmem : Set.Ioo (0:ℝ) 1 ∈ nhds x := isOpen_Ioo.mem_nhds hxIoo
          filter_upwards [hmem] with y hy
          exact hagree σ hσpos hστ (Set.Ioo_subset_Icc_self hy)
        rw [hEq.deriv_eq, (cosineCoeffSeries_grad_hasDerivAt hbsumσ x).deriv]
        exact hgrad_bound
  · exact ⟨0, le_rfl, fun σ hσ => absurd (le_trans hσ.1 hσ.2) hab⟩

/-- **Hessian bound on a compact window (PATCHED bounded source).** -/
theorem deriv2_lift_bound_on_compact_patched
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {τ : ℝ}
    (src : DuhamelSourceBddOn (patchedSource p u₀ u) τ)
    (hbsum : ∀ σ, 0 < σ → σ ≤ τ →
      Summable (fun k => (λ_ k) * |limitCoeff p u₀ u σ k|))
    (hagree : ∀ σ, 0 < σ → σ ≤ τ → Set.EqOn (intervalDomainLift (u σ))
      (fun x => ∑' n, limitCoeff p u₀ u σ n * cosineMode n x) (Set.Icc (0:ℝ) 1))
    {a' b' : ℝ} (ha' : 0 < a') (hb'τ : b' ≤ τ) :
    ∃ G2, 0 ≤ G2 ∧ ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0:ℝ) 1,
      |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2 := by
  by_cases hab : a' ≤ b'
  · have hWsum : Summable (windowEigEnv M₀ src.M a' (src.env (a' / 2))) :=
      windowEigEnv_summable ha' (src.henv_summable (a' / 2) (by linarith) (by linarith))
    have hWnn : ∀ k, 0 ≤ windowEigEnv M₀ src.M a' (src.env (a' / 2)) k := by
      intro k
      have h1 : 0 ≤ (λ_ k) := by unfold unitIntervalCosineEigenvalue; positivity
      refine le_trans (mul_nonneg h1 (abs_nonneg (limitCoeff p u₀ u a' k))) ?_
      exact eigenvalue_mul_abs_limitCoeff_le_uniform_patched p u₀ u hM₀ hu₀_bound src
        ha' le_rfl (le_trans hab hb'τ) k
    refine ⟨∑' k, windowEigEnv M₀ src.M a' (src.env (a' / 2)) k,
      tsum_nonneg hWnn, ?_⟩
    intro σ hσ x hx
    obtain ⟨hσa, hσb⟩ := hσ
    have hσpos : 0 < σ := lt_of_lt_of_le ha' hσa
    have hστ : σ ≤ τ := le_trans hσb hb'τ
    have hbsumσ : Summable (fun k => (λ_ k) * |limitCoeff p u₀ u σ k|) :=
      hbsum σ hσpos hστ
    have henvU : ∀ k, (λ_ k) * |limitCoeff p u₀ u σ k|
        ≤ windowEigEnv M₀ src.M a' (src.env (a' / 2)) k :=
      fun k => eigenvalue_mul_abs_limitCoeff_le_uniform_patched p u₀ u hM₀ hu₀_bound src
        ha' hσa hστ k
    have hgrad2_bound : |∑' n, limitCoeff p u₀ u σ n
          * (-(((n : ℝ) * Real.pi) ^ 2) * Real.cos ((n : ℝ) * Real.pi * x))|
        ≤ ∑' k, windowEigEnv M₀ src.M a' (src.env (a' / 2)) k :=
      grad2_series_abs_le (fun n => limitCoeff p u₀ u σ n)
        (windowEigEnv M₀ src.M a' (src.env (a' / 2))) x hWsum henvU
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    · rw [← hx0, deriv2_lift_eq_zero_left u σ, abs_zero]; exact tsum_nonneg hWnn
    · rcases eq_or_lt_of_le hx.2 with hx1 | hx1
      · rw [hx1, deriv2_lift_eq_zero_right u σ, abs_zero]; exact tsum_nonneg hWnn
      · have hxIoo : x ∈ Set.Ioo (0:ℝ) 1 := ⟨hx0, hx1⟩
        have hEq : intervalDomainLift (u σ)
            =ᶠ[nhds x] (fun y => ∑' n, limitCoeff p u₀ u σ n * cosineMode n y) := by
          have hmem : Set.Ioo (0:ℝ) 1 ∈ nhds x := isOpen_Ioo.mem_nhds hxIoo
          filter_upwards [hmem] with y hy
          exact hagree σ hσpos hστ (Set.Ioo_subset_Icc_self hy)
        have hderiv_eq : deriv (intervalDomainLift (u σ))
            =ᶠ[nhds x] deriv (fun y => ∑' n, limitCoeff p u₀ u σ n * cosineMode n y) :=
          hEq.deriv
        rw [hderiv_eq.deriv_eq, cosineCoeffSeries_deriv2_eq hbsumσ x]
        exact hgrad2_bound
  · exact ⟨0, le_rfl, fun σ hσ => absurd (le_trans hσ.1 hσ.2) hab⟩

end ShenWork.Paper2.BddAdapterPatched
