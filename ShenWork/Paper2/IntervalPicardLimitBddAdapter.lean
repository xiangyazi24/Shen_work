/-
  ShenWork/Paper2/IntervalPicardLimitBddAdapter.lean

  **BddOn-side consumer adapters: per-window gradient / Hessian bounds.**

  The `DuhamelSourceBddOn` package (`IntervalPicardLimitRestartBdd`) is the
  satisfiable replacement for the unfillable global summable envelope of
  `DuhamelSourceL1ContOn`.  The producer
  `IntervalPicardLimitBddProducer.duhamelSourceBddOn_of_mildData` builds it
  (0-sorry) for the patched canonical limit-source family.

  This file ports the K2 gradient/Hessian compact-window bounds
  (`IntervalCompactSliceGradientBounds.deriv_lift_bound_on_compact` /
  `deriv2_lift_bound_on_compact`) — which currently consume
  `DuhamelSourceL1ContOn`'s GLOBAL envelope — to the bounded package.  The only
  envelope consumption in those lemmas is the σ-UNIFORM eigenvalue-weighted
  limitCoeff bound `λ_k |limitCoeff σ k| ≤ E_k` on a window `[a',b'] ⋐ (0,T)`;
  away from `s = 0` the bounded package supplies exactly such a window-uniform
  majorant via a FIXED-point time split at `a'/2` (head gains `e^{-(a'/2)λ}`
  against the crude `(a'/2)·M` bound; tail reads the family on `[a'/2, σ] ⊆
  [a'/2, τ]` where the window envelope `env (a'/2)` decays).  The rest of the
  gradient-bound proof (series-derivative transfer at interior `x`, junk-deriv at
  the endpoints) is family-independent and is re-used verbatim from
  `CompactSliceGradientBounds` (those helpers are public `theorem`s).

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalPicardLimitRestartBdd
import ShenWork.Paper2.IntervalCompactSliceGradientBounds

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalDuhamelClosedC2
  (duhamelSpectralCoeff cosineCoeffSeries_grad_hasDerivAt cosineCoeffSeries_deriv2_eq)
open ShenWork.IntervalPicardLimitRestart (limitCoeff)
open ShenWork.IntervalPicardLimitRestartWeak (duhamelSpectralCoeff_general_split_on)
open ShenWork.IntervalPicardLimitRestartBdd
  (DuhamelSourceBddOn
   abs_duhamelSpectralCoeff_le_of_bound
   eigenvalue_mul_abs_duhamelSpectralCoeff_le_of_bound)
open ShenWork.Paper2.CompactSliceGradientBounds
  (grad_series_abs_le grad2_series_abs_le
   not_differentiableAt_lift_left not_differentiableAt_lift_right
   deriv2_lift_eq_zero_left deriv2_lift_eq_zero_right)
open ShenWork.IntervalMildRegularityBootstrap (unitIntervalCosineEigenvalue_mul_exp_summable)

noncomputable section

namespace ShenWork.IntervalPicardLimitBddAdapter

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## 1. The σ-uniform eigenvalue-weighted `limitCoeff` majorant from `BddOn`.

For a window `[a', b'] ⋐ (0, τ]` (`0 < a'`), the bounded package gives a
window-uniform summable majorant
`Eλ a' k := M₀·(λ_k e^{-a' λ_k}) + (a'/2)·M·(λ_k e^{-(a'/2) λ_k}) + env (a'/2) k`
for `λ_k |limitCoeff σ k|`, valid for every `σ ∈ [a', b']`. -/

/-- The σ-uniform window majorant. -/
def windowEigEnv (M₀ M a' : ℝ) (env : ℕ → ℝ) (k : ℕ) : ℝ :=
  M₀ * ((λ_ k) * Real.exp (-a' * (λ_ k)))
    + (a' / 2 * M) * ((λ_ k) * Real.exp (-(a' / 2) * (λ_ k)))
    + env k

theorem windowEigEnv_summable {M₀ M a' : ℝ} (ha' : 0 < a')
    {env : ℕ → ℝ} (henv : Summable env) :
    Summable (windowEigEnv M₀ M a' env) := by
  have ha'2 : 0 < a' / 2 := by linarith
  have h1 : Summable (fun k => M₀ * ((λ_ k) * Real.exp (-a' * (λ_ k)))) :=
    (unitIntervalCosineEigenvalue_mul_exp_summable ha').mul_left M₀
  have h2 : Summable (fun k => (a' / 2 * M) * ((λ_ k) * Real.exp (-(a' / 2) * (λ_ k)))) :=
    (unitIntervalCosineEigenvalue_mul_exp_summable ha'2).mul_left (a' / 2 * M)
  exact (h1.add h2).add henv

/-- **σ-uniform eigenvalue-weighted `limitCoeff` bound (bounded source).**
For the canonical limit-source family with bounded package `src` on horizon `τ`,
`λ_k |limitCoeff σ k| ≤ windowEigEnv M₀ src.M a' (src.env (a'/2)) k` for every
`σ ∈ [a', τ]` and mode `k` (the fixed-split analog of
`eigenvalue_mul_abs_limitCoeff_le_uniform` against `DuhamelSourceBddOn`). -/
theorem eigenvalue_mul_abs_limitCoeff_le_uniform_bdd
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {τ : ℝ}
    (src : DuhamelSourceBddOn
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) τ)
    {a' : ℝ} (ha' : 0 < a') {σ : ℝ} (hσ : a' ≤ σ) (hστ : σ ≤ τ) (k : ℕ) :
    (λ_ k) * |limitCoeff p u₀ u σ k|
      ≤ windowEigEnv M₀ src.M a' (src.env (a' / 2)) k := by
  let a : ℝ → ℕ → ℝ := fun s k => cosineCoeffs (logisticLifted p (u s)) k
  have heig_nn : 0 ≤ (λ_ k) := by unfold unitIntervalCosineEigenvalue; positivity
  have hσpos : 0 < σ := lt_of_lt_of_le ha' hσ
  -- fixed split point
  set m : ℝ := a' / 2 with hmdef
  have hm : 0 < m := by rw [hmdef]; linarith
  have hmσ : m ≤ σ := le_trans (by rw [hmdef]; linarith) hσ
  have hmτ : m ≤ τ := le_trans hmσ hστ
  have hσmσ : 0 < σ - m := by linarith
  -- the per-mode split at m
  have hsplit : duhamelSpectralCoeff a σ k
      = Real.exp (-(σ - m) * (λ_ k)) * duhamelSpectralCoeff a m k
        + duhamelSpectralCoeff (fun ρ k => a (m + ρ) k) (σ - m) k :=
    duhamelSpectralCoeff_general_split_on (a := a) (T := τ) src.hcont hm.le hmσ hστ k
  -- head crude bound
  have hhead : |duhamelSpectralCoeff a m k| ≤ m * src.M :=
    abs_duhamelSpectralCoeff_le_of_bound hm k
      (fun s hs hsm => src.hM s hs (le_trans hsm hmτ) k)
  -- tail: λ_k · |duh(shifted) (σ-m) k| ≤ env m k
  have htail : (λ_ k) * |duhamelSpectralCoeff (fun ρ k => a (m + ρ) k) (σ - m) k|
      ≤ src.env m k := by
    refine eigenvalue_mul_abs_duhamelSpectralCoeff_le_of_bound hσmσ k ?_ ?_
    · intro ρ hρ hρσm
      exact src.henv_bound m hm (m + ρ) (by linarith) (by linarith) k
    · have hmaps : Set.MapsTo (fun ρ : ℝ => m + ρ) (Set.Icc 0 (σ - m)) (Set.Icc 0 τ) :=
        fun ρ hρ => ⟨by linarith [hρ.1, hm.le], by linarith [hρ.2]⟩
      exact (src.hcont k).comp (continuous_const.add continuous_id).continuousOn hmaps
  -- assemble
  unfold limitCoeff
  calc (λ_ k) * |Real.exp (-σ * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k
          + duhamelSpectralCoeff a σ k|
      ≤ (λ_ k) * (|Real.exp (-σ * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k|
          + |duhamelSpectralCoeff a σ k|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) heig_nn
    _ = (λ_ k) * |Real.exp (-σ * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k|
          + (λ_ k) * |duhamelSpectralCoeff a σ k| := by ring
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
          calc (λ_ k) * |Real.exp (-(σ - m) * (λ_ k)) * duhamelSpectralCoeff a m k
                  + duhamelSpectralCoeff (fun ρ k => a (m + ρ) k) (σ - m) k|
              ≤ (λ_ k) * (|Real.exp (-(σ - m) * (λ_ k)) * duhamelSpectralCoeff a m k|
                  + |duhamelSpectralCoeff (fun ρ k => a (m + ρ) k) (σ - m) k|) :=
                mul_le_mul_of_nonneg_left (abs_add_le _ _) heig_nn
            _ = (λ_ k) * |Real.exp (-(σ - m) * (λ_ k)) * duhamelSpectralCoeff a m k|
                  + (λ_ k) * |duhamelSpectralCoeff (fun ρ k => a (m + ρ) k) (σ - m) k| := by ring
            _ ≤ (a' / 2 * src.M) * ((λ_ k) * Real.exp (-(a' / 2) * (λ_ k))) + src.env m k := by
                apply add_le_add _ htail
                rw [abs_mul, abs_of_pos (Real.exp_pos _)]
                -- e^{-(σ-m)λ} ≤ e^{-mλ} since σ-m ≥ m
                have hexp_mono : Real.exp (-(σ - m) * (λ_ k)) ≤ Real.exp (-m * (λ_ k)) :=
                  Real.exp_le_exp.mpr (by nlinarith [heig_nn, hmσ])
                calc (λ_ k) * (Real.exp (-(σ - m) * (λ_ k)) * |duhamelSpectralCoeff a m k|)
                    ≤ (λ_ k) * (Real.exp (-m * (λ_ k)) * (m * src.M)) := by
                      apply mul_le_mul_of_nonneg_left _ heig_nn
                      exact mul_le_mul hexp_mono hhead (abs_nonneg _) (Real.exp_pos _).le
                  _ = (a' / 2 * src.M) * ((λ_ k) * Real.exp (-(a' / 2) * (λ_ k))) := by
                      rw [hmdef]; ring
    _ = windowEigEnv M₀ src.M a' (src.env (a' / 2)) k := by
        unfold windowEigEnv; rw [hmdef]; ring

/-! ## 2. Gradient / Hessian compact-window bounds (bounded source).

BddOn analogs of `CompactSliceGradientBounds.deriv_lift_bound_on_compact` /
`deriv2_lift_bound_on_compact`.  The series-derivative transfer (interior `x`) and
junk-deriv (endpoints) are family-independent and re-used verbatim; the envelope
consumption is replaced by the σ-uniform window majorant `windowEigEnv` above. -/

/-- **Gradient bound on a compact window `[a', b'] ⊂ (0, τ]` (bounded source).** -/
theorem deriv_lift_bound_on_compact_bdd
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {τ : ℝ}
    (src : DuhamelSourceBddOn
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) τ)
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
      exact eigenvalue_mul_abs_limitCoeff_le_uniform_bdd p u₀ u hM₀ hu₀_bound src
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
      fun k => eigenvalue_mul_abs_limitCoeff_le_uniform_bdd p u₀ u hM₀ hu₀_bound src
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

/-- **Hessian bound on a compact window `[a', b'] ⊂ (0, τ]` (bounded source).** -/
theorem deriv2_lift_bound_on_compact_bdd
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {τ : ℝ}
    (src : DuhamelSourceBddOn
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) τ)
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
      exact eigenvalue_mul_abs_limitCoeff_le_uniform_bdd p u₀ u hM₀ hu₀_bound src
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
      fun k => eigenvalue_mul_abs_limitCoeff_le_uniform_bdd p u₀ u hM₀ hu₀_bound src
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

end ShenWork.IntervalPicardLimitBddAdapter
