import ShenWork.Paper3.MinimalSteadyWADirection
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Selecting the backward side of the local `m = 3` branch

The sensitivity derivative vanishes at the bifurcation point and has strictly
negative derivative there.  Hence the sensitivity is strictly decreasing on a
small right-hand interval.  In particular, positive amplitudes sufficiently
close to zero have sensitivity strictly between zero and the linear threshold.
-/

noncomputable section

namespace ShenWork.M3Counterexample

open ShenWork.Wiener
open Filter SignType Set Topology

theorem eventually_deriv_minimalSteadySensitivity_eq_selected :
    ∀ᶠ a in 𝓝 (0 : ℝ),
      deriv minimalSteadySensitivity a =
        minimalSteadySensitivityDeriv a := by
  have hdiff :
      ∀ᶠ a in 𝓝 (0 : ℝ),
        @ContDiffAt
          ℝ inferInstance
          ℝ inferInstance inferInstance
          BranchImplicit branchImplicitNormedAddCommGroup
            branchImplicitNormedSpace
          3 minimalSteadyImplicitBranch a :=
    @ContDiffAt.eventually
      ℝ inferInstance
      ℝ inferInstance inferInstance
      BranchImplicit branchImplicitNormedAddCommGroup
        branchImplicitNormedSpace
      minimalSteadyImplicitBranch 0 3
      minimalSteadyImplicitBranch_contDiffAt (by norm_num)
  filter_upwards [hdiff] with a hcont
  have hq :=
    @ContDiffAt.differentiableAt
      ℝ inferInstance
      ℝ inferInstance inferInstance
      BranchImplicit branchImplicitNormedAddCommGroup
        branchImplicitNormedSpace
      minimalSteadyImplicitBranch a 3 hcont (by norm_num)
  have hqderiv :=
    @DifferentiableAt.hasDerivAt
      ℝ inferInstance BranchImplicit
      branchImplicitNormedAddCommGroup branchImplicitNormedSpace
      minimalSteadyImplicitBranch a hq
  have hs := implicitSensitivity_comp_hasDerivAt hqderiv
  have hs' :
      HasDerivAt minimalSteadySensitivity
        (minimalSteadySensitivityDeriv a) a := by
    simpa only [minimalSteadySensitivity, minimalSteadyBranchPoint,
      branchSensitivityCLM_apply,
      minimalSteadySensitivityDeriv] using hs
  exact hs'.deriv

theorem eventually_minimalSteadySensitivityDeriv_neg_right :
    ∀ᶠ a in 𝓝[>] (0 : ℝ),
      minimalSteadySensitivityDeriv a < 0 := by
  have hsecond :
      deriv minimalSteadySensitivityDeriv 0 < 0 := by
    rw [minimalSteadySensitivityDeriv_hasDerivAt.deriv]
    exact minimalSensitivitySecondJet_neg
  have hfirst :
      minimalSteadySensitivityDeriv 0 = 0 := by
    rw [minimalSteadySensitivityDeriv_zero,
      minimalSensitivityFirstJet_eq_zero]
  have hsign :
      ∀ᶠ a in 𝓝 (0 : ℝ),
        sign (minimalSteadySensitivityDeriv a) =
          sign (0 - a) :=
    eventually_nhdsWithin_sign_eq_of_deriv_neg hsecond hfirst
  have hsignRight :
      ∀ᶠ a in 𝓝[>] (0 : ℝ),
        sign (minimalSteadySensitivityDeriv a) =
          sign (0 - a) :=
    hsign.filter_mono inf_le_left
  filter_upwards [hsignRight, self_mem_nhdsWithin] with a hs ha
  rw [← sign_eq_neg_one_iff, hs, sign_eq_neg_one_iff]
  exact sub_neg.mpr ha

theorem eventually_deriv_minimalSteadySensitivity_neg_right :
    ∀ᶠ a in 𝓝[>] (0 : ℝ),
      deriv minimalSteadySensitivity a < 0 := by
  have heq :
      ∀ᶠ a in 𝓝[>] (0 : ℝ),
        deriv minimalSteadySensitivity a =
          minimalSteadySensitivityDeriv a :=
    eventually_deriv_minimalSteadySensitivity_eq_selected.filter_mono
      inf_le_left
  filter_upwards
    [heq, eventually_minimalSteadySensitivityDeriv_neg_right]
      with a ha hneg
  rw [ha]
  exact hneg

theorem eventually_minimalSteadySensitivity_lt_threshold_right :
    ∀ᶠ a in 𝓝[>] (0 : ℝ),
      minimalSteadySensitivity a < minimalChiLin := by
  rcases
      (nhdsGT_basis (0 : ℝ)).eventually_iff.mp
        eventually_deriv_minimalSteadySensitivity_neg_right with
    ⟨u, hu, hderiv⟩
  apply (nhdsGT_basis (0 : ℝ)).eventually_iff.mpr
  refine ⟨u, hu, ?_⟩
  intro a ha
  have hcont :
      ContinuousOn minimalSteadySensitivity (Icc 0 a) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      exact
        minimalSteadySensitivity_contDiffAt.continuousAt.continuousWithinAt
    · have hxpos : 0 < x :=
        lt_of_le_of_ne hx.1 (Ne.symm hx0)
      have hxltu : x < u :=
        lt_of_le_of_lt hx.2 ha.2
      exact
        (differentiableAt_of_deriv_ne_zero
          (hderiv ⟨hxpos, hxltu⟩).ne).continuousAt.continuousWithinAt
  have hanti :
      StrictAntiOn minimalSteadySensitivity (Icc 0 a) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 a) hcont
    intro x hx
    rw [interior_Icc] at hx
    exact hderiv ⟨hx.1, lt_trans hx.2 ha.2⟩
  have hlt :
      minimalSteadySensitivity a <
        minimalSteadySensitivity 0 :=
    hanti (left_mem_Icc.mpr ha.1.le)
      (right_mem_Icc.mpr ha.1.le) ha.1
  simpa only [minimalSteadySensitivity_zero] using hlt

theorem eventually_minimalSteadySensitivity_pos :
    ∀ᶠ a in 𝓝 (0 : ℝ),
      0 < minimalSteadySensitivity a := by
  have h :=
    continuousAt_const.eventually_lt
      minimalSteadySensitivity_contDiffAt.continuousAt
      (by simpa only [minimalSteadySensitivity_zero] using
        minimalChiLin_pos)
  simpa only [Pi.zero_apply] using h

theorem eventually_minimalSteadySensitivity_bounds_right :
    ∀ᶠ a in 𝓝[>] (0 : ℝ),
      0 < minimalSteadySensitivity a ∧
        minimalSteadySensitivity a < minimalChiLin := by
  have hpos :
      ∀ᶠ a in 𝓝[>] (0 : ℝ),
        0 < minimalSteadySensitivity a :=
    eventually_minimalSteadySensitivity_pos.filter_mono inf_le_left
  filter_upwards
    [hpos, eventually_minimalSteadySensitivity_lt_threshold_right]
      with a hpa hlt
  exact ⟨hpa, hlt⟩

end ShenWork.M3Counterexample
