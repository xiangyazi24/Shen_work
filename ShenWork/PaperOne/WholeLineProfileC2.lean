import ShenWork.PaperOne.WholeLineProfileRegularity
import ShenWork.PaperOne.WholeLineDuhamelDifferentiation
import Mathlib.Tactic

open MeasureTheory Filter Topology Real Set
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-!
Profile-side `C²` bootstrap from the stationary equation.

The file separates the two Lean obligations in the paper argument:

* the stationary equation rewrites the second derivative as a continuous
  expression built from `U`, `U'`, `V'`, and `V''`;
* the Lean statement that `U''` exists is carried as a `HasDerivAt (deriv U)`
  equation, because a pointwise equality involving `deriv (deriv U)` values
  alone does not establish differentiability of `deriv U`.
-/

/-- Product-rule right-hand side for `∂ₓ (U^m Vₓ)`. -/
def waveProfileFluxDerivativeRHS (p : CMParams) (U V : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    (deriv U x * p.m * (U x) ^ (p.m - 1)) * deriv V x +
      (U x) ^ p.m * deriv (deriv V) x

/-- Stationary-equation right-hand side for `U''`. -/
def waveProfileSecondRHS
    (p : CMParams) (c : ℝ) (U V : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    -(c * deriv U x) +
      p.χ * waveProfileFluxDerivativeRHS p U V x -
        wholeLineReaction p U x

/-- Divergence-form stationary equation with an explicit signal profile `V`. -/
def WaveProfileDivergenceStationaryEquation
    (p : CMParams) (c : ℝ) (U V : ℝ → ℝ) : Prop :=
  ∀ x,
    iteratedDeriv 2 U x + c * deriv U x
      - p.χ * deriv (fun y => (U y) ^ p.m * deriv V y) x
      + wholeLineReaction p U x = 0

theorem waveProfileFluxDerivativeRHS_continuous
    {p : CMParams} {U V : ℝ → ℝ}
    (hU1 : ContDiff ℝ 1 U)
    (hV2 : ContDiff ℝ 2 V) :
    Continuous (waveProfileFluxDerivativeRHS p U V) := by
  have hm_nonneg : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hm_sub_nonneg : 0 ≤ p.m - 1 := sub_nonneg.mpr p.hm
  have hU_cont : Continuous U := hU1.continuous
  have hUd_cont : Continuous (deriv U) :=
    ContDiff.continuous_deriv_one hU1
  have hVd_cont : Continuous (deriv V) :=
    hV2.continuous_deriv (by norm_num)
  have hV2' : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) V := by
    simpa using hV2
  have hVd1 : ContDiff ℝ 1 (deriv V) :=
    (contDiff_succ_iff_deriv.mp hV2').2.2
  have hVdd_cont : Continuous (deriv (deriv V)) :=
    ContDiff.continuous_deriv_one hVd1
  have hpow_m_sub_one : Continuous (fun x : ℝ => (U x) ^ (p.m - 1)) :=
    hU_cont.rpow_const (fun _ => Or.inr hm_sub_nonneg)
  have hpow_m : Continuous (fun x : ℝ => (U x) ^ p.m) :=
    hU_cont.rpow_const (fun _ => Or.inr hm_nonneg)
  have hterm1 :
      Continuous
        (fun x : ℝ =>
          (deriv U x * p.m * (U x) ^ (p.m - 1)) * deriv V x) :=
    (((hUd_cont.mul continuous_const).mul hpow_m_sub_one).mul hVd_cont)
  have hterm2 :
      Continuous (fun x : ℝ => (U x) ^ p.m * deriv (deriv V) x) :=
    hpow_m.mul hVdd_cont
  simpa [waveProfileFluxDerivativeRHS] using hterm1.add hterm2

theorem waveProfileSecondRHS_continuous
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hU1 : ContDiff ℝ 1 U)
    (hV2 : ContDiff ℝ 2 V) :
    Continuous (waveProfileSecondRHS p c U V) := by
  have hα_nonneg : 0 ≤ p.α := le_trans zero_le_one p.hα
  have hU_cont : Continuous U := hU1.continuous
  have hUd_cont : Continuous (deriv U) :=
    ContDiff.continuous_deriv_one hU1
  have hpow_α : Continuous (fun x : ℝ => (U x) ^ p.α) :=
    hU_cont.rpow_const (fun _ => Or.inr hα_nonneg)
  have hreaction : Continuous (wholeLineReaction p U) := by
    simpa [wholeLineReaction] using
      hU_cont.mul (continuous_const.sub hpow_α)
  have hflux : Continuous (waveProfileFluxDerivativeRHS p U V) :=
    waveProfileFluxDerivativeRHS_continuous hU1 hV2
  have hlinear : Continuous (fun x : ℝ => -(c * deriv U x)) :=
    (continuous_const.mul hUd_cont).neg
  have hchem :
      Continuous (fun x : ℝ => p.χ * waveProfileFluxDerivativeRHS p U V x) :=
    continuous_const.mul hflux
  simpa [waveProfileSecondRHS] using (hlinear.add hchem).sub hreaction

theorem waveProfile_flux_deriv_eq
    {p : CMParams} {U V : ℝ → ℝ}
    (hU1 : ContDiff ℝ 1 U)
    (hV2 : ContDiff ℝ 2 V) :
    ∀ x,
      deriv (fun y : ℝ => (U y) ^ p.m * deriv V y) x =
        waveProfileFluxDerivativeRHS p U V x := by
  intro x
  have hU_diff : Differentiable ℝ U :=
    (contDiff_one_iff_deriv.mp hU1).1
  have hV2' : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) V := by
    simpa using hV2
  have hVd1 : ContDiff ℝ 1 (deriv V) :=
    (contDiff_succ_iff_deriv.mp hV2').2.2
  have hVd_diff : Differentiable ℝ (deriv V) :=
    (contDiff_one_iff_deriv.mp hVd1).1
  have hpow :
      HasDerivAt (fun y : ℝ => (U y) ^ p.m)
        (deriv U x * p.m * (U x) ^ (p.m - 1)) x :=
    (hU_diff x).hasDerivAt.rpow_const (Or.inr p.hm)
  have hprod :=
    hpow.mul (hVd_diff x).hasDerivAt
  have hderiv :
      deriv (fun y : ℝ => (U y) ^ p.m * deriv V y) x =
        (deriv U x * p.m * (U x) ^ (p.m - 1)) * deriv V x +
          (U x) ^ p.m * deriv (deriv V) x :=
    hprod.deriv
  simpa [waveProfileFluxDerivativeRHS] using hderiv

theorem waveProfile_second_deriv_eq_of_stationary
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hU1 : ContDiff ℝ 1 U)
    (hV2 : ContDiff ℝ 2 V)
    (hstationary : WaveProfileDivergenceStationaryEquation p c U V) :
    ∀ x, deriv (deriv U) x = waveProfileSecondRHS p c U V x := by
  intro x
  have hflux := waveProfile_flux_deriv_eq (p := p) hU1 hV2 x
  have hstat := hstationary x
  have hiter : iteratedDeriv 2 U x = deriv (deriv U) x := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_one]
  rw [hiter, hflux] at hstat
  have h :
      deriv (deriv U) x =
        (-c) * deriv U x +
          p.χ * waveProfileFluxDerivativeRHS p U V x -
            wholeLineReaction p U x := by
    linarith
  simpa [waveProfileSecondRHS] using h

/--
Bootstrap data for the profile-side `C²` theorem.

`profile_hasDerivAt` and `profile_deriv_continuous` are the C¹ output supplied
by the Leibniz bridge.  `stationary_hasDerivAt` is the stationary equation
written in the derivative-existence form needed by Lean.
-/
structure WholeLineProfileC2Data
    (p : CMParams) (c : ℝ) (U V Ux : ℝ → ℝ) : Prop where
  U_nonneg : ∀ x, 0 ≤ U x
  profile_hasDerivAt : ∀ x, HasDerivAt U (Ux x) x
  profile_deriv_continuous : Continuous Ux
  signal_contDiff_two : ContDiff ℝ 2 V
  stationary_hasDerivAt :
    ∀ x, HasDerivAt (deriv U) (waveProfileSecondRHS p c U V x) x

namespace WholeLineProfileC2Data

theorem waveProfile_contDiff_one
    {p : CMParams} {c : ℝ} {U V Ux : ℝ → ℝ}
    (H : WholeLineProfileC2Data p c U V Ux) :
    ContDiff ℝ 1 U := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (H.profile_hasDerivAt x).differentiableAt, ?_⟩
  have hderiv_eq : deriv U = Ux := by
    funext x
    exact (H.profile_hasDerivAt x).deriv
  rw [hderiv_eq]
  exact H.profile_deriv_continuous

theorem waveProfile_second_deriv_continuous
    {p : CMParams} {c : ℝ} {U V Ux : ℝ → ℝ}
    (H : WholeLineProfileC2Data p c U V Ux) :
    Continuous (deriv (deriv U)) := by
  have hU1 : ContDiff ℝ 1 U := H.waveProfile_contDiff_one
  have hRHS :
      Continuous (waveProfileSecondRHS p c U V) :=
    waveProfileSecondRHS_continuous hU1 H.signal_contDiff_two
  have hderiv_eq :
      deriv (deriv U) = waveProfileSecondRHS p c U V := by
    funext x
    exact (H.stationary_hasDerivAt x).deriv
  rw [hderiv_eq]
  exact hRHS

/-- The profile-side `C²` bootstrap from C¹ plus the stationary equation. -/
theorem waveProfile_contDiff_two
    {p : CMParams} {c : ℝ} {U V Ux : ℝ → ℝ}
    (H : WholeLineProfileC2Data p c U V Ux) :
    ContDiff ℝ 2 U := by
  have hU1 : ContDiff ℝ 1 U := H.waveProfile_contDiff_one
  have hdiff : Differentiable ℝ U :=
    (contDiff_one_iff_deriv.mp hU1).1
  have hderiv_c1 : ContDiff ℝ 1 (deriv U) := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun x => (H.stationary_hasDerivAt x).differentiableAt, ?_⟩
    exact H.waveProfile_second_deriv_continuous
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  exact ⟨hdiff, by simp, hderiv_c1⟩

end WholeLineProfileC2Data

/-- Top-level name requested by the profile-C² task. -/
theorem waveProfile_contDiff_two
    {p : CMParams} {c : ℝ} {U V Ux : ℝ → ℝ}
    (H : WholeLineProfileC2Data p c U V Ux) :
    ContDiff ℝ 2 U :=
  WholeLineProfileC2Data.waveProfile_contDiff_two H

/--
If the divergence-form stationary equation is already known and `deriv U` is
differentiable, it supplies the derivative-form stationary equation consumed
by `WholeLineProfileC2Data`.
-/
theorem stationary_hasDerivAt_of_divergence_stationary
    {p : CMParams} {c : ℝ} {U V : ℝ → ℝ}
    (hU1 : ContDiff ℝ 1 U)
    (hV2 : ContDiff ℝ 2 V)
    (hstationary : WaveProfileDivergenceStationaryEquation p c U V)
    (hUderiv_diff : Differentiable ℝ (deriv U)) :
    ∀ x, HasDerivAt (deriv U) (waveProfileSecondRHS p c U V x) x := by
  intro x
  have hsecond := waveProfile_second_deriv_eq_of_stationary
    hU1 hV2 hstationary x
  convert (hUderiv_diff x).hasDerivAt using 1
  exact hsecond.symm

/--
Constructor that consumes the C¹ Leibniz output, the V-side `C²` result, and
the divergence stationary equation once a separate source has established
existence of `U''`.
-/
def WholeLineProfileC2Data.of_divergence_stationary
    {p : CMParams} {c : ℝ} {U V Ux : ℝ → ℝ}
    (hU_nonneg : ∀ x, 0 ≤ U x)
    (hprofile_hasDerivAt : ∀ x, HasDerivAt U (Ux x) x)
    (hprofile_deriv_continuous : Continuous Ux)
    (hV2 : ContDiff ℝ 2 V)
    (hstationary : WaveProfileDivergenceStationaryEquation p c U V)
    (hUderiv_diff : Differentiable ℝ (deriv U)) :
    WholeLineProfileC2Data p c U V Ux where
  U_nonneg := hU_nonneg
  profile_hasDerivAt := hprofile_hasDerivAt
  profile_deriv_continuous := hprofile_deriv_continuous
  signal_contDiff_two := hV2
  stationary_hasDerivAt :=
    stationary_hasDerivAt_of_divergence_stationary
      (by
        rw [contDiff_one_iff_deriv]
        refine ⟨fun x => (hprofile_hasDerivAt x).differentiableAt, ?_⟩
        have hderiv_eq : deriv U = Ux := by
          funext x
          exact (hprofile_hasDerivAt x).deriv
        rw [hderiv_eq]
        exact hprofile_deriv_continuous)
      hV2 hstationary hUderiv_diff

section AxiomAudit

#print axioms waveProfileFluxDerivativeRHS
#print axioms waveProfileSecondRHS
#print axioms WaveProfileDivergenceStationaryEquation
#print axioms waveProfileFluxDerivativeRHS_continuous
#print axioms waveProfileSecondRHS_continuous
#print axioms waveProfile_flux_deriv_eq
#print axioms waveProfile_second_deriv_eq_of_stationary
#print axioms WholeLineProfileC2Data
#print axioms WholeLineProfileC2Data.waveProfile_contDiff_one
#print axioms WholeLineProfileC2Data.waveProfile_second_deriv_continuous
#print axioms WholeLineProfileC2Data.waveProfile_contDiff_two
#print axioms waveProfile_contDiff_two
#print axioms stationary_hasDerivAt_of_divergence_stationary
#print axioms WholeLineProfileC2Data.of_divergence_stationary

end AxiomAudit

end ShenWork.PaperOne
