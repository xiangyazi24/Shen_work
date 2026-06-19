import ShenWork.PaperOne.WholeLineDiagonalEquation
import ShenWork.PaperOne.WholeLineAuxiliaryExistence
import Mathlib.Tactic

open MeasureTheory Filter Topology Real Set
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-!
Spatial `C²` assembly for the whole-line profile and the auxiliary mild flow.

The resolvent part is closed here from the banked whole-line Green kernel
facts: `V = Ψ(U^γ)` is `C²` and satisfies `V'' = V - U^γ`.  The remaining
singular parabolic second-differentiation step is carried as an explicitly
named Duhamel hypothesis, as requested.
-/

/-- The whole-line resolvent maps a continuous bounded nonnegative source to a
`C²` function.  The second derivative is continuous because the elliptic
identity rewrites it as `Ψ f - f`. -/
theorem wholeLineResolvent_contDiff_two {f : ℝ → ℝ}
    (hf : IsCUnifBdd f) (hf_nonneg : ∀ x, 0 ≤ f x) :
    ContDiff ℝ 2 (wholeLineResolvent f) := by
  have hfun : wholeLineResolvent f = fun z : ℝ => Psi f 1 1 z := by
    funext z
    exact wholeLineResolvent_eq_Psi f z
  rw [hfun]
  have hdiff : Differentiable ℝ (fun z : ℝ => Psi f 1 1 z) :=
    Psi_differentiable one_pos one_pos hf
  have hderiv_diff :
      Differentiable ℝ (deriv (fun z : ℝ => Psi f 1 1 z)) :=
    fun x => Psi_deriv_differentiableAt one_pos one_pos hf x
  have hsecond_cont :
      Continuous (deriv (deriv (fun z : ℝ => Psi f 1 1 z))) := by
    have hsecond_eq :
        deriv (deriv (fun z : ℝ => Psi f 1 1 z)) =
          fun x : ℝ => Psi f 1 1 x - f x := by
      funext x
      have hode :=
        Psi_elliptic_ode (u := f) (l := 1) (mu := 1)
          one_pos one_pos hf hf_nonneg x
      have hiter :
          iteratedDeriv 2 (fun z : ℝ => Psi f 1 1 z) x =
            Psi f 1 1 x - f x := by
        linarith
      simpa [iteratedDeriv_succ, iteratedDeriv_zero] using hiter
    rw [hsecond_eq]
    exact (Psi_continuous one_pos one_pos hf).sub hf.1
  have hderiv_c1 :
      ContDiff ℝ 1 (deriv (fun z : ℝ => Psi f 1 1 z)) := by
    rw [contDiff_one_iff_deriv]
    exact ⟨hderiv_diff, hsecond_cont⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  exact ⟨hdiff, by simp, hderiv_c1⟩

/-- Frozen whole-line signal regularity, with the source `U^γ`. -/
theorem frozenSignal_contDiff_two (p : CMParams) {U : ℝ → ℝ}
    (hU_bdd : IsCUnifBdd U) (hU_nonneg : ∀ x, 0 ≤ U x) :
    ContDiff ℝ 2 (frozenSignal p.γ U) := by
  unfold frozenSignal
  exact wholeLineResolvent_contDiff_two
    (f := fun y : ℝ => (U y) ^ p.γ)
    (wholeLine_rpow_source_cunif_bdd p.hγ hU_bdd hU_nonneg)
    (fun y => Real.rpow_nonneg (hU_nonneg y) p.γ)

/--
Profile regularity data after the gradient-Duhamel and second-Duhamel
differentiation steps.

The second Duhamel fields are deliberately stated after receiving the
resolvent identity `V'' = V - U^γ`; this records exactly where the chemotaxis
second derivative has been reduced to the elliptic resolvent term.
-/
structure WholeLineProfileRegularityData
    (p : CMParams) (U V Ux Uxx : ℝ → ℝ) : Prop where
  U_bdd : IsCUnifBdd U
  U_nonneg : ∀ x, 0 ≤ U x
  signal_eq : V = frozenSignal p.γ U
  gradientDuhamel_hasDerivAt : ∀ x, HasDerivAt U (Ux x) x
  gradientDuhamel_continuous : Continuous Ux
  secondDuhamel_hasDerivAt_after_resolvent :
    (∀ x, deriv (deriv V) x = V x - (U x) ^ p.γ) →
      ∀ x, HasDerivAt (deriv U) (Uxx x) x
  secondDuhamel_continuous_after_resolvent :
    (∀ x, deriv (deriv V) x = V x - (U x) ^ p.γ) →
      Continuous Uxx

namespace WholeLineProfileRegularityData

/-- The closed resolvent identity used by the profile second-Duhamel step. -/
theorem signal_second_deriv
    {p : CMParams} {U V Ux Uxx : ℝ → ℝ}
    (H : WholeLineProfileRegularityData p U V Ux Uxx) :
    ∀ x, deriv (deriv V) x = V x - (U x) ^ p.γ := by
  intro x
  rw [H.signal_eq]
  exact wholeLine_frozenSignal_second_deriv p H.U_bdd H.U_nonneg x

/-- The frozen signal in the profile certificate is `C²`. -/
theorem waveSignal_contDiff_two
    {p : CMParams} {U V Ux Uxx : ℝ → ℝ}
    (H : WholeLineProfileRegularityData p U V Ux Uxx) :
    ContDiff ℝ 2 V := by
  rw [H.signal_eq]
  exact frozenSignal_contDiff_two p H.U_bdd H.U_nonneg

/-- C¹ regularity of the profile from the gradient-Duhamel representation. -/
theorem waveProfile_contDiff_one
    {p : CMParams} {U V Ux Uxx : ℝ → ℝ}
    (H : WholeLineProfileRegularityData p U V Ux Uxx) :
    ContDiff ℝ 1 U := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (H.gradientDuhamel_hasDerivAt x).differentiableAt, ?_⟩
  have hderiv_eq : deriv U = Ux := by
    funext x
    exact (H.gradientDuhamel_hasDerivAt x).deriv
  rw [hderiv_eq]
  exact H.gradientDuhamel_continuous

/--
`C²` regularity of the wave profile.

This consumes the second-Duhamel differentiability hypothesis only after the
resolvent identity has been produced from `V = frozenSignal p.γ U`.
-/
theorem waveProfile_contDiff_two
    {p : CMParams} {U V Ux Uxx : ℝ → ℝ}
    (H : WholeLineProfileRegularityData p U V Ux Uxx) :
    ContDiff ℝ 2 U := by
  have hVxx := H.signal_second_deriv
  have hdiff : Differentiable ℝ U :=
    fun x => (H.gradientDuhamel_hasDerivAt x).differentiableAt
  have hderiv_c1 : ContDiff ℝ 1 (deriv U) := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun x =>
      (H.secondDuhamel_hasDerivAt_after_resolvent hVxx x).differentiableAt, ?_⟩
    have hderiv2_eq : deriv (deriv U) = Uxx := by
      funext x
      exact (H.secondDuhamel_hasDerivAt_after_resolvent hVxx x).deriv
    rw [hderiv2_eq]
    exact H.secondDuhamel_continuous_after_resolvent hVxx
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  exact ⟨hdiff, by simp, hderiv_c1⟩

end WholeLineProfileRegularityData

/-- Spatial slice of the auxiliary mild map. -/
def auxiliaryMildSpatialSlice
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ)
    (W Wx : ℝ → ℝ → ℝ) (V Vx : ℝ → ℝ) (t : ℝ) : ℝ → ℝ :=
  fun x => auxiliaryMildMap p c Uplus W Wx V Vx t x

/-- The gradient-Duhamel profile expected from differentiating the auxiliary
mild map once in space. -/
def auxiliaryMildGradientProfile
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ)
    (W Wx : ℝ → ℝ → ℝ) (V Vx : ℝ → ℝ) (t : ℝ) : ℝ → ℝ :=
  fun x =>
    movingFrameHeatGradOp c t Uplus x +
      auxiliaryGradDuhamel p c W Wx V Vx t x

/-- C¹ data for the auxiliary mild slice from the gradient-Duhamel formula. -/
structure AuxiliaryMildGradientDuhamelRegularity
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ)
    (W Wx : ℝ → ℝ → ℝ) (V Vx : ℝ → ℝ) (t : ℝ) : Prop where
  hasDerivAt :
    ∀ x,
      HasDerivAt
        (auxiliaryMildSpatialSlice p c Uplus W Wx V Vx t)
        (auxiliaryMildGradientProfile p c Uplus W Wx V Vx t x) x
  continuous_gradient :
    Continuous (auxiliaryMildGradientProfile p c Uplus W Wx V Vx t)

/-- The second-Duhamel frontier for an auxiliary mild slice. -/
structure AuxiliaryMildSecondDuhamelRegularity
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ)
    (W Wx : ℝ → ℝ → ℝ) (V Vx : ℝ → ℝ) (t : ℝ)
    (secondProfile : ℝ → ℝ) : Prop where
  gradient :
    AuxiliaryMildGradientDuhamelRegularity p c Uplus W Wx V Vx t
  hasSecondDerivAt :
    ∀ x,
      HasDerivAt
        (deriv (auxiliaryMildSpatialSlice p c Uplus W Wx V Vx t))
        (secondProfile x) x
  continuous_second : Continuous secondProfile

/-- Auxiliary-flow spatial `C¹` from the gradient-Duhamel formula. -/
theorem auxiliaryMildSpatialSlice_contDiff_one_of_gradientDuhamel
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ}
    {W Wx : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ} {t : ℝ}
    (H : AuxiliaryMildGradientDuhamelRegularity p c Uplus W Wx V Vx t) :
    ContDiff ℝ 1 (auxiliaryMildSpatialSlice p c Uplus W Wx V Vx t) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (H.hasDerivAt x).differentiableAt, ?_⟩
  have hderiv_eq :
      deriv (auxiliaryMildSpatialSlice p c Uplus W Wx V Vx t) =
        auxiliaryMildGradientProfile p c Uplus W Wx V Vx t := by
    funext x
    exact (H.hasDerivAt x).deriv
  rw [hderiv_eq]
  exact H.continuous_gradient

/-- Auxiliary-flow spatial `C²` from second differentiation of Duhamel. -/
theorem auxiliaryMildSpatialSlice_contDiff_two_of_secondDuhamel
    {p : CMParams} {c : ℝ} {Uplus : ℝ → ℝ}
    {W Wx : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ} {t : ℝ}
    {secondProfile : ℝ → ℝ}
    (H : AuxiliaryMildSecondDuhamelRegularity p c Uplus W Wx V Vx t secondProfile) :
    ContDiff ℝ 2 (auxiliaryMildSpatialSlice p c Uplus W Wx V Vx t) := by
  have hdiff :
      Differentiable ℝ (auxiliaryMildSpatialSlice p c Uplus W Wx V Vx t) :=
    fun x => (H.gradient.hasDerivAt x).differentiableAt
  have hderiv_c1 :
      ContDiff ℝ 1
        (deriv (auxiliaryMildSpatialSlice p c Uplus W Wx V Vx t)) := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun x => (H.hasSecondDerivAt x).differentiableAt, ?_⟩
    have hderiv2_eq :
        deriv (deriv (auxiliaryMildSpatialSlice p c Uplus W Wx V Vx t)) =
          secondProfile := by
      funext x
      exact (H.hasSecondDerivAt x).deriv
    rw [hderiv2_eq]
    exact H.continuous_second
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  exact ⟨hdiff, by simp, hderiv_c1⟩

section AxiomAudit

#print axioms wholeLineResolvent_contDiff_two
#print axioms frozenSignal_contDiff_two
#print axioms WholeLineProfileRegularityData.signal_second_deriv
#print axioms WholeLineProfileRegularityData.waveSignal_contDiff_two
#print axioms WholeLineProfileRegularityData.waveProfile_contDiff_one
#print axioms WholeLineProfileRegularityData.waveProfile_contDiff_two
#print axioms auxiliaryMildSpatialSlice_contDiff_one_of_gradientDuhamel
#print axioms auxiliaryMildSpatialSlice_contDiff_two_of_secondDuhamel

end AxiomAudit

end ShenWork.PaperOne
