import ShenWork.Paper1.WholeLineCauchyC1HolderBootstrap

open Filter Topology MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Positive-time C1 regularity of the whole-line chemotaxis flux

The clamp is not differentiated.  On a physical slice it is first removed,
and the ordinary product rule is applied to the unclamped flux.  A global
bound for the population derivative follows from boundedness of the slice,
its Holder derivative, and the mean value theorem on unit intervals.
-/

/-- A globally bounded differentiable function with a globally Holder
derivative has a globally bounded derivative. -/
theorem deriv_abs_le_of_bounded_of_deriv_holder
    {f : ℝ → ℝ} {M H eta : ℝ}
    (hH : 0 ≤ H) (heta0 : 0 < eta)
    (hbound : ∀ x, |f x| ≤ M)
    (hdiff : ∀ x, DifferentiableAt ℝ f x)
    (hholder : ∀ x y, |deriv f x - deriv f y| ≤ H * |x - y| ^ eta) :
    ∀ x, |deriv f x| ≤ H + 2 * M := by
  intro x
  have hxx : x < x + 1 := by linarith
  have hcont : Continuous f := continuous_iff_continuousAt.2 fun q =>
    (hdiff q).continuousAt
  obtain ⟨c, hc, hcEq⟩ := exists_deriv_eq_slope f hxx
    hcont.continuousOn (fun q _ => (hdiff q).differentiableWithinAt)
  have hcEq' : deriv f c = f (x + 1) - f x := by
    convert hcEq using 1 <;> ring
  have hcBound : |deriv f c| ≤ 2 * M := by
    rw [hcEq']
    calc
      |f (x + 1) - f x| ≤ |f (x + 1)| + |f x| := abs_sub _ _
      _ ≤ M + M := add_le_add (hbound _) (hbound _)
      _ = 2 * M := by ring
  have hxc : |x - c| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hc.1.le)]
    linarith [hc.2]
  have hxcpow : |x - c| ^ eta ≤ 1 :=
    Real.rpow_le_one (abs_nonneg _) hxc heta0.le
  calc
    |deriv f x| = |(deriv f x - deriv f c) + deriv f c| := by ring_nf
    _ ≤ |deriv f x - deriv f c| + |deriv f c| := abs_add_le _ _
    _ ≤ H * |x - c| ^ eta + 2 * M :=
      add_le_add (hholder x c) hcBound
    _ ≤ H * 1 + 2 * M :=
      add_le_add (mul_le_mul_of_nonneg_left hxcpow hH) le_rfl
    _ = H + 2 * M := by ring

/-- On a physical positive-time slice, the canonical population derivative
is globally bounded. -/
theorem wholeLineCauchyBUCMildFixedPoint_spatial_deriv_bounded_positive
    (p : CMParams) {M T theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      |deriv (fun w : ℝ =>
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 w) x| ≤ B := by
  let f : ℝ → ℝ := fun w =>
    (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 w
  rcases wholeLineCauchyBUCMildFixedPoint_spatial_deriv_Ceta
      p hM hT u₀ hsmall z hz htheta0 htheta1 heta0 heta1 hrel with
    ⟨H, hH, hholder⟩
  let B : ℝ := H + 2 * M
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  have hbound : ∀ x, |f x| ≤ M := by
    intro x
    rw [abs_of_nonneg (hstrip x).1]
    exact (hstrip x).2
  have hdiff : ∀ x, DifferentiableAt ℝ f x := by
    intro x
    exact (wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
      p hM hT u₀ hsmall z hz x).differentiableAt
  intro x
  exact deriv_abs_le_of_bounded_of_deriv_holder hH heta0
    hbound hdiff hholder x

/-- Product-rule derivative of the physical whole-line chemotaxis flux. -/
theorem wholeLineChemotaxisFlux_hasDerivAt
    (p : CMParams) {u : ℝ → ℝ} {x ux : ℝ}
    (hu : IsCUnifBdd u) (hu0 : ∀ y, 0 ≤ u y)
    (hux : HasDerivAt u ux x) :
    HasDerivAt (wholeLineChemotaxisFlux p u)
      (p.m * (u x) ^ (p.m - 1) * ux * deriv (frozenElliptic p u) x +
        (u x) ^ p.m * (frozenElliptic p u x - (u x) ^ p.γ)) x := by
  have hpow : HasDerivAt (fun y : ℝ => (u y) ^ p.m)
      (ux * p.m * (u x) ^ (p.m - 1)) x :=
    hux.rpow_const (Or.inr p.hm)
  have hresolver : HasDerivAt (deriv (frozenElliptic p u))
      (deriv (deriv (frozenElliptic p u)) x) x :=
    (frozenElliptic_deriv_differentiableAt p hu hu0 x).hasDerivAt
  have hmul := hpow.mul hresolver
  have hode := frozenElliptic_deriv_deriv_eq p hu hu0 x
  convert hmul using 1
  rw [hode]
  ring

/-- Once the clamp is inactive, the actual flux-source slice is genuinely
differentiable and obeys the physical product/elliptic derivative formula. -/
theorem wholeLineCauchyFluxSourceTrajectory_slice_hasDerivAt_positive
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (hstrip : ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) (x : ℝ) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    HasDerivAt
      (wholeLineCauchyFluxSourceTrajectory p hM hT U z.1).1
      (p.m * ((U z).1 x) ^ (p.m - 1) * deriv (U z).1 x *
          deriv (frozenElliptic p (U z).1) x +
        ((U z).1 x) ^ p.m *
          (frozenElliptic p (U z).1 x - ((U z).1 x) ^ p.γ)) x := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  have hext : wholeLineBUCTrajectoryExtend hT U z.1 = U z :=
    wholeLineBUCTrajectoryExtend_eq hT U z.2
  have hfluxEq :
      (wholeLineCauchyFluxSourceTrajectory p hM hT U z.1).1 =
        wholeLineChemotaxisFlux p (U z).1 := by
    funext y
    simpa [wholeLineCauchyFluxSourceTrajectory, hext] using congrFun
      (wholeLineCauchyTruncatedFlux_eq_of_mem_Icc p hM hstrip) y
  have huDeriv : HasDerivAt (U z).1 (deriv (U z).1 x) x := by
    exact (wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
      p hM hT u₀ hsmall z hz x).differentiableAt.hasDerivAt
  rw [hfluxEq]
  exact wholeLineChemotaxisFlux_hasDerivAt p
    (WholeLineBUC.isCUnifBdd (U z)) (fun y => (hstrip y).1) huDeriv

section WholeLineCauchyFluxC1BootstrapAxiomAudit

#print axioms deriv_abs_le_of_bounded_of_deriv_holder
#print axioms wholeLineCauchyBUCMildFixedPoint_spatial_deriv_bounded_positive
#print axioms wholeLineChemotaxisFlux_hasDerivAt
#print axioms wholeLineCauchyFluxSourceTrajectory_slice_hasDerivAt_positive

end WholeLineCauchyFluxC1BootstrapAxiomAudit

end ShenWork.Paper1
