/-
  ShenWork/Paper2/IntervalResolverHolder.lean

  Spatial Holder wrappers for the elliptic resolver value.

  The theorem in this file is intentionally a thin consumer of the existing
  source-decay regularity in `IntervalResolverSpatialC2`: it proves the missing
  value-side Holder modulus needed by the chemotaxis-flux component algebra.
-/
import ShenWork.Paper2.IntervalDomainL2UEnergyCombine
import ShenWork.PDE.IntervalResolverSpatialC2

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.PDE (intervalNeumannResolverR intervalNeumannResolverCoeff)
open ShenWork.CosineSpectrum

namespace ShenWork.Paper2

noncomputable section

/-- Resolver value is `θ`-Holder on `[0,1]` from source quadratic decay.

The proof runs the mean-value inequality on the global cosine series supplied by
`IntervalResolverSpatialC2`, then rewrites the endpoint values back to the
zero-extension `intervalDomainLift` only after the closed-interval estimate is
obtained. -/
theorem intervalNeumannResolverR_lift_holder_Icc_of_sourceDecay
    {p : CM2Params} {w : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p w)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ Hv : ℝ, 0 ≤ Hv ∧
      ∀ x y, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
        |intervalDomainLift (intervalNeumannResolverR p w) x -
          intervalDomainLift (intervalNeumannResolverR p w) y| ≤
            Hv * |x - y| ^ θ := by
  classical
  let F : ℝ → ℝ := fun x =>
    ∑' k : ℕ, (intervalNeumannResolverCoeff p w k).re * cosineMode k x
  have hFcd : ContDiff ℝ 2 F := by
    simpa [F] using
      (ShenWork.IntervalResolverSpatialC2.resolverR_contDiff_two
        (p := p) (u := w) hdecay)
  have hFdiff : ∀ x ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ F x :=
    fun x _ => (hFcd.differentiable (by norm_num)).differentiableAt
  have hderiv_cont : ContinuousOn (fun x : ℝ => deriv F x) (Set.Icc (0 : ℝ) 1) :=
    (hFcd.continuous_deriv (by norm_num)).continuousOn
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hderiv_cont
  let Hv : ℝ := max B 0
  have hHv_nonneg : 0 ≤ Hv := by
    dsimp [Hv]
    exact le_max_right _ _
  refine ⟨Hv, hHv_nonneg, ?_⟩
  intro x y hx hy
  have hderiv_bound : ∀ z ∈ Set.Icc (0 : ℝ) 1, ‖deriv F z‖ ≤ Hv := by
    intro z hz
    exact (hB z hz).trans (le_max_left _ _)
  have hmvt :=
    (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (f := F) (s := Set.Icc (0 : ℝ) 1)
      hFdiff hderiv_bound hx hy
  have hmvt_abs : |F x - F y| ≤ Hv * |x - y| := by
    simpa [Real.norm_eq_abs, abs_sub_comm] using hmvt
  have hdist_le_one : |x - y| ≤ 1 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hdist_le_pow : |x - y| ≤ |x - y| ^ θ := by
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge'
        (x := |x - y|) (y := 1) (z := θ)
        (abs_nonneg _) hdist_le_one hθ0.le hθ1)
  have hF_holder : |F x - F y| ≤ Hv * |x - y| ^ θ := by
    exact hmvt_abs.trans (mul_le_mul_of_nonneg_left hdist_le_pow hHv_nonneg)
  have hxF :
      intervalDomainLift (intervalNeumannResolverR p w) x = F x := by
    simp only [intervalDomainLift, hx, dif_pos, F]
    exact ShenWork.IntervalResolverSpatialC2.resolverR_eq_cosineSeries
      (p := p) (u := w) ⟨x, hx⟩
  have hyF :
      intervalDomainLift (intervalNeumannResolverR p w) y = F y := by
    simp only [intervalDomainLift, hy, dif_pos, F]
    exact ShenWork.IntervalResolverSpatialC2.resolverR_eq_cosineSeries
      (p := p) (u := w) ⟨y, hy⟩
  simpa [hxF, hyF] using hF_holder

end

end ShenWork.Paper2
