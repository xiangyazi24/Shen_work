/-
  Positive-time Holder regularity of the nonlinear chemotaxis flux along the
  faithful conjugate-kernel mild solution.

  This is produced from the already-proved positive-time Holder modulus of u
  and the weak bounded-data resolver estimates.  No source-decay or classical
  regularity hypothesis is used.
-/
import ShenWork.Paper2.IntervalConjugateMildHolderBootstrap
import ShenWork.Paper2.IntervalChemFluxHolderFrontier
import ShenWork.Paper2.IntervalResolverWeakBounds
import ShenWork.Paper2.IntervalDuhamelIntegrability

open MeasureTheory
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.IntervalConjugatePicard (ConjugateMildSolutionData)

namespace ShenWork.Paper2

noncomputable section

/-- On every positive time slab, the faithful conjugate mild solution's
chemotaxis flux has a uniform small-exponent spatial Holder modulus. -/
theorem conjugateMild_chemFlux_positiveTime_holder
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {θ τ : ℝ} (hθ0 : 0 < θ) (hθhalf : θ < (1 / 2 : ℝ)) (hτ : 0 < τ) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧ ∀ s ∈ Set.Icc τ D.T,
      ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |chemFluxLifted p (D.u s) a - chemFluxLifted p (D.u s) b| ≤
          HQ * |a - b| ^ θ := by
  have hθ1 : θ < 1 := by linarith
  obtain ⟨Hu, hHu, hu_holder⟩ :=
    conjugateMild_positiveTime_holder D hu₀ hu₀_meas hθ0 hθ1 hτ
  set G : ℝ := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ)) with hG
  set Hg : ℝ := (2 : ℝ) ^ (1 - θ) *
      Real.sqrt (∑' k : ℕ,
        (ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverGradHolderWeight
          p θ k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ)) with hHg
  set HQ : ℝ := Hu * G + D.M * Hg + D.M * G * p.β * G with hHQdef
  have hGnn : 0 ≤ G := by
    rw [hG]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _)))
  have hHgnn : 0 ≤ Hg := by
    rw [hHg]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
        (Real.sqrt_nonneg _))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _)))
  have hHQnn : 0 ≤ HQ := by
    rw [hHQdef]
    exact add_nonneg
      (add_nonneg (mul_nonneg hHu hGnn) (mul_nonneg D.hM.le hHgnn))
      (mul_nonneg (mul_nonneg (mul_nonneg D.hM.le hGnn) p.hβ) hGnn)
  refine ⟨HQ, hHQnn, ?_⟩
  intro s hs a b ha hb
  have hs0 : 0 < s := lt_of_lt_of_le hτ hs.1
  have hUcont : ContinuousOn (intervalDomainLift (D.u s)) (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : Set.restrict (Set.Icc (0 : ℝ) 1)
        (intervalDomainLift (D.u s)) = D.u s := by
      ext ⟨y, hy⟩
      simp [Set.restrict, intervalDomainLift, hy]
      rfl
    rw [heq]
    exact D.hcont s hs0 hs.2
  have hlb : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ intervalDomainLift (D.u s) y := by
    intro y hy
    simpa [intervalDomainLift, hy] using D.hnonneg s hs0 hs.2 ⟨y, hy⟩
  have hub : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (D.u s) y ≤ D.M := by
    intro y hy
    have h := D.hbound s hs0 hs.2 ⟨y, hy⟩
    simpa [intervalDomainLift, hy] using (abs_le.mp h).2
  have hu_bound : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift (D.u s) y| ≤ D.M := by
    intro y hy
    simpa [intervalDomainLift, hy] using D.hbound s hs0 hs.2 ⟨y, hy⟩
  have hg_bound : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |resolverGradReal p (D.u s) y| ≤ G := by
    intro y hy
    rw [hG]
    exact ShenWork.IntervalResolverWeakBounds.resolverGrad_sup_le_of_bounded
      p hUcont hlb hub hy
  have hR_nonneg : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (D.u s)) y := by
    intro y hy
    have h := ShenWork.IntervalMildToClassical.mildChemical_nonneg
      (T := D.T) p (u := D.u) D.hnonneg D.hcont hs0 hs.2 ⟨y, hy⟩
    simpa [ShenWork.IntervalMildToClassical.mildChemicalConcentration,
      intervalDomainLift, hy] using h
  have hu_holder_lift : ∀ x y : ℝ,
      x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
        |intervalDomainLift (D.u s) x - intervalDomainLift (D.u s) y| ≤
          Hu * |x - y| ^ θ := by
    intro x y hx hy
    simpa [intervalDomainLift, hx, hy] using
      hu_holder s hs ⟨x, hx⟩ ⟨y, hy⟩
  have hg_holder : ∀ x y : ℝ,
      x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
        |resolverGradReal p (D.u s) x - resolverGradReal p (D.u s) y| ≤
          Hg * |x - y| ^ θ := by
    intro x y hx hy
    rw [hHg]
    exact ShenWork.IntervalResolverWeakBounds.resolverGradReal_holder_Icc_of_bounded_smallTheta
      p hθ0 hθhalf hUcont hlb hub hx hy
  have hR_holder : ∀ x y : ℝ,
      x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
        |intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (D.u s)) x -
            intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (D.u s)) y| ≤
          G * |x - y| ^ θ := by
    intro x y hx hy
    rw [hG]
    exact ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverR_lift_holder_Icc_of_bounded
      p hθ0 hθ1.le hUcont hlb hub hx hy
  rw [hHQdef]
  exact chemFluxLifted_holder_of_component_holder
    (p := p) (w := D.u s) (θ := θ) (U := D.M) (G := G)
    (Hu := Hu) (Hg := Hg) (Hv := G)
    D.hM.le hGnn hHu hHgnn hu_bound hg_bound hR_nonneg
    hu_holder_lift hg_holder hR_holder a b ha hb

end

end ShenWork.Paper2

