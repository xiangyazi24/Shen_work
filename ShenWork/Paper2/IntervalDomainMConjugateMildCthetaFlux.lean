/-
  Positive-time Holder regularity of the nonlinear chemotaxis flux along the
  faithful conjugate-kernel mild solution.

  This is produced from the already-proved positive-time Holder modulus of u
  and the weak bounded-data resolver estimates.  No source-decay or classical
  regularity hypothesis is used.
-/
import ShenWork.Paper2.IntervalDomainMConjugateMildHolderBootstrap
import ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
import ShenWork.Paper2.IntervalResolverWeakBounds
import ShenWork.Paper2.IntervalDuhamelIntegrability

open MeasureTheory
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
  (chemFluxMLifted chemFlux_div_lipschitz_with_massLip)
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM)
open ShenWork.IntervalPositiveFloorNonlinearLipschitz
  (powerLip powerLip_nonneg)

namespace ShenWork.Paper2

noncomputable section

/-- On every positive time slab, the faithful conjugate mild solution's
chemotaxis flux has a uniform small-exponent spatial Holder modulus. -/
theorem conjugateMildM_chemFlux_positiveTime_holder
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {θ τ : ℝ} (hθ0 : 0 < θ) (hθhalf : θ < (1 / 2 : ℝ)) (hτ : 0 < τ) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧ ∀ s ∈ Set.Icc τ D.T,
      ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |chemFluxMLifted p (D.u s) a - chemFluxMLifted p (D.u s) b| ≤
          HQ * |a - b| ^ θ := by
  have hθ1 : θ < 1 := by linarith
  obtain ⟨Hu, hHu, hu_holder⟩ :=
    conjugateMildM_positiveTime_holder D hu₀ hu₀_meas hθ0 hθ1 hτ
  set G : ℝ := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ)) with hG
  set Hg : ℝ := (2 : ℝ) ^ (1 - θ) *
      Real.sqrt (∑' k : ℕ,
        (ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverGradHolderWeight
          p θ k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ)) with hHg
  set Lm : ℝ := powerLip p.m D.c D.M with hLm
  set A : ℝ := D.M ^ p.m with hA
  set HQ : ℝ := (Lm * Hu) * G + A * Hg + A * G * p.β * G with hHQdef
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
  have hcM : D.c ≤ D.M := by
    let x0 : intervalDomainPoint := ⟨0, ⟨le_rfl, zero_le_one⟩⟩
    exact (D.hfloor D.T D.hT le_rfl x0).trans
      ((le_abs_self _).trans (D.hbound D.T D.hT le_rfl x0))
  have hLmnn : 0 ≤ Lm := by
    rw [hLm]
    exact powerLip_nonneg p.hm D.hc hcM
  have hAnn : 0 ≤ A := by
    rw [hA]
    exact Real.rpow_nonneg D.hM.le _
  have hHQnn : 0 ≤ HQ := by
    rw [hHQdef]
    exact add_nonneg
      (add_nonneg (mul_nonneg (mul_nonneg hLmnn hHu) hGnn)
        (mul_nonneg hAnn hHgnn))
      (mul_nonneg (mul_nonneg (mul_nonneg hAnn hGnn) p.hβ) hGnn)
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
    exact (by simpa [intervalDomainLift, hy] using
      D.hc.le.trans (D.hfloor s hs0 hs.2 ⟨y, hy⟩))
  have hub : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (D.u s) y ≤ D.M := by
    intro y hy
    have h := D.hbound s hs0 hs.2 ⟨y, hy⟩
    simpa [intervalDomainLift, hy] using (abs_le.mp h).2
  have hstrip : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (D.u s) y ∈ Set.Icc D.c D.M := by
    intro y hy
    exact ⟨by simpa [intervalDomainLift, hy] using
        D.hfloor s hs0 hs.2 ⟨y, hy⟩,
      hub y hy⟩
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
      (T := D.T) p (u := D.u)
        (fun t ht htT x => D.hc.le.trans (D.hfloor t ht htT x))
        D.hcont hs0 hs.2 ⟨y, hy⟩
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
  have hmass :
      |intervalDomainLift (D.u s) a ^ p.m -
          intervalDomainLift (D.u s) b ^ p.m| ≤
        (Lm * Hu) * |a - b| ^ θ := by
    have hp := rpow_lipschitz_on_pos_Icc p.hm D.hc (hstrip a ha) (hstrip b hb)
    calc
      _ ≤ Lm * |intervalDomainLift (D.u s) a -
          intervalDomainLift (D.u s) b| := by simpa [hLm] using hp
      _ ≤ Lm * (Hu * |a - b| ^ θ) :=
        mul_le_mul_of_nonneg_left (hu_holder_lift a b ha hb) hLmnn
      _ = (Lm * Hu) * |a - b| ^ θ := by ring
  have hmass_b : |intervalDomainLift (D.u s) b ^ p.m| ≤ A := by
    rw [abs_of_nonneg (Real.rpow_nonneg (hlb b hb) _), hA]
    exact Real.rpow_le_rpow (hlb b hb) (hub b hb) p.hm.le
  have hd : 0 ≤ |a - b| ^ θ := Real.rpow_nonneg (abs_nonneg _) _
  rw [hHQdef]
  exact chemFlux_div_lipschitz_with_massLip p.hβ hmass_b
    (hg_bound a ha) (hg_bound b hb) (hR_nonneg a ha) (hR_nonneg b hb)
    hmass (hg_holder a b ha hb) (hR_holder a b ha hb)
    hAnn hGnn (mul_nonneg hLmnn hHu) hHgnn hGnn hd

end

end ShenWork.Paper2

#print axioms ShenWork.Paper2.conjugateMildM_chemFlux_positiveTime_holder
