import ShenWork.Paper3.IntervalDomainEntropyStrong2Rate

/-! # Dynamic dissipation slices in the second strong-logistic branch -/

namespace ShenWork.Paper3

open Filter Topology Set
open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

/-- Late-slice version of the nonnegative-energy argument: the dissipation
inequality is only required from the supplied starting time onward. -/
theorem exists_late_dissipation_lt_of_nonnegative_energy_on_Ici
    {E D slope : ℝ → ℝ} {c T q : ℝ}
    (hc : 0 < c) (hT : 0 < T) (hq : 0 < q)
    (hE : ∀ t, 0 < t → 0 ≤ E t)
    (hderiv : ∀ t, 0 < t → HasDerivAt E (slope t) t)
    (hdiss : ∀ t, T ≤ t → slope t ≤ -c * D t) :
    ∃ t, T ≤ t ∧ D t < q := by
  by_contra hsmall
  push_neg at hsmall
  have hcq : 0 < c * q := mul_pos hc hq
  let L : ℝ := E T / (c * q) + 1
  let b : ℝ := T + L
  let F : ℝ → ℝ := fun t => E t + c * q * t
  have hET : 0 ≤ E T := hE T hT
  have hL : 0 < L := by
    dsimp [L]
    have : 0 ≤ E T / (c * q) := div_nonneg hET hcq.le
    linarith
  have hTb : T ≤ b := by dsimp [b]; linarith
  have hb : 0 < b := lt_of_lt_of_le hT hTb
  have hFderiv : ∀ t, 0 < t → HasDerivAt F (slope t + c * q) t := by
    intro t ht
    have hlin : HasDerivAt (fun s : ℝ => c * q * s) (c * q) t := by
      simpa using (hasDerivAt_id t).const_mul (c * q)
    simpa [F] using (hderiv t ht).add hlin
  have hFcont : ContinuousOn F (Set.Icc T b) := by
    intro t ht
    exact (hFderiv t (lt_of_lt_of_le hT ht.1)).continuousAt.continuousWithinAt
  have hFdiff : DifferentiableOn ℝ F (Set.Ioo T b) := by
    intro t ht
    exact (hFderiv t (lt_trans hT ht.1)).differentiableAt.differentiableWithinAt
  have hFderiv_nonpos : ∀ t ∈ interior (Set.Icc T b), deriv F t ≤ 0 := by
    intro t ht
    rw [interior_Icc] at ht
    have ht0 : 0 < t := lt_trans hT ht.1
    rw [(hFderiv t ht0).deriv]
    have hD : q ≤ D t := hsmall t ht.1.le
    have hcD : c * q ≤ c * D t := mul_le_mul_of_nonneg_left hD hc.le
    linarith [hdiss t ht.1.le]
  have hanti : AntitoneOn F (Set.Icc T b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hFcont
    · rw [interior_Icc]
      exact hFdiff
    · exact hFderiv_nonpos
  have hFb : F b ≤ F T :=
    hanti (Set.left_mem_Icc.mpr hTb) (Set.right_mem_Icc.mpr hTb) hTb
  have hcancel : c * q * (E T / (c * q)) = E T := by
    field_simp [hcq.ne']
  have hEb : E b ≤ -(c * q) := by
    dsimp [F, b, L] at hFb
    nlinarith [hcancel]
  exact (not_lt_of_ge (hE b hb))
    (lt_of_le_of_lt hEb (neg_neg_of_pos hcq))

/-- Every positive bounded global orbit in branch two has arbitrarily late
small theta-dissipation slices. -/
theorem intervalDomain_strong2_exists_late_thetaDissipation_lt
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b) (hβ : 1 ≤ p.β)
    (hrel : 2 * p.γ ≤ p.α + 1)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong2Formula p
      (positiveEquilibrium p ⟨ha, hb⟩).1)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    {T q : ℝ} (hq : 0 < q) :
    ∃ t, T ≤ t ∧
      chemotaxisThetaDissipation intervalDomain
        (positiveEquilibrium p ⟨ha, hb⟩).1 p.α (u t) < q := by
  let uStar := (positiveEquilibrium p ⟨ha, hb⟩).1
  let vStar := (positiveEquilibrium p ⟨ha, hb⟩).2
  let c := strong2EntropyCoefficient p uStar
  have heq : Paper3ConstantEquilibrium p uStar vStar := by
    simpa [uStar, vStar] using paper3ConstantEquilibrium_positive p ha hb
  have hc : 0 < c := strong2EntropyCoefficient_pos_of_chi_lt
    p hm ha hb heq.u_pos hχpos (by simpa [uStar] using hχ)
  have hevFloor := intervalDomain_strong2_eventually_vABLower
    p hm ha hb hβ hχpos hχ huv
  rcases eventually_atTop.1 hevFloor with ⟨Tv, hTv⟩
  let Tbase : ℝ := max (max T Tv) 1
  have hTbase : 0 < Tbase :=
    lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hTle : T ≤ Tbase :=
    (le_max_left T Tv).trans (le_max_left (max T Tv) 1)
  have hTvle : Tv ≤ Tbase :=
    (le_max_right T Tv).trans (le_max_left (max T Tv) 1)
  obtain ⟨t, htbase, htSmall⟩ :=
    exists_late_dissipation_lt_of_nonnegative_energy_on_Ici
      (E := fun s => chemotaxisEntropyFunctional intervalDomain 1 uStar u s)
      (D := fun s => chemotaxisThetaDissipation intervalDomain uStar p.α (u s))
      (slope := fun s => intervalDomain.integral (fun x =>
        (1 - uStar / u s x) * intervalDomain.timeDeriv u s x))
      hc hTbase hq
      (fun s hs =>
        intervalDomain_chemotaxisEntropyFunctional_nonneg_of_positiveGlobalBoundedSolution
          (by norm_num) heq.u_pos huv hs)
      (intervalDomain_strong1Entropy_hasDerivAt p heq huv)
      (fun s hs => by
        have hs0 : 0 < s := lt_of_lt_of_le hTbase hs
        have hH : 0 < s + 1 := by linarith
        exact intervalDomain_entropySlope_le_strong2Coefficient
          hm (huv.classical (s + 1) hH) hs0 (by linarith) heq hrel
          (vABLowerFormula_pos p ha hb (by rw [hm])).le
          (hTv s (hTvle.trans hs)))
  exact ⟨t, hTle.trans htbase, by simpa [uStar] using htSmall⟩

#print axioms exists_late_dissipation_lt_of_nonnegative_energy_on_Ici
#print axioms intervalDomain_strong2_exists_late_thetaDissipation_lt

end

end ShenWork.Paper3
