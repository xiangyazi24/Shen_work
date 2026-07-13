import ShenWork.Paper3.IntervalDomainEntropyStrong1Rate

/-!
# Dynamic entropy consequences in the first strong-logistic branch

The exact classical entropy identity and the positive coefficient are combined
here for an arbitrary positive bounded global orbit.  A short real-analysis
lemma then shows that a nonnegative free energy whose derivative controls a
nonnegative dissipation has arbitrarily late slices with small dissipation.
This conclusion uses no stability or orbit-bound input.
-/

namespace ShenWork.Paper3

open Filter Topology Set
open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

/-- A nonnegative differentiable energy satisfying `E' ≤ -c D`, with `c > 0`,
has a dissipation-small slice after every positive starting time. -/
theorem exists_late_dissipation_lt_of_nonnegative_energy
    {E D slope : ℝ → ℝ} {c T q : ℝ}
    (hc : 0 < c) (hT : 0 < T) (hq : 0 < q)
    (hE : ∀ t, 0 < t → 0 ≤ E t)
    (hderiv : ∀ t, 0 < t → HasDerivAt E (slope t) t)
    (hdiss : ∀ t, 0 < t → slope t ≤ -c * D t) :
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
  have hFderiv : ∀ t, 0 < t →
      HasDerivAt F (slope t + c * q) t := by
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
    have hD : q ≤ D t := hsmall t (le_of_lt ht.1)
    have hcD : c * q ≤ c * D t := mul_le_mul_of_nonneg_left hD hc.le
    linarith [hdiss t ht0]
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
  have : E b < 0 := lt_of_le_of_lt hEb (neg_neg_of_pos hcq)
  exact (not_lt_of_ge (hE b hb)) this

/-- The entropy functional of every positive bounded global orbit has the
proved classical derivative at every positive time. -/
theorem intervalDomain_strong1Entropy_hasDerivAt
    (p : CM2Params) {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    ∀ t, 0 < t →
      HasDerivAt
        (fun s => chemotaxisEntropyFunctional intervalDomain 1 uStar u s)
        (intervalDomain.integral (fun x =>
          (1 - uStar / u t x) * intervalDomain.timeDeriv u t x)) t := by
  intro t ht
  have hT : 0 < t + 1 := by linarith
  exact intervalDomain_entropy_hasDerivAt
    (huv.classical (t + 1) hT) heq.u_pos ⟨ht, by linarith⟩

/-- The exact first-branch entropy derivative controls theta dissipation with
the concrete positive coefficient. -/
theorem intervalDomain_strong1Entropy_dissipative
    (p : CM2Params) (hm : p.m = 1)
    {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hrel : 2 * p.γ ≤ p.α + 1)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    ∀ t, 0 < t →
      intervalDomain.integral (fun x =>
          (1 - uStar / u t x) * intervalDomain.timeDeriv u t x) ≤
        -strong1EntropyCoefficient p uStar vStar *
          chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
  intro t ht
  have hT : 0 < t + 1 := by linarith
  simpa [strong1EntropyCoefficient] using
    (intervalDomain_entropySlope_le_strong1Coefficient
      hm (huv.classical (t + 1) hT) ht (by linarith) heq hrel)

/-- In the first strict formula branch, theta dissipation is arbitrarily small
at late times along every positive bounded global orbit. -/
theorem intervalDomain_strong1_exists_late_thetaDissipation_lt
    (p : CM2Params) (hm : p.m = 1)
    {uStar vStar : ℝ}
    (hb : 0 < p.b)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hrel : 2 * p.γ ≤ p.α + 1)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong1Formula p uStar vStar)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    {T q : ℝ} (hT : 0 < T) (hq : 0 < q) :
    ∃ t, T ≤ t ∧
      chemotaxisThetaDissipation intervalDomain uStar p.α (u t) < q := by
  let c := strong1EntropyCoefficient p uStar vStar
  have hc : 0 < c := strong1EntropyCoefficient_pos_of_chi_lt
    p hm hb heq.u_pos heq.v_nonneg hχpos hχ
  exact exists_late_dissipation_lt_of_nonnegative_energy
    (E := fun t => chemotaxisEntropyFunctional intervalDomain 1 uStar u t)
    (D := fun t => chemotaxisThetaDissipation intervalDomain uStar p.α (u t))
    (slope := fun t => intervalDomain.integral (fun x =>
      (1 - uStar / u t x) * intervalDomain.timeDeriv u t x))
    hc hT hq
    (fun t ht =>
      intervalDomain_chemotaxisEntropyFunctional_nonneg_of_positiveGlobalBoundedSolution
        (by norm_num) heq.u_pos huv ht)
    (intervalDomain_strong1Entropy_hasDerivAt p heq huv)
    (intervalDomain_strong1Entropy_dissipative p hm heq hrel huv)

#print axioms exists_late_dissipation_lt_of_nonnegative_energy
#print axioms intervalDomain_strong1Entropy_hasDerivAt
#print axioms intervalDomain_strong1Entropy_dissipative
#print axioms intervalDomain_strong1_exists_late_thetaDissipation_lt

end

end ShenWork.Paper3
