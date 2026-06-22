import ShenWork.Paper3.IntervalDomainPersistenceActualLinearFaithfulUV

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

/-- Strict-subthreshold liminf transfer for the interval `v` component.

If `δ < liminf inf_x u`, then the existing elliptic/parabolic comparison gives
`liminf inf_x v ≥ (ν/μ) δ^γ`.  The exact-threshold statement requires a
separate limiting step as `δ ↑ θ`. -/
theorem intervalDomain_liminf_v_ge_of_strict_u_liminf_lower
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ} {θ δ : ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hδ : 0 < δ)
    (hu_bdd : IsBoundedUnder GE.ge atTop
      (fun t => intervalDomain.infValue (u t)))
    (hv_cobdd : IsCoboundedUnder GE.ge atTop
      (fun t => intervalDomain.infValue (v t)))
    (hθ : θ ≤ liminfInfValue intervalDomain u)
    (hδθ : δ < θ) :
    p.ν / p.μ * δ ^ p.γ ≤ liminfInfValue intervalDomain v := by
  have hδ_liminf : δ < liminfInfValue intervalDomain u :=
    lt_of_lt_of_le hδθ hθ
  have hu_inf :
      ∀ᶠ t in atTop, δ < intervalDomain.infValue (u t) :=
    eventually_lt_of_lt_liminf hδ_liminf hu_bdd
  have hu_point :
      ∀ᶠ t in atTop, ∀ x : intervalDomain.Point, δ ≤ u t x := by
    exact intervalDomain_eventually_pointwise_lower_of_eventuallyLowerBound
      ⟨hδ, hu_inf.mono (fun _ ht => le_of_lt ht)⟩
  simpa [liminfInfValue] using
    intervalDomain_liminf_v_ge_of_eventually_u_lower
      hsol hδ hv_cobdd hu_point

/-- Exact-threshold liminf transfer for the interval `v` component. -/
theorem intervalDomain_liminf_v_ge_of_u_liminf_lower
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ} {θ : ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hθpos : 0 < θ)
    (hu_bdd : IsBoundedUnder GE.ge atTop
      (fun t => intervalDomain.infValue (u t)))
    (hv_cobdd : IsCoboundedUnder GE.ge atTop
      (fun t => intervalDomain.infValue (v t)))
    (hθ : θ ≤ liminfInfValue intervalDomain u) :
    p.ν / p.μ * θ ^ p.γ ≤ liminfInfValue intervalDomain v := by
  let φ : ℝ → ℝ := fun y => p.ν / p.μ * y ^ p.γ
  have hcont : ContinuousAt φ θ := by
    dsimp [φ]
    exact (continuousAt_id.rpow_const (Or.inl (ne_of_gt hθpos))).const_mul _
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have hnear_event :
      ∀ᶠ y in 𝓝 θ, |φ y - φ θ| < ε :=
    hcont.eventually (Metric.ball_mem_nhds (φ θ) hε)
  rw [Metric.eventually_nhds_iff] at hnear_event
  rcases hnear_event with ⟨η, hηpos, hη⟩
  set d : ℝ := min (θ / 2) (η / 2) with hd_def
  have hdpos : 0 < d := by
    simp [hd_def, hθpos, hηpos]
  set δ : ℝ := θ - d with hδ_def
  have hδpos : 0 < δ := by
    have hd_le : d ≤ θ / 2 := by simp [hd_def]
    linarith
  have hδθ : δ < θ := by
    simp [hδ_def, hdpos]
  have hdist : dist δ θ < η := by
    rw [Real.dist_eq]
    have hd_le : d ≤ η / 2 := by simp [hd_def]
    have habs : |δ - θ| = d := by
      rw [hδ_def]
      simp [abs_of_nonneg hdpos.le]
    rw [habs]
    linarith
  have hclose : |φ δ - φ θ| < ε := hη (y := δ) hdist
  have hstrict :=
    intervalDomain_liminf_v_ge_of_strict_u_liminf_lower
      (p := p) (u := u) (v := v) (θ := θ) (δ := δ)
      hsol hδpos hu_bdd hv_cobdd hθ hδθ
  have hφ_le : φ θ ≤ φ δ + ε := by
    have := (abs_lt.mp hclose).1
    linarith
  dsimp [φ] at hstrict hφ_le ⊢
  linarith

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomain_liminf_v_ge_of_strict_u_liminf_lower
#print axioms ShenWork.Paper3.intervalDomain_liminf_v_ge_of_u_liminf_lower
