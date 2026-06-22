import ShenWork.Paper3.ScalarLogisticDiniLiminf

open Filter Topology
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- Exact scalar logistic liminf threshold, obtained as the limit of strict
logistic subsolution thresholds. -/
theorem logistic_liminf_ge_of_RightLowerDiniGE
    {q : CM2Params} {z : ℝ → ℝ} {T0 : ℝ}
    (hqa : 0 < q.a) (hqb : 0 < q.b)
    (hcont : ∀ T, T0 ≤ T → ContinuousOn z (Set.Icc T0 T))
    (hD : RightLowerDiniGE z
      (fun y => q.a * y - q.b * y ^ (1 + q.α)) (Set.Ioi 0))
    (hT0 : 0 < T0) (hz0 : 0 < z T0)
    (hcobdd : IsCoboundedUnder GE.ge atTop z) :
    (q.a / q.b) ^ (1 / q.α) ≤ Filter.liminf z atTop := by
  let φ : ℝ → ℝ := fun a => (a / q.b) ^ (1 / q.α)
  have hbase : 0 < q.a / q.b := div_pos hqa hqb
  have hφcont : ContinuousAt φ q.a := by
    dsimp [φ]
    exact (continuousAt_id.div_const q.b).rpow_const (Or.inl (ne_of_gt hbase))
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have hnear_event :
      ∀ᶠ y in 𝓝 q.a, |φ y - φ q.a| < ε :=
    hφcont.eventually (Metric.ball_mem_nhds (φ q.a) hε)
  rw [Metric.eventually_nhds_iff] at hnear_event
  rcases hnear_event with ⟨η0, hη0pos, hη0⟩
  set η : ℝ := min (q.a / 2) (η0 / 2) with hη_def
  have hηpos : 0 < η := by
    simp [hη_def, hqa, hη0pos]
  have hηlt : η < q.a := by
    have hle : η ≤ q.a / 2 := by simp [hη_def]
    linarith
  have hqaηpos : 0 < q.a - η := sub_pos.mpr hηlt
  let qη : CM2Params :=
    { N := q.N
      hN := q.hN
      α := q.α
      γ := q.γ
      m := q.m
      μ := q.μ
      ν := q.ν
      χ₀ := q.χ₀
      a := q.a - η
      b := q.b
      β := q.β
      hα := q.hα
      hγ := q.hγ
      hm := q.hm
      hμ := q.hμ
      hν := q.hν
      ha := hqaηpos.le
      hb := q.hb
      hβ := q.hβ }
  have hdist : dist (q.a - η) q.a < η0 := by
    rw [Real.dist_eq]
    have hle : η ≤ η0 / 2 := by simp [hη_def]
    have habs : |q.a - η - q.a| = η := by
      simp [abs_of_nonneg hηpos.le]
    rw [habs]
    linarith
  have hclose : |φ (q.a - η) - φ q.a| < ε := hη0 hdist
  have hφ_le : φ q.a ≤ φ (q.a - η) + ε := by
    have := (abs_lt.mp hclose).1
    linarith
  have hstrict :
      φ (q.a - η) ≤ Filter.liminf z atTop := by
    have h := strict_logistic_liminf_ge_of_RightLowerDiniGE
      (q := q) (qη := qη) (η := η) (T0 := T0)
      hqaηpos hqb hηpos rfl rfl rfl hcont hD hT0 hz0 hcobdd
    simpa [φ, qη] using h
  have hsum : φ (q.a - η) + ε ≤ Filter.liminf z atTop + ε := by
    simpa [add_comm] using add_le_add_right hstrict ε
  exact le_trans hφ_le hsum

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.logistic_liminf_ge_of_RightLowerDiniGE
