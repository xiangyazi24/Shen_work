import ShenWork.Paper1.WholeLineChiPosSqueezeAlgebra

open Filter Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Finite entry for the affine rectangle recurrence
-/

/-- A sequence satisfying the squeeze recurrence enters every neighborhood
strictly larger than its stationary affine error. -/
theorem exists_index_affine_recurrence_lt
    {g : ℕ → ℝ} {r c epsilon : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hc : 0 ≤ c)
    (hstep : ∀ k, g (k + 1) ≤ r * g k + c)
    (hepsilon : c / (1 - r) < epsilon) :
    ∃ n, g n < epsilon := by
  have hpow : Tendsto (fun n : ℕ => r ^ n * g 0) atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const (g 0)
  have hroom : 0 < epsilon - c / (1 - r) := by linarith
  have hnear : Set.Iio (epsilon - c / (1 - r)) ∈ nhds (0 : ℝ) :=
    Iio_mem_nhds hroom
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hpow.eventually hnear)
  refine ⟨N, ?_⟩
  have hbound := affine_recurrence_iterate_le hr0 hr1 hc hstep N
  linarith [hN N le_rfl]

section AxiomAudit

#print axioms exists_index_affine_recurrence_lt

end AxiomAudit

end ShenWork.Paper1
