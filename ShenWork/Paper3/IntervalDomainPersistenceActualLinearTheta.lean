import ShenWork.Paper3.IntervalDomainPersistenceActualLinearMinPoint

open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

theorem theta_linear_bound_public {p : CM2Params} {V : ℝ}
    (hβ : 1 ≤ p.β) (hV : 0 ≤ V) :
    V / (1 + V) ^ p.β ≤ Theta_beta (p.β - 1) := by
  have hb_nonneg : 0 ≤ p.β - 1 := by linarith
  rcases lt_or_eq_of_le hb_nonneg with hbpos | hbzero
  · by_cases hV0 : V = 0
    · subst hV0
      simp [Theta_beta_nonneg hb_nonneg]
    · have hVpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hV0)
      have h := Lemma_2_5_normalized_Theta_bound
        (beta := p.β - 1) hbpos (v := V) hVpos
      simpa [show 1 + (p.β - 1) = p.β by ring] using h
  · have hpβ : p.β = 1 := by linarith
    rw [hpβ, show (1 : ℝ) - 1 = 0 by ring, Theta_beta_zero]
    have hpos : 0 < 1 + V := by linarith
    rw [Real.rpow_one, div_le_iff₀ hpos]
    linarith

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.theta_linear_bound_public
