import ShenWork.Paper1.WholeLineChiPosDispersion

/-!
# The sharp Turing threshold for the whole-line dispersion relation

For `χγ > 1`, completing the square after multiplying by `1 + s` shows that
the dispersion relation is maximized at `s = √(χγ) - 1`.  Its maximal value is
`(√(χγ) - 1)² - α`, so the exact strict-stability threshold is
`χγ < (1 + √α)²`.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- Below the Turing threshold, every nonnegative Fourier mode has strictly
negative growth. -/
theorem dispersion_le_of_lt_turing
    (α χγ : ℝ) (hα : 0 < α) (hχγ0 : 0 ≤ χγ)
    (hthreshold : χγ < (1 + Real.sqrt α) ^ 2) :
    ∀ s : ℝ, 0 ≤ s → dispersion α χγ s < 0 := by
  intro s hs
  by_cases hχγ1 : χγ ≤ 1
  · exact dispersion_neg_of_chiGamma_le_one α χγ hα hχγ0 hχγ1 hs
  · have hχγgt : 1 < χγ := lt_of_not_ge hχγ1
    have hsqrtα0 : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
    have hsqrtχγ0 : 0 ≤ Real.sqrt χγ := Real.sqrt_nonneg χγ
    have hsqrtχγ1 : 1 < Real.sqrt χγ := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) hχγgt
    have hsqrt_lt : Real.sqrt χγ < 1 + Real.sqrt α := by
      exact (Real.sqrt_lt' (by linarith)).2 hthreshold
    have hsqα : (Real.sqrt α) ^ 2 = α := Real.sq_sqrt hα.le
    have hsqχγ : (Real.sqrt χγ) ^ 2 = χγ := Real.sq_sqrt hχγ0
    have henvelope : (Real.sqrt χγ - 1) ^ 2 - α < 0 := by
      nlinarith
    have hden : 0 < 1 + s := by linarith
    have hmode : dispersion α χγ s ≤ (Real.sqrt χγ - 1) ^ 2 - α := by
      have hfrac :
          χγ * s / (1 + s) ≤ s + (Real.sqrt χγ - 1) ^ 2 := by
        rw [div_le_iff₀ hden]
        nlinarith [sq_nonneg (1 + s - Real.sqrt χγ)]
      unfold dispersion
      linarith
    exact lt_of_le_of_lt hmode henvelope

/-- For `χγ > 1`, the admissible mode `s = √(χγ) - 1` attains the global
maximum of the dispersion relation. -/
theorem dispersion_attains_at_sqrt
    (α χγ : ℝ) (hχγ : 1 < χγ) :
    dispersion α χγ (Real.sqrt χγ - 1) =
        (Real.sqrt χγ - 1) ^ 2 - α ∧
      ∀ s : ℝ, 0 ≤ s →
        dispersion α χγ s ≤ dispersion α χγ (Real.sqrt χγ - 1) := by
  have hχγ0 : 0 ≤ χγ := le_trans (by norm_num) hχγ.le
  have hsqrtχγ0 : 0 ≤ Real.sqrt χγ := Real.sqrt_nonneg χγ
  have hsqrtχγ1 : 1 < Real.sqrt χγ := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hχγ
  have hsqrtχγne : Real.sqrt χγ ≠ 0 := ne_of_gt (lt_trans (by norm_num) hsqrtχγ1)
  have hsqχγ : (Real.sqrt χγ) ^ 2 = χγ := Real.sq_sqrt hχγ0
  have hattain :
      dispersion α χγ (Real.sqrt χγ - 1) =
        (Real.sqrt χγ - 1) ^ 2 - α := by
    unfold dispersion
    rw [show 1 + (Real.sqrt χγ - 1) = Real.sqrt χγ by ring]
    field_simp
    nlinarith
  refine ⟨hattain, ?_⟩
  intro s hs
  rw [hattain]
  have hden : 0 < 1 + s := by linarith
  have hfrac :
      χγ * s / (1 + s) ≤ s + (Real.sqrt χγ - 1) ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg (1 + s - Real.sqrt χγ)]
  unfold dispersion
  linarith

/-- Above the Turing threshold, the maximizing mode has strictly positive
growth, proving that the threshold is sharp. -/
theorem dispersion_pos_of_gt_turing
    (α χγ : ℝ) (hα : 0 < α) (hχγ0 : 0 ≤ χγ)
    (hthreshold : (1 + Real.sqrt α) ^ 2 < χγ) :
    ∃ s : ℝ, 0 ≤ s ∧ 0 < dispersion α χγ s := by
  have hsqrtα0 : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
  have hsqrtχγ0 : 0 ≤ Real.sqrt χγ := Real.sqrt_nonneg χγ
  have hsqα : (Real.sqrt α) ^ 2 = α := Real.sq_sqrt hα.le
  have hsqχγ : (Real.sqrt χγ) ^ 2 = χγ := Real.sq_sqrt hχγ0
  have hχγ1 : 1 < χγ := by nlinarith [sq_nonneg (Real.sqrt α)]
  have hsqrt_gt : 1 + Real.sqrt α < Real.sqrt χγ := by
    nlinarith [sq_nonneg (Real.sqrt χγ + (1 + Real.sqrt α))]
  have hsstar : 0 ≤ Real.sqrt χγ - 1 := by linarith
  have hpositive : 0 < (Real.sqrt χγ - 1) ^ 2 - α := by
    nlinarith
  refine ⟨Real.sqrt χγ - 1, hsstar, ?_⟩
  rw [(dispersion_attains_at_sqrt α χγ hχγ1).1]
  exact hpositive

section AxiomAudit

#print axioms dispersion_le_of_lt_turing
#print axioms dispersion_attains_at_sqrt
#print axioms dispersion_pos_of_gt_turing

end AxiomAudit

end ShenWork.Paper1
