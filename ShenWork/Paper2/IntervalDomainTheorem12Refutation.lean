import ShenWork.Paper2.IntervalDomainMass

/-!
# The mixed undamped branch refutes Paper 2 Theorem 1.2

The formal statement of `Theorem_1_2` permits `a > 0` together with `b = 0`.
On the unit interval this is incompatible with the theorem's eventual uniform
boundedness conclusion: integrating the PDE gives `M' = a M`, while positivity
gives a strictly positive mass.  The proof below uses only the concrete
interval-domain mass identity, so it applies to every classical solution
returned by the claimed theorem and does not require a uniqueness theorem.
-/

open Filter Set
open ShenWork.IntervalDomain

namespace ShenWork.Paper2

noncomputable section

/-- Concrete parameters in the mixed undamped branch `a = 1`, `b = 0`.
They also satisfy the critical hypotheses `m = 1`, `β = 1`, and
`χ₀ = 0 < chiBeta`. -/
def theorem12IntervalRefutationParams : CM2Params where
  N := 1
  hN := by norm_num
  α := 1
  hα := by norm_num
  γ := 1
  hγ := by norm_num
  m := 1
  hm := by norm_num
  μ := 1
  hμ := by norm_num
  ν := 1
  hν := by norm_num
  χ₀ := 0
  a := 1
  ha := by norm_num
  b := 0
  hb := by norm_num
  β := 1
  hβ := by norm_num

/-- The published parameter quantification in Paper 2 Theorem 1.2 is false on
the actual unit interval: the allowed branch `a > 0`, `b = 0`, `χ₀ = 0`
forces positive mass to grow without bound. -/
theorem not_Theorem_1_2_intervalDomain_when_a_pos_b_zero :
    ¬ Theorem_1_2 intervalDomain theorem12IntervalRefutationParams := by
  intro h12
  have hbranches := h12
    (by norm_num [theorem12IntervalRefutationParams])
    (by norm_num [theorem12IntervalRefutationParams])
    (by norm_num [theorem12IntervalRefutationParams])
  have hchi :
      theorem12IntervalRefutationParams.χ₀ <
        chiBeta theorem12IntervalRefutationParams := by
    norm_num [theorem12IntervalRefutationParams, chiBeta]
  let u₀ : intervalDomain.Point → ℝ := fun _ => 1
  have hu₀ : PaperPositiveInitialDatum intervalDomain u₀ := by
    refine ⟨⟨?_, continuous_const⟩, 1, by norm_num, ?_⟩
    · refine ⟨1, ?_⟩
      rintro _ ⟨x, rfl⟩
      simp [u₀]
    · intro x
      simp [u₀]
  obtain ⟨u, v, hglobal, _htrace, hbounded⟩ :=
    hbranches.2
      (by norm_num [theorem12IntervalRefutationParams]) hchi u₀ hu₀
  let M : ℝ → ℝ := fun t => intervalDomain.integral (u t)
  have hM_deriv : ∀ t : ℝ, 0 < t → HasDerivAt M (M t) t := by
    intro t ht
    have hT : 0 < t + 1 := by linarith
    have hsol := hglobal.classical (T := t + 1) hT
    have hderiv :=
      (intervalDomain_Paper2MassDerivativeIdentity
        theorem12IntervalRefutationParams)
        (t + 1) hT u v hsol t ht (by linarith)
    simpa [M, theorem12IntervalRefutationParams] using hderiv
  have hM_pos : ∀ t : ℝ, 0 < t → 0 < M t := by
    intro t ht
    have hT : 0 < t + 1 := by linarith
    exact intervalDomain_classicalSolution_mass_pos
      (hglobal.classical (T := t + 1) hT) ⟨ht, by linarith⟩
  have hM_diff : DifferentiableOn ℝ M (Set.Ioi 0) := by
    intro t ht
    exact (hM_deriv t ht).differentiableAt.differentiableWithinAt
  have hM_mono : MonotoneOn M (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro t ht
      exact (hM_deriv t (lt_of_lt_of_le one_pos ht)).continuousAt.continuousWithinAt
    · exact hM_diff.mono (by
        intro t ht
        rw [interior_Ici] at ht
        exact Set.mem_Ioi.mpr (lt_trans one_pos ht))
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hM_deriv t (lt_trans one_pos ht)).deriv]
      exact (hM_pos t (lt_trans one_pos ht)).le
  have hM1_pos : 0 < M 1 := hM_pos 1 one_pos
  have hderiv_lb :
      ∀ x : ℝ, x ∈ interior (Set.Ici (1 : ℝ)) → M 1 ≤ deriv M x := by
    intro x hx
    rw [interior_Ici] at hx
    rw [(hM_deriv x (lt_trans one_pos hx)).deriv]
    exact hM_mono (Set.mem_Ici.mpr le_rfl)
      (Set.mem_Ici.mpr hx.le) hx.le
  have hgrowth : ∀ t : ℝ, 1 ≤ t → M 1 * (t - 1) ≤ M t - M 1 := by
    intro t ht
    exact (convex_Ici 1).mul_sub_le_image_sub_of_le_deriv
      (fun x hx =>
        (hM_deriv x (lt_of_lt_of_le one_pos hx)).continuousAt.continuousWithinAt)
      (hM_diff.mono (by
        intro x hx
        rw [interior_Ici] at hx
        exact Set.mem_Ioi.mpr (lt_trans one_pos hx)))
      hderiv_lb 1 (Set.mem_Ici.mpr le_rfl) t (Set.mem_Ici.mpr ht) ht
  obtain ⟨B, hB⟩ := hbounded
  rw [Filter.eventually_atTop] at hB
  obtain ⟨T₀, hT₀⟩ := hB
  let tbase : ℝ := max T₀ 1
  have htbase_pos : 0 < tbase := lt_of_lt_of_le one_pos (le_max_right _ _)
  have htbase_ge : T₀ ≤ tbase := le_max_left _ _
  have hB_nonneg : 0 ≤ B := by
    have hT : 0 < tbase + 1 := by linarith
    have hmass_le := intervalDomain_classicalSolution_mass_le_supNorm
      (hglobal.classical (T := tbase + 1) hT)
      ⟨htbase_pos, by linarith⟩
    exact (hM_pos tbase htbase_pos).le.trans
      (hmass_le.trans (hT₀ tbase htbase_ge))
  let tstar : ℝ := tbase + B / M 1 + 1
  have hdiv_nonneg : 0 ≤ B / M 1 := div_nonneg hB_nonneg hM1_pos.le
  have htstar_ge_T₀ : T₀ ≤ tstar := by
    dsimp [tstar]
    linarith [htbase_ge]
  have htstar_ge_one : 1 ≤ tstar := by
    dsimp [tstar, tbase]
    linarith [le_max_right T₀ (1 : ℝ)]
  have htstar_pos : 0 < tstar := lt_of_lt_of_le one_pos htstar_ge_one
  have hmass_le_B : M tstar ≤ B := by
    have hT : 0 < tstar + 1 := by linarith
    exact (intervalDomain_classicalSolution_mass_le_supNorm
      (hglobal.classical (T := tstar + 1) hT)
      ⟨htstar_pos, by linarith⟩).trans
      (hT₀ tstar htstar_ge_T₀)
  have hgrowth_star := hgrowth tstar htstar_ge_one
  have hrecover : M 1 * (B / M 1) = B :=
    mul_div_cancel₀ B (ne_of_gt hM1_pos)
  have htbase_nonneg : 0 ≤ tbase :=
    le_trans (by norm_num) (le_max_right T₀ (1 : ℝ))
  have hexpand : M 1 * (tstar - 1) = M 1 * tbase + B := by
    dsimp [tstar]
    rw [show tbase + B / M 1 + 1 - 1 = tbase + B / M 1 by ring,
      mul_add, hrecover]
  rw [hexpand] at hgrowth_star
  nlinarith [mul_nonneg hM1_pos.le htbase_nonneg]

end

#print axioms not_Theorem_1_2_intervalDomain_when_a_pos_b_zero

end ShenWork.Paper2
