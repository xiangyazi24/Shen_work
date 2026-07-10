import ShenWork.Paper2.IntervalBFormSquareHeatT0Restart

open Filter Topology Set

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Data for applying the regular drift comparison after restarting time at
`s`.  The solution and coefficients are read through `τ ↦ s + τ`; the square
heat barrier itself starts at the new time `τ = 0`. -/
structure TimeShiftedSquareHeatBarrierData
    (L s A D Mbar : ℝ) (f : ℝ → ℝ) (B C u : ℝ → ℝ → ℝ) : Prop where
  coeff :
    NeumannLinearDriftCoefficientsRegular L
      (restartTimeShift s B) (restartTimeShift s C)
  super :
    IsClassicalNeumannLinearDriftSuperSolution L
      (restartTimeShift s B) (restartTimeShift s C)
      (restartTimeShift s u)
  barrier_reg :
    NeumannLinearDriftSubSolutionRegularity L
      (restartTimeShift s B) (restartTimeShift s C)
      (squareHeatBarrier Mbar f)
  calculus :
    SquareHeatSubsolutionCalculus L Mbar f
      (restartTimeShift s B) (restartTimeShift s C)
  M_bound : A ^ 2 / 2 + D ≤ Mbar
  drift_bound :
    ∀ τ x, 0 < τ → τ < L → x ∈ Set.Ioo (0 : ℝ) 1 →
      |B (s + τ) x| ≤ A
  reaction_neg_bound :
    ∀ τ x, 0 < τ → τ < L → x ∈ Set.Ioo (0 : ℝ) 1 →
      -C (s + τ) x ≤ D

/-- Open-endpoint time-shifted lower barrier.  This is just the proved regular
comparison theorem applied to `uShift(τ,x) = u(s+τ,x)` on `[0,T-s]`. -/
theorem square_heat_hbarrier_timeShifted_open
    {T s A D Mbar : ℝ} {f : ℝ → ℝ} {B C u : ℝ → ℝ → ℝ}
    (_hs_pos : 0 < s) (hsT : s < T)
    (H : TimeShiftedSquareHeatBarrierData (T - s) s A D Mbar f B C u)
    (hseed : SquareHeatSeed (fun x : ℝ => u s x) f) :
    ∀ t x, s < t → t < T → x ∈ Set.Icc (0 : ℝ) 1 →
      squareHeatBarrier Mbar f (t - s) x ≤ u t x := by
  have hL : 0 < T - s := by linarith
  have hB_bound :
      ∀ τ x, 0 < τ → τ < T - s → x ∈ Set.Ioo (0 : ℝ) 1 →
        |restartTimeShift s B τ x| ≤ A := by
    intro τ x hτ0 hτL hx
    simpa [restartTimeShift] using H.drift_bound τ x hτ0 hτL hx
  have hC_bound :
      ∀ τ x, 0 < τ → τ < T - s → x ∈ Set.Ioo (0 : ℝ) 1 →
        -restartTimeShift s C τ x ≤ D := by
    intro τ x hτ0 hτL hx
    simpa [restartTimeShift] using H.reaction_neg_bound τ x hτ0 hτL hx
  have hu_initial :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        restartTimeShift s u 0 x = u s x := by
    intro x _hx
    simp [restartTimeShift]
  intro t x hst htT hx
  have hτ0 : 0 < t - s := by linarith
  have hτL : t - s < T - s := by linarith
  have hle :=
    square_heat_hbarrier_of_neumann_linear_drift_square_heat_subsolution_regular
      (T := T - s) (A := A) (D := D) (M := Mbar)
      (u₀ := fun x : ℝ => u s x) (f := f)
      (B := restartTimeShift s B) (C := restartTimeShift s C)
      (u := restartTimeShift s u)
      hL H.coeff H.super hu_initial neumann_interval_comparison_with_drift
      H.barrier_reg H.calculus H.M_bound hB_bound hC_bound hseed
      (t - s) x hτ0 hτL hx
  have htime : s + (t - s) = t := by ring
  simpa [restartTimeShift, htime] using hle

private theorem timeShifted_endpoint_le
    {L s A D Mbar : ℝ} {f : ℝ → ℝ} {B C u : ℝ → ℝ → ℝ}
    (hL : 0 < L)
    (H : TimeShiftedSquareHeatBarrierData L s A D Mbar f B C u)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hopen :
      ∀ τ, 0 < τ → τ < L →
        squareHeatBarrier Mbar f τ x ≤ restartTimeShift s u τ x) :
    squareHeatBarrier Mbar f L x ≤ restartTimeShift s u L x := by
  let F : ℝ → ℝ :=
    fun τ => squareHeatBarrier Mbar f τ x - restartTimeShift s u τ x
  have hmap :
      Set.MapsTo (fun τ : ℝ => (τ, x))
        (Set.Icc (0 : ℝ) L)
        (Set.Icc (0 : ℝ) L ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro τ hτ
    exact ⟨hτ, hx⟩
  have hbar_cont :
      ContinuousOn (fun τ : ℝ => squareHeatBarrier Mbar f τ x)
        (Set.Icc (0 : ℝ) L) :=
    H.barrier_reg.continuousOn_rect.comp
      (continuous_id.prodMk continuous_const).continuousOn hmap
  have hu_cont :
      ContinuousOn (fun τ : ℝ => restartTimeShift s u τ x)
        (Set.Icc (0 : ℝ) L) :=
    H.super.continuousOn_rect.comp
      (continuous_id.prodMk continuous_const).continuousOn hmap
  have hF_cont : ContinuousOn F (Set.Icc (0 : ℝ) L) := hbar_cont.sub hu_cont
  let S : Set ℝ := Set.Icc (0 : ℝ) L ∩ F ⁻¹' Set.Iic (0 : ℝ)
  have hS_closed : IsClosed S :=
    hF_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hIoo_subset : Set.Ioo (0 : ℝ) L ⊆ S := by
    intro τ hτ
    exact
      ⟨⟨le_of_lt hτ.1, le_of_lt hτ.2⟩,
        sub_nonpos.mpr (hopen τ hτ.1 hτ.2)⟩
  have hclosure_subset : closure (Set.Ioo (0 : ℝ) L) ⊆ S :=
    closure_minimal hIoo_subset hS_closed
  have hL_mem : L ∈ closure (Set.Ioo (0 : ℝ) L) := by
    rw [closure_Ioo (ne_of_lt hL)]
    exact right_mem_Icc.mpr hL.le
  have hFL : F L ≤ 0 := (hclosure_subset hL_mem).2
  exact sub_nonpos.mp hFL

/-- Time-shifted lower barrier on `s < t ≤ T`.  The endpoint `t = T` is obtained
by closing the open comparison through the closed-strip continuity already
contained in the shifted super-solution and barrier regularity packages. -/
theorem square_heat_hbarrier_timeShifted_Ioc
    {T s A D Mbar : ℝ} {f : ℝ → ℝ} {B C u : ℝ → ℝ → ℝ}
    (hs_pos : 0 < s) (hsT : s < T)
    (H : TimeShiftedSquareHeatBarrierData (T - s) s A D Mbar f B C u)
    (hseed : SquareHeatSeed (fun x : ℝ => u s x) f) :
    ∀ t x, s < t → t ≤ T → x ∈ Set.Icc (0 : ℝ) 1 →
      squareHeatBarrier Mbar f (t - s) x ≤ u t x := by
  intro t x hst htT hx
  by_cases htT_strict : t < T
  · exact square_heat_hbarrier_timeShifted_open
      hs_pos hsT H hseed t x hst htT_strict hx
  · have ht_eq : t = T := by linarith
    subst t
    have hL : 0 < T - s := by linarith
    have hendpoint :
        squareHeatBarrier Mbar f (T - s) x ≤
          restartTimeShift s u (T - s) x := by
      refine timeShifted_endpoint_le (L := T - s) hL H hx ?_
      intro τ hτ0 hτL
      have hshift :=
        square_heat_hbarrier_timeShifted_open
          hs_pos hsT H hseed (s + τ) x (by linarith) (by linarith) hx
      have hτ_eq : s + τ - s = τ := by ring
      simpa [restartTimeShift, hτ_eq] using hshift
    have htime : s + (T - s) = T := by ring
    simpa [restartTimeShift, htime] using hendpoint

end ShenWork.Paper2.BFormPositiveDatumNegPart
