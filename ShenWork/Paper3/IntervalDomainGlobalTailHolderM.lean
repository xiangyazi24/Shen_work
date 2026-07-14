import ShenWork.Paper2.IntervalDomainMClassicalInitialOverlap
import ShenWork.Paper2.IntervalDomainMConjugateMildHolderBootstrap
import ShenWork.Paper3.IntervalDomainTailHolderCompactness

/-!
# General-power mild restarts on uniformly bounded orbit tails

For each fixed restart window, strict positivity and compactness supply a
positive floor.  The floor may depend on the window; the spatial Holder
constant used below does not.  This is the faithful general-`m` replacement
for the linear-flux tail Lipschitz package.
-/

namespace ShenWork.Paper3

open Filter Set Topology MeasureTheory
open ShenWork.IntervalDomain ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit

noncomputable section

private theorem intervalDomainM_abs_le_supNorm
    {f : intervalDomainPoint → ℝ}
    (hbdd : BddAbove (Set.range (fun x : intervalDomainPoint ↦ |f x|)))
    (x : intervalDomainPoint) :
    |f x| ≤ intervalDomainM.supNorm f := by
  change |f x| ≤ intervalDomainSupNorm f
  unfold intervalDomainSupNorm
  exact le_csSup hbdd ⟨x, rfl⟩

/-- A physical restart of a faithful general-`m` classical solution admits a
positive-strip conjugate mild solution.  Its ceiling is any supplied uniform
tail ceiling; only its floor is selected from the individual compact window. -/
theorem intervalDomainM_tailRestartMildData_exists
    (p : CM2Params)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    {a h M : ℝ} (ha : 0 < a) (hh : 0 < h) (hM : 0 < M)
    (hub : ∀ t, a ≤ t → intervalDomainM.supNorm (u t) ≤ M) :
    ∃ D : ConjugateMildSolutionDataM p (u a),
      D.T = h ∧ D.M = M ∧ D.u = classicalRestartTrajectoryM a h u := by
  let H : ℝ := a + h + 1
  have hH : 0 < H := by dsimp [H]; linarith
  have hahH : a + h < H := by dsimp [H]; linarith
  have hsol : IsPaper2ClassicalSolution intervalDomainM p H u v :=
    hglobal H hH
  obtain ⟨c, _B, hc, _hcB, htwo⟩ :=
    intervalDomainM_u_two_sided_on_compact hsol ha
      (by linarith : a ≤ a + h) hahH
  have hcM : c ≤ M := by
    let x0 : intervalDomainPoint := ⟨0, by constructor <;> norm_num⟩
    have hca : c ≤ u a x0 := (htwo a (by constructor <;> linarith) x0).1
    have hbdd := solution_slice_abs_bddAbove hsol
      (t := a) (by constructor <;> linarith : a ∈ Ioo (0 : ℝ) H)
    have hpoint := intervalDomainM_abs_le_supNorm hbdd x0
    exact hca.trans ((le_abs_self _).trans (hpoint.trans (hub a le_rfl)))
  let w := classicalRestartTrajectoryM a h u
  refine ⟨
    { T := h
      hT := hh
      M := M
      hM := hM
      c := c
      hc := hc
      u := w
      hmild := ?_
      hbound := ?_
      hfloor := ?_
      hcont := ?_
      hmeas := ?_
      datum_bound := ?_ }, rfl, rfl, rfl⟩
  · intro r hr0 hrh x
    have hpoint := intervalDomainM_classical_bform_restart_pointwise
      hsol ha hh.le hahH hr0 hrh x
    have hrmem : r ∈ Icc (0 : ℝ) h := ⟨hr0.le, hrh⟩
    have hw : w r x = u (a + r) x := by
      simpa [w] using congrFun (classicalRestartTrajectoryM_eq hrmem) x
    rw [hw]
    exact hpoint
  · intro r hr0 hrh x
    have hrmem : r ∈ Icc (0 : ℝ) h := ⟨hr0.le, hrh⟩
    have ht : a + r ∈ Ioo (0 : ℝ) H := by
      constructor
      · linarith
      · exact lt_of_le_of_lt (by linarith) hahH
    have hbdd := solution_slice_abs_bddAbove hsol ht
    have hpoint := intervalDomainM_abs_le_supNorm hbdd x
    have hw : w r x = u (a + r) x := by
      simpa [w] using congrFun (classicalRestartTrajectoryM_eq hrmem) x
    rw [hw]
    exact hpoint.trans (hub (a + r) (by linarith))
  · intro r hr0 hrh x
    have hrmem : r ∈ Icc (0 : ℝ) h := ⟨hr0.le, hrh⟩
    have hw : w r x = u (a + r) x := by
      simpa [w] using congrFun (classicalRestartTrajectoryM_eq hrmem) x
    rw [hw]
    exact (htwo (a + r) (by constructor <;> linarith) x).1
  · simpa [w] using classicalRestartTrajectoryM_hasContinuousSlices
      hsol ha hh.le hahH
  · simpa [w] using classicalRestartTrajectoryM_hasJointMeasurability
      hsol ha hh.le hahH
  · intro x
    have hbdd := solution_slice_abs_bddAbove hsol
      (t := a) (by constructor <;> linarith : a ∈ Ioo (0 : ℝ) H)
    exact (intervalDomainM_abs_le_supNorm hbdd x).trans (hub a le_rfl)

/-- Every bounded faithful general-`m` global orbit has one common spatial
Holder modulus on its positive-time tail.  The exponent is fixed at `1/2`;
the constant is independent of the window-specific positive floor. -/
theorem intervalDomainM_globalBounded_eventual_holder
    (p : CM2Params)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    ∃ T M G : ℝ, 0 < T ∧ 0 < M ∧ 0 ≤ G ∧
      (∀ t, T ≤ t → intervalDomainM.supNorm (u t) ≤ M) ∧
      ∀ t, T ≤ t → ∀ x y : intervalDomainPoint,
        |u t x - u t y| ≤ G * |x.1 - y.1| ^ ((1 : ℝ) / 2) := by
  rcases huv.bounded with ⟨M₀, hM₀⟩
  rcases eventually_atTop.1 hM₀ with ⟨T₀, hT₀⟩
  let M : ℝ := max M₀ 1
  let T : ℝ := max (T₀ + 1) 2
  let G : ℝ := conjugateMildMHolderConstant p M 1 ((1 : ℝ) / 2) 1
  have hM : 0 < M :=
    lt_of_lt_of_le zero_lt_one (le_max_right M₀ 1)
  have hT : 0 < T :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right (T₀ + 1) 2)
  have htail : ∀ t, T ≤ t → 0 ≤ G ∧ ∀ x y : intervalDomainPoint,
      |u t x - u t y| ≤ G * |x.1 - y.1| ^ ((1 : ℝ) / 2) := by
    intro t ht
    let a : ℝ := t - 1
    have ha : 0 < a := by
      dsimp [a, T] at *
      linarith [le_max_right (T₀ + 1) (2 : ℝ)]
    have hT₀a : T₀ ≤ a := by
      dsimp [a, T] at *
      linarith [le_max_left (T₀ + 1) (2 : ℝ)]
    have hub : ∀ s, a ≤ s → intervalDomainM.supNorm (u s) ≤ M := by
      intro s has
      exact (hT₀ s (le_trans hT₀a has)).trans (le_max_left M₀ 1)
    obtain ⟨D, hDT, hDM, hDu⟩ :=
      intervalDomainM_tailRestartMildData_exists p huv.classical ha
        (show (0 : ℝ) < 1 by norm_num) hM hub
    have huaBound : ∀ z, |intervalDomainLift (u a) z| ≤ D.M := by
      intro z
      by_cases hz : z ∈ Icc (0 : ℝ) 1
      · simpa [intervalDomainLift, hz, hDM]
          using D.datum_bound ⟨z, hz⟩
      · simp [intervalDomainLift, hz, hDM, hM.le]
    have huaMeas : AEStronglyMeasurable
        (intervalDomainLift (u a)) (intervalMeasure 1) := by
      have hH : 0 < a + 2 := by linarith
      have hsol := huv.classical (a + 2) hH
      exact
        (ShenWork.IntervalMildPicardThreshold.intervalDomainLift_measurable_of_continuous'
          (solutionSlice_continuous hsol ⟨ha, by linarith⟩)).aestronglyMeasurable
    have hlocal := conjugateMildM_positiveTime_holder_bound
      D huaBound huaMeas
        (θ := (1 : ℝ) / 2) (τ := 1) (by norm_num) (by norm_num) (by norm_num)
    rw [hDT, hDM] at hlocal
    refine ⟨by simpa [G] using hlocal.1, ?_⟩
    intro x y
    have hslice : D.u 1 = u t := by
      rw [hDu, classicalRestartTrajectoryM_eq
        (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)]
      dsimp [a]
      congr 1
      ring
    have hxy := hlocal.2 1 ⟨le_rfl, le_rfl⟩ x y
    simpa [G, hslice] using hxy
  have hG : 0 ≤ G := (htail T le_rfl).1
  have hsup : ∀ t, T ≤ t → intervalDomainM.supNorm (u t) ≤ M := by
    intro t ht
    have hT₀t : T₀ ≤ t := by
      dsimp [T] at ht
      linarith [le_max_left (T₀ + 1) (2 : ℝ)]
    exact (hT₀ t hT₀t).trans (le_max_left M₀ 1)
  have hholder : ∀ t, T ≤ t → ∀ x y : intervalDomainPoint,
      |u t x - u t y| ≤ G * |x.1 - y.1| ^ ((1 : ℝ) / 2) :=
    fun t ht ↦ (htail t ht).2
  exact ⟨T, M, G, hT, hM, hG, hsup, hholder⟩

/-- Along every sequence of times tending to infinity, a bounded faithful
general-`m` global orbit has a uniformly convergent subsequence of spatial
slices.  This is the concrete spatial Arzela--Ascoli layer used by the
time-translate argument. -/
theorem intervalDomainM_globalBounded_tailSlices_subseq
    (p : CM2Params)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (times : ℕ → ℝ) (htimes : Tendsto times atTop atTop) :
    ∃ g : C(intervalDomainPoint, ℝ), ∃ phi : ℕ → ℕ, StrictMono phi ∧
      TendstoUniformly (fun n x ↦ u (times (phi n)) x) g atTop := by
  obtain ⟨T, M, G, hT, hM, hG, hsup, hholder⟩ :=
    intervalDomainM_globalBounded_eventual_holder p huv
  have hevent : ∀ᶠ n : ℕ in atTop, T ≤ times n :=
    htimes (eventually_ge_atTop T)
  rcases eventually_atTop.1 hevent with ⟨N, hN⟩
  have htail (n : ℕ) : T ≤ times (N + n) :=
    hN (N + n) (by omega)
  have htime_pos (n : ℕ) : 0 < times (N + n) :=
    lt_of_lt_of_le hT (htail n)
  let f : ℕ → C(intervalDomainPoint, ℝ) := fun n ↦
    ⟨u (times (N + n)), by
      have hs := htime_pos n
      have hsol := huv.classical (times (N + n) + 1) (by linarith)
      exact solutionSlice_continuous hsol ⟨hs, by linarith⟩⟩
  have hf_abs : ∀ n x, |f n x| ≤ M := by
    intro n x
    have hs := htime_pos n
    have hsol := huv.classical (times (N + n) + 1) (by linarith)
    have hbdd := solution_slice_abs_bddAbove hsol
      (show times (N + n) ∈ Ioo (0 : ℝ) (times (N + n) + 1) by
        constructor <;> linarith)
    have hpoint := intervalDomainM_abs_le_supNorm hbdd x
    exact hpoint.trans (hsup (times (N + n)) (htail n))
  have hf_holder : ∀ n x y,
      |f n x - f n y| ≤ G * |x.1 - y.1| ^ ((1 : ℝ) / 2) := by
    intro n x y
    exact hholder (times (N + n)) (htail n) x y
  obtain ⟨g, psi, hpsi, hfg⟩ :=
    intervalDomain_exists_uniform_convergent_subseq_of_holder f
      hM.le hG (by norm_num : (0 : ℝ) < 1 / 2) hf_abs hf_holder
  let phi : ℕ → ℕ := fun n ↦ N + psi n
  have hphi : StrictMono phi := by
    intro i j hij
    exact Nat.add_lt_add_left (hpsi hij) N
  refine ⟨g, phi, hphi, ?_⟩
  simpa [f, phi] using hfg

#print axioms intervalDomainM_tailRestartMildData_exists
#print axioms intervalDomainM_globalBounded_eventual_holder
#print axioms intervalDomainM_globalBounded_tailSlices_subseq

end

end ShenWork.Paper3
