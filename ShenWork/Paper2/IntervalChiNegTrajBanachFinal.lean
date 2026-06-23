/-
  ShenWork/Paper2/IntervalChiNegTrajBanachFinal.lean

  χ₀<0 — closing the carried inputs of the trajectory-BCF Banach machine.

  ## BUILD (a) — joint (τ,x)-continuity of the conjugate kernel operator (τ>0)

  The carried input `hG_cont` of `conjugateLeg_continuous`
  (IntervalChiNegTrajBanachClose) is the a.e.-fibre joint continuity of
      `z ↦ z.1.1 · B_N(z.1.1(1−r))(F(z.1.1·r))(z.2.1)`
  over the box `[0,t] × Ω̄`.  This file BUILDS it, axiom-clean, from the Neumann
  heat-gradient eigen-series `B_N(τ)Q x = −∫ DerivSeries(τ,y,x)·Q(y) dy`:

   * `derivSeries_jointCont` — the deriv-series `Σ_k ∂heat(τ)(±x+y+2k)` is JOINTLY
     `(τ,x)`-continuous on `[τ₀,T] × [0,1]` (`τ₀>0`), via `continuousOn_tsum` with
     the τ-uniform exponential majorant `M·exp(−(2k)²/16T)` (`e^{−τλ_k}≤e^{−τ₀λ_k}`
     dominates the polynomial growth — `pref_bound` bounds the τ-prefactor on the
     compact `[τ₀,T]`, `win_bound` the windowed Gaussian).

   * `kernelOp_jointCont` / `kernelOp_src_jointCont` — lift to the kernel operator
     `(τ,x) ↦ B_N(τ)Q x` (fixed `Q`) resp. `(τ,s,x) ↦ B_N(τ)(F s)x` (jointly
     continuous source family `F`) via `continuousOn_of_dominated` with the
     τ-uniform integrable majorant `B·CF` (`derivSeries_abs_le`).

   * `interior_contAt` (τ>0 region, three-param lemma + local box) and
     `boundary_contAt` (τ=0, the `√(z.1.1)` squeeze of
     `intervalConjugateKernelOperator_abs_le`) combine in
     `conjugateLeg_hG_cont` to the FULL `Continuous` over `[0,t] × Ω̄`,
     discharging `hG_cont` for any jointly-continuous bounded source family `F`.
     `conjugateLeg_continuous_full` then consumes the landed engine.

  ## DERIVED vs CARRIED

  DERIVED-NEW here (axiom-clean ⊆ {propext, Classical.choice, Quot.sound}):
  the entire joint `(τ,x)`-continuity tower of the conjugate kernel operator
  (the unbuilt deriv-series joint continuity named in
  IntervalChiNegTrajBanachClose), and the full `hG_cont` discharge for a
  jointly-continuous bounded source family `F` (boundary squeeze + interior
  three-param continuity), feeding `conjugateLeg_continuous`.

  CARRIED (explicit hypothesis, NOT a disguised conclusion): the joint
  continuity / boundedness / integrability of the candidate flux family `F`
  itself (for the χ₀<0 application `F s = chemFluxLifted p (w s)` — the nonlinear
  resolver flux of the box candidate `w`).  This is exactly the "time-continuity
  of the candidate's flux slices" the carried-input note records; it is a
  candidate-specific nonlinear-PDE fact, supplied as the `hF_*` hypotheses.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  Lines ≤ 100.
-/
import ShenWork.Paper2.IntervalConjugateKernelJointMeas
import ShenWork.Paper2.IntervalChiNegTrajBanachClose

open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalDomain (intervalMeasure intervalDomainPoint)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator intervalConjugateKernelOperator_abs_le)
open ShenWork.IntervalConjugateKernelJointMeas
  (intervalConjugateKernelOperator_eq_neg_derivSeries_integral)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)
open MeasureTheory
open scoped Topology

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegTrajBanachFinal

theorem pref_bound {τ₀ T : ℝ} (hτ₀ : 0 < τ₀) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc τ₀ T,
      heatGradPointwiseBound τ * Real.exp (2 ^ 2 / (4 * (2 * τ))) ≤ M := by
  have hcont : ContinuousOn
      (fun τ => heatGradPointwiseBound τ * Real.exp (2 ^ 2 / (4 * (2 * τ))))
      (Set.Icc τ₀ T) := by
    apply ContinuousOn.mul
    · unfold heatGradPointwiseBound
      apply ContinuousOn.mul
      apply ContinuousOn.mul
      · apply ContinuousOn.div continuousOn_const (by fun_prop)
        intro τ hτ; have : 0 < τ := lt_of_lt_of_le hτ₀ hτ.1; positivity
      · apply ContinuousOn.div continuousOn_const
        · apply Continuous.continuousOn; fun_prop
        · intro τ hτ; have h : 0 < τ := lt_of_lt_of_le hτ₀ hτ.1
          exact Real.sqrt_ne_zero'.mpr (by positivity)
      · apply Continuous.continuousOn; fun_prop
    · apply ContinuousOn.rexp
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro τ hτ; have : 0 < τ := lt_of_lt_of_le hτ₀ hτ.1; positivity
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hcont).bddAbove
  exact ⟨max M 0, le_max_right _ _,
    fun τ hτ => le_trans (hM ⟨τ, hτ, rfl⟩) (le_max_left _ _)⟩

theorem term_cont (a c : ℝ) {τ₀ T : ℝ} (hτ₀ : 0 < τ₀) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (fun z => heatKernel p.1 z) (a * p.2 + c))
      (Set.Icc τ₀ T ×ˢ Set.univ) := by
  have heq : (fun p : ℝ × ℝ => deriv (fun z => heatKernel p.1 z) (a * p.2 + c))
      = fun p : ℝ × ℝ => -((a * p.2 + c) / (2 * p.1)) * heatKernel p.1 (a * p.2 + c) := by
    funext p; exact deriv_heatKernel_global p.1 (a * p.2 + c)
  rw [heq]; unfold heatKernel
  apply ContinuousOn.mul
  · apply ContinuousOn.neg
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro p hp; have h : 0 < p.1 := lt_of_lt_of_le hτ₀ hp.1.1; positivity
  · apply ContinuousOn.mul
    · apply ContinuousOn.div continuousOn_const (by apply Continuous.continuousOn; fun_prop)
      intro p hp; have h : 0 < p.1 := lt_of_lt_of_le hτ₀ hp.1.1
      exact Real.sqrt_ne_zero'.mpr (by positivity)
    · apply ContinuousOn.rexp
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro p hp; have h : 0 < p.1 := lt_of_lt_of_le hτ₀ hp.1.1; positivity

theorem win_bound {τ₀ T : ℝ} (hτ₀ : 0 < τ₀) (y : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 1)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hMbd : ∀ τ ∈ Set.Icc τ₀ T,
      heatGradPointwiseBound τ * Real.exp (2 ^ 2 / (4 * (2 * τ))) ≤ M)
    (a : ℝ) (ha : |a| ≤ 1) (k : ℤ) (p : ℝ × ℝ)
    (hp : p ∈ Set.Icc τ₀ T ×ˢ Set.Icc (0:ℝ) 1) :
    ‖deriv (fun z : ℝ => heatKernel p.1 z) (a * p.2 + y + 2 * (k:ℝ))‖
      ≤ M * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (4 * T))) := by
  rw [Real.norm_eq_abs]
  have hτpos : 0 < p.1 := lt_of_lt_of_le hτ₀ hp.1.1
  have hwbd : |deriv (fun z : ℝ => heatKernel p.1 z) (a * p.2 + y + 2 * (k:ℝ))|
      ≤ heatGradWindowBound p.1 0 2 k := by
    apply abs_deriv_heatKernel_le_windowShift hτpos 0 2 k
    have he : a * p.2 + y + 2 * (k:ℝ) - (0 + 2 * (k:ℝ)) = a * p.2 + y := by ring
    rw [he]
    have h1 : |a * p.2| ≤ 1 := by
      rw [abs_mul]
      calc |a| * |p.2| ≤ 1 * |p.2| := by apply mul_le_mul_of_nonneg_right ha (abs_nonneg _)
        _ = |p.2| := one_mul _
        _ ≤ 1 := by rw [abs_of_nonneg hp.2.1]; exact hp.2.2
    have h2 : |y| ≤ 1 := by rw [abs_of_nonneg hy.1]; exact hy.2
    calc |a * p.2 + y| ≤ |a * p.2| + |y| := abs_add_le _ _
      _ ≤ 1 + 1 := by linarith
      _ = 2 := by norm_num
  refine hwbd.trans ?_
  unfold heatGradWindowBound
  have hP : heatGradPointwiseBound p.1 * Real.exp (2 ^ 2 / (4 * (2 * p.1))) ≤ M := hMbd p.1 hp.1
  have hgauss : Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (4 * p.1)))
      ≤ Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (4 * T))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    linarith [hp.1.2]
  calc heatGradPointwiseBound p.1 * Real.exp (2 ^ 2 / (4 * (2 * p.1)))
          * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (4 * p.1)))
        ≤ M * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (4 * p.1))) :=
          mul_le_mul_of_nonneg_right hP (Real.exp_pos _).le
      _ ≤ M * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (4 * T))) :=
          mul_le_mul_of_nonneg_left hgauss hM0

theorem derivSeries_jointCont {τ₀ T : ℝ} (hτ₀ : 0 < τ₀) (hτ₀T : τ₀ ≤ T) (y : ℝ)
    (hy : y ∈ Set.Icc (0:ℝ) 1) :
    ContinuousOn (fun p : ℝ × ℝ => intervalNeumannFullKernelDerivSeries p.1 y p.2)
      (Set.Icc τ₀ T ×ˢ Set.Icc 0 1) := by
  obtain ⟨M, hM0, hMbd⟩ := pref_bound (T := T) hτ₀
  have hsummable : Summable
      (fun k : ℤ => M * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (4 * T)))) :=
    (latticeExpSummable (by linarith : (0:ℝ) < 4 * T) 0).mul_left M
  have hfun : (fun p : ℝ × ℝ => intervalNeumannFullKernelDerivSeries p.1 y p.2)
      = fun p : ℝ × ℝ =>
        (∑' k : ℤ, deriv (fun z : ℝ => heatKernel p.1 z) (y - p.2 + 2 * (k : ℝ))) +
        (∑' k : ℤ, deriv (fun z : ℝ => heatKernel p.1 z) (y + p.2 + 2 * (k : ℝ))) := by
    funext p; rfl
  rw [hfun]
  apply ContinuousOn.add
  · refine continuousOn_tsum (fun k => ?_) hsummable (fun k p hp => ?_)
    · have hc : ContinuousOn
          (fun p : ℝ × ℝ => deriv (fun z => heatKernel p.1 z) ((-1) * p.2 + (y + 2 * (k:ℝ))))
          (Set.Icc τ₀ T ×ˢ Set.univ) := term_cont (-1) (y + 2 * (k:ℝ)) hτ₀
      have hmono := hc.mono
        (fun p (hp : p ∈ Set.Icc τ₀ T ×ˢ Set.Icc (0:ℝ) 1) => ⟨hp.1, Set.mem_univ _⟩)
      refine (hmono : ContinuousOn _ (Set.Icc τ₀ T ×ˢ Set.Icc (0:ℝ) 1)).congr ?_
      intro p hp
      simp only
      rw [show y - p.2 + 2 * (k:ℝ) = (-1) * p.2 + (y + 2 * (k:ℝ)) by ring]
    · have hb := win_bound hτ₀ y hy hM0 hMbd (-1) (by norm_num) k p hp
      have he : (-1) * p.2 + y + 2 * (k:ℝ) = y - p.2 + 2 * (k:ℝ) := by ring
      rw [he] at hb; exact hb
  · refine continuousOn_tsum (fun k => ?_) hsummable (fun k p hp => ?_)
    · have hc : ContinuousOn
          (fun p : ℝ × ℝ => deriv (fun z => heatKernel p.1 z) (1 * p.2 + (y + 2 * (k:ℝ))))
          (Set.Icc τ₀ T ×ˢ Set.univ) := term_cont 1 (y + 2 * (k:ℝ)) hτ₀
      have hmono := hc.mono
        (fun p (hp : p ∈ Set.Icc τ₀ T ×ˢ Set.Icc (0:ℝ) 1) => ⟨hp.1, Set.mem_univ _⟩)
      refine (hmono : ContinuousOn _ (Set.Icc τ₀ T ×ˢ Set.Icc (0:ℝ) 1)).congr ?_
      intro p hp
      simp only
      rw [show y + p.2 + 2 * (k:ℝ) = 1 * p.2 + (y + 2 * (k:ℝ)) by ring]
    · have hb := win_bound hτ₀ y hy hM0 hMbd 1 (by norm_num) k p hp
      have he : 1 * p.2 + y + 2 * (k:ℝ) = y + p.2 + 2 * (k:ℝ) := by ring
      rw [he] at hb; exact hb


open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)

-- τ-uniform absolute bound on DerivSeries over the box
theorem derivSeries_abs_le {τ₀ T : ℝ} (hτ₀ : 0 < τ₀) {M : ℝ} (hM0 : 0 ≤ M)
    (hMbd : ∀ τ ∈ Set.Icc τ₀ T,
      heatGradPointwiseBound τ * Real.exp (2 ^ 2 / (4 * (2 * τ))) ≤ M)
    (y : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 1) (p : ℝ × ℝ)
    (hp : p ∈ Set.Icc τ₀ T ×ˢ Set.Icc (0:ℝ) 1) :
    |intervalNeumannFullKernelDerivSeries p.1 y p.2|
      ≤ (∑' k : ℤ, M * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (4 * T))))
        + (∑' k : ℤ, M * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (4 * T)))) := by
  have hsummable : Summable
      (fun k : ℤ => M * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (4 * T)))) :=
    (latticeExpSummable (by linarith [hp.1.2, hp.1.1, hτ₀] : (0:ℝ) < 4 * T) 0).mul_left M
  have hfun : intervalNeumannFullKernelDerivSeries p.1 y p.2
      = (∑' k : ℤ, deriv (fun z : ℝ => heatKernel p.1 z) (y - p.2 + 2 * (k : ℝ))) +
        (∑' k : ℤ, deriv (fun z : ℝ => heatKernel p.1 z) (y + p.2 + 2 * (k : ℝ))) := rfl
  rw [hfun]
  have hbnd1 : ∀ k : ℤ, ‖deriv (fun z : ℝ => heatKernel p.1 z) (y - p.2 + 2 * (k:ℝ))‖
      ≤ M * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (4 * T))) := by
    intro k
    have hb := win_bound hτ₀ y hy hM0 hMbd (-1) (by norm_num) k p hp
    rwa [show (-1) * p.2 + y + 2 * (k:ℝ) = y - p.2 + 2 * (k:ℝ) by ring] at hb
  have hbnd2 : ∀ k : ℤ, ‖deriv (fun z : ℝ => heatKernel p.1 z) (y + p.2 + 2 * (k:ℝ))‖
      ≤ M * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (4 * T))) := by
    intro k
    have hb := win_bound hτ₀ y hy hM0 hMbd 1 (by norm_num) k p hp
    rwa [show 1 * p.2 + y + 2 * (k:ℝ) = y + p.2 + 2 * (k:ℝ) by ring] at hb
  have hns1 : Summable
      (fun k : ℤ => ‖deriv (fun z : ℝ => heatKernel p.1 z) (y - p.2 + 2*(k:ℝ))‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hbnd1 hsummable
  have hns2 : Summable
      (fun k : ℤ => ‖deriv (fun z : ℝ => heatKernel p.1 z) (y + p.2 + 2*(k:ℝ))‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hbnd2 hsummable
  rw [← Real.norm_eq_abs]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (norm_tsum_le_tsum_norm hns1).trans (Summable.tsum_le_tsum hbnd1 hns1 hsummable)
  · exact (norm_tsum_le_tsum_norm hns2).trans (Summable.tsum_le_tsum hbnd2 hns2 hsummable)

set_option maxHeartbeats 800000 in
theorem kernelOp_jointCont {τ₀ T : ℝ} (hτ₀ : 0 < τ₀) (hτ₀T : τ₀ ≤ T)
    {Q : ℝ → ℝ} {CQ : ℝ} (hQ_int : Integrable Q (intervalMeasure 1))
    (hQ_bound : ∀ y, |Q y| ≤ CQ) :
    ContinuousOn (fun p : ℝ × ℝ => intervalConjugateKernelOperator p.1 Q p.2)
      (Set.Icc τ₀ T ×ˢ Set.Icc 0 1) := by
  haveI : IsFiniteMeasure (intervalMeasure 1) :=
    ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
  obtain ⟨M, hM0, hMbd⟩ := pref_bound (T := T) hτ₀
  have hCQ : 0 ≤ CQ := le_trans (abs_nonneg (Q 0)) (hQ_bound 0)
  set B : ℝ := (∑' k : ℤ, M * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (4 * T))))
    + (∑' k : ℤ, M * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (4 * T)))) with hBdef
  have hrepr : (fun p : ℝ × ℝ => intervalConjugateKernelOperator p.1 Q p.2)
      = fun p : ℝ × ℝ =>
        -∫ y, intervalNeumannFullKernelDerivSeries p.1 y p.2 * Q y ∂(intervalMeasure 1) := by
    funext p
    exact intervalConjugateKernelOperator_eq_neg_derivSeries_integral p.1 Q p.2
  rw [hrepr]
  apply ContinuousOn.neg
  apply continuousOn_of_dominated (bound := fun _ : ℝ => B * CQ)
  · intro p hp
    have hm : Measurable (fun y : ℝ => intervalNeumannFullKernelDerivSeries p.1 y p.2) :=
      (intervalNeumannFullKernelDerivSeries_joint_measurable).comp
        ((measurable_const.prodMk measurable_id).prodMk measurable_const)
    exact hm.aestronglyMeasurable.mul hQ_int.aestronglyMeasurable
  · intro p hp
    change ∀ᵐ y ∂(volume.restrict (Set.Icc (0:ℝ) 1)), _
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun y hy => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have hDS := derivSeries_abs_le hτ₀ hM0 hMbd y hy p hp
    have hBnn : 0 ≤ B := by
      rw [hBdef]; refine add_nonneg ?_ ?_ <;>
        exact tsum_nonneg (fun k => mul_nonneg hM0 (Real.exp_pos _).le)
    exact mul_le_mul hDS (hQ_bound y) (abs_nonneg _) hBnn
  · exact integrable_const _
  · show ∀ᵐ y ∂(intervalMeasure 1), ContinuousOn (fun p : ℝ × ℝ =>
        intervalNeumannFullKernelDerivSeries p.1 y p.2 * Q y) (Set.Icc τ₀ T ×ˢ Set.Icc 0 1)
    rw [intervalMeasure, ShenWork.IntervalDomain.intervalSet,
      MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun y hy => ?_
    exact (derivSeries_jointCont hτ₀ hτ₀T y hy).mul continuousOn_const

-- THREE-PARAM joint continuity: source varies continuously
set_option maxHeartbeats 1200000 in
theorem kernelOp_src_jointCont {τ₀ T : ℝ} (hτ₀ : 0 < τ₀) (hτ₀T : τ₀ ≤ T)
    {F : ℝ → ℝ → ℝ} {CF : ℝ}
    (_hF_meas : Measurable (Function.uncurry F))
    (hF_cont : Continuous (Function.uncurry F))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CF) :
    ContinuousOn (fun q : (ℝ × ℝ) × ℝ =>
        intervalConjugateKernelOperator q.1.1 (F q.1.2) q.2)
      ((Set.Icc τ₀ T ×ˢ Set.univ) ×ˢ Set.Icc 0 1) := by
  haveI : IsFiniteMeasure (intervalMeasure 1) :=
    ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
  obtain ⟨M, hM0, hMbd⟩ := pref_bound (T := T) hτ₀
  have hCF : 0 ≤ CF := le_trans (abs_nonneg (F 0 0)) (hF_bound 0 0)
  set B : ℝ := (∑' k : ℤ, M * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (4 * T))))
    + (∑' k : ℤ, M * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (4 * T)))) with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]; refine add_nonneg ?_ ?_ <;>
      exact tsum_nonneg (fun k => mul_nonneg hM0 (Real.exp_pos _).le)
  have hrepr : (fun q : (ℝ × ℝ) × ℝ => intervalConjugateKernelOperator q.1.1 (F q.1.2) q.2)
      = fun q : (ℝ × ℝ) × ℝ =>
        -∫ y, intervalNeumannFullKernelDerivSeries q.1.1 y q.2 * F q.1.2 y
          ∂(intervalMeasure 1) := by
    funext q
    exact intervalConjugateKernelOperator_eq_neg_derivSeries_integral q.1.1 (F q.1.2) q.2
  rw [hrepr]
  apply ContinuousOn.neg
  apply continuousOn_of_dominated (bound := fun _ : ℝ => B * CF)
  · intro q hq
    have hm : Measurable (fun y : ℝ => intervalNeumannFullKernelDerivSeries q.1.1 y q.2) :=
      (intervalNeumannFullKernelDerivSeries_joint_measurable).comp
        ((measurable_const.prodMk measurable_id).prodMk measurable_const)
    exact hm.aestronglyMeasurable.mul (hF_int q.1.2).aestronglyMeasurable
  · intro q hq
    change ∀ᵐ y ∂(volume.restrict (Set.Icc (0:ℝ) 1)), _
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun y hy => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have hqbox : (q.1.1, q.2) ∈ Set.Icc τ₀ T ×ˢ Set.Icc (0:ℝ) 1 := ⟨hq.1.1, hq.2⟩
    have hDS := derivSeries_abs_le hτ₀ hM0 hMbd y hy (q.1.1, q.2) hqbox
    exact mul_le_mul hDS (hF_bound q.1.2 y) (abs_nonneg _) hBnn
  · exact integrable_const _
  · show ∀ᵐ y ∂(intervalMeasure 1), ContinuousOn (fun q : (ℝ × ℝ) × ℝ =>
        intervalNeumannFullKernelDerivSeries q.1.1 y q.2 * F q.1.2 y)
          ((Set.Icc τ₀ T ×ˢ Set.univ) ×ˢ Set.Icc 0 1)
    rw [intervalMeasure, ShenWork.IntervalDomain.intervalSet,
      MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun y hy => ?_
    apply ContinuousOn.mul
    · -- (τ,s,x) ↦ DerivSeries τ y x  : continuous in (τ,x), independent of s
      have hbase := derivSeries_jointCont hτ₀ hτ₀T y hy
      have hcomp : ContinuousOn
          (fun q : (ℝ × ℝ) × ℝ => intervalNeumannFullKernelDerivSeries q.1.1 y q.2)
          ((Set.Icc τ₀ T ×ˢ Set.univ) ×ˢ Set.Icc 0 1) := by
        apply hbase.comp (continuousOn_fst.fst.prodMk continuousOn_snd)
        intro q hq; exact ⟨hq.1.1, hq.2⟩
      exact hcomp
    · -- (τ,s,x) ↦ F s y  : continuous in s
      apply Continuous.continuousOn
      exact (hF_cont.comp (continuous_fst.snd.prodMk continuous_const))

theorem boundary_contAt {t : ℝ} {F : ℝ → ℝ → ℝ} {CF : ℝ}
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1)) (hF_bound : ∀ s y, |F s y| ≤ CF)
    {r : ℝ} (hr1 : r < 1)
    (z₀ : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint) (hz0 : z₀.1.1 = 0) :
    ContinuousAt (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      z.1.1 * intervalConjugateKernelOperator (z.1.1 - z.1.1 * r) (F (z.1.1 * r)) z.2.1) z₀ := by
  have hCF : 0 ≤ CF := le_trans (abs_nonneg (F 0 0)) (hF_bound 0 0)
  set Cg := heatGradientLinftyLinftyConstant
  have hCgnn : 0 ≤ Cg := heatGradientLinftyLinftyConstant_nonneg
  have hbound : ∀ z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint,
      ‖z.1.1 * intervalConjugateKernelOperator (z.1.1 - z.1.1 * r) (F (z.1.1 * r)) z.2.1‖
        ≤ Cg * CF * Real.sqrt z.1.1 * (1 - r) ^ (-(1/2):ℝ) := by
    intro z
    rw [Real.norm_eq_abs]
    have hgnn : 0 ≤ Cg * CF * Real.sqrt z.1.1 * (1 - r) ^ (-(1/2):ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg hCgnn hCF) (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (by linarith) _)
    rcases eq_or_lt_of_le z.1.2.1 with hzz | hzpos
    · rw [show z.1.1 = (0:ℝ) from hzz.symm]; simp
    · have hfac : z.1.1 - z.1.1 * r = z.1.1 * (1 - r) := by ring
      have hlag : 0 < z.1.1 * (1 - r) := mul_pos hzpos (by linarith)
      have hb := intervalConjugateKernelOperator_abs_le (hfac ▸ hlag)
        (hF_int (z.1.1 * r)) (hF_bound (z.1.1 * r)) z.2.1
      rw [hfac, Real.mul_rpow hzpos.le (by linarith : (0:ℝ) ≤ 1 - r)] at hb
      rw [hfac, abs_mul, abs_of_pos hzpos]
      calc z.1.1 * |intervalConjugateKernelOperator (z.1.1 * (1 - r)) (F (z.1.1*r)) z.2.1|
          ≤ z.1.1 * (Cg * (z.1.1 ^ (-(1/2):ℝ) * (1 - r) ^ (-(1/2):ℝ)) * CF) :=
            mul_le_mul_of_nonneg_left hb hzpos.le
        _ = Cg * CF * (z.1.1 * z.1.1 ^ (-(1/2):ℝ)) * (1 - r) ^ (-(1/2):ℝ) := by ring
        _ = Cg * CF * Real.sqrt z.1.1 * (1 - r) ^ (-(1/2):ℝ) := by
            have hhalf : z.1.1 * z.1.1 ^ (-(1/2):ℝ) = Real.sqrt z.1.1 := by
              rw [Real.sqrt_eq_rpow]; nth_rewrite 1 [← Real.rpow_one (z.1.1)]
              rw [← Real.rpow_add hzpos]; norm_num
            rw [hhalf]
  have hval0 : z₀.1.1 * intervalConjugateKernelOperator (z₀.1.1 - z₀.1.1 * r)
      (F (z₀.1.1 * r)) z₀.2.1 = 0 := by simp [hz0]
  have htend0 : Filter.Tendsto (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      Cg * CF * Real.sqrt z.1.1 * (1 - r) ^ (-(1/2):ℝ)) (𝓝 z₀) (𝓝 0) := by
    have : Filter.Tendsto (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
        Cg * CF * Real.sqrt z.1.1 * (1 - r) ^ (-(1/2):ℝ)) (𝓝 z₀)
        (𝓝 (Cg * CF * Real.sqrt z₀.1.1 * (1 - r) ^ (-(1/2):ℝ))) := by
      apply Continuous.tendsto; fun_prop
    rw [hz0, Real.sqrt_zero, mul_zero, zero_mul] at this; exact this
  have hsq := squeeze_zero_norm hbound htend0
  rw [ContinuousAt]; rw [hval0]; exact hsq

theorem interior_contAt {t : ℝ} {F : ℝ → ℝ → ℝ}
    (hsrc : ∀ τ₀ : ℝ, 0 < τ₀ →
      ContinuousOn
        (fun q : (ℝ × ℝ) × ℝ => intervalConjugateKernelOperator q.1.1 (F q.1.2) q.2)
        ((Set.Icc τ₀ t ×ˢ Set.univ) ×ˢ Set.Icc 0 1))
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (z₀ : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint) (hz0 : 0 < z₀.1.1) :
    ContinuousAt (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      z.1.1 * intervalConjugateKernelOperator (z.1.1 - z.1.1 * r) (F (z.1.1 * r)) z.2.1) z₀ := by
  set τ₀ : ℝ := (z₀.1.1 / 4) * (1 - r) with hτ₀def
  have hτ₀pos : 0 < τ₀ := mul_pos (by linarith) (by linarith)
  set g : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint → (ℝ × ℝ) × ℝ :=
    fun z => ((z.1.1 * (1 - r), z.1.1 * r), z.2.1) with hgdef
  have hg_cont : Continuous g := by rw [hgdef]; fun_prop
  set S : Set ((ℝ × ℝ) × ℝ) :=
    (Set.Icc τ₀ t ×ˢ Set.univ) ×ˢ Set.Icc (0:ℝ) 1 with hSdef
  have hKon : ContinuousOn (fun q : (ℝ × ℝ) × ℝ =>
      intervalConjugateKernelOperator q.1.1 (F q.1.2) q.2) S := hsrc τ₀ hτ₀pos
  have hmem₀ : g z₀ ∈ S := by
    refine ⟨⟨⟨?_, ?_⟩, Set.mem_univ _⟩, z₀.2.2.1, z₀.2.2.2⟩
    · rw [hτ₀def]; apply mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    · calc z₀.1.1 * (1 - r) ≤ z₀.1.1 * 1 :=
            mul_le_mul_of_nonneg_left (by linarith) z₀.1.2.1
        _ = z₀.1.1 := mul_one _
        _ ≤ t := z₀.1.2.2
  -- g⁻¹ S ∈ 𝓝 z₀
  have hnbhd : g ⁻¹' S ∈ 𝓝 z₀ := by
    have hopen : ∀ᶠ z in 𝓝 z₀, z₀.1.1 / 2 < z.1.1 := by
      have hc : Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint => z.1.1) := by
        fun_prop
      have hmem : z₀ ∈ (fun z => z.1.1) ⁻¹' (Set.Ioi (z₀.1.1 / 2)) := by
        simp only [Set.mem_preimage, Set.mem_Ioi]; linarith
      have := (hc.isOpen_preimage _ isOpen_Ioi).mem_nhds hmem
      filter_upwards [this] with z hz using hz
    filter_upwards [hopen] with z hz
    refine ⟨⟨⟨?_, ?_⟩, Set.mem_univ _⟩, z.2.2.1, z.2.2.2⟩
    · rw [hτ₀def]
      have h1r : 0 ≤ 1 - r := by linarith
      calc z₀.1.1 / 4 * (1 - r) ≤ z₀.1.1 / 2 * (1 - r) :=
            mul_le_mul_of_nonneg_right (by linarith) h1r
        _ ≤ z.1.1 * (1 - r) := mul_le_mul_of_nonneg_right (le_of_lt hz) h1r
    · calc z.1.1 * (1 - r) ≤ z.1.1 * 1 := mul_le_mul_of_nonneg_left (by linarith) z.1.2.1
        _ = z.1.1 := mul_one _
        _ ≤ t := z.1.2.2
  have hKat : ContinuousAt
      (fun z => intervalConjugateKernelOperator (g z).1.1 (F (g z).1.2) (g z).2)
      z₀ := by
    have h1 : ContinuousWithinAt (fun q : (ℝ × ℝ) × ℝ =>
        intervalConjugateKernelOperator q.1.1 (F q.1.2) q.2) S (g z₀) := hKon _ hmem₀
    have h2 : ContinuousWithinAt g (g ⁻¹' S) z₀ := hg_cont.continuousWithinAt
    exact (h1.comp h2 (Set.mapsTo_preimage g S)).continuousAt hnbhd
  have hmul : ContinuousAt
      (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint => z.1.1) z₀ := by
    fun_prop
  have hfin : ContinuousAt (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      z.1.1 * intervalConjugateKernelOperator (g z).1.1 (F (g z).1.2) (g z).2) z₀ := hmul.mul hKat
  have heq : (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      z.1.1 * intervalConjugateKernelOperator (g z).1.1 (F (g z).1.2) (g z).2)
      = fun z => z.1.1 * intervalConjugateKernelOperator
          (z.1.1 - z.1.1 * r) (F (z.1.1 * r)) z.2.1 := by
    funext z; rw [hgdef]; congr 2; ring
  rw [heq] at hfin
  exact hfin

/-! ## (a) — FULL `hG_cont` discharge: boundary squeeze ⊕ interior continuity. -/

/-- **(a) — the full joint continuity discharging `hG_cont`.**  For any jointly
continuous, bounded, per-slice-integrable source family `F`, the rescaled
conjugate-leg integrand
`z ↦ z.1.1 · B_N(z.1.1(1−r))(F(z.1.1·r))(z.2.1)` is `Continuous` on the whole box
`[0,t] × Ω̄`: at `z.1.1=0` by the `√(z.1.1)` squeeze (`boundary_contAt`), at
`z.1.1>0` by the three-param joint continuity (`interior_contAt`). -/
theorem conjugateLeg_hG_cont {t : ℝ} {F : ℝ → ℝ → ℝ} {CF : ℝ}
    (hF_meas : Measurable (Function.uncurry F)) (hF_cont : Continuous (Function.uncurry F))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1)) (hF_bound : ∀ s y, |F s y| ≤ CF)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      z.1.1 * intervalConjugateKernelOperator (z.1.1 - z.1.1 * r) (F (z.1.1 * r)) z.2.1) := by
  have hsrc : ∀ τ₀ : ℝ, 0 < τ₀ →
      ContinuousOn
        (fun q : (ℝ × ℝ) × ℝ => intervalConjugateKernelOperator q.1.1 (F q.1.2) q.2)
        ((Set.Icc τ₀ t ×ˢ Set.univ) ×ˢ Set.Icc 0 1) := by
    intro τ₀ hτ₀
    by_cases htt : τ₀ ≤ t
    · exact kernelOp_src_jointCont hτ₀ htt hF_meas hF_cont hF_int hF_bound
    · have hempty : (Set.Icc τ₀ t ×ˢ (Set.univ : Set ℝ)) ×ˢ Set.Icc (0:ℝ) 1 = ∅ := by
        rw [Set.Icc_eq_empty (by linarith)]; simp
      rw [hempty]; exact continuousOn_empty _
  rw [continuous_iff_continuousAt]
  intro z₀
  rcases eq_or_lt_of_le z₀.1.2.1 with hz0 | hz0
  · exact boundary_contAt hF_int hF_bound hr1 z₀ hz0.symm
  · exact interior_contAt hsrc hr0 hr1 z₀ hz0

/-- **(a) — the discharged `conjugateLeg_continuous`.**  The landed singular-
Duhamel engine `ShenWork.Paper2.IntervalChiNegTrajBanachClose.conjugateLeg_continuous`
with its sole carried input `hG_cont` supplied by `conjugateLeg_hG_cont`, for any
jointly continuous bounded source family `F`. -/
theorem conjugateLeg_continuous_full {t : ℝ} {F : ℝ → ℝ → ℝ} {CF : ℝ} (hCF : 0 ≤ CF)
    (hF_meas : Measurable (Function.uncurry F)) (hF_cont : Continuous (Function.uncurry F))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1)) (hF_bound : ∀ s y, |F s y| ≤ CF) :
    Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      ∫ s in (0 : ℝ)..(z.1.1),
        intervalConjugateKernelOperator (z.1.1 - s) (F s) z.2.1) :=
  ShenWork.Paper2.IntervalChiNegTrajBanachClose.conjugateLeg_continuous hCF hF_meas hF_int hF_bound
    (by
      have hne1 : ∀ᵐ r : ℝ ∂volume, r ≠ 1 := by
        rw [MeasureTheory.ae_iff]
        simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
      filter_upwards [hne1] with r hr1 hr
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hr
      exact conjugateLeg_hG_cont hF_meas hF_cont hF_int hF_bound hr.1
        (lt_of_le_of_ne hr.2 hr1))

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms derivSeries_jointCont
#print axioms kernelOp_jointCont
#print axioms kernelOp_src_jointCont
#print axioms boundary_contAt
#print axioms interior_contAt
#print axioms conjugateLeg_hG_cont
#print axioms conjugateLeg_continuous_full
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegTrajBanachFinal
