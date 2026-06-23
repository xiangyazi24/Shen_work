/-
  ShenWork/Paper2/IntervalChiNegValueOpCont.lean

  chi0<0 -- crux B: the logistic-leg (NON-singular semigroup) joint continuity.

  Builds `valueOp_src_jointCont`, the SOURCE-GENERIC joint (tau,x)-continuity of
  the value operator `intervalFullSemigroupOperator`, MIRRORING the landed
  B-kernel analogue `kernelOp_src_jointCont` (IntervalChiNegTrajBanachFinal) but
  for the value (non-singular) operator: constant L-infty majorant, no diagonal
  singularity.  This discharges the sole carried `hG_cont` of the landed
  `logisticLeg_continuous_reduced` (IntervalChiNegLegContinuity), closing the
  logistic value-Duhamel leg's full-box continuity for the conjugate solution.

  Two-way audited.  Consumed landed lemmas (hyps supplied here):
   * `continuousOn_of_dominated` (Mathlib) -- the DCT joint-continuity engine,
     instantiated exactly as `kernelOp_src_jointCont` does.
   * `heatKernel_le_windowShift` + `latticeExpSummable` -- the T-uniform value
     Weierstrass majorant.
   * `term_cont` (IntervalChiNegTrajBanachFinal, value-side via `heatKernel`)
     -- per-term joint (t,x) continuity (built here for the value kernel).
   * `intervalFullSemigroupOperator_Linfty_bound`, `intervalFullSemigroupOperator_zero`
     -- the constant majorant + the tau=0 value.
   * `logisticLeg_continuous_reduced` -- the engine whose `hG_cont` we discharge.

  hmean0 (`|cosineCoeffs (lift u0) 0| <= D.M`): the cosine-0-to-mean bridge is the
  landed `cosineCoeffs_zero_abs_le_of_bound`; the residual is the accessor
  `|u0 x| <= D.M` on the conjugate data `D` (see CARRIED note at end).

  No sorry/admit/native_decide/custom axiom.  Lines <= 100.  Mathlib v4.29.1.
-/
import ShenWork.Paper2.IntervalChiNegLegContinuity
import ShenWork.PDE.IntervalFullKernelGradientLinfty
import ShenWork.PDE.IntervalFullKernelSDependentMeasurable
import ShenWork.Paper2.IntervalMildPicardRegularity

open MeasureTheory Set
open scoped Topology Interval
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure intervalSet)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalNeumannFullKernel cosineCoeffs
   heatKernel_le_windowShift heatKernelWindowBound latticeExpSummable
   latticeGaussianSummable heatKernel_of_nonpos measurable_tsum_int_of_summable)

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegValueOpCont

/-! ## Per-term joint (t,x) continuity of the value kernel. -/

/-- The shifted Gaussian `(t,x) ↦ heatKernel t (a·x + c)` is jointly continuous on
`[τ₀,T] × univ` (τ₀ > 0).  Value-side analogue of `term_cont`. -/
theorem valueTerm_cont (a c : ℝ) {τ₀ T : ℝ} (hτ₀ : 0 < τ₀) :
    ContinuousOn (fun p : ℝ × ℝ => heatKernel p.1 (a * p.2 + c))
      (Set.Icc τ₀ T ×ˢ Set.univ) := by
  unfold heatKernel
  apply ContinuousOn.mul
  · apply ContinuousOn.div continuousOn_const
      (by apply Continuous.continuousOn; fun_prop)
    intro p hp; have h : 0 < p.1 := lt_of_lt_of_le hτ₀ hp.1.1
    exact Real.sqrt_ne_zero'.mpr (by positivity)
  · apply ContinuousOn.rexp
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro p hp; have h : 0 < p.1 := lt_of_lt_of_le hτ₀ hp.1.1; positivity

/-! ## T-uniform value Weierstrass majorant. -/

/-- The `[τ₀,T]×[0,1]`-uniform value-kernel term bound: with `|a·x + y| ≤ 2`
(the unit window), `heatKernel t (a·x+y+2k) ≤ Mval·exp(−(2k)²/(8T))` for a
`(t,x)`-free `Mval = (1/√(4πτ₀))·exp(1/τ₀)`.  Value analogue of `win_bound`. -/
theorem valueWin_bound {τ₀ T : ℝ} (hτ₀ : 0 < τ₀) (c : ℝ) (hc : |c| ≤ 1)
    (a : ℝ) (ha : |a| ≤ 1) (k : ℤ) (p : ℝ × ℝ)
    (hp : p ∈ Set.Icc τ₀ T ×ˢ Set.Icc (0:ℝ) 1) :
    ‖heatKernel p.1 (a * p.2 + c + 2 * (k:ℝ))‖
      ≤ ((1 / Real.sqrt (4 * Real.pi * τ₀)) * Real.exp (1 / τ₀))
          * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (2 * T))) := by
  have hτpos : 0 < p.1 := lt_of_lt_of_le hτ₀ hp.1.1
  rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg hτpos _)]
  have hwin : |a * p.2 + c + 2 * (k:ℝ) - (0 + 2 * (k:ℝ))| ≤ 2 := by
    have h1 : |a * p.2| ≤ 1 := by
      rw [abs_mul]
      calc |a| * |p.2| ≤ 1 * |p.2| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
        _ = |p.2| := one_mul _
        _ ≤ 1 := by rw [abs_of_nonneg hp.2.1]; exact hp.2.2
    calc |a * p.2 + c + 2 * (k:ℝ) - (0 + 2 * (k:ℝ))|
        = |a * p.2 + c| := by ring_nf
      _ ≤ |a * p.2| + |c| := abs_add_le _ _
      _ ≤ 1 + 1 := by linarith
      _ = 2 := by norm_num
  have hbd := heatKernel_le_windowShift hτpos 0 2 k hwin
  refine hbd.trans ?_
  unfold heatKernelWindowBound
  have hpref : (1 / Real.sqrt (4 * Real.pi * p.1)) * Real.exp (2 ^ 2 / (4 * p.1))
      ≤ (1 / Real.sqrt (4 * Real.pi * τ₀)) * Real.exp (1 / τ₀) := by
    apply mul_le_mul
    · apply one_div_le_one_div_of_le (by positivity)
      apply Real.sqrt_le_sqrt; nlinarith [hp.1.1, Real.pi_pos]
    · apply Real.exp_le_exp.mpr
      rw [show (2:ℝ) ^ 2 / (4 * p.1) = 1 / p.1 by ring]
      exact one_div_le_one_div_of_le hτ₀ hp.1.1
    · exact (Real.exp_pos _).le
    · positivity
  have hgauss : Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (2 * p.1)))
      ≤ Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (2 * T))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [hp.1.2]
  calc (1 / Real.sqrt (4 * Real.pi * p.1)) * Real.exp (2 ^ 2 / (4 * p.1))
          * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (2 * p.1)))
        ≤ ((1 / Real.sqrt (4 * Real.pi * τ₀)) * Real.exp (1 / τ₀))
            * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (2 * p.1))) :=
          mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le
      _ ≤ ((1 / Real.sqrt (4 * Real.pi * τ₀)) * Real.exp (1 / τ₀))
            * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (2 * T))) :=
          mul_le_mul_of_nonneg_left hgauss (by positivity)

/-! ## Joint (t,x) continuity of the value kernel (fixed y). -/

/-- The full value kernel `(t,x) ↦ K_full t x y` is jointly continuous on
`[τ₀,T]×[0,1]` (fixed `y∈[0,1]`).  Value analogue of `derivSeries_jointCont`:
`continuousOn_tsum` with per-term `valueTerm_cont` and majorant `valueWin_bound`. -/
theorem fullKernel_jointCont {τ₀ T : ℝ} (hτ₀ : 0 < τ₀) (hτ₀T : τ₀ ≤ T) (y : ℝ)
    (hy : y ∈ Set.Icc (0:ℝ) 1) :
    ContinuousOn (fun p : ℝ × ℝ => intervalNeumannFullKernel p.1 p.2 y)
      (Set.Icc τ₀ T ×ˢ Set.Icc 0 1) := by
  have hT : 0 < T := lt_of_lt_of_le hτ₀ hτ₀T
  have hcy : |(-y)| ≤ 1 := by rw [abs_neg, abs_of_nonneg hy.1]; exact hy.2
  have hcy' : |y| ≤ 1 := by rw [abs_of_nonneg hy.1]; exact hy.2
  have hsummable : Summable
      (fun k : ℤ => ((1 / Real.sqrt (4 * Real.pi * τ₀)) * Real.exp (1 / τ₀))
        * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (2 * T)))) :=
    (latticeExpSummable (by linarith : (0:ℝ) < 2 * T) 0).mul_left _
  have hfun : (fun p : ℝ × ℝ => intervalNeumannFullKernel p.1 p.2 y)
      = fun p : ℝ × ℝ =>
        (∑' k : ℤ, heatKernel p.1 (p.2 - y + 2 * (k:ℝ))) +
        (∑' k : ℤ, heatKernel p.1 (p.2 + y + 2 * (k:ℝ))) := by
    funext p
    rw [intervalNeumannFullKernel]
    by_cases hp1 : 0 < p.1
    · rw [Summable.tsum_add (latticeGaussianSummable hp1 (p.2 - y))
        (latticeGaussianSummable hp1 (p.2 + y))]
    · rw [not_lt] at hp1
      simp only [heatKernel_of_nonpos hp1, add_zero, tsum_zero]
  rw [hfun]
  apply ContinuousOn.add
  · refine continuousOn_tsum (fun k => ?_) hsummable (fun k p hp => ?_)
    · have hc := valueTerm_cont (T := T) 1 ((-y) + 2 * (k:ℝ)) hτ₀
      have hmono := hc.mono
        (fun p (hp : p ∈ Set.Icc τ₀ T ×ˢ Set.Icc (0:ℝ) 1) => ⟨hp.1, Set.mem_univ _⟩)
      refine (hmono : ContinuousOn _ (Set.Icc τ₀ T ×ˢ Set.Icc (0:ℝ) 1)).congr ?_
      intro p hp; simp only
      rw [show p.2 - y + 2 * (k:ℝ) = 1 * p.2 + ((-y) + 2 * (k:ℝ)) by ring]
    · have hb := valueWin_bound hτ₀ (-y) hcy 1 (by norm_num) k p hp
      have he : 1 * p.2 + (-y) + 2 * (k:ℝ) = p.2 - y + 2 * (k:ℝ) := by ring
      rw [he] at hb; exact hb
  · refine continuousOn_tsum (fun k => ?_) hsummable (fun k p hp => ?_)
    · have hc := valueTerm_cont (T := T) 1 (y + 2 * (k:ℝ)) hτ₀
      have hmono := hc.mono
        (fun p (hp : p ∈ Set.Icc τ₀ T ×ˢ Set.Icc (0:ℝ) 1) => ⟨hp.1, Set.mem_univ _⟩)
      refine (hmono : ContinuousOn _ (Set.Icc τ₀ T ×ˢ Set.Icc (0:ℝ) 1)).congr ?_
      intro p hp; simp only
      rw [show p.2 + y + 2 * (k:ℝ) = 1 * p.2 + (y + 2 * (k:ℝ)) by ring]
    · have hb := valueWin_bound hτ₀ y hcy' 1 (by norm_num) k p hp
      have he : 1 * p.2 + y + 2 * (k:ℝ) = p.2 + y + 2 * (k:ℝ) := by ring
      rw [he] at hb; exact hb

/-! ## Box-uniform pointwise bound on the value kernel. -/

/-- The box-uniform pointwise value-kernel majorant constant. -/
def valueKernelBound (τ₀ T : ℝ) : ℝ :=
  (∑' k : ℤ, ((1 / Real.sqrt (4 * Real.pi * τ₀)) * Real.exp (1 / τ₀))
      * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (2 * T))))
  + (∑' k : ℤ, ((1 / Real.sqrt (4 * Real.pi * τ₀)) * Real.exp (1 / τ₀))
      * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (2 * T))))

theorem valueKernelBound_nonneg {τ₀ T : ℝ} (hτ₀ : 0 < τ₀) :
    0 ≤ valueKernelBound τ₀ T := by
  refine add_nonneg ?_ ?_ <;>
    exact tsum_nonneg (fun k => mul_nonneg (by positivity) (Real.exp_pos _).le)

/-- Box-uniform pointwise bound: `K_full(t,x,y) ≤ valueKernelBound` for
`(t,x)∈[τ₀,T]×[0,1]`, `y∈[0,1]`.  Termwise `valueWin_bound` on each lattice sum. -/
theorem fullKernel_le {τ₀ T : ℝ} (hτ₀ : 0 < τ₀) (hτ₀T : τ₀ ≤ T)
    {t x y : ℝ} (ht : t ∈ Set.Icc τ₀ T) (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hy : y ∈ Set.Icc (0:ℝ) 1) :
    intervalNeumannFullKernel t x y ≤ valueKernelBound τ₀ T := by
  have htpos : 0 < t := lt_of_lt_of_le hτ₀ ht.1
  have hMaj : Summable
      (fun k : ℤ => ((1 / Real.sqrt (4 * Real.pi * τ₀)) * Real.exp (1 / τ₀))
        * Real.exp (-(0 + 2 * (k:ℝ)) ^ 2 / (4 * (2 * T)))) :=
    (latticeExpSummable (by linarith [lt_of_lt_of_le hτ₀ hτ₀T] : (0:ℝ) < 2 * T) 0).mul_left _
  have hsplit : intervalNeumannFullKernel t x y
      = (∑' k : ℤ, heatKernel t (x - y + 2 * (k:ℝ)))
        + (∑' k : ℤ, heatKernel t (x + y + 2 * (k:ℝ))) := by
    rw [intervalNeumannFullKernel, Summable.tsum_add (latticeGaussianSummable htpos (x - y))
      (latticeGaussianSummable htpos (x + y))]
  have hpref_le : ∀ (k_ : ℤ) (z : ℝ), |z| ≤ 2 →
      heatKernel t (z + 2 * (k_ : ℝ)) ≤ ((1 / Real.sqrt (4 * Real.pi * τ₀)) * Real.exp (1 / τ₀))
        * Real.exp (-(0 + 2 * (k_:ℝ)) ^ 2 / (4 * (2 * T))) := by
    intro k_ z hz
    have hbd := heatKernel_le_windowShift htpos 0 2 k_
      (by rw [show z + 2 * (k_:ℝ) - (0 + 2 * (k_:ℝ)) = z by ring]; exact hz)
    refine hbd.trans ?_
    unfold heatKernelWindowBound
    have hpref : (1 / Real.sqrt (4 * Real.pi * t)) * Real.exp (2 ^ 2 / (4 * t))
        ≤ (1 / Real.sqrt (4 * Real.pi * τ₀)) * Real.exp (1 / τ₀) := by
      apply mul_le_mul
      · apply one_div_le_one_div_of_le (by positivity)
        apply Real.sqrt_le_sqrt; nlinarith [ht.1, Real.pi_pos]
      · apply Real.exp_le_exp.mpr
        rw [show (2:ℝ) ^ 2 / (4 * t) = 1 / t by ring]
        exact one_div_le_one_div_of_le hτ₀ ht.1
      · exact (Real.exp_pos _).le
      · positivity
    have hgauss : Real.exp (-(0 + 2 * (k_:ℝ)) ^ 2 / (4 * (2 * t)))
        ≤ Real.exp (-(0 + 2 * (k_:ℝ)) ^ 2 / (4 * (2 * T))) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_div, neg_le_neg_iff]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [ht.2]
    calc (1 / Real.sqrt (4 * Real.pi * t)) * Real.exp (2 ^ 2 / (4 * t))
            * Real.exp (-(0 + 2 * (k_:ℝ)) ^ 2 / (4 * (2 * t)))
          ≤ ((1 / Real.sqrt (4 * Real.pi * τ₀)) * Real.exp (1 / τ₀))
              * Real.exp (-(0 + 2 * (k_:ℝ)) ^ 2 / (4 * (2 * t))) :=
            mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le
        _ ≤ ((1 / Real.sqrt (4 * Real.pi * τ₀)) * Real.exp (1 / τ₀))
              * Real.exp (-(0 + 2 * (k_:ℝ)) ^ 2 / (4 * (2 * T))) :=
            mul_le_mul_of_nonneg_left hgauss (by positivity)
  rw [hsplit, valueKernelBound]
  apply add_le_add
  · refine Summable.tsum_le_tsum (fun k => ?_) (latticeGaussianSummable htpos (x - y)) hMaj
    have hz : |x - y| ≤ 2 := by
      rw [abs_le]; exact ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
    have he : x - y + 2 * (k:ℝ) = (x - y) + 2 * (k:ℝ) := by ring
    rw [he]; exact hpref_le k (x - y) hz
  · refine Summable.tsum_le_tsum (fun k => ?_) (latticeGaussianSummable htpos (x + y)) hMaj
    have hz : |x + y| ≤ 2 := by
      rw [abs_le]; exact ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩
    have he : x + y + 2 * (k:ℝ) = (x + y) + 2 * (k:ℝ) := by ring
    rw [he]; exact hpref_le k (x + y) hz

/-! ## Joint measurability of the value kernel. -/

/-- Joint measurability of `(q,y) ↦ K_full(q.1.1, q.2, y)` — value analogue of the
private `intervalNeumannFullKernel_joint_measurable`, built inline from
`measurable_tsum_int_of_summable`. -/
theorem fullKernel_joint_measurable :
    Measurable (fun q : (ℝ × ℝ) × ℝ =>
      intervalNeumannFullKernel q.1.1 q.1.2 q.2) := by
  set g : ℤ → (ℝ × ℝ) × ℝ → ℝ :=
    fun k q => heatKernel q.1.1 (q.1.2 - q.2 + 2 * (k:ℝ)) +
      heatKernel q.1.1 (q.1.2 + q.2 + 2 * (k:ℝ)) with hg_def
  have hg_meas : ∀ k, Measurable (g k) := by
    intro k
    show Measurable (fun q : (ℝ × ℝ) × ℝ =>
      heatKernel q.1.1 (q.1.2 - q.2 + 2 * (k:ℝ)) +
        heatKernel q.1.1 (q.1.2 + q.2 + 2 * (k:ℝ)))
    unfold heatKernel; fun_prop
  have hg_sum : ∀ q : (ℝ × ℝ) × ℝ, Summable (fun k : ℤ => g k q) := by
    intro q
    rcases lt_or_ge 0 q.1.1 with ht | ht
    · exact (latticeGaussianSummable ht (q.1.2 - q.2)).add
        (latticeGaussianSummable ht (q.1.2 + q.2))
    · have hzero : (fun k : ℤ => g k q) = fun _ : ℤ => (0:ℝ) := by
        funext k; simp [hg_def, heatKernel_of_nonpos ht]
      rw [hzero]; exact summable_zero
  have hmeas := measurable_tsum_int_of_summable hg_meas hg_sum
  have hfun : (fun q : (ℝ × ℝ) × ℝ => intervalNeumannFullKernel q.1.1 q.1.2 q.2)
      = fun q : (ℝ × ℝ) × ℝ => ∑' k : ℤ, g k q := by funext q; rfl
  rw [hfun]; exact hmeas

/-! ## Crux B — `valueOp_src_jointCont` (the source-generic value-op continuity). -/

set_option maxHeartbeats 1200000 in
/-- **Crux B.**  THREE-param joint continuity of the value operator: for a jointly
continuous bounded measurable source family `F`, the map
`q ↦ S(q.1.1)(F q.1.2)(q.2)` is continuous on `[τ₀,T]×univ×[0,1]`.  Value
(non-singular) analogue of `kernelOp_src_jointCont`: DCT (`continuousOn_of_dominated`)
with the CONSTANT majorant `1·CF` (the kernel has unit mass), per-fibre continuity
from `fullKernel_jointCont`. -/
theorem valueOp_src_jointCont {τ₀ T : ℝ} (hτ₀ : 0 < τ₀) (hτ₀T : τ₀ ≤ T)
    {F : ℝ → ℝ → ℝ} {CF : ℝ}
    (hF_meas : Measurable (Function.uncurry F))
    (hF_cont : Continuous (Function.uncurry F))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CF) :
    ContinuousOn (fun q : (ℝ × ℝ) × ℝ =>
        intervalFullSemigroupOperator q.1.1 (F q.1.2) q.2)
      ((Set.Icc τ₀ T ×ˢ Set.univ) ×ˢ Set.Icc 0 1) := by
  haveI : IsFiniteMeasure (intervalMeasure 1) :=
    ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
  have hCF : 0 ≤ CF := le_trans (abs_nonneg (F 0 0)) (hF_bound 0 0)
  apply continuousOn_of_dominated (bound := fun _ : ℝ => valueKernelBound τ₀ T * CF)
  · intro q hq
    have hm : Measurable (fun y : ℝ => intervalNeumannFullKernel q.1.1 q.2 y) :=
      fullKernel_joint_measurable.comp
        (f := fun y : ℝ => ((q.1.1, q.2), y))
        ((measurable_const.prodMk measurable_const).prodMk measurable_id)
    exact hm.aestronglyMeasurable.mul (hF_int q.1.2).aestronglyMeasurable
  · intro q hq
    rw [intervalMeasure, ShenWork.IntervalDomain.intervalSet,
      MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun y hy => ?_
    have hq1 : 0 < q.1.1 := lt_of_lt_of_le hτ₀ hq.1.1.1
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_nonneg hq1 _ _)]
    exact mul_le_mul (fullKernel_le hτ₀ hτ₀T hq.1.1 hq.2 hy) (hF_bound q.1.2 y)
      (abs_nonneg _) (valueKernelBound_nonneg hτ₀)
  · exact integrable_const _
  · show ∀ᵐ y ∂(intervalMeasure 1), ContinuousOn (fun q : (ℝ × ℝ) × ℝ =>
        intervalNeumannFullKernel q.1.1 q.2 y * F q.1.2 y)
          ((Set.Icc τ₀ T ×ˢ Set.univ) ×ˢ Set.Icc 0 1)
    rw [intervalMeasure, ShenWork.IntervalDomain.intervalSet,
      MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun y hy => ?_
    apply ContinuousOn.mul
    · have hbase := fullKernel_jointCont hτ₀ hτ₀T y hy
      have hcomp : ContinuousOn
          (fun q : (ℝ × ℝ) × ℝ => intervalNeumannFullKernel q.1.1 q.2 y)
          ((Set.Icc τ₀ T ×ˢ Set.univ) ×ˢ Set.Icc 0 1) := by
        apply hbase.comp (continuousOn_fst.fst.prodMk continuousOn_snd)
        intro q hq; exact ⟨hq.1.1, hq.2⟩
      exact hcomp
    · exact (hF_cont.comp (continuous_fst.snd.prodMk continuous_const)).continuousOn

/-! ## `hG_cont` discharge for the logistic (value) leg — boundary squeeze. -/

/-- **Boundary continuity (z.1.1 = 0).**  At `z.1.1 = 0` the rescaled value-leg
integrand vanishes; the constant `z.1.1·CL` majorant squeezes it to `0`.  Value
analogue of `boundary_contAt` (no `√t`, constant majorant). -/
theorem valueLeg_boundary_contAt {t : ℝ} {Lsrc : ℝ → ℝ → ℝ} {CL : ℝ}
    (hCL : 0 ≤ CL) (hL_bound : ∀ s y, |Lsrc s y| ≤ CL)
    {r : ℝ} (hr1 : r < 1)
    (z₀ : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint) (hz0 : z₀.1.1 = 0) :
    ContinuousAt (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      z.1.1 * intervalFullSemigroupOperator (z.1.1 - z.1.1 * r) (Lsrc (z.1.1 * r)) z.2.1) z₀ := by
  have hbound : ∀ z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint,
      ‖z.1.1 * intervalFullSemigroupOperator (z.1.1 - z.1.1 * r) (Lsrc (z.1.1 * r)) z.2.1‖
        ≤ z.1.1 * CL := by
    intro z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg z.1.2.1]
    rcases eq_or_lt_of_le z.1.2.1 with hzz | hzpos
    · rw [show z.1.1 = (0:ℝ) from hzz.symm]; simp
    · have hfac : 0 < z.1.1 - z.1.1 * r := by nlinarith [hr1, hzpos]
      have hb := ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
        hfac hCL (hL_bound (z.1.1 * r)) z.2.1
      exact mul_le_mul_of_nonneg_left hb z.1.2.1
  have hval0 : z₀.1.1 * intervalFullSemigroupOperator (z₀.1.1 - z₀.1.1 * r)
      (Lsrc (z₀.1.1 * r)) z₀.2.1 = 0 := by rw [hz0]; ring
  have htend0 : Filter.Tendsto (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      z.1.1 * CL) (𝓝 z₀) (𝓝 0) := by
    have : Filter.Tendsto (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint => z.1.1 * CL)
        (𝓝 z₀) (𝓝 (z₀.1.1 * CL)) := by apply Continuous.tendsto; fun_prop
    rw [hz0, zero_mul] at this; exact this
  have hsq := squeeze_zero_norm hbound htend0
  rw [ContinuousAt, hval0]; exact hsq

/-! ## `hG_cont` discharge — interior continuity. -/

/-- **Interior continuity (z.1.1 > 0).**  Via `valueOp_src_jointCont` (the source
generic value-op joint continuity), composed with the rescaling map
`z ↦ ((z.1.1(1−r), z.1.1·r), z.2.1)`.  Value analogue of `interior_contAt`. -/
theorem valueLeg_interior_contAt {t : ℝ} {Lsrc : ℝ → ℝ → ℝ} {CL : ℝ} (hCL : 0 ≤ CL)
    (hL_meas : Measurable (Function.uncurry Lsrc))
    (hL_cont : Continuous (Function.uncurry Lsrc))
    (hL_int : ∀ s, Integrable (Lsrc s) (intervalMeasure 1))
    (hL_bound : ∀ s y, |Lsrc s y| ≤ CL)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (z₀ : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint) (hz0 : 0 < z₀.1.1) :
    ContinuousAt (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      z.1.1 * intervalFullSemigroupOperator (z.1.1 - z.1.1 * r) (Lsrc (z.1.1 * r)) z.2.1) z₀ := by
  set τ₀ : ℝ := (z₀.1.1 / 4) * (1 - r) with hτ₀def
  have hτ₀pos : 0 < τ₀ := mul_pos (by linarith) (by linarith)
  set g : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint → (ℝ × ℝ) × ℝ :=
    fun z => ((z.1.1 * (1 - r), z.1.1 * r), z.2.1) with hgdef
  have hg_cont : Continuous g := by rw [hgdef]; fun_prop
  set S : Set ((ℝ × ℝ) × ℝ) :=
    (Set.Icc τ₀ t ×ˢ Set.univ) ×ˢ Set.Icc (0:ℝ) 1 with hSdef
  have hKon : ContinuousOn (fun q : (ℝ × ℝ) × ℝ =>
      intervalFullSemigroupOperator q.1.1 (Lsrc q.1.2) q.2) S :=
    valueOp_src_jointCont hτ₀pos (by
      calc τ₀ = (z₀.1.1 / 4) * (1 - r) := hτ₀def
        _ ≤ z₀.1.1 * 1 := by
            apply mul_le_mul (by linarith) (by linarith) (by linarith) z₀.1.2.1
        _ = z₀.1.1 := mul_one _
        _ ≤ t := z₀.1.2.2) hL_meas hL_cont hL_int hL_bound
  have hmem₀ : g z₀ ∈ S := by
    refine ⟨⟨⟨?_, ?_⟩, Set.mem_univ _⟩, z₀.2.2.1, z₀.2.2.2⟩
    · rw [hτ₀def]; apply mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    · calc z₀.1.1 * (1 - r) ≤ z₀.1.1 * 1 :=
            mul_le_mul_of_nonneg_left (by linarith) z₀.1.2.1
        _ = z₀.1.1 := mul_one _
        _ ≤ t := z₀.1.2.2
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
      (fun z => intervalFullSemigroupOperator (g z).1.1 (Lsrc (g z).1.2) (g z).2) z₀ := by
    have h1 : ContinuousWithinAt (fun q : (ℝ × ℝ) × ℝ =>
        intervalFullSemigroupOperator q.1.1 (Lsrc q.1.2) q.2) S (g z₀) := hKon _ hmem₀
    have h2 : ContinuousWithinAt g (g ⁻¹' S) z₀ := hg_cont.continuousWithinAt
    exact (h1.comp h2 (Set.mapsTo_preimage g S)).continuousAt hnbhd
  have hmul : ContinuousAt
      (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint => z.1.1) z₀ := by fun_prop
  have hfin : ContinuousAt (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      z.1.1 * intervalFullSemigroupOperator (g z).1.1 (Lsrc (g z).1.2) (g z).2) z₀ :=
    hmul.mul hKat
  have heq : (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      z.1.1 * intervalFullSemigroupOperator (g z).1.1 (Lsrc (g z).1.2) (g z).2)
      = fun z => z.1.1 * intervalFullSemigroupOperator
          (z.1.1 - z.1.1 * r) (Lsrc (z.1.1 * r)) z.2.1 := by
    funext z; rw [hgdef]; congr 2; ring
  rw [heq] at hfin; exact hfin

/-! ## `hG_cont` discharge — full box, then the logistic-leg closer. -/

/-- **The full `hG_cont` of the logistic (value) leg.**  For every `r < 1` the
rescaled value-leg integrand `z ↦ z.1.1·S(z.1.1(1−r))(Lsrc(z.1.1·r))(z.2)` is
`Continuous` on the whole box `[0,t]×Ω̄`: boundary squeeze at `z.1.1=0`, interior
joint continuity at `z.1.1>0`.  Value analogue of `conjugateLeg_hG_cont`. -/
theorem valueLeg_hG_cont {t : ℝ} {Lsrc : ℝ → ℝ → ℝ} {CL : ℝ} (hCL : 0 ≤ CL)
    (hL_meas : Measurable (Function.uncurry Lsrc))
    (hL_cont : Continuous (Function.uncurry Lsrc))
    (hL_int : ∀ s, Integrable (Lsrc s) (intervalMeasure 1))
    (hL_bound : ∀ s y, |Lsrc s y| ≤ CL)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      z.1.1 * intervalFullSemigroupOperator (z.1.1 - z.1.1 * r) (Lsrc (z.1.1 * r)) z.2.1) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  rcases eq_or_lt_of_le z₀.1.2.1 with hz0 | hz0
  · exact valueLeg_boundary_contAt hCL hL_bound hr1 z₀ hz0.symm
  · exact valueLeg_interior_contAt hCL hL_meas hL_cont hL_int hL_bound hr0 hr1 z₀ hz0

/-- **The discharged logistic value-Duhamel leg continuity.**  The landed engine
`logisticLeg_continuous_reduced` (IntervalChiNegLegContinuity) with its sole carried
input `hG_cont` supplied by `valueLeg_hG_cont`, for any jointly continuous bounded
integrable measurable source family `Lsrc`.  This closes the logistic leg's full-box
continuity for the conjugate solution. -/
theorem logisticLeg_continuous_full {t : ℝ} (ht0 : 0 ≤ t) {Lsrc : ℝ → ℝ → ℝ} {CL : ℝ}
    (hCL : 0 ≤ CL) (hL_meas : Measurable (Function.uncurry Lsrc))
    (hL_cont : Continuous (Function.uncurry Lsrc))
    (hL_int : ∀ s, Integrable (Lsrc s) (intervalMeasure 1))
    (hL_bound : ∀ s y, |Lsrc s y| ≤ CL) :
    Continuous (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
      ∫ s in (0 : ℝ)..(z.1.1),
        intervalFullSemigroupOperator (z.1.1 - s) (Lsrc s) z.2.1) :=
  ShenWork.Paper2.IntervalChiNegLegContinuity.logisticLeg_continuous_reduced ht0 hCL hL_meas
    hL_bound
    (by
      have hne1 : ∀ᵐ r : ℝ ∂volume, r ≠ 1 := by
        rw [MeasureTheory.ae_iff]
        simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
      filter_upwards [hne1] with r hr1 hr
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hr
      exact valueLeg_hG_cont hCL hL_meas hL_cont hL_int hL_bound hr.1
        (lt_of_le_of_ne hr.2 hr1))

/-! ## hmean0 — the cosine-0-to-mean bridge, REDUCED to the datum-bound accessor.

`hmean0 : |cosineCoeffs (lift u₀) 0| ≤ M`.  The bridge `cosineCoeffs (lift u₀) 0`
= `∫₀¹ u₀` (the k=0 cosine mode = mean), bounded by `sup|u₀| ≤ M`, is the landed
`cosineCoeffs_zero_abs_le_of_bound`.  The ONLY residual is the datum sup-bound
`∀ x∈[0,1], |lift u₀ x| ≤ M`; we expose it as an explicit hypothesis.  For the
conjugate capstone, `M := (conjugateMildData …).M` and this hypothesis is exactly
the accessor `|u₀ x| ≤ D.M` that is NOT exposed on `D` (see CARRIED note). -/
theorem conjugate_hmean0_of_datumBound {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀) {M : ℝ} (hM : 0 ≤ M)
    (hbd : ∀ x : intervalDomainPoint, |u₀ x| ≤ M) :
    |cosineCoeffs (intervalDomainLift u₀) 0| ≤ M := by
  have hcont : ContinuousOn (intervalDomainLift u₀) (Set.Icc (0:ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (Set.Icc (0:ℝ) 1).restrict (intervalDomainLift u₀) = u₀ := by
      funext ⟨y, hy⟩
      simp only [Set.restrict_apply, intervalDomainLift]
      split_ifs
      exact congr_arg u₀ (Subtype.ext rfl)
    rw [heq]; exact hu₀_cont
  have hbd' : ∀ x ∈ Set.Icc (0:ℝ) 1, |intervalDomainLift u₀ x| ≤ M := by
    intro x hx
    rw [intervalDomainLift]; simp only [hx, dif_pos]; exact hbd ⟨x, hx⟩
  exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_zero_abs_le_of_bound hM hcont hbd'

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms conjugate_hmean0_of_datumBound
#print axioms valueTerm_cont
#print axioms valueWin_bound
#print axioms fullKernel_jointCont
#print axioms fullKernel_le
#print axioms fullKernel_joint_measurable
#print axioms valueOp_src_jointCont
#print axioms valueLeg_boundary_contAt
#print axioms valueLeg_interior_contAt
#print axioms valueLeg_hG_cont
#print axioms logisticLeg_continuous_full
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegValueOpCont
