/-
  Joint positive-time continuity of the faithful interior time derivative.

  The proof first establishes the only nonsingular kernel fact not already
  exposed by the positive-time C2 files: away from zero lag, the literal
  Hessians of both the full and conjugate Neumann operators are jointly
  continuous in lag and space.  The conjugate statement uses a fixed
  positive half-step and the committed full-semigroup second-value series.
-/
import ShenWork.Paper2.IntervalConjugateMildTimeDerivativeClosed
import ShenWork.Paper2.IntervalConjugateMildChemDivJointContinuity
import ShenWork.Paper2.IntervalConjugateMildLogisticTimeDerivative
import ShenWork.Paper2.ChemMildC1eta

open MeasureTheory Filter Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (constExtend_eq_lift_on_Icc intervalDomainConstExtend intervalDomainLift
    intervalDomainPoint intervalMeasure semigroupOperator_constExtend_eq_lift)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalGradientDuhamelMap
  (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugatePicard (ConjugateMildSolutionData)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.IntervalDomainRegularityBootstrap
  (unitIntervalCosineHeatSecondValue)
open ShenWork.IntervalMildPicardThreshold
  (unitClip unitClip_continuous unitClip_of_mem)

/-- Away from zero lag, the literal Hessian of a fixed full-semigroup slice
is jointly continuous in lag and closed physical space. -/
theorem intervalFullSemigroupOperator_secondDeriv_jointContinuousOn_Ioi_Icc
    {h : ℝ → ℝ} (hh : Continuous h) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs h n| ≤ M) :
    ContinuousOn
      (fun q : ℝ × ℝ ↦ deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator q.1 h z) y) q.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hspec :=
    ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatSecondValue_continuousOn_Ioi_prod
      hM
  refine (hspec.mono (Set.prod_mono (fun _ hq ↦ hq) (fun _ _ ↦ Set.mem_univ _))).congr ?_
  intro q hq
  exact intervalFullSemigroupOperator_secondDeriv_eq_secondValue_Icc
    hq.1 hh hM hq.2

/-- Interior-space restriction of the closed full-semigroup Hessian theorem. -/
theorem intervalFullSemigroupOperator_secondDeriv_jointContinuousOn_Ioi_Ioo
    {h : ℝ → ℝ} (hh : Continuous h) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs h n| ≤ M) :
    ContinuousOn
      (fun q : ℝ × ℝ ↦ deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator q.1 h z) y) q.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) 1) :=
  (intervalFullSemigroupOperator_secondDeriv_jointContinuousOn_Ioi_Icc
    hh hM).mono (Set.prod_mono (fun _ hq ↦ hq) Set.Ioo_subset_Icc_self)

/-- Joint positive-lag continuity of the literal Hessian of a lifted subtype
datum.  The zero-extension is never treated as continuous: the semigroup is
first replaced by the continuous clipped extension, which agrees with it on
the whole support of the interval measure. -/
theorem intervalFullSemigroupOperator_lift_secondDeriv_jointContinuousOn_Ioi_Icc
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : Continuous u₀) :
    ContinuousOn
      (fun q : ℝ × ℝ ↦ deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator q.1
          (intervalDomainLift u₀) z) y) q.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  let f : ℝ → ℝ := fun y ↦ u₀ (unitClip y)
  have hf : Continuous f := hu₀.comp unitClip_continuous
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  let C : ℝ := max B 0
  have hC : 0 ≤ C := le_max_right B 0
  have hf_bound : ∀ y ∈ Set.Icc (0 : ℝ) 1, |f y| ≤ C := by
    intro y hy
    have hyB := hB y hy
    rw [Real.norm_eq_abs] at hyB
    exact hyB.trans (le_max_left B 0)
  have hcoeff : ∀ n, |cosineCoeffs f n| ≤ 2 * C :=
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      hf.continuousOn hC hf_bound
  have hbase :=
    intervalFullSemigroupOperator_secondDeriv_jointContinuousOn_Ioi_Icc
      hf hcoeff
  have hlift_eq : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u₀ y = f y := by
    intro y hy
    simp [f, intervalDomainLift, hy, unitClip_of_mem hy]
  have hsemigroup : ∀ r z,
      intervalFullSemigroupOperator r (intervalDomainLift u₀) z =
        intervalFullSemigroupOperator r f z := by
    intro r z
    exact intervalFullSemigroupOperator_congr_on_Icc hlift_eq z
  refine hbase.congr ?_
  intro q _hq
  have hspace :
      (fun z : ℝ ↦ intervalFullSemigroupOperator q.1
        (intervalDomainLift u₀) z) =
      (fun z : ℝ ↦ intervalFullSemigroupOperator q.1 f z) := by
    funext z
    exact hsemigroup q.1 z
  change deriv (fun y : ℝ ↦ deriv
      (fun z : ℝ ↦ intervalFullSemigroupOperator q.1
        (intervalDomainLift u₀) z) y) q.2 =
    deriv (fun y : ℝ ↦ deriv
      (fun z : ℝ ↦ intervalFullSemigroupOperator q.1 f z) y) q.2
  rw [hspace]

/-- An arbitrary positive full-semigroup step composed after a positive
conjugate step agrees with the summed conjugate step on a genuine
neighbourhood of every physical endpoint. -/
theorem intervalFullSemigroup_comp_conjugate_eventuallyEq_Icc_of_add
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {Q : ℝ → ℝ} (hQcont : Continuous Q)
    (hQint : Integrable Q (intervalMeasure 1)) {CQ : ℝ}
    (hQbound : ∀ y, |Q y| ≤ CQ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (fun z ↦ intervalFullSemigroupOperator a
        (fun w ↦ intervalConjugateKernelOperator b Q w) z) =ᶠ[nhds x]
      (fun z ↦ intervalConjugateKernelOperator (a + b) Q z) := by
  let B : ℝ → ℝ := fun z ↦ intervalConjugateKernelOperator b Q z
  let F : ℝ → ℝ := fun z ↦ intervalFullSemigroupOperator a B z
  let J : ℝ → ℝ := fun z ↦ intervalConjugateKernelOperator (a + b) Q z
  have hEqOn : Set.EqOn F J (Set.Icc (0 : ℝ) 1) := by
    intro z hz
    dsimp [F, J, B]
    exact intervalFullSemigroupOperator_comp_conjugateKernel
      ha hb hQcont hQint hQbound hz
  have hEqOpen : Set.EqOn F J (Set.Ioo (-1 : ℝ) 2) := by
    intro z hz
    by_cases hz0 : z < 0
    · have hnz : -z ∈ Set.Icc (0 : ℝ) 1 := by
        constructor <;> linarith [hz.1, hz.2]
      calc
        F z = F (-z) := by
          dsimp [F]
          exact (ShenWork.intervalFullSemigroupOperator_even_zero a B z).symm
        _ = J (-z) := hEqOn hnz
        _ = J z := by
          dsimp [J]
          exact
            ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator_even_zero
              (a + b) Q z
    · by_cases hz1 : z ≤ 1
      · exact hEqOn ⟨le_of_not_gt hz0, hz1⟩
      · have htwoz : 2 - z ∈ Set.Icc (0 : ℝ) 1 := by
          constructor <;> linarith [hz.1, hz.2]
        calc
          F z = F (2 - z) := by
            dsimp [F]
            exact (ShenWork.intervalFullSemigroupOperator_even_one a B z).symm
          _ = J (2 - z) := hEqOn htwoz
          _ = J z := by
            dsimp [J]
            exact
              ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator_even_one
                (a + b) Q z
  have hxOpen : x ∈ Set.Ioo (-1 : ℝ) 2 := by
    constructor <;> linarith [hx.1, hx.2]
  filter_upwards [isOpen_Ioo.mem_nhds hxOpen] with z hz
  simpa [F, J, B] using hEqOpen hz

/-- Away from zero lag, the literal Hessian of a fixed conjugate-kernel
slice is jointly continuous in lag and closed physical space. -/
theorem intervalConjugateKernelOperator_secondDeriv_jointContinuousOn_Ioi_Icc
    {Q : ℝ → ℝ} (hQcont : Continuous Q)
    (hQint : Integrable Q (intervalMeasure 1)) {CQ : ℝ}
    (hQbound : ∀ y, |Q y| ≤ CQ) :
    ContinuousOn
      (fun q : ℝ × ℝ ↦ deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalConjugateKernelOperator q.1 Q z) y) q.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  intro q hq
  rcases q with ⟨r, x⟩
  have hr : 0 < r := hq.1
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := hq.2
  let b : ℝ := r / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hbr : b < r := by dsimp [b]; linarith
  let B : ℝ → ℝ := fun z ↦ intervalConjugateKernelOperator b Q z
  have hBdiff : Differentiable ℝ B := fun z ↦
    (ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator_hasDerivAt
      hb hQint hQbound z).differentiableAt
  have hBcont : Continuous B := hBdiff.continuous
  obtain ⟨MB, hMB⟩ :=
    intervalConjugateKernelOperator_cosineCoeff_bounded hb hQcont
  let G : ℝ × ℝ → ℝ := fun w ↦
    unitIntervalCosineHeatSecondValue (w.1 - b) (cosineCoeffs B) w.2
  have hGAt : ContinuousAt G (r, x) := by
    have hspec :=
      ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatSecondValue_continuousOn_Ioi_prod
        hMB
    have hmem : (r - b, x) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.univ :=
      ⟨sub_pos.mpr hbr, Set.mem_univ x⟩
    have hspecAt := hspec.continuousAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem)
    have hmap : ContinuousAt (fun w : ℝ × ℝ ↦ (w.1 - b, w.2)) (r, x) := by
      fun_prop
    have hcomp := ContinuousAt.comp (x := (r, x)) hspecAt hmap
    simpa [G, B] using hcomp
  let S : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1
  have hagree : ∀ w ∈ S, b < w.1 →
      (fun w : ℝ × ℝ ↦ deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalConjugateKernelOperator w.1 Q z) y) w.2)
      w = G w := by
    intro w hw hbw
    have hlag : 0 < w.1 - b := sub_pos.mpr hbw
    have hev := intervalFullSemigroup_comp_conjugate_eventuallyEq_Icc_of_add
      hlag hb hQcont hQint hQbound hw.2
    calc
      deriv (fun y : ℝ ↦ deriv
          (fun z : ℝ ↦ intervalConjugateKernelOperator w.1 Q z) y) w.2 =
          deriv (fun y : ℝ ↦ deriv
            (fun z : ℝ ↦ intervalFullSemigroupOperator (w.1 - b) B z) y) w.2 := by
        have heqLag : w.1 - b + b = w.1 := by ring
        simpa [B, heqLag] using hev.deriv.deriv_eq.symm
      _ = G w := intervalFullSemigroupOperator_secondDeriv_eq_secondValue_Icc
        hlag hBcont hMB hw.2
  have hb_event : ∀ᶠ w in nhds (r, x), b < w.1 := by
    filter_upwards [prod_mem_nhds (Ioi_mem_nhds hbr) univ_mem] with w hw
    exact hw.1
  have heq :
      (fun w : ℝ × ℝ ↦ deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalConjugateKernelOperator w.1 Q z) y) w.2)
        =ᶠ[nhdsWithin (r, x) S] G := by
    filter_upwards [self_mem_nhdsWithin,
      hb_event.filter_mono nhdsWithin_le_nhds] with w hwS hbw
    exact hagree w hwS hbw
  exact (hGAt.continuousWithinAt.congr_of_eventuallyEq heq
    (hagree (r, x) hq hbr))

/-- Interior-space restriction of the closed conjugate Hessian theorem. -/
theorem intervalConjugateKernelOperator_secondDeriv_jointContinuousOn_Ioi_Ioo
    {Q : ℝ → ℝ} (hQcont : Continuous Q)
    (hQint : Integrable Q (intervalMeasure 1)) {CQ : ℝ}
    (hQbound : ∀ y, |Q y| ≤ CQ) :
    ContinuousOn
      (fun q : ℝ × ℝ ↦ deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalConjugateKernelOperator q.1 Q z) y) q.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) 1) :=
  (intervalConjugateKernelOperator_secondDeriv_jointContinuousOn_Ioi_Icc
    hQcont hQint hQbound).mono
      (Set.prod_mono (fun _ hq ↦ hq) Set.Ioo_subset_Icc_self)

/-! ## Fixed old histories -/

/-- A full-semigroup Hessian history cut off strictly before the target time
is jointly continuous in target time and interior space.  The positive lag
gap supplies one constant dominator; no time regularity of the source is
used. -/
theorem intervalFullDuhamel_fixedHistory_secondDeriv_continuousWithinAt_joint
    {a t x CQ : ℝ} (ha0 : 0 ≤ a) (hat : a < t)
    {F : ℝ → ℝ → ℝ}
    (hF_meas : Measurable (Function.uncurry F))
    (hF_cont : ∀ s, Continuous (F s))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CQ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousWithinAt
      (fun q : ℝ × ℝ ↦ ∫ s in (0 : ℝ)..a, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator (q.1 - s) (F s) z) y) q.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1)
      (t, x) := by
  let d : ℝ := (t - a) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  let c : ℝ := a + d
  have hct : c < t := by dsimp [c, d]; linarith
  let Cmix : ℝ := 5 * Real.sqrt 2 / 2
  let B : ℝ := Cmix * d ^ (-(1 : ℝ)) * CQ
  let S : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1
  have hnear0 : Set.Ioi c ×ˢ Set.univ ∈ nhds (t, x) :=
    prod_mem_nhds (Ioi_mem_nhds hct) univ_mem
  have hnear : Set.Ioi c ×ˢ Set.univ ∈ nhdsWithin (t, x) S :=
    Filter.mem_inf_of_left hnear0
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (s := S)
    (bound := fun _ : ℝ ↦ B) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [hnear, self_mem_nhdsWithin] with q hq hqS
    have hqc : c < q.1 := hq.1
    have hqa : a < q.1 := by
      dsimp [c] at hqc
      linarith [hd]
    have hq0 : 0 < q.1 := lt_of_le_of_lt ha0 hqa
    have hF_ae : AEStronglyMeasurable (Function.uncurry F)
        ((volume.restrict (Set.uIoc (0 : ℝ) q.1)).prod (intervalMeasure 1)) :=
      hF_meas.aestronglyMeasurable
    have hm :=
      intervalFullSemigroupOperator_s_dependent_secondDeriv_aestronglyMeasurable_x₀
        hq0 hF_ae hF_int hF_bound q.2
    have hsub : Set.uIoc (0 : ℝ) a ⊆ Set.uIoc (0 : ℝ) q.1 := by
      rw [Set.uIoc_of_le ha0, Set.uIoc_of_le hq0.le]
      exact Set.Ioc_subset_Ioc le_rfl hqa.le
    exact hm.mono_measure (Measure.restrict_mono hsub le_rfl)
  · filter_upwards [hnear, self_mem_nhdsWithin] with q hq hqS
    filter_upwards with s hs
    rw [Set.uIoc_of_le ha0] at hs
    have hqc : c < q.1 := hq.1
    dsimp [c] at hqc
    have hlag : 0 < q.1 - s := by
      linarith [hd, hs.2, hqc]
    have hdlag : d ≤ q.1 - s := by
      linarith [hs.2, hqc]
    have hp : (q.1 - s) ^ (-(1 : ℝ)) ≤ d ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hd hdlag (by norm_num)
    have hraw :=
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_secondDeriv_Linfty_pointwise_inv_t
        hlag (hF_int s).aestronglyMeasurable (hF_bound s) q.2
    rw [Real.norm_eq_abs]
    exact hraw.trans (by
      dsimp [B, Cmix]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (by positivity))
        ((abs_nonneg (F s 0)).trans (hF_bound s 0)))
  · filter_upwards with s hs
    rw [Set.uIoc_of_le ha0] at hs
    have hlag : 0 < t - s := by linarith [hs.2, hat]
    have hbase :=
      intervalFullSemigroupOperator_secondDeriv_jointContinuousOn_Ioi_Icc
        (hF_cont s)
        (ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
          (hF_cont s).continuousOn
          ((abs_nonneg (F s 0)).trans (hF_bound s 0))
          (fun y _hy ↦ hF_bound s y))
    let L : Set (ℝ × ℝ) := Set.Ioi s ×ˢ Set.Icc (0 : ℝ) 1
    have hcomp : ContinuousOn
        (fun q : ℝ × ℝ ↦ deriv (fun y : ℝ ↦ deriv
          (fun z : ℝ ↦ intervalFullSemigroupOperator (q.1 - s) (F s) z) y) q.2)
        L := by
      apply hbase.comp
        (by fun_prop : Continuous (fun q : ℝ × ℝ ↦ (q.1 - s, q.2))).continuousOn
      intro q hq
      have hmapmem : (q.1 - s, q.2) ∈
          Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1 := by
        change 0 < q.1 - s ∧ q.2 ∈ Set.Icc (0 : ℝ) 1
        exact ⟨sub_pos.mpr hq.1, hq.2⟩
      exact hmapmem
    have hst : s < t := hs.2.trans_lt hat
    have hmemL : (t, x) ∈ L := by
      change s < t ∧ x ∈ Set.Icc (0 : ℝ) 1
      exact ⟨hst, hx⟩
    have hopen : Set.Ioi s ×ˢ Set.univ ∈ nhds (t, x) :=
      prod_mem_nhds (Ioi_mem_nhds hst) univ_mem
    have hlocal : L ∈ nhdsWithin (t, x) S := by
      have hinter := Filter.inter_mem (Filter.mem_inf_of_left hopen)
        (self_mem_nhdsWithin (a := (t, x)) (s := S))
      refine Filter.mem_of_superset hinter ?_
      intro q hq
      exact ⟨hq.1.1, hq.2.2⟩
    exact (hcomp.continuousWithinAt hmemL).mono_of_mem_nhdsWithin hlocal

/-- Interior-point ordinary-continuity corollary of the closed-space fixed
history theorem. -/
theorem intervalFullDuhamel_fixedHistory_secondDeriv_continuousAt_joint
    {a t x CQ : ℝ} (ha0 : 0 ≤ a) (hat : a < t)
    {F : ℝ → ℝ → ℝ}
    (hF_meas : Measurable (Function.uncurry F))
    (hF_cont : ∀ s, Continuous (F s))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CQ)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousAt
      (fun q : ℝ × ℝ ↦ ∫ s in (0 : ℝ)..a, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator (q.1 - s) (F s) z) y) q.2)
      (t, x) := by
  have hwithin := intervalFullDuhamel_fixedHistory_secondDeriv_continuousWithinAt_joint
    ha0 hat hF_meas hF_cont hF_int hF_bound (Set.Ioo_subset_Icc_self hx)
  have hspace : Set.Icc (0 : ℝ) 1 ∈ nhds x :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hx) Set.Ioo_subset_Icc_self
  exact hwithin.continuousAt
    (prod_mem_nhds (Ioi_mem_nhds (lt_of_le_of_lt ha0 hat)) hspace)

/-- A conjugate-kernel Hessian history cut off strictly before the target
time is jointly continuous in target time and interior space. -/
theorem intervalConjugateDuhamel_fixedHistory_secondDeriv_continuousWithinAt_joint
    {a t x CQ : ℝ} (ha0 : 0 ≤ a) (hat : a < t)
    {Q : ℝ → ℝ → ℝ}
    (hQ_meas : Measurable (Function.uncurry Q))
    (hQ_cont : ∀ s, Continuous (Q s))
    (hQ_int : ∀ s, Integrable (Q s) (intervalMeasure 1))
    (hQ_bound : ∀ s y, |Q s y| ≤ CQ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousWithinAt
      (fun q : ℝ × ℝ ↦ ∫ s in (0 : ℝ)..a, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalConjugateKernelOperator (q.1 - s) (Q s) z) y) q.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1)
      (t, x) := by
  let d : ℝ := (t - a) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  let c : ℝ := a + d
  have hct : c < t := by dsimp [c, d]; linarith
  let B : ℝ :=
    (5 * Real.sqrt 2 / 2) * (d / 2) ^ (-(1 : ℝ)) *
      (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (d / 2) ^ (-(1 / 2) : ℝ) * CQ)
  let S : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1
  have hnear0 : Set.Ioi c ×ˢ Set.univ ∈ nhds (t, x) :=
    prod_mem_nhds (Ioi_mem_nhds hct) univ_mem
  have hnear : Set.Ioi c ×ˢ Set.univ ∈ nhdsWithin (t, x) S :=
    Filter.mem_inf_of_left hnear0
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (s := S)
    (bound := fun _ : ℝ ↦ B) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [hnear, self_mem_nhdsWithin] with q hq hqS
    have hqc : c < q.1 := hq.1
    have hqa : a < q.1 := by
      dsimp [c] at hqc
      linarith [hd]
    have hq0 : 0 < q.1 := lt_of_le_of_lt ha0 hqa
    have hsecond : ∀ s ∈ Set.Ioo (0 : ℝ) q.1,
        DifferentiableAt ℝ
          (fun z ↦ deriv
            (fun w ↦ intervalConjugateKernelOperator (q.1 - s) (Q s) w) z) q.2 := by
      intro s hs
      exact intervalConjugateKernelOperator_hasDerivAt_deriv_of_split_Icc
        (sub_pos.mpr hs.2) (hQ_cont s) (hQ_int s) (hQ_bound s) hqS.2
    have hm :=
      intervalConjugateKernelOperator_s_dependent_secondDeriv_aestronglyMeasurable_x
        hq0 hQ_meas hQ_int hQ_bound hsecond
    have hsub : Set.uIoc (0 : ℝ) a ⊆ Set.uIoc (0 : ℝ) q.1 := by
      rw [Set.uIoc_of_le ha0, Set.uIoc_of_le hq0.le]
      exact Set.Ioc_subset_Ioc le_rfl hqa.le
    exact hm.mono_measure (Measure.restrict_mono hsub le_rfl)
  · filter_upwards [hnear, self_mem_nhdsWithin] with q hq hqS
    filter_upwards with s hs
    rw [Set.uIoc_of_le ha0] at hs
    have hqc : c < q.1 := hq.1
    dsimp [c] at hqc
    have hlag : 0 < q.1 - s := by linarith [hd, hs.2, hqc]
    have hdlag : d ≤ q.1 - s := by linarith [hs.2, hqc]
    have hraw := intervalConjugateKernelOperator_timeDeriv_abs_le_of_lower
      hd hdlag (hQ_cont s) (hQ_int s) (hQ_bound s)
        hqS.2
    rw [(intervalConjugateKernelOperator_hasDerivAt_time_secondDeriv_Icc
      hlag (hQ_cont s) (hQ_int s) (hQ_bound s)
        hqS.2).deriv] at hraw
    simpa [B, Real.norm_eq_abs] using hraw
  · filter_upwards with s hs
    rw [Set.uIoc_of_le ha0] at hs
    have hlag : 0 < t - s := by linarith [hs.2, hat]
    have hbase :=
      intervalConjugateKernelOperator_secondDeriv_jointContinuousOn_Ioi_Icc
        (hQ_cont s) (hQ_int s) (hQ_bound s)
    let L : Set (ℝ × ℝ) := Set.Ioi s ×ˢ Set.Icc (0 : ℝ) 1
    have hcomp : ContinuousOn
        (fun q : ℝ × ℝ ↦ deriv (fun y : ℝ ↦ deriv
          (fun z : ℝ ↦ intervalConjugateKernelOperator (q.1 - s) (Q s) z) y) q.2)
        L := by
      apply hbase.comp
        (by fun_prop : Continuous (fun q : ℝ × ℝ ↦ (q.1 - s, q.2))).continuousOn
      intro q hq
      have hmapmem : (q.1 - s, q.2) ∈
          Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) 1 := by
        change 0 < q.1 - s ∧ q.2 ∈ Set.Icc (0 : ℝ) 1
        exact ⟨sub_pos.mpr hq.1, hq.2⟩
      exact hmapmem
    have hst : s < t := hs.2.trans_lt hat
    have hmemL : (t, x) ∈ L := by
      change s < t ∧ x ∈ Set.Icc (0 : ℝ) 1
      exact ⟨hst, hx⟩
    have hopen : Set.Ioi s ×ˢ Set.univ ∈ nhds (t, x) :=
      prod_mem_nhds (Ioi_mem_nhds hst) univ_mem
    have hlocal : L ∈ nhdsWithin (t, x) S := by
      have hinter := Filter.inter_mem (Filter.mem_inf_of_left hopen)
        (self_mem_nhdsWithin (a := (t, x)) (s := S))
      refine Filter.mem_of_superset hinter ?_
      intro q hq
      exact ⟨hq.1.1, hq.2.2⟩
    exact (hcomp.continuousWithinAt hmemL).mono_of_mem_nhdsWithin hlocal

/-- Interior-point ordinary-continuity corollary of the closed conjugate
fixed-history theorem. -/
theorem intervalConjugateDuhamel_fixedHistory_secondDeriv_continuousAt_joint
    {a t x CQ : ℝ} (ha0 : 0 ≤ a) (hat : a < t)
    {Q : ℝ → ℝ → ℝ}
    (hQ_meas : Measurable (Function.uncurry Q))
    (hQ_cont : ∀ s, Continuous (Q s))
    (hQ_int : ∀ s, Integrable (Q s) (intervalMeasure 1))
    (hQ_bound : ∀ s y, |Q s y| ≤ CQ)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousAt
      (fun q : ℝ × ℝ ↦ ∫ s in (0 : ℝ)..a, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalConjugateKernelOperator (q.1 - s) (Q s) z) y) q.2)
      (t, x) := by
  have hwithin :=
    intervalConjugateDuhamel_fixedHistory_secondDeriv_continuousWithinAt_joint
      ha0 hat hQ_meas hQ_cont hQ_int hQ_bound (Set.Ioo_subset_Icc_self hx)
  have hspace : Set.Icc (0 : ℝ) 1 ∈ nhds x :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hx) Set.Ioo_subset_Icc_self
  exact hwithin.continuousAt
    (prod_mem_nhds (Ioi_mem_nhds (lt_of_le_of_lt ha0 hat)) hspace)

/-! ## Uniform short tails -/

/-- Evaluation of the cancellative Hessian time weight on an arbitrary
terminal subinterval. -/
theorem integral_sub_rpow_hessian_from
    {a t theta : ℝ} (hat : a ≤ t) (htheta0 : 0 < theta) :
    (∫ s in a..t, (t - s) ^ (-1 + theta / 2 : ℝ)) =
      (t - a) ^ (theta / 2 : ℝ) / (theta / 2) := by
  have hshift := intervalIntegral.integral_comp_add_right
    (f := fun s : ℝ ↦ (t - s) ^ (-1 + theta / 2 : ℝ))
    (a := (0 : ℝ)) (b := t - a) a
  have heq : (fun r : ℝ ↦ (t - (r + a)) ^ (-1 + theta / 2 : ℝ)) =
      fun r : ℝ ↦ ((t - a) - r) ^ (-1 + theta / 2 : ℝ) := by
    funext r
    congr 1
    ring
  have hbase :=
    ShenWork.IntervalNeumannFullKernel.integral_sub_rpow_hessian
      (t := t - a) (sub_nonneg.mpr hat) htheta0
  rw [heq] at hshift
  simpa using hshift.symm.trans hbase

/-- Uniform-in-space bound for a short terminal full-Hessian history.  Only
the interior spatial Holder modulus of the source is used. -/
theorem intervalFullDuhamel_secondDeriv_tail_abs_le
    {a t theta CQ HQ : ℝ} (ha0 : 0 ≤ a) (hat : a ≤ t)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) (hHQ : 0 ≤ HQ)
    {F : ℝ → ℝ → ℝ}
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CQ)
    (hF_holder : ∀ s, a < s → s < t →
      ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∀ q ∈ Set.Ioo (0 : ℝ) 1,
        |F s p - F s q| ≤ HQ * |p - q| ^ theta)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable
      (fun s ↦ deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x)
      volume a t →
    |∫ s in a..t, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x| ≤
      (ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta * HQ) *
        ((t - a) ^ (theta / 2 : ℝ) / (theta / 2)) := by
  intro h2_int
  rcases eq_or_lt_of_le hat with rfl | hatlt
  · have hhalf_ne : (theta / 2 : ℝ) ≠ 0 := by linarith
    simp [Real.zero_rpow hhalf_ne]
  let Ctheta : ℝ :=
    ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta * HQ
  let g : ℝ → ℝ := fun s ↦
    Ctheta * (t - s) ^ (-1 + theta / 2 : ℝ)
  have ht0 : 0 < t := lt_of_le_of_lt ha0 hatlt
  have hg_int : IntervalIntegrable g volume a t := by
    have hbase :=
      (ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := t) htheta0).const_mul Ctheta
    exact hbase.mono_set (by
      rw [Set.uIcc_of_le hat, Set.uIcc_of_le ht0.le]
      exact Set.Icc_subset_Icc ha0 le_rfl)
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  have hpt : ∀ᵐ s : ℝ ∂volume, s ∈ Set.Ioc a t →
      ‖deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x‖ ≤ g s := by
    filter_upwards [hne] with s hst_ne hs
    have hst : s < t := lt_of_le_of_ne hs.2 hst_ne
    have hlag : 0 < t - s := sub_pos.mpr hst
    rw [Real.norm_eq_abs]
    dsimp [g, Ctheta]
    have hraw := intervalFullSemigroupOperator_secondDeriv_abs_le_of_interior_holder_Icc
      hlag htheta0 htheta1 (hF_int s) (hF_bound s) hHQ
        (hF_holder s hs.1 hst) hx
    convert hraw using 1 <;> ring
  have hne_a : ∀ᵐ s : ℝ ∂volume, s ≠ a := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  have hmono_ae :
      (fun s ↦ |deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x|)
      ≤ᵐ[volume.restrict (Set.Icc a t)] g := by
    show ∀ᵐ s : ℝ ∂(volume.restrict (Set.Icc a t)),
      |deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x| ≤ g s
    refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
    filter_upwards [hpt, hne_a] with s hpt_s hsa hs
    have hsIoc : s ∈ Set.Ioc a t :=
      ⟨lt_of_le_of_ne hs.1 (Ne.symm hsa), hs.2⟩
    simpa [Real.norm_eq_abs] using hpt_s hsIoc
  have habs := intervalIntegral.abs_integral_le_integral_abs
    (μ := volume)
    (f := fun s ↦ deriv (fun y : ℝ ↦ deriv
      (fun z : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x)
    hat
  have hmono := intervalIntegral.integral_mono_ae_restrict
    hat h2_int.abs hg_int hmono_ae
  calc
    |∫ s in a..t, deriv (fun y : ℝ ↦ deriv
          (fun z : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x|
        ≤ ∫ s in a..t, |deriv (fun y : ℝ ↦ deriv
          (fun z : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x| := habs
    _ ≤ ∫ s in a..t, g s := hmono
    _ = Ctheta * ((t - a) ^ (theta / 2 : ℝ) / (theta / 2)) := by
      rw [show (fun s : ℝ ↦ g s) =
          fun s : ℝ ↦ Ctheta * (t - s) ^ (-1 + theta / 2 : ℝ) by rfl,
        intervalIntegral.integral_const_mul,
        integral_sub_rpow_hessian_from hat htheta0]
    _ = (ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta * HQ) *
          ((t - a) ^ (theta / 2 : ℝ) / (theta / 2)) := by rfl

/-- Integrability of a nonsingular full-Hessian history ending before the
target time. -/
theorem intervalFullDuhamel_fixedHistory_secondDeriv_intervalIntegrable
    {a t CQ : ℝ} (ha0 : 0 ≤ a) (hat : a < t)
    {F : ℝ → ℝ → ℝ}
    (hF_meas : Measurable (Function.uncurry F))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CQ) (x : ℝ) :
    IntervalIntegrable
      (fun s : ℝ ↦ deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x)
      volume 0 a := by
  have ht0 : 0 < t := lt_of_le_of_lt ha0 hat
  have hF_ae : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)) :=
    hF_meas.aestronglyMeasurable
  have hmeas_full :=
    intervalFullSemigroupOperator_s_dependent_secondDeriv_aestronglyMeasurable_x₀
      ht0 hF_ae hF_int hF_bound x
  have hsub : Set.uIoc (0 : ℝ) a ⊆ Set.uIoc (0 : ℝ) t := by
    rw [Set.uIoc_of_le ha0, Set.uIoc_of_le ht0.le]
    exact Set.Ioc_subset_Ioc le_rfl hat.le
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ ↦ deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x)
      (volume.restrict (Set.uIoc (0 : ℝ) a)) :=
    hmeas_full.mono_measure (Measure.restrict_mono hsub le_rfl)
  let Cmix : ℝ := 5 * Real.sqrt 2 / 2
  let B : ℝ := Cmix * (t - a) ^ (-(1 : ℝ)) * CQ
  refine IntervalIntegrable.mono_fun'
    (f := fun s : ℝ ↦ deriv (fun y : ℝ ↦ deriv
      (fun z : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x)
    (g := fun _ : ℝ ↦ B) intervalIntegrable_const hmeas ?_
  refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
  filter_upwards with s hs
  rw [Set.uIoc_of_le ha0] at hs
  have hlag : 0 < t - s := by linarith [hs.2, hat]
  have hbase : t - a ≤ t - s := by linarith [hs.2]
  have hp : (t - s) ^ (-(1 : ℝ)) ≤ (t - a) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hat) hbase (by norm_num)
  have hraw :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_secondDeriv_Linfty_pointwise_inv_t
      hlag (hF_int s).aestronglyMeasurable (hF_bound s) x
  rw [Real.norm_eq_abs]
  exact hraw.trans (by
    dsimp [B, Cmix]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (by positivity))
      ((abs_nonneg (F s 0)).trans (hF_bound s 0)))

/-- Integrability of a terminal full-Hessian history under the same
cancellative Holder estimate used by the tail bound. -/
theorem intervalFullDuhamel_secondDeriv_tail_intervalIntegrable
    {a t theta CQ HQ : ℝ} (ha0 : 0 ≤ a) (hat : a < t)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) (hHQ : 0 ≤ HQ)
    {F : ℝ → ℝ → ℝ}
    (hF_meas : Measurable (Function.uncurry F))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CQ)
    (hF_holder : ∀ s, a < s → s < t →
      ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∀ q ∈ Set.Ioo (0 : ℝ) 1,
        |F s p - F s q| ≤ HQ * |p - q| ^ theta)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable
      (fun s : ℝ ↦ deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x)
      volume a t := by
  have ht0 : 0 < t := lt_of_le_of_lt ha0 hat
  have hF_ae : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)) :=
    hF_meas.aestronglyMeasurable
  have hmeas_full :=
    intervalFullSemigroupOperator_s_dependent_secondDeriv_aestronglyMeasurable_x₀
      ht0 hF_ae hF_int hF_bound x
  have hsub : Set.uIoc a t ⊆ Set.uIoc (0 : ℝ) t := by
    rw [Set.uIoc_of_le hat.le, Set.uIoc_of_le ht0.le]
    exact Set.Ioc_subset_Ioc ha0 le_rfl
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ ↦ deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x)
      (volume.restrict (Set.uIoc a t)) :=
    hmeas_full.mono_measure (Measure.restrict_mono hsub le_rfl)
  let Ctheta : ℝ :=
    ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta * HQ
  let g : ℝ → ℝ := fun s ↦ Ctheta * (t - s) ^ (-1 + theta / 2 : ℝ)
  have hg_int : IntervalIntegrable g volume a t := by
    have hbase :=
      (ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := t) htheta0).const_mul Ctheta
    exact hbase.mono_set (by
      rw [Set.uIcc_of_le hat.le, Set.uIcc_of_le ht0.le]
      exact Set.Icc_subset_Icc ha0 le_rfl)
  refine IntervalIntegrable.mono_fun'
    (f := fun s : ℝ ↦ deriv (fun y : ℝ ↦ deriv
      (fun z : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x)
    (g := g) hg_int hmeas ?_
  refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  filter_upwards [hne] with s hst_ne hs
  rw [Set.uIoc_of_le hat.le] at hs
  have hst : s < t := lt_of_le_of_ne hs.2 hst_ne
  have hlag : 0 < t - s := sub_pos.mpr hst
  rw [Real.norm_eq_abs]
  dsimp [g, Ctheta]
  have hraw := intervalFullSemigroupOperator_secondDeriv_abs_le_of_interior_holder_Icc
    hlag htheta0 htheta1 (hF_int s) (hF_bound s) hHQ
      (hF_holder s hs.1 hst) hx
  convert hraw using 1 <;> ring

/-- Integrability on the whole Duhamel interval, obtained by joining the
nonsingular old history and the cancellative terminal history. -/
theorem intervalFullDuhamel_secondDeriv_intervalIntegrable_of_cutoff_holder
    {a t theta CQ HQ : ℝ} (ha0 : 0 ≤ a) (hat : a < t)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) (hHQ : 0 ≤ HQ)
    {F : ℝ → ℝ → ℝ}
    (hF_meas : Measurable (Function.uncurry F))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CQ)
    (hF_holder : ∀ s, a < s → s < t →
      ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∀ q ∈ Set.Ioo (0 : ℝ) 1,
        |F s p - F s q| ≤ HQ * |p - q| ^ theta)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable
      (fun s : ℝ ↦ deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) z) y) x)
      volume 0 t :=
  (intervalFullDuhamel_fixedHistory_secondDeriv_intervalIntegrable
      ha0 hat hF_meas hF_int hF_bound x).trans
    (intervalFullDuhamel_secondDeriv_tail_intervalIntegrable
      ha0 hat htheta0 htheta1 hHQ hF_meas hF_int hF_bound hF_holder hx)

/-- The integrated cancellative power law can be made uniformly small by
making the terminal interval short. -/
theorem exists_delta_weighted_hessian_tail_small
    {theta C eps : ℝ} (htheta0 : 0 < theta) (hC : 0 ≤ C)
    (heps : 0 < eps) :
    ∃ delta > 0, ∀ h, 0 < h → h < delta →
      C * (h ^ (theta / 2 : ℝ) / (theta / 2)) < eps := by
  let phi : ℝ → ℝ := fun h ↦
    C * (h ^ (theta / 2 : ℝ) / (theta / 2))
  have hp : 0 < theta / 2 := by linarith
  have hphi : ContinuousAt phi 0 := by
    dsimp [phi]
    exact continuousAt_const.mul
      ((continuousAt_id.rpow_const (Or.inr hp.le)).div_const (theta / 2))
  have hphi0 : phi 0 = 0 := by
    dsimp [phi]
    rw [Real.zero_rpow hp.ne']
    ring
  rw [Metric.continuousAt_iff] at hphi
  obtain ⟨delta, hdelta, hsmall⟩ := hphi eps heps
  refine ⟨delta, hdelta, ?_⟩
  intro h hh hhd
  have hdist : dist h (0 : ℝ) < delta := by
    simpa [Real.dist_eq, abs_of_pos hh] using hhd
  have hout := hsmall hdist
  have hphi_nonneg : 0 ≤ phi h := by
    dsimp [phi]
    exact mul_nonneg hC
      (div_nonneg (Real.rpow_nonneg hh.le _) hp.le)
  simpa [hphi0, Real.dist_eq, abs_of_nonneg hphi_nonneg] using hout

/-! ## Joint continuity of a full Duhamel Hessian -/

/-- A bounded full-semigroup source whose slices have a common Holder modulus
on every positive-time strip has a jointly continuous integrated Hessian on
the strict-positive-time closed-space slab.  The proof uses a fixed old
history and a locally uniform cancellative short tail. -/
theorem intervalFullDuhamel_secondDeriv_jointContinuousOn_of_positiveStripHolder
    {T CQ : ℝ} (hT : 0 < T) {F : ℝ → ℝ → ℝ}
    (hF_meas : Measurable (Function.uncurry F))
    (hF_cont : ∀ s, Continuous (F s))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CQ)
    (hF_holder : ∀ tau, 0 < tau →
      ∃ theta HQ : ℝ, 0 < theta ∧ theta < 1 ∧ 0 ≤ HQ ∧
        ∀ s, tau ≤ s → s ≤ T →
          ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∀ q ∈ Set.Ioo (0 : ℝ) 1,
            |F s p - F s q| ≤ HQ * |p - q| ^ theta) :
    ContinuousOn
      (fun q : ℝ × ℝ ↦ ∫ s in (0 : ℝ)..q.1, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator (q.1 - s) (F s) z) y) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  intro q hq
  rcases q with ⟨t, x⟩
  have ht : 0 < t := hq.1.1
  have htT : t < T := hq.1.2
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := hq.2
  let tau : ℝ := t / 4
  have htau : 0 < tau := by dsimp [tau]; positivity
  obtain ⟨theta, HQ, htheta0, htheta1, hHQ, hholder⟩ :=
    hF_holder tau htau
  let Ctail : ℝ :=
    ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta * HQ
  have hCtail : 0 ≤ Ctail := by
    dsimp [Ctail]
    exact mul_nonneg
      (ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta) hHQ
  rw [Metric.continuousWithinAt_iff]
  intro eps heps
  have heps3 : 0 < eps / 3 := by linarith
  obtain ⟨deltaTail, hdeltaTail, htailSmall⟩ :=
    exists_delta_weighted_hessian_tail_small htheta0 hCtail heps3
  let ell : ℝ := min (t / 4) (deltaTail / 4)
  have hell : 0 < ell := by
    dsimp [ell]
    exact lt_min (by positivity) (by positivity)
  have hell_t : ell ≤ t / 4 := min_le_left _ _
  have hell_delta : ell ≤ deltaTail / 4 := min_le_right _ _
  let a : ℝ := t - ell
  have ha0 : 0 ≤ a := by
    dsimp [a]
    linarith [hell_t, ht]
  have hat : a < t := by dsimp [a]; linarith
  have htau_a : tau ≤ a := by
    dsimp [tau, a]
    linarith [hell_t, ht]
  have hholder_t : ∀ s, a < s → s < t →
      ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∀ z ∈ Set.Ioo (0 : ℝ) 1,
        |F s p - F s z| ≤ HQ * |p - z| ^ theta := by
    intro s has hst p hp z hz
    exact hholder s (htau_a.trans (le_of_lt has))
      (le_of_lt (hst.trans htT)) p hp z hz
  have hOldCont :=
    intervalFullDuhamel_fixedHistory_secondDeriv_continuousWithinAt_joint
      ha0 hat hF_meas hF_cont hF_int hF_bound hx
  let S : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1
  have hOldContS : ContinuousWithinAt
      (fun q : ℝ × ℝ ↦ ∫ s in (0 : ℝ)..a, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator (q.1 - s) (F s) z) y) q.2)
      S (t, x) := by
    exact hOldCont.mono (Set.prod_mono Set.Ioo_subset_Ioi_self (fun _ hz ↦ hz))
  rw [Metric.continuousWithinAt_iff] at hOldContS
  obtain ⟨deltaOld, hdeltaOld, hOldSmall⟩ := hOldContS (eps / 3) heps3
  refine ⟨min deltaOld ell, lt_min hdeltaOld hell, ?_⟩
  intro z hzS hzdist
  have hzdist_old : dist z (t, x) < deltaOld :=
    hzdist.trans_le (min_le_left _ _)
  have hzdist_ell : dist z (t, x) < ell :=
    hzdist.trans_le (min_le_right _ _)
  have hztime_dist : dist z.1 t < ell := by
    calc
      dist z.1 t ≤ dist z (t, x) := by
        rw [Prod.dist_eq]
        exact le_max_left _ _
      _ < ell := hzdist_ell
  rw [Real.dist_eq] at hztime_dist
  have hztime_abs := abs_lt.mp hztime_dist
  have haz : a < z.1 := by
    dsimp [a]
    linarith
  have hzlen_pos : 0 < z.1 - a := sub_pos.mpr haz
  have hzlen_delta : z.1 - a < deltaTail := by
    dsimp [a]
    have hell2 : 2 * ell ≤ deltaTail / 2 := by linarith [hell_delta]
    linarith [hztime_abs.2, hdeltaTail]
  have htlen_pos : 0 < t - a := sub_pos.mpr hat
  have htlen_delta : t - a < deltaTail := by
    dsimp [a]
    linarith [hell_delta, hdeltaTail]
  have hholder_z : ∀ s, a < s → s < z.1 →
      ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∀ w ∈ Set.Ioo (0 : ℝ) 1,
        |F s p - F s w| ≤ HQ * |p - w| ^ theta := by
    intro s has hsz p hp w hw
    exact hholder s (htau_a.trans (le_of_lt has))
      (le_of_lt (hsz.trans hzS.1.2)) p hp w hw
  have hOldInt_z :=
    intervalFullDuhamel_fixedHistory_secondDeriv_intervalIntegrable
      ha0 haz hF_meas hF_int hF_bound z.2
  have hTailInt_z :=
    intervalFullDuhamel_secondDeriv_tail_intervalIntegrable
      ha0 haz htheta0 htheta1 hHQ hF_meas hF_int hF_bound hholder_z hzS.2
  have hOldInt_t :=
    intervalFullDuhamel_fixedHistory_secondDeriv_intervalIntegrable
      ha0 hat hF_meas hF_int hF_bound x
  have hTailInt_t :=
    intervalFullDuhamel_secondDeriv_tail_intervalIntegrable
      ha0 hat htheta0 htheta1 hHQ hF_meas hF_int hF_bound hholder_t hx
  have hTail_z := intervalFullDuhamel_secondDeriv_tail_abs_le
    ha0 haz.le htheta0 htheta1 hHQ hF_int hF_bound hholder_z hzS.2 hTailInt_z
  have hTail_t := intervalFullDuhamel_secondDeriv_tail_abs_le
    ha0 hat.le htheta0 htheta1 hHQ hF_int hF_bound hholder_t hx hTailInt_t
  have hTail_z_small :
      |∫ s in a..z.1, deriv (fun y : ℝ ↦ deriv
        (fun w : ℝ ↦ intervalFullSemigroupOperator (z.1 - s) (F s) w) y) z.2| <
        eps / 3 :=
    hTail_z.trans_lt (by
      simpa [Ctail] using htailSmall (z.1 - a) hzlen_pos hzlen_delta)
  have hTail_t_small :
      |∫ s in a..t, deriv (fun y : ℝ ↦ deriv
        (fun w : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) w) y) x| <
        eps / 3 :=
    hTail_t.trans_lt (by
      simpa [Ctail] using htailSmall (t - a) htlen_pos htlen_delta)
  have hOld_small := hOldSmall hzS hzdist_old
  have hSplit_z :
      (∫ s in (0 : ℝ)..a, deriv (fun y : ℝ ↦ deriv
          (fun w : ℝ ↦ intervalFullSemigroupOperator (z.1 - s) (F s) w) y) z.2) +
        ∫ s in a..z.1, deriv (fun y : ℝ ↦ deriv
          (fun w : ℝ ↦ intervalFullSemigroupOperator (z.1 - s) (F s) w) y) z.2 =
        ∫ s in (0 : ℝ)..z.1, deriv (fun y : ℝ ↦ deriv
          (fun w : ℝ ↦ intervalFullSemigroupOperator (z.1 - s) (F s) w) y) z.2 :=
    intervalIntegral.integral_add_adjacent_intervals hOldInt_z hTailInt_z
  have hSplit_t :
      (∫ s in (0 : ℝ)..a, deriv (fun y : ℝ ↦ deriv
          (fun w : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) w) y) x) +
        ∫ s in a..t, deriv (fun y : ℝ ↦ deriv
          (fun w : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) w) y) x =
        ∫ s in (0 : ℝ)..t, deriv (fun y : ℝ ↦ deriv
          (fun w : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) w) y) x :=
    intervalIntegral.integral_add_adjacent_intervals hOldInt_t hTailInt_t
  let Oz : ℝ := ∫ s in (0 : ℝ)..a, deriv (fun y : ℝ ↦ deriv
    (fun w : ℝ ↦ intervalFullSemigroupOperator (z.1 - s) (F s) w) y) z.2
  let Ot : ℝ := ∫ s in (0 : ℝ)..a, deriv (fun y : ℝ ↦ deriv
    (fun w : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) w) y) x
  let Tz : ℝ := ∫ s in a..z.1, deriv (fun y : ℝ ↦ deriv
    (fun w : ℝ ↦ intervalFullSemigroupOperator (z.1 - s) (F s) w) y) z.2
  let Tt : ℝ := ∫ s in a..t, deriv (fun y : ℝ ↦ deriv
    (fun w : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) w) y) x
  have hOld_small' : |Oz - Ot| < eps / 3 := by
    simpa [Oz, Ot, Real.dist_eq] using hOld_small
  have hTz_small : |Tz| < eps / 3 := by
    simpa [Tz] using hTail_z_small
  have hTt_small : |Tt| < eps / 3 := by
    simpa [Tt] using hTail_t_small
  have hSplit_z' : Oz + Tz =
      ∫ s in (0 : ℝ)..z.1, deriv (fun y : ℝ ↦ deriv
        (fun w : ℝ ↦ intervalFullSemigroupOperator (z.1 - s) (F s) w) y) z.2 := by
    simpa [Oz, Tz] using hSplit_z
  have hSplit_t' : Ot + Tt =
      ∫ s in (0 : ℝ)..t, deriv (fun y : ℝ ↦ deriv
        (fun w : ℝ ↦ intervalFullSemigroupOperator (t - s) (F s) w) y) x := by
    simpa [Ot, Tt] using hSplit_t
  rw [Real.dist_eq, ← hSplit_z', ← hSplit_t']
  change |(Oz + Tz) - (Ot + Tt)| < eps
  have htri : |(Oz + Tz) - (Ot + Tt)| ≤
      |Oz - Ot| + |Tz| + |Tt| := by
    calc
      |(Oz + Tz) - (Ot + Tt)| = |(Oz - Ot) + (Tz - Tt)| := by ring
      _ ≤ |Oz - Ot| + |Tz - Tt| := abs_add_le _ _
      _ ≤ |Oz - Ot| + (|Tz| + |Tt|) := by
        gcongr
        exact abs_sub Tz Tt
      _ = |Oz - Ot| + |Tz| + |Tt| := by ring
  linarith

/-! ## Faithful chemotaxis Hessian -/

private def jointChemFluxBoundConst
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀) : ℝ :=
  D.M * (Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
      (2 * (p.ν * D.M ^ p.γ)))

private theorem jointChemFluxBoundConst_nonneg
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀) :
    0 ≤ jointChemFluxBoundConst D := by
  unfold jointChemFluxBoundConst
  exact mul_nonneg D.hM.le
    (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))))

private def jointChemFluxWindowCutoff
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀) : ℝ → ℝ → ℝ :=
  fun s y =>
    if 0 < s ∧ s ≤ D.T then chemFluxLifted p (D.u s) y else 0

private theorem jointChemFluxWindowCutoff_measurable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀) :
    Measurable (Function.uncurry (jointChemFluxWindowCutoff D)) := by
  have hbase := ShenWork.Paper2.chemFluxLifted_uncurry_measurable
    (p := p) (u := D.u) D.hmeas
  unfold jointChemFluxWindowCutoff
  refine Measurable.ite ?_ hbase measurable_const
  exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
    ((isClosed_Iic.preimage continuous_fst).measurableSet)

private theorem jointChemFluxWindowCutoff_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀) :
    ∀ s y, |jointChemFluxWindowCutoff D s y| ≤ jointChemFluxBoundConst D := by
  intro s y
  unfold jointChemFluxWindowCutoff
  split_ifs with hs
  · exact ShenWork.IntervalConjugateChemFluxIntegrable.chemFluxLifted_sup_bound_of_ball
      p D.hM.le (D.hbound s hs.1 hs.2) (D.hnonneg s hs.1 hs.2)
        (D.hcont s hs.1 hs.2) y
  · simpa using jointChemFluxBoundConst_nonneg D

private theorem jointChemFluxWindowCutoff_continuous
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀) :
    ∀ s, Continuous (jointChemFluxWindowCutoff D s) := by
  intro s
  unfold jointChemFluxWindowCutoff
  split_ifs with hs
  · exact ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_continuous_of_continuous
      p (D.hcont s hs.1 hs.2) (D.hnonneg s hs.1 hs.2)
  · exact continuous_const

private theorem jointChemFluxWindowCutoff_integrable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀) :
    ∀ s, Integrable (jointChemFluxWindowCutoff D s) (intervalMeasure 1) := by
  intro s
  simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
  exact (jointChemFluxWindowCutoff_continuous D s).continuousOn.integrableOn_Icc

private theorem jointIntervalFullSemigroupOperator_congr_on_Ioo
    {f g : ℝ → ℝ} (hfg : Set.EqOn f g (Set.Ioo (0 : ℝ) 1))
    (r x : ℝ) :
    intervalFullSemigroupOperator r f x =
      intervalFullSemigroupOperator r g x := by
  unfold intervalFullSemigroupOperator
  apply MeasureTheory.integral_congr_ae
  have hmem : ∀ᵐ y : ℝ ∂(intervalMeasure 1),
      y ∈ Set.Ioo (0 : ℝ) 1 := by
    simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
    refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
    have hne0 : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by
      rw [ae_iff]
      simp only [not_not, Set.setOf_eq_eq_singleton]
      exact Real.volume_singleton
    have hne1 : ∀ᵐ y : ℝ ∂volume, y ≠ 1 := by
      rw [ae_iff]
      simp only [not_not, Set.setOf_eq_eq_singleton]
      exact Real.volume_singleton
    filter_upwards [hne0, hne1] with y hy0 hy1 hy
    exact ⟨lt_of_le_of_ne hy.1 (Ne.symm hy0),
      lt_of_le_of_ne hy.2 hy1⟩
  filter_upwards [hmem] with y hy
  rw [hfg hy]

private theorem jointConstExtend_eq_apply_unitClip
    (f : intervalDomainPoint → ℝ) (y : ℝ) :
    intervalDomainConstExtend f y = f (unitClip y) := by
  unfold intervalDomainConstExtend unitClip
  by_cases h0 : y ≤ 0
  · simp only [dif_pos h0]
    congr 1
    apply Subtype.ext
    simp [min_eq_left (h0.trans zero_le_one), max_eq_left h0]
  · simp only [dif_neg h0]
    by_cases h1 : 1 ≤ y
    · simp only [dif_pos h1]
      congr 1
      apply Subtype.ext
      simp [min_eq_right h1]
    · simp only [dif_neg h1]
      congr 1
      apply Subtype.ext
      simp [min_eq_left (le_of_not_ge h1), max_eq_right (le_of_not_ge h0)]

/-- A continuous constant extension of the physical flux-divergence
representative, switched on only after the fixed positive cutoff `a`. -/
private def jointChemDivLateConstCutoff
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀) (a : ℝ) : ℝ → ℝ → ℝ :=
  fun s y =>
    if a < s ∧ s < D.T then
      intervalDomainConstExtend
        (fun x : intervalDomainPoint =>
          conjugateMildChemDivJointRep p D.u s x.1) y
    else 0

private theorem jointChemDivLateConstCutoff_measurable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {a : ℝ} (ha : 0 ≤ a) :
    Measurable (Function.uncurry (jointChemDivLateConstCutoff D a)) := by
  let A : Set (ℝ × ℝ) := {q | a < q.1 ∧ q.1 < D.T}
  let R : ℝ × ℝ → ℝ := fun q =>
    conjugateMildChemDivJointRep p D.u q.1 (unitClip q.2).1
  have hmap : Continuous
      (fun q : ℝ × ℝ => (q.1, (unitClip q.2).1)) :=
    continuous_fst.prodMk
      (continuous_subtype_val.comp (unitClip_continuous.comp continuous_snd))
  have hR : ContinuousOn R A := by
    apply (conjugateMildChemDivJointRep_jointContinuousOn
      D hu₀_bound hu₀_meas).comp hmap.continuousOn
    intro q hq
    exact Set.mem_prod.mpr
      ⟨⟨ha.trans_lt hq.1, hq.2⟩, (unitClip q.2).2⟩
  have hA : MeasurableSet A :=
    ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isOpen_Iio.preimage continuous_fst).measurableSet)
  have hpiece : Function.uncurry (jointChemDivLateConstCutoff D a) =
      A.piecewise R (fun _ => 0) := by
    funext q
    by_cases hq : q ∈ A
    · rw [Set.piecewise_eq_of_mem _ _ _ hq]
      have hq' : a < q.1 ∧ q.1 < D.T := by simpa [A] using hq
      change (if a < q.1 ∧ q.1 < D.T then
          intervalDomainConstExtend
            (fun x : intervalDomainPoint =>
              conjugateMildChemDivJointRep p D.u q.1 x.1) q.2 else 0) = _
      rw [if_pos hq', jointConstExtend_eq_apply_unitClip]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hq]
      have hq' : ¬ (a < q.1 ∧ q.1 < D.T) := by simpa [A] using hq
      change (if a < q.1 ∧ q.1 < D.T then
          intervalDomainConstExtend
            (fun x : intervalDomainPoint =>
              conjugateMildChemDivJointRep p D.u q.1 x.1) q.2 else 0) = 0
      rw [if_neg hq']
  rw [hpiece]
  exact ContinuousOn.measurable_piecewise hR continuousOn_const hA

private theorem jointChemDivLateConstCutoff_continuous
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {a : ℝ} (ha : 0 ≤ a) :
    ∀ s, Continuous (jointChemDivLateConstCutoff D a s) := by
  intro s
  by_cases hs : a < s ∧ s < D.T
  · rw [show jointChemDivLateConstCutoff D a s =
        intervalDomainConstExtend
          (fun x : intervalDomainPoint =>
            conjugateMildChemDivJointRep p D.u s x.1) by
      funext y
      simp [jointChemDivLateConstCutoff, hs]]
    apply ShenWork.IntervalDomain.constExtend_continuous
    have hslice : ContinuousOn
        (fun x : intervalDomainPoint =>
          conjugateMildChemDivJointRep p D.u s x.1) Set.univ := by
      apply (conjugateMildChemDivJointRep_jointContinuousOn
        D hu₀_bound hu₀_meas).comp
        (continuous_const.prodMk continuous_subtype_val).continuousOn
      intro x _hx
      exact Set.mem_prod.mpr ⟨⟨ha.trans_lt hs.1, hs.2⟩, x.2⟩
    simpa only [continuousOn_univ] using hslice
  · rw [show jointChemDivLateConstCutoff D a s = fun _ : ℝ => 0 by
      funext y
      simp [jointChemDivLateConstCutoff, hs]]
    exact continuous_const

private theorem jointChemDivLateConstCutoff_integrable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {a : ℝ} (ha : 0 ≤ a) :
    ∀ s, Integrable (jointChemDivLateConstCutoff D a s) (intervalMeasure 1) := by
  intro s
  simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
  exact (jointChemDivLateConstCutoff_continuous
    D hu₀_bound hu₀_meas ha s).continuousOn.integrableOn_Icc

private theorem jointChemDivLateConstCutoff_bounded
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s y, |jointChemDivLateConstCutoff D a s y| ≤ C := by
  obtain ⟨C, hC, hraw⟩ :=
    conjugateMild_chemFlux_deriv_positiveTime_uniformBound
      D hu₀_bound hu₀_meas ha
  refine ⟨C, hC, ?_⟩
  intro s y
  by_cases hs : a < s ∧ s < D.T
  · rw [jointChemDivLateConstCutoff, if_pos hs,
      jointConstExtend_eq_apply_unitClip]
    let R : ℝ → ℝ := conjugateMildChemDivJointRep p D.u s
    have hRcont : ContinuousOn R (Set.Icc (0 : ℝ) 1) := by
      apply (conjugateMildChemDivJointRep_jointContinuousOn
        D hu₀_bound hu₀_meas).comp
        (continuous_const.prodMk continuous_id).continuousOn
      intro z hz
      exact Set.mem_prod.mpr ⟨⟨ha.trans hs.1, hs.2⟩, hz⟩
    have hRIoo : ∀ z ∈ Set.Ioo (0 : ℝ) 1, |R z| ≤ C := by
      intro z hz
      rw [show R z = deriv (chemFluxLifted p (D.u s)) z by
        symm
        exact deriv_chemFluxLifted_eq_conjugateMildChemDivJointRep_interior
          D hu₀_bound hu₀_meas (ha.trans hs.1) hs.2.le hz]
      exact hraw s hs.1.le hs.2.le z hz
    have hcl : closure (Set.Ioo (0 : ℝ) 1) = Set.Icc (0 : ℝ) 1 :=
      closure_Ioo (by norm_num)
    have hzcl : (unitClip y).1 ∈ closure (Set.Ioo (0 : ℝ) 1) := by
      rw [hcl]
      exact (unitClip y).2
    exact le_on_closure (s := Set.Ioo (0 : ℝ) 1)
      (f := fun z => |R z|) (g := fun _ => C) hRIoo
      (by simpa [hcl] using hRcont.abs) continuousOn_const hzcl
  · rw [jointChemDivLateConstCutoff, if_neg hs, abs_zero]
    exact hC

private theorem jointChemDivLateConstCutoff_positiveStripHolder
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    (a : ℝ) :
    ∀ tau, 0 < tau →
      ∃ theta HQ : ℝ, 0 < theta ∧ theta < 1 ∧ 0 ≤ HQ ∧
        ∀ s, tau ≤ s → s ≤ D.T →
          ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
            |jointChemDivLateConstCutoff D a s x -
              jointChemDivLateConstCutoff D a s y| ≤
                HQ * |x - y| ^ theta := by
  intro tau htau
  obtain ⟨theta, HQ, htheta0, htheta1, hHQ, hraw⟩ :=
    conjugateMildChemDivJointRep_positiveTime_holder_uniform
      D hu₀_bound hu₀_meas htau
  refine ⟨theta, HQ, htheta0, htheta1, hHQ, ?_⟩
  intro s htaus hsT x hx y hy
  by_cases hs : a < s ∧ s < D.T
  · have hLx : jointChemDivLateConstCutoff D a s x =
        conjugateMildChemDivJointRep p D.u s x := by
      rw [jointChemDivLateConstCutoff, if_pos hs,
        constExtend_eq_lift_on_Icc (Set.Ioo_subset_Icc_self hx)]
      simp [intervalDomainLift, Set.Ioo_subset_Icc_self hx]
    have hLy : jointChemDivLateConstCutoff D a s y =
        conjugateMildChemDivJointRep p D.u s y := by
      rw [jointChemDivLateConstCutoff, if_pos hs,
        constExtend_eq_lift_on_Icc (Set.Ioo_subset_Icc_self hy)]
      simp [intervalDomainLift, Set.Ioo_subset_Icc_self hy]
    rw [hLx, hLy]
    exact hraw s htaus hsT x hx y hy
  · simp only [jointChemDivLateConstCutoff, if_neg hs, sub_self, abs_zero]
    exact mul_nonneg hHQ (Real.rpow_nonneg (abs_nonneg _) _)

/-- On a time window lying strictly after `a`, the actual conjugate-kernel
Hessian splits into a nonsingular old conjugate history and a full-semigroup
history of the continuous physical divergence representative.  Every
adjacent-interval split below carries explicit integrability evidence. -/
private theorem conjugateMild_chemHessian_decomposition_after
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {a t x : ℝ} (ha : 0 < a) (hat : a < t) (htT : t < D.T)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..a, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalConjugateKernelOperator (t - s)
          (jointChemFluxWindowCutoff D s) z) y) x) +
      ∫ s in (0 : ℝ)..t, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator (t - s)
          (jointChemDivLateConstCutoff D a s) z) y) x =
    ∫ s in (0 : ℝ)..t, deriv (fun y : ℝ ↦ deriv
      (fun z : ℝ ↦ intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p (D.u s)) z) y) x := by
  let Qc : ℝ → ℝ → ℝ := jointChemFluxWindowCutoff D
  let L : ℝ → ℝ → ℝ := jointChemDivLateConstCutoff D a
  let A : ℝ → ℝ := fun s => deriv (fun y : ℝ => deriv
    (fun z : ℝ => intervalConjugateKernelOperator (t - s)
      (chemFluxLifted p (D.u s)) z) y) x
  let AO : ℝ → ℝ := fun s => deriv (fun y : ℝ => deriv
    (fun z : ℝ => intervalConjugateKernelOperator (t - s) (Qc s) z) y) x
  let AL : ℝ → ℝ := fun s => deriv (fun y : ℝ => deriv
    (fun z : ℝ => intervalFullSemigroupOperator (t - s) (L s) z) y) x
  have ht : 0 < t := ha.trans hat
  have hActualInt : IntervalIntegrable A volume 0 t := by
    simpa [A] using
      (conjugateMild_chemDuhamel_secondDeriv_intervalIntegrable_Icc
        D hu₀_bound hu₀_meas ht htT.le hx)
  have hActualOld : IntervalIntegrable A volume 0 a :=
    hActualInt.mono_set (by
      rw [Set.uIcc_of_le ha.le, Set.uIcc_of_le ht.le]
      exact Set.Icc_subset_Icc le_rfl hat.le)
  have hActualLate : IntervalIntegrable A volume a t :=
    hActualInt.mono_set (by
      rw [Set.uIcc_of_le hat.le, Set.uIcc_of_le ht.le]
      exact Set.Icc_subset_Icc ha.le le_rfl)
  have hOldEq : (∫ s in (0 : ℝ)..a, AO s) = ∫ s in (0 : ℝ)..a, A s := by
    apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le ha.le]
    filter_upwards with s hs
    have hsT : s ≤ D.T := hs.2.trans (hat.le.trans htT.le)
    have hQeq : Qc s = chemFluxLifted p (D.u s) := by
      funext y
      simp [Qc, jointChemFluxWindowCutoff, hs.1, hsT]
    dsimp [AO, A]
    rw [hQeq]
  have hALearly : IntervalIntegrable AL volume 0 a := by
    have hzeroInt : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 a :=
      intervalIntegrable_const
    refine hzeroInt.congr_ae ?_
    rw [Set.uIoc_of_le ha.le]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro s hs
    symm
    have hsa : ¬ a < s := not_lt_of_ge hs.2
    have hLs : L s = fun _ : ℝ => 0 := by
      change jointChemDivLateConstCutoff D a s = fun _ : ℝ => 0
      funext y
      simp [jointChemDivLateConstCutoff, hsa]
    dsimp [AL]
    rw [hLs]
    simp [intervalFullSemigroupOperator]
  have hALeq : A =ᵐ[volume.restrict (Set.uIoc a t)] AL := by
    rw [Set.uIoc_of_le hat.le]
    change ∀ᵐ s ∂volume.restrict (Set.Ioc a t), A s = AL s
    refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
    have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
      rw [ae_iff]
      simp only [not_not, Set.setOf_eq_eq_singleton]
      exact Real.volume_singleton
    filter_upwards [hne] with s hst_ne hs
    have hst : s < t := lt_of_le_of_ne hs.2 hst_ne
    have hs0 : 0 < s := ha.trans hs.1
    have hsT : s ≤ D.T := (hst.trans htT).le
    have hlag : 0 < t - s := sub_pos.mpr hst
    have hLrep : Set.EqOn (L s)
        (conjugateMildChemDivJointRep p D.u s) (Set.Icc (0 : ℝ) 1) := by
      intro z hz
      change jointChemDivLateConstCutoff D a s z = _
      rw [jointChemDivLateConstCutoff,
        if_pos ⟨hs.1, hst.trans htT⟩, constExtend_eq_lift_on_Icc hz]
      simp [intervalDomainLift, hz]
    have hspace :
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (L s) z) =
        (fun z : ℝ => intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (D.u s)) z) := by
      funext z
      have hSLrep :=
        ShenWork.Paper2.intervalFullSemigroupOperator_congr_on_Icc
          (t := t - s) hLrep z
      have hrawrep := jointIntervalFullSemigroupOperator_congr_on_Ioo
        (fun w hw => deriv_chemFluxLifted_eq_conjugateMildChemDivJointRep_interior
          D hu₀_bound hu₀_meas hs0 hsT hw) (t - s) z
      have hIBP := conjugateMild_intervalConjugateKernelOperator_eq_semigroup_fluxDeriv
        D hu₀_bound hu₀_meas hs0 hsT hlag (x := z)
      exact hSLrep.trans (hrawrep.symm.trans hIBP.symm)
    dsimp [A, AL]
    rw [hspace]
  have hALlate : IntervalIntegrable AL volume a t :=
    hActualLate.congr_ae hALeq
  have hLateEq : (∫ s in (0 : ℝ)..t, AL s) = ∫ s in a..t, A s := by
    rw [(intervalIntegral.integral_add_adjacent_intervals hALearly hALlate).symm]
    have hzero : (∫ s in (0 : ℝ)..a, AL s) = 0 := by
      calc
        _ = ∫ _s in (0 : ℝ)..a, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [Set.uIcc_of_le ha.le] at hs
          have hsa : ¬ a < s := not_lt_of_ge hs.2
          have hLs : L s = fun _ : ℝ => 0 := by
            change jointChemDivLateConstCutoff D a s = fun _ : ℝ => 0
            funext y
            simp [jointChemDivLateConstCutoff, hsa]
          dsimp [AL]
          rw [hLs]
          simp [intervalFullSemigroupOperator]
        _ = 0 := by simp
    rw [hzero, zero_add]
    apply intervalIntegral.integral_congr_ae
    rw [← ae_restrict_iff' measurableSet_uIoc]
    exact hALeq.symm
  have hActualSplit :
      (∫ s in (0 : ℝ)..a, A s) + ∫ s in a..t, A s =
        ∫ s in (0 : ℝ)..t, A s :=
    intervalIntegral.integral_add_adjacent_intervals hActualOld hActualLate
  change (∫ s in (0 : ℝ)..a, AO s) + ∫ s in (0 : ℝ)..t, AL s =
    ∫ s in (0 : ℝ)..t, A s
  rw [hOldEq, hLateEq]
  exact hActualSplit

/-- Joint continuity of the actual chemotaxis Hessian on any strip whose
lower endpoint is strictly positive. -/
private theorem conjugateMild_chemDuhamel_secondDeriv_jointContinuousOn_after
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {a : ℝ} (ha : 0 < a) :
    ContinuousOn
      (fun q : ℝ × ℝ ↦ ∫ s in (0 : ℝ)..q.1, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalConjugateKernelOperator (q.1 - s)
          (chemFluxLifted p (D.u s)) z) y) q.2)
      (Set.Ioo a D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  let Qc : ℝ → ℝ → ℝ := jointChemFluxWindowCutoff D
  let L : ℝ → ℝ → ℝ := jointChemDivLateConstCutoff D a
  let S : Set (ℝ × ℝ) := Set.Ioo a D.T ×ˢ Set.Icc (0 : ℝ) 1
  have hQc_meas : Measurable (Function.uncurry Qc) := by
    simpa [Qc] using jointChemFluxWindowCutoff_measurable D
  have hQc_cont : ∀ s, Continuous (Qc s) := by
    simpa [Qc] using jointChemFluxWindowCutoff_continuous D
  have hQc_int : ∀ s, Integrable (Qc s) (intervalMeasure 1) := by
    simpa [Qc] using jointChemFluxWindowCutoff_integrable D
  have hQc_bound : ∀ s y, |Qc s y| ≤ jointChemFluxBoundConst D := by
    simpa [Qc] using jointChemFluxWindowCutoff_bound D
  have hOldCont : ContinuousOn
      (fun q : ℝ × ℝ ↦ ∫ s in (0 : ℝ)..a, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalConjugateKernelOperator (q.1 - s) (Qc s) z) y) q.2)
      S := by
    intro q hq
    have hbase :=
      intervalConjugateDuhamel_fixedHistory_secondDeriv_continuousWithinAt_joint
        ha.le hq.1.1 hQc_meas hQc_cont hQc_int hQc_bound hq.2
    exact hbase.mono (by
      intro z hz
      exact Set.mem_prod.mpr ⟨ha.trans hz.1.1, hz.2⟩)
  obtain ⟨CL, hCL, hLbound⟩ :=
    jointChemDivLateConstCutoff_bounded D hu₀_bound hu₀_meas ha
  have hLmeas : Measurable (Function.uncurry L) := by
    simpa [L] using jointChemDivLateConstCutoff_measurable
      D hu₀_bound hu₀_meas ha.le
  have hLcont : ∀ s, Continuous (L s) := by
    simpa [L] using jointChemDivLateConstCutoff_continuous
      D hu₀_bound hu₀_meas ha.le
  have hLint : ∀ s, Integrable (L s) (intervalMeasure 1) := by
    simpa [L] using jointChemDivLateConstCutoff_integrable
      D hu₀_bound hu₀_meas ha.le
  have hLholder : ∀ tau, 0 < tau →
      ∃ theta HQ : ℝ, 0 < theta ∧ theta < 1 ∧ 0 ≤ HQ ∧
        ∀ s, tau ≤ s → s ≤ D.T →
          ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
            |L s x - L s y| ≤ HQ * |x - y| ^ theta := by
    simpa [L] using
      (jointChemDivLateConstCutoff_positiveStripHolder
        D hu₀_bound hu₀_meas a)
  have hLateBase :=
    intervalFullDuhamel_secondDeriv_jointContinuousOn_of_positiveStripHolder
      D.hT hLmeas hLcont hLint hLbound hLholder
  have hLateCont : ContinuousOn
      (fun q : ℝ × ℝ ↦ ∫ s in (0 : ℝ)..q.1, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator (q.1 - s) (L s) z) y) q.2)
      S :=
    hLateBase.mono (by
      intro q hq
      exact Set.mem_prod.mpr ⟨⟨ha.trans hq.1.1, hq.1.2⟩, hq.2⟩)
  have hsum := hOldCont.add hLateCont
  refine hsum.congr ?_
  intro q hq
  simpa [Qc, L, S] using
    (conjugateMild_chemHessian_decomposition_after
      D hu₀_bound hu₀_meas ha hq.1.1 hq.1.2 hq.2).symm

/-- The Hessian history of the faithful chemotaxis Duhamel leg is jointly
continuous at strict positive times, including both physical endpoints. -/
theorem conjugateMild_chemDuhamel_secondDeriv_jointContinuousOn
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1)) :
    ContinuousOn
      (fun q : ℝ × ℝ ↦ ∫ s in (0 : ℝ)..q.1, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalConjugateKernelOperator (q.1 - s)
          (chemFluxLifted p (D.u s)) z) y) q.2)
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  let S : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1
  intro q hq
  let a : ℝ := q.1 / 2
  have ha : 0 < a := by dsimp [a]; linarith [hq.1.1]
  have haq : a < q.1 := by dsimp [a]; linarith [hq.1.1]
  have hstrip := conjugateMild_chemDuhamel_secondDeriv_jointContinuousOn_after
    D hu₀_bound hu₀_meas ha
  have hqstrip : q ∈ Set.Ioo a D.T ×ˢ Set.Icc (0 : ℝ) 1 :=
    Set.mem_prod.mpr ⟨⟨haq, hq.1.2⟩, hq.2⟩
  have hwithin := hstrip q hqstrip
  have hnear0 : Set.Ioi a ×ˢ Set.univ ∈ nhds q :=
    prod_mem_nhds (Ioi_mem_nhds haq) univ_mem
  have hlocal : Set.Ioo a D.T ×ˢ Set.Icc (0 : ℝ) 1 ∈
      nhdsWithin q S := by
    have hinter := Filter.inter_mem (Filter.mem_inf_of_left hnear0)
      (self_mem_nhdsWithin (a := q) (s := S))
    refine Filter.mem_of_superset hinter ?_
    intro z hz
    exact Set.mem_prod.mpr ⟨⟨hz.1.1, hz.2.1.2⟩, hz.2.2⟩
  exact hwithin.mono_of_mem_nhdsWithin hlocal

/-! ## Faithful logistic Hessian -/

/-- The Hessian history of the faithful logistic Duhamel leg is jointly
continuous at strict positive times, including both physical endpoints. -/
theorem conjugateMild_logisticDuhamel_secondDeriv_jointContinuousOn
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1)) :
    ContinuousOn
      (fun q : ℝ × ℝ ↦ ∫ s in (0 : ℝ)..q.1, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator (q.1 - s)
          (logisticLifted p (D.u s)) z) y) q.2)
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  let F : ℝ → ℝ → ℝ := conjugateMildLogisticConstCutoff D
  let CL : ℝ := D.M * (p.a + p.b * D.M ^ p.α)
  have hF_meas : Measurable (Function.uncurry F) := by
    simpa [F] using conjugateMildLogisticConstCutoff_measurable D
  have hF_cont : ∀ s, Continuous (F s) := by
    simpa [F] using conjugateMildLogisticConstCutoff_continuous D
  have hF_int : ∀ s, Integrable (F s) (intervalMeasure 1) := by
    simpa [F] using conjugateMildLogisticConstCutoff_integrable D
  have hF_bound : ∀ s y, |F s y| ≤ CL := by
    simpa [F, CL] using conjugateMildLogisticConstCutoff_bound D
  have hF_holder : ∀ tau, 0 < tau →
      ∃ theta HQ : ℝ, 0 < theta ∧ theta < 1 ∧ 0 ≤ HQ ∧
        ∀ s, tau ≤ s → s ≤ D.T →
          ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
            |F s x - F s y| ≤ HQ * |x - y| ^ theta := by
    intro tau htau
    obtain ⟨HQ, hHQ, hraw⟩ :=
      conjugateMild_logisticLifted_positiveTime_holder_uniform
        D hu₀_bound hu₀_meas htau
    refine ⟨(1 / 4 : ℝ), HQ, by norm_num, by norm_num, hHQ, ?_⟩
    intro s htaus hsT x hx y hy
    have hs0 : 0 < s := htau.trans_le htaus
    have hxIcc := Set.Ioo_subset_Icc_self hx
    have hyIcc := Set.Ioo_subset_Icc_self hy
    have hFx : F s x = logisticLifted p (D.u s) x := by
      dsimp [F, conjugateMildLogisticConstCutoff]
      rw [if_pos ⟨hs0, hsT⟩, constExtend_eq_lift_on_Icc hxIcc]
      rfl
    have hFy : F s y = logisticLifted p (D.u s) y := by
      dsimp [F, conjugateMildLogisticConstCutoff]
      rw [if_pos ⟨hs0, hsT⟩, constExtend_eq_lift_on_Icc hyIcc]
      rfl
    rw [hFx, hFy]
    exact hraw s htaus hsT x hx y hy
  have hbase :=
    intervalFullDuhamel_secondDeriv_jointContinuousOn_of_positiveStripHolder
      D.hT hF_meas hF_cont hF_int hF_bound hF_holder
  refine hbase.congr ?_
  intro q hq
  apply intervalIntegral.integral_congr_ae
  rw [Set.uIoc_of_le hq.1.1.le]
  filter_upwards with s hs
  have hsT : s ≤ D.T := hs.2.trans hq.1.2.le
  have hspace :
      (fun z : ℝ ↦ intervalFullSemigroupOperator (q.1 - s) (F s) z) =
      (fun z : ℝ ↦ intervalFullSemigroupOperator (q.1 - s)
        (logisticLifted p (D.u s)) z) := by
    funext z
    have hFs : F s =
        intervalDomainConstExtend (intervalLogisticSource p (D.u s)) := by
      funext y
      dsimp [F, conjugateMildLogisticConstCutoff]
      rw [if_pos ⟨hs.1, hsT⟩]
    rw [hFs]
    exact semigroupOperator_constExtend_eq_lift
  rw [hspace]

/-! ## Closed-slab joint time derivative -/

/-- The faithful positive-time derivative representative is jointly
continuous in time and closed physical space.  Its construction uses only
the mild-solution data and the original datum's continuity, bound, and
measurability. -/
theorem conjugateMildTimeDerivJointRep_jointContinuousOn
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1)) :
    ContinuousOn
      (Function.uncurry (conjugateMildTimeDerivJointRep D))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  let S : Set (ℝ × ℝ) :=
    Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1
  have hinit : ContinuousOn
      (fun q : ℝ × ℝ ↦ deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator q.1
          (intervalDomainLift u₀) z) y) q.2) S := by
    apply (intervalFullSemigroupOperator_lift_secondDeriv_jointContinuousOn_Ioi_Icc
      hu₀_cont).mono
    intro q hq
    exact Set.mem_prod.mpr ⟨hq.1.1, hq.2⟩
  have hchemH :=
    conjugateMild_chemDuhamel_secondDeriv_jointContinuousOn
      D hu₀_bound hu₀_meas
  have hchemTrace :=
    conjugateMildChemDivJointRep_jointContinuousOn
      D hu₀_bound hu₀_meas
  have hlogH :=
    conjugateMild_logisticDuhamel_secondDeriv_jointContinuousOn
      D hu₀_bound hu₀_meas
  have hlogTrace :=
    conjugateMild_logisticLifted_jointContinuousOn
      D hu₀_bound hu₀_meas
  have hchi : ContinuousOn (fun _ : ℝ × ℝ ↦ (-p.χ₀)) S :=
    continuousOn_const
  have hsum :=
    (hinit.add (hchi.mul (hchemH.add hchemTrace))).add
      (hlogH.add hlogTrace)
  simpa [S, conjugateMildTimeDerivJointRep, Function.uncurry] using hsum

/-- The literal target-time derivative of the lifted faithful solution is
jointly continuous on the same closed spatial slab. -/
theorem conjugateMild_intervalDomainLift_timeDeriv_jointContinuousOn_Icc
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1)) :
    ContinuousOn
      (Function.uncurry (fun t x ↦
        deriv (fun s : ℝ ↦ intervalDomainLift (D.u s) x) t))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  refine (conjugateMildTimeDerivJointRep_jointContinuousOn
    D hu₀_cont hu₀_bound hu₀_meas).congr ?_
  intro q hq
  simpa [Function.uncurry] using
    (conjugateMild_intervalDomainLift_hasDerivAt_time_Icc
      D hu₀_cont hu₀_bound hu₀_meas hq.1.1 hq.1.2 hq.2).deriv

section AxiomAudit

#print axioms intervalFullSemigroupOperator_secondDeriv_jointContinuousOn_Ioi_Icc
#print axioms intervalFullSemigroupOperator_secondDeriv_jointContinuousOn_Ioi_Ioo
#print axioms intervalConjugateKernelOperator_secondDeriv_jointContinuousOn_Ioi_Ioo
#print axioms intervalFullDuhamel_secondDeriv_jointContinuousOn_of_positiveStripHolder
#print axioms conjugateMild_chemDuhamel_secondDeriv_jointContinuousOn
#print axioms conjugateMild_logisticDuhamel_secondDeriv_jointContinuousOn
#print axioms conjugateMildTimeDerivJointRep_jointContinuousOn
#print axioms conjugateMild_intervalDomainLift_timeDeriv_jointContinuousOn_Icc

end AxiomAudit

end ShenWork.Paper2
