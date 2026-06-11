import ShenWork.Paper2.IntervalMildPicardRegularityEndpoint2
import ShenWork.Paper2.IntervalPicardIterateTimeC1JointEndpoint

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalPicardIterateTimeC1
  (restartFieldTimeDeriv logisticSourceDot)
open ShenWork.IntervalPicardIterateTimeC1JointEndpoint
  (restartFieldTimeDeriv_continuousOn_joint_On
   restartFieldTimeDeriv_continuousOn_joint_On_shift)

noncomputable section

namespace ShenWork.IntervalPicardIterateTimeC1Endpoint

/-- One-sided closed-window version of `logisticSource_adot_hasDerivAt`.

The represented field is read at physical time `s` but its restart coefficients
are read at `s - offset`; `hshift` is the closed-window compatibility needed by
the endpoint restart-field derivative atom. -/
theorem logisticSource_adot_hasDerivWithinAt_endpoint
    {p : CM2Params} (hα : 0 < p.α)
    {w : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} {offset W a' σ : ℝ}
    (src : DuhamelSourceTimeC1On a 0 W)
    (ha'pos : 0 < a') (hσ : σ ∈ Set.Icc a' W)
    (hshift : Set.MapsTo (fun s : ℝ => s - offset)
      (Set.Icc a' W) (Set.Icc a' W))
    (hagree : ∀ s ∈ Set.Icc a' W, ∀ x : intervalDomainPoint,
      intervalDomainLift (w s) x.1 =
        ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n x.1)
    (hpos : ∀ s ∈ Set.Icc a' W, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (w s) x)
    (hC2cont : ∀ s ∈ Set.Icc a' W,
      ContinuousOn (intervalDomainLift (w s)) (Set.Icc (0 : ℝ) 1))
    (hprofile_joint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (w s) x))
      (Set.Icc a' W ×ˢ Set.Icc (0 : ℝ) 1))
    (k : ℕ) :
    HasDerivWithinAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (w r))) k)
      (cosineCoeffs (fun x => logisticSourceDot a₀ a p w offset σ x) k)
      (Set.Icc a' W) σ := by
  set f : ℝ → ℝ → ℝ := fun s x =>
    logisticSourceFun p.a p.b p.α (intervalDomainLift (w s)) x with hfdef
  set f' : ℝ → ℝ → ℝ := fun s x =>
    logisticSourceDot a₀ a p w offset s x with hf'def
  have ha'W : a' ≤ W := le_trans hσ.1 hσ.2
  have hf_cont : ∀ s ∈ Set.Icc a' W,
      ContinuousOn (f s) (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    have hgc : ContinuousOn (intervalDomainLift (w s)) (Set.Icc (0 : ℝ) 1) :=
      hC2cont s hs
    have hpos' : ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
        intervalDomainLift (w s) x ≠ 0 :=
      fun x hx => ne_of_gt (hpos s hs x hx)
    simp only [hfdef, logisticSourceFun]
    apply ContinuousOn.mul hgc
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    exact ContinuousOn.rpow_const hgc (fun x hx => Or.inl (hpos' x hx))
  have h_diff : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Set.Icc a' W,
      HasDerivWithinAt (fun r => f r x) (f' s x) (Set.Icc a' W) s := by
    intro x hx s hs
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
    have hτmem : s - offset ∈ Set.Icc a' W := hshift hs
    have hfield : HasDerivWithinAt (fun r => intervalDomainLift (w r) x)
        (restartFieldTimeDeriv a₀ a offset s x) (Set.Icc a' W) s := by
      exact restartField_hasDerivWithinAt_endpoint_shift hM₀ ha₀ src
        ha'pos hτmem.1 hτmem.2 hs hshift hagree x hxIcc
    have hpos_s : 0 < intervalDomainLift (w s) x := hpos s hs x hxIcc
    have hchain := logisticSourceFun_hasDerivWithinAt_time (a := p.a) (b := p.b)
      (α := p.α) hα (f := fun r => intervalDomainLift (w r) x)
      (f' := restartFieldTimeDeriv a₀ a offset s x) (σ := s)
      hpos_s hfield
    simp only [hfdef, hf'def, logisticSourceFun, logisticSourceDot]
    exact hchain
  have h_cont_deriv : ContinuousOn (Function.uncurry f')
      (Set.Icc a' W ×ˢ Set.Icc (0 : ℝ) 1) := by
    have hfieldjoint : ContinuousOn
        (Function.uncurry (fun s x => restartFieldTimeDeriv a₀ a offset s x))
        (Set.Icc a' W ×ˢ Set.Icc (0 : ℝ) 1) :=
      restartFieldTimeDeriv_continuousOn_joint_On hM₀ ha₀ src ha'pos hshift
    have hpowjoint : ContinuousOn
        (Function.uncurry (fun s x => (intervalDomainLift (w s) x) ^ p.α))
        (Set.Icc a' W ×ˢ Set.Icc (0 : ℝ) 1) := by
      have hne : ∀ q ∈ Set.Icc a' W ×ˢ Set.Icc (0 : ℝ) 1,
          intervalDomainLift (w q.1) q.2 ≠ 0 := by
        intro q hq
        obtain ⟨hq1, hq2⟩ := Set.mem_prod.1 hq
        exact ne_of_gt (hpos q.1 hq1 q.2 hq2)
      exact ContinuousOn.rpow_const hprofile_joint (fun q hq => Or.inl (hne q hq))
    simp only [hf'def, logisticSourceDot]
    change ContinuousOn (fun q : ℝ × ℝ =>
        restartFieldTimeDeriv a₀ a offset q.1 q.2 *
          (p.a - p.b * (1 + p.α) *
            (intervalDomainLift (w q.1) q.2) ^ p.α)) _
    exact hfieldjoint.mul
      ((continuousOn_const).sub (continuousOn_const.mul hpowjoint))
  have hkey :=
    ShenWork.IntervalMildPicardRegularityEndpoint2.cosineCoeffs_hasDerivWithinAt_of_smooth_param
      (f := f) (f' := f') (a' := a') (W := W) (n := k)
      ha'W hσ hf_cont h_diff h_cont_deriv
  simpa only [hfdef, hf'def] using hkey

/-- One-sided closed-window version of `logisticSource_adot_hasDerivAt`, with
separate physical and coefficient-time windows.

The physical represented field is differentiated on `[lo, hi]`.  Its restart
coefficient time is `τ = s - offset`, and `hshift` records that this lands in the
positive coefficient window `[aτ, W]` where the `_On` source package is available. -/
theorem logisticSource_adot_hasDerivWithinAt_endpoint_window
    {p : CM2Params} (hα : 0 < p.α)
    {w : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀) (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} {offset W lo hi aτ σ : ℝ}
    (src : DuhamelSourceTimeC1On a 0 W)
    (haτpos : 0 < aτ) (hσ : σ ∈ Set.Icc lo hi)
    (hshift : Set.MapsTo (fun s : ℝ => s - offset)
      (Set.Icc lo hi) (Set.Icc aτ W))
    (hagree : ∀ s ∈ Set.Icc lo hi, ∀ x : intervalDomainPoint,
      intervalDomainLift (w s) x.1 =
        ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n x.1)
    (hpos : ∀ s ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (w s) x)
    (hC2cont : ∀ s ∈ Set.Icc lo hi,
      ContinuousOn (intervalDomainLift (w s)) (Set.Icc (0 : ℝ) 1))
    (hprofile_joint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (w s) x))
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1))
    (k : ℕ) :
    HasDerivWithinAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (w r))) k)
      (cosineCoeffs (fun x => logisticSourceDot a₀ a p w offset σ x) k)
      (Set.Icc lo hi) σ := by
  set f : ℝ → ℝ → ℝ := fun s x =>
    logisticSourceFun p.a p.b p.α (intervalDomainLift (w s)) x with hfdef
  set f' : ℝ → ℝ → ℝ := fun s x =>
    logisticSourceDot a₀ a p w offset s x with hf'def
  have hlohi : lo ≤ hi := le_trans hσ.1 hσ.2
  have hf_cont : ∀ s ∈ Set.Icc lo hi,
      ContinuousOn (f s) (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    have hgc : ContinuousOn (intervalDomainLift (w s)) (Set.Icc (0 : ℝ) 1) :=
      hC2cont s hs
    have hpos' : ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
        intervalDomainLift (w s) x ≠ 0 :=
      fun x hx => ne_of_gt (hpos s hs x hx)
    simp only [hfdef, logisticSourceFun]
    apply ContinuousOn.mul hgc
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    exact ContinuousOn.rpow_const hgc (fun x hx => Or.inl (hpos' x hx))
  have h_diff : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Set.Icc lo hi,
      HasDerivWithinAt (fun r => f r x) (f' s x) (Set.Icc lo hi) s := by
    intro x hx s hs
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
    have hτmem_s : s - offset ∈ Set.Icc aτ W := hshift hs
    have hfield : HasDerivWithinAt (fun r => intervalDomainLift (w r) x)
        (restartFieldTimeDeriv a₀ a offset s x) (Set.Icc lo hi) s := by
      exact restartField_hasDerivWithinAt_endpoint_shift_window hM₀ ha₀ src
        haτpos hτmem_s hs hshift hagree x hxIcc
    have hpos_s : 0 < intervalDomainLift (w s) x := hpos s hs x hxIcc
    have hchain := logisticSourceFun_hasDerivWithinAt_time (a := p.a) (b := p.b)
      (α := p.α) hα (f := fun r => intervalDomainLift (w r) x)
      (f' := restartFieldTimeDeriv a₀ a offset s x) (σ := s)
      hpos_s hfield
    simp only [hfdef, hf'def, logisticSourceFun, logisticSourceDot]
    exact hchain
  have h_cont_deriv : ContinuousOn (Function.uncurry f')
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1) := by
    have hfieldjoint : ContinuousOn
        (Function.uncurry (fun s x => restartFieldTimeDeriv a₀ a offset s x))
        (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1) :=
      restartFieldTimeDeriv_continuousOn_joint_On_shift hM₀ ha₀ src haτpos hshift
    have hpowjoint : ContinuousOn
        (Function.uncurry (fun s x => (intervalDomainLift (w s) x) ^ p.α))
        (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1) := by
      have hne : ∀ q ∈ Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1,
          intervalDomainLift (w q.1) q.2 ≠ 0 := by
        intro q hq
        obtain ⟨hq1, hq2⟩ := Set.mem_prod.1 hq
        exact ne_of_gt (hpos q.1 hq1 q.2 hq2)
      exact ContinuousOn.rpow_const hprofile_joint (fun q hq => Or.inl (hne q hq))
    simp only [hf'def, logisticSourceDot]
    change ContinuousOn (fun q : ℝ × ℝ =>
        restartFieldTimeDeriv a₀ a offset q.1 q.2 *
          (p.a - p.b * (1 + p.α) *
            (intervalDomainLift (w q.1) q.2) ^ p.α)) _
    exact hfieldjoint.mul
      ((continuousOn_const).sub (continuousOn_const.mul hpowjoint))
  have hkey :=
    ShenWork.IntervalMildPicardRegularityEndpoint2.cosineCoeffs_hasDerivWithinAt_of_smooth_param
      (f := f) (f' := f') (a' := lo) (W := hi) (n := k)
      hlohi hσ hf_cont h_diff h_cont_deriv
  simpa only [hfdef, hf'def] using hkey

end ShenWork.IntervalPicardIterateTimeC1Endpoint
