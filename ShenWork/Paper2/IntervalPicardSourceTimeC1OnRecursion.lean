import ShenWork.Paper2.IntervalPicardIterateTimeC1EndpointAdot
import ShenWork.Paper2.IntervalDomainLimitSourceRepresentationOn
import ShenWork.Paper2.IntervalDomainPositiveWindowK1OnEndpoint
import ShenWork.Paper2.IntervalPicardLevel0SourceTimeC1On

/-!
# Endpoint-inclusive source `TimeC1On` recursion

This file records the Path-B recursion step in the endpoint-inclusive `On` form.
The step is deliberately local: it consumes the shifted predecessor source package
and the restart/field facts that the tower carries on the closed window, and it
produces the successor logistic-source package on that same closed window.
-/

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun cosineCoeffs_abs_le_of_continuous_bounded)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalDomainLimitSourceRepresentationOn
  (limitSource_duhamelSourceTimeC1On_of_representation)
open ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
  (cosineCoeffs_continuousOn_of_jointContinuousOn_Icc)
open ShenWork.IntervalPicardIterateTimeC1
  (logisticSourceDot restartFieldTimeDeriv)
open ShenWork.IntervalPicardIterateTimeC1Endpoint
  (logisticSource_adot_hasDerivWithinAt_endpoint_window)
open ShenWork.IntervalPicardIterateTimeC1JointEndpoint
  (restartFieldTimeDeriv_continuousOn_joint_On_shift)

noncomputable section

namespace ShenWork.IntervalPicardSourceTimeC1OnRecursion

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-- Joint continuity of the successor source-derivative slice assembled from a
shifted predecessor `TimeC1On` source and a closed-window restart representation. -/
theorem logisticSourceDot_continuousOn_joint_On_shift
    {p : CM2Params}
    {w : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀)
    (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} {offset W lo hi aτ : ℝ}
    (src : DuhamelSourceTimeC1On a 0 W)
    (haτpos : 0 < aτ)
    (hshift : Set.MapsTo (fun s : ℝ => s - offset)
      (Set.Icc lo hi) (Set.Icc aτ W))
    (hpos : ∀ s ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (w s) x)
    (hprofile_joint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (w s) x))
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn
      (Function.uncurry (fun s x => logisticSourceDot a₀ a p w offset s x))
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hfieldjoint : ContinuousOn
      (Function.uncurry
        (fun s x => restartFieldTimeDeriv a₀ a offset s x))
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1) :=
    restartFieldTimeDeriv_continuousOn_joint_On_shift
      hM₀ ha₀ src haτpos hshift
  have hpowjoint : ContinuousOn
      (fun q : ℝ × ℝ => (intervalDomainLift (w q.1) q.2) ^ p.α)
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.rpow_const hprofile_joint
    intro q hq
    obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
    exact Or.inl (ne_of_gt (hpos q.1 hq1 q.2 hq2))
  simp only [logisticSourceDot]
  change ContinuousOn (fun q : ℝ × ℝ =>
      restartFieldTimeDeriv a₀ a offset q.1 q.2 *
        (p.a - p.b * (1 + p.α) *
          (intervalDomainLift (w q.1) q.2) ^ p.α)) _
  exact hfieldjoint.mul
    ((continuousOn_const).sub (continuousOn_const.mul hpowjoint))

/-- A compact-window uniform bound for the successor source-derivative
coefficients.  This supplies the `derivBound` field of `DuhamelSourceTimeC1On`. -/
theorem exists_logisticSource_adot_bound_On_shift
    {p : CM2Params}
    {w : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀)
    (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} {offset W lo hi aτ : ℝ}
    (src : DuhamelSourceTimeC1On a 0 W)
    (haτpos : 0 < aτ)
    (hshift : Set.MapsTo (fun s : ℝ => s - offset)
      (Set.Icc lo hi) (Set.Icc aτ W))
    (hpos : ∀ s ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (w s) x)
    (hprofile_joint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (w s) x))
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1)) :
    ∃ Mdot : ℝ, ∀ σ ∈ Set.Icc lo hi, ∀ k,
      |cosineCoeffs (fun x => logisticSourceDot a₀ a p w offset σ x) k|
        ≤ Mdot := by
  classical
  set K : Set (ℝ × ℝ) := Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1 with hKdef
  have hdotjoint : ContinuousOn
      (Function.uncurry (fun s x => logisticSourceDot a₀ a p w offset s x))
      K := by
    simpa [hKdef] using
      logisticSourceDot_continuousOn_joint_On_shift
        hM₀ ha₀ src haτpos hshift hpos hprofile_joint
  have hKcompact : IsCompact K := by
    rw [hKdef]
    exact isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hKcompact.bddAbove_image hdotjoint.norm
  set B' : ℝ := max B 0 with hB'def
  have hB'nn : 0 ≤ B' := le_max_right _ _
  have hbd : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |logisticSourceDot a₀ a p w offset σ x| ≤ B' := by
    intro σ hσ x hx
    have hmem : (σ, x) ∈ K := by
      rw [hKdef]
      exact Set.mem_prod.mpr ⟨hσ, hx⟩
    have hb : ‖Function.uncurry
        (fun s x => logisticSourceDot a₀ a p w offset s x) (σ, x)‖ ≤ B :=
      hB (Set.mem_image_of_mem _ hmem)
    have hBle : B ≤ B' := by
      rw [hB'def]
      exact le_max_left _ _
    simpa [Function.uncurry, Real.norm_eq_abs] using le_trans hb hBle
  refine ⟨2 * B', fun σ hσ k => ?_⟩
  have hsec : ContinuousOn (fun x => logisticSourceDot a₀ a p w offset σ x)
      (Set.Icc (0 : ℝ) 1) := by
    have hmaps : Set.MapsTo (fun x : ℝ => ((σ, x) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) K := by
      intro x hx
      rw [hKdef]
      exact Set.mem_prod.mpr ⟨hσ, hx⟩
    exact hdotjoint.comp (continuousOn_const.prodMk continuousOn_id) hmaps
  exact cosineCoeffs_abs_le_of_continuous_bounded hsec hB'nn
    (fun x hx => hbd σ hσ x hx) k

/-- Endpoint-inclusive successor source package.

The predecessor enters only through the shifted `src : DuhamelSourceTimeC1On a 0 W`.
All remaining assumptions are the satisfiable restart/field facts on the closed
window `[lo, hi]`: representation, positivity, sup/C2 bounds, coefficient-window
shift, and restart agreement. -/
noncomputable def sourceTimeC1On_succ_of_sourceTimeC1On
    {p : CM2Params}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {w : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀)
    (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} {offset W lo hi aτ M G1 G2 : ℝ}
    (src : DuhamelSourceTimeC1On a 0 W)
    (hlohi : lo ≤ hi)
    (haτpos : 0 < aτ)
    (hshift : Set.MapsTo (fun s : ℝ => s - offset)
      (Set.Icc lo hi) (Set.Icc aτ W))
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ ∈ Set.Icc lo hi,
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ ∈ Set.Icc lo hi,
      Set.EqOn (intervalDomainLift (w σ))
        (fun x => ∑' n, bc σ n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (w σ) x)
    (hub : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (w σ) x ≤ M)
    (hG1 : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (w σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (w σ))) x| ≤ G2)
    (hrestart : ∀ s ∈ Set.Icc lo hi, ∀ x : intervalDomainPoint,
      intervalDomainLift (w s) x.1 =
        ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n x.1)
    (hC2cont : ∀ s ∈ Set.Icc lo hi,
      ContinuousOn (intervalDomainLift (w s)) (Set.Icc (0 : ℝ) 1))
    (hprofile_joint : ContinuousOn
      (Function.uncurry (fun s x => intervalDomainLift (w s) x))
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1)) :
    DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (w s)) k) lo hi := by
  classical
  let adot : ℝ → ℕ → ℝ :=
    fun σ k => cosineCoeffs (fun x => logisticSourceDot a₀ a p w offset σ x) k
  have hMdot_ex := exists_logisticSource_adot_bound_On_shift
    (p := p) hM₀ ha₀ src haτpos hshift hpos hprofile_joint
  let Mdot : ℝ := Classical.choose hMdot_ex
  have hMdot : ∀ σ ∈ Set.Icc lo hi, ∀ k, |adot σ k| ≤ Mdot := by
    simpa [adot, Mdot] using Classical.choose_spec hMdot_ex
  have hdotjoint : ContinuousOn
      (Function.uncurry (fun s x => logisticSourceDot a₀ a p w offset s x))
      (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1) :=
    logisticSourceDot_continuousOn_joint_On_shift
      (p := p) hM₀ ha₀ src haτpos hshift hpos hprofile_joint
  refine limitSource_duhamelSourceTimeC1On_of_representation
    p w hα ha hb hlohi bc hbsum hagree hpos hub hG1 hG2 adot ?_ ?_ hMdot
  · intro σ hσ k
    have hαpos : 0 < p.α := lt_of_lt_of_le one_pos hα
    exact logisticSource_adot_hasDerivWithinAt_endpoint_window
      hαpos hM₀ ha₀ src haτpos hσ hshift hrestart hpos
      hC2cont hprofile_joint k
  · intro k
    simpa [adot] using
      cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
        (c := lo) (T := hi) k hdotjoint

/-- The level-`n` canonical source package on the positive window `[c,T]`. -/
abbrev LevelSourceTimeC1On
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (n : ℕ) (c T : ℝ) :=
  DuhamelSourceTimeC1On
    (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
    c T

/-- A level source package on every positive lower endpoint, all reaching `T`. -/
abbrev LevelSourceTimeC1OnUpTo
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) (T : ℝ) :=
  ∀ c, 0 < c → c < T → LevelSourceTimeC1On p u₀ n c T

/-- The induction signature for producing all level source packages from a base
case and an endpoint-inclusive successor step. -/
noncomputable def sourceTimeC1On_all_windows_of_base_step
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {T : ℝ}
    (base : LevelSourceTimeC1OnUpTo p u₀ 0 T)
    (step : ∀ n,
      LevelSourceTimeC1OnUpTo p u₀ n T →
        LevelSourceTimeC1OnUpTo p u₀ (n + 1) T) :
    ∀ n, LevelSourceTimeC1OnUpTo p u₀ n T
  | 0 => base
  | n + 1 => step n (sourceTimeC1On_all_windows_of_base_step p u₀ base step n)

#print axioms sourceTimeC1On_succ_of_sourceTimeC1On
#print axioms sourceTimeC1On_all_windows_of_base_step

end ShenWork.IntervalPicardSourceTimeC1OnRecursion
