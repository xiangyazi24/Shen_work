import ShenWork.Paper2.IntervalDomainPositiveWindowK1OnEndpoint
import ShenWork.Paper2.IntervalPicardIterateRepresentation
import ShenWork.Paper2.IntervalPicardIterateTimeC1EndpointAdot

/-!
# Level-0 heat-slice source `TimeC1On`

This file builds the Path-B base case on a positive closed time window.  The
field is the homogeneous heat slice
`picardIter p u₀ 0 σ = S(σ)(lift u₀)`, so its time derivative is the explicit
heat derivative `unitIntervalCosineHeatSecondValue`.

The final producer keeps the non-heat window data as hypotheses: positivity,
supremum/C2 bounds, and a uniform bound on the explicit heat time-derivative
field.  These are the cone/tower window facts; no global `hsrc0` or
`DuhamelSourceTimeC1` is consumed.
-/

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalDuhamelClosedC2
  (unitIntervalCosineHeatValue_hasDerivAt_time)
open ShenWork.IntervalDomainRegularityBootstrap
  (unitIntervalCosineHeatSecondValue)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun logisticLifted_eq_logisticSourceFun_on_Icc
   cosineCoeffs_abs_le_of_continuous_bounded)
open ShenWork.IntervalMildPicardRegularityEndpoint2
  (cosineCoeffs_hasDerivWithinAt_of_smooth_param)
open ShenWork.IntervalPicardIterateTimeC1Endpoint
  (logisticSourceFun_hasDerivWithinAt_time)
open ShenWork.IntervalPicardIterateRepresentation
  (iterateReprCoeff hbsum_zero hagree_zero)
open ShenWork.IntervalDomainLimitSourceRepresentationOn
  (limitSource_duhamelSourceTimeC1On_of_representation)
open ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
  (cosineCoeffs_continuousOn_of_jointContinuousOn_Icc)
open ShenWork.IntervalSpectralSubtypeAdapter
  (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont)
open ShenWork.IntervalSemigroupComposition
  (cosineCoeffs_unitIntervalCosineHeatValue)
open ShenWork.IntervalSemigroupNeumann
  (unitIntervalCosineHeatValue_continuousOn_Ioi_prod
   unitIntervalCosineHeatSecondValue_continuousOn_Ioi_prod)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)

noncomputable section

namespace ShenWork.IntervalPicardLevel0SourceTimeC1On

local notation "λ_" n => unitIntervalCosineEigenvalue n

abbrev heatCoeff (u₀ : intervalDomainPoint → ℝ) : ℕ → ℝ :=
  cosineCoeffs (intervalDomainLift u₀)

def heatSourceDot (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (σ x : ℝ) : ℝ :=
  unitIntervalCosineHeatSecondValue σ (heatCoeff u₀) x *
    (p.a - p.b * (1 + p.α) *
      (intervalDomainLift (picardIter p u₀ 0 σ) x) ^ p.α)

def heatSourceMdot (p : CM2Params) (M Udot : ℝ) : ℝ :=
  2 * (p.a + p.b * (1 + p.α) * M ^ p.α) * Udot

theorem heatCoeff_hasDerivAt
    (u₀ : intervalDomainPoint → ℝ) (k : ℕ) (σ : ℝ) :
    HasDerivAt
      (fun r : ℝ => Real.exp (-r * (λ_ k)) * heatCoeff u₀ k)
      (-(λ_ k) * (Real.exp (-σ * (λ_ k)) * heatCoeff u₀ k)) σ := by
  have hexp : HasDerivAt (fun r : ℝ => Real.exp (-r * (λ_ k)))
      (-(λ_ k) * Real.exp (-σ * (λ_ k))) σ := by
    have hlin : HasDerivAt (fun r : ℝ => -r * (λ_ k)) (-(λ_ k)) σ := by
      have hneg : HasDerivAt (fun r : ℝ => -r) (-1 : ℝ) σ := by
        simpa using (hasDerivAt_id σ).neg
      simpa [mul_comm] using hneg.mul_const (λ_ k)
    simpa [mul_comm] using hlin.exp
  have h := hexp.mul_const (heatCoeff u₀ k)
  convert h using 1
  ring

theorem heatSlice_profile_eq_heatValue
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {σ x M₀ : ℝ} (hσ : 0 < σ) (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalDomainLift (picardIter p u₀ 0 σ) x =
      unitIntervalCosineHeatValue σ (heatCoeff u₀) x := by
  have hlift : intervalDomainLift (picardIter p u₀ 0 σ) x =
      intervalFullSemigroupOperator σ (intervalDomainLift u₀) x := by
    simp only [intervalDomainLift, picardIter, dif_pos hx]
  rw [hlift]
  exact intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
    hσ hu₀_cont hu₀_bound hx

theorem heatSliceCoeff_eq_damped
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {σ M₀ : ℝ} (hσ : 0 < σ) (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀) (k : ℕ) :
    cosineCoeffs (intervalDomainLift (picardIter p u₀ 0 σ)) k =
      Real.exp (-σ * (λ_ k)) * heatCoeff u₀ k := by
  have hcongr :
      cosineCoeffs (intervalDomainLift (picardIter p u₀ 0 σ)) k =
        cosineCoeffs
          (fun x => unitIntervalCosineHeatValue σ (heatCoeff u₀) x) k :=
    cosineCoeffs_congr_on_Icc
      (fun x hx =>
        heatSlice_profile_eq_heatValue p hσ hu₀_cont hu₀_bound hx) k
  rw [hcongr]
  exact cosineCoeffs_unitIntervalCosineHeatValue hσ hu₀_bound k

theorem heatSliceCoeff_hasDerivWithinAt
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T σ M₀ : ℝ} (hc : 0 < c) (hσ : σ ∈ Set.Icc c T)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀) (k : ℕ) :
    HasDerivWithinAt
      (fun r : ℝ => cosineCoeffs
        (intervalDomainLift (picardIter p u₀ 0 r)) k)
      (-(λ_ k) * (Real.exp (-σ * (λ_ k)) * heatCoeff u₀ k))
      (Set.Icc c T) σ := by
  have hdamp := (heatCoeff_hasDerivAt u₀ k σ).hasDerivWithinAt
    (s := Set.Icc c T)
  refine hdamp.congr_of_mem ?_ ?_
  · intro r hr
    exact heatSliceCoeff_eq_damped p
      (lt_of_lt_of_le hc hr.1) hu₀_cont hu₀_bound k
  · exact hσ

theorem heatSlice_field_hasDerivWithinAt
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T σ x M₀ : ℝ} (hc : 0 < c) (hσ : σ ∈ Set.Icc c T)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt
      (fun r : ℝ => intervalDomainLift (picardIter p u₀ 0 r) x)
      (unitIntervalCosineHeatSecondValue σ (heatCoeff u₀) x)
      (Set.Icc c T) σ := by
  have hσpos : 0 < σ := lt_of_lt_of_le hc hσ.1
  have hheat :=
    (unitIntervalCosineHeatValue_hasDerivAt_time hσpos hu₀_bound
      (x := x)).hasDerivWithinAt (s := Set.Icc c T)
  refine hheat.congr_of_mem ?_ ?_
  · intro r hr
    exact heatSlice_profile_eq_heatValue p
      (lt_of_lt_of_le hc hr.1) hu₀_cont hu₀_bound hx
  · exact hσ

theorem heatSlice_profile_jointContinuousOn
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M₀ : ℝ} (hc : 0 < c) (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀) :
    ContinuousOn
      (Function.uncurry
        (fun σ x => intervalDomainLift (picardIter p u₀ 0 σ) x))
      (Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hheat := unitIntervalCosineHeatValue_continuousOn_Ioi_prod hu₀_bound
  have hcont : ContinuousOn
      (fun q : ℝ × ℝ => unitIntervalCosineHeatValue q.1 (heatCoeff u₀) q.2)
      (Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1) := by
    refine hheat.mono ?_
    intro q hq
    obtain ⟨hσ, _hx⟩ := Set.mem_prod.mp hq
    exact Set.mem_prod.mpr ⟨lt_of_lt_of_le hc hσ.1, Set.mem_univ _⟩
  refine hcont.congr ?_
  intro q hq
  exact heatSlice_profile_eq_heatValue p
    (lt_of_lt_of_le hc (Set.mem_prod.mp hq).1.1)
    hu₀_cont hu₀_bound (Set.mem_prod.mp hq).2

theorem heatSlice_secondValue_jointContinuousOn
    {u₀ : intervalDomainPoint → ℝ} {c T M₀ : ℝ} (hc : 0 < c)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀) :
    ContinuousOn
      (fun q : ℝ × ℝ =>
        unitIntervalCosineHeatSecondValue q.1 (heatCoeff u₀) q.2)
      (Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hsecond :=
    unitIntervalCosineHeatSecondValue_continuousOn_Ioi_prod hu₀_bound
  refine hsecond.mono ?_
  intro q hq
  obtain ⟨hσ, _hx⟩ := Set.mem_prod.mp hq
  exact Set.mem_prod.mpr ⟨lt_of_lt_of_le hc hσ.1, Set.mem_univ _⟩

theorem heatSourceDot_jointContinuousOn
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M₀ : ℝ} (hc : 0 < c) (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ 0 σ) x) :
    ContinuousOn
      (Function.uncurry (fun σ x => heatSourceDot p u₀ σ x))
      (Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hsecond := heatSlice_secondValue_jointContinuousOn (u₀ := u₀)
    (c := c) (T := T) hc hu₀_bound
  have hprofile := heatSlice_profile_jointContinuousOn p
    (c := c) (T := T) hc hu₀_cont hu₀_bound
  have hpow : ContinuousOn
      (fun q : ℝ × ℝ =>
        (intervalDomainLift (picardIter p u₀ 0 q.1) q.2) ^ p.α)
      (Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.rpow_const hprofile
    intro q hq
    obtain ⟨hσ, hx⟩ := Set.mem_prod.mp hq
    exact Or.inl (ne_of_gt (hpos q.1 hσ q.2 hx))
  simpa [heatSourceDot, Function.uncurry] using
    hsecond.mul
      ((continuousOn_const).sub (continuousOn_const.mul hpow))

theorem heatSourceCoeff_hasDerivWithinAt
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T σ M₀ : ℝ} (hc : 0 < c) (hσ : σ ∈ Set.Icc c T)
    (hαpos : 0 < p.α) (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ τ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ 0 τ) x)
    (k : ℕ) :
    HasDerivWithinAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α
          (intervalDomainLift (picardIter p u₀ 0 r))) k)
      (cosineCoeffs (heatSourceDot p u₀ σ) k)
      (Set.Icc c T) σ := by
  have hcT : c ≤ T := le_trans hσ.1 hσ.2
  have hprofile := heatSlice_profile_jointContinuousOn p
    (c := c) (T := T) hc hu₀_cont hu₀_bound
  have hf_cont : ∀ τ ∈ Set.Icc c T,
      ContinuousOn
        (logisticSourceFun p.a p.b p.α
          (intervalDomainLift (picardIter p u₀ 0 τ)))
        (Set.Icc (0 : ℝ) 1) := by
    intro τ hτ
    have hslice : ContinuousOn
        (fun x => intervalDomainLift (picardIter p u₀ 0 τ) x)
        (Set.Icc (0 : ℝ) 1) := by
      exact hprofile.comp (continuousOn_const.prodMk continuousOn_id)
        (fun x hx => Set.mem_prod.mpr ⟨hτ, hx⟩)
    have hne : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift (picardIter p u₀ 0 τ) x ≠ 0 :=
      fun x hx => ne_of_gt (hpos τ hτ x hx)
    unfold logisticSourceFun
    exact hslice.mul
      (continuousOn_const.sub
        (continuousOn_const.mul
          (ContinuousOn.rpow_const hslice (fun x hx => Or.inl (hne x hx)))))
  have h_diff : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ τ ∈ Set.Icc c T,
      HasDerivWithinAt
        (fun r =>
          logisticSourceFun p.a p.b p.α
            (intervalDomainLift (picardIter p u₀ 0 r)) x)
        (heatSourceDot p u₀ τ x) (Set.Icc c T) τ := by
    intro x hx τ hτ
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
    have hfield := heatSlice_field_hasDerivWithinAt p
      (c := c) (T := T) hc hτ hu₀_cont hu₀_bound hxIcc
    have hchain := logisticSourceFun_hasDerivWithinAt_time
      (a := p.a) (b := p.b) (α := p.α) hαpos
      (f := fun r => intervalDomainLift (picardIter p u₀ 0 r) x)
      (f' := unitIntervalCosineHeatSecondValue τ (heatCoeff u₀) x)
      (σ := τ) (hpos τ hτ x hxIcc) hfield
    simpa [logisticSourceFun, heatSourceDot] using hchain
  have hdotcont := heatSourceDot_jointContinuousOn p
    (c := c) (T := T) hc hu₀_cont hu₀_bound hpos
  exact cosineCoeffs_hasDerivWithinAt_of_smooth_param
    (f := fun τ => logisticSourceFun p.a p.b p.α
      (intervalDomainLift (picardIter p u₀ 0 τ)))
    (f' := heatSourceDot p u₀)
    (a' := c) (W := T) (n := k) hcT hσ hf_cont h_diff hdotcont

theorem heatSourceCoeff_continuousOn
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M₀ : ℝ} (hc : 0 < c) (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ 0 σ) x) (k : ℕ) :
    ContinuousOn (fun σ => cosineCoeffs (heatSourceDot p u₀ σ) k)
      (Set.Icc c T) :=
  cosineCoeffs_continuousOn_of_jointContinuousOn_Icc (c := c) (T := T) k
    (heatSourceDot_jointContinuousOn p hc hu₀_cont hu₀_bound hpos)

theorem heatSourceCoeff_abs_le
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M M₀ Udot σ : ℝ} (hc : 0 < c) (hα : 1 ≤ p.α)
    (ha : 0 ≤ p.a) (hb : 0 ≤ p.b) (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ τ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ 0 τ) x)
    (hub : ∀ τ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ 0 τ) x ≤ M)
    (hUdot : ∀ τ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |unitIntervalCosineHeatSecondValue τ (heatCoeff u₀) x| ≤ Udot)
    (hσ : σ ∈ Set.Icc c T) (k : ℕ) :
    |cosineCoeffs (heatSourceDot p u₀ σ) k| ≤ heatSourceMdot p M Udot := by
  have hMnn : 0 ≤ M := by
    have hp := hpos σ hσ 0 (by constructor <;> norm_num)
    have hu := hub σ hσ 0 (by constructor <;> norm_num)
    linarith
  have hUnn : 0 ≤ Udot :=
    le_trans (abs_nonneg _)
      (hUdot σ hσ 0 (by constructor <;> norm_num))
  set Bfac : ℝ := p.a + p.b * (1 + p.α) * M ^ p.α with hBfacdef
  have hBfac_nn : 0 ≤ Bfac := by
    have hαnn : 0 ≤ p.α := le_trans zero_le_one hα
    have h1α : 0 ≤ 1 + p.α := by linarith
    have hpow : 0 ≤ M ^ p.α := Real.rpow_nonneg hMnn p.α
    have hterm : 0 ≤ p.b * (1 + p.α) * M ^ p.α :=
      mul_nonneg (mul_nonneg hb h1α) hpow
    rw [hBfacdef]
    exact add_nonneg ha hterm
  have hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |heatSourceDot p u₀ σ x| ≤ Bfac * Udot := by
    intro x hx
    have hfactor :
        |p.a - p.b * (1 + p.α) *
          (intervalDomainLift (picardIter p u₀ 0 σ) x) ^ p.α| ≤ Bfac := by
      rw [hBfacdef]
      exact ShenWork.IntervalPicardIterateTimeC1.logisticDerivFactor_abs_le
        hα ha hb (hpos σ hσ x hx) (hub σ hσ x hx)
    rw [heatSourceDot, abs_mul]
    calc |unitIntervalCosineHeatSecondValue σ (heatCoeff u₀) x| *
          |p.a - p.b * (1 + p.α) *
            (intervalDomainLift (picardIter p u₀ 0 σ) x) ^ p.α|
        ≤ Udot * Bfac :=
          mul_le_mul (hUdot σ hσ x hx) hfactor (abs_nonneg _) hUnn
      _ = Bfac * Udot := by ring
  have hdot_cont : ContinuousOn (heatSourceDot p u₀ σ)
      (Set.Icc (0 : ℝ) 1) := by
    have hdot_joint := heatSourceDot_jointContinuousOn p
      (c := c) (T := T) hc hu₀_cont hu₀_bound hpos
    exact hdot_joint.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => Set.mem_prod.mpr ⟨hσ, hx⟩)
  have hcoeff := cosineCoeffs_abs_le_of_continuous_bounded
    hdot_cont (mul_nonneg hBfac_nn hUnn) hsup k
  calc |cosineCoeffs (heatSourceDot p u₀ σ) k|
      ≤ 2 * (Bfac * Udot) := hcoeff
    _ = heatSourceMdot p M Udot := by
      rw [heatSourceMdot, hBfacdef]
      ring

noncomputable def level0Source_timeC1On
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M G1 G2 Udot M₀ : ℝ}
    (hc : 0 < c) (hcT : c < T)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (picardIter p u₀ 0 σ) x)
    (hub : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (picardIter p u₀ 0 σ) x ≤ M)
    (hG1 : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (picardIter p u₀ 0 σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (picardIter p u₀ 0 σ))) x| ≤ G2)
    (hUdot : ∀ σ ∈ Set.Icc c T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |unitIntervalCosineHeatSecondValue σ (heatCoeff u₀) x| ≤ Udot) :
    DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ 0 s)) k)
      c T := by
  have hαpos : 0 < p.α := lt_of_lt_of_le one_pos hα
  exact limitSource_duhamelSourceTimeC1On_of_representation
    p (picardIter p u₀ 0) hα ha hb hcT.le
    (iterateReprCoeff p u₀ 0)
    (fun σ hσ =>
      hbsum_zero p u₀ (lt_of_lt_of_le hc hσ.1) hu₀_bound)
    (fun σ hσ =>
      hagree_zero p u₀ (lt_of_lt_of_le hc hσ.1)
        hu₀_cont hu₀_bound)
    hpos hub hG1 hG2
    (fun σ k => cosineCoeffs (heatSourceDot p u₀ σ) k)
    (fun σ hσ k =>
      heatSourceCoeff_hasDerivWithinAt p hc hσ hαpos
        hu₀_cont hu₀_bound hpos k)
    (fun k =>
      heatSourceCoeff_continuousOn p hc hu₀_cont hu₀_bound hpos k)
    (fun σ hσ k =>
      heatSourceCoeff_abs_le p hc hα ha hb hu₀_cont hu₀_bound
        hpos hub hUdot hσ k)

/-- The shifted-window form consumed by the tower's `σ = T` restart branch. -/
noncomputable def level0Source_shiftedTimeC1On
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {σ M G1 G2 Udot M₀ : ℝ}
    (hσ : 0 < σ)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ τ ∈ Set.Icc (σ / 2) σ,
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        0 < intervalDomainLift (picardIter p u₀ 0 τ) x)
    (hub : ∀ τ ∈ Set.Icc (σ / 2) σ,
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift (picardIter p u₀ 0 τ) x ≤ M)
    (hG1 : ∀ τ ∈ Set.Icc (σ / 2) σ,
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (intervalDomainLift (picardIter p u₀ 0 τ)) x| ≤ G1)
    (hG2 : ∀ τ ∈ Set.Icc (σ / 2) σ,
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (deriv (intervalDomainLift (picardIter p u₀ 0 τ))) x| ≤ G2)
    (hUdot : ∀ τ ∈ Set.Icc (σ / 2) σ,
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |unitIntervalCosineHeatSecondValue τ (heatCoeff u₀) x| ≤ Udot) :
    DuhamelSourceTimeC1On
      (fun s k =>
        cosineCoeffs (logisticLifted p (picardIter p u₀ 0 (σ / 2 + s))) k)
      0 (σ / 2) := by
  have hhalf : 0 < σ / 2 := by positivity
  have hhalfσ : σ / 2 < σ := by linarith
  have hphys : DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ 0 s)) k)
      (σ / 2) σ :=
    level0Source_timeC1On p hhalf hhalfσ hα ha hb
      hu₀_cont hu₀_bound hpos hub hG1 hG2 hUdot
  have hsum : σ / 2 + σ / 2 = σ := by ring
  have hphys' : DuhamelSourceTimeC1On
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ 0 s)) k)
      (σ / 2) (σ / 2 + σ / 2) := by
    rw [hsum]
    exact hphys
  simpa [add_comm] using
    ShenWork.IntervalDuhamelSourceTimeC1On.DuhamelSourceTimeC1On.shift_zero
      (offset := σ / 2) (W := σ / 2) hphys'

#print axioms level0Source_timeC1On
#print axioms level0Source_shiftedTimeC1On

end ShenWork.IntervalPicardLevel0SourceTimeC1On
