import ShenWork.Paper3.IntervalDomainMPositiveStripSquareHeat
import ShenWork.Paper3.IntervalDomainMHolderSeedMass
import ShenWork.Paper3.IntervalDomainPositiveTimeHeatKernelFloor
import ShenWork.Paper3.IntervalDomainGlobalTailTimeEquicontinuityM
import ShenWork.Paper3.IntervalDomainPersistenceGeneralMPositiveLogisticPart1

/-!
# Contact-small-ceiling producer for faithful general powers

A non-small terminal value is pulled a fixed short time backwards by the
uniform tail time modulus.  The tail Holder estimate turns it into a seed of
fixed positive mass.  The matched linear square-heat comparison and the
positive-time Neumann kernel floor then give a uniform lower bound for the
whole terminal slice, contradicting contact with a sufficiently small
minimum.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.BFormPositiveDatumNegPart
open ShenWork.IntervalMildPicardThreshold (unitClip)
open ShenWork.IntervalNeumannFullKernel

theorem intervalDomainM_contactSmallCeiling
    (p : CM2Params) (hm : 1 ≤ p.m)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    IntervalDomainMContactSmallCeiling u := by
  intro eps heps
  obtain ⟨Th, M, G, hTh, hM, hG, hsup, hholder⟩ :=
    intervalDomainM_globalBounded_eventual_holder p huv
  obtain ⟨Tt, hTt, htime⟩ :=
    intervalDomainM_globalBounded_eventual_time_equi p huv
  obtain ⟨δt, hδt, htimemod⟩ := htime (eps / 2) (by linarith)
  let τ : ℝ := min (δt / 2) (1 / 2)
  have hτ : 0 < τ := lt_min (half_pos hδt) (by norm_num)
  have hτδ : τ < δt := by
    have := min_le_left (δt / 2) (1 / 2 : ℝ)
    linarith
  let T0 : ℝ := max Th Tt + τ
  have hT0 : 0 < T0 := by
    have : 0 < max Th Tt := hTh.trans_le (le_max_left _ _)
    dsimp [T0]
    positivity
  let eta : ℝ := eps / 2
  have heta : 0 < eta := half_pos heps
  let mass0 : ℝ := holderHalfSqrtSeedMassLower eta G
  have hmass0 : 0 < mass0 :=
    holderHalfSqrtSeedMassLower_pos heta hG
  let floor0 : ℝ := positiveTimeWindowHeatKernelFloor τ
  have hfloor0 : 0 < floor0 := positiveTimeWindowHeatKernelFloor_pos hτ
  let E : ℝ := intervalDomainMLinearBarrierDiscount p M
  have hE : 0 ≤ E := intervalDomainMLinearBarrierDiscount_nonneg hm hM.le
  let d : ℝ := Real.exp (-E * (2 * τ)) * (floor0 * mass0) ^ 2
  have hd : 0 < d := by
    dsimp [d]
    exact mul_pos (Real.exp_pos _)
      (sq_pos_of_pos (mul_pos hfloor0 hmass0))
  refine ⟨T0, hT0, d / 2, half_pos hd, ?_⟩
  intro t ht hmin y
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · by_contra hnot
    have hlarge : eps < |intervalDomainLift (u t) y| := lt_of_not_ge hnot
    have htpos : 0 < t := lt_of_lt_of_le hT0 ht
    let X : intervalDomainPoint := ⟨y, hy⟩
    have hHpos : 0 < t + τ + 1 := by positivity
    have hclassNow := huv.classical (t + τ + 1) hHpos
    have hut_pos : 0 < u t X :=
      hclassNow.u_pos' htpos (by linarith)
    have hlargeX : eps < u t X := by
      have hlarge' : eps < |u t X| := by
        simpa [intervalDomainLift, hy, X] using hlarge
      rwa [abs_of_pos hut_pos] at hlarge'
    let s : ℝ := t - τ
    have hsTh : Th ≤ s := by
      dsimp [s, T0] at *
      linarith [le_max_left Th Tt]
    have hsTt : Tt ≤ s := by
      dsimp [s, T0] at *
      linarith [le_max_right Th Tt]
    have htTt : Tt ≤ t := hsTt.trans (by dsimp [s]; linarith)
    have htimeDist : |t - s| < δt := by
      have : t - s = τ := by dsimp [s]; ring
      rw [this, abs_of_pos hτ]
      exact hτδ
    have hback := htimemod s t hsTt htTt htimeDist X
    have hus_eta : eta ≤ u s X := by
      dsimp [eta]
      nlinarith [hlargeX, (abs_lt.mp hback).2]
    have hspos : 0 < s := lt_of_lt_of_le hTh hsTh
    have hholder_s : ∀ x z : intervalDomainPoint,
        |u s x - u s z| ≤ G * |x.1 - z.1| ^ ((1 : ℝ) / 2) :=
      hholder s hsTh
    let L : ℝ := 2 * τ
    have hL : 0 < L := by dsimp [L]; positivity
    let H : ℝ := t + τ + 1
    have hH : 0 < H := by dsimp [H]; positivity
    have hsol : IsPaper2ClassicalSolution intervalDomainM p H u v :=
      huv.classical H hH
    have hsLH : s + L < H := by
      dsimp [s, L, H]
      linarith
    have hu_le : ∀ r ∈ Set.Icc (0 : ℝ) L,
        ∀ x : intervalDomainPoint, u (s + r) x ≤ M := by
      intro r hr x
      have htimeTail : Th ≤ s + r := hsTh.trans (le_add_of_nonneg_right hr.1)
      have htimeMem : s + r ∈ Set.Ioo (0 : ℝ) H := by
        constructor
        · exact lt_of_lt_of_le hTh htimeTail
        · dsimp [H, L, s] at *
          linarith [hr.2]
      have habs := intervalDomainM_abs_lift_le_supNorm hsol htimeMem x.2
      have hlift : intervalDomainLift (u (s + r)) x.1 = u (s + r) x := by
        simp [intervalDomainLift]
      exact (le_abs_self _).trans (by
        rw [← hlift]
        exact habs.trans (hsup (s + r) htimeTail))
    rcases intervalDomainM_classical_positiveStrip_squareHeat_lower
        hm hsol hspos hL hsLH hM.le hu_le hτ with
      ⟨δ, hδ, hδτ, K, f, hf_eq, hf_cont, hseed, hcoeff, hl2, hbar⟩
    have hw_cont : Continuous (u s) :=
      ShenWork.Paper2.IntervalDomainM.solutionSlice_continuous hsol
        ⟨hspos, by dsimp [H, s]; linarith⟩
    have hmass : mass0 ≤ ∫ z, f z ∂(intervalMeasure 1) := by
      rw [hf_eq]
      simpa [mass0, eta] using
        (halfRestartSliceSqrtSeed_integral_lower_of_holder_point
          hw_cont heta hG hholder_s hus_eta)
    have hf_bound : ∀ z, |f z| ≤ Real.sqrt M / 2 := by
      intro z
      have hUle : u s (unitClip z) ≤ M := by
        have hraw := hu_le 0 (by
          constructor
          · norm_num
          · dsimp [L]
            positivity) (unitClip z)
        simpa using hraw
      have hUnn : 0 ≤ u s (unitClip z) :=
        (hsol.u_pos' hspos (by dsimp [H, s]; linarith)).le
      rw [hf_eq]
      change |Real.sqrt (u s (unitClip z)) / 2| ≤ Real.sqrt M / 2
      rw [abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num))]
      exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hUle) (by norm_num)
    have hf_int : Integrable f (intervalMeasure 1) :=
      intervalMeasure_integrable_of_abs_bound hf_cont.aestronglyMeasurable hf_bound
    have hf_nonneg : ∀ z, z ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ f z := by
      intro z hz
      exact hseed.nonneg z hz
    have hheatTime : δ + τ ∈ Set.Icc τ (2 * τ) := by
      constructor <;> linarith
    have hSmass_pos : 0 < floor0 * mass0 := mul_pos hfloor0 hmass0
    have hexp : Real.exp (-E * (2 * τ)) ≤ Real.exp (-E * (δ + τ)) := by
      apply Real.exp_le_exp.mpr
      have hsum : δ + τ ≤ 2 * τ := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hsum hE]
    have hminLower : d ≤ intervalDomainSpatialMin u t := by
      let Hmin := intervalDomainM_generalM_compactMinFamily huv
      rcases Hmin.exists_min t with ⟨z, hz, hzmin⟩
      have hSzfloor : floor0 * (∫ q, f q ∂(intervalMeasure 1)) ≤
          intervalFullSemigroupOperator (δ + τ) f z := by
        simpa [floor0] using
          positiveTimeWindowHeatKernelFloor_mul_integral_le_semigroup
            hτ hheatTime hz hf_int hf_cont.aestronglyMeasurable
            hf_nonneg hf_bound
      have hSzmass : floor0 * mass0 ≤
          intervalFullSemigroupOperator (δ + τ) f z :=
        (mul_le_mul_of_nonneg_left hmass hfloor0.le).trans hSzfloor
      have hSz_nonneg : 0 ≤ intervalFullSemigroupOperator (δ + τ) f z :=
        hSmass_pos.le.trans hSzmass
      have hSqz : (floor0 * mass0) ^ 2 ≤
          (intervalFullSemigroupOperator (δ + τ) f z) ^ 2 :=
        (sq_le_sq₀ hSmass_pos.le hSz_nonneg).2 hSzmass
      have hdzbar : d ≤ squareHeatBarrier E f (δ + τ) z := by
        unfold squareHeatBarrier
        dsimp [d]
        exact mul_le_mul hexp hSqz (sq_nonneg _) (Real.exp_nonneg _)
      have hbarz := hbar τ z hτ (by dsimp [L]; linarith) hz
      have htime : s + τ = t := by dsimp [s]; ring
      have hclampMin : classicalClampField u t z =
          intervalDomainSpatialMin u t := by
        rw [classicalClampField_eq_lift (u := u) (t := t) hz]
        simpa [intervalDomainActualLinearDanskinF, htpos] using hzmin
      have hbarz' : squareHeatBarrier E f (δ + τ) z ≤
          classicalClampField u t z := by
        simpa [E, htime] using hbarz
      exact hdzbar.trans (hbarz'.trans_eq hclampMin)
    linarith
  · simp [intervalDomainLift, hy, heps.le]

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomainM_contactSmallCeiling
