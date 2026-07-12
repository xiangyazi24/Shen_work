import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergyA2
import ShenWork.Paper2.IntervalChiNegUniformCoreComplete
import ShenWork.PDE.P3MoserEnergyContinuity
open Set MeasureTheory
open scoped Topology
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalMildPicard (HasContinuousSlices)
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
noncomputable section
namespace ShenWork.Paper2.BFormPositiveDatumNegPart

lemma negativePart_le_of_neg_lt {r η : ℝ} (hη : 0 ≤ η) (hr : -η < r) :
    negativePart r ≤ η := by
  by_cases hnonneg : 0 ≤ r
  · simp [negativePart_eq_zero_of_nonneg hnonneg, hη]
  · rw [negativePart_eq_neg_of_nonpos (le_of_lt (lt_of_not_ge hnonneg))]
    linarith

theorem negativePart_sq_integrable_of_continuous_bound
    {w : intervalDomainPoint → ℝ} {R : ℝ}
    (hwcont : Continuous w) (hR : 0 ≤ R) (hwbound : ∀ x, |w x| ≤ R) :
    Integrable (fun x => (negativePartLift w x) ^ 2) (intervalMeasure 1) := by
  have hlift_cont :
      ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) :=
    intervalDomain_lift_continuousOn_Icc_of_continuous hwcont
  have hneg_cont :
      ContinuousOn (fun x => (negativePartLift w x) ^ 2)
        (Set.Icc (0 : ℝ) 1) := by
    have hneg :
        ContinuousOn (negativePartLift w) (Set.Icc (0 : ℝ) 1) :=
      negativePart_continuous.continuousOn.comp hlift_cont
        (fun _ _ => Set.mem_univ _)
    exact hneg.pow 2
  refine ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound (M := R ^ 2)
    (hneg_cont.aestronglyMeasurable measurableSet_Icc) ?_
  intro y
  have hlift_bound : |intervalDomainLift w y| ≤ R := by
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · simpa [intervalDomainLift, hy] using hwbound ⟨y, hy⟩
    · simp [intervalDomainLift, hy, hR]
  have hneg_bound : |negativePartLift w y| ≤ R :=
    (negativePart_abs_le_abs (intervalDomainLift w y)).trans hlift_bound
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hneg_bound 2

theorem negativePartEnergy_initial_vanishes_of_trace_nonneg
    {T R : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hu₀_adm : intervalDomain.initialAdmissible u₀)
    (hu₀_nonneg : ∀ x : intervalDomainPoint, 0 ≤ u₀ x)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hcont : HasContinuousSlices T u)
    (hR : 0 ≤ R)
    (hbound : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint, |u t x| ≤ R) :
    ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
      negativePartEnergy u s < ε := by
  intro ε hε
  let η : ℝ := min 1 (ε / 2)
  have hη_pos : 0 < η := lt_min (by norm_num) (by linarith)
  have hη_nonneg : 0 ≤ η := hη_pos.le
  have hη_le_one : η ≤ 1 := min_le_left _ _
  have hη_le_eps2 : η ≤ ε / 2 := min_le_right _ _
  have hη_sq_lt : η ^ 2 < ε := by
    have hsq_le : η ^ 2 ≤ η := by nlinarith
    nlinarith
  obtain ⟨δ, hδ, hsmall⟩ := InitialTrace.eventually_small htrace hη_pos
  refine ⟨δ, hδ, ?_⟩
  intro s hs hsδ hsT
  have hsTle : s ≤ T := le_of_lt hsT
  have hs_point : ∀ x : intervalDomainPoint, |u s x - u₀ x| < η := by
    have hus_bdd : BddAbove (Set.range (fun x : intervalDomainPoint => |u s x|)) :=
      ⟨R, by
        rintro _ ⟨x, rfl⟩
        exact hbound s hs hsTle x⟩
    have hdiff_bdd :
        BddAbove (Set.range (fun x : intervalDomainPoint => |u s x - u₀ x|)) :=
      bddAbove_abs_sub_of_bddAbove_abs hus_bdd hu₀_adm.1
    exact intervalDomain_pointwise_abs_lt_of_supNorm_lt
      hdiff_bdd (hsmall s hs hsδ)
  have hdens_int :
      Integrable (fun x => (negativePartLift (u s) x) ^ 2) (intervalMeasure 1) :=
    negativePart_sq_integrable_of_continuous_bound
      (hcont s hs hsTle) hR (hbound s hs hsTle)
  have hconst_int : Integrable (fun _ : ℝ => η ^ 2) (intervalMeasure 1) :=
    integrable_const _
  have hle_point :
      ∀ y : ℝ, (negativePartLift (u s) y) ^ 2 ≤ η ^ 2 := by
    intro y
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · let x : intervalDomainPoint := ⟨y, hy⟩
      have hclose := hs_point x
      have hlower : -η < u s x := by
        have hleft := (abs_lt.mp hclose).1
        linarith [hu₀_nonneg x]
      have hneg_le : negativePart (u s x) ≤ η :=
        negativePart_le_of_neg_lt hη_nonneg hlower
      have hsq : (negativePart (u s x)) ^ 2 ≤ η ^ 2 :=
        pow_le_pow_left₀ (negativePart_nonneg _) hneg_le 2
      simpa [negativePartLift, intervalDomainLift, hy] using hsq
    · have hηsq_nonneg : 0 ≤ η ^ 2 := sq_nonneg η
      simpa [negativePartLift, intervalDomainLift, hy,
        negativePart_eq_zero_of_nonneg (le_refl (0 : ℝ))] using hηsq_nonneg
  have hle_int :
      negativePartEnergy u s ≤ ∫ _ : ℝ, η ^ 2 ∂ intervalMeasure 1 := by
    exact MeasureTheory.integral_mono hdens_int hconst_int hle_point
  have hconst :
      (∫ _ : ℝ, η ^ 2 ∂ intervalMeasure 1) = η ^ 2 := by
    simpa using
      (ShenWork.IntervalDomain.intervalMeasure_integral_const
        (L := 1) (c := η ^ 2) (by norm_num : (0 : ℝ) ≤ 1))
  linarith

theorem negativePartEnergy_zero_to_pointwise_nonneg_of_continuous
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hcont : HasContinuousSlices T u)
    (hint : ∀ t, 0 < t → t ≤ T →
      Integrable (fun x => (negativePartLift (u t) x) ^ 2) (intervalMeasure 1)) :
    ∀ t, 0 < t → t ≤ T →
      negativePartEnergy u t = 0 → ∀ x : intervalDomainPoint, 0 ≤ u t x := by
  intro t ht htT hzero x
  have hae_nonneg := ae_nonneg_of_negativePartEnergy_eq_zero
    (u := u) (t := t) (hint t ht htT) hzero
  have hae_zero :
      negativePartLift (u t) =ᵐ[intervalMeasure 1] fun _ : ℝ => 0 := by
    filter_upwards [hae_nonneg] with y hy
    simp [negativePartLift, negativePart_eq_zero_of_nonneg hy]
  have hlift_cont :
      ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    intervalDomain_lift_continuousOn_Icc_of_continuous (hcont t ht htT)
  have hneg_cont :
      ContinuousOn (negativePartLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    negativePart_continuous.continuousOn.comp hlift_cont
      (fun _ _ => Set.mem_univ _)
  have heqOn :
      Set.EqOn (negativePartLift (u t)) (fun _ : ℝ => 0)
        (Set.Icc (0 : ℝ) 1) := by
    refine MeasureTheory.Measure.eqOn_of_ae_eq
      (μ := volume) (s := Set.Icc (0 : ℝ) 1) ?_ hneg_cont continuousOn_const ?_
    · simpa [intervalMeasure, ShenWork.IntervalDomain.intervalSet] using hae_zero
    · rw [interior_Icc, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  have hxzero := heqOn x.2
  have hneg_zero : negativePart (u t x) = 0 := by
    simpa [negativePartLift, intervalDomainLift, x.2] using hxzero
  exact negativePart_eq_zero_iff.mp hneg_zero

structure TruncatedPicardNegativePartEnergyA3Data
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ} (T : ℝ) (E' : ℝ → ℝ) where
  R : ℝ
  hR : 0 ≤ R
  hcont : HasContinuousSlices T (truncatedConjugatePicardLimit p u₀ T)
  hbound : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    |truncatedConjugatePicardLimit p u₀ T t x| ≤ R
  hu₀_adm : intervalDomain.initialAdmissible u₀
  hu₀_nonneg : ∀ x : intervalDomainPoint, 0 ≤ u₀ x
  htrace : InitialTrace intervalDomain u₀ (truncatedConjugatePicardLimit p u₀ T)
  energy_cont :
    ContinuousOn (negativePartEnergy (truncatedConjugatePicardLimit p u₀ T))
      (Set.Icc (0 : ℝ) T)
  energy_has_deriv :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (negativePartEnergy (truncatedConjugatePicardLimit p u₀ T))
        (E' t) (Set.Ici t) t

def TruncatedPicardNegativePartEnergyA3Data.energyIntegrable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ} {E' : ℝ → ℝ}
    (H : TruncatedPicardNegativePartEnergyA3Data p (u₀ := u₀) T E') :
    ∀ t, 0 < t → t ≤ T →
      Integrable (fun x =>
        (negativePartLift (truncatedConjugatePicardLimit p u₀ T t) x) ^ 2)
        (intervalMeasure 1) := by
  intro t ht htT
  exact negativePart_sq_integrable_of_continuous_bound
    (H.hcont t ht htT) H.hR (H.hbound t ht htT)

def TruncatedPicardNegativePartEnergyA3Data.toCoreRegularDataFor
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ} {E' : ℝ → ℝ}
    (Hweak : ∀ t, 0 < t → t < T →
      NegativePartWeakTestIdentityAt p (truncatedConjugatePicardLimit p u₀ T) t)
    (HA2 : TruncatedPicardNegativePartEnergyEstimateA2Data p (u₀ := u₀) T E')
    (HA3 : TruncatedPicardNegativePartEnergyA3Data p (u₀ := u₀) T E') :
    NegativePartEnergyCoreRegularDataFor p T
      (truncatedConjugatePicardLimit p u₀ T) where
  weak_test := Hweak
  ell := p.a
  hell_nonneg := p.ha
  E' := E'
  estimate := HA2.toEstimate
  energy_cont := HA3.energy_cont
  energy_has_deriv := HA3.energy_has_deriv
  energy_integrable := HA3.energyIntegrable
  initial_vanishes :=
    negativePartEnergy_initial_vanishes_of_trace_nonneg HA3.hu₀_adm
      HA3.hu₀_nonneg HA3.htrace HA3.hcont HA3.hR HA3.hbound
  zero_energy_to_pointwise_nonneg :=
    negativePartEnergy_zero_to_pointwise_nonneg_of_continuous
      HA3.hcont HA3.energyIntegrable

end ShenWork.Paper2.BFormPositiveDatumNegPart
