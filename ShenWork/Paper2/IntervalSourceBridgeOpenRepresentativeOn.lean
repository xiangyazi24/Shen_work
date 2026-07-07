/-
  Windowed/constant-extension B-form global cosine producer.

  This is the bank-shaped analogue of
  `IntervalSourceBridgeOpenRepresentative`: the B-form source regularity is
  only required on `[0,T]`, and the initial datum is only required to be
  continuous on the interval subtype.  The latter avoids the false global
  continuity assumption on the zero extension `intervalDomainLift u₀`.
-/
import ShenWork.Paper2.IntervalSourceBridgeOpenRepresentative
import ShenWork.PDE.IntervalDuhamelSpectralEqCosineSeriesOn
import ShenWork.PDE.IntervalSpectralSubtypeAdapter

open MeasureTheory Set Filter Topology
open scoped Topology

noncomputable section

namespace ShenWork.IntervalConjugateCosineSeries

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (IntervalConjugateMildSolution intervalConjugateKernelOperator
   intervalConjugateDuhamelMap)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalSpectralSubtypeAdapter
  (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont)
open ShenWork.CosineSpectrum (cosineMode)

/-- B-form Duhamel-map cosine series from a window-local source package and
subtype-continuity of the initial datum. -/
theorem intervalConjugateDuhamelMap_cosineSeries_on_constInit
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {T t x M₀ : ℝ}
    (ht : 0 < t) (htT : t ≤ T) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrcB_on : DuhamelSourceTimeC1On (bFormSourceCoeffs p u) 0 T)
    (hB_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p (u s)) x) volume 0 t)
    (hlog_int : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s)
        (logisticLifted p (u s)) x) volume 0 t)
    (hsource_bridge : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      (-p.χ₀) * intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (u s)) x
        + intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x
        = unitIntervalCosineHeatValue (t - s) (bFormSourceCoeffs p u s) x) :
    intervalConjugateDuhamelMap p u₀ u t ⟨x, hx⟩ =
      ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p u) t n * cosineMode n x := by
  have hhom : intervalFullSemigroupOperator t (intervalDomainLift u₀) x =
      ∑' n : ℕ,
        (Real.exp (-t * unitIntervalCosineEigenvalue n) *
          cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n x := by
    rw [
      intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
        ht hu₀_cont hu₀_bound hx]
    simpa using congrFun
      (ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatValue_eq_cosineCoeffSeries
        t (cosineCoeffs (intervalDomainLift u₀))) x
  have hsource_eq : (-p.χ₀) *
        (∫ s in (0 : ℝ)..t,
          intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x)
      + ∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x
      = ∫ s in (0 : ℝ)..t,
          unitIntervalCosineHeatValue (t - s) (bFormSourceCoeffs p u s) x := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add (hB_int.const_mul (-p.χ₀)) hlog_int]
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le ht.le]
    have hmem : ∀ᵐ s ∂volume, s ∈ Set.Ioc (0 : ℝ) t → s ∈ Set.Ioo (0 : ℝ) t := by
      have hnull : volume ({t} : Set ℝ) = 0 := by simp
      filter_upwards [(MeasureTheory.compl_mem_ae_iff.mpr hnull)] with s hs hst
      exact ⟨hst.1, lt_of_le_of_ne hst.2 (fun heq => hs (by simp [heq]))⟩
    filter_upwards [hmem] with s hs hsIoc
    exact hsource_bridge s (hs hsIoc)
  rw [intervalConjugateDuhamelMap]
  change (intervalFullSemigroupOperator t (intervalDomainLift u₀) x
      + (-p.χ₀) *
          (∫ s in (0 : ℝ)..t,
            intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x)
      + ∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x)
      = ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p u) t n * cosineMode n x
  rw [hhom]
  rw [add_assoc]
  rw [hsource_eq,
    ShenWork.IntervalDuhamelSpectralEqCosineSeriesOn.duhamelSpectral_eq_cosineSeries_on
      hsrcB_on ht htT]
  have hsum_hom : Summable (fun n : ℕ =>
      (Real.exp (-t * unitIntervalCosineEigenvalue n) *
        cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n x) := by
    have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
    refine Summable.of_norm_bounded
      (g := fun n : ℕ =>
        |Real.exp (-t * unitIntervalCosineEigenvalue n) *
          cosineCoeffs (intervalDomainLift u₀) n|) ?_ (fun n => ?_)
    · refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
        ((ShenWork.IntervalSemigroupComposition.expEigSummable ht).mul_right M₀)
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hu₀_bound n) (Real.exp_pos _).le
    · rw [Real.norm_eq_abs, abs_mul]
      calc |Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n| * |cosineMode n x|
          ≤ |Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n| * 1 := by
              gcongr
              simpa [cosineMode] using
                Real.abs_cos_le_one ((n : ℝ) * Real.pi * x)
        _ = |Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n| := by ring
  have hsum_duh : Summable (fun n : ℕ =>
      duhamelSpectralCoeff (bFormSourceCoeffs p u) t n * cosineMode n x) := by
    refine Summable.of_norm_bounded
      (g := fun n : ℕ => |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n|)
      ?_ (fun n => ?_)
    · refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
        (hsrcB_on.henv_summable.mul_left t)
      unfold duhamelSpectralCoeff
      rw [← Real.norm_eq_abs]
      calc ‖∫ s in (0 : ℝ)..t,
            Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) *
              bFormSourceCoeffs p u s n‖
          ≤ hsrcB_on.envelope n * |t - 0| := by
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro s hs
            rw [Set.uIoc_of_le ht.le] at hs
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
            calc Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) *
                  |bFormSourceCoeffs p u s n|
                ≤ 1 * |bFormSourceCoeffs p u s n| := by
                  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                  rw [Real.exp_le_one_iff]
                  have hts : 0 ≤ t - s := by linarith [hs.2]
                  have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
                    unfold unitIntervalCosineEigenvalue
                    positivity
                  nlinarith [mul_nonneg hts hlam]
              _ = |bFormSourceCoeffs p u s n| := one_mul _
              _ ≤ hsrcB_on.envelope n :=
                  hsrcB_on.henv_bound s
                    ⟨le_of_lt hs.1, le_trans hs.2 htT⟩ n
          _ = t * hsrcB_on.envelope n := by
            rw [sub_zero, abs_of_pos ht]
            ring
    · rw [Real.norm_eq_abs, abs_mul]
      calc |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n| * |cosineMode n x|
          ≤ |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n| * 1 := by
              gcongr
              simpa [cosineMode] using
                Real.abs_cos_le_one ((n : ℝ) * Real.pi * x)
        _ = |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n| := by ring
  rw [← Summable.tsum_add hsum_hom hsum_duh]
  refine tsum_congr (fun n => ?_)
  unfold localRestartCoeff
  ring

/-- Cosine-series form of the conjugate Picard limit from a window-local B-form
source package and subtype-continuous initial datum. -/
theorem conjugatePicardLimit_cosineSeries_on_constInit
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T t x M₀ : ℝ}
    (hfix : IntervalConjugateMildSolution p T u₀
      (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
    (ht : 0 < t) (htT : t ≤ T) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrcB_on : DuhamelSourceTimeC1On
      (bFormSourceCoeffs p
        (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)) 0 T)
    (hB_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
      volume 0 t)
    (hlog_int : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s)
        (logisticLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
      volume 0 t)
    (hsource_bridge : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      (-p.χ₀) * intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x
        + intervalFullSemigroupOperator (t - s)
          (logisticLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x
        = unitIntervalCosineHeatValue (t - s)
          (bFormSourceCoeffs p
            (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s) x) :
    intervalDomainLift
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t) x =
      ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p
            (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
          t n * cosineMode n x := by
  have hpoint :=
    hfix t ht htT ⟨x, hx⟩
  rw [show intervalDomainLift
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t) x =
        (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t ⟨x, hx⟩ by
      simp [intervalDomainLift, hx]]
  rw [hpoint]
  exact intervalConjugateDuhamelMap_cosineSeries_on_constInit
    (p := p) (u₀ := u₀)
    (u := ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)
    (T := T) (t := t) (x := x) (M₀ := M₀)
    ht htT hx hu₀_cont hu₀_bound hsrcB_on hB_int hlog_int hsource_bridge

#print axioms intervalConjugateDuhamelMap_cosineSeries_on_constInit
#print axioms conjugatePicardLimit_cosineSeries_on_constInit

end ShenWork.IntervalConjugateCosineSeries

namespace ShenWork.Paper2.IntervalSourceBridgeOpen

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (IntervalConjugateMildSolution intervalConjugateKernelOperator)
open ShenWork.IntervalConjugatePicard (conjugatePicardLimit)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledChemDivSourceLift)
open ShenWork.CosineSpectrum (cosineMode)

/-- Bank-shaped `hB_global` for the conjugate Picard limit from endpoint-safe
source-bridge data, using only windowed B-form source regularity and subtype
continuity of the initial datum. -/
theorem conjugatePicardLimit_hB_global_of_open_sourceBridgeRepresentativeSubtypeLogisticDataOn
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T M₀ : ℝ}
    (hfix : IntervalConjugateMildSolution p T u₀
      (conjugatePicardLimit p u₀ T))
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrcB_on : DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardLimit p u₀ T)) 0 T)
    (hB_int : ∀ t, 0 < t → t ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      IntervalIntegrable
        (fun s : ℝ => intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p ((conjugatePicardLimit p u₀ T) s)) x)
        volume 0 t)
    (hlog_int : ∀ t, 0 < t → t ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      IntervalIntegrable
        (fun s : ℝ => intervalFullSemigroupOperator (t - s)
          (logisticLifted p ((conjugatePicardLimit p u₀ T) s)) x)
        volume 0 t)
    (hchem_cont : ∀ s, 0 < s → s < T →
      Continuous (chemFluxLifted p ((conjugatePicardLimit p u₀ T) s)))
    (hlog_cont : ∀ s, 0 < s → s < T →
      Continuous (intervalLogisticSource p ((conjugatePicardLimit p u₀ T) s)))
    (hlog_bound : ∀ s, 0 < s → s < T →
      ∃ Mlog : ℝ, ∀ n,
        |cosineCoeffs
          (logisticLifted p ((conjugatePicardLimit p u₀ T) s)) n| ≤ Mlog)
    (hchem_bound : ∀ s, 0 < s → s < T →
      ∃ Mchem : ℝ, ∀ n,
        |coupledChemDivSourceCoeffs p
          (conjugatePicardLimit p u₀ T) s n| ≤ Mchem)
    (hQderiv : ∀ s, 0 < s → s < T → ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt
        (chemFluxLifted p ((conjugatePicardLimit p u₀ T) s))
        (coupledChemDivSourceLift p (conjugatePicardLimit p u₀ T) s y)
        (Set.Ioi y) y)
    (hdiv_rep : ∀ s, 0 < s → s < T →
      ∃ Gdiv : ℝ → ℝ,
        ContinuousOn Gdiv (Set.Icc (0 : ℝ) 1) ∧
        Set.EqOn
          (coupledChemDivSourceLift p (conjugatePicardLimit p u₀ T) s)
          Gdiv (Set.Ioo (0 : ℝ) 1)) :
    ∀ t, 0 < t → t ≤ T →
      Set.EqOn
        (intervalDomainLift ((conjugatePicardLimit p u₀ T) t))
        (fun x => ∑' n,
          localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
            (bFormSourceCoeffs p (conjugatePicardLimit p u₀ T))
            t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1) := by
  intro t ht htT x hx
  exact
    ShenWork.IntervalConjugateCosineSeries.conjugatePicardLimit_cosineSeries_on_constInit
      (p := p) (u₀ := u₀) (T := T) (t := t) (x := x) (M₀ := M₀)
      hfix ht htT hx hu₀_cont hu₀_bound hsrcB_on
      (hB_int t ht htT x hx)
      (hlog_int t ht htT x hx)
      (fun s hs => by
        have hsT : s < T := lt_of_lt_of_le hs.2 htT
        obtain ⟨Mlog, hMlog⟩ := hlog_bound s hs.1 hsT
        obtain ⟨Mchem, hMchem⟩ := hchem_bound s hs.1 hsT
        obtain ⟨Gdiv, hGcont, hGeq⟩ := hdiv_rep s hs.1 hsT
        exact source_bridge_slice_open_representative_subtypeLogistic
          (p := p)
          (u := conjugatePicardLimit p u₀ T)
          (r := t - s) (x := x) (s := s)
          (sub_pos.mpr hs.2) hx
          (hchem_cont s hs.1 hsT)
          (hlog_cont s hs.1 hsT)
          (Mlog := Mlog) hMlog
          (Mchem := Mchem) hMchem
          (hQderiv s hs.1 hsT)
          (Gdiv := Gdiv) hGcont hGeq)

#print axioms conjugatePicardLimit_hB_global_of_open_sourceBridgeRepresentativeSubtypeLogisticDataOn

end ShenWork.Paper2.IntervalSourceBridgeOpen
