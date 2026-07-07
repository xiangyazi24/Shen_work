/-
  Endpoint-insensitive B-kernel source bridge.

  `IntervalSourceBridgeOpen` removed the false endpoint derivative hypothesis,
  but its global `hB_global` producer still asked for ambient continuity of the
  zero-extended chem-div source.  This file replaces that last closed-endpoint
  source-continuity input by a continuous representative on `[0,1]` agreeing
  with the literal source only on `(0,1)`.
-/
import ShenWork.Paper2.IntervalSourceBridgeOpen
import ShenWork.Paper2.IntervalBankChemSliceFix
import ShenWork.PDE.IntervalSpectralSubtypeAdapter

noncomputable section

namespace ShenWork.Paper2.IntervalSourceBridgeOpen

open MeasureTheory intervalIntegral
open scoped Real
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.IntervalConjugateCosineSeries (intervalSineInner)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs coupledChemDivSourceLift
   chemFluxLifted_endpoint_zero chemFluxLifted_endpoint_one)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalSemigroupComposition (expEigSummable)
open ShenWork.IntervalSpectralSubtypeAdapter
  (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont)
open ShenWork.Paper2.HSigmaScale (lam)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_pos_eq_integral cosineCoeffs_zero_eq_integral)
open ShenWork.Paper2.IntervalDivergenceModeIdentity
  (sineCoeffs sineCoeffs_zero sineCoeffs_pos hasDerivAt_cos_kpi sqrt_lam_eq_kpi)

/-- Normalized open IBP with only interval-integrability of the derivative
representative. -/
theorem cosineCoeffs_deriv_eq_sqrtLambda_sineCoeff_open_integrable
    {Q Q' : ℝ → ℝ} (k : ℕ)
    (hQcont : ContinuousOn Q (Set.Icc (0 : ℝ) 1))
    (hQderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt Q (Q' x) (Set.Ioi x) x)
    (hQ'int : IntervalIntegrable Q' volume 0 1)
    (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0) :
    cosineCoeffs Q' k = Real.sqrt (lam k) * sineCoeffs Q k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [cosineCoeffs_zero_eq_integral, sineCoeffs_zero, mul_zero]
    have hzo : (0 : ℝ) ≤ 1 := by norm_num
    have hint : (∫ x in (0 : ℝ)..1, Q' x) = Q 1 - Q 0 := by
      apply integral_eq_sub_of_hasDeriv_right_of_le hzo hQcont
      · intro x hx
        exact hQderiv x hx
      · exact hQ'int
    rw [hint, hQ0, hQ1, sub_zero]
  · have hkne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
    rw [cosineCoeffs_pos_eq_integral hkne, sineCoeffs_pos hkne, sqrt_lam_eq_kpi]
    have hraw := rawCosCoeff_deriv_eq_kpi_rawSinCoeff_open
      k hQcont hQderiv hQ'int hQ0 hQ1
    have hcomm :
        (∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * Q' x)
          =
        ∫ x in (0 : ℝ)..1, Q' x * Real.cos ((k : ℝ) * Real.pi * x) := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      ring
    have hsincomm :
        (∫ x in (0 : ℝ)..1, Q x * Real.sin ((k : ℝ) * Real.pi * x))
          =
        ∫ x in (0 : ℝ)..1, Real.sin ((k : ℝ) * Real.pi * x) * Q x := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      ring
    rw [hcomm, hraw, hsincomm]
    ring

private theorem sineInner_eq_sineCoeffs_rep (g : ℝ → ℝ) (n : ℕ) :
    intervalSineInner g n
      = ShenWork.Paper2.IntervalDivergenceModeIdentity.sineCoeffs g n := by
  unfold intervalSineInner ShenWork.Paper2.IntervalDivergenceModeIdentity.sineCoeffs
  rfl

private theorem intervalIntegrable_of_continuousOn_Icc {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1)) :
    IntervalIntegrable g volume (0 : ℝ) 1 := by
  exact (by
    rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] :
      ContinuousOn g (Set.uIcc (0 : ℝ) 1)).intervalIntegrable

private theorem heatValue_summand_summable
    {r x M : ℝ} (hr : 0 < r) {a : ℕ → ℝ} (hbound : ∀ n, |a n| ≤ M) :
    Summable (fun n => unitIntervalCosineHeatPointWeight r x n * a n) := by
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hbound 0)
  refine Summable.of_norm_bounded
    (g := fun n => Real.exp (-r * unitIntervalCosineEigenvalue n) * M)
    ((expEigSummable hr).mul_right M) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  unfold unitIntervalCosineHeatPointWeight
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hcos : |unitIntervalCosineMode n x| ≤ 1 := by
    simpa [unitIntervalCosineMode] using Real.abs_cos_le_one ((n : ℝ) * Real.pi * x)
  have hEnn : 0 ≤ Real.exp (-r * unitIntervalCosineEigenvalue n) := (Real.exp_pos _).le
  calc Real.exp (-r * unitIntervalCosineEigenvalue n)
          * |unitIntervalCosineMode n x| * |a n|
      ≤ Real.exp (-r * unitIntervalCosineEigenvalue n) * 1 * M := by
        apply mul_le_mul _ (hbound n) (abs_nonneg _)
          (mul_nonneg hEnn (by norm_num))
        exact mul_le_mul_of_nonneg_left hcos hEnn
    _ = Real.exp (-r * unitIntervalCosineEigenvalue n) * M := by ring

/-- Divergence-mode identity with an endpoint-insensitive continuous
representative for the chem-div source. -/
theorem divMode_of_sliceC1_open_representative
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s : ℝ}
    (hQcont : ContinuousOn (chemFluxLifted p (u s)) (Set.Icc (0 : ℝ) 1))
    (hQderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (chemFluxLifted p (u s))
        (coupledChemDivSourceLift p u s x) (Set.Ioi x) x)
    {Gdiv : ℝ → ℝ}
    (hdiv_rep_cont : ContinuousOn Gdiv (Set.Icc (0 : ℝ) 1))
    (hdiv_rep_eq :
      Set.EqOn (coupledChemDivSourceLift p u s) Gdiv (Set.Ioo (0 : ℝ) 1))
    (n : ℕ) :
    ((n : ℝ) * Real.pi) * intervalSineInner (chemFluxLifted p (u s)) n
      = coupledChemDivSourceCoeffs p u s n := by
  have hQ0 : chemFluxLifted p (u s) 0 = 0 := chemFluxLifted_endpoint_zero p (u s)
  have hQ1 : chemFluxLifted p (u s) 1 = 0 := chemFluxLifted_endpoint_one p (u s)
  have hQderiv_rep : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (chemFluxLifted p (u s)) (Gdiv x) (Set.Ioi x) x := by
    intro x hx
    have hxeq : coupledChemDivSourceLift p u s x = Gdiv x := hdiv_rep_eq hx
    simpa [hxeq] using hQderiv x hx
  have hGint : IntervalIntegrable Gdiv volume (0 : ℝ) 1 :=
    intervalIntegrable_of_continuousOn_Icc hdiv_rep_cont
  have hibp :=
    cosineCoeffs_deriv_eq_sqrtLambda_sineCoeff_open_integrable
      (Q := chemFluxLifted p (u s)) (Q' := Gdiv) n
      hQcont hQderiv_rep hGint hQ0 hQ1
  have hcoeff :
      coupledChemDivSourceCoeffs p u s n = cosineCoeffs Gdiv n := by
    rw [coupledChemDivSourceCoeffs]
    exact ShenWork.Paper2.BankChemSliceFix.cosineCoeffs_congr_on_Ioo
      hdiv_rep_eq n
  rw [hcoeff, hibp, sqrt_lam_eq_kpi, sineInner_eq_sineCoeffs_rep]

/-- Per-slice B-form source bridge with an endpoint-insensitive chem-div
representative instead of ambient source continuity. -/
theorem source_bridge_slice_open_representative
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {s : ℝ}
    (hchem_cont : Continuous (chemFluxLifted p (u s)))
    (hlog_cont : Continuous (logisticLifted p (u s)))
    {Mlog : ℝ}
    (hlog_bound : ∀ n, |cosineCoeffs (logisticLifted p (u s)) n| ≤ Mlog)
    {Mchem : ℝ}
    (hchem_bound : ∀ n, |coupledChemDivSourceCoeffs p u s n| ≤ Mchem)
    (hQderiv : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (chemFluxLifted p (u s))
        (coupledChemDivSourceLift p u s y) (Set.Ioi y) y)
    {Gdiv : ℝ → ℝ}
    (hdiv_rep_cont : ContinuousOn Gdiv (Set.Icc (0 : ℝ) 1))
    (hdiv_rep_eq :
      Set.EqOn (coupledChemDivSourceLift p u s) Gdiv (Set.Ioo (0 : ℝ) 1)) :
    (-p.χ₀) * intervalConjugateKernelOperator r (chemFluxLifted p (u s)) x
        + intervalFullSemigroupOperator r (logisticLifted p (u s)) x
      = unitIntervalCosineHeatValue r (bFormSourceCoeffs p u s) x :=
  ShenWork.Paper2.IntervalChiNegFinalClose.source_bridge_slice_of_divMode
    hr hx hchem_cont hlog_cont hlog_bound hchem_bound
    (divMode_of_sliceC1_open_representative
      hchem_cont.continuousOn hQderiv hdiv_rep_cont hdiv_rep_eq)

/-- Per-slice B-form source bridge with endpoint-insensitive representatives
for the chem-div source and subtype continuity for the logistic source.  This
avoids the false global-continuity requirement for the zero extension
`logisticLifted`. -/
theorem source_bridge_slice_open_representative_subtypeLogistic
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {s : ℝ}
    (hchem_cont : Continuous (chemFluxLifted p (u s)))
    (hlog_cont : Continuous (intervalLogisticSource p (u s)))
    {Mlog : ℝ}
    (hlog_bound : ∀ n, |cosineCoeffs (logisticLifted p (u s)) n| ≤ Mlog)
    {Mchem : ℝ}
    (hchem_bound : ∀ n, |coupledChemDivSourceCoeffs p u s n| ≤ Mchem)
    (hQderiv : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (chemFluxLifted p (u s))
        (coupledChemDivSourceLift p u s y) (Set.Ioi y) y)
    {Gdiv : ℝ → ℝ}
    (hdiv_rep_cont : ContinuousOn Gdiv (Set.Icc (0 : ℝ) 1))
    (hdiv_rep_eq :
      Set.EqOn (coupledChemDivSourceLift p u s) Gdiv (Set.Ioo (0 : ℝ) 1)) :
    (-p.χ₀) * intervalConjugateKernelOperator r (chemFluxLifted p (u s)) x
        + intervalFullSemigroupOperator r (logisticLifted p (u s)) x
      = unitIntervalCosineHeatValue r (bFormSourceCoeffs p u s) x := by
  have hDivMode : ∀ n : ℕ,
      ((n : ℝ) * Real.pi) * intervalSineInner (chemFluxLifted p (u s)) n
        = coupledChemDivSourceCoeffs p u s n :=
    divMode_of_sliceC1_open_representative
      hchem_cont.continuousOn hQderiv hdiv_rep_cont hdiv_rep_eq
  rw [ShenWork.Paper2.IntervalSourceBridgeTest.conjugateKernel_eq_heatValue_divMode
    hr hchem_cont x]
  have hlog_heat :
      intervalFullSemigroupOperator r (logisticLifted p (u s)) x =
        unitIntervalCosineHeatValue r
          (cosineCoeffs (logisticLifted p (u s))) x := by
    simpa [logisticLifted] using
      intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
        (t := r) hr (f := intervalLogisticSource p (u s))
        hlog_cont hlog_bound hx
  rw [hlog_heat]
  unfold unitIntervalCosineHeatValue
  rw [show (fun n => unitIntervalCosineHeatPointWeight r x n *
        (((n : ℝ) * Real.pi) * intervalSineInner (chemFluxLifted p (u s)) n))
      = (fun n => unitIntervalCosineHeatPointWeight r x n *
          coupledChemDivSourceCoeffs p u s n) from
    funext (fun n => by rw [hDivMode n])]
  rw [← tsum_mul_left]
  rw [← Summable.tsum_add
        ((heatValue_summand_summable (M := Mchem) hr hchem_bound).mul_left (-p.χ₀))
        (heatValue_summand_summable (M := Mlog) hr hlog_bound)]
  refine tsum_congr (fun n => ?_)
  change (-p.χ₀) * (unitIntervalCosineHeatPointWeight r x n *
          coupledChemDivSourceCoeffs p u s n)
      + unitIntervalCosineHeatPointWeight r x n *
          cosineCoeffs (logisticLifted p (u s)) n
    = unitIntervalCosineHeatPointWeight r x n * bFormSourceCoeffs p u s n
  change (-p.χ₀) * (unitIntervalCosineHeatPointWeight r x n *
          coupledChemDivSourceCoeffs p u s n)
      + unitIntervalCosineHeatPointWeight r x n *
          coupledLogisticSourceCoeffs p u s n
    = unitIntervalCosineHeatPointWeight r x n * bFormSourceCoeffs p u s n
  unfold bFormSourceCoeffs
  ring

/-- `hB_global` for the conjugate Picard limit from open source-bridge data
using endpoint-insensitive chem-div representatives. -/
theorem conjugatePicardLimit_hB_global_of_open_sourceBridgeRepresentativeData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T M₀ : ℝ}
    (hfix :
      ShenWork.IntervalConjugateDuhamelMap.IntervalConjugateMildSolution
        p T u₀ (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrcB : DuhamelSourceTimeC1
      (bFormSourceCoeffs p
        (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)))
    (hB_int : ∀ t, 0 < t → t ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      IntervalIntegrable
        (fun s : ℝ => intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
        volume 0 t)
    (hlog_int : ∀ t, 0 < t → t ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      IntervalIntegrable
        (fun s : ℝ => intervalFullSemigroupOperator (t - s)
          (logisticLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
        volume 0 t)
    (hchem_cont : ∀ s, 0 < s → s < T →
      Continuous
        (chemFluxLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)))
    (hlog_cont : ∀ s, 0 < s → s < T →
      Continuous
        (logisticLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)))
    (hlog_bound : ∀ s, 0 < s → s < T →
      ∃ Mlog : ℝ, ∀ n,
        |cosineCoeffs
          (logisticLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) n|
          ≤ Mlog)
    (hchem_bound : ∀ s, 0 < s → s < T →
      ∃ Mchem : ℝ, ∀ n,
        |coupledChemDivSourceCoeffs p
          (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s n|
          ≤ Mchem)
    (hQderiv : ∀ s, 0 < s → s < T → ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt
        (chemFluxLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s))
        (coupledChemDivSourceLift p
          (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s y)
        (Set.Ioi y) y)
    (hdiv_rep : ∀ s, 0 < s → s < T →
      ∃ Gdiv : ℝ → ℝ,
        ContinuousOn Gdiv (Set.Icc (0 : ℝ) 1) ∧
        Set.EqOn
          (coupledChemDivSourceLift p
            (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)
          Gdiv (Set.Ioo (0 : ℝ) 1)) :
    ∀ t, 0 < t → t ≤ T →
      Set.EqOn
        (intervalDomainLift
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t))
        (fun x => ∑' n,
          localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
            (bFormSourceCoeffs p
              (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
            t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1) := by
  intro t ht htT x hx
  exact
    ShenWork.IntervalConjugateCosineSeries.conjugatePicardLimit_cosineSeries
      (p := p) (u₀ := u₀) (T := T) (t := t) (x := x) (M₀ := M₀)
      hfix ht htT hx hu₀_cont hu₀_bound hsrcB
      (hB_int t ht htT x hx)
      (hlog_int t ht htT x hx)
      (fun s hs => by
        have hsT : s < T := lt_of_lt_of_le hs.2 htT
        obtain ⟨Mlog, hMlog⟩ := hlog_bound s hs.1 hsT
        obtain ⟨Mchem, hMchem⟩ := hchem_bound s hs.1 hsT
        obtain ⟨Gdiv, hGcont, hGeq⟩ := hdiv_rep s hs.1 hsT
        exact source_bridge_slice_open_representative
          (p := p)
          (u := ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)
          (r := t - s) (x := x) (s := s)
          (sub_pos.mpr hs.2) hx
          (hchem_cont s hs.1 hsT)
          (hlog_cont s hs.1 hsT)
          (Mlog := Mlog) hMlog
          (Mchem := Mchem) hMchem
          (hQderiv s hs.1 hsT)
          (Gdiv := Gdiv) hGcont hGeq)

/-- `hB_global` for the conjugate Picard limit from endpoint-safe open
source-bridge data.  This version removes both false ambient-continuity
requirements: chem-div is supplied by an `Icc` representative and the logistic
source is continuous as a subtype profile. -/
theorem conjugatePicardLimit_hB_global_of_open_sourceBridgeRepresentativeSubtypeLogisticData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T M₀ : ℝ}
    (hfix :
      ShenWork.IntervalConjugateDuhamelMap.IntervalConjugateMildSolution
        p T u₀ (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrcB : DuhamelSourceTimeC1
      (bFormSourceCoeffs p
        (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)))
    (hB_int : ∀ t, 0 < t → t ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      IntervalIntegrable
        (fun s : ℝ => intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
        volume 0 t)
    (hlog_int : ∀ t, 0 < t → t ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      IntervalIntegrable
        (fun s : ℝ => intervalFullSemigroupOperator (t - s)
          (logisticLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
        volume 0 t)
    (hchem_cont : ∀ s, 0 < s → s < T →
      Continuous
        (chemFluxLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)))
    (hlog_cont : ∀ s, 0 < s → s < T →
      Continuous
        (intervalLogisticSource p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)))
    (hlog_bound : ∀ s, 0 < s → s < T →
      ∃ Mlog : ℝ, ∀ n,
        |cosineCoeffs
          (logisticLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) n|
          ≤ Mlog)
    (hchem_bound : ∀ s, 0 < s → s < T →
      ∃ Mchem : ℝ, ∀ n,
        |coupledChemDivSourceCoeffs p
          (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s n|
          ≤ Mchem)
    (hQderiv : ∀ s, 0 < s → s < T → ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt
        (chemFluxLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s))
        (coupledChemDivSourceLift p
          (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s y)
        (Set.Ioi y) y)
    (hdiv_rep : ∀ s, 0 < s → s < T →
      ∃ Gdiv : ℝ → ℝ,
        ContinuousOn Gdiv (Set.Icc (0 : ℝ) 1) ∧
        Set.EqOn
          (coupledChemDivSourceLift p
            (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)
          Gdiv (Set.Ioo (0 : ℝ) 1)) :
    ∀ t, 0 < t → t ≤ T →
      Set.EqOn
        (intervalDomainLift
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t))
        (fun x => ∑' n,
          localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
            (bFormSourceCoeffs p
              (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
            t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1) := by
  intro t ht htT x hx
  exact
    ShenWork.IntervalConjugateCosineSeries.conjugatePicardLimit_cosineSeries
      (p := p) (u₀ := u₀) (T := T) (t := t) (x := x) (M₀ := M₀)
      hfix ht htT hx hu₀_cont hu₀_bound hsrcB
      (hB_int t ht htT x hx)
      (hlog_int t ht htT x hx)
      (fun s hs => by
        have hsT : s < T := lt_of_lt_of_le hs.2 htT
        obtain ⟨Mlog, hMlog⟩ := hlog_bound s hs.1 hsT
        obtain ⟨Mchem, hMchem⟩ := hchem_bound s hs.1 hsT
        obtain ⟨Gdiv, hGcont, hGeq⟩ := hdiv_rep s hs.1 hsT
        exact source_bridge_slice_open_representative_subtypeLogistic
          (p := p)
          (u := ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)
          (r := t - s) (x := x) (s := s)
          (sub_pos.mpr hs.2) hx
          (hchem_cont s hs.1 hsT)
          (hlog_cont s hs.1 hsT)
          (Mlog := Mlog) hMlog
          (Mchem := Mchem) hMchem
          (hQderiv s hs.1 hsT)
          (Gdiv := Gdiv) hGcont hGeq)

#print axioms divMode_of_sliceC1_open_representative
#print axioms source_bridge_slice_open_representative
#print axioms source_bridge_slice_open_representative_subtypeLogistic
#print axioms conjugatePicardLimit_hB_global_of_open_sourceBridgeRepresentativeData
#print axioms conjugatePicardLimit_hB_global_of_open_sourceBridgeRepresentativeSubtypeLogisticData

end ShenWork.Paper2.IntervalSourceBridgeOpen
