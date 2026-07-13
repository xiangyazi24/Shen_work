import ShenWork.Paper2.IntervalBFormSquareHeatT0RestartDerivativeData
import ShenWork.PDE.IntervalFullKernelRegularity
import ShenWork.Paper2.IntervalNegativePartWeakEnergy
import ShenWork.Paper2.IntervalChiNegCloseBaseSeed
import ShenWork.PDE.IntervalSemigroupC1ApproxIdentity

open Filter Topology Set MeasureTheory
open scoped BigOperators Topology

noncomputable section

namespace ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms

open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)

private theorem measurable_tsum_nat {X : Type*} [MeasurableSpace X]
    {f : ℕ → X → ℝ} (hf : ∀ n, Measurable (f n)) :
    Measurable (fun x => ∑' n : ℕ, f n x) := by
  classical
  let L := SummationFilter.unconditional ℕ
  let S : Finset ℕ → X → ℝ := fun s x => ∑ n ∈ s, f n x
  have hS_meas : ∀ s, StronglyMeasurable (S s) := by
    intro s
    exact (Finset.measurable_sum _ (fun n _ => hf n)).stronglyMeasurable
  let C : Set X := {x | ∃ c : ℝ,
    Tendsto (fun s : Finset ℕ => S s x) L.filter (nhds c)}
  have hC_meas : MeasurableSet C := by
    simpa [C] using MeasureTheory.StronglyMeasurable.measurableSet_exists_tendsto
      (l := L.filter) (f := S) hS_meas
  have hlim_meas : Measurable (fun x =>
      L.filter.limUnder (fun s : Finset ℕ => S s x)) :=
    (MeasureTheory.StronglyMeasurable.limUnder (l := L.filter) hS_meas).measurable
  have heq : (fun x => ∑' n : ℕ, f n x) = fun x =>
      if x ∈ C then L.filter.limUnder (fun s : Finset ℕ => S s x) else 0 := by
    funext x
    by_cases hx : x ∈ C
    · simp only [hx, if_true]
      rcases hx with ⟨c, hc⟩
      have hs : Summable (fun n => f n x) := ⟨c, hc⟩
      exact hs.hasSum.limUnder_eq.symm
    · simp only [hx, if_false]
      exact tsum_eq_zero_of_not_summable (fun hs =>
        hx ⟨∑' n, f n x, hs.hasSum⟩)
  rw [heq]
  exact Measurable.ite hC_meas hlim_meas measurable_const

private theorem gradientMajorant_summable
    {K δ : ℝ} (hδ : 0 < δ) :
    Summable (fun n : ℕ =>
      ((n : ℝ) * Real.pi) *
        Real.exp (-δ * ((n : ℝ) * Real.pi) ^ 2) * |K|) := by
  have hr : 0 < δ * Real.pi ^ 2 := mul_pos hδ (sq_pos_of_pos Real.pi_pos)
  have hbase := (Real.summable_pow_mul_exp_neg_nat_mul 1 hr).mul_left
    (Real.pi * |K|)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbase
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · simp [hn0]
    · exact le_self_pow₀ (Nat.one_le_cast.2 hn0) (by norm_num)
  have hexp : Real.exp (-δ * ((n : ℝ) * Real.pi) ^ 2) ≤
      Real.exp (-(δ * Real.pi ^ 2) * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hδπ : 0 ≤ δ * Real.pi ^ 2 := hr.le
    rw [show -δ * ((n : ℝ) * Real.pi) ^ 2 =
      -(δ * Real.pi ^ 2) * (n : ℝ) ^ 2 by ring]
    nlinarith
  calc
    (n : ℝ) * Real.pi * Real.exp (-δ * ((n : ℝ) * Real.pi) ^ 2) * |K|
        ≤ (n : ℝ) * Real.pi *
            Real.exp (-(δ * Real.pi ^ 2) * (n : ℝ)) * |K| := by
          gcongr
    _ = Real.pi * |K| *
        ((n : ℝ) ^ 1 * Real.exp (-(δ * Real.pi ^ 2) * (n : ℝ))) := by
          ring

theorem cosineHeatGradientValue_continuousOn_Ici
    {f : ℝ → ℝ} {K δ : ℝ} (hδ : 0 < δ)
    (hK : ∀ n, |cosineCoeffs f n| ≤ K) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        unitIntervalCosineHeatGradientValue p.1 (cosineCoeffs f) p.2)
      (Set.Ici δ ×ˢ Set.univ) := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg (cosineCoeffs f 0)) (hK 0)
  have hterm : ∀ n : ℕ, Continuous (fun p : ℝ × ℝ =>
      unitIntervalCosineHeatGradientPointWeight p.1 p.2 n *
        cosineCoeffs f n) := by
    intro n
    change Continuous (fun p : ℝ × ℝ =>
      Real.exp (-p.1 * unitIntervalCosineEigenvalue n) *
        (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * p.2)) *
          cosineCoeffs f n)
    fun_prop
  apply continuousOn_tsum
    (fun n => (hterm n).continuousOn)
    (gradientMajorant_summable (K := K) hδ)
  intro n p hp
  rw [Real.norm_eq_abs, abs_mul]
  have ht : δ ≤ p.1 := hp.1
  have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
    dsimp [unitIntervalCosineEigenvalue]
    positivity
  have hexp : Real.exp (-p.1 * unitIntervalCosineEigenvalue n) ≤
      Real.exp (-δ * unitIntervalCosineEigenvalue n) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hweight :
      |unitIntervalCosineHeatGradientPointWeight p.1 p.2 n| ≤
        (n : ℝ) * Real.pi *
          Real.exp (-δ * ((n : ℝ) * Real.pi) ^ 2) := by
    rw [unitIntervalCosineHeatGradientPointWeight, abs_mul,
      abs_of_nonneg (Real.exp_nonneg _), abs_mul, abs_neg,
      abs_mul, abs_of_nonneg (Nat.cast_nonneg n), abs_of_pos Real.pi_pos]
    calc
      Real.exp (-p.1 * unitIntervalCosineEigenvalue n) *
          ((n : ℝ) * Real.pi * |Real.sin ((n : ℝ) * Real.pi * p.2)|)
          ≤ Real.exp (-δ * unitIntervalCosineEigenvalue n) *
              ((n : ℝ) * Real.pi * 1) := by
            gcongr
            exact Real.abs_sin_le_one _
      _ = (n : ℝ) * Real.pi *
          Real.exp (-δ * ((n : ℝ) * Real.pi) ^ 2) := by
            dsimp [unitIntervalCosineEigenvalue]
            ring
  calc
    |unitIntervalCosineHeatGradientPointWeight p.1 p.2 n| *
        |cosineCoeffs f n|
      ≤ ((n : ℝ) * Real.pi *
          Real.exp (-δ * ((n : ℝ) * Real.pi) ^ 2)) * K :=
        mul_le_mul hweight (hK n) (abs_nonneg _) (by positivity)
    _ ≤ (n : ℝ) * Real.pi *
          Real.exp (-δ * ((n : ℝ) * Real.pi) ^ 2) * |K| := by
        rw [abs_of_nonneg hK0]

def barrierSpaceDerivRep (M : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  Real.exp (-M * t) *
    (2 * unitIntervalCosineHeatValue t (cosineCoeffs f) x *
      unitIntervalCosineHeatGradientValue t (cosineCoeffs f) x)

def barrierTimeDerivRep (M : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  Real.exp (-M * t) *
    (-M * unitIntervalCosineHeatValue t (cosineCoeffs f) x ^ 2 +
      2 * unitIntervalCosineHeatValue t (cosineCoeffs f) x *
        ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue
          t (cosineCoeffs f) x)

theorem barrierSpaceDerivRep_continuousOn_Ici
    {M : ℝ} {f : ℝ → ℝ} {K δ : ℝ} (hδ : 0 < δ)
    (hK : ∀ n, |cosineCoeffs f n| ≤ K) :
    ContinuousOn (fun p : ℝ × ℝ => barrierSpaceDerivRep M f p.1 p.2)
      (Set.Ici δ ×ˢ Set.univ) := by
  have hsub : Set.Ici δ ×ˢ (Set.univ : Set ℝ) ⊆
      Set.Ioi (0 : ℝ) ×ˢ Set.univ := by
    intro p hp
    exact ⟨hδ.trans_le hp.1, Set.mem_univ _⟩
  have hval : ContinuousOn
      (fun p : ℝ × ℝ =>
        unitIntervalCosineHeatValue p.1 (cosineCoeffs f) p.2)
      (Set.Ici δ ×ˢ Set.univ) :=
    (ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatValue_continuousOn_Ioi_prod
      hK).mono hsub
  have hgrad := cosineHeatGradientValue_continuousOn_Ici hδ hK
  have hexp : ContinuousOn (fun p : ℝ × ℝ => Real.exp (-M * p.1))
      (Set.Ici δ ×ˢ Set.univ) := by fun_prop
  simpa [barrierSpaceDerivRep] using hexp.mul (continuousOn_const.mul hval |>.mul hgrad)

theorem barrierTimeDerivRep_continuousOn_Ioi
    {M : ℝ} {f : ℝ → ℝ} {K : ℝ}
    (hK : ∀ n, |cosineCoeffs f n| ≤ K) :
    ContinuousOn (fun p : ℝ × ℝ => barrierTimeDerivRep M f p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have hval :=
    ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatValue_continuousOn_Ioi_prod
      hK
  have hsecond :=
    ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatSecondValue_continuousOn_Ioi_prod
      hK
  have hexp : ContinuousOn (fun p : ℝ × ℝ => Real.exp (-M * p.1))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by fun_prop
  simpa [barrierTimeDerivRep] using
    hexp.mul ((continuousOn_const.mul (hval.pow 2)).neg.add
      (continuousOn_const.mul hval |>.mul hsecond))

theorem semigroup_space_hasDerivAt_gradientValue
    {t x : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {K : ℝ} (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun y : ℝ => intervalFullSemigroupOperator t f y)
      (unitIntervalCosineHeatGradientValue t (cosineCoeffs f) x) x := by
  have hC2 :=
    ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_contDiff_two_clean
      ht hf hK
  have hbase := (hC2.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0) x).hasDerivAt
  have hderiv : deriv (fun y : ℝ => intervalFullSemigroupOperator t f y) x =
      unitIntervalCosineHeatGradientValue t (cosineCoeffs f) x := by
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    · subst x
      rw [ShenWork.IntervalSemigroupNeumann.intervalFullSemigroupOperator_neumann_at_zero
        ht hf hK,
        ShenWork.IntervalFullKernelRegularity.unitIntervalCosineHeatGradientValue_eq_zero_at_zero]
    · rcases eq_or_lt_of_le hx.2 with hx1 | hx1
      · subst x
        rw [ShenWork.IntervalSemigroupNeumann.intervalFullSemigroupOperator_neumann_at_one
          ht hf hK,
          ShenWork.IntervalFullKernelRegularity.unitIntervalCosineHeatGradientValue_eq_zero_at_one]
      · have hEqOn : Set.EqOn
            (fun y : ℝ => intervalFullSemigroupOperator t f y)
            (fun y : ℝ => unitIntervalCosineHeatValue t (cosineCoeffs f) y)
            (Set.Ioo (0 : ℝ) 1) := by
          intro y hy
          exact
            ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_clean
              ht hf hy
        have hev := Filter.eventuallyEq_of_mem
          (isOpen_Ioo.mem_nhds ⟨hx0, hx1⟩) hEqOn
        rw [hev.deriv_eq]
        exact unitIntervalCosineHeatValue_deriv_of_l2 ht
          ShenWork.HeatKernelGradientEstimates.unitIntervalCosineReciprocalEigenvalueTerm_summable hl2
  simpa [hderiv] using hbase

theorem squareHeatBarrier_space_hasDerivAt_rep
    {M t x : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {K : ℝ} (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun y : ℝ =>
        ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier M f t y)
      (barrierSpaceDerivRep M f t x) x := by
  have hS := semigroup_space_hasDerivAt_gradientValue ht hf hK hl2 hx
  have hsq := hS.mul hS
  have h := hsq.const_mul (Real.exp (-M * t))
  have hSval :=
    ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
      ht hf hK hx
  convert h using 1
  · ext y
    simp [ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier, pow_two]
  · simp [barrierSpaceDerivRep, hSval]
    ring

theorem squareHeatBarrier_time_hasDerivAt_rep
    {M t x : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {K : ℝ} (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun r : ℝ =>
        ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier M f r x)
      (barrierTimeDerivRep M f t x) t := by
  have hcos :=
    ShenWork.IntervalDuhamelClosedC2.unitIntervalCosineHeatValue_hasDerivAt_time
      (r := t) (x := x) ht hK
  have hS : HasDerivAt
      (fun r : ℝ => intervalFullSemigroupOperator r f x)
      (ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue
        t (cosineCoeffs f) x) t := by
    refine hcos.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with r hr
    exact
      ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
        hr hf hK hx
  have hinner : HasDerivAt (fun r : ℝ => -M * r) (-M) t := by
    convert (hasDerivAt_id t).const_mul (-M) using 1 <;> ring
  have hexp : HasDerivAt (fun r : ℝ => Real.exp (-M * r))
      (Real.exp (-M * t) * (-M)) t := by
    convert (Real.hasDerivAt_exp (-M * t)).comp t hinner using 1 <;>
      simp [Function.comp_def] <;> ring
  have h := hexp.mul (hS.mul hS)
  have hSval :=
    ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
      ht hf hK hx
  convert h using 1
  · ext r
    simp [ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier, pow_two]
  · simp [barrierTimeDerivRep, hSval]
    ring

theorem HasDerivWithinAt.tendsto_forwardSlope_Ici
    {E : ℝ → ℝ} {d : ℝ}
    (h : HasDerivWithinAt E d (Set.Ici (0 : ℝ)) 0) :
    Tendsto (fun q : ℝ => q⁻¹ * (E q - E 0))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds d) := by
  have hs := (hasDerivWithinAt_iff_tendsto_slope).1 h
  have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
    ext x
    simp
  rw [hset] at hs
  convert hs using 1
  funext q
  simp [slope]

theorem right_intervalAverage_tendsto
    {F : ℝ → ℝ} {T L : ℝ} (hT : 0 < T)
    (hFint : IntervalIntegrable F volume 0 T)
    (hFmeas : AEStronglyMeasurable F
      (volume.restrict (Set.uIoc (0 : ℝ) T)))
    (hFlim : Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    Tendsto (fun q : ℝ => q⁻¹ * ∫ r in (0 : ℝ)..q, F r)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  classical
  let Fu : ℝ → ℝ := Function.update F 0 L
  have hFu_ae : Fu =ᵐ[volume.restrict (Set.uIoc (0 : ℝ) T)] F := by
    filter_upwards [(Measure.ae_ne volume 0).filter_mono ae_restrict_le] with x hx
    simp [Fu, Function.update_of_ne hx]
  have hFu_meas : AEStronglyMeasurable Fu
      (volume.restrict (Set.uIoc (0 : ℝ) T)) :=
    hFmeas.congr hFu_ae.symm
  have hFu_int : IntervalIntegrable Fu volume 0 T := by
    rw [intervalIntegrable_iff] at hFint ⊢
    apply hFint.congr
    filter_upwards [(Measure.ae_ne volume 0).filter_mono ae_restrict_le] with x hx
    simp [Fu, Function.update_of_ne hx]
  have hFu_cont : ContinuousWithinAt Fu (Set.Ici (0 : ℝ)) 0 := by
    rw [continuousWithinAt_update_same]
    have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
      ext x
      simp
    rwa [hset]
  have hFu_at : StronglyMeasurableAtFilter Fu
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) volume :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem hFu_meas (by
      simpa [Set.uIoc_of_le hT.le] using Ioc_mem_nhdsGT hT)
  have hHderiv : HasDerivWithinAt
      (fun u => ∫ r in T..u, Fu r) L (Set.Ici (0 : ℝ)) 0 := by
    simpa [Fu] using
      (intervalIntegral.integral_hasDerivWithinAt_right
        (s := Set.Ici (0 : ℝ)) (t := Set.Ioi (0 : ℝ))
        hFu_int.symm hFu_at (hFu_cont.mono Set.Ioi_subset_Ici_self))
  have hslope := HasDerivWithinAt.tendsto_forwardSlope_Ici hHderiv
  refine hslope.congr' ?_
  have hsmall : ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0), q < T :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hT)
  filter_upwards [self_mem_nhdsWithin, hsmall] with q hq hqT
  have h0q : IntervalIntegrable Fu volume 0 q := by
    apply IntervalIntegrable.mono_set hFu_int
    rw [Set.uIcc_of_le hq.le, Set.uIcc_of_le hT.le]
    exact Set.Icc_subset_Icc le_rfl hqT.le
  have hadd := intervalIntegral.integral_add_adjacent_intervals hFu_int.symm h0q
  have htail : (∫ r in (0 : ℝ)..q, Fu r) = ∫ r in (0 : ℝ)..q, F r := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(Measure.ae_ne volume 0)] with r hr _hrI
    simp [Fu, Function.update_of_ne hr]
  change q⁻¹ * ((∫ r in T..q, Fu r) - ∫ r in T..0, Fu r) =
    q⁻¹ * ∫ r in (0 : ℝ)..q, F r
  rw [← htail, ← hadd]
  ring

theorem semigroup_dirichletPairing_integrable_tendsto
    {f df φ : ℝ → ℝ} {Cf K Gf Gφ T : ℝ}
    (hT : 0 < T)
    (hf_cont : Continuous f)
    (hCf : 0 ≤ Cf) (hf_bound : ∀ y, |f y| ≤ Cf)
    (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
    (hf_ac : AbsolutelyContinuousOnInterval f 0 1)
    (hGf : 0 ≤ Gf) (hf_deriv_bound : ∀ y, |df y| ≤ Gf)
    (hf_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt f (df y) y)
    (hdf_cont : ContinuousOn df (Set.Icc (0 : ℝ) 1))
    (hdf_zero : df 0 = 0) (hdf_one : df 1 = 0)
    (hGφ : 0 ≤ Gφ) (hφ_deriv_bound : ∀ᵐ y ∂volume, |deriv φ y| ≤ Gφ) :
    let H : ℝ → ℝ := fun r => ∫ x,
      deriv (fun z => intervalFullSemigroupOperator r f z) x * deriv φ x
        ∂ShenWork.IntervalDomain.intervalMeasure 1
    IntervalIntegrable H volume 0 T ∧
      Tendsto H (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∫ x, df x * deriv φ x
          ∂ShenWork.IntervalDomain.intervalMeasure 1)) := by
  let μ := ShenWork.IntervalDomain.intervalMeasure 1
  let H : ℝ → ℝ := fun r => ∫ x,
    deriv (fun z => intervalFullSemigroupOperator r f z) x * deriv φ x ∂μ
  let HS : ℝ → ℝ := fun r => ∫ x,
    unitIntervalCosineHeatGradientValue r (cosineCoeffs f) x * deriv φ x ∂μ
  have hf_meas : AEStronglyMeasurable f μ := by
    simpa [μ] using hf_cont.aestronglyMeasurable
  have hφderiv_μ : ∀ᵐ x ∂μ, |deriv φ x| ≤ Gφ := by
    dsimp [μ, ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet]
    exact hφ_deriv_bound.filter_mono ae_restrict_le
  have hdf_int : IntervalIntegrable df volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hdf_cont
  have hSbound : ∀ r, 0 < r → ∀ x,
      |deriv (fun z => intervalFullSemigroupOperator r f z) x| ≤ Gf := by
    intro r hr x
    exact
      ShenWork.IntervalNeumannFullKernel.abs_deriv_intervalFullSemigroupOperator_le_of_source_deriv_bound
        hr hf_meas hf_bound hf_deriv hdf_int hGf hf_deriv_bound x
  have hHbound : ∀ r, 0 < r → |H r| ≤ Gf * Gφ := by
    intro r hr
    have hprod_int : Integrable
        (fun x => deriv (fun z => intervalFullSemigroupOperator r f z) x * deriv φ x)
        μ := by
      haveI : IsFiniteMeasure μ := by
        dsimp [μ]
        exact ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
      exact Integrable.of_bound
        ((measurable_deriv _).aestronglyMeasurable.mul
          (measurable_deriv φ).aestronglyMeasurable)
        (Gf * Gφ) (by
          filter_upwards [hφderiv_μ] with x hx
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hSbound r hr x) hx (abs_nonneg _) hGf)
    have hconst : Integrable (fun _ : ℝ => Gf * Gφ) μ := integrable_const _
    have hi := MeasureTheory.norm_integral_le_of_norm_le hconst (by
      filter_upwards [hφderiv_μ] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hSbound r hr x) hx (abs_nonneg _) hGf)
    have hmass : μ.real Set.univ = 1 := by
      dsimp [μ, ShenWork.IntervalDomain.intervalMeasure,
        ShenWork.IntervalDomain.intervalSet]
      rw [measureReal_restrict_apply_univ, measureReal_def, Real.volume_Icc]
      simp
    rw [Real.norm_eq_abs, MeasureTheory.integral_const, hmass, one_smul] at hi
    simpa [H] using hi
  have hSG_meas : Measurable (fun p : ℝ × ℝ =>
      unitIntervalCosineHeatGradientValue p.1 (cosineCoeffs f) p.2) := by
    apply measurable_tsum_nat
    intro n
    change Measurable (fun p : ℝ × ℝ =>
      Real.exp (-p.1 * unitIntervalCosineEigenvalue n) *
        (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * p.2)) *
          cosineCoeffs f n)
    fun_prop
  have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      unitIntervalCosineHeatGradientValue p.1 (cosineCoeffs f) p.2 *
        deriv φ p.2) (volume.prod μ) :=
    hSG_meas.aestronglyMeasurable.mul
      (((measurable_deriv φ).comp measurable_snd).aestronglyMeasurable)
  have hHS_meas : AEStronglyMeasurable HS volume := by
    exact MeasureTheory.AEStronglyMeasurable.integral_prod_right' hjoint
  have hH_eq_HS : ∀ r, 0 < r → H r = HS r := by
    intro r hr
    apply integral_congr_ae
    simp only [μ, ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet]
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [(semigroup_space_hasDerivAt_gradientValue hr hf_cont hK hl2 hx).deriv]
  have hHS_int : IntegrableOn HS (Set.Ioc (0 : ℝ) T) volume := by
    apply Integrable.of_bound
      (hHS_meas.mono_measure Measure.restrict_le_self)
      (Gf * Gφ)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [← hH_eq_HS r hr.1, Real.norm_eq_abs]
    exact hHbound r hr.1
  have hHint : IntervalIntegrable H volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    apply hHS_int.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact (hH_eq_HS r hr.1).symm
  have happrox :=
    ShenWork.IntervalSemigroupC1ApproxIdentity.initialLegC1Approx_of_sourceIBP_continuousOn_zero
      hf_meas hf_bound hf_deriv hdf_cont hdf_zero hdf_one
  have hpoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun r => deriv (fun z => intervalFullSemigroupOperator r f z) x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (df x)) := by
    intro x hx
    rw [Metric.tendsto_nhds]
    intro ε hε
    rcases happrox ε hε with ⟨δ, hδ, haδ⟩
    have hsmall : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), r < δ :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hδ)
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrδ
    simpa [Real.dist_eq] using haδ r hr hrδ x hx
  have hFmeas : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0),
      AEStronglyMeasurable
        (fun x => deriv (fun z => intervalFullSemigroupOperator r f z) x * deriv φ x)
        μ := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (measurable_deriv _).aestronglyMeasurable.mul
      (measurable_deriv φ).aestronglyMeasurable
  have hFbound : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), ∀ᵐ x ∂μ,
      ‖deriv (fun z => intervalFullSemigroupOperator r f z) x * deriv φ x‖ ≤
        Gf * Gφ := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    filter_upwards [hφderiv_μ] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hSbound r hr x) hx (abs_nonneg _) hGf
  have hFlim : ∀ᵐ x ∂μ,
      Tendsto
        (fun r => deriv (fun z => intervalFullSemigroupOperator r f z) x * deriv φ x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (df x * deriv φ x)) := by
    simp only [μ, ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet]
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (hpoint x hx).mul_const (deriv φ x)
  have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => Gf * Gφ) hFmeas hFbound (integrable_const _) hFlim
  exact ⟨hHint, by simpa [H, μ] using hlim⟩

theorem semigroup_deriv_sub_abs_le_of_source_deriv_diff
    {f g df dg : ℝ → ℝ} {r D Cf Cg : ℝ} (hr : 0 < r)
    (hf_meas : AEStronglyMeasurable f
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hg_meas : AEStronglyMeasurable g
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hCf : 0 ≤ Cf) (hf_bound : ∀ y, |f y| ≤ Cf)
    (hCg : 0 ≤ Cg) (hg_bound : ∀ y, |g y| ≤ Cg)
    (hf_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt f (df y) y)
    (hg_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt g (dg y) y)
    (hdf_int : IntervalIntegrable df volume 0 1)
    (hdg_int : IntervalIntegrable dg volume 0 1)
    (hD : 0 ≤ D) (hdiff : ∀ y, |df y - dg y| ≤ D) (x : ℝ) :
    |deriv (fun z => intervalFullSemigroupOperator r f z) x -
        deriv (fun z => intervalFullSemigroupOperator r g z) x| ≤ D := by
  let μ := ShenWork.IntervalDomain.intervalMeasure 1
  have hsub_meas : AEStronglyMeasurable (fun y => f y - g y) μ := by
    simpa [μ] using hf_meas.sub hg_meas
  have hsub_bound : ∀ y, |f y - g y| ≤ Cf + Cg := by
    intro y
    exact (abs_sub _ _).trans (add_le_add (hf_bound y) (hg_bound y))
  have hsub_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun z => f z - g z) (df y - dg y) y := by
    intro y hy
    exact (hf_deriv y hy).sub (hg_deriv y hy)
  have hbound_sub :=
    ShenWork.IntervalNeumannFullKernel.abs_deriv_intervalFullSemigroupOperator_le_of_source_deriv_bound
      hr hsub_meas hsub_bound hsub_deriv (hdf_int.sub hdg_int) hD hdiff x
  have hKf : ∀ z, Integrable
      (fun y => ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel r z y * f y)
      μ := by
    intro z
    have hbdd : ∀ᵐ y ∂μ, ‖f y‖ ≤ Cf :=
      Filter.Eventually.of_forall fun y => by
        simpa [Real.norm_eq_abs] using hf_bound y
    exact
      ((ShenWork.IntervalNeumannFullKernel.continuousOn_intervalNeumannFullKernel_snd
        hr z).integrableOn_Icc).mul_bdd hf_meas hbdd
  have hKg : ∀ z, Integrable
      (fun y => ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel r z y * g y)
      μ := by
    intro z
    have hbdd : ∀ᵐ y ∂μ, ‖g y‖ ≤ Cg :=
      Filter.Eventually.of_forall fun y => by
        simpa [Real.norm_eq_abs] using hg_bound y
    exact
      ((ShenWork.IntervalNeumannFullKernel.continuousOn_intervalNeumannFullKernel_snd
        hr z).integrableOn_Icc).mul_bdd hg_meas hbdd
  have hdf :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
      hr hf_meas hf_bound x
  have hdg :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
      hr hg_meas hg_bound x
  have hlin := ShenWork.IntervalGradDuhamelBound.intervalFullSemigroupOperator_deriv_sub
    hKf hKg hdf.differentiableAt hdg.differentiableAt
  rw [hlin] at hbound_sub
  exact hbound_sub

/-- Pairing version of the derivative contraction estimate.  The interval
measure has total mass one, so a uniform source-derivative difference gives
the same uniform pairing bound up to the test derivative envelope. -/
theorem semigroup_dirichletPairing_sub_abs_le_of_source_deriv_diff
    {f g df dg φ : ℝ → ℝ} {r D Cf Cg Gf Gg Gφ : ℝ} (hr : 0 < r)
    (hf_meas : AEStronglyMeasurable f
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hg_meas : AEStronglyMeasurable g
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hCf : 0 ≤ Cf) (hf_bound : ∀ y, |f y| ≤ Cf)
    (hCg : 0 ≤ Cg) (hg_bound : ∀ y, |g y| ≤ Cg)
    (hf_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt f (df y) y)
    (hg_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt g (dg y) y)
    (hdf_int : IntervalIntegrable df volume 0 1)
    (hdg_int : IntervalIntegrable dg volume 0 1)
    (hGf : 0 ≤ Gf) (hdf_bound : ∀ y, |df y| ≤ Gf)
    (hGg : 0 ≤ Gg) (hdg_bound : ∀ y, |dg y| ≤ Gg)
    (hD : 0 ≤ D) (hdiff : ∀ y, |df y - dg y| ≤ D)
    (hGφ : 0 ≤ Gφ) (hφ_bound : ∀ᵐ y ∂volume, |deriv φ y| ≤ Gφ) :
    |(∫ x,
        deriv (fun z => intervalFullSemigroupOperator r f z) x * deriv φ x
          ∂ShenWork.IntervalDomain.intervalMeasure 1) -
      ∫ x,
        deriv (fun z => intervalFullSemigroupOperator r g z) x * deriv φ x
          ∂ShenWork.IntervalDomain.intervalMeasure 1| ≤ D * Gφ := by
  let μ := ShenWork.IntervalDomain.intervalMeasure 1
  have hφμ : ∀ᵐ x ∂μ, |deriv φ x| ≤ Gφ := by
    dsimp [μ, ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet]
    exact hφ_bound.filter_mono ae_restrict_le
  have hfS : ∀ x,
      |deriv (fun z => intervalFullSemigroupOperator r f z) x| ≤ Gf := by
    intro x
    exact
      ShenWork.IntervalNeumannFullKernel.abs_deriv_intervalFullSemigroupOperator_le_of_source_deriv_bound
        hr hf_meas hf_bound hf_deriv hdf_int hGf hdf_bound x
  have hgS : ∀ x,
      |deriv (fun z => intervalFullSemigroupOperator r g z) x| ≤ Gg := by
    intro x
    exact
      ShenWork.IntervalNeumannFullKernel.abs_deriv_intervalFullSemigroupOperator_le_of_source_deriv_bound
        hr hg_meas hg_bound hg_deriv hdg_int hGg hdg_bound x
  have hfprod : Integrable
      (fun x => deriv (fun z => intervalFullSemigroupOperator r f z) x *
        deriv φ x) μ := by
    haveI : IsFiniteMeasure μ := by
      dsimp [μ]
      exact ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
    exact Integrable.of_bound
      ((measurable_deriv _).aestronglyMeasurable.mul
        (measurable_deriv φ).aestronglyMeasurable)
      (Gf * Gφ) (by
        filter_upwards [hφμ] with x hx
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hfS x) hx (abs_nonneg _) hGf)
  have hgprod : Integrable
      (fun x => deriv (fun z => intervalFullSemigroupOperator r g z) x *
        deriv φ x) μ := by
    haveI : IsFiniteMeasure μ := by
      dsimp [μ]
      exact ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
    exact Integrable.of_bound
      ((measurable_deriv _).aestronglyMeasurable.mul
        (measurable_deriv φ).aestronglyMeasurable)
      (Gg * Gφ) (by
        filter_upwards [hφμ] with x hx
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hgS x) hx (abs_nonneg _) hGg)
  have hdiffS : ∀ x,
      |deriv (fun z => intervalFullSemigroupOperator r f z) x -
        deriv (fun z => intervalFullSemigroupOperator r g z) x| ≤ D := by
    intro x
    exact semigroup_deriv_sub_abs_le_of_source_deriv_diff hr
      hf_meas hg_meas hCf hf_bound hCg hg_bound hf_deriv hg_deriv
      hdf_int hdg_int hD hdiff x
  have hdom : Integrable (fun _ : ℝ => D * Gφ) μ := integrable_const _
  have hi := MeasureTheory.norm_integral_le_of_norm_le hdom (by
    filter_upwards [hφμ] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hdiffS x) hx (abs_nonneg _) hD)
  have hmass : μ.real Set.univ = 1 := by
    dsimp [μ, ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet]
    rw [measureReal_restrict_apply_univ, measureReal_def, Real.volume_Icc]
    simp
  rw [← MeasureTheory.integral_sub hfprod hgprod]
  rw [Real.norm_eq_abs, MeasureTheory.integral_const, hmass, one_smul] at hi
  have hpoint :
      (∫ x,
        deriv (fun z => intervalFullSemigroupOperator r f z) x * deriv φ x -
          deriv (fun z => intervalFullSemigroupOperator r g z) x * deriv φ x
        ∂μ) =
      ∫ x,
        (deriv (fun z => intervalFullSemigroupOperator r f z) x -
          deriv (fun z => intervalFullSemigroupOperator r g z) x) * deriv φ x
        ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [hpoint]
  exact hi

/-! ## Positive-time squared-barrier slices -/

/-- Spatial regularity data for one strictly positive squared-heat barrier
slice.  The derivative is recorded by the spectral representative used in the
moving-source weak-generator limit below. -/
structure SquareHeatBarrierSliceRegularData
    (M t : ℝ) (f : ℝ → ℝ) : Prop where
  time_pos : 0 < t
  continuous : Continuous
    (fun x =>
      ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier M f t x)
  deriv_rep_continuous : ContinuousOn
    (barrierSpaceDerivRep M f t) (Set.Icc (0 : ℝ) 1)
  hasDerivAt : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    HasDerivAt
      (fun y =>
        ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier M f t y)
      (barrierSpaceDerivRep M f t x) x
  deriv_bounded : ∃ G : ℝ, 0 ≤ G ∧
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |barrierSpaceDerivRep M f t x| ≤ G
  absolutelyContinuous : AbsolutelyContinuousOnInterval
    (fun x =>
      ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier M f t x)
    0 1

/-- Construct the spatial regularity record of a positive squared-heat
barrier slice from the semigroup coefficient bounds. -/
theorem squareHeatBarrierSliceRegularData_of_semigroup
    {M t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf : Continuous f) {Cf K : ℝ} (hCf : 0 ≤ Cf)
    (hf_bound : ∀ y, |f y| ≤ Cf)
    (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2) :
    SquareHeatBarrierSliceRegularData M t f := by
  let w : ℝ → ℝ := fun x =>
    ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier M f t x
  have hf_meas : AEStronglyMeasurable f
      (ShenWork.IntervalDomain.intervalMeasure 1) :=
    hf.aestronglyMeasurable
  have hScont : Continuous
      (fun x => intervalFullSemigroupOperator t f x) :=
    ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
      ht hCf hf_bound hf_meas
  have hwcont : Continuous w := by
    simpa [w, ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier]
      using continuous_const.mul (hScont.pow 2)
  have hrepcont : ContinuousOn (barrierSpaceDerivRep M f t)
      (Set.Icc (0 : ℝ) 1) := by
    have hjoint := barrierSpaceDerivRep_continuousOn_Ici (M := M) ht hK
    have hcomp : Continuous (fun x : ℝ => ((t, x) : ℝ × ℝ)) := by
      fun_prop
    exact hjoint.comp hcomp.continuousOn
      (fun x hx => ⟨Set.mem_Ici.mpr le_rfl, Set.mem_univ x⟩)
  have hhas : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt w (barrierSpaceDerivRep M f t x) x := by
    intro x hx
    simpa [w] using
      squareHeatBarrier_space_hasDerivAt_rep ht hf hK hl2 hx
  obtain ⟨G0, hG0⟩ := isCompact_Icc.bddAbove_image
    hrepcont.abs
  let G : ℝ := max G0 0
  have hG : 0 ≤ G := le_max_right _ _
  have hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |barrierSpaceDerivRep M f t x| ≤ G := by
    intro x hx
    exact (hG0 (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)
  have hlip : LipschitzOnWith ⟨G, hG⟩ w (Set.Icc (0 : ℝ) 1) := by
    apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (convex_Icc (0 : ℝ) 1)
    · intro x hx
      exact (hhas x hx).hasDerivWithinAt
    · intro x hx
      rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mk, Real.norm_eq_abs]
      exact hbound x hx
  have hIcc : Set.Icc (0 : ℝ) 1 = Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num)]
  have hwac : AbsolutelyContinuousOnInterval w 0 1 := by
    rw [hIcc] at hlip
    exact hlip.absolutelyContinuousOnInterval
  exact
    { time_pos := ht
      continuous := by simpa [w] using hwcont
      deriv_rep_continuous := hrepcont
      hasDerivAt := by simpa [w] using hhas
      deriv_bounded := ⟨G, hG, hbound⟩
      absolutelyContinuous := by simpa [w] using hwac }

/-- Global spatial derivative formula for a positive squared-heat barrier.
This kernel-level version is used only to provide a measurable global
dominator to the finite-increment semigroup identity. -/
theorem squareHeatBarrier_space_hasDerivAt_global
    {M t x : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {Cf : ℝ}
    (hf_meas : AEStronglyMeasurable f
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hf_bound : ∀ y, |f y| ≤ Cf) :
    HasDerivAt
      (fun z =>
        ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier M f t z)
      (Real.exp (-M * t) *
        (2 * intervalFullSemigroupOperator t f x *
          deriv (fun z => intervalFullSemigroupOperator t f z) x)) x := by
  have hS :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
      ht hf_meas hf_bound x
  have h := (hS.mul hS).const_mul (Real.exp (-M * t))
  convert h using 1
  · ext z
    simp [ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier, pow_two]
  · rw [hS.deriv]
    ring

/-- Global derivative envelope for a positive squared-heat barrier. -/
theorem squareHeatBarrier_deriv_abs_le_global
    {M t x : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {Cf : ℝ}
    (hCf : 0 ≤ Cf)
    (hf_meas : AEStronglyMeasurable f
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hf_bound : ∀ y, |f y| ≤ Cf) :
    |deriv
      (fun z =>
        ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier M f t z) x| ≤
      Real.exp (-M * t) *
        (2 * Cf *
          (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
            t ^ (-(1 / 2) : ℝ) * Cf)) := by
  have hS :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      ht hCf hf_bound x
  have hdx :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t
      ht hf_meas hf_bound x
  rw [(squareHeatBarrier_space_hasDerivAt_global
    (M := M) ht hf_meas hf_bound).deriv]
  rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (mul_le_mul_of_nonneg_left hS (by norm_num)) hdx
      (abs_nonneg _) (mul_nonneg (by norm_num) hCf))
    (Real.exp_pos _).le

/-- The spatial derivative of the squared-heat barrier varies uniformly in
space when the positive time is moved a small distance to the left. -/
theorem barrierSpaceDerivRep_tendsto_uniform_left
    {M t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {K : ℝ}
    (hK : ∀ n, |cosineCoeffs f n| ≤ K) :
    ∀ ε > 0, ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0),
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |barrierSpaceDerivRep M f (t - q) x -
            barrierSpaceDerivRep M f t x| < ε := by
  intro ε hε
  have hhalf : 0 < t / 2 := half_pos ht
  let Krect : Set (ℝ × ℝ) :=
    Set.Icc (t / 2) t ×ˢ Set.Icc (0 : ℝ) 1
  have hcompact : IsCompact Krect := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => barrierSpaceDerivRep M f p.1 p.2) Krect := by
    exact (barrierSpaceDerivRep_continuousOn_Ici (M := M) hhalf hK).mono
      (fun p hp => ⟨Set.mem_Ici.mpr hp.1.1, Set.mem_univ p.2⟩)
  have hunif := hcompact.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at hunif
  obtain ⟨δ, hδ, hδmap⟩ := hunif ε hε
  have hsmall : ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0),
      q < min (t / 2) δ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Iio_mem_nhds (lt_min hhalf hδ))
  filter_upwards [self_mem_nhdsWithin, hsmall] with q hq hqsmall
  intro x hx
  have hqpos : 0 < q := hq
  have hqhalf : q < t / 2 := hqsmall.trans_le (min_le_left _ _)
  have hqδ : q < δ := hqsmall.trans_le (min_le_right _ _)
  have hp : (t - q, x) ∈ Krect := by
    refine ⟨⟨?_, ?_⟩, hx⟩
    · linarith
    · linarith
  have hpt : (t, x) ∈ Krect := by
    exact ⟨⟨(half_le_self ht.le), le_rfl⟩, hx⟩
  have hdist : dist (t - q, x) (t, x) < δ := by
    simpa [Prod.dist_eq, Real.dist_eq, abs_of_pos hqpos] using And.intro hqδ hδ
  have hout := hδmap (t - q, x) hp (t, x) hpt hdist
  simpa [Real.dist_eq] using hout

/-- Extend the genuine squared-barrier derivative on `[0,1]` by zero.  The
extension is used only as an integration-by-parts representative; all
derivative assertions remain on the closed interval. -/
def barrierSpaceDerivCutoff (M : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  if x ∈ Set.Icc (0 : ℝ) 1 then barrierSpaceDerivRep M f t x else 0

/-- The Dirichlet pairing of the heat flow from one positive squared-barrier
slice is integrable down to lag zero and converges to the slice derivative
pairing. -/
theorem squareHeatBarrier_dirichletPairing_integrable_tendsto
    {M t T : ℝ} (ht : 0 < t) (hT : 0 < T)
    {f : ℝ → ℝ} (hf : Continuous f) {Cf K : ℝ} (hCf : 0 ≤ Cf)
    (hf_bound : ∀ y, |f y| ≤ Cf)
    (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
    {φ : ℝ → ℝ} {Gφ : ℝ} (hGφ : 0 ≤ Gφ)
    (hφ_deriv_bound : ∀ᵐ y ∂volume, |deriv φ y| ≤ Gφ) :
    let w : ℝ → ℝ := fun x =>
      ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier M f t x
    let dw : ℝ → ℝ := barrierSpaceDerivCutoff M f t
    let H : ℝ → ℝ := fun r => ∫ x,
      deriv (fun z => intervalFullSemigroupOperator r w z) x * deriv φ x
        ∂ShenWork.IntervalDomain.intervalMeasure 1
    IntervalIntegrable H volume 0 T ∧
      Tendsto H (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∫ x, dw x * deriv φ x
          ∂ShenWork.IntervalDomain.intervalMeasure 1)) := by
  let w : ℝ → ℝ := fun x =>
    ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier M f t x
  let dw : ℝ → ℝ := barrierSpaceDerivCutoff M f t
  let Cw : ℝ := Real.exp (-M * t) * Cf ^ 2
  have hreg := squareHeatBarrierSliceRegularData_of_semigroup
    (M := M) ht hf hCf hf_bound hK hl2
  have hCw : 0 ≤ Cw := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hSbound : ∀ x, |intervalFullSemigroupOperator t f x| ≤ Cf :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      ht hCf hf_bound
  have hwbound : ∀ x, |w x| ≤ Cw := by
    intro x
    dsimp [w, Cw, ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier]
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (hSbound x) 2)
      (Real.exp_pos _).le
  have hwcoeff : ∀ n, |cosineCoeffs w n| ≤ 2 * Cw := by
    exact
      ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
        (by simpa [w] using hreg.continuous.continuousOn) hCw
        (fun x _hx => by simpa [w] using hwbound x)
  have hwl2 : Summable fun n : ℕ => (cosineCoeffs w n) ^ 2 := by
    have hmem :=
      ShenWork.Paper2.ChiNegCloseBaseSeed.memHSigma_zero_of_continuousOn
        hreg.continuous.continuousOn
    simpa [ShenWork.Paper2.HSigmaScale.memHSigma_zero] using hmem
  have hdw_eq : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      dw x = barrierSpaceDerivRep M f t x := by
    intro x hx
    simp [dw, barrierSpaceDerivCutoff, hx]
  have hdw_cont : ContinuousOn dw (Set.Icc (0 : ℝ) 1) :=
    hreg.deriv_rep_continuous.congr (fun x hx => hdw_eq x hx)
  obtain ⟨Gw, hGw, hGw_bound⟩ := hreg.deriv_bounded
  have hdw_bound : ∀ x, |dw x| ≤ Gw := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · simpa [dw, barrierSpaceDerivCutoff, hx] using hGw_bound x hx
    · simp [dw, barrierSpaceDerivCutoff, hx, hGw]
  have hdw_deriv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt w (dw x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    simpa [hdw_eq x hx'] using hreg.hasDerivAt x hx'
  have hdw_zero : dw 0 = 0 := by
    simp [dw, barrierSpaceDerivCutoff, barrierSpaceDerivRep,
      ShenWork.IntervalFullKernelRegularity.unitIntervalCosineHeatGradientValue_eq_zero_at_zero]
  have hdw_one : dw 1 = 0 := by
    simp [dw, barrierSpaceDerivCutoff, barrierSpaceDerivRep,
      ShenWork.IntervalFullKernelRegularity.unitIntervalCosineHeatGradientValue_eq_zero_at_one]
  simpa [w, dw] using
    (semigroup_dirichletPairing_integrable_tendsto
      (f := w) (df := dw) (φ := φ) (Cf := Cw) (K := 2 * Cw)
      (Gf := Gw) (Gφ := Gφ) hT hreg.continuous hCw hwbound hwcoeff
      hwl2 hreg.absolutelyContinuous hGw hdw_bound hdw_deriv hdw_cont
      hdw_zero hdw_one hGφ hφ_deriv_bound)

/-- A uniform change of the squared-barrier spatial derivative controls the
Dirichlet pairing after any positive Neumann heat lag. -/
theorem squareHeatBarrier_dirichletPairing_sub_abs_le
    {M tq tt r : ℝ} (htq : 0 < tq) (htt : 0 < tt) (hr : 0 < r)
    {f : ℝ → ℝ} (hf : Continuous f) {Cf K : ℝ} (hCf : 0 ≤ Cf)
    (hf_bound : ∀ y, |f y| ≤ Cf)
    (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
    {φ : ℝ → ℝ} {D Gφ : ℝ} (hD : 0 ≤ D)
    (hclose : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |barrierSpaceDerivRep M f tq x -
        barrierSpaceDerivRep M f tt x| ≤ D)
    (hGφ : 0 ≤ Gφ)
    (hφ_deriv_bound : ∀ᵐ y ∂volume, |deriv φ y| ≤ Gφ) :
    let wq : ℝ → ℝ := fun x =>
      ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier M f tq x
    let wt : ℝ → ℝ := fun x =>
      ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier M f tt x
    |(∫ x,
        deriv (fun z => intervalFullSemigroupOperator r wq z) x * deriv φ x
          ∂ShenWork.IntervalDomain.intervalMeasure 1) -
      ∫ x,
        deriv (fun z => intervalFullSemigroupOperator r wt z) x * deriv φ x
          ∂ShenWork.IntervalDomain.intervalMeasure 1| ≤ D * Gφ := by
  let wq : ℝ → ℝ := fun x =>
    ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier M f tq x
  let wt : ℝ → ℝ := fun x =>
    ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier M f tt x
  let dq : ℝ → ℝ := barrierSpaceDerivCutoff M f tq
  let dt : ℝ → ℝ := barrierSpaceDerivCutoff M f tt
  let Cq : ℝ := Real.exp (-M * tq) * Cf ^ 2
  let Ct : ℝ := Real.exp (-M * tt) * Cf ^ 2
  have hregq := squareHeatBarrierSliceRegularData_of_semigroup
    (M := M) htq hf hCf hf_bound hK hl2
  have hregt := squareHeatBarrierSliceRegularData_of_semigroup
    (M := M) htt hf hCf hf_bound hK hl2
  have hCq : 0 ≤ Cq := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hCt : 0 ≤ Ct := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hSq : ∀ x, |intervalFullSemigroupOperator tq f x| ≤ Cf :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      htq hCf hf_bound
  have hSt : ∀ x, |intervalFullSemigroupOperator tt f x| ≤ Cf :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      htt hCf hf_bound
  have hwq_bound : ∀ x, |wq x| ≤ Cq := by
    intro x
    dsimp [wq, Cq, ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier]
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (hSq x) 2) (Real.exp_pos _).le
  have hwt_bound : ∀ x, |wt x| ≤ Ct := by
    intro x
    dsimp [wt, Ct, ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier]
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (hSt x) 2) (Real.exp_pos _).le
  have hdq_eq : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      dq x = barrierSpaceDerivRep M f tq x := by
    intro x hx
    simp [dq, barrierSpaceDerivCutoff, hx]
  have hdt_eq : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      dt x = barrierSpaceDerivRep M f tt x := by
    intro x hx
    simp [dt, barrierSpaceDerivCutoff, hx]
  have hdq_cont : ContinuousOn dq (Set.Icc (0 : ℝ) 1) :=
    hregq.deriv_rep_continuous.congr (fun x hx => hdq_eq x hx)
  have hdt_cont : ContinuousOn dt (Set.Icc (0 : ℝ) 1) :=
    hregt.deriv_rep_continuous.congr (fun x hx => hdt_eq x hx)
  have hdq_int : IntervalIntegrable dq volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hdq_cont
  have hdt_int : IntervalIntegrable dt volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hdt_cont
  have hdq_deriv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt wq (dq x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    simpa [wq, hdq_eq x hx'] using hregq.hasDerivAt x hx'
  have hdt_deriv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt wt (dt x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    simpa [wt, hdt_eq x hx'] using hregt.hasDerivAt x hx'
  obtain ⟨Gq, hGq, hGq0⟩ := hregq.deriv_bounded
  obtain ⟨Gt, hGt, hGt0⟩ := hregt.deriv_bounded
  have hdq_bound : ∀ x, |dq x| ≤ Gq := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · simpa [dq, barrierSpaceDerivCutoff, hx] using hGq0 x hx
    · simp [dq, barrierSpaceDerivCutoff, hx, hGq]
  have hdt_bound : ∀ x, |dt x| ≤ Gt := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · simpa [dt, barrierSpaceDerivCutoff, hx] using hGt0 x hx
    · simp [dt, barrierSpaceDerivCutoff, hx, hGt]
  have hdiff : ∀ x, |dq x - dt x| ≤ D := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · simpa [hdq_eq x hx, hdt_eq x hx] using hclose x hx
    · simp [dq, dt, barrierSpaceDerivCutoff, hx, hD]
  exact semigroup_dirichletPairing_sub_abs_le_of_source_deriv_diff
    (f := wq) (g := wt) (df := dq) (dg := dt) (φ := φ)
    (D := D) (Cf := Cq) (Cg := Ct) (Gf := Gq) (Gg := Gt) (Gφ := Gφ)
    hr hregq.continuous.aestronglyMeasurable
    hregt.continuous.aestronglyMeasurable hCq hwq_bound hCt hwt_bound
    hdq_deriv hdt_deriv hdq_int hdt_int hGq hdq_bound hGt hdt_bound
    hD hdiff hGφ hφ_deriv_bound

/-- Moving-source weak-generator limit for the squared barrier.  The source
at lag `r` is the earlier barrier slice `w(t-q)`; uniform positive-time
continuity of its spatial derivative lets the fixed-source right-average
identity pass to this moving source. -/
theorem squareHeatBarrier_moving_dirichletAverage_tendsto
    {M t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : Continuous f) {Cf K : ℝ} (hCf : 0 ≤ Cf)
    (hf_bound : ∀ y, |f y| ≤ Cf)
    (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
    {φ : ℝ → ℝ} {Gφ : ℝ} (hGφ : 0 ≤ Gφ)
    (hφ_deriv_bound : ∀ᵐ y ∂volume, |deriv φ y| ≤ Gφ) :
    Tendsto
      (fun q : ℝ => q⁻¹ * ∫ r in (0 : ℝ)..q, ∫ x,
        deriv (fun z => intervalFullSemigroupOperator r
          (fun y =>
            ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier
              M f (t - q) y) z) x * deriv φ x
          ∂ShenWork.IntervalDomain.intervalMeasure 1)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x, barrierSpaceDerivRep M f t x * deriv φ x
        ∂ShenWork.IntervalDomain.intervalMeasure 1)) := by
  let H : ℝ → ℝ := fun r => ∫ x,
    deriv (fun z => intervalFullSemigroupOperator r
      (fun y =>
        ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier M f t y) z) x *
      deriv φ x ∂ShenWork.IntervalDomain.intervalMeasure 1
  let Hq : ℝ → ℝ → ℝ := fun q r => ∫ x,
    deriv (fun z => intervalFullSemigroupOperator r
      (fun y =>
        ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier
          M f (t - q) y) z) x *
      deriv φ x ∂ShenWork.IntervalDomain.intervalMeasure 1
  let L : ℝ := ∫ x, barrierSpaceDerivRep M f t x * deriv φ x
    ∂ShenWork.IntervalDomain.intervalMeasure 1
  have hhalf : 0 < t / 2 := half_pos ht
  obtain ⟨hHint, hHlim⟩ :=
    squareHeatBarrier_dirichletPairing_integrable_tendsto
      (M := M) (t := t) (T := t / 2) ht hhalf hf hCf hf_bound hK hl2
      hGφ hφ_deriv_bound
  have hcutoff_target :
      (∫ x, barrierSpaceDerivCutoff M f t x * deriv φ x
        ∂ShenWork.IntervalDomain.intervalMeasure 1) = L := by
    apply integral_congr_ae
    simp only [ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet]
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simp [L, barrierSpaceDerivCutoff, hx]
  have hHlim' : Tendsto H (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
    simpa [H, hcutoff_target] using hHlim
  have hHmeas : AEStronglyMeasurable H
      (volume.restrict (Set.uIoc (0 : ℝ) (t / 2))) := by
    rw [intervalIntegrable_iff] at hHint
    simpa [H] using hHint.aestronglyMeasurable
  have havg : Tendsto (fun q : ℝ => q⁻¹ * ∫ r in (0 : ℝ)..q, H r)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) :=
    right_intervalAverage_tendsto hhalf (by simpa [H] using hHint)
      hHmeas hHlim'
  have hdiffavg : Tendsto
      (fun q : ℝ =>
        q⁻¹ * (∫ r in (0 : ℝ)..q, Hq q r) -
          q⁻¹ * (∫ r in (0 : ℝ)..q, H r))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let η : ℝ := ε / (Gφ + 1)
    have hden : 0 < Gφ + 1 := by linarith
    have hη : 0 < η := div_pos hε hden
    have hηG : η * Gφ < ε := by
      have hlt : η * Gφ < η * (Gφ + 1) :=
        mul_lt_mul_of_pos_left (by linarith) hη
      have heq : η * (Gφ + 1) = ε := by
        dsimp [η]
        exact div_mul_cancel₀ ε hden.ne'
      rwa [heq] at hlt
    have hclose_event :=
      barrierSpaceDerivRep_tendsto_uniform_left (M := M) ht hK η hη
    have hsmall : ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0), q < t / 2 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hhalf)
    filter_upwards [self_mem_nhdsWithin, hsmall, hclose_event] with
      q hq hqhalf hclose
    have hqpos : 0 < q := hq
    have htq : 0 < t - q := by linarith
    have hHqint : IntervalIntegrable (Hq q) volume 0 q := by
      exact (squareHeatBarrier_dirichletPairing_integrable_tendsto
        (M := M) (t := t - q) (T := q) htq hqpos hf hCf hf_bound hK hl2
        hGφ hφ_deriv_bound).1
    have hHintq : IntervalIntegrable H volume 0 q := by
      apply IntervalIntegrable.mono_set hHint
      rw [Set.uIcc_of_le hqpos.le, Set.uIcc_of_le hhalf.le]
      exact Set.Icc_subset_Icc le_rfl hqhalf.le
    have hpoint : ∀ r ∈ Set.uIoc (0 : ℝ) q,
        ‖Hq q r - H r‖ ≤ η * Gφ := by
      intro r hr
      rw [Set.uIoc_of_le hqpos.le] at hr
      rw [Real.norm_eq_abs]
      exact squareHeatBarrier_dirichletPairing_sub_abs_le
        (M := M) (tq := t - q) (tt := t) (r := r)
        htq ht hr.1 hf hCf hf_bound hK hl2 hη.le
        (fun x hx => (hclose x hx).le) hGφ hφ_deriv_bound
    have htime := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    have hsubint :
        (∫ r in (0 : ℝ)..q, Hq q r - H r) =
          (∫ r in (0 : ℝ)..q, Hq q r) - ∫ r in (0 : ℝ)..q, H r :=
      intervalIntegral.integral_sub hHqint hHintq
    have hbound :
        |q⁻¹ * (∫ r in (0 : ℝ)..q, Hq q r) -
            q⁻¹ * ∫ r in (0 : ℝ)..q, H r| ≤ η * Gφ := by
      rw [← mul_sub, ← hsubint, abs_mul]
      rw [abs_of_nonneg (inv_nonneg.mpr hqpos.le)]
      calc
        q⁻¹ * |∫ r in (0 : ℝ)..q, Hq q r - H r|
            ≤ q⁻¹ * ((η * Gφ) * |q - 0|) :=
              mul_le_mul_of_nonneg_left (by
                simpa [Real.norm_eq_abs] using htime) (inv_nonneg.mpr hqpos.le)
        _ = η * Gφ := by
          rw [sub_zero, abs_of_pos hqpos]
          field_simp
    rw [Real.dist_eq, sub_zero]
    exact hbound.trans_lt hηG
  have hsum := hdiffavg.add havg
  have hsum' : Tendsto
      (fun q : ℝ =>
        (q⁻¹ * (∫ r in (0 : ℝ)..q, Hq q r) -
          q⁻¹ * (∫ r in (0 : ℝ)..q, H r)) +
        q⁻¹ * (∫ r in (0 : ℝ)..q, H r))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
    simpa using hsum
  refine hsum'.congr' ?_
  filter_upwards [] with q
  dsimp [Hq, H]
  ring

/-- Backward time difference quotients of a positive squared-barrier slice
converge after pairing with any bounded measurable spatial test. -/
theorem squareHeatBarrier_timeIncrement_pairing_tendsto
    {M t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : Continuous f) {Cf K : ℝ} (hCf : 0 ≤ Cf)
    (hf_bound : ∀ y, |f y| ≤ Cf)
    (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    {φ : ℝ → ℝ} {Cφ : ℝ}
    (hφ_meas : AEStronglyMeasurable φ
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hCφ : 0 ≤ Cφ) (hφ_bound : ∀ y, |φ y| ≤ Cφ) :
    Tendsto
      (fun q : ℝ => q⁻¹ * ∫ x,
        (ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier M f t x -
          ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier
            M f (t - q) x) * φ x
        ∂ShenWork.IntervalDomain.intervalMeasure 1)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x, barrierTimeDerivRep M f t x * φ x
        ∂ShenWork.IntervalDomain.intervalMeasure 1)) := by
  let μ := ShenWork.IntervalDomain.intervalMeasure 1
  let W : ℝ → ℝ → ℝ := fun r x =>
    ShenWork.Paper2.BFormPositiveDatumNegPart.squareHeatBarrier M f r x
  let V : ℝ → ℝ → ℝ := fun q x => q⁻¹ * (W t x - W (t - q) x) * φ x
  let v : ℝ → ℝ := fun x => barrierTimeDerivRep M f t x * φ x
  have hhalf : 0 < t / 2 := half_pos ht
  let Krect : Set (ℝ × ℝ) :=
    Set.Icc (t / 2) t ×ˢ Set.Icc (0 : ℝ) 1
  have hcompact : IsCompact Krect := isCompact_Icc.prod isCompact_Icc
  have htime_cont : ContinuousOn
      (fun p : ℝ × ℝ => barrierTimeDerivRep M f p.1 p.2) Krect := by
    exact (barrierTimeDerivRep_continuousOn_Ioi (M := M) hK).mono
      (fun p hp => ⟨hhalf.trans_le hp.1.1, Set.mem_univ p.2⟩)
  obtain ⟨B0, hB0⟩ := hcompact.bddAbove_image htime_cont.abs
  let B : ℝ := max B0 0
  have hB : 0 ≤ B := le_max_right _ _
  have htime_bound : ∀ r ∈ Set.Icc (t / 2) t,
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |barrierTimeDerivRep M f r x| ≤ B := by
    intro r hr x hx
    have hp : (r, x) ∈ Krect := ⟨hr, hx⟩
    exact (hB0 (Set.mem_image_of_mem _ hp)).trans (le_max_left _ _)
  have hWlip : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      LipschitzOnWith ⟨B, hB⟩ (fun r => W r x) (Set.Icc (t / 2) t) := by
    intro x hx
    apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (convex_Icc (t / 2) t)
    · intro r hr
      exact (squareHeatBarrier_time_hasDerivAt_rep
        (M := M) (t := r) (x := x) (hhalf.trans_le hr.1) hf hK hx).hasDerivWithinAt
    · intro r hr
      rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mk, Real.norm_eq_abs]
      exact htime_bound r hr x hx
  have hsmall : ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0), q < t / 2 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hhalf)
  have hVmeas : ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0),
      AEStronglyMeasurable (V q) μ := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with q hq hqhalf
    have htq : 0 < t - q := by linarith [show 0 < q from hq]
    have hWt := squareHeatBarrierSliceRegularData_of_semigroup
      (M := M) ht hf hCf hf_bound hK
      (by
        have hmem :=
          ShenWork.Paper2.ChiNegCloseBaseSeed.memHSigma_zero_of_continuousOn
            hf.continuousOn
        simpa [ShenWork.Paper2.HSigmaScale.memHSigma_zero] using hmem)
    have hWq := squareHeatBarrierSliceRegularData_of_semigroup
      (M := M) htq hf hCf hf_bound hK
      (by
        have hmem :=
          ShenWork.Paper2.ChiNegCloseBaseSeed.memHSigma_zero_of_continuousOn
            hf.continuousOn
        simpa [ShenWork.Paper2.HSigmaScale.memHSigma_zero] using hmem)
    exact ((hWt.continuous.aestronglyMeasurable.sub
      hWq.continuous.aestronglyMeasurable).const_mul q⁻¹).mul hφ_meas
  have hVbound : ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0),
      ∀ᵐ x ∂μ, ‖V q x‖ ≤ B * Cφ := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with q hq hqhalf
    have hqpos : 0 < q := hq
    simp only [μ, ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet]
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have htmq : t - q ∈ Set.Icc (t / 2) t := by
      constructor <;> linarith
    have htmem : t ∈ Set.Icc (t / 2) t :=
      ⟨half_le_self ht.le, le_rfl⟩
    have hdist : |W t x - W (t - q) x| ≤ B * q := by
      have hd := (hWlip x hx).dist_le_mul (t - q) htmq t htmem
      rw [Real.dist_eq, Real.dist_eq] at hd
      have htimeabs : |t - q - t| = q := by
        rw [show t - q - t = -q by ring, abs_neg, abs_of_pos hqpos]
      rw [htimeabs] at hd
      simpa [abs_sub_comm] using hd
    change |q⁻¹ * (W t x - W (t - q) x) * φ x| ≤ B * Cφ
    rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr hqpos.le)]
    have hslope : q⁻¹ * |W t x - W (t - q) x| ≤ B := by
      calc
        q⁻¹ * |W t x - W (t - q) x| ≤ q⁻¹ * (B * q) :=
          mul_le_mul_of_nonneg_left hdist (inv_nonneg.mpr hqpos.le)
        _ = B := by field_simp
    exact mul_le_mul hslope (hφ_bound x) (abs_nonneg _) hB
  have hVlim : ∀ᵐ x ∂μ,
      Tendsto (fun q => V q x) (nhdsWithin 0 (Set.Ioi 0)) (nhds (v x)) := by
    simp only [μ, ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet]
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hslope :=
      ShenWork.Paper2.IntervalNegativePartWeakEnergy.HasDerivAt.tendsto_backwardSlope
        (squareHeatBarrier_time_hasDerivAt_rep
          (M := M) (t := t) (x := x) ht hf hK hx)
    have hmul := hslope.mul_const (φ x)
    simpa [V, v, W] using hmul
  have hdom : Integrable (fun _ : ℝ => B * Cφ) μ := integrable_const _
  have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => B * Cφ) hVmeas hVbound hdom hVlim
  have heq :
      (fun q : ℝ => q⁻¹ * ∫ x, (W t x - W (t - q) x) * φ x ∂μ) =
      fun q : ℝ => ∫ x, V q x ∂μ := by
    funext q
    symm
    calc
      (∫ x, V q x ∂μ) =
          ∫ x, q⁻¹ * ((W t x - W (t - q) x) * φ x) ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with x
            simp [V]
            ring
      _ = q⁻¹ * ∫ x, (W t x - W (t - q) x) * φ x ∂μ :=
        MeasureTheory.integral_const_mul q⁻¹
          (fun x => (W t x - W (t - q) x) * φ x)
  rw [heq]
  simpa [V, v, W, μ] using hlim

end ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms
