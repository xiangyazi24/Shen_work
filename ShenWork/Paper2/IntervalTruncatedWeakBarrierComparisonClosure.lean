import ShenWork.Paper2.IntervalTruncatedWeakBarrierComparison
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.Weierstrass

open Filter Topology Set MeasureTheory
open scoped BigOperators Topology ENNReal Polynomial

noncomputable section

namespace ShenWork.Paper2.IntervalTruncatedWeakBarrierComparisonClosure

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.Paper2.BFormPositiveDatumNegPart
  (SquareHeatSeed squareHeatBarrier squareHeatResidualCore
   neumannLinearDriftResidual)
open ShenWork.Paper2.BFormPositiveDatumNegPart
open ShenWork.Paper2.IntervalTruncatedWeakBarrierComparison

/-- Analytic data of the terminal Stampacchia test `(w-u)₊`. -/
structure ComparisonTerminalTestData
    (w u : intervalDomainPoint → ℝ) where
  continuousOn : ContinuousOn
    (fun x => positivePart (intervalDomainLift w x - intervalDomainLift u x))
    (Set.Icc (0 : ℝ) 1)
  zero_outside : ∀ x, x ∉ Set.Icc (0 : ℝ) 1 →
    positivePart (intervalDomainLift w x - intervalDomainLift u x) = 0
  C : ℝ
  C_nonneg : 0 ≤ C
  bound : ∀ x,
    |positivePart (intervalDomainLift w x - intervalDomainLift u x)| ≤ C
  absolutelyContinuous : AbsolutelyContinuousOnInterval
    (fun x => positivePart (intervalDomainLift w x - intervalDomainLift u x))
    0 1
  G : ℝ
  G_nonneg : 0 ≤ G
  deriv_bound : ∀ᵐ x ∂volume,
    |deriv (fun y =>
      positivePart (intervalDomainLift w y - intervalDomainLift u y)) x| ≤ G

/-- Continuous subtype slices lift continuously on the physical interval. -/
private theorem intervalDomainLift_continuousOn_Icc
    {w : intervalDomainPoint → ℝ} (hw : Continuous w) :
    ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift w) = w := by
    funext X
    simp [intervalDomainLift, X.2]
  rw [heq]
  exact hw

/-- A Lipschitz function on `[0,1]` that vanishes off the interval has its
global derivative bounded almost everywhere by the same constant. -/
private theorem deriv_abs_le_ae_of_lipschitzOn_Icc_zero_outside
    {φ : ℝ → ℝ} {G : ℝ} (hG : 0 ≤ G)
    (hlip : LipschitzOnWith ⟨G, hG⟩ φ (Set.Icc (0 : ℝ) 1))
    (hzero : ∀ x, x ∉ Set.Icc (0 : ℝ) 1 → φ x = 0) :
    ∀ᵐ x ∂volume, |deriv φ x| ≤ G := by
  filter_upwards [Measure.ae_ne volume (0 : ℝ),
    Measure.ae_ne volume (1 : ℝ)] with x hx0 hx1
  by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
  · have hn := norm_deriv_le_of_lipschitzOn
      (Icc_mem_nhds hx.1 hx.2) hlip
    simpa [Real.norm_eq_abs] using hn
  · have hout : x < 0 ∨ 1 < x := by
      by_cases hxlt : x < 0
      · exact Or.inl hxlt
      · right
        have hxnonneg : 0 ≤ x := le_of_not_gt hxlt
        have hone : 1 ≤ x := le_of_not_gt (fun hxone =>
          hx ⟨lt_of_le_of_ne hxnonneg (Ne.symm hx0), hxone⟩)
        exact lt_of_le_of_ne hone (Ne.symm hx1)
    rcases hout with hxlt | hxgt
    · have hev : φ =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
        filter_upwards [Iio_mem_nhds hxlt] with y hy
        exact hzero y (by intro hmem; exact (not_lt_of_ge hmem.1) hy)
      rw [hev.deriv_eq]
      simp [hG]
    · have hev : φ =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
        filter_upwards [Ioi_mem_nhds hxgt] with y hy
        exact hzero y (by intro hmem; exact (not_lt_of_ge hmem.2) hy)
      rw [hev.deriv_eq]
      simp [hG]

/-- Build the terminal comparison test from two continuous Lipschitz slices. -/
def comparisonTerminalTestData_of_lipschitz
    {w u : intervalDomainPoint → ℝ} {Mw Mu Gw Gu : ℝ}
    (hw : Continuous w) (hu : Continuous u)
    (hMw : 0 ≤ Mw) (hw_bound : ∀ X, |w X| ≤ Mw)
    (hMu : 0 ≤ Mu) (hu_bound : ∀ X, |u X| ≤ Mu)
    (hGw : 0 ≤ Gw)
    (hw_lip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift w x - intervalDomainLift w y| ≤ Gw * |x - y|)
    (hGu : 0 ≤ Gu)
    (hu_lip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift u x - intervalDomainLift u y| ≤ Gu * |x - y|) :
    ComparisonTerminalTestData w u := by
  let z : ℝ → ℝ := fun x => intervalDomainLift w x - intervalDomainLift u x
  let φ : ℝ → ℝ := fun x => positivePart (z x)
  let G : ℝ := Gw + Gu
  let C : ℝ := Mw + Mu
  have hG : 0 ≤ G := add_nonneg hGw hGu
  have hC : 0 ≤ C := add_nonneg hMw hMu
  have hwLip : LipschitzOnWith ⟨Gw, hGw⟩ (intervalDomainLift w)
      (Set.Icc (0 : ℝ) 1) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    simpa [Real.dist_eq] using hw_lip x hx y hy
  have huLip : LipschitzOnWith ⟨Gu, hGu⟩ (intervalDomainLift u)
      (Set.Icc (0 : ℝ) 1) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    simpa [Real.dist_eq] using hu_lip x hx y hy
  have hzLip : LipschitzOnWith (⟨Gw, hGw⟩ + ⟨Gu, hGu⟩) z
      (Set.Icc (0 : ℝ) 1) := by
    simpa [z] using hwLip.sub huLip
  have hφLip : LipschitzOnWith ⟨G, hG⟩ φ (Set.Icc (0 : ℝ) 1) := by
    rw [lipschitzOnWith_iff_restrict]
    have hzR := hzLip.to_restrict.max_const 0
    simpa [φ, z, positivePart, G] using hzR
  have hzero : ∀ x, x ∉ Set.Icc (0 : ℝ) 1 → φ x = 0 := by
    intro x hx
    have hpair : ¬(0 ≤ x ∧ x ≤ 1) := by simpa using hx
    simp [φ, z, intervalDomainLift, hpair, positivePart]
  have hφac : AbsolutelyContinuousOnInterval φ 0 1 := by
    have hIcc : Set.Icc (0 : ℝ) 1 = Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num)]
    rw [hIcc] at hφLip
    exact hφLip.absolutelyContinuousOnInterval
  have hφcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1) := hφLip.continuousOn
  have hbound : ∀ x, |φ x| ≤ C := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · let X : intervalDomainPoint := ⟨x, hx⟩
      have hwx : |intervalDomainLift w x| ≤ Mw := by
        simpa [intervalDomainLift, hx, X] using hw_bound X
      have hux : |intervalDomainLift u x| ≤ Mu := by
        simpa [intervalDomainLift, hx, X] using hu_bound X
      have hp : |positivePart (z x)| ≤ |z x| := by
        by_cases hz : 0 ≤ z x
        · simp [positivePart, max_eq_left hz]
        · have hz' : z x ≤ 0 := le_of_not_ge hz
          simp [positivePart, max_eq_right hz', abs_nonneg]
      exact hp.trans
        ((abs_sub _ _).trans (by simpa [z, C] using add_le_add hwx hux))
    · have hpair : ¬(0 ≤ x ∧ x ≤ 1) := by simpa using hx
      simp [φ, z, intervalDomainLift, hpair, C, hC, positivePart]
  exact
    { continuousOn := by simpa [φ, z] using hφcont
      zero_outside := by simpa [φ, z] using hzero
      C := C
      C_nonneg := hC
      bound := by simpa [φ, z] using hbound
      absolutelyContinuous := by simpa [φ, z] using hφac
      G := G
      G_nonneg := hG
      deriv_bound := by
        simpa [φ, z] using
          deriv_abs_le_ae_of_lipschitzOn_Icc_zero_outside hG hφLip hzero }

/-- Algebraic reaction chain for the positive comparison defect. -/
theorem comparison_defect_mul_positivePart
    (w u : intervalDomainPoint → ℝ) (x : ℝ) :
    (intervalDomainLift w x - intervalDomainLift u x) *
        positivePart (intervalDomainLift w x - intervalDomainLift u x) =
      positivePart (intervalDomainLift w x - intervalDomainLift u x) ^ 2 := by
  let z := intervalDomainLift w x - intervalDomainLift u x
  by_cases hz : 0 ≤ z
  · simp [z, positivePart, max_eq_left hz, pow_two]
  · have hz' : z ≤ 0 := le_of_not_ge hz
    simp [z, positivePart, max_eq_right hz']

/-- Matched-divergence chain rule.  On the active set the defect equals its
positive part; on the strictly inactive set continuity makes the positive
part locally zero.  Thus no derivative of the drift coefficient appears. -/
theorem comparison_defect_mul_positivePart_deriv_ae
    {w u : intervalDomainPoint → ℝ} (hw : Continuous w) (hu : Continuous u) :
    ∀ᵐ x ∂intervalMeasure 1,
      (intervalDomainLift w x - intervalDomainLift u x) *
          deriv (fun y =>
            positivePart (intervalDomainLift w y - intervalDomainLift u y)) x =
        positivePart (intervalDomainLift w x - intervalDomainLift u x) *
          deriv (fun y =>
            positivePart (intervalDomainLift w y - intervalDomainLift u y)) x := by
  have hwlift := intervalDomainLift_continuousOn_Icc hw
  have hulift := intervalDomainLift_continuousOn_Icc hu
  simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    (Measure.ae_ne volume (0 : ℝ)).filter_mono ae_restrict_le,
    (Measure.ae_ne volume (1 : ℝ)).filter_mono ae_restrict_le] with x hx hx0 hx1
  let z : ℝ → ℝ := fun y => intervalDomainLift w y - intervalDomainLift u y
  let φ : ℝ → ℝ := fun y => positivePart (z y)
  have hxoo : x ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
  by_cases hz : 0 ≤ z x
  · simp [z, φ, positivePart, max_eq_left hz]
  · have hzlt : z x < 0 := lt_of_not_ge hz
    have hzcont : ContinuousAt z x := by
      exact (hwlift.continuousAt (Icc_mem_nhds hxoo.1 hxoo.2)).sub
        (hulift.continuousAt (Icc_mem_nhds hxoo.1 hxoo.2))
    have hevent : ∀ᶠ y in 𝓝 x, z y < 0 :=
      hzcont.eventually (Iio_mem_nhds hzlt)
    have hφzero : φ =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
      filter_upwards [hevent] with y hy
      have hyle : z y ≤ 0 := hy.le
      simp [φ, positivePart, max_eq_right hyle]
    rw [show deriv (fun y => positivePart
        (intervalDomainLift w y - intervalDomainLift u y)) x = 0 by
      simpa [φ, z] using hφzero.deriv_eq]
    simp

/-- Backward supporting-line inequality for the squared positive part. -/
theorem positivePart_sq_sub_le_two_mul (a b : ℝ) :
    positivePart a ^ 2 - positivePart b ^ 2 ≤
      2 * positivePart a * (a - b) := by
  by_cases ha : 0 ≤ a
  · rw [show positivePart a = a by simp [positivePart, max_eq_left ha]]
    by_cases hb : 0 ≤ b
    · rw [show positivePart b = b by simp [positivePart, max_eq_left hb]]
      nlinarith [sq_nonneg (a - b)]
    · have hble : b ≤ 0 := le_of_not_ge hb
      rw [show positivePart b = 0 by simp [positivePart, max_eq_right hble]]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos ha hble]
  · have hale : a ≤ 0 := le_of_not_ge ha
    rw [show positivePart a = 0 by simp [positivePart, max_eq_right hale]]
    nlinarith [sq_nonneg (positivePart b)]

/-- Closed-endpoint bridge for the weak comparison.  Vanishing comparison
energy first gives `(w-u)₊ = 0` almost everywhere; continuity then upgrades
the equality to every point of `[0,1]`, including both endpoints. -/
theorem pointwise_le_on_closed_of_comparisonPositivePartEnergy_eq_zero
    {w u : intervalDomainPoint → ℝ}
    (H : ComparisonTerminalTestData w u)
    (hzero : (∫ x, positivePart
        (intervalDomainLift w x - intervalDomainLift u x) ^ 2
        ∂intervalMeasure 1) = 0) :
    ∀ X : intervalDomainPoint, w X ≤ u X := by
  let φ : ℝ → ℝ := fun x =>
    positivePart (intervalDomainLift w x - intervalDomainLift u x)
  have hφmeas : AEStronglyMeasurable φ (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
      (by simpa [φ] using H.continuousOn)
  have hint : Integrable (fun x => φ x ^ 2) (intervalMeasure 1) := by
    apply ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      (M := H.C ^ 2) (hφmeas.pow 2)
    intro x
    rw [Pi.pow_apply, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by simpa [φ] using H.bound x) 2
  have hnn : 0 ≤ᵐ[intervalMeasure 1] fun x => φ x ^ 2 :=
    Filter.Eventually.of_forall fun x => sq_nonneg (φ x)
  have hsqzero : (fun x => φ x ^ 2) =ᵐ[intervalMeasure 1] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnn hint).1 (by
      simpa [φ] using hzero)
  have hφzero : φ =ᵐ[intervalMeasure 1] 0 := by
    filter_upwards [hsqzero] with x hx
    exact sq_eq_zero_iff.mp (by simpa using hx)
  have hφzero_restrict :
      φ =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] fun _ => 0 := by
    simpa [intervalMeasure, ShenWork.IntervalDomain.intervalSet] using hφzero
  have hevery : Set.EqOn φ (fun _ : ℝ => 0) (Set.Icc (0 : ℝ) 1) :=
    MeasureTheory.Measure.eqOn_Icc_of_ae_eq volume (by norm_num)
      hφzero_restrict (by simpa [φ] using H.continuousOn) continuousOn_const
  intro X
  have hX := hevery X.2
  have hpp : positivePart (w X - u X) = 0 := by
    have hx0 : 0 ≤ X.1 := X.2.1
    have hx1 : X.1 ≤ 1 := X.2.2
    simpa [φ, intervalDomainLift, hx0, hx1] using hX
  exact sub_nonpos.mp (positivePart_eq_zero_iff.mp hpp)

/-- Pointwise Stampacchia diffusion chain at a common differentiability
point of the two profiles. -/
private theorem deriv_sub_mul_positivePart_deriv_eq_sq
    {w u : ℝ → ℝ} {x : ℝ}
    (hw : DifferentiableAt ℝ w x) (hu : DifferentiableAt ℝ u x)
    (hzcont : ContinuousAt (fun y => w y - u y) x) :
    (deriv w x - deriv u x) *
        deriv (fun y => positivePart (w y - u y)) x =
      deriv (fun y => positivePart (w y - u y)) x ^ 2 := by
  let z : ℝ → ℝ := fun y => w y - u y
  have hzder : deriv z x = deriv w x - deriv u x := by
    exact (hw.hasDerivAt.sub hu.hasDerivAt).deriv
  rcases lt_trichotomy (z x) 0 with hzneg | hzero | hzpos
  · have hev : (fun y => positivePart (z y)) =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
      have hlt : ∀ᶠ y in 𝓝 x, z y < 0 :=
        hzcont.tendsto.eventually (Iio_mem_nhds hzneg)
      filter_upwards [hlt] with y hy
      simp [positivePart, max_eq_right hy.le]
    rw [show deriv (fun y => positivePart (w y - u y)) x = 0 by
      simpa [z] using hev.deriv_eq]
    simp
  · have hmin : IsLocalMin (fun y => positivePart (z y)) x := by
      filter_upwards [] with y
      rw [hzero]
      simpa [positivePart] using positivePart_nonneg (z y)
    rw [show deriv (fun y => positivePart (w y - u y)) x = 0 by
      simpa [z] using hmin.deriv_eq_zero]
    simp
  · have hev : (fun y => positivePart (z y)) =ᶠ[𝓝 x] z := by
      have hpos : ∀ᶠ y in 𝓝 x, 0 < z y :=
        hzcont.tendsto.eventually (Ioi_mem_nhds hzpos)
      filter_upwards [hpos] with y hy
      simp [positivePart, max_eq_left hy.le]
    have hpp : deriv (fun y => positivePart (w y - u y)) x = deriv z x := by
      simpa [z] using hev.deriv_eq
    rw [hpp, hzder]
    ring

/-- Terminal Stampacchia diffusion chain for the concrete barrier and
truncated slice.  The solution derivative is that of the constant extension;
on the open physical interval this agrees locally with the lifted slice. -/
theorem truncatedSquareHeatBarrier_terminal_diffusion_chain_ae
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {Mbar t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T)
    {f : ℝ → ℝ} (hf : Continuous f) {Cf K : ℝ} (hCf : 0 ≤ Cf)
    (hf_bound : ∀ y, |f y| ≤ Cf)
    (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2) :
    let W : ℝ → intervalDomainPoint → ℝ :=
      fun r X => squareHeatBarrier Mbar f r X.1
    let U := truncatedConjugatePicardLimit p u₀ DT.T
    let φ := comparisonPositivePartLift W U t
    let et := ShenWork.IntervalDomain.intervalDomainConstExtend (U t)
    ∀ᵐ x ∂intervalMeasure 1,
      (deriv (fun y => squareHeatBarrier Mbar f t y) x - deriv et x) *
          deriv φ x = deriv φ x ^ 2 := by
  let W : ℝ → intervalDomainPoint → ℝ :=
    fun r X => squareHeatBarrier Mbar f r X.1
  let U := truncatedConjugatePicardLimit p u₀ DT.T
  let φ : ℝ → ℝ := comparisonPositivePartLift W U t
  let et : ℝ → ℝ :=
    ShenWork.IntervalDomain.intervalDomainConstExtend (U t)
  let wt : ℝ → ℝ := fun y => squareHeatBarrier Mbar f t y
  have hUtcont : Continuous (U t) := by
    simpa [U] using
      (truncatedConjugateMildSolutionData_of_data DT).hcont t ht htT
  obtain ⟨Gu, hGu, hUlip⟩ :=
    _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedPicardLimit_lipschitzOn_positive_time
      DT ht htT
  have hetlip : LipschitzOnWith ⟨Gu, hGu⟩ et (Set.Icc (0 : ℝ) 1) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    simpa [et, U, Real.dist_eq,
      ShenWork.IntervalDomain.constExtend_eq_lift_on_Icc hx,
      ShenWork.IntervalDomain.constExtend_eq_lift_on_Icc hy] using
      hUlip x hx y hy
  have hetac : AbsolutelyContinuousOnInterval et 0 1 := by
    have hI : Set.Icc (0 : ℝ) 1 = Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num)]
    rw [hI] at hetlip
    exact hetlip.absolutelyContinuousOnInterval
  have hwtreg :=
    ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.squareHeatBarrierSliceRegularData_of_semigroup
      (M := Mbar) ht hf hCf hf_bound hK hl2
  have hetcont : Continuous et :=
    ShenWork.IntervalDomain.constExtend_continuous hUtcont
  simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    hetac.ae_differentiableAt.filter_mono ae_restrict_le,
    (Measure.ae_ne volume (0 : ℝ)).filter_mono ae_restrict_le,
    (Measure.ae_ne volume (1 : ℝ)).filter_mono ae_restrict_le]
      with x hx hxdiff hx0 hx1
  have hxoo : x ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
  have hxdiff' : DifferentiableAt ℝ et x :=
    hxdiff (by simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx)
  have hevent : φ =ᶠ[nhds x]
      fun y => positivePart (wt y - et y) := by
    filter_upwards [Ioo_mem_nhds hxoo.1 hxoo.2] with y hy
    have hycc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
    simp [φ, W, U, wt, et, comparisonPositivePartLift, intervalDomainLift,
      hycc, ShenWork.IntervalDomain.constExtend_eq_lift_on_Icc hycc]
  have hchain := deriv_sub_mul_positivePart_deriv_eq_sq
    (hwtreg.hasDerivAt x hx).differentiableAt hxdiff'
    (hwtreg.continuous.continuousAt.sub hetcont.continuousAt)
  have hder : deriv φ x =
      deriv (fun y => positivePart (wt y - et y)) x := hevent.deriv_eq
  change (deriv wt x - deriv et x) * deriv φ x = deriv φ x ^ 2
  rw [hder]
  simpa [wt] using hchain

/-- A globally `C²` real function has an absolutely continuous first
derivative on the unit interval. -/
theorem deriv_absolutelyContinuousOnInterval_of_contDiff_two
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) :
    AbsolutelyContinuousOnInterval (deriv F) 0 1 := by
  have hD : Continuous (deriv (deriv F)) := by
    have hF' : ContDiff ℝ 1 (deriv F) := by
      simpa using hF.deriv'
    exact hF'.continuous_deriv (by norm_num)
  obtain ⟨B0, hB0⟩ := isCompact_Icc.bddAbove_image hD.continuousOn.abs
  let B : ℝ := max B0 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv F) x| ≤ B := by
    intro x hx
    exact (hB0 (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)
  have hlip : LipschitzOnWith ⟨B, hB⟩ (deriv F) (Set.Icc (0 : ℝ) 1) := by
    apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (convex_Icc (0 : ℝ) 1)
    · intro x _hx
      exact (hF.differentiable_deriv_two x).hasDerivAt.hasDerivWithinAt
    · intro x hx
      rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mk, Real.norm_eq_abs]
      exact hbound x hx
  have hIcc : Set.Icc (0 : ℝ) 1 = Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num)]
  rw [hIcc] at hlip
  exact hlip.absolutelyContinuousOnInterval

/-- Integrating against the physical interval measure is the ordinary
oriented integral over `[0,1]`. -/
theorem intervalMeasure_integral_eq_intervalIntegral (F : ℝ → ℝ) :
    (∫ x, F x ∂intervalMeasure 1) = ∫ x in (0 : ℝ)..1, F x := by
  simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- Polynomial profiles are absolutely continuous on the unit interval. -/
private theorem polynomial_eval_absolutelyContinuousOnInterval (P : ℝ[X]) :
    AbsolutelyContinuousOnInterval (fun x : ℝ => P.eval x) 0 1 := by
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.bddAbove_image
    P.derivative.continuous.continuousOn.abs
  let B : ℝ := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |P.derivative.eval x| ≤ B := by
    intro x hx
    exact (hB₀ (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)
  have hlip : LipschitzOnWith ⟨B, hB⟩ (fun x : ℝ => P.eval x)
      (Set.Icc (0 : ℝ) 1) := by
    apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (convex_Icc (0 : ℝ) 1)
    · intro x _hx
      exact (P.hasDerivAt x).hasDerivWithinAt
    · intro x hx
      rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mk, Real.norm_eq_abs]
      exact hbound x hx
  have hIcc : Set.Icc (0 : ℝ) 1 = Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num)]
  rw [hIcc] at hlip
  exact hlip.absolutelyContinuousOnInterval

/-- An integrable real profile on the physical interval can be approximated
in `L¹` by a polynomial. -/
private theorem exists_polynomial_intervalMeasure_integral_abs_sub_lt
    {f : ℝ → ℝ} (hf : Integrable f (intervalMeasure 1))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ P : ℝ[X],
      (∫ x, |f x - P.eval x| ∂intervalMeasure 1) < eps := by
  obtain ⟨g, hfg, hgint⟩ :=
    hf.exists_boundedContinuous_integral_sub_le (show 0 < eps / 4 by positivity)
  obtain ⟨P, hPg⟩ := exists_polynomial_near_of_continuousOn
    0 1 (fun x : ℝ => g x) g.continuous.continuousOn (eps / 4)
      (by positivity)
  refine ⟨P, ?_⟩
  have hgp_meas : AEStronglyMeasurable
      (fun x : ℝ => |g x - P.eval x|) (intervalMeasure 1) :=
    (g.continuous.aestronglyMeasurable.sub
      P.continuous.aestronglyMeasurable).norm
  have hgp_bound : ∀ᵐ x ∂intervalMeasure 1,
      |g x - P.eval x| ≤ eps / 4 := by
    simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simpa [abs_sub_comm] using (hPg x hx).le
  have hgp_int : Integrable (fun x : ℝ => |g x - P.eval x|)
      (intervalMeasure 1) := by
    haveI : IsFiniteMeasure (intervalMeasure 1) :=
      ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
    exact Integrable.of_bound hgp_meas (eps / 4)
      (hgp_bound.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
  have hgp_integral :
      (∫ x, |g x - P.eval x| ∂intervalMeasure 1) ≤ eps / 4 := by
    have hconst : Integrable (fun _ : ℝ => eps / 4) (intervalMeasure 1) :=
      integrable_const _
    calc
      (∫ x, |g x - P.eval x| ∂intervalMeasure 1) ≤
          ∫ _x : ℝ, eps / 4 ∂intervalMeasure 1 :=
        MeasureTheory.integral_mono_ae hgp_int hconst hgp_bound
      _ = eps / 4 := by
        simpa using ShenWork.IntervalDomain.intervalMeasure_integral_const
          (L := 1) (c := eps / 4) (by norm_num : (0 : ℝ) ≤ 1)
  have htri : ∀ x : ℝ,
      |f x - P.eval x| ≤ ‖f x - g x‖ + |g x - P.eval x| := by
    intro x
    rw [Real.norm_eq_abs]
    calc
      |f x - P.eval x| = |(f x - g x) + (g x - P.eval x)| := by ring_nf
      _ ≤ |f x - g x| + |g x - P.eval x| := abs_add_le _ _
  have hleft_int : Integrable (fun x => ‖f x - g x‖) (intervalMeasure 1) :=
    (hf.sub hgint).norm
  have htarget_int : Integrable (fun x => |f x - P.eval x|)
      (intervalMeasure 1) := by
    exact (hleft_int.add hgp_int).mono'
      ((hf.aestronglyMeasurable.sub
        P.continuous.aestronglyMeasurable).norm)
      (Filter.Eventually.of_forall
        fun x => by simpa [Real.norm_eq_abs] using htri x)
  have hint_le :
      (∫ x, |f x - P.eval x| ∂intervalMeasure 1) ≤
        (∫ x, ‖f x - g x‖ ∂intervalMeasure 1) +
          ∫ x, |g x - P.eval x| ∂intervalMeasure 1 := by
    rw [← MeasureTheory.integral_add hleft_int hgp_int]
    exact MeasureTheory.integral_mono_ae htarget_int (hleft_int.add hgp_int)
      (Filter.Eventually.of_forall htri)
  calc
    (∫ x, |f x - P.eval x| ∂intervalMeasure 1)
        ≤ (∫ x, ‖f x - g x‖ ∂intervalMeasure 1) +
            ∫ x, |g x - P.eval x| ∂intervalMeasure 1 := hint_le
    _ ≤ eps / 4 + eps / 4 := add_le_add hfg hgp_integral
    _ < eps := by linarith

/-- A common spatial Lipschitz modulus gives a uniform `O(√t)` heat
approximation bound. -/
private theorem intervalFullSemigroupOperator_sub_abs_le_of_lipschitzOn
    {r G : ℝ} (hr : 0 < r) (hG : 0 ≤ G) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hlip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |f x - f y| ≤ G * |x - y|)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |intervalFullSemigroupOperator r f x - f x| ≤
      2 * G * Real.sqrt r := by
  let K : ℝ → ℝ := fun y =>
    ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel r x y
  have hKnn : ∀ y, 0 ≤ K y := fun y =>
    ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_nonneg hr x y
  have hKint : Integrable K (intervalMeasure 1) := by
    simpa [K] using
      ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_integrable hr x
  have hmass : (∫ y, K y ∂intervalMeasure 1) = 1 := by
    simpa [K] using
      ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_intervalMeasure_integral_eq_one
        hr x
  have hKf : Integrable (fun y => K y * f y) (intervalMeasure 1) := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
    have hfmeas : AEStronglyMeasurable f (intervalMeasure 1) :=
      ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure hf
    exact (hKint.bdd_mul hfmeas
      (by
        simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
        filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
        simpa [Real.norm_eq_abs] using hC y hy)).congr
      (Filter.Eventually.of_forall fun y => by ring)
  have hconstK : Integrable (fun y => f x * K y) (intervalMeasure 1) :=
    hKint.const_mul (f x)
  have hrewrite :
      intervalFullSemigroupOperator r f x - f x =
        ∫ y, K y * (f y - f x) ∂intervalMeasure 1 := by
    have hsem : intervalFullSemigroupOperator r f x =
        ∫ y, K y * f y ∂intervalMeasure 1 := rfl
    have hfx : f x = ∫ y, f x * K y ∂intervalMeasure 1 := by
      rw [MeasureTheory.integral_const_mul, hmass, mul_one]
    calc
      intervalFullSemigroupOperator r f x - f x =
          (∫ y, K y * f y ∂intervalMeasure 1) - f x := by rw [hsem]
      _ = (∫ y, K y * f y ∂intervalMeasure 1) -
            ∫ y, f x * K y ∂intervalMeasure 1 := by
        exact congrArg (fun z => (∫ y, K y * f y ∂intervalMeasure 1) - z) hfx
      _ = ∫ y, K y * f y - f x * K y ∂intervalMeasure 1 := by
        rw [MeasureTheory.integral_sub hKf hconstK]
      _ = ∫ y, K y * (f y - f x) ∂intervalMeasure 1 := by
        apply integral_congr_ae
        filter_upwards [] with y
        ring
  have hmoment_int : Integrable (fun y => K y * |y - x|)
      (intervalMeasure 1) := by
    simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
    exact ((ShenWork.IntervalNeumannFullKernel.continuousOn_intervalNeumannFullKernel_snd
      hr x).mul
        ((continuous_abs.comp (continuous_id.sub continuous_const)).continuousOn)).integrableOn_Icc
  have hprod_int : Integrable (fun y => K y * (f y - f x))
      (intervalMeasure 1) := (hKf.sub hconstK).congr
        (Filter.Eventually.of_forall fun y => by
          change K y * f y - f x * K y = K y * (f y - f x)
          ring)
  have habs :
      |∫ y, K y * (f y - f x) ∂intervalMeasure 1| ≤
        ∫ y, K y * |f y - f x| ∂intervalMeasure 1 := by
    calc
      |∫ y, K y * (f y - f x) ∂intervalMeasure 1| =
          ‖∫ y, K y * (f y - f x) ∂intervalMeasure 1‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ∫ y, ‖K y * (f y - f x)‖ ∂intervalMeasure 1 :=
        norm_integral_le_integral_norm _
      _ = ∫ y, K y * |f y - f x| ∂intervalMeasure 1 := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hKnn y)]
  have hmod_int : Integrable (fun y => K y * |f y - f x|)
      (intervalMeasure 1) := hprod_int.norm.congr
        (Filter.Eventually.of_forall fun y => by
          change |K y * (f y - f x)| = K y * |f y - f x|
          rw [abs_mul, abs_of_nonneg (hKnn y)])
  have hmod :
      (∫ y, K y * |f y - f x| ∂intervalMeasure 1) ≤
        G * (∫ y, K y * |y - x| ∂intervalMeasure 1) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_mono_ae hmod_int (hmoment_int.const_mul G)
    simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    calc
      K y * |f y - f x| ≤ K y * (G * |y - x|) :=
        mul_le_mul_of_nonneg_left
          (by simpa [abs_sub_comm] using hlip x hx y hy) (hKnn y)
      _ = G * (K y * |y - x|) := by ring
  have hmoment :
      (∫ y, K y * |y - x| ∂intervalMeasure 1) ≤
        4 * r / Real.sqrt (4 * Real.pi * r) := by
    rw [intervalMeasure_integral_eq_intervalIntegral]
    simpa [K, mul_comm] using
      ShenWork.IntervalSemigroupUniform.intervalNeumannFullKernel_abs_moment_le
        hr x hx
  have h4pir : 0 < 4 * Real.pi * r := by positivity
  have hpi_ge : 4 * r ≤ 4 * Real.pi * r := by
    nlinarith [Real.pi_gt_three]
  have hsqrt4r : Real.sqrt (4 * r) = 2 * Real.sqrt r := by
    have hsq : (4 : ℝ) * r =
        (2 * Real.sqrt r) * (2 * Real.sqrt r) := by
      nlinarith [Real.mul_self_sqrt hr.le]
    rw [hsq, Real.sqrt_mul_self (by positivity : 0 ≤ 2 * Real.sqrt r)]
  have hmoment_simple :
      4 * r / Real.sqrt (4 * Real.pi * r) ≤ 2 * Real.sqrt r := by
    rw [div_le_iff₀ (Real.sqrt_pos_of_pos h4pir)]
    calc
      4 * r = 2 * Real.sqrt r * Real.sqrt (4 * r) := by
        rw [hsqrt4r]
        nlinarith [Real.mul_self_sqrt hr.le]
      _ ≤ 2 * Real.sqrt r * Real.sqrt (4 * Real.pi * r) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hpi_ge) (by positivity)
  rw [hrewrite]
  calc
    |∫ y, K y * (f y - f x) ∂intervalMeasure 1|
        ≤ ∫ y, K y * |f y - f x| ∂intervalMeasure 1 := habs
    _ ≤ G * (∫ y, K y * |y - x| ∂intervalMeasure 1) := hmod
    _ ≤ G * (2 * Real.sqrt r) :=
      mul_le_mul_of_nonneg_left (hmoment.trans hmoment_simple) hG
    _ = 2 * G * Real.sqrt r := by ring

/-- The constant extension of a Lipschitz interval slice has the same
almost-everywhere derivative bound on the real line. -/
private theorem constExtend_deriv_abs_le_ae_of_lipschitzOn
    {u : intervalDomainPoint → ℝ} {G : ℝ} (hG : 0 ≤ G)
    (hlip : LipschitzOnWith ⟨G, hG⟩
      (ShenWork.IntervalDomain.intervalDomainConstExtend u)
      (Set.Icc (0 : ℝ) 1)) :
    ∀ᵐ x ∂volume,
      |deriv (ShenWork.IntervalDomain.intervalDomainConstExtend u) x| ≤ G := by
  let f := ShenWork.IntervalDomain.intervalDomainConstExtend u
  filter_upwards [Measure.ae_ne volume (0 : ℝ),
    Measure.ae_ne volume (1 : ℝ)] with x hx0 hx1
  by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
  · have hn := norm_deriv_le_of_lipschitzOn
      (Icc_mem_nhds hx.1 hx.2) hlip
    simpa [f, Real.norm_eq_abs] using hn
  · have hout : x < 0 ∨ 1 < x := by
      by_cases hxlt : x < 0
      · exact Or.inl hxlt
      · right
        have hxnonneg : 0 ≤ x := le_of_not_gt hxlt
        have hone : 1 ≤ x := le_of_not_gt (fun hxone =>
          hx ⟨lt_of_le_of_ne hxnonneg (Ne.symm hx0), hxone⟩)
        exact lt_of_le_of_ne hone (Ne.symm hx1)
    rcases hout with hxlt | hxgt
    · have hev : f =ᶠ[𝓝 x] fun _ : ℝ =>
          u ⟨0, ⟨le_rfl, by norm_num⟩⟩ := by
        filter_upwards [Iio_mem_nhds hxlt] with y hy
        have hy0 : y ≤ 0 := hy.le
        simp [f, ShenWork.IntervalDomain.intervalDomainConstExtend, hy0]
      rw [show deriv f x = 0 by rw [hev.deriv_eq]; simp]
      simpa [hG]
    · have hev : f =ᶠ[𝓝 x] fun _ : ℝ =>
          u ⟨1, ⟨by norm_num, le_rfl⟩⟩ := by
        filter_upwards [Ioi_mem_nhds hxgt] with y hy
        have hy1 : 1 ≤ y := hy.le
        have hy0 : ¬y ≤ 0 := by linarith
        simp [f, ShenWork.IntervalDomain.intervalDomainConstExtend, hy0, hy1]
      rw [show deriv f x = 0 by rw [hev.deriv_eq]; simp]
      simpa [hG]

/-- A subtype sup bound is preserved by the constant extension. -/
private theorem constExtend_abs_le
    {u : intervalDomainPoint → ℝ} {M : ℝ}
    (hbound : ∀ X, |u X| ≤ M) :
    ∀ x, |ShenWork.IntervalDomain.intervalDomainConstExtend u x| ≤ M := by
  intro x
  by_cases hx0 : x ≤ 0
  · simp [ShenWork.IntervalDomain.intervalDomainConstExtend, hx0,
      hbound ⟨0, ⟨by norm_num, by norm_num⟩⟩]
  · by_cases hx1 : 1 ≤ x
    · simp [ShenWork.IntervalDomain.intervalDomainConstExtend, hx0, hx1,
        hbound ⟨1, ⟨by norm_num, by norm_num⟩⟩]
    · simpa [ShenWork.IntervalDomain.intervalDomainConstExtend, hx0, hx1] using
        hbound ⟨x, ⟨(not_le.mp hx0).le, (not_le.mp hx1).le⟩⟩

/-- At a fixed source slice the Neumann Dirichlet pairing is integrable in
heat time down to zero. -/
private theorem intervalFullSemigroup_dirichletPairing_intervalIntegrable
    {f φ : ℝ → ℝ} {T Cf Cφ Gf Gφ : ℝ}
    (hT : 0 < T) (hf_cont : Continuous f)
    (hCf : 0 ≤ Cf) (hf_bound : ∀ y, |f y| ≤ Cf)
    (hf_ac : AbsolutelyContinuousOnInterval f 0 1)
    (hGf : 0 ≤ Gf) (hf_deriv_bound : ∀ᵐ y ∂volume, |deriv f y| ≤ Gf)
    (hφcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1))
    (hCφ : 0 ≤ Cφ) (hφbound : ∀ y, |φ y| ≤ Cφ)
    (hφ_ac : AbsolutelyContinuousOnInterval φ 0 1)
    (hGφ : 0 ≤ Gφ) (hφ_deriv_bound : ∀ᵐ y ∂volume, |deriv φ y| ≤ Gφ) :
    IntervalIntegrable (fun r => ∫ x,
      deriv (fun z => intervalFullSemigroupOperator r f z) x * deriv φ x
      ∂intervalMeasure 1) volume 0 T := by
  let H : ℝ → ℝ := fun r =>
    ∫ x, intervalFullSemigroupOperator r f x * φ x ∂intervalMeasure 1
  let J : ℝ → ℝ := fun r => ∫ x,
    deriv (fun z => intervalFullSemigroupOperator r f z) x * deriv φ x
    ∂intervalMeasure 1
  have hf_meas : AEStronglyMeasurable f (intervalMeasure 1) :=
    hf_cont.aestronglyMeasurable
  have hφderiv_μ : ∀ᵐ x ∂intervalMeasure 1, |deriv φ x| ≤ Gφ := by
    simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
    exact hφ_deriv_bound.filter_mono ae_restrict_le
  have hHderiv : ∀ r, 0 < r → HasDerivAt H (-J r) r := by
    intro r hr
    simpa [H, J] using
      intervalFullSemigroup_pairing_hasDerivAt_dirichlet
        hr hf_cont hCf hf_bound hf_ac hGf hf_deriv_bound
        hφcont hCφ hφbound hφ_ac hGφ hφ_deriv_bound
  have hJbound : ∀ r, 0 < r → |J r| ≤ Gf * Gφ := by
    intro r hr
    have hSbound : ∀ x,
        |deriv (fun z => intervalFullSemigroupOperator r f z) x| ≤ Gf :=
      ShenWork.Paper2.IntervalNegativePartWeakEnergy.abs_deriv_intervalFullSemigroupOperator_le_of_ac
        hr hf_meas hf_bound hf_ac hGf hf_deriv_bound
    have hconst : Integrable (fun _ : ℝ => Gf * Gφ) (intervalMeasure 1) :=
      integrable_const _
    have hnorm := MeasureTheory.norm_integral_le_of_norm_le hconst (by
      filter_upwards [hφderiv_μ] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hSbound x) hx (abs_nonneg _) hGf)
    have hmass : (intervalMeasure 1).real Set.univ = 1 := by
      rw [intervalMeasure, ShenWork.IntervalDomain.intervalSet,
        measureReal_restrict_apply_univ, measureReal_def, Real.volume_Icc]
      simp
    rw [Real.norm_eq_abs, MeasureTheory.integral_const, hmass, one_smul] at hnorm
    simpa [J] using hnorm
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
  have hderiv_int : IntegrableOn (deriv H) (Set.Ioc (0 : ℝ) T) volume := by
    have hmeas : AEStronglyMeasurable (deriv H)
        (volume.restrict (Set.Ioc (0 : ℝ) T)) :=
      (measurable_deriv H).aestronglyMeasurable
    exact Integrable.of_bound hmeas (Gf * Gφ) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [(hHderiv r hr.1).deriv, Real.norm_eq_abs, abs_neg]
      exact hJbound r hr.1)
  apply hderiv_int.neg.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  change -deriv H r = J r
  rw [(hHderiv r hr.1).deriv]
  simp

/-- Polynomial tests convert weak convergence of uniformly Lipschitz source
slices into convergence of the corresponding Dirichlet pairings. -/
private theorem semigroup_dirichletPairing_polynomial_sub_abs_le
    {F f : ℝ → ℝ} {P : ℝ[X]} {r Cf G δ Cp : ℝ}
    (hr : 0 < r) (hCf : 0 ≤ Cf) (hF_bound : ∀ x, |F x| ≤ Cf)
    (hF_cont : Continuous F) (hG : 0 ≤ G)
    (hF_lip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |F x - F y| ≤ G * |x - y|)
    (hf_ac : AbsolutelyContinuousOnInterval f 0 1)
    (hδ : 0 ≤ δ)
    (hclose : ∀ x ∈ Set.Icc (0 : ℝ) 1, |F x - f x| ≤ δ)
    (hCp : 0 ≤ Cp)
    (hP_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |P.derivative.eval x| ≤ Cp) :
    |(∫ x,
        deriv (fun z => intervalFullSemigroupOperator r F z) x * P.eval x
          ∂intervalMeasure 1) -
      ∫ x, deriv f x * P.eval x ∂intervalMeasure 1| ≤
      (2 * G * Real.sqrt r + δ) *
        (|P.eval 0| + |P.eval 1| + Cp) := by
  let S : ℝ → ℝ := fun x => intervalFullSemigroupOperator r F x
  let B : ℝ := 2 * G * Real.sqrt r + δ
  have hB : 0 ≤ B := add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hG) (Real.sqrt_nonneg _)) hδ
  have hcoeff : ∀ n, |cosineCoeffs F n| ≤ 2 * Cf :=
    cosineCoeffs_abs_le_of_continuous_bounded hF_cont.continuousOn hCf
      (fun x _hx => hF_bound x)
  have hS2 : ContDiff ℝ 2 S := by
    simpa [S] using
      ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_contDiff_two_clean
        hr hF_cont hcoeff
  have hSderiv_cont : Continuous (deriv S) :=
    hS2.continuous_deriv (by norm_num)
  have hPderiv_int : IntervalIntegrable
      (fun x : ℝ => P.derivative.eval x) volume 0 1 :=
    P.derivative.continuous.intervalIntegrable 0 1
  have hSderiv_int : IntervalIntegrable (deriv S) volume 0 1 :=
    hSderiv_cont.intervalIntegrable 0 1
  have hIBPS := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    P.continuous.continuousOn hS2.continuous.continuousOn
    (fun x _hx => P.hasDerivAt x)
    (fun x _hx =>
      (hS2.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0) x).hasDerivAt)
    hPderiv_int hSderiv_int
  have hIBPf :=
    (polynomial_eval_absolutelyContinuousOnInterval P).integral_mul_deriv_eq_deriv_mul
      hf_ac
  have hJS :
      (∫ x, deriv S x * P.eval x ∂intervalMeasure 1) =
        P.eval 1 * S 1 - P.eval 0 * S 0 -
          ∫ x in (0 : ℝ)..1, P.derivative.eval x * S x := by
    rw [intervalMeasure_integral_eq_intervalIntegral]
    calc
      (∫ x in (0 : ℝ)..1, deriv S x * P.eval x) =
          ∫ x in (0 : ℝ)..1, P.eval x * deriv S x := by
        apply intervalIntegral.integral_congr
        intro x _hx
        ring
      _ = _ := by simpa [(P.hasDerivAt (0 : ℝ)).deriv] using hIBPS
  have hJf :
      (∫ x, deriv f x * P.eval x ∂intervalMeasure 1) =
        P.eval 1 * f 1 - P.eval 0 * f 0 -
          ∫ x in (0 : ℝ)..1, P.derivative.eval x * f x := by
    rw [intervalMeasure_integral_eq_intervalIntegral]
    calc
      (∫ x in (0 : ℝ)..1, deriv f x * P.eval x) =
          ∫ x in (0 : ℝ)..1, P.eval x * deriv f x := by
        apply intervalIntegral.integral_congr
        intro x _hx
        ring
      _ = _ := by
        have hPderiv : deriv (fun x : ℝ => P.eval x) =
            fun x => P.derivative.eval x := by
          funext x
          exact (P.hasDerivAt x).deriv
        rw [hPderiv] at hIBPf
        exact hIBPf
  have hSclose : ∀ x ∈ Set.Icc (0 : ℝ) 1, |S x - f x| ≤ B := by
    intro x hx
    calc
      |S x - f x| ≤ |S x - F x| + |F x - f x| := by
        rw [show S x - f x = (S x - F x) + (F x - f x) by ring]
        exact abs_add_le _ _
      _ ≤ 2 * G * Real.sqrt r + δ := by
        exact add_le_add
          (by
            simpa [S] using
              (intervalFullSemigroupOperator_sub_abs_le_of_lipschitzOn
                hr hG hF_cont.continuousOn hF_lip hx))
          (hclose x hx)
      _ = B := rfl
  have hPS_int : IntervalIntegrable
      (fun x => P.derivative.eval x * S x) volume 0 1 :=
    (P.derivative.continuous.mul hS2.continuous).intervalIntegrable 0 1
  have hPf_int : IntervalIntegrable
      (fun x => P.derivative.eval x * f x) volume 0 1 := by
    exact hPderiv_int.mul_continuousOn hf_ac.continuousOn
  have hint_sub :
      (∫ x in (0 : ℝ)..1, P.derivative.eval x * S x) -
          ∫ x in (0 : ℝ)..1, P.derivative.eval x * f x =
        ∫ x in (0 : ℝ)..1, P.derivative.eval x * (S x - f x) := by
    rw [← intervalIntegral.integral_sub hPS_int hPf_int]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  have hint_bound :
      |∫ x in (0 : ℝ)..1, P.derivative.eval x * (S x - f x)| ≤
        B * Cp := by
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := B * Cp)
      (f := fun x => P.derivative.eval x * (S x - f x)) (by
        intro x hx
        have hxI : x ∈ Set.Icc (0 : ℝ) 1 := by
          simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
            Set.uIoc_subset_uIcc hx
        rw [Real.norm_eq_abs, abs_mul]
        simpa [mul_comm] using
          (mul_le_mul (hP_bound x hxI) (hSclose x hxI)
            (abs_nonneg _) hCp))
    simpa [Real.norm_eq_abs] using hn
  change |(∫ x, deriv S x * P.eval x ∂intervalMeasure 1) -
      ∫ x, deriv f x * P.eval x ∂intervalMeasure 1| ≤ _
  rw [hJS, hJf]
  have htri :
      |P.eval 1 * S 1 - P.eval 0 * S 0 -
          (∫ x in (0 : ℝ)..1, P.derivative.eval x * S x) -
        (P.eval 1 * f 1 - P.eval 0 * f 0 -
          ∫ x in (0 : ℝ)..1, P.derivative.eval x * f x)| ≤
        |P.eval 1| * B + |P.eval 0| * B + B * Cp := by
    calc
      |P.eval 1 * S 1 - P.eval 0 * S 0 -
          (∫ x in (0 : ℝ)..1, P.derivative.eval x * S x) -
        (P.eval 1 * f 1 - P.eval 0 * f 0 -
          ∫ x in (0 : ℝ)..1, P.derivative.eval x * f x)| =
          |P.eval 1 * (S 1 - f 1) - P.eval 0 * (S 0 - f 0) -
            ((∫ x in (0 : ℝ)..1, P.derivative.eval x * S x) -
              ∫ x in (0 : ℝ)..1, P.derivative.eval x * f x)| := by
            congr 1
            ring
      _ ≤ |P.eval 1 * (S 1 - f 1)| +
          |P.eval 0 * (S 0 - f 0)| +
          |(∫ x in (0 : ℝ)..1, P.derivative.eval x * S x) -
            ∫ x in (0 : ℝ)..1, P.derivative.eval x * f x| := by
            calc
              |P.eval 1 * (S 1 - f 1) - P.eval 0 * (S 0 - f 0) -
                  ((∫ x in (0 : ℝ)..1, P.derivative.eval x * S x) -
                    ∫ x in (0 : ℝ)..1, P.derivative.eval x * f x)|
                  ≤ |P.eval 1 * (S 1 - f 1) - P.eval 0 * (S 0 - f 0)| +
                      |(∫ x in (0 : ℝ)..1, P.derivative.eval x * S x) -
                        ∫ x in (0 : ℝ)..1, P.derivative.eval x * f x| :=
                    abs_sub _ _
              _ ≤ (|P.eval 1 * (S 1 - f 1)| +
                    |P.eval 0 * (S 0 - f 0)|) +
                  |(∫ x in (0 : ℝ)..1, P.derivative.eval x * S x) -
                    ∫ x in (0 : ℝ)..1, P.derivative.eval x * f x| :=
                    by
                      have hab := abs_sub
                        (P.eval 1 * (S 1 - f 1))
                        (P.eval 0 * (S 0 - f 0))
                      linarith
      _ ≤ |P.eval 1| * B + |P.eval 0| * B + B * Cp := by
        rw [abs_mul, abs_mul, hint_sub]
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left (hSclose 1 (by norm_num)) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (hSclose 0 (by norm_num)) (abs_nonneg _)))
          hint_bound
  calc
    _ ≤ |P.eval 1| * B + |P.eval 0| * B + B * Cp := htri
    _ = B * (|P.eval 0| + |P.eval 1| + Cp) := by ring
    _ = _ := rfl

/-- A bounded multiplier turns an `L¹` approximation of a test into the
corresponding pairing approximation. -/
private theorem integral_pairing_sub_abs_le_of_multiplier_bound
    {a b c : ℝ → ℝ} {G : ℝ} (hG : 0 ≤ G)
    (ha_meas : AEStronglyMeasurable a (intervalMeasure 1))
    (ha_bound : ∀ᵐ x ∂intervalMeasure 1, |a x| ≤ G)
    (hb : Integrable b (intervalMeasure 1))
    (hc : Integrable c (intervalMeasure 1)) :
    |(∫ x, a x * b x ∂intervalMeasure 1) -
      ∫ x, a x * c x ∂intervalMeasure 1| ≤
      G * ∫ x, |b x - c x| ∂intervalMeasure 1 := by
  have hab : Integrable (fun x => a x * b x) (intervalMeasure 1) := by
    exact (hb.bdd_mul ha_meas (by
      filter_upwards [ha_bound] with x hx
      simpa [Real.norm_eq_abs] using hx)).congr
        (Filter.Eventually.of_forall fun x => by ring)
  have hac : Integrable (fun x => a x * c x) (intervalMeasure 1) := by
    exact (hc.bdd_mul ha_meas (by
      filter_upwards [ha_bound] with x hx
      simpa [Real.norm_eq_abs] using hx)).congr
        (Filter.Eventually.of_forall fun x => by ring)
  have hdom : Integrable (fun x => G * |b x - c x|)
      (intervalMeasure 1) := (hb.sub hc).abs.const_mul G
  have hn := MeasureTheory.norm_integral_le_of_norm_le hdom (by
    filter_upwards [ha_bound] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hx le_rfl (abs_nonneg _) hG)
  calc
    |(∫ x, a x * b x ∂intervalMeasure 1) -
        ∫ x, a x * c x ∂intervalMeasure 1| =
        |∫ x, a x * (b x - c x) ∂intervalMeasure 1| := by
      rw [← MeasureTheory.integral_sub hab hac]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ ≤ G * ∫ x, |b x - c x| ∂intervalMeasure 1 := by
      rw [Real.norm_eq_abs, MeasureTheory.integral_const_mul] at hn
      exact hn

/-- On a compact interval, pointwise convergence of a family with one common
Lipschitz modulus is uniform. -/
private theorem tendstoUniformlyOn_Icc_of_common_lipschitz
    {ι : Type*} {l : Filter ι} {F : ι → ℝ → ℝ} {f : ℝ → ℝ} {G : ℝ}
    (hG : 0 ≤ G)
    (hF_lip : ∀ i, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ∀ y ∈ Set.Icc (0 : ℝ) 1, |F i x - F i y| ≤ G * |x - y|)
    (hpoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun i => F i x) l (nhds (f x))) :
    TendstoUniformlyOn F f l (Set.Icc (0 : ℝ) 1) := by
  let X := Set.Icc (0 : ℝ) 1
  let Fs : ι → X → ℝ := fun i x => F i x.1
  let fs : X → ℝ := fun x => f x.1
  have hb : Tendsto (fun r : ℝ => G * r) (nhds 0) (nhds 0) := by
    have hid : Tendsto (fun r : ℝ => r) (nhds 0) (nhds 0) := tendsto_id
    simpa using (tendsto_const_nhds (x := G)).mul hid
  have heq : Equicontinuous Fs :=
    Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => G * r) hb Fs
      (by
        intro x y i
        simpa [Fs, X, Real.dist_eq] using hF_lip i x.1 x.2 y.1 y.2)
  have hp : Tendsto Fs l (nhds fs) := by
    rw [tendsto_pi_nhds]
    intro x
    simpa [Fs, fs, X] using hpoint x.1 x.2
  have hu := (heq.tendsto_uniformFun_iff_pi l fs).2 hp
  have htu : TendstoUniformly Fs fs l := by
    have := UniformFun.tendsto_iff_tendstoUniformly.mp hu
    simpa [Fs, fs] using this
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  simpa [Fs, fs, X] using htu

/-- A uniformly convergent, commonly Lipschitz family of moving source
slices has the expected right heat-time averaged Dirichlet limit. -/
private theorem moving_dirichletAverage_tendsto_of_common_lipschitz
    {F : ℝ → ℝ → ℝ} {f φ : ℝ → ℝ}
    {T Cf Cφ G Gφ : ℝ} (hT : 0 < T)
    (hF_cont : ∀ q, 0 < q → q < T → Continuous (F q))
    (hCf : 0 ≤ Cf)
    (hF_bound : ∀ q, 0 < q → q < T → ∀ x, |F q x| ≤ Cf)
    (hG : 0 ≤ G)
    (hF_lip : ∀ q, 0 < q → q < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |F q x - F q y| ≤ G * |x - y|)
    (hF_ac : ∀ q, 0 < q → q < T →
      AbsolutelyContinuousOnInterval (F q) 0 1)
    (hF_deriv : ∀ q, 0 < q → q < T →
      ∀ᵐ x ∂volume, |deriv (F q) x| ≤ G)
    (hFuniform : TendstoUniformlyOn F f
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (Set.Icc (0 : ℝ) 1))
    (hf_ac : AbsolutelyContinuousOnInterval f 0 1)
    (hf_deriv : ∀ᵐ x ∂volume, |deriv f x| ≤ G)
    (hφcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1))
    (hCφ : 0 ≤ Cφ) (hφbound : ∀ x, |φ x| ≤ Cφ)
    (hφ_ac : AbsolutelyContinuousOnInterval φ 0 1)
    (hGφ : 0 ≤ Gφ)
    (hφ_deriv : ∀ᵐ x ∂volume, |deriv φ x| ≤ Gφ) :
    Tendsto
      (fun q : ℝ => q⁻¹ * ∫ r in (0 : ℝ)..q, ∫ x,
        deriv (fun z => intervalFullSemigroupOperator r (F q) z) x *
          deriv φ x ∂intervalMeasure 1)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x, deriv f x * deriv φ x ∂intervalMeasure 1)) := by
  let μ := intervalMeasure 1
  let L : ℝ := ∫ x, deriv f x * deriv φ x ∂μ
  haveI : IsFiniteMeasure μ :=
    ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
  have hφderiv_on : IntegrableOn (deriv φ) (Set.Icc (0 : ℝ) 1) volume := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    have h := intervalIntegrable_iff.mp hφ_ac.intervalIntegrable_deriv
    simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using h
  have hφderiv_int : Integrable (deriv φ) μ := by
    simpa [μ, intervalMeasure, ShenWork.IntervalDomain.intervalSet] using hφderiv_on
  have hfderiv_μ : ∀ᵐ x ∂μ, |deriv f x| ≤ G := by
    simp only [μ, intervalMeasure, ShenWork.IntervalDomain.intervalSet]
    exact hf_deriv.filter_mono ae_restrict_le
  rw [Metric.tendsto_nhds]
  intro ε hε
  let e : ℝ := ε / 2
  have he : 0 < e := by dsimp [e]; linarith
  let epsP : ℝ := e / (8 * (G + 1))
  have hGden : 0 < G + 1 := by linarith
  have hepsP : 0 < epsP := by
    dsimp [epsP]
    positivity
  obtain ⟨P, hPapprox⟩ :=
    exists_polynomial_intervalMeasure_integral_abs_sub_lt
      hφderiv_int hepsP
  obtain ⟨Cp₀, hCp₀⟩ := isCompact_Icc.bddAbove_image
    P.derivative.continuous.continuousOn.abs
  let Cp : ℝ := max Cp₀ 0
  have hCp : 0 ≤ Cp := le_max_right _ _
  have hPbound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |P.derivative.eval x| ≤ Cp := by
    intro x hx
    exact (hCp₀ (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)
  let Cpoly : ℝ := |P.eval 0| + |P.eval 1| + Cp
  have hCpoly : 0 ≤ Cpoly := by
    dsimp [Cpoly]
    positivity
  let η : ℝ := e / (8 * (Cpoly + 1))
  have hCden : 0 < Cpoly + 1 := by linarith
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have happrox_small : G * epsP < e / 8 := by
    have hlt : G * epsP < (G + 1) * epsP :=
      mul_lt_mul_of_pos_right (by linarith) hepsP
    have heq : (G + 1) * epsP = e / 8 := by
      dsimp [epsP]
      field_simp [hGden.ne']
    linarith
  have hpoly_small : 2 * η * Cpoly < e / 4 := by
    have hlt : 2 * η * Cpoly < 2 * η * (Cpoly + 1) := by
      have h2η : 0 < 2 * η := by positivity
      exact mul_lt_mul_of_pos_left (by linarith) h2η
    have heq : 2 * η * (Cpoly + 1) = e / 4 := by
      dsimp [η]
      field_simp [hCden.ne']
      ring
    linarith
  have hunif_event : ∀ᶠ q in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |F q x - f x| < η := by
    have hu := (Metric.tendstoUniformlyOn_iff.mp hFuniform) η hη
    filter_upwards [hu] with q hq x hx
    simpa [Real.dist_eq, abs_sub_comm] using hq x hx
  have hqid : Tendsto (fun q : ℝ => q)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsqrt : Tendsto (fun q : ℝ => 2 * G * Real.sqrt q)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) := by
    have hs := (Real.continuous_sqrt.tendsto 0).comp hqid
    simpa using (tendsto_const_nhds (x := 2 * G)).mul hs
  have hsqrt_event : ∀ᶠ q in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
      2 * G * Real.sqrt q < η := hsqrt (Iio_mem_nhds hη)
  have hqT : ∀ᶠ q in nhdsWithin 0 (Set.Ioi (0 : ℝ)), q < T :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hT)
  filter_upwards [self_mem_nhdsWithin, hqT, hunif_event, hsqrt_event] with
    q hq hqT hcloseq hsqrtq
  have hqpos : 0 < q := hq
  let J : ℝ → ℝ := fun r => ∫ x,
    deriv (fun z => intervalFullSemigroupOperator r (F q) z) x * deriv φ x ∂μ
  let LP : ℝ := ∫ x, deriv f x * P.eval x ∂μ
  let JP : ℝ → ℝ := fun r => ∫ x,
    deriv (fun z => intervalFullSemigroupOperator r (F q) z) x * P.eval x ∂μ
  have hFq_meas : AEStronglyMeasurable (F q) μ :=
    (hF_cont q hqpos hqT).aestronglyMeasurable
  have hJint : IntervalIntegrable J volume 0 q := by
    simpa [J, μ] using
      intervalFullSemigroup_dirichletPairing_intervalIntegrable
        hqpos (hF_cont q hqpos hqT) hCf (hF_bound q hqpos hqT)
        (hF_ac q hqpos hqT) hG (hF_deriv q hqpos hqT)
        hφcont hCφ hφbound hφ_ac hGφ hφ_deriv
  have hPint : Integrable (fun x : ℝ => P.eval x) μ := by
    have hPon : IntegrableOn (fun x : ℝ => P.eval x)
        (Set.Icc (0 : ℝ) 1) volume :=
      P.continuous.continuousOn.integrableOn_Icc
    simpa [μ, intervalMeasure, ShenWork.IntervalDomain.intervalSet] using hPon
  have hpoint : ∀ r ∈ Set.uIoc (0 : ℝ) q, |J r - L| < e := by
    intro r hr
    have hrpos : 0 < r := by
      rw [Set.uIoc_of_le hqpos.le] at hr
      exact hr.1
    have hrq : r ≤ q := by
      rw [Set.uIoc_of_le hqpos.le] at hr
      exact hr.2
    have hsqrtr : Real.sqrt r ≤ Real.sqrt q :=
      Real.sqrt_le_sqrt hrq
    have hheat_small : 2 * G * Real.sqrt r < η :=
      lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left hsqrtr (mul_nonneg (by norm_num) hG))
        hsqrtq
    have hSbound : ∀ x,
        |deriv (fun z => intervalFullSemigroupOperator r (F q) z) x| ≤ G :=
      ShenWork.Paper2.IntervalNegativePartWeakEnergy.abs_deriv_intervalFullSemigroupOperator_le_of_ac
        hrpos hFq_meas (hF_bound q hqpos hqT)
        (hF_ac q hqpos hqT) hG (hF_deriv q hqpos hqT)
    have hSderiv_μ : ∀ᵐ x ∂μ,
        |deriv (fun z => intervalFullSemigroupOperator r (F q) z) x| ≤ G :=
      Filter.Eventually.of_forall hSbound
    have hJapprox : |J r - JP r| ≤ G *
        (∫ x, |deriv φ x - P.eval x| ∂μ) := by
      simpa [J, JP] using
        integral_pairing_sub_abs_le_of_multiplier_bound hG
          (measurable_deriv _).aestronglyMeasurable hSderiv_μ
          hφderiv_int hPint
    have hLapprox : |L - LP| ≤ G *
        (∫ x, |deriv φ x - P.eval x| ∂μ) := by
      simpa [L, LP] using
        integral_pairing_sub_abs_le_of_multiplier_bound hG
          (measurable_deriv f).aestronglyMeasurable hfderiv_μ
          hφderiv_int hPint
    have hpoly := semigroup_dirichletPairing_polynomial_sub_abs_le
      (F := F q) (f := f) (P := P) (r := r) (Cf := Cf)
      (G := G) (δ := η) (Cp := Cp) hrpos hCf
      (hF_bound q hqpos hqT) (hF_cont q hqpos hqT) hG
      (hF_lip q hqpos hqT) hf_ac hη.le
      (fun x hx => (hcloseq x hx).le) hCp hPbound
    have hpoly' : |JP r - LP| < e / 4 := by
      have hfac : 2 * G * Real.sqrt r + η < 2 * η := by linarith
      have hp : |JP r - LP| ≤
          (2 * G * Real.sqrt r + η) * Cpoly := by
        simpa [JP, LP, Cpoly, μ] using hpoly
      by_cases hCpos : 0 < Cpoly
      · have hmul : (2 * G * Real.sqrt r + η) * Cpoly <
            2 * η * Cpoly := mul_lt_mul_of_pos_right hfac hCpos
        exact hp.trans_lt (hmul.trans hpoly_small)
      · have hCzero : Cpoly = 0 :=
          le_antisymm (le_of_not_gt hCpos) hCpoly
        rw [hCzero, mul_zero] at hp
        have hz : |JP r - LP| = 0 := le_antisymm hp (abs_nonneg _)
        rw [hz]
        positivity
    have hJa : |J r - JP r| < e / 8 :=
      hJapprox.trans_lt
        ((mul_le_mul_of_nonneg_left hPapprox.le hG).trans_lt happrox_small)
    have hLa : |L - LP| < e / 8 :=
      hLapprox.trans_lt
        ((mul_le_mul_of_nonneg_left hPapprox.le hG).trans_lt happrox_small)
    have hLa' : |LP - L| < e / 8 := by
      simpa [abs_sub_comm] using hLa
    calc
      |J r - L| ≤ |J r - JP r| + |JP r - LP| + |LP - L| := by
        calc
          |J r - L| = |(J r - JP r) + (JP r - LP) + (LP - L)| := by
            congr 1
            ring
          _ ≤ |J r - JP r| + |JP r - LP| + |LP - L| := by
            calc
              |(J r - JP r) + (JP r - LP) + (LP - L)| ≤
              |(J r - JP r) + (JP r - LP)| + |LP - L| :=
                    abs_add_le _ _
              _ ≤ (|J r - JP r| + |JP r - LP|) + |LP - L| :=
                    by
                      have hab := abs_add_le (J r - JP r) (JP r - LP)
                      linarith
      _ < e / 8 + e / 4 + e / 8 :=
        add_lt_add (add_lt_add hJa hpoly') hLa'
      _ < e := by linarith
  have hdiff_int : IntervalIntegrable (fun r => J r - L) volume 0 q :=
    hJint.sub (Continuous.intervalIntegrable continuous_const 0 q)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := q) (C := e)
    (f := fun r => J r - L) (fun r hr => by
      rw [Real.norm_eq_abs]
      exact (hpoint r hr).le)
  have hrewrite : q⁻¹ * (∫ r in (0 : ℝ)..q, J r) - L =
      q⁻¹ * ∫ r in (0 : ℝ)..q, (J r - L) := by
    rw [intervalIntegral.integral_sub hJint
      (Continuous.intervalIntegrable continuous_const 0 q),
      intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero]
    field_simp [hqpos.ne']
  change dist (q⁻¹ * ∫ r in (0 : ℝ)..q, J r) L < ε
  rw [Real.dist_eq, hrewrite]
  have hinv : 0 ≤ q⁻¹ := inv_nonneg.mpr hqpos.le
  rw [abs_mul, abs_of_nonneg hinv]
  calc
    q⁻¹ * |∫ r in (0 : ℝ)..q, (J r - L)| ≤ q⁻¹ * (e * |q - 0|) :=
      mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hnorm) hinv
    _ = e := by
      rw [sub_zero, abs_of_pos hqpos]
      calc
        q⁻¹ * (e * q) = e * (q⁻¹ * q) := by ring
        _ = e := by rw [inv_mul_cancel₀ hqpos.ne', mul_one]
    _ < ε := by dsimp [e]; linarith

/-- U-side weak-generator leaf.  Positive-time common-window Lipschitz
control and joint time continuity identify the moving restart slice in the
Neumann Dirichlet average, without a pointwise time derivative or Laplacian. -/
theorem truncatedLimit_moving_dirichletAverage_tendsto
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t Cφ Gφ : ℝ} (ht : 0 < t) (htT : t ≤ DT.T)
    {φ : ℝ → ℝ}
    (hφcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1))
    (hCφ : 0 ≤ Cφ) (hφbound : ∀ x, |φ x| ≤ Cφ)
    (hφ_ac : AbsolutelyContinuousOnInterval φ 0 1)
    (hGφ : 0 ≤ Gφ)
    (hφ_deriv : ∀ᵐ x ∂volume, |deriv φ x| ≤ Gφ) :
    let U := truncatedConjugatePicardLimit p u₀ DT.T
    let E : ℝ → ℝ → ℝ := fun q =>
      ShenWork.IntervalDomain.intervalDomainConstExtend (U (t - q))
    let et : ℝ → ℝ :=
      ShenWork.IntervalDomain.intervalDomainConstExtend (U t)
    Tendsto
      (fun q : ℝ => q⁻¹ * ∫ r in (0 : ℝ)..q, ∫ x,
        deriv (fun z => intervalFullSemigroupOperator r (E q) z) x *
          deriv φ x ∂intervalMeasure 1)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x, deriv et x * deriv φ x ∂intervalMeasure 1)) := by
  let U := truncatedConjugatePicardLimit p u₀ DT.T
  let SD := truncatedConjugateMildSolutionData_of_data DT
  let ext : ℝ → ℝ → ℝ := fun s =>
    ShenWork.IntervalDomain.intervalDomainConstExtend (U s)
  obtain ⟨lo, G, hlo, hlot, hG, hwindow⟩ :=
    _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedPicardLimit_lipschitzOn_positive_window
      DT ht htT
  let T₀ : ℝ := t - lo
  have hT₀ : 0 < T₀ := sub_pos.mpr hlot
  let valid : ℝ → Prop := fun q => 0 < q ∧ q < T₀
  let F : ℝ → ℝ → ℝ := fun q =>
    if valid q then ext (t - q) else ext t
  have hslice_cont : ∀ s, 0 < s → s ≤ DT.T → Continuous (U s) := by
    intro s hs hsT
    simpa [U, SD] using SD.hcont s hs hsT
  have hslice_bound : ∀ s, 0 < s → s ≤ DT.T →
      ∀ X, |U s X| ≤ DT.M := by
    intro s hs hsT X
    simpa [U, SD] using SD.hbound s hs hsT X
  have hslice_lip : ∀ s, lo ≤ s → s ≤ t →
      LipschitzOnWith ⟨G, hG⟩ (ext s) (Set.Icc (0 : ℝ) 1) := by
    intro s hlos hst
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    simpa [ext, Real.dist_eq,
      ShenWork.IntervalDomain.constExtend_eq_lift_on_Icc hx,
      ShenWork.IntervalDomain.constExtend_eq_lift_on_Icc hy] using
      hwindow s hlos hst x hx y hy
  have hslice_ac : ∀ s, lo ≤ s → s ≤ t →
      AbsolutelyContinuousOnInterval (ext s) 0 1 := by
    intro s hlos hst
    have h := hslice_lip s hlos hst
    have hu : Set.Icc (0 : ℝ) 1 = Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num)]
    rw [hu] at h
    exact h.absolutelyContinuousOnInterval
  have hslice_deriv : ∀ s, lo ≤ s → s ≤ t →
      ∀ᵐ x ∂volume, |deriv (ext s) x| ≤ G := by
    intro s hlos hst
    exact constExtend_deriv_abs_le_ae_of_lipschitzOn hG
      (hslice_lip s hlos hst)
  have hvalid_time : ∀ q, valid q →
      lo ≤ t - q ∧ t - q ≤ t ∧ 0 < t - q ∧ t - q ≤ DT.T := by
    intro q hq
    have hqt : q < t - lo := by simpa [valid, T₀] using hq.2
    constructor
    · linarith
    constructor
    · linarith [hq.1]
    constructor
    · linarith [hlo]
    · exact (by linarith [hq.1] : t - q ≤ t).trans htT
  have hF_cont : ∀ q, 0 < q → q < T₀ → Continuous (F q) := by
    intro q hq hqT
    have hv : valid q := ⟨hq, hqT⟩
    rw [show F q = ext (t - q) by simp [F, hv]]
    exact ShenWork.IntervalDomain.constExtend_continuous
      (hslice_cont (t - q) (hvalid_time q hv).2.2.1
        (hvalid_time q hv).2.2.2)
  have hF_bound : ∀ q, 0 < q → q < T₀ → ∀ x, |F q x| ≤ DT.M := by
    intro q hq hqT x
    have hv : valid q := ⟨hq, hqT⟩
    rw [show F q = ext (t - q) by simp [F, hv]]
    exact constExtend_abs_le
      (hslice_bound (t - q) (hvalid_time q hv).2.2.1
        (hvalid_time q hv).2.2.2) x
  have hF_lip_local : ∀ q, 0 < q → q < T₀ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |F q x - F q y| ≤ G * |x - y| := by
    intro q hq hqT x hx y hy
    have hv : valid q := ⟨hq, hqT⟩
    have hl := hslice_lip (t - q) (hvalid_time q hv).1
      (hvalid_time q hv).2.1
    rw [lipschitzOnWith_iff_dist_le_mul] at hl
    simpa [F, hv, Real.dist_eq] using hl x hx y hy
  have hF_ac : ∀ q, 0 < q → q < T₀ →
      AbsolutelyContinuousOnInterval (F q) 0 1 := by
    intro q hq hqT
    have hv : valid q := ⟨hq, hqT⟩
    simpa [F, hv] using hslice_ac (t - q) (hvalid_time q hv).1
      (hvalid_time q hv).2.1
  have hF_deriv : ∀ q, 0 < q → q < T₀ →
      ∀ᵐ x ∂volume, |deriv (F q) x| ≤ G := by
    intro q hq hqT
    have hv : valid q := ⟨hq, hqT⟩
    simpa [F, hv] using hslice_deriv (t - q) (hvalid_time q hv).1
      (hvalid_time q hv).2.1
  have hF_lip_all : ∀ q, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ∀ y ∈ Set.Icc (0 : ℝ) 1, |F q x - F q y| ≤ G * |x - y| := by
    intro q x hx y hy
    by_cases hv : valid q
    · have hl := hslice_lip (t - q) (hvalid_time q hv).1
        (hvalid_time q hv).2.1
      rw [lipschitzOnWith_iff_dist_le_mul] at hl
      simpa [F, hv, Real.dist_eq] using hl x hx y hy
    · have hl := hslice_lip t hlot.le le_rfl
      rw [lipschitzOnWith_iff_dist_le_mul] at hl
      simpa [F, hv, Real.dist_eq] using hl x hx y hy
  have hmap : Tendsto (fun q : ℝ => t - q)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhdsWithin t (Set.Iio t)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : ContinuousAt (fun q : ℝ => t - q) 0 :=
        continuousAt_const.sub continuousAt_id
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact sub_lt_self t hq
  have hvalid_event : ∀ᶠ q in nhdsWithin 0 (Set.Ioi (0 : ℝ)), valid q := by
    have hsmall : ∀ᶠ q in nhdsWithin 0 (Set.Ioi (0 : ℝ)), q < T₀ :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hT₀)
    filter_upwards [self_mem_nhdsWithin, hsmall] with q hq hqT
    exact ⟨hq, hqT⟩
  have hpoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun q => F q x) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (ext t x)) := by
    intro x hx
    let X : intervalDomainPoint := ⟨x, hx⟩
    have hu₁ := truncatedLimit_timeSlice_continuousWithinAt_Iio DT ht htT X
    change Tendsto (fun s => U s X) (nhdsWithin t (Set.Iio t))
      (nhds (U t X)) at hu₁
    have hu := hu₁.comp hmap
    rw [show ext t x = U t X by
      simp [ext, ShenWork.IntervalDomain.constExtend_eq_lift_on_Icc hx,
        intervalDomainLift, hx, X]]
    refine hu.congr' ?_
    filter_upwards [hvalid_event] with q hv
    simp [F, hv, ext, ShenWork.IntervalDomain.constExtend_eq_lift_on_Icc hx,
      intervalDomainLift, hx, X]
  have hFuniform : TendstoUniformlyOn F (ext t)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (Set.Icc (0 : ℝ) 1) :=
    tendstoUniformlyOn_Icc_of_common_lipschitz hG hF_lip_all hpoint
  have hmove := moving_dirichletAverage_tendsto_of_common_lipschitz
    (F := F) (f := ext t) (φ := φ) (T := T₀) (Cf := DT.M)
    (Cφ := Cφ) (G := G) (Gφ := Gφ) hT₀ hF_cont DT.hM.le
    hF_bound hG hF_lip_local hF_ac hF_deriv hFuniform
    (hslice_ac t hlot.le le_rfl) (hslice_deriv t hlot.le le_rfl)
    hφcont hCφ hφbound hφ_ac hGφ hφ_deriv
  have hmove' := hmove.congr' (by
    filter_upwards [hvalid_event] with q hv
    rw [show F q = ext (t - q) by simp [F, hv]])
  simpa [U, ext] using hmove'

/-- Convert a classical expanded subsolution into the weak formulation of
the matched divergence operator.  The derivative of `g` occurs only inside
the classical product rule and is removed by integration by parts. -/
theorem matchedDivergence_weak_subsolution_of_classical
    {χ : ℝ} {W Wt g c φ : ℝ → ℝ}
    (hWc2 : ContDiff ℝ 2 W)
    (hWac : AbsolutelyContinuousOnInterval W 0 1)
    (hWt : ContinuousOn Wt (Set.uIcc (0 : ℝ) 1))
    (hgac : AbsolutelyContinuousOnInterval g 0 1)
    (hg0 : g 0 = 0) (hg1 : g 1 = 0)
    (hc : ContinuousOn c (Set.uIcc (0 : ℝ) 1))
    (hφac : AbsolutelyContinuousOnInterval φ 0 1)
    (hφnonneg : ∀ x, 0 ≤ φ x)
    (hneu0 : deriv W 0 = 0) (hneu1 : deriv W 1 = 0)
    (hres : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      Wt x - deriv (deriv W) x +
          χ * g x * deriv W x + χ * deriv g x * W x - c x * W x ≤ 0) :
    (∫ x, Wt x * φ x ∂intervalMeasure 1) +
        (∫ x, deriv W x * deriv φ x ∂intervalMeasure 1) -
        χ * (∫ x, g x * W x * deriv φ x ∂intervalMeasure 1) -
        ∫ x, c x * W x * φ x ∂intervalMeasure 1 ≤ 0 := by
  let A : ℝ → ℝ := fun x => Wt x * φ x
  let B : ℝ → ℝ := fun x => (-deriv (deriv W) x) * φ x
  let D : ℝ → ℝ := fun x =>
    χ * (deriv g x * W x + g x * deriv W x) * φ x
  let C : ℝ → ℝ := fun x => -(c x * W x * φ x)
  let R : ℝ → ℝ := fun x => A x + B x + D x + C x
  have hφcont := hφac.continuousOn
  have hgcont := hgac.continuousOn
  have hWcont : Continuous W := hWc2.continuous
  have hWxcont : Continuous (deriv W) := hWc2.continuous_deriv (by norm_num)
  have hWxxcont : Continuous (deriv (deriv W)) := by
    have hW' : ContDiff ℝ 1 (deriv W) := by
      simpa using hWc2.deriv'
    exact hW'.continuous_deriv (by norm_num)
  have hWxac : AbsolutelyContinuousOnInterval (deriv W) 0 1 :=
    deriv_absolutelyContinuousOnInterval_of_contDiff_two hWc2
  have hAint : IntervalIntegrable A volume 0 1 := by
    exact (hWt.mul hφcont).intervalIntegrable
  have hBint : IntervalIntegrable B volume 0 1 := by
    exact (hWxxcont.neg.continuousOn.mul hφcont).intervalIntegrable
  have hDfirst : IntervalIntegrable
      (fun x => deriv g x * W x * φ x) volume 0 1 := by
    have hbase := hgac.intervalIntegrable_deriv.mul_continuousOn
      (hWcont.continuousOn.mul hφcont)
    exact hbase.congr (fun x _hx => by simp [Pi.mul_apply]; ring)
  have hDsecond : IntervalIntegrable
      (fun x => g x * deriv W x * φ x) volume 0 1 := by
    exact ((hgcont.mul hWxcont.continuousOn).mul hφcont).intervalIntegrable
  have hDint : IntervalIntegrable D volume 0 1 := by
    have hbase := (hDfirst.add hDsecond).const_mul χ
    exact hbase.congr (fun x _hx => by simp [D]; ring)
  have hCint : IntervalIntegrable C volume 0 1 := by
    exact (((hc.mul hWcont.continuousOn).mul hφcont).neg).intervalIntegrable
  have hRint : IntervalIntegrable R volume 0 1 :=
    ((hAint.add hBint).add hDint).add hCint
  have hRpoint : ∀ x ∈ Set.Ioo (0 : ℝ) 1, R x ≤ 0 := by
    intro x hx
    have hr := hres x hx
    calc
      R x = (Wt x - deriv (deriv W) x +
          χ * g x * deriv W x + χ * deriv g x * W x - c x * W x) *
          φ x := by dsimp [R, A, B, D, C]; ring
      _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hr (hφnonneg x)
  have hRle : (∫ x in (0 : ℝ)..1, R x) ≤ 0 := by
    have hzeroInt : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 1 :=
      Continuous.intervalIntegrable continuous_const 0 1
    have hae : R ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] fun _ => 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        (Measure.ae_ne volume (0 : ℝ)).filter_mono ae_restrict_le,
        (Measure.ae_ne volume (1 : ℝ)).filter_mono ae_restrict_le] with
        x hx hx0 hx1
      have hxoo : x ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
      exact hRpoint x hxoo
    simpa using intervalIntegral.integral_mono_ae_restrict
      (by norm_num : (0 : ℝ) ≤ 1) hRint hzeroInt hae
  have hdiffIBP := hφac.integral_mul_deriv_eq_deriv_mul hWxac
  have hBweak : (∫ x in (0 : ℝ)..1, B x) =
      ∫ x in (0 : ℝ)..1, deriv W x * deriv φ x := by
    have hleft : (∫ x in (0 : ℝ)..1, φ x * deriv (deriv W) x) =
        -(∫ x in (0 : ℝ)..1, deriv φ x * deriv W x) := by
      rw [hneu0, hneu1] at hdiffIBP
      simpa using hdiffIBP
    rw [show (fun x => B x) =
        fun x => -(φ x * deriv (deriv W) x) by
      funext x; simp [B]; ring,
      intervalIntegral.integral_neg, hleft]
    rw [neg_neg]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  have hGWac : AbsolutelyContinuousOnInterval (g * W) 0 1 :=
    hgac.mul hWac
  have hDriftIBP := hGWac.integral_mul_deriv_eq_deriv_mul hφac
  have hprod_deriv :
      (∫ x in (0 : ℝ)..1,
        (deriv g x * W x + g x * deriv W x) * φ x) =
      ∫ x in (0 : ℝ)..1, deriv (g * W) x * φ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hgac.ae_differentiableAt] with x hgd hxU
    have hgdiff := hgd (Set.uIoc_subset_uIcc hxU)
    have hWdiff := hWc2.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0) x
    rw [(hgdiff.hasDerivAt.mul hWdiff.hasDerivAt).deriv]
  have hDriftWeak :
      (∫ x in (0 : ℝ)..1, D x) =
        -χ * ∫ x in (0 : ℝ)..1, g x * W x * deriv φ x := by
    have hboundary : (g * W) 1 * φ 1 - (g * W) 0 * φ 0 = 0 := by
      simp [Pi.mul_apply, hg0, hg1]
    rw [hboundary] at hDriftIBP
    have hcore : (∫ x in (0 : ℝ)..1, deriv (g * W) x * φ x) =
        -(∫ x in (0 : ℝ)..1, g x * W x * deriv φ x) := by
      have h := hDriftIBP
      simp only [zero_sub] at h
      have hleft : (∫ x in (0 : ℝ)..1, (g * W) x * deriv φ x) =
          ∫ x in (0 : ℝ)..1, g x * W x * deriv φ x := by
        apply intervalIntegral.integral_congr
        intro x _hx
        simp [Pi.mul_apply]
      rw [hleft] at h
      linarith
    rw [show (fun x => D x) = fun x =>
        χ * ((deriv g x * W x + g x * deriv W x) * φ x) by
      funext x; simp [D]; ring,
      intervalIntegral.integral_const_mul, hprod_deriv, hcore]
    ring
  have hRexpand : (∫ x in (0 : ℝ)..1, R x) =
      (∫ x in (0 : ℝ)..1, A x) +
        (∫ x in (0 : ℝ)..1, B x) +
        (∫ x in (0 : ℝ)..1, D x) +
        ∫ x in (0 : ℝ)..1, C x := by
    rw [show (fun x => R x) = fun x => ((A x + B x) + D x) + C x by
      funext x; rfl,
      intervalIntegral.integral_add ((hAint.add hBint).add hDint) hCint,
      intervalIntegral.integral_add (hAint.add hBint) hDint,
      intervalIntegral.integral_add hAint hBint]
  have hCweak : (∫ x in (0 : ℝ)..1, C x) =
      -(∫ x in (0 : ℝ)..1, c x * W x * φ x) := by
    rw [show (fun x => C x) = fun x => -(c x * W x * φ x) by
      funext x; rfl, intervalIntegral.integral_neg]
  rw [intervalMeasure_integral_eq_intervalIntegral,
    intervalMeasure_integral_eq_intervalIntegral,
    intervalMeasure_integral_eq_intervalIntegral,
    intervalMeasure_integral_eq_intervalIntegral]
  rw [hRexpand, hBweak, hDriftWeak, hCweak] at hRle
  simpa [A] using hRle

/-! ## Concrete squared barrier for the truncated limit -/

def truncatedBarrierDriftBound (p : CM2Params) (M : ℝ) : ℝ :=
  |p.χ₀| * truncatedDriftFactorC0 p M

def truncatedBarrierReactionNegBound (p : CM2Params) (M : ℝ) : ℝ :=
  p.a + p.b * M ^ p.α + |p.χ₀| * truncatedDriftFactorC1 p M

def truncatedBarrierDiscount (p : CM2Params) (M : ℝ) : ℝ :=
  truncatedBarrierDriftBound p M ^ 2 / 2 +
    truncatedBarrierReactionNegBound p M

theorem truncatedBarrierDriftBound_nonneg
    (p : CM2Params) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ truncatedBarrierDriftBound p M := by
  exact mul_nonneg (abs_nonneg _)
    (by
      dsimp [truncatedDriftFactorC0]
      exact mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num)
          (mul_nonneg p.hν.le (Real.rpow_nonneg hM _))))

theorem truncatedBarrierReactionNegBound_nonneg
    (p : CM2Params) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ truncatedBarrierReactionNegBound p M := by
  have hC1 : 0 ≤ truncatedDriftFactorC1 p M := by
    dsimp [truncatedDriftFactorC1]
    have hH : 0 ≤ ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound p M := by
      dsimp [ShenWork.IntervalResolverWeakBounds.resolverWeakLapBound,
        ShenWork.IntervalResolverWeakBounds.resolverWeakValueBound]
      exact add_nonneg
        (mul_nonneg p.hμ.le
          (mul_nonneg (Real.sqrt_nonneg _)
            (mul_nonneg (by norm_num)
              (mul_nonneg p.hν.le (Real.rpow_nonneg hM _)))))
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM _))
    exact add_nonneg hH (mul_nonneg p.hβ (sq_nonneg _))
  exact add_nonneg
    (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg hM _)))
    (mul_nonneg (abs_nonneg _) hC1)

/-- The squared heat barrier is a weak subsolution of the exact frozen
matched-divergence operator at every positive terminal time.  The derivative
bound on `g` is used only to prove the barrier residual; it is absent from the
resulting weak formulation. -/
theorem truncatedSquareHeatBarrier_weak_subsolution
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T)
    {f : ℝ → ℝ} (hf : Continuous f) {Cf K : ℝ} (hCf : 0 ≤ Cf)
    (hf_bound : ∀ y, |f y| ≤ Cf)
    (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
    {φ : ℝ → ℝ}
    (hφac : AbsolutelyContinuousOnInterval φ 0 1)
    (hφnonneg : ∀ x, 0 ≤ φ x) :
    let U := truncatedConjugatePicardLimit p u₀ DT.T
    let g := truncatedDriftFactor p (U t)
    let c := truncatedReactionCoefficient p (U t)
    let Mbar := truncatedBarrierDiscount p DT.M
    (∫ x,
      ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.barrierTimeDerivRep
        Mbar f t x * φ x ∂intervalMeasure 1) +
      (∫ x, deriv (fun y => squareHeatBarrier Mbar f t y) x * deriv φ x
        ∂intervalMeasure 1) -
      p.χ₀ * (∫ x, g x * squareHeatBarrier Mbar f t x * deriv φ x
        ∂intervalMeasure 1) -
      ∫ x, c x * squareHeatBarrier Mbar f t x * φ x
        ∂intervalMeasure 1 ≤ 0 := by
  let U := truncatedConjugatePicardLimit p u₀ DT.T
  let g := truncatedDriftFactor p (U t)
  let c := truncatedReactionCoefficient p (U t)
  let A := truncatedBarrierDriftBound p DT.M
  let D := truncatedBarrierReactionNegBound p DT.M
  let Mbar := truncatedBarrierDiscount p DT.M
  let W : ℝ → ℝ := fun x => squareHeatBarrier Mbar f t x
  let Wt : ℝ → ℝ :=
    ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.barrierTimeDerivRep
      Mbar f t
  have hUcont : Continuous (U t) := by
    simpa [U] using (truncatedConjugateMildSolutionData_of_data DT).hcont t ht htT
  have hUbound : ∀ X, |U t X| ≤ DT.M := by
    intro X
    simpa [U] using
      (truncatedConjugateMildSolutionData_of_data DT).hbound t ht htT X
  obtain ⟨hgcont, hgac, hg0, hg1, hgbound, hgderiv⟩ :=
    truncatedDriftFactor_regular p hUcont DT.hM.le hUbound
  have hccont : ContinuousOn c (Set.uIcc (0 : ℝ) 1) := by
    have hlift : ContinuousOn (intervalDomainLift (U t))
        (Set.Icc (0 : ℝ) 1) := intervalDomainLift_continuousOn_Icc hUcont
    have hp : ContinuousOn
        (fun x => positivePart (intervalDomainLift (U t) x))
        (Set.Icc (0 : ℝ) 1) := by
      simpa [positivePart] using
        continuous_max.comp_continuousOn (hlift.prodMk continuousOn_const)
    have hpow := hp.rpow_const (fun _ _ => Or.inr p.hα.le)
    have hcI : ContinuousOn c (Set.Icc (0 : ℝ) 1) := by
      simpa [c, truncatedReactionCoefficient] using
        continuousOn_const.sub (continuousOn_const.mul hpow)
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hcI
  have hS2 :=
    ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_contDiff_two_clean
      ht hf hK
  have hWc2 : ContDiff ℝ 2 W := by
    have hmodel : ContDiff ℝ 2 (fun x => Real.exp (-Mbar * t) *
        (intervalFullSemigroupOperator t f x *
          intervalFullSemigroupOperator t f x)) :=
      contDiff_const.mul (hS2.mul hS2)
    simpa [W, squareHeatBarrier, pow_two] using hmodel
  have hreg :=
    ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.squareHeatBarrierSliceRegularData_of_semigroup
      (M := Mbar) ht hf hCf hf_bound hK hl2
  have hWtcont : ContinuousOn Wt (Set.uIcc (0 : ℝ) 1) := by
    have hjoint :=
      ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.barrierTimeDerivRep_continuousOn_Ioi
        (M := Mbar) hK
    have hcomp : Continuous (fun x : ℝ => ((t, x) : ℝ × ℝ)) := by fun_prop
    have hI : ContinuousOn Wt (Set.Icc (0 : ℝ) 1) := by
      exact hjoint.comp hcomp.continuousOn
        (fun x hx => ⟨ht, Set.mem_univ x⟩)
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hI
  have hneu0 : deriv W 0 = 0 := by
    rw [(hreg.hasDerivAt 0 (by norm_num)).deriv]
    simp [ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.barrierSpaceDerivRep,
      ShenWork.IntervalFullKernelRegularity.unitIntervalCosineHeatGradientValue_eq_zero_at_zero]
  have hneu1 : deriv W 1 = 0 := by
    rw [(hreg.hasDerivAt 1 (by norm_num)).deriv]
    simp [ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.barrierSpaceDerivRep,
      ShenWork.IntervalFullKernelRegularity.unitIntervalCosineHeatGradientValue_eq_zero_at_one]
  have hA : 0 ≤ A := by
    exact truncatedBarrierDriftBound_nonneg p DT.hM.le
  have hD : 0 ≤ D := by
    exact truncatedBarrierReactionNegBound_nonneg p DT.hM.le
  have hMbar : A ^ 2 / 2 + D ≤ Mbar := by
    rfl
  let Bcoef : ℝ → ℝ → ℝ := fun _ x => -p.χ₀ * g x
  let Ccoef : ℝ → ℝ → ℝ := fun _ x => c x - p.χ₀ * deriv g x
  have hBbound : ∀ r x, 0 < r → r < t → x ∈ Set.Ioo (0 : ℝ) 1 →
      |Bcoef r x| ≤ A := by
    intro r x _hr _hrt hx
    dsimp [Bcoef, A, truncatedBarrierDriftBound]
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left
      (hgbound x (Set.Ioo_subset_Icc_self hx)) (abs_nonneg _)
  have hcabs : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |c x| ≤ p.a + p.b * DT.M ^ p.α := by
    intro x hx
    let X : intervalDomainPoint := ⟨x, Set.Ioo_subset_Icc_self hx⟩
    have hUx : |intervalDomainLift (U t) x| ≤ DT.M := by
      simpa [intervalDomainLift, Set.Ioo_subset_Icc_self hx, X] using hUbound X
    have hpM : positivePart (intervalDomainLift (U t) x) ≤ DT.M := by
      have hpabs : |positivePart (intervalDomainLift (U t) x)| ≤ DT.M := by
        by_cases hpos : 0 ≤ intervalDomainLift (U t) x
        · simpa [positivePart, max_eq_left hpos] using hUx
        · have hle := le_of_not_ge hpos
          simp [positivePart, max_eq_right hle, DT.hM.le]
      simpa [abs_of_nonneg (positivePart_nonneg _)] using hpabs
    have hpow : positivePart (intervalDomainLift (U t) x) ^ p.α ≤
        DT.M ^ p.α := Real.rpow_le_rpow
          (positivePart_nonneg _) hpM p.hα.le
    have hterm : |p.b * positivePart (intervalDomainLift (U t) x) ^ p.α| ≤
        p.b * DT.M ^ p.α := by
      rw [abs_mul, abs_of_nonneg p.hb, abs_of_nonneg
        (Real.rpow_nonneg (positivePart_nonneg _) _)]
      exact mul_le_mul_of_nonneg_left hpow p.hb
    change |p.a - p.b * positivePart (intervalDomainLift (U t) x) ^ p.α| ≤ _
    exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg p.ha]
      exact add_le_add le_rfl hterm)
  have hCbound : ∀ r x, 0 < r → r < t → x ∈ Set.Ioo (0 : ℝ) 1 →
      -Ccoef r x ≤ D := by
    intro r x _hr _hrt hx
    have hc' := hcabs x hx
    have hg' := hgderiv x hx
    dsimp [Ccoef, D, truncatedBarrierReactionNegBound]
    calc
      -(c x - p.χ₀ * deriv g x)
          ≤ |c x| + |p.χ₀| * |deriv g x| := by
            have h1 := neg_le_abs (c x)
            have h2 := le_abs_self (p.χ₀ * deriv g x)
            rw [abs_mul] at h2
            linarith
      _ ≤ (p.a + p.b * DT.M ^ p.α) +
          |p.χ₀| * truncatedDriftFactorC1 p DT.M :=
        add_le_add hc' (mul_le_mul_of_nonneg_left hg' (abs_nonneg _))
      _ = p.a + p.b * DT.M ^ p.α +
          |p.χ₀| * truncatedDriftFactorC1 p DT.M := by ring
  have hresidual : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      Wt x - deriv (deriv W) x +
          p.χ₀ * g x * deriv W x + p.χ₀ * deriv g x * W x - c x * W x ≤ 0 := by
    intro x hx
    let τ : ℝ := t / 2
    let s : ℝ := t / 2
    have hτ : 0 < τ := by dsimp [τ]; linarith
    have hs : 0 < s := by dsimp [s]; linarith
    have hst : s < t := by dsimp [s]; linarith
    have hadd : τ + s = t := by dsimp [τ, s]; ring
    have hderiv := squareHeatRestartDerivativeData_of_semigroup
      (L := t) (τ := τ) (M := Mbar) hτ hf hK hl2
    have hcalc := restartedSquareHeatBarrier_calculus
      (B := Bcoef) (C := Ccoef) hderiv
    have hres := restarted_squareHeatBarrier_subsolution_residual_nonpos
      (L := t) (τ := τ) (A := A) (D := D) (M := Mbar)
      (f := f) (B := Bcoef) (C := Ccoef)
      hcalc hMbar hBbound hCbound s x hs hst hx
    have htime :=
      ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.squareHeatBarrier_time_hasDerivAt_rep
        (M := Mbar) (t := t) (x := x) ht hf hK
          (Set.Ioo_subset_Icc_self hx)
    rw [neumannLinearDriftResidual] at hres
    simp only [restartedSquareHeatBarrier, restartTimeShift] at hres
    have htime' := htime
    rw [← hadd] at htime'
    have hshift : HasDerivAt
        (fun r : ℝ => squareHeatBarrier Mbar f (τ + r) x)
        (ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.barrierTimeDerivRep
          Mbar f (τ + s) x) s := by
      simpa [Function.comp_def] using
        htime'.comp s ((hasDerivAt_const s τ).add (hasDerivAt_id s))
    rw [hshift.deriv, hadd] at hres
    dsimp [W, Wt, Bcoef, Ccoef] at hres ⊢
    linarith
  simpa [U, g, c, Mbar, W, Wt] using
    (matchedDivergence_weak_subsolution_of_classical
      (χ := p.χ₀) (W := W) (Wt := Wt) (g := g) (c := c) (φ := φ)
      hWc2 hreg.absolutelyContinuous hWtcont hgac hg0 hg1 hccont hφac
      hφnonneg hneu0 hneu1 hresidual)

/-! ## Terminal Stampacchia test for the concrete comparison -/

/-- Positive-time regularity of the truncated slice and the squared heat
barrier supplies the bounded absolutely-continuous terminal test
`(W(t)-U(t))₊`. -/
def truncatedSquareHeatBarrier_terminalTestData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {Mbar t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T)
    {f : ℝ → ℝ} (hf : Continuous f) {Cf K : ℝ} (hCf : 0 ≤ Cf)
    (hf_bound : ∀ y, |f y| ≤ Cf)
    (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2) :
    let W : intervalDomainPoint → ℝ :=
      fun X => squareHeatBarrier Mbar f t X.1
    let U := truncatedConjugatePicardLimit p u₀ DT.T t
    ComparisonTerminalTestData W U := by
  let W : intervalDomainPoint → ℝ :=
    fun X => squareHeatBarrier Mbar f t X.1
  let U := truncatedConjugatePicardLimit p u₀ DT.T t
  let Ct : ℝ := Real.exp (-Mbar * t) * Cf ^ 2
  have hCt : 0 ≤ Ct := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hreg :=
    ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.squareHeatBarrierSliceRegularData_of_semigroup
      (M := Mbar) ht hf hCf hf_bound hK hl2
  have hwcont : Continuous W := hreg.continuous.comp continuous_subtype_val
  have hucont : Continuous U := by
    simpa [U] using (truncatedConjugateMildSolutionData_of_data DT).hcont t ht htT
  have hSbound : ∀ x, |intervalFullSemigroupOperator t f x| ≤ Cf :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      ht hCf hf_bound
  have hwbound : ∀ X, |W X| ≤ Ct := by
    intro X
    dsimp [W, Ct, squareHeatBarrier]
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (hSbound X.1) 2)
      (Real.exp_pos _).le
  have hubound : ∀ X, |U X| ≤ DT.M := by
    intro X
    simpa [U] using
      (truncatedConjugateMildSolutionData_of_data DT).hbound t ht htT X
  let Gw : ℝ := Classical.choose hreg.deriv_bounded
  have hGwdata := Classical.choose_spec hreg.deriv_bounded
  have hGw : 0 ≤ Gw := hGwdata.1
  have hGwbound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.barrierSpaceDerivRep
        Mbar f t x| ≤ Gw := hGwdata.2
  have hwLip : LipschitzOnWith ⟨Gw, hGw⟩
      (fun x => squareHeatBarrier Mbar f t x) (Set.Icc (0 : ℝ) 1) := by
    apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (convex_Icc (0 : ℝ) 1)
    · intro x hx
      exact (hreg.hasDerivAt x hx).hasDerivWithinAt
    · intro x hx
      rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mk, Real.norm_eq_abs]
      simpa [(hreg.hasDerivAt x hx).deriv] using hGwbound x hx
  have hw_lip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift W x - intervalDomainLift W y| ≤
        Gw * |x - y| := by
    rw [lipschitzOnWith_iff_dist_le_mul] at hwLip
    intro x hx y hy
    have h := hwLip x hx y hy
    simpa [W, intervalDomainLift, hx, hy, Real.dist_eq] using h
  have hu_lip_data :=
    _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedPicardLimit_lipschitzOn_positive_time
      DT ht htT
  let Gu : ℝ := Classical.choose hu_lip_data
  have hGu_data := Classical.choose_spec hu_lip_data
  have hGu : 0 ≤ Gu := hGu_data.1
  have hu_lip := hGu_data.2
  exact comparisonTerminalTestData_of_lipschitz hwcont hucont hCt hwbound
    DT.hM.le hubound hGw hw_lip hGu (by simpa [U, Gu] using hu_lip)

private theorem ae_mem_unitInterval :
    ∀ᵐ x ∂intervalMeasure 1, x ∈ Set.Icc (0 : ℝ) 1 := by
  simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
  exact ae_restrict_mem measurableSet_Icc

/-! ## Backward comparison-energy increment -/

/-- The positive comparison energy increment is controlled by the weak
barrier remainder and the two tested nonlinear tails of the truncated mild
restart. -/
theorem truncatedBarrierComparison_backward_energy_increment_le
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {Mbar a t : ℝ} (ha : 0 < a) (hat : a < t) (htT : t ≤ DT.T)
    {f : ℝ → ℝ} (hf : Continuous f) {Cf K : ℝ} (hCf : 0 ≤ Cf)
    (hf_bound : ∀ y, |f y| ≤ Cf)
    (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2) :
    let W : ℝ → intervalDomainPoint → ℝ :=
      fun r X => squareHeatBarrier Mbar f r X.1
    let U := truncatedConjugatePicardLimit p u₀ DT.T
    let φ := comparisonPositivePartLift W U t
    comparisonPositivePartEnergy W U t - comparisonPositivePartEnergy W U a ≤
      2 * ((∫ x,
          (squareHeatBarrier Mbar f t x -
            intervalFullSemigroupOperator (t - a)
              (fun y => squareHeatBarrier Mbar f a y) x) * φ x
          ∂intervalMeasure 1) -
        p.χ₀ * (∫ s in a..t, ∫ x,
          truncatedChemFluxLifted p (U s) x *
            deriv (fun z => intervalFullSemigroupOperator (t - s) φ z) x
          ∂intervalMeasure 1) -
        ∫ s in a..t, ∫ x,
          intervalFullSemigroupOperator (t - s)
            (truncatedLogisticLifted p (U s)) x * φ x
          ∂intervalMeasure 1) := by
  let W : ℝ → intervalDomainPoint → ℝ :=
    fun r X => squareHeatBarrier Mbar f r X.1
  let U := truncatedConjugatePicardLimit p u₀ DT.T
  let φ : ℝ → ℝ := comparisonPositivePartLift W U t
  let fa : ℝ → ℝ := fun x =>
    squareHeatBarrier Mbar f a x - intervalDomainLift (U a) x
  let ut : ℝ → ℝ := fun x =>
    squareHeatBarrier Mbar f t x - intervalDomainLift (U t) x
  let BR : ℝ → ℝ := fun x => squareHeatBarrier Mbar f t x -
    intervalFullSemigroupOperator (t - a)
      (fun y => squareHeatBarrier Mbar f a y) x
  let BT : ℝ → ℝ := fun x => ∫ s in a..t,
    intervalConjugateKernelOperator (t - s)
      (truncatedChemFluxLifted p (U s)) x
  let LT : ℝ → ℝ := fun x => ∫ s in a..t,
    intervalFullSemigroupOperator (t - s)
      (truncatedLogisticLifted p (U s)) x
  let z : ℝ → ℝ := fun x => BR x + p.χ₀ * BT x - LT x
  let CP : ℝ → ℝ := fun s => ∫ x,
    truncatedChemFluxLifted p (U s) x *
      deriv (fun y => intervalFullSemigroupOperator (t - s) φ y) x
    ∂intervalMeasure 1
  let LP : ℝ → ℝ := fun s => ∫ x,
    intervalFullSemigroupOperator (t - s)
      (truncatedLogisticLifted p (U s)) x * φ x
    ∂intervalMeasure 1
  have ht : 0 < t := ha.trans hat
  have haT : a ≤ DT.T := (le_of_lt hat).trans htT
  let Ca : ℝ := Real.exp (-Mbar * a) * Cf ^ 2
  let Ct : ℝ := Real.exp (-Mbar * t) * Cf ^ 2
  let Cfa : ℝ := Ca + DT.M
  have hCa : 0 ≤ Ca := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hCt : 0 ≤ Ct := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hCfa : 0 ≤ Cfa := add_nonneg hCa DT.hM.le
  have hUa_cont : Continuous (U a) := by
    simpa [U] using (truncatedConjugateMildSolutionData_of_data DT).hcont a ha haT
  have hUt_cont : Continuous (U t) := by
    simpa [U] using (truncatedConjugateMildSolutionData_of_data DT).hcont t ht htT
  have hUa_bound : ∀ X, |U a X| ≤ DT.M := by
    intro X
    simpa [U] using
      (truncatedConjugateMildSolutionData_of_data DT).hbound a ha haT X
  have hUt_bound : ∀ X, |U t X| ≤ DT.M := by
    intro X
    simpa [U] using
      (truncatedConjugateMildSolutionData_of_data DT).hbound t ht htT X
  have hSa_bound : ∀ x, |intervalFullSemigroupOperator a f x| ≤ Cf :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      ha hCf hf_bound
  have hSt_bound : ∀ x, |intervalFullSemigroupOperator t f x| ≤ Cf :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      ht hCf hf_bound
  have hWa_bound : ∀ x, |squareHeatBarrier Mbar f a x| ≤ Ca := by
    intro x
    dsimp [squareHeatBarrier, Ca]
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (hSa_bound x) 2) (Real.exp_pos _).le
  have hWt_bound : ∀ x, |squareHeatBarrier Mbar f t x| ≤ Ct := by
    intro x
    dsimp [squareHeatBarrier, Ct]
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (hSt_bound x) 2) (Real.exp_pos _).le
  have hUa_lift_bound : ∀ x, |intervalDomainLift (U a) x| ≤ DT.M := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · simpa [intervalDomainLift, hx] using hUa_bound ⟨x, hx⟩
    · simp [intervalDomainLift, hx, DT.hM.le]
  have hUt_lift_bound : ∀ x, |intervalDomainLift (U t) x| ≤ DT.M := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · simpa [intervalDomainLift, hx] using hUt_bound ⟨x, hx⟩
    · simp [intervalDomainLift, hx, DT.hM.le]
  have hfa_bound : ∀ x, |fa x| ≤ Cfa := by
    intro x
    exact (abs_sub _ _).trans (by
      simpa [fa, Cfa] using add_le_add (hWa_bound x) (hUa_lift_bound x))
  have hUa_lift_meas : AEStronglyMeasurable (intervalDomainLift (U a))
      (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
      (intervalDomainLift_continuousOn_Icc hUa_cont)
  have hUt_lift_meas : AEStronglyMeasurable (intervalDomainLift (U t))
      (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
      (intervalDomainLift_continuousOn_Icc hUt_cont)
  have hWa_cont :=
    (ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.squareHeatBarrierSliceRegularData_of_semigroup
      (M := Mbar) ha hf hCf hf_bound hK hl2).continuous
  have hWt_cont :=
    (ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.squareHeatBarrierSliceRegularData_of_semigroup
      (M := Mbar) ht hf hCf hf_bound hK hl2).continuous
  have hfa_meas : AEStronglyMeasurable fa (intervalMeasure 1) := by
    exact hWa_cont.aestronglyMeasurable.sub hUa_lift_meas
  have hfa_int : Integrable fa (intervalMeasure 1) :=
    ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      hfa_meas hfa_bound
  have hWa_int : Integrable (fun x => squareHeatBarrier Mbar f a x)
      (intervalMeasure 1) :=
    ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      hWa_cont.aestronglyMeasurable hWa_bound
  have hUa_int : Integrable (intervalDomainLift (U a)) (intervalMeasure 1) :=
    ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      hUa_lift_meas hUa_lift_bound
  have hut_meas : AEStronglyMeasurable ut (intervalMeasure 1) := by
    exact hWt_cont.aestronglyMeasurable.sub hUt_lift_meas
  have hut_bound : ∀ x, |ut x| ≤ Ct + DT.M := by
    intro x
    exact (abs_sub _ _).trans (add_le_add (hWt_bound x) (hUt_lift_bound x))
  have huE : Integrable (fun x => positivePart (ut x) ^ 2)
      (intervalMeasure 1) := by
    have hpcont : Continuous (fun r : ℝ => positivePart r) := by
      simpa [positivePart] using continuous_id.max continuous_const
    apply ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      (M := (Ct + DT.M) ^ 2)
      ((hpcont.comp_aestronglyMeasurable hut_meas).pow 2)
    intro x
    rw [Pi.pow_apply, abs_pow]
    have hp := (abs_positivePart_le_abs (ut x)).trans (hut_bound x)
    exact pow_le_pow_left₀ (abs_nonneg _) hp 2
  have hScont : Continuous (fun x => intervalFullSemigroupOperator (t - a) fa x) :=
    ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
      (sub_pos.mpr hat) hCfa hfa_bound hfa_meas
  have hSbound : ∀ x, |intervalFullSemigroupOperator (t - a) fa x| ≤ Cfa :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      (sub_pos.mpr hat) hCfa hfa_bound
  have hSE : Integrable
      (fun x => positivePart (intervalFullSemigroupOperator (t - a) fa x) ^ 2)
      (intervalMeasure 1) := by
    have hpcont : Continuous (fun r : ℝ => positivePart r) := by
      simpa [positivePart] using continuous_id.max continuous_const
    apply ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      ((hpcont.comp hScont).pow 2 |>.aestronglyMeasurable)
    intro x
    rw [abs_pow]
    have hp := (abs_positivePart_le_abs
      (intervalFullSemigroupOperator (t - a) fa x)).trans (hSbound x)
    exact pow_le_pow_left₀ (abs_nonneg _) hp 2
  let Hφ : ComparisonTerminalTestData (W t) (U t) :=
    truncatedSquareHeatBarrier_terminalTestData DT ht htT hf hCf hf_bound hK hl2
  have hφmeas : AEStronglyMeasurable φ (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
      Hφ.continuousOn
  obtain ⟨hLint, _hLPint, hLpair⟩ :=
    truncatedLimit_logistic_tail_pairing DT ha hat htT hφmeas Hφ.C_nonneg Hφ.bound
  obtain ⟨hBint, _hCPint, hBpair⟩ :=
    truncatedLimit_chem_tail_pairing DT ha hat htT hφmeas Hφ.C_nonneg Hφ.bound
  change Integrable (fun x => LT x * φ x) (intervalMeasure 1) at hLint
  change Integrable (fun x => BT x * φ x) (intervalMeasure 1) at hBint
  have hSWa_cont :=
    ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
      (sub_pos.mpr hat) hCa hWa_bound hWa_cont.aestronglyMeasurable
  have hSWa_bound : ∀ x,
      |intervalFullSemigroupOperator (t - a)
        (fun y => squareHeatBarrier Mbar f a y) x| ≤ Ca :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      (sub_pos.mpr hat) hCa hWa_bound
  have hBRint : Integrable (fun x => BR x * φ x) (intervalMeasure 1) := by
    haveI : IsFiniteMeasure (intervalMeasure 1) :=
      ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
    exact Integrable.of_bound
      ((hWt_cont.aestronglyMeasurable.sub hSWa_cont.aestronglyMeasurable).mul hφmeas)
      ((Ct + Ca) * Hφ.C) (by
        filter_upwards [] with x
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul
          ((abs_sub _ _).trans (add_le_add (hWt_bound x) (hSWa_bound x)))
          (Hφ.bound x) (abs_nonneg _) (add_nonneg hCt hCa))
  have hcomb : Integrable (fun x =>
      BR x * φ x + p.χ₀ * (BT x * φ x) - LT x * φ x)
      (intervalMeasure 1) :=
    (hBRint.add (hBint.const_mul p.χ₀)).sub hLint
  have hpair : Integrable (fun x => (2 * positivePart (ut x)) * z x)
      (intervalMeasure 1) := by
    have hbase := hcomb.const_mul 2
    apply hbase.congr
    filter_upwards [ae_mem_unitInterval] with x hx
    simp only [ut, z, BR, BT, LT, φ, comparisonPositivePartLift,
      W, intervalDomainLift, dif_pos hx]
    ring
  have hrepr : ∀ᵐ x ∂intervalMeasure 1,
      ut x = intervalFullSemigroupOperator (t - a) fa x + z x := by
    filter_upwards [ae_mem_unitInterval] with x hx
    let X : intervalDomainPoint := ⟨x, hx⟩
    have hr := truncatedLimit_backward_restart DT ha hat htT X
    have hKWa :=
      ShenWork.IntervalDuhamelIntegrability.kernel_mul_integrable_of_source_integrable
        (sub_pos.mpr hat) x hWa_int hCa hWa_bound
    have hKUa :=
      ShenWork.IntervalDuhamelIntegrability.kernel_mul_integrable_of_source_integrable
        (sub_pos.mpr hat) x hUa_int DT.hM.le hUa_lift_bound
    have hlin :=
      ShenWork.IntervalGradDuhamelBound.intervalFullSemigroupOperator_sub hKWa hKUa
    have hr' : intervalDomainLift (U t) x =
        intervalFullSemigroupOperator (t - a) (intervalDomainLift (U a)) x +
          (-p.χ₀) * BT x + LT x := by
      simpa [U, BT, LT, intervalDomainLift, hx, X] using hr
    dsimp [ut, fa, z, BR]
    rw [hlin, hr']
    ring
  have hinc := positivePartEnergy_sub_le_remainder_pairing
    (h := t - a) (f := fa) (u := ut) (z := z) (M := Cfa)
    (sub_pos.mpr hat) hfa_meas hfa_bound hrepr huE hSE hpair
  have hpair_integral :
      (∫ x, (2 * positivePart (ut x)) * z x ∂intervalMeasure 1) =
        2 * ((∫ x, BR x * φ x ∂intervalMeasure 1) -
          p.χ₀ * (∫ s in a..t, CP s) - ∫ s in a..t, LP s) := by
    calc
      (∫ x, (2 * positivePart (ut x)) * z x ∂intervalMeasure 1) =
          2 * (∫ x, BR x * φ x + p.χ₀ * (BT x * φ x) -
            LT x * φ x ∂intervalMeasure 1) := by
        rw [← MeasureTheory.integral_const_mul]
        apply integral_congr_ae
        filter_upwards [ae_mem_unitInterval] with x hx
        simp only [ut, z, BR, BT, LT, φ, comparisonPositivePartLift,
          W, intervalDomainLift, dif_pos hx]
        ring
      _ = 2 * ((∫ x, BR x * φ x ∂intervalMeasure 1) +
          p.χ₀ * (∫ x, BT x * φ x ∂intervalMeasure 1) -
          ∫ x, LT x * φ x ∂intervalMeasure 1) := by
        congr 1
        have hsub := MeasureTheory.integral_sub
          (hBRint.add (hBint.const_mul p.χ₀)) hLint
        have hadd := MeasureTheory.integral_add hBRint (hBint.const_mul p.χ₀)
        have hconst := MeasureTheory.integral_const_mul
          (μ := intervalMeasure 1) p.χ₀ (fun x => BT x * φ x)
        calc
          (∫ x, BR x * φ x + p.χ₀ * (BT x * φ x) - LT x * φ x
              ∂intervalMeasure 1) =
              (∫ x, BR x * φ x + p.χ₀ * (BT x * φ x)
                ∂intervalMeasure 1) -
                ∫ x, LT x * φ x ∂intervalMeasure 1 := by
                  simpa only [Pi.add_apply, Pi.sub_apply] using hsub
          _ = ((∫ x, BR x * φ x ∂intervalMeasure 1) +
                ∫ x, p.χ₀ * (BT x * φ x) ∂intervalMeasure 1) -
                ∫ x, LT x * φ x ∂intervalMeasure 1 := by
                  rw [show (∫ x, BR x * φ x + p.χ₀ * (BT x * φ x)
                    ∂intervalMeasure 1) =
                    (∫ x, BR x * φ x ∂intervalMeasure 1) +
                      ∫ x, p.χ₀ * (BT x * φ x) ∂intervalMeasure 1 by
                        simpa only [Pi.add_apply] using hadd]
          _ = _ := by rw [hconst]
      _ = 2 * ((∫ x, BR x * φ x ∂intervalMeasure 1) -
          p.χ₀ * (∫ s in a..t, CP s) - ∫ s in a..t, LP s) := by
        have hb : (∫ x, BT x * φ x ∂intervalMeasure 1) =
            -(∫ s in a..t, CP s) := by
          simpa [BT, CP, U, φ] using hBpair
        have hl : (∫ x, LT x * φ x ∂intervalMeasure 1) =
            ∫ s in a..t, LP s := by
          simpa [LT, LP, U, φ] using hLpair
        rw [hb, hl]
        ring
  rw [hpair_integral] at hinc
  have hEt : (∫ x, positivePart (ut x) ^ 2 ∂intervalMeasure 1) =
      comparisonPositivePartEnergy W U t := by
    unfold comparisonPositivePartEnergy
    apply integral_congr_ae
    filter_upwards [ae_mem_unitInterval] with x hx
    change positivePart
        (squareHeatBarrier Mbar f t x - intervalDomainLift (U t) x) ^ 2 =
      positivePart
        (intervalDomainLift (W t) x - intervalDomainLift (U t) x) ^ 2
    congr 2
    simp [W, intervalDomainLift, hx]
  have hEa : (∫ x, positivePart (fa x) ^ 2 ∂intervalMeasure 1) =
      comparisonPositivePartEnergy W U a := by
    unfold comparisonPositivePartEnergy
    apply integral_congr_ae
    filter_upwards [ae_mem_unitInterval] with x hx
    change positivePart
        (squareHeatBarrier Mbar f a x - intervalDomainLift (U a) x) ^ 2 =
      positivePart
        (intervalDomainLift (W a) x - intervalDomainLift (U a) x) ^ 2
    congr 2
    simp [W, intervalDomainLift, hx]
  rw [hEt, hEa] at hinc
  simpa [BR, CP, LP, W, U, φ] using hinc

/-- Refined backward supporting-line increment.  Unlike the Markov
contraction estimate above, this identity retains the solution's Neumann
Dirichlet contribution, which is the diffusion term needed for matched-form
drift absorption. -/
theorem truncatedBarrierComparison_backward_supporting_increment_le
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {Mbar a t : ℝ} (ha : 0 < a) (hat : a < t) (htT : t ≤ DT.T)
    {f : ℝ → ℝ} (hf : Continuous f) {Cf K : ℝ} (hCf : 0 ≤ Cf)
    (hf_bound : ∀ y, |f y| ≤ Cf)
    (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2) :
    let W : ℝ → intervalDomainPoint → ℝ :=
      fun r X => squareHeatBarrier Mbar f r X.1
    let U := truncatedConjugatePicardLimit p u₀ DT.T
    let φ := comparisonPositivePartLift W U t
    comparisonPositivePartEnergy W U t - comparisonPositivePartEnergy W U a ≤
      2 * ((∫ x,
          (squareHeatBarrier Mbar f t x - squareHeatBarrier Mbar f a x) * φ x
          ∂intervalMeasure 1) +
        (∫ r in (0 : ℝ)..(t - a), ∫ x,
          deriv (fun z => intervalFullSemigroupOperator r
            (ShenWork.IntervalDomain.intervalDomainConstExtend (U a)) z) x *
              deriv φ x ∂intervalMeasure 1) -
        p.χ₀ * (∫ s in a..t, ∫ x,
          truncatedChemFluxLifted p (U s) x *
            deriv (fun z => intervalFullSemigroupOperator (t - s) φ z) x
          ∂intervalMeasure 1) -
        ∫ s in a..t, ∫ x,
          intervalFullSemigroupOperator (t - s)
            (truncatedLogisticLifted p (U s)) x * φ x
          ∂intervalMeasure 1) := by
  let W : ℝ → intervalDomainPoint → ℝ :=
    fun r X => squareHeatBarrier Mbar f r X.1
  let U := truncatedConjugatePicardLimit p u₀ DT.T
  let φ : ℝ → ℝ := comparisonPositivePartLift W U t
  let ua : ℝ → ℝ :=
    ShenWork.IntervalDomain.intervalDomainConstExtend (U a)
  let wt : ℝ → ℝ := fun x => squareHeatBarrier Mbar f t x
  let wa : ℝ → ℝ := fun x => squareHeatBarrier Mbar f a x
  let zt : ℝ → ℝ := fun x => wt x - intervalDomainLift (U t) x
  let za : ℝ → ℝ := fun x => wa x - intervalDomainLift (U a) x
  let BT : ℝ → ℝ := fun x => ∫ s in a..t,
    intervalConjugateKernelOperator (t - s)
      (truncatedChemFluxLifted p (U s)) x
  let LT : ℝ → ℝ := fun x => ∫ s in a..t,
    intervalFullSemigroupOperator (t - s)
      (truncatedLogisticLifted p (U s)) x
  let CP : ℝ → ℝ := fun s => ∫ x,
    truncatedChemFluxLifted p (U s) x *
      deriv (fun y => intervalFullSemigroupOperator (t - s) φ y) x
    ∂intervalMeasure 1
  let LP : ℝ → ℝ := fun s => ∫ x,
    intervalFullSemigroupOperator (t - s)
      (truncatedLogisticLifted p (U s)) x * φ x
    ∂intervalMeasure 1
  let R : ℝ → ℝ := fun x =>
    (wt x - wa x) - (intervalFullSemigroupOperator (t - a) ua x - ua x) +
      p.χ₀ * BT x - LT x
  have ht : 0 < t := ha.trans hat
  have haT : a ≤ DT.T := (le_of_lt hat).trans htT
  have hq : 0 < t - a := sub_pos.mpr hat
  have hUa_cont : Continuous (U a) := by
    simpa [U] using (truncatedConjugateMildSolutionData_of_data DT).hcont a ha haT
  have hUt_cont : Continuous (U t) := by
    simpa [U] using (truncatedConjugateMildSolutionData_of_data DT).hcont t ht htT
  have hUa_bound : ∀ X, |U a X| ≤ DT.M := by
    intro X
    simpa [U] using
      (truncatedConjugateMildSolutionData_of_data DT).hbound a ha haT X
  have hUt_bound : ∀ X, |U t X| ≤ DT.M := by
    intro X
    simpa [U] using
      (truncatedConjugateMildSolutionData_of_data DT).hbound t ht htT X
  have hua_cont : Continuous ua := by
    exact ShenWork.IntervalDomain.constExtend_continuous hUa_cont
  have hua_bound : ∀ x, |ua x| ≤ DT.M := constExtend_abs_le hUa_bound
  have hUa_lift_bound : ∀ x, |intervalDomainLift (U a) x| ≤ DT.M := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · simpa [intervalDomainLift, hx] using hUa_bound ⟨x, hx⟩
    · simp [intervalDomainLift, hx, DT.hM.le]
  have hUt_lift_bound : ∀ x, |intervalDomainLift (U t) x| ≤ DT.M := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · simpa [intervalDomainLift, hx] using hUt_bound ⟨x, hx⟩
    · simp [intervalDomainLift, hx, DT.hM.le]
  let Ca : ℝ := Real.exp (-Mbar * a) * Cf ^ 2
  let Ct : ℝ := Real.exp (-Mbar * t) * Cf ^ 2
  have hCa : 0 ≤ Ca := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hCt : 0 ≤ Ct := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hSa_bound : ∀ x, |intervalFullSemigroupOperator a f x| ≤ Cf :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      ha hCf hf_bound
  have hSt_bound : ∀ x, |intervalFullSemigroupOperator t f x| ≤ Cf :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      ht hCf hf_bound
  have hwa_bound : ∀ x, |wa x| ≤ Ca := by
    intro x
    dsimp [wa, Ca, squareHeatBarrier]
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (hSa_bound x) 2) (Real.exp_pos _).le
  have hwt_bound : ∀ x, |wt x| ≤ Ct := by
    intro x
    dsimp [wt, Ct, squareHeatBarrier]
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (hSt_bound x) 2) (Real.exp_pos _).le
  have hwa_cont :=
    (ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.squareHeatBarrierSliceRegularData_of_semigroup
      (M := Mbar) ha hf hCf hf_bound hK hl2).continuous
  have hwt_cont :=
    (ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.squareHeatBarrierSliceRegularData_of_semigroup
      (M := Mbar) ht hf hCf hf_bound hK hl2).continuous
  let Hφ : ComparisonTerminalTestData (W t) (U t) :=
    truncatedSquareHeatBarrier_terminalTestData DT ht htT hf hCf hf_bound hK hl2
  have hφmeas : AEStronglyMeasurable φ (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
      Hφ.continuousOn
  obtain ⟨hLint, _hLPint, hLpair⟩ :=
    truncatedLimit_logistic_tail_pairing DT ha hat htT hφmeas Hφ.C_nonneg Hφ.bound
  obtain ⟨hBint, _hCPint, hBpair⟩ :=
    truncatedLimit_chem_tail_pairing DT ha hat htT hφmeas Hφ.C_nonneg Hφ.bound
  change Integrable (fun x => LT x * φ x) (intervalMeasure 1) at hLint
  change Integrable (fun x => BT x * φ x) (intervalMeasure 1) at hBint
  obtain ⟨Gu, hGu, hUlip⟩ :=
    _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedPicardLimit_lipschitzOn_positive_time
      DT ha haT
  have hua_lip : LipschitzOnWith ⟨Gu, hGu⟩ ua (Set.Icc (0 : ℝ) 1) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    simpa [ua, Real.dist_eq,
      ShenWork.IntervalDomain.constExtend_eq_lift_on_Icc hx,
      ShenWork.IntervalDomain.constExtend_eq_lift_on_Icc hy] using
      hUlip x hx y hy
  have hua_ac : AbsolutelyContinuousOnInterval ua 0 1 := by
    have hu : Set.Icc (0 : ℝ) 1 = Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num)]
    rw [hu] at hua_lip
    exact hua_lip.absolutelyContinuousOnInterval
  have hua_deriv : ∀ᵐ x ∂volume, |deriv ua x| ≤ Gu :=
    constExtend_deriv_abs_le_ae_of_lipschitzOn hGu hua_lip
  have hheat := intervalFullSemigroup_pairing_increment_eq_neg_dirichletTail
    (f := ua) (φ := φ) (h := t - a) (Cf := DT.M) (Cφ := Hφ.C)
    (Gf := Gu) (Gφ := Hφ.G) hq hua_cont DT.hM.le hua_bound hua_ac
    hGu hua_deriv Hφ.continuousOn Hφ.C_nonneg Hφ.bound
    Hφ.absolutelyContinuous Hφ.G_nonneg Hφ.deriv_bound
  have hScont : Continuous
      (fun x => intervalFullSemigroupOperator (t - a) ua x) :=
    ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
      hq DT.hM.le hua_bound hua_cont.aestronglyMeasurable
  have hSbound : ∀ x, |intervalFullSemigroupOperator (t - a) ua x| ≤ DT.M :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      hq DT.hM.le hua_bound
  have hWdiff_int : Integrable (fun x => (wt x - wa x) * φ x)
      (intervalMeasure 1) := by
    haveI : IsFiniteMeasure (intervalMeasure 1) :=
      ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
    exact Integrable.of_bound
      ((hwt_cont.aestronglyMeasurable.sub hwa_cont.aestronglyMeasurable).mul hφmeas)
      ((Ct + Ca) * Hφ.C) (by
        filter_upwards [] with x
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul
          ((abs_sub _ _).trans (add_le_add (hwt_bound x) (hwa_bound x)))
          (Hφ.bound x) (abs_nonneg _) (add_nonneg hCt hCa))
  have hHeat_int : Integrable (fun x =>
      (intervalFullSemigroupOperator (t - a) ua x - ua x) * φ x)
      (intervalMeasure 1) := by
    haveI : IsFiniteMeasure (intervalMeasure 1) :=
      ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
    exact Integrable.of_bound
      ((hScont.aestronglyMeasurable.sub hua_cont.aestronglyMeasurable).mul hφmeas)
      ((DT.M + DT.M) * Hφ.C) (by
        filter_upwards [] with x
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul
          ((abs_sub _ _).trans (add_le_add (hSbound x) (hua_bound x)))
          (Hφ.bound x) (abs_nonneg _) (add_nonneg DT.hM.le DT.hM.le))
  have hRpair_int : Integrable (fun x => (2 * positivePart (zt x)) * R x)
      (intervalMeasure 1) := by
    have hbase := ((hWdiff_int.sub hHeat_int).add
      (hBint.const_mul p.χ₀)).sub hLint |>.const_mul 2
    apply hbase.congr
    filter_upwards [ae_mem_unitInterval] with x hx
    have hφx : φ x = positivePart (zt x) := by
      rcases hx with ⟨hx0, hx1⟩
      simp [φ, zt, wt, comparisonPositivePartLift, W, intervalDomainLift,
        hx0, hx1]
    change 2 * ((((wt x - wa x) * φ x) -
          ((intervalFullSemigroupOperator (t - a) ua x - ua x) * φ x)) +
        p.χ₀ * (BT x * φ x) - LT x * φ x) =
      (2 * positivePart (zt x)) * R x
    rw [hφx]
    dsimp only [R]
    ring
  have hrepr : ∀ᵐ x ∂intervalMeasure 1, zt x - za x = R x := by
    filter_upwards [ae_mem_unitInterval] with x hx
    let X : intervalDomainPoint := ⟨x, hx⟩
    have hr := truncatedLimit_backward_restart DT ha hat htT X
    have hsem : intervalFullSemigroupOperator (t - a) ua x =
        intervalFullSemigroupOperator (t - a) (intervalDomainLift (U a)) x := by
      simpa [ua] using
        (ShenWork.IntervalDomain.semigroupOperator_constExtend_eq_lift
          (f := U a) (t := t - a) (x := x))
    have hr' : intervalDomainLift (U t) x =
        intervalFullSemigroupOperator (t - a) ua x +
          (-p.χ₀) * BT x + LT x := by
      simpa [U, BT, LT, intervalDomainLift, hx, X, hsem] using hr
    simp only [zt, za, R, wt, wa]
    rw [hr']
    have hua_eq : ua x = intervalDomainLift (U a) x := by
      exact ShenWork.IntervalDomain.constExtend_eq_lift_on_Icc hx
    rw [hua_eq]
    ring
  have hzt_int : Integrable (fun x => positivePart (zt x) ^ 2)
      (intervalMeasure 1) := by
    apply ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      (M := (Ct + DT.M) ^ 2)
    · have hpcont : Continuous (fun r : ℝ => positivePart r) := by
        simpa [positivePart] using continuous_id.max continuous_const
      exact ((hpcont.comp_aestronglyMeasurable
        (hwt_cont.aestronglyMeasurable.sub
          (ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
            (intervalDomainLift_continuousOn_Icc hUt_cont)))).pow 2)
    · intro x
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _)
        ((abs_positivePart_le_abs (zt x)).trans
          ((abs_sub _ _).trans (add_le_add (hwt_bound x) (hUt_lift_bound x)))) 2
  have hza_int : Integrable (fun x => positivePart (za x) ^ 2)
      (intervalMeasure 1) := by
    apply ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      (M := (Ca + DT.M) ^ 2)
    · have hpcont : Continuous (fun r : ℝ => positivePart r) := by
        simpa [positivePart] using continuous_id.max continuous_const
      exact ((hpcont.comp_aestronglyMeasurable
        (hwa_cont.aestronglyMeasurable.sub
          (ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
            (intervalDomainLift_continuousOn_Icc hUa_cont)))).pow 2)
    · intro x
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _)
        ((abs_positivePart_le_abs (za x)).trans
          ((abs_sub _ _).trans (add_le_add (hwa_bound x) (hUa_lift_bound x)))) 2
  have hleft_int : Integrable (fun x =>
      positivePart (zt x) ^ 2 - positivePart (za x) ^ 2)
      (intervalMeasure 1) := hzt_int.sub hza_int
  have hright_int : Integrable (fun x =>
      (2 * positivePart (zt x)) * (zt x - za x)) (intervalMeasure 1) :=
    hRpair_int.congr (hrepr.mono fun x hx => by
      change 2 * positivePart (zt x) * R x =
        2 * positivePart (zt x) * (zt x - za x)
      rw [hx])
  have hmono := MeasureTheory.integral_mono hleft_int hright_int
    (fun x => positivePart_sq_sub_le_two_mul (zt x) (za x))
  have hsupport :
      (∫ x, positivePart (zt x) ^ 2 ∂intervalMeasure 1) -
          ∫ x, positivePart (za x) ^ 2 ∂intervalMeasure 1 ≤
        ∫ x, (2 * positivePart (zt x)) * R x ∂intervalMeasure 1 := by
    rw [← MeasureTheory.integral_sub hzt_int hza_int]
    exact hmono.trans_eq (integral_congr_ae
      (hrepr.mono fun x hx => by rw [hx])).symm
  have hpair_expand :
      (∫ x, (2 * positivePart (zt x)) * R x ∂intervalMeasure 1) =
        2 * ((∫ x, (wt x - wa x) * φ x ∂intervalMeasure 1) -
          (∫ x, (intervalFullSemigroupOperator (t - a) ua x - ua x) * φ x
            ∂intervalMeasure 1) +
          p.χ₀ * (∫ x, BT x * φ x ∂intervalMeasure 1) -
          ∫ x, LT x * φ x ∂intervalMeasure 1) := by
    calc
      (∫ x, (2 * positivePart (zt x)) * R x ∂intervalMeasure 1) =
          ∫ x, 2 * (((wt x - wa x) * φ x -
              (intervalFullSemigroupOperator (t - a) ua x - ua x) * φ x) +
            p.χ₀ * (BT x * φ x) - LT x * φ x) ∂intervalMeasure 1 := by
        apply integral_congr_ae
        filter_upwards [ae_mem_unitInterval] with x hx
        simp only [R, zt, wt, wa, BT, LT, φ, comparisonPositivePartLift,
          W, intervalDomainLift, dif_pos hx]
        ring
      _ = 2 * (∫ x, (((wt x - wa x) * φ x -
              (intervalFullSemigroupOperator (t - a) ua x - ua x) * φ x) +
            p.χ₀ * (BT x * φ x) - LT x * φ x) ∂intervalMeasure 1) := by
        exact MeasureTheory.integral_const_mul 2 _
      _ = 2 * ((∫ x, (wt x - wa x) * φ x ∂intervalMeasure 1) -
          (∫ x, (intervalFullSemigroupOperator (t - a) ua x - ua x) * φ x
            ∂intervalMeasure 1) +
          p.χ₀ * (∫ x, BT x * φ x ∂intervalMeasure 1) -
          ∫ x, LT x * φ x ∂intervalMeasure 1) := by
        congr 1
        calc
          (∫ x, (((wt x - wa x) * φ x -
                (intervalFullSemigroupOperator (t - a) ua x - ua x) * φ x) +
              p.χ₀ * (BT x * φ x) - LT x * φ x) ∂intervalMeasure 1) =
              (∫ x, ((wt x - wa x) * φ x -
                (intervalFullSemigroupOperator (t - a) ua x - ua x) * φ x) +
                p.χ₀ * (BT x * φ x) ∂intervalMeasure 1) -
                ∫ x, LT x * φ x ∂intervalMeasure 1 := by
            simpa only [Pi.add_apply, Pi.sub_apply] using
              (MeasureTheory.integral_sub
                ((hWdiff_int.sub hHeat_int).add (hBint.const_mul p.χ₀)) hLint)
          _ = ((∫ x, (wt x - wa x) * φ x -
                (intervalFullSemigroupOperator (t - a) ua x - ua x) * φ x
                ∂intervalMeasure 1) +
              ∫ x, p.χ₀ * (BT x * φ x) ∂intervalMeasure 1) -
                ∫ x, LT x * φ x ∂intervalMeasure 1 := by
            apply congrArg (fun r : ℝ => r - ∫ x, LT x * φ x ∂intervalMeasure 1)
            simpa only [Pi.add_apply, Pi.sub_apply] using
              (MeasureTheory.integral_add (hWdiff_int.sub hHeat_int)
                (hBint.const_mul p.χ₀))
          _ = ((∫ x, (wt x - wa x) * φ x ∂intervalMeasure 1) -
                (∫ x, (intervalFullSemigroupOperator (t - a) ua x - ua x) * φ x
                  ∂intervalMeasure 1) +
              p.χ₀ * (∫ x, BT x * φ x ∂intervalMeasure 1)) -
                ∫ x, LT x * φ x ∂intervalMeasure 1 := by
            rw [MeasureTheory.integral_sub hWdiff_int hHeat_int]
            rw [MeasureTheory.integral_const_mul]
  rw [hpair_expand, hheat] at hsupport
  have hb : (∫ x, BT x * φ x ∂intervalMeasure 1) =
      -(∫ s in a..t, CP s) := by
    simpa [BT, CP, U, φ] using hBpair
  have hl : (∫ x, LT x * φ x ∂intervalMeasure 1) =
      ∫ s in a..t, LP s := by
    simpa [LT, LP, U, φ] using hLpair
  rw [hb, hl] at hsupport
  have hEt : (∫ x, positivePart (zt x) ^ 2 ∂intervalMeasure 1) =
      comparisonPositivePartEnergy W U t := by
    unfold comparisonPositivePartEnergy
    apply integral_congr_ae
    filter_upwards [ae_mem_unitInterval] with x hx
    rcases hx with ⟨hx0, hx1⟩
    simp [zt, wt, comparisonPositivePartLift, W, intervalDomainLift, hx0, hx1]
  have hEa : (∫ x, positivePart (za x) ^ 2 ∂intervalMeasure 1) =
      comparisonPositivePartEnergy W U a := by
    unfold comparisonPositivePartEnergy
    apply integral_congr_ae
    filter_upwards [ae_mem_unitInterval] with x hx
    rcases hx with ⟨hx0, hx1⟩
    simp [za, wa, comparisonPositivePartLift, W, intervalDomainLift, hx0, hx1]
  rw [hEt, hEa] at hsupport
  simpa [wt, wa, ua, CP, LP, W, U, φ] using hsupport

/-- The refined increment has a convergent backward-quotient majorant.  Its
limit is exactly the terminal matched-divergence weak pairing. -/
theorem truncatedBarrierComparison_backward_quotient_upper_tendsto
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {Mbar t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T)
    {f : ℝ → ℝ} (hf : Continuous f) {Cf K : ℝ} (hCf : 0 ≤ Cf)
    (hf_bound : ∀ y, |f y| ≤ Cf)
    (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2) :
    let W : ℝ → intervalDomainPoint → ℝ :=
      fun r X => squareHeatBarrier Mbar f r X.1
    let U := truncatedConjugatePicardLimit p u₀ DT.T
    let E := comparisonPositivePartEnergy W U
    let φ := comparisonPositivePartLift W U t
    let et := ShenWork.IntervalDomain.intervalDomainConstExtend (U t)
    let d := 2 *
      ((∫ x,
          ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.barrierTimeDerivRep
            Mbar f t x * φ x ∂intervalMeasure 1) +
        (∫ x, deriv et x * deriv φ x ∂intervalMeasure 1) -
        p.χ₀ * (∫ x,
          truncatedChemFluxLifted p (U t) x * deriv φ x
          ∂intervalMeasure 1) -
        ∫ x, truncatedLogisticLifted p (U t) x * φ x
          ∂intervalMeasure 1)
    ∃ R : ℝ → ℝ,
      Tendsto R (nhdsWithin 0 (Set.Ioi 0)) (nhds d) ∧
      ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0),
        q⁻¹ * (E t - E (t - q)) ≤ R q := by
  let W : ℝ → intervalDomainPoint → ℝ :=
    fun r X => squareHeatBarrier Mbar f r X.1
  let U := truncatedConjugatePicardLimit p u₀ DT.T
  let E := comparisonPositivePartEnergy W U
  let φ : ℝ → ℝ := comparisonPositivePartLift W U t
  let et : ℝ → ℝ :=
    ShenWork.IntervalDomain.intervalDomainConstExtend (U t)
  let CP : ℝ → ℝ := fun s => ∫ x,
    truncatedChemFluxLifted p (U s) x *
      deriv (fun y : ℝ => intervalFullSemigroupOperator (t - s) φ y) x
    ∂intervalMeasure 1
  let LP : ℝ → ℝ := fun s => ∫ x,
    intervalFullSemigroupOperator (t - s)
      (truncatedLogisticLifted p (U s)) x * φ x
    ∂intervalMeasure 1
  let W0 : ℝ := ∫ x,
    ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.barrierTimeDerivRep
      Mbar f t x * φ x ∂intervalMeasure 1
  let U0 : ℝ := ∫ x, deriv et x * deriv φ x ∂intervalMeasure 1
  let Q0 : ℝ := ∫ x,
    truncatedChemFluxLifted p (U t) x * deriv φ x ∂intervalMeasure 1
  let L0 : ℝ := ∫ x,
    truncatedLogisticLifted p (U t) x * φ x ∂intervalMeasure 1
  let d : ℝ := 2 * (W0 + U0 - p.χ₀ * Q0 - L0)
  let c : ℝ := t / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hct : c < t := by dsimp [c]; linarith
  let Hφ : ComparisonTerminalTestData (W t) (U t) :=
    truncatedSquareHeatBarrier_terminalTestData DT ht htT hf hCf hf_bound hK hl2
  have hφmeas : AEStronglyMeasurable φ (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
      Hφ.continuousOn
  obtain ⟨_hLspatial, hLPint, _hLswap⟩ :=
    truncatedLimit_logistic_tail_pairing DT hc hct htT
      hφmeas Hφ.C_nonneg Hφ.bound
  obtain ⟨_hQspatial, hCPint, _hQswap⟩ :=
    truncatedLimit_chem_tail_pairing DT hc hct htT
      hφmeas Hφ.C_nonneg Hφ.bound
  have hLPint' : IntervalIntegrable LP volume c t := by
    simpa [LP, U, φ] using hLPint
  have hCPint' : IntervalIntegrable CP volume c t := by
    simpa [CP, U, φ] using hCPint
  have hLPmeas : AEStronglyMeasurable LP
      (volume.restrict (Set.uIoc c t)) := by
    rw [intervalIntegrable_iff] at hLPint'
    exact hLPint'.aestronglyMeasurable
  have hCPmeas : AEStronglyMeasurable CP
      (volume.restrict (Set.uIoc c t)) := by
    rw [intervalIntegrable_iff] at hCPint'
    exact hCPint'.aestronglyMeasurable
  have hLPlim : Tendsto LP (nhdsWithin t (Set.Iio t)) (nhds L0) := by
    simpa [LP, L0, U, φ] using
      (truncatedLimit_logistic_pairing_tendsto DT ht htT
        Hφ.continuousOn Hφ.zero_outside Hφ.C_nonneg Hφ.bound)
  have hCPlim : Tendsto CP (nhdsWithin t (Set.Iio t)) (nhds Q0) := by
    simpa [CP, Q0, U, φ] using
      (truncatedLimit_chem_pairing_tendsto DT ht htT
        Hφ.continuousOn Hφ.C_nonneg Hφ.bound Hφ.absolutelyContinuous
        Hφ.G_nonneg Hφ.deriv_bound)
  have hLPavg :=
    ShenWork.Paper2.IntervalNegativePartWeakEnergy.left_intervalAverage_tendsto
      hct hLPint' hLPmeas hLPlim
  have hCPavg :=
    ShenWork.Paper2.IntervalNegativePartWeakEnergy.left_intervalAverage_tendsto
      hct hCPint' hCPmeas hCPlim
  have hWavg : Tendsto
      (fun q : ℝ => q⁻¹ * ∫ x,
        (squareHeatBarrier Mbar f t x - squareHeatBarrier Mbar f (t - q) x) *
          φ x ∂intervalMeasure 1)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds W0) := by
    simpa [W0] using
      (ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.squareHeatBarrier_timeIncrement_pairing_tendsto
        (M := Mbar) ht hf hCf hf_bound hK hφmeas Hφ.C_nonneg Hφ.bound)
  have hUavg : Tendsto
      (fun q : ℝ => q⁻¹ * ∫ r in (0 : ℝ)..q, ∫ x,
        deriv (fun z => intervalFullSemigroupOperator r
          (ShenWork.IntervalDomain.intervalDomainConstExtend (U (t - q))) z) x *
            deriv φ x ∂intervalMeasure 1)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds U0) := by
    simpa [U0, U, et, φ] using
      (truncatedLimit_moving_dirichletAverage_tendsto DT ht htT
        Hφ.continuousOn Hφ.C_nonneg Hφ.bound Hφ.absolutelyContinuous
        Hφ.G_nonneg Hφ.deriv_bound)
  let R : ℝ → ℝ := fun q => 2 *
    ((q⁻¹ * ∫ x,
        (squareHeatBarrier Mbar f t x - squareHeatBarrier Mbar f (t - q) x) *
          φ x ∂intervalMeasure 1) +
      (q⁻¹ * ∫ r in (0 : ℝ)..q, ∫ x,
        deriv (fun z => intervalFullSemigroupOperator r
          (ShenWork.IntervalDomain.intervalDomainConstExtend (U (t - q))) z) x *
            deriv φ x ∂intervalMeasure 1) -
      p.χ₀ * (q⁻¹ * ∫ s in (t - q)..t, CP s) -
      q⁻¹ * ∫ s in (t - q)..t, LP s)
  refine ⟨R, ?_, ?_⟩
  · have hinner := hWavg.add hUavg |>.sub
      ((tendsto_const_nhds (x := p.χ₀)).mul hCPavg) |>.sub hLPavg
    have hmul := (tendsto_const_nhds (x := (2 : ℝ))).mul hinner
    simpa [R, d, W0, U0, Q0, L0] using hmul
  · have hqt : ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0), q < t :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds ht)
    filter_upwards [self_mem_nhdsWithin, hqt] with q hq hqt
    have hq0 : 0 < q := hq
    have ha : 0 < t - q := sub_pos.mpr hqt
    have hat : t - q < t := sub_lt_self t hq0
    have hinc := truncatedBarrierComparison_backward_supporting_increment_le
      (Mbar := Mbar) (a := t - q) (t := t)
      DT ha hat htT hf hCf hf_bound hK hl2
    have hinc' : E t - E (t - q) ≤ 2 *
        ((∫ x,
            (squareHeatBarrier Mbar f t x - squareHeatBarrier Mbar f (t - q) x) *
              φ x ∂intervalMeasure 1) +
          (∫ r in (0 : ℝ)..q, ∫ x,
            deriv (fun z => intervalFullSemigroupOperator r
              (ShenWork.IntervalDomain.intervalDomainConstExtend (U (t - q))) z) x *
                deriv φ x ∂intervalMeasure 1) -
          p.χ₀ * (∫ s in (t - q)..t, CP s) -
          ∫ s in (t - q)..t, LP s) := by
      simpa [E, W, U, φ, CP, LP, sub_sub_cancel] using hinc
    have hm := mul_le_mul_of_nonneg_left hinc' (inv_nonneg.mpr hq0.le)
    calc
      q⁻¹ * (E t - E (t - q)) ≤ q⁻¹ * (2 *
          ((∫ x,
              (squareHeatBarrier Mbar f t x - squareHeatBarrier Mbar f (t - q) x) *
                φ x ∂intervalMeasure 1) +
            (∫ r in (0 : ℝ)..q, ∫ x,
              deriv (fun z => intervalFullSemigroupOperator r
                (ShenWork.IntervalDomain.intervalDomainConstExtend (U (t - q))) z) x *
                  deriv φ x ∂intervalMeasure 1) -
            p.χ₀ * (∫ s in (t - q)..t, CP s) -
            ∫ s in (t - q)..t, LP s)) := hm
      _ = R q := by dsimp [R]; ring

set_option maxHeartbeats 0

/-- Matched-divergence terminal estimate.  The derivative of the drift was
used upstream only to certify the smooth barrier residual.  In the comparison
itself the drift enters solely through its `L∞` bound. -/
theorem truncatedBarrierComparison_terminal_pairing_le
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T)
    (hU_nonneg : ∀ X : intervalDomainPoint,
      0 ≤ truncatedConjugatePicardLimit p u₀ DT.T t X)
    {f : ℝ → ℝ} (hf : Continuous f) {Cf K : ℝ} (hCf : 0 ≤ Cf)
    (hf_bound : ∀ y, |f y| ≤ Cf)
    (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2) :
    let Mbar := truncatedBarrierDiscount p DT.M
    let G₀ := truncatedDriftFactorC0 p DT.M
    let ell := p.a + (|p.χ₀| * G₀) ^ 2 / 2
    let W : ℝ → intervalDomainPoint → ℝ :=
      fun r X => squareHeatBarrier Mbar f r X.1
    let U := truncatedConjugatePicardLimit p u₀ DT.T
    let φ := comparisonPositivePartLift W U t
    let et := ShenWork.IntervalDomain.intervalDomainConstExtend (U t)
    2 *
      ((∫ x,
          ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.barrierTimeDerivRep
            Mbar f t x * φ x ∂intervalMeasure 1) +
        (∫ x, deriv et x * deriv φ x ∂intervalMeasure 1) -
        p.χ₀ * (∫ x,
          truncatedChemFluxLifted p (U t) x * deriv φ x
          ∂intervalMeasure 1) -
        ∫ x, truncatedLogisticLifted p (U t) x * φ x
          ∂intervalMeasure 1) ≤
      (2 * ell) * comparisonPositivePartEnergy W U t := by
  let Mbar := truncatedBarrierDiscount p DT.M
  let G₀ := truncatedDriftFactorC0 p DT.M
  let ell := p.a + (|p.χ₀| * G₀) ^ 2 / 2
  let W : ℝ → intervalDomainPoint → ℝ :=
    fun r X => squareHeatBarrier Mbar f r X.1
  let U := truncatedConjugatePicardLimit p u₀ DT.T
  let φ : ℝ → ℝ := comparisonPositivePartLift W U t
  let et : ℝ → ℝ :=
    ShenWork.IntervalDomain.intervalDomainConstExtend (U t)
  let wt : ℝ → ℝ := fun x => squareHeatBarrier Mbar f t x
  let Wt : ℝ → ℝ :=
    ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.barrierTimeDerivRep
      Mbar f t
  let g : ℝ → ℝ := truncatedDriftFactor p (U t)
  let c : ℝ → ℝ := truncatedReactionCoefficient p (U t)
  let Q : ℝ → ℝ := truncatedChemFluxLifted p (U t)
  let L : ℝ → ℝ := truncatedLogisticLifted p (U t)
  let Rest : ℝ → ℝ := fun x =>
    Wt x * φ x + deriv et x * deriv φ x -
      p.χ₀ * (Q x * deriv φ x) - L x * φ x
  let Barrier : ℝ → ℝ := fun x =>
    Wt x * φ x + deriv wt x * deriv φ x -
      p.χ₀ * (g x * wt x * deriv φ x) - c x * wt x * φ x
  let Good : ℝ → ℝ := fun x =>
    -(deriv φ x) ^ 2 + p.χ₀ * g x * φ x * deriv φ x +
      c x * φ x ^ 2
  let Hφ : ComparisonTerminalTestData (W t) (U t) :=
    truncatedSquareHeatBarrier_terminalTestData DT ht htT hf hCf hf_bound hK hl2
  have hUcont : Continuous (U t) := by
    simpa [U] using
      (truncatedConjugateMildSolutionData_of_data DT).hcont t ht htT
  have hUbound : ∀ X, |U t X| ≤ DT.M := by
    intro X
    simpa [U] using
      (truncatedConjugateMildSolutionData_of_data DT).hbound t ht htT X
  have hetcont : Continuous et :=
    ShenWork.IntervalDomain.constExtend_continuous hUcont
  have hetbound : ∀ x, |et x| ≤ DT.M := constExtend_abs_le hUbound
  obtain ⟨Gu, hGu, hUlip⟩ :=
    _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedPicardLimit_lipschitzOn_positive_time
      DT ht htT
  have hetlip : LipschitzOnWith ⟨Gu, hGu⟩ et (Set.Icc (0 : ℝ) 1) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    simpa [et, U, Real.dist_eq,
      ShenWork.IntervalDomain.constExtend_eq_lift_on_Icc hx,
      ShenWork.IntervalDomain.constExtend_eq_lift_on_Icc hy] using
      hUlip x hx y hy
  have hetderiv_vol : ∀ᵐ x ∂volume, |deriv et x| ≤ Gu :=
    constExtend_deriv_abs_le_ae_of_lipschitzOn hGu hetlip
  have hφderiv : ∀ᵐ x ∂intervalMeasure 1, |deriv φ x| ≤ Hφ.G := by
    dsimp [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
    exact Hφ.deriv_bound.filter_mono ae_restrict_le
  have hetderiv : ∀ᵐ x ∂intervalMeasure 1, |deriv et x| ≤ Gu := by
    dsimp [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
    exact hetderiv_vol.filter_mono ae_restrict_le
  have hφmeas : AEStronglyMeasurable φ (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
      Hφ.continuousOn
  have hwtreg :=
    ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.squareHeatBarrierSliceRegularData_of_semigroup
      (M := Mbar) ht hf hCf hf_bound hK hl2
  obtain ⟨Gw, hGw, hGwbound⟩ := hwtreg.deriv_bounded
  have hwtderiv : ∀ᵐ x ∂intervalMeasure 1, |deriv wt x| ≤ Gw := by
    filter_upwards [ae_mem_unitInterval] with x hx
    rw [(hwtreg.hasDerivAt x hx).deriv]
    exact hGwbound x hx
  have hStbound : ∀ x, |intervalFullSemigroupOperator t f x| ≤ Cf :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      ht hCf hf_bound
  let Cw : ℝ := Real.exp (-Mbar * t) * Cf ^ 2
  have hCw : 0 ≤ Cw := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hwtbound : ∀ x, |wt x| ≤ Cw := by
    intro x
    dsimp [wt, Cw, squareHeatBarrier]
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (hStbound x) 2) (Real.exp_pos _).le
  obtain ⟨hgcont, _hgac, _hg0, _hg1, hgbound, _hgderiv⟩ :=
    truncatedDriftFactor_regular p hUcont DT.hM.le hUbound
  have hG₀ : 0 ≤ G₀ := by
    dsimp [G₀, truncatedDriftFactorC0]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg DT.hM.le _)))
  have hgmeas : AEStronglyMeasurable g (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
      (by simpa [g] using hgcont)
  have hgbound' : ∀ᵐ x ∂intervalMeasure 1, |g x| ≤ G₀ := by
    filter_upwards [ae_mem_unitInterval] with x hx
    simpa [g, G₀] using hgbound x hx
  have hliftcont : ContinuousOn (intervalDomainLift (U t))
      (Set.Icc (0 : ℝ) 1) := intervalDomainLift_continuousOn_Icc hUcont
  have hppcont : ContinuousOn
      (fun x => positivePart (intervalDomainLift (U t) x))
      (Set.Icc (0 : ℝ) 1) := by
    simpa [positivePart] using
      continuous_max.comp_continuousOn (hliftcont.prodMk continuousOn_const)
  have hccont : ContinuousOn c (Set.Icc (0 : ℝ) 1) := by
    have hp := hppcont.rpow_const (fun _ _ => Or.inr p.hα.le)
    simpa [c, truncatedReactionCoefficient] using
      continuousOn_const.sub (continuousOn_const.mul hp)
  have hcmeas : AEStronglyMeasurable c (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
      hccont
  let Cc : ℝ := p.a + p.b * DT.M ^ p.α
  have hCc : 0 ≤ Cc := add_nonneg p.ha
    (mul_nonneg p.hb (Real.rpow_nonneg DT.hM.le _))
  have hcbounds : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |c x| ≤ Cc ∧ c x ≤ p.a := by
    intro x hx
    let X : intervalDomainPoint := ⟨x, hx⟩
    have hUx : |intervalDomainLift (U t) x| ≤ DT.M := by
      simpa [intervalDomainLift, hx, X] using hUbound X
    have hpple : positivePart (intervalDomainLift (U t) x) ≤ DT.M := by
      have habs := (abs_positivePart_le_abs
        (intervalDomainLift (U t) x)).trans hUx
      simpa [abs_of_nonneg (positivePart_nonneg _)] using habs
    have hpowle : positivePart (intervalDomainLift (U t) x) ^ p.α ≤
        DT.M ^ p.α :=
      Real.rpow_le_rpow (positivePart_nonneg _) hpple p.hα.le
    have hterm : |p.b * positivePart (intervalDomainLift (U t) x) ^ p.α| ≤
        p.b * DT.M ^ p.α := by
      rw [abs_of_nonneg (mul_nonneg p.hb
        (Real.rpow_nonneg (positivePart_nonneg _) _))]
      exact mul_le_mul_of_nonneg_left hpowle p.hb
    constructor
    · dsimp [c, Cc, truncatedReactionCoefficient]
      calc
        |p.a - p.b * positivePart (intervalDomainLift (U t) x) ^ p.α| ≤
            |p.a| + |p.b * positivePart (intervalDomainLift (U t) x) ^ p.α| :=
          abs_sub _ _
        _ ≤ p.a + p.b * DT.M ^ p.α := by
          exact add_le_add (by rw [abs_of_nonneg p.ha]) hterm
    · dsimp [c, truncatedReactionCoefficient]
      exact sub_le_self _ (mul_nonneg p.hb
        (Real.rpow_nonneg (positivePart_nonneg _) _))
  have hcbound : ∀ᵐ x ∂intervalMeasure 1, |c x| ≤ Cc := by
    filter_upwards [ae_mem_unitInterval] with x hx
    exact (hcbounds x hx).1
  have hcle : ∀ᵐ x ∂intervalMeasure 1, c x ≤ p.a := by
    filter_upwards [ae_mem_unitInterval] with x hx
    exact (hcbounds x hx).2
  have hWtcont : ContinuousOn Wt (Set.Icc (0 : ℝ) 1) := by
    have hjoint :=
      ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.barrierTimeDerivRep_continuousOn_Ioi
        (M := Mbar) hK
    have hcomp : Continuous (fun x : ℝ => ((t, x) : ℝ × ℝ)) := by fun_prop
    exact hjoint.comp hcomp.continuousOn
      (fun x hx => ⟨ht, Set.mem_univ x⟩)
  obtain ⟨Cwt₀, hCwt₀⟩ := isCompact_Icc.bddAbove_image hWtcont.abs
  let Cwt : ℝ := max Cwt₀ 0
  have hCwt : 0 ≤ Cwt := le_max_right _ _
  have hWtbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |Wt x| ≤ Cwt := by
    intro x hx
    exact (hCwt₀ (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)
  have hWtmeas : AEStronglyMeasurable Wt (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
      hWtcont
  have hφd_meas : AEStronglyMeasurable (deriv φ) (intervalMeasure 1) :=
    (measurable_deriv φ).aestronglyMeasurable
  have hetd_meas : AEStronglyMeasurable (deriv et) (intervalMeasure 1) :=
    (measurable_deriv et).aestronglyMeasurable
  have hwtd_meas : AEStronglyMeasurable (deriv wt) (intervalMeasure 1) :=
    (measurable_deriv wt).aestronglyMeasurable
  haveI : IsFiniteMeasure (intervalMeasure 1) :=
    ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
  have hWtφ : Integrable (fun x => Wt x * φ x) (intervalMeasure 1) :=
    Integrable.of_bound (hWtmeas.mul hφmeas) (Cwt * Hφ.C) (by
      filter_upwards [ae_mem_unitInterval] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hWtbound x hx) (Hφ.bound x) (abs_nonneg _) hCwt)
  have hwtDφ : Integrable (fun x => deriv wt x * deriv φ x)
      (intervalMeasure 1) :=
    Integrable.of_bound (hwtd_meas.mul hφd_meas) (Gw * Hφ.G) (by
      filter_upwards [hwtderiv, hφderiv] with x hxw hxφ
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul hxw hxφ (abs_nonneg _) hGw)
  have hetDφ : Integrable (fun x => deriv et x * deriv φ x)
      (intervalMeasure 1) :=
    Integrable.of_bound (hetd_meas.mul hφd_meas) (Gu * Hφ.G) (by
      filter_upwards [hetderiv, hφderiv] with x hxe hxφ
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul hxe hxφ (abs_nonneg _) hGu)
  have hgwtDφ : Integrable (fun x => g x * wt x * deriv φ x)
      (intervalMeasure 1) :=
    Integrable.of_bound ((hgmeas.mul hwtreg.continuous.aestronglyMeasurable).mul
      hφd_meas) (G₀ * Cw * Hφ.G) (by
      filter_upwards [hgbound', hφderiv] with x hxg hxφ
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul
        (mul_le_mul hxg (hwtbound x) (abs_nonneg _) hG₀) hxφ
        (abs_nonneg _) (mul_nonneg hG₀ hCw))
  have hcwtφ : Integrable (fun x => c x * wt x * φ x)
      (intervalMeasure 1) :=
    Integrable.of_bound ((hcmeas.mul hwtreg.continuous.aestronglyMeasurable).mul
      hφmeas) (Cc * Cw * Hφ.C) (by
      filter_upwards [hcbound] with x hxc
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul
        (mul_le_mul hxc (hwtbound x) (abs_nonneg _) hCc) (Hφ.bound x)
        (abs_nonneg _) (mul_nonneg hCc hCw))
  have hgdφφ : Integrable (fun x => g x * φ x * deriv φ x)
      (intervalMeasure 1) :=
    Integrable.of_bound ((hgmeas.mul hφmeas).mul hφd_meas)
      (G₀ * Hφ.C * Hφ.G) (by
        filter_upwards [hgbound', hφderiv] with x hxg hxφ
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        exact mul_le_mul
          (mul_le_mul hxg (Hφ.bound x) (abs_nonneg _) hG₀) hxφ
          (abs_nonneg _) (mul_nonneg hG₀ Hφ.C_nonneg))
  have hcdφφ : Integrable (fun x => c x * φ x ^ 2)
      (intervalMeasure 1) :=
    Integrable.of_bound (hcmeas.mul (hφmeas.pow 2)) (Cc * Hφ.C ^ 2) (by
      filter_upwards [hcbound] with x hxc
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul hxc
        (pow_le_pow_left₀ (abs_nonneg _) (Hφ.bound x) 2)
        (by positivity) hCc)
  have hDφsq : Integrable (fun x => deriv φ x ^ 2)
      (intervalMeasure 1) :=
    Integrable.of_bound (hφd_meas.pow 2) (Hφ.G ^ 2) (by
      filter_upwards [hφderiv] with x hx
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hx 2)
  have hφsq : Integrable (fun x => φ x ^ 2) (intervalMeasure 1) :=
    Integrable.of_bound (hφmeas.pow 2) (Hφ.C ^ 2) (by
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (Hφ.bound x) 2)
  have hQeq : ∀ᵐ x ∂intervalMeasure 1, Q x = et x * g x := by
    filter_upwards [ae_mem_unitInterval] with x hx
    have hlift_nonneg : 0 ≤ intervalDomainLift (U t) x := by
      simpa [intervalDomainLift, hx] using hU_nonneg ⟨x, hx⟩
    rw [show Q x = truncatedChemFluxLifted p (U t) x by rfl,
      truncatedChemFluxLifted_eq_positivePart_mul_driftFactor p hUcont]
    rw [show positivePart (intervalDomainLift (U t) x) =
      intervalDomainLift (U t) x by
        simp [positivePart, max_eq_left hlift_nonneg]]
    have heteq : et x = intervalDomainLift (U t) x :=
      ShenWork.IntervalDomain.constExtend_eq_lift_on_Icc hx
    rw [heteq]
  have hLeq : ∀ᵐ x ∂intervalMeasure 1, L x = et x * c x := by
    filter_upwards [ae_mem_unitInterval] with x hx
    rw [show L x = truncatedLogisticLifted p (U t) x by rfl,
      truncatedLogisticLifted_eq_mul_reactionCoefficient]
    have heteq : et x = intervalDomainLift (U t) x :=
      ShenWork.IntervalDomain.constExtend_eq_lift_on_Icc hx
    rw [heteq]
  have hQdφ : Integrable (fun x => Q x * deriv φ x)
      (intervalMeasure 1) := by
    have hbase : Integrable (fun x => (et x * g x) * deriv φ x)
        (intervalMeasure 1) :=
      Integrable.of_bound ((hetcont.aestronglyMeasurable.mul hgmeas).mul hφd_meas)
        (DT.M * G₀ * Hφ.G) (by
          filter_upwards [hgbound', hφderiv] with x hxg hxφ
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
          exact mul_le_mul
            (mul_le_mul (hetbound x) hxg (abs_nonneg _) DT.hM.le) hxφ
            (abs_nonneg _) (mul_nonneg DT.hM.le hG₀))
    exact hbase.congr (hQeq.mono fun x hx => by
      change (et x * g x) * deriv φ x = Q x * deriv φ x
      rw [hx])
  have hLφ : Integrable (fun x => L x * φ x) (intervalMeasure 1) := by
    have hbase : Integrable (fun x => (et x * c x) * φ x)
        (intervalMeasure 1) :=
      Integrable.of_bound ((hetcont.aestronglyMeasurable.mul hcmeas).mul hφmeas)
        (DT.M * Cc * Hφ.C) (by
          filter_upwards [hcbound] with x hxc
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
          exact mul_le_mul
            (mul_le_mul (hetbound x) hxc (abs_nonneg _) DT.hM.le)
            (Hφ.bound x) (abs_nonneg _) (mul_nonneg DT.hM.le hCc))
    exact hbase.congr (hLeq.mono fun x hx => by
      change (et x * c x) * φ x = L x * φ x
      rw [hx])
  have hBarrierInt : Integrable Barrier (intervalMeasure 1) := by
    exact (((hWtφ.add hwtDφ).sub (hgwtDφ.const_mul p.χ₀)).sub hcwtφ)
  have hGoodInt : Integrable Good (intervalMeasure 1) := by
    apply ((hDφsq.neg.add (hgdφφ.const_mul p.χ₀)).add hcdφφ).congr
    filter_upwards [] with x
    dsimp [Good]
    ring
  have hRestInt : Integrable Rest (intervalMeasure 1) := by
    exact (((hWtφ.add hetDφ).sub (hQdφ.const_mul p.χ₀)).sub hLφ)
  have hchain := truncatedSquareHeatBarrier_terminal_diffusion_chain_ae
    DT (Mbar := Mbar) ht htT hf hCf hf_bound hK hl2
  have hdrift := comparison_defect_mul_positivePart_deriv_ae
    (w := W t) (u := U t)
    (hwtreg.continuous.comp continuous_subtype_val) hUcont
  have hdecomp_point : ∀ᵐ x ∂intervalMeasure 1,
      Rest x = Barrier x + Good x := by
    filter_upwards [ae_mem_unitInterval, hchain, hdrift, hQeq, hLeq]
      with x hx hxchain hxdrift hxQ hxL
    have hwtlift : intervalDomainLift (W t) x = wt x := by
      simp [W, wt, intervalDomainLift, hx]
    have hUte : intervalDomainLift (U t) x = et x := by
      exact (ShenWork.IntervalDomain.constExtend_eq_lift_on_Icc hx).symm
    have hφx : φ x = positivePart (wt x - et x) := by
      simp [φ, comparisonPositivePartLift, hwtlift, hUte]
    have hdrift' : (wt x - et x) * deriv φ x =
        φ x * deriv φ x := by
      change (intervalDomainLift (W t) x - intervalDomainLift (U t) x) *
          deriv φ x =
        positivePart (intervalDomainLift (W t) x - intervalDomainLift (U t) x) *
          deriv φ x at hxdrift
      rw [hwtlift, hUte] at hxdrift
      rw [hφx]
      exact hxdrift
    have hreact := comparison_defect_mul_positivePart (W t) (U t) x
    have hreact' : (wt x - et x) * φ x = φ x ^ 2 := by
      rw [hφx]
      simpa [hwtlift, hUte] using hreact
    have hxchain' : (deriv wt x - deriv et x) * deriv φ x =
        deriv φ x ^ 2 := by
      simpa [wt, et, φ, W, U] using hxchain
    have hdiff : deriv et x * deriv φ x =
        deriv wt x * deriv φ x - deriv φ x ^ 2 := by
      linarith [hxchain']
    have hdrift_base : et x * deriv φ x =
        wt x * deriv φ x - φ x * deriv φ x := by
      linarith [hdrift']
    have hdrift2 : et x * g x * deriv φ x =
        g x * wt x * deriv φ x - g x * φ x * deriv φ x := by
      calc
        et x * g x * deriv φ x = g x * (et x * deriv φ x) := by ring
        _ = g x * (wt x * deriv φ x - φ x * deriv φ x) := by
          rw [hdrift_base]
        _ = _ := by ring
    have hreact_base : et x * φ x = wt x * φ x - φ x ^ 2 := by
      linarith [hreact']
    have hreact2 : et x * c x * φ x =
        c x * wt x * φ x - c x * φ x ^ 2 := by
      calc
        et x * c x * φ x = c x * (et x * φ x) := by ring
        _ = c x * (wt x * φ x - φ x ^ 2) := by rw [hreact_base]
        _ = _ := by ring
    dsimp [Rest, Barrier, Good]
    rw [hxQ, hxL]
    rw [hdiff, hdrift2, hreact2]
    ring
  have hdecomp_integral :
      (∫ x, Rest x ∂intervalMeasure 1) =
        (∫ x, Barrier x ∂intervalMeasure 1) +
          ∫ x, Good x ∂intervalMeasure 1 := by
    calc
      (∫ x, Rest x ∂intervalMeasure 1) =
          ∫ x, Barrier x + Good x ∂intervalMeasure 1 :=
        integral_congr_ae hdecomp_point
      _ = _ := MeasureTheory.integral_add hBarrierInt hGoodInt
  have hRestSplit :
      (∫ x, Rest x ∂intervalMeasure 1) =
        (∫ x, Wt x * φ x ∂intervalMeasure 1) +
        (∫ x, deriv et x * deriv φ x ∂intervalMeasure 1) -
        p.χ₀ * (∫ x, Q x * deriv φ x ∂intervalMeasure 1) -
        ∫ x, L x * φ x ∂intervalMeasure 1 := by
    have h1 := MeasureTheory.integral_add hWtφ hetDφ
    have h2 := MeasureTheory.integral_const_mul
      (μ := intervalMeasure 1) p.χ₀ (fun x => Q x * deriv φ x)
    have h3 := MeasureTheory.integral_sub (hWtφ.add hetDφ)
      (hQdφ.const_mul p.χ₀)
    have h4 := MeasureTheory.integral_sub
      ((hWtφ.add hetDφ).sub (hQdφ.const_mul p.χ₀)) hLφ
    dsimp [Rest]
    rw [show (∫ x,
        Wt x * φ x + deriv et x * deriv φ x -
          p.χ₀ * (Q x * deriv φ x) - L x * φ x
        ∂intervalMeasure 1) =
        (∫ x, Wt x * φ x + deriv et x * deriv φ x -
          p.χ₀ * (Q x * deriv φ x) ∂intervalMeasure 1) -
          ∫ x, L x * φ x ∂intervalMeasure 1 by
      simpa only [Pi.sub_apply] using h4]
    rw [show (∫ x, Wt x * φ x + deriv et x * deriv φ x -
        p.χ₀ * (Q x * deriv φ x) ∂intervalMeasure 1) =
        (∫ x, Wt x * φ x + deriv et x * deriv φ x
          ∂intervalMeasure 1) -
          ∫ x, p.χ₀ * (Q x * deriv φ x) ∂intervalMeasure 1 by
      simpa only [Pi.sub_apply] using h3]
    rw [show (∫ x, Wt x * φ x + deriv et x * deriv φ x
        ∂intervalMeasure 1) =
        (∫ x, Wt x * φ x ∂intervalMeasure 1) +
          ∫ x, deriv et x * deriv φ x ∂intervalMeasure 1 by
      simpa only [Pi.add_apply] using h1]
    rw [h2]
  have hBarrierSplit :
      (∫ x, Barrier x ∂intervalMeasure 1) =
        (∫ x, Wt x * φ x ∂intervalMeasure 1) +
        (∫ x, deriv wt x * deriv φ x ∂intervalMeasure 1) -
        p.χ₀ * (∫ x, g x * wt x * deriv φ x ∂intervalMeasure 1) -
        ∫ x, c x * wt x * φ x ∂intervalMeasure 1 := by
    have h1 := MeasureTheory.integral_add hWtφ hwtDφ
    have h2 := MeasureTheory.integral_const_mul
      (μ := intervalMeasure 1) p.χ₀ (fun x => g x * wt x * deriv φ x)
    have h3 := MeasureTheory.integral_sub (hWtφ.add hwtDφ)
      (hgwtDφ.const_mul p.χ₀)
    have h4 := MeasureTheory.integral_sub
      ((hWtφ.add hwtDφ).sub (hgwtDφ.const_mul p.χ₀)) hcwtφ
    dsimp [Barrier]
    rw [show (∫ x,
        Wt x * φ x + deriv wt x * deriv φ x -
          p.χ₀ * (g x * wt x * deriv φ x) - c x * wt x * φ x
        ∂intervalMeasure 1) =
        (∫ x, Wt x * φ x + deriv wt x * deriv φ x -
          p.χ₀ * (g x * wt x * deriv φ x) ∂intervalMeasure 1) -
          ∫ x, c x * wt x * φ x ∂intervalMeasure 1 by
      simpa only [Pi.sub_apply] using h4]
    rw [show (∫ x, Wt x * φ x + deriv wt x * deriv φ x -
        p.χ₀ * (g x * wt x * deriv φ x) ∂intervalMeasure 1) =
        (∫ x, Wt x * φ x + deriv wt x * deriv φ x
          ∂intervalMeasure 1) -
          ∫ x, p.χ₀ * (g x * wt x * deriv φ x) ∂intervalMeasure 1 by
      simpa only [Pi.sub_apply] using h3]
    rw [show (∫ x, Wt x * φ x + deriv wt x * deriv φ x
        ∂intervalMeasure 1) =
        (∫ x, Wt x * φ x ∂intervalMeasure 1) +
          ∫ x, deriv wt x * deriv φ x ∂intervalMeasure 1 by
      simpa only [Pi.add_apply] using h1]
    rw [h2]
  have hsub := truncatedSquareHeatBarrier_weak_subsolution
    DT ht htT hf hCf hf_bound hK hl2 Hφ.absolutelyContinuous
      (fun x => positivePart_nonneg _)
  have hsub' : (∫ x, Barrier x ∂intervalMeasure 1) ≤ 0 := by
    rw [hBarrierSplit]
    simpa [Mbar, Wt, wt, g, c, U, W, φ] using hsub
  have hgood_point : ∀ᵐ x ∂intervalMeasure 1,
      Good x ≤ ell * φ x ^ 2 := by
    filter_upwards [hgbound', hcle] with x hxg hxc
    have hA : |p.χ₀ * g x| ≤ |p.χ₀| * G₀ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hxg (abs_nonneg _)
    have hA2 : (p.χ₀ * g x) ^ 2 ≤ (|p.χ₀| * G₀) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hA 2
      calc
        (p.χ₀ * g x) ^ 2 = |p.χ₀ * g x| ^ 2 := (sq_abs _).symm
        _ ≤ (|p.χ₀| * G₀) ^ 2 := this
    have hyoung := sq_nonneg (deriv φ x - (p.χ₀ * g x) * φ x)
    have hreact : c x * φ x ^ 2 ≤ p.a * φ x ^ 2 :=
      mul_le_mul_of_nonneg_right hxc (sq_nonneg _)
    dsimp [Good, ell]
    nlinarith [sq_nonneg (deriv φ x), sq_nonneg (φ x)]
  have hell : 0 ≤ ell := by
    dsimp [ell]
    exact add_nonneg p.ha (div_nonneg (sq_nonneg _) (by norm_num))
  have hEllInt : Integrable (fun x => ell * φ x ^ 2)
      (intervalMeasure 1) := hφsq.const_mul ell
  have hgood_integral : (∫ x, Good x ∂intervalMeasure 1) ≤
      ell * comparisonPositivePartEnergy W U t := by
    have hm := MeasureTheory.integral_mono_ae hGoodInt hEllInt hgood_point
    rw [MeasureTheory.integral_const_mul] at hm
    simpa [comparisonPositivePartEnergy, W, U, φ] using hm
  rw [hRestSplit, hBarrierSplit] at hdecomp_integral
  have hinner :
      (∫ x, Wt x * φ x ∂intervalMeasure 1) +
        (∫ x, deriv et x * deriv φ x ∂intervalMeasure 1) -
        p.χ₀ * (∫ x, Q x * deriv φ x ∂intervalMeasure 1) -
        ∫ x, L x * φ x ∂intervalMeasure 1 ≤
      ell * comparisonPositivePartEnergy W U t := by
    linarith
  have htwice :=
    mul_le_mul_of_nonneg_left hinner (by norm_num : (0 : ℝ) ≤ 2)
  change 2 *
      ((∫ x, Wt x * φ x ∂intervalMeasure 1) +
        (∫ x, deriv et x * deriv φ x ∂intervalMeasure 1) -
        p.χ₀ * (∫ x, Q x * deriv φ x ∂intervalMeasure 1) -
        ∫ x, L x * φ x ∂intervalMeasure 1) ≤
      (2 * ell) * comparisonPositivePartEnergy W U t
  nlinarith

/-- Backward-slope input for the fencing Gronwall lemma. -/
theorem truncatedBarrierComparison_backward_energy_upper_tendsto
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T)
    (hU_nonneg : ∀ X : intervalDomainPoint,
      0 ≤ truncatedConjugatePicardLimit p u₀ DT.T t X)
    {f : ℝ → ℝ} (hf : Continuous f) {Cf K : ℝ} (hCf : 0 ≤ Cf)
    (hf_bound : ∀ y, |f y| ≤ Cf)
    (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2) :
    let Mbar := truncatedBarrierDiscount p DT.M
    let G₀ := truncatedDriftFactorC0 p DT.M
    let ell := p.a + (|p.χ₀| * G₀) ^ 2 / 2
    let W : ℝ → intervalDomainPoint → ℝ :=
      fun r X => squareHeatBarrier Mbar f r X.1
    let U := truncatedConjugatePicardLimit p u₀ DT.T
    let E := comparisonPositivePartEnergy W U
    ∃ d : ℝ, ∃ R : ℝ → ℝ,
      d ≤ (2 * ell) * E t ∧
      Tendsto R (nhdsWithin 0 (Set.Ioi 0)) (nhds d) ∧
      ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0),
        q⁻¹ * (E t - E (t - q)) ≤ R q := by
  let Mbar := truncatedBarrierDiscount p DT.M
  let G₀ := truncatedDriftFactorC0 p DT.M
  let ell := p.a + (|p.χ₀| * G₀) ^ 2 / 2
  let W : ℝ → intervalDomainPoint → ℝ :=
    fun r X => squareHeatBarrier Mbar f r X.1
  let U := truncatedConjugatePicardLimit p u₀ DT.T
  let E := comparisonPositivePartEnergy W U
  let φ : ℝ → ℝ := comparisonPositivePartLift W U t
  let et : ℝ → ℝ :=
    ShenWork.IntervalDomain.intervalDomainConstExtend (U t)
  let d : ℝ := 2 *
    ((∫ x,
        ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.barrierTimeDerivRep
          Mbar f t x * φ x ∂intervalMeasure 1) +
      (∫ x, deriv et x * deriv φ x ∂intervalMeasure 1) -
      p.χ₀ * (∫ x,
        truncatedChemFluxLifted p (U t) x * deriv φ x
        ∂intervalMeasure 1) -
      ∫ x, truncatedLogisticLifted p (U t) x * φ x
        ∂intervalMeasure 1)
  obtain ⟨R, hRlim, hRupper⟩ :=
    truncatedBarrierComparison_backward_quotient_upper_tendsto
      DT (Mbar := Mbar) ht htT hf hCf hf_bound hK hl2
  refine ⟨d, R, ?_, ?_, ?_⟩
  · simpa [d, Mbar, G₀, ell, W, U, E, φ, et] using
      (truncatedBarrierComparison_terminal_pairing_le
        DT ht htT hU_nonneg hf hCf hf_bound hK hl2)
  · simpa [d, Mbar, W, U, φ, et] using hRlim
  · simpa [Mbar, W, U, E] using hRupper

/-- Comparison energy is continuous on every compact positive-time window. -/
theorem truncatedBarrierComparison_energy_continuousOn_positive_window
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ DT.T)
    {f : ℝ → ℝ} (hf : Continuous f) {Cf K : ℝ} (hCf : 0 ≤ Cf)
    (hf_bound : ∀ y, |f y| ≤ Cf)
    (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2) :
    let Mbar := truncatedBarrierDiscount p DT.M
    let W : ℝ → intervalDomainPoint → ℝ :=
      fun r X => squareHeatBarrier Mbar f r X.1
    let U := truncatedConjugatePicardLimit p u₀ DT.T
    ContinuousOn (comparisonPositivePartEnergy W U) (Set.Icc a b) := by
  let Mbar := truncatedBarrierDiscount p DT.M
  let W : ℝ → intervalDomainPoint → ℝ :=
    fun r X => squareHeatBarrier Mbar f r X.1
  let U := truncatedConjugatePicardLimit p u₀ DT.T
  let F : ℝ → ℝ → ℝ := fun r y =>
    positivePart (intervalDomainLift (W r) y - intervalDomainLift (U r) y) ^ 2
  have hMbar : 0 ≤ Mbar := by
    dsimp [Mbar, truncatedBarrierDiscount]
    exact add_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
      (truncatedBarrierReactionNegBound_nonneg p DT.hM.le)
  have hwindow : Set.Icc a b ⊆ Set.Ioc (0 : ℝ) DT.T := by
    intro r hr
    exact ⟨ha.trans_le hr.1, hr.2.trans hbT⟩
  have hWbound : ∀ r ∈ Set.Icc a b, ∀ y,
      |squareHeatBarrier Mbar f r y| ≤ Cf ^ 2 := by
    intro r hr y
    have hr0 : 0 ≤ r := ha.le.trans hr.1
    have hS :=
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
        (ha.trans_le hr.1) hCf hf_bound y
    dsimp [squareHeatBarrier]
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
    have hexp : Real.exp (-Mbar * r) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hmr := mul_nonneg hMbar hr0
      nlinarith
    calc
      Real.exp (-Mbar * r) * |intervalFullSemigroupOperator r f y| ^ 2 ≤
          1 * Cf ^ 2 := mul_le_mul hexp
        (pow_le_pow_left₀ (abs_nonneg _) hS 2) (sq_nonneg _) (by norm_num)
      _ = Cf ^ 2 := one_mul _
  have hFmeas : ∀ r ∈ Set.Icc a b,
      AEStronglyMeasurable (F r) (intervalMeasure 1) := by
    intro r hr
    have hr0 : 0 < r := ha.trans_le hr.1
    have hrT : r ≤ DT.T := hr.2.trans hbT
    have hWr :=
      (ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.squareHeatBarrierSliceRegularData_of_semigroup
        (M := Mbar) hr0 hf hCf hf_bound hK hl2)
    have hUr : Continuous (U r) := by
      simpa [U] using
        (truncatedConjugateMildSolutionData_of_data DT).hcont r hr0 hrT
    have hWsub : Continuous (W r) :=
      hWr.continuous.comp continuous_subtype_val
    have hliftW := intervalDomainLift_continuousOn_Icc hWsub
    have hliftU := intervalDomainLift_continuousOn_Icc hUr
    have hp : Continuous (fun z : ℝ => positivePart z) := by
      simpa [positivePart] using continuous_id.max continuous_const
    exact ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
      ((hp.continuousOn.comp
        (hliftW.sub hliftU) (fun _ _ => Set.mem_univ _)).pow 2)
  let C : ℝ := (Cf ^ 2 + DT.M) ^ 2
  have hC : 0 ≤ C := sq_nonneg _
  have hFbound : ∀ r ∈ Set.Icc a b, ∀ᵐ y ∂intervalMeasure 1,
      ‖F r y‖ ≤ C := by
    intro r hr
    filter_upwards [ae_mem_unitInterval] with y hy
    have hU : |intervalDomainLift (U r) y| ≤ DT.M := by
      simpa [intervalDomainLift, hy, U] using
        (truncatedConjugateMildSolutionData_of_data DT).hbound r
          (ha.trans_le hr.1) (hr.2.trans hbT) ⟨y, hy⟩
    have hW : |intervalDomainLift (W r) y| ≤ Cf ^ 2 := by
      simpa [intervalDomainLift, hy, W] using hWbound r hr y
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      ((abs_positivePart_le_abs _).trans
        ((abs_sub _ _).trans (add_le_add hW hU))) 2
  have hFcont : ∀ᵐ y ∂intervalMeasure 1,
      ContinuousOn (fun r => F r y) (Set.Icc a b) := by
    filter_upwards [ae_mem_unitInterval] with y hy
    let X : intervalDomainPoint := ⟨y, hy⟩
    have hUtime : ContinuousOn (fun r => U r X) (Set.Icc a b) :=
      (ShenWork.Paper2.IntervalTruncatedEnergyProducer.truncatedLimit_timeSlice_continuousOn_Ioc
        DT X).mono hwindow
    have hWtime : ContinuousOn
        (fun r => squareHeatBarrier Mbar f r y) (Set.Icc a b) := by
      intro r hr
      exact
        (ShenWork.Paper2.IntervalMatchedDivergenceBarrierAtoms.squareHeatBarrier_time_hasDerivAt_rep
          (M := Mbar) (t := r) (x := y) (ha.trans_le hr.1) hf hK hy).continuousAt.continuousWithinAt
    have hp : Continuous (fun z : ℝ => positivePart z) := by
      simpa [positivePart] using continuous_id.max continuous_const
    have hcomp := (hp.continuousOn.comp
      (hWtime.sub hUtime) (fun _ _ => Set.mem_univ _)).pow 2
    have hy0 : 0 ≤ y := hy.1
    have hy1 : y ≤ 1 := hy.2
    simpa [F, W, U, intervalDomainLift, hy0, hy1, X] using hcomp
  have hdom : Integrable (fun _ : ℝ => C) (intervalMeasure 1) :=
    integrable_const _
  have hint := MeasureTheory.continuousOn_of_dominated
    hFmeas hFbound hdom hFcont
  simpa [comparisonPositivePartEnergy, F, W, U] using hint

/-- If the squared seed agrees with the initial datum, the comparison energy
tends to zero at the artificial zero-time endpoint. -/
theorem truncatedBarrierComparison_energy_tendsto_zero_at_initial
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (htrace : InitialTrace intervalDomain u₀
      (truncatedConjugatePicardLimit p u₀ DT.T))
    {f : ℝ → ℝ} (hf : Continuous f) {Cf : ℝ} (hCf : 0 ≤ Cf)
    (hf_bound : ∀ y, |f y| ≤ Cf)
    (hfsq : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      f y ^ 2 = intervalDomainLift u₀ y) :
    let Mbar := truncatedBarrierDiscount p DT.M
    let W : ℝ → intervalDomainPoint → ℝ :=
      fun r X => squareHeatBarrier Mbar f r X.1
    let U := truncatedConjugatePicardLimit p u₀ DT.T
    Tendsto (comparisonPositivePartEnergy W U)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let Mbar := truncatedBarrierDiscount p DT.M
  let W : ℝ → intervalDomainPoint → ℝ :=
    fun r X => squareHeatBarrier Mbar f r X.1
  let U := truncatedConjugatePicardLimit p u₀ DT.T
  let F : ℝ → ℝ → ℝ := fun r y =>
    positivePart (intervalDomainLift (W r) y - intervalDomainLift (U r) y) ^ 2
  have hMbar : 0 ≤ Mbar := by
    dsimp [Mbar, truncatedBarrierDiscount]
    exact add_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
      (truncatedBarrierReactionNegBound_nonneg p DT.hM.le)
  have hUlim : ∀ X : intervalDomainPoint,
      Tendsto (fun r => U r X) (nhdsWithin 0 (Set.Ioi 0)) (nhds (u₀ X)) := by
    intro X
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := InitialTrace.eventually_small htrace hε
    have hmin : 0 < min δ DT.T := lt_min hδ DT.hT
    filter_upwards [Ioo_mem_nhdsGT hmin] with r hr
    have hr0 : 0 < r := hr.1
    have hrδ : r < δ := hr.2.trans_le (min_le_left _ _)
    have hrT : r < DT.T := hr.2.trans_le (min_le_right _ _)
    have hsup := hsmall r hr0 hrδ
    have hUr_bound : ∀ Y : intervalDomainPoint, |U r Y| ≤ DT.M := by
      intro Y
      simpa [U] using
        (truncatedConjugateMildSolutionData_of_data DT).hbound r hr0 hrT.le Y
    have hdiff_bdd : BddAbove
        (Set.range (fun Y : intervalDomainPoint => |U r Y - u₀ Y|)) :=
      ShenWork.Paper2.BFormPositiveDatumNegPart.bddAbove_abs_sub_of_bddAbove_abs_restart
        (ShenWork.Paper2.BFormPositiveDatumNegPart.bddAbove_abs_of_uniform_bound_restart
          hUr_bound) hu₀.admissible.1
    have hpoint :=
      ShenWork.Paper2.BFormPositiveDatumNegPart.intervalDomain_pointwise_abs_lt_of_supNorm_lt_restart
        hdiff_bdd hsup X
    simpa [Real.dist_eq, U] using hpoint
  have hExp : Tendsto (fun r : ℝ => Real.exp (-Mbar * r))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hc : ContinuousAt (fun r : ℝ => Real.exp (-Mbar * r)) 0 := by
      fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hFmeas : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0),
      AEStronglyMeasurable (F r) (intervalMeasure 1) := by
    have hsmall : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), r < DT.T :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds DT.hT)
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr0 hrT
    have hScont : Continuous (fun y => intervalFullSemigroupOperator r f y) :=
      ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
        hr0 hCf hf_bound hf.aestronglyMeasurable
    have hWcont : Continuous (fun y => squareHeatBarrier Mbar f r y) := by
      simpa [squareHeatBarrier] using continuous_const.mul (hScont.pow 2)
    have hUcont : Continuous (U r) := by
      simpa [U] using
        (truncatedConjugateMildSolutionData_of_data DT).hcont r hr0 hrT.le
    have hWsub : Continuous (W r) := hWcont.comp continuous_subtype_val
    have hp : Continuous (fun z : ℝ => positivePart z) := by
      simpa [positivePart] using continuous_id.max continuous_const
    exact ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
      ((hp.continuousOn.comp
        ((intervalDomainLift_continuousOn_Icc hWsub).sub
          (intervalDomainLift_continuousOn_Icc hUcont))
        (fun _ _ => Set.mem_univ _)).pow 2)
  let C : ℝ := (Cf ^ 2 + DT.M) ^ 2
  have hFbound : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0),
      ∀ᵐ y ∂intervalMeasure 1, ‖F r y‖ ≤ C := by
    have hsmall : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), r < DT.T :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds DT.hT)
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr0 hrT
    filter_upwards [ae_mem_unitInterval] with y hy
    have hS :=
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
        hr0 hCf hf_bound y
    have hexp : Real.exp (-Mbar * r) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hmr := mul_nonneg hMbar hr0.le
      nlinarith
    have hW : |intervalDomainLift (W r) y| ≤ Cf ^ 2 := by
      simp only [intervalDomainLift, dif_pos hy, W]
      dsimp [squareHeatBarrier]
      rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
      calc
        Real.exp (-Mbar * r) * |intervalFullSemigroupOperator r f y| ^ 2 ≤
            1 * Cf ^ 2 := mul_le_mul hexp
          (pow_le_pow_left₀ (abs_nonneg _) hS 2) (sq_nonneg _) (by norm_num)
        _ = Cf ^ 2 := one_mul _
    have hU : |intervalDomainLift (U r) y| ≤ DT.M := by
      simpa [intervalDomainLift, hy, U] using
        (truncatedConjugateMildSolutionData_of_data DT).hbound r hr0 hrT.le ⟨y, hy⟩
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      ((abs_positivePart_le_abs _).trans
        ((abs_sub _ _).trans (add_le_add hW hU))) 2
  have hFlim : ∀ᵐ y ∂intervalMeasure 1,
      Tendsto (fun r => F r y) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    filter_upwards [ae_mem_unitInterval] with y hy
    let X : intervalDomainPoint := ⟨y, hy⟩
    have hS :=
      (ShenWork.IntervalSemigroupUniform.intervalFullSemigroup_tendstoUniformlyOn
        f hf).tendsto_at hy
    have hWlim : Tendsto (fun r => squareHeatBarrier Mbar f r y)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (f y ^ 2)) := by
      simpa [squareHeatBarrier] using hExp.mul (hS.pow 2)
    have hdiff := hWlim.sub (hUlim X)
    have hp : Continuous (fun z : ℝ => positivePart z ^ 2) := by
      have hp0 : Continuous (fun z : ℝ => positivePart z) := by
        simpa [positivePart] using continuous_id.max continuous_const
      exact hp0.pow 2
    have hcomp := hp.continuousAt.tendsto.comp hdiff
    have hsquare : f y ^ 2 - u₀ X = 0 := by
      simpa [X, intervalDomainLift, hy] using sub_eq_zero.mpr (hfsq y hy)
    have hy0 : 0 ≤ y := hy.1
    have hy1 : y ≤ 1 := hy.2
    simpa [F, W, U, intervalDomainLift, hy0, hy1, X, hsquare,
      positivePart, Function.comp_def] using hcomp
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => C) hFmeas hFbound (integrable_const _) hFlim
  simpa [comparisonPositivePartEnergy, F, W, U] using hDCT

/-- Positive-window continuity plus the matched initial trace gives continuity
on the whole closed active interval. -/
theorem truncatedBarrierComparison_energy_continuousOn_Icc
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (htrace : InitialTrace intervalDomain u₀
      (truncatedConjugatePicardLimit p u₀ DT.T))
    {f : ℝ → ℝ} (hf : Continuous f) {Cf K : ℝ} (hCf : 0 ≤ Cf)
    (hf_bound : ∀ y, |f y| ≤ Cf)
    (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
    (hfsq : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      f y ^ 2 = intervalDomainLift u₀ y) :
    let Mbar := truncatedBarrierDiscount p DT.M
    let W : ℝ → intervalDomainPoint → ℝ :=
      fun r X => squareHeatBarrier Mbar f r X.1
    let U := truncatedConjugatePicardLimit p u₀ DT.T
    ContinuousOn (comparisonPositivePartEnergy W U)
      (Set.Icc (0 : ℝ) DT.T) := by
  let Mbar := truncatedBarrierDiscount p DT.M
  let W : ℝ → intervalDomainPoint → ℝ :=
    fun r X => squareHeatBarrier Mbar f r X.1
  let U := truncatedConjugatePicardLimit p u₀ DT.T
  let E : ℝ → ℝ := comparisonPositivePartEnergy W U
  have hEtend : Tendsto E (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [E, Mbar, W, U] using
      (truncatedBarrierComparison_energy_tendsto_zero_at_initial
        hu₀ DT htrace hf hCf hf_bound hfsq)
  have hE0 : E 0 = 0 := by
    have hU0 : U 0 = fun _ : intervalDomainPoint => 0 := by
      funext X
      simp [U, truncatedConjugatePicardLimit]
    have hW0 : W 0 = fun _ : intervalDomainPoint => 0 := by
      funext X
      simp [W, squareHeatBarrier,
        ShenWork.IntervalSemigroupAtZero.intervalFullSemigroupOperator_zero]
    simp [E, comparisonPositivePartEnergy, comparisonPositivePartLift,
      hU0, hW0, intervalDomainLift, positivePart]
  have hzero : ContinuousWithinAt E (Set.Ici (0 : ℝ)) 0 := by
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hev : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), dist (E r) 0 < ε :=
      (Metric.tendsto_nhds.mp hEtend) ε hε
    change {r : ℝ | dist (E r) 0 < ε} ∈ nhdsWithin 0 (Set.Ioi 0) at hev
    obtain ⟨S, hSnh, hSsub⟩ :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hev
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hSnh
    refine ⟨δ, hδ, ?_⟩
    intro r hrI hdist
    rw [hE0]
    by_cases hrz : r = 0
    · subst r
      simpa [hE0] using hε
    · have hrpos : 0 < r := lt_of_le_of_ne hrI (Ne.symm hrz)
      have hrball : r ∈ Metric.ball (0 : ℝ) δ := by simpa using hdist
      exact hSsub ⟨hball hrball, hrpos⟩
  change ContinuousOn E (Set.Icc (0 : ℝ) DT.T)
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    exact hzero.mono fun r hr => hr.1
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    let a : ℝ := t / 2
    have ha : 0 < a := by dsimp [a]; linarith
    have hat : a ≤ t := by dsimp [a]; linarith
    have htmem : t ∈ Set.Icc a DT.T := ⟨hat, ht.2⟩
    have hposwin : ContinuousOn E (Set.Icc a DT.T) := by
      simpa [E, Mbar, W, U] using
        truncatedBarrierComparison_energy_continuousOn_positive_window
          DT ha (hat.trans ht.2) le_rfl hf hCf hf_bound hK hl2
    have hnhds : Set.Icc a DT.T ∈
        nhdsWithin t (Set.Icc (0 : ℝ) DT.T) := by
      have hopen : Set.Ioi a ∈ nhds t := Ioi_mem_nhds (by dsimp [a]; linarith)
      have hinter : Set.Icc (0 : ℝ) DT.T ∩ Set.Ioi a ∈
          nhdsWithin t (Set.Icc (0 : ℝ) DT.T) :=
        inter_mem_nhdsWithin _ hopen
      exact mem_of_superset hinter fun r hr => ⟨hr.2.le, hr.1.2⟩
    exact (hposwin.continuousWithinAt htmem).mono_of_mem_nhdsWithin hnhds

/-- Weak matched-divergence comparison of the squared heat barrier with the
nonnegative truncated mild solution, on the closed spatial interval. -/
theorem truncatedSquareHeatBarrier_le_truncatedLimit
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (htrace : InitialTrace intervalDomain u₀
      (truncatedConjugatePicardLimit p u₀ DT.T))
    (hnonneg : ∀ r, 0 < r → r ≤ DT.T →
      ∀ X : intervalDomainPoint,
        0 ≤ truncatedConjugatePicardLimit p u₀ DT.T r X)
    {f : ℝ → ℝ} (hf : Continuous f) {Cf K : ℝ} (hCf : 0 ≤ Cf)
    (hf_bound : ∀ y, |f y| ≤ Cf)
    (hK : ∀ n, |cosineCoeffs f n| ≤ K)
    (hl2 : Summable fun n : ℕ => (cosineCoeffs f n) ^ 2)
    (hfsq : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      f y ^ 2 = intervalDomainLift u₀ y) :
    ∀ t, 0 < t → t ≤ DT.T → ∀ X : intervalDomainPoint,
      squareHeatBarrier (truncatedBarrierDiscount p DT.M) f t X.1 ≤
        truncatedConjugatePicardLimit p u₀ DT.T t X := by
  let Mbar := truncatedBarrierDiscount p DT.M
  let G₀ := truncatedDriftFactorC0 p DT.M
  let ell := p.a + (|p.χ₀| * G₀) ^ 2 / 2
  let W : ℝ → intervalDomainPoint → ℝ :=
    fun r X => squareHeatBarrier Mbar f r X.1
  let U := truncatedConjugatePicardLimit p u₀ DT.T
  let E : ℝ → ℝ := comparisonPositivePartEnergy W U
  have hcont : ContinuousOn E (Set.Icc (0 : ℝ) DT.T) := by
    simpa [E, Mbar, W, U] using
      truncatedBarrierComparison_energy_continuousOn_Icc
        hu₀ DT htrace hf hCf hf_bound hK hl2 hfsq
  have hEnonneg : ∀ r ∈ Set.Icc (0 : ℝ) DT.T, 0 ≤ E r := by
    intro r _hr
    exact integral_nonneg fun y => sq_nonneg (comparisonPositivePartLift W U r y)
  have hE0 : E 0 = 0 := by
    have hU0 : U 0 = fun _ : intervalDomainPoint => 0 := by
      funext X
      simp [U, truncatedConjugatePicardLimit]
    have hW0 : W 0 = fun _ : intervalDomainPoint => 0 := by
      funext X
      simp [W, squareHeatBarrier,
        ShenWork.IntervalSemigroupAtZero.intervalFullSemigroupOperator_zero]
    simp [E, comparisonPositivePartEnergy, comparisonPositivePartLift,
      hU0, hW0, intervalDomainLift, positivePart]
  have hupper : ∀ r ∈ Set.Ioc (0 : ℝ) DT.T,
      ∃ d : ℝ, ∃ R : ℝ → ℝ,
        d ≤ (2 * ell) * E r ∧
        Tendsto R (nhdsWithin 0 (Set.Ioi 0)) (nhds d) ∧
        ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0),
          q⁻¹ * (E r - E (r - q)) ≤ R q := by
    intro r hr
    simpa [Mbar, G₀, ell, W, U, E] using
      (truncatedBarrierComparison_backward_energy_upper_tendsto
        DT hr.1 hr.2 (hnonneg r hr.1 hr.2) hf hCf hf_bound hK hl2)
  have hzero :=
    ShenWork.Paper2.IntervalNegativePartWeakEnergy.backward_gronwall_zero_of_upper_tendsto
      DT.hT.le hcont hEnonneg hE0 hupper
  intro t ht htT X
  have hEt : comparisonPositivePartEnergy W U t = 0 := by
    simpa [E] using hzero t ⟨ht.le, htT⟩
  let Hφ : ComparisonTerminalTestData (W t) (U t) :=
    truncatedSquareHeatBarrier_terminalTestData DT ht htT hf hCf hf_bound hK hl2
  have hpoint :=
    pointwise_le_on_closed_of_comparisonPositivePartEnergy_eq_zero Hφ (by
      simpa [comparisonPositivePartEnergy] using hEt) X
  simpa [Mbar, W, U] using hpoint

end ShenWork.Paper2.IntervalTruncatedWeakBarrierComparisonClosure
