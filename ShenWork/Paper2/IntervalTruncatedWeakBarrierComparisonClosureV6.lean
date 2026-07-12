import ShenWork.Paper2.IntervalTruncatedWeakBarrierComparisonV6

open Filter Topology Set MeasureTheory
open scoped BigOperators Topology ENNReal

noncomputable section

namespace ShenWork.Paper2.IntervalTruncatedWeakBarrierComparisonClosureV6

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.Paper2.BFormPositiveDatumNegPart
  (SquareHeatSeed squareHeatBarrier squareHeatResidualCore
   neumannLinearDriftResidual)
open ShenWork.Paper2.IntervalTruncatedWeakBarrierComparisonV6

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

end ShenWork.Paper2.IntervalTruncatedWeakBarrierComparisonClosureV6
