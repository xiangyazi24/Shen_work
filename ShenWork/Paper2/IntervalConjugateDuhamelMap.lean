/-
  ShenWork/Paper2/IntervalConjugateDuhamelMap.lean

  Paper 2, general χ: the B-form / conjugate-kernel Picard map.

  The chemotaxis leg uses

    B_N(t) Q (x) = -∫₀¹ ∂ᵧ K_N(t,x,y) Q(y) dy,

  so the spatial output is a Neumann/cosine object.  This file is additive:
  it introduces new names only and does not alter the existing gradient-Duhamel
  assembly.

  Fully proved; no placeholder proof terms or custom logical constants.
-/
import ShenWork.PDE.IntervalFullKernelGradientLinfty
import ShenWork.PDE.IntervalFullKernelSDependentMeasurable
import ShenWork.PDE.IntervalFullSemigroupNeumann
import ShenWork.PDE.IntervalGradDuhamelBound
import ShenWork.Paper2.IntervalGradientDuhamelMap
import ShenWork.Paper2.IntervalDomainPdeUChiZero
import ShenWork.PDE.IntervalFullKernelGradientTiling

open MeasureTheory intervalIntegral
open scoped Topology

noncomputable section

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain
open ShenWork.HeatKernelGradientEstimates (heatGradientLinftyLinftyConstant)

/-! ## The second-variable full-kernel derivative -/

/-- `∂ᵧ` of the full periodised Neumann kernel.  The direct image has the
opposite sign from the first-variable derivative; the reflected image has the
same sign. -/
theorem hasDerivAt_intervalNeumannFullKernel_snd {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun y : ℝ => intervalNeumannFullKernel t x y)
      (-(∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (x - y + 2 * (k : ℝ)))
        + (∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (x + y + 2 * (k : ℝ)))) y := by
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1 : ℝ) y := by
    convert (hasDerivAt_const y (0 : ℝ)).sub (hasDerivAt_id y) using 1
    · ext z
      simp
    · norm_num
  have hL0 : HasDerivAt
      (fun w : ℝ => ∑' k : ℤ, heatKernel t (w + x + 2 * (k : ℝ)))
      (∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) ((-y) + x + 2 * (k : ℝ))) (-y) :=
    hasDerivAt_heatKernel_lattice_tsum ht x (-y)
  have hL : HasDerivAt
      (fun y : ℝ => ∑' k : ℤ, heatKernel t (x - y + 2 * (k : ℝ)))
      (-(∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (x - y + 2 * (k : ℝ)))) y := by
    have hcomp := hL0.comp y hneg
    change HasDerivAt
        (fun y : ℝ => ∑' k : ℤ, heatKernel t ((-y) + x + 2 * (k : ℝ)))
        ((∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) ((-y) + x + 2 * (k : ℝ)))
          * (-1 : ℝ)) y at hcomp
    have hfun :
        (fun y : ℝ => ∑' k : ℤ, heatKernel t ((-y) + x + 2 * (k : ℝ)))
          = fun y : ℝ => ∑' k : ℤ, heatKernel t (x - y + 2 * (k : ℝ)) := by
      funext z
      refine tsum_congr (fun k => ?_)
      congr 1
      ring
    have hder :
        (∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) ((-y) + x + 2 * (k : ℝ))) * (-1 : ℝ)
          = -(∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (x - y + 2 * (k : ℝ))) := by
      have hsum :
          (∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) ((-y) + x + 2 * (k : ℝ)))
            = ∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (x - y + 2 * (k : ℝ)) := by
        refine tsum_congr (fun k => ?_)
        congr 1
        ring
      rw [hsum]
      ring
    rw [hfun] at hcomp
    simpa [hder] using hcomp
  have hR : HasDerivAt
      (fun y : ℝ => ∑' k : ℤ, heatKernel t (x + y + 2 * (k : ℝ)))
      (∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (x + y + 2 * (k : ℝ))) y := by
    have hbase := hasDerivAt_heatKernel_lattice_tsum ht x y
    have hfun :
        (fun y : ℝ => ∑' k : ℤ, heatKernel t (y + x + 2 * (k : ℝ)))
          = fun y : ℝ => ∑' k : ℤ, heatKernel t (x + y + 2 * (k : ℝ)) := by
      funext z
      refine tsum_congr (fun k => ?_)
      congr 1
      ring
    have hder :
        (∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (y + x + 2 * (k : ℝ)))
          = ∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (x + y + 2 * (k : ℝ)) := by
      refine tsum_congr (fun k => ?_)
      congr 1
      ring
    rw [hfun] at hbase
    simpa [hder] using hbase
  have hfun : (fun y : ℝ => intervalNeumannFullKernel t x y)
      = fun y => (∑' k : ℤ, heatKernel t (x - y + 2 * (k : ℝ)))
          + (∑' k : ℤ, heatKernel t (x + y + 2 * (k : ℝ))) := by
    funext y
    rw [intervalNeumannFullKernel]
    exact Summable.tsum_add (latticeGaussianSummable ht (x - y))
      (latticeGaussianSummable ht (x + y))
  rw [hfun]
  exact hL.add hR

/-- Pointwise absolute bound for `∂ᵧ K_full`, mirroring the first-variable
bound. -/
theorem abs_deriv_intervalNeumannFullKernel_snd_le {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    |deriv (fun y : ℝ => intervalNeumannFullKernel t x y) y|
      ≤ ∑' k : ℤ, (|deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|
          + |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))|) := by
  rw [(hasDerivAt_intervalNeumannFullKernel_snd ht x y).deriv]
  have hsumA : Summable
      (fun k : ℤ => |deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|) :=
    summable_abs_iff.mpr (latticeGaussianGradSummable ht (x - y))
  have hsumB : Summable
      (fun k : ℤ => |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))|) :=
    summable_abs_iff.mpr (latticeGaussianGradSummable ht (x + y))
  have hA : |∑' k : ℤ, deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|
      ≤ ∑' k : ℤ, |deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm
        (f := fun k : ℤ => deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ)))
        (by simpa [Real.norm_eq_abs] using hsumA)
  have hB : |∑' k : ℤ, deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))|
      ≤ ∑' k : ℤ, |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm
        (f := fun k : ℤ => deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ)))
        (by simpa [Real.norm_eq_abs] using hsumB)
  calc |-(∑' k : ℤ, deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ)))
          + (∑' k : ℤ, deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ)))|
      ≤ |∑' k : ℤ, deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|
          + |∑' k : ℤ, deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))| := by
        simpa [abs_neg] using
          abs_add_le (-(∑' k : ℤ, deriv (fun z : ℝ => heatKernel t z)
            (x - y + 2 * (k : ℝ))))
            (∑' k : ℤ, deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ)))
    _ ≤ (∑' k : ℤ, |deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|)
          + (∑' k : ℤ, |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))|) :=
        add_le_add hA hB
    _ = ∑' k : ℤ, (|deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|
          + |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))|) :=
        (Summable.tsum_add hsumA hsumB).symm

/-- Continuity of `y ↦ ∂ᵧ K_full(t,x,y)` on `[0,1]`. -/
theorem continuousOn_deriv_intervalNeumannFullKernel_snd {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ContinuousOn (fun y : ℝ => deriv (fun y : ℝ => intervalNeumannFullKernel t x y) y)
      (Set.Icc 0 1) := by
  have hcd := continuous_deriv_heatKernel ht
  have hfun : (fun y : ℝ => deriv (fun y : ℝ => intervalNeumannFullKernel t x y) y)
      = fun y : ℝ =>
          -(∑' k : ℤ, deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ)))
          + (∑' k : ℤ, deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))) := by
    funext y
    exact (hasDerivAt_intervalNeumannFullKernel_snd ht x y).deriv
  rw [hfun]
  refine ContinuousOn.add ?_ ?_
  · apply ContinuousOn.neg
    refine continuousOn_tsum (fun k => (hcd.comp (by fun_prop)).continuousOn)
      (summable_heatGradUnitBound ht x) (fun k y hy => ?_)
    rw [Real.norm_eq_abs]
    refine abs_deriv_heatKernel_le_unitShift ht x k ?_
    rw [show x - y + 2 * (k : ℝ) - (x + 2 * (k : ℝ)) = -y by ring, abs_neg]
    exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  · refine continuousOn_tsum (fun k => (hcd.comp (by fun_prop)).continuousOn)
      (summable_heatGradUnitBound ht x) (fun k y hy => ?_)
    rw [Real.norm_eq_abs]
    refine abs_deriv_heatKernel_le_unitShift ht x k ?_
    rw [show x + y + 2 * (k : ℝ) - (x + 2 * (k : ℝ)) = y by ring]
    exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- Joint measurability of the full-kernel second-variable derivative closed form
in `(s, y)`. -/
theorem deriv_intervalNeumannFullKernel_snd_s_dependent_measurable (t x₀ : ℝ) :
    Measurable (fun w : ℝ × ℝ =>
      -(∑' k : ℤ, deriv (fun z : ℝ => heatKernel (t - w.1) z)
          (x₀ - w.2 + 2 * (k : ℝ)))
        + (∑' k : ℤ, deriv (fun z : ℝ => heatKernel (t - w.1) z)
          (x₀ + w.2 + 2 * (k : ℝ)))) := by
  set g₁ : ℤ → ℝ × ℝ → ℝ :=
    fun k w => deriv (fun z : ℝ => heatKernel (t - w.1) z)
      (x₀ - w.2 + 2 * (k : ℝ)) with hg₁_def
  set g₂ : ℤ → ℝ × ℝ → ℝ :=
    fun k w => deriv (fun z : ℝ => heatKernel (t - w.1) z)
      (x₀ + w.2 + 2 * (k : ℝ)) with hg₂_def
  have hg₁_meas : ∀ k, Measurable (g₁ k) := fun _ =>
    measurable_deriv_heatKernel_comp (by fun_prop) t
  have hg₂_meas : ∀ k, Measurable (g₂ k) := fun _ =>
    measurable_deriv_heatKernel_comp (by fun_prop) t
  have hsum_aux : ∀ (z : ℝ) (w : ℝ × ℝ),
      Summable (fun k : ℤ =>
        deriv (fun u : ℝ => heatKernel (t - w.1) u) (z + 2 * (k : ℝ))) := by
    intro z w
    rcases lt_or_ge 0 (t - w.1) with hτ | hτ
    · exact latticeGaussianGradSummable hτ z
    · have hz : (fun k : ℤ =>
          deriv (fun u : ℝ => heatKernel (t - w.1) u) (z + 2 * (k : ℝ)))
          = fun _ : ℤ => (0 : ℝ) := by
        funext k
        have hzero : (fun u : ℝ => heatKernel (t - w.1) u) = fun _ : ℝ => (0 : ℝ) := by
          funext u
          exact heatKernel_of_nonpos hτ u
        rw [hzero, deriv_const]
      rw [hz]
      exact summable_zero
  have hg₁_sum : ∀ w, Summable (fun k : ℤ => g₁ k w) := fun w =>
    hsum_aux (x₀ - w.2) w
  have hg₂_sum : ∀ w, Summable (fun k : ℤ => g₂ k w) := fun w =>
    hsum_aux (x₀ + w.2) w
  simpa [g₁, g₂] using
    ((measurable_tsum_int_of_summable hg₁_meas hg₁_sum).neg.add
      (measurable_tsum_int_of_summable hg₂_meas hg₂_sum))

/-- Interval-integrability of `∂ᵧ K_full(t,x,y)` on `[0,1]`. -/
theorem intervalIntegrable_deriv_intervalNeumannFullKernel_snd {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    IntervalIntegrable (fun y : ℝ => deriv (fun y : ℝ => intervalNeumannFullKernel t x y) y)
      MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact continuousOn_deriv_intervalNeumannFullKernel_snd ht x

/-- The same `L¹` mass bound for `∂ᵧK_full` as for `∂ₓK_full`. -/
theorem intervalNeumannFullKernel_deriv_snd_abs_interval_integral_le {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    (∫ y in (0 : ℝ)..1, |deriv (fun y : ℝ => intervalNeumannFullKernel t x y) y|)
      ≤ heatGradientLinftyLinftyConstant * t ^ (-(1 / 2) : ℝ) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hcd := continuous_deriv_heatKernel ht
  have hAcont : ∀ k : ℤ,
      Continuous (fun y : ℝ => |deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|) :=
    fun k => (hcd.comp (by fun_prop)).abs
  have hBcont : ∀ k : ℤ,
      Continuous (fun y : ℝ => |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))|) :=
    fun k => (hcd.comp (by fun_prop)).abs
  have hAii : ∀ k : ℤ,
      IntervalIntegrable (fun y : ℝ => |deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|)
        MeasureTheory.volume 0 1 := fun k => (hAcont k).intervalIntegrable 0 1
  have hBii : ∀ k : ℤ,
      IntervalIntegrable (fun y : ℝ => |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))|)
        MeasureTheory.volume 0 1 := fun k => (hBcont k).intervalIntegrable 0 1
  set hk : ℤ → ℝ → ℝ := fun k y =>
    |deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|
      + |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))| with hk_def
  have hk_nonneg : ∀ k y, 0 ≤ hk k y := fun k y => by rw [hk_def]; positivity
  have hu2 : Summable (fun k : ℤ => 2 * heatGradUnitBound t x k) :=
    (summable_heatGradUnitBound ht x).mul_left 2
  have hk_bound : ∀ (k : ℤ) (y : ℝ), y ∈ Set.Icc (0 : ℝ) 1 →
      ‖hk k y‖ ≤ 2 * heatGradUnitBound t x k := by
    intro k y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (hk_nonneg k y)]
    have h1 := abs_deriv_heatKernel_le_unitShift ht x k (w := x - y + 2 * (k : ℝ))
      (by rw [show x - y + 2 * (k : ℝ) - (x + 2 * (k : ℝ)) = -y by ring, abs_neg]
          exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    have h2 := abs_deriv_heatKernel_le_unitShift ht x k (w := x + y + 2 * (k : ℝ))
      (by rw [show x + y + 2 * (k : ℝ) - (x + 2 * (k : ℝ)) = y by ring]
          exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    rw [hk_def]
    linarith [h1, h2]
  have hDii : IntervalIntegrable (fun y : ℝ => ∑' k : ℤ, hk k y)
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h01]
    exact continuousOn_tsum (fun k => ((hAcont k).add (hBcont k)).continuousOn) hu2 hk_bound
  have hmono : (∫ y in (0 : ℝ)..1, |deriv (fun y : ℝ => intervalNeumannFullKernel t x y) y|)
      ≤ ∫ y in (0 : ℝ)..1, ∑' k : ℤ, hk k y := by
    refine intervalIntegral.integral_mono_on h01
      (intervalIntegrable_deriv_intervalNeumannFullKernel_snd ht x).abs hDii
      (fun y _ => ?_)
    rw [hk_def]
    exact abs_deriv_intervalNeumannFullKernel_snd_le ht x y
  refine hmono.trans (le_of_eq ?_)
  have hμint : ∀ k : ℤ, Integrable (hk k)
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro k
    rw [hk_def]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mp ((hAii k).add (hBii k))
  have heq : ∀ k : ℤ,
      (∫ y, ‖hk k y‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)))
        = (∫ y in (0 : ℝ)..1,
              |deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|)
            + (∫ y in (0 : ℝ)..1,
              |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))|) := by
    intro k
    have e1 : (∫ y, ‖hk k y‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)))
        = ∫ y in (0 : ℝ)..1, hk k y := by
      rw [intervalIntegral.integral_of_le h01]
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun y => Real.norm_of_nonneg (hk_nonneg k y))
    rw [e1]
    exact intervalIntegral.integral_add (hAii k) (hBii k)
  have hμsum : Summable
      (fun k : ℤ => ∫ y, ‖hk k y‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    (summable_cell_heatGrad_interval_integral ht x).congr (fun k => (heq k).symm)
  have key := integral_tsum_of_summable_integral_norm
    (μ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) (F := hk) hμint hμsum
  calc (∫ y in (0 : ℝ)..1, ∑' k : ℤ, hk k y)
      = ∫ y, (∑' k : ℤ, hk k y)
          ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
        intervalIntegral.integral_of_le h01
    _ = ∑' k : ℤ, ∫ y, hk k y
          ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := key.symm
    _ = ∑' k : ℤ,
          ((∫ y in (0 : ℝ)..1,
              |deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))|)
            + (∫ y in (0 : ℝ)..1,
              |deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))|)) := by
        refine tsum_congr (fun k => ?_)
        rw [← intervalIntegral.integral_of_le h01]
        exact intervalIntegral.integral_add (hAii k) (hBii k)
    _ = heatGradientLinftyLinftyConstant * t ^ (-(1 / 2) : ℝ) :=
        ShenWork.tsum_cell_heatGrad_abs_integral_eq ht x

end ShenWork.IntervalNeumannFullKernel

namespace ShenWork.IntervalConjugateDuhamelMap

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)

/-! ## The B-form operator and Picard map -/

/-- The conjugate-kernel chemotaxis operator
`B_N(t)Q(x) = -∫₀¹ ∂ᵧK_N(t,x,y)Q(y)dy`. -/
def intervalConjugateKernelOperator (t : ℝ) (Q : ℝ → ℝ) (x : ℝ) : ℝ :=
  -∫ y, deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y * Q y
      ∂ intervalMeasure 1

/-- For a jointly measurable time-dependent source, the B-kernel time integrand
is strongly measurable on `[0,t]`. -/
theorem intervalConjugateKernelOperator_s_dependent_aestronglyMeasurable_x
    {t : ℝ} (ht : 0 < t) {F : ℝ → ℝ → ℝ}
    (hF_ae : AEStronglyMeasurable (Function.uncurry F)
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)))
    (x₀ : ℝ) :
    AEStronglyMeasurable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s) (F s) x₀)
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) := by
  set Kd : ℝ × ℝ → ℝ :=
    fun w =>
      -(∑' k : ℤ, deriv (fun z : ℝ => heatKernel (t - w.1) z)
          (x₀ - w.2 + 2 * (k : ℝ)))
        + (∑' k : ℤ, deriv (fun z : ℝ => heatKernel (t - w.1) z)
          (x₀ + w.2 + 2 * (k : ℝ))) with hKd_def
  have hKd_meas := deriv_intervalNeumannFullKernel_snd_s_dependent_measurable t x₀
  set D : ℝ → ℝ := fun s => -∫ y, Kd (s, y) * F s y ∂(intervalMeasure 1) with hD_def
  have hD_aestrong : AEStronglyMeasurable D
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    have hint_ae : AEStronglyMeasurable (fun w : ℝ × ℝ => Kd w * F w.1 w.2)
        ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)) :=
      hKd_meas.aestronglyMeasurable.mul hF_ae
    exact (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t))
      (ν := intervalMeasure 1) (f := fun w : ℝ × ℝ => Kd w * F w.1 w.2)
      hint_ae).neg
  refine hD_aestrong.congr ?_
  have huIoc_eq : Set.uIoc (0 : ℝ) t = Set.Ioc (0 : ℝ) t := Set.uIoc_of_le ht.le
  have hae_lt_t : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 t)), s < t := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    have hae_ne_t : ∀ᵐ s ∂MeasureTheory.volume, s ≠ t := by
      have heq : {s : ℝ | ¬ s ≠ t} = {t} := by ext s; simp [eq_comm]
      rw [MeasureTheory.ae_iff, heq]
      exact Real.volume_singleton
    filter_upwards [hae_ne_t] with s hsne hs
    rw [huIoc_eq] at hs
    exact lt_of_le_of_ne hs.2 hsne
  filter_upwards [hae_lt_t] with s hst
  have htms_pos : 0 < t - s := sub_pos.mpr hst
  simp only [hD_def, intervalConjugateKernelOperator]
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with y
  have hKfun :
      deriv (fun y' : ℝ => intervalNeumannFullKernel (t - s) x₀ y') y =
        Kd (s, y) := by
    rw [hKd_def]
    exact (hasDerivAt_intervalNeumannFullKernel_snd htms_pos x₀ y).deriv
  rw [hKfun]

/-- The B-form Picard map.  Compared with `intervalGradientDuhamelMap`, only the
chemotaxis leg changes: `∂ₓS(t-s)Q` is replaced by `B_N(t-s)Q`. -/
def intervalConjugateDuhamelMap (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) (x : intervalDomainPoint) : ℝ :=
  intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
    + (-p.χ₀) * (∫ s in (0:ℝ)..t,
        intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x.1)
    + ∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1

/-- The corresponding fixed-point predicate. -/
def IntervalConjugateMildSolution (p : CM2Params) (T : ℝ)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    u t x = intervalConjugateDuhamelMap p u₀ u t x

/-! ## Unconditional Neumann symmetry of the B-kernel output -/

theorem intervalConjugateKernelOperator_even_zero (t : ℝ) (Q : ℝ → ℝ) (x : ℝ) :
    intervalConjugateKernelOperator t Q (-x) = intervalConjugateKernelOperator t Q x := by
  unfold intervalConjugateKernelOperator
  congr 1
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    have hfun : (fun y' : ℝ => intervalNeumannFullKernel t (-x) y')
        = fun y' : ℝ => intervalNeumannFullKernel t x y' := by
      funext y'
      exact intervalNeumannFullKernel_even_zero t x y'
    rw [hfun]

theorem intervalConjugateKernelOperator_even_one (t : ℝ) (Q : ℝ → ℝ) (x : ℝ) :
    intervalConjugateKernelOperator t Q (2 - x) = intervalConjugateKernelOperator t Q x := by
  unfold intervalConjugateKernelOperator
  congr 1
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    have hfun : (fun y' : ℝ => intervalNeumannFullKernel t (2 - x) y')
        = fun y' : ℝ => intervalNeumannFullKernel t x y' := by
      funext y'
      exact intervalNeumannFullKernel_even_one t x y'
    rw [hfun]

theorem intervalConjugateKernelOperator_deriv_at_zero_eq_zero
    (t : ℝ) (Q : ℝ → ℝ) :
    deriv (fun z : ℝ => intervalConjugateKernelOperator t Q z) 0 = 0 := by
  refine ShenWork.deriv_eq_zero_of_even_about (c := 0) (fun x => ?_)
  rw [show (2 * (0 : ℝ) - x) = -x by ring]
  exact intervalConjugateKernelOperator_even_zero t Q x

theorem intervalConjugateKernelOperator_deriv_at_one_eq_zero
    (t : ℝ) (Q : ℝ → ℝ) :
    deriv (fun z : ℝ => intervalConjugateKernelOperator t Q z) 1 = 0 := by
  refine ShenWork.deriv_eq_zero_of_even_about (c := 1) (fun x => ?_)
  rw [show (2 * (1 : ℝ) - x) = 2 - x by ring]
  exact intervalConjugateKernelOperator_even_one t Q x

/-- Kernel-level Neumann endpoint derivative, proved from the B-kernel evenness
alone.  This is independent of any solution-level flux identity. -/
theorem intervalConjugate_deriv_endpoints_zero (t : ℝ) (Q : ℝ → ℝ) :
    deriv (fun z : ℝ => intervalConjugateKernelOperator t Q z) 0 = 0 ∧
      deriv (fun z : ℝ => intervalConjugateKernelOperator t Q z) 1 = 0 :=
  ⟨intervalConjugateKernelOperator_deriv_at_zero_eq_zero t Q,
    intervalConjugateKernelOperator_deriv_at_one_eq_zero t Q⟩

/-- Formal one-sided interval normal derivative for the B-kernel output, assuming
only endpoint differentiability of the B-output.  The derivative value itself is
supplied by the unconditional evenness theorem above; no solution-level Neumann
or flux endpoint lemma is used. -/
theorem intervalConjugate_normalDeriv_zero (t : ℝ) (Q : ℝ → ℝ)
    (hdiff0 : DifferentiableAt ℝ (fun z : ℝ => intervalConjugateKernelOperator t Q z) 0)
    (hdiff1 : DifferentiableAt ℝ (fun z : ℝ => intervalConjugateKernelOperator t Q z) 1)
    {x : intervalDomainPoint} (hx : x ∈ ShenWork.IntervalDomain.intervalDomain.boundary) :
    ShenWork.IntervalDomain.intervalDomain.normalDeriv
      (fun x : intervalDomainPoint => intervalConjugateKernelOperator t Q x.1) x = 0 := by
  change intervalDomainNormalDeriv
      (fun x : intervalDomainPoint => intervalConjugateKernelOperator t Q x.1) x = 0
  let B : ℝ → ℝ := fun z => intervalConjugateKernelOperator t Q z
  have hB0 : HasDerivAt B 0 0 := by
    have h := hdiff0.hasDerivAt
    simpa [B, intervalConjugateKernelOperator_deriv_at_zero_eq_zero] using h
  have hB1 : HasDerivAt B 0 1 := by
    have h := hdiff1.hasDerivAt
    simpa [B, intervalConjugateKernelOperator_deriv_at_one_eq_zero] using h
  have hEq0 :
      intervalDomainLift (fun x : intervalDomainPoint => intervalConjugateKernelOperator t Q x.1)
        =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici 0)] B := by
    have hnear : ∀ᶠ y in nhdsWithin (0 : ℝ) (Set.Ici 0), y ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
        with y hy0 hy1 using ⟨hy0, hy1⟩
    filter_upwards [hnear] with y hy
    simp [intervalDomainLift, hy, B]
  have hEq1 :
      intervalDomainLift (fun x : intervalDomainPoint => intervalConjugateKernelOperator t Q x.1)
        =ᶠ[nhdsWithin (1 : ℝ) (Set.Iic 1)] B := by
    have hnear : ∀ᶠ y in nhdsWithin (1 : ℝ) (Set.Iic 1), y ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Ici_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
        with y hy1 hy0 using ⟨hy0, hy1⟩
    filter_upwards [hnear] with y hy
    simp [intervalDomainLift, hy, B]
  rcases hx with h0 | h1
  · unfold intervalDomainNormalDeriv
    rw [if_pos h0]
    have h0Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
    have hEqAt0 :
        intervalDomainLift
            (fun x : intervalDomainPoint => intervalConjugateKernelOperator t Q x.1) 0
          = B 0 := by
      simp [intervalDomainLift, h0Icc, B]
    exact (hB0.hasDerivWithinAt.congr_of_eventuallyEq hEq0 hEqAt0).derivWithin
      (uniqueDiffWithinAt_Ici (0 : ℝ))
  · unfold intervalDomainNormalDeriv
    rw [if_neg (by rw [h1]; norm_num), if_pos h1]
    have h1Icc : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
    have hEqAt1 :
        intervalDomainLift
            (fun x : intervalDomainPoint => intervalConjugateKernelOperator t Q x.1) 1
          = B 1 := by
      simp [intervalDomainLift, h1Icc, B]
    exact (hB1.hasDerivWithinAt.congr_of_eventuallyEq hEq1 hEqAt1).derivWithin
      (uniqueDiffWithinAt_Iic (1 : ℝ))

/-! ## `√T` bounds for the B-form Duhamel leg -/

theorem intervalConjugateKernelOperator_abs_le {t : ℝ} (ht : 0 < t)
    {Q : ℝ → ℝ} (hQ_int : Integrable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ : ∀ y, |Q y| ≤ CQ) (x : ℝ) :
    |intervalConjugateKernelOperator t Q x|
      ≤ heatGradientLinftyLinftyConstant * t ^ (-(1 / 2) : ℝ) * CQ := by
  have hCQ : 0 ≤ CQ := le_trans (abs_nonneg (Q 0)) (hQ 0)
  have hKint : Integrable
      (fun y : ℝ => deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y)
      (intervalMeasure 1) := by
    simp only [intervalMeasure, intervalSet]
    exact (continuousOn_deriv_intervalNeumannFullKernel_snd ht x).integrableOn_Icc
  have hbdd : ∀ᵐ y ∂(intervalMeasure 1), ‖Q y‖ ≤ CQ :=
    Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hQ y
  have hprod_int : Integrable
      (fun y : ℝ => deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y * Q y)
      (intervalMeasure 1) := hKint.mul_bdd hQ_int.aestronglyMeasurable hbdd
  have hint_le :
      (∫ y, |deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y| ∂(intervalMeasure 1))
        ≤ heatGradientLinftyLinftyConstant * t ^ (-(1 / 2) : ℝ) := by
    have hcv :
        (∫ y, |deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y|
            ∂(intervalMeasure 1))
          = ∫ y in (0 : ℝ)..1,
              |deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y| := by
      simp only [intervalMeasure, intervalSet]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [hcv]
    exact intervalNeumannFullKernel_deriv_snd_abs_interval_integral_le ht x
  unfold intervalConjugateKernelOperator
  rw [abs_neg]
  calc |∫ y, deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y * Q y
        ∂(intervalMeasure 1)|
      ≤ ∫ y, ‖deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y * Q y‖
          ∂(intervalMeasure 1) := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ y, |deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y| * CQ
          ∂(intervalMeasure 1) := by
        refine MeasureTheory.integral_mono hprod_int.norm (hKint.abs.mul_const CQ) (fun y => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hQ y) (abs_nonneg _)
    _ = (∫ y, |deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y|
          ∂(intervalMeasure 1)) * CQ := by
        rw [MeasureTheory.integral_mul_const]
    _ ≤ (heatGradientLinftyLinftyConstant * t ^ (-(1 / 2) : ℝ)) * CQ :=
        mul_le_mul_of_nonneg_right hint_le hCQ
    _ = heatGradientLinftyLinftyConstant * t ^ (-(1 / 2) : ℝ) * CQ := by ring

theorem conjugateDuhamel_sup_bound
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) {q : ℝ → ℝ → ℝ}
    (hq_int : ∀ s, Integrable (q s) (intervalMeasure 1))
    {Cq : ℝ} (hCq : 0 ≤ Cq) (hq_sup : ∀ s y, |q s y| ≤ Cq) (x : ℝ)
    (hB_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s) (q s) x) volume 0 t) :
    |∫ s in (0:ℝ)..t, intervalConjugateKernelOperator (t - s) (q s) x|
      ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * Cq := by
  set Cg := heatGradientLinftyLinftyConstant with hCgdef
  have hCgnn : 0 ≤ Cg := heatGradientLinftyLinftyConstant_nonneg
  have hptw : ∀ s, 0 ≤ s → s < t →
      |intervalConjugateKernelOperator (t - s) (q s) x|
        ≤ Cg * Cq * (t - s) ^ (-(1/2) : ℝ) := by
    intro s _hs0 hst
    have hts : 0 < t - s := sub_pos.mpr hst
    have h := intervalConjugateKernelOperator_abs_le hts (hq_int s) (hq_sup s) x
    calc |intervalConjugateKernelOperator (t - s) (q s) x|
        ≤ Cg * (t - s) ^ (-(1 / 2) : ℝ) * Cq := by simpa [Cg] using h
      _ = Cg * Cq * (t - s) ^ (-(1 / 2) : ℝ) := by ring
  have hdom_int : IntervalIntegrable
      (fun s : ℝ => Cg * Cq * (t - s) ^ (-(1/2) : ℝ)) volume 0 t :=
    ((ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul
      (Cg * Cq))
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  have hae : (fun s : ℝ => |intervalConjugateKernelOperator (t - s) (q s) x|)
      ≤ᵐ[volume.restrict (Set.Icc 0 t)]
      (fun s : ℝ => Cg * Cq * (t - s) ^ (-(1/2) : ℝ)) := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [hne] with s hs_ne hs_mem
    exact hptw s hs_mem.1 (lt_of_le_of_ne hs_mem.2 hs_ne)
  calc |∫ s in (0:ℝ)..t, intervalConjugateKernelOperator (t - s) (q s) x|
      ≤ ∫ s in (0:ℝ)..t, |intervalConjugateKernelOperator (t - s) (q s) x| :=
        intervalIntegral.abs_integral_le_integral_abs ht.le
    _ ≤ ∫ s in (0:ℝ)..t, Cg * Cq * (t - s) ^ (-(1/2) : ℝ) :=
        intervalIntegral.integral_mono_ae_restrict ht.le hB_int.abs hdom_int hae
    _ = Cg * Cq * (2 * Real.sqrt t) := by
        rw [intervalIntegral.integral_const_mul,
          ShenWork.IntervalGradDuhamelBound.integral_sub_rpow_neg_half ht.le]
    _ ≤ Cg * (2 * Real.sqrt T) * Cq := by
        have hsqrt : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt htT
        nlinarith [hCgnn, hCq, Real.sqrt_nonneg t, Real.sqrt_nonneg T, hsqrt,
          mul_nonneg hCgnn hCq]

/-- B-kernel Duhamel integrand of a bounded jointly-measurable source is
IntervalIntegrable in time. -/
theorem conjugateKernelDuhamel_intervalIntegrable_of_joint_measurable
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ → ℝ}
    (hf_meas : Measurable (Function.uncurry f))
    {C : ℝ} (_hC : 0 ≤ C) (hf_bdd : ∀ s y, |f s y| ≤ C) (x : ℝ) :
    IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (t - s) (f s) x) volume 0 t := by
  rw [intervalIntegrable_iff]
  have hf_slice_int : ∀ s, Integrable (f s) (intervalMeasure 1) := fun s =>
    ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      ((hf_meas.comp measurable_prodMk_left).aestronglyMeasurable)
      (hf_bdd s)
  have hmeas : AEStronglyMeasurable
      (fun s => intervalConjugateKernelOperator (t - s) (f s) x)
      (volume.restrict (Set.uIoc 0 t)) :=
    intervalConjugateKernelOperator_s_dependent_aestronglyMeasurable_x
      ht hf_meas.aestronglyMeasurable x
  set Cg := heatGradientLinftyLinftyConstant
  have hdom_int : IntegrableOn
      (fun s => Cg * (t - s) ^ (-(1/2) : ℝ) * C) (Set.uIoc 0 t) volume := by
    rw [show (fun s => Cg * (t - s) ^ (-(1/2) : ℝ) * C) =
        (fun s => (Cg * C) * (t - s) ^ (-(1/2) : ℝ)) from by ext; ring]
    rw [← intervalIntegrable_iff]
    exact (ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul
      (Cg * C)
  have hne : ∀ᵐ s ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  have hae : ∀ᵐ s ∂(volume.restrict (Set.uIoc 0 t)),
      ‖(fun s => intervalConjugateKernelOperator (t - s) (f s) x) s‖
        ≤ (fun s => Cg * (t - s) ^ (-(1/2) : ℝ) * C) s := by
    rw [Set.uIoc_of_le ht.le, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hne] with s hs_ne hs_mem
    rw [Real.norm_eq_abs]
    have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs_mem.2 hs_ne)
    have h :=
      intervalConjugateKernelOperator_abs_le hts (hf_slice_int s) (hf_bdd s) x
    simpa [Cg] using h
  exact Integrable.mono' hdom_int.integrable hmeas hae

theorem intervalConjugateKernelOperator_sub {τ x : ℝ} {f g : ℝ → ℝ}
    (hf : Integrable
      (fun y => deriv (fun y' : ℝ => intervalNeumannFullKernel τ x y') y * f y)
      (intervalMeasure 1))
    (hg : Integrable
      (fun y => deriv (fun y' : ℝ => intervalNeumannFullKernel τ x y') y * g y)
      (intervalMeasure 1)) :
    intervalConjugateKernelOperator τ (fun y => f y - g y) x
      = intervalConjugateKernelOperator τ f x - intervalConjugateKernelOperator τ g x := by
  unfold intervalConjugateKernelOperator
  have hpt : (fun y => deriv (fun y' : ℝ => intervalNeumannFullKernel τ x y') y * (f y - g y))
      = (fun y => deriv (fun y' : ℝ => intervalNeumannFullKernel τ x y') y * f y
          - deriv (fun y' : ℝ => intervalNeumannFullKernel τ x y') y * g y) := by
    funext y
    ring
  rw [hpt, MeasureTheory.integral_sub hf hg]
  ring

theorem conjugateDuhamel_diff_sup_bound
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) {q₁ q₂ : ℝ → ℝ → ℝ}
    {D : ℝ} (hD : 0 ≤ D) (hq_diff : ∀ s y, |q₁ s y - q₂ s y| ≤ D)
    (hq_int_diff : ∀ s, Integrable (fun y => q₁ s y - q₂ s y) (intervalMeasure 1))
    (x : ℝ)
    (hKq₁ : ∀ s, Integrable
      (fun y => deriv (fun y' : ℝ => intervalNeumannFullKernel (t - s) x y') y * q₁ s y)
      (intervalMeasure 1))
    (hKq₂ : ∀ s, Integrable
      (fun y => deriv (fun y' : ℝ => intervalNeumannFullKernel (t - s) x y') y * q₂ s y)
      (intervalMeasure 1))
    (hB_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s) (fun y => q₁ s y - q₂ s y) x)
      volume 0 t) :
    |∫ s in (0:ℝ)..t,
        (intervalConjugateKernelOperator (t - s) (q₁ s) x
          - intervalConjugateKernelOperator (t - s) (q₂ s) x)|
      ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * D := by
  have hcongr : (fun s : ℝ => intervalConjugateKernelOperator (t - s) (q₁ s) x
        - intervalConjugateKernelOperator (t - s) (q₂ s) x)
      = fun s : ℝ =>
          intervalConjugateKernelOperator (t - s) (fun y => q₁ s y - q₂ s y) x := by
    funext s
    rw [intervalConjugateKernelOperator_sub (hKq₁ s) (hKq₂ s)]
  rw [intervalIntegral.integral_congr
      (g := fun s : ℝ =>
        intervalConjugateKernelOperator (t - s) (fun y => q₁ s y - q₂ s y) x)
      (fun s _ => congrFun hcongr s)]
  exact conjugateDuhamel_sup_bound ht htT hq_int_diff hD hq_diff x hB_int

/-! ## Algebraic interior PDE core with the chemotaxis source retained -/

open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)

/-- General-χ version of the `hpde_u_core` algebra: the time-boundary Duhamel
mechanism contributes a chemotaxis spectral source `chem`, and the algebra keeps
the term `-χ₀·chemDiv` instead of dropping it. -/
theorem hpde_u_core_general_chi (p : CM2Params)
    {u : ℝ → intervalDomainPoint → ℝ} {t₀ : ℝ} {x : intervalDomainPoint}
    {b src chem : ℕ → ℝ}
    (hsum_src : Summable (fun n => src n * cosineMode n x.1))
    (hsum_chem : Summable (fun n => chem n * cosineMode n x.1))
    (hsum_lb : Summable
      (fun n => unitIntervalCosineEigenvalue n * b n * cosineMode n x.1))
    (htime : intervalDomain.timeDeriv u t₀ x
        = ∑' n, (src n - p.χ₀ * chem n - unitIntervalCosineEigenvalue n * b n)
            * cosineMode n x.1)
    (hlap : intervalDomain.laplacian (u t₀) x
        = ∑' n, b n * (-(((n : ℝ) * Real.pi) ^ 2)
            * Real.cos ((n : ℝ) * Real.pi * x.1)))
    (hreact : (∑' n, src n * cosineMode n x.1)
        = u t₀ x * (p.a - p.b * (u t₀ x) ^ p.α))
    (hchem : (∑' n, chem n * cosineMode n x.1)
        = intervalDomain.chemotaxisDiv p (u t₀)
            (mildChemicalConcentration p u t₀) x) :
    intervalDomain.timeDeriv u t₀ x
      = intervalDomain.laplacian (u t₀) x
        - p.χ₀ * intervalDomain.chemotaxisDiv p (u t₀)
            (mildChemicalConcentration p u t₀) x
        + u t₀ x * (p.a - p.b * (u t₀ x) ^ p.α) := by
  have hsum_chi : Summable (fun n => p.χ₀ * chem n * cosineMode n x.1) := by
    simpa [mul_assoc] using hsum_chem.mul_left p.χ₀
  have hsplit : (∑' n, (src n - p.χ₀ * chem n - unitIntervalCosineEigenvalue n * b n)
        * cosineMode n x.1)
      = (∑' n, src n * cosineMode n x.1)
        - (∑' n, p.χ₀ * chem n * cosineMode n x.1)
        - ∑' n, unitIntervalCosineEigenvalue n * b n * cosineMode n x.1 := by
    have hsum_src_chi : Summable
        (fun n => src n * cosineMode n x.1 - p.χ₀ * chem n * cosineMode n x.1) :=
      hsum_src.sub hsum_chi
    calc
      (∑' n, (src n - p.χ₀ * chem n - unitIntervalCosineEigenvalue n * b n)
          * cosineMode n x.1)
          = ∑' n, ((src n * cosineMode n x.1 - p.χ₀ * chem n * cosineMode n x.1)
              - unitIntervalCosineEigenvalue n * b n * cosineMode n x.1) := by
            exact tsum_congr (fun n => by ring)
      _ = (∑' n, (src n * cosineMode n x.1 - p.χ₀ * chem n * cosineMode n x.1))
            - ∑' n, unitIntervalCosineEigenvalue n * b n * cosineMode n x.1 :=
            hsum_src_chi.tsum_sub hsum_lb
      _ = (∑' n, src n * cosineMode n x.1)
            - (∑' n, p.χ₀ * chem n * cosineMode n x.1)
            - ∑' n, unitIntervalCosineEigenvalue n * b n * cosineMode n x.1 := by
            rw [hsum_src.tsum_sub hsum_chi]
  have hchi_tsum : (∑' n, p.χ₀ * chem n * cosineMode n x.1)
      = p.χ₀ * (∑' n, chem n * cosineMode n x.1) := by
    calc
      (∑' n, p.χ₀ * chem n * cosineMode n x.1)
          = ∑' n, p.χ₀ * (chem n * cosineMode n x.1) := by
            exact tsum_congr (fun n => by ring)
      _ = p.χ₀ * (∑' n, chem n * cosineMode n x.1) := by
            rw [tsum_mul_left]
  have hlap_eq : (∑' n, b n * (-(((n : ℝ) * Real.pi) ^ 2)
        * Real.cos ((n : ℝ) * Real.pi * x.1)))
      = -∑' n, unitIntervalCosineEigenvalue n * b n * cosineMode n x.1 := by
    rw [← tsum_neg]
    exact tsum_congr (fun n => by
      simp only [unitIntervalCosineEigenvalue, cosineMode]
      ring)
  rw [htime, hlap, hsplit, hreact, hlap_eq, hchi_tsum, hchem]
  ring

/-! ## Small-time contraction scalar for the B-form leg -/

theorem conjugateDuhamel_contraction_pointwise {χ₀ Cgrad C_Q C_L T d G V : ℝ}
    (hG : |G| ≤ Cgrad * (2 * Real.sqrt T) * (C_Q * d))
    (hV : |V| ≤ T * (C_L * d)) :
    |(-χ₀) * G + V| ≤ (2 * |χ₀| * Cgrad * C_Q * Real.sqrt T + C_L * T) * d :=
  ShenWork.IntervalChemFluxLipschitz.gradientDuhamel_contraction_pointwise hG hV

theorem exists_small_conjugate_contraction_time {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ T : ℝ, 0 < T ∧ A * Real.sqrt T + B * T < 1 :=
  ShenWork.IntervalChemFluxLipschitz.exists_small_contraction_time hA hB

end ShenWork.IntervalConjugateDuhamelMap
