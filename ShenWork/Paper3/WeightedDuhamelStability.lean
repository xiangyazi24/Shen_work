/- Exponential decay from a singular quadratic Duhamel norm inequality. -/
import ShenWork.Paper3.IntervalDomainDuhamelConvolution
import ShenWork.Paper3.WeightedTailBootstrap

namespace ShenWork.Paper3

open MeasureTheory Set Real

noncomputable section

/-- Scalar norm data obtained after taking the strong phase norm in the full
diagonal Duhamel formula. -/
structure WeightedQuadraticDuhamelData (size : ℝ → ℝ) where
  theta : ℝ
  smoothingRate : ℝ
  delta : ℝ
  rate : ℝ
  linearConst : ℝ
  nonlinearConst : ℝ
  datum : ℝ
  radius : ℝ
  theta_pos : 0 < theta
  theta_lt_one : theta < 1
  rate_pos : 0 < rate
  rate_lt_smoothingRate : rate < smoothingRate
  rate_le_delta : rate ≤ delta
  linearConst_nonneg : 0 ≤ linearConst
  nonlinearConst_nonneg : 0 ≤ nonlinearConst
  datum_nonneg : 0 ≤ datum
  radius_pos : 0 < radius
  size_nonneg : ∀ t, 0 ≤ t → 0 ≤ size t
  size_continuous : ContinuousOn size (Set.Ici (0 : ℝ))
  source_integrable : ∀ t, 0 ≤ t →
    IntervalIntegrable
      (fun s : ℝ =>
        (t - s) ^ (-theta) * Real.exp (-smoothingRate * (t - s)) *
          size s ^ 2) volume 0 t
  duhamel_bound : ∀ t, 0 ≤ t →
    size t ≤
      linearConst * Real.exp (-delta * t) * datum +
        nonlinearConst * (∫ s in (0 : ℝ)..t,
          (t - s) ^ (-theta) * Real.exp (-smoothingRate * (t - s)) *
            size s ^ 2)
  datum_small : linearConst * datum ≤ radius / 2
  quadratic_small :
    nonlinearConst * radius ^ 2 *
      reservedSingularKernelMass theta (smoothingRate - rate) ≤ radius / 4

/-- The singular-kernel Duhamel inequality closes globally in the exponential
weight. -/
theorem WeightedQuadraticDuhamelData.exponential_bound
    {size : ℝ → ℝ} (H : WeightedQuadraticDuhamelData size) :
    ∀ t, 0 ≤ t → size t ≤ H.radius * Real.exp (-H.rate * t) := by
  let z : ℝ → ℝ := fun t => Real.exp (H.rate * t) * size t
  let B : ℝ := H.radius / 2 + H.radius / 4
  have hB : B < H.radius := by
    dsimp [B]
    linarith [H.radius_pos]
  have hzcont : ContinuousOn z (Set.Ici (0 : ℝ)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      H.size_continuous
  have hz0 : z 0 < H.radius := by
    have hduh0 := H.duhamel_bound 0 le_rfl
    simp only [mul_zero, Real.exp_zero,
      intervalIntegral.integral_same, mul_zero, add_zero] at hduh0
    have hsmall0 : size 0 < H.radius :=
      lt_of_le_of_lt (hduh0.trans (by simpa using H.datum_small)) (by
        linarith [H.radius_pos])
    simpa [z] using hsmall0
  have hstep : ∀ t, 0 ≤ t →
      (∀ s ∈ Set.Icc (0 : ℝ) t, z s ≤ H.radius) → z t ≤ B := by
    intro t ht hpast
    let source : ℝ → ℝ := fun s =>
      (t - s) ^ (-H.theta) *
        Real.exp (-H.smoothingRate * (t - s)) *
        size s ^ 2
    let major : ℝ → ℝ := fun s =>
      H.radius ^ 2 *
        ((t - s) ^ (-H.theta) *
          Real.exp (-H.smoothingRate * (t - s)) *
          Real.exp (-2 * H.rate * s))
    have hsourceInt : IntervalIntegrable source volume 0 t := by
      simpa [source] using H.source_integrable t ht
    have hbaseInt :=
      weighted_singular_quadratic_convolution_intervalIntegrable
        H.theta_pos H.theta_lt_one H.rate_pos
          H.rate_lt_smoothingRate ht
    have hmajorInt : IntervalIntegrable major volume 0 t := by
      simpa [major, mul_assoc] using hbaseInt.const_mul (H.radius ^ 2)
    have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) t, source s ≤ major s := by
      intro s hs
      have hs0 : 0 ≤ s := hs.1
      have hweighted : Real.exp (H.rate * s) * size s ≤ H.radius :=
        hpast s hs
      have hsize : size s ≤ H.radius * Real.exp (-H.rate * s) := by
        have hexppos : 0 < Real.exp (H.rate * s) := Real.exp_pos _
        apply (mul_le_mul_iff_of_pos_left hexppos).mp
        rw [show Real.exp (H.rate * s) *
            (H.radius * Real.exp (-H.rate * s)) = H.radius by
          calc
            Real.exp (H.rate * s) *
                (H.radius * Real.exp (-H.rate * s)) =
              H.radius * (Real.exp (H.rate * s) *
                Real.exp (-H.rate * s)) := by ring
            _ = H.radius * Real.exp 0 := by
              rw [← Real.exp_add]
              congr 2
              ring
            _ = H.radius := by simp]
        exact hweighted
      have hsize0 := H.size_nonneg s hs0
      have hsquare : size s ^ 2 ≤
          H.radius ^ 2 * Real.exp (-2 * H.rate * s) := by
        have hsq := mul_self_le_mul_self hsize0 hsize
        calc
          size s ^ 2 ≤ (H.radius * Real.exp (-H.rate * s)) ^ 2 := by
            simpa [pow_two] using hsq
          _ = H.radius ^ 2 * Real.exp (-2 * H.rate * s) := by
            rw [mul_pow, ← Real.exp_nat_mul]
            congr 2
            ring
      have hkernel0 : 0 ≤
          (t - s) ^ (-H.theta) *
            Real.exp (-H.smoothingRate * (t - s)) :=
        mul_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)
          (Real.exp_nonneg _)
      dsimp [source, major]
      calc
        (t - s) ^ (-H.theta) *
            Real.exp (-H.smoothingRate * (t - s)) *
            size s ^ 2 ≤
          ((t - s) ^ (-H.theta) *
              Real.exp (-H.smoothingRate * (t - s))) *
            (H.radius ^ 2 * Real.exp (-2 * H.rate * s)) :=
              mul_le_mul_of_nonneg_left hsquare hkernel0
        _ = H.radius ^ 2 *
            ((t - s) ^ (-H.theta) *
                Real.exp (-H.smoothingRate * (t - s)) *
              Real.exp (-2 * H.rate * s)) := by ring
    have hintegral : (∫ s in (0 : ℝ)..t, source s) ≤
        ∫ s in (0 : ℝ)..t, major s :=
      intervalIntegral.integral_mono_on ht hsourceInt hmajorInt hpoint
    have hconv := weighted_singular_quadratic_convolution_le
      H.theta_pos H.theta_lt_one H.rate_pos
        H.rate_lt_smoothingRate ht
    have hmajorBound : (∫ s in (0 : ℝ)..t, major s) ≤
        H.radius ^ 2 * (Real.exp (-H.rate * t) *
          reservedSingularKernelMass H.theta
            (H.smoothingRate - H.rate)) := by
      dsimp [major]
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left hconv (sq_nonneg H.radius)
    have hsourceBound : (∫ s in (0 : ℝ)..t, source s) ≤
        H.radius ^ 2 * (Real.exp (-H.rate * t) *
          reservedSingularKernelMass H.theta
            (H.smoothingRate - H.rate)) :=
      hintegral.trans hmajorBound
    have hlinearExp :
        Real.exp (H.rate * t) * Real.exp (-H.delta * t) ≤ 1 := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hcoef : H.rate - H.delta ≤ 0 := sub_nonpos.mpr H.rate_le_delta
      have hmul : (H.rate - H.delta) * t ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hcoef ht
      nlinarith
    have hduh := H.duhamel_bound t ht
    have hexp0 := Real.exp_nonneg (H.rate * t)
    have hweightedDuh := mul_le_mul_of_nonneg_left hduh hexp0
    dsimp [z, B]
    calc
      Real.exp (H.rate * t) * size t ≤
          Real.exp (H.rate * t) *
            (H.linearConst * Real.exp (-H.delta * t) * H.datum +
              H.nonlinearConst * (∫ s in (0 : ℝ)..t, source s)) := by
            simpa [source] using hweightedDuh
      _ ≤ H.linearConst * H.datum +
          H.nonlinearConst * H.radius ^ 2 *
            reservedSingularKernelMass H.theta
              (H.smoothingRate - H.rate) := by
        have hlin0 : 0 ≤ H.linearConst * H.datum :=
          mul_nonneg H.linearConst_nonneg H.datum_nonneg
        have hlinTerm :
            (Real.exp (H.rate * t) * Real.exp (-H.delta * t)) *
                (H.linearConst * H.datum) ≤
              1 * (H.linearConst * H.datum) :=
          mul_le_mul_of_nonneg_right hlinearExp hlin0
        have hsourceMul := mul_le_mul_of_nonneg_left
          hsourceBound H.nonlinearConst_nonneg
        have hsourceWeighted := mul_le_mul_of_nonneg_left
          hsourceMul (Real.exp_nonneg (H.rate * t))
        have hcancel : Real.exp (H.rate * t) *
            Real.exp (-H.rate * t) = 1 := by
          rw [← Real.exp_add]
          simp
        have hsourceTerm :
            Real.exp (H.rate * t) *
                (H.nonlinearConst *
                  (∫ s in (0 : ℝ)..t, source s)) ≤
              H.nonlinearConst * H.radius ^ 2 *
                reservedSingularKernelMass H.theta
                  (H.smoothingRate - H.rate) := by
          calc
            _ ≤ Real.exp (H.rate * t) *
                (H.nonlinearConst * (H.radius ^ 2 *
                  (Real.exp (-H.rate * t) *
                    reservedSingularKernelMass H.theta
                      (H.smoothingRate - H.rate)))) := hsourceWeighted
            _ = (Real.exp (H.rate * t) * Real.exp (-H.rate * t)) *
                (H.nonlinearConst * H.radius ^ 2 *
                  reservedSingularKernelMass H.theta
                    (H.smoothingRate - H.rate)) := by ring
            _ = H.nonlinearConst * H.radius ^ 2 *
                reservedSingularKernelMass H.theta
                  (H.smoothingRate - H.rate) := by rw [hcancel, one_mul]
        calc
          Real.exp (H.rate * t) *
              (H.linearConst * Real.exp (-H.delta * t) * H.datum +
                H.nonlinearConst * (∫ s in (0 : ℝ)..t, source s)) =
            (Real.exp (H.rate * t) * Real.exp (-H.delta * t)) *
                (H.linearConst * H.datum) +
              Real.exp (H.rate * t) *
                (H.nonlinearConst * (∫ s in (0 : ℝ)..t, source s)) := by ring
          _ ≤
              1 * (H.linearConst * H.datum) +
                H.nonlinearConst * H.radius ^ 2 *
                  reservedSingularKernelMass H.theta
                    (H.smoothingRate - H.rate) :=
            add_le_add hlinTerm hsourceTerm
          _ = H.linearConst * H.datum +
              H.nonlinearConst * H.radius ^ 2 *
              reservedSingularKernelMass H.theta
                (H.smoothingRate - H.rate) := by ring
      _ ≤ H.radius / 2 + H.radius / 4 :=
        add_le_add H.datum_small H.quadratic_small
  have hzbound := weightedTail_bound_of_bootstrap
    H.radius_pos hB hzcont hz0 hstep
  intro t ht
  have hz := hzbound t ht
  dsimp [z] at hz
  have hexppos : 0 < Real.exp (H.rate * t) := Real.exp_pos _
  apply (mul_le_mul_iff_of_pos_left hexppos).mp
  rw [show Real.exp (H.rate * t) *
      (H.radius * Real.exp (-H.rate * t)) = H.radius by
    calc
      Real.exp (H.rate * t) *
          (H.radius * Real.exp (-H.rate * t)) =
        H.radius * (Real.exp (H.rate * t) *
          Real.exp (-H.rate * t)) := by ring
      _ = H.radius * Real.exp 0 := by
        rw [← Real.exp_add]
        congr 2
        ring
      _ = H.radius := by simp]
  exact hz

#print axioms WeightedQuadraticDuhamelData.exponential_bound

end

end ShenWork.Paper3
