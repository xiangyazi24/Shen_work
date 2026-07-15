import ShenWork.Paper1.WholeLineWeightedRegularityBUCTimeHolder
import ShenWork.Paper1.WholeLineWeightedRegularityFluxDerivative
import ShenWork.Paper1.WholeLineWeightedRegularityForcingHolder

open Filter MeasureTheory Real Set
open scoped RealInnerProductSpace

noncomputable section

namespace ShenWork.Paper1

/-!
# Concrete positive-window forcing trajectories

The conjugated moving heat semigroup has generator

`partial_xx + (c - 2 * eta) * partial_x + (eta^2 - c * eta)`.

Accordingly, its forcing is the lower-order source from the pure-drift
formulation minus `(eta^2 - c * eta) * W`.  The first theorem below records
this normalization explicitly.  The later declarations build the canonical
positive-window forcing and transfer its BUC time modulus to whole-line
weighted `L2` through a strict weight gap.
-/

/-- The physical forcing paired with the full conjugated moving-heat
generator. -/
def paper5WeightedGeneratorForcing
    (p : CMParams) (eta : ℝ)
    (u v : ℝ → ℝ → ℝ) (U V : ℝ → ℝ) (t x : ℝ) : ℝ :=
  Real.exp (eta * x) *
    (-p.χ *
        (deriv
            (fun y => (u t y) ^ p.m * deriv (v t) y) x -
          deriv (fun y => (U y) ^ p.m * deriv V y) x) +
      (reactionFun p.α (u t x) - reactionFun p.α (U x)))

/-- The four-term lower-order source, after removal of the zero-order growth
already contained in `weightedMovingHeatEta`, is exactly the physical
chemotaxis-plus-reaction forcing. -/
theorem paper5WeightedLowerOrderSource_sub_growth_eq_generatorForcing
    (p : CMParams) {T eta c t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu : 0 ≤ coMovingPath c u t x) (hU : 0 ≤ U x)
    (hu1 : ContDiff ℝ 1 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU1 : ContDiff ℝ 1 U) (hV2 : ContDiff ℝ 2 V) :
    paper5WeightedLowerOrderSource p eta c
        (coMovingPath c u) (coMovingPath c v) U
        (paper5WeightedPopulation eta (coMovingPath c u) U t)
        (paper5WeightedPopulationX eta (coMovingPath c u) U t)
        (paper5WeightedSignal eta (coMovingPath c v) V t)
        (paper5WeightedSignalX eta (coMovingPath c v) V t) t x -
      (eta ^ 2 - c * eta) *
          paper5WeightedPopulation eta (coMovingPath c u) U t x =
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V t x := by
  have hflux := paper5WeightedFluxDerivativeExpanded_eq
    p (eta := eta) (t := t) (x := x)
    hsol ht0 htT hTW hu hU hu1 hv2 hU1 hV2
  have hpow_u : coMovingPath c u t x *
      (coMovingPath c u t x) ^ p.α =
      (coMovingPath c u t x) ^ (1 + p.α) := by
    rw [Real.rpow_add_of_nonneg hu zero_le_one
      (zero_le_one.trans p.hα), Real.rpow_one]
  have hpow_U : U x * (U x) ^ p.α = (U x) ^ (1 + p.α) := by
    rw [Real.rpow_add_of_nonneg hU zero_le_one
      (zero_le_one.trans p.hα), Real.rpow_one]
  have hreact :
      reactionFun p.α (coMovingPath c u t x) -
          reactionFun p.α (U x) =
        (1 - paper5A (1 + p.α) (coMovingPath c u) U t x) *
          (coMovingPath c u t x - U x) := by
    have hA := paper5A_mul_sub
      (1 + p.α) (coMovingPath c u) U t x
    unfold reactionFun
    rw [show coMovingPath c u t x *
          (1 - coMovingPath c u t x ^ p.α) =
        coMovingPath c u t x -
          coMovingPath c u t x * coMovingPath c u t x ^ p.α by ring,
      show U x * (1 - U x ^ p.α) =
        U x - U x * U x ^ p.α by ring,
      hpow_u, hpow_U]
    ring_nf at hA ⊢
    linarith
  unfold paper5WeightedLowerOrderSource paper5CorrectedJ2Coefficient
    paper5WeightedGeneratorForcing paper5WeightedPopulation
  rw [show Real.exp (eta * x) *
        (-p.χ *
            (deriv
                (fun y => coMovingPath c u t y ^ p.m *
                  deriv (coMovingPath c v t) y) x -
              deriv (fun y => U y ^ p.m * deriv V y) x) +
          (reactionFun p.α (coMovingPath c u t x) -
            reactionFun p.α (U x))) =
      -p.χ * (Real.exp (eta * x) *
        (deriv
            (fun y => coMovingPath c u t y ^ p.m *
              deriv (coMovingPath c v t) y) x -
          deriv (fun y => U y ^ p.m * deriv V y) x)) +
        Real.exp (eta * x) *
          (reactionFun p.α (coMovingPath c u t x) -
            reactionFun p.α (U x)) by ring,
      hflux]
  unfold paper5WeightedFluxDerivativeExpanded
    paper5WeightedPopulationX paper5WeightedPopulation
    paper5WeightedSignalX paper5WeightedSignal
  rw [hreact]
  ring

/-- Moving the observation point at constant speed preserves the canonical
positive-window square-root time modulus. -/
theorem exists_wholeLineCauchyBUCMildFixedPoint_coMoving_time_sqrt_holder_positive_window
    (p : CMParams) {M T a b theta zeta : ℝ} (c : ℝ)
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (hrel : zeta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x : ℝ,
        |t - s| ≤ 1 →
        |(wholeLineBUCTrajectoryExtend hT
              (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) t).1
              (x + c * t) -
            (wholeLineBUCTrajectoryExtend hT
              (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1
              (x + c * s)| ≤
          H * |t - s| ^ (1 / 2 : ℝ) := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  rcases
      exists_wholeLineCauchyBUCMildFixedPoint_time_pointwise_sqrt_holder_positive_window
        p hM hT ha hab hbT u₀ hsmall htheta0 htheta1
          hzeta0 hzeta1 hrel hstrip with
    ⟨Ht, hHt, htime⟩
  have hstripWindow : ∀ s ∈ Set.Icc a b, ∀ x,
      (wholeLineBUCTrajectoryExtend hT U s).1 x ∈ Set.Icc (0 : ℝ) M := by
    intro s hs x
    let zs : Set.Icc (0 : ℝ) T :=
      ⟨s, (ha.trans_le hs.1).le, hs.2.trans hbT⟩
    have hext : wholeLineBUCTrajectoryExtend hT U s = U zs :=
      wholeLineBUCTrajectoryExtend_eq hT U zs.2
    rw [hext]
    exact hstrip zs x
  rcases wholeLineCauchyBUCMildFixedPoint_spatial_deriv_bounded_positive_window
      p hM hT ha hab hbT u₀ hsmall htheta0 htheta1
        hzeta0 hzeta1 hrel hstripWindow with
    ⟨Bx, hBx, hderiv⟩
  let H : ℝ := Ht + Bx * |c|
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨H, hH, ?_⟩
  intro s hs t ht x hdist
  let d : ℝ := |t - s|
  have hd0 : 0 ≤ d := abs_nonneg _
  have hd1 : d ≤ 1 := by simpa only [d] using hdist
  have hdsqrt : d ≤ d ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    have hs0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
    have hs1 : Real.sqrt d ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hd1
    nlinarith [Real.sq_sqrt hd0]
  have htemporal :
      |(wholeLineBUCTrajectoryExtend hT U t).1 (x + c * t) -
          (wholeLineBUCTrajectoryExtend hT U s).1 (x + c * t)| ≤
        Ht * d ^ (1 / 2 : ℝ) := by
    simpa only [U, d] using htime s hs t ht (x + c * t) hdist
  have hsdiff : Differentiable ℝ
      (wholeLineBUCTrajectoryExtend hT U s).1 := by
    intro y
    let zs : Set.Icc (0 : ℝ) T :=
      ⟨s, (ha.trans_le hs.1).le, hs.2.trans hbT⟩
    have hext : wholeLineBUCTrajectoryExtend hT U s = U zs :=
      wholeLineBUCTrajectoryExtend_eq hT U zs.2
    have hy :=
      (wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
        p hM hT u₀ hsmall zs (ha.trans_le hs.1) y).differentiableAt
    simpa [U, hext] using hy
  have hspatial :
      |(wholeLineBUCTrajectoryExtend hT U s).1 (x + c * t) -
          (wholeLineBUCTrajectoryExtend hT U s).1 (x + c * s)| ≤
        Bx * |c| * d := by
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.univ)
      (f := (wholeLineBUCTrajectoryExtend hT U s).1)
      (C := Bx)
      (fun y _ => hsdiff y)
      (fun y _ => by
        rw [Real.norm_eq_abs]
        exact hderiv s hs y)
      convex_univ (Set.mem_univ (x + c * t))
      (Set.mem_univ (x + c * s))
    calc
      |(wholeLineBUCTrajectoryExtend hT U s).1 (x + c * t) -
          (wholeLineBUCTrajectoryExtend hT U s).1 (x + c * s)| ≤
          Bx * |(x + c * t) - (x + c * s)| := by
            simpa [Real.norm_eq_abs, abs_sub_comm] using hmv
      _ = Bx * |c| * d := by
        rw [show (x + c * t) - (x + c * s) = c * (t - s) by ring,
          abs_mul]
        dsimp only [d]
        ring
  calc
    |(wholeLineBUCTrajectoryExtend hT U t).1 (x + c * t) -
        (wholeLineBUCTrajectoryExtend hT U s).1 (x + c * s)| ≤
      |(wholeLineBUCTrajectoryExtend hT U t).1 (x + c * t) -
        (wholeLineBUCTrajectoryExtend hT U s).1 (x + c * t)| +
      |(wholeLineBUCTrajectoryExtend hT U s).1 (x + c * t) -
        (wholeLineBUCTrajectoryExtend hT U s).1 (x + c * s)| := by
          exact abs_sub_le _ _ _
    _ ≤ Ht * d ^ (1 / 2 : ℝ) + Bx * |c| * d :=
      add_le_add htemporal hspatial
    _ ≤ Ht * d ^ (1 / 2 : ℝ) +
        Bx * |c| * d ^ (1 / 2 : ℝ) := by gcongr
    _ = H * |t - s| ^ (1 / 2 : ℝ) := by
      dsimp [H, d]
      ring

section AxiomAudit

#print axioms paper5WeightedLowerOrderSource_sub_growth_eq_generatorForcing
#print axioms
  exists_wholeLineCauchyBUCMildFixedPoint_coMoving_time_sqrt_holder_positive_window

end AxiomAudit

end ShenWork.Paper1
