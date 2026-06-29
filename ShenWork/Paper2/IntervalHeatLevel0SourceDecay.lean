import ShenWork.Paper2.IntervalWeakH2SmoothRepresentative
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.PDE.IntervalSourceDecayQuantitative

/-!
# Decay certificates for the heat level-0 resolver source

This file starts the direct-route source-decay layer used by
`IntervalHeatResolverJointC2`: for the heat base iterate, the zeroth source slice
`ν * (S(t)u₀)^γ` has a depth-two weak Neumann certificate at every positive time.
Consequently its cosine coefficients have the eigenvalue-weighted `ℓ¹` decay
needed by the gradient resolver series.
-/

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice)
open ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData (heatDu heatD2u)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1 srcSlice2)

noncomputable section

namespace ShenWork.Paper2.HeatLevel0SourceDecay

open ShenWork.PDE.IntervalMildSourceDecayHelper
open ShenWork.Paper2.SourceRepresentative
open ShenWork.Paper2.WeakH2SmoothRepresentative
open ShenWork.Paper2.HeatSemigroupHighRegularity

private theorem norm_iteratedFDeriv_deriv_deriv_eq
    (f : ℝ → ℝ) (i : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ i (fun y : ℝ => deriv (deriv f) y) x‖ =
      ‖iteratedFDeriv ℝ (i + 2) f x‖ := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simp [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

private theorem norm_iteratedFDeriv_two_mul_bound
    {f g : ℝ → ℝ} (hf : ContDiff ℝ (2 : ℕ∞) f)
    (hg : ContDiff ℝ (2 : ℕ∞) g) {Cf Cg : ℝ}
    (hCf : 0 ≤ Cf) {x : ℝ}
    (hfB : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i f x‖ ≤ Cf)
    (hgB : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i g x‖ ≤ Cg) :
    ‖iteratedFDeriv ℝ 2 (fun y : ℝ => f y * g y) x‖ ≤
      4 * Cf * Cg := by
  have hprod := norm_iteratedFDeriv_mul_le hf hg x
    (by norm_num : (2 : ℕ) ≤ ((2 : ℕ∞) : WithTop ℕ∞))
  refine hprod.trans ?_
  calc
    (∑ i ∈ Finset.range (2 + 1), (Nat.choose 2 i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ *
        ‖iteratedFDeriv ℝ (2 - i) g x‖)
        ≤ ∑ i ∈ Finset.range (2 + 1), (Nat.choose 2 i : ℝ) * Cf * Cg := by
          apply Finset.sum_le_sum
          intro i hi
          have hi2 : i ≤ 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hsub2 : 2 - i ≤ 2 := Nat.sub_le 2 i
          have hchoose : 0 ≤ (Nat.choose 2 i : ℝ) := Nat.cast_nonneg _
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hfB i hi2) hchoose)
            (hgB (2 - i) hsub2)
            (norm_nonneg _)
            (mul_nonneg hchoose hCf)
    _ = 4 * Cf * Cg := by
      norm_num [Finset.sum_range_succ]
      ring

private theorem norm_iteratedFDeriv_mul_bound_of_le_two
    {f g : ℝ → ℝ} (hf : ContDiff ℝ (2 : ℕ∞) f)
    (hg : ContDiff ℝ (2 : ℕ∞) g) {Cf Cg : ℝ}
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) {x : ℝ} (n : ℕ) (hn : n ≤ 2)
    (hfB : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i f x‖ ≤ Cf)
    (hgB : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i g x‖ ≤ Cg) :
    ‖iteratedFDeriv ℝ n (fun y : ℝ => f y * g y) x‖ ≤
      4 * Cf * Cg := by
  have hnTop : (n : ℕ) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast hn
  have hprod := norm_iteratedFDeriv_mul_le hf hg x hnTop
  refine hprod.trans ?_
  have hsum_le :
      (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ) *
          ‖iteratedFDeriv ℝ i f x‖ *
          ‖iteratedFDeriv ℝ (n - i) g x‖)
        ≤ ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ) * Cf * Cg := by
    apply Finset.sum_le_sum
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hi2 : i ≤ 2 := le_trans hin hn
    have hsub2 : n - i ≤ 2 := le_trans (Nat.sub_le n i) hn
    have hchoose : 0 ≤ (Nat.choose n i : ℝ) := Nat.cast_nonneg _
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hfB i hi2) hchoose)
      (hgB (n - i) hsub2)
      (norm_nonneg _)
      (mul_nonneg hchoose hCf)
  exact hsum_le.trans (by
    interval_cases n
    · norm_num [Finset.sum_range_succ]
      nlinarith [hCf, hCg]
    · norm_num [Finset.sum_range_succ]
      nlinarith [hCf, hCg]
    · norm_num [Finset.sum_range_succ]
      ring_nf
      exact le_rfl)

private theorem norm_iteratedFDeriv_two_const_mul_bound
    {f : ℝ → ℝ} (hf : ContDiff ℝ (2 : ℕ∞) f) {A C : ℝ} {x : ℝ}
    (hB : ‖iteratedFDeriv ℝ 2 f x‖ ≤ C) :
    ‖iteratedFDeriv ℝ 2 (fun y : ℝ => A * f y) x‖ ≤ |A| * C := by
  have hB_abs : |iteratedDeriv 2 f x| ≤ C := by
    simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using hB
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  rw [iteratedDeriv_const_mul A hf.contDiffAt]
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left hB_abs (abs_nonneg _)

/-- At positive time, `heatDu` is the classical second spatial derivative of
the heat cosine representative. -/
theorem heatDu_eq_heatValue_secondDeriv
    {u₀ : intervalDomainPoint → ℝ} {M₀ t x : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (ht : 0 < t) :
    heatDu u₀ t x =
      deriv (fun y : ℝ =>
        deriv (fun z : ℝ =>
          unitIntervalCosineHeatValue t (cosineCoeffs (intervalDomainLift u₀)) z) y) x := by
  have hsecond : heatDu u₀ t x =
      ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue
        t (cosineCoeffs (intervalDomainLift u₀)) x := by
    simp only [heatDu, if_pos ht]
    simp only [ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue,
      ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue]
    congr 1; ext n
    simp only [ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight,
      ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondPointWeight,
      unitIntervalCosineHeatPointWeight, unitIntervalCosineMode,
      unitIntervalCosineEigenvalue]
    ring
  exact hsecond.trans
    (ShenWork.IntervalDuhamelClosedC2.unitIntervalCosineHeatValue_spatial_second_deriv
      ht hu₀_bound).symm

/-- The `λ² e^{-tλ}` heat series defining `heatD2u` is spatially `C²` at
positive time. -/
theorem heatD2u_contDiff_two
    {u₀ : intervalDomainPoint → ℝ} {M₀ t : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (ht : 0 < t) :
    ContDiff ℝ 2 (fun x : ℝ => heatD2u u₀ t x) := by
  have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
  have hsumm : Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        |unitIntervalCosineEigenvalue n ^ 2 *
          (Real.exp (-t * unitIntervalCosineEigenvalue n) *
            cosineCoeffs (intervalDomainLift u₀) n)|) := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
        (abs_nonneg _)) (fun n => ?_)
      ((ShenWork.Paper2.HeatSemigroupJointRegularity.eigenvalue_pow_mul_exp_summable
        3 ht).mul_left M₀)
    have hlam_nn : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hlam_nn 2),
      abs_of_nonneg (Real.exp_nonneg _)]
    calc unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n ^ 2 *
            (Real.exp (-t * unitIntervalCosineEigenvalue n) *
              |cosineCoeffs (intervalDomainLift u₀) n|))
        ≤ unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n ^ 2 *
            (Real.exp (-t * unitIntervalCosineEigenvalue n) * M₀)) := by
            gcongr
            exact hu₀_bound n
      _ = M₀ * (unitIntervalCosineEigenvalue n ^ 3 *
            Real.exp (-t * unitIntervalCosineEigenvalue n)) := by ring
  have hseries :
      ContDiff ℝ 2 (fun x : ℝ => ∑' n : ℕ,
        (unitIntervalCosineEigenvalue n ^ 2 *
          (Real.exp (-t * unitIntervalCosineEigenvalue n) *
            cosineCoeffs (intervalDomainLift u₀) n)) * cosineMode n x) :=
    ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two hsumm
  simpa [heatD2u, if_pos ht, mul_assoc] using hseries

/-- The heat semigroup applied to bounded initial data is C⁶ in space for
positive time.  This is the C⁶ companion of `heatSemigroup_contDiff_four`, using
the existing eigenvalue-cube cosine-series engine. -/
theorem heatSemigroup_contDiff_six
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ 6 (fun x => ∑' k : ℕ,
      (Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x) := by
  have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
  have hsumm : Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            |Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n|))) := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
        (mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
          (mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
            (abs_nonneg _)))) (fun n => ?_)
      ((ShenWork.Paper2.HeatSemigroupJointRegularity.eigenvalue_pow_mul_exp_summable
        3 ht).mul_right M₀)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              (Real.exp (-t * unitIntervalCosineEigenvalue n) *
                |cosineCoeffs (intervalDomainLift u₀) n|)))
        ≤ unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              (Real.exp (-t * unitIntervalCosineEigenvalue n) * M₀))) := by
            have hlam_nn : 0 ≤ unitIntervalCosineEigenvalue n := by
              unfold unitIntervalCosineEigenvalue
              positivity
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (hu₀_bound n) (Real.exp_nonneg _))
                  hlam_nn)
                hlam_nn)
              hlam_nn
      _ = unitIntervalCosineEigenvalue n ^ 3 *
            Real.exp (-t * unitIntervalCosineEigenvalue n) * M₀ := by ring
  exact
    ShenWork.Paper2.SpatialC6Certificate.cosineCoeffSeries_contDiff_six_of_eigenvalue_cube_summable
      hsumm

private theorem heatSemigroup_spatialTerm_iteratedFDeriv_bound
    {u₀ : intervalDomainPoint → ℝ} {M₀ t : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (r n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ r
      (fun y : ℝ =>
        (Real.exp (-t * unitIntervalCosineEigenvalue n) *
          cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n y) x‖ ≤
      |(n : ℝ) * Real.pi| ^ r *
        Real.exp (-t * unitIntervalCosineEigenvalue n) * M₀ := by
  have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
  set c : ℝ := Real.exp (-t * unitIntervalCosineEigenvalue n) *
    cosineCoeffs (intervalDomainLift u₀) n with hc
  have hterm :
      (fun y : ℝ =>
        (Real.exp (-t * unitIntervalCosineEigenvalue n) *
          cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n y) =
      fun y : ℝ => c * cosineMode n y := by
    funext y
    rw [hc]
  rw [hterm, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hcd : ContDiffAt ℝ (r : WithTop ℕ∞) (cosineMode n) x := by
    unfold cosineMode
    fun_prop
  rw [iteratedDeriv_const_mul c hcd, Real.norm_eq_abs, abs_mul]
  have hmode : |iteratedDeriv r (cosineMode n) x| ≤
      |(n : ℝ) * Real.pi| ^ r := by
    simpa [cosineMode, unitIntervalCosineMode,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      using
        ShenWork.Paper2.CD6CosineModeBounds.unitIntervalCosineMode_iteratedFDeriv_bound
          r n x
  have hcoeff : |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀ := hu₀_bound n
  have hcabs :
      |c| ≤ Real.exp (-t * unitIntervalCosineEigenvalue n) * M₀ := by
    rw [hc, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_left hcoeff (Real.exp_nonneg _)
  calc |c| * |iteratedDeriv r (cosineMode n) x|
      ≤ (Real.exp (-t * unitIntervalCosineEigenvalue n) * M₀) *
          |(n : ℝ) * Real.pi| ^ r := by
        exact mul_le_mul hcabs hmode (abs_nonneg _)
          (mul_nonneg (Real.exp_nonneg _) hM₀nn)
    _ = |(n : ℝ) * Real.pi| ^ r *
          Real.exp (-t * unitIntervalCosineEigenvalue n) * M₀ := by ring

/-- Uniform spatial derivative bound for the heat cosine representative on the
positive-time tail `t ≥ a`. -/
theorem heatSemigroup_iteratedFDeriv_tail_bound
    {u₀ : intervalDomainPoint → ℝ} {M₀ a : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (ha : 0 < a) (r : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, a ≤ t → ∀ x : ℝ,
      ‖iteratedFDeriv ℝ r
        (fun y : ℝ => ∑' n : ℕ,
          (Real.exp (-t * unitIntervalCosineEigenvalue n) *
            cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n y) x‖ ≤ B := by
  have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
  let B : ℝ := ∑' n : ℕ,
    |(n : ℝ) * Real.pi| ^ r *
      Real.exp (-a * unitIntervalCosineEigenvalue n) * M₀
  have hmaj_summ :
      Summable (fun n : ℕ =>
        |(n : ℝ) * Real.pi| ^ r *
          Real.exp (-a * unitIntervalCosineEigenvalue n) * M₀) :=
    (ShenWork.Paper2.CD6CosineModeBounds.frequency_pow_mul_exp_summable r ha).mul_right M₀
  have hmaj_nonneg : ∀ n : ℕ,
      0 ≤ |(n : ℝ) * Real.pi| ^ r *
        Real.exp (-a * unitIntervalCosineEigenvalue n) * M₀ := by
    intro n
    positivity
  have hB_nonneg : 0 ≤ B := tsum_nonneg hmaj_nonneg
  refine ⟨B, hB_nonneg, ?_⟩
  intro t ht x
  have htpos : 0 < t := lt_of_lt_of_le ha ht
  let v : ℕ → ℕ → ℝ := fun k n =>
    |(n : ℝ) * Real.pi| ^ k *
      Real.exp (-t * unitIntervalCosineEigenvalue n) * M₀
  have hv : ∀ k : ℕ, (k : ℕ∞) ≤ (r : ℕ∞) → Summable (v k) := by
    intro k _hk
    exact
      (ShenWork.Paper2.CD6CosineModeBounds.frequency_pow_mul_exp_summable k htpos).mul_right M₀
  have hterm_bound :
      ∀ (k n : ℕ) (x : ℝ), (k : ℕ∞) ≤ (r : ℕ∞) →
        ‖iteratedFDeriv ℝ k
          (fun y : ℝ =>
            (Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n y) x‖ ≤
          v k n := by
    intro k n x _hk
    exact heatSemigroup_spatialTerm_iteratedFDeriv_bound hu₀_bound k n x
  have hseries :
      iteratedFDeriv ℝ r
        (fun y : ℝ => ∑' n : ℕ,
          (Real.exp (-t * unitIntervalCosineEigenvalue n) *
            cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n y) x =
        ∑' n : ℕ, iteratedFDeriv ℝ r
          (fun y : ℝ =>
            (Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n y) x := by
    exact iteratedFDeriv_tsum_apply
      (f := fun n y =>
        (Real.exp (-t * unitIntervalCosineEigenvalue n) *
          cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n y)
      (v := v) (N := (r : ℕ∞))
      (by intro n; unfold cosineMode; fun_prop) hv hterm_bound (by rfl) x
  have hnorm_summ :
      Summable (fun n : ℕ =>
        ‖iteratedFDeriv ℝ r
          (fun y : ℝ =>
            (Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n y) x‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hv r (by rfl))
    exact hterm_bound r n x (by rfl)
  have hnorm_le :
      ‖iteratedFDeriv ℝ r
        (fun y : ℝ => ∑' n : ℕ,
          (Real.exp (-t * unitIntervalCosineEigenvalue n) *
            cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n y) x‖ ≤
        ∑' n : ℕ, v r n := by
    rw [hseries]
    exact (norm_tsum_le_tsum_norm hnorm_summ).trans
      (hnorm_summ.tsum_le_tsum (fun n => hterm_bound r n x (by rfl)) (hv r (by rfl)))
  have hvt_le : ∀ n : ℕ, v r n ≤
      |(n : ℝ) * Real.pi| ^ r *
        Real.exp (-a * unitIntervalCosineEigenvalue n) * M₀ := by
    intro n
    have hlam_nn : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    have hexp_le :
        Real.exp (-t * unitIntervalCosineEigenvalue n) ≤
          Real.exp (-a * unitIntervalCosineEigenvalue n) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right ht hlam_nn]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp_le (pow_nonneg (abs_nonneg _) r))
      hM₀nn
  have htsum_le : (∑' n : ℕ, v r n) ≤ B := by
    exact (hv r (by rfl)).tsum_le_tsum hvt_le hmaj_summ
  exact hnorm_le.trans htsum_le

private theorem heatD2cos_spatialTerm_iteratedFDeriv_bound
    {u₀ : intervalDomainPoint → ℝ} {M₀ t : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (r n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ r
      (fun y : ℝ =>
        (unitIntervalCosineEigenvalue n ^ 2 *
          (Real.exp (-t * unitIntervalCosineEigenvalue n) *
            cosineCoeffs (intervalDomainLift u₀) n)) * cosineMode n y) x‖ ≤
      |(n : ℝ) * Real.pi| ^ (r + 4) *
        Real.exp (-t * unitIntervalCosineEigenvalue n) * M₀ := by
  have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
  set freq : ℝ := |(n : ℝ) * Real.pi| with hfreq_def
  set lam : ℝ := unitIntervalCosineEigenvalue n with hlam_def
  have hlam_nn : 0 ≤ lam := by
    rw [hlam_def]
    unfold unitIntervalCosineEigenvalue
    positivity
  have hlam_freq : lam = freq ^ 2 := by
    rw [hlam_def, hfreq_def]
    unfold unitIntervalCosineEigenvalue
    exact (sq_abs ((n : ℝ) * Real.pi)).symm
  set c : ℝ := lam ^ 2 *
    (Real.exp (-t * lam) * cosineCoeffs (intervalDomainLift u₀) n) with hc
  have hterm :
      (fun y : ℝ =>
        (unitIntervalCosineEigenvalue n ^ 2 *
          (Real.exp (-t * unitIntervalCosineEigenvalue n) *
            cosineCoeffs (intervalDomainLift u₀) n)) * cosineMode n y) =
      fun y : ℝ => c * cosineMode n y := by
    funext y
    rw [hc, hlam_def]
  rw [hterm, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hcd : ContDiffAt ℝ (r : WithTop ℕ∞) (cosineMode n) x := by
    unfold cosineMode
    fun_prop
  rw [iteratedDeriv_const_mul c hcd, Real.norm_eq_abs, abs_mul]
  have hmode : |iteratedDeriv r (cosineMode n) x| ≤ freq ^ r := by
    rw [hfreq_def]
    simpa [cosineMode, unitIntervalCosineMode,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      using
        ShenWork.Paper2.CD6CosineModeBounds.unitIntervalCosineMode_iteratedFDeriv_bound
          r n x
  have hcoeff : |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀ := hu₀_bound n
  have hcabs :
      |c| ≤ lam ^ 2 * (Real.exp (-t * lam) * M₀) := by
    rw [hc, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hlam_nn 2),
      abs_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hcoeff (Real.exp_nonneg _))
      (pow_nonneg hlam_nn 2)
  calc |c| * |iteratedDeriv r (cosineMode n) x|
      ≤ (lam ^ 2 * (Real.exp (-t * lam) * M₀)) * freq ^ r := by
        exact mul_le_mul hcabs hmode (abs_nonneg _)
          (mul_nonneg (pow_nonneg hlam_nn 2)
            (mul_nonneg (Real.exp_nonneg _) hM₀nn))
    _ = freq ^ (r + 4) * Real.exp (-t * lam) * M₀ := by
        rw [hlam_freq, pow_add]
        ring
    _ = |(n : ℝ) * Real.pi| ^ (r + 4) *
          Real.exp (-t * unitIntervalCosineEigenvalue n) * M₀ := by
        rw [hfreq_def, hlam_def]

private theorem heatD2cos_iteratedFDeriv_tail_bound
    {u₀ : intervalDomainPoint → ℝ} {M₀ a : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (ha : 0 < a) (r : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, a ≤ t → ∀ x : ℝ,
      ‖iteratedFDeriv ℝ r
        (fun y : ℝ => ∑' n : ℕ,
          (unitIntervalCosineEigenvalue n ^ 2 *
            (Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n)) * cosineMode n y) x‖ ≤ B := by
  have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
  let B : ℝ := ∑' n : ℕ,
    |(n : ℝ) * Real.pi| ^ (r + 4) *
      Real.exp (-a * unitIntervalCosineEigenvalue n) * M₀
  have hmaj_summ :
      Summable (fun n : ℕ =>
        |(n : ℝ) * Real.pi| ^ (r + 4) *
          Real.exp (-a * unitIntervalCosineEigenvalue n) * M₀) :=
    (ShenWork.Paper2.CD6CosineModeBounds.frequency_pow_mul_exp_summable (r + 4) ha).mul_right M₀
  have hmaj_nonneg : ∀ n : ℕ,
      0 ≤ |(n : ℝ) * Real.pi| ^ (r + 4) *
        Real.exp (-a * unitIntervalCosineEigenvalue n) * M₀ := by
    intro n
    positivity
  have hB_nonneg : 0 ≤ B := tsum_nonneg hmaj_nonneg
  refine ⟨B, hB_nonneg, ?_⟩
  intro t ht x
  have htpos : 0 < t := lt_of_lt_of_le ha ht
  let v : ℕ → ℕ → ℝ := fun k n =>
    |(n : ℝ) * Real.pi| ^ (k + 4) *
      Real.exp (-t * unitIntervalCosineEigenvalue n) * M₀
  have hv : ∀ k : ℕ, (k : ℕ∞) ≤ (r : ℕ∞) → Summable (v k) := by
    intro k _hk
    exact
      (ShenWork.Paper2.CD6CosineModeBounds.frequency_pow_mul_exp_summable
        (k + 4) htpos).mul_right M₀
  have hterm_bound :
      ∀ (k n : ℕ) (x : ℝ), (k : ℕ∞) ≤ (r : ℕ∞) →
        ‖iteratedFDeriv ℝ k
          (fun y : ℝ =>
            (unitIntervalCosineEigenvalue n ^ 2 *
              (Real.exp (-t * unitIntervalCosineEigenvalue n) *
                cosineCoeffs (intervalDomainLift u₀) n)) * cosineMode n y) x‖ ≤
          v k n := by
    intro k n x _hk
    exact heatD2cos_spatialTerm_iteratedFDeriv_bound hu₀_bound k n x
  have hseries :
      iteratedFDeriv ℝ r
        (fun y : ℝ => ∑' n : ℕ,
          (unitIntervalCosineEigenvalue n ^ 2 *
            (Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n)) * cosineMode n y) x =
        ∑' n : ℕ, iteratedFDeriv ℝ r
          (fun y : ℝ =>
            (unitIntervalCosineEigenvalue n ^ 2 *
              (Real.exp (-t * unitIntervalCosineEigenvalue n) *
                cosineCoeffs (intervalDomainLift u₀) n)) * cosineMode n y) x := by
    exact iteratedFDeriv_tsum_apply
      (f := fun n y =>
        (unitIntervalCosineEigenvalue n ^ 2 *
          (Real.exp (-t * unitIntervalCosineEigenvalue n) *
            cosineCoeffs (intervalDomainLift u₀) n)) * cosineMode n y)
      (v := v) (N := (r : ℕ∞))
      (by intro n; unfold cosineMode; fun_prop) hv hterm_bound (by rfl) x
  have hnorm_summ :
      Summable (fun n : ℕ =>
        ‖iteratedFDeriv ℝ r
          (fun y : ℝ =>
            (unitIntervalCosineEigenvalue n ^ 2 *
              (Real.exp (-t * unitIntervalCosineEigenvalue n) *
                cosineCoeffs (intervalDomainLift u₀) n)) * cosineMode n y) x‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hv r (by rfl))
    exact hterm_bound r n x (by rfl)
  have hnorm_le :
      ‖iteratedFDeriv ℝ r
        (fun y : ℝ => ∑' n : ℕ,
          (unitIntervalCosineEigenvalue n ^ 2 *
            (Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n)) * cosineMode n y) x‖ ≤
        ∑' n : ℕ, v r n := by
    rw [hseries]
    exact (norm_tsum_le_tsum_norm hnorm_summ).trans
      (hnorm_summ.tsum_le_tsum (fun n => hterm_bound r n x (by rfl)) (hv r (by rfl)))
  have hvt_le : ∀ n : ℕ, v r n ≤
      |(n : ℝ) * Real.pi| ^ (r + 4) *
        Real.exp (-a * unitIntervalCosineEigenvalue n) * M₀ := by
    intro n
    have hlam_nn : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    have hexp_le :
        Real.exp (-t * unitIntervalCosineEigenvalue n) ≤
          Real.exp (-a * unitIntervalCosineEigenvalue n) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right ht hlam_nn]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp_le (pow_nonneg (abs_nonneg _) (r + 4)))
      hM₀nn
  have htsum_le : (∑' n : ℕ, v r n) ≤ B := by
    exact (hv r (by rfl)).tsum_le_tsum hvt_le hmaj_summ
  exact hnorm_le.trans htsum_le

/-- The level-0 heat representative stays in a fixed positive compact interval,
uniformly for all positive times. -/
theorem heatLevel0_heatValue_uniform_bounds
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ t : ℝ, 0 < t → ∀ x : ℝ,
        m ≤ (∑' k : ℕ,
          (Real.exp (-t * unitIntervalCosineEigenvalue k) *
            cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x) ∧
        (∑' k : ℕ,
          (Real.exp (-t * unitIntervalCosineEigenvalue k) *
            cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x) ≤ M := by
  classical
  haveI : CompactSpace intervalDomainPoint :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  haveI : Nonempty intervalDomainPoint :=
    ⟨⟨0, Set.left_mem_Icc.mpr (by norm_num)⟩⟩
  obtain ⟨xmin, _, hmin⟩ := IsCompact.exists_isMinOn isCompact_univ
    Set.univ_nonempty hu₀_cont.continuousOn
  obtain ⟨xmax, _, hmax⟩ := IsCompact.exists_isMaxOn isCompact_univ
    Set.univ_nonempty hu₀_cont.norm.continuousOn
  set m : ℝ := u₀ xmin with hm_def
  set M : ℝ := ‖u₀ xmax‖ with hM_def
  have hm_pos : 0 < m := by
    rw [hm_def]
    exact hu₀_pos xmin
  have hlift_lo : ∀ y, y ∈ Set.Icc (0 : ℝ) 1 →
      m ≤ intervalDomainLift u₀ y := by
    intro y hy
    rw [hm_def]
    unfold intervalDomainLift
    rw [dif_pos hy]
    exact hmin (Set.mem_univ (⟨y, hy⟩ : intervalDomainPoint))
  have hlift_hi : ∀ y, |intervalDomainLift u₀ y| ≤ M := by
    intro y
    rw [hM_def]
    unfold intervalDomainLift
    split_ifs with hy
    · exact Real.norm_eq_abs _ ▸ hmax (Set.mem_univ (⟨y, hy⟩ : intervalDomainPoint))
    · exact (le_of_eq abs_zero).trans (norm_nonneg _)
  have hmM : m ≤ M := by
    rw [hm_def, hM_def]
    exact (le_abs_self _).trans (Real.norm_eq_abs _ ▸ hmax (Set.mem_univ xmin))
  refine ⟨m, M, hm_pos, hmM, ?_⟩
  intro t ht
  set Ucos : ℝ → ℝ := fun x => ∑' k : ℕ,
    (Real.exp (-t * unitIntervalCosineEigenvalue k) *
      cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x with hUcos
  have hU_DE : DoublyEven Ucos := by
    simpa [Ucos] using doublyEven_cosineSeries
      (fun k => Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k)
  have hU_agree : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 t) x = Ucos x := by
    intro x hx
    have h := ShenWork.IntervalPicardIterateRepresentation.hagree_zero
      p u₀ ht hu₀_cont hu₀_bound hx
    simpa [Ucos, ShenWork.IntervalPicardIterateRepresentation.iterateReprCoeff] using h
  have hlift_m :=
    ShenWork.IntervalDuhamelIntegrability.intervalDomainLift_aestronglyMeasurable_of_continuous
      hu₀_cont
  have hbounds_Icc : ∀ x ∈ Set.Icc (0 : ℝ) 1, m ≤ Ucos x ∧ Ucos x ≤ M := by
    intro x hx
    have hdef : intervalDomainLift (conjugatePicardIter p u₀ 0 t) x =
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
          t (intervalDomainLift u₀) x := by
      unfold intervalDomainLift
      rw [dif_pos hx]
      rfl
    have hlo : m ≤ intervalDomainLift (conjugatePicardIter p u₀ 0 t) x := by
      rw [hdef]
      exact ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_lower_bound
        ht hm_pos.le hmM hlift_m hlift_lo hlift_hi x
    have hhi : intervalDomainLift (conjugatePicardIter p u₀ 0 t) x ≤ M := by
      rw [hdef]
      exact le_of_abs_le
        (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
          ht (by rw [hM_def]; exact norm_nonneg _) hlift_hi x)
    rw [hU_agree x hx] at hlo hhi
    exact ⟨hlo, hhi⟩
  intro x
  simpa [Ucos] using
    hU_DE.bounds_of_bounds_Icc
      (fun y hy => (hbounds_Icc y hy).1)
      (fun y hy => (hbounds_Icc y hy).2) x

private theorem heatLevel0_rpow_iteratedFDeriv_two_tail_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ a β : ℝ}
    (ha : 0 < a)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, a ≤ t → ∀ x : ℝ, ∀ i : ℕ, i ≤ 2 →
      ‖iteratedFDeriv ℝ i
        (fun y : ℝ =>
          (∑' k : ℕ,
            (Real.exp (-t * unitIntervalCosineEigenvalue k) *
              cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k y) ^ β) x‖ ≤ B := by
  obtain ⟨m, M, hm_pos, hmM, hUM⟩ :=
    heatLevel0_heatValue_uniform_bounds (p := p)
      hu₀_bound hu₀_cont hu₀_pos
  obtain ⟨B1, hB1nn, hB1⟩ :=
    heatSemigroup_iteratedFDeriv_tail_bound hu₀_bound ha 1
  obtain ⟨B2, hB2nn, hB2⟩ :=
    heatSemigroup_iteratedFDeriv_tail_bound hu₀_bound ha 2
  set D : ℝ := max 1 (max B1 B2) with hD_def
  have hD_ge_one : 1 ≤ D := by
    rw [hD_def]
    exact le_max_left _ _
  have hD_nonneg : 0 ≤ D := le_trans zero_le_one hD_ge_one
  have hDpow_ge_D : ∀ i : ℕ, 1 ≤ i → D ≤ D ^ i := by
    intro i hi
    cases i with
    | zero => omega
    | succ j =>
        have hone : (1 : ℝ) ≤ D ^ j := one_le_pow₀ hD_ge_one
        calc D = D * 1 := by ring
          _ ≤ D * D ^ j := mul_le_mul_of_nonneg_left hone hD_nonneg
          _ = D ^ (j + 1) := by rw [pow_succ']
  have hB1D : B1 ≤ D := by
    rw [hD_def]
    exact (le_max_left B1 B2).trans (le_max_right 1 _)
  have hB2D : B2 ≤ D := by
    rw [hD_def]
    exact (le_max_right B1 B2).trans (le_max_right 1 _)
  set K : Set ℝ := Set.Icc (m / 2) (M + 1) with hK_def
  have hK_unique : UniqueDiffOn ℝ K := by
    rw [hK_def]
    apply uniqueDiffOn_Icc
    linarith
  set g : ℝ → ℝ := fun y => y ^ β with hg_def
  have hgC2 : ContDiffOn ℝ (2 : ℕ∞) g K := by
    have hposK : ∀ y ∈ K, y ≠ 0 := by
      intro y hy
      rw [hK_def] at hy
      exact ne_of_gt (lt_of_lt_of_le (by linarith : 0 < m / 2) hy.1)
    simpa [g] using
      (contDiffOn_id (𝕜 := ℝ) (s := K)).rpow_const_of_ne hposK
  have hcont_i : ∀ i : ℕ, i ≤ 2 →
      ContinuousOn (fun y => ‖iteratedFDerivWithin ℝ i g K y‖) K := by
    intro i hi
    exact (hgC2.continuousOn_iteratedFDerivWithin (by exact_mod_cast hi) hK_unique).norm
  obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (by simpa [K] using hcont_i 0 (by norm_num))
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (by simpa [K] using hcont_i 1 (by norm_num))
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (by simpa [K] using hcont_i 2 (by norm_num))
  set C : ℝ := max 0 (max C0 (max C1 C2)) with hC_def
  have hC_nonneg : 0 ≤ C := by
    rw [hC_def]
    exact le_max_left _ _
  have hC0C : C0 ≤ C := by
    rw [hC_def]
    exact (le_max_left C0 (max C1 C2)).trans (le_max_right 0 _)
  have hC1C : C1 ≤ C := by
    rw [hC_def]
    exact ((le_max_left C1 C2).trans (le_max_right C0 _)).trans (le_max_right 0 _)
  have hC2C : C2 ≤ C := by
    rw [hC_def]
    exact ((le_max_right C1 C2).trans (le_max_right C0 _)).trans (le_max_right 0 _)
  have hC_bound : ∀ i : ℕ, i ≤ 2 → ∀ y ∈ K,
      ‖iteratedFDerivWithin ℝ i g K y‖ ≤ C := by
    intro i hi y hy
    interval_cases i
    · have hy' : y ∈ Set.Icc (m / 2) (M + 1) := by simpa [K] using hy
      have h : ‖iteratedFDerivWithin ℝ 0 g K y‖ ≤ C0 := by
        simpa [K] using hC0 y hy'
      exact h.trans hC0C
    · have hy' : y ∈ Set.Icc (m / 2) (M + 1) := by simpa [K] using hy
      have h : ‖iteratedFDerivWithin ℝ 1 g K y‖ ≤ C1 := by
        simpa [K] using hC1 y hy'
      exact h.trans hC1C
    · have hy' : y ∈ Set.Icc (m / 2) (M + 1) := by simpa [K] using hy
      have h : ‖iteratedFDerivWithin ℝ 2 g K y‖ ≤ C2 := by
        simpa [K] using hC2 y hy'
      exact h.trans hC2C
  refine ⟨Nat.factorial 2 * C * D ^ (2 : ℕ), by positivity, ?_⟩
  intro t ht x i hi
  set Ucos : ℝ → ℝ := fun y => ∑' k : ℕ,
    (Real.exp (-t * unitIntervalCosineEigenvalue k) *
      cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k y with hUcos
  have htpos : 0 < t := lt_of_lt_of_le ha ht
  have hU_C2 : ContDiff ℝ (2 : ℕ∞) Ucos := by
    simpa [Ucos] using (heatSemigroup_contDiff_four hu₀_bound htpos).of_le
      (by norm_num : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((4 : ℕ∞) : WithTop ℕ∞))
  have hU_range : Set.range Ucos ⊆ K := by
    rintro z ⟨y, rfl⟩
    have hy := hUM t htpos y
    rw [hK_def]
    exact ⟨by linarith, by linarith⟩
  have hD_bound : ∀ j : ℕ, 1 ≤ j → j ≤ i →
      ‖iteratedFDeriv ℝ j Ucos x‖ ≤ D ^ j := by
    intro j hj hji
    have hj2 : j ≤ 2 := le_trans hji hi
    interval_cases j
    · have h : ‖iteratedFDeriv ℝ 1 Ucos x‖ ≤ B1 := by
        simpa [Ucos] using hB1 t ht x
      exact h.trans (le_trans hB1D (hDpow_ge_D 1 (by norm_num)))
    · have h : ‖iteratedFDeriv ℝ 2 Ucos x‖ ≤ B2 := by
        simpa [Ucos] using hB2 t ht x
      exact h.trans (le_trans hB2D (hDpow_ge_D 2 (by norm_num)))
  have hcomp :=
    norm_iteratedFDeriv_comp_le'
      (𝕜 := ℝ) (g := g) (f := Ucos) (n := i) (N := (2 : ℕ∞)) (t := K)
      hU_range hK_unique hgC2 hU_C2 (by exact_mod_cast hi) x
      (fun j hj => hC_bound j (le_trans hj hi) (Ucos x) (hU_range ⟨x, rfl⟩))
      hD_bound
  have htarget : Nat.factorial i * C * D ^ i ≤
      Nat.factorial 2 * C * D ^ (2 : ℕ) := by
    interval_cases i
    · have hD2 : 1 ≤ D ^ (2 : ℕ) := one_le_pow₀ hD_ge_one
      norm_num
      nlinarith [hC_nonneg, hD2]
    · have hD2 : D ≤ D ^ (2 : ℕ) := hDpow_ge_D 2 (by norm_num)
      norm_num
      nlinarith [hC_nonneg, hD2]
    · norm_num
  have hmain :
      ‖iteratedFDeriv ℝ i
        (fun y : ℝ =>
          (∑' k : ℕ,
            (Real.exp (-t * unitIntervalCosineEigenvalue k) *
              cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k y) ^ β) x‖
        ≤ Nat.factorial i * C * D ^ i := by
    simpa [g, Ucos, Function.comp_def] using hcomp
  exact hmain.trans htarget

/-- Uniform fourth spatial-derivative bound for the heat level-0 power source
`ν · (S(t)u₀)^γ` on a positive-time tail. -/
theorem heatLevel0_powerSource_iteratedFDeriv_four_tail_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ a : ℝ}
    (ha : 0 < a)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, a ≤ t → ∀ x : ℝ,
      ‖iteratedFDeriv ℝ 4
        (fun y : ℝ =>
          p.ν * (∑' k : ℕ,
            (Real.exp (-t * unitIntervalCosineEigenvalue k) *
              cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k y) ^ p.γ) x‖ ≤ B := by
  obtain ⟨m, M, hm_pos, hmM, hUM⟩ :=
    heatLevel0_heatValue_uniform_bounds (p := p)
      hu₀_bound hu₀_cont hu₀_pos
  obtain ⟨B1, hB1nn, hB1⟩ :=
    heatSemigroup_iteratedFDeriv_tail_bound hu₀_bound ha 1
  obtain ⟨B2, hB2nn, hB2⟩ :=
    heatSemigroup_iteratedFDeriv_tail_bound hu₀_bound ha 2
  obtain ⟨B3, hB3nn, hB3⟩ :=
    heatSemigroup_iteratedFDeriv_tail_bound hu₀_bound ha 3
  obtain ⟨B4, hB4nn, hB4⟩ :=
    heatSemigroup_iteratedFDeriv_tail_bound hu₀_bound ha 4
  set D : ℝ := max 1 (max B1 (max B2 (max B3 B4))) with hD_def
  have hD_ge_one : 1 ≤ D := by
    rw [hD_def]
    exact le_max_left _ _
  have hD_nonneg : 0 ≤ D := le_trans zero_le_one hD_ge_one
  have hDpow_ge_D : ∀ i : ℕ, 1 ≤ i → D ≤ D ^ i := by
    intro i hi
    cases i with
    | zero => omega
    | succ j =>
        have hone : (1 : ℝ) ≤ D ^ j := one_le_pow₀ hD_ge_one
        calc D = D * 1 := by ring
          _ ≤ D * D ^ j := mul_le_mul_of_nonneg_left hone hD_nonneg
          _ = D ^ (j + 1) := by rw [pow_succ']
  have hB1D : B1 ≤ D := by
    rw [hD_def]
    exact (le_max_left B1 (max B2 (max B3 B4))).trans (le_max_right 1 _)
  have hB2D : B2 ≤ D := by
    rw [hD_def]
    exact ((le_max_left B2 (max B3 B4)).trans
      (le_max_right B1 _)).trans (le_max_right 1 _)
  have hB3D : B3 ≤ D := by
    rw [hD_def]
    exact (((le_max_left B3 B4).trans (le_max_right B2 _)).trans
      (le_max_right B1 _)).trans (le_max_right 1 _)
  have hB4D : B4 ≤ D := by
    rw [hD_def]
    exact (((le_max_right B3 B4).trans (le_max_right B2 _)).trans
      (le_max_right B1 _)).trans (le_max_right 1 _)
  have hB_le_D : ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      (match i with
        | 1 => B1
        | 2 => B2
        | 3 => B3
        | _ => B4) ≤ D := by
    intro i hi hile
    interval_cases i
    · simpa using hB1D
    · simpa using hB2D
    · simpa using hB3D
    · simpa using hB4D
  set K : Set ℝ := Set.Icc (m / 2) (M + 1) with hK_def
  have hK_unique : UniqueDiffOn ℝ K := by
    rw [hK_def]
    apply uniqueDiffOn_Icc
    linarith
  set g : ℝ → ℝ := fun y => p.ν * y ^ p.γ with hg_def
  have hgC4 : ContDiffOn ℝ (4 : ℕ∞) g K := by
    have hposK : ∀ y ∈ K, y ≠ 0 := by
      intro y hy
      rw [hK_def] at hy
      exact ne_of_gt (lt_of_lt_of_le (by linarith : 0 < m / 2) hy.1)
    simpa [g, smul_eq_mul] using
      ((contDiffOn_id (𝕜 := ℝ) (s := K)).rpow_const_of_ne hposK).const_smul p.ν
  have hcont_i : ∀ i : ℕ, i ≤ 4 →
      ContinuousOn (fun y => ‖iteratedFDerivWithin ℝ i g K y‖) K := by
    intro i hi
    exact (hgC4.continuousOn_iteratedFDerivWithin (by exact_mod_cast hi) hK_unique).norm
  obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (by simpa [K] using hcont_i 0 (by norm_num))
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (by simpa [K] using hcont_i 1 (by norm_num))
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (by simpa [K] using hcont_i 2 (by norm_num))
  obtain ⟨C3, hC3⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (by simpa [K] using hcont_i 3 (by norm_num))
  obtain ⟨C4, hC4⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (by simpa [K] using hcont_i 4 (by norm_num))
  set C : ℝ := max 0 (max C0 (max C1 (max C2 (max C3 C4)))) with hC_def
  have hC_nonneg : 0 ≤ C := by
    rw [hC_def]
    exact le_max_left _ _
  have hC0C : C0 ≤ C := by
    rw [hC_def]
    exact (le_max_left C0 (max C1 (max C2 (max C3 C4)))).trans (le_max_right 0 _)
  have hC1C : C1 ≤ C := by
    rw [hC_def]
    exact ((le_max_left C1 (max C2 (max C3 C4))).trans
      (le_max_right C0 _)).trans (le_max_right 0 _)
  have hC2C : C2 ≤ C := by
    rw [hC_def]
    exact (((le_max_left C2 (max C3 C4)).trans (le_max_right C1 _)).trans
      (le_max_right C0 _)).trans (le_max_right 0 _)
  have hC3C : C3 ≤ C := by
    rw [hC_def]
    exact ((((le_max_left C3 C4).trans (le_max_right C2 _)).trans
      (le_max_right C1 _)).trans (le_max_right C0 _)).trans (le_max_right 0 _)
  have hC4C : C4 ≤ C := by
    rw [hC_def]
    exact ((((le_max_right C3 C4).trans (le_max_right C2 _)).trans
      (le_max_right C1 _)).trans (le_max_right C0 _)).trans (le_max_right 0 _)
  have hC_bound : ∀ i : ℕ, i ≤ 4 → ∀ y ∈ K,
      ‖iteratedFDerivWithin ℝ i g K y‖ ≤ C := by
    intro i hi y hy
    interval_cases i
    · have hy' : y ∈ Set.Icc (m / 2) (M + 1) := by simpa [K] using hy
      have h : ‖iteratedFDerivWithin ℝ 0 g K y‖ ≤ C0 := by
        simpa [K] using hC0 y hy'
      exact h.trans hC0C
    · have hy' : y ∈ Set.Icc (m / 2) (M + 1) := by simpa [K] using hy
      have h : ‖iteratedFDerivWithin ℝ 1 g K y‖ ≤ C1 := by
        simpa [K] using hC1 y hy'
      exact h.trans hC1C
    · have hy' : y ∈ Set.Icc (m / 2) (M + 1) := by simpa [K] using hy
      have h : ‖iteratedFDerivWithin ℝ 2 g K y‖ ≤ C2 := by
        simpa [K] using hC2 y hy'
      exact h.trans hC2C
    · have hy' : y ∈ Set.Icc (m / 2) (M + 1) := by simpa [K] using hy
      have h : ‖iteratedFDerivWithin ℝ 3 g K y‖ ≤ C3 := by
        simpa [K] using hC3 y hy'
      exact h.trans hC3C
    · have hy' : y ∈ Set.Icc (m / 2) (M + 1) := by simpa [K] using hy
      have h : ‖iteratedFDerivWithin ℝ 4 g K y‖ ≤ C4 := by
        simpa [K] using hC4 y hy'
      exact h.trans hC4C
  refine ⟨Nat.factorial 4 * C * D ^ (4 : ℕ), by positivity, ?_⟩
  intro t ht x
  set Ucos : ℝ → ℝ := fun y => ∑' k : ℕ,
    (Real.exp (-t * unitIntervalCosineEigenvalue k) *
      cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k y with hUcos
  have htpos : 0 < t := lt_of_lt_of_le ha ht
  have hU_C4 : ContDiff ℝ (4 : ℕ∞) Ucos := by
    simpa [Ucos] using heatSemigroup_contDiff_four hu₀_bound htpos
  have hU_range : Set.range Ucos ⊆ K := by
    rintro z ⟨y, rfl⟩
    have hy := hUM t htpos y
    rw [hK_def]
    exact ⟨by linarith, by linarith⟩
  have hD_bound : ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      ‖iteratedFDeriv ℝ i Ucos x‖ ≤ D ^ i := by
    intro i hi hile
    interval_cases i
    · have h : ‖iteratedFDeriv ℝ 1 Ucos x‖ ≤ B1 := by
        simpa [Ucos] using hB1 t ht x
      exact h.trans
        (le_trans (hB_le_D 1 (by norm_num) (by norm_num)) (hDpow_ge_D 1 (by norm_num)))
    · have h : ‖iteratedFDeriv ℝ 2 Ucos x‖ ≤ B2 := by
        simpa [Ucos] using hB2 t ht x
      exact h.trans
        (le_trans (hB_le_D 2 (by norm_num) (by norm_num)) (hDpow_ge_D 2 (by norm_num)))
    · have h : ‖iteratedFDeriv ℝ 3 Ucos x‖ ≤ B3 := by
        simpa [Ucos] using hB3 t ht x
      exact h.trans
        (le_trans (hB_le_D 3 (by norm_num) (by norm_num)) (hDpow_ge_D 3 (by norm_num)))
    · have h : ‖iteratedFDeriv ℝ 4 Ucos x‖ ≤ B4 := by
        simpa [Ucos] using hB4 t ht x
      exact h.trans
        (le_trans (hB_le_D 4 (by norm_num) (by norm_num)) (hDpow_ge_D 4 (by norm_num)))
  have hcomp :=
    norm_iteratedFDeriv_comp_le'
      (𝕜 := ℝ) (g := g) (f := Ucos) (n := 4) (N := (4 : ℕ∞)) (t := K)
      hU_range hK_unique hgC4 hU_C4 (by norm_num) x
      (fun i hi => hC_bound i hi (Ucos x) (hU_range ⟨x, rfl⟩))
      hD_bound
  simpa [g, Ucos, Function.comp_def] using hcomp

/-- At every positive time, the heat level-0 power source has a depth-two weak
`H²_N` tower.  The proof uses the global heat cosine representative, whose
doubly-even parity supplies the Neumann endpoint conditions. -/
noncomputable def heatLevel0_srcSlice_weakH4
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ t : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (ht : 0 < t)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) :
    Σ hf : IntervalWeakH2Neumann
        (srcSlice p (conjugatePicardIter p u₀ 0) t),
      IntervalWeakH2Neumann hf.secondDeriv := by
  set Ucos : ℝ → ℝ := fun x => ∑' k : ℕ,
    (Real.exp (-t * unitIntervalCosineEigenvalue k) *
      cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x with hUcos
  have hU_C4 : ContDiff ℝ 4 Ucos := by
    simpa [Ucos] using heatSemigroup_contDiff_four hu₀_bound ht
  have hU_DE : DoublyEven Ucos := by
    simpa [Ucos] using doublyEven_cosineSeries
      (fun k => Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k)
  have hU_agree : ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 t) x = Ucos x := by
    intro x hx
    have h := ShenWork.IntervalPicardIterateRepresentation.hagree_zero
      p u₀ ht hu₀_cont hu₀_bound hx
    simpa [Ucos, ShenWork.IntervalPicardIterateRepresentation.iterateReprCoeff] using h
  have hU_pos_all : ∀ x : ℝ, 0 < Ucos x :=
    hU_DE.pos_of_pos_Icc (fun x hx => by
      rw [← hU_agree x hx]
      exact hpos x hx)
  set G : ℝ → ℝ := fun x => p.ν * Ucos x ^ p.γ with hG
  have hG_C4 : ContDiff ℝ 4 G := by
    have hU_ne : ∀ x, Ucos x ≠ 0 := fun x => ne_of_gt (hU_pos_all x)
    simpa [G] using contDiff_const.mul (hU_C4.rpow_const_of_ne hU_ne)
  have hG_DE : DoublyEven G := by
    have hpow : DoublyEven (fun x => Ucos x ^ p.γ) :=
      hU_DE.comp (fun y => y ^ p.γ)
    simpa [G] using DoublyEven.const_mul p.ν hpow
  have hG_src : ∀ x ∈ Icc (0 : ℝ) 1,
      G x = srcSlice p (conjugatePicardIter p u₀ 0) t x := by
    intro x hx
    simp [G, srcSlice, hU_agree x hx]
  exact intervalWeakH4Neumann_of_doublyEven_agree hG_C4 hG_DE hG_src

/-- Uniform `L¹` bound for the fourth weak derivative stored in the heat level-0
power-source `H⁴_N` certificate on a positive-time tail. -/
theorem heatLevel0_srcSlice_fourth_abs_integral_tail_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ a : ℝ}
    (ha : 0 < a)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x) :
    ∃ B₂ : ℝ, 0 ≤ B₂ ∧ ∀ t : ℝ, (ht : a ≤ t) →
      (∫ x in (0 : ℝ)..1,
        |(heatLevel0_srcSlice_weakH4 (p := p) hu₀_bound hu₀_cont
          (lt_of_lt_of_le ha ht)
          (fun y hy =>
            ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
              (p := p) hu₀_cont hu₀_pos (lt_of_lt_of_le ha ht) hy)).2.secondDeriv x|)
        ≤ B₂ := by
  obtain ⟨B, hBnn, hB⟩ :=
    heatLevel0_powerSource_iteratedFDeriv_four_tail_bound ha
      hu₀_bound hu₀_cont hu₀_pos
  refine ⟨B, hBnn, ?_⟩
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le ha ht
  let hpos : ∀ y ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) y :=
    fun y hy =>
      ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
        (p := p) hu₀_cont hu₀_pos htpos hy
  let H := heatLevel0_srcSlice_weakH4 (p := p) hu₀_bound hu₀_cont htpos hpos
  set Ucos : ℝ → ℝ := fun y => ∑' k : ℕ,
    (Real.exp (-t * unitIntervalCosineEigenvalue k) *
      cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k y with hUcos
  set G : ℝ → ℝ := fun y => p.ν * Ucos y ^ p.γ with hG
  have hU_C4 : ContDiff ℝ 4 Ucos := by
    simpa [Ucos] using heatSemigroup_contDiff_four hu₀_bound htpos
  have hU_DE : DoublyEven Ucos := by
    simpa [Ucos] using doublyEven_cosineSeries
      (fun k => Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k)
  have hU_agree : ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 t) x = Ucos x := by
    intro x hx
    have h := ShenWork.IntervalPicardIterateRepresentation.hagree_zero
      p u₀ htpos hu₀_cont hu₀_bound hx
    simpa [Ucos, ShenWork.IntervalPicardIterateRepresentation.iterateReprCoeff] using h
  have hU_pos_all : ∀ x : ℝ, 0 < Ucos x :=
    hU_DE.pos_of_pos_Icc (fun x hx => by
      rw [← hU_agree x hx]
      exact hpos x hx)
  have hG_C4 : ContDiff ℝ 4 G := by
    have hU_ne : ∀ x, Ucos x ≠ 0 := fun x => ne_of_gt (hU_pos_all x)
    simpa [G] using contDiff_const.mul (hU_C4.rpow_const_of_ne hU_ne)
  have hG_DE : DoublyEven G := by
    have hpow : DoublyEven (fun x => Ucos x ^ p.γ) :=
      hU_DE.comp (fun y => y ^ p.γ)
    simpa [G] using DoublyEven.const_mul p.ν hpow
  have hG_src : ∀ x ∈ Icc (0 : ℝ) 1,
      G x = srcSlice p (conjugatePicardIter p u₀ 0) t x := by
    intro x hx
    simp [G, srcSlice, hU_agree x hx]
  have hH_eq :
      H.2.secondDeriv = deriv (deriv (deriv (deriv G))) := by
    simpa [H, G, Ucos, heatLevel0_srcSlice_weakH4] using
      intervalWeakH4Neumann_of_doublyEven_agree_fourthDeriv hG_C4 hG_DE hG_src
  have hpoint : ∀ x : ℝ, |H.2.secondDeriv x| ≤ B := by
    intro x
    rw [hH_eq]
    have hb := hB t ht x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hb
    simpa [G, Ucos, iteratedDeriv_eq_iterate] using hb
  have hint : IntervalIntegrable (fun x => |H.2.secondDeriv x|)
      MeasureTheory.volume (0 : ℝ) 1 := by
    simpa [Real.norm_eq_abs] using H.2.second_intervalIntegrable.norm
  have hconst : IntervalIntegrable (fun _ : ℝ => B) MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_const
  have hle :
      (∫ x in (0 : ℝ)..1, |H.2.secondDeriv x|)
        ≤ ∫ x in (0 : ℝ)..1, B := by
    refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      hint hconst ?_
    intro x _hx
    exact hpoint x
  calc
    (∫ x in (0 : ℝ)..1,
        |(heatLevel0_srcSlice_weakH4 (p := p) hu₀_bound hu₀_cont
          (lt_of_lt_of_le ha ht)
          (fun y hy =>
            ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
              (p := p) hu₀_cont hu₀_pos (lt_of_lt_of_le ha ht) hy)).2.secondDeriv x|)
        = ∫ x in (0 : ℝ)..1, |H.2.secondDeriv x| := by
          rfl
    _ ≤ ∫ x in (0 : ℝ)..1, B := hle
    _ = B := by simp

/-- Eigenvalue-weighted `ℓ¹` summability of the zeroth heat-level source slice. -/
theorem heatLevel0_srcSlice_eigenvalue_L1_summable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ t : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (ht : 0 < t)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        |cosineCoeffs (srcSlice p (conjugatePicardIter p u₀ 0) t) k|) := by
  let H := heatLevel0_srcSlice_weakH4 hu₀_bound hu₀_cont ht hpos
  exact ShenWork.IntervalSourceDecayQuantitative.intervalWeakH4Neumann_eigenvalue_L1_summable
    H.1 H.2

/-- Fixed-time quartic coefficient decay of the zeroth heat-level source slice. -/
theorem heatLevel0_srcSlice_quartic_decay
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ t : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (ht : 0 < t)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (srcSlice p (conjugatePicardIter p u₀ 0) t) k|
        ≤ C / ((k : ℝ) * Real.pi) ^ 4 := by
  let H := heatLevel0_srcSlice_weakH4 hu₀_bound hu₀_cont ht hpos
  obtain ⟨B₂, hB₂_nonneg, hB₂⟩ := H.2.second_abs_integral_bound
  refine ⟨2 * B₂, by positivity, ?_⟩
  intro k hk
  simpa using
    ShenWork.IntervalSourceDecayQuantitative.intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound
      H.1 H.2 hB₂ k hk

/-- Window-uniform quartic decay of the zeroth heat-level source slice from a
window-uniform `L¹` bound on the fourth weak derivative.

This is the summability-facing form: the remaining analytic obligation is the
single bound `hB₂` on the depth-two weak-H² certificate over the positive time
window. -/
theorem heatLevel0_srcSlice_quartic_decay_window_of_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ a b B₂ : ℝ}
    (ha : 0 < a)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hpos : ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (hB₂ : ∀ t (ht : t ∈ Icc a b),
      (∫ x in (0 : ℝ)..1,
        |(heatLevel0_srcSlice_weakH4 hu₀_bound hu₀_cont
          (lt_of_lt_of_le ha ht.1) (hpos t ht)).2.secondDeriv x|)
        ≤ B₂) :
    ∀ t ∈ Icc a b, ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (srcSlice p (conjugatePicardIter p u₀ 0) t) k|
        ≤ 2 * B₂ / ((k : ℝ) * Real.pi) ^ 4 := by
  intro t ht k hk
  have htpos : 0 < t := lt_of_lt_of_le ha ht.1
  let H := heatLevel0_srcSlice_weakH4 hu₀_bound hu₀_cont htpos (hpos t ht)
  exact
    ShenWork.IntervalSourceDecayQuantitative.intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound
      H.1 H.2 (by simpa [H] using hB₂ t ht) k hk

/-- Tail-uniform quartic coefficient decay of the zeroth heat-level source
slice. -/
theorem heatLevel0_srcSlice_quartic_decay_tail
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ a : ℝ}
    (ha : 0 < a)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, a ≤ t → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (srcSlice p (conjugatePicardIter p u₀ 0) t) k|
        ≤ C / ((k : ℝ) * Real.pi) ^ 4 := by
  obtain ⟨B₂, hB₂nn, hB₂⟩ :=
    heatLevel0_srcSlice_fourth_abs_integral_tail_bound ha
      hu₀_bound hu₀_cont hu₀_pos
  refine ⟨2 * B₂, by positivity, ?_⟩
  intro t ht k hk
  have htpos : 0 < t := lt_of_lt_of_le ha ht
  let hpos : ∀ y ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) y :=
    fun y hy =>
      ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
        (p := p) hu₀_cont hu₀_pos htpos hy
  let H := heatLevel0_srcSlice_weakH4 (p := p) hu₀_bound hu₀_cont htpos hpos
  exact
    ShenWork.IntervalSourceDecayQuantitative.intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound
      H.1 H.2 (by simpa [H] using hB₂ t ht) k hk

private theorem heatLevel0_srcSlice1_source_iteratedFDeriv_two_tail_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ a : ℝ}
    (ha : 0 < a)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, a ≤ t → ∀ x : ℝ,
      ‖iteratedFDeriv ℝ 2
        (fun y : ℝ =>
          p.ν * p.γ *
            (∑' k : ℕ,
              (Real.exp (-t * unitIntervalCosineEigenvalue k) *
                cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k y) ^ (p.γ - 1) *
            deriv (deriv (fun z : ℝ =>
              ∑' k : ℕ,
                (Real.exp (-t * unitIntervalCosineEigenvalue k) *
                  cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k z)) y) x‖ ≤ B := by
  obtain ⟨BP, hBPnn, hBP⟩ :=
    heatLevel0_rpow_iteratedFDeriv_two_tail_bound
      (p := p) (β := p.γ - 1) ha hu₀_bound hu₀_cont hu₀_pos
  obtain ⟨B2, hB2nn, hB2⟩ :=
    heatSemigroup_iteratedFDeriv_tail_bound hu₀_bound ha 2
  obtain ⟨B3, hB3nn, hB3⟩ :=
    heatSemigroup_iteratedFDeriv_tail_bound hu₀_bound ha 3
  obtain ⟨B4, hB4nn, hB4⟩ :=
    heatSemigroup_iteratedFDeriv_tail_bound hu₀_bound ha 4
  set BQ : ℝ := max 0 (max B2 (max B3 B4)) with hBQ_def
  have hBQnn : 0 ≤ BQ := by
    rw [hBQ_def]
    exact le_max_left _ _
  have hB2Q : B2 ≤ BQ := by
    rw [hBQ_def]
    exact (le_max_left B2 (max B3 B4)).trans (le_max_right 0 _)
  have hB3Q : B3 ≤ BQ := by
    rw [hBQ_def]
    exact ((le_max_left B3 B4).trans (le_max_right B2 _)).trans (le_max_right 0 _)
  have hB4Q : B4 ≤ BQ := by
    rw [hBQ_def]
    exact ((le_max_right B3 B4).trans (le_max_right B2 _)).trans (le_max_right 0 _)
  refine ⟨|p.ν * p.γ| * (4 * BP * BQ), by positivity, ?_⟩
  intro t ht x
  set Ucos : ℝ → ℝ := fun y => ∑' k : ℕ,
    (Real.exp (-t * unitIntervalCosineEigenvalue k) *
      cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k y with hUcos
  set P : ℝ → ℝ := fun y => Ucos y ^ (p.γ - 1) with hP
  set Q : ℝ → ℝ := fun y => deriv (deriv Ucos) y with hQ
  have htpos : 0 < t := lt_of_lt_of_le ha ht
  have hU_C4 : ContDiff ℝ 4 Ucos := by
    simpa [Ucos] using heatSemigroup_contDiff_four hu₀_bound htpos
  have hU_DE : DoublyEven Ucos := by
    simpa [Ucos] using doublyEven_cosineSeries
      (fun k => Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k)
  have hU_agree : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 t) y = Ucos y := by
    intro y hy
    have h := ShenWork.IntervalPicardIterateRepresentation.hagree_zero
      p u₀ htpos hu₀_cont hu₀_bound hy
    simpa [Ucos, ShenWork.IntervalPicardIterateRepresentation.iterateReprCoeff] using h
  have hU_pos_all : ∀ y : ℝ, 0 < Ucos y :=
    hU_DE.pos_of_pos_Icc (fun y hy => by
      rw [← hU_agree y hy]
      exact ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
        (p := p) hu₀_cont hu₀_pos htpos hy)
  have hP_C2 : ContDiff ℝ (2 : ℕ∞) P := by
    have hU_ne : ∀ y, Ucos y ≠ 0 := fun y => ne_of_gt (hU_pos_all y)
    simpa [P] using (hU_C4.of_le
      (by norm_num : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((4 : ℕ∞) : WithTop ℕ∞))).rpow_const_of_ne hU_ne
  have hU3 : ContDiff ℝ 3 (deriv Ucos) := by
    simpa using (hU_C4.deriv' : ContDiff ℝ 3 (deriv Ucos))
  have hQ_C2 : ContDiff ℝ (2 : ℕ∞) Q := by
    simpa [Q] using (hU3.deriv' : ContDiff ℝ 2 (deriv (deriv Ucos)))
  have hP_bound : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i P x‖ ≤ BP := by
    intro i hi
    simpa [P, Ucos] using hBP t ht x i hi
  have hQ_bound : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i Q x‖ ≤ BQ := by
    intro i hi
    interval_cases i
    · have h : ‖iteratedFDeriv ℝ 0 Q x‖ ≤ B2 := by
        rw [hQ, norm_iteratedFDeriv_deriv_deriv_eq]
        simpa [Ucos] using hB2 t ht x
      exact h.trans hB2Q
    · have h : ‖iteratedFDeriv ℝ 1 Q x‖ ≤ B3 := by
        rw [hQ, norm_iteratedFDeriv_deriv_deriv_eq]
        simpa [Ucos] using hB3 t ht x
      exact h.trans hB3Q
    · have h : ‖iteratedFDeriv ℝ 2 Q x‖ ≤ B4 := by
        rw [hQ, norm_iteratedFDeriv_deriv_deriv_eq]
        simpa [Ucos] using hB4 t ht x
      exact h.trans hB4Q
  have hPQ_C2 : ContDiff ℝ (2 : ℕ∞) (fun y : ℝ => P y * Q y) :=
    hP_C2.mul hQ_C2
  have hPQ_bound :
      ‖iteratedFDeriv ℝ 2 (fun y : ℝ => P y * Q y) x‖ ≤
        4 * BP * BQ :=
    norm_iteratedFDeriv_two_mul_bound hP_C2 hQ_C2 hBPnn
      hP_bound hQ_bound
  have hconst :
      ‖iteratedFDeriv ℝ 2 (fun y : ℝ => (p.ν * p.γ) * (P y * Q y)) x‖ ≤
        |p.ν * p.γ| * (4 * BP * BQ) := by
    have hPQ_abs :
        |iteratedDeriv 2 (fun y : ℝ => P y * Q y) x| ≤ 4 * BP * BQ := by
      simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using hPQ_bound
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    rw [iteratedDeriv_const_mul (p.ν * p.γ) hPQ_C2.contDiffAt]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left hPQ_abs (abs_nonneg _)
  simpa [P, Q, Ucos, mul_assoc] using hconst

/-- At every positive time, the first time-derivative source slice has a weak
`H²_N` certificate.  The representative is
`νγ U^(γ-1) U''`, where `U = S(t)u₀`. -/
noncomputable def heatLevel0_srcSlice1_weakH2
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ t : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (ht : 0 < t)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) :
    IntervalWeakH2Neumann
      (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) := by
  set Ucos : ℝ → ℝ := fun x => ∑' k : ℕ,
    (Real.exp (-t * unitIntervalCosineEigenvalue k) *
      cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x with hUcos
  have hU_C4 : ContDiff ℝ 4 Ucos := by
    simpa [Ucos] using heatSemigroup_contDiff_four hu₀_bound ht
  have hU_DE : DoublyEven Ucos := by
    simpa [Ucos] using doublyEven_cosineSeries
      (fun k => Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k)
  have hU_agree : ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 t) x = Ucos x := by
    intro x hx
    have h := ShenWork.IntervalPicardIterateRepresentation.hagree_zero
      p u₀ ht hu₀_cont hu₀_bound hx
    simpa [Ucos, ShenWork.IntervalPicardIterateRepresentation.iterateReprCoeff] using h
  have hU_pos_all : ∀ x : ℝ, 0 < Ucos x :=
    hU_DE.pos_of_pos_Icc (fun x hx => by
      rw [← hU_agree x hx]
      exact hpos x hx)
  have hU_fun : Ucos =
      fun x : ℝ => unitIntervalCosineHeatValue t
        (cosineCoeffs (intervalDomainLift u₀)) x := by
    funext x
    have h := ShenWork.Paper2.unitIntervalCosineHeatValue_eq_cosineCoeffSeries
      t (cosineCoeffs (intervalDomainLift u₀)) x
    simpa [Ucos] using h.symm
  have hU3 : ContDiff ℝ 3 (deriv Ucos) := by
    simpa using (hU_C4.deriv' : ContDiff ℝ 3 (deriv Ucos))
  have hUdd_C2 : ContDiff ℝ 2 (deriv (deriv Ucos)) := by
    simpa using (hU3.deriv' : ContDiff ℝ 2 (deriv (deriv Ucos)))
  have hUdd_DE : DoublyEven (deriv (deriv Ucos)) := hU_DE.deriv_deriv
  set G : ℝ → ℝ := fun x =>
    p.ν * p.γ * Ucos x ^ (p.γ - 1) * deriv (deriv Ucos) x with hG
  have hG_C2 : ContDiff ℝ 2 G := by
    have hU_ne : ∀ x, Ucos x ≠ 0 := fun x => ne_of_gt (hU_pos_all x)
    have hpow : ContDiff ℝ 2 (fun x => Ucos x ^ (p.γ - 1)) :=
      (hU_C4.of_le (by norm_num)).rpow_const_of_ne hU_ne
    simpa [G, mul_assoc] using
      (((contDiff_const.mul contDiff_const).mul hpow).mul hUdd_C2)
  have hG_DE : DoublyEven G := by
    have hpow : DoublyEven (fun x => Ucos x ^ (p.γ - 1)) :=
      hU_DE.comp (fun y => y ^ (p.γ - 1))
    have hprod : DoublyEven (fun x => Ucos x ^ (p.γ - 1) *
        deriv (deriv Ucos) x) :=
      hpow.mul hUdd_DE
    simpa [G, mul_assoc] using DoublyEven.const_mul (p.ν * p.γ) hprod
  have hG_src : ∀ x ∈ Icc (0 : ℝ) 1,
      G x = srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t x := by
    intro x hx
    have hdu : heatDu u₀ t x = deriv (deriv Ucos) x := by
      rw [hU_fun]
      exact heatDu_eq_heatValue_secondDeriv hu₀_bound ht
    simp [G, srcSlice1, hU_agree x hx, hdu, mul_assoc]
  exact intervalWeakH2Neumann_of_doublyEven_agree hG_C2 hG_DE hG_src

/-- Uniform `L¹` bound for the weak second derivative of the first
time-derivative heat-level source slice on a positive-time tail. -/
theorem heatLevel0_srcSlice1_second_abs_integral_tail_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ a : ℝ}
    (ha : 0 < a)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x) :
    ∃ B₁ : ℝ, 0 ≤ B₁ ∧ ∀ t : ℝ, (ht : a ≤ t) →
      (∫ x in (0 : ℝ)..1,
        |(heatLevel0_srcSlice1_weakH2 (p := p) hu₀_bound hu₀_cont
          (lt_of_lt_of_le ha ht)
          (fun y hy =>
            ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
              (p := p) hu₀_cont hu₀_pos (lt_of_lt_of_le ha ht) hy)).secondDeriv x|)
        ≤ B₁ := by
  obtain ⟨B, hBnn, hB⟩ :=
    heatLevel0_srcSlice1_source_iteratedFDeriv_two_tail_bound ha
      hu₀_bound hu₀_cont hu₀_pos
  refine ⟨B, hBnn, ?_⟩
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le ha ht
  let hpos : ∀ y ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) y :=
    fun y hy =>
      ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
        (p := p) hu₀_cont hu₀_pos htpos hy
  let H := heatLevel0_srcSlice1_weakH2 (p := p) hu₀_bound hu₀_cont htpos hpos
  set Ucos : ℝ → ℝ := fun y => ∑' k : ℕ,
    (Real.exp (-t * unitIntervalCosineEigenvalue k) *
      cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k y with hUcos
  set G : ℝ → ℝ := fun y =>
    p.ν * p.γ * Ucos y ^ (p.γ - 1) * deriv (deriv Ucos) y with hG
  have hU_C4 : ContDiff ℝ 4 Ucos := by
    simpa [Ucos] using heatSemigroup_contDiff_four hu₀_bound htpos
  have hU_DE : DoublyEven Ucos := by
    simpa [Ucos] using doublyEven_cosineSeries
      (fun k => Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k)
  have hU_agree : ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 t) x = Ucos x := by
    intro x hx
    have h := ShenWork.IntervalPicardIterateRepresentation.hagree_zero
      p u₀ htpos hu₀_cont hu₀_bound hx
    simpa [Ucos, ShenWork.IntervalPicardIterateRepresentation.iterateReprCoeff] using h
  have hU_pos_all : ∀ x : ℝ, 0 < Ucos x :=
    hU_DE.pos_of_pos_Icc (fun x hx => by
      rw [← hU_agree x hx]
      exact hpos x hx)
  have hU3 : ContDiff ℝ 3 (deriv Ucos) := by
    simpa using (hU_C4.deriv' : ContDiff ℝ 3 (deriv Ucos))
  have hUdd_C2 : ContDiff ℝ 2 (deriv (deriv Ucos)) := by
    simpa using (hU3.deriv' : ContDiff ℝ 2 (deriv (deriv Ucos)))
  have hUdd_DE : DoublyEven (deriv (deriv Ucos)) := hU_DE.deriv_deriv
  have hG_C2 : ContDiff ℝ 2 G := by
    have hU_ne : ∀ x, Ucos x ≠ 0 := fun x => ne_of_gt (hU_pos_all x)
    have hpow : ContDiff ℝ 2 (fun x => Ucos x ^ (p.γ - 1)) :=
      (hU_C4.of_le (by norm_num)).rpow_const_of_ne hU_ne
    simpa [G, mul_assoc] using
      (((contDiff_const.mul contDiff_const).mul hpow).mul hUdd_C2)
  have hG_DE : DoublyEven G := by
    have hpow : DoublyEven (fun x => Ucos x ^ (p.γ - 1)) :=
      hU_DE.comp (fun y => y ^ (p.γ - 1))
    have hprod : DoublyEven (fun x => Ucos x ^ (p.γ - 1) *
        deriv (deriv Ucos) x) :=
      hpow.mul hUdd_DE
    simpa [G, mul_assoc] using DoublyEven.const_mul (p.ν * p.γ) hprod
  have hU_fun : Ucos =
      fun x : ℝ => unitIntervalCosineHeatValue t
        (cosineCoeffs (intervalDomainLift u₀)) x := by
    funext x
    have h := ShenWork.Paper2.unitIntervalCosineHeatValue_eq_cosineCoeffSeries
      t (cosineCoeffs (intervalDomainLift u₀)) x
    simpa [Ucos] using h.symm
  have hG_src : ∀ x ∈ Icc (0 : ℝ) 1,
      G x = srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t x := by
    intro x hx
    have hdu : heatDu u₀ t x = deriv (deriv Ucos) x := by
      rw [hU_fun]
      exact heatDu_eq_heatValue_secondDeriv hu₀_bound htpos
    simp [G, srcSlice1, hU_agree x hx, hdu, mul_assoc]
  have hH_eq : H.secondDeriv = deriv (deriv G) := by
    simpa [H, G, Ucos, heatLevel0_srcSlice1_weakH2] using
      intervalWeakH2Neumann_of_doublyEven_agree_secondDeriv hG_C2 hG_DE hG_src
  have hpoint : ∀ x : ℝ, |H.secondDeriv x| ≤ B := by
    intro x
    rw [hH_eq]
    have hb := hB t ht x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hb
    simpa [G, Ucos, iteratedDeriv_eq_iterate] using hb
  have hint : IntervalIntegrable (fun x => |H.secondDeriv x|)
      MeasureTheory.volume (0 : ℝ) 1 := by
    simpa [Real.norm_eq_abs] using H.second_intervalIntegrable.norm
  have hconst : IntervalIntegrable (fun _ : ℝ => B) MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_const
  have hle :
      (∫ x in (0 : ℝ)..1, |H.secondDeriv x|)
        ≤ ∫ x in (0 : ℝ)..1, B := by
    refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      hint hconst ?_
    intro x _hx
    exact hpoint x
  calc
    (∫ x in (0 : ℝ)..1,
        |(heatLevel0_srcSlice1_weakH2 (p := p) hu₀_bound hu₀_cont
          (lt_of_lt_of_le ha ht)
          (fun y hy =>
            ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
              (p := p) hu₀_cont hu₀_pos (lt_of_lt_of_le ha ht) hy)).secondDeriv x|)
        = ∫ x in (0 : ℝ)..1, |H.secondDeriv x| := by
          rfl
    _ ≤ ∫ x in (0 : ℝ)..1, B := hle
    _ = B := by simp

/-- Tail-uniform quadratic coefficient decay of the first time-derivative
heat-level source slice. -/
theorem heatLevel0_srcSlice1_quadratic_decay_tail
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ a : ℝ}
    (ha : 0 < a)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, a ≤ t → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k|
        ≤ C / ((k : ℝ) * Real.pi) ^ 2 := by
  obtain ⟨B₁, hB₁nn, hB₁⟩ :=
    heatLevel0_srcSlice1_second_abs_integral_tail_bound ha
      hu₀_bound hu₀_cont hu₀_pos
  refine ⟨2 * B₁, by positivity, ?_⟩
  intro t ht k hk
  have htpos : 0 < t := lt_of_lt_of_le ha ht
  let hpos : ∀ y ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) y :=
    fun y hy =>
      ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
        (p := p) hu₀_cont hu₀_pos htpos hy
  let H := heatLevel0_srcSlice1_weakH2 (p := p) hu₀_bound hu₀_cont htpos hpos
  exact
    ShenWork.IntervalSourceDecayQuantitative.intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound
      H (by simpa [H] using hB₁ t ht) k hk

private theorem heatLevel0_srcSlice2_source_iteratedFDeriv_two_tail_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ a : ℝ}
    (ha : 0 < a)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, a ≤ t → ∀ x : ℝ,
      ‖iteratedFDeriv ℝ 2
        (fun y : ℝ =>
          p.ν * p.γ * (p.γ - 1) *
              (∑' k : ℕ,
                (Real.exp (-t * unitIntervalCosineEigenvalue k) *
                  cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k y) ^ (p.γ - 1 - 1) *
              (deriv (deriv (fun z : ℝ =>
                ∑' k : ℕ,
                  (Real.exp (-t * unitIntervalCosineEigenvalue k) *
                    cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k z)) y) ^ (2 : ℕ)
            + p.ν * p.γ *
              (∑' k : ℕ,
                (Real.exp (-t * unitIntervalCosineEigenvalue k) *
                  cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k y) ^ (p.γ - 1) *
              (∑' k : ℕ,
                (unitIntervalCosineEigenvalue k ^ 2 *
                  (Real.exp (-t * unitIntervalCosineEigenvalue k) *
                    cosineCoeffs (intervalDomainLift u₀) k)) * cosineMode k y)) x‖ ≤ B := by
  obtain ⟨BP1, hBP1nn, hBP1⟩ :=
    heatLevel0_rpow_iteratedFDeriv_two_tail_bound
      (p := p) (β := p.γ - 1) ha hu₀_bound hu₀_cont hu₀_pos
  obtain ⟨BP2, hBP2nn, hBP2⟩ :=
    heatLevel0_rpow_iteratedFDeriv_two_tail_bound
      (p := p) (β := p.γ - 1 - 1) ha hu₀_bound hu₀_cont hu₀_pos
  obtain ⟨B2, hB2nn, hB2⟩ :=
    heatSemigroup_iteratedFDeriv_tail_bound hu₀_bound ha 2
  obtain ⟨B3, hB3nn, hB3⟩ :=
    heatSemigroup_iteratedFDeriv_tail_bound hu₀_bound ha 3
  obtain ⟨B4, hB4nn, hB4⟩ :=
    heatSemigroup_iteratedFDeriv_tail_bound hu₀_bound ha 4
  obtain ⟨R0, hR0nn, hR0⟩ := heatD2cos_iteratedFDeriv_tail_bound hu₀_bound ha 0
  obtain ⟨R1, hR1nn, hR1⟩ := heatD2cos_iteratedFDeriv_tail_bound hu₀_bound ha 1
  obtain ⟨R2, hR2nn, hR2⟩ := heatD2cos_iteratedFDeriv_tail_bound hu₀_bound ha 2
  set BQ : ℝ := max 0 (max B2 (max B3 B4)) with hBQ_def
  have hBQnn : 0 ≤ BQ := by
    rw [hBQ_def]
    exact le_max_left _ _
  have hB2Q : B2 ≤ BQ := by
    rw [hBQ_def]
    exact (le_max_left B2 (max B3 B4)).trans (le_max_right 0 _)
  have hB3Q : B3 ≤ BQ := by
    rw [hBQ_def]
    exact ((le_max_left B3 B4).trans (le_max_right B2 _)).trans (le_max_right 0 _)
  have hB4Q : B4 ≤ BQ := by
    rw [hBQ_def]
    exact ((le_max_right B3 B4).trans (le_max_right B2 _)).trans (le_max_right 0 _)
  set BR : ℝ := max 0 (max R0 (max R1 R2)) with hBR_def
  have hBRnn : 0 ≤ BR := by
    rw [hBR_def]
    exact le_max_left _ _
  have hR0R : R0 ≤ BR := by
    rw [hBR_def]
    exact (le_max_left R0 (max R1 R2)).trans (le_max_right 0 _)
  have hR1R : R1 ≤ BR := by
    rw [hBR_def]
    exact ((le_max_left R1 R2).trans (le_max_right R0 _)).trans (le_max_right 0 _)
  have hR2R : R2 ≤ BR := by
    rw [hBR_def]
    exact ((le_max_right R1 R2).trans (le_max_right R0 _)).trans (le_max_right 0 _)
  set BQQ : ℝ := 4 * BQ * BQ with hBQQ_def
  set BT1 : ℝ := |p.ν * p.γ * (p.γ - 1)| * (4 * BP2 * BQQ) with hBT1_def
  set BT2 : ℝ := |p.ν * p.γ| * (4 * BP1 * BR) with hBT2_def
  refine ⟨BT1 + BT2, by
    rw [hBT1_def, hBT2_def, hBQQ_def]
    positivity, ?_⟩
  intro t ht x
  set Ucos : ℝ → ℝ := fun y => ∑' k : ℕ,
    (Real.exp (-t * unitIntervalCosineEigenvalue k) *
      cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k y with hUcos
  set Q : ℝ → ℝ := fun y => deriv (deriv Ucos) y with hQ
  set R : ℝ → ℝ := fun y => ∑' k : ℕ,
    (unitIntervalCosineEigenvalue k ^ 2 *
      (Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k)) * cosineMode k y with hR
  set P1 : ℝ → ℝ := fun y => Ucos y ^ (p.γ - 1) with hP1
  set P2 : ℝ → ℝ := fun y => Ucos y ^ (p.γ - 1 - 1) with hP2
  have htpos : 0 < t := lt_of_lt_of_le ha ht
  have hU_C4 : ContDiff ℝ 4 Ucos := by
    simpa [Ucos] using heatSemigroup_contDiff_four hu₀_bound htpos
  have hU_DE : DoublyEven Ucos := by
    simpa [Ucos] using doublyEven_cosineSeries
      (fun k => Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k)
  have hU_agree : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 t) y = Ucos y := by
    intro y hy
    have h := ShenWork.IntervalPicardIterateRepresentation.hagree_zero
      p u₀ htpos hu₀_cont hu₀_bound hy
    simpa [Ucos, ShenWork.IntervalPicardIterateRepresentation.iterateReprCoeff] using h
  have hU_pos_all : ∀ y : ℝ, 0 < Ucos y :=
    hU_DE.pos_of_pos_Icc (fun y hy => by
      rw [← hU_agree y hy]
      exact ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
        (p := p) hu₀_cont hu₀_pos htpos hy)
  have hP1_C2 : ContDiff ℝ (2 : ℕ∞) P1 := by
    have hU_ne : ∀ y, Ucos y ≠ 0 := fun y => ne_of_gt (hU_pos_all y)
    simpa [P1] using (hU_C4.of_le
      (by norm_num : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((4 : ℕ∞) : WithTop ℕ∞))).rpow_const_of_ne hU_ne
  have hP2_C2 : ContDiff ℝ (2 : ℕ∞) P2 := by
    have hU_ne : ∀ y, Ucos y ≠ 0 := fun y => ne_of_gt (hU_pos_all y)
    simpa [P2] using (hU_C4.of_le
      (by norm_num : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((4 : ℕ∞) : WithTop ℕ∞))).rpow_const_of_ne hU_ne
  have hU3 : ContDiff ℝ 3 (deriv Ucos) := by
    simpa using (hU_C4.deriv' : ContDiff ℝ 3 (deriv Ucos))
  have hQ_C2 : ContDiff ℝ (2 : ℕ∞) Q := by
    simpa [Q] using (hU3.deriv' : ContDiff ℝ 2 (deriv (deriv Ucos)))
  have hR_C2 : ContDiff ℝ (2 : ℕ∞) R := by
    simpa [R, heatD2u, if_pos htpos, mul_assoc] using
      heatD2u_contDiff_two hu₀_bound htpos
  have hP1_bound : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i P1 x‖ ≤ BP1 := by
    intro i hi
    simpa [P1, Ucos] using hBP1 t ht x i hi
  have hP2_bound : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i P2 x‖ ≤ BP2 := by
    intro i hi
    simpa [P2, Ucos] using hBP2 t ht x i hi
  have hQ_bound : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i Q x‖ ≤ BQ := by
    intro i hi
    interval_cases i
    · have h : ‖iteratedFDeriv ℝ 0 Q x‖ ≤ B2 := by
        rw [hQ, norm_iteratedFDeriv_deriv_deriv_eq]
        simpa [Ucos] using hB2 t ht x
      exact h.trans hB2Q
    · have h : ‖iteratedFDeriv ℝ 1 Q x‖ ≤ B3 := by
        rw [hQ, norm_iteratedFDeriv_deriv_deriv_eq]
        simpa [Ucos] using hB3 t ht x
      exact h.trans hB3Q
    · have h : ‖iteratedFDeriv ℝ 2 Q x‖ ≤ B4 := by
        rw [hQ, norm_iteratedFDeriv_deriv_deriv_eq]
        simpa [Ucos] using hB4 t ht x
      exact h.trans hB4Q
  have hR_bound : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i R x‖ ≤ BR := by
    intro i hi
    interval_cases i
    · have h : ‖iteratedFDeriv ℝ 0 R x‖ ≤ R0 := by
        simpa [R] using hR0 t ht x
      exact h.trans hR0R
    · have h : ‖iteratedFDeriv ℝ 1 R x‖ ≤ R1 := by
        simpa [R] using hR1 t ht x
      exact h.trans hR1R
    · have h : ‖iteratedFDeriv ℝ 2 R x‖ ≤ R2 := by
        simpa [R] using hR2 t ht x
      exact h.trans hR2R
  have hQsq_C2 : ContDiff ℝ (2 : ℕ∞) (fun y : ℝ => Q y * Q y) :=
    hQ_C2.mul hQ_C2
  have hQsq_bound : ∀ i : ℕ, i ≤ 2 →
      ‖iteratedFDeriv ℝ i (fun y : ℝ => Q y * Q y) x‖ ≤ BQQ := by
    intro i hi
    rw [hBQQ_def]
    exact norm_iteratedFDeriv_mul_bound_of_le_two hQ_C2 hQ_C2
      hBQnn hBQnn i hi hQ_bound hQ_bound
  have hT1core_C2 : ContDiff ℝ (2 : ℕ∞) (fun y : ℝ => P2 y * (Q y * Q y)) :=
    hP2_C2.mul hQsq_C2
  have hT1core_bound :
      ‖iteratedFDeriv ℝ 2 (fun y : ℝ => P2 y * (Q y * Q y)) x‖ ≤
        4 * BP2 * BQQ :=
    norm_iteratedFDeriv_two_mul_bound hP2_C2 hQsq_C2 hBP2nn
      hP2_bound hQsq_bound
  have hT2core_C2 : ContDiff ℝ (2 : ℕ∞) (fun y : ℝ => P1 y * R y) :=
    hP1_C2.mul hR_C2
  have hT2core_bound :
      ‖iteratedFDeriv ℝ 2 (fun y : ℝ => P1 y * R y) x‖ ≤ 4 * BP1 * BR :=
    norm_iteratedFDeriv_two_mul_bound hP1_C2 hR_C2 hBP1nn hP1_bound hR_bound
  have hT1_bound :
      ‖iteratedFDeriv ℝ 2
        (fun y : ℝ => (p.ν * p.γ * (p.γ - 1)) *
          (P2 y * (Q y * Q y))) x‖ ≤ BT1 := by
    rw [hBT1_def]
    exact norm_iteratedFDeriv_two_const_mul_bound hT1core_C2 hT1core_bound
  have hT2_bound :
      ‖iteratedFDeriv ℝ 2
        (fun y : ℝ => (p.ν * p.γ) * (P1 y * R y)) x‖ ≤ BT2 := by
    rw [hBT2_def]
    exact norm_iteratedFDeriv_two_const_mul_bound hT2core_C2 hT2core_bound
  have hT1_C2 : ContDiff ℝ (2 : ℕ∞)
      (fun y : ℝ => (p.ν * p.γ * (p.γ - 1)) * (P2 y * (Q y * Q y))) :=
    contDiff_const.mul hT1core_C2
  have hT2_C2 : ContDiff ℝ (2 : ℕ∞)
      (fun y : ℝ => (p.ν * p.γ) * (P1 y * R y)) :=
    contDiff_const.mul hT2core_C2
  have hsum :
      ‖iteratedFDeriv ℝ 2
        (fun y : ℝ =>
          (p.ν * p.γ * (p.γ - 1)) * (P2 y * (Q y * Q y)) +
            (p.ν * p.γ) * (P1 y * R y)) x‖ ≤ BT1 + BT2 := by
    change ‖iteratedFDeriv ℝ 2
      ((fun y : ℝ => (p.ν * p.γ * (p.γ - 1)) * (P2 y * (Q y * Q y))) +
        (fun y : ℝ => (p.ν * p.γ) * (P1 y * R y))) x‖ ≤ BT1 + BT2
    rw [iteratedFDeriv_add_apply hT1_C2.contDiffAt hT2_C2.contDiffAt]
    exact (norm_add_le _ _).trans (add_le_add hT1_bound hT2_bound)
  simpa [P1, P2, Q, R, Ucos, pow_two, mul_assoc, mul_left_comm, mul_comm] using hsum

/-- Fixed-time quadratic coefficient decay of the first time-derivative source
slice. -/
theorem heatLevel0_srcSlice1_quadratic_decay
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ t : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (ht : 0 < t)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k|
        ≤ C / ((k : ℝ) * Real.pi) ^ 2 := by
  exact ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_cosineCoeff_quadratic_decay
    (heatLevel0_srcSlice1_weakH2 hu₀_bound hu₀_cont ht hpos)

/-- Window-uniform quadratic decay of the first time-derivative heat-level source
slice from a window-uniform `L¹` bound on its weak second derivative. -/
theorem heatLevel0_srcSlice1_quadratic_decay_window_of_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ a b B₁ : ℝ}
    (ha : 0 < a)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hpos : ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (hB₁ : ∀ t (ht : t ∈ Icc a b),
      (∫ x in (0 : ℝ)..1,
        |(heatLevel0_srcSlice1_weakH2 hu₀_bound hu₀_cont
          (lt_of_lt_of_le ha ht.1) (hpos t ht)).secondDeriv x|)
        ≤ B₁) :
    ∀ t ∈ Icc a b, ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k|
        ≤ 2 * B₁ / ((k : ℝ) * Real.pi) ^ 2 := by
  intro t ht k hk
  let H := heatLevel0_srcSlice1_weakH2 hu₀_bound hu₀_cont
    (lt_of_lt_of_le ha ht.1) (hpos t ht)
  exact
    ShenWork.IntervalSourceDecayQuantitative.intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound
      H (by simpa [H] using hB₁ t ht) k hk

/-- At every positive time, the second time-derivative source slice has a weak
`H²_N` certificate. -/
noncomputable def heatLevel0_srcSlice2_weakH2
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ t : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (ht : 0 < t)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) :
    IntervalWeakH2Neumann
      (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀) t) := by
  set Ucos : ℝ → ℝ := fun x => ∑' k : ℕ,
    (Real.exp (-t * unitIntervalCosineEigenvalue k) *
      cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x with hUcos
  set D2cos : ℝ → ℝ := fun x => ∑' k : ℕ,
    (unitIntervalCosineEigenvalue k ^ 2 *
      (Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k)) * cosineMode k x with hD2cos
  have hU_C4 : ContDiff ℝ 4 Ucos := by
    simpa [Ucos] using heatSemigroup_contDiff_four hu₀_bound ht
  have hU_DE : DoublyEven Ucos := by
    simpa [Ucos] using doublyEven_cosineSeries
      (fun k => Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k)
  have hU_agree : ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 t) x = Ucos x := by
    intro x hx
    have h := ShenWork.IntervalPicardIterateRepresentation.hagree_zero
      p u₀ ht hu₀_cont hu₀_bound hx
    simpa [Ucos, ShenWork.IntervalPicardIterateRepresentation.iterateReprCoeff] using h
  have hU_pos_all : ∀ x : ℝ, 0 < Ucos x :=
    hU_DE.pos_of_pos_Icc (fun x hx => by
      rw [← hU_agree x hx]
      exact hpos x hx)
  have hU_fun : Ucos =
      fun x : ℝ => unitIntervalCosineHeatValue t
        (cosineCoeffs (intervalDomainLift u₀)) x := by
    funext x
    have h := ShenWork.Paper2.unitIntervalCosineHeatValue_eq_cosineCoeffSeries
      t (cosineCoeffs (intervalDomainLift u₀)) x
    simpa [Ucos] using h.symm
  have hU3 : ContDiff ℝ 3 (deriv Ucos) := by
    simpa using (hU_C4.deriv' : ContDiff ℝ 3 (deriv Ucos))
  have hUdd_C2 : ContDiff ℝ 2 (deriv (deriv Ucos)) := by
    simpa using (hU3.deriv' : ContDiff ℝ 2 (deriv (deriv Ucos)))
  have hUdd_DE : DoublyEven (deriv (deriv Ucos)) := hU_DE.deriv_deriv
  have hD2_C2 : ContDiff ℝ 2 D2cos := by
    simpa [D2cos, heatD2u, if_pos ht, mul_assoc] using
      heatD2u_contDiff_two hu₀_bound ht
  have hD2_DE : DoublyEven D2cos := by
    simpa [D2cos] using doublyEven_cosineSeries
      (fun k => unitIntervalCosineEigenvalue k ^ 2 *
        (Real.exp (-t * unitIntervalCosineEigenvalue k) *
          cosineCoeffs (intervalDomainLift u₀) k))
  set G : ℝ → ℝ := fun x =>
    p.ν * p.γ * (p.γ - 1) * Ucos x ^ (p.γ - 1 - 1) *
        (deriv (deriv Ucos) x) ^ (2 : ℕ)
      + p.ν * p.γ * Ucos x ^ (p.γ - 1) * D2cos x with hG
  have hG_C2 : ContDiff ℝ 2 G := by
    have hU_ne : ∀ x, Ucos x ≠ 0 := fun x => ne_of_gt (hU_pos_all x)
    have hpow2 : ContDiff ℝ 2 (fun x => Ucos x ^ (p.γ - 1 - 1)) :=
      (hU_C4.of_le (by norm_num)).rpow_const_of_ne hU_ne
    have hpow1 : ContDiff ℝ 2 (fun x => Ucos x ^ (p.γ - 1)) :=
      (hU_C4.of_le (by norm_num)).rpow_const_of_ne hU_ne
    have hterm1 : ContDiff ℝ 2 (fun x =>
        p.ν * p.γ * (p.γ - 1) * Ucos x ^ (p.γ - 1 - 1) *
          (deriv (deriv Ucos) x) ^ (2 : ℕ)) := by
      have hconst : ContDiff ℝ 2
          (fun _ : ℝ => p.ν * p.γ * (p.γ - 1)) := contDiff_const
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
        ((hconst.mul hpow2).mul (hUdd_C2.mul hUdd_C2))
    have hterm2 : ContDiff ℝ 2 (fun x =>
        p.ν * p.γ * Ucos x ^ (p.γ - 1) * D2cos x) := by
      have hconst : ContDiff ℝ 2 (fun _ : ℝ => p.ν * p.γ) := contDiff_const
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ((hconst.mul hpow1).mul hD2_C2)
    simpa [G] using hterm1.add hterm2
  have hG_DE : DoublyEven G := by
    have hpow2 : DoublyEven (fun x => Ucos x ^ (p.γ - 1 - 1)) :=
      hU_DE.comp (fun y => y ^ (p.γ - 1 - 1))
    have hpow1 : DoublyEven (fun x => Ucos x ^ (p.γ - 1)) :=
      hU_DE.comp (fun y => y ^ (p.γ - 1))
    have hsq : DoublyEven (fun x => (deriv (deriv Ucos) x) ^ (2 : ℕ)) := by
      simpa [pow_two] using hUdd_DE.mul hUdd_DE
    have hterm1 : DoublyEven (fun x =>
        p.ν * p.γ * (p.γ - 1) * Ucos x ^ (p.γ - 1 - 1) *
          (deriv (deriv Ucos) x) ^ (2 : ℕ)) := by
      simpa [mul_assoc] using
        DoublyEven.const_mul (p.ν * p.γ * (p.γ - 1)) (hpow2.mul hsq)
    have hterm2 : DoublyEven (fun x =>
        p.ν * p.γ * Ucos x ^ (p.γ - 1) * D2cos x) := by
      simpa [mul_assoc] using
        DoublyEven.const_mul (p.ν * p.γ) (hpow1.mul hD2_DE)
    simpa [G] using hterm1.add hterm2
  have hG_src : ∀ x ∈ Icc (0 : ℝ) 1,
      G x =
        srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀) t x := by
    intro x hx
    have hdu : heatDu u₀ t x = deriv (deriv Ucos) x := by
      rw [hU_fun]
      exact heatDu_eq_heatValue_secondDeriv hu₀_bound ht
    have hd2 : heatD2u u₀ t x = D2cos x := by
      simp [D2cos, heatD2u, if_pos ht, mul_assoc]
    simp [G, srcSlice2, hU_agree x hx, hdu, hd2, mul_assoc]
  exact intervalWeakH2Neumann_of_doublyEven_agree hG_C2 hG_DE hG_src

/-- Uniform `L¹` bound for the weak second derivative of the second
time-derivative heat-level source slice on a positive-time tail. -/
theorem heatLevel0_srcSlice2_second_abs_integral_tail_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ a : ℝ}
    (ha : 0 < a)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x) :
    ∃ B₂ : ℝ, 0 ≤ B₂ ∧ ∀ t : ℝ, (ht : a ≤ t) →
      (∫ x in (0 : ℝ)..1,
        |(heatLevel0_srcSlice2_weakH2 (p := p) hu₀_bound hu₀_cont
          (lt_of_lt_of_le ha ht)
          (fun y hy =>
            ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
              (p := p) hu₀_cont hu₀_pos (lt_of_lt_of_le ha ht) hy)).secondDeriv x|)
        ≤ B₂ := by
  obtain ⟨B, hBnn, hB⟩ :=
    heatLevel0_srcSlice2_source_iteratedFDeriv_two_tail_bound ha
      hu₀_bound hu₀_cont hu₀_pos
  refine ⟨B, hBnn, ?_⟩
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le ha ht
  let hpos : ∀ y ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) y :=
    fun y hy =>
      ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
        (p := p) hu₀_cont hu₀_pos htpos hy
  let H := heatLevel0_srcSlice2_weakH2 (p := p) hu₀_bound hu₀_cont htpos hpos
  set Ucos : ℝ → ℝ := fun y => ∑' k : ℕ,
    (Real.exp (-t * unitIntervalCosineEigenvalue k) *
      cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k y with hUcos
  set D2cos : ℝ → ℝ := fun y => ∑' k : ℕ,
    (unitIntervalCosineEigenvalue k ^ 2 *
      (Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k)) * cosineMode k y with hD2cos
  set G : ℝ → ℝ := fun y =>
    p.ν * p.γ * (p.γ - 1) * Ucos y ^ (p.γ - 1 - 1) *
        (deriv (deriv Ucos) y) ^ (2 : ℕ)
      + p.ν * p.γ * Ucos y ^ (p.γ - 1) * D2cos y with hG
  have hU_C4 : ContDiff ℝ 4 Ucos := by
    simpa [Ucos] using heatSemigroup_contDiff_four hu₀_bound htpos
  have hU_DE : DoublyEven Ucos := by
    simpa [Ucos] using doublyEven_cosineSeries
      (fun k => Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k)
  have hU_agree : ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 t) x = Ucos x := by
    intro x hx
    have h := ShenWork.IntervalPicardIterateRepresentation.hagree_zero
      p u₀ htpos hu₀_cont hu₀_bound hx
    simpa [Ucos, ShenWork.IntervalPicardIterateRepresentation.iterateReprCoeff] using h
  have hU_pos_all : ∀ x : ℝ, 0 < Ucos x :=
    hU_DE.pos_of_pos_Icc (fun x hx => by
      rw [← hU_agree x hx]
      exact hpos x hx)
  have hU_fun : Ucos =
      fun x : ℝ => unitIntervalCosineHeatValue t
        (cosineCoeffs (intervalDomainLift u₀)) x := by
    funext x
    have h := ShenWork.Paper2.unitIntervalCosineHeatValue_eq_cosineCoeffSeries
      t (cosineCoeffs (intervalDomainLift u₀)) x
    simpa [Ucos] using h.symm
  have hU3 : ContDiff ℝ 3 (deriv Ucos) := by
    simpa using (hU_C4.deriv' : ContDiff ℝ 3 (deriv Ucos))
  have hUdd_C2 : ContDiff ℝ 2 (deriv (deriv Ucos)) := by
    simpa using (hU3.deriv' : ContDiff ℝ 2 (deriv (deriv Ucos)))
  have hUdd_DE : DoublyEven (deriv (deriv Ucos)) := hU_DE.deriv_deriv
  have hD2_C2 : ContDiff ℝ 2 D2cos := by
    simpa [D2cos, heatD2u, if_pos htpos, mul_assoc] using
      heatD2u_contDiff_two hu₀_bound htpos
  have hD2_DE : DoublyEven D2cos := by
    simpa [D2cos] using doublyEven_cosineSeries
      (fun k => unitIntervalCosineEigenvalue k ^ 2 *
        (Real.exp (-t * unitIntervalCosineEigenvalue k) *
          cosineCoeffs (intervalDomainLift u₀) k))
  have hG_C2 : ContDiff ℝ 2 G := by
    have hU_ne : ∀ x, Ucos x ≠ 0 := fun x => ne_of_gt (hU_pos_all x)
    have hpow2 : ContDiff ℝ 2 (fun x => Ucos x ^ (p.γ - 1 - 1)) :=
      (hU_C4.of_le (by norm_num)).rpow_const_of_ne hU_ne
    have hpow1 : ContDiff ℝ 2 (fun x => Ucos x ^ (p.γ - 1)) :=
      (hU_C4.of_le (by norm_num)).rpow_const_of_ne hU_ne
    have hterm1 : ContDiff ℝ 2 (fun x =>
        p.ν * p.γ * (p.γ - 1) * Ucos x ^ (p.γ - 1 - 1) *
          (deriv (deriv Ucos) x) ^ (2 : ℕ)) := by
      have hconst : ContDiff ℝ 2
          (fun _ : ℝ => p.ν * p.γ * (p.γ - 1)) := contDiff_const
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
        ((hconst.mul hpow2).mul (hUdd_C2.mul hUdd_C2))
    have hterm2 : ContDiff ℝ 2 (fun x =>
        p.ν * p.γ * Ucos x ^ (p.γ - 1) * D2cos x) := by
      have hconst : ContDiff ℝ 2 (fun _ : ℝ => p.ν * p.γ) := contDiff_const
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ((hconst.mul hpow1).mul hD2_C2)
    simpa [G] using hterm1.add hterm2
  have hG_DE : DoublyEven G := by
    have hpow2 : DoublyEven (fun x => Ucos x ^ (p.γ - 1 - 1)) :=
      hU_DE.comp (fun y => y ^ (p.γ - 1 - 1))
    have hpow1 : DoublyEven (fun x => Ucos x ^ (p.γ - 1)) :=
      hU_DE.comp (fun y => y ^ (p.γ - 1))
    have hsq : DoublyEven (fun x => (deriv (deriv Ucos) x) ^ (2 : ℕ)) := by
      simpa [pow_two] using hUdd_DE.mul hUdd_DE
    have hterm1 : DoublyEven (fun x =>
        p.ν * p.γ * (p.γ - 1) * Ucos x ^ (p.γ - 1 - 1) *
          (deriv (deriv Ucos) x) ^ (2 : ℕ)) := by
      simpa [mul_assoc] using
        DoublyEven.const_mul (p.ν * p.γ * (p.γ - 1)) (hpow2.mul hsq)
    have hterm2 : DoublyEven (fun x =>
        p.ν * p.γ * Ucos x ^ (p.γ - 1) * D2cos x) := by
      simpa [mul_assoc] using
        DoublyEven.const_mul (p.ν * p.γ) (hpow1.mul hD2_DE)
    simpa [G] using hterm1.add hterm2
  have hG_src : ∀ x ∈ Icc (0 : ℝ) 1,
      G x =
        srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀) t x := by
    intro x hx
    have hdu : heatDu u₀ t x = deriv (deriv Ucos) x := by
      rw [hU_fun]
      exact heatDu_eq_heatValue_secondDeriv hu₀_bound htpos
    have hd2 : heatD2u u₀ t x = D2cos x := by
      simp [D2cos, heatD2u, if_pos htpos, mul_assoc]
    simp [G, srcSlice2, hU_agree x hx, hdu, hd2, mul_assoc]
  have hH_eq : H.secondDeriv = deriv (deriv G) := by
    simpa [H, G, Ucos, D2cos, heatLevel0_srcSlice2_weakH2] using
      intervalWeakH2Neumann_of_doublyEven_agree_secondDeriv hG_C2 hG_DE hG_src
  have hpoint : ∀ x : ℝ, |H.secondDeriv x| ≤ B := by
    intro x
    rw [hH_eq]
    have hb := hB t ht x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hb
    simpa [G, Ucos, D2cos, iteratedDeriv_eq_iterate] using hb
  have hint : IntervalIntegrable (fun x => |H.secondDeriv x|)
      MeasureTheory.volume (0 : ℝ) 1 := by
    simpa [Real.norm_eq_abs] using H.second_intervalIntegrable.norm
  have hconst : IntervalIntegrable (fun _ : ℝ => B) MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_const
  have hle :
      (∫ x in (0 : ℝ)..1, |H.secondDeriv x|)
        ≤ ∫ x in (0 : ℝ)..1, B := by
    refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      hint hconst ?_
    intro x _hx
    exact hpoint x
  calc
    (∫ x in (0 : ℝ)..1,
        |(heatLevel0_srcSlice2_weakH2 (p := p) hu₀_bound hu₀_cont
          (lt_of_lt_of_le ha ht)
          (fun y hy =>
            ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
              (p := p) hu₀_cont hu₀_pos (lt_of_lt_of_le ha ht) hy)).secondDeriv x|)
        = ∫ x in (0 : ℝ)..1, |H.secondDeriv x| := by
          rfl
    _ ≤ ∫ x in (0 : ℝ)..1, B := hle
    _ = B := by simp

/-- Tail-uniform quadratic coefficient decay of the second time-derivative
heat-level source slice. -/
theorem heatLevel0_srcSlice2_quadratic_decay_tail
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ a : ℝ}
    (ha : 0 < a)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, a ≤ t → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs
        (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀) t) k|
        ≤ C / ((k : ℝ) * Real.pi) ^ 2 := by
  obtain ⟨B₂, hB₂nn, hB₂⟩ :=
    heatLevel0_srcSlice2_second_abs_integral_tail_bound ha
      hu₀_bound hu₀_cont hu₀_pos
  refine ⟨2 * B₂, by positivity, ?_⟩
  intro t ht k hk
  have htpos : 0 < t := lt_of_lt_of_le ha ht
  let hpos : ∀ y ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) y :=
    fun y hy =>
      ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
        (p := p) hu₀_cont hu₀_pos htpos hy
  let H := heatLevel0_srcSlice2_weakH2 (p := p) hu₀_bound hu₀_cont htpos hpos
  exact
    ShenWork.IntervalSourceDecayQuantitative.intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound
      H (by simpa [H] using hB₂ t ht) k hk

/-- Fixed-time quadratic coefficient decay of the second time-derivative source
slice. -/
theorem heatLevel0_srcSlice2_quadratic_decay
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ t : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (ht : 0 < t)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs
        (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀) t) k|
        ≤ C / ((k : ℝ) * Real.pi) ^ 2 := by
  exact ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_cosineCoeff_quadratic_decay
    (heatLevel0_srcSlice2_weakH2 hu₀_bound hu₀_cont ht hpos)

/-- Window-uniform quadratic decay of the second time-derivative heat-level source
slice from a window-uniform `L¹` bound on its weak second derivative. -/
theorem heatLevel0_srcSlice2_quadratic_decay_window_of_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ a b B₂ : ℝ}
    (ha : 0 < a)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hpos : ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (hB₂ : ∀ t (ht : t ∈ Icc a b),
      (∫ x in (0 : ℝ)..1,
        |(heatLevel0_srcSlice2_weakH2 hu₀_bound hu₀_cont
          (lt_of_lt_of_le ha ht.1) (hpos t ht)).secondDeriv x|)
        ≤ B₂) :
    ∀ t ∈ Icc a b, ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs
        (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀) t) k|
        ≤ 2 * B₂ / ((k : ℝ) * Real.pi) ^ 2 := by
  intro t ht k hk
  let H := heatLevel0_srcSlice2_weakH2 hu₀_bound hu₀_cont
    (lt_of_lt_of_le ha ht.1) (hpos t ht)
  exact
    ShenWork.IntervalSourceDecayQuantitative.intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound
      H (by simpa [H] using hB₂ t ht) k hk

end ShenWork.Paper2.HeatLevel0SourceDecay

end -- noncomputable section
