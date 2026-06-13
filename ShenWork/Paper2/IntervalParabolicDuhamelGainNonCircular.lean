import ShenWork.Paper2.IntervalSpatialC6Certificate
import ShenWork.Paper2.IntervalChiNegSourceTail

open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1 duhamelSpectralCoeff duhamelSpectral_eq_cosineSeries)
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.Paper2.ParabolicGainInduction
open ShenWork.Paper2.SpatialC6Certificate
open ShenWork.Paper2.ChiNegSourceTail
open ShenWork.Paper2.CD6CosineModeBounds
open ShenWork.IntervalResolverTimeRegularity (ResolverHasSpectralAgreement)
open ShenWork.IntervalResolverJointC2 (ResolverHasSpectralAgreementC2Coeff)
open ShenWork.Paper2.PicardLimitK1 (LocalRestart)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.Paper2.ParabolicDuhamelGainNonCircular

/-- A time-`C¹` Duhamel source with one eigenvalue of spatial coefficient
summability.  This is the coefficient form of the lower half of the
`spatial-C^(k-1)` input for the `k = 2, 3` gain steps. -/
structure DuhamelSourceSpatialWeightOne (a : ℝ → ℕ → ℝ) where
  toTimeC1 : DuhamelSourceTimeC1 a
  sourceEigenEnvelope : ℕ → ℝ
  sourceEigen_nonneg : ∀ n, 0 ≤ sourceEigenEnvelope n
  sourceEigen_summable : Summable sourceEigenEnvelope
  sourceEigen_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n * |a s n| ≤ sourceEigenEnvelope n
  adotEigenEnvelope : ℕ → ℝ
  adotEigen_nonneg : ∀ n, 0 ≤ adotEigenEnvelope n
  adotEigen_summable : Summable adotEigenEnvelope
  adotEigen_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n * |toTimeC1.adot s n| ≤
      adotEigenEnvelope n

/-- A time-`C¹` Duhamel source with two eigenvalue weights of spatial coefficient
summability.  This is the coefficient form of the higher half of the
`spatial-C^(k-1)` input for the `k = 4, 5` gain steps. -/
structure DuhamelSourceSpatialWeightTwo (a : ℝ → ℕ → ℝ) where
  toTimeC1 : DuhamelSourceTimeC1 a
  sourceEigenSqEnvelope : ℕ → ℝ
  sourceEigenSq_nonneg : ∀ n, 0 ≤ sourceEigenSqEnvelope n
  sourceEigenSq_summable : Summable sourceEigenSqEnvelope
  sourceEigenSq_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n * |a s n|) ≤
        sourceEigenSqEnvelope n
  adotEigenSqEnvelope : ℕ → ℝ
  adotEigenSq_nonneg : ∀ n, 0 ≤ adotEigenSqEnvelope n
  adotEigenSq_summable : Summable adotEigenSqEnvelope
  adotEigenSq_bound : ∀ s, 0 ≤ s → ∀ n,
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n * |toTimeC1.adot s n|) ≤
        adotEigenSqEnvelope n

/-- Concrete Duhamel representation for one closed interval slice.  The two
producer fields consume the spatial slice hypothesis, so the gain atom does not
ask for any coefficient-`C²` package. -/
structure DuhamelGainSliceData
    (k : ℕ) (g w : intervalDomainPoint → ℝ) where
  a : ℝ → ℕ → ℝ
  τ : ℝ
  hτ : 0 < τ
  eqOn :
    Set.EqOn (intervalDomainLift w)
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..τ, unitIntervalCosineHeatValue (τ - s) (a s) x)
      (Set.Icc (0 : ℝ) 1)
  lowSource :
    k = 2 ∨ k = 3 →
      SpatialSlice (k - 1) g → DuhamelSourceSpatialWeightOne a
  highSource :
    k = 4 ∨ k = 5 →
      SpatialSlice (k - 1) g → DuhamelSourceSpatialWeightTwo a

private theorem eigenEnvelope_le_tsum
    {E : ℕ → ℝ} (hE : Summable E) (hEnn : ∀ n, 0 ≤ E n) (n : ℕ) :
    E n ≤ ∑' m, E m := by
  have hsingle := hE.sum_le_tsum ({n} : Finset ℕ) (fun m _hm => hEnn m)
  simpa using hsingle

def DuhamelSourceSpatialWeightOne.toWeightedTimeC1
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceSpatialWeightOne a) :
    DuhamelSourceTimeC1
      (fun s n => unitIntervalCosineEigenvalue n * a s n) where
  adot := fun s n =>
    unitIntervalCosineEigenvalue n * src.toTimeC1.adot s n
  hderiv := by
    intro s n
    exact (src.toTimeC1.hderiv s n).const_mul
      (unitIntervalCosineEigenvalue n)
  hadotcont := by
    intro n
    exact (src.toTimeC1.hadotcont n).const_mul
      (unitIntervalCosineEigenvalue n)
  envelope := src.sourceEigenEnvelope
  henv_summable := src.sourceEigen_summable
  henv_bound := by
    intro s hs n
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    rw [abs_mul, abs_of_nonneg hlam]
    exact src.sourceEigen_bound s hs n
  derivBound := ∑' n, src.adotEigenEnvelope n
  hderivBound := by
    intro s hs n
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    rw [abs_mul, abs_of_nonneg hlam]
    exact le_trans (src.adotEigen_bound s hs n)
      (eigenEnvelope_le_tsum src.adotEigen_summable src.adotEigen_nonneg n)

def DuhamelSourceSpatialWeightTwo.toWeightedTimeC1
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceSpatialWeightTwo a) :
    DuhamelSourceTimeC1
      (fun s n =>
        unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n * a s n)) where
  adot := fun s n =>
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n * src.toTimeC1.adot s n)
  hderiv := by
    intro s n
    exact ((src.toTimeC1.hderiv s n).const_mul
      (unitIntervalCosineEigenvalue n)).const_mul
      (unitIntervalCosineEigenvalue n)
  hadotcont := by
    intro n
    exact ((src.toTimeC1.hadotcont n).const_mul
      (unitIntervalCosineEigenvalue n)).const_mul
      (unitIntervalCosineEigenvalue n)
  envelope := src.sourceEigenSqEnvelope
  henv_summable := src.sourceEigenSq_summable
  henv_bound := by
    intro s hs n
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    rw [abs_mul, abs_of_nonneg hlam, abs_mul, abs_of_nonneg hlam]
    exact src.sourceEigenSq_bound s hs n
  derivBound := ∑' n, src.adotEigenSqEnvelope n
  hderivBound := by
    intro s hs n
    have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    rw [abs_mul, abs_of_nonneg hlam, abs_mul, abs_of_nonneg hlam]
    exact le_trans (src.adotEigenSq_bound s hs n)
      (eigenEnvelope_le_tsum src.adotEigenSq_summable src.adotEigenSq_nonneg n)

private theorem duhamelSpectralCoeff_weight_one
    {a : ℝ → ℕ → ℝ} (τ : ℝ) (n : ℕ) :
    duhamelSpectralCoeff
        (fun s n => unitIntervalCosineEigenvalue n * a s n) τ n
      =
    unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a τ n := by
  unfold duhamelSpectralCoeff
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _hs
  ring

private theorem duhamelSpectralCoeff_weight_two
    {a : ℝ → ℕ → ℝ} (τ : ℝ) (n : ℕ) :
    duhamelSpectralCoeff
        (fun s n =>
          unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n * a s n)) τ n
      =
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a τ n) := by
  unfold duhamelSpectralCoeff
  rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _hs
  ring

theorem duhamelSpectralCoeff_eigenvalue_sq_summable_of_spatialWeightOne
    {τ : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceSpatialWeightOne a) (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          |duhamelSpectralCoeff a τ n|)) := by
  have hS :=
    ShenWork.IntervalDuhamelClosedC2.duhamelSpectralCoeff_eigenvalue_summable
      (a := fun s n => unitIntervalCosineEigenvalue n * a s n)
      src.toWeightedTimeC1 hτ
  refine hS.congr (fun n => ?_)
  have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue
    positivity
  rw [duhamelSpectralCoeff_weight_one τ n]
  rw [abs_mul, abs_of_nonneg hlam]

theorem duhamelSpectralCoeff_eigenvalue_cube_summable_of_spatialWeightTwo
    {τ : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceSpatialWeightTwo a) (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            |duhamelSpectralCoeff a τ n|))) := by
  have hS :=
    ShenWork.IntervalDuhamelClosedC2.duhamelSpectralCoeff_eigenvalue_summable
      (a := fun s n =>
        unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n * a s n))
      src.toWeightedTimeC1 hτ
  refine hS.congr (fun n => ?_)
  have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue
    positivity
  rw [duhamelSpectralCoeff_weight_two τ n]
  rw [abs_mul, abs_of_nonneg hlam, abs_mul, abs_of_nonneg hlam]

theorem cosineCoeffSeries_contDiff_four_of_eigenvalue_sq_summable
    {b : ℕ → ℝ}
    (hb : Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n * |b n|))) :
    ContDiff ℝ 4 (fun x : ℝ => ∑' n : ℕ, b n * cosineMode n x) := by
  let v : ℕ → ℕ → ℝ := fun _ n =>
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n * |b n|)
  refine contDiff_tsum_of_eventually
    (f := fun n x => b n * cosineMode n x) (v := v)
    (N := (4 : ℕ∞)) ?_ ?_ ?_
  · intro n
    unfold cosineMode
    fun_prop
  · intro k _hk
    simpa [v] using hb
  · intro k hk
    filter_upwards [Filter.eventually_cofinite_ne 0] with n hn x
    have hk_nat : k ≤ 4 := by exact_mod_cast hk
    have hcd : ContDiffAt ℝ (k : WithTop ℕ∞) (cosineMode n) x := by
      unfold cosineMode
      fun_prop
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_const_mul (b n) hcd, Real.norm_eq_abs, abs_mul]
    have hmode : |iteratedDeriv k (cosineMode n) x| ≤
        |(n : ℝ) * Real.pi| ^ k := by
      simpa [cosineMode, unitIntervalCosineMode,
        norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
        using unitIntervalCosineMode_iteratedFDeriv_bound k n x
    have hfreq1 : (1 : ℝ) ≤ |(n : ℝ) * Real.pi| := by
      have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) Real.pi_pos.le)]
      nlinarith [Real.two_le_pi, hn1]
    have hpow : |(n : ℝ) * Real.pi| ^ k ≤
        |(n : ℝ) * Real.pi| ^ (4 : ℕ) :=
      pow_le_pow_right₀ hfreq1 hk_nat
    have hlam : unitIntervalCosineEigenvalue n =
        |(n : ℝ) * Real.pi| ^ (2 : ℕ) := by
      unfold unitIntervalCosineEigenvalue
      rw [sq_abs]
    calc |b n| * |iteratedDeriv k (cosineMode n) x|
        ≤ |b n| * |(n : ℝ) * Real.pi| ^ k :=
          mul_le_mul_of_nonneg_left hmode (abs_nonneg _)
      _ ≤ |b n| * |(n : ℝ) * Real.pi| ^ (4 : ℕ) :=
          mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
      _ = v k n := by
          dsimp [v]
          rw [hlam]
          ring

theorem intervalDuhamelTerm_contDiff_four_of_spatialWeightOne_timeC1
    {τ : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceSpatialWeightOne a) (hτ : 0 < τ) :
    ContDiff ℝ 4
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..τ,
          unitIntervalCosineHeatValue (τ - s) (a s) x) := by
  have hseries : ContDiff ℝ 4
      (fun x : ℝ =>
        ∑' n : ℕ, duhamelSpectralCoeff a τ n * cosineMode n x) :=
    cosineCoeffSeries_contDiff_four_of_eigenvalue_sq_summable
      (duhamelSpectralCoeff_eigenvalue_sq_summable_of_spatialWeightOne
        src hτ)
  have hEq :
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..τ,
          unitIntervalCosineHeatValue (τ - s) (a s) x)
        =
      (fun x : ℝ =>
        ∑' n : ℕ, duhamelSpectralCoeff a τ n * cosineMode n x) := by
    funext x
    exact duhamelSpectral_eq_cosineSeries src.toTimeC1 hτ
  rwa [hEq]

theorem intervalDuhamelTerm_contDiff_six_of_spatialWeightTwo_timeC1
    {τ : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceSpatialWeightTwo a) (hτ : 0 < τ) :
    ContDiff ℝ 6
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..τ,
          unitIntervalCosineHeatValue (τ - s) (a s) x) := by
  have hseries : ContDiff ℝ 6
      (fun x : ℝ =>
        ∑' n : ℕ, duhamelSpectralCoeff a τ n * cosineMode n x) :=
    cosineCoeffSeries_contDiff_six_of_eigenvalue_cube_summable
      (duhamelSpectralCoeff_eigenvalue_cube_summable_of_spatialWeightTwo
        src hτ)
  have hEq :
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..τ,
          unitIntervalCosineHeatValue (τ - s) (a s) x)
        =
      (fun x : ℝ =>
        ∑' n : ℕ, duhamelSpectralCoeff a τ n * cosineMode n x) := by
    funext x
    exact duhamelSpectral_eq_cosineSeries src.toTimeC1 hτ
  rwa [hEq]

theorem duhamelTerm_spatial_contDiff_three_of_spatialC1_timeC1
    {τ : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceSpatialWeightOne a) (hτ : 0 < τ) :
    ContDiff ℝ 3
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..τ,
          unitIntervalCosineHeatValue (τ - s) (a s) x) :=
  (intervalDuhamelTerm_contDiff_four_of_spatialWeightOne_timeC1
    src hτ).of_le (by norm_num)

theorem duhamelTerm_spatial_contDiff_four_of_spatialC2_timeC1
    {τ : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceSpatialWeightOne a) (hτ : 0 < τ) :
    ContDiff ℝ 4
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..τ,
          unitIntervalCosineHeatValue (τ - s) (a s) x) :=
  intervalDuhamelTerm_contDiff_four_of_spatialWeightOne_timeC1 src hτ

theorem duhamelTerm_spatial_contDiff_five_of_spatialC3_timeC1
    {τ : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceSpatialWeightTwo a) (hτ : 0 < τ) :
    ContDiff ℝ 5
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..τ,
          unitIntervalCosineHeatValue (τ - s) (a s) x) :=
  (intervalDuhamelTerm_contDiff_six_of_spatialWeightTwo_timeC1
    src hτ).of_le (by norm_num)

theorem duhamelTerm_spatial_contDiff_six_of_spatialC4_timeC1
    {τ : ℝ} {a : ℝ → ℕ → ℝ}
    (src : DuhamelSourceSpatialWeightTwo a) (hτ : 0 < τ) :
    ContDiff ℝ 6
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..τ,
          unitIntervalCosineHeatValue (τ - s) (a s) x) :=
  intervalDuhamelTerm_contDiff_six_of_spatialWeightTwo_timeC1 src hτ

theorem duhamelGainsTwo
    {U F : ℕ → intervalDomainPoint → ℝ}
    (data : ∀ k, 2 ≤ k → k < 6 →
      DuhamelGainSliceData k (F k) (U (k + 1))) :
    ∀ k, 2 ≤ k → k < 6 →
      SpatialSlice (k - 1) (F k) → SpatialSlice (k + 1) (U (k + 1)) := by
  intro k hk2 hk6 hF
  have hk : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases hk with rfl | rfl | rfl | rfl
  · let D := data 2 (by norm_num) (by norm_num)
    have hcd :=
      duhamelTerm_spatial_contDiff_three_of_spatialC1_timeC1
        (D.lowSource (Or.inl rfl) hF) D.hτ
    simpa [SpatialSlice] using hcd.contDiffOn.congr D.eqOn
  · let D := data 3 (by norm_num) (by norm_num)
    have hcd :=
      duhamelTerm_spatial_contDiff_four_of_spatialC2_timeC1
        (D.lowSource (Or.inr rfl) hF) D.hτ
    simpa [SpatialSlice] using hcd.contDiffOn.congr D.eqOn
  · let D := data 4 (by norm_num) (by norm_num)
    have hcd :=
      duhamelTerm_spatial_contDiff_five_of_spatialC3_timeC1
        (D.highSource (Or.inl rfl) hF) D.hτ
    simpa [SpatialSlice] using hcd.contDiffOn.congr D.eqOn
  · let D := data 5 (by norm_num) (by norm_num)
    have hcd :=
      duhamelTerm_spatial_contDiff_six_of_spatialC4_timeC1
        (D.highSource (Or.inr rfl) hF) D.hτ
    simpa [SpatialSlice] using hcd.contDiffOn.congr D.eqOn

def assembleParabolicGainAtomsNonCircular
    {U V F : ℕ → intervalDomainPoint → ℝ}
    (baseC2 : SpatialSlice 2 (U 2))
    (resolverAhead :
      ∀ k, 2 ≤ k → k < 6 → SpatialSlice (k + 1) (V k))
    (chemDivLosesOne :
      ∀ k, 2 ≤ k → k < 6 →
        CoupledSlice k (U k) (V k) → SpatialSlice (k - 1) (F k))
    (data : ∀ k, 2 ≤ k → k < 6 →
      DuhamelGainSliceData k (F k) (U (k + 1))) :
    ParabolicGainAtoms U V F where
  baseC2 := baseC2
  resolverAhead := resolverAhead
  chemDivLosesOne := chemDivLosesOne
  duhamelGainsTwo := duhamelGainsTwo data

theorem assembledAtoms_climb_C2_to_C6_nonCircular
    {U V F : ℕ → intervalDomainPoint → ℝ}
    (baseC2 : SpatialSlice 2 (U 2))
    (resolverAhead :
      ∀ k, 2 ≤ k → k < 6 → SpatialSlice (k + 1) (V k))
    (chemDivLosesOne :
      ∀ k, 2 ≤ k → k < 6 →
        CoupledSlice k (U k) (V k) → SpatialSlice (k - 1) (F k))
    (data : ∀ k, 2 ≤ k → k < 6 →
      DuhamelGainSliceData k (F k) (U (k + 1))) :
    SpatialSlice 6 (U 6) :=
  intervalIterate_contDiff_six
    (assembleParabolicGainAtomsNonCircular
      baseC2 resolverAhead chemDivLosesOne data)

theorem chiNeg_close_of_nonCircular_climb
    {U V F : ℕ → intervalDomainPoint → ℝ}
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (baseC2 : SpatialSlice 2 (U 2))
    (resolverAhead :
      ∀ k, 2 ≤ k → k < 6 → SpatialSlice (k + 1) (V k))
    (chemDivLosesOne :
      ∀ k, 2 ≤ k → k < 6 →
        CoupledSlice k (U k) (V k) → SpatialSlice (k - 1) (F k))
    (data : ∀ k, 2 ≤ k → k < 6 →
      DuhamelGainSliceData k (F k) (U (k + 1)))
    (H : ResolverHasSpectralAgreement T u)
    (mkL : ∀ σ, 0 < σ → σ < T → LocalRestart p u T σ)
    (C0 C C0dot Cdot : ℝ → ℝ)
    (hC6 : ∀ σ, 0 ≤ max (C0 σ) (64 * C σ))
    (hCdot6 : ∀ σ, 0 ≤ max (C0dot σ) (64 * Cdot σ))
    (tailOfC6 : SpatialSlice 6 (U 6) →
      ∀ σ (hσ0 : 0 < σ) (hσT : σ < T),
        SourceEigenCubeTailFields
          (mkL σ hσ0 hσT) (C0 σ) (C σ) (C0dot σ) (Cdot σ)) :
    ResolverHasSpectralAgreementC2Coeff T u := by
  have hU6 : SpatialSlice 6 (U 6) :=
    assembledAtoms_climb_C2_to_C6_nonCircular
      baseC2 resolverAhead chemDivLosesOne data
  exact resolverHasSpectralAgreementC2Coeff_of_eigenCubeTail
    H mkL C0 C C0dot Cdot hC6 hCdot6 (tailOfC6 hU6)

#print axioms duhamelGainsTwo
#print axioms assembledAtoms_climb_C2_to_C6_nonCircular
#print axioms chiNeg_close_of_nonCircular_climb

end ShenWork.Paper2.ParabolicDuhamelGainNonCircular
