/-
  ShenWork/Paper2/IntervalResolverPowerDecay.lean

  **R-Hvsrc-1: window-uniform quadratic decay for the power source `ν·u^γ`.**

  The clamped resolver-source witness
  (`ResolverSourceClampedWitness.clampedResolverSource_duhamelSourceTimeC1`)
  consumes a SINGLE constant `C` controlling the cosine coefficients of
  `x ↦ ν·(lift (D.u σ) x)^γ` uniformly over the clamp window `σ ∈ [c', d']`
  (the `hdecay`/`ha0` inputs).  This file produces that single `C`.

  Mirroring the logistic explicit envelope
  (`IntervalLogisticSourceQuantBound.logisticSourceFun_cosineCoeff_quadratic_decay_explicit`,
  whose constant `B_log` is built from the K2 window data `(M, G1, G2)`), the
  power source has the explicit pointwise second-derivative

      (ν·u^γ)'' = ν·γ·(γ−1)·u^{γ−2}·(u')²  +  ν·γ·u^{γ−1}·u'',

  so under `0 < m ≤ u ≤ M` on `[0,1]`, `|u'| ≤ G1`, `|u''| ≤ G2`,

      |(ν·u^γ)''| ≤ ν·γ·|γ−1|·P₂·G1²  +  ν·γ·P₁·G2  =:  B_pow,

  where `P₂ = max (m^{γ−2}) (M^{γ−2})` and `P₁ = max (m^{γ−1}) (M^{γ−1})`
  uniformly dominate `u^{γ−2}` and `u^{γ−1}` for `m ≤ u ≤ M` (the negative
  exponent `γ−2 < 0` is handled by `Real.rpow_le_rpow_of_nonpos`, which is why
  a positive LOWER bound `m` is required — the logistic side never needs one
  because `α ≥ 1` keeps every exponent nonnegative).

  Then `∫₀¹ |(ν·u^γ)''| ≤ B_pow` (constant over the unit interval) and the
  weak-`H²_N` quantitative decay
  (`IntervalSourceDecayQuantitative.intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound`)
  gives `|cosineCoeffs (ν·u^γ) k| ≤ 2·B_pow / ((k:ℝ)·π)²` for `k ≥ 1`.

  The window-uniform constant `C := max (2·B_pow) (ν·P_M^γ-ish zeroth sup-bound)`
  is read off from the K2 window data and a window-uniform positive LOWER bound
  `m` on the lift (obtained from joint continuity + compactness, the same
  `IsCompact.exists_isMinOn` route as `lift_u_uniformPositive_on_compact`).

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.PDE.IntervalMildSourceDecayHelper
import ShenWork.PDE.IntervalSourceDecayQuantitative
import ShenWork.Paper2.IntervalMildPicardRegularity
import ShenWork.Paper2.IntervalDomainLimitSourceRepresentation
import ShenWork.Paper2.IntervalDomainL2StaticVDifference

open MeasureTheory
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.PDE.IntervalMildSourceDecayHelper
open ShenWork.IntervalMildPicardRegularity
open ShenWork.IntervalEllipticCharacterization
  (intervalIntegrable_deriv_deriv_of_contDiffOn_two)
open ShenWork.IntervalDomainLimitSourceRepresentation (le_on_Icc_of_le_on_Ioo)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)

noncomputable section

namespace ShenWork.Paper2.ResolverPowerDecay

/-- The explicit pointwise second-derivative bound constant for the power source
`ν·u^γ` on `[0,1]` under `0 < m ≤ u ≤ M`, `|u'| ≤ G1`, `|u''| ≤ G2`. -/
def B_pow (ν γ M m G1 G2 : ℝ) : ℝ :=
  ν * γ * |γ - 1| * max (m ^ (γ - 2)) (M ^ (γ - 2)) * G1 ^ 2
    + ν * γ * max (m ^ (γ - 1)) (M ^ (γ - 1)) * G2

/-- The explicit first-derivative function of the power source where `u > 0`:
`(ν·u^γ)' = ν·γ·u^{γ−1}·u'`. -/
def Fp1 (ν γ : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun x => ν * γ * u x ^ (γ - 1) * deriv u x

/-- The explicit second-derivative function of the power source where `u > 0`:
`(ν·u^γ)'' = ν·γ·(γ−1)·u^{γ−2}·(u')² + ν·γ·u^{γ−1}·u''`. -/
def Fp2 (ν γ : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    ν * γ * (γ - 1) * u x ^ (γ - 2) * (deriv u x) ^ 2
      + ν * γ * u x ^ (γ - 1) * deriv (deriv u) x

/-- First derivative of the power source where `u x > 0` (globally, using
`ContDiff ℝ 2 u`). -/
theorem powerSourceFun_hasDerivAt
    {ν γ : ℝ} {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) {x : ℝ} (hx : 0 < u x) :
    HasDerivAt (fun y => ν * u y ^ γ) (Fp1 ν γ u x) x := by
  have hux_ne : u x ≠ 0 := ne_of_gt hx
  have hu_diff : HasDerivAt u (deriv u x) x :=
    (hu.differentiable (by norm_num) x).hasDerivAt
  -- d/dx u^γ = γ·u^{γ−1}·u'
  have hpow : HasDerivAt (fun y => u y ^ γ)
      (deriv u x * γ * u x ^ (γ - 1)) x :=
    hu_diff.rpow_const (Or.inl hux_ne)
  have hmul := hpow.const_mul ν
  refine hmul.congr_deriv ?_
  simp only [Fp1]; ring

/-- Second derivative of `Fp1` (= first derivative of the source's derivative)
where `u x > 0`. -/
theorem Fp1_hasDerivAt
    {ν γ : ℝ} {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) {x : ℝ} (hx : 0 < u x) :
    HasDerivAt (Fp1 ν γ u) (Fp2 ν γ u x) x := by
  have hux_ne : u x ≠ 0 := ne_of_gt hx
  -- u' is differentiable (u is C²)
  have hu'_has : HasDerivAt (deriv u) (deriv (deriv u) x) x := by
    have hC1 : ContDiff ℝ 1 (deriv u) := (contDiff_succ_iff_deriv.mp hu).2.2
    exact (hC1.differentiable (by norm_num) x).hasDerivAt
  have hu_has : HasDerivAt u (deriv u x) x :=
    (hu.differentiable (by norm_num) x).hasDerivAt
  -- d/dx u^{γ−1} = (γ−1)·u^{γ−2}·u'
  have hpow1 : HasDerivAt (fun y => u y ^ (γ - 1))
      (deriv u x * (γ - 1) * u x ^ (γ - 1 - 1)) x :=
    hu_has.rpow_const (Or.inl hux_ne)
  -- Fp1 = ν·γ · (u^{γ−1} · u') ; product rule
  have hprod0 : HasDerivAt (fun y => u y ^ (γ - 1) * deriv u y)
      (deriv u x * (γ - 1) * u x ^ (γ - 1 - 1) * deriv u x
        + u x ^ (γ - 1) * deriv (deriv u) x) x :=
    hpow1.mul hu'_has
  have hprod := hprod0.const_mul (ν * γ)
  have hfun : Fp1 ν γ u = fun y => ν * γ * (u y ^ (γ - 1) * deriv u y) := by
    funext y; simp only [Fp1]; ring
  rw [hfun]
  refine hprod.congr_deriv ?_
  have hexp : (γ - 1 - 1) = (γ - 2) := by ring
  simp only [Fp2, hexp]
  ring

/-- `Fp1` equals the genuine first derivative of the power source on `[0,1]`. -/
theorem deriv_powerSource_eq_Fp1
    {ν γ : ℝ} {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < u x)
    {x : ℝ} (hxmem : x ∈ Set.Icc (0 : ℝ) 1) :
    deriv (fun y => ν * u y ^ γ) x = Fp1 ν γ u x := by
  obtain ⟨U, hUopen, hKU, hUpos⟩ :=
    exists_pos_neighborhood_of_compact_positive hu.continuous isCompact_Icc hpos
  have hxU : x ∈ U := hKU hxmem
  exact (powerSourceFun_hasDerivAt hu (hUpos x hxU)).deriv

/-- The second derivative of the power source equals `Fp2` on `[0,1]`. -/
theorem secondDeriv_powerSource_eq_Fp2
    {ν γ : ℝ} {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < u x)
    {x : ℝ} (hxmem : x ∈ Set.Icc (0 : ℝ) 1) :
    deriv (deriv (fun y => ν * u y ^ γ)) x = Fp2 ν γ u x := by
  obtain ⟨U, hUopen, hKU, hUpos⟩ :=
    exists_pos_neighborhood_of_compact_positive hu.continuous isCompact_Icc hpos
  have hxU : x ∈ U := hKU hxmem
  -- deriv (power source) = Fp1 on a neighborhood of x
  have hderiv_eq : deriv (fun y => ν * u y ^ γ) =ᶠ[nhds x] Fp1 ν γ u := by
    filter_upwards [hUopen.mem_nhds hxU] with y hy
    exact (powerSourceFun_hasDerivAt hu (hUpos y hy)).deriv
  rw [Filter.EventuallyEq.deriv_eq hderiv_eq]
  exact (Fp1_hasDerivAt hu (hUpos x hxU)).deriv

/-- The uniform power dominates: for `0 < m ≤ z ≤ M` and any exponent `e`,
`z ^ e ≤ max (m ^ e) (M ^ e)`. -/
theorem rpow_le_max
    {m z M e : ℝ} (hm : 0 < m) (hmz : m ≤ z) (hzM : z ≤ M) :
    z ^ e ≤ max (m ^ e) (M ^ e) := by
  rcases le_or_gt 0 e with he | he
  · exact le_trans (Real.rpow_le_rpow (le_of_lt (lt_of_lt_of_le hm hmz)) hzM he)
      (le_max_right _ _)
  · exact le_trans (Real.rpow_le_rpow_of_nonpos hm hmz (le_of_lt he)) (le_max_left _ _)

/-- Pointwise bound `|Fp2| ≤ B_pow` on `[0,1]`. -/
theorem Fp2_abs_le_B_pow
    {ν γ M m G1 G2 : ℝ} {u : ℝ → ℝ}
    (hν : 0 ≤ ν) (hγ : 0 ≤ γ) (hm : 0 < m)
    (hlb : ∀ x ∈ Set.Icc (0 : ℝ) 1, m ≤ u x)
    (hub : ∀ x ∈ Set.Icc (0 : ℝ) 1, u x ≤ M)
    (hG1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv u x| ≤ G1)
    (hG2 : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv u) x| ≤ G2)
    {x : ℝ} (hxmem : x ∈ Set.Icc (0 : ℝ) 1) :
    |Fp2 ν γ u x| ≤ B_pow ν γ M m G1 G2 := by
  have hux_lb : m ≤ u x := hlb x hxmem
  have hux_ub : u x ≤ M := hub x hxmem
  have hux_pos : 0 < u x := lt_of_lt_of_le hm hux_lb
  have hG1x : |deriv u x| ≤ G1 := hG1 x hxmem
  have hG2x : |deriv (deriv u) x| ≤ G2 := hG2 x hxmem
  have hG1_nn : 0 ≤ G1 := le_trans (abs_nonneg _) hG1x
  have hG2_nn : 0 ≤ G2 := le_trans (abs_nonneg _) hG2x
  -- uniform power dominations
  have hP2 : u x ^ (γ - 2) ≤ max (m ^ (γ - 2)) (M ^ (γ - 2)) :=
    rpow_le_max hm hux_lb hux_ub
  have hP2_nn : 0 ≤ u x ^ (γ - 2) := Real.rpow_nonneg (le_of_lt hux_pos) _
  have hmaxP2_nn : 0 ≤ max (m ^ (γ - 2)) (M ^ (γ - 2)) := le_trans hP2_nn hP2
  have hP1 : u x ^ (γ - 1) ≤ max (m ^ (γ - 1)) (M ^ (γ - 1)) :=
    rpow_le_max hm hux_lb hux_ub
  have hP1_nn : 0 ≤ u x ^ (γ - 1) := Real.rpow_nonneg (le_of_lt hux_pos) _
  have hmaxP1_nn : 0 ≤ max (m ^ (γ - 1)) (M ^ (γ - 1)) := le_trans hP1_nn hP1
  -- term 1: |ν·γ·(γ−1)·u^{γ−2}·(u')²| ≤ ν·γ·|γ−1|·P₂·G1²
  have hterm1 :
      |ν * γ * (γ - 1) * u x ^ (γ - 2) * (deriv u x) ^ 2|
        ≤ ν * γ * |γ - 1| * max (m ^ (γ - 2)) (M ^ (γ - 2)) * G1 ^ 2 := by
    have hrw : |ν * γ * (γ - 1) * u x ^ (γ - 2) * (deriv u x) ^ 2|
        = ν * γ * |γ - 1| * u x ^ (γ - 2) * (deriv u x) ^ 2 := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hν, abs_of_nonneg hγ,
        abs_of_nonneg hP2_nn, abs_of_nonneg (sq_nonneg (deriv u x))]
    rw [hrw]
    have hsq : (deriv u x) ^ 2 ≤ G1 ^ 2 := by
      nlinarith [abs_nonneg (deriv u x), hG1x, sq_abs (deriv u x)]
    have hcoef_nn : 0 ≤ ν * γ * |γ - 1| := by positivity
    calc ν * γ * |γ - 1| * u x ^ (γ - 2) * (deriv u x) ^ 2
        ≤ ν * γ * |γ - 1| * max (m ^ (γ - 2)) (M ^ (γ - 2)) * (deriv u x) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left hP2 hcoef_nn
      _ ≤ ν * γ * |γ - 1| * max (m ^ (γ - 2)) (M ^ (γ - 2)) * G1 ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
  -- term 2: |ν·γ·u^{γ−1}·u''| ≤ ν·γ·P₁·G2
  have hterm2 :
      |ν * γ * u x ^ (γ - 1) * deriv (deriv u) x|
        ≤ ν * γ * max (m ^ (γ - 1)) (M ^ (γ - 1)) * G2 := by
    have hrw : |ν * γ * u x ^ (γ - 1) * deriv (deriv u) x|
        = ν * γ * u x ^ (γ - 1) * |deriv (deriv u) x| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hν, abs_of_nonneg hγ,
        abs_of_nonneg hP1_nn]
    rw [hrw]
    have hcoef_nn : 0 ≤ ν * γ := by positivity
    calc ν * γ * u x ^ (γ - 1) * |deriv (deriv u) x|
        ≤ ν * γ * max (m ^ (γ - 1)) (M ^ (γ - 1)) * |deriv (deriv u) x| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left hP1 hcoef_nn
      _ ≤ ν * γ * max (m ^ (γ - 1)) (M ^ (γ - 1)) * G2 :=
          mul_le_mul_of_nonneg_left hG2x (by positivity)
  calc |Fp2 ν γ u x|
      ≤ |ν * γ * (γ - 1) * u x ^ (γ - 2) * (deriv u x) ^ 2|
          + |ν * γ * u x ^ (γ - 1) * deriv (deriv u) x| := by
        simp only [Fp2]; exact abs_add_le _ _
    _ ≤ ν * γ * |γ - 1| * max (m ^ (γ - 2)) (M ^ (γ - 2)) * G1 ^ 2
          + ν * γ * max (m ^ (γ - 1)) (M ^ (γ - 1)) * G2 := add_le_add hterm1 hterm2
    _ = B_pow ν γ M m G1 G2 := rfl

/-- `B_pow` is nonnegative under the hypotheses. -/
theorem B_pow_nonneg
    {ν γ M m G1 G2 : ℝ}
    (hν : 0 ≤ ν) (hγ : 0 ≤ γ) (hm : 0 < m) (hmM : m ≤ M)
    (_hG1 : 0 ≤ G1) (hG2 : 0 ≤ G2) :
    0 ≤ B_pow ν γ M m G1 G2 := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hmaxP2_nn : 0 ≤ max (m ^ (γ - 2)) (M ^ (γ - 2)) :=
    le_trans (Real.rpow_nonneg (le_of_lt hm) _) (le_max_left _ _)
  have hmaxP1_nn : 0 ≤ max (m ^ (γ - 1)) (M ^ (γ - 1)) :=
    le_trans (Real.rpow_nonneg (le_of_lt hm) _) (le_max_left _ _)
  unfold B_pow
  have h1 : 0 ≤ ν * γ * |γ - 1| * max (m ^ (γ - 2)) (M ^ (γ - 2)) * G1 ^ 2 := by
    positivity
  have h2 : 0 ≤ ν * γ * max (m ^ (γ - 1)) (M ^ (γ - 1)) * G2 := by positivity
  linarith

/-- **Explicit `W^{2,1}` bound for the power source.**
For `ContDiff ℝ 2 u`, `0 < m ≤ u ≤ M` on `[0,1]`, `|u'| ≤ G1`, `|u''| ≤ G2`,
`0 ≤ ν`, `0 ≤ γ`:

  `∫₀¹ |deriv (deriv (fun x => ν·u x^γ)) x| dx ≤ B_pow ν γ M m G1 G2`. -/
theorem powerSourceFun_secondDeriv_abs_integral_le
    {ν γ M m G1 G2 : ℝ} {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hν : 0 ≤ ν) (hγ : 0 ≤ γ) (hm : 0 < m)
    (hlb : ∀ x ∈ Set.Icc (0 : ℝ) 1, m ≤ u x)
    (hub : ∀ x ∈ Set.Icc (0 : ℝ) 1, u x ≤ M)
    (hG1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv u x| ≤ G1)
    (hG2 : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv u) x| ≤ G2) :
    (∫ x in (0 : ℝ)..1, |deriv (deriv (fun y => ν * u y ^ γ)) x|)
      ≤ B_pow ν γ M m G1 G2 := by
  have hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < u x :=
    fun x hx => lt_of_lt_of_le hm (hlb x hx)
  -- ContDiffOn ℝ 2 of g = ν·u^γ on [0,1] (chain rule via positivity)
  have hC2g : ContDiffOn ℝ 2 (fun y => ν * u y ^ γ) (Set.Icc (0 : ℝ) 1) :=
    (hu.contDiffOn.rpow_const_of_ne (fun x hx => ne_of_gt (hpos x hx))).const_smul ν
      |>.congr (fun x _ => by rw [smul_eq_mul])
  have hint : IntervalIntegrable
      (deriv (deriv (fun y => ν * u y ^ γ))) volume (0 : ℝ) 1 :=
    intervalIntegrable_deriv_deriv_of_contDiffOn_two hC2g
  have habs_int : IntervalIntegrable
      (fun x => |deriv (deriv (fun y => ν * u y ^ γ)) x|) volume (0 : ℝ) 1 := by
    simpa [Real.norm_eq_abs] using hint.norm
  calc
    (∫ x in (0 : ℝ)..1, |deriv (deriv (fun y => ν * u y ^ γ)) x|)
        ≤ ∫ _x in (0 : ℝ)..1, B_pow ν γ M m G1 G2 := by
          refine intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
            habs_int intervalIntegrable_const ?_
          intro x hx
          have hxmem : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, hx.2⟩
          rw [secondDeriv_powerSource_eq_Fp2 hu hpos hxmem]
          exact Fp2_abs_le_B_pow hν hγ hm hlb hub hG1 hG2 hxmem
    _ = B_pow ν γ M m G1 G2 := by
          rw [intervalIntegral.integral_const]; norm_num

/-- **Explicit quadratic cosine-coefficient decay for the power source.**
Under `ContDiff ℝ 2 u`, `0 < m ≤ u ≤ M` on `[0,1]`, `|u'| ≤ G1`, `|u''| ≤ G2`,
`0 ≤ ν`, `0 < γ` and the Neumann endpoint data `u' 0 = u' 1 = 0`:

  `|cosineCoeffs (fun x => ν·u x^γ) k| ≤ 2·B_pow / ((k:ℝ)·π)²` for `k ≥ 1`. -/
theorem powerSourceFun_cosineCoeff_quadratic_decay_explicit
    {ν γ M m G1 G2 : ℝ} {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hν : 0 ≤ ν) (hγ : 0 < γ) (hm : 0 < m)
    (hlb : ∀ x ∈ Set.Icc (0 : ℝ) 1, m ≤ u x)
    (hub : ∀ x ∈ Set.Icc (0 : ℝ) 1, u x ≤ M)
    (hG1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv u x| ≤ G1)
    (hG2 : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv u) x| ≤ G2)
    (hdu0 : deriv u 0 = 0) (hdu1 : deriv u 1 = 0) :
    ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (fun x => ν * u x ^ γ) k|
        ≤ 2 * B_pow ν γ M m G1 G2 / ((k : ℝ) * Real.pi) ^ 2 := by
  have hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < u x :=
    fun x hx => lt_of_lt_of_le hm (hlb x hx)
  -- ContDiffOn ℝ 2 of g = ν·u^γ
  have hC2g : ContDiffOn ℝ 2 (fun y => ν * u y ^ γ) (Set.Icc (0 : ℝ) 1) :=
    (hu.contDiffOn.rpow_const_of_ne (fun x hx => ne_of_gt (hpos x hx))).const_smul ν
      |>.congr (fun x _ => by rw [smul_eq_mul])
  -- Neumann endpoints of g: deriv g 0 = 0, deriv g 1 = 0.
  have hg0 : deriv (fun y => ν * u y ^ γ) 0 = 0 := by
    rw [deriv_powerSource_eq_Fp1 hu hpos (Set.left_mem_Icc.mpr (by norm_num))]
    simp only [Fp1, hdu0, mul_zero]
  have hg1 : deriv (fun y => ν * u y ^ γ) 1 = 0 := by
    rw [deriv_powerSource_eq_Fp1 hu hpos (Set.right_mem_Icc.mpr (by norm_num))]
    simp only [Fp1, hdu1, mul_zero]
  -- One-sided Neumann limits of deriv g at endpoints (deriv g is continuous on [0,1]
  -- and equals 0 at the endpoints; tend through the boundary trace of Fp1).
  -- We use the `intervalWeakH2Neumann_of_contDiffOn` constructor: it needs the
  -- one-sided tendsto facts.  Build them from continuity of Fp1 ∘ trace.
  have hFp1_cont : ContinuousOn (Fp1 ν γ u) (Set.Icc (0 : ℝ) 1) := by
    have hu_cont : Continuous u := hu.continuous
    have hu'_cont : Continuous (deriv u) := hu.continuous_deriv (by norm_num)
    have hpow_cont : ContinuousOn (fun x => u x ^ (γ - 1)) (Set.Icc (0 : ℝ) 1) :=
      hu_cont.continuousOn.rpow_const (fun x hx => Or.inl (ne_of_gt (hpos x hx)))
    have : ContinuousOn (fun x => ν * γ * u x ^ (γ - 1) * deriv u x) (Set.Icc (0 : ℝ) 1) :=
      (continuousOn_const.mul hpow_cont).mul hu'_cont.continuousOn
    exact this
  have hdg_cont : ContinuousOn (deriv (fun y => ν * u y ^ γ)) (Set.Icc (0 : ℝ) 1) :=
    hFp1_cont.congr (fun x hx => deriv_powerSource_eq_Fp1 hu hpos hx)
  have htend0 : Filter.Tendsto (deriv (fun y => ν * u y ^ γ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := (hdg_cont.continuousWithinAt
      (Set.left_mem_Icc.mpr (by norm_num : (0:ℝ) ≤ 1))).tendsto
    rw [hg0] at h
    -- 𝓝[Ioi 0] 0 ≤ 𝓝[Icc 0 1] 0 : `Icc 0 1 ∈ 𝓝[Ioi 0] 0`.
    have hmem : Set.Icc (0:ℝ) 1 ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := by
      refine Filter.mem_of_superset
        (mem_nhdsWithin.mpr ⟨Set.Iio 1, isOpen_Iio, by norm_num, ?_⟩)
        (Set.Ioo_subset_Icc_self (a := (0:ℝ)) (b := 1))
      exact fun z hz => ⟨hz.2, hz.1⟩
    exact h.mono_left (nhdsWithin_le_iff.mpr hmem)
  have htend1 : Filter.Tendsto (deriv (fun y => ν * u y ^ γ))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
    have h := (hdg_cont.continuousWithinAt
      (Set.right_mem_Icc.mpr (by norm_num : (0:ℝ) ≤ 1))).tendsto
    rw [hg1] at h
    have hmem : Set.Icc (0:ℝ) 1 ∈ nhdsWithin (1:ℝ) (Set.Iio 1) := by
      refine Filter.mem_of_superset
        (mem_nhdsWithin.mpr ⟨Set.Ioi 0, isOpen_Ioi, by norm_num, ?_⟩)
        (Set.Ioo_subset_Icc_self (a := (0:ℝ)) (b := 1))
      exact fun z hz => ⟨hz.1, hz.2⟩
    exact h.mono_left (nhdsWithin_le_iff.mpr hmem)
  -- Build the weak-H²ₙ certificate (secondDeriv = deriv (deriv g)).
  set hf := intervalWeakH2Neumann_of_contDiffOn hC2g htend0 htend1 hg0 hg1 with hf_def
  have hB : (∫ x in (0 : ℝ)..1, |hf.secondDeriv x|) ≤ B_pow ν γ M m G1 G2 :=
    powerSourceFun_secondDeriv_abs_integral_le hu hν (le_of_lt hγ) hm hlb hub hG1 hG2
  exact ShenWork.IntervalSourceDecayQuantitative.intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound
    hf hB

/-- **Window-uniform power-source decay (R-Hvsrc-1).**

Given, on the clamp window `σ ∈ [c', d']`, the per-slice cosine representation
(`hbsum`/`hagree`), pointwise positivity (`hpos`), a window-uniform positive
LOWER bound `m > 0` (`hlb`), a window-uniform UPPER bound `M` (`hub`), and the K2
gradient/Hessian window bounds (`hG1`/`hG2`), produce a SINGLE constant `C`
controlling the power-source cosine coefficients `cosineCoeffs (ν·lift(w σ)^γ)`
uniformly over the window (both the `k ≥ 1` quadratic decay and the zeroth bound).

This is the `ν·u^γ` analogue of the logistic
`IntervalDomainLimitSourceRepresentation.limitSource_duhamelSourceTimeC1_of_representation`
uniform constant `C := max (2·B_log …) (M·…)` — but with the explicit `B_pow`
envelope (needing the positive lower bound `m`). -/
theorem powerSource_window_uniform_decay
    {ν γ M m : ℝ} (hν : 0 ≤ ν) (hγ : 0 < γ) (hm : 0 < m)
    {w : ℝ → intervalDomainPoint → ℝ} {c' d' : ℝ} (hcd' : c' ≤ d')
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ ∈ Set.Icc c' d',
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ ∈ Set.Icc c' d', Set.EqOn (intervalDomainLift (w σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hlb : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      m ≤ intervalDomainLift (w σ) x)
    (hub : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (w σ) x ≤ M)
    {G1 G2 : ℝ}
    (hG1 : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (w σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (w σ))) x| ≤ G2) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ σ ∈ Set.Icc c' d', ∀ k : ℕ, 1 ≤ k →
        |cosineCoeffs (fun x => ν * intervalDomainLift (w σ) x ^ γ) k|
          ≤ C / ((k : ℝ) * Real.pi) ^ 2) ∧
      (∀ σ ∈ Set.Icc c' d',
        |cosineCoeffs (fun x => ν * intervalDomainLift (w σ) x ^ γ) 0| ≤ C) := by
  have hmM : m ≤ M := le_trans (hlb c' ⟨le_rfl, hcd'⟩ 0 ⟨le_rfl, by norm_num⟩)
    (hub c' ⟨le_rfl, hcd'⟩ 0 ⟨le_rfl, by norm_num⟩)
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  -- the per-slice genuinely-`C²` cosine series.
  set cs : ℝ → ℝ → ℝ := fun σ x => ∑' n, bc σ n * cosineMode n x with hcs
  have hcsC2 : ∀ σ ∈ Set.Icc c' d', ContDiff ℝ 2 (cs σ) :=
    fun σ hσ => ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two (hbsum σ hσ)
  -- bounds transfer lift → cs on `[0,1]` (pointwise agreement).
  have hcseq : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      cs σ x = intervalDomainLift (w σ) x :=
    fun σ hσ x hx => (hagree σ hσ hx).symm
  have hlb_cs : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1, m ≤ cs σ x := by
    intro σ hσ x hx; rw [hcseq σ hσ x hx]; exact hlb σ hσ x hx
  have hub_cs : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1, cs σ x ≤ M := by
    intro σ hσ x hx; rw [hcseq σ hσ x hx]; exact hub σ hσ x hx
  have hpos_cs : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < cs σ x :=
    fun σ hσ x hx => lt_of_lt_of_le hm (hlb_cs σ hσ x hx)
  -- gradient bound transfer: on `(0,1)` cs and lift agree on an open nbhd, so
  -- their derivatives agree; extend by continuity (`le_on_Icc_of_le_on_Ioo`).
  have hG1nn : 0 ≤ G1 :=
    le_trans (abs_nonneg _) (hG1 c' ⟨le_rfl, hcd'⟩ 0 ⟨le_rfl, by norm_num⟩)
  have hG2nn : 0 ≤ G2 :=
    le_trans (abs_nonneg _) (hG2 c' ⟨le_rfl, hcd'⟩ 0 ⟨le_rfl, by norm_num⟩)
  have hG1_cs : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (cs σ) x| ≤ G1 := by
    intro σ hσ
    refine le_on_Icc_of_le_on_Ioo ((hcsC2 σ hσ).continuous_deriv (by norm_num)).abs
      (fun x hx => ?_)
    have hloc : intervalDomainLift (w σ) =ᶠ[nhds x] cs σ := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hagree σ hσ (Set.Ioo_subset_Icc_self hy)
    rw [← hloc.deriv_eq]
    exact hG1 σ hσ x (Set.Ioo_subset_Icc_self hx)
  have hG2_cs : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (cs σ)) x| ≤ G2 := by
    intro σ hσ
    have hdd_cont : Continuous (deriv (deriv (cs σ))) := by
      have h2 : ContDiff ℝ (1 + 1) (cs σ) := by simpa using hcsC2 σ hσ
      exact ((contDiff_succ_iff_deriv.mp h2).2.2).continuous_deriv le_rfl
    refine le_on_Icc_of_le_on_Ioo hdd_cont.abs (fun x hx => ?_)
    have hloc : intervalDomainLift (w σ) =ᶠ[nhds x] cs σ := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hagree σ hσ (Set.Ioo_subset_Icc_self hy)
    have hloc' : deriv (intervalDomainLift (w σ)) =ᶠ[nhds x] deriv (cs σ) := hloc.deriv
    rw [← hloc'.deriv_eq]
    exact hG2 σ hσ x (Set.Ioo_subset_Icc_self hx)
  -- Neumann endpoints of the cosine series.
  have hN0 : ∀ σ ∈ Set.Icc c' d', deriv (cs σ) 0 = 0 :=
    fun σ hσ => ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv_at_zero (hbsum σ hσ)
  have hN1 : ∀ σ ∈ Set.Icc c' d', deriv (cs σ) 1 = 0 :=
    fun σ hσ => ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv_at_one (hbsum σ hσ)
  -- power source of lift equals that of cs on `[0,1]` (pointwise).
  have hsrc_eq : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ν * intervalDomainLift (w σ) x ^ γ = ν * cs σ x ^ γ := by
    intro σ hσ x hx; rw [hcseq σ hσ x hx]
  -- window-uniform constant.
  set Cz : ℝ := ν * max (m ^ γ) (M ^ γ) with hCzdef
  set C : ℝ := max (2 * B_pow ν γ M m G1 G2) (2 * Cz) with hCdef
  have hBpownn : 0 ≤ B_pow ν γ M m G1 G2 :=
    B_pow_nonneg hν (le_of_lt hγ) hm hmM hG1nn hG2nn
  have hCznn : 0 ≤ Cz := by
    have : 0 ≤ max (m ^ γ) (M ^ γ) :=
      le_trans (Real.rpow_nonneg (le_of_lt hm) _) (le_max_left _ _)
    rw [hCzdef]; positivity
  have hCnn : 0 ≤ C := le_trans (by linarith : (0:ℝ) ≤ 2 * B_pow ν γ M m G1 G2)
    (le_max_left _ _)
  refine ⟨C, hCnn, ?_, ?_⟩
  · -- quadratic decay (k ≥ 1)
    intro σ hσ k hk
    rw [cosineCoeffs_congr_on_Icc (hsrc_eq σ hσ) k]
    have hden : 0 < ((k : ℝ) * Real.pi) ^ 2 := by
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
      positivity
    refine le_trans
      (powerSourceFun_cosineCoeff_quadratic_decay_explicit (hcsC2 σ hσ) hν hγ hm
        (hlb_cs σ hσ) (hub_cs σ hσ) (hG1_cs σ hσ) (hG2_cs σ hσ) (hN0 σ hσ) (hN1 σ hσ) k hk) ?_
    gcongr
    exact le_max_left _ _
  · -- zeroth bound: |cosineCoeffs (ν·cs^γ) 0| ≤ 2·Cz ≤ C
    intro σ hσ
    rw [cosineCoeffs_congr_on_Icc (hsrc_eq σ hσ) 0]
    have hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1, |ν * cs σ x ^ γ| ≤ Cz := by
      intro x hx
      have hposx : 0 < cs σ x := hpos_cs σ hσ x hx
      have hpowle : cs σ x ^ γ ≤ max (m ^ γ) (M ^ γ) :=
        rpow_le_max hm (hlb_cs σ hσ x hx) (hub_cs σ hσ x hx)
      have hpownn : 0 ≤ cs σ x ^ γ := Real.rpow_nonneg (le_of_lt hposx) _
      rw [abs_mul, abs_of_nonneg hν, abs_of_nonneg hpownn]
      exact mul_le_mul_of_nonneg_left hpowle hν
    have hcsCont : ContinuousOn (fun x => ν * cs σ x ^ γ) (Set.Icc (0 : ℝ) 1) :=
      (continuousOn_const.mul ((hcsC2 σ hσ).continuous.continuousOn.rpow_const
        (fun x hx => Or.inl (ne_of_gt (hpos_cs σ hσ x hx)))))
    have h2Cz := cosineCoeffs_abs_le_of_continuous_bounded hcsCont hCznn hsup 0
    exact le_trans h2Cz (le_max_right _ _)

end ShenWork.Paper2.ResolverPowerDecay
