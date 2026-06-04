import ShenWork.PDE.IntervalNeumannFullKernel
import ShenWork.PDE.IntervalEllipticCharacterization
import ShenWork.PDE.IntervalDuhamelClosedC2
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Quadratic decay of positive `H²_N` power-source cosine coefficients

This helper isolates the weak one-dimensional `H²_N` input needed for the mild
source coefficient decay.  The main analytic step is independent of the mild
solution: if a source has a weak second derivative on `[0,1]`, the Neumann
cosine IBP identity, and an `L¹` bound on that weak second derivative, then its
normalized cosine coefficients decay like `1 / k²`.

For a bounded Lipschitz profile `u` with `u ≥ m > 0`, the Sobolev chain-rule
step should provide the same weak `H²_N` certificate for `x ↦ ν * u x ^ γ`.
The theorem `powerSource_cosineCoeff_quadratic_decay_of_chain_rule` records the
resulting coefficient decay without importing or modifying
`IntervalMildSourceDecay.lean`.
-/

open MeasureTheory intervalIntegral
open scoped Topology NNReal

namespace ShenWork.PDE.IntervalMildSourceDecayHelper

open ShenWork.HeatKernelGradientEstimates
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalEllipticCharacterization
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open Asymptotics

noncomputable section

/-- Bounded, Lipschitz, strictly positive profile data on `[0,1]`. -/
structure BoundedLipschitzPositiveOnUnit (u : ℝ → ℝ) (m : ℝ) where
  m_pos : 0 < m
  lower_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1, m ≤ u x
  bounded : ∃ M : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, |u x| ≤ M
  lipschitz : ∃ K : ℝ≥0, LipschitzOnWith K u (Set.Icc (0 : ℝ) 1)

/-- A lightweight weak `H²_N` certificate on `[0,1]`.

The field `weak_cosine_laplacian` is the Neumann cosine weak-IBP identity.  The
`second_abs_integral_bound` field is the `L¹` control implied by an `L²` weak
second derivative on the finite interval. -/
structure IntervalWeakH2Neumann (f : ℝ → ℝ) where
  secondDeriv : ℝ → ℝ
  second_intervalIntegrable : IntervalIntegrable secondDeriv volume (0 : ℝ) 1
  second_abs_integral_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∫ x in (0 : ℝ)..1, |secondDeriv x| ≤ B
  weak_cosine_laplacian : ∀ k : ℕ,
    (∫ x in (0 : ℝ)..1,
        Real.cos ((k : ℝ) * Real.pi * x) * secondDeriv x) =
      -((k : ℝ) * Real.pi) ^ 2 *
        ∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * f x

/-- Positive `H²_N` profile plus the Sobolev-chain-rule output for
`x ↦ ν * u x ^ γ`. -/
structure PowerSourceH2NeumannData (ν γ m : ℝ) (u : ℝ → ℝ) where
  profile : BoundedLipschitzPositiveOnUnit u m
  profile_h2_neumann : IntervalWeakH2Neumann u
  source_h2_neumann : IntervalWeakH2Neumann (fun x : ℝ => ν * u x ^ γ)

/-- Build the weak `H²_N` certificate from a closed-interval `C²` representative
with homogeneous Neumann endpoint data.

This packages the existing cosine eigenfunction integration-by-parts theorem:
the weak second derivative is the classical `deriv (deriv g)`, its `L¹` bound is
the absolute integral itself, and the weak cosine Laplacian identity is
`intervalCosineLaplacianCoeff_eq_of_contDiffOn`. -/
noncomputable def intervalWeakH2Neumann_of_contDiffOn
    {g : ℝ → ℝ}
    (hgC2 : ContDiffOn ℝ 2 g (Set.Icc (0 : ℝ) 1))
    (htend0 : Filter.Tendsto (deriv g) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htend1 : Filter.Tendsto (deriv g) (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hbc0 : deriv g 0 = 0) (hbc1 : deriv g 1 = 0) :
    IntervalWeakH2Neumann g where
  secondDeriv := deriv (deriv g)
  second_intervalIntegrable :=
    intervalIntegrable_deriv_deriv_of_contDiffOn_two hgC2
  second_abs_integral_bound := by
    refine ⟨∫ x in (0 : ℝ)..1, |deriv (deriv g) x|, ?_, le_rfl⟩
    exact intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      (fun x _hx => abs_nonneg _)
  weak_cosine_laplacian := by
    intro k
    exact intervalCosineLaplacianCoeff_eq_of_contDiffOn k hgC2 htend0 htend1 hbc0 hbc1

/-- Construct `IntervalWeakH2Neumann` for the power source
`g x = ν * u x ^ γ` once the Sobolev chain-rule step has supplied closed-interval
`C²` regularity and Neumann endpoint data for this source. -/
noncomputable def powerSource_intervalWeakH2Neumann
    {ν γ : ℝ} {u : ℝ → ℝ}
    (hgC2 : ContDiffOn ℝ 2 (fun x : ℝ => ν * u x ^ γ) (Set.Icc (0 : ℝ) 1))
    (htend0 : Filter.Tendsto (deriv (fun x : ℝ => ν * u x ^ γ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htend1 : Filter.Tendsto (deriv (fun x : ℝ => ν * u x ^ γ))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hbc0 : deriv (fun x : ℝ => ν * u x ^ γ) 0 = 0)
    (hbc1 : deriv (fun x : ℝ => ν * u x ^ γ) 1 = 0) :
    IntervalWeakH2Neumann (fun x : ℝ => ν * u x ^ γ) :=
  intervalWeakH2Neumann_of_contDiffOn hgC2 htend0 htend1 hbc0 hbc1

/-- Assemble the positive-profile data and the chain-rule source certificate into
the packaged power-source `H²_N` datum. -/
noncomputable def powerSourceH2NeumannData_of_source_contDiffOn
    {ν γ m : ℝ} {u : ℝ → ℝ}
    (hprofile : BoundedLipschitzPositiveOnUnit u m)
    (huH2 : IntervalWeakH2Neumann u)
    (hgC2 : ContDiffOn ℝ 2 (fun x : ℝ => ν * u x ^ γ) (Set.Icc (0 : ℝ) 1))
    (htend0 : Filter.Tendsto (deriv (fun x : ℝ => ν * u x ^ γ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htend1 : Filter.Tendsto (deriv (fun x : ℝ => ν * u x ^ γ))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hbc0 : deriv (fun x : ℝ => ν * u x ^ γ) 0 = 0)
    (hbc1 : deriv (fun x : ℝ => ν * u x ^ γ) 1 = 0) :
    PowerSourceH2NeumannData ν γ m u where
  profile := hprofile
  profile_h2_neumann := huH2
  source_h2_neumann :=
    powerSource_intervalWeakH2Neumann hgC2 htend0 htend1 hbc0 hbc1

private theorem weak_laplacianCoeff_abs_le
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ,
      |∫ x in (0 : ℝ)..1,
          Real.cos ((k : ℝ) * Real.pi * x) * hf.secondDeriv x| ≤ B := by
  rcases hf.second_abs_integral_bound with ⟨B, hB_nonneg, hB⟩
  refine ⟨B, hB_nonneg, ?_⟩
  intro k
  have hcos_cont :
      ContinuousOn (fun x : ℝ => Real.cos ((k : ℝ) * Real.pi * x))
        (Set.uIcc (0 : ℝ) 1) := by
    fun_prop
  have hmul_int :
      IntervalIntegrable
        (fun x : ℝ => Real.cos ((k : ℝ) * Real.pi * x) * hf.secondDeriv x)
        volume (0 : ℝ) 1 :=
    hf.second_intervalIntegrable.continuousOn_mul hcos_cont
  have hmul_abs_int :
      IntervalIntegrable
        (fun x : ℝ => |Real.cos ((k : ℝ) * Real.pi * x) * hf.secondDeriv x|)
        volume (0 : ℝ) 1 := by
    simpa [Real.norm_eq_abs] using hmul_int.norm
  have hsecond_abs_int :
      IntervalIntegrable (fun x : ℝ => |hf.secondDeriv x|) volume (0 : ℝ) 1 := by
    simpa [Real.norm_eq_abs] using hf.second_intervalIntegrable.norm
  calc
    |∫ x in (0 : ℝ)..1,
        Real.cos ((k : ℝ) * Real.pi * x) * hf.secondDeriv x|
        ≤ ∫ x in (0 : ℝ)..1,
            |Real.cos ((k : ℝ) * Real.pi * x) * hf.secondDeriv x| :=
          intervalIntegral.abs_integral_le_integral_abs (by norm_num : (0 : ℝ) ≤ 1)
    _ ≤ ∫ x in (0 : ℝ)..1, |hf.secondDeriv x| := by
      refine intervalIntegral.integral_mono_on
        (by norm_num : (0 : ℝ) ≤ 1) hmul_abs_int hsecond_abs_int ?_
      intro x _hx
      rw [abs_mul]
      calc
        |Real.cos ((k : ℝ) * Real.pi * x)| * |hf.secondDeriv x|
            ≤ 1 * |hf.secondDeriv x| :=
              mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _)
                (abs_nonneg _)
        _ = |hf.secondDeriv x| := one_mul _
    _ ≤ B := hB

private theorem cosineCoeffs_eq_two_raw_integral
    {f : ℝ → ℝ} {k : ℕ} (hk : k ≠ 0) :
    cosineCoeffs f k =
      2 * ∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * f x := by
  simp only [cosineCoeffs, unitIntervalNeumannCosineCoeff, if_neg hk]
  rw [unitIntervalCosineRawCoeff]
  have hcast :
      (fun x : ℝ =>
          (Real.cos ((k : ℝ) * Real.pi * x) : ℂ) * ((f x : ℝ) : ℂ)) =
        fun x : ℝ =>
          ((Real.cos ((k : ℝ) * Real.pi * x) * f x : ℝ) : ℂ) := by
    funext x
    push_cast
    ring
  rw [hcast, intervalIntegral.integral_ofReal, Complex.ofReal_re]

/-- Weak `H²_N` coefficient decay for normalized unit-interval Neumann cosine
coefficients. -/
theorem intervalWeakH2Neumann_cosineCoeff_quadratic_decay
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs f k| ≤ C / ((k : ℝ) * Real.pi) ^ 2 := by
  rcases weak_laplacianCoeff_abs_le hf with ⟨B, hB_nonneg, hBcoeff⟩
  refine ⟨2 * B, by positivity, ?_⟩
  intro k hk
  have hk_ne : k ≠ 0 := by omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hlam_pos : 0 < ((k : ℝ) * Real.pi) ^ 2 := by positivity
  set raw : ℝ :=
    ∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * f x
  set lap : ℝ :=
    ∫ x in (0 : ℝ)..1,
      Real.cos ((k : ℝ) * Real.pi * x) * hf.secondDeriv x
  have hweak : lap = -((k : ℝ) * Real.pi) ^ 2 * raw := by
    simpa [lap, raw] using hf.weak_cosine_laplacian k
  have hraw : raw = -(1 / ((k : ℝ) * Real.pi) ^ 2) * lap := by
    rw [hweak]
    field_simp [ne_of_gt hlam_pos]
  have hlap_bound : |lap| ≤ B := by
    simpa [lap] using hBcoeff k
  have hraw_bound : |raw| ≤ B / ((k : ℝ) * Real.pi) ^ 2 := by
    rw [hraw, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1 / ((k : ℝ) * Real.pi) ^ 2)]
    calc
      1 / ((k : ℝ) * Real.pi) ^ 2 * |lap|
          ≤ 1 / ((k : ℝ) * Real.pi) ^ 2 * B :=
            mul_le_mul_of_nonneg_left hlap_bound (by positivity)
      _ = B / ((k : ℝ) * Real.pi) ^ 2 := by ring
  have hcoeff :
      cosineCoeffs f k = 2 * raw := by
    simpa [raw] using cosineCoeffs_eq_two_raw_integral (f := f) hk_ne
  rw [hcoeff, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |raw| ≤ 2 * (B / ((k : ℝ) * Real.pi) ^ 2) :=
      mul_le_mul_of_nonneg_left hraw_bound (by norm_num)
    _ = 2 * B / ((k : ℝ) * Real.pi) ^ 2 := by ring

/-- The same decay expressed as a Big-O statement. -/
theorem intervalWeakH2Neumann_cosineCoeff_isBigO_inv_sq
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f) :
    (fun k : ℕ => |cosineCoeffs f k|) =O[Filter.atTop]
      (fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ 2) := by
  rcases intervalWeakH2Neumann_cosineCoeff_quadratic_decay hf with
    ⟨C, hC_nonneg, hdecay⟩
  refine IsBigO.of_bound (C / Real.pi ^ 2) <|
    Filter.eventually_atTop.mpr ⟨1, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hk_sq_pos : 0 < (k : ℝ) ^ 2 := by positivity
  have htarget_pos : 0 ≤ (1 : ℝ) / (k : ℝ) ^ 2 := by positivity
  have hsplit :
      C / ((k : ℝ) * Real.pi) ^ 2 =
        (C / Real.pi ^ 2) * (1 / (k : ℝ) ^ 2) := by
    rw [mul_pow]
    field_simp [ne_of_gt hk_sq_pos, Real.pi_ne_zero]
  have hbd := hdecay k hk1
  rw [hsplit] at hbd
  rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg htarget_pos]
  exact hbd

/-- Construct `IntervalWeakH2Neumann` for a source `g = ν * u ^ γ` from
eigenvalue-summable cosine coefficients of the profile `u` and strict
positivity.  Route: `cosineCoeffSeries_contDiff_two` → `ContDiffOn ℝ 2` of `u`
→ chain rule (`rpow_const_of_ne` for positivity) → `ContDiffOn ℝ 2` of `g`
→ Neumann limits from the cosine series derivatives at endpoints
→ `intervalWeakH2Neumann_of_contDiffOn`. -/
noncomputable def intervalWeakH2Neumann_of_eigenvalue_summable
    {ν γ : ℝ} (hν : 0 < ν) (hγ : 0 < γ)
    {b : ℕ → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|))
    {w : intervalDomainPoint → ℝ}
    (hagree : Set.EqOn (intervalDomainLift w)
        (fun x => ∑' n, b n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift w x) :
    IntervalWeakH2Neumann (fun x : ℝ => ν * intervalDomainLift w x ^ γ) := by
  set u := intervalDomainLift w
  set cseries := fun x : ℝ => ∑' n, b n * cosineMode n x
  set g := fun x : ℝ => ν * u x ^ γ
  -- Step 1: ContDiffOn ℝ 2 g (Icc 0 1) from eigenvalue summability + chain rule.
  have hC2u : ContDiffOn ℝ 2 u (Set.Icc (0 : ℝ) 1) :=
    (ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two hb).contDiffOn.congr hagree
  have hC2g : ContDiffOn ℝ 2 g (Set.Icc (0 : ℝ) 1) :=
    (hC2u.rpow_const_of_ne (fun x hx => ne_of_gt (hpos x hx))).const_smul ν
      |>.congr (fun x _ => by rw [smul_eq_mul])
  -- Step 2: deriv g vanishes at endpoints by junk-value (zero-extension jump).
  have hg_out : ∀ x, x ∉ Set.Icc (0 : ℝ) 1 → g x = 0 := by
    intro x hx; simp only [g, u, intervalDomainLift, dif_neg hx,
      Real.zero_rpow hγ.ne', mul_zero]
  have hbc0 : deriv g 0 = 0 := by
    apply deriv_zero_of_not_differentiableAt; intro hdiff
    have hgp : g 0 ≠ 0 := ne_of_gt
      (mul_pos hν (Real.rpow_pos_of_pos (hpos 0 ⟨le_refl _, by norm_num⟩) _))
    exact hgp (tendsto_nhds_unique
      (hdiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Set.Iio 0, self_mem_nhdsWithin, fun y hy =>
          (hg_out y (fun h => absurd h.1 (not_le.mpr hy))).symm⟩)))
  have hbc1 : deriv g 1 = 0 := by
    apply deriv_zero_of_not_differentiableAt; intro hdiff
    have hgp : g 1 ≠ 0 := ne_of_gt
      (mul_pos hν (Real.rpow_pos_of_pos (hpos 1 ⟨by norm_num, le_refl _⟩) _))
    exact hgp (tendsto_nhds_unique
      (hdiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Set.Ioi 1, self_mem_nhdsWithin, fun y hy =>
          (hg_out y (fun h => absurd h.2 (not_le.mpr hy))).symm⟩)))
  -- Step 3: One-sided Neumann limits deriv g → 0 at endpoints.
  -- On (0,1), g = ν · cseries^γ (from hagree), so deriv g = deriv(ν · cseries^γ)
  -- eventually near each endpoint.  The cseries derivative vanishes at endpoints
  -- (cosineCoeffSeries_deriv_at_zero/_one), and cseries^{γ-1} is bounded, so
  -- deriv(ν · cseries^γ) = ν γ cseries^{γ-1} · deriv cseries → 0.
  have htend0 : Filter.Tendsto (deriv g) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    -- deriv g agrees with deriv(ν * cseries^γ) on (0,1)
    have hmem : Set.Ioo (0:ℝ) 1 ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
      mem_nhdsWithin.mpr ⟨Set.Iio 1, isOpen_Iio, by norm_num, fun z hz => ⟨hz.2, hz.1⟩⟩
    have hevt : deriv g =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)]
        deriv (fun x => ν * cseries x ^ γ) := by
      filter_upwards [hmem] with y hy
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
      simp only [g, hagree (Set.Ioo_subset_Icc_self hz)]
    refine Filter.Tendsto.congr' hevt.symm ?_
    -- deriv(ν * cseries^γ) is continuous near 0 and vanishes at 0
    -- because cseries is C² and deriv cseries 0 = 0
    have hC2cs : ContDiff ℝ 2 cseries :=
      ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two hb
    have hdcs0 : deriv cseries 0 = 0 :=
      ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv_at_zero
        hb
    -- cseries(0) = u(0) > 0, so cseries is locally positive near 0
    have hcs0_pos : 0 < cseries 0 := by
      rw [← hagree (Set.left_mem_Icc.mpr (by norm_num))]
      exact hpos 0 ⟨le_refl _, by norm_num⟩
    -- There is a neighborhood of 0 where cseries > 0
    have hcs_cont : Continuous cseries := hC2cs.continuous
    have hcs_pos_near : ∀ᶠ x in nhds (0:ℝ), 0 < cseries x :=
      hcs_cont.continuousAt.eventually (isOpen_Ioi.mem_nhds hcs0_pos)
    -- On this neighborhood, ν * cseries^γ is C¹ and its derivative is
    -- ν * γ * cseries^{γ-1} * deriv cseries, which → ν * γ * cseries(0)^{γ-1} * 0 = 0
    -- The chain rule derivative ν * γ * cseries^{γ-1} * deriv cseries is continuous
    -- and vanishes at 0 (since deriv cseries 0 = 0).
    set F := fun x => ν * (deriv cseries x * γ * cseries x ^ (γ - 1))
    have hF_at : ContinuousAt F 0 := by
      simp only [F]
      have h1 : ContinuousAt (fun x => cseries x ^ (γ - 1)) 0 :=
        hcs_cont.continuousAt.rpow_const (Or.inl (ne_of_gt hcs0_pos))
      have h2 : ContinuousAt (deriv cseries) 0 :=
        (hC2cs.continuous_deriv (by norm_num)).continuousAt
      exact ((h2.mul_const γ).mul h1).const_mul ν
    have hhas : ∀ᶠ x in nhds (0:ℝ), HasDerivAt (fun z => ν * cseries z ^ γ)
        (F x) x := by
      filter_upwards [hcs_pos_near] with x hx
      have hd : HasDerivAt cseries (deriv cseries x) x :=
        (hC2cs.differentiable (by norm_num) x).hasDerivAt
      exact (hd.rpow_const (Or.inl (ne_of_gt hx))).const_mul ν
    have hderiv_eq : (fun x => deriv (fun z => ν * cseries z ^ γ) x) =ᶠ[nhds (0:ℝ)] F := by
      filter_upwards [hhas] with x hx; exact hx.deriv
    have hval : F 0 = 0 := by simp only [F]; rw [hdcs0, zero_mul, zero_mul, mul_zero]
    have htF : Filter.Tendsto F (nhds (0:ℝ)) (nhds 0) := by
      have := hF_at.tendsto; rwa [hval] at this
    exact (htF.congr' hderiv_eq.symm).mono_left nhdsWithin_le_nhds
  have htend1 : Filter.Tendsto (deriv g) (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
    have hmem : Set.Ioo (0:ℝ) 1 ∈ nhdsWithin (1:ℝ) (Set.Iio 1) :=
      mem_nhdsWithin.mpr ⟨Set.Ioi 0, isOpen_Ioi, by norm_num, fun z hz => ⟨hz.1, hz.2⟩⟩
    have hevt : deriv g =ᶠ[nhdsWithin (1:ℝ) (Set.Iio 1)]
        deriv (fun x => ν * cseries x ^ γ) := by
      filter_upwards [hmem] with y hy
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
      simp only [g, hagree (Set.Ioo_subset_Icc_self hz)]
    refine Filter.Tendsto.congr' hevt.symm ?_
    have hC2cs : ContDiff ℝ 2 cseries :=
      ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two hb
    have hdcs1 : deriv cseries 1 = 0 :=
      ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv_at_one
        hb
    have hcs1_pos : 0 < cseries 1 := by
      rw [← hagree (Set.right_mem_Icc.mpr (by norm_num))]
      exact hpos 1 ⟨by norm_num, le_refl _⟩
    have hcs_cont : Continuous cseries := hC2cs.continuous
    have hcs_pos_near : ∀ᶠ x in nhds (1:ℝ), 0 < cseries x :=
      hcs_cont.continuousAt.eventually (isOpen_Ioi.mem_nhds hcs1_pos)
    set G := fun x => ν * (deriv cseries x * γ * cseries x ^ (γ - 1))
    have hG_at : ContinuousAt G 1 := by
      simp only [G]
      have h1 : ContinuousAt (fun x => cseries x ^ (γ - 1)) 1 :=
        hcs_cont.continuousAt.rpow_const (Or.inl (ne_of_gt hcs1_pos))
      have h2 : ContinuousAt (deriv cseries) 1 :=
        (hC2cs.continuous_deriv (by norm_num)).continuousAt
      exact ((h2.mul_const γ).mul h1).const_mul ν
    have hhas : ∀ᶠ x in nhds (1:ℝ), HasDerivAt (fun z => ν * cseries z ^ γ)
        (G x) x := by
      filter_upwards [hcs_pos_near] with x hx
      have hd : HasDerivAt cseries (deriv cseries x) x :=
        (hC2cs.differentiable (by norm_num) x).hasDerivAt
      exact (hd.rpow_const (Or.inl (ne_of_gt hx))).const_mul ν
    have hderiv_eq : (fun x => deriv (fun z => ν * cseries z ^ γ) x) =ᶠ[nhds (1:ℝ)] G := by
      filter_upwards [hhas] with x hx; exact hx.deriv
    have hval : G 1 = 0 := by simp only [G]; rw [hdcs1, zero_mul, zero_mul, mul_zero]
    have htG : Filter.Tendsto G (nhds (1:ℝ)) (nhds 0) := by
      have := hG_at.tendsto; rwa [hval] at this
    exact (htG.congr' hderiv_eq.symm).mono_left nhdsWithin_le_nhds
  exact intervalWeakH2Neumann_of_contDiffOn hC2g htend0 htend1 hbc0 hbc1

/-- Bounded Lipschitz positive `u`, `u ∈ H²_N`, and the Sobolev chain-rule
certificate for `ν*u^γ` imply `O(1/k²)` decay of the power-source cosine
coefficients. -/
theorem powerSource_cosineCoeff_quadratic_decay_of_chain_rule
    {ν γ m : ℝ} {u : ℝ → ℝ}
    (hu : PowerSourceH2NeumannData ν γ m u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (fun x : ℝ => ν * u x ^ γ) k| ≤
        C / ((k : ℝ) * Real.pi) ^ 2 :=
  intervalWeakH2Neumann_cosineCoeff_quadratic_decay hu.source_h2_neumann

/-- Big-O form of `powerSource_cosineCoeff_quadratic_decay_of_chain_rule`. -/
theorem powerSource_cosineCoeff_isBigO_inv_sq_of_chain_rule
    {ν γ m : ℝ} {u : ℝ → ℝ}
    (hu : PowerSourceH2NeumannData ν γ m u) :
    (fun k : ℕ => |cosineCoeffs (fun x : ℝ => ν * u x ^ γ) k|)
      =O[Filter.atTop] (fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ 2) :=
  intervalWeakH2Neumann_cosineCoeff_isBigO_inv_sq hu.source_h2_neumann

end

end ShenWork.PDE.IntervalMildSourceDecayHelper
