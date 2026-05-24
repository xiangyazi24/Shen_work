import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
  Fourier-to-cosine Parseval bridge scaffolding.

  The cosine basis on `[0,1]` should be transported from the even part of the
  Fourier basis on `AddCircle 2`.  This file records the Mathlib Fourier
  Parseval input and the first concrete even-reflection integral identity.
-/

open MeasureTheory

open scoped ENNReal

noncomputable section

namespace ShenWork.CosineParsevalBridge

/-- Even reflection of a unit-interval function to the doubled interval. -/
def unitIntervalEvenReflection (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => f |x|

theorem unitIntervalEvenReflection_apply_of_nonneg
    (f : ℝ → ℂ) {x : ℝ} (hx : 0 ≤ x) :
    unitIntervalEvenReflection f x = f x := by
  simp [unitIntervalEvenReflection, abs_of_nonneg hx]

theorem unitIntervalEvenReflection_apply_neg
    (f : ℝ → ℂ) (x : ℝ) :
    unitIntervalEvenReflection f (-x) = unitIntervalEvenReflection f x := by
  simp [unitIntervalEvenReflection]

/-- The negative half of the doubled interval contributes the same squared
`L²` mass as the positive half for an even reflection. -/
theorem unitIntervalEvenReflection_norm_sq_integral_neg
    (f : ℝ → ℂ) :
    (∫ x in (-1 : ℝ)..0, ‖unitIntervalEvenReflection f x‖ ^ 2) =
      ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 := by
  have heven :
      (∫ x in (-1 : ℝ)..0, ‖unitIntervalEvenReflection f x‖ ^ 2)
        =
          ∫ x in (-1 : ℝ)..0,
            ‖unitIntervalEvenReflection f (-x)‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x _hx
    simp [unitIntervalEvenReflection_apply_neg]
  calc
    (∫ x in (-1 : ℝ)..0, ‖unitIntervalEvenReflection f x‖ ^ 2)
        =
          ∫ x in (-1 : ℝ)..0,
            ‖unitIntervalEvenReflection f (-x)‖ ^ 2 := heven
    _ = ∫ x in (0 : ℝ)..1, ‖unitIntervalEvenReflection f x‖ ^ 2 := by
          simpa using
            (intervalIntegral.integral_comp_neg
              (f := fun x : ℝ => ‖unitIntervalEvenReflection f x‖ ^ 2)
              (a := (-1 : ℝ)) (b := 0))
    _ = ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hx_nonneg : 0 ≤ x := by
            have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
              simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
            exact hxIcc.1
          simp [unitIntervalEvenReflection, abs_of_nonneg hx_nonneg]

/-- Squared `L²` mass of the even reflection on `[-1,1]`. -/
theorem unitIntervalEvenReflection_norm_sq_integral
    {f : ℝ → ℂ}
    (hf : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1) :
    (∫ x in (-1 : ℝ)..1, ‖unitIntervalEvenReflection f x‖ ^ 2) =
      2 * ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 := by
  let g : ℝ → ℝ := fun x => ‖unitIntervalEvenReflection f x‖ ^ 2
  have hpos : IntervalIntegrable g volume 0 1 := by
    refine hf.congr (fun x hx => ?_)
    have hx_nonneg : 0 ≤ x := by
      have hxIoc : x ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      exact hxIoc.1.le
    simp [g, unitIntervalEvenReflection, abs_of_nonneg hx_nonneg]
  have hneg :
      IntervalIntegrable g volume (-1) 0 := by
    have hcomp :
        IntervalIntegrable (fun x => g (-x)) volume 0 (-1) :=
      by
        simpa only [neg_zero] using
          (IntervalIntegrable.iff_comp_neg (f := g) (a := 0) (b := 1)).mp hpos
    exact hcomp.symm.congr (fun x _hx => by
      simp [g, unitIntervalEvenReflection_apply_neg])
  calc
    (∫ x in (-1 : ℝ)..1, g x)
        =
          (∫ x in (-1 : ℝ)..0, g x) +
            ∫ x in (0 : ℝ)..1, g x := by
          rw [← intervalIntegral.integral_add_adjacent_intervals hneg hpos]
    _ =
          (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) +
            ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 := by
          dsimp [g]
          rw [unitIntervalEvenReflection_norm_sq_integral_neg]
          congr 1
          apply intervalIntegral.integral_congr
          intro x hx
          have hx_nonneg : 0 ≤ x := by
            have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
              simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
            exact hxIcc.1
          simp [unitIntervalEvenReflection, abs_of_nonneg hx_nonneg]
    _ = 2 * ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 := by ring

/-- Mathlib's Parseval identity on the doubled interval, specialized to the
even reflection.  This is the Fourier side from which cosine Parseval should
be extracted by proving coefficient symmetry/equality. -/
theorem unitIntervalEvenReflection_fourier_parseval_raw
    {f : ℝ → ℂ}
    (hL2 :
      MemLp (unitIntervalEvenReflection f) 2
        (volume.restrict (Set.Ioc (-1 : ℝ) 1))) :
    (∑' i : ℤ,
        ‖fourierCoeffOn (show (-1 : ℝ) < 1 by norm_num)
          (unitIntervalEvenReflection f) i‖ ^ 2)
      =
        (2 : ℝ)⁻¹ *
          ∫ x in (-1 : ℝ)..1, ‖unitIntervalEvenReflection f x‖ ^ 2 := by
  have h :=
    tsum_sq_fourierCoeffOn
      (hab := show (-1 : ℝ) < 1 by norm_num)
      (f := unitIntervalEvenReflection f) hL2
  norm_num at h ⊢
  simpa using h

/-- Parseval on the doubled interval after reducing the even-reflection mass
back to the unit interval.  The remaining missing bridge is the coefficient
identity between these Fourier coefficients and the Neumann cosine
coefficients. -/
theorem unitIntervalEvenReflection_fourier_parseval_unit_mass
    {f : ℝ → ℂ}
    (hL2 :
      MemLp (unitIntervalEvenReflection f) 2
        (volume.restrict (Set.Ioc (-1 : ℝ) 1)))
    (hf : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1) :
    (∑' i : ℤ,
        ‖fourierCoeffOn (show (-1 : ℝ) < 1 by norm_num)
          (unitIntervalEvenReflection f) i‖ ^ 2)
      =
        ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 := by
  rw [unitIntervalEvenReflection_fourier_parseval_raw hL2,
    unitIntervalEvenReflection_norm_sq_integral hf]
  ring

/-- On the doubled circle, the paired Fourier characters are exactly the
unit-interval cosine mode.  This is the pointwise algebraic kernel used to turn
even Fourier coefficients into cosine coefficients. -/
theorem unitIntervalCosine_eq_fourier_pair (n : ℕ) (x : ℝ) :
    ((Real.cos ((n : ℝ) * Real.pi * x) : ℂ)) =
      (1 / 2 : ℂ) *
        (fourier (T := (2 : ℝ)) (n : ℤ) (x : AddCircle (2 : ℝ)) +
          fourier (T := (2 : ℝ)) (-(n : ℤ)) (x : AddCircle (2 : ℝ))) := by
  let θ : ℂ := ((n : ℝ) * Real.pi * x : ℝ)
  have hpos :
      fourier (T := (2 : ℝ)) (n : ℤ) (x : AddCircle (2 : ℝ)) =
        Complex.exp (θ * Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    dsimp [θ]
    norm_num
    ring
  have hneg :
      fourier (T := (2 : ℝ)) (-(n : ℤ)) (x : AddCircle (2 : ℝ)) =
        Complex.exp (-θ * Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    dsimp [θ]
    norm_num
    ring
  rw [hpos, hneg, ← Complex.two_cos]
  rw [← Complex.ofReal_cos]
  ring

/-- Integer-frequency form of `unitIntervalCosine_eq_fourier_pair`. -/
theorem unitIntervalCosine_int_eq_fourier_pair (n : ℤ) (x : ℝ) :
    ((Real.cos ((n : ℝ) * Real.pi * x) : ℂ)) =
      (1 / 2 : ℂ) *
        (fourier (T := (2 : ℝ)) n (x : AddCircle (2 : ℝ)) +
          fourier (T := (2 : ℝ)) (-n) (x : AddCircle (2 : ℝ))) := by
  let θ : ℂ := ((n : ℝ) * Real.pi * x : ℝ)
  have hpos :
      fourier (T := (2 : ℝ)) n (x : AddCircle (2 : ℝ)) =
        Complex.exp (θ * Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    dsimp [θ]
    norm_num
    ring
  have hneg :
      fourier (T := (2 : ℝ)) (-n) (x : AddCircle (2 : ℝ)) =
        Complex.exp (-θ * Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    dsimp [θ]
    norm_num
    ring
  rw [hpos, hneg, ← Complex.two_cos]
  rw [← Complex.ofReal_cos]
  ring

/-- The cosine coefficient of an interval function is the Fourier coefficient
of its even reflection on the doubled circle. -/
theorem unitIntervalEvenReflection_fourierCoeffOn_eq_cosineCoeff
    {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 1) (n : ℤ) :
    fourierCoeffOn (show (-1 : ℝ) < 1 by norm_num)
        (unitIntervalEvenReflection f) n =
      ∫ x in (0 : ℝ)..1,
        (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * f x := by
  let T : ℝ := (1 : ℝ) - (-1)
  let F : ℝ → ℂ :=
    fun x => fourier (T := T) (-n) (x : AddCircle T) •
      unitIntervalEvenReflection f x
  have hF_neg :
      IntervalIntegrable F volume (-1) 0 := by
    have hcomp_pos :
        IntervalIntegrable (fun x : ℝ => F (-x)) volume 0 1 := by
      have hbase :
          IntervalIntegrable
            (fun x : ℝ =>
              fourier (T := T) (-n) ((-x : ℝ) : AddCircle T) •
                f x)
            volume 0 1 := by
        refine hf.continuousOn_smul ?_
        fun_prop
      refine hbase.congr (fun x hx => ?_)
      have hx_nonneg : 0 ≤ x := by
        have hxIoc : x ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
        exact hxIoc.1.le
      change
        fourier (T := T) (-n) ((-x : ℝ) : AddCircle T) • f x =
          fourier (T := T) (-n) ((-x : ℝ) : AddCircle T) •
            unitIntervalEvenReflection f (-x)
      rw [unitIntervalEvenReflection_apply_neg,
        unitIntervalEvenReflection_apply_of_nonneg f hx_nonneg]
    exact (IntervalIntegrable.iff_comp_neg (f := F) (a := (-1 : ℝ)) (b := 0)).mpr
      (by simpa only [neg_neg, neg_zero] using hcomp_pos.symm)
  have hF_pos : IntervalIntegrable F volume 0 1 := by
    have hbase :
        IntervalIntegrable
          (fun x : ℝ =>
            fourier (T := T) (-n) (x : AddCircle T) • f x)
          volume 0 1 := by
      refine hf.continuousOn_smul ?_
      fun_prop
    refine hbase.congr (fun x hx => ?_)
    have hx_nonneg : 0 ≤ x := by
      have hxIoc : x ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      exact hxIoc.1.le
    change
      fourier (T := T) (-n) (x : AddCircle T) • f x =
        fourier (T := T) (-n) (x : AddCircle T) •
          unitIntervalEvenReflection f x
    rw [unitIntervalEvenReflection_apply_of_nonneg f hx_nonneg]
  have hsplit :
      ∫ x in (-1 : ℝ)..1, F x =
        (∫ x in (-1 : ℝ)..0, F x) + ∫ x in (0 : ℝ)..1, F x := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hF_neg hF_pos]
  have hneg :
      (∫ x in (-1 : ℝ)..0, F x) =
        ∫ x in (0 : ℝ)..1,
          fourier (T := T) n (x : AddCircle T) • f x := by
    have hcomp := intervalIntegral.integral_comp_neg
        (f := fun x : ℝ => F x) (a := (0 : ℝ)) (b := 1)
    calc
      (∫ x in (-1 : ℝ)..0, F x)
          = ∫ x in (0 : ℝ)..1, F (-x) := by
              simp
      _ = ∫ x in (0 : ℝ)..1,
          fourier (T := T) n (x : AddCircle T) • f x := by
            apply intervalIntegral.integral_congr
            intro x hx
            have hx_nonneg : 0 ≤ x := by
              have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
                simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
              exact hxIcc.1
            have hfourier :
                fourier (T := T) (-n) ((-x : ℝ) : AddCircle T) =
                  fourier (T := T) n (x : AddCircle T) := by
              rw [fourier_coe_apply, fourier_coe_apply]
              congr 1
              dsimp [T]
              norm_num
            change
              fourier (T := T) (-n) ((-x : ℝ) : AddCircle T) •
                  unitIntervalEvenReflection f (-x) =
                fourier (T := T) n (x : AddCircle T) • f x
            rw [hfourier, unitIntervalEvenReflection_apply_neg,
              unitIntervalEvenReflection_apply_of_nonneg f hx_nonneg]
  have hpos :
      (∫ x in (0 : ℝ)..1, F x) =
        ∫ x in (0 : ℝ)..1,
          fourier (T := T) (-n) (x : AddCircle T) • f x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx_nonneg : 0 ≤ x := by
      have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      exact hxIcc.1
    change
      fourier (T := T) (-n) (x : AddCircle T) •
          unitIntervalEvenReflection f x =
        fourier (T := T) (-n) (x : AddCircle T) • f x
    rw [unitIntervalEvenReflection_apply_of_nonneg f hx_nonneg]
  let A : ℝ → ℂ :=
    fun x => fourier (T := T) n (x : AddCircle T) • f x
  let B : ℝ → ℂ :=
    fun x => fourier (T := T) (-n) (x : AddCircle T) • f x
  have hA_int : IntervalIntegrable A volume 0 1 := by
    refine hf.continuousOn_smul ?_
    fun_prop
  have hB_int : IntervalIntegrable B volume 0 1 := by
    refine hf.continuousOn_smul ?_
    fun_prop
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_neg_eq_add, one_add_one_eq_two, one_div]
  change
      ((2 : ℝ)⁻¹) • ∫ x in (-1 : ℝ)..1, F x =
        ∫ x in (0 : ℝ)..1,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * f x
  rw [hsplit, hneg, hpos]
  change
      ((2 : ℝ)⁻¹) • ((∫ x in (0 : ℝ)..1, A x) + ∫ x in (0 : ℝ)..1, B x) =
        ∫ x in (0 : ℝ)..1,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * f x
  rw [Complex.real_smul]
  rw [show ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) = (1 / 2 : ℂ) by norm_num]
  rw [← intervalIntegral.integral_add hA_int hB_int]
  change
      (1 / 2 : ℂ) * (∫ x in (0 : ℝ)..1, A x + B x) =
        ∫ x in (0 : ℝ)..1,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * f x
  calc
    (1 / 2 : ℂ) * (∫ x in (0 : ℝ)..1, A x + B x)
        =
          ∫ x in (0 : ℝ)..1, (1 / 2 : ℂ) * (A x + B x) := by
            exact (intervalIntegral.integral_const_mul (μ := volume)
              (a := (0 : ℝ)) (b := 1) (r := (1 / 2 : ℂ))
              (f := fun x : ℝ => A x + B x)).symm
    _ =
        ∫ x in (0 : ℝ)..1,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * f x := by
        apply intervalIntegral.integral_congr
        intro x _hx
        change
          (1 / 2 : ℂ) * (A x + B x) =
            (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * f x
        change
          (1 / 2 : ℂ) *
              (fourier (T := T) n (x : AddCircle T) * f x +
                fourier (T := T) (-n) (x : AddCircle T) * f x) =
            (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * f x
        rw [← add_mul]
        have hcos :
            (1 / 2 : ℂ) *
                (fourier (T := T) n (x : AddCircle T) +
                  fourier (T := T) (-n) (x : AddCircle T)) =
              (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) := by
          let θ : ℂ := ((n : ℝ) * Real.pi * x : ℝ)
          have hpos :
              fourier (T := T) n (x : AddCircle T) =
                Complex.exp (θ * Complex.I) := by
            rw [fourier_coe_apply]
            congr 1
            dsimp [θ, T]
            norm_num
            ring
          have hneg :
              fourier (T := T) (-n) (x : AddCircle T) =
                Complex.exp (-θ * Complex.I) := by
            rw [fourier_coe_apply]
            congr 1
            dsimp [θ, T]
            norm_num
            ring
          rw [hpos, hneg, ← Complex.two_cos]
          rw [← Complex.ofReal_cos]
          ring
        rw [← mul_assoc]
        rw [hcos]

/-- Completeness of the integer-indexed cosine system on the unit interval,
in the totality form needed for the cosine Hilbert-basis transport: if all
cosine coefficients vanish, then the function is zero a.e. on `(0,1]`.

This is the core Parseval/completeness bridge: the even reflection has all
Fourier coefficients zero, hence its Fourier `L²` mass is zero, and the
mass identity transfers that back to the interval. -/
theorem unitIntervalCosine_int_total_ae_zero
    {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 1)
    (hL2 :
      MemLp (unitIntervalEvenReflection f) 2
        (volume.restrict (Set.Ioc (-1 : ℝ) 1)))
    (hf_sq : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1)
    (hcoeff :
      ∀ n : ℤ,
        ∫ x in (0 : ℝ)..1,
          (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * f x = 0) :
    f =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] 0 := by
  have hfourier_zero :
      ∀ n : ℤ,
        fourierCoeffOn (show (-1 : ℝ) < 1 by norm_num)
          (unitIntervalEvenReflection f) n = 0 := by
    intro n
    rw [unitIntervalEvenReflection_fourierCoeffOn_eq_cosineCoeff
      (f := f) hf n, hcoeff n]
  have hmass_zero :
      ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 = 0 := by
    rw [← unitIntervalEvenReflection_fourier_parseval_unit_mass hL2 hf_sq]
    simp [hfourier_zero]
  have hnorm_sq_zero :
      (fun x : ℝ => ‖f x‖ ^ 2)
        =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
          (fun _ : ℝ => (0 : ℝ)) := by
    have hnonneg :
        0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
          (fun x : ℝ => ‖f x‖ ^ 2) :=
      Filter.Eventually.of_forall fun x => sq_nonneg _
    exact
      (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
        (μ := volume) (a := (0 : ℝ)) (b := 1)
        (show (0 : ℝ) ≤ 1 by norm_num) hnonneg hf_sq).mp hmass_zero
  filter_upwards [hnorm_sq_zero] with x hx
  have hx' : ‖f x‖ ^ 2 = 0 := by
    simpa using hx
  have hnorm : ‖f x‖ = 0 := by
    nlinarith [sq_nonneg (‖f x‖)]
  exact norm_eq_zero.mp hnorm

end ShenWork.CosineParsevalBridge
