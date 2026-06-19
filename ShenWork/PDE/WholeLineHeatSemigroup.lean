import ShenWork.PDE.HeatSemigroup
open MeasureTheory Real
noncomputable section
def wholeLineHeatKernel (t z : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-(z ^ 2) / (4 * t))
def wholeLineHeatOp (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-t) * ∫ y : ℝ, wholeLineHeatKernel t (x - y) * f y
def wholeLineHeatGradOp (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-t) * ∫ y : ℝ, deriv (fun z : ℝ => wholeLineHeatKernel t (z - y)) x * f y
lemma wholeLineHeatKernel_eq_heatKernel {t : ℝ} (ht : 0 < t) (z : ℝ) :
    wholeLineHeatKernel t z = heatKernel t z := by
  unfold wholeLineHeatKernel heatKernel
  have hpos : 0 < 4 * Real.pi * t := by positivity
  rw [Real.rpow_neg hpos.le, ← Real.sqrt_eq_rpow]
  ring
lemma wholeLineHeatKernel_deriv_eq_heatKernel_deriv {t : ℝ} (ht : 0 < t)
    (x y : ℝ) :
    deriv (fun z : ℝ => wholeLineHeatKernel t (z - y)) x =
      deriv (fun z : ℝ => heatKernel t (z - y)) x := by
  rw [show (fun z : ℝ => wholeLineHeatKernel t (z - y)) =
      fun z : ℝ => heatKernel t (z - y) by
    funext z
    exact wholeLineHeatKernel_eq_heatKernel ht (z - y)]
lemma wholeLineHeat_deriv_const_eq {t : ℝ} (ht : 0 < t) :
    2 / Real.sqrt (4 * Real.pi * t) = (Real.pi * t) ^ (-(1 / 2 : ℝ)) := by
  have hpit : 0 < Real.pi * t := by positivity
  have hsqrt : Real.sqrt (4 * Real.pi * t) = 2 * Real.sqrt (Real.pi * t) := by
    rw [show (4 * Real.pi * t : ℝ) = 4 * (Real.pi * t) by ring]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) (Real.pi * t)]
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h4]
  rw [hsqrt]
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hs : Real.sqrt (Real.pi * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpit)
  rw [Real.rpow_neg hpit.le, ← Real.sqrt_eq_rpow]
  field_simp [h2, hs]
theorem wholeLineHeat_mass_one {t : ℝ} (ht : 0 < t) :
    ∫ z : ℝ, wholeLineHeatKernel t z = 1 := by
  simpa [wholeLineHeatKernel_eq_heatKernel ht] using heatKernel_integral_eq_one ht
lemma wholeLineHeatOp_eq_modifiedSemigroup {t : ℝ} (ht : 0 < t)
    (f : ℝ → ℝ) (x : ℝ) :
    wholeLineHeatOp t f x = modifiedSemigroup t f x := by
  unfold wholeLineHeatOp modifiedSemigroup heatSemigroup
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [wholeLineHeatKernel_eq_heatKernel ht (x - y)]
theorem wholeLineHeatOp_sup_le {f : ℝ → ℝ} {M t : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) (hf : ∀ y, |f y| ≤ M)
    (hf_meas : AEStronglyMeasurable f volume) (x : ℝ) :
    |wholeLineHeatOp t f x| ≤ Real.exp (-t) * M := by
  rw [wholeLineHeatOp_eq_modifiedSemigroup ht f x]
  exact modifiedSemigroup_Linfty_bound hf ht hM hf_meas x
theorem wholeLineHeatKernel_deriv_abs_integral {t : ℝ} (ht : 0 < t) :
    ∫ z : ℝ, |deriv (fun w : ℝ => wholeLineHeatKernel t w) z| =
      (Real.pi * t) ^ (-(1 / 2 : ℝ)) := by
  simpa [wholeLineHeatKernel_eq_heatKernel ht, wholeLineHeat_deriv_const_eq ht]
    using heatKernel_deriv_abs_integral ht
theorem wholeLineHeatGradOp_eq_deriv {f : ℝ → ℝ} {t : ℝ}
    (ht : 0 < t) (hf_int : Integrable f) (x : ℝ) :
    wholeLineHeatGradOp t f x = deriv (fun z : ℝ => wholeLineHeatOp t f z) x := by
  unfold wholeLineHeatGradOp
  have hop : (fun z : ℝ => wholeLineHeatOp t f z) =
      fun z : ℝ => modifiedSemigroup t f z := by
    funext z
    exact wholeLineHeatOp_eq_modifiedSemigroup ht f z
  rw [hop, deriv_modifiedSemigroup ht x hf_int]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [wholeLineHeatKernel_deriv_eq_heatKernel_deriv ht x y]
theorem wholeLineHeatGrad_sup_le {f : ℝ → ℝ} {M t : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) (hf : ∀ y, |f y| ≤ M)
    (hf_int : Integrable f) (x : ℝ) :
    |deriv (fun z : ℝ => wholeLineHeatOp t f z) x| ≤
      Real.exp (-t) * ((Real.pi * t) ^ (-(1 / 2 : ℝ)) * M) := by
  rw [← wholeLineHeatGradOp_eq_deriv ht hf_int x]
  unfold wholeLineHeatGradOp
  rw [← MeasureTheory.integral_const_mul]
  rw [show
      (∫ y : ℝ,
          Real.exp (-t) *
            (deriv (fun z : ℝ => wholeLineHeatKernel t (z - y)) x * f y)) =
        ∫ y : ℝ,
          Real.exp (-t) *
            (deriv (fun z : ℝ => heatKernel t (z - y)) x * f y) by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [wholeLineHeatKernel_deriv_eq_heatKernel_deriv ht x y]]
  have h := modifiedHeatKernel_deriv_convolution_bounded_abs_le
    (t := t) (M := M) ht hM (f := f) hf x
  refine h.trans_eq ?_
  rw [wholeLineHeat_deriv_const_eq ht]
#print axioms wholeLineHeat_mass_one
#print axioms wholeLineHeatOp_sup_le
#print axioms wholeLineHeatKernel_deriv_abs_integral
#print axioms wholeLineHeatGradOp_eq_deriv
#print axioms wholeLineHeatGrad_sup_le
