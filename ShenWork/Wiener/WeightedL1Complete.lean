import ShenWork.Wiener.WeightedL1Algebra
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Brick 4b-ii — `CompleteSpace (WA r)` via the weighted-ℓ¹ isometry

This file closes the brick-4b stall by equipping the bundled weighted Wiener
algebra `WA r` with a `CompleteSpace` instance.

The route is an **isometric equivalence**

  `Φ r : WA r ≃ᵢ lp (fun _ : ℤ => ℂ) 1`

given by the weighted-sequence map `a ↦ (n ↦ (wWeight r n : ℂ) * a.toFun n)`,
with inverse `g ↦ (n ↦ g n / (wWeight r n : ℂ))` (well-defined since
`wWeight r n > 0`).  Completeness transfers from `lp.completeSpace` (valid for
`1 ≤ p`) through `IsometryEquiv.completeSpace_iff`.

The two technical translations:

* `memℓp_one_weighted_iff` : `Memℓp (fun n => (wWeight r n:ℂ)*a n) 1 ↔ MemW r a`,
  proved through `lp.memℓp_gen_iff` (with `p.toReal = 1`) which reduces `Memℓp f 1`
  to `Summable ‖f·‖`, plus the cast identity
  `‖(wWeight r n:ℂ)*x‖ = wWeight r n * ‖x‖` (`Complex.norm_of_nonneg`).
* the **isometry** `‖Φ a‖ = ‖a‖`, obtained by unfolding the `lp`-`1` norm with
  `lp.norm_eq_tsum_rpow` (here `p.toReal = 1`, so `rpow 1` and `^(1/1)` are the
  identity) into `∑' n, wWeight r n * ‖a.toFun n‖ = wNorm r a.toFun`.
-/

open scoped BigOperators NNReal ENNReal

namespace ShenWork.Wiener

namespace WA

variable {r : ℕ}

/-- The weight is strictly positive. -/
theorem wWeight_pos (r : ℕ) (n : ℤ) : 0 < wWeight r n := by
  have h1 : (0 : ℝ) < 1 + |(n : ℝ)| :=
    lt_of_lt_of_le one_pos (le_add_of_nonneg_right (abs_nonneg _))
  simpa [wWeight] using pow_pos h1 r

/-- The weight is nonzero as a complex number. -/
theorem wWeight_ne_zero (r : ℕ) (n : ℤ) : (wWeight r n : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt (wWeight_pos r n)

/-- The pointwise cast-norm identity: `‖(wWeight r n:ℂ) * x‖ = wWeight r n * ‖x‖`. -/
theorem norm_wWeight_mul (r : ℕ) (n : ℤ) (x : ℂ) :
    ‖(wWeight r n : ℂ) * x‖ = wWeight r n * ‖x‖ := by
  rw [norm_mul, Complex.norm_of_nonneg (le_of_lt (wWeight_pos r n))]

/-! ### The `Memℓp ↔ MemW` translation. -/

/-- `p = 1` has `(1 : ℝ≥0∞).toReal = 1 > 0`. -/
theorem one_toReal_pos : (0 : ℝ) < ((1 : ℝ≥0∞).toReal) := by simp

/-- **Forward/backward membership translation.**
`Memℓp (fun n => (wWeight r n:ℂ)*a n) 1 ↔ MemW r a`. -/
theorem memℓp_one_weighted_iff (r : ℕ) (a : ℤ → ℂ) :
    Memℓp (fun n => (wWeight r n : ℂ) * a n) (1 : ℝ≥0∞) ↔ MemW r a := by
  rw [memℓp_gen_iff one_toReal_pos]
  have htr : ((1 : ℝ≥0∞).toReal) = 1 := by simp
  rw [MemW]
  refine summable_congr (fun n => ?_)
  rw [htr, Real.rpow_one, norm_wWeight_mul]

/-- The weighted map sends a `MemW`-witnessed sequence to a member of `lp .. 1`. -/
theorem memℓp_of_memW {a : ℤ → ℂ} (ha : MemW r a) :
    Memℓp (fun n => (wWeight r n : ℂ) * a n) (1 : ℝ≥0∞) :=
  (memℓp_one_weighted_iff r a).mpr ha

/-- The unweighted/divided sequence of an `lp .. 1` element is in `MemW r`. -/
theorem memW_of_lp (g : lp (fun _ : ℤ => ℂ) 1) :
    MemW r (fun n => (g : ℤ → ℂ) n / (wWeight r n : ℂ)) := by
  refine (memℓp_one_weighted_iff r (fun n => (g : ℤ → ℂ) n / (wWeight r n : ℂ))).mp ?_
  have hcongr : (fun n => (wWeight r n : ℂ) * ((g : ℤ → ℂ) n / (wWeight r n : ℂ)))
      = fun n => (g : ℤ → ℂ) n := by
    funext n
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self (wWeight_ne_zero r n), mul_one]
  rw [hcongr]
  exact lp.memℓp g

/-! ### The bijection `Equiv`. -/

/-- The forward function `WA r → lp (fun _:ℤ=>ℂ) 1`. -/
noncomputable def toLpFun (a : WA r) : lp (fun _ : ℤ => ℂ) 1 :=
  ⟨fun n => (wWeight r n : ℂ) * a.toFun n, memℓp_of_memW a.mem⟩

/-- The inverse function `lp (fun _:ℤ=>ℂ) 1 → WA r`. -/
noncomputable def ofLpFun (r : ℕ) (g : lp (fun _ : ℤ => ℂ) 1) : WA r :=
  ⟨fun n => (g : ℤ → ℂ) n / (wWeight r n : ℂ), memW_of_lp g⟩

@[simp] theorem toLpFun_coe (a : WA r) (n : ℤ) :
    (toLpFun a : ℤ → ℂ) n = (wWeight r n : ℂ) * a.toFun n := rfl

@[simp] theorem ofLpFun_toFun (r : ℕ) (g : lp (fun _ : ℤ => ℂ) 1) (n : ℤ) :
    (ofLpFun r g).toFun n = (g : ℤ → ℂ) n / (wWeight r n : ℂ) := rfl

/-- The weighted bijection between `WA r` and `lp (fun _:ℤ=>ℂ) 1`. -/
noncomputable def weightEquiv (r : ℕ) : WA r ≃ lp (fun _ : ℤ => ℂ) 1 where
  toFun := toLpFun
  invFun := ofLpFun r
  left_inv a := by
    apply WA.ext
    funext n
    rw [ofLpFun_toFun, toLpFun_coe, mul_comm, mul_div_assoc,
      div_self (wWeight_ne_zero r n), mul_one]
  right_inv g := by
    apply lp.ext
    funext n
    rw [toLpFun_coe, ofLpFun_toFun, mul_div_assoc', mul_comm, mul_div_assoc,
      div_self (wWeight_ne_zero r n), mul_one]

/-! ### The isometry. -/

/-- The `lp`-`1` norm of `Φ a` equals `wNorm r a.toFun = ‖a‖`. -/
theorem norm_toLpFun (a : WA r) : ‖toLpFun a‖ = ‖a‖ := by
  rw [lp.norm_eq_tsum_rpow one_toReal_pos, norm_def, wNorm]
  have htr : ((1 : ℝ≥0∞).toReal) = 1 := by simp
  have hsum : (∑' n, ‖(toLpFun a : ℤ → ℂ) n‖ ^ ((1 : ℝ≥0∞).toReal))
      = ∑' n, wWeight r n * ‖a.toFun n‖ := by
    refine tsum_congr (fun n => ?_)
    rw [toLpFun_coe, htr, Real.rpow_one, norm_wWeight_mul]
  rw [hsum, htr, one_div_one, Real.rpow_one]

/-- `Φ` is an isometry: `dist (Φ a) (Φ b) = dist a b`. -/
theorem isometry_toLpFun : Isometry (toLpFun (r := r)) := by
  refine Isometry.of_dist_eq (fun a b => ?_)
  rw [dist_eq_norm, dist_eq_norm]
  have hsub : toLpFun a - toLpFun b = toLpFun (a - b) := by
    apply lp.ext
    funext n
    rw [lp.coeFn_sub, Pi.sub_apply, toLpFun_coe, toLpFun_coe, toLpFun_coe,
      sub_toFun, Pi.sub_apply, mul_sub]
  rw [hsub]
  exact norm_toLpFun (a - b)

/-- The weighted **isometric equivalence** `WA r ≃ᵢ lp (fun _:ℤ=>ℂ) 1`. -/
noncomputable def weightIsometryEquiv (r : ℕ) : WA r ≃ᵢ lp (fun _ : ℤ => ℂ) 1 where
  toEquiv := weightEquiv r
  isometry_toFun := isometry_toLpFun

/-! ### Completeness transfer. -/

/-- **`WA r` is a complete metric space** — completeness transfers from
`lp.completeSpace` through the weighted isometric equivalence. -/
noncomputable instance instCompleteSpace : CompleteSpace (WA r) :=
  (weightIsometryEquiv r).completeSpace_iff.mpr lp.completeSpace

/-- Sanity test: the `CompleteSpace` instance is found by typeclass resolution. -/
theorem test_complete : CompleteSpace (WA 1) := inferInstance

end WA

end ShenWork.Wiener
