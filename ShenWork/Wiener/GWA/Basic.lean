import Mathlib
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# The generic weighted-ℓ¹ Banach space `GWA K r`

This file generalizes the committed concrete weighted Wiener algebra (over `ℂ`,
`ShenWork/Wiener/WeightedL1Algebra.lean` + `WeightedL1Complete.lean`) to an
arbitrary complete `ℂ`-Banach-algebra coefficient ring `K`.

`GWA K r` is the bundled type of bilateral sequences `a : ℤ → K` whose weighted
ℓ¹ norm `∑' n, (1+|n|)^r ‖a n‖` is summable.  This brick (E1) delivers the
**Banach space** structure only:

* module-closure lemmas `gMemW_zero/add/neg/smul` and the norm facts
  `gNorm_zero/eq_zero/add_le/smul`;
* instances `Add/Zero/Neg/Sub/SMul ℂ/AddCommGroup/Module ℂ/Norm`;
* `NormedAddCommGroup (GWA K r)` and `NormedSpace ℂ (GWA K r)` via a single
  `NormedSpace.Core ℂ (GWA K r)`;
* `CompleteSpace (GWA K r)` via the weighted isometric equivalence
  `GWA K r ≃ᵢ lp (fun _ : ℤ => K) 1` and `lp.completeSpace`.

The convolution Banach **algebra** (Mul, ring laws, `norm_mul_le`,
`NormedCommRing`) is the next brick (E2).
-/

open scoped BigOperators NNReal ENNReal

namespace ShenWork.GWA

variable {K : Type*} [NormedCommRing K] [NormedAlgebra ℂ K] [CompleteSpace K]

/-- The submultiplicative weight `(1 + |n|)^r` on `ℤ` (`ℝ`-valued, `K`-independent). -/
def gWeight (r : ℕ) (n : ℤ) : ℝ := (1 + |(n : ℝ)|) ^ r

/-- Membership in the generic weighted ℓ¹ space: `(1+|n|)^r ‖a n‖` is summable. -/
def GMemW (r : ℕ) (a : ℤ → K) : Prop := Summable (fun n => gWeight r n * ‖a n‖)

/-- The generic weighted ℓ¹ norm. -/
noncomputable def gNorm (r : ℕ) (a : ℤ → K) : ℝ := ∑' n, gWeight r n * ‖a n‖

/-- The weight is strictly positive. -/
theorem gWeight_pos (r : ℕ) (n : ℤ) : 0 < gWeight r n := by
  have h1 : (0 : ℝ) < 1 + |(n : ℝ)| :=
    lt_of_lt_of_le one_pos (le_add_of_nonneg_right (abs_nonneg _))
  simpa [gWeight] using pow_pos h1 r

/-- The weight is nonnegative. -/
theorem gWeight_nonneg (r : ℕ) (n : ℤ) : 0 ≤ gWeight r n := le_of_lt (gWeight_pos r n)

/-- The weighted summand `(1+|n|)^r ‖a n‖` is nonnegative. -/
theorem gWeightedNorm_nonneg (r : ℕ) (a : ℤ → K) (n : ℤ) :
    0 ≤ gWeight r n * ‖a n‖ := by
  have := gWeight_nonneg r n; positivity

/-! ### Module-closure lemmas. -/

/-- The zero sequence is in the space. -/
theorem gMemW_zero (r : ℕ) : GMemW r (0 : ℤ → K) := by
  have : (fun n => gWeight r n * ‖(0 : ℤ → K) n‖) = fun _ => (0 : ℝ) := by
    funext n; simp
  rw [GMemW, this]; exact summable_zero

/-- Sums stay in the space (termwise triangle inequality + `Summable.add`). -/
theorem gMemW_add {r : ℕ} {a b : ℤ → K} (ha : GMemW r a) (hb : GMemW r b) :
    GMemW r (a + b) := by
  rw [GMemW]
  refine Summable.of_nonneg_of_le (fun n => gWeightedNorm_nonneg r (a + b) n) ?_
    (ha.add hb)
  intro n
  have ht : ‖(a + b) n‖ ≤ ‖a n‖ + ‖b n‖ := by
    simpa [Pi.add_apply] using norm_add_le (a n) (b n)
  calc gWeight r n * ‖(a + b) n‖
      ≤ gWeight r n * (‖a n‖ + ‖b n‖) :=
        mul_le_mul_of_nonneg_left ht (gWeight_nonneg r n)
    _ = gWeight r n * ‖a n‖ + gWeight r n * ‖b n‖ := by ring

/-- Negation stays in the space. -/
theorem gMemW_neg {r : ℕ} {a : ℤ → K} (ha : GMemW r a) : GMemW r (-a) := by
  have : (fun n => gWeight r n * ‖(-a) n‖) = fun n => gWeight r n * ‖a n‖ := by
    funext n; simp [Pi.neg_apply]
  rw [GMemW, this]; exact ha

/-- Scalar multiples (by `ℂ`) stay in the space (`norm_smul` + `Summable.mul_left`). -/
theorem gMemW_smul {r : ℕ} (c : ℂ) {a : ℤ → K} (ha : GMemW r a) : GMemW r (c • a) := by
  have : (fun n => gWeight r n * ‖(c • a) n‖)
      = fun n => ‖c‖ * (gWeight r n * ‖a n‖) := by
    funext n; rw [Pi.smul_apply, norm_smul]; ring
  rw [GMemW, this]; exact ha.mul_left ‖c‖

/-! ### Norm facts. -/

/-- The norm of `0` is `0`. -/
theorem gNorm_zero (r : ℕ) : gNorm r (0 : ℤ → K) = 0 := by
  have : (fun n => gWeight r n * ‖(0 : ℤ → K) n‖) = fun _ => (0 : ℝ) := by
    funext n; simp
  rw [gNorm, this]; exact tsum_zero

/-- The norm is nonnegative (a tsum of nonnegative terms). -/
theorem gNorm_nonneg (r : ℕ) (a : ℤ → K) : 0 ≤ gNorm r a :=
  tsum_nonneg (fun n => gWeightedNorm_nonneg r a n)

/-- `gNorm r a = 0 ↔ a = 0` (a tsum of nonnegative terms vanishes iff each does). -/
theorem gNorm_eq_zero {r : ℕ} {a : ℤ → K} (ha : GMemW r a) : gNorm r a = 0 ↔ a = 0 := by
  constructor
  · intro h
    funext n
    by_contra hne
    have hpos : (0 : ℝ) < gWeight r n * ‖a n‖ := by
      have : (0 : ℝ) < ‖a n‖ := by
        have := norm_nonneg (a n)
        rcases lt_or_eq_of_le this with hlt | heq
        · exact hlt
        · exact absurd (by simpa using heq.symm) (by simpa [Pi.zero_apply] using hne)
      exact mul_pos (gWeight_pos r n) this
    have hposT : (0 : ℝ) < gNorm r a := by
      rw [gNorm]; exact ha.tsum_pos (fun m => gWeightedNorm_nonneg r a m) n hpos
    exact absurd h (ne_of_gt hposT)
  · intro h; rw [h]; exact gNorm_zero r

/-- Triangle inequality for `gNorm`. -/
theorem gNorm_add_le {r : ℕ} {a b : ℤ → K} (ha : GMemW r a) (hb : GMemW r b) :
    gNorm r (a + b) ≤ gNorm r a + gNorm r b := by
  rw [gNorm, gNorm, gNorm, ← Summable.tsum_add ha hb]
  refine Summable.tsum_mono (gMemW_add ha hb) (ha.add hb) ?_
  intro n
  have ht : ‖(a + b) n‖ ≤ ‖a n‖ + ‖b n‖ := by
    simpa [Pi.add_apply] using norm_add_le (a n) (b n)
  calc gWeight r n * ‖(a + b) n‖
      ≤ gWeight r n * (‖a n‖ + ‖b n‖) :=
        mul_le_mul_of_nonneg_left ht (gWeight_nonneg r n)
    _ = gWeight r n * ‖a n‖ + gWeight r n * ‖b n‖ := by ring

/-- `gNorm` is absolutely homogeneous (`norm_smul` + `tsum_mul_left`). -/
theorem gNorm_smul {r : ℕ} (c : ℂ) {a : ℤ → K} : gNorm r (c • a) = ‖c‖ * gNorm r a := by
  rw [gNorm, gNorm, ← tsum_mul_left]
  refine tsum_congr ?_
  intro n
  rw [Pi.smul_apply, norm_smul]; ring

/-! ### The bundled type and its algebraic instances. -/

/-- The bundled generic weighted Wiener space `GWA K r`: sequences in `GMemW r`. -/
structure GWA (K : Type*) [NormedCommRing K] [NormedAlgebra ℂ K] (r : ℕ) where
  /-- The underlying sequence. -/
  toFun : ℤ → K
  /-- Membership witness: the generic weighted ℓ¹ summability. -/
  mem : GMemW r toFun

namespace GWA

variable {r : ℕ}

@[ext]
theorem ext {a b : GWA K r} (h : a.toFun = b.toFun) : a = b := by
  cases a; cases b; cases h; rfl

/-- Componentwise addition. -/
instance : Add (GWA K r) := ⟨fun a b => ⟨a.toFun + b.toFun, gMemW_add a.mem b.mem⟩⟩
/-- The zero element. -/
instance : Zero (GWA K r) := ⟨⟨0, gMemW_zero r⟩⟩
/-- Componentwise negation. -/
instance : Neg (GWA K r) := ⟨fun a => ⟨-a.toFun, gMemW_neg a.mem⟩⟩
/-- Componentwise subtraction. -/
instance : Sub (GWA K r) := ⟨fun a b => ⟨a.toFun - b.toFun, by
  have : a.toFun - b.toFun = a.toFun + -b.toFun := by ring
  rw [this]; exact gMemW_add a.mem (gMemW_neg b.mem)⟩⟩
/-- Scalar multiplication by `ℂ`. -/
instance : SMul ℂ (GWA K r) := ⟨fun c a => ⟨c • a.toFun, gMemW_smul c a.mem⟩⟩
/-- Scalar multiplication by `ℕ` (for the `AddCommGroup` `nsmul` field). -/
instance : SMul ℕ (GWA K r) := ⟨fun k a => ⟨(k : ℂ) • a.toFun, gMemW_smul (k : ℂ) a.mem⟩⟩
/-- Scalar multiplication by `ℤ` (for the `AddCommGroup` `zsmul` field). -/
instance : SMul ℤ (GWA K r) := ⟨fun k a => ⟨(k : ℂ) • a.toFun, gMemW_smul (k : ℂ) a.mem⟩⟩

@[simp] theorem add_toFun (a b : GWA K r) : (a + b).toFun = a.toFun + b.toFun := rfl
@[simp] theorem zero_toFun : (0 : GWA K r).toFun = 0 := rfl
@[simp] theorem neg_toFun (a : GWA K r) : (-a).toFun = -a.toFun := rfl
@[simp] theorem sub_toFun (a b : GWA K r) : (a - b).toFun = a.toFun - b.toFun := rfl
@[simp] theorem smul_toFun (c : ℂ) (a : GWA K r) : (c • a).toFun = c • a.toFun := rfl
@[simp] theorem nsmul_toFun (k : ℕ) (a : GWA K r) :
    (k • a).toFun = (k : ℂ) • a.toFun := rfl
@[simp] theorem zsmul_toFun (k : ℤ) (a : GWA K r) :
    (k • a).toFun = (k : ℂ) • a.toFun := rfl

instance : AddCommGroup (GWA K r) where
  add_assoc a b c := by ext; simp [add_assoc]
  zero_add a := by ext; simp
  add_zero a := by ext; simp
  add_comm a b := by ext; simp [add_comm]
  neg_add_cancel a := by ext; simp
  sub_eq_add_neg a b := by ext; simp [sub_eq_add_neg]
  nsmul := (· • ·)
  nsmul_zero a := by ext n; simp
  nsmul_succ k a := by
    ext n; simp only [nsmul_toFun, add_toFun, Pi.add_apply, Pi.smul_apply]
    push_cast; rw [add_smul, one_smul]
  zsmul := (· • ·)
  zsmul_zero' a := by ext n; simp
  zsmul_succ' k a := by
    ext n
    simp only [zsmul_toFun, add_toFun, Pi.add_apply, Pi.smul_apply]
    push_cast; rw [add_smul, one_smul]
  zsmul_neg' k a := by
    ext n
    simp only [zsmul_toFun, neg_toFun, Pi.neg_apply, Pi.smul_apply]
    push_cast; rw [neg_smul, add_smul, one_smul]

instance : Module ℂ (GWA K r) where
  one_smul a := by ext n; simp
  mul_smul x y a := by ext n; simp only [smul_toFun, Pi.smul_apply]; rw [mul_smul]
  smul_zero c := by ext n; simp
  smul_add c a b := by
    ext n; simp only [smul_toFun, add_toFun, Pi.add_apply, Pi.smul_apply]; rw [smul_add]
  add_smul x y a := by
    ext n; simp only [smul_toFun, add_toFun, Pi.add_apply, Pi.smul_apply]; rw [add_smul]
  zero_smul a := by ext n; simp

/-- The generic Wiener norm on the bundled type. -/
noncomputable instance : Norm (GWA K r) := ⟨fun a => gNorm r a.toFun⟩

@[simp] theorem norm_def (a : GWA K r) : ‖a‖ = gNorm r a.toFun := rfl

/-- The `NormedSpace.Core` for `GWA K r`: nonnegativity, homogeneity, triangle,
and `‖·‖ = 0 ↔ · = 0`.  This packages the `NormedAddCommGroup` and `NormedSpace`. -/
noncomputable def normCore : NormedSpace.Core ℂ (GWA K r) where
  norm_nonneg a := gNorm_nonneg r a.toFun
  norm_smul c a := by
    show gNorm r ((c • a).toFun) = ‖c‖ * gNorm r a.toFun
    rw [smul_toFun, gNorm_smul]
  norm_triangle a b := by
    show gNorm r ((a + b).toFun) ≤ gNorm r a.toFun + gNorm r b.toFun
    rw [add_toFun]; exact gNorm_add_le a.mem b.mem
  norm_eq_zero_iff a := by
    show gNorm r a.toFun = 0 ↔ a = 0
    rw [gNorm_eq_zero a.mem]
    exact ⟨fun h => GWA.ext (by simpa using h),
      fun h => by simpa using congrArg GWA.toFun h⟩

/-- `GWA K r` is a normed additive commutative group (norm = `gNorm`). -/
noncomputable instance : NormedAddCommGroup (GWA K r) := NormedAddCommGroup.ofCore normCore

/-- `GWA K r` is a normed `ℂ`-vector space. -/
noncomputable instance : NormedSpace ℂ (GWA K r) := NormedSpace.ofCore normCore

/-! ### Completeness via the weighted isometry to `lp (fun _:ℤ=>K) 1`. -/

/-- The weight is nonzero as a complex scalar. -/
theorem gWeight_ne_zero (r : ℕ) (n : ℤ) : (gWeight r n : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt (gWeight_pos r n)

/-- The pointwise scaled-norm identity: `‖(gWeight r n:ℂ) • x‖ = gWeight r n * ‖x‖`. -/
theorem norm_gWeight_smul (r : ℕ) (n : ℤ) (x : K) :
    ‖(gWeight r n : ℂ) • x‖ = gWeight r n * ‖x‖ := by
  rw [norm_smul, Complex.norm_of_nonneg (gWeight_nonneg r n)]

/-- `p = 1` has `(1 : ℝ≥0∞).toReal = 1 > 0`. -/
theorem one_toReal_pos : (0 : ℝ) < ((1 : ℝ≥0∞).toReal) := by simp

/-- **Membership translation.**
`Memℓp (fun n => (gWeight r n:ℂ) • a n) 1 ↔ GMemW r a`. -/
theorem memℓp_one_weighted_iff (r : ℕ) (a : ℤ → K) :
    Memℓp (fun n => (gWeight r n : ℂ) • a n) (1 : ℝ≥0∞) ↔ GMemW r a := by
  rw [memℓp_gen_iff one_toReal_pos]
  have htr : ((1 : ℝ≥0∞).toReal) = 1 := by simp
  rw [GMemW]
  refine summable_congr (fun n => ?_)
  rw [htr, Real.rpow_one, norm_gWeight_smul]

/-- The weighted map sends a `GMemW`-witnessed sequence to a member of `lp .. 1`. -/
theorem memℓp_of_gMemW {a : ℤ → K} (ha : GMemW r a) :
    Memℓp (fun n => (gWeight r n : ℂ) • a n) (1 : ℝ≥0∞) :=
  (memℓp_one_weighted_iff r a).mpr ha

/-- The unscaled sequence of an `lp .. 1` element is in `GMemW r`. -/
theorem gMemW_of_lp (g : lp (fun _ : ℤ => K) 1) :
    GMemW r (fun n => (gWeight r n : ℂ)⁻¹ • (g : ℤ → K) n) := by
  refine (memℓp_one_weighted_iff r
    (fun n => (gWeight r n : ℂ)⁻¹ • (g : ℤ → K) n)).mp ?_
  have hcongr : (fun n => (gWeight r n : ℂ) • ((gWeight r n : ℂ)⁻¹ • (g : ℤ → K) n))
      = fun n => (g : ℤ → K) n := by
    funext n
    rw [smul_smul, mul_inv_cancel₀ (gWeight_ne_zero r n), one_smul]
  rw [hcongr]
  exact lp.memℓp g

/-- The forward function `GWA K r → lp (fun _:ℤ=>K) 1`. -/
noncomputable def toLpFun (a : GWA K r) : lp (fun _ : ℤ => K) 1 :=
  ⟨fun n => (gWeight r n : ℂ) • a.toFun n, memℓp_of_gMemW a.mem⟩

/-- The inverse function `lp (fun _:ℤ=>K) 1 → GWA K r`. -/
noncomputable def ofLpFun (r : ℕ) (g : lp (fun _ : ℤ => K) 1) : GWA K r :=
  ⟨fun n => (gWeight r n : ℂ)⁻¹ • (g : ℤ → K) n, gMemW_of_lp g⟩

@[simp] theorem toLpFun_coe (a : GWA K r) (n : ℤ) :
    (toLpFun a : ℤ → K) n = (gWeight r n : ℂ) • a.toFun n := rfl

@[simp] theorem ofLpFun_toFun (r : ℕ) (g : lp (fun _ : ℤ => K) 1) (n : ℤ) :
    (ofLpFun r g).toFun n = (gWeight r n : ℂ)⁻¹ • (g : ℤ → K) n := rfl

/-- The weighted bijection between `GWA K r` and `lp (fun _:ℤ=>K) 1`. -/
noncomputable def weightEquiv (r : ℕ) : GWA K r ≃ lp (fun _ : ℤ => K) 1 where
  toFun := toLpFun
  invFun := ofLpFun r
  left_inv a := by
    apply GWA.ext
    funext n
    rw [ofLpFun_toFun, toLpFun_coe, smul_smul, inv_mul_cancel₀ (gWeight_ne_zero r n),
      one_smul]
  right_inv g := by
    apply lp.ext
    funext n
    rw [toLpFun_coe, ofLpFun_toFun, smul_smul, mul_inv_cancel₀ (gWeight_ne_zero r n),
      one_smul]

/-- The `lp`-`1` norm of `Φ a` equals `gNorm r a.toFun = ‖a‖`. -/
theorem norm_toLpFun (a : GWA K r) : ‖toLpFun a‖ = ‖a‖ := by
  rw [lp.norm_eq_tsum_rpow one_toReal_pos, norm_def, gNorm]
  have htr : ((1 : ℝ≥0∞).toReal) = 1 := by simp
  have hsum : (∑' n, ‖(toLpFun a : ℤ → K) n‖ ^ ((1 : ℝ≥0∞).toReal))
      = ∑' n, gWeight r n * ‖a.toFun n‖ := by
    refine tsum_congr (fun n => ?_)
    rw [toLpFun_coe, htr, Real.rpow_one, norm_gWeight_smul]
  rw [hsum, htr, one_div_one, Real.rpow_one]

/-- `Φ` is an isometry. -/
theorem isometry_toLpFun : Isometry (toLpFun (K := K) (r := r)) := by
  refine Isometry.of_dist_eq (fun a b => ?_)
  rw [dist_eq_norm, dist_eq_norm]
  have hsub : toLpFun a - toLpFun b = toLpFun (a - b) := by
    apply lp.ext
    funext n
    rw [lp.coeFn_sub, Pi.sub_apply, toLpFun_coe, toLpFun_coe, toLpFun_coe,
      sub_toFun, Pi.sub_apply, smul_sub]
  rw [hsub]
  exact norm_toLpFun (a - b)

/-- The weighted **isometric equivalence** `GWA K r ≃ᵢ lp (fun _:ℤ=>K) 1`. -/
noncomputable def weightIsometryEquiv (r : ℕ) : GWA K r ≃ᵢ lp (fun _ : ℤ => K) 1 where
  toEquiv := weightEquiv r
  isometry_toFun := isometry_toLpFun

/-- **`GWA K r` is a complete metric space** — completeness transfers from
`lp.completeSpace` (the fiber `K` is complete) through the weighted isometry. -/
noncomputable instance instCompleteSpace : CompleteSpace (GWA K r) :=
  (weightIsometryEquiv r).completeSpace_iff.mpr lp.completeSpace

/-- Sanity test lemma exercising the `Norm` instance. -/
theorem test_norm (a : GWA K r) : ‖a‖ = gNorm r a.toFun := rfl

/-- Sanity test: `ℂ` is a valid coefficient ring `K`, so the `CompleteSpace`
instance fires on `GWA ℂ 1`. -/
example : CompleteSpace (GWA ℂ 1) := inferInstance

end GWA

end ShenWork.GWA
