import ShenWork.PDE.HeatSemigroup
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# The eigenvalue-ℓ¹ complete normed space `EigenL1`

Crux (B) of the route-(A) `χ₀ < 0` cosine-coefficient construction: the complete
normed space in which the Duhamel coefficient map becomes a contraction.

`EigenL1` is the space of real sequences `a : ℕ → ℝ` with finite **eigenvalue-ℓ¹**
norm
$$ \|a\| = \sum_n \lambda_n\,|a_n|, \qquad \lambda_n = (n\pi)^2 $$
where `λ_n = unitIntervalCosineEigenvalue n` (`HeatSemigroup.lean:1507`).  The
membership predicate is exactly
`Summable (fun n => unitIntervalCosineEigenvalue n * |a n|)`, i.e. the hypothesis
that the committed `cosineCoeffSeries_contDiff_two` engine consumes to produce
a `C²` cosine series.

The construction **mirrors** `ShenWork/Wiener/WeightedL1Complete.lean` (the bundled
weighted Wiener algebra `WA r`), translating:

* index `ℤ → ℕ`,
* scalar `ℂ → ℝ`,
* weight `wWeight r n → unitIntervalCosineEigenvalue n = (nπ)²`.

The completeness is transferred from `lp.completeSpace` (`p = 1`) through the
weighted isometric equivalence `EigenL1 ≃ᵢ lp (fun _ : ℕ => ℝ) 1`, exactly as in
the committed Wiener file (`weightIsometryEquiv`, `instCompleteSpace`).

A subtlety vs. `WA r`: the weight `λ_n` **vanishes at `n = 0`** (`λ_0 = 0`), so the
weighted map `a ↦ (n ↦ λ_n · a_n)` is *not* injective — it forgets `a_0`.  We
therefore bundle the coefficient `a_0` separately in the isometry's target
`ℝ × lp (fun _ : ℕ => ℝ) 1` is **not** needed: the *norm* ignores `a_0`
(`λ_0 = 0`), so the seminorm degenerates and is genuinely zero on `a` supported at
`0`.  To keep an honest `NormedAddCommGroup` (norm separates points) we use the
**index `{n // n ≠ 0}`** in the `lp` target and prove `‖a‖ = 0 ↔ a = 0` directly
from `λ_n > 0` for `n ≠ 0` together with the convention that membership forces the
sum over `n ≠ 0`; but since `a_0` carries weight `0`, `‖a‖ = 0` does **not** force
`a_0 = 0`.  Hence the eigenvalue-ℓ¹ object is a genuine **seminormed** space, not
normed, unless we quotient or restrict.  We expose both:

* `EigenL1` — the bundled subtype with its `SeminormedAddCommGroup` and the
  `λ_n`-weighted seminorm; and
* the honest `NormedAddCommGroup` is obtained on the natural target by the
  isometry to `lp (fun _ : {n : ℕ // n ≠ 0} => ℝ) 1` once `a_0` is pinned.

For the fixed-point engine we deliver the **complete** structure plus the
membership ↔ `Summable (λ_n |a_n|)` bridge.
-/

open scoped BigOperators NNReal ENNReal

namespace ShenWork.PDE

/-- The Neumann cosine eigenvalue `λ_n = (nπ)²` is nonnegative. -/
theorem unitIntervalCosineEigenvalue_nonneg (n : ℕ) :
    0 ≤ unitIntervalCosineEigenvalue n := by
  unfold unitIntervalCosineEigenvalue; positivity

/-- The eigenvalue `λ_n = (nπ)²` is strictly positive for `n ≠ 0`. -/
theorem unitIntervalCosineEigenvalue_pos {n : ℕ} (hn : n ≠ 0) :
    0 < unitIntervalCosineEigenvalue n := by
  unfold unitIntervalCosineEigenvalue
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  positivity

/-! ### The membership predicate, norm, and bundled type. -/

/-- Eigenvalue-ℓ¹ membership: `Σ_n λ_n |a_n|` converges. -/
def MemEig (a : ℕ → ℝ) : Prop :=
  Summable (fun n => unitIntervalCosineEigenvalue n * |a n|)

/-- The eigenvalue-ℓ¹ (semi)norm `‖a‖ = Σ_n λ_n |a_n|`. -/
noncomputable def eigNorm (a : ℕ → ℝ) : ℝ :=
  ∑' n, unitIntervalCosineEigenvalue n * |a n|

/-- The bundled eigenvalue-ℓ¹ space: real sequences with finite eigenvalue-ℓ¹
norm.  This is the metric space of the cosine-coefficient fixed-point engine. -/
structure EigenL1 where
  /-- The underlying coefficient sequence. -/
  toFun : ℕ → ℝ
  /-- Membership witness: the eigenvalue-ℓ¹ summability. -/
  mem : MemEig toFun

namespace EigenL1

@[ext]
theorem ext {a b : EigenL1} (h : a.toFun = b.toFun) : a = b := by
  cases a; cases b; cases h; rfl

/-! ### Membership-closure lemmas (mirror `memW_*`). -/

/-- The zero sequence is in `EigenL1`. -/
theorem memEig_zero : MemEig (0 : ℕ → ℝ) := by
  have : (fun n => unitIntervalCosineEigenvalue n * |(0 : ℕ → ℝ) n|)
      = fun _ => (0 : ℝ) := by funext n; simp
  rw [MemEig, this]; exact summable_zero

/-- Sums stay in `EigenL1` (termwise triangle inequality + `Summable.add`). -/
theorem memEig_add {a b : ℕ → ℝ} (ha : MemEig a) (hb : MemEig b) :
    MemEig (a + b) := by
  rw [MemEig]
  refine Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => ?_) (ha.add hb)
  rw [Pi.add_apply]
  calc unitIntervalCosineEigenvalue n * |a n + b n|
      ≤ unitIntervalCosineEigenvalue n * (|a n| + |b n|) := by
        apply mul_le_mul_of_nonneg_left (abs_add _ _)
          (unitIntervalCosineEigenvalue_nonneg n)
    _ = unitIntervalCosineEigenvalue n * |a n|
        + unitIntervalCosineEigenvalue n * |b n| := by ring

/-- Negation stays in `EigenL1`. -/
theorem memEig_neg {a : ℕ → ℝ} (ha : MemEig a) : MemEig (-a) := by
  rw [MemEig]
  have : (fun n => unitIntervalCosineEigenvalue n * |(-a) n|)
      = fun n => unitIntervalCosineEigenvalue n * |a n| := by
    funext n; rw [Pi.neg_apply, abs_neg]
  rw [this]; exact ha

/-- Scalar multiples stay in `EigenL1`. -/
theorem memEig_smul (c : ℝ) {a : ℕ → ℝ} (ha : MemEig a) : MemEig (c • a) := by
  rw [MemEig]
  have : (fun n => unitIntervalCosineEigenvalue n * |(c • a) n|)
      = fun n => |c| * (unitIntervalCosineEigenvalue n * |a n|) := by
    funext n; rw [Pi.smul_apply, smul_eq_mul, abs_mul]; ring
  rw [this]; exact ha.mul_left _

/-! ### Norm facts (mirror `wNorm_*`). -/

/-- The eigenvalue-ℓ¹ norm is nonnegative. -/
theorem eigNorm_nonneg (a : ℕ → ℝ) : 0 ≤ eigNorm a := by
  rw [eigNorm]
  exact tsum_nonneg (fun n => by positivity)

/-- Homogeneity of the eigenvalue-ℓ¹ norm. -/
theorem eigNorm_smul (c : ℝ) (a : ℕ → ℝ) : eigNorm (c • a) = |c| * eigNorm a := by
  rw [eigNorm, eigNorm, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]; ring

/-- Triangle inequality for the eigenvalue-ℓ¹ norm. -/
theorem eigNorm_add_le {a b : ℕ → ℝ} (ha : MemEig a) (hb : MemEig b) :
    eigNorm (a + b) ≤ eigNorm a + eigNorm b := by
  rw [eigNorm, eigNorm, eigNorm, ← tsum_add ha hb]
  refine tsum_le_tsum (fun n => ?_) (memEig_add ha hb) (ha.add hb)
  rw [Pi.add_apply]
  calc unitIntervalCosineEigenvalue n * |a n + b n|
      ≤ unitIntervalCosineEigenvalue n * (|a n| + |b n|) := by
        apply mul_le_mul_of_nonneg_left (abs_add _ _)
          (unitIntervalCosineEigenvalue_nonneg n)
    _ = unitIntervalCosineEigenvalue n * |a n|
        + unitIntervalCosineEigenvalue n * |b n| := by ring

end EigenL1

/-! ### Algebraic instances on `EigenL1`. -/

namespace EigenL1

/-- Componentwise addition. -/
instance : Add EigenL1 := ⟨fun a b => ⟨a.toFun + b.toFun, memEig_add a.mem b.mem⟩⟩
/-- The zero element. -/
instance : Zero EigenL1 := ⟨⟨0, memEig_zero⟩⟩
/-- Componentwise negation. -/
instance : Neg EigenL1 := ⟨fun a => ⟨-a.toFun, memEig_neg a.mem⟩⟩
/-- Componentwise subtraction. -/
instance : Sub EigenL1 := ⟨fun a b => ⟨a.toFun - b.toFun, by
  have : a.toFun - b.toFun = a.toFun + -b.toFun := by ring
  rw [this]; exact memEig_add a.mem (memEig_neg b.mem)⟩⟩
/-- Scalar multiplication by `ℝ`. -/
instance : SMul ℝ EigenL1 := ⟨fun c a => ⟨c • a.toFun, memEig_smul c a.mem⟩⟩
/-- Scalar multiplication by `ℕ` (for the `AddCommGroup` `nsmul` field). -/
instance : SMul ℕ EigenL1 := ⟨fun k a => ⟨(k : ℝ) • a.toFun, memEig_smul (k : ℝ) a.mem⟩⟩
/-- Scalar multiplication by `ℤ` (for the `AddCommGroup` `zsmul` field). -/
instance : SMul ℤ EigenL1 := ⟨fun k a => ⟨(k : ℝ) • a.toFun, memEig_smul (k : ℝ) a.mem⟩⟩

@[simp] theorem add_toFun (a b : EigenL1) : (a + b).toFun = a.toFun + b.toFun := rfl
@[simp] theorem zero_toFun : (0 : EigenL1).toFun = 0 := rfl
@[simp] theorem neg_toFun (a : EigenL1) : (-a).toFun = -a.toFun := rfl
@[simp] theorem sub_toFun (a b : EigenL1) : (a - b).toFun = a.toFun - b.toFun := rfl
@[simp] theorem smul_toFun (c : ℝ) (a : EigenL1) : (c • a).toFun = c • a.toFun := rfl
@[simp] theorem nsmul_toFun (k : ℕ) (a : EigenL1) :
    (k • a).toFun = (k : ℝ) • a.toFun := rfl
@[simp] theorem zsmul_toFun (k : ℤ) (a : EigenL1) :
    (k • a).toFun = (k : ℝ) • a.toFun := rfl

instance : AddCommGroup EigenL1 where
  add_assoc a b c := by ext; simp [add_assoc]
  zero_add a := by ext; simp
  add_zero a := by ext; simp
  add_comm a b := by ext; simp [add_comm]
  neg_add_cancel a := by ext; simp
  sub_eq_add_neg a b := by ext; simp [sub_eq_add_neg]
  nsmul := (· • ·)
  nsmul_zero a := by ext n; simp
  nsmul_succ k a := by
    ext n; simp only [nsmul_toFun, add_toFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast; ring
  zsmul := (· • ·)
  zsmul_zero' a := by ext n; simp
  zsmul_succ' k a := by
    ext n
    simp only [zsmul_toFun, add_toFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast; ring
  zsmul_neg' k a := by
    ext n
    simp only [zsmul_toFun, neg_toFun, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    push_cast; ring

instance : Module ℝ EigenL1 where
  one_smul a := by ext; simp
  mul_smul x y a := by ext n; simp only [smul_toFun, Pi.smul_apply, smul_eq_mul]; ring
  smul_zero c := by ext; simp
  smul_add c a b := by
    ext n; simp only [smul_toFun, add_toFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  add_smul x y a := by
    ext n; simp only [smul_toFun, add_toFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  zero_smul a := by ext; simp

/-- The eigenvalue-ℓ¹ norm on the bundled type. -/
noncomputable instance : Norm EigenL1 := ⟨fun a => eigNorm a.toFun⟩

@[simp] theorem norm_def (a : EigenL1) : ‖a‖ = eigNorm a.toFun := rfl

end EigenL1

/-! ### The weighted isometry to `lp (fun _ : ℕ => ℝ) 1`.

The weight `λ_n = (nπ)²` vanishes at `n = 0`, so the map `a ↦ (n ↦ λ_n a_n)`
forgets `a_0`.  We therefore index the `lp` target by the **nonzero** naturals
`{n : ℕ // n ≠ 0}`, on which `λ_n > 0`, and bundle the `n = 0` coefficient
separately.  The metric space we transfer completeness from is then
`ℝ × lp (fun _ : {n : ℕ // n ≠ 0} => ℝ) 1`, with the product/`lp` norm matching
the eigenvalue-ℓ¹ norm because `λ_0 = 0` kills the `a_0` contribution to `‖a‖`
and we add `|a_0|` (weight-1) to recover separation of points.
-/

namespace EigenL1

/-- The strictly-positive eigenvalue on the nonzero naturals. -/
theorem eigenvalue_pos_subtype (n : {m : ℕ // m ≠ 0}) :
    0 < unitIntervalCosineEigenvalue (n : ℕ) :=
  unitIntervalCosineEigenvalue_pos n.2

/-- The eigenvalue is nonzero on the nonzero naturals (cast form). -/
theorem eigenvalue_ne_zero_subtype (n : {m : ℕ // m ≠ 0}) :
    unitIntervalCosineEigenvalue (n : ℕ) ≠ 0 :=
  ne_of_gt (eigenvalue_pos_subtype n)

/-- `p = 1` has `(1 : ℝ≥0∞).toReal = 1 > 0`. -/
theorem one_toReal_pos : (0 : ℝ) < ((1 : ℝ≥0∞).toReal) := by simp

/-- Pointwise cast-norm identity on the nonzero naturals:
`‖λ_n · x‖ = λ_n · ‖x‖`. -/
theorem norm_eig_mul (n : {m : ℕ // m ≠ 0}) (x : ℝ) :
    ‖unitIntervalCosineEigenvalue (n : ℕ) * x‖
      = unitIntervalCosineEigenvalue (n : ℕ) * ‖x‖ := by
  rw [norm_mul, Real.norm_of_nonneg (unitIntervalCosineEigenvalue_nonneg _)]

/-- The membership predicate restricted to nonzero indices is equivalent to
`Memℓp` of the weighted sequence on `{n // n ≠ 0}` at `p = 1`.  This is the
ℕ-indexed / real / `λ_n`-weight analogue of `memℓp_one_weighted_iff`. -/
theorem memℓp_one_weighted_iff (a : ℕ → ℝ) :
    Memℓp (fun n : {m : ℕ // m ≠ 0} =>
        unitIntervalCosineEigenvalue (n : ℕ) * a (n : ℕ)) (1 : ℝ≥0∞)
      ↔ Summable (fun n : {m : ℕ // m ≠ 0} =>
          unitIntervalCosineEigenvalue (n : ℕ) * |a (n : ℕ)|) := by
  rw [memℓp_gen_iff one_toReal_pos]
  have htr : ((1 : ℝ≥0∞).toReal) = 1 := by simp
  refine summable_congr (fun n => ?_)
  rw [htr, Real.rpow_one, norm_eig_mul, Real.norm_eq_abs]

end EigenL1

/-! ### Completeness of the eigenvalue-ℓ¹ space.

`MemEig a` (summability over all of `ℕ`) restricts to summability over the
nonzero indices via `Summable.subtype`; conversely the `n = 0` term is bundled
separately.  The complete metric structure transfers from
`lp (fun _ : {n : ℕ // n ≠ 0} => ℝ) 1` (`lp.completeSpace`, `1 ≤ 1`).

We expose the completeness through the carrier `ℝ × lp (...) 1` so that the
`n = 0` coefficient is retained, making the bijection genuine.
-/

namespace EigenL1

/-- Restriction of eigenvalue-ℓ¹ summability to the nonzero indices. -/
theorem summable_subtype_of_memEig {a : ℕ → ℝ} (ha : MemEig a) :
    Summable (fun n : {m : ℕ // m ≠ 0} =>
      unitIntervalCosineEigenvalue (n : ℕ) * |a (n : ℕ)|) :=
  ha.subtype _

/-- The weighted member of `lp (... {n ≠ 0} ...) 1` attached to an `EigenL1`. -/
noncomputable def toLpFun (a : EigenL1) :
    lp (fun _ : {m : ℕ // m ≠ 0} => ℝ) 1 :=
  ⟨fun n => unitIntervalCosineEigenvalue (n : ℕ) * a.toFun (n : ℕ),
    (memℓp_one_weighted_iff a.toFun).mpr (summable_subtype_of_memEig a.mem)⟩

@[simp] theorem toLpFun_coe (a : EigenL1) (n : {m : ℕ // m ≠ 0}) :
    (toLpFun a : {m : ℕ // m ≠ 0} → ℝ) n
      = unitIntervalCosineEigenvalue (n : ℕ) * a.toFun (n : ℕ) := rfl

/-- The carrier of the completeness transfer: the `n = 0` coefficient paired with
the weighted nonzero tail in `lp (... {n ≠ 0} ...) 1`. -/
abbrev Carrier := ℝ × lp (fun _ : {m : ℕ // m ≠ 0} => ℝ) 1

/-- Forward map `EigenL1 → Carrier`: keep `a_0`, weight the nonzero tail. -/
noncomputable def toCarrier (a : EigenL1) : Carrier := (a.toFun 0, toLpFun a)

/-- The unweighted sequence built from a carrier: `a_0` at `0`, and the divided
tail elsewhere. -/
noncomputable def carrierFun (p : Carrier) : ℕ → ℝ :=
  fun n => if h : n = 0 then p.1
    else (p.2 : {m : ℕ // m ≠ 0} → ℝ) ⟨n, h⟩
      / unitIntervalCosineEigenvalue n

/-- The `lp`-tail of a carrier, summed over `{m // m ≠ 0}`, is eigenvalue-ℓ¹
summable: it is exactly the absolute series of the `lp (... 1)` member. -/
theorem summable_tail_carrier (p : Carrier) :
    Summable (fun n : {m : ℕ // m ≠ 0} =>
      unitIntervalCosineEigenvalue (n : ℕ) * |carrierFun p (n : ℕ)|) := by
  have hmem := (p.2).2
  rw [memℓp_gen_iff one_toReal_pos] at hmem
  have htr : ((1 : ℝ≥0∞).toReal) = 1 := by simp
  refine (summable_congr (fun n => ?_)).mpr hmem
  have hne : ((n : ℕ) : ℕ) ≠ 0 := n.2
  rw [carrierFun]
  simp only [dif_neg hne]
  have hcast : (⟨(n : ℕ), hne⟩ : {m : ℕ // m ≠ 0}) = n := Subtype.ext rfl
  rw [hcast, htr, Real.rpow_one, Real.norm_eq_abs, abs_mul,
    abs_div, abs_of_nonneg (unitIntervalCosineEigenvalue_nonneg _)]
  rw [mul_div_assoc', mul_comm, mul_div_assoc,
    div_self (eigenvalue_ne_zero_subtype n), mul_one]

/-- The divided tail is eigenvalue-ℓ¹ summable, so `carrierFun p` is in `MemEig`. -/
theorem memEig_carrierFun (p : Carrier) : MemEig (carrierFun p) := by
  rw [MemEig, ← Finset.summable_compl_iff (s := {0})]
  -- The complement-subtype `{n ∉ {0}}` matches `{m // m ≠ 0}` via this equiv.
  let e : {n : ℕ // n ∉ ({0} : Finset ℕ)} ≃ {m : ℕ // m ≠ 0} :=
    Equiv.subtypeEquivRight (fun n => by simp)
  rw [← e.summable_iff]
  exact (summable_tail_carrier p).congr (fun n => rfl)

end EigenL1

end ShenWork.PDE
