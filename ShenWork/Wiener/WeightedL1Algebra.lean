import ShenWork.Wiener.WeightedL1RingLaws

/-!
# The bundled weighted Wiener algebra `WA r` as a `NormedCommRing`

Brick 4b.  This file packages the weighted ℓ¹ space `A^r` (the subtype of
sequences `a : ℤ → ℂ` with `MemW r a`) as a bundled type `WA r`, and equips it
with a `NormedCommRing` instance whose multiplication is convolution `wConv`,
unit is `wOne`, and norm is `wNorm r`.

The instances are genuine:

* `AddCommGroup (WA r)` — componentwise `+`, `-`, `0`, closed by `memW_add`,
  `memW_neg`, `memW_zero`.
* `Module ℂ (WA r)` — componentwise scalar multiplication, closed by `memW_smul`.
* `NormedAddCommGroup (WA r)` — via `NormedAddCommGroup.ofCore`, supplying a
  `NormedSpace.Core ℂ (WA r)` (`norm_nonneg`, `norm_smul`, `norm_triangle`,
  `norm_eq_zero_iff`) built from `wNorm_nonneg`, `wNorm_smul`, `wNorm_add_le`,
  `wNorm_eq_zero`.  The same core also yields `NormedSpace ℂ (WA r)`.
* `CommRing (WA r)` — `mul = wConv` (closed by `memW_conv`), `one = wOne`
  (`memW_wOne`), ring axioms from `wConv_comm`/`wConv_assoc`/`wConv_wOne_*`
  (the `MemW 0` versions, applied via `memW_mono`), distributivity from the new
  helper `wConv_add`.
* `NormedRing (WA r)` and `NormedCommRing (WA r)` — `norm_mul_le` from
  `wNorm_conv_le`, sharing the metric of the `NormedAddCommGroup`.

This is the gateway to `Mathlib`'s `NormedSpace.exp` on `WA r` (bricks 4c–4e).
-/

open scoped BigOperators

namespace ShenWork.Wiener

/-- The bundled weighted Wiener algebra `A^r`: sequences in `MemW r`. -/
structure WA (r : ℕ) where
  /-- The underlying sequence. -/
  toFun : ℤ → ℂ
  /-- Membership witness: the weighted ℓ¹ summability. -/
  mem : MemW r toFun

namespace WA

variable {r : ℕ}

@[ext]
theorem ext {a b : WA r} (h : a.toFun = b.toFun) : a = b := by
  cases a; cases b; cases h; rfl

/-! ### Step 1 — module-closure lemmas and the norm facts. -/

/-- The zero sequence is in `A^r`. -/
theorem memW_zero (r : ℕ) : MemW r (0 : ℤ → ℂ) := by
  have : (fun n => wWeight r n * ‖(0 : ℤ → ℂ) n‖) = fun _ => (0 : ℝ) := by
    funext n; simp
  rw [MemW, this]; exact summable_zero

/-- Sums stay in `A^r` (termwise triangle inequality + `Summable.add`). -/
theorem memW_add {r : ℕ} {a b : ℤ → ℂ} (ha : MemW r a) (hb : MemW r b) :
    MemW r (a + b) := by
  rw [MemW]
  refine Summable.of_nonneg_of_le (fun n => weightedNorm_nonneg r (a + b) n) ?_
    (ha.add hb)
  intro n
  have ht : ‖(a + b) n‖ ≤ ‖a n‖ + ‖b n‖ := by
    simpa [Pi.add_apply] using norm_add_le (a n) (b n)
  calc wWeight r n * ‖(a + b) n‖
      ≤ wWeight r n * (‖a n‖ + ‖b n‖) :=
        mul_le_mul_of_nonneg_left ht (wWeight_nonneg r n)
    _ = wWeight r n * ‖a n‖ + wWeight r n * ‖b n‖ := by ring

/-- Negation stays in `A^r`. -/
theorem memW_neg {r : ℕ} {a : ℤ → ℂ} (ha : MemW r a) : MemW r (-a) := by
  have : (fun n => wWeight r n * ‖(-a) n‖) = fun n => wWeight r n * ‖a n‖ := by
    funext n; simp [Pi.neg_apply]
  rw [MemW, this]; exact ha

/-- Scalar multiples stay in `A^r` (`Summable.mul_left`). -/
theorem memW_smul {r : ℕ} (c : ℂ) {a : ℤ → ℂ} (ha : MemW r a) : MemW r (c • a) := by
  have : (fun n => wWeight r n * ‖(c • a) n‖)
      = fun n => ‖c‖ * (wWeight r n * ‖a n‖) := by
    funext n; rw [Pi.smul_apply, norm_smul]; ring
  rw [MemW, this]; exact ha.mul_left ‖c‖

/-- The weighted norm of `0` is `0`. -/
theorem wNorm_zero (r : ℕ) : wNorm r (0 : ℤ → ℂ) = 0 := by
  have : (fun n => wWeight r n * ‖(0 : ℤ → ℂ) n‖) = fun _ => (0 : ℝ) := by
    funext n; simp
  rw [wNorm, this]; exact tsum_zero

/-- `wNorm r a = 0 ↔ a = 0` (a tsum of nonnegative terms vanishes iff each does). -/
theorem wNorm_eq_zero {r : ℕ} {a : ℤ → ℂ} (ha : MemW r a) : wNorm r a = 0 ↔ a = 0 := by
  have hw : ∀ n, (0 : ℝ) < wWeight r n := by
    intro n
    have h1 : (0 : ℝ) < 1 + |(n : ℝ)| :=
      lt_of_lt_of_le one_pos (le_add_of_nonneg_right (abs_nonneg _))
    simpa [wWeight] using pow_pos h1 r
  constructor
  · intro h
    funext n
    by_contra hne
    have hpos : (0 : ℝ) < wWeight r n * ‖a n‖ := by
      have : (0 : ℝ) < ‖a n‖ := by
        have := norm_nonneg (a n)
        rcases lt_or_eq_of_le this with hlt | heq
        · exact hlt
        · exact absurd (by simpa using heq.symm) (by simpa [Pi.zero_apply] using hne)
      exact mul_pos (hw n) this
    have hposT : (0 : ℝ) < wNorm r a := by
      rw [wNorm]; exact ha.tsum_pos (fun m => weightedNorm_nonneg r a m) n hpos
    exact absurd h (ne_of_gt hposT)
  · intro h; rw [h]; exact wNorm_zero r

/-- Triangle inequality for `wNorm` (termwise `norm_add_le`, then `tsum_add`). -/
theorem wNorm_add_le {r : ℕ} {a b : ℤ → ℂ} (ha : MemW r a) (hb : MemW r b) :
    wNorm r (a + b) ≤ wNorm r a + wNorm r b := by
  rw [wNorm, wNorm, wNorm, ← Summable.tsum_add ha hb]
  refine Summable.tsum_mono (memW_add ha hb) (ha.add hb) ?_
  intro n
  have ht : ‖(a + b) n‖ ≤ ‖a n‖ + ‖b n‖ := by
    simpa [Pi.add_apply] using norm_add_le (a n) (b n)
  calc wWeight r n * ‖(a + b) n‖
      ≤ wWeight r n * (‖a n‖ + ‖b n‖) :=
        mul_le_mul_of_nonneg_left ht (wWeight_nonneg r n)
    _ = wWeight r n * ‖a n‖ + wWeight r n * ‖b n‖ := by ring

/-- `wNorm` is absolutely homogeneous (`tsum_mul_left`). -/
theorem wNorm_smul {r : ℕ} (c : ℂ) {a : ℤ → ℂ} : wNorm r (c • a) = ‖c‖ * wNorm r a := by
  rw [wNorm, wNorm, ← tsum_mul_left]
  refine tsum_congr ?_
  intro n
  rw [Pi.smul_apply, norm_smul]; ring

/-! ### Step 2 — the algebraic and normed instances on `WA r`. -/

/-- Componentwise addition. -/
instance : Add (WA r) := ⟨fun a b => ⟨a.toFun + b.toFun, memW_add a.mem b.mem⟩⟩
/-- The zero element. -/
instance : Zero (WA r) := ⟨⟨0, memW_zero r⟩⟩
/-- Componentwise negation. -/
instance : Neg (WA r) := ⟨fun a => ⟨-a.toFun, memW_neg a.mem⟩⟩
/-- Componentwise subtraction. -/
instance : Sub (WA r) := ⟨fun a b => ⟨a.toFun - b.toFun, by
  have : a.toFun - b.toFun = a.toFun + -b.toFun := by ring
  rw [this]; exact memW_add a.mem (memW_neg b.mem)⟩⟩
/-- Scalar multiplication by `ℂ`. -/
instance : SMul ℂ (WA r) := ⟨fun c a => ⟨c • a.toFun, memW_smul c a.mem⟩⟩
/-- Scalar multiplication by `ℕ` (for the `AddCommGroup` `nsmul` field). -/
instance : SMul ℕ (WA r) := ⟨fun k a => ⟨(k : ℂ) • a.toFun, memW_smul (k : ℂ) a.mem⟩⟩
/-- Scalar multiplication by `ℤ` (for the `AddCommGroup` `zsmul` field). -/
instance : SMul ℤ (WA r) := ⟨fun k a => ⟨(k : ℂ) • a.toFun, memW_smul (k : ℂ) a.mem⟩⟩

@[simp] theorem add_toFun (a b : WA r) : (a + b).toFun = a.toFun + b.toFun := rfl
@[simp] theorem zero_toFun : (0 : WA r).toFun = 0 := rfl
@[simp] theorem neg_toFun (a : WA r) : (-a).toFun = -a.toFun := rfl
@[simp] theorem sub_toFun (a b : WA r) : (a - b).toFun = a.toFun - b.toFun := rfl
@[simp] theorem smul_toFun (c : ℂ) (a : WA r) : (c • a).toFun = c • a.toFun := rfl
@[simp] theorem nsmul_toFun (k : ℕ) (a : WA r) :
    (k • a).toFun = (k : ℂ) • a.toFun := rfl
@[simp] theorem zsmul_toFun (k : ℤ) (a : WA r) :
    (k • a).toFun = (k : ℂ) • a.toFun := rfl

instance : AddCommGroup (WA r) where
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

instance : Module ℂ (WA r) where
  one_smul a := by ext; simp
  mul_smul x y a := by ext n; simp only [smul_toFun, Pi.smul_apply, smul_eq_mul]; ring
  smul_zero c := by ext; simp
  smul_add c a b := by
    ext n; simp only [smul_toFun, add_toFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  add_smul x y a := by
    ext n; simp only [smul_toFun, add_toFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  zero_smul a := by ext; simp

/-- The Wiener norm on the bundled type. -/
noncomputable instance : Norm (WA r) := ⟨fun a => wNorm r a.toFun⟩

@[simp] theorem norm_def (a : WA r) : ‖a‖ = wNorm r a.toFun := rfl

/-- The `NormedSpace.Core` for `WA r`: nonnegativity, homogeneity, triangle, and
`‖·‖ = 0 ↔ · = 0`.  This packages the `NormedAddCommGroup` and `NormedSpace`. -/
noncomputable def normCore : NormedSpace.Core ℂ (WA r) where
  norm_nonneg a := wNorm_nonneg r a.toFun
  norm_smul c a := by
    show wNorm r ((c • a).toFun) = ‖c‖ * wNorm r a.toFun
    rw [smul_toFun, wNorm_smul]
  norm_triangle a b := by
    show wNorm r ((a + b).toFun) ≤ wNorm r a.toFun + wNorm r b.toFun
    rw [add_toFun]; exact wNorm_add_le a.mem b.mem
  norm_eq_zero_iff a := by
    show wNorm r a.toFun = 0 ↔ a = 0
    rw [wNorm_eq_zero a.mem]
    exact ⟨fun h => WA.ext (by simpa using h),
      fun h => by simpa using congrArg WA.toFun h⟩

/-- `WA r` is a normed additive commutative group (norm = `wNorm`). -/
noncomputable instance : NormedAddCommGroup (WA r) := NormedAddCommGroup.ofCore normCore

/-- `WA r` is a normed `ℂ`-vector space. -/
noncomputable instance : NormedSpace ℂ (WA r) := NormedSpace.ofCore normCore

/-! ### The `CommRing` structure (mul = convolution). -/

/-- `wConv` distributes over `+` on the right.  New helper (`Summable.tsum_add`). -/
theorem wConv_add {a b c : ℤ → ℂ} (ha : MemW r a) (hb : MemW r b) (hc : MemW r c) :
    wConv a (b + c) = wConv a b + wConv a c := by
  funext n
  show (∑' m, a m * (b + c) (n - m))
    = (∑' m, a m * b (n - m)) + ∑' m, a m * c (n - m)
  have hsb : Summable (fun m => a m * b (n - m)) := summable_conv_term ha hb n
  have hsc : Summable (fun m => a m * c (n - m)) := summable_conv_term ha hc n
  rw [← Summable.tsum_add hsb hsc]
  refine tsum_congr ?_
  intro m
  rw [Pi.add_apply]; ring

/-- Convolution multiplication on `WA r`. -/
noncomputable instance : Mul (WA r) :=
  ⟨fun a b => ⟨wConv a.toFun b.toFun, memW_conv a.mem b.mem⟩⟩
/-- The convolution unit `wOne`. -/
instance : One (WA r) := ⟨⟨wOne, memW_wOne r⟩⟩

@[simp] theorem mul_toFun (a b : WA r) : (a * b).toFun = wConv a.toFun b.toFun := rfl
@[simp] theorem one_toFun : (1 : WA r).toFun = wOne := rfl

/-- Cast a `MemW r` witness down to `MemW 0` (since `0 ≤ r`), to apply the
`MemW 0` ring laws. -/
theorem mem0 (a : WA r) : MemW 0 a.toFun := memW_mono (Nat.zero_le r) a.mem

noncomputable instance : CommRing (WA r) where
  mul_comm a b := WA.ext (by simp only [mul_toFun]; exact wConv_comm (mem0 a) (mem0 b))
  mul_assoc a b c :=
    WA.ext (by simp only [mul_toFun]; exact wConv_assoc (mem0 a) (mem0 b) (mem0 c))
  one_mul a := WA.ext (by simp only [mul_toFun, one_toFun]; exact wConv_wOne_left)
  mul_one a := WA.ext (by simp only [mul_toFun, one_toFun]; exact wConv_wOne_right)
  left_distrib a b c :=
    WA.ext (by simp only [mul_toFun, add_toFun]; exact wConv_add a.mem b.mem c.mem)
  right_distrib a b c := WA.ext (by
    simp only [mul_toFun, add_toFun]
    rw [wConv_comm (memW_add (mem0 a) (mem0 b)) (mem0 c),
      wConv_add (mem0 c) (mem0 a) (mem0 b),
      wConv_comm (mem0 c) (mem0 a), wConv_comm (mem0 c) (mem0 b)])
  zero_mul a := WA.ext (by
    simp only [mul_toFun, zero_toFun]
    funext n; simp [wConv])
  mul_zero a := WA.ext (by
    simp only [mul_toFun, zero_toFun]
    funext n; simp [wConv])

/-- The submultiplicative norm bound on `WA r`: `‖a * b‖ ≤ ‖a‖ * ‖b‖`. -/
theorem norm_mul_le_wa (a b : WA r) : ‖a * b‖ ≤ ‖a‖ * ‖b‖ := by
  show wNorm r (wConv a.toFun b.toFun) ≤ wNorm r a.toFun * wNorm r b.toFun
  exact wNorm_conv_le r a.mem b.mem

/-- `WA r` is a normed ring (convolution, submultiplicative `wNorm`). -/
noncomputable instance : NormedRing (WA r) where
  dist_eq a b := by rw [dist_eq_norm]; rw [show -a + b = b - a by ring, norm_sub_rev]
  norm_mul_le := norm_mul_le_wa

/-- `WA r` is a normed commutative ring — the gateway to `NormedSpace.exp`. -/
noncomputable instance : NormedCommRing (WA r) where
  mul_comm := mul_comm

/-- Sanity test lemma exercising the `NormedCommRing` `norm_mul_le` field. -/
theorem test_norm_mul_le (a b : WA r) : ‖a * b‖ ≤ ‖a‖ * ‖b‖ := norm_mul_le a b

/-!
### Step 3 — `CompleteSpace (WA r)` — STALLED (follow-on brick 4b-ii).

Steps 1+2 above deliver a genuine `NormedCommRing (WA r)`.  Completeness is
deferred.  The intended route and the precise stall point:

* **Target.** Build `Φ : WA r ≃ᵢ lp (fun _ : ℤ => ℂ) 1` (an `IsometryEquiv`),
  then `CompleteSpace (WA r)` follows from `lp.completeSpace` via
  `Isometry.completeSpace_iff` / `IsometryEquiv.completeSpace_iff`
  (`Mathlib/Topology/MetricSpace/Isometry.lean:592`).  Note: only an
  *isometric equivalence* is needed for completeness transfer, NOT a
  `LinearIsometryEquiv` — so the linear-map bundling can be skipped here.

* **The map.** `Φ a := ⟨fun n => (wWeight r n : ℂ) • a.toFun n, hΦ⟩` where
  `hΦ : Memℓp (fun n => (wWeight r n : ℂ) • a.toFun n) 1`.  Inverse:
  `Φ.symm g := ⟨fun n => g n / (wWeight r n : ℂ), _⟩` (well-defined since
  `wWeight r n > 0`).

* **The two open translations (the stall).**
  1. `Memℓp (fun n => (wWeight r n:ℂ) • a.toFun n) 1 ↔ MemW r a.toFun`.
     With `p = 1`, `p.toReal = 1`, so by `memℓp_gen_iff` / `memℓp_one_iff`
     (`Mathlib/Analysis/Normed/Lp/lpSpace.lean:96`) `Memℓp f 1 ↔ Summable ‖f·‖`,
     and `‖(wWeight r n:ℂ) • a.toFun n‖ = wWeight r n * ‖a.toFun n‖` (via
     `norm_smul`, `Complex.norm_natCast`/`Complex.norm_real` on the nonneg
     real weight), which is exactly the `MemW r` summand.  Need: the
     `wWeight r n` cast `(↑(wWeight r n) : ℂ)` norm-simplification lemma and a
     clean `Summable.congr`.
  2. **Isometry / `dist`-preservation** — the actual reached goal:
     `Isometry Φ`, i.e. `edist (Φ a) (Φ b) = edist a b`, reduced (via
     `Isometry.of_dist_eq`) to `‖Φ a - Φ b‖ = ‖a - b‖`.  Unfolding the lp-1 norm
     with `lp.norm_eq_tsum_rpow (by norm_num : (0:ℝ) < (1:ℝ≥0∞).toReal)`
     (`lpSpace.lean:375`) gives
     `(∑' n, ‖(wWeight r n:ℂ) • (a.toFun n - b.toFun n)‖ ^ (1:ℝ)) ^ (1/1)`,
     which must be shown `= ∑' n, wWeight r n * ‖(a - b).toFun n‖ = ‖a - b‖`.
     The friction: discharging `lp.coeFn_sub`/`coeFn_smul` to push the
     subtraction through `Φ`, the `rpow 1` and `^(1/1)` cleanups, and matching
     `(1:ℝ≥0∞).toReal = 1` definitionally inside `norm_eq_tsum_rpow`.

  Mathlib lemma reached for: `lp.norm_eq_tsum_rpow` (the p=1 norm formula) and
  `IsometryEquiv.completeSpace_iff`.  No mathematical gap — purely the
  `Memℓp↔MemW` + lp-norm-`rpow`-bookkeeping plumbing — left for brick 4b-ii.
-/

end WA

end ShenWork.Wiener
