import ShenWork.Wiener.GWA.Operators
import ShenWork.Wiener.WeightedL1Eval

/-!
# The time-envelope algebra `EWA T r` and the slice bridge `sliceWA τ` (brick E4)

This file (Phase-A capstone) instantiates the generic weighted Wiener algebra
`GWA K r` (bricks E1–E3) at the **time-coefficient ring** `CT T := C(Icc 0 T, ℂ)`,
giving `EWA T r := GWA (CT T) r`, and builds the strategically-essential
algebra-homomorphism bridge `sliceWA τ : EWA T r →ₐ[ℂ] WA r` that evaluates the
time-coefficients at a fixed time `τ`, landing in the **committed** concrete
`ℂ`-Wiener algebra `WA r`.  Its key compatibility `sliceWA_exp` (slice commutes
with `NormedSpace.exp`) reduces the time-envelope exponential to the committed
`WA r` exponential pointwise-in-time, the central trick fed to Phase B/C.

* CT instances: `NormedCommRing (CT T)`, `NormedAlgebra ℂ (CT T)`,
  `CompleteSpace (CT T)` are real Mathlib `ContinuousMap` instances (compact
  domain `Icc 0 T`).
* `EWA T r := GWA (CT T) r` reuses all of E1–E3 generically.
* `sliceWA τ : EWA T r →ₐ[ℂ] WA r`, with `map_mul` via eval-at-τ commuting with
  the convolution `tsum` (the `ContinuousMap.evalCLM` CLM + `map_tsum`).
* `sliceWA_exp` via `NormedSpace.map_exp` through the slice ring hom.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener

set_option linter.dupNamespace false

namespace ShenWork.EWA

/-- The compact time domain `[0, T] ⊆ ℝ`. -/
abbrev TimeDom (T : ℝ) : Type := Set.Icc (0 : ℝ) T

/-- The time-coefficient ring: continuous `ℂ`-valued functions on `[0, T]`. -/
abbrev CT (T : ℝ) : Type := C(TimeDom T, ℂ)

section CTInstances

variable (T : ℝ)

/-- `CT T` is a normed commutative ring (Mathlib `ContinuousMap.instNormedCommRing`
on the compact space `Icc 0 T`). -/
noncomputable example : NormedCommRing (CT T) := inferInstance

/-- `CT T` is a normed `ℂ`-algebra (Mathlib `ContinuousMap.instNormedAlgebra`). -/
noncomputable example : NormedAlgebra ℂ (CT T) := inferInstance

/-- `CT T` is complete: `Icc 0 T` is compact, hence (weakly locally) compact,
hence compactly coherent, so `C(Icc 0 T, ℂ)` is complete. -/
example : CompleteSpace (CT T) := inferInstance

end CTInstances

/-- **The time-envelope weighted Wiener algebra** `EWA T r := GWA (CT T) r`,
reusing all of E1–E3 generically over the coefficient ring `CT T`. -/
abbrev EWA (T : ℝ) (r : ℕ) : Type := GWA (CT T) r

section EWATests

variable {T : ℝ} {r : ℕ}

/-- The generic convolution Banach-algebra structure fires on `EWA T r`. -/
noncomputable example : NormedCommRing (EWA T r) := inferInstance

/-- The generic `ℂ`-algebra structure fires on `EWA T r`. -/
noncomputable example : NormedAlgebra ℂ (EWA T r) := inferInstance

/-- The generic operators fire on `EWA T r`: e.g. the Fourier derivative. -/
noncomputable example : EWA T 2 →L[ℂ] EWA T 1 := GWA.gDeriv

end EWATests

/-! ### The slice bridge `sliceWA τ : EWA T r →ₐ[ℂ] WA r`. -/

section Slice

variable {T : ℝ} {r : ℕ}

/-- `gWeight = wWeight` definitionally (both are `(1+|n|)^r`). -/
theorem gWeight_eq_wWeight (n : ℤ) : GWA.gWeight r n = wWeight r n := rfl

/-- **Slice membership.** Evaluating each time-coefficient of `a : EWA T r` at a
fixed time `τ` lands in the committed `MemW r`, via the pointwise bound
`‖(a.toFun n) τ‖ ≤ ‖a.toFun n‖` (`ContinuousMap.norm_coe_le_norm`). -/
theorem memW_slice (a : EWA T r) (τ : TimeDom T) :
    MemW r (fun n => (a.toFun n) τ) := by
  have hwnn : ∀ n : ℤ, (0 : ℝ) ≤ wWeight r n := fun n => by
    rw [← gWeight_eq_wWeight]; exact GWA.gWeight_nonneg r n
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (hwnn n) (norm_nonneg _)) ?_ a.mem
  intro n
  have hle : ‖(a.toFun n) τ‖ ≤ ‖a.toFun n‖ := ContinuousMap.norm_coe_le_norm (a.toFun n) τ
  have hw : (0 : ℝ) ≤ GWA.gWeight r n := GWA.gWeight_nonneg r n
  calc wWeight r n * ‖(a.toFun n) τ‖
      = GWA.gWeight r n * ‖(a.toFun n) τ‖ := by rw [gWeight_eq_wWeight]
    _ ≤ GWA.gWeight r n * ‖a.toFun n‖ := mul_le_mul_of_nonneg_left hle hw

/-- The underlying map of the slice bridge: `a ↦ ⟨fun n => (a.toFun n) τ, _⟩`. -/
noncomputable def sliceFun (τ : TimeDom T) (a : EWA T r) : WA r :=
  ⟨fun n => (a.toFun n) τ, memW_slice a τ⟩

@[simp] theorem sliceFun_toFun (τ : TimeDom T) (a : EWA T r) (n : ℤ) :
    (sliceFun τ a).toFun n = (a.toFun n) τ := rfl

/-- **The crux: eval-at-τ commutes with the convolution `tsum`.**
`(gConv a.toFun b.toFun n) τ = ∑' m, (a.toFun m τ) * (b.toFun (n-m) τ)`.
Eval-at-τ is the continuous linear map `ContinuousMap.evalCLM ℂ τ`, so it
commutes with the (summable) convolution `tsum` via `ContinuousLinearMap.map_tsum`;
on each term it is the ring evaluation `(f*g) τ = f τ * g τ`. -/
theorem eval_gConv (τ : TimeDom T) (a b : EWA T r) (n : ℤ) :
    (GWA.gConv a.toFun b.toFun n) τ
      = ∑' m, (a.toFun m) τ * (b.toFun (n - m)) τ := by
  have hsum : Summable (fun m => a.toFun m * b.toFun (n - m)) :=
    GWA.summable_gConv_term a.mem b.mem n
  have hmap := (ContinuousMap.evalCLM (R := ℂ) (M := ℂ) τ).map_tsum hsum
  simp only [ContinuousMap.evalCLM_apply] at hmap
  rw [GWA.gConv]
  rw [hmap]
  exact tsum_congr (fun m => by rw [ContinuousMap.mul_apply])

/-- **`map_mul` for the slice bridge.** `slice (a*b) = (slice a)*(slice b)` in
`WA r`: eval-at-τ commutes with convolution (`eval_gConv`). -/
theorem sliceFun_mul (τ : TimeDom T) (a b : EWA T r) :
    sliceFun τ (a * b) = sliceFun τ a * sliceFun τ b := by
  apply WA.ext
  funext n
  rw [WA.mul_toFun]
  show (GWA.gConv a.toFun b.toFun n) τ = wConv (sliceFun τ a).toFun (sliceFun τ b).toFun n
  rw [eval_gConv, wConv]
  rfl

/-- `map_one`: `slice 1 = 1` (`gOne` vs `wOne`, both `if n=0 then 1 else 0`). -/
theorem sliceFun_one (τ : TimeDom T) : sliceFun τ (1 : EWA T r) = 1 := by
  apply WA.ext
  funext n
  show (GWA.gOne n : CT T) τ = wOne n
  rw [GWA.gOne, wOne]
  by_cases h : n = 0 <;> simp [h]

/-- `map_zero`. -/
theorem sliceFun_zero (τ : TimeDom T) : sliceFun τ (0 : EWA T r) = 0 := by
  apply WA.ext; funext n; rfl

/-- `map_add`. -/
theorem sliceFun_add (τ : TimeDom T) (a b : EWA T r) :
    sliceFun τ (a + b) = sliceFun τ a + sliceFun τ b := by
  apply WA.ext; funext n
  show (a.toFun n + b.toFun n) τ = (a.toFun n) τ + (b.toFun n) τ
  rw [ContinuousMap.add_apply]

/-- `commutes'`: slice commutes with `algebraMap ℂ`. -/
theorem sliceFun_algebraMap (τ : TimeDom T) (c : ℂ) :
    sliceFun τ (algebraMap ℂ (EWA T r) c) = algebraMap ℂ (WA r) c := by
  apply WA.ext; funext n
  show (c • GWA.gOne n : CT T) τ = (c • wOne) n
  rw [Pi.smul_apply, ContinuousMap.smul_apply, GWA.gOne, wOne, smul_eq_mul]
  by_cases h : n = 0 <;> simp [h]

/-- **The slice bridge** `sliceWA τ : EWA T r →ₐ[ℂ] WA r`: evaluate each
time-coefficient at `τ`, landing in the committed concrete `WA r`.  A genuine
`ℂ`-algebra homomorphism (`map_mul` is the real eval-commutes-with-`tsum`). -/
noncomputable def sliceWA (τ : TimeDom T) : EWA T r →ₐ[ℂ] WA r where
  toFun := sliceFun τ
  map_one' := sliceFun_one τ
  map_mul' := sliceFun_mul τ
  map_zero' := sliceFun_zero τ
  map_add' := sliceFun_add τ
  commutes' := sliceFun_algebraMap τ

@[simp] theorem sliceWA_apply (τ : TimeDom T) (a : EWA T r) :
    sliceWA τ a = sliceFun τ a := rfl

/-- `coeff_sliceWA : (sliceWA τ a).toFun n = (a.toFun n) τ` (definitional). -/
@[simp] theorem coeff_sliceWA (τ : TimeDom T) (a : EWA T r) (n : ℤ) :
    (sliceWA τ a).toFun n = (a.toFun n) τ := rfl

/-- **Continuity of the slice bridge**: `‖sliceWA τ a‖ ≤ ‖a‖` termwise, so the
underlying linear map is bounded with constant `1`. -/
theorem norm_sliceWA_le (τ : TimeDom T) (a : EWA T r) :
    ‖sliceWA τ a‖ ≤ ‖a‖ := by
  show wNorm r (sliceFun τ a).toFun ≤ GWA.gNorm r a.toFun
  rw [wNorm, GWA.gNorm]
  refine Summable.tsum_le_tsum (fun n => ?_) (memW_slice a τ) a.mem
  have hle : ‖(a.toFun n) τ‖ ≤ ‖a.toFun n‖ := ContinuousMap.norm_coe_le_norm (a.toFun n) τ
  have hw : (0 : ℝ) ≤ GWA.gWeight r n := GWA.gWeight_nonneg r n
  calc wWeight r n * ‖(sliceFun τ a).toFun n‖
      = GWA.gWeight r n * ‖(a.toFun n) τ‖ := by rw [gWeight_eq_wWeight]; rfl
    _ ≤ GWA.gWeight r n * ‖a.toFun n‖ := mul_le_mul_of_nonneg_left hle hw

/-- The slice algebra hom is continuous (Lipschitz constant `1`, all `n`). -/
theorem sliceWA_continuous (τ : TimeDom T) :
    Continuous (sliceWA τ (r := r)) := by
  refine AddMonoidHomClass.continuous_of_bound (sliceWA τ) 1 (fun a => ?_)
  simpa using norm_sliceWA_le τ a

/-! #### `ℚ`-algebra structures needed for `NormedSpace.map_exp`.

`NormedSpace.map_exp` requires `[NormedAlgebra ℚ 𝔸]` on the source and
`[Algebra ℚ 𝔹]` on the target.  We supply these generically (via `ℚ →+* ℂ →+*
·`) for `EWA T r` and `WA r`. -/

/-- `EWA T r` is a `ℚ`-algebra (via `ℚ →+* ℂ →+* EWA T r`). -/
noncomputable instance ewaAlgebraRat : Algebra ℚ (EWA T r) :=
  RingHom.toAlgebra ((algebraMap ℂ (EWA T r)).comp (algebraMap ℚ ℂ))

/-- The `ℚ`-action on `EWA T r` factors through `ℂ`. -/
instance : IsScalarTower ℚ ℂ (EWA T r) :=
  IsScalarTower.of_algebraMap_eq (fun q => by
    show (algebraMap ℚ (EWA T r)) q = _
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply])

/-- `EWA T r` is a `ℚ`-normed algebra. -/
noncomputable instance ewaNormedAlgebraRat : NormedAlgebra ℚ (EWA T r) where
  norm_smul_le q a := by
    rw [← smul_one_smul ℂ q a, Rat.smul_one_eq_cast, norm_smul, Complex.norm_ratCast,
      ← Real.norm_eq_abs, Rat.norm_cast_real]

/-- `WA r` is a `ℚ`-algebra (via `ℚ →+* ℂ →+* WA r`). -/
noncomputable instance waAlgebraRat : Algebra ℚ (WA r) :=
  RingHom.toAlgebra ((algebraMap ℂ (WA r)).comp (algebraMap ℚ ℂ))

/-- **The key compatibility (feeds E6).** `sliceWA τ` commutes with
`NormedSpace.exp`: exp on the time-envelope `EWA T r` reduces to the committed
`WA r` exp evaluated at each time `τ`.  Via `NormedSpace.map_exp` through the
continuous slice ring hom. -/
theorem sliceWA_exp (τ : TimeDom T) (a : EWA T r) :
    sliceWA τ (NormedSpace.exp a) = NormedSpace.exp (sliceWA τ a) :=
  NormedSpace.map_exp (sliceWA τ).toRingHom (sliceWA_continuous τ) a

end Slice

/-! ### Axiom-cleanliness witnesses. -/

section AxiomTests

/-- The generic `NormedCommRing` instance on `EWA T r` as a named term (axiom
test target: the generic algebra structure fires on the time-envelope). -/
noncomputable def ewaNormedCommRing (T : ℝ) (r : ℕ) : NormedCommRing (EWA T r) :=
  inferInstance

/-- The generic operators fire on `EWA T r` (named test target). -/
noncomputable def ewaGDerivTest (T : ℝ) : EWA T 2 →L[ℂ] EWA T 1 := GWA.gDeriv

end AxiomTests

end ShenWork.EWA

#print axioms ShenWork.EWA.sliceWA_exp
#print axioms ShenWork.EWA.ewaNormedCommRing
#print axioms ShenWork.EWA.ewaGDerivTest
