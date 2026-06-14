import ShenWork.Wiener.WeightedL1Complete
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Wiener brick 4c — the evaluation homomorphism `WA 0 → C(AddCircle 2, ℂ)`
and Fourier coefficient recovery.

We synthesise, from a weighted-ℓ¹ sequence `a : WA 0`, the continuous function
`evalC a (x) = ∑' n, a.toFun n • fourier n x` on `AddCircle 2`, show it is an
algebra homomorphism (multiplicativity via finite-support density), and recover
the coefficients `fourierCoeff (evalC a) n = a.toFun n`, yielding the decisive
estimate `‖a.toFun n‖ ≤ sup ‖evalC a‖`.
-/

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace ShenWork.Wiener

namespace WA

/-- The base circle `AddCircle 2`. -/
abbrev Circ := AddCircle (2 : ℝ)

instance : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩

/-! ### Piece 1 — the coefficient CLM `coeff0CLM n : WA 0 →L[ℂ] ℂ`. -/

/-- For `r = 0`, the weight is `1`, so the underlying sequence is absolutely
summable: `Summable (fun n => ‖a.toFun n‖)`. -/
theorem summable_norm_toFun (a : WA 0) : Summable (fun n => ‖a.toFun n‖) := by
  have h := a.mem
  rw [MemW] at h
  refine h.congr ?_
  intro n; simp [wWeight]

/-- `‖a‖ = ∑' n, ‖a.toFun n‖` at `r = 0`. -/
theorem norm_eq_tsum_norm (a : WA 0) : ‖a‖ = ∑' n, ‖a.toFun n‖ := by
  rw [norm_def, wNorm]
  refine tsum_congr ?_
  intro n; simp [wWeight]

/-- The `n`-th coefficient as a linear map. -/
def coeff0Lin (n : ℤ) : WA 0 →ₗ[ℂ] ℂ where
  toFun a := a.toFun n
  map_add' a b := by simp
  map_smul' c a := by simp

/-- The coefficient bound: `‖a.toFun n‖ ≤ ‖a‖`. -/
theorem norm_coeff_le (n : ℤ) (a : WA 0) : ‖a.toFun n‖ ≤ ‖a‖ := by
  rw [norm_eq_tsum_norm]
  exact (summable_norm_toFun a).le_tsum n (fun m _ => norm_nonneg _)

/-- The coefficient CLM. -/
def coeff0CLM (n : ℤ) : WA 0 →L[ℂ] ℂ :=
  (coeff0Lin n).mkContinuous 1 (fun a => by
    simpa [coeff0Lin] using norm_coeff_le n a)

@[simp] theorem coeff0CLM_apply (n : ℤ) (a : WA 0) : coeff0CLM n a = a.toFun n := rfl

/-! ### Piece 2 — the synthesis CLM `evalLin : WA 0 →L[ℂ] C(Circ, ℂ)`. -/

/-- The term family `n ↦ a.toFun n • fourier n` in `C(Circ, ℂ)`. -/
def evalTerm (a : WA 0) (n : ℤ) : C(Circ, ℂ) := a.toFun n • fourier n

/-- The norm of the `n`-th term equals `‖a.toFun n‖` (`fourier_norm = 1`). -/
theorem norm_evalTerm (a : WA 0) (n : ℤ) : ‖evalTerm a n‖ = ‖a.toFun n‖ := by
  rw [evalTerm, norm_smul, fourier_norm, mul_one]

/-- The term family is summable in `C(Circ, ℂ)` (absolute summability). -/
theorem summable_evalTerm (a : WA 0) : Summable (evalTerm a) := by
  refine Summable.of_norm ?_
  refine (summable_norm_toFun a).congr ?_
  intro n; rw [norm_evalTerm]

/-- The synthesised continuous function `evalFun a = ∑' n, a.toFun n • fourier n`. -/
def evalFun (a : WA 0) : C(Circ, ℂ) := ∑' n, evalTerm a n

/-- Additivity of `evalFun`. -/
theorem evalFun_add (a b : WA 0) : evalFun (a + b) = evalFun a + evalFun b := by
  rw [evalFun, evalFun, evalFun, ← (summable_evalTerm a).tsum_add (summable_evalTerm b)]
  refine tsum_congr ?_
  intro n
  rw [evalTerm, evalTerm, evalTerm, add_toFun, Pi.add_apply, add_smul]

/-- ℂ-scalar homogeneity of `evalFun`. -/
theorem evalFun_smul (c : ℂ) (a : WA 0) : evalFun (c • a) = c • evalFun a := by
  rw [evalFun, evalFun, ← (summable_evalTerm a).tsum_const_smul c]
  refine tsum_congr ?_
  intro n
  rw [evalTerm, evalTerm, smul_toFun, Pi.smul_apply, smul_assoc]

/-- The synthesis as a linear map. -/
def evalLinₗ : WA 0 →ₗ[ℂ] C(Circ, ℂ) where
  toFun := evalFun
  map_add' := evalFun_add
  map_smul' := evalFun_smul

/-- The synthesis norm bound `‖evalFun a‖ ≤ ‖a‖`. -/
theorem evalFun_norm_le (a : WA 0) : ‖evalFun a‖ ≤ ‖a‖ := by
  rw [evalFun]
  refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
  · refine (summable_norm_toFun a).congr ?_
    intro n; rw [norm_evalTerm]
  · rw [norm_eq_tsum_norm]
    refine le_of_eq (tsum_congr ?_)
    intro n; rw [norm_evalTerm]

/-- The synthesis CLM `evalLin : WA 0 →L[ℂ] C(Circ, ℂ)`. -/
def evalLin : WA 0 →L[ℂ] C(Circ, ℂ) :=
  evalLinₗ.mkContinuous 1 (fun a => by simpa [evalLinₗ] using evalFun_norm_le a)

@[simp] theorem evalLin_apply (a : WA 0) : evalLin a = evalFun a := rfl

/-- The synthesis bound, restated for the CLM. -/
theorem evalLin_norm_le (a : WA 0) : ‖evalLin a‖ ≤ ‖a‖ := by
  simpa using evalFun_norm_le a

/-! ### The `Algebra ℂ (WA r)` / `NormedAlgebra ℂ (WA r)` instances. -/

/-- Convolution pulls a left scalar out: `wConv (c • a) b = c • wConv a b`. -/
theorem wConv_smul_left (c : ℂ) (a b : ℤ → ℂ) :
    wConv (c • a) b = c • wConv a b := by
  funext n
  show (∑' m, (c • a) m * b (n - m)) = c • (∑' m, a m * b (n - m))
  rw [smul_eq_mul, ← tsum_mul_left]
  refine tsum_congr ?_
  intro m; rw [Pi.smul_apply, smul_eq_mul]; ring

/-- `WA r` is a `ℂ`-algebra (algebraMap `c ↦ c • 1`). -/
noncomputable instance algebraInst {r : ℕ} : Algebra ℂ (WA r) :=
  Algebra.ofModule
    (fun c a b => by
      apply WA.ext
      simp only [smul_toFun, mul_toFun, smul_toFun]
      exact wConv_smul_left c a.toFun b.toFun)
    (fun c a b => by
      apply WA.ext
      simp only [smul_toFun, mul_toFun, smul_toFun]
      rw [wConv_comm (mem0 a) (memW_smul c (mem0 b)), wConv_smul_left,
        wConv_comm (mem0 b) (mem0 a)])

@[simp] theorem algebraMap_toFun {r : ℕ} (c : ℂ) :
    (algebraMap ℂ (WA r) c).toFun = c • wOne := rfl

/-- `WA r` is a `ℂ`-normed algebra. -/
noncomputable instance normedAlgebraInst {r : ℕ} : NormedAlgebra ℂ (WA r) where
  norm_smul_le c a := by
    rw [norm_def, norm_def, smul_toFun, wNorm_smul]

/-! ### Piece 3 — finite-support density `ofFS`. -/

/-- The Kronecker delta sequence at `n`. -/
def deltaSeq (n : ℤ) : ℤ → ℂ := fun k => if k = n then 1 else 0

/-- Kronecker deltas are finitely supported, hence in `MemW 0`. -/
theorem memW_deltaSeq (n : ℤ) : MemW 0 (deltaSeq n) := by
  rw [MemW]
  apply summable_of_finite_support
  apply Set.Finite.subset (Set.finite_singleton n)
  intro k hk
  simp only [Function.mem_support, Set.mem_singleton_iff] at *
  by_contra hne
  apply hk; simp [deltaSeq, hne]

/-- The bundled Kronecker delta in `WA 0`. -/
def delta (n : ℤ) : WA 0 := ⟨deltaSeq n, memW_deltaSeq n⟩

@[simp] theorem delta_toFun (n : ℤ) : (delta n).toFun = deltaSeq n := rfl

/-- `delta 0 = 1` (the convolution unit `wOne`). -/
theorem delta_zero : delta 0 = (1 : WA 0) := by
  apply WA.ext; funext k; simp [delta, deltaSeq, wOne]

/-- Convolution of two Kronecker deltas: `delta m * delta n = delta (m + n)`. -/
theorem delta_mul (m n : ℤ) : delta m * delta n = delta (m + n) := by
  apply WA.ext; funext k
  rw [mul_toFun, delta_toFun, delta_toFun, delta_toFun]
  show (∑' j, deltaSeq m j * deltaSeq n (k - j)) = deltaSeq (m + n) k
  rw [tsum_eq_single m]
  · show (if m = m then (1:ℂ) else 0) * (if k - m = n then 1 else 0) = if k = m + n then 1 else 0
    rw [if_pos rfl, one_mul]
    by_cases h : k = m + n
    · rw [if_pos (show k - m = n by omega), if_pos h]
    · rw [if_neg (show ¬ k - m = n by omega), if_neg h]
  · intro j hj
    show (if j = m then (1:ℂ) else 0) * _ = 0
    rw [if_neg hj, zero_mul]

/-- The Kronecker delta as a monoid hom `Multiplicative ℤ →* WA 0`. -/
def deltaHom : Multiplicative ℤ →* WA 0 where
  toFun x := delta (Multiplicative.toAdd x)
  map_one' := delta_zero
  map_mul' x y := by
    show delta (Multiplicative.toAdd x + Multiplicative.toAdd y) = _
    rw [delta_mul]

/-- The finite-support inclusion `ofFS : AddMonoidAlgebra ℂ ℤ →ₐ[ℂ] WA 0`. -/
def ofFS : AddMonoidAlgebra ℂ ℤ →ₐ[ℂ] WA 0 :=
  AddMonoidAlgebra.lift ℂ (WA 0) ℤ deltaHom

/-- `ofFS (single m b) = b • delta m`. -/
theorem ofFS_single (m : ℤ) (b : ℂ) : ofFS (AddMonoidAlgebra.single m b) = b • delta m := by
  rw [ofFS, AddMonoidAlgebra.lift_single]; rfl

/-- Coefficient compatibility on a single: `coeff0CLM n (ofFS (single m b)) = (single m b) n`. -/
theorem coeff_ofFS_single (m n : ℤ) (b : ℂ) :
    coeff0CLM n (ofFS (AddMonoidAlgebra.single m b)) = (AddMonoidAlgebra.single m b) n := by
  rw [ofFS_single, map_smul, coeff0CLM_apply, delta_toFun, smul_eq_mul]
  show b * (if n = m then (1:ℂ) else 0) = (AddMonoidAlgebra.single m b) n
  rw [AddMonoidAlgebra.single_apply]
  by_cases h : n = m
  · rw [if_pos h, if_pos h.symm, mul_one]
  · rw [if_neg h, if_neg (fun hh => h hh.symm), mul_zero]

/-- The combined linear map `p ↦ coeff0CLM n (ofFS p)`. -/
def coeffOfFSLin (n : ℤ) : AddMonoidAlgebra ℂ ℤ →ₗ[ℂ] ℂ :=
  (coeff0CLM n).toLinearMap.comp ofFS.toLinearMap

@[simp] theorem coeffOfFSLin_apply (n : ℤ) (p : AddMonoidAlgebra ℂ ℤ) :
    coeffOfFSLin n p = coeff0CLM n (ofFS p) := rfl

/-- Coefficient compatibility: `coeff0CLM n (ofFS p) = p n`. -/
theorem coeff_ofFS (p : AddMonoidAlgebra ℂ ℤ) (n : ℤ) : coeff0CLM n (ofFS p) = p n := by
  rw [← coeffOfFSLin_apply]
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; rfl
  | add p q hp hq => rw [map_add, hp, hq]; exact (Finsupp.add_apply p q n).symm
  | single m b =>
      rw [coeffOfFSLin_apply, coeff_ofFS_single]

/-! ### Density of finitely-supported elements (`dense_ofFS`). -/

/-- `‖delta n‖ = 1` (the Kronecker delta has unit weighted-ℓ¹ norm at `r = 0`). -/
theorem norm_delta (n : ℤ) : ‖delta n‖ = 1 := by
  rw [norm_eq_tsum_norm]
  rw [tsum_eq_single n]
  · simp [delta, deltaSeq]
  · intro j hj; simp [delta, deltaSeq, hj]

/-- The δ-expansion `n ↦ a.toFun n • delta n` is summable in `WA 0`. -/
theorem summable_deltaExpansion (a : WA 0) :
    Summable (fun n => a.toFun n • delta n) := by
  refine Summable.of_norm ?_
  refine (summable_norm_toFun a).congr ?_
  intro n; rw [norm_smul, norm_delta, mul_one]

/-- The δ-expansion of `a` sums to `a`: the `k`-th coefficient of the sum is `a.toFun k`. -/
theorem deltaExpansion_hasSum (a : WA 0) :
    HasSum (fun n => a.toFun n • delta n) a := by
  obtain ⟨s, hs⟩ := summable_deltaExpansion a
  have hcoeff : ∀ k : ℤ, s.toFun k = a.toFun k := by
    intro k
    have hmap : HasSum (fun n => coeff0CLM k (a.toFun n • delta n)) (coeff0CLM k s) :=
      (coeff0CLM k).hasSum hs
    have hval : ∀ n, coeff0CLM k (a.toFun n • delta n) = if k = n then a.toFun n else 0 := by
      intro n
      rw [map_smul, coeff0CLM_apply, delta_toFun, deltaSeq, smul_eq_mul]
      by_cases h : k = n
      · rw [if_pos h, if_pos h, mul_one]
      · rw [if_neg h, if_neg h, mul_zero]
    have hmap2 : HasSum (fun n => if k = n then a.toFun n else 0) (coeff0CLM k s) := by
      refine hmap.congr_fun ?_
      intro n; rw [hval]
    have hsingle : HasSum (fun n => if k = n then a.toFun n else 0) (a.toFun k) := by
      have h0 : (fun n => if k = n then a.toFun n else 0)
          = (fun n => if n = k then a.toFun k else 0) := by
        funext n; by_cases h : k = n
        · rw [if_pos h, if_pos h.symm, h]
        · rw [if_neg h, if_neg (fun hh => h hh.symm)]
      rw [h0]; simpa using hasSum_ite_eq k (a.toFun k)
    have := hmap2.unique hsingle
    simpa [coeff0CLM_apply] using this
  have hsa : s = a := WA.ext (funext hcoeff)
  rw [hsa] at hs; exact hs

/-- **Finite-support density.** The range of `ofFS` is dense in `WA 0`. -/
theorem dense_ofFS : DenseRange ofFS := by
  intro a
  refine mem_closure_of_tendsto (deltaExpansion_hasSum a) ?_
  refine Filter.Eventually.of_forall (fun s => ?_)
  refine ⟨∑ n ∈ s, AddMonoidAlgebra.single n (a.toFun n), ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro n _; rw [ofFS_single]

/-! ### Piece 4 — multiplicativity of `evalLin` and the algebra hom `evalC`. -/

/-- `fourier (m + n) = fourier m * fourier n` as continuous maps. -/
theorem fourier_mul (m n : ℤ) :
    (fourier (m + n) : C(Circ, ℂ)) = fourier m * fourier n := by
  ext x; rw [ContinuousMap.mul_apply]; exact fourier_add

/-- The exponential characters as a monoid hom `Multiplicative ℤ →* C(Circ, ℂ)`. -/
def fourierHom : Multiplicative ℤ →* C(Circ, ℂ) where
  toFun x := fourier (Multiplicative.toAdd x)
  map_one' := by show (fourier 0 : C(Circ, ℂ)) = 1; ext x; simp
  map_mul' x y := by
    show (fourier (Multiplicative.toAdd x + Multiplicative.toAdd y) : C(Circ, ℂ)) = _
    rw [fourier_mul]

/-- The finite-support evaluation as an algebra hom `AddMonoidAlgebra ℂ ℤ →ₐ[ℂ] C(Circ, ℂ)`. -/
def evalFS : AddMonoidAlgebra ℂ ℤ →ₐ[ℂ] C(Circ, ℂ) :=
  AddMonoidAlgebra.lift ℂ (C(Circ, ℂ)) ℤ fourierHom

/-- `evalFS (single m b) = b • fourier m`. -/
theorem evalFS_single (m : ℤ) (b : ℂ) :
    evalFS (AddMonoidAlgebra.single m b) = b • fourier m := by
  rw [evalFS, AddMonoidAlgebra.lift_single]; rfl

/-- `evalLin` on the delta basis: `evalLin (delta n) = fourier n`. -/
theorem evalLin_delta (n : ℤ) : evalLin (delta n) = fourier n := by
  rw [evalLin_apply, evalFun]
  rw [tsum_eq_single n]
  · rw [evalTerm, delta_toFun, deltaSeq, if_pos rfl, one_smul]
  · intro j hj
    rw [evalTerm, delta_toFun, deltaSeq, if_neg hj, zero_smul]

/-- `evalLin ∘ ofFS = evalFS` on singles (both linear, used for the dense identity). -/
theorem evalLin_ofFS_single (m : ℤ) (b : ℂ) :
    evalLin (ofFS (AddMonoidAlgebra.single m b)) = evalFS (AddMonoidAlgebra.single m b) := by
  rw [ofFS_single, evalFS_single, map_smul, evalLin_delta]

/-- The composite `evalLin ∘ ofFS` agrees with `evalFS` (linear extension). -/
theorem evalLin_ofFS (p : AddMonoidAlgebra ℂ ℤ) : evalLin (ofFS p) = evalFS p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | single m b => rw [evalLin_ofFS_single]

/-- Multiplicativity of `evalLin`. -/
theorem evalLin_mul (a b : WA 0) : evalLin (a * b) = evalLin a * evalLin b := by
  refine DenseRange.induction_on₂ dense_ofFS ?_ ?_ a b
  · have h₁ : Continuous fun q : WA 0 × WA 0 => evalLin (q.1 * q.2) :=
      evalLin.continuous.comp (continuous_fst.mul continuous_snd)
    have h₂ : Continuous fun q : WA 0 × WA 0 => evalLin q.1 * evalLin q.2 :=
      (evalLin.continuous.comp continuous_fst).mul (evalLin.continuous.comp continuous_snd)
    exact isClosed_eq h₁ h₂
  · intro p q
    rw [← map_mul ofFS, evalLin_ofFS, evalLin_ofFS, evalLin_ofFS, map_mul]

/-- `evalLin` preserves `1`. -/
theorem evalLin_one : evalLin (1 : WA 0) = 1 := by
  rw [← delta_zero, evalLin_delta]
  ext x; simp

/-- `evalLin` commutes with the algebra map. -/
theorem evalLin_commutes (c : ℂ) :
    evalLin (algebraMap ℂ (WA 0) c) = algebraMap ℂ (C(Circ, ℂ)) c := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, evalLin_one]

/-- The synthesis algebra hom `evalC : WA 0 →A[ℂ] C(Circ, ℂ)`. -/
def evalC : WA 0 →A[ℂ] C(Circ, ℂ) where
  toFun := evalLin
  map_zero' := evalLin.map_zero
  map_add' := evalLin.map_add
  map_one' := evalLin_one
  map_mul' := evalLin_mul
  commutes' := evalLin_commutes
  cont := evalLin.continuous

@[simp] theorem evalC_apply (a : WA 0) : evalC a = evalLin a := rfl

/-! ### The `ℚ`-algebra structure on `WA 0` (needed for `NormedSpace.exp`). -/

/-- `WA 0` is a `ℚ`-algebra (via `ℚ →+* ℂ →+* WA 0`). -/
noncomputable instance algebraRatInst : Algebra ℚ (WA 0) :=
  RingHom.toAlgebra ((algebraMap ℂ (WA 0)).comp (algebraMap ℚ ℂ))

/-- The `ℚ`-scalar action on `WA 0` factors through `ℂ`. -/
instance : IsScalarTower ℚ ℂ (WA 0) :=
  IsScalarTower.of_algebraMap_eq (fun q => by
    show (algebraMap ℚ (WA 0)) q = _
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply])

/-- `WA 0` is a `ℚ`-normed algebra. -/
noncomputable instance normedAlgebraRatInst : NormedAlgebra ℚ (WA 0) where
  norm_smul_le q a := by
    rw [← smul_one_smul ℂ q a, Rat.smul_one_eq_cast, norm_smul, Complex.norm_ratCast,
      ← Real.norm_eq_abs, Rat.norm_cast_real]

/-! ### Piece 5 — point evaluation `evalAt` and `evalAt_exp` (`map_exp`). -/

/-- Point evaluation `evalAt x : WA 0 →ₐ[ℂ] ℂ` (eval-at-`x` ∘ `evalC`). -/
def evalAtAlg (x : Circ) : WA 0 →ₐ[ℂ] ℂ :=
  (ContinuousMap.evalAlgHom ℂ ℂ x).comp evalC.toAlgHom

/-- Point evaluation as a ring hom. -/
def evalAt (x : Circ) : WA 0 →+* ℂ := (evalAtAlg x).toRingHom

@[simp] theorem evalAt_apply (x : Circ) (a : WA 0) : evalAt x a = evalLin a x := rfl

/-- Point evaluation is continuous. -/
theorem continuous_evalAt (x : Circ) : Continuous (evalAt x : WA 0 → ℂ) := by
  have h_eval : Continuous fun f : C(Circ, ℂ) => f x :=
    (ContinuousMap.evalCLM ℂ x : C(Circ, ℂ) →L[ℂ] ℂ).continuous
  exact h_eval.comp evalC.continuous

/-- **`evalAt_exp`.** Point evaluation commutes with the exponential:
`evalAt x (exp a) = Complex.exp (evalAt x a)`. -/
theorem evalAt_exp (x : Circ) (a : WA 0) :
    evalAt x (NormedSpace.exp a) = Complex.exp (evalAt x a) := by
  have h := NormedSpace.map_exp (evalAt x) (continuous_evalAt x) a
  rw [Complex.exp_eq_exp_ℂ]; exact h

/-! ### Piece 6 — Fourier coefficient recovery and the decisive estimate. -/

/-- Every `g : C(Circ, ℂ)` is integrable w.r.t. `haarAddCircle` (continuous on a finite measure). -/
theorem integrable_coe (g : C(Circ, ℂ)) :
    Integrable (fun x : Circ => g x) AddCircle.haarAddCircle := by
  refine Integrable.of_bound g.continuous.aestronglyMeasurable ‖g‖ ?_
  filter_upwards with x; exact g.norm_coe_le_norm x

/-- **Coefficient norm bound.** `‖fourierCoeff (g) n‖ ≤ ‖g‖` (normalized Haar measure). -/
theorem fourierCoeff_norm_le (g : C(Circ, ℂ)) (n : ℤ) :
    ‖fourierCoeff (T := (2 : ℝ)) (fun x : Circ => g x) n‖ ≤ ‖g‖ := by
  rw [fourierCoeff]
  have hbound : ∀ᵐ x ∂(AddCircle.haarAddCircle (T := (2:ℝ))),
      ‖fourier (-n) x • g x‖ ≤ ‖g‖ := by
    filter_upwards with x
    rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
    exact g.norm_coe_le_norm x
  have h := norm_integral_le_of_norm_le_const (μ := AddCircle.haarAddCircle) hbound
  rwa [probReal_univ, mul_one] at h

/-- The Fourier coefficient as a linear functional on `C(Circ, ℂ)`. -/
def fourierCoeffLin (n : ℤ) : C(Circ, ℂ) →ₗ[ℂ] ℂ where
  toFun g := fourierCoeff (T := (2 : ℝ)) (fun x : Circ => g x) n
  map_add' f g := by
    have h := fourierCoeff.add (integrable_coe f) (integrable_coe g)
    exact congrFun h n
  map_smul' c f := by
    show fourierCoeff (T := (2:ℝ)) (fun x => (c • f) x) n = c • _
    have : (fun x : Circ => (c • f) x) = c • (fun x : Circ => f x) := by
      funext x; rw [ContinuousMap.smul_apply]; rfl
    rw [this, fourierCoeff.const_smul]

/-- The Fourier coefficient as a continuous linear functional. -/
def fourierCoeffCLM (n : ℤ) : C(Circ, ℂ) →L[ℂ] ℂ :=
  (fourierCoeffLin n).mkContinuous 1 (fun g => by
    simpa [fourierCoeffLin] using fourierCoeff_norm_le g n)

@[simp] theorem fourierCoeffCLM_apply (n : ℤ) (g : C(Circ, ℂ)) :
    fourierCoeffCLM n g = fourierCoeff (T := (2 : ℝ)) (fun x : Circ => g x) n := rfl

/-- Coefficient recovery on finite support:
`fourierCoeff (evalC (ofFS p)) n = coeff0CLM n (ofFS p)`. -/
theorem fourierCoeff_evalC_ofFS (p : AddMonoidAlgebra ℂ ℤ) (n : ℤ) :
    fourierCoeff (T := (2 : ℝ)) (fun x : Circ => evalC (ofFS p) x) n = coeff0CLM n (ofFS p) := by
  rw [evalC_apply, evalLin_ofFS, coeff_ofFS]
  induction p using AddMonoidAlgebra.induction_linear with
  | zero =>
      simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
      show fourierCoeff (T := (2:ℝ)) (fun _ : Circ => (0 : C(Circ, ℂ)) _) n = 0
      simp [fourierCoeff]
  | add p q hp hq =>
      rw [map_add]
      have hadd : (fun x : Circ => (evalFS p + evalFS q) x)
          = (fun x : Circ => evalFS p x) + (fun x : Circ => evalFS q x) := by
        funext x; rw [ContinuousMap.add_apply]; rfl
      rw [hadd, fourierCoeff.add (integrable_coe _) (integrable_coe _), Pi.add_apply,
        hp, hq]
      exact (Finsupp.add_apply p q n).symm
  | single m b =>
      rw [evalFS_single, AddMonoidAlgebra.single_apply]
      have hsmul : (fun x : Circ => (b • fourier m) x) = b • (fun x : Circ => fourier m x) := by
        funext x; rw [ContinuousMap.smul_apply]; rfl
      rw [hsmul, fourierCoeff.const_smul, fourierCoeff_fourier, Pi.single_apply, smul_eq_mul]
      by_cases h : n = m
      · rw [if_pos h, if_pos h.symm, mul_one]
      · rw [if_neg h, if_neg (fun hh => h hh.symm), mul_zero]

/-- **Coefficient recovery.** `fourierCoeff (evalC a) n = a.toFun n` for all `a : WA 0`. -/
theorem fourierCoeff_evalC_eq_coeff (a : WA 0) (n : ℤ) :
    fourierCoeff (T := (2 : ℝ)) (fun x : Circ => evalC a x) n = a.toFun n := by
  have hF : Continuous fun a : WA 0 =>
      fourierCoeff (T := (2 : ℝ)) (fun x : Circ => evalC a x) n :=
    (fourierCoeffCLM n).continuous.comp evalC.continuous
  have hG : Continuous fun a : WA 0 => coeff0CLM n a := (coeff0CLM n).continuous
  have hEq : (fun a : WA 0 => fourierCoeff (T := (2 : ℝ)) (fun x : Circ => evalC a x) n)
      = (fun a : WA 0 => coeff0CLM n a) :=
    DenseRange.equalizer dense_ofFS hF hG (funext (fun p => fourierCoeff_evalC_ofFS p n))
  have := congrFun hEq a
  simpa using this

/-- **The decisive estimate.** If `‖evalC a x‖ ≤ B` for all `x`, then `‖a.toFun n‖ ≤ B`. -/
theorem norm_coeff_le_of_eval_bound (a : WA 0) (n : ℤ) (B : ℝ)
    (hB : ∀ x : Circ, ‖evalC a x‖ ≤ B) : ‖a.toFun n‖ ≤ B := by
  have hBnn : 0 ≤ B := le_trans (norm_nonneg _) (hB (Classical.arbitrary Circ))
  have hrec : a.toFun n = fourierCoeff (T := (2 : ℝ)) (fun x : Circ => evalC a x) n :=
    (fourierCoeff_evalC_eq_coeff a n).symm
  rw [hrec]
  refine le_trans (fourierCoeff_norm_le (evalC a) n) ?_
  exact (ContinuousMap.norm_le _ hBnn).2 hB

end WA

end ShenWork.Wiener
