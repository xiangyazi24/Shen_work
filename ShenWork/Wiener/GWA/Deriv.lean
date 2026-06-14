import ShenWork.Wiener.GWA.Operators

/-!
# Brick E3d — the generic cross-space derivation `gDeriv`'s Leibniz rule + `exp`

This file builds, **generically over the complete `ℂ`-Banach-algebra coefficient
ring `K`**, the Leibniz rule and the exponential derivative for the Fourier
derivation `gDeriv : GWA K (r+1) →L[ℂ] GWA K r` (brick E3,
`ShenWork/Wiener/GWA/Operators.lean`), mirroring the committed concrete-`ℂ`
Wiener-algebra brick 4d (`ShenWork/Wiener/WeightedL1Deriv.lean`).

* **Generic `Algebra ℚ (GWA K r)`** (via `ℚ →+* ℂ →+* GWA K r`) so that
  `NormedSpace.exp` on `GWA K r` is the *genuine* exponential series, not the
  junk `1`.  `EWA T r := GWA (CT T) r` reuses this generic instance (E4's old
  `ewaAlgebraRat` is removed in favour of it — no diamond).
* **`gIncl (h : r ≤ s) : GWA K s →ₐ[ℂ] GWA K r`** — the inclusion as an algebra
  hom (the algebra-hom upgrade of E3's CLM `incl`).
* **`gD_one : gDeriv 1 = 0`** — `(iπn)·(gOne n) = 0`.
* **`gD_mul`** — the convolution Leibniz rule
  `gDeriv (a*b) = gDeriv a * gIncl _ b + gIncl _ a * gDeriv b`, proved at the
  coefficient level via the split `iπn = iπm + iπ(n−m)` (the genuine new
  content; `K`-multiplication is commutative so the recombination works).
* **`gD_exp`** — `gDeriv (exp u) = gDeriv u * gIncl _ (exp u)`, via
  `gDeriv.map_tsum` + the factorial shift + `tsum_mul_right` + `map_exp`.
* **`gD_exp_neg_t`** — the `(-t)•f` form consumed by B2.
-/

open scoped BigOperators

noncomputable section

namespace ShenWork.GWA

namespace GWA

variable {K : Type*} [NormedCommRing K] [NormedAlgebra ℂ K] [CompleteSpace K]

/-! ### The generic `ℚ`-algebra structure on `GWA K r` (for `NormedSpace.exp`). -/

/-- `GWA K r` is a `ℚ`-algebra (via `ℚ →+* ℂ →+* GWA K r`).  This is the generic
parent of E4's `EWA T r := GWA (CT T) r` `ℚ`-algebra instance. -/
noncomputable instance algebraRatInst {r : ℕ} : Algebra ℚ (GWA K r) :=
  RingHom.toAlgebra ((algebraMap ℂ (GWA K r)).comp (algebraMap ℚ ℂ))

/-- The `ℚ`-scalar action on `GWA K r` factors through `ℂ`. -/
instance isScalarTowerRat {r : ℕ} : IsScalarTower ℚ ℂ (GWA K r) :=
  IsScalarTower.of_algebraMap_eq (fun q => by
    show (algebraMap ℚ (GWA K r)) q = _
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply])

/-- `GWA K r` is a `ℚ`-normed algebra. -/
noncomputable instance normedAlgebraRatInst {r : ℕ} : NormedAlgebra ℚ (GWA K r) where
  norm_smul_le q a := by
    rw [← smul_one_smul ℂ q a, Rat.smul_one_eq_cast, norm_smul, Complex.norm_ratCast,
      ← Real.norm_eq_abs, Rat.norm_cast_real]

/-! ### Piece 1 — the inclusion as an algebra hom `gIncl : GWA K s →ₐ[ℂ] GWA K r`. -/

/-- Coefficient of `incl h a` at `n`: the underlying sequence is unchanged
(the multiplier is the constant `1`). -/
theorem incl_toFun {r s : ℕ} (h : r ≤ s) (a : GWA K s) :
    (incl h a).toFun = a.toFun := by
  funext n
  show (incl h a).toFun n = a.toFun n
  rw [incl, scalarMultiplier_toFun, one_smul]

/-- **`gIncl`** — the inclusion `GWA K s ↪ GWA K r` (for `r ≤ s`) as a `ℂ`-algebra
homomorphism: identical underlying sequence, `map_mul`/`map_one` from `gConv`/
`gOne` unchanged. -/
def gIncl {r s : ℕ} (h : r ≤ s) : GWA K s →ₐ[ℂ] GWA K r where
  toFun := incl h
  map_one' := by apply GWA.ext; rw [incl_toFun]; rfl
  map_mul' a b := by
    apply GWA.ext
    rw [incl_toFun, mul_toFun, mul_toFun, incl_toFun, incl_toFun]
  map_zero' := (incl h).map_zero
  map_add' a b := (incl h).map_add a b
  commutes' c := by
    apply GWA.ext
    rw [incl_toFun]
    rfl

@[simp] theorem gIncl_toFun {r s : ℕ} (h : r ≤ s) (a : GWA K s) :
    (gIncl h a).toFun = a.toFun := incl_toFun h a

@[simp] theorem gIncl_apply {r s : ℕ} (h : r ≤ s) (a : GWA K s) :
    gIncl h a = incl h a := rfl

/-! ### Piece 2 — the coefficient form of `gDeriv`. -/

/-- Coefficient of `gDeriv a` at `n`: `(iπn)·a_n`. -/
@[simp] theorem gDeriv_toFun {r : ℕ} (a : GWA K (r + 1)) (n : ℤ) :
    (gDeriv a).toFun n = (Complex.I * Real.pi * (n : ℂ)) • a.toFun n := by
  show (gDeriv a).toFun n = _
  rw [gDeriv, scalarMultiplier_toFun]

/-! ### Piece 3 — `gD_one`. -/

/-- **`gD_one`.** The derivative of the unit is `0`: `(iπn)·(gOne n) = 0`. -/
theorem gD_one {r : ℕ} : gDeriv (1 : GWA K (r + 1)) = 0 := by
  apply GWA.ext
  funext n
  rw [gDeriv_toFun, one_toFun, zero_toFun, Pi.zero_apply]
  by_cases h : n = 0
  · subst h; simp [gOne]
  · simp [gOne, h]

/-! ### Piece 4 — `gD_mul`, the convolution Leibniz rule (the genuine new content). -/

/-- **The coefficient-level Leibniz identity**, stated on the bundled derivative
and inclusion images so that all summability witnesses come from the `.mem`
fields of `GWA K r` elements.  Here `da, db : GWA K r` carry the
derivative-multiplied sequences `m ↦ (iπm)·a_m` and `m ↦ (iπm)·b_m`, and `ar`,
`br : GWA K r` carry the (unchanged) sequences `a`, `b`.  Proved via the split
`iπn = iπm + iπ(n−m)`; `K`-multiplication is commutative so it recombines. -/
theorem gDeriv_gConv {r : ℕ} (a b : GWA K (r + 1)) (n : ℤ) :
    (Complex.I * Real.pi * (n : ℂ)) • gConv a.toFun b.toFun n
      = gConv (gDeriv a).toFun (incl (Nat.le_succ r) b).toFun n
        + gConv (incl (Nat.le_succ r) a).toFun (gDeriv b).toFun n := by
  have har : GMemW r a.toFun := by
    rw [← incl_toFun (Nat.le_succ r) a]; exact (incl (Nat.le_succ r) a).mem
  have hbr : GMemW r b.toFun := by
    rw [← incl_toFun (Nat.le_succ r) b]; exact (incl (Nat.le_succ r) b).mem
  have hC : Summable (fun m => a.toFun m * b.toFun (n - m)) :=
    summable_gConv_term har hbr n
  have hL : Summable (fun m => (gDeriv a).toFun m * (incl (Nat.le_succ r) b).toFun (n - m)) :=
    summable_gConv_term (gDeriv a).mem (incl (Nat.le_succ r) b).mem n
  have hR : Summable (fun m => (incl (Nat.le_succ r) a).toFun m * (gDeriv b).toFun (n - m)) :=
    summable_gConv_term (incl (Nat.le_succ r) a).mem (gDeriv b).mem n
  rw [gConv, gConv, gConv]
  rw [← tsum_const_smul'' (Complex.I * Real.pi * (n : ℂ)), ← Summable.tsum_add hL hR]
  refine tsum_congr (fun m => ?_)
  rw [gDeriv_toFun, gDeriv_toFun, incl_toFun, incl_toFun]
  have hsplit : (Complex.I * Real.pi * (n : ℂ))
      = (Complex.I * Real.pi * (m : ℂ)) + (Complex.I * Real.pi * ((n - m : ℤ) : ℂ)) := by
    push_cast; ring
  rw [hsplit, add_smul, smul_mul_assoc, mul_smul_comm]

/-- **`gD_mul` (the convolution Leibniz rule).**
`gDeriv (a*b) = gDeriv a * gIncl _ b + gIncl _ a * gDeriv b` in `GWA K r`. -/
theorem gD_mul {r : ℕ} (a b : GWA K (r + 1)) :
    gDeriv (a * b)
      = gDeriv a * gIncl (Nat.le_succ r) b + gIncl (Nat.le_succ r) a * gDeriv b := by
  apply GWA.ext
  funext n
  rw [add_toFun, Pi.add_apply, mul_toFun, mul_toFun, gIncl_apply, gIncl_apply]
  rw [gDeriv_toFun, mul_toFun]
  exact gDeriv_gConv a b n

/-! ### Piece 5 — `gD_exp`, mirroring the committed WA `D_exp`. -/

/-- `gIncl` commutes with `exp` (`NormedSpace.map_exp` through the algebra hom). -/
theorem gIncl_exp {r s : ℕ} (h : r ≤ s) (u : GWA K s) :
    gIncl h (NormedSpace.exp u) = NormedSpace.exp (gIncl h u) := by
  simpa using NormedSpace.map_exp (gIncl h).toRingHom (incl h).continuous u

/-- **Power rule.** `gDeriv (u^(j+1)) = (j+1)•((gIncl _ u)^j * gDeriv u)`. -/
theorem gD_pow_succ (u : GWA K 1) :
    ∀ j : ℕ, gDeriv (u ^ (j + 1))
      = ((j + 1 : ℕ) : ℂ) • ((gIncl (by omega : (0:ℕ) ≤ 1) u) ^ j * gDeriv u) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      calc
        gDeriv (u ^ (j + 2))
            = gDeriv (u ^ (j + 1) * u) := by rw [pow_succ]
        _ = gDeriv (u ^ (j + 1)) * gIncl (Nat.le_succ 0) u
              + gIncl (Nat.le_succ 0) (u ^ (j + 1)) * gDeriv u := by
              rw [gD_mul]
        _ = (((j + 1 : ℕ) : ℂ) • ((gIncl (by omega : (0:ℕ) ≤ 1) u) ^ j * gDeriv u))
                * gIncl (Nat.le_succ 0) u
              + (gIncl (by omega : (0:ℕ) ≤ 1) u) ^ (j + 1) * gDeriv u := by
              rw [ih, map_pow]
        _ = ((j + 2 : ℕ) : ℂ) • ((gIncl (by omega : (0:ℕ) ≤ 1) u) ^ (j + 1) * gDeriv u) := by
              have hX : ((gIncl (by omega : (0:ℕ) ≤ 1) u) ^ j * gDeriv u)
                  * gIncl (Nat.le_succ 0) u
                  = (gIncl (by omega : (0:ℕ) ≤ 1) u) ^ (j + 1) * gDeriv u := by
                rw [pow_succ]; ring
              rw [smul_mul_assoc, hX]
              push_cast
              module

/-- The exponential series term in `GWA K 1`. -/
private abbrev gExpTerm (u : GWA K 1) (j : ℕ) : GWA K 1 := (j.factorial : ℂ)⁻¹ • u ^ j

/-- **Derivative of one exp term.**
`gDeriv (gExpTerm u (j+1)) = (j!)⁻¹•((gIncl _ u)^j * gDeriv u)`. -/
theorem gD_expTerm_succ (u : GWA K 1) (j : ℕ) :
    gDeriv (gExpTerm u (j + 1))
      = (j.factorial : ℂ)⁻¹ • ((gIncl (by omega : (0:ℕ) ≤ 1) u) ^ j * gDeriv u) := by
  show gDeriv ((((j + 1).factorial : ℂ)⁻¹) • u ^ (j + 1)) = _
  rw [map_smul, gD_pow_succ u j]
  have hfac : ((j + 1).factorial : ℂ)⁻¹ * (((j + 1 : ℕ)) : ℂ) = (j.factorial : ℂ)⁻¹ := by
    have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hsj : (((j + 1 : ℕ)) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    rw [Nat.factorial_succ]; push_cast; field_simp
  rw [smul_smul, hfac]

/-- **`gD_exp`.** `gDeriv (exp u) = gDeriv u * gIncl _ (exp u)`. -/
theorem gD_exp (u : GWA K 1) :
    gDeriv (NormedSpace.exp u)
      = gDeriv u * gIncl (by omega : (0:ℕ) ≤ 1) (NormedSpace.exp u) := by
  classical
  set term : ℕ → GWA K 1 := fun j => (j.factorial : ℂ)⁻¹ • u ^ j with hterm_def
  set term0 : ℕ → GWA K 0 :=
    fun j => (j.factorial : ℂ)⁻¹ • (gIncl (by omega : (0:ℕ) ≤ 1) u) ^ j with hterm0_def
  have hterm : Summable term := NormedSpace.expSeries_summable' (𝕂 := ℂ) (x := u)
  have hterm0 : Summable term0 :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) (x := gIncl (by omega : (0:ℕ) ≤ 1) u)
  have hExp : NormedSpace.exp u = ∑' j : ℕ, term j := by
    rw [hterm_def]; exact congrFun (NormedSpace.exp_eq_tsum ℂ) u
  have hExp0 : NormedSpace.exp (gIncl (by omega : (0:ℕ) ≤ 1) u) = ∑' j : ℕ, term0 j := by
    rw [hterm0_def]; exact congrFun (NormedSpace.exp_eq_tsum ℂ) _
  have hmap : gDeriv (∑' j : ℕ, term j) = ∑' j : ℕ, gDeriv (term j) := by
    simpa using gDeriv.map_tsum hterm
  have hDterm_summ : Summable fun j : ℕ => gDeriv (term j) := hterm.map gDeriv gDeriv.continuous
  calc
    gDeriv (NormedSpace.exp u)
        = ∑' j : ℕ, gDeriv (term j) := by rw [hExp, hmap]
    _ = ∑' j : ℕ, gDeriv (term (j + 1)) := by
          rw [hDterm_summ.tsum_eq_zero_add]
          have h0 : term 0 = 1 := by rw [hterm_def]; simp
          rw [h0, gD_one, zero_add]
    _ = ∑' j : ℕ, (j.factorial : ℂ)⁻¹ • ((gIncl (by omega : (0:ℕ) ≤ 1) u) ^ j * gDeriv u) := by
          refine tsum_congr (fun j => ?_)
          rw [hterm_def]; exact gD_expTerm_succ u j
    _ = ∑' j : ℕ, term0 j * gDeriv u := by
          refine tsum_congr (fun j => ?_)
          rw [hterm0_def, smul_mul_assoc]
    _ = (∑' j : ℕ, term0 j) * gDeriv u := hterm0.tsum_mul_right (gDeriv u)
    _ = NormedSpace.exp (gIncl (by omega : (0:ℕ) ≤ 1) u) * gDeriv u := by rw [← hExp0]
    _ = gDeriv u * gIncl (by omega : (0:ℕ) ≤ 1) (NormedSpace.exp u) := by
          rw [gIncl_exp]; ring

/-! ### Piece 6 — `gD_exp_neg_t`, the form consumed by B2. -/

/-- **`gD_exp_neg_t`.** With `u = (-t)•f`:
`gDeriv (exp ((-t)•f)) = (-t)•(gDeriv f * gIncl _ (exp ((-t)•f)))`. -/
theorem gD_exp_neg_t (t : ℂ) (f : GWA K 1) :
    gDeriv (NormedSpace.exp ((-t : ℂ) • f))
      = (-t : ℂ) • (gDeriv f * gIncl (by omega : (0:ℕ) ≤ 1) (NormedSpace.exp ((-t : ℂ) • f))) := by
  rw [gD_exp ((-t : ℂ) • f), gDeriv.map_smul, smul_mul_assoc]

/-! ### Sanity test (non-vacuity). -/

/-- Sanity test: `gD_exp` fires on the concrete coefficient ring `K = ℂ`. -/
example : gDeriv (NormedSpace.exp (0 : GWA ℂ 1))
    = gDeriv (0 : GWA ℂ 1) * gIncl (by omega : (0:ℕ) ≤ 1) (NormedSpace.exp 0) :=
  gD_exp 0

end GWA

end ShenWork.GWA
