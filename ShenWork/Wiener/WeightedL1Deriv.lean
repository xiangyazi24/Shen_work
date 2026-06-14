import ShenWork.Wiener.WeightedL1Eval

/-!
# Wiener brick 4d — the cross-space derivation `D : WA 1 →L[ℂ] WA 0`

This brick builds the Fourier derivative as a bundled continuous linear map
between the weighted Wiener algebras, together with its Leibniz rule and the
derivative of the exponential.

* **`incl10 : WA 1 →A[ℂ] WA 0`** — the inclusion `A¹ ↪ A⁰`, the identity on the
  underlying sequence (membership drops by `memW_mono`).  An algebra hom with
  operator norm `≤ 1`.
* **`D : WA 1 →L[ℂ] WA 0`** — `D a = ⟨wDeriv a.toFun, …⟩`, the derivative
  multiplier `(a_n) ↦ (iπn·a_n)`, continuous with `‖D a‖ ≤ π·‖a‖`.
* **`D_one : D 1 = 0`** — `(iπn)·(wOne n) = 0` for every `n`.
* **`D_mul`** — the convolution Leibniz rule
  `D (a*b) = D a * incl10 b + incl10 a * D b`, proved at the coefficient level
  via the split `iπn = iπm + iπ(n−m)`.  This is the genuine new content.
* **`D_exp`** — `D (exp u) = D u * incl10 (exp u)`, following ChatGPT's
  Step-4d skeleton (`D_pow_succ`, `D_expTerm_succ`, `D.map_tsum` + factorial
  shift + `tsum_mul_right`).
* **`D_exp_neg_t`** — the `(-t)•f` form consumed by the decisive estimate.
-/

open scoped BigOperators

noncomputable section

namespace ShenWork.Wiener

namespace WA

/-! ### The `ℚ`-algebra structure on `WA 1` (needed for `NormedSpace.exp`). -/

/-- `WA r` is a `ℚ`-algebra (via `ℚ →+* ℂ →+* WA r`). -/
noncomputable instance algebraRatInst' {r : ℕ} : Algebra ℚ (WA r) :=
  RingHom.toAlgebra ((algebraMap ℂ (WA r)).comp (algebraMap ℚ ℂ))

/-- The `ℚ`-scalar action on `WA r` factors through `ℂ`. -/
instance isScalarTowerRat' {r : ℕ} : IsScalarTower ℚ ℂ (WA r) :=
  IsScalarTower.of_algebraMap_eq (fun q => by
    show (algebraMap ℚ (WA r)) q = _
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply])

/-- `WA r` is a `ℚ`-normed algebra. -/
noncomputable instance normedAlgebraRatInst' {r : ℕ} : NormedAlgebra ℚ (WA r) where
  norm_smul_le q a := by
    rw [← smul_one_smul ℂ q a, Rat.smul_one_eq_cast, norm_smul, Complex.norm_ratCast,
      ← Real.norm_eq_abs, Rat.norm_cast_real]

/-! ### Piece 1 — the inclusion `incl10 : WA 1 →A[ℂ] WA 0`. -/

/-- The underlying-sequence inclusion `A¹ → A⁰` as a `ℂ`-linear map. -/
def incl10Lin : WA 1 →ₗ[ℂ] WA 0 where
  toFun a := ⟨a.toFun, memW_mono (Nat.le_succ 0) a.mem⟩
  map_add' a b := by apply WA.ext; rfl
  map_smul' c a := by apply WA.ext; rfl

@[simp] theorem incl10Lin_toFun (a : WA 1) : (incl10Lin a).toFun = a.toFun := rfl

/-- The inclusion `incl10 : WA 1 →A[ℂ] WA 0` (a continuous algebra hom). -/
def incl10 : WA 1 →A[ℂ] WA 0 where
  toFun := incl10Lin
  map_zero' := incl10Lin.map_zero
  map_add' := incl10Lin.map_add
  map_one' := by apply WA.ext; rfl
  map_mul' a b := by apply WA.ext; rfl
  commutes' c := by apply WA.ext; rfl
  cont := by
    refine AddMonoidHomClass.continuous_of_bound incl10Lin 1 ?_
    intro a
    rw [one_mul, norm_def, norm_def]
    exact wNorm_mono_le (Nat.le_succ 0) a.mem

@[simp] theorem incl10_apply (a : WA 1) : incl10 a = incl10Lin a := rfl

@[simp] theorem incl10_toFun (a : WA 1) : (incl10 a).toFun = a.toFun := rfl

/-! ### Piece 2 — the derivation CLM `D : WA 1 →L[ℂ] WA 0`. -/

/-- The derivative `(a_n) ↦ (iπn·a_n)` as a `ℂ`-linear map `WA 1 → WA 0`. -/
def DLin : WA 1 →ₗ[ℂ] WA 0 where
  toFun a := ⟨wDeriv a.toFun, memW_wDeriv a.mem⟩
  map_add' a b := by
    apply WA.ext
    funext n
    show wDeriv (a.toFun + b.toFun) n = wDeriv a.toFun n + wDeriv b.toFun n
    simp only [wDeriv, Pi.add_apply]; ring
  map_smul' c a := by
    apply WA.ext
    funext n
    show wDeriv (c • a.toFun) n = c • wDeriv a.toFun n
    simp only [wDeriv, Pi.smul_apply, smul_eq_mul]; ring

@[simp] theorem DLin_toFun (a : WA 1) : (DLin a).toFun = wDeriv a.toFun := rfl

/-- The derivation `D : WA 1 →L[ℂ] WA 0`, continuous with `‖D a‖ ≤ π·‖a‖`. -/
def D : WA 1 →L[ℂ] WA 0 :=
  DLin.mkContinuous Real.pi (fun a => by
    rw [norm_def, norm_def]
    exact wNorm_wDeriv_le a.mem)

theorem D_apply (a : WA 1) : D a = DLin a := rfl

theorem D_toFun (a : WA 1) : (D a).toFun = wDeriv a.toFun := rfl

/-! ### Piece 3 — `D 1 = 0`. -/

/-- **`D_one`.** The derivative of the unit is `0`: `(iπn)·(wOne n) = 0`. -/
theorem D_one : D (1 : WA 1) = 0 := by
  apply WA.ext
  funext n
  show wDeriv wOne n = (0 : WA 0).toFun n
  rw [zero_toFun]
  simp only [wDeriv, wOne, Pi.zero_apply]
  by_cases h : n = 0
  · subst h; simp
  · simp [h]

/-! ### Piece 4 — `D_mul`, the convolution Leibniz rule (the genuine new content). -/

/-- **The coefficient-level Leibniz identity** on raw sequences:
`wDeriv (wConv a b) = wConv (wDeriv a) b + wConv a (wDeriv b)` whenever
`a ∈ MemW 1`, `b ∈ MemW 0`.  Proved via the split `iπn = iπm + iπ(n−m)`. -/
theorem wDeriv_wConv {a b : ℤ → ℂ} (ha : MemW 1 a) (hb : MemW 1 b) :
    wDeriv (wConv a b) = wConv (wDeriv a) b + wConv a (wDeriv b) := by
  funext n
  have ha0 : MemW 0 a := memW_mono (Nat.zero_le 1) ha
  have hb0 : MemW 0 b := memW_mono (Nat.zero_le 1) hb
  have hL : Summable (fun m => wDeriv a m * b (n - m)) :=
    summable_conv_term (memW_wDeriv ha) hb0 n
  have hR : Summable (fun m => a m * wDeriv b (n - m)) :=
    summable_conv_term ha0 (memW_wDeriv hb) n
  have hC : Summable (fun m => a m * b (n - m)) := summable_conv_term ha0 hb0 n
  -- LHS as a single tsum: `iπn·(∑ₘ aₘb_{n−m}) = ∑ₘ iπn·(aₘb_{n−m})`.
  have hLHS : wDeriv (wConv a b) n
      = ∑' m, (Complex.I * Real.pi * (n : ℂ)) * (a m * b (n - m)) := by
    simp only [wDeriv, wConv]
    exact (hC.tsum_mul_left _).symm
  -- RHS as a single tsum, via termwise summability.
  have hRHS : (wConv (wDeriv a) b + wConv a (wDeriv b)) n
      = ∑' m, (wDeriv a m * b (n - m) + a m * wDeriv b (n - m)) := by
    simp only [Pi.add_apply, wConv]
    exact (Summable.tsum_add hL hR).symm
  rw [hLHS, hRHS]
  refine tsum_congr (fun m => ?_)
  simp only [wDeriv]
  -- (iπn)·(aₘ b_{n−m}) = (iπm·aₘ)b_{n−m} + aₘ(iπ(n−m)·b_{n−m}).
  have hsplit : (n : ℂ) = (m : ℂ) + ((n - m : ℤ) : ℂ) := by push_cast; ring
  rw [hsplit]; ring

/-- **`D_mul` (the convolution Leibniz rule).**
`D (a*b) = D a * incl10 b + incl10 a * D b` in `WA 0`. -/
theorem D_mul (a b : WA 1) :
    D (a * b) = D a * incl10 b + incl10 a * D b := by
  apply WA.ext
  simp only [D_toFun, mul_toFun, add_toFun, incl10_toFun, D_toFun]
  exact wDeriv_wConv a.mem b.mem

/-! ### Piece 5 — `D_exp`, following the ChatGPT Step-4d skeleton. -/

/-- `incl10` commutes with `exp` (`NormedSpace.map_exp`). -/
theorem incl_exp (u : WA 1) :
    incl10 (NormedSpace.exp u) = NormedSpace.exp (incl10 u) := by
  simpa using NormedSpace.map_exp incl10.toRingHom incl10.continuous u

/-- **Power rule.** `D (u^(j+1)) = (j+1)•((incl10 u)^j * D u)`. -/
theorem D_pow_succ (u : WA 1) :
    ∀ j : ℕ, D (u ^ (j + 1))
      = ((j + 1 : ℕ) : ℂ) • ((incl10 u) ^ j * D u) := by
  intro j
  induction j with
  | zero => simp [D_one]
  | succ j ih =>
      calc
        D (u ^ (j + 2))
            = D (u ^ (j + 1) * u) := by rw [pow_succ]
        _ = D (u ^ (j + 1)) * incl10 u + incl10 (u ^ (j + 1)) * D u := by
              rw [D_mul]
        _ = (((j + 1 : ℕ) : ℂ) • ((incl10 u) ^ j * D u)) * incl10 u
              + (incl10 u) ^ (j + 1) * D u := by
              rw [ih, map_pow]
        _ = ((j + 2 : ℕ) : ℂ) • ((incl10 u) ^ (j + 1) * D u) := by
              have hX : ((incl10 u) ^ j * D u) * incl10 u
                  = (incl10 u) ^ (j + 1) * D u := by
                rw [pow_succ]; ring
              rw [smul_mul_assoc, hX]
              push_cast
              module

/-- The exponential series term in `WA 1`. -/
private abbrev expTerm (u : WA 1) (j : ℕ) : WA 1 := (j.factorial : ℂ)⁻¹ • u ^ j

/-- **Derivative of one exp term.** `D (expTerm u (j+1)) = (j!)⁻¹•((incl10 u)^j * D u)`. -/
theorem D_expTerm_succ (u : WA 1) (j : ℕ) :
    D (expTerm u (j + 1)) = (j.factorial : ℂ)⁻¹ • ((incl10 u) ^ j * D u) := by
  show D ((((j + 1).factorial : ℂ)⁻¹) • u ^ (j + 1)) = _
  rw [map_smul, D_pow_succ u j]
  have hfac : ((j + 1).factorial : ℂ)⁻¹ * (((j + 1 : ℕ)) : ℂ) = (j.factorial : ℂ)⁻¹ := by
    have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hsj : (((j + 1 : ℕ)) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    rw [Nat.factorial_succ]; push_cast; field_simp
  rw [smul_smul, hfac]

/-- **`D_exp`.** `D (exp u) = D u * incl10 (exp u)`. -/
theorem D_exp (u : WA 1) :
    D (NormedSpace.exp u) = D u * incl10 (NormedSpace.exp u) := by
  classical
  set term : ℕ → WA 1 := fun j => (j.factorial : ℂ)⁻¹ • u ^ j with hterm_def
  set term0 : ℕ → WA 0 := fun j => (j.factorial : ℂ)⁻¹ • (incl10 u) ^ j with hterm0_def
  have hterm : Summable term := NormedSpace.expSeries_summable' (𝕂 := ℂ) (x := u)
  have hterm0 : Summable term0 :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) (x := incl10 u)
  have hExp : NormedSpace.exp u = ∑' j : ℕ, term j := by
    rw [hterm_def]; exact congrFun (NormedSpace.exp_eq_tsum ℂ) u
  have hExp0 : NormedSpace.exp (incl10 u) = ∑' j : ℕ, term0 j := by
    rw [hterm0_def]; exact congrFun (NormedSpace.exp_eq_tsum ℂ) (incl10 u)
  have hmap : D (∑' j : ℕ, term j) = ∑' j : ℕ, D (term j) := by
    simpa using D.map_tsum hterm
  have hDterm_summ : Summable fun j : ℕ => D (term j) := hterm.map D D.continuous
  calc
    D (NormedSpace.exp u)
        = ∑' j : ℕ, D (term j) := by rw [hExp, hmap]
    _ = ∑' j : ℕ, D (term (j + 1)) := by
          rw [hDterm_summ.tsum_eq_zero_add]
          have h0 : term 0 = 1 := by rw [hterm_def]; simp
          rw [h0, D_one, zero_add]
    _ = ∑' j : ℕ, (j.factorial : ℂ)⁻¹ • ((incl10 u) ^ j * D u) := by
          refine tsum_congr (fun j => ?_)
          rw [hterm_def]; exact D_expTerm_succ u j
    _ = ∑' j : ℕ, term0 j * D u := by
          refine tsum_congr (fun j => ?_)
          rw [hterm0_def, smul_mul_assoc]
    _ = (∑' j : ℕ, term0 j) * D u := hterm0.tsum_mul_right (D u)
    _ = NormedSpace.exp (incl10 u) * D u := by rw [← hExp0]
    _ = D u * incl10 (NormedSpace.exp u) := by rw [incl_exp u]; ring

/-! ### Piece 6 — `D_exp_neg_t`, the form consumed by the decisive estimate. -/

/-- **`D_exp_neg_t`.** With `u = (-t)•f`:
`D (exp ((-t)•f)) = (-t)•(D f * incl10 (exp ((-t)•f)))`. -/
theorem D_exp_neg_t (t : ℂ) (f : WA 1) :
    D (NormedSpace.exp ((-t : ℂ) • f))
      = (-t : ℂ) • (D f * incl10 (NormedSpace.exp ((-t : ℂ) • f))) := by
  rw [D_exp ((-t : ℂ) • f), D.map_smul, smul_mul_assoc]

end WA

end ShenWork.Wiener
