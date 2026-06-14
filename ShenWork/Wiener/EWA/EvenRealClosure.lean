import ShenWork.Wiener.EWA.ConvParity
import ShenWork.Wiener.EWA.ChemDivSourceAssembly

/-!
# EWA brick (parity closure) — `EvenRealEWA` / `OddImagEWA` propagation

The **parity closure** of the time-envelope weighted Wiener algebra: even/real
structure of the EWA coefficients propagates through the EWA operators
(`incl`, `gDeriv`, the convolution product `*`, scalar multipliers, `gResolver`),
so that the chemotaxis-divergence source `chemDivEWA U = gDeriv (chemFluxEWA U)`
is even+real.  This is exactly what is needed to discharge the coefficient
bridge's `heven`/`hreal` hypotheses for `chemDivEWA`.

Everything is stated **at the slice level**: `EvenRealEWA U` asserts that, for
every time `τ`, the sliced sequence `(sliceWA τ U).toFun : ℤ → ℂ` is even and
real.  Since each EWA operator acts coefficientwise and commutes with slicing,
the committed `ConvParity` atoms (`gConv_even_even`, `gDeriv_toFun_odd_of_even`,
…) — which live over the slice sequences — propagate the structure.

The genuinely-hard step is the **Wiener–Lévy parity**: `FnegEWA f s` (the
Gamma/Laplace integral `(1/Γs)•∫ t^{s−1}•e^{−tf} dt`) of an even-real `f` is
even-real.  At the slice/coefficient level this is `exp` of an even-real
sequence integrated over `t`; it does not reduce to the structural atoms here.
Per the brick contract we PROVE the entire structural propagation (operator /
product / `gDeriv` closures + the `chemFlux`/`chemDiv` targets) **modulo** a
single isolated hypothesis `FnegEWA_evenReal` (equivalently `realPowEWA_evenReal`
/ `qFactor_evenReal`), and name it precisely as the open Wiener–Lévy parity
lemma.

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ} {r : ℕ}

/-! ### Sequence-level reality predicates (companions of `IsEvenSeq`/`IsOddSeq`). -/

/-- A real ℤ-indexed `ℂ`-sequence: every coefficient has zero imaginary part. -/
def IsRealSeq (a : ℤ → ℂ) : Prop := ∀ n, (a n).im = 0

/-- A purely-imaginary ℤ-indexed `ℂ`-sequence: every coefficient has zero real part. -/
def IsImagSeq (a : ℤ → ℂ) : Prop := ∀ n, (a n).re = 0

/-! ### The two parity structures (slice-level even/real and odd/imaginary). -/

/-- `U : EWA T r` is **even-real**: at every time `τ` the sliced sequence is even
and real. -/
structure EvenRealEWA (U : EWA T r) : Prop where
  even : ∀ (τ : TimeDom T) (n : ℤ), (sliceWA τ U).toFun (-n) = (sliceWA τ U).toFun n
  real : ∀ (τ : TimeDom T) (n : ℤ), ((sliceWA τ U).toFun n).im = 0

/-- `U : EWA T r` is **odd-imaginary**: at every time `τ` the sliced sequence is
odd and purely imaginary. -/
structure OddImagEWA (U : EWA T r) : Prop where
  odd  : ∀ (τ : TimeDom T) (n : ℤ), (sliceWA τ U).toFun (-n) = -(sliceWA τ U).toFun n
  imag : ∀ (τ : TimeDom T) (n : ℤ), ((sliceWA τ U).toFun n).re = 0

/-- Repackage the slice-level data of `EvenRealEWA` as the `ConvParity` predicates. -/
theorem EvenRealEWA.isEvenSeq {U : EWA T r} (h : EvenRealEWA U) (τ : TimeDom T) :
    IsEvenSeq (sliceWA τ U).toFun := fun n => h.even τ n

theorem EvenRealEWA.isRealSeq {U : EWA T r} (h : EvenRealEWA U) (τ : TimeDom T) :
    IsRealSeq (sliceWA τ U).toFun := fun n => h.real τ n

theorem OddImagEWA.isOddSeq {U : EWA T r} (h : OddImagEWA U) (τ : TimeDom T) :
    IsOddSeq (sliceWA τ U).toFun := fun n => h.odd τ n

theorem OddImagEWA.isImagSeq {U : EWA T r} (h : OddImagEWA U) (τ : TimeDom T) :
    IsImagSeq (sliceWA τ U).toFun := fun n => h.imag τ n

/-! ### Slice-commutation of the EWA operators (the structural skeleton). -/

/-- Slicing commutes with the EWA inclusion: the underlying sequence is unchanged. -/
theorem coeff_sliceWA_incl {s : ℕ} (h : r ≤ s) (U : EWA T s) (τ : TimeDom T) (n : ℤ) :
    (sliceWA τ (GWA.incl h U)).toFun n = (sliceWA τ U).toFun n := by
  rw [coeff_sliceWA, coeff_sliceWA, GWA.incl_toFun]

/-- Slicing commutes with the Fourier derivative: `(slice (gDeriv U))_n = iπn·(slice U)_n`. -/
theorem coeff_sliceWA_gDeriv (U : EWA T (r + 1)) (τ : TimeDom T) (n : ℤ) :
    (sliceWA τ (GWA.gDeriv U)).toFun n
      = (Complex.I * Real.pi * (n : ℂ)) • (sliceWA τ U).toFun n := by
  rw [coeff_sliceWA, GWA.gDeriv_toFun, ContinuousMap.smul_apply, coeff_sliceWA]

/-- Slicing commutes with the convolution product (via the slice algebra-hom). -/
theorem coeff_sliceWA_mul (U V : EWA T r) (τ : TimeDom T) (n : ℤ) :
    (sliceWA τ (U * V)).toFun n
      = GWA.gConv (sliceWA τ U).toFun (sliceWA τ V).toFun n := by
  rw [map_mul, WA.mul_toFun]
  rfl

/-- Slicing commutes with `ℂ`-scalar multiplication. -/
theorem coeff_sliceWA_smul (c : ℂ) (U : EWA T r) (τ : TimeDom T) (n : ℤ) :
    (sliceWA τ (c • U)).toFun n = c • (sliceWA τ U).toFun n := by
  rw [coeff_sliceWA, GWA.smul_toFun, Pi.smul_apply, ContinuousMap.smul_apply, coeff_sliceWA]

/-! ### Closure 1 — `incl` preserves both parity structures (identity coefficients). -/

theorem EvenRealEWA.incl {s : ℕ} (h : r ≤ s) {U : EWA T s} (hU : EvenRealEWA U) :
    EvenRealEWA (GWA.incl h U) where
  even τ n := by rw [coeff_sliceWA_incl, coeff_sliceWA_incl]; exact hU.even τ n
  real τ n := by rw [coeff_sliceWA_incl]; exact hU.real τ n

theorem OddImagEWA.incl {s : ℕ} (h : r ≤ s) {U : EWA T s} (hU : OddImagEWA U) :
    OddImagEWA (GWA.incl h U) where
  odd τ n := by rw [coeff_sliceWA_incl, coeff_sliceWA_incl]; exact hU.odd τ n
  imag τ n := by rw [coeff_sliceWA_incl]; exact hU.imag τ n

/-! ### Closure 2 — `gDeriv` flips parity (`iπn` symbol is odd + imaginary). -/

/-- `gDeriv : EvenReal → OddImag`.  Even ↦ odd by `gDeriv_symbol_odd_of_even`;
real ↦ imaginary because `(iπn·z).re = -π·n·z.im = 0` when `z.im = 0`. -/
theorem EvenRealEWA.gDeriv {U : EWA T (r + 1)} (hU : EvenRealEWA U) :
    OddImagEWA (GWA.gDeriv U) where
  odd τ := by
    have hsym : (fun n => (sliceWA τ (GWA.gDeriv U)).toFun n)
        = fun n : ℤ => Complex.I * Real.pi * (n : ℂ) * (sliceWA τ U).toFun n := by
      funext n; rw [coeff_sliceWA_gDeriv, smul_eq_mul]
    have := gDeriv_symbol_odd_of_even (hU.isEvenSeq τ)
    intro n
    have h1 := congrFun hsym (-n)
    have h2 := congrFun hsym n
    rw [h1, h2]; exact this n
  imag τ n := by
    rw [coeff_sliceWA_gDeriv, smul_eq_mul, Complex.mul_re]
    have : (Complex.I * Real.pi * (n : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [this, hU.real τ n]; ring

/-- `gDeriv : OddImag → EvenReal`.  Odd ↦ even by `gDeriv_symbol_even_of_odd`;
imaginary ↦ real because `(iπn·z).im = π·n·z.re = 0` when `z.re = 0`. -/
theorem OddImagEWA.gDeriv {U : EWA T (r + 1)} (hU : OddImagEWA U) :
    EvenRealEWA (GWA.gDeriv U) where
  even τ := by
    have hsym : (fun n => (sliceWA τ (GWA.gDeriv U)).toFun n)
        = fun n : ℤ => Complex.I * Real.pi * (n : ℂ) * (sliceWA τ U).toFun n := by
      funext n; rw [coeff_sliceWA_gDeriv, smul_eq_mul]
    have := gDeriv_symbol_even_of_odd (hU.isOddSeq τ)
    intro n
    have h1 := congrFun hsym (-n)
    have h2 := congrFun hsym n
    rw [h1, h2]; exact this n
  real τ n := by
    rw [coeff_sliceWA_gDeriv, smul_eq_mul, Complex.mul_im]
    have hre : (Complex.I * Real.pi * (n : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    have him : (Complex.I * Real.pi * (n : ℂ)).im = Real.pi * (n : ℝ) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, him, hU.imag τ n]; ring

/-! ### Closure 3 — product (`*`) closures (the parity multiplication table). -/

/-- If every term of a ℂ-valued family is real (`im = 0`), the `tsum`'s `im` is `0`.
The family equals `ofReal ∘ re`, so the sum is `ofReal` of a real sum. -/
theorem im_tsum_eq_zero_of_terms_real {f : ℤ → ℂ} (hf : ∀ m, (f m).im = 0) :
    (∑' m : ℤ, f m).im = 0 := by
  have hrw : (fun m => f m) = fun m => (((f m).re : ℝ) : ℂ) := by
    funext m
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im, hf m]
  rw [show (∑' m : ℤ, f m) = ∑' m : ℤ, (((f m).re : ℝ) : ℂ) from by rw [hrw],
    ← Complex.ofReal_tsum, Complex.ofReal_im]

/-- If every term of a ℂ-valued family is purely imaginary (`re = 0`), the `tsum`'s
`re` is `0`.  Apply the real version to `-I • f` (whose terms are real). -/
theorem re_tsum_eq_zero_of_terms_imag {f : ℤ → ℂ} (hf : ∀ m, (f m).re = 0) :
    (∑' m : ℤ, f m).re = 0 := by
  have hI : (∑' m : ℤ, (-Complex.I * f m)).im = 0 :=
    im_tsum_eq_zero_of_terms_real (fun m => by
      rw [Complex.mul_im, hf m]; simp)
  rw [tsum_mul_left, Complex.mul_im] at hI
  simpa using hI

/-- The convolution of a real and a real sequence is real (`(z·w).im = 0`). -/
theorem isRealSeq_gConv {a b : ℤ → ℂ} (ha : IsRealSeq a) (hb : IsRealSeq b) :
    IsRealSeq (GWA.gConv a b) := fun n =>
  im_tsum_eq_zero_of_terms_real (fun m => by rw [Complex.mul_im, ha m, hb (n - m)]; ring)

/-- The convolution of two purely-imaginary sequences is real
(`(z·w).im = z.re·w.im + z.im·w.re = 0` when both `.re = 0`). -/
theorem isRealSeq_gConv_imag {a b : ℤ → ℂ} (ha : IsImagSeq a) (hb : IsImagSeq b) :
    IsRealSeq (GWA.gConv a b) := fun n =>
  im_tsum_eq_zero_of_terms_real (fun m => by rw [Complex.mul_im, ha m, hb (n - m)]; ring)

/-- The convolution of a real and a purely-imaginary sequence is purely imaginary
(`(z·w).re = z.re·w.re − z.im·w.im = 0` when `z.im = 0` and `w.re = 0`). -/
theorem isImagSeq_gConv_real_imag {a b : ℤ → ℂ} (ha : IsRealSeq a) (hb : IsImagSeq b) :
    IsImagSeq (GWA.gConv a b) := fun n =>
  re_tsum_eq_zero_of_terms_imag (fun m => by rw [Complex.mul_re, ha m, hb (n - m)]; ring)

/-- **EvenReal · EvenReal = EvenReal.** -/
theorem EvenRealEWA.mul {U V : EWA T r} (hU : EvenRealEWA U) (hV : EvenRealEWA V) :
    EvenRealEWA (U * V) where
  even τ n := by
    rw [coeff_sliceWA_mul, coeff_sliceWA_mul]
    exact gConv_even_even (hU.isEvenSeq τ) (hV.isEvenSeq τ) n
  real τ n := by
    rw [coeff_sliceWA_mul]
    exact isRealSeq_gConv (hU.isRealSeq τ) (hV.isRealSeq τ) n

/-- **EvenReal · OddImag = OddImag.** -/
theorem EvenRealEWA.mul_oddImag {U V : EWA T r} (hU : EvenRealEWA U) (hV : OddImagEWA V) :
    OddImagEWA (U * V) where
  odd τ n := by
    rw [coeff_sliceWA_mul, coeff_sliceWA_mul]
    exact gConv_even_odd (hU.isEvenSeq τ) (hV.isOddSeq τ) n
  imag τ n := by
    rw [coeff_sliceWA_mul]
    exact isImagSeq_gConv_real_imag (hU.isRealSeq τ) (hV.isImagSeq τ) n

/-- **OddImag · EvenReal = OddImag.** -/
theorem OddImagEWA.mul_evenReal {U V : EWA T r} (hU : OddImagEWA U) (hV : EvenRealEWA V) :
    OddImagEWA (U * V) where
  odd τ n := by
    rw [coeff_sliceWA_mul, coeff_sliceWA_mul]
    exact gConv_odd_even (hU.isOddSeq τ) (hV.isEvenSeq τ) n
  imag τ n := by
    rw [coeff_sliceWA_mul]
    -- `re (z·w) = z.re·w.re − z.im·w.im = 0` when `z.re = 0` and `w.im = 0`.
    exact re_tsum_eq_zero_of_terms_imag
      (fun m => by rw [Complex.mul_re, hU.imag τ m, hV.real τ (n - m)]; ring)

/-- **OddImag · OddImag = EvenReal.** -/
theorem OddImagEWA.mul {U V : EWA T r} (hU : OddImagEWA U) (hV : OddImagEWA V) :
    EvenRealEWA (U * V) where
  even τ n := by
    rw [coeff_sliceWA_mul, coeff_sliceWA_mul]
    exact gConv_odd_odd (hU.isOddSeq τ) (hV.isOddSeq τ) n
  real τ n := by
    rw [coeff_sliceWA_mul]
    exact isRealSeq_gConv_imag (hU.isImagSeq τ) (hV.isImagSeq τ) n

/-! ### Closure 4 — `ℂ`-scalar multiplication by a real scalar preserves EvenReal. -/

/-- Scaling by a **real** scalar `(c:ℝ)` preserves the even-real structure. -/
theorem EvenRealEWA.smul_real (c : ℝ) {U : EWA T r} (hU : EvenRealEWA U) :
    EvenRealEWA ((c : ℂ) • U) where
  even τ n := by
    rw [coeff_sliceWA_smul, coeff_sliceWA_smul, smul_eq_mul, smul_eq_mul, hU.even τ n]
  real τ n := by
    rw [coeff_sliceWA_smul, smul_eq_mul, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, hU.real τ n]; ring

/-- Scaling by a real scalar preserves the odd-imaginary structure. -/
theorem OddImagEWA.smul_real (c : ℝ) {U : EWA T r} (hU : OddImagEWA U) :
    OddImagEWA ((c : ℂ) • U) where
  odd τ n := by
    rw [coeff_sliceWA_smul, coeff_sliceWA_smul, smul_eq_mul, smul_eq_mul, hU.odd τ n,
      mul_neg]
  imag τ n := by
    rw [coeff_sliceWA_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_im,
      Complex.ofReal_re, hU.imag τ n]; ring

/-! ### Closure 5 — `gOne`, `1`, and addition. -/

/-- The unit `gOne` slices to the Kronecker delta, which is even and real. -/
theorem EvenRealEWA.one : EvenRealEWA (1 : EWA T r) where
  even τ n := by
    rw [coeff_sliceWA, coeff_sliceWA]
    change (GWA.gOne (-n) : CT T) τ = (GWA.gOne n : CT T) τ
    by_cases h : n = 0
    · subst h; simp
    · have hn : (-n) ≠ 0 := by omega
      rw [GWA.gOne, GWA.gOne]; simp [h, hn]
  real τ n := by
    rw [coeff_sliceWA]
    change ((GWA.gOne n : CT T) τ).im = 0
    by_cases h : n = 0
    · subst h; rw [GWA.gOne]; simp
    · rw [GWA.gOne]; simp [h]

/-- Slicing commutes with addition. -/
theorem coeff_sliceWA_add (U V : EWA T r) (τ : TimeDom T) (n : ℤ) :
    (sliceWA τ (U + V)).toFun n
      = (sliceWA τ U).toFun n + (sliceWA τ V).toFun n := by
  rw [coeff_sliceWA, GWA.add_toFun, Pi.add_apply, ContinuousMap.add_apply,
    coeff_sliceWA, coeff_sliceWA]

/-- Sums of even-real elements are even-real. -/
theorem EvenRealEWA.add {U V : EWA T r} (hU : EvenRealEWA U) (hV : EvenRealEWA V) :
    EvenRealEWA (U + V) where
  even τ n := by
    rw [coeff_sliceWA_add, coeff_sliceWA_add, hU.even τ n, hV.even τ n]
  real τ n := by
    rw [coeff_sliceWA_add, Complex.add_im, hU.real τ n, hV.real τ n]; ring

/-! ### THE WIENER–LÉVY PARITY (the isolated hard step).

`FnegEWA f s = (1/Γs)•∫_{Ioi 0} t^{s−1}•e^{−tf} dt`.  For even-real `f` the
exponential `e^{−tf}` is even-real (its slice is `exp` of an even-real sequence;
`exp = Σ powers`, and `EvenReal` is closed under powers and real-scalar smul by
the product closure above), and the `(1/Γs)•∫dt` of an even-real `EWA`-valued
integrand stays even-real per coefficient.  This is the only step NOT reducible to
the structural atoms in this file (it needs the Bochner-integral / `exp`-series
even-real interchange).  It is isolated as the hypothesis below. -/

/-- **The open Wiener–Lévy parity (HYPOTHESIS).**  `FnegEWA f s` of an even-real
`f` is even-real.  This is the single Wiener–Lévy step left open; it requires the
`exp`-series + Bochner-integral even-real interchange, not the structural atoms of
this file.  Everything downstream is proved modulo this. -/
def FnegEWA_evenReal_Hyp : Prop :=
  ∀ {T : ℝ} (f : EWA T 1) (s : ℝ), EvenRealEWA f → EvenRealEWA (FnegEWA f s)

/-! ### Closure 6 — `realPowEWA` and `qFactor`, modulo the WL parity hypothesis. -/

/-- **`realPowEWA` preserves EvenReal**, modulo the WL-parity hypothesis.
`realPowEWA u γ = u^(⌊γ⌋+1)·FnegEWA u (⌊γ⌋+1−γ)`: the power is EvenReal by the
product closure (`EvenRealEWA.mul` + `EvenRealEWA.one`), and `FnegEWA` is EvenReal
by `hWL`. -/
theorem realPowEWA_evenReal (hWL : FnegEWA_evenReal_Hyp)
    {u : EWA T 1} (hu : EvenRealEWA u) (γ : ℝ) :
    EvenRealEWA (realPowEWA u γ) := by
  rw [realPowEWA]
  refine EvenRealEWA.mul ?_ (hWL u _ hu)
  -- `u ^ (Nat.floor γ + 1)` is even-real by induction via the product closure.
  generalize Nat.floor γ + 1 = m
  induction m with
  | zero => simpa using EvenRealEWA.one
  | succ k ih => rw [pow_succ]; exact ih.mul hu

/-- **`qFactor` preserves EvenReal**, modulo the WL-parity hypothesis.
`qFactor β v = FnegEWA (1+v) β`: `1+v` is EvenReal (`one` + `add`), then `hWL`. -/
theorem qFactor_evenReal (hWL : FnegEWA_evenReal_Hyp)
    (β : ℝ) {v : EWA T 1} (hv : EvenRealEWA v) :
    EvenRealEWA (qFactor β v) := by
  rw [qFactor]
  exact hWL (1 + v) β (EvenRealEWA.one.add hv)

/-! ### Closure 7 — the resolved field `vFieldEWA` is EvenReal (modulo WL). -/

/-- `vFieldEWA μ ν γ hμ u = gResolver μ (ν • realPowEWA u γ)`.  `gResolver` is a
diagonal scalar multiplier with the **even-real** symbol `1/(μ+(nπ)²)`, so it
preserves the even-real structure; the `ν•realPowEWA` argument is even-real by
`realPowEWA_evenReal` + `smul_real`. -/
theorem vFieldEWA_evenReal (hWL : FnegEWA_evenReal_Hyp)
    {μ ν γ : ℝ} (hμ : 0 < μ) {u : EWA T 1} (hu : EvenRealEWA u) :
    EvenRealEWA (vFieldEWA μ ν γ hμ u) := by
  rw [vFieldEWA]
  -- the argument `ν • realPowEWA u γ` is even-real.
  have harg : EvenRealEWA ((ν : ℂ) • realPowEWA u γ) :=
    (realPowEWA_evenReal hWL hu γ).smul_real ν
  -- `gResolver` is a scalar multiplier with symbol `m n = 1/(μ+(nπ)²)`, even & real.
  set W : EWA T 1 := (ν : ℂ) • realPowEWA u γ with hW
  refine ⟨?_, ?_⟩
  · intro τ n
    have hcoe : ∀ k : ℤ, (sliceWA τ (GWA.gResolver μ hμ W)).toFun k
        = ((1 / (μ + ((k : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) • (sliceWA τ W).toFun k := by
      intro k
      rw [coeff_sliceWA, GWA.gResolver, GWA.scalarMultiplier_toFun,
        ContinuousMap.smul_apply, coeff_sliceWA]
    rw [hcoe (-n), hcoe n, harg.even τ n]
    congr 2
    push_cast; ring_nf
  · intro τ n
    have hcoe : (sliceWA τ (GWA.gResolver μ hμ W)).toFun n
        = ((1 / (μ + ((n : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) • (sliceWA τ W).toFun n := by
      rw [coeff_sliceWA, GWA.gResolver, GWA.scalarMultiplier_toFun,
        ContinuousMap.smul_apply, coeff_sliceWA]
    rw [hcoe, smul_eq_mul, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      harg.real τ n]; ring

/-! ### THE TARGETS — `chemFluxEWA` is OddImag, `chemDivEWA` is EvenReal. -/

/-- **Target 1: `chemFluxEWA` is OddImag** (modulo WL).  Structurally
`chemFluxEWA u = u · v_x · q`, where `u` is EvenReal, `v_x = incl (gDeriv vField)`
is OddImag (`gDeriv` of the EvenReal field, then `incl`), and `q = qFactor β
(incl vField)` is EvenReal.  Hence `EvenReal · OddImag · EvenReal = OddImag`. -/
theorem chemFluxEWA_oddImag (hWL : FnegEWA_evenReal_Hyp)
    {μ ν β γ : ℝ} (hμ : 0 < μ) {u : EWA T 1} (hu : EvenRealEWA u) :
    OddImagEWA (chemFluxEWA μ ν β γ hμ u) := by
  rw [chemFluxEWA]
  have hv : EvenRealEWA (vFieldEWA μ ν γ hμ u) := vFieldEWA_evenReal hWL hμ hu
  -- `v_x = incl (gDeriv vField)` is OddImag.
  have hvx : OddImagEWA (GWA.incl (by omega : (1:ℕ) ≤ 2)
      (GWA.gDeriv (vFieldEWA μ ν γ hμ u))) :=
    (hv.gDeriv).incl (by omega : (1:ℕ) ≤ 2)
  -- `q = qFactor β (incl vField)` is EvenReal.
  have hq : EvenRealEWA (qFactor β
      (GWA.incl (by omega : (1:ℕ) ≤ 3) (vFieldEWA μ ν γ hμ u))) :=
    qFactor_evenReal hWL β (hv.incl (by omega : (1:ℕ) ≤ 3))
  -- assemble: (u · v_x) · q = (EvenReal · OddImag) · EvenReal = OddImag · EvenReal = OddImag.
  exact (hu.mul_oddImag hvx).mul_evenReal hq

/-- **Target 2: `chemDivEWA` is EvenReal** (modulo WL).  `chemDivEWA = gDeriv
(chemFluxEWA u)`, and `gDeriv` maps OddImag → EvenReal.  These two targets
discharge the coefficient bridge's `heven`/`hreal` hypotheses for `chemDivEWA`. -/
theorem chemDivEWA_evenReal (hWL : FnegEWA_evenReal_Hyp)
    {μ ν γ : ℝ} (hμ : 0 < μ) (p : CM2Params) {u : EWA T 1} (hu : EvenRealEWA u) :
    EvenRealEWA (chemDivEWA μ ν γ hμ p u) := by
  rw [chemDivEWA]
  exact (chemFluxEWA_oddImag hWL hμ hu).gDeriv

end ShenWork.EWA

#print axioms ShenWork.EWA.chemFluxEWA_oddImag
#print axioms ShenWork.EWA.chemDivEWA_evenReal
