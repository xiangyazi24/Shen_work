import ShenWork.Wiener.EWA.Duhamel
import ShenWork.Wiener.EWA.EvenRealClosure
import ShenWork.Wiener.EWA.NonCircularCoeffBridge
import ShenWork.Wiener.EWA.CoeffBridge

/-!
# EWA brick (χ₀<0 Route A′) — BRIDGE B: the DUHAMEL-SYNTHESIS EVAL bridge

The space-time evaluation (`evalST`) of the EWA Duhamel elements equals the cosine
spectral synthesis of their per-mode Duhamel coefficients.  This MIRRORS the committed
heat bridge `heatEWA_evalST_eq_cosineHeatValue` (`HeatFloor.lean:169`): the slice of the
Duhamel element is an even cosine embedding `ofCosineCoeffs` of its real per-mode
coefficients, and the committed full-circle synthesis `evalC_ofCosineCoeffs_all` reads it
off as a `cosineMode` series.

This is the chemDiv/logistic Duhamel half of the `realizes` field of
`SourceStrongSolutionData` (`SourceStrongSolution.lean:282`): with the heat leg supplied
by `heatEWA_evalST_eq_cosineHeatValue`, the value/divergence Duhamel legs (the eval of
`valDuhamelEWA`/`divDuhamelEWA`) are realized here.

## The two ingredients

1. **Parity propagation** (the genuinely-new, PDE-substantive step).  The EWA Duhamel
   operators inherit parity from their input:
   * `valDuhamelEWA` of an **even-real** input is **even-real**
     (`EvenRealEWA.valDuhamelEWA`) — the per-mode value kernel `coef = 1` is even in `n`
     and real, so the time integral of an even-real integrand stays even-real;
   * `divDuhamelEWA` of an **odd-imaginary** input is **even-real**
     (`OddImagEWA.divDuhamelEWA`) — the per-mode divergence kernel multiplier
     `coef = inπ` is **odd** in `n` and **imaginary**, so it flips both parities: an odd
     integrand times an odd multiplier is even, an imaginary integrand times an imaginary
     multiplier is real.  This is the spectral `∂ₓ` flipping the parity of the (odd,
     imaginary) flux back to the (even, real) divergence source.

   At the slice/coefficient level both reduce to a pointwise `duhFun`-parity identity
   (`duhFun_neg_mode`/`duhFun_re`), since the per-mode Duhamel integral commutes with the
   slice.

2. **The synthesis** (the structural mirror of the heat bridge).  Once the Duhamel slice
   is even-real, `slice_eq_ofCosineCoeffs_of_even_real` makes it `ofCosineCoeffs` of the
   `±`-mode extractor `ewaCosCoeffAt`, and `evalC_ofCosineCoeffs_all` gives the cosine
   synthesis at every real spatial point.  Summability is INTRINSIC (`summable_abs_of_slice_eq`
   from the EWA element's membership), exactly as in the non-circular coefficient bridge.

## What this discharges

`evalDuhamel_eq_cosineSynthesis` is the `evalST (Duhamel …) x = Σₙ b̂ₙ cosineMode n x` shape
the `realizes` field consumes.  Combined with the committed integrand realizations
(`evalST_chemDivEWA_eq_coupledChemDivSourceLift`, `evalST_growthEWA_eq_logisticLifted`) and
`heatEWA_evalST_eq_cosineHeatValue` for the heat leg, the Picard map `Φ(u*)` evaluates to
the full cosine synthesis — i.e. `realizes` becomes dischargeable from the fixed point.

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Part 1 — the per-mode slice of the Duhamel element. -/

/-- The slice of `valDuhamelEWA hT F` at mode `n` and time `τ` is the per-mode value
Duhamel integral applied to the slice integrand `ext hT (F.toFun n)`. -/
theorem coeff_sliceWA_valDuhamelEWA {r : ℕ} (hT : 0 ≤ T) (F : EWA T r)
    (τ : TimeDom T) (n : ℤ) :
    (sliceWA τ (valDuhamelEWA hT F)).toFun n
      = duhFun (((n : ℝ) * Real.pi) ^ 2) 1 (ext hT (F.toFun n)) (τ : ℝ) := by
  rw [coeff_sliceWA, valDuhamelEWA, GWA.coeffwiseCLM_toFun, duhValModeCLM_apply]
  rfl

/-- The slice of `divDuhamelEWA hT B` at mode `n` and time `τ` is the per-mode divergence
Duhamel integral (multiplier `inπ`) applied to the slice integrand `ext hT (B.toFun n)`. -/
theorem coeff_sliceWA_divDuhamelEWA {r : ℕ} (hT : 0 ≤ T) (B : EWA T r)
    (τ : TimeDom T) (n : ℤ) :
    (sliceWA τ (divDuhamelEWA hT B)).toFun n
      = duhFun (((n : ℝ) * Real.pi) ^ 2) (Complex.I * ((n : ℝ) * Real.pi))
          (ext hT (B.toFun n)) (τ : ℝ) := by
  rw [coeff_sliceWA, divDuhamelEWA, GWA.coeffwiseCLM_toFun, duhDivModeCLM_apply]
  rfl

/-! ### Part 2 — the slice integrand `ext hT (F.toFun n)` as a slice coefficient. -/

/-- **The slice integrand as a slice coefficient.**  At every real time `s`, the extended
integrand `ext hT (F.toFun n) s` equals the EWA slice coefficient `(sliceWA σ F).toFun n`
at the clamped time `σ = projIcc s`.  This is the bridge between the per-mode Duhamel
integrand and the slice-level parity hypotheses (which range over all `σ : TimeDom T`). -/
theorem ext_toFun_eq_slice {r : ℕ} (hT : 0 ≤ T) (F : EWA T r) (n : ℤ) (s : ℝ) :
    ext hT (F.toFun n) s
      = (sliceWA (Set.projIcc 0 T hT s) F).toFun n := by
  rw [coeff_sliceWA]
  rfl

/-- **`duhFun` congruence.**  If the multiplier-integrand products agree pointwise, the
two `duhFun` integrals agree. -/
theorem duhFun_congr (y2 : ℝ) {coef coef' : ℂ} {g g' : ℝ → ℂ} (t : ℝ)
    (hcg : ∀ s, coef * g s = coef' * g' s) :
    duhFun y2 coef g t = duhFun y2 coef' g' t := by
  unfold duhFun
  apply intervalIntegral.integral_congr
  intro s _; simp only []; rw [hcg s]

/-- The kernel square is even in the mode: `((-n)π)² = (nπ)²`. -/
theorem modeSq_neg (n : ℤ) :
    (((-n : ℤ) : ℝ) * Real.pi) ^ 2 = ((n : ℝ) * Real.pi) ^ 2 := by
  push_cast; ring

/-- The complex heat factor of the per-mode kernel is the cast of a real exponential. -/
theorem duhKernel_ofReal (y2 t s : ℝ) :
    Complex.exp (-((↑(t - s)) * (↑y2))) = ((Real.exp (-((t - s) * y2)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast; ring

/-- **`duhFun` reality.**  If the multiplier-integrand product is the cast of a continuous
real function `h` pointwise, then `duhFun` is the cast of a real integral, hence has zero
imaginary part. -/
theorem duhFun_im_zero (y2 t : ℝ) (coef : ℂ) (g : ℝ → ℂ)
    (h : ℝ → ℝ) (hcg : ∀ s, coef * g s = ((h s : ℝ) : ℂ)) :
    (duhFun y2 coef g t).im = 0 := by
  have hrw : duhFun y2 coef g t
      = ((∫ s in (0:ℝ)..t, Real.exp (-((t - s) * y2)) * h s : ℝ) : ℂ) := by
    unfold duhFun
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    rw [duhKernel_ofReal, hcg s]
    push_cast; ring
  rw [hrw, Complex.ofReal_im]

/-! ### Part 3 — the EWA Duhamel parity closures. -/

/-- **Value Duhamel preserves even-real.**  `valDuhamelEWA hT F` of an even-real `F` is
even-real: the value multiplier `coef = 1` is mode-independent and real, so the per-mode
integral inherits evenness (integrand `ext (F.toFun (-n)) = ext (F.toFun n)` pointwise) and
reality (real integrand). -/
theorem EvenRealEWA.valDuhamelEWA {r : ℕ} (hT : 0 ≤ T) {F : EWA T r}
    (hF : EvenRealEWA F) : EvenRealEWA (ShenWork.EWA.valDuhamelEWA hT F) where
  even τ n := by
    rw [coeff_sliceWA_valDuhamelEWA, coeff_sliceWA_valDuhamelEWA, modeSq_neg]
    apply duhFun_congr
    intro s
    rw [one_mul, one_mul, ext_toFun_eq_slice, ext_toFun_eq_slice]
    exact hF.even _ n
  real τ n := by
    rw [coeff_sliceWA_valDuhamelEWA]
    refine duhFun_im_zero _ _ _ _ (fun s => (ext hT (F.toFun n) s).re) (fun s => ?_)
    rw [one_mul]
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im, ext_toFun_eq_slice]; exact hF.real _ n

/-- **Divergence Duhamel sends odd-imaginary to even-real.**  `divDuhamelEWA hT B` of an
odd-imaginary `B` is even-real.  The divergence multiplier `coef = inπ` is **odd** in `n`
(`i(-n)π = -inπ`) and **imaginary**; pairing with the odd integrand `B.toFun (-n) = -B.toFun n`
gives an **even** product, and pairing the imaginary multiplier with the imaginary integrand
gives a **real** product.  This is the spectral `∂ₓ` turning the (odd, imaginary) flux back
into the (even, real) divergence source. -/
theorem OddImagEWA.divDuhamelEWA {r : ℕ} (hT : 0 ≤ T) {B : EWA T r}
    (hB : OddImagEWA B) : EvenRealEWA (ShenWork.EWA.divDuhamelEWA hT B) where
  even τ n := by
    rw [coeff_sliceWA_divDuhamelEWA, coeff_sliceWA_divDuhamelEWA, modeSq_neg]
    apply duhFun_congr
    intro s
    -- `i(-n)π · ext(B_{-n}) s = inπ · ext(B_n) s`: odd×odd = even.
    rw [ext_toFun_eq_slice, ext_toFun_eq_slice, hB.odd _ n]
    push_cast; ring
  real τ n := by
    rw [coeff_sliceWA_divDuhamelEWA]
    -- `inπ · ext(B_n) s` is real: imaginary × imaginary.  Witness `h s = -nπ·(integrand).im`.
    refine duhFun_im_zero _ _ _ _
      (fun s => -((n : ℝ) * Real.pi) * (ext hT (B.toFun n) s).im) (fun s => ?_)
    -- `inπ · z = (-(nπ)·z.im : ℝ)` when `z.re = 0`.
    have hz : (ext hT (B.toFun n) s).re = 0 := by
      rw [ext_toFun_eq_slice]; exact hB.imag _ n
    apply Complex.ext
    · -- real parts: `(inπ·z).re = -nπ·z.im = h s`.
      rw [Complex.ofReal_re]
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    · -- imag parts: `(inπ·z).im = nπ·z.re = 0` (by `hz`); `(h s : ℂ).im = 0`.
      rw [Complex.ofReal_im]
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      rw [hz]; ring

/-! ### Part 4 — the synthesis bridge (mirror of `heatEWA_evalST_eq_cosineHeatValue`). -/

/-- **The generic eval-synthesis bridge.**  For any grade-0 EWA element `F` whose slice at
`τ` is even-real, the space-time evaluation at every real `x` is the cosine synthesis of the
`±`-mode coefficient extractor `ewaCosCoeffAt F τ`:
`evalST τ x F = Σₙ ewaCosCoeffAt F τ n · cosineMode n x`.

This is exactly the synthesis step inside `ewaCosCoeffAt_eq_cosineCoeffs_of_even_real`, lifted
to a standalone bridge.  Summability is INTRINSIC (`summable_abs_of_slice_eq` from `F.mem`),
mirroring `heatEWA_evalST_eq_cosineHeatValue`. -/
theorem evalST_eq_cosineSynthesis_of_even_real {F : EWA T 0} {τ : TimeDom T}
    (heven : ∀ n : ℤ, (sliceWA τ F).toFun (-n) = (sliceWA τ F).toFun n)
    (hreal : ∀ n : ℤ, ((sliceWA τ F).toFun n).im = 0) (x : ℝ) :
    evalST τ ((x : ℝ) : WA.Circ) F
      = ((∑' n : ℕ, ewaCosCoeffAt F τ n * cosineMode n x : ℝ) : ℂ) := by
  set c : ℕ → ℝ := ewaCosCoeffAt F τ with hc
  have hslice : (sliceWA τ F).toFun = ofCosineCoeffs c :=
    slice_eq_ofCosineCoeffs_of_even_real heven hreal
  have hcsum : Summable (fun k : ℕ => |c k|) := summable_abs_of_slice_eq hslice
  set a' : WA 0 := ⟨ofCosineCoeffs c, memW_ofCosineCoeffs (r := 0) (by simpa using hcsum)⟩
    with ha'
  have hsliceWA : sliceWA τ F = a' := by apply WA.ext; rw [ha']; exact hslice
  rw [evalST_apply, WA.evalAt_apply, ← WA.evalC_apply, hsliceWA, ha']
  exact evalC_ofCosineCoeffs_all c hcsum x

/-- **BRIDGE B (value leg).**  The space-time evaluation of the value Duhamel element
(grade-dropped to `0`) is the cosine synthesis of the per-mode value-Duhamel coefficients,
for any even-real input `F`.  This realizes the EWA `valDuhamelEWA` element (the logistic
Duhamel leg) as the cosine synthesis of `∫₀ᵗ e^{−(t−s)λₙ}·F̂ₙ(s) ds`. -/
theorem valDuhamelEWA_evalST_eq_cosineSynthesis (hT : 0 ≤ T) {F : EWA T 1}
    (hF : EvenRealEWA F) (τ : TimeDom T) (x : ℝ) :
    evalST τ ((x : ℝ) : WA.Circ)
        (GWA.incl (by omega : (0:ℕ) ≤ 1) (ShenWork.EWA.valDuhamelEWA hT F))
      = ((∑' n : ℕ,
          ewaCosCoeffAt (GWA.incl (by omega : (0:ℕ) ≤ 1)
            (ShenWork.EWA.valDuhamelEWA hT F)) τ n * cosineMode n x : ℝ) : ℂ) := by
  have hER : EvenRealEWA (GWA.incl (by omega : (0:ℕ) ≤ 1) (ShenWork.EWA.valDuhamelEWA hT F)) :=
    (hF.valDuhamelEWA hT).incl (by omega)
  exact evalST_eq_cosineSynthesis_of_even_real (fun n => hER.even τ n)
    (fun n => hER.real τ n) x

/-- **BRIDGE B (divergence leg).**  The space-time evaluation of the divergence Duhamel
element (grade-dropped to `0`) is the cosine synthesis of the per-mode divergence-Duhamel
coefficients, for any odd-imaginary input `B`.  This realizes the EWA `divDuhamelEWA` element
(the chemDiv source leg, `B = chemFluxEWA …`, odd-imaginary) as the cosine synthesis of
`∫₀ᵗ e^{−(t−s)λₙ}·(inπ)·B̂ₙ(s) ds` — the spectral `∂ₓ` divergence landing in `cosineMode`. -/
theorem divDuhamelEWA_evalST_eq_cosineSynthesis (hT : 0 ≤ T) {B : EWA T 1}
    (hB : OddImagEWA B) (τ : TimeDom T) (x : ℝ) :
    evalST τ ((x : ℝ) : WA.Circ)
        (GWA.incl (by omega : (0:ℕ) ≤ 1) (ShenWork.EWA.divDuhamelEWA hT B))
      = ((∑' n : ℕ,
          ewaCosCoeffAt (GWA.incl (by omega : (0:ℕ) ≤ 1)
            (ShenWork.EWA.divDuhamelEWA hT B)) τ n * cosineMode n x : ℝ) : ℂ) := by
  have hER : EvenRealEWA (GWA.incl (by omega : (0:ℕ) ≤ 1) (ShenWork.EWA.divDuhamelEWA hT B)) :=
    (hB.divDuhamelEWA hT).incl (by omega)
  exact evalST_eq_cosineSynthesis_of_even_real (fun n => hER.even τ n)
    (fun n => hER.real τ n) x

end ShenWork.EWA
