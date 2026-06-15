/-
  ShenWork/Paper1/WaveGreenIdentity.lean

  Variation-of-parameters solve for the constant-coefficient operator
      `Lλ = ∂² + c∂ − λ`        (λ > 0).
  The two-sided Green kernel `Kλ` has roots `r₊ > 0 > r₋` of `s² + c s − λ = 0`.
  The function (the explicit two-sided-exponential split, `= −(Kλ ∗ H)(x)`)
      `w(x) = (1/δ)·[ e^{r₊x} ∫_x^∞ e^{−r₊y} H dy + e^{r₋x} ∫_{−∞}^x e^{−r₋y} H dy ]`
  satisfies `w'' + c w' − λ w = H` pointwise.

  We prove the GENERIC scalar lemma `green_variation_of_parameters`, carrying the
  minimal decay hypotheses (the two families of tail integrals converge), by
  differentiating the explicit split twice.  The FTC kink (the `δ₀`/jump term)
  surfaces on the second derivative and produces the inhomogeneous `+ H` term.
-/
import ShenWork.Paper1.WaveAuxMap

open Filter Topology MeasureTheory Real Set intervalIntegral

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## Weighted tail integrals

For a root `r` and source `H` we abbreviate the weight `e^{−r y} H(y)`. -/

/-- Weighted integrand `g_r(y) = e^{−r y}·H(y)`. -/
def gWeight (r : ℝ) (H : ℝ → ℝ) (y : ℝ) : ℝ := Real.exp (-r * y) * H y

theorem gWeight_continuous {r : ℝ} {H : ℝ → ℝ} (hH : Continuous H) :
    Continuous (gWeight r H) := by
  unfold gWeight
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hH

/-- Upper tail `∫_x^∞ e^{−r y} H(y) dy`. -/
def tailHi (r : ℝ) (H : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in Ioi x, gWeight r H y

/-- Lower tail `∫_{−∞}^x e^{−r y} H(y) dy`. -/
def tailLo (r : ℝ) (H : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in Iic x, gWeight r H y

/-- The variation-of-parameters convolution `w = −(Kλ ∗ H)`, explicit split form. -/
def greenConv (c lam : ℝ) (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  (greenDelta c lam)⁻¹ *
    (Real.exp (greenRootPlus c lam * x) * tailHi (greenRootPlus c lam) H x
      + Real.exp (greenRootMinus c lam * x) * tailLo (greenRootMinus c lam) H x)

/-! ## Derivatives of the tails (FTC) -/

/-- `d/dx ∫_x^∞ g = −g(x)`, via `∫_x^∞ g = ∫_0^∞ g − ∫_0^x g`. -/
theorem tailHi_hasDerivAt {r : ℝ} {H : ℝ → ℝ} (hH : Continuous H)
    (hInt : ∀ t : ℝ, IntegrableOn (gWeight r H) (Ioi t)) (x : ℝ) :
    HasDerivAt (tailHi r H) (-(gWeight r H x)) x := by
  have hcong : tailHi r H =ᶠ[𝓝 x]
      fun u => tailHi r H 0 - ∫ y in (0)..u, gWeight r H y := by
    filter_upwards with u
    have hsub := integral_Ioi_sub_Ioi' (f := gWeight r H) (μ := volume)
      (a := 0) (b := u) (hInt 0) (hInt u)
    -- hsub : ∫ Ioi 0 − ∫ Ioi u = ∫ 0..u
    simp only [tailHi]
    linarith [hsub]
  have hftc : HasDerivAt (fun u => ∫ y in (0)..u, gWeight r H y) (gWeight r H x) x :=
    ((gWeight_continuous (r := r) hH).integral_hasStrictDerivAt 0 x).hasDerivAt
  have := (hasDerivAt_const x (tailHi r H 0)).sub hftc
  simpa using this.congr_of_eventuallyEq hcong

/-- `d/dx ∫_{−∞}^x g = g(x)`, via `∫_{−∞}^x g = ∫_{−∞}^0 g + ∫_0^x g`. -/
theorem tailLo_hasDerivAt {r : ℝ} {H : ℝ → ℝ} (hH : Continuous H)
    (hInt : ∀ t : ℝ, IntegrableOn (gWeight r H) (Iic t)) (x : ℝ) :
    HasDerivAt (tailLo r H) (gWeight r H x) x := by
  have hcong : tailLo r H =ᶠ[𝓝 x]
      fun u => tailLo r H 0 + ∫ y in (0)..u, gWeight r H y := by
    filter_upwards with u
    have hsub := integral_Iic_sub_Iic (f := gWeight r H) (μ := volume)
      (a := 0) (b := u) (hInt 0) (hInt u)
    -- hsub : ∫ Iic u − ∫ Iic 0 = ∫ 0..u
    simp only [tailLo]
    linarith [hsub]
  have hftc : HasDerivAt (fun u => ∫ y in (0)..u, gWeight r H y) (gWeight r H x) x :=
    ((gWeight_continuous (r := r) hH).integral_hasStrictDerivAt 0 x).hasDerivAt
  have := (hasDerivAt_const x (tailLo r H 0)).add hftc
  simpa using this.congr_of_eventuallyEq hcong

/-! ## The two products `A = e^{r₊x}·tailHi`, `B = e^{r₋x}·tailLo` -/

/-- `e^{r₊x}` factor for the upper branch. -/
def expHi (r : ℝ) (x : ℝ) : ℝ := Real.exp (r * x)

theorem expHi_hasDerivAt (r x : ℝ) : HasDerivAt (expHi r) (r * Real.exp (r * x)) x := by
  have hlin : HasDerivAt (fun w => r * w) r x := by
    simpa using (hasDerivAt_id x).const_mul r
  simpa [expHi, mul_comm] using hlin.exp

/-- First derivative of `A(x) = e^{r₊x}·tailHi`.  The FTC boundary term is
`e^{r₊x}·(−g_{r₊}(x)) = −H(x)`. -/
theorem prodHi_hasDerivAt {r : ℝ} {H : ℝ → ℝ} (hH : Continuous H)
    (hInt : ∀ t : ℝ, IntegrableOn (gWeight r H) (Ioi t)) (x : ℝ) :
    HasDerivAt (fun x => expHi r x * tailHi r H x)
      (r * Real.exp (r * x) * tailHi r H x - H x) x := by
  have hd := (expHi_hasDerivAt r x).mul (tailHi_hasDerivAt hH hInt x)
  have hsimp : Real.exp (r * x) * -(gWeight r H x) = -H x := by
    unfold gWeight
    have he : Real.exp (r * x) * Real.exp (-r * x) = 1 := by
      rw [← Real.exp_add]; simp
    linear_combination (-H x) * he
  convert hd using 1
  simp only [expHi]
  rw [hsimp]; ring

/-- First derivative of `B(x) = e^{r₋x}·tailLo`.  The FTC boundary term is
`e^{r₋x}·g_{r₋}(x) = +H(x)`. -/
theorem prodLo_hasDerivAt {r : ℝ} {H : ℝ → ℝ} (hH : Continuous H)
    (hInt : ∀ t : ℝ, IntegrableOn (gWeight r H) (Iic t)) (x : ℝ) :
    HasDerivAt (fun x => expHi r x * tailLo r H x)
      (r * Real.exp (r * x) * tailLo r H x + H x) x := by
  have hd := (expHi_hasDerivAt r x).mul (tailLo_hasDerivAt hH hInt x)
  have hsimp : Real.exp (r * x) * gWeight r H x = H x := by
    unfold gWeight
    have he : Real.exp (r * x) * Real.exp (-r * x) = 1 := by
      rw [← Real.exp_add]; simp
    linear_combination (H x) * he
  convert hd using 1
  simp only [expHi]
  rw [hsimp]

/-! ## First derivative `w'` (the H terms cancel) -/

/-- Value of `w'(x) = (1/δ)·[ r₊ e^{r₊x} tailHi + r₋ e^{r₋x} tailLo ]`. -/
def greenConvDeriv (c lam : ℝ) (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  (greenDelta c lam)⁻¹ *
    (greenRootPlus c lam * Real.exp (greenRootPlus c lam * x) * tailHi (greenRootPlus c lam) H x
      + greenRootMinus c lam * Real.exp (greenRootMinus c lam * x)
          * tailLo (greenRootMinus c lam) H x)

/-- The first derivative of `greenConv`.  The two FTC boundary terms
`∓H(x)` cancel (the kernel `Kλ` is `C⁰` at the kink). -/
theorem greenConv_hasDerivAt {H : ℝ → ℝ} (hH : Continuous H)
    (hHi : ∀ t : ℝ, IntegrableOn (gWeight (greenRootPlus c lam) H) (Ioi t))
    (hLo : ∀ t : ℝ, IntegrableOn (gWeight (greenRootMinus c lam) H) (Iic t))
    (x : ℝ) :
    HasDerivAt (greenConv c lam H) (greenConvDeriv c lam H x) x := by
  have hA := prodHi_hasDerivAt (r := greenRootPlus c lam) hH hHi x
  have hB := prodLo_hasDerivAt (r := greenRootMinus c lam) hH hLo x
  have hAB := hA.add hB
  have hscaled := hAB.const_mul (greenDelta c lam)⁻¹
  have hfun : greenConv c lam H =
      fun x => (greenDelta c lam)⁻¹ *
        (expHi (greenRootPlus c lam) x * tailHi (greenRootPlus c lam) H x
          + expHi (greenRootMinus c lam) x * tailLo (greenRootMinus c lam) H x) := rfl
  rw [hfun]
  convert hscaled using 1
  simp only [greenConvDeriv]; ring

/-! ## Second derivative `w''` (the FTC kink now survives) -/

/-- `w''(x) = (1/δ)·[ r₊² e^{r₊x} tailHi + r₋² e^{r₋x} tailLo + (r₋−r₊) H(x) ]`. -/
def greenConvDeriv2 (c lam : ℝ) (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  (greenDelta c lam)⁻¹ *
    (greenRootPlus c lam ^ 2 * Real.exp (greenRootPlus c lam * x)
        * tailHi (greenRootPlus c lam) H x
      + greenRootMinus c lam ^ 2 * Real.exp (greenRootMinus c lam * x)
          * tailLo (greenRootMinus c lam) H x
      + (greenRootMinus c lam - greenRootPlus c lam) * H x)

/-- The second derivative of `greenConv`.  Differentiating `w'` re-invokes the
product lemmas; this time the boundary terms `r₊·(−H) + r₋·(+H) = (r₋−r₊)H`
do NOT cancel — this is the `δ₀`/kink contribution. -/
theorem greenConvDeriv_hasDerivAt {H : ℝ → ℝ} (hH : Continuous H)
    (hHi : ∀ t : ℝ, IntegrableOn (gWeight (greenRootPlus c lam) H) (Ioi t))
    (hLo : ∀ t : ℝ, IntegrableOn (gWeight (greenRootMinus c lam) H) (Iic t))
    (x : ℝ) :
    HasDerivAt (greenConvDeriv c lam H) (greenConvDeriv2 c lam H x) x := by
  have hA := (prodHi_hasDerivAt (r := greenRootPlus c lam) hH hHi x).const_mul
    (greenRootPlus c lam)
  have hB := (prodLo_hasDerivAt (r := greenRootMinus c lam) hH hLo x).const_mul
    (greenRootMinus c lam)
  have hAB := hA.add hB
  have hscaled := hAB.const_mul (greenDelta c lam)⁻¹
  have hfun : greenConvDeriv c lam H =
      fun x => (greenDelta c lam)⁻¹ *
        (greenRootPlus c lam * (expHi (greenRootPlus c lam) x * tailHi (greenRootPlus c lam) H x)
          + greenRootMinus c lam
              * (expHi (greenRootMinus c lam) x * tailLo (greenRootMinus c lam) H x)) := by
    funext y; simp only [greenConvDeriv, expHi]; ring
  rw [hfun]
  convert hscaled using 1
  simp only [greenConvDeriv2]; ring

/-! ## The variation-of-parameters solve

`greenConv = +(Kλ ∗ H)` solves `Lλ w = −H` (consistent with `Lλ Kλ = −δ₀`),
so `w = −(Kλ ∗ H) = −greenConv` solves `Lλ w = H`. -/

/-- `greenConv = Kλ ∗ H` solves `Lλ w = −H` pointwise (pure algebra of the two
characteristic-equation cancellations and the `(r₋−r₊)=−δ` kink coefficient). -/
theorem greenConv_solves (hlam : 0 < lam) {H : ℝ → ℝ}
    (x : ℝ) :
    greenConvDeriv2 c lam H x + c * greenConvDeriv c lam H x - lam * greenConv c lam H x
      = -H x := by
  have hδ : greenDelta c lam ≠ 0 := ne_of_gt (greenDelta_pos (c := c) hlam)
  have hcp : greenRootPlus c lam ^ 2 + c * greenRootPlus c lam = lam :=
    greenRootPlus_char (c := c) hlam
  have hcm : greenRootMinus c lam ^ 2 + c * greenRootMinus c lam = lam :=
    greenRootMinus_char (c := c) hlam
  have hdiff : greenRootMinus c lam - greenRootPlus c lam = -greenDelta c lam := by
    simp only [greenRootMinus, greenRootPlus]; ring
  simp only [greenConvDeriv2, greenConvDeriv, greenConv]
  -- abbreviations
  generalize tailHi (greenRootPlus c lam) H x = TH
  generalize tailLo (greenRootMinus c lam) H x = TL
  generalize Real.exp (greenRootPlus c lam * x) = EP
  generalize Real.exp (greenRootMinus c lam * x) = EM
  rw [show (greenDelta c lam)⁻¹ *
      (greenRootPlus c lam ^ 2 * EP * TH + greenRootMinus c lam ^ 2 * EM * TL
        + (greenRootMinus c lam - greenRootPlus c lam) * H x)
      + c * ((greenDelta c lam)⁻¹ *
          (greenRootPlus c lam * EP * TH + greenRootMinus c lam * EM * TL))
      - lam * ((greenDelta c lam)⁻¹ * (EP * TH + EM * TL))
      = (greenDelta c lam)⁻¹ *
          ((greenRootPlus c lam ^ 2 + c * greenRootPlus c lam - lam) * (EP * TH)
            + (greenRootMinus c lam ^ 2 + c * greenRootMinus c lam - lam) * (EM * TL)
            + (greenRootMinus c lam - greenRootPlus c lam) * H x) from by ring]
  rw [hcp, hcm, hdiff]
  have : (greenDelta c lam)⁻¹ * ((lam - lam) * (EP * TH) + (lam - lam) * (EM * TL)
      + -greenDelta c lam * H x) = -H x := by
    rw [sub_self, zero_mul, zero_mul, zero_add, zero_add]
    rw [show -greenDelta c lam * H x = -(greenDelta c lam * H x) by ring,
      mul_neg, ← mul_assoc, inv_mul_cancel₀ hδ, one_mul]
  exact this

/-- **Variation of parameters.**  For `Lλ = ∂²+c∂−λ` (λ>0) and continuous `H`
with convergent two-sided exponential-weighted tails, the function
`w(x) = −(Kλ ∗ H)(x) = −greenConv c λ H x` satisfies `w'' + c w' − λ w = H`
pointwise, where `w'`/`w''` are the genuine `deriv`/`iteratedDeriv 2`. -/
theorem green_variation_of_parameters (hlam : 0 < lam) {H : ℝ → ℝ} (hH : Continuous H)
    (hHi : ∀ t : ℝ, IntegrableOn (gWeight (greenRootPlus c lam) H) (Ioi t))
    (hLo : ∀ t : ℝ, IntegrableOn (gWeight (greenRootMinus c lam) H) (Iic t))
    (x : ℝ) :
    iteratedDeriv 2 (fun x => -greenConv c lam H x) x
        + c * deriv (fun x => -greenConv c lam H x) x
        - lam * (fun x => -greenConv c lam H x) x
      = H x := by
  -- w = −greenConv.  w' = −greenConvDeriv, w'' = −greenConvDeriv2.
  have hw' : ∀ y, HasDerivAt (fun x => -greenConv c lam H x)
      (-greenConvDeriv c lam H y) y := fun y =>
    (greenConv_hasDerivAt hH hHi hLo y).neg
  have hderiv_eq : deriv (fun x => -greenConv c lam H x) = fun y => -greenConvDeriv c lam H y :=
    funext fun y => (hw' y).deriv
  have hw'' : HasDerivAt (deriv (fun x => -greenConv c lam H x))
      (-greenConvDeriv2 c lam H x) x := by
    rw [hderiv_eq]
    exact (greenConvDeriv_hasDerivAt hH hHi hLo x).neg
  have hiter : iteratedDeriv 2 (fun x => -greenConv c lam H x) x
      = -greenConvDeriv2 c lam H x := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact hw''.deriv
  rw [hiter, hderiv_eq]
  simp only
  have hsolve := greenConv_solves (c := c) (lam := lam) hlam (H := H) x
  linarith [hsolve]

/-! ## Bridge to `GreenIdentity`

`auxMap` (divergence form) represents `−(Kλ ∗ H)` with `H = auxRHS`.  Granting
that representation (a change-of-variables `z = x−y` plus one integration by
parts of the chemotactic flux term — a separate analytic brick), the generic
variation-of-parameters solve discharges `GreenIdentity` outright. -/

/-- If `auxMap p c λ u` equals the variation-of-parameters solution
`x ↦ −greenConv c λ (auxRHS p λ u) x`, and the source has convergent tails,
then `GreenIdentity p c λ u` holds.  Pure instantiation of
`green_variation_of_parameters`. -/
theorem greenIdentity_of_convRepr (hlam : 0 < lam) (p : CMParams) (u : ℝ → ℝ)
    (hH : Continuous (auxRHS p lam u))
    (hHi : ∀ t : ℝ,
      IntegrableOn (gWeight (greenRootPlus c lam) (auxRHS p lam u)) (Ioi t))
    (hLo : ∀ t : ℝ,
      IntegrableOn (gWeight (greenRootMinus c lam) (auxRHS p lam u)) (Iic t))
    (hrepr : auxMap p c lam u = fun x => -greenConv c lam (auxRHS p lam u) x) :
    GreenIdentity p c lam u := by
  intro x
  rw [hrepr]
  exact green_variation_of_parameters (c := c) (lam := lam) hlam hH hHi hLo x

end ShenWork.Paper1
