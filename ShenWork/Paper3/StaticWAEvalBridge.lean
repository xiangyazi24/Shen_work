import ShenWork.Paper3.StaticWANeumann
import ShenWork.Wiener.WeightedL1EvalDeriv
import ShenWork.Wiener.EWA.CoeffBridge
import ShenWork.Wiener.EWA.ParityFoundations
import ShenWork.PDE.IntervalDuhamelClosedC2
import ShenWork.Paper2.IntervalPicardIterateRestart

/-!
# Evaluation of static even-real Wiener profiles

This file connects the static coefficient spaces used by the `m = 3`
counterexample to real `C²` functions on the unit interval.

For an even-real element of `WA r`, its bilateral Fourier coefficients are
repackaged as the usual real cosine coefficients.  The resulting synthesis
identity supplies:

* real-valued Wiener evaluation;
* the uniform point-evaluation bound;
* `C²` regularity for `WA 2`;
* the two Neumann endpoint identities;
* the interval integral as the zeroth Fourier coefficient; and
* commutation of real evaluation with the first two Fourier derivatives.
-/

open scoped BigOperators

noncomputable section

namespace ShenWork.M3Counterexample

open ShenWork.Wiener
open ShenWork.CosineSpectrum
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalMildPicardRegularity
open ShenWork.IntervalPicardIterateRestart

/-! ## Real evaluation -/

/-- Real part of the period-two Wiener synthesis on the ambient real line. -/
def staticEval {r : ℕ} (a : WA r) (x : ℝ) : ℝ :=
  (WA.evalC (WA.toZero a) (x : WA.Circ)).re

theorem staticEval_continuous {r : ℕ} (a : WA r) :
    Continuous (staticEval a) := by
  exact Complex.continuous_re.comp
    ((WA.evalC (WA.toZero a)).continuous.comp continuous_quotient_mk')

/-- Point evaluation is bounded by the weighted Wiener norm. -/
theorem abs_staticEval_le_norm {r : ℕ} (a : WA r) (x : ℝ) :
    |staticEval a x| ≤ ‖a‖ := by
  calc
    |staticEval a x| ≤ ‖WA.evalC (WA.toZero a) (x : WA.Circ)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖WA.evalC (WA.toZero a)‖ :=
      (WA.evalC (WA.toZero a)).norm_coe_le_norm _
    _ ≤ ‖WA.toZero a‖ := WA.evalLin_norm_le (WA.toZero a)
    _ ≤ ‖a‖ := by
      change wNorm 0 a.toFun ≤ wNorm r a.toFun
      exact wNorm_mono_le (Nat.zero_le r) a.mem

/-! ## Static cosine coefficients -/

/-- Cosine coefficients associated with an even-real bilateral sequence. -/
def staticCosCoeff {r : ℕ} (a : EvenRealWA r) (k : ℕ) : ℝ :=
  if k = 0 then (a.1.toFun 0).re else 2 * (a.1.toFun (k : ℤ)).re

@[simp]
theorem staticCosCoeff_zero {r : ℕ} (a : EvenRealWA r) :
    staticCosCoeff a 0 = (a.1.toFun 0).re := by
  simp [staticCosCoeff]

theorem staticCosCoeff_of_ne_zero {r : ℕ} (a : EvenRealWA r)
    {k : ℕ} (hk : k ≠ 0) :
    staticCosCoeff a k = 2 * (a.1.toFun (k : ℤ)).re := by
  simp [staticCosCoeff, hk]

private theorem complex_eq_ofReal_re_of_im_zero {z : ℂ} (hz : z.im = 0) :
    z = (z.re : ℂ) := by
  apply Complex.ext <;> simp [hz]

/-- An even-real bilateral sequence is exactly the bilateral embedding of its
static cosine coefficients. -/
theorem evenReal_toFun_eq_ofCosineCoeffs {r : ℕ} (a : EvenRealWA r) :
    a.1.toFun = ofCosineCoeffs (staticCosCoeff a) := by
  funext n
  have ha_im : (a.1.toFun n).im = 0 := EvenRealWA.coeff_im_eq_zero a n
  have hc_im : (ofCosineCoeffs (staticCosCoeff a) n).im = 0 :=
    ofCosineCoeffs_im (staticCosCoeff a) n
  rw [complex_eq_ofReal_re_of_im_zero ha_im,
    complex_eq_ofReal_re_of_im_zero hc_im]
  congr 1
  by_cases hn : n = 0
  · subst hn
    simp [ofCosineCoeffs, staticCosCoeff]
  · rw [ShenWork.EWA.re_ofCosineCoeffs, if_neg hn]
    set k : ℕ := n.natAbs with hk
    have hk0 : k ≠ 0 := by
      rw [hk]
      exact Int.natAbs_ne_zero.mpr hn
    rw [staticCosCoeff_of_ne_zero a hk0]
    have hcoeff :
        a.1.toFun n = a.1.toFun (k : ℤ) := by
      rcases le_or_gt 0 n with hnonneg | hneg
      · have hnrep : n = (k : ℤ) := by
          rw [hk, Int.natCast_natAbs, abs_of_nonneg hnonneg]
        exact congrArg a.1.toFun hnrep
      · have hnrep : n = -(n.natAbs : ℤ) := by
          rw [Int.natCast_natAbs, abs_of_neg hneg]
          ring
        have hnrep' : n = -(k : ℤ) := by simpa [hk] using hnrep
        calc
          a.1.toFun n = a.1.toFun (-(k : ℤ)) :=
            congrArg a.1.toFun hnrep'
          _ = a.1.toFun (k : ℤ) := EvenRealWA.coeff_neg a (k : ℤ)
    rw [← hcoeff]
    ring

/-- Weighted summability of the associated cosine coefficients follows from
the defining weighted bilateral `ℓ¹` summability. -/
theorem staticCosCoeff_weighted_summable {r : ℕ} (a : EvenRealWA r) :
    Summable (fun k : ℕ =>
      (1 + (k : ℝ)) ^ r * |staticCosCoeff a k|) := by
  have hsZ :
      Summable (fun n : ℤ => wWeight r n * ‖a.1.toFun n‖) :=
    a.1.mem
  have hinj : Function.Injective (fun k : ℕ => (k : ℤ)) := by
    exact_mod_cast Nat.cast_injective
  have hsN :
      Summable (fun k : ℕ => wWeight r (k : ℤ) * ‖a.1.toFun (k : ℤ)‖) :=
    hsZ.comp_injective hinj
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (by positivity) (abs_nonneg _)) (fun k => ?_)
    (hsN.mul_left 2)
  have hweight :
      wWeight r (k : ℤ) = (1 + (k : ℝ)) ^ r := by
    simp [wWeight, abs_of_nonneg]
  by_cases hk : k = 0
  · subst hk
    rw [staticCosCoeff_zero, hweight]
    simp only [Nat.cast_zero, add_zero, one_pow, one_mul]
    calc
      |(a.1.toFun 0).re| ≤ ‖a.1.toFun 0‖ := Complex.abs_re_le_norm _
      _ ≤ 2 * ‖a.1.toFun 0‖ := by
        nlinarith [norm_nonneg (a.1.toFun 0)]
  · rw [staticCosCoeff_of_ne_zero a hk, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), hweight]
    calc
      (1 + (k : ℝ)) ^ r * (2 * |(a.1.toFun (k : ℤ)).re|)
          = 2 * ((1 + (k : ℝ)) ^ r * |(a.1.toFun (k : ℤ)).re|) := by ring
      _ ≤ 2 * ((1 + (k : ℝ)) ^ r * ‖a.1.toFun (k : ℤ)‖) := by
        gcongr
        exact Complex.abs_re_le_norm _

theorem staticCosCoeff_summable {r : ℕ} (a : EvenRealWA r) :
    Summable (fun k : ℕ => |staticCosCoeff a k|) := by
  simpa using staticCosCoeff_weighted_summable (r := 0)
    (⟨WA.toZero a.1, by
      rw [mem_evenRealSubmodule_iff]
      exact ⟨fun n => EvenRealWA.coeff_im_eq_zero a n,
        fun n => EvenRealWA.coeff_neg a n⟩⟩ : EvenRealWA 0)

/-- Full real-line cosine synthesis of a static even-real Wiener element. -/
theorem evalC_evenReal_eq_cosineSeries {r : ℕ} (a : EvenRealWA r) (x : ℝ) :
    WA.evalC (WA.toZero a.1) (x : WA.Circ) =
      ((∑' k : ℕ, staticCosCoeff a k * cosineMode k x : ℝ) : ℂ) := by
  have hsum := staticCosCoeff_summable a
  let b : WA 0 :=
    ⟨ofCosineCoeffs (staticCosCoeff a),
      memW_ofCosineCoeffs (r := 0) (by simpa using hsum)⟩
  have hab : WA.toZero a.1 = b := by
    apply WA.ext
    exact evenReal_toFun_eq_ofCosineCoeffs a
  rw [hab]
  exact ShenWork.EWA.evalC_ofCosineCoeffs_all (staticCosCoeff a) hsum x

theorem evalC_evenReal_eq_ofReal_staticEval {r : ℕ}
    (a : EvenRealWA r) (x : ℝ) :
    WA.evalC (WA.toZero a.1) (x : WA.Circ) =
      ((staticEval a.1 x : ℝ) : ℂ) := by
  apply Complex.ext
  · rfl
  · rw [evalC_evenReal_eq_cosineSeries]
    simp

theorem staticEval_evenReal_eq_cosineSeries {r : ℕ}
    (a : EvenRealWA r) :
    staticEval a.1 =
      fun x => ∑' k : ℕ, staticCosCoeff a k * cosineMode k x := by
  funext x
  have h := evalC_evenReal_eq_cosineSeries a x
  exact congrArg Complex.re h

/-! ## `C²`, Neumann, and mass -/

theorem staticCosCoeff_eigenvalue_summable (a : EvenRealWA 2) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k * |staticCosCoeff a k|) := by
  have hs := staticCosCoeff_weighted_summable a
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (sq_nonneg _) (abs_nonneg _)) (fun k => ?_)
    (hs.mul_left (Real.pi ^ 2))
  unfold unitIntervalCosineEigenvalue
  have hk : (k : ℝ) ≤ 1 + (k : ℝ) := by linarith
  have hsquare : (k : ℝ) ^ 2 ≤ (1 + (k : ℝ)) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ (k : ℝ) by positivity]
  calc
    ((k : ℝ) * Real.pi) ^ 2 * |staticCosCoeff a k|
        = Real.pi ^ 2 * ((k : ℝ) ^ 2 * |staticCosCoeff a k|) := by ring
    _ ≤ Real.pi ^ 2 *
        ((1 + (k : ℝ)) ^ 2 * |staticCosCoeff a k|) := by
      gcongr

theorem staticEval_contDiff_two (a : EvenRealWA 2) :
    ContDiff ℝ 2 (staticEval a.1) := by
  rw [staticEval_evenReal_eq_cosineSeries a]
  exact ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two
    (staticCosCoeff_eigenvalue_summable a)

theorem staticEval_neumann_zero (a : EvenRealWA 2) :
    deriv (staticEval a.1) 0 = 0 := by
  rw [staticEval_evenReal_eq_cosineSeries a]
  exact ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv_at_zero
    (staticCosCoeff_eigenvalue_summable a)

theorem staticEval_neumann_one (a : EvenRealWA 2) :
    deriv (staticEval a.1) 1 = 0 := by
  rw [staticEval_evenReal_eq_cosineSeries a]
  exact ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_deriv_at_one
    (staticCosCoeff_eigenvalue_summable a)

theorem intervalIntegral_staticEval_eq_coeff_zero {r : ℕ}
    (a : EvenRealWA r) :
    ∫ x in (0 : ℝ)..1, staticEval a.1 x = (a.1.toFun 0).re := by
  have hsum := staticCosCoeff_summable a
  have hcoeff :=
    cosineCoeffs_of_l1_cosineSeries hsum 0
  rw [← staticEval_evenReal_eq_cosineSeries a] at hcoeff
  rw [cosineCoeffs_eq_factor_mul_integral] at hcoeff
  simpa [staticCosCoeff, cosineMode] using hcoeff

/-! ## Fourier differentiation and real differentiation -/

theorem staticEval_hasDerivAt_wD {r : ℕ} (a : WA (r + 1)) (x : ℝ) :
    HasDerivAt (staticEval a) (staticEval (WA.wD a) x) x := by
  have hc := WA.evalC_hasDerivAt_wD a x
  have hr :=
    (Complex.reCLM.hasFDerivAt.comp x hc.hasFDerivAt).hasDerivAt
  simpa [staticEval] using hr

theorem deriv_staticEval_eq_wD {r : ℕ} (a : WA (r + 1)) (x : ℝ) :
    deriv (staticEval a) x = staticEval (WA.wD a) x :=
  (staticEval_hasDerivAt_wD a x).deriv

/-- The complex synthesis of the Fourier derivative of an even-real profile
is the real derivative, embedded in `ℂ`. -/
theorem evalC_wD_evenReal_eq_ofReal_deriv {r : ℕ}
    (a : EvenRealWA (r + 1)) (x : ℝ) :
    WA.evalC (WA.toZero (WA.wD a.1)) (x : WA.Circ) =
      ((deriv (staticEval a.1) x : ℝ) : ℂ) := by
  have hc := WA.evalC_hasDerivAt_wD a.1 x
  have heq :
      (fun y : ℝ => WA.evalC (WA.toZero a.1) (y : WA.Circ)) =
        fun y : ℝ => ((staticEval a.1 y : ℝ) : ℂ) := by
    funext y
    exact evalC_evenReal_eq_ofReal_staticEval a y
  rw [heq] at hc
  have hr :=
    (staticEval_hasDerivAt_wD a.1 x).ofReal_comp
  have hunique := hc.unique hr
  rw [deriv_staticEval_eq_wD]
  exact hunique

theorem secondDeriv_staticEval_eq_wD_wD (a : WA 2) (x : ℝ) :
    deriv (deriv (staticEval a)) x =
      staticEval (WA.wD (WA.wD a)) x := by
  have hfirst :
      deriv (staticEval a) = staticEval (WA.wD a) := by
    funext y
    exact deriv_staticEval_eq_wD a y
  rw [hfirst]
  exact deriv_staticEval_eq_wD (WA.wD a) x

end ShenWork.M3Counterexample
