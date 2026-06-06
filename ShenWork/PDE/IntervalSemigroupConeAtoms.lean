/-
  Cone atoms (Q1 groundwork): operator scalar linearity and the
  Duhamel-of-cone evaluation.

  For the χ₀ = 0 cone-invariance route, the mild map's Duhamel term must
  be evaluated EXACTLY on cone elements `c(s)·S(s)f`:

    `∫₀ᵗ S(t−s)(c(s)·S(s)f)(x) ds = (∫₀ᵗ c(s) ds) · S(t)f(x)`,

  which re-absorbs the Grönwall envelope into the same `S(t)f` profile:
  with `c(s) = a·e^{as}` this gives `(e^{at} − 1)·S(t)f`, hence the exact
  invariance of the upper cone `w ≤ e^{at}·S(t)u₀`, and with
  `c(s) = −K·e^{as}` the lower envelope `θ(t)·S(t)u₀`,
  `θ(t) = 1 − K(e^{at}−1)/a`.

  Atoms:
  * `intervalFullSemigroupOperator_const_mul` — `S(t)(c·f) = c·S(t)f`;
  * `intervalFullSemigroupOperator_comp_const_mul` —
    `S(t−s)(c·S(s)f)(x) = c·S(t)f(x)` on `[0,1]` (composition law);
  * `duhamel_cone_eval` — the displayed integral evaluation
    (no integrability hypothesis: `integral_mul_const` is unconditional).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalSemigroupComposition

open MeasureTheory
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalSemigroupComposition

noncomputable section

namespace ShenWork.IntervalSemigroupConeAtoms

/-- Scalar linearity of the full Neumann propagator. -/
theorem intervalFullSemigroupOperator_const_mul
    (t c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator t (fun y => c * f y) x
      = c * intervalFullSemigroupOperator t f x := by
  unfold intervalFullSemigroupOperator
  calc (∫ y, intervalNeumannFullKernel t x y * (c * f y)
        ∂(ShenWork.IntervalDomain.intervalMeasure 1))
      = ∫ y, c * (intervalNeumannFullKernel t x y * f y)
          ∂(ShenWork.IntervalDomain.intervalMeasure 1) := by
        congr 1; funext y; ring
    _ = c * ∫ y, intervalNeumannFullKernel t x y * f y
          ∂(ShenWork.IntervalDomain.intervalMeasure 1) :=
        integral_const_mul c _

/-- **Composition + scalar linearity on cone elements**:
`S(t−s)(c·S(s)f)(x) = c·S(t)f(x)` for `0 < s < t`, on `[0,1]`. -/
theorem intervalFullSemigroupOperator_comp_const_mul
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M) (c : ℝ)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator (t - s)
        (fun y => c * intervalFullSemigroupOperator s f y) x
      = c * intervalFullSemigroupOperator t f x := by
  rw [intervalFullSemigroupOperator_const_mul]
  congr 1
  have hcomp := intervalFullSemigroupOperator_comp
    (sub_pos.mpr hst) hs hf hM hx
  have hts : t - s + s = t := by ring
  rw [hcomp, hts]

/-- **Duhamel-of-cone evaluation**: the Duhamel integral of a cone family
`s ↦ c(s)·S(s)f` collapses to `(∫₀ᵗ c)·S(t)f(x)`, for any interval-
integrable scalar profile `c`. -/
theorem duhamel_cone_eval
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M)
    {c : ℝ → ℝ}
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
        (fun y => c s * intervalFullSemigroupOperator s f y) x)
      = (∫ s in (0:ℝ)..t, c s) * intervalFullSemigroupOperator t f x := by
  have hcongr : (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
        (fun y => c s * intervalFullSemigroupOperator s f y) x)
      = ∫ s in (0:ℝ)..t, c s * intervalFullSemigroupOperator t f x := by
    apply intervalIntegral.integral_congr_ae
    have hne_t : ∀ᵐ s : ℝ ∂MeasureTheory.volume, s ≠ t := by
      rw [MeasureTheory.ae_iff]
      simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
    filter_upwards [hne_t] with s hsne hsI
    rw [Set.uIoc_of_le ht.le] at hsI
    have hst : s < t := lt_of_le_of_ne hsI.2 hsne
    exact intervalFullSemigroupOperator_comp_const_mul hsI.1 hst hf hM
      (c s) hx
  rw [hcongr, intervalIntegral.integral_mul_const]

end ShenWork.IntervalSemigroupConeAtoms
