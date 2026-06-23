import ShenWork.Paper2.IntervalWienerAlgebraConnect

/-!
  # The Wiener-algebra ℓ¹-convolution-closure for `reflCircle` Fourier coefficients

  This file proves the classical **Wiener algebra** closure fact in the exact form
  the χ₀<0 candidate-generic bridges (`cosineMulBridge_of_summable` /
  `mixedMulBridge_of_summable`) need it: if continuous `f, g` have `reflCircle`
  Fourier coefficients that are summable (ℓ¹), then so does their pointwise product
  `f·g`.  This discharges the `hWsum`/`hvxsum` summability hypotheses
  *candidate-generically*.

  ## Route (all `DERIVED` here; Mathlib has no `fourierCoeff_mul` for `AddCircle`)

  * `reflCircle_mul` (landed): `reflCircle (f·g) = reflCircle f · reflCircle g`.
  * `fcCLM n` — the `n`-th Fourier coefficient as a **continuous ℂ-linear map** on
    `C(AddCircle 2, ℂ)` (integration against `fourier (-n)`, operator-norm `≤ 1`).
  * `fc_mono` — orthogonality: `fourierCoeff (fourier m) n = if n = m then 1 else 0`.
  * The Fourier series of each factor converges in `C(AddCircle 2, ℂ)`
    (`hasSum_fourier_series_of_summable`); the **product** converges via Young's
    ℓ¹-bound (`summable_mul_of_summable_norm` + `tsum_mul_tsum_of_summable_norm` in
    the normed ring `C(AddCircle 2, ℂ)`).  Applying the CLM `fcCLM n` term-by-term
    collapses the product to the **convolution** `∑' j, aₙ₋ⱼ bⱼ`, whose
    summability over `n` is Young's ℓ¹-closure (`Summable.prod` of the reindexed
    double sum).

  No `sorry`/`admit`/`native_decide`/custom axiom; `#print axioms` ⊆
  `{propext, Classical.choice, Quot.sound}`.
-/

noncomputable section

open MeasureTheory AddCircle ShenWork.IntervalCosineInversion
open ShenWork.Paper2.IntervalWienerAlgebra

namespace ShenWork.Paper2.IntervalReflCircleWiener

/-! ## 1. The `n`-th Fourier coefficient as a continuous linear map. -/

/-- Integration against `fourier (-n)` as a ℂ-linear map on `C(AddCircle 2, ℂ)`. -/
def fcLin (n : ℤ) : C(AddCircle (2 : ℝ), ℂ) →ₗ[ℂ] ℂ where
  toFun := fun F => ∫ t, fourier (-n) t • (F t) ∂haarAddCircle
  map_add' := by
    intro F G
    simp only [ContinuousMap.add_apply, smul_add]
    refine integral_add ?_ ?_ <;>
      exact ((by fun_prop : Continuous _).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  map_smul' := by
    intro c F
    simp only [ContinuousMap.smul_apply, RingHom.id_apply, smul_comm (fourier (-n) _) c]
    rw [integral_smul]

/-- The `n`-th Fourier coefficient as a **continuous** ℂ-linear map (norm `≤ 1`). -/
def fcCLM (n : ℤ) : C(AddCircle (2 : ℝ), ℂ) →L[ℂ] ℂ :=
  (fcLin n).mkContinuous 1 (by
    intro F
    change ‖∫ t, fourier (-n) t • (F t) ∂haarAddCircle‖ ≤ 1 * ‖F‖
    rw [one_mul]
    calc ‖∫ t, fourier (-n) t • (F t) ∂haarAddCircle‖
        ≤ ∫ t, ‖fourier (-n) t • (F t)‖ ∂haarAddCircle :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ _t, ‖F‖ ∂haarAddCircle := by
          apply integral_mono_of_nonneg
          · filter_upwards with t; positivity
          · exact integrable_const _
          · filter_upwards with t
            rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
            exact F.norm_coe_le_norm t
      _ = ‖F‖ := by simp)

theorem fcCLM_apply (n : ℤ) (F : C(AddCircle (2 : ℝ), ℂ)) :
    fcCLM n F = fourierCoeff (⇑F) n := by
  rw [fcCLM, LinearMap.mkContinuous_apply]; rfl

/-- **Orthogonality of the Fourier monomials.** -/
theorem fc_mono (m n : ℤ) :
    fourierCoeff (⇑(fourier m : C(AddCircle (2 : ℝ), ℂ))) n = if n = m then 1 else 0 := by
  show fourierCoeff (fourier m) n = _
  unfold fourierCoeff
  have hpt : ∀ t : AddCircle (2 : ℝ),
      (fourier (-n) t : ℂ) • (fourier m t : ℂ) = fourier (-n + m) t := by
    intro t; rw [smul_eq_mul, ← fourier_add', fourier_apply]
  simp_rw [hpt]
  split_ifs with h
  · subst h; simp
  · have hij : -n + m ≠ 0 := by intro hc; apply h; omega
    exact integral_eq_zero_of_add_right_eq_neg (μ := haarAddCircle)
      (fourier_add_half_inv_index hij (Fact.out (p := (0 < (2 : ℝ)))))

/-- `fcCLM n` on a product of two `fourier`-monomial terms collapses to the
convolution contribution `(cᵢ dⱼ)·[n = i+j]`. -/
theorem fcCLM_term (n i j : ℤ) (c d : ℂ) :
    fcCLM n ((c • (fourier i : C(AddCircle (2 : ℝ), ℂ))) * (d • fourier j))
      = c * d * (if n = i + j then 1 else 0) := by
  have hprod : (c • (fourier i : C(AddCircle (2 : ℝ), ℂ))) * (d • fourier j)
      = (c * d) • fourier (i + j) := by
    ext t
    simp only [ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul]
    rw [show (fourier (i+j) t : ℂ) = fourier i t * fourier j t from fourier_add']; ring
  rw [hprod, map_smul, smul_eq_mul, fcCLM_apply, fc_mono]

/-! ## 2. The main Wiener ℓ¹-convolution-closure theorem. -/

/-- **Wiener algebra ℓ¹-closure of `reflCircle` Fourier coefficients.**
For continuous `f, g` whose even-reflection (`reflCircle`) Fourier coefficients are
summable (ℓ¹), the pointwise product `f·g` again has summable `reflCircle` Fourier
coefficients.  This is the classical Wiener algebra fact (`ℓ¹` is a Banach algebra
under convolution), and it discharges the `hWsum`/`hvxsum` candidate-generic
hypotheses of the χ₀<0 bridges. -/
theorem reflCircle_mul_fourier_summable {f g : ℝ → ℝ}
    (hf : Summable (fun n : ℤ => fourierCoeff (reflCircle f) n))
    (hg : Summable (fun n : ℤ => fourierCoeff (reflCircle g) n))
    (hf_cont : Continuous f) (hg_cont : Continuous g) :
    Summable (fun n : ℤ => fourierCoeff (reflCircle (fun x => f x * g x)) n) := by
  -- Bundle each `reflCircle` factor as an opaque continuous map (no `mk` unfolding).
  obtain ⟨Ff, hFf⟩ : ∃ Ff : C(AddCircle (2 : ℝ), ℂ), ⇑Ff = reflCircle f :=
    ⟨⟨reflCircle f, reflCircle_continuous f hf_cont⟩, rfl⟩
  obtain ⟨Fg, hFg⟩ : ∃ Fg : C(AddCircle (2 : ℝ), ℂ), ⇑Fg = reflCircle g :=
    ⟨⟨reflCircle g, reflCircle_continuous g hg_cont⟩, rfl⟩
  set a : ℤ → ℂ := fun n => fourierCoeff (reflCircle f) n with ha
  set b : ℤ → ℂ := fun n => fourierCoeff (reflCircle g) n with hb
  have hna : Summable (fun i => ‖a i‖) := hf.norm
  have hnb : Summable (fun j => ‖b j‖) := hg.norm
  -- Fourier series of each factor in `C(AddCircle 2, ℂ)`.
  have Ha : HasSum (fun i => a i • (fourier i : C(AddCircle (2 : ℝ), ℂ))) Ff := by
    have := hasSum_fourier_series_of_summable (f := Ff) (by rw [hFf]; exact hf)
    simpa only [hFf] using this
  have Hb : HasSum (fun j => b j • (fourier j : C(AddCircle (2 : ℝ), ℂ))) Fg := by
    have := hasSum_fourier_series_of_summable (f := Fg) (by rw [hFg]; exact hg)
    simpa only [hFg] using this
  -- Young: the product family is summable in the normed ring `C(AddCircle 2, ℂ)`.
  have hxn : Summable (fun i => ‖a i • (fourier i : C(AddCircle (2 : ℝ), ℂ))‖) := by
    simp_rw [norm_smul, fourier_norm, mul_one]; exact hna
  have hyn : Summable (fun j => ‖b j • (fourier j : C(AddCircle (2 : ℝ), ℂ))‖) := by
    simp_rw [norm_smul, fourier_norm, mul_one]; exact hnb
  have hprodSum := summable_mul_of_summable_norm hxn hyn
  have htsum := tsum_mul_tsum_of_summable_norm hxn hyn
  rw [Ha.tsum_eq, Hb.tsum_eq] at htsum
  have Hprod : HasSum (fun p : ℤ × ℤ =>
      (a p.1 • (fourier p.1 : C(AddCircle (2 : ℝ), ℂ))) * (b p.2 • fourier p.2))
        (Ff * Fg) := by
    rw [htsum]; exact hprodSum.hasSum
  -- Reindex `(n,j) ↦ aₙ₋ⱼ bⱼ` summable over `(n,j)`; sum over `j` gives ℓ¹ over `n`.
  have hpair : Summable (fun p : ℤ × ℤ => a p.1 * b p.2) :=
    summable_mul_of_summable_norm hna hnb
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.1 - p.2, p.2), invFun := fun p => (p.1 + p.2, p.2)
      left_inv := by intro p; simp, right_inv := by intro p; simp }
  have hshift : Summable (fun p : ℤ × ℤ => a (p.1 - p.2) * b p.2) := by
    have h2 := (e.summable_iff (f := fun p : ℤ × ℤ => a p.1 * b p.2)).mpr hpair
    convert h2 using 1
  refine (hshift.prod).congr ?_
  intro n
  -- Identify `fourierCoeff (reflCircle (f·g)) n` with the convolution `∑' j, aₙ₋ⱼ bⱼ`.
  have hcoe : fourierCoeff (reflCircle (fun x => f x * g x)) n = fourierCoeff (⇑(Ff * Fg)) n := by
    congr 1; funext z
    rw [ContinuousMap.coe_mul, Pi.mul_apply, hFf, hFg]
    exact reflCircle_mul f g z
  -- The mapped HasSum at coefficient `n`.
  have Hn : HasSum (fun p : ℤ × ℤ => a p.1 * b p.2 * (if n = p.1 + p.2 then (1:ℂ) else 0))
      (fcCLM n (Ff * Fg)) :=
    ((fcCLM n).hasSum Hprod).congr_fun (fun p => (fcCLM_term n p.1 p.2 (a p.1) (b p.2)).symm)
  rw [fcCLM_apply] at Hn
  -- Collapse the indicator double sum to the single convolution sum over `j`.
  have hg2 : Function.Injective (fun j : ℤ => ((n - j, j) : ℤ × ℤ)) := by
    intro x y hxy; simpa using congrArg Prod.snd hxy
  have hzero : ∀ p ∉ Set.range (fun j : ℤ => ((n - j, j) : ℤ × ℤ)),
      a p.1 * b p.2 * (if n = p.1 + p.2 then (1:ℂ) else 0) = 0 := by
    intro p hp
    have hne : n ≠ p.1 + p.2 := by
      intro hc
      exact hp ⟨p.2, Prod.ext (by simp; omega) (by simp)⟩
    simp [hne]
  have Hconv : HasSum (fun j : ℤ => a (n - j) * b j) (fourierCoeff (⇑(Ff * Fg)) n) := by
    have hcomp : ((fun p : ℤ × ℤ =>
        a p.1 * b p.2 * (if n = p.1 + p.2 then (1:ℂ) else 0))
          ∘ (fun j : ℤ => ((n - j, j) : ℤ × ℤ))) = fun j => a (n - j) * b j := by
      funext j; simp
    rw [← hcomp]; exact (hg2.hasSum_iff hzero).mpr Hn
  rw [hcoe, Hconv.tsum_eq]

/-! ## 3. Axiom audit. -/

section AxiomAudit
#print axioms reflCircle_mul_fourier_summable
end AxiomAudit

end ShenWork.Paper2.IntervalReflCircleWiener
