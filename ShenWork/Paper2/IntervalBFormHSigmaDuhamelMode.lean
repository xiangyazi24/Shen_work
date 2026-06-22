import ShenWork.Paper2.IntervalBFormHSigmaLinftyMultiplier
import ShenWork.Paper2.IntervalBFormHSigmaSmoothing
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
  Brick 3 (operator-feeding per-mode core) — the per-mode `L∞_t → H^σ_x`
  divergence-Duhamel smoothing bound, fully assembled from the landed scalar
  cores (`linfty_multiplier_bound`, `integral_terminal_singularity`).

  The single mode `k` carries the scalar Duhamel coefficient

      B_k(s) = ∫₀ˢ √λ_k · exp(−d λ_k (s−τ)) · F_k(τ) dτ,

  the spectral coefficient of `(−Δ)^{1/2} e^{(s−τ)Δ}` applied to the source.
  This file proves, for `0 ≤ σ < 1`, `d > 0`, `0 < s ≤ 1`, and a pointwise
  source bound `|F_k(τ)| ≤ M_k` on `[0,s]`:

      (1+λ_k)^{σ/2} · |B_k(s)| ≤ C_σ · M_k · s^{(1−σ)/2} / ((1−σ)/2).

  This is the per-mode `H^σ` bound; the `L∞_t L²_x → H^σ_x` operator estimate is
  the ℓ²-in-`k` assembly of this bound (Minkowski integral-triangle in `ℓ²`).
  Every step here is scalar interval-integral calculus over `[0,s]`, so the brick
  is axiom-clean.  The boundary point `τ = s` (where `s−τ = 0` and the multiplier
  bound is unavailable) is excluded via `integral_mono_on_of_le_Ioo` (the bound is
  only needed on the open interval; the endpoint is null).
-/

noncomputable section

namespace ShenWork.Paper2.BFormHSigmaDuhamelMode

open ShenWork.Paper2.BFormHSigmaLinftyMultiplier
open ShenWork.Paper2.BFormHSigmaSmoothing
open ShenWork.Paper2.HSigmaScale
open Real intervalIntegral MeasureTheory

/-- The scalar divergence-Duhamel coefficient for a single Neumann cosine mode
of eigenvalue `lam`:  `∫₀ˢ √lam · exp(−d lam (s−τ)) · F τ dτ`. -/
def duhamelModeCoeff (d lam : ℝ) (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ τ in (0:ℝ)..s, lam ^ (1/2 : ℝ) * Real.exp (-(d * lam * (s - τ))) * F τ

/-- The reflected terminal integral `∫₀ˢ (s−τ)^{−p} dτ = s^{1−p}/(1−p)` for
`0 ≤ p < 1`, `0 < s`.  Obtained from `integral_terminal_singularity` by the
change of variables `r = s − τ` (interval-integral reflection `comp_sub_left`). -/
theorem integral_reflected_singularity {p s : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hs : 0 < s) :
    (∫ τ in (0:ℝ)..s, (s - τ) ^ (-p)) = s ^ (1 - p) / (1 - p) := by
  have hcomp : (∫ τ in (0:ℝ)..s, (s - τ) ^ (-p))
      = ∫ r in (s - s)..(s - 0), r ^ (-p) := by
    rw [← intervalIntegral.integral_comp_sub_left (fun r => r ^ (-p)) s]
  rw [hcomp]
  simp only [sub_self, sub_zero]
  exact integral_terminal_singularity hp0 hp1 hs

/-- Interval integrability of the reflected singular integrand `(s−τ)^{−p}` on
`[0,s]` for `0 ≤ p < 1`, `0 < s` (reflection of `r^{−p}`, integrable since the
integral converges). -/
theorem intervalIntegrable_reflected_singularity {p s : ℝ} (hp1 : p < 1)
    (_hs : 0 < s) :
    IntervalIntegrable (fun τ : ℝ => (s - τ) ^ (-p)) volume 0 s := by
  have hbase : IntervalIntegrable (fun r : ℝ => r ^ (-p)) volume 0 s := by
    apply intervalIntegral.intervalIntegrable_rpow'
    linarith
  have := (hbase.comp_sub_left s)
  -- this : IntervalIntegrable (fun τ => (s - τ)^(-p)) volume (s-0) (s-s)
  simpa using this.symm

/-- **Per-mode `L∞_t → H^σ_x` divergence-Duhamel smoothing bound.**

For `0 ≤ σ < 1`, `d > 0`, `0 < s ≤ 1`, eigenvalue `lam ≥ 0`, a continuous source
`F` with `∀ τ ∈ [0,s], |F τ| ≤ M` (`0 ≤ M`), and the landed multiplier constant
`C_σ` of `linfty_multiplier_bound`:

    (1 + lam)^{σ/2} · |duhamelModeCoeff d lam F s|
        ≤ C_σ · M · s^{(1−σ)/2} / ((1−σ)/2).

The whole argument is scalar interval-integral calculus over `[0,s]`. -/
theorem hSigma_mode_duhamel_bound {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    {d : ℝ} (hd : 0 < d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {lam : ℝ} (hlam : 0 ≤ lam) {F : ℝ → ℝ} (hFcont : Continuous F)
    {M : ℝ} (_hM0 : 0 ≤ M) (hFbd : ∀ τ ∈ Set.Icc (0:ℝ) s, |F τ| ≤ M) :
    (1 + lam) ^ (σ/2) * |duhamelModeCoeff d lam F s| ≤
      (Classical.choose (linfty_multiplier_bound hσ0 hσ1 d hd)) * M
        * (s ^ ((1 - σ)/2) / ((1 - σ)/2)) := by
  obtain ⟨hCpos, hC⟩ := Classical.choose_spec (linfty_multiplier_bound hσ0 hσ1 d hd)
  set C := Classical.choose (linfty_multiplier_bound hσ0 hσ1 d hd) with hCdef
  have hw : (0:ℝ) ≤ (1 + lam) ^ (σ/2) := Real.rpow_nonneg (by linarith) _
  have hp0 : (0:ℝ) ≤ (σ + 1)/2 := by linarith
  have hp1 : (σ + 1)/2 < 1 := by linarith
  -- LHS integrand and the dominating integrand
  set g : ℝ → ℝ := fun τ =>
    (1 + lam) ^ (σ/2) * |lam ^ (1/2 : ℝ) * Real.exp (-(d * lam * (s - τ))) * F τ|
    with hgdef
  set h : ℝ → ℝ := fun τ => C * M * (s - τ) ^ (-((σ + 1)/2)) with hhdef
  -- Step 1: weight `(1+lam)^{σ/2}` into the abs-integral-triangle bound.
  have hstep1 : (1 + lam) ^ (σ/2) * |duhamelModeCoeff d lam F s|
      ≤ ∫ τ in (0:ℝ)..s, g τ := by
    have hAbs : |duhamelModeCoeff d lam F s|
        ≤ ∫ τ in (0:ℝ)..s,
            |lam ^ (1/2 : ℝ) * Real.exp (-(d * lam * (s - τ))) * F τ| := by
      unfold duhamelModeCoeff
      exact intervalIntegral.abs_integral_le_integral_abs hs.le
    calc (1 + lam) ^ (σ/2) * |duhamelModeCoeff d lam F s|
        ≤ (1 + lam) ^ (σ/2) * ∫ τ in (0:ℝ)..s,
            |lam ^ (1/2 : ℝ) * Real.exp (-(d * lam * (s - τ))) * F τ| :=
          mul_le_mul_of_nonneg_left hAbs hw
      _ = ∫ τ in (0:ℝ)..s, g τ := by
          rw [hgdef]; rw [intervalIntegral.integral_const_mul]
  -- Step 2: pointwise domination `g ≤ h` on the OPEN interval (0,s).
  have hdom : ∀ τ ∈ Set.Ioo (0:ℝ) s, g τ ≤ h τ := by
    intro τ hτ
    obtain ⟨hτ0, hτs⟩ := hτ
    have hr : (0:ℝ) < s - τ := by linarith
    have hr1 : s - τ ≤ 1 := by linarith
    have hexp_nonneg : (0:ℝ) ≤ Real.exp (-(d * lam * (s - τ))) := (Real.exp_pos _).le
    have hsqrt_nonneg : (0:ℝ) ≤ lam ^ (1/2 : ℝ) := Real.rpow_nonneg hlam _
    have habs : |lam ^ (1/2 : ℝ) * Real.exp (-(d * lam * (s - τ))) * F τ|
        = lam ^ (1/2 : ℝ) * Real.exp (-(d * lam * (s - τ))) * |F τ| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hsqrt_nonneg, abs_of_nonneg hexp_nonneg]
    have hFτ : |F τ| ≤ M := hFbd τ ⟨hτ0.le, hτs.le⟩
    have hmul := hC (s - τ) lam hr hr1 hlam
    have harg : d * (s - τ) * lam = d * lam * (s - τ) := by ring
    rw [harg] at hmul
    -- hmul : (1+lam)^{σ/2} * lam^{1/2} * exp(-(d*lam*(s−τ))) ≤ C*(s−τ)^{-(σ+1)/2}
    show (1 + lam) ^ (σ/2)
        * |lam ^ (1/2 : ℝ) * Real.exp (-(d * lam * (s - τ))) * F τ|
        ≤ C * M * (s - τ) ^ (-((σ + 1)/2))
    rw [habs]
    have hLHS_eq : (1 + lam) ^ (σ/2)
          * (lam ^ (1/2 : ℝ) * Real.exp (-(d * lam * (s - τ))) * |F τ|)
        = ((1 + lam) ^ (σ/2) * lam ^ (1/2 : ℝ)
              * Real.exp (-(d * lam * (s - τ)))) * |F τ| := by ring
    rw [hLHS_eq]
    have hker_nonneg : (0:ℝ) ≤ (1 + lam) ^ (σ/2) * lam ^ (1/2 : ℝ)
        * Real.exp (-(d * lam * (s - τ))) := by positivity
    calc ((1 + lam) ^ (σ/2) * lam ^ (1/2 : ℝ)
            * Real.exp (-(d * lam * (s - τ)))) * |F τ|
        ≤ (C * (s - τ) ^ (-((σ + 1)/2))) * M :=
          mul_le_mul hmul hFτ (abs_nonneg _) (le_trans hker_nonneg hmul)
      _ = C * M * (s - τ) ^ (-((σ + 1)/2)) := by ring
  -- Step 3: integrability of g and h.
  have hg_int : IntervalIntegrable g volume 0 s := by
    rw [hgdef]
    apply Continuous.intervalIntegrable
    have : Continuous (fun τ : ℝ =>
        lam ^ (1/2 : ℝ) * Real.exp (-(d * lam * (s - τ))) * F τ) := by
      fun_prop
    fun_prop
  have hh_int : IntervalIntegrable h volume 0 s := by
    rw [hhdef]
    exact ((intervalIntegrable_reflected_singularity hp1 hs).const_mul (C * M))
  -- Step 4: monotonicity (over open interval, endpoint null).
  have hmono : (∫ τ in (0:ℝ)..s, g τ) ≤ ∫ τ in (0:ℝ)..s, h τ :=
    intervalIntegral.integral_mono_on_of_le_Ioo hs.le hg_int hh_int hdom
  -- Step 5: evaluate the dominating integral.
  have heval : (∫ τ in (0:ℝ)..s, h τ)
      = C * M * (s ^ ((1 - σ)/2) / ((1 - σ)/2)) := by
    rw [hhdef]
    rw [intervalIntegral.integral_const_mul]
    rw [integral_reflected_singularity hp0 hp1 hs]
    have hrate : (1 : ℝ) - (σ + 1)/2 = (1 - σ)/2 := by ring
    rw [hrate]
  calc (1 + lam) ^ (σ/2) * |duhamelModeCoeff d lam F s|
      ≤ ∫ τ in (0:ℝ)..s, g τ := hstep1
    _ ≤ ∫ τ in (0:ℝ)..s, h τ := hmono
    _ = C * M * (s ^ ((1 - σ)/2) / ((1 - σ)/2)) := heval

#print axioms hSigma_mode_duhamel_bound

end ShenWork.Paper2.BFormHSigmaDuhamelMode
