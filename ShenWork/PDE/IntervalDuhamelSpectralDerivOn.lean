import ShenWork.PDE.IntervalDuhamelSourceTimeC1On
/-! # Windowed Duhamel spectral coefficient derivative
`HasDerivAt` of `duhamelSpectralCoeff` at interior points of `(0,T)` from
`DuhamelSourceTimeC1On a 0 T`, windowed eigenvalue IBP, and continuity. -/
open MeasureTheory Set
open scoped Topology
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalDuhamelSourceTimeC1On
  (DuhamelSourceTimeC1On duhamelCoeff_eigenvalue_mul_on)

namespace ShenWork.IntervalDuhamelSpectralDerivOn

private theorem continuousOn_coeff_of_on {a : ℝ → ℕ → ℝ} {T : ℝ}
    (src : DuhamelSourceTimeC1On a 0 T) (n : ℕ) :
    ContinuousOn (fun s => a s n) (Icc 0 T) :=
  fun s hs => (src.hderiv s hs n).continuousWithinAt

/-- Windowed spectral Duhamel ODE from `DuhamelSourceTimeC1On a 0 T`. -/
theorem duhamelSpectralCoeff_hasDerivAt_of_on {a : ℝ → ℕ → ℝ} {T : ℝ}
    (src : DuhamelSourceTimeC1On a 0 T)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (n : ℕ) :
    HasDerivAt (fun r => duhamelSpectralCoeff a r n)
      (a t n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a t n) t := by
  set lam := unitIntervalCosineEigenvalue n
  have hcontOn := continuousOn_coeff_of_on src n
  have hcont_at : ContinuousAt (fun s => a s n) t :=
    hcontOn.continuousAt (Icc_mem_nhds ht0 htT)
  set G : ℝ → ℝ := fun r => ∫ s in (0 : ℝ)..r, Real.exp (s * lam) * a s n
  have hfactor : ∀ r, duhamelSpectralCoeff a r n = Real.exp (-r * lam) * G r := by
    intro r; show (∫ s in (0:ℝ)..r, _) = _
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun s _ => by
      rw [show -(r - s) * lam = -r * lam + s * lam from by ring,
        Real.exp_add, mul_assoc])
  have hd_exp : HasDerivAt (fun r => Real.exp (-r * lam))
      (-lam * Real.exp (-t * lam)) t := by
    have h1 : HasDerivAt (fun r : ℝ => -r * lam) (-1 * lam) t :=
      (hasDerivAt_id t).neg.mul_const lam
    have h2 := h1.exp
    simp only [neg_mul, one_mul] at h2 ⊢; convert h2 using 1; ring
  set integrand := fun s => Real.exp (s * lam) * a s n
  have hI_contOn : ContinuousOn integrand (Icc 0 T) :=
    ((Real.continuous_exp.comp (continuous_id.mul continuous_const)).continuousOn).mul hcontOn
  have hG_ii : IntervalIntegrable integrand volume 0 t :=
    (hI_contOn.mono (Icc_subset_Icc le_rfl htT.le)).intervalIntegrable_of_Icc ht0.le
  have hG_ca : ContinuousAt integrand t :=
    hI_contOn.continuousAt (Icc_mem_nhds ht0 htT)
  have hG_smf : StronglyMeasurableAtFilter integrand (𝓝 t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hI_contOn.mono Ioo_subset_Icc_self) t ⟨ht0, htT⟩
  have hd_G : HasDerivAt G (Real.exp (t * lam) * a t n) t :=
    intervalIntegral.integral_hasDerivAt_right hG_ii hG_smf hG_ca
  have hexp_cancel : Real.exp (-t * lam) * Real.exp (t * lam) = 1 := by
    rw [← Real.exp_add, show -t * lam + t * lam = 0 from by ring, Real.exp_zero]
  have hderiv_val : -lam * Real.exp (-t * lam) * G t +
      Real.exp (-t * lam) * (Real.exp (t * lam) * a t n) =
      a t n - lam * (Real.exp (-t * lam) * G t) := by
    rw [← mul_assoc (Real.exp _), hexp_cancel, one_mul]; ring
  rw [show (fun r => duhamelSpectralCoeff a r n) =
      (fun r => Real.exp (-r * lam) * G r) from funext hfactor, hfactor t]
  exact (hd_exp.mul hd_G).congr_deriv hderiv_val

/-- Windowed continuity of the Duhamel spectral coefficient on `(0,T)`. -/
theorem duhamelSpectralCoeff_continuous_of_on {a : ℝ → ℕ → ℝ} {T : ℝ}
    (src : DuhamelSourceTimeC1On a 0 T) (n : ℕ) :
    ContinuousOn (fun r => duhamelSpectralCoeff a r n) (Ioo 0 T) :=
  fun _ ht =>
    (duhamelSpectralCoeff_hasDerivAt_of_on src ht.1 ht.2 n).continuousAt.continuousWithinAt

/-- Windowed eigenvalue IBP: `λₙ |bₙ(t)| = |aₙ(t) − e^{−tλₙ}aₙ(0) − ∫₀ᵗ …|`. -/
theorem duhamelCoeff_eigenvalue_mul_of_on {a : ℝ → ℕ → ℝ} {T : ℝ}
    (src : DuhamelSourceTimeC1On a 0 T)
    {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T) (n : ℕ) :
    unitIntervalCosineEigenvalue n *
      |∫ s in (0:ℝ)..t,
        Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n|
    = |a t n - Real.exp (-(t - 0) * unitIntervalCosineEigenvalue n) * a 0 n
        - ∫ s in (0:ℝ)..t, Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) *
            src.adot s n| := by
  have hkey := duhamelCoeff_eigenvalue_mul_on (lo := 0) (hi := T) (t := t)
    (lam := unitIntervalCosineEigenvalue n) (a := fun s => a s n)
    (adot := fun s => src.adot s n) (by linarith) ht0.le htT
    (fun s hs => src.hderiv s ⟨hs.1, le_trans hs.2 htT⟩ n) (src.hadotcont n)
  simp only [] at hkey
  have hlam_nn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  have : unitIntervalCosineEigenvalue n *
      |∫ s in (0:ℝ)..t,
        Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n|
    = |unitIntervalCosineEigenvalue n *
        ∫ s in (0:ℝ)..t,
          Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n| := by
    rw [abs_mul, abs_of_nonneg hlam_nn]
  rw [this, hkey]

end ShenWork.IntervalDuhamelSpectralDerivOn
