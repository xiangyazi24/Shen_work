import ShenWork.PDE.IntervalSourceCoefficientTimeC1

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.IntervalDuhamelCoeffFTC

open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)

/-- Derivative of `t ↦ exp (-(t - c) * lam)`. -/
theorem hasDerivAt_exp_neg_lambda_mul (lam c t : ℝ) :
    HasDerivAt (fun r : ℝ => Real.exp (-(r - c) * lam))
      (-lam * Real.exp (-(t - c) * lam)) t := by
  have harg : HasDerivAt (fun r : ℝ => -(r - c) * lam) (-lam) t := by
    convert ((hasDerivAt_id t).sub (hasDerivAt_const t c)).neg.mul_const lam using 1
    ring
  convert harg.exp using 1
  ring_nf

/-- Trivial restart-form expansion of the existing relative-time definition. -/
theorem localRestartCoeff_eq_restart_form
    (a₀ : ℕ → ℝ) (a : ℝ → ℕ → ℝ) (τ : ℝ) (k : ℕ) :
    localRestartCoeff a₀ a τ k =
      Real.exp (-τ * unitIntervalCosineEigenvalue k) * a₀ k +
        ∫ s in (0 : ℝ)..τ,
          Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) * a s k := by
  rfl

/-- Duhamel coefficient ODE from continuity of one source coefficient on a
time window containing the differentiation point. -/
theorem hasDerivAt_duhamelIntegral_of_cont
    {a : ℝ → ℕ → ℝ} {T t : ℝ} (ht0 : 0 < t) (htT : t < T) (k : ℕ)
    (hcont : ContinuousOn (fun s => a s k) (Icc (0 : ℝ) T)) :
    HasDerivAt (fun r => duhamelSpectralCoeff a r k)
      (a t k - unitIntervalCosineEigenvalue k * duhamelSpectralCoeff a t k) t := by
  set lam := unitIntervalCosineEigenvalue k
  set G : ℝ → ℝ := fun r =>
    ∫ s in (0 : ℝ)..r, Real.exp (s * lam) * a s k
  have hfactor : ∀ r, duhamelSpectralCoeff a r k = Real.exp (-r * lam) * G r := by
    intro r
    show (∫ s in (0 : ℝ)..r, _) = _
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun s _ => by
      rw [show -(r - s) * lam = -r * lam + s * lam by ring,
        Real.exp_add, mul_assoc])
  have hd_exp : HasDerivAt (fun r : ℝ => Real.exp (-r * lam))
      (-lam * Real.exp (-t * lam)) t := by
    simpa using hasDerivAt_exp_neg_lambda_mul lam 0 t
  set integrand : ℝ → ℝ := fun s => Real.exp (s * lam) * a s k
  have hI_contOn : ContinuousOn integrand (Icc (0 : ℝ) T) :=
    ((Real.continuous_exp.comp
      (continuous_id.mul continuous_const)).continuousOn).mul hcont
  have hI_int : IntervalIntegrable integrand volume 0 t :=
    (hI_contOn.mono (Icc_subset_Icc le_rfl htT.le)).intervalIntegrable_of_Icc ht0.le
  have hI_ca : ContinuousAt integrand t :=
    hI_contOn.continuousAt (Icc_mem_nhds ht0 htT)
  have hI_smf : StronglyMeasurableAtFilter integrand (𝓝 t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hI_contOn.mono Ioo_subset_Icc_self) t ⟨ht0, htT⟩
  have hd_G : HasDerivAt G (Real.exp (t * lam) * a t k) t :=
    intervalIntegral.integral_hasDerivAt_right hI_int hI_smf hI_ca
  have hexp_cancel : Real.exp (-t * lam) * Real.exp (t * lam) = 1 := by
    rw [← Real.exp_add, show -t * lam + t * lam = 0 by ring, Real.exp_zero]
  have hderiv_val :
      -lam * Real.exp (-t * lam) * G t +
        Real.exp (-t * lam) * (Real.exp (t * lam) * a t k) =
      a t k - lam * (Real.exp (-t * lam) * G t) := by
    rw [← mul_assoc (Real.exp _), hexp_cancel, one_mul]
    ring
  rw [show (fun r => duhamelSpectralCoeff a r k) =
      (fun r => Real.exp (-r * lam) * G r) from funext hfactor, hfactor t]
  exact (hd_exp.mul hd_G).congr_deriv hderiv_val

/-- Relative-time restart coefficient ODE from continuous source coefficients. -/
theorem localRestartCoeff_hasDerivAt_of_contSource_relative
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {T t : ℝ}
    (ht0 : 0 < t) (htT : t < T) (k : ℕ)
    (hcont : ContinuousOn (fun s => a s k) (Icc (0 : ℝ) T)) :
    HasDerivAt (fun τ => localRestartCoeff a₀ a τ k)
      (a t k - unitIntervalCosineEigenvalue k * localRestartCoeff a₀ a t k) t := by
  set lam := unitIntervalCosineEigenvalue k
  have hhom : HasDerivAt
      (fun r : ℝ => Real.exp (-r * lam) * a₀ k)
      (-(lam * Real.exp (-t * lam)) * a₀ k) t := by
    have hd : HasDerivAt (fun r : ℝ => Real.exp (-r * lam))
        (-lam * Real.exp (-t * lam)) t := by
      simpa using hasDerivAt_exp_neg_lambda_mul lam 0 t
    exact (hd.mul_const (a₀ k)).congr_deriv (by ring)
  have hduh : HasDerivAt (fun r => duhamelSpectralCoeff a r k)
      (a t k - lam * duhamelSpectralCoeff a t k) t :=
    hasDerivAt_duhamelIntegral_of_cont ht0 htT k hcont
  rw [show (fun τ => localRestartCoeff a₀ a τ k) =
      fun τ => Real.exp (-τ * lam) * a₀ k + duhamelSpectralCoeff a τ k
      from by ext τ; simp [localRestartCoeff, lam]]
  convert hhom.add hduh using 1
  simp [localRestartCoeff, lam]
  ring

/-- Absolute-time restart coefficient ODE.  The source in `localRestartCoeff` is
shifted by the restart time `c`, so the relative Duhamel integral is exactly the
variation-of-constants integral over absolute time. -/
theorem localRestartCoeff_hasDerivAt_of_contSource
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {c d t : ℝ}
    (hct : c < t) (htd : t < d) (k : ℕ)
    (hcont : ContinuousOn (fun s => a s k) (Icc c d)) :
    HasDerivAt
      (fun τ => localRestartCoeff a₀ (fun ρ n => a (c + ρ) n) (τ - c) k)
      (a t k - unitIntervalCosineEigenvalue k *
        localRestartCoeff a₀ (fun ρ n => a (c + ρ) n) (t - c) k) t := by
  have htdiff_pos : 0 < t - c := by linarith
  have htdiff_T : t - c < d - c := by linarith
  have hshift_cont :
      ContinuousOn (fun s : ℝ => a (c + s) k) (Icc (0 : ℝ) (d - c)) := by
    refine hcont.comp' ((continuous_const.add continuous_id).continuousOn) ?_
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hrel := localRestartCoeff_hasDerivAt_of_contSource_relative
    (a₀ := a₀) (a := fun ρ n => a (c + ρ) n) (T := d - c)
    htdiff_pos htdiff_T k hshift_cont
  have hshift_deriv0 := (hasDerivAt_id t).sub (hasDerivAt_const t c)
  have hshift_deriv : HasDerivAt (fun τ : ℝ => τ - c) (1 : ℝ) t := by
    convert hshift_deriv0 using 1
    norm_num
  have hcomp := hrel.comp t hshift_deriv
  simpa [one_mul, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hcomp

end ShenWork.IntervalDuhamelCoeffFTC
