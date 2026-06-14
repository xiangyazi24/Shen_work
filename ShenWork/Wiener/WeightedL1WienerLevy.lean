import ShenWork.Wiener.WeightedL1Decisive

/-!
# Wiener brick 5 — Gamma/Laplace Wiener–Lévy (WL1/WL2)

`(eval f)^{−s}` and `(eval f)^γ` realized as eval of genuine `A¹` elements via
`Fneg s = (1/Γ s) • ∫_{Ioi 0} t^{s−1} • e^{−tf} dt`, consuming `decisive_exp_bound`.
-/

open scoped BigOperators
open MeasureTheory Set Real

noncomputable section

namespace ShenWork.Wiener

namespace WA

/-! ### Part 0 — scalar integrability of `t^c·e^{−δt}` on `Ioi 0`. -/

/-- `t ↦ t^c · e^{−(δ t)}` is integrable on `Ioi 0` for `−1 < c`, `0 < δ`. -/
theorem integrableOn_rpow_mul_exp (c δ : ℝ) (hc : -1 < c) (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ => t ^ c * Real.exp (-(δ * t))) (Ioi 0) := by
  have hconv : IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ c) (Ioi 0) := by
    have := Real.GammaIntegral_convergent (s := c + 1) (by linarith)
    simpa using this
  have hscale : IntegrableOn (fun x : ℝ => Real.exp (-(δ * x)) * (δ * x) ^ c) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => Real.exp (-u) * u ^ c) 0 hδ).mpr (by simpa using hconv)
    simpa using h
  have hg : IntegrableOn (fun t : ℝ => (δ ^ c) • (t ^ c * Real.exp (-(δ * t)))) (Ioi 0) := by
    apply hscale.congr_fun _ measurableSet_Ioi
    intro t ht
    have htpos : 0 < t := ht
    simp only [smul_eq_mul]
    rw [Real.mul_rpow hδ.le htpos.le]; ring
  exact (integrable_smul_iff (by positivity : (δ ^ c) ≠ 0) _).mp hg

/-! ### Part 1 — the eval CLM and the `WA 1`-valued integrand. -/

/-- Point evaluation `WA 1 →L[ℂ] ℂ` at `x`, namely `evalAt x ∘ incl10`. -/
def evalAt1CLM (x : Circ) : WA 1 →L[ℂ] ℂ :=
  ((ContinuousMap.evalCLM ℂ x).comp evalLin).comp incl10.toContinuousLinearMap

@[simp] theorem evalAt1CLM_apply (x : Circ) (a : WA 1) :
    evalAt1CLM x a = evalAt x (incl10 a) := rfl

/-- The `WA 1`-valued integrand `t ↦ t^{s−1} • e^{−tf}` (ℂ-scalar). -/
def gammaIntegrand (f : WA 1) (s : ℝ) (t : ℝ) : WA 1 :=
  ((t ^ (s - 1) : ℝ) : ℂ) • NormedSpace.exp (((-t : ℝ) : ℂ) • f)

/-- Continuity of `t ↦ e^{−tf}` (in `WA 1`). -/
theorem continuous_expNeg (f : WA 1) :
    Continuous (fun t : ℝ => NormedSpace.exp (((-t : ℝ) : ℂ) • f)) := by
  have hc : Continuous (fun t : ℝ => ((-t : ℝ) : ℂ) • f) :=
    (Complex.continuous_ofReal.comp continuous_neg).smul continuous_const
  exact NormedSpace.exp_continuous.comp hc

/-- The integrand is continuous on `Ioi 0` (rpow is continuous away from 0). -/
theorem continuousOn_gammaIntegrand (f : WA 1) (s : ℝ) :
    ContinuousOn (gammaIntegrand f s) (Ioi 0) := by
  refine ContinuousOn.smul ?_ (continuous_expNeg f).continuousOn
  refine Complex.continuous_ofReal.comp_continuousOn ?_
  refine ContinuousOn.rpow_const ?_ (fun t ht => Or.inl (ne_of_gt ht))
  exact continuousOn_id

/-- AE-strong-measurability of the integrand on `Ioi 0`. -/
theorem aesm_gammaIntegrand (f : WA 1) (s : ℝ) :
    AEStronglyMeasurable (gammaIntegrand f s) (volume.restrict (Ioi 0)) :=
  (continuousOn_gammaIntegrand f s).aestronglyMeasurable measurableSet_Ioi

/-! ### Part 2 — Bochner integrability via the real majorant. -/

/-- The majorant `t^{s−1}·C·(1+t‖Df‖)²·e^{−δt}` is integrable on `Ioi 0`. -/
theorem integrable_majorant (f : WA 1) (s δ : ℝ) (hs : 0 < s) (hδpos : 0 < δ) :
    IntegrableOn (fun t : ℝ => t ^ (s - 1) *
      ((8 * (1 + 1 / Real.pi) ^ 2) * (1 + t * ‖D f‖) ^ 2 * Real.exp (-δ * t))) (Ioi 0) := by
  set C : ℝ := 8 * (1 + 1 / Real.pi) ^ 2 with hC
  set M : ℝ := ‖D f‖ with hM
  have e0 := integrableOn_rpow_mul_exp (s - 1) δ (by linarith) hδpos
  have e1 := integrableOn_rpow_mul_exp ((s - 1) + 1) δ (by linarith) hδpos
  have e2 := integrableOn_rpow_mul_exp ((s - 1) + 2) δ (by linarith) hδpos
  have hcomb : IntegrableOn
      (fun t : ℝ => C * (t ^ (s - 1) * Real.exp (-(δ * t)))
        + C * (2 * M) * (t ^ ((s - 1) + 1) * Real.exp (-(δ * t)))
        + C * (M ^ 2) * (t ^ ((s - 1) + 2) * Real.exp (-(δ * t)))) (Ioi 0) :=
    ((e0.const_mul C).add (e1.const_mul (C * (2 * M)))).add (e2.const_mul (C * M ^ 2))
  apply hcomb.congr_fun _ measurableSet_Ioi
  intro t ht
  have htpos : 0 < t := ht
  simp only []
  have hr1 : t ^ ((s - 1) + 1) = t ^ (s - 1) * t := by
    rw [Real.rpow_add htpos, Real.rpow_one]
  have hr2 : t ^ ((s - 1) + 2) = t ^ (s - 1) * t ^ 2 := by
    rw [Real.rpow_add htpos]; norm_num
  have hexp : Real.exp (-(δ * t)) = Real.exp (-δ * t) := by rw [neg_mul]
  rw [hr1, hr2, hexp]
  ring

/-- **Bochner integrability** of the `WA 1`-valued integrand `t^{s−1}•e^{−tf}`
on `Ioi 0`, under the spectral floor `δ ≤ Re(eval f)` and `δ>0`, `s>0`. -/
theorem integrable_gammaIntegrand (f : WA 1) (s δ : ℝ) (hs : 0 < s) (hδpos : 0 < δ)
    (hδ : ∀ x : Circ, δ ≤ (evalAt x (incl10 f)).re) :
    IntegrableOn (gammaIntegrand f s) (Ioi 0) := by
  refine Integrable.mono' (integrable_majorant f s δ hs hδpos)
    (aesm_gammaIntegrand f s) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with t ht
  have htpos : 0 < t := ht
  have htnn : (0 : ℝ) ≤ t ^ (s - 1) := Real.rpow_nonneg htpos.le _
  have hdec := decisive_exp_bound f t δ htpos.le hδ
  rw [gammaIntegrand, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htnn]
  have hCnn : (0 : ℝ) ≤ (8 * (1 + 1 / Real.pi) ^ 2) * (1 + t * ‖D f‖) ^ 2 *
      Real.exp (-δ * t) := by positivity
  calc t ^ (s - 1) * ‖NormedSpace.exp (((-t : ℝ) : ℂ) • f)‖
      ≤ t ^ (s - 1) * ((8 * (1 + 1 / Real.pi) ^ 2) * (1 + t * ‖D f‖) ^ 2 *
        Real.exp (-δ * t)) := by
        exact mul_le_mul_of_nonneg_left hdec htnn

/-! ### Part 3 — the genuine `A¹` element `Fneg s` and eval-commute. -/

/-- `Fneg f s = (1/Γ s) • ∫_{Ioi 0} t^{s−1}•e^{−tf} dt ∈ WA 1` (ℂ-scalar). -/
def Fneg (f : WA 1) (s : ℝ) : WA 1 :=
  ((1 / Real.Gamma s : ℝ) : ℂ) • ∫ t in Ioi 0, gammaIntegrand f s t

/-- **Eval commutes through the Bochner integral.**  For each `x`,
`evalAt x (incl10 (Fneg f s)) = (1/Γ s)·∫ t^{s−1}·e^{−t·(evalAt x (incl10 f))}`. -/
theorem evalAt_Fneg (f : WA 1) (s δ : ℝ) (hs : 0 < s) (hδpos : 0 < δ)
    (hδ : ∀ x : Circ, δ ≤ (evalAt x (incl10 f)).re) (x : Circ) :
    evalAt x (incl10 (Fneg f s))
      = ((1 / Real.Gamma s : ℝ) : ℂ) * ∫ t in Ioi 0,
        ((t ^ (s - 1) : ℝ) : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * evalAt x (incl10 f)) := by
  have hint := integrable_gammaIntegrand f s δ hs hδpos hδ
  have hcomm : evalAt1CLM x (∫ t in Ioi 0, gammaIntegrand f s t)
      = ∫ t in Ioi 0, evalAt1CLM x (gammaIntegrand f s t) :=
    (ContinuousLinearMap.integral_comp_comm _ hint).symm
  rw [show evalAt x (incl10 (Fneg f s)) = evalAt1CLM x (Fneg f s) from rfl, Fneg,
    map_smul, hcomm, smul_eq_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [gammaIntegrand, map_smul, evalAt1CLM_apply, smul_eq_mul, incl_exp, evalAt_exp]
  congr 2
  rw [map_smul, evalAt_smul]

/-! ### Part 4 — the scalar Gamma identity and `negPow_eval` (WL for `r^{−s}`). -/

/-- **`negPow_eval`.** Under the floor `δ ≤ Re(eval f)`, `δ>0`, and `f` real
(`Im(eval f) = 0`), `Fneg f s` is a genuine `A¹` element whose evaluation is
`(Re(eval f))^{−s}` (real `rpow`, coerced to `ℂ`). -/
theorem negPow_eval {f : WA 1} {s δ : ℝ} (hs : 0 < s) (hδpos : 0 < δ)
    (hfloor : ∀ x : Circ, δ ≤ (evalAt x (incl10 f)).re)
    (hreal : ∀ x : Circ, (evalAt x (incl10 f)).im = 0) (x : Circ) :
    evalAt x (incl10 (Fneg f s))
      = (((evalAt x (incl10 f)).re ^ (-s) : ℝ) : ℂ) := by
  set r : ℝ := (evalAt x (incl10 f)).re with hr
  have hrpos : 0 < r := lt_of_lt_of_le hδpos (hfloor x)
  have hcr : evalAt x (incl10 f) = (r : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im, hreal x]
  rw [evalAt_Fneg f s δ hs hδpos hfloor x, hcr]
  -- rewrite the complex integrand as the coercion of a real integrand
  have hre : ∀ t : ℝ, ((t ^ (s - 1) : ℝ) : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * (r : ℂ))
      = ((t ^ (s - 1) * Real.exp (-(r * t)) : ℝ) : ℂ) := by
    intro t
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    congr 2
    push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hre t),
    integral_complex_ofReal, integral_rpow_mul_exp_neg_mul_Ioi hs hrpos]
  have hΓ : Real.Gamma s ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hs)
  have hval : (1 / Real.Gamma s) * ((1 / r) ^ s * Real.Gamma s) = r ^ (-s) := by
    have h1 : (1 / r) ^ s = r ^ (-s) := by
      rw [Real.rpow_neg hrpos.le, one_div, Real.inv_rpow hrpos.le]
    rw [h1]; field_simp
  rw [← Complex.ofReal_mul, hval]

/-! ### Part 5 — `realPow_eval` (WL1/WL2 for arbitrary real powers `r^γ`). -/

/-- **`realPow_eval`.** Under the floor and `f` real, `(eval f)^γ = (Re(eval f))^γ`
is the evaluation of a genuine `A¹` element `F = f^m · Fneg f (m−γ)` (with `m>γ`).
This realizes WL1 (`u^γ`) and WL2 (`(1+v)^{−β}`). -/
theorem realPow_eval {f : WA 1} {γ δ : ℝ} (hδpos : 0 < δ)
    (hfloor : ∀ x : Circ, δ ≤ (evalAt x (incl10 f)).re)
    (hreal : ∀ x : Circ, (evalAt x (incl10 f)).im = 0) :
    ∃ F : WA 1, ∀ x : Circ,
      evalAt x (incl10 F) = (((evalAt x (incl10 f)).re ^ γ : ℝ) : ℂ) := by
  obtain ⟨m, hm⟩ := exists_nat_gt γ
  have hs : 0 < (m : ℝ) - γ := by linarith
  refine ⟨f ^ m * Fneg f ((m : ℝ) - γ), fun x => ?_⟩
  set r : ℝ := (evalAt x (incl10 f)).re with hr
  have hrpos : 0 < r := lt_of_lt_of_le hδpos (hfloor x)
  have hcr : evalAt x (incl10 f) = (r : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im, hreal x]
  have hpow : evalAt x (incl10 (f ^ m)) = (r : ℂ) ^ m := by
    rw [map_pow, map_pow, hcr]
  have hneg := negPow_eval hs hδpos hfloor hreal x
  rw [map_mul, map_mul, hpow, hneg]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.rpow_natCast r m, ← Real.rpow_add hrpos]
  congr 1; ring

end WA

end ShenWork.Wiener
