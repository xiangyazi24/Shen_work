import ShenWork.Wiener.EWA.Decisive
import ShenWork.Wiener.WeightedL1WienerLevy

/-!
# EWA brick B3 — EWA Gamma/Laplace Wiener–Lévy (cron2 Brick 6)

The EWA¹ analogue of the committed `WA.realPow_eval`
(`ShenWork/Wiener/WeightedL1WienerLevy.lean`, the TEMPLATE), reran with
`EWA T 1` in place of `WA 1` and the space-time evaluation `evalST` in place of
`evalAt`.  The single genuinely-new input is the EWA decisive bound
`EWA_decisive_exp_bound` (B2) for the Bochner integrability; everything else is
the same structure pushed through the central trick `sliceWA_exp`.

`(eval f)^{−s}` and `(eval f)^γ` realized as `evalST` of genuine `EWA T 1`
elements via `FnegEWA f s = (1/Γ s) • ∫_{Ioi 0} t^{s−1} • e^{−tf} dt`,
consuming `EWA_decisive_exp_bound`.
-/

open scoped BigOperators
open MeasureTheory Set Real
open ShenWork.GWA ShenWork.Wiener

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Part 1 — the `evalST` CLM and the `EWA T 1`-valued integrand. -/

/-- The slice bridge as a CLM `EWA T 1 →L[ℂ] WA 1` (Lipschitz constant `1`,
from `norm_sliceWA_le`). -/
def sliceCLM (τ : TimeDom T) : EWA T 1 →L[ℂ] WA 1 :=
  (sliceWA τ).toLinearMap.mkContinuous 1 (fun a => by simpa using norm_sliceWA_le τ a)

@[simp] theorem sliceCLM_apply (τ : TimeDom T) (a : EWA T 1) :
    sliceCLM τ a = sliceWA τ a := rfl

/-- **Space-time point evaluation through the inclusion**, as a CLM
`EWA T 1 →L[ℂ] ℂ`: `a ↦ evalST τ x (incl a)`, factored as
`evalAt1CLM x ∘ sliceCLM τ` via `sliceWA_incl`. -/
def evalSTCLM (τ : TimeDom T) (x : WA.Circ) : EWA T 1 →L[ℂ] ℂ :=
  (WA.evalAt1CLM x).comp (sliceCLM τ)

@[simp] theorem evalSTCLM_apply (τ : TimeDom T) (x : WA.Circ) (a : EWA T 1) :
    evalSTCLM τ x a = evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) a) := by
  show WA.evalAt1CLM x (sliceWA τ a) = _
  rw [WA.evalAt1CLM_apply, evalST_apply, sliceWA_incl]

/-- The `EWA T 1`-valued integrand `t ↦ t^{s−1} • e^{−tf}` (ℂ-scalar). -/
def gammaIntegrandEWA (f : EWA T 1) (s : ℝ) (t : ℝ) : EWA T 1 :=
  ((t ^ (s - 1) : ℝ) : ℂ) • NormedSpace.exp (((-t : ℝ) : ℂ) • f)

/-- Continuity of `t ↦ e^{−tf}` (in `EWA T 1`). -/
theorem continuous_expNegEWA (f : EWA T 1) :
    Continuous (fun t : ℝ => NormedSpace.exp (((-t : ℝ) : ℂ) • f)) := by
  have hc : Continuous (fun t : ℝ => ((-t : ℝ) : ℂ) • f) :=
    (Complex.continuous_ofReal.comp continuous_neg).smul continuous_const
  exact NormedSpace.exp_continuous.comp hc

/-- The integrand is continuous on `Ioi 0` (rpow is continuous away from 0). -/
theorem continuousOn_gammaIntegrandEWA (f : EWA T 1) (s : ℝ) :
    ContinuousOn (gammaIntegrandEWA f s) (Ioi 0) := by
  refine ContinuousOn.smul ?_ (continuous_expNegEWA f).continuousOn
  refine Complex.continuous_ofReal.comp_continuousOn ?_
  refine ContinuousOn.rpow_const ?_ (fun t ht => Or.inl (ne_of_gt ht))
  exact continuousOn_id

/-- AE-strong-measurability of the integrand on `Ioi 0`. -/
theorem aesm_gammaIntegrandEWA (f : EWA T 1) (s : ℝ) :
    AEStronglyMeasurable (gammaIntegrandEWA f s) (volume.restrict (Ioi 0)) :=
  (continuousOn_gammaIntegrandEWA f s).aestronglyMeasurable measurableSet_Ioi

/-! ### Part 2 — Bochner integrability via the EWA real majorant (B2). -/

/-- The majorant `t^{s−1}·C·(1+t‖gDeriv f‖)²·e^{−δt}` is integrable on `Ioi 0`
(SAME finite combo of `Γ(s+j)/δ^{s+j}` as the committed WA WL). -/
theorem integrable_majorantEWA (f : EWA T 1) (s δ : ℝ) (hs : 0 < s) (hδpos : 0 < δ) :
    IntegrableOn (fun t : ℝ => t ^ (s - 1) *
      ((8 * (1 + 1 / Real.pi) ^ 2) * (1 + t * ‖GWA.gDeriv f‖) ^ 2 * Real.exp (-δ * t)))
      (Ioi 0) := by
  set C : ℝ := 8 * (1 + 1 / Real.pi) ^ 2 with hC
  set M : ℝ := ‖GWA.gDeriv f‖ with hM
  have e0 := WA.integrableOn_rpow_mul_exp (s - 1) δ (by linarith) hδpos
  have e1 := WA.integrableOn_rpow_mul_exp ((s - 1) + 1) δ (by linarith) hδpos
  have e2 := WA.integrableOn_rpow_mul_exp ((s - 1) + 2) δ (by linarith) hδpos
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

/-- **Bochner integrability** of the `EWA T 1`-valued integrand `t^{s−1}•e^{−tf}`
on `Ioi 0`, under the uniform spectral floor (`UniformFloor f δ`), `δ>0`, `s>0`.
The norm bound is the genuine B2 `EWA_decisive_exp_bound`. -/
theorem integrable_gammaIntegrandEWA (f : EWA T 1) (s δ : ℝ) (hs : 0 < s) (hδpos : 0 < δ)
    (hδ : UniformFloor f δ) :
    IntegrableOn (gammaIntegrandEWA f s) (Ioi 0) := by
  refine Integrable.mono' (integrable_majorantEWA f s δ hs hδpos)
    (aesm_gammaIntegrandEWA f s) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with t ht
  have htpos : 0 < t := ht
  have htnn : (0 : ℝ) ≤ t ^ (s - 1) := Real.rpow_nonneg htpos.le _
  have hdec := EWA_decisive_exp_bound f t δ htpos.le hδ
  rw [gammaIntegrandEWA, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htnn]
  calc t ^ (s - 1) * ‖NormedSpace.exp (((-t : ℝ) : ℂ) • f)‖
      ≤ t ^ (s - 1) * ((8 * (1 + 1 / Real.pi) ^ 2) * (1 + t * ‖GWA.gDeriv f‖) ^ 2 *
        Real.exp (-δ * t)) := mul_le_mul_of_nonneg_left hdec htnn

/-! ### Part 3 — the genuine `EWA T 1` element `FnegEWA s` and eval-commute. -/

/-- `FnegEWA f s = (1/Γ s) • ∫_{Ioi 0} t^{s−1}•e^{−tf} dt ∈ EWA T 1` (ℂ-scalar). -/
def FnegEWA (f : EWA T 1) (s : ℝ) : EWA T 1 :=
  ((1 / Real.Gamma s : ℝ) : ℂ) • ∫ t in Ioi 0, gammaIntegrandEWA f s t

/-- **`evalST` commutes through the Bochner integral.** For each `(τ, x)`,
`evalST τ x (incl (FnegEWA f s)) = (1/Γ s)·∫ t^{s−1}·e^{−t·(evalST τ x (incl f))}`. -/
theorem evalST_FnegEWA (f : EWA T 1) (s δ : ℝ) (hs : 0 < s) (hδpos : 0 < δ)
    (hδ : UniformFloor f δ) (τ : TimeDom T) (x : WA.Circ) :
    evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (FnegEWA f s))
      = ((1 / Real.Gamma s : ℝ) : ℂ) * ∫ t in Ioi 0,
        ((t ^ (s - 1) : ℝ) : ℂ) *
          Complex.exp (((-t : ℝ) : ℂ) *
            evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) f)) := by
  have hint := integrable_gammaIntegrandEWA f s δ hs hδpos hδ
  have hcomm : evalSTCLM τ x (∫ t in Ioi 0, gammaIntegrandEWA f s t)
      = ∫ t in Ioi 0, evalSTCLM τ x (gammaIntegrandEWA f s t) :=
    (ContinuousLinearMap.integral_comp_comm _ hint).symm
  rw [show evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (FnegEWA f s))
        = evalSTCLM τ x (FnegEWA f s) from (evalSTCLM_apply τ x _).symm, FnegEWA,
    map_smul, hcomm, smul_eq_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [gammaIntegrandEWA, map_smul, evalSTCLM_apply, smul_eq_mul]
  congr 1
  -- reduce `evalST τ x (incl (exp((-t)•f)))` via sliceWA_incl + sliceWA_exp + WA exp/smul.
  rw [evalST_apply, sliceWA_incl, sliceWA_exp, map_smul (sliceWA τ),
    WA.incl_exp, map_smul WA.incl10, WA.evalAt_exp, WA.evalAt_smul]
  congr 1
  rw [evalST_apply, sliceWA_incl]

/-! ### Part 4 — the scalar Gamma identity and `eval_FnegEWA`. -/

/-- **`eval_FnegEWA`.** Under the uniform floor `δ`, `δ>0`, and `f` real
(`Im(evalST τ x (incl f)) = 0`), `FnegEWA f s` is a genuine `EWA T 1` element
whose evaluation is `(Re(evalST τ x (incl f)))^{−s}`. -/
theorem eval_FnegEWA {f : EWA T 1} {s δ : ℝ} (hs : 0 < s) (hδpos : 0 < δ)
    (hfloor : UniformFloor f δ)
    (hreal : ∀ (τ : TimeDom T) (x : WA.Circ),
      (evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) f)).im = 0)
    (τ : TimeDom T) (x : WA.Circ) :
    evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (FnegEWA f s))
      = (((evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) f)).re ^ (-s) : ℝ) : ℂ) := by
  set r : ℝ := (evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) f)).re with hr
  have hrpos : 0 < r := lt_of_lt_of_le hδpos (hfloor τ x)
  have hcr : evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) f) = (r : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im, hreal τ x]
  rw [evalST_FnegEWA f s δ hs hδpos hfloor τ x, hcr]
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

/-! ### Part 5 — `realPow_eval_EWA` (WL1/WL2 for arbitrary real powers `r^γ`). -/

/-- **`realPow_eval_EWA`.** Under the uniform floor and `f` real,
`(evalST f)^γ = (Re(evalST f))^γ` is the evaluation of a genuine `EWA T 1`
element `F = f^m · FnegEWA f (m−γ)` (with `m>γ`).  Realizes WL1 (`u^γ`) and
WL2 (`(1+v)^{−β}`). -/
theorem realPow_eval_EWA {f : EWA T 1} {γ δ : ℝ} (hδpos : 0 < δ)
    (hfloor : UniformFloor f δ)
    (hreal : ∀ (τ : TimeDom T) (x : WA.Circ),
      (evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) f)).im = 0) :
    ∃ F : EWA T 1, ∀ (τ : TimeDom T) (x : WA.Circ),
      evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) F)
        = (((evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) f)).re ^ γ : ℝ) : ℂ) := by
  obtain ⟨m, hm⟩ := exists_nat_gt γ
  have hs : 0 < (m : ℝ) - γ := by linarith
  refine ⟨f ^ m * FnegEWA f ((m : ℝ) - γ), fun τ x => ?_⟩
  set r : ℝ := (evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) f)).re with hr
  have hrpos : 0 < r := lt_of_lt_of_le hδpos (hfloor τ x)
  have hcr : evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) f) = (r : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im, hreal τ x]
  have hincl_mul : ∀ a b : EWA T 1,
      GWA.incl (by omega : (0:ℕ) ≤ 1) (a * b)
        = GWA.incl (by omega : (0:ℕ) ≤ 1) a * GWA.incl (by omega : (0:ℕ) ≤ 1) b := by
    intro a b; rw [← GWA.gIncl_apply, map_mul, GWA.gIncl_apply, GWA.gIncl_apply]
  have hincl_pow : GWA.incl (by omega : (0:ℕ) ≤ 1) (f ^ m)
      = (GWA.incl (by omega : (0:ℕ) ≤ 1) f) ^ m := by
    rw [← GWA.gIncl_apply, map_pow, GWA.gIncl_apply]
  have hpow : evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (f ^ m)) = (r : ℂ) ^ m := by
    rw [hincl_pow, map_pow, hcr]
  have hneg := eval_FnegEWA hs hδpos hfloor hreal τ x
  rw [hincl_mul, map_mul, hpow, hneg]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.rpow_natCast r m, ← Real.rpow_add hrpos]
  congr 1; ring

end ShenWork.EWA

#print axioms ShenWork.EWA.eval_FnegEWA
#print axioms ShenWork.EWA.realPow_eval_EWA
