import ShenWork.Wiener.EWA.ExpLipschitz

/-!
# EWA brick — `FnegLipschitz`: the negative-power Laplace bound + Lipschitz (Phase C)

Quantitative companion of `WienerLevy`'s `integrable_gammaIntegrandEWA`.  Two
estimates feeding the EWA flux fixed-point contraction:

* `FnegEWA_norm_le` — `‖FnegEWA f s‖ ≤ negNormConst s δ Md` (the operator-norm
  bound of `(eval f)^{−s}` realized as a genuine `EWA T 1` element);
* `FnegEWA_lipschitz` — `‖FnegEWA f s − FnegEWA g s‖ ≤ negLipConst s δ Md·‖f−g‖`,
  via distributing the subtraction across the Bochner integral, dominating each
  integrand by `expNeg_sub_expNeg_norm_le`, and integrating the `t^s`-shifted
  majorant.

Both reduce to scalar Γ-integrals evaluated through Mathlib's
`Real.integral_rpow_mul_exp_neg_mul_Ioi`.
-/

open scoped BigOperators
open MeasureTheory Set Real
open ShenWork.GWA ShenWork.Wiener

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Part 0 — the explicit Γ-combination constants. -/

/-- Operator-norm constant for `FnegEWA f s` (the negative power `(eval f)^{−s}`).
`Cdec := 8·(1+1/π)²` is the committed decisive constant. -/
def negNormConst (s δ Md : ℝ) : ℝ :=
  (1 / Real.Gamma s) * (8 * (1 + 1 / Real.pi) ^ 2) *
    ((1 / δ) ^ s * Real.Gamma s + 2 * Md * (1 / δ) ^ (s + 1) * Real.Gamma (s + 1)
      + Md ^ 2 * (1 / δ) ^ (s + 2) * Real.Gamma (s + 2))

/-- Lipschitz constant for `f ↦ FnegEWA f s`.  Powers are shifted up by one
relative to `negNormConst` (the extra factor `t` from differentiating `e^{−tf}`). -/
def negLipConst (s δ Md : ℝ) : ℝ :=
  (1 / Real.Gamma s) * (8 * (1 + 1 / Real.pi) ^ 2) *
    ((1 / δ) ^ (s + 1) * Real.Gamma (s + 1) + 2 * Md * (1 / δ) ^ (s + 2) * Real.Gamma (s + 2)
      + Md ^ 2 * (1 / δ) ^ (s + 3) * Real.Gamma (s + 3))

/-! ### Part 1 — the shifted majorant: integrability and integral value. -/

/-- The `t^p`-weighted decisive majorant `t^{p−1}·C·(1+t·Md)²·e^{−δt}` is
integrable on `Ioi 0` for `p>0`, `δ>0`.  (`p = s` gives the norm majorant,
`p = s+1` the Lipschitz majorant: the extra factor `t` shifts `s−1 → s`.) -/
theorem integrable_lip_majorantEWA (p δ Md : ℝ) (hp : 0 < p) (hδpos : 0 < δ) :
    IntegrableOn (fun t : ℝ => t ^ (p - 1) *
      ((8 * (1 + 1 / Real.pi) ^ 2) * (1 + t * Md) ^ 2 * Real.exp (-δ * t))) (Ioi 0) := by
  set C : ℝ := 8 * (1 + 1 / Real.pi) ^ 2 with hC
  have e0 := WA.integrableOn_rpow_mul_exp (p - 1) δ (by linarith) hδpos
  have e1 := WA.integrableOn_rpow_mul_exp ((p - 1) + 1) δ (by linarith) hδpos
  have e2 := WA.integrableOn_rpow_mul_exp ((p - 1) + 2) δ (by linarith) hδpos
  have hcomb : IntegrableOn
      (fun t : ℝ => C * (t ^ (p - 1) * Real.exp (-(δ * t)))
        + C * (2 * Md) * (t ^ ((p - 1) + 1) * Real.exp (-(δ * t)))
        + C * (Md ^ 2) * (t ^ ((p - 1) + 2) * Real.exp (-(δ * t)))) (Ioi 0) :=
    ((e0.const_mul C).add (e1.const_mul (C * (2 * Md)))).add (e2.const_mul (C * Md ^ 2))
  apply hcomb.congr_fun _ measurableSet_Ioi
  intro t ht
  have htpos : 0 < t := ht
  simp only []
  have hr1 : t ^ ((p - 1) + 1) = t ^ (p - 1) * t := by
    rw [Real.rpow_add htpos, Real.rpow_one]
  have hr2 : t ^ ((p - 1) + 2) = t ^ (p - 1) * t ^ 2 := by
    rw [Real.rpow_add htpos]; norm_num
  have hexp : Real.exp (-(δ * t)) = Real.exp (-δ * t) := by rw [neg_mul]
  rw [hr1, hr2, hexp]
  ring

/-- The integral value of the `t^p`-weighted majorant: the explicit Γ-combination
`C·((1/δ)^p·Γ(p) + 2Md·(1/δ)^{p+1}·Γ(p+1) + Md²·(1/δ)^{p+2}·Γ(p+2))`. -/
theorem integral_lip_majorantEWA (p δ Md : ℝ) (hp : 0 < p) (hδpos : 0 < δ) :
    ∫ t in Ioi 0, t ^ (p - 1) *
        ((8 * (1 + 1 / Real.pi) ^ 2) * (1 + t * Md) ^ 2 * Real.exp (-δ * t))
      = (8 * (1 + 1 / Real.pi) ^ 2) *
        ((1 / δ) ^ p * Real.Gamma p + 2 * Md * (1 / δ) ^ (p + 1) * Real.Gamma (p + 1)
          + Md ^ 2 * (1 / δ) ^ (p + 2) * Real.Gamma (p + 2)) := by
  set C : ℝ := 8 * (1 + 1 / Real.pi) ^ 2 with hC
  have e0 := WA.integrableOn_rpow_mul_exp (p - 1) δ (by linarith) hδpos
  have e1 := WA.integrableOn_rpow_mul_exp ((p - 1) + 1) δ (by linarith) hδpos
  have e2 := WA.integrableOn_rpow_mul_exp ((p - 1) + 2) δ (by linarith) hδpos
  -- rewrite the integrand as the sum of three scalar rpow·exp terms.
  have hcong : ∫ t in Ioi 0, t ^ (p - 1) * (C * (1 + t * Md) ^ 2 * Real.exp (-δ * t))
      = ∫ t in Ioi 0, (C * (t ^ (p - 1) * Real.exp (-(δ * t)))
        + C * (2 * Md) * (t ^ ((p - 1) + 1) * Real.exp (-(δ * t)))
        + C * (Md ^ 2) * (t ^ ((p - 1) + 2) * Real.exp (-(δ * t)))) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have htpos : 0 < t := ht
    have hr1 : t ^ ((p - 1) + 1) = t ^ (p - 1) * t := by
      rw [Real.rpow_add htpos, Real.rpow_one]
    have hr2 : t ^ ((p - 1) + 2) = t ^ (p - 1) * t ^ 2 := by
      rw [Real.rpow_add htpos]; norm_num
    have hexp : Real.exp (-(δ * t)) = Real.exp (-δ * t) := by rw [neg_mul]
    rw [hr1, hr2, hexp]; ring
  rw [hcong]
  -- split the sum-integral term by term via two `integral_add` applications.
  have iA : IntegrableOn (fun t : ℝ => C * (t ^ (p - 1) * Real.exp (-(δ * t)))) (Ioi 0) :=
    e0.const_mul C
  have iB : IntegrableOn (fun t : ℝ => C * (2 * Md) * (t ^ ((p - 1) + 1) * Real.exp (-(δ * t))))
      (Ioi 0) := e1.const_mul (C * (2 * Md))
  have iC : IntegrableOn (fun t : ℝ => C * (Md ^ 2) * (t ^ ((p - 1) + 2) * Real.exp (-(δ * t))))
      (Ioi 0) := e2.const_mul (C * Md ^ 2)
  have iAB : IntegrableOn (fun t : ℝ => C * (t ^ (p - 1) * Real.exp (-(δ * t)))
      + C * (2 * Md) * (t ^ ((p - 1) + 1) * Real.exp (-(δ * t)))) (Ioi 0) := iA.add iB
  rw [integral_add iAB iC, integral_add iA iB,
    integral_const_mul, integral_const_mul, integral_const_mul]
  have g0 : ∫ t in Ioi 0, t ^ (p - 1) * Real.exp (-(δ * t)) = (1 / δ) ^ p * Real.Gamma p :=
    integral_rpow_mul_exp_neg_mul_Ioi hp hδpos
  have g1 : ∫ t in Ioi 0, t ^ (p - 1 + 1) * Real.exp (-(δ * t))
      = (1 / δ) ^ (p + 1) * Real.Gamma (p + 1) := by
    have h := integral_rpow_mul_exp_neg_mul_Ioi (a := p + 1) (by linarith) hδpos
    rw [show p + 1 - 1 = p - 1 + 1 by ring] at h; rw [h]
  have g2 : ∫ t in Ioi 0, t ^ (p - 1 + 2) * Real.exp (-(δ * t))
      = (1 / δ) ^ (p + 2) * Real.Gamma (p + 2) := by
    have h := integral_rpow_mul_exp_neg_mul_Ioi (a := p + 2) (by linarith) hδpos
    rw [show p + 2 - 1 = p - 1 + 2 by ring] at h; rw [h]
  rw [g0, g1, g2]; ring

/-! ### Part 2 — the operator-norm bound `FnegEWA_norm_le`. -/

/-- **`FnegEWA_norm_le`.** Under the uniform spectral floor `δ>0`, `s>0`, and a
derivative bound `Md`, `‖FnegEWA f s‖ ≤ negNormConst s δ Md`.  Quantitative
version of `integrable_gammaIntegrandEWA`. -/
theorem FnegEWA_norm_le {f : EWA T 1} {s δ Md : ℝ} (hs : 0 < s) (hδpos : 0 < δ)
    (hMd : 0 ≤ Md) (hf_floor : UniformFloor f δ) (hfD : ‖GWA.gDeriv f‖ ≤ Md) :
    ‖FnegEWA f s‖ ≤ negNormConst s δ Md := by
  have hΓpos : 0 < Real.Gamma s := Real.Gamma_pos_of_pos hs
  set C : ℝ := 8 * (1 + 1 / Real.pi) ^ 2 with hC
  -- pointwise majorant of the EWA-valued integrand (via the decisive bound + Md).
  have hmaj : ∀ t ∈ Ioi (0 : ℝ), ‖gammaIntegrandEWA f s t‖
      ≤ t ^ (s - 1) * (C * (1 + t * Md) ^ 2 * Real.exp (-δ * t)) := by
    intro t ht
    have htpos : 0 < t := ht
    have htnn : (0 : ℝ) ≤ t ^ (s - 1) := Real.rpow_nonneg htpos.le _
    have hdec := EWA_decisive_exp_bound f t δ htpos.le hf_floor
    have hmono : (1 + t * ‖GWA.gDeriv f‖) ^ 2 ≤ (1 + t * Md) ^ 2 := by
      have hle : 1 + t * ‖GWA.gDeriv f‖ ≤ 1 + t * Md := by
        nlinarith [mul_le_mul_of_nonneg_left hfD htpos.le]
      have hnn : (0 : ℝ) ≤ 1 + t * ‖GWA.gDeriv f‖ := by positivity
      nlinarith [hle, hnn]
    have hexp_pos : (0 : ℝ) ≤ Real.exp (-δ * t) := le_of_lt (Real.exp_pos _)
    have hCpos : (0 : ℝ) ≤ C := by rw [hC]; positivity
    have hdec' : ‖NormedSpace.exp (((-t : ℝ) : ℂ) • f)‖
        ≤ C * (1 + t * Md) ^ 2 * Real.exp (-δ * t) := by
      refine le_trans hdec ?_
      have := mul_le_mul_of_nonneg_right hmono hexp_pos
      nlinarith [this, hCpos, hexp_pos]
    rw [gammaIntegrandEWA, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htnn]
    exact mul_le_mul_of_nonneg_left hdec' htnn
  -- integrability of the EWA-valued integrand and of the majorant.
  have hint := integrable_gammaIntegrandEWA f s δ hs hδpos hf_floor
  have hmajint : IntegrableOn (fun t : ℝ => t ^ (s - 1) *
      (C * (1 + t * Md) ^ 2 * Real.exp (-δ * t))) (Ioi 0) :=
    integrable_lip_majorantEWA s δ Md hs hδpos
  -- bound the integral norm.
  have hnorm_int : ‖∫ t in Ioi 0, gammaIntegrandEWA f s t‖
      ≤ ∫ t in Ioi 0, t ^ (s - 1) * (C * (1 + t * Md) ^ 2 * Real.exp (-δ * t)) := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine setIntegral_mono_on hint.norm hmajint measurableSet_Ioi (fun t ht => hmaj t ht)
  rw [FnegEWA, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
    (by positivity : (0 : ℝ) ≤ 1 / Real.Gamma s)]
  rw [negNormConst, ← hC]
  rw [integral_lip_majorantEWA s δ Md hs hδpos] at hnorm_int
  calc (1 / Real.Gamma s) * ‖∫ t in Ioi 0, gammaIntegrandEWA f s t‖
      ≤ (1 / Real.Gamma s) * (C *
          ((1 / δ) ^ s * Real.Gamma s + 2 * Md * (1 / δ) ^ (s + 1) * Real.Gamma (s + 1)
            + Md ^ 2 * (1 / δ) ^ (s + 2) * Real.Gamma (s + 2))) :=
        mul_le_mul_of_nonneg_left hnorm_int (by positivity)
    _ = (1 / Real.Gamma s) * C *
          ((1 / δ) ^ s * Real.Gamma s + 2 * Md * (1 / δ) ^ (s + 1) * Real.Gamma (s + 1)
            + Md ^ 2 * (1 / δ) ^ (s + 2) * Real.Gamma (s + 2)) := by ring

/-! ### Part 3 — the Lipschitz bound `FnegEWA_lipschitz`. -/

/-- **`FnegEWA_lipschitz`.** Under common floor `δ>0`, `s>0`, and a common
derivative bound `Md`, `f ↦ FnegEWA f s` is Lipschitz with constant
`negLipConst s δ Md`. -/
theorem FnegEWA_lipschitz {f g : EWA T 1} {s δ Md : ℝ} (hs : 0 < s) (hδpos : 0 < δ)
    (hMd : 0 ≤ Md) (hf_floor : UniformFloor f δ) (hg_floor : UniformFloor g δ)
    (hfD : ‖GWA.gDeriv f‖ ≤ Md) (hgD : ‖GWA.gDeriv g‖ ≤ Md) :
    ‖FnegEWA f s - FnegEWA g s‖ ≤ negLipConst s δ Md * ‖f - g‖ := by
  have hΓpos : 0 < Real.Gamma s := Real.Gamma_pos_of_pos hs
  set C : ℝ := 8 * (1 + 1 / Real.pi) ^ 2 with hC
  set κ : ℝ := 1 / Real.Gamma s with hκ
  -- the difference is (1/Γs)•∫ t^{s−1}•(e^{−tf} − e^{−tg}).
  have hdiff : FnegEWA f s - FnegEWA g s
      = (κ : ℂ) • ∫ t in Ioi 0, gammaIntegrandEWA f s t - gammaIntegrandEWA g s t := by
    rw [FnegEWA, FnegEWA, ← smul_sub, hκ]
    congr 1
    rw [integral_sub (integrable_gammaIntegrandEWA f s δ hs hδpos hf_floor)
      (integrable_gammaIntegrandEWA g s δ hs hδpos hg_floor)]
  -- pointwise majorant of the integrand difference: t^{s−1}·(t·‖f−g‖·C·(1+tMd)²·e^{−δt}).
  have hmaj : ∀ t ∈ Ioi (0 : ℝ),
      ‖gammaIntegrandEWA f s t - gammaIntegrandEWA g s t‖
      ≤ ‖f - g‖ * (t ^ ((s + 1) - 1) * (C * (1 + t * Md) ^ 2 * Real.exp (-δ * t))) := by
    intro t ht
    have htpos : 0 < t := ht
    have htnn : (0 : ℝ) ≤ t ^ (s - 1) := Real.rpow_nonneg htpos.le _
    have hexpdiff := expNeg_sub_expNeg_norm_le (f := f) (g := g) (t := t) (δ := δ) (Md := Md)
      htpos.le hMd hf_floor hg_floor hfD hgD
    have hfac : gammaIntegrandEWA f s t - gammaIntegrandEWA g s t
        = ((t ^ (s - 1) : ℝ) : ℂ) •
          (NormedSpace.exp (((-t : ℝ) : ℂ) • f) - NormedSpace.exp (((-t : ℝ) : ℂ) • g)) := by
      rw [gammaIntegrandEWA, gammaIntegrandEWA, smul_sub]
    rw [hfac, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htnn]
    have hts : t ^ ((s + 1) - 1) = t ^ (s - 1) * t := by
      rw [show (s + 1) - 1 = (s - 1) + 1 by ring, Real.rpow_add htpos, Real.rpow_one]
    rw [hts]
    calc t ^ (s - 1) *
          ‖NormedSpace.exp (((-t : ℝ) : ℂ) • f) - NormedSpace.exp (((-t : ℝ) : ℂ) • g)‖
        ≤ t ^ (s - 1) * (t * ‖f - g‖ * C * (1 + t * Md) ^ 2 * Real.exp (-δ * t)) :=
          mul_le_mul_of_nonneg_left hexpdiff htnn
      _ = ‖f - g‖ * (t ^ (s - 1) * t * (C * (1 + t * Md) ^ 2 * Real.exp (-δ * t))) := by ring
  -- integrability of the difference and of the (s+1)-shifted majorant.
  have hintf := integrable_gammaIntegrandEWA f s δ hs hδpos hf_floor
  have hintg := integrable_gammaIntegrandEWA g s δ hs hδpos hg_floor
  have hintdiff : IntegrableOn (fun t : ℝ => gammaIntegrandEWA f s t - gammaIntegrandEWA g s t)
      (Ioi 0) := hintf.sub hintg
  have hmajint : IntegrableOn (fun t : ℝ => ‖f - g‖ * (t ^ ((s + 1) - 1) *
      (C * (1 + t * Md) ^ 2 * Real.exp (-δ * t)))) (Ioi 0) :=
    (integrable_lip_majorantEWA (s + 1) δ Md (by linarith) hδpos).const_mul _
  -- bound the integral norm.
  have hnorm_int : ‖∫ t in Ioi 0, gammaIntegrandEWA f s t - gammaIntegrandEWA g s t‖
      ≤ ∫ t in Ioi 0, ‖f - g‖ * (t ^ ((s + 1) - 1) *
          (C * (1 + t * Md) ^ 2 * Real.exp (-δ * t))) := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    exact setIntegral_mono_on hintdiff.norm hmajint measurableSet_Ioi (fun t ht => hmaj t ht)
  -- evaluate the shifted majorant integral.
  have hval : ∫ t in Ioi 0, ‖f - g‖ * (t ^ ((s + 1) - 1) *
        (C * (1 + t * Md) ^ 2 * Real.exp (-δ * t)))
      = ‖f - g‖ * (C * ((1 / δ) ^ (s + 1) * Real.Gamma (s + 1)
          + 2 * Md * (1 / δ) ^ (s + 2) * Real.Gamma (s + 2)
          + Md ^ 2 * (1 / δ) ^ (s + 3) * Real.Gamma (s + 3))) := by
    rw [integral_const_mul, integral_lip_majorantEWA (s + 1) δ Md (by linarith) hδpos]
    have h2 : (s + 1) + 1 = s + 2 := by ring
    have h3 : (s + 1) + 2 = s + 3 := by ring
    rw [h2, h3]
  rw [hdiff, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
    (by rw [hκ]; positivity : (0 : ℝ) ≤ κ)]
  rw [negLipConst, ← hC]
  rw [hval] at hnorm_int
  calc κ * ‖∫ t in Ioi 0, gammaIntegrandEWA f s t - gammaIntegrandEWA g s t‖
      ≤ κ * (‖f - g‖ * (C * ((1 / δ) ^ (s + 1) * Real.Gamma (s + 1)
          + 2 * Md * (1 / δ) ^ (s + 2) * Real.Gamma (s + 2)
          + Md ^ 2 * (1 / δ) ^ (s + 3) * Real.Gamma (s + 3)))) :=
        mul_le_mul_of_nonneg_left hnorm_int (by rw [hκ]; positivity)
    _ = κ * C * ((1 / δ) ^ (s + 1) * Real.Gamma (s + 1)
          + 2 * Md * (1 / δ) ^ (s + 2) * Real.Gamma (s + 2)
          + Md ^ 2 * (1 / δ) ^ (s + 3) * Real.Gamma (s + 3)) * ‖f - g‖ := by ring

end ShenWork.EWA

#print axioms ShenWork.EWA.FnegEWA_lipschitz
#print axioms ShenWork.EWA.FnegEWA_norm_le
