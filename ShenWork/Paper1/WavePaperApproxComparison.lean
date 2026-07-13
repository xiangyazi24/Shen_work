import ShenWork.Paper1.WavePaperRouteA

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-! ## Tail-free comparison for a paper implicit step

On the whole line a pointwise maximum of `W - B` need not be attained.  The
bounded `C²` approximate-maximum lemma supplies points at which its first and
upper second derivative errors are arbitrarily small.  A strict resolvent gap
then absorbs those errors, so no endpoint limit or orbit-uniform tail is used.
-/

/-- Tail-free upper comparison for the paper implicit Euler step.  The final
operator estimate is deliberately exposed separately: Route-A coefficient
bookkeeping can establish it at the penalized almost-maximum without assuming
that a genuine global maximum exists. -/
theorem paperImplicitStep_le_barrier_of_quasiMonotone_tailfree
    {p : CMParams} {c lam Cmono E Q : ℝ} {u Z W B : ℝ → ℝ}
    (hlam : 0 < lam)
    (hsmall : (1 / lam) * Cmono < 1)
    (hE : 0 ≤ E)
    (hstep : ∀ x,
      paperImplicitStepOp p c (1 / lam) u W x = Z x)
    (hZB : ∀ x, Z x ≤ B x)
    (hf2 : ContDiff ℝ 2 (fun x => W x - B x))
    (hfbound : ∀ x, |W x - B x| ≤ Q)
    (hBsuper : ∀ x, paperWaveOperator p c u B x ≤ 0)
    (hop_approx : ∀ eta, 0 < eta → ∀ x₀,
      0 < W x₀ - B x₀ →
      |deriv (fun x => W x - B x) x₀| < eta →
      deriv (deriv (fun x => W x - B x)) x₀ < eta →
      paperWaveOperator p c u W x₀ - paperWaveOperator p c u B x₀ ≤
        Cmono * (W x₀ - B x₀) + E * eta) :
    ∀ x, W x ≤ B x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁⟩ := hcon
  have hfpos : 0 < W x₁ - B x₁ := sub_pos.mpr hx₁
  have hClam : Cmono < lam := by
    have hmul := mul_lt_mul_of_pos_left hsmall hlam
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    field_simp [hlamne] at hmul
    linarith
  let eta : ℝ :=
    (lam - Cmono) * (W x₁ - B x₁) / (4 * (E + 1))
  have heta : 0 < eta := by
    dsimp [eta]
    exact div_pos (mul_pos (sub_pos.mpr hClam) hfpos)
      (mul_pos (by norm_num) (by linarith))
  obtain ⟨x₀, hfvalue, hfSlope, hfSecond⟩ :=
    exists_approx_positive_max_deriv_data
      (f := fun x => W x - B x) (A := Q) (eta := eta) (x₁ := x₁)
      hf2 hfbound hfpos heta
  have hfpos₀ : 0 < W x₀ - B x₀ := by
    linarith
  have hA := hop_approx eta heta x₀ hfpos₀ hfSlope hfSecond
  have hstep₀ := hstep x₀
  have hdiv : W x₀ - B x₀ ≤
      (1 / lam) * paperWaveOperator p c u W x₀ := by
    simp only [paperImplicitStepOp_apply] at hstep₀
    linarith [hZB x₀]
  have hA_lower : lam * (W x₀ - B x₀) ≤
      paperWaveOperator p c u W x₀ - paperWaveOperator p c u B x₀ := by
    have hmul := mul_le_mul_of_nonneg_left hdiv hlam.le
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    have hmain : lam * (W x₀ - B x₀) ≤
        paperWaveOperator p c u W x₀ := by
      calc
        lam * (W x₀ - B x₀) ≤
            lam * ((1 / lam) * paperWaveOperator p c u W x₀) := hmul
        _ = paperWaveOperator p c u W x₀ := by field_simp [hlamne]
    linarith [hBsuper x₀]
  have hEeta :
      E * eta < (lam - Cmono) * (W x₁ - B x₁) / 4 := by
    dsimp [eta]
    have hE1 : E < E + 1 := by linarith
    have hbase : 0 < (lam - Cmono) * (W x₁ - B x₁) :=
      mul_pos (sub_pos.mpr hClam) hfpos
    have hden : 0 < 4 * (E + 1) :=
      mul_pos (by norm_num) (by linarith)
    have hscaled :
        E * ((lam - Cmono) * (W x₁ - B x₁)) <
          (E + 1) * ((lam - Cmono) * (W x₁ - B x₁)) :=
      mul_lt_mul_of_pos_right hE1 hbase
    calc
      E * ((lam - Cmono) * (W x₁ - B x₁) / (4 * (E + 1))) =
          (E * ((lam - Cmono) * (W x₁ - B x₁))) /
            (4 * (E + 1)) := by ring
      _ < ((E + 1) * ((lam - Cmono) * (W x₁ - B x₁))) /
          (4 * (E + 1)) := (div_lt_div_iff_of_pos_right hden).2 hscaled
      _ = (lam - Cmono) * (W x₁ - B x₁) / 4 := by
        field_simp [ne_of_gt (show 0 < E + 1 by linarith)]
  have hfscaled :
      (lam - Cmono) * ((W x₁ - B x₁) / 2) <
        (lam - Cmono) * (W x₀ - B x₀) :=
    mul_lt_mul_of_pos_left hfvalue (sub_pos.mpr hClam)
  have hgap_le :
      (lam - Cmono) * (W x₀ - B x₀) ≤ E * eta := by
    linarith [hA_lower, hA]
  have hbase : 0 < (lam - Cmono) * (W x₁ - B x₁) :=
    mul_pos (sub_pos.mpr hClam) hfpos
  have hquarter :
      (lam - Cmono) * (W x₁ - B x₁) / 4 <
        (lam - Cmono) * ((W x₁ - B x₁) / 2) := by
    calc
      (lam - Cmono) * (W x₁ - B x₁) / 4 <
          (lam - Cmono) * (W x₁ - B x₁) / 2 := by linarith
      _ = (lam - Cmono) * ((W x₁ - B x₁) / 2) := by ring
  exact (not_lt_of_ge hgap_le)
    (lt_trans (lt_trans hEeta hquarter) hfscaled)

/-- Tail-free lower comparison for the paper implicit Euler step.  This is the
dual statement for a subsolution `A`; it uses approximate positive maxima of
`A - W` and therefore carries no limit at either end of the real line. -/
theorem paperImplicitStep_ge_barrier_of_quasiMonotone_tailfree
    {p : CMParams} {c lam Cmono E Q : ℝ} {u Z W A : ℝ → ℝ}
    (hlam : 0 < lam)
    (hsmall : (1 / lam) * Cmono < 1)
    (hE : 0 ≤ E)
    (hstep : ∀ x,
      paperImplicitStepOp p c (1 / lam) u W x = Z x)
    (hAZ : ∀ x, A x ≤ Z x)
    (hf2 : ContDiff ℝ 2 (fun x => A x - W x))
    (hfbound : ∀ x, |A x - W x| ≤ Q)
    (hAsub : ∀ x, 0 ≤ paperWaveOperator p c u A x)
    (hop_approx : ∀ eta, 0 < eta → ∀ x₀,
      0 < A x₀ - W x₀ →
      |deriv (fun x => A x - W x) x₀| < eta →
      deriv (deriv (fun x => A x - W x)) x₀ < eta →
      paperWaveOperator p c u A x₀ - paperWaveOperator p c u W x₀ ≤
        Cmono * (A x₀ - W x₀) + E * eta) :
    ∀ x, A x ≤ W x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁⟩ := hcon
  have hfpos : 0 < A x₁ - W x₁ := sub_pos.mpr hx₁
  have hClam : Cmono < lam := by
    have hmul := mul_lt_mul_of_pos_left hsmall hlam
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    field_simp [hlamne] at hmul
    linarith
  let eta : ℝ :=
    (lam - Cmono) * (A x₁ - W x₁) / (4 * (E + 1))
  have heta : 0 < eta := by
    dsimp [eta]
    exact div_pos (mul_pos (sub_pos.mpr hClam) hfpos)
      (mul_pos (by norm_num) (by linarith))
  obtain ⟨x₀, hfvalue, hfSlope, hfSecond⟩ :=
    exists_approx_positive_max_deriv_data
      (f := fun x => A x - W x) (A := Q) (eta := eta) (x₁ := x₁)
      hf2 hfbound hfpos heta
  have hfpos₀ : 0 < A x₀ - W x₀ := by
    linarith
  have hA := hop_approx eta heta x₀ hfpos₀ hfSlope hfSecond
  have hstep₀ := hstep x₀
  have hdiv : A x₀ - W x₀ ≤
      -(1 / lam) * paperWaveOperator p c u W x₀ := by
    simp only [paperImplicitStepOp_apply] at hstep₀
    linarith [hAZ x₀]
  have hA_lower : lam * (A x₀ - W x₀) ≤
      paperWaveOperator p c u A x₀ - paperWaveOperator p c u W x₀ := by
    have hmul := mul_le_mul_of_nonneg_left hdiv hlam.le
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    have hmain : lam * (A x₀ - W x₀) ≤
        -paperWaveOperator p c u W x₀ := by
      calc
        lam * (A x₀ - W x₀) ≤
            lam * (-(1 / lam) * paperWaveOperator p c u W x₀) := hmul
        _ = -paperWaveOperator p c u W x₀ := by field_simp [hlamne]
    linarith [hAsub x₀]
  have hEeta :
      E * eta < (lam - Cmono) * (A x₁ - W x₁) / 4 := by
    dsimp [eta]
    have hE1 : E < E + 1 := by linarith
    have hbase : 0 < (lam - Cmono) * (A x₁ - W x₁) :=
      mul_pos (sub_pos.mpr hClam) hfpos
    have hden : 0 < 4 * (E + 1) :=
      mul_pos (by norm_num) (by linarith)
    have hscaled :
        E * ((lam - Cmono) * (A x₁ - W x₁)) <
          (E + 1) * ((lam - Cmono) * (A x₁ - W x₁)) :=
      mul_lt_mul_of_pos_right hE1 hbase
    calc
      E * ((lam - Cmono) * (A x₁ - W x₁) / (4 * (E + 1))) =
          (E * ((lam - Cmono) * (A x₁ - W x₁))) /
            (4 * (E + 1)) := by ring
      _ < ((E + 1) * ((lam - Cmono) * (A x₁ - W x₁))) /
          (4 * (E + 1)) := (div_lt_div_iff_of_pos_right hden).2 hscaled
      _ = (lam - Cmono) * (A x₁ - W x₁) / 4 := by
        field_simp [ne_of_gt (show 0 < E + 1 by linarith)]
  have hfscaled :
      (lam - Cmono) * ((A x₁ - W x₁) / 2) <
        (lam - Cmono) * (A x₀ - W x₀) :=
    mul_lt_mul_of_pos_left hfvalue (sub_pos.mpr hClam)
  have hgap_le :
      (lam - Cmono) * (A x₀ - W x₀) ≤ E * eta := by
    linarith [hA_lower, hA]
  have hbase : 0 < (lam - Cmono) * (A x₁ - W x₁) :=
    mul_pos (sub_pos.mpr hClam) hfpos
  have hquarter :
      (lam - Cmono) * (A x₁ - W x₁) / 4 <
        (lam - Cmono) * ((A x₁ - W x₁) / 2) := by
    calc
      (lam - Cmono) * (A x₁ - W x₁) / 4 <
          (lam - Cmono) * (A x₁ - W x₁) / 2 := by linarith
      _ = (lam - Cmono) * ((A x₁ - W x₁) / 2) := by ring
  exact (not_lt_of_ge hgap_le)
    (lt_trans (lt_trans hEeta hquarter) hfscaled)

section AxiomAudit

#print axioms paperImplicitStep_le_barrier_of_quasiMonotone_tailfree
#print axioms paperImplicitStep_ge_barrier_of_quasiMonotone_tailfree

end AxiomAudit

end ShenWork.Paper1
