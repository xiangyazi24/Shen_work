import ShenWork.Paper1.WavePinnedStepComparison

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-! ## Uniqueness of one lower-pinned paper step

For two implicit steps with the same frozen profile and the same old iterate,
the right-hand sides cancel.  The strict resolvent gap then absorbs the
one-sided nonlinear increment at an approximate maximum.  This is a
whole-line argument and uses no tail limit.
-/

/-- Abstract same-right-hand-side comparison for the paper implicit step. -/
theorem paperImplicitStep_same_rhs_le_of_quasiMonotone_tailfree
    {p : CMParams} {c lam Cmono E Q : ℝ}
    {u Z A B : ℝ → ℝ}
    (hlam : 0 < lam)
    (hsmall : (1 / lam) * Cmono < 1)
    (hE : 0 ≤ E)
    (hstepA : ∀ x,
      paperImplicitStepOp p c (1 / lam) u A x = Z x)
    (hstepB : ∀ x,
      paperImplicitStepOp p c (1 / lam) u B x = Z x)
    (hf2 : ContDiff ℝ 2 (fun x => A x - B x))
    (hfbound : ∀ x, A x - B x ≤ Q)
    (hop_approx : ∀ eta, 0 < eta → ∀ x₀,
      0 < A x₀ - B x₀ →
      |deriv (fun x => A x - B x) x₀| < eta →
      deriv (deriv (fun x => A x - B x)) x₀ < eta →
      paperWaveOperator p c u A x₀ - paperWaveOperator p c u B x₀ ≤
        Cmono * (A x₀ - B x₀) + E * eta) :
    ∀ x, A x ≤ B x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁⟩ := hcon
  have hfpos : 0 < A x₁ - B x₁ := sub_pos.mpr hx₁
  have hClam : Cmono < lam := by
    have hmul := mul_lt_mul_of_pos_left hsmall hlam
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    field_simp [hlamne] at hmul
    linarith
  let eta : ℝ :=
    (lam - Cmono) * (A x₁ - B x₁) / (4 * (E + 1))
  have heta : 0 < eta := by
    dsimp [eta]
    exact div_pos (mul_pos (sub_pos.mpr hClam) hfpos)
      (mul_pos (by norm_num) (by linarith))
  obtain ⟨x₀, hfvalue, hfSlope, hfSecond⟩ :=
    exists_approx_positive_max_deriv_data_of_upperBound
      (f := fun x => A x - B x) (A := Q) (eta := eta) (x₁ := x₁)
      hf2 hfbound hfpos heta
  have hfpos₀ : 0 < A x₀ - B x₀ := by
    linarith
  have hop := hop_approx eta heta x₀ hfpos₀ hfSlope hfSecond
  have hA := hstepA x₀
  have hB := hstepB x₀
  simp only [paperImplicitStepOp_apply] at hA hB
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  have hoperatorEq :
      lam * (A x₀ - B x₀) =
        paperWaveOperator p c u A x₀ - paperWaveOperator p c u B x₀ := by
    have hrel :
        A x₀ - B x₀ =
          (1 / lam) *
            (paperWaveOperator p c u A x₀ -
              paperWaveOperator p c u B x₀) := by
      linarith
    calc
      lam * (A x₀ - B x₀) =
          lam * ((1 / lam) *
            (paperWaveOperator p c u A x₀ -
              paperWaveOperator p c u B x₀)) := by rw [hrel]
      _ = paperWaveOperator p c u A x₀ -
          paperWaveOperator p c u B x₀ := by field_simp [hlamne]
  have hgap_le :
      (lam - Cmono) * (A x₀ - B x₀) ≤ E * eta := by
    linarith [hop, hoperatorEq]
  have hEeta :
      E * eta < (lam - Cmono) * (A x₁ - B x₁) / 4 := by
    dsimp [eta]
    have hE1 : E < E + 1 := by linarith
    have hbase : 0 < (lam - Cmono) * (A x₁ - B x₁) :=
      mul_pos (sub_pos.mpr hClam) hfpos
    have hden : 0 < 4 * (E + 1) :=
      mul_pos (by norm_num) (by linarith)
    have hscaled :
        E * ((lam - Cmono) * (A x₁ - B x₁)) <
          (E + 1) * ((lam - Cmono) * (A x₁ - B x₁)) :=
      mul_lt_mul_of_pos_right hE1 hbase
    calc
      E * ((lam - Cmono) * (A x₁ - B x₁) / (4 * (E + 1))) =
          (E * ((lam - Cmono) * (A x₁ - B x₁))) /
            (4 * (E + 1)) := by ring
      _ < ((E + 1) * ((lam - Cmono) * (A x₁ - B x₁))) /
          (4 * (E + 1)) := (div_lt_div_iff_of_pos_right hden).2 hscaled
      _ = (lam - Cmono) * (A x₁ - B x₁) / 4 := by
        field_simp [ne_of_gt (show 0 < E + 1 by linarith)]
  have hfscaled :
      (lam - Cmono) * ((A x₁ - B x₁) / 2) <
        (lam - Cmono) * (A x₀ - B x₀) :=
    mul_lt_mul_of_pos_left hfvalue (sub_pos.mpr hClam)
  have hbase : 0 < (lam - Cmono) * (A x₁ - B x₁) :=
    mul_pos (sub_pos.mpr hClam) hfpos
  have hquarter :
      (lam - Cmono) * (A x₁ - B x₁) / 4 <
        (lam - Cmono) * ((A x₁ - B x₁) / 2) := by
    calc
      (lam - Cmono) * (A x₁ - B x₁) / 4 <
          (lam - Cmono) * (A x₁ - B x₁) / 2 := by linarith
      _ = (lam - Cmono) * ((A x₁ - B x₁) / 2) := by ring
  exact (not_lt_of_ge hgap_le)
    (lt_trans (lt_trans hEeta hquarter) hfscaled)

/-- Two lower-pinned smooth paper steps with the same old iterate coincide.
The logarithmic slope is required only for the lower profile in each one-sided
comparison; applying the theorem in both directions yields equality. -/
theorem paperImplicitStep_unique_of_pinned_smooth
    {p : CMParams} {c lam M κ Cmono K : ℝ}
    {u Z W₁ W₂ : ℝ → ℝ}
    (hlam : 0 < lam) (hM : 0 < M)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hbox : PaperFrozenEllipticSourceBox p κ M)
    (hχ : p.χ ≤ 0)
    (hsmall : (1 / lam) * Cmono < 1)
    (hCmono :
      reactionLip p.α M
          + (-p.χ) * (M ^ p.γ) * rpowLip p.m M
          + ((-p.χ) * p.m * (M ^ p.γ) * K *
              (p.m - 1) * M ^ (p.m - 1)) ≤ Cmono)
    (hK : 0 ≤ K)
    (hstep₁ : ∀ x, paperImplicitStepOp p c (1 / lam) u W₁ x = Z x)
    (hstep₂ : ∀ x, paperImplicitStepOp p c (1 / lam) u W₂ x = Z x)
    (hW₁2 : ContDiff ℝ 2 W₁) (hW₂2 : ContDiff ℝ 2 W₂)
    (hW₁range : ∀ x, W₁ x ∈ Set.Icc (0 : ℝ) M)
    (hW₂range : ∀ x, W₂ x ∈ Set.Icc (0 : ℝ) M)
    (hW₁log : ∀ x, |deriv W₁ x| ≤ K * W₁ x)
    (hW₂log : ∀ x, |deriv W₂ x| ≤ K * W₂ x) :
    W₁ = W₂ := by
  have oneSide : ∀ (A C : ℝ → ℝ),
      (∀ x, paperImplicitStepOp p c (1 / lam) u A x = Z x) →
      (∀ x, paperImplicitStepOp p c (1 / lam) u C x = Z x) →
      ContDiff ℝ 2 A → ContDiff ℝ 2 C →
      (∀ x, A x ∈ Set.Icc (0 : ℝ) M) →
      (∀ x, C x ∈ Set.Icc (0 : ℝ) M) →
      (∀ x, |deriv C x| ≤ K * C x) →
      ∀ x, A x ≤ C x := by
    intro A C hstepA hstepC hA2 hC2 hArange hCrange hClog
    let Ccross : ℝ :=
      (-p.χ) * p.m * (M ^ p.γ) * K *
        (p.m - 1) * M ^ (p.m - 1)
    let Ecross : ℝ :=
      (-p.χ) * p.m * (M ^ p.γ) * M ^ (p.m - 1)
    let E : ℝ := 1 + |c| + Ecross
    have hE0 : 0 ≤ E := by
      dsimp [E, Ecross]
      have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
      have hnegχ : 0 ≤ -p.χ := neg_nonneg.mpr hχ
      have hpγ : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM.le _
      have hpm : 0 ≤ M ^ (p.m - 1) := Real.rpow_nonneg hM.le _
      have ht : 0 ≤ (-p.χ) * p.m * M ^ p.γ * M ^ (p.m - 1) := by
        exact mul_nonneg (mul_nonneg (mul_nonneg hnegχ hm0) hpγ) hpm
      linarith [abs_nonneg c]
    have hf2 : ContDiff ℝ 2 (fun x => A x - C x) := hA2.sub hC2
    have hfbound : ∀ x, A x - C x ≤ M := by
      intro x
      linarith [(hArange x).2, (hCrange x).1]
    have hop : ∀ eta, 0 < eta → ∀ x₀,
        0 < A x₀ - C x₀ →
        |deriv (fun x => A x - C x) x₀| < eta →
        deriv (deriv (fun x => A x - C x)) x₀ < eta →
        paperWaveOperator p c u A x₀ - paperWaveOperator p c u C x₀ ≤
          Cmono * (A x₀ - C x₀) + E * eta := by
      intro eta heta x₀ hcontact hfSlope hfSecond
      have hCA : C x₀ ≤ A x₀ := by linarith
      have hslope : |deriv A x₀ - deriv C x₀| ≤ eta := by
        have heq : deriv (fun x => A x - C x) x₀ =
            deriv A x₀ - deriv C x₀ :=
          deriv_sub (hA2.differentiable (by norm_num) x₀)
            (hC2.differentiable (by norm_num) x₀)
        rw [heq] at hfSlope
        exact hfSlope.le
      have hsecond :
          iteratedDeriv 2 A x₀ - iteratedDeriv 2 C x₀ ≤ eta := by
        have heq : deriv (deriv (fun x => A x - C x)) x₀ =
            iteratedDeriv 2 A x₀ - iteratedDeriv 2 C x₀ := by
          calc
            deriv (deriv (fun x => A x - C x)) x₀ =
                iteratedDeriv 2 (fun x => A x - C x) x₀ := by
              simp [iteratedDeriv_succ, iteratedDeriv_zero]
            _ = iteratedDeriv 2 A x₀ - iteratedDeriv 2 C x₀ :=
              iteratedDeriv_fun_sub hA2.contDiffAt hC2.contDiffAt
        rw [heq] at hfSecond
        exact hfSecond.le
      have hcross :
          (-p.χ) * p.m * (A x₀) ^ (p.m - 1) *
                deriv (frozenElliptic p u) x₀ * deriv A x₀
            - (-p.χ) * p.m * (C x₀) ^ (p.m - 1) *
                deriv (frozenElliptic p u) x₀ * deriv C x₀ ≤
          Ccross * (A x₀ - C x₀) + Ecross * eta := by
        simpa [Ccross, Ecross] using
          paperCrossGradient_diff_le_of_lower_log_slope
            (p := p) (a := -p.χ) (M := M) (BVd := M ^ p.γ)
            (K := K) (eta := eta) (u := u) (A := A) (B := C) (x₀ := x₀)
            rfl hχ hM (Real.rpow_nonneg hM.le _) hK
            (hCrange x₀).1 hCA (hArange x₀).2
            (hbox.deriv_abs_le u hu x₀) (hClog x₀) hslope
      have hop0 := paperWaveOperator_diff_le_of_approx_contact
        (p := p) (c := c) (a := -p.χ) (M := M) (BV := M ^ p.γ)
        (Ccross := Ccross) (Ecross := Ecross) (eta := eta)
        (u := u) (A := A) (W := C) (x₀ := x₀)
        rfl hχ hM.le (hArange x₀) (hCrange x₀) hCA
        (hbox.value_nonneg u hu x₀) (hbox.value_le u hu x₀)
        hsecond hslope hcross
      dsimp [Ccross, Ecross, E] at hop0 ⊢
      nlinarith [hop0, hCmono]
    exact paperImplicitStep_same_rhs_le_of_quasiMonotone_tailfree
      (p := p) (c := c) (lam := lam) (Cmono := Cmono)
      (E := E) (Q := M) (u := u) (Z := Z) (A := A) (B := C)
      hlam hsmall hE0 hstepA hstepC hf2 hfbound hop
  apply funext
  intro x
  exact le_antisymm
    (oneSide W₁ W₂ hstep₁ hstep₂ hW₁2 hW₂2
      hW₁range hW₂range hW₂log x)
    (oneSide W₂ W₁ hstep₂ hstep₁ hW₂2 hW₁2
      hW₂range hW₁range hW₁log x)

section AxiomAudit

#print axioms paperImplicitStep_same_rhs_le_of_quasiMonotone_tailfree
#print axioms paperImplicitStep_unique_of_pinned_smooth

end AxiomAudit

end ShenWork.Paper1
