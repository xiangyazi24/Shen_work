import ShenWork.Paper1.WholeLineWeightedRegularityScaledTrapNatural

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-!
# Scaled lower-barrier operator estimate

The normalized proof of Paper 1, Lemma 4.2 applies to a coefficient-one
right-tail trap.  A Cauchy restart instead supplies a common amplitude `Q`.
The frozen resolver is homogeneous of degree `gamma`, so its derivative loss
is enlarged by exactly `Q^gamma`.  This file records that factor in the
Lemma-4.2 constant and repeats only the short pointwise operator ledger.
-/

/-- The Lemma-4.2 bad-term constant for a tail trap of amplitude `Q`. -/
def paperScaledSubsolutionK
    (p : CMParams) (Q kappa kappaTilde : ℝ) : ℝ :=
  Q ^ p.γ * paperSubsolutionK 1 kappa kappaTilde p.m p.γ

/-- The corresponding lower-barrier `D` threshold. -/
def paperScaledDMin
    (p : CMParams) (Q kappa kappaTilde c : ℝ) : ℝ :=
  (1 + |p.χ| * paperScaledSubsolutionK p Q kappa kappaTilde) /
    paperSpeedDenominator c kappaTilde

theorem paperScaledSubsolutionK_nonneg
    (p : CMParams) {Q c kappa kappaTilde : ℝ}
    (hcond : PaperLemma42ExactConditions p c kappa kappaTilde 1)
    (hQ : 0 ≤ Q) :
    0 ≤ paperScaledSubsolutionK p Q kappa kappaTilde := by
  exact mul_nonneg (Real.rpow_nonneg hQ p.γ)
    (paperSubsolutionK_nonneg_of_conditions hcond)

theorem paperDMin_one_le_paperScaledDMin
    (p : CMParams) {Q c kappa kappaTilde : ℝ}
    (hcond : PaperLemma42ExactConditions p c kappa kappaTilde 1)
    (hQ : 1 ≤ Q) :
    paperDMin p.χ 1 kappa kappaTilde p.m p.γ c ≤
      paperScaledDMin p Q kappa kappaTilde c := by
  have hQpow : 1 ≤ Q ^ p.γ :=
    Real.one_le_rpow hQ (by linarith [p.hγ])
  have hK0 :
      0 ≤ paperSubsolutionK 1 kappa kappaTilde p.m p.γ :=
    paperSubsolutionK_nonneg_of_conditions hcond
  have hnum :
      1 + |p.χ| * paperSubsolutionK 1 kappa kappaTilde p.m p.γ ≤
        1 + |p.χ| * paperScaledSubsolutionK p Q kappa kappaTilde := by
    dsimp [paperScaledSubsolutionK]
    nlinarith [abs_nonneg p.χ,
      mul_le_mul_of_nonneg_right hQpow hK0]
  exact (div_le_div_iff_of_pos_right hcond.den_pos).2 hnum

theorem paperScaledDMin_pos
    (p : CMParams) {Q c kappa kappaTilde : ℝ}
    (hcond : PaperLemma42ExactConditions p c kappa kappaTilde 1)
    (hQ : 1 ≤ Q) :
    0 < paperScaledDMin p Q kappa kappaTilde c := by
  exact lt_of_lt_of_le (paperDMin_pos_of_conditions hcond)
    (paperDMin_one_le_paperScaledDMin p hcond hQ)

/-- On a scaled time-trap slice, the derivative chemotaxis loss and the
algebraic `m+gamma` loss are bounded by the genuinely scaled constant.

The proof normalizes the slice by `Q`, invokes the already proved three-case
coefficient-one estimate, restores the exact resolver scaling, and uses
`1 ≤ Q^gamma` to absorb the algebraic term as well. -/
theorem paperLemma42_KTerm_le_scaled_of_inTimeWaveTrapSet
    (p : CMParams) {Q T c kappa kappaTilde D t x : ℝ}
    (hcond : PaperLemma42ExactConditions p c kappa kappaTilde 1)
    (hQ : 1 ≤ Q)
    (hD : paperScaledDMin p Q kappa kappaTilde c < D)
    (hD1 : 1 ≤ D)
    {q : ℝ → ℝ → ℝ} (htrap : InTimeWaveTrapSet kappa Q T q)
    (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hx : x ∈ Set.Ioi (lowerBarrierXMinus kappa kappaTilde D)) :
    p.m * (lowerBarrierRaw kappa kappaTilde D x) ^ (p.m - 1) *
          |deriv (frozenElliptic p (q t)) x| *
          |deriv (lowerBarrierRaw kappa kappaTilde D) x| +
        lowerBarrierRaw kappa kappaTilde D x *
          (lowerBarrierRaw kappa kappaTilde D x) ^
            (p.m + p.γ - 1) ≤
      paperScaledSubsolutionK p Q kappa kappaTilde *
        Real.exp (-kappaTilde * x) := by
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hDbase :
      paperDMin p.χ 1 kappa kappaTilde p.m p.γ c < D :=
    lt_of_le_of_lt (paperDMin_one_le_paperScaledDMin p hcond hQ) hD
  have hnorm : InWaveTrapSet kappa 1 (fun y => q t y / Q) :=
    htrap.div_slice_inWaveTrapSet_one hQpos ht
  have hbase :=
    (PaperLemma42KTermEstimate_of_conditions hcond hDbase hD1)
      (fun y => q t y / Q) hnorm x hx
  have hQpow : 1 ≤ Q ^ p.γ :=
    Real.one_le_rpow hQ (by linarith [p.hγ])
  have hQpow0 : 0 ≤ Q ^ p.γ := le_trans zero_le_one hQpow
  have hWnonneg : 0 ≤ lowerBarrierRaw kappa kappaTilde D x := by
    exact lowerBarrierRaw_nonneg_on_paper_region hcond hDbase hx
  have hA0 :
      0 ≤ p.m * (lowerBarrierRaw kappa kappaTilde D x) ^ (p.m - 1) *
          |deriv (frozenElliptic p (fun y => q t y / Q)) x| *
          |deriv (lowerBarrierRaw kappa kappaTilde D) x| := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (le_trans zero_le_one p.hm)
          (Real.rpow_nonneg hWnonneg _))
        (abs_nonneg _))
      (abs_nonneg _)
  have hB0 :
      0 ≤ lowerBarrierRaw kappa kappaTilde D x *
          (lowerBarrierRaw kappa kappaTilde D x) ^
            (p.m + p.γ - 1) := by
    exact mul_nonneg hWnonneg (Real.rpow_nonneg hWnonneg _)
  rw [frozenElliptic_deriv_eq_rpow_mul_div_profile p hQpos
    (fun y => htrap.nonneg ht y) x, abs_mul,
    abs_of_nonneg hQpow0]
  dsimp [paperScaledSubsolutionK]
  calc
    p.m * (lowerBarrierRaw kappa kappaTilde D x) ^ (p.m - 1) *
          (Q ^ p.γ *
            |deriv (frozenElliptic p (fun y => q t y / Q)) x|) *
          |deriv (lowerBarrierRaw kappa kappaTilde D) x| +
        lowerBarrierRaw kappa kappaTilde D x *
          (lowerBarrierRaw kappa kappaTilde D x) ^
            (p.m + p.γ - 1)
        ≤ Q ^ p.γ *
            (p.m * (lowerBarrierRaw kappa kappaTilde D x) ^ (p.m - 1) *
                |deriv (frozenElliptic p (fun y => q t y / Q)) x| *
                |deriv (lowerBarrierRaw kappa kappaTilde D) x| +
              lowerBarrierRaw kappa kappaTilde D x *
                (lowerBarrierRaw kappa kappaTilde D x) ^
                  (p.m + p.γ - 1)) := by
          nlinarith [mul_le_mul_of_nonneg_right hQpow hB0]
    _ ≤ Q ^ p.γ *
          (paperSubsolutionK 1 kappa kappaTilde p.m p.γ *
            Real.exp (-kappaTilde * x)) :=
      mul_le_mul_of_nonneg_left hbase hQpow0
    _ = Q ^ p.γ * paperSubsolutionK 1 kappa kappaTilde p.m p.γ *
          Real.exp (-kappaTilde * x) := by ring

/-- Scaled Paper-1 Lemma 4.2 on one slice of a common finite-time trap. -/
theorem paperWaveOperator_lowerBarrierRaw_nonneg_chiNonpos_scaled
    (p : CMParams) {Q T c kappa kappaTilde D t x : ℝ}
    (hcond : PaperLemma42ExactConditions p c kappa kappaTilde 1)
    (hQ : 1 ≤ Q)
    (hD : paperScaledDMin p Q kappa kappaTilde c < D)
    (hD1 : 1 ≤ D)
    {q : ℝ → ℝ → ℝ} (htrap : InTimeWaveTrapSet kappa Q T q)
    (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hx : x ∈ Set.Ioi (lowerBarrierXMinus kappa kappaTilde D)) :
    0 ≤ paperWaveOperator p c (q t)
      (lowerBarrierRaw kappa kappaTilde D) x := by
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hDbase :
      paperDMin p.χ 1 kappa kappaTilde p.m p.γ c < D :=
    lt_of_le_of_lt (paperDMin_one_le_paperScaledDMin p hcond hQ) hD
  have hnorm : InWaveTrapSet kappa 1 (fun y => q t y / Q) :=
    htrap.div_slice_inWaveTrapSet_one hQpos ht
  have hlog :=
    (PaperLemma42LogisticEstimate_of_conditions hcond hDbase hD1)
      (fun y => q t y / Q) hnorm x hx
  have hK := paperLemma42_KTerm_le_scaled_of_inTimeWaveTrapSet
    p hcond hQ hD hD1 htrap ht hx
  have hχK := mul_le_mul_of_nonneg_left hK (abs_nonneg p.χ)
  have hbad :
      paperLemma42BadTerm p (q t)
          (lowerBarrierRaw kappa kappaTilde D) x ≤
        (1 + |p.χ| * paperScaledSubsolutionK p Q kappa kappaTilde) *
          Real.exp (-kappaTilde * x) := by
    dsimp [paperLemma42BadTerm]
    calc
      lowerBarrierRaw kappa kappaTilde D x *
            (lowerBarrierRaw kappa kappaTilde D x) ^ p.α +
          |p.χ| *
            (p.m * (lowerBarrierRaw kappa kappaTilde D x) ^ (p.m - 1) *
                |deriv (frozenElliptic p (q t)) x| *
                |deriv (lowerBarrierRaw kappa kappaTilde D) x| +
              lowerBarrierRaw kappa kappaTilde D x *
                (lowerBarrierRaw kappa kappaTilde D x) ^
                  (p.m + p.γ - 1))
          ≤ Real.exp (-kappaTilde * x) +
              |p.χ| *
                (paperScaledSubsolutionK p Q kappa kappaTilde *
                  Real.exp (-kappaTilde * x)) :=
        add_le_add hlog hχK
      _ = (1 + |p.χ| *
              paperScaledSubsolutionK p Q kappa kappaTilde) *
            Real.exp (-kappaTilde * x) := by ring
  set W : ℝ → ℝ := lowerBarrierRaw kappa kappaTilde D with hWdef
  set V : ℝ → ℝ := frozenElliptic p (q t) with hVdef
  set lin : ℝ :=
    D * paperSpeedDenominator c kappaTilde * Real.exp (-kappaTilde * x)
  set chem : ℝ :=
    -p.χ * p.m * (W x) ^ (p.m - 1) * deriv V x * deriv W x
  set good : ℝ := W x * (-p.χ * (W x) ^ (p.m - 1) * V x)
  set logistic : ℝ := W x * (W x) ^ p.α
  set derivBad : ℝ :=
    |p.χ| * (p.m * (W x) ^ (p.m - 1) * |deriv V x| * |deriv W x|)
  set gammaBad : ℝ := |p.χ| * (W x * (W x) ^ (p.m + p.γ - 1))
  have hW_nonneg : 0 ≤ W x := by
    rw [hWdef]
    exact lowerBarrierRaw_nonneg_on_paper_region hcond hDbase hx
  have hWpow_nonneg : 0 ≤ (W x) ^ (p.m - 1) :=
    Real.rpow_nonneg hW_nonneg _
  have hV_nonneg : 0 ≤ V x := by
    rw [hVdef]
    exact frozenElliptic_nonneg p (fun y => htrap.nonneg ht y) x
  have hminus_chi : -p.χ = |p.χ| := by
    rw [abs_of_nonpos hcond.hχ]
  have hchi : p.χ = -|p.χ| := by linarith
  have hcoef_nonneg :
      0 ≤ |p.χ| * (p.m * (W x) ^ (p.m - 1)) := by
    exact mul_nonneg (abs_nonneg p.χ)
      (mul_nonneg (le_trans zero_le_one p.hm) hWpow_nonneg)
  have hprod_lower :
      -(|deriv V x| * |deriv W x|) ≤ deriv V x * deriv W x := by
    have h := neg_abs_le (deriv V x * deriv W x)
    rwa [abs_mul] at h
  have hchem_lower : -derivBad ≤ chem := by
    have hmul := mul_le_mul_of_nonneg_left hprod_lower hcoef_nonneg
    dsimp [derivBad, chem] at hmul ⊢
    rw [hminus_chi]
    linarith
  have hgood_nonneg : 0 ≤ good := by
    dsimp [good]
    exact mul_nonneg hW_nonneg
      (mul_nonneg (mul_nonneg (neg_nonneg.mpr hcond.hχ) hWpow_nonneg)
        hV_nonneg)
  have hop :
      paperWaveOperator p c (q t) W x =
        lin + chem + good - logistic - gammaBad := by
    rw [hWdef]
    rw [paperWaveOperator_lowerBarrierRaw_eq_of_kappa_speed p (q t) x
      (ne_of_gt hcond.hκ0) hcond.hc]
    dsimp [lin, chem, good, logistic, gammaBad]
    rw [hVdef, hWdef]
    rw [hminus_chi, hchi]
    simp [abs_of_nonneg (abs_nonneg p.χ)]
    ring_nf
  have hbad_eq :
      paperLemma42BadTerm p (q t) W x =
        logistic + derivBad + gammaBad := by
    dsimp [paperLemma42BadTerm, logistic, derivBad, gammaBad]
    rw [hVdef]
    ring
  have hop_lower :
      lin - paperLemma42BadTerm p (q t) W x ≤
        paperWaveOperator p c (q t) W x := by
    rw [hbad_eq, hop]
    nlinarith [hchem_lower, hgood_nonneg]
  have hmargin :
      0 < D * paperSpeedDenominator c kappaTilde - 1 -
        |p.χ| * paperScaledSubsolutionK p Q kappa kappaTilde := by
    dsimp [paperScaledDMin] at hD
    rw [div_lt_iff₀ hcond.den_pos] at hD
    linarith
  have hleft :
      (D * paperSpeedDenominator c kappaTilde - 1 -
          |p.χ| * paperScaledSubsolutionK p Q kappa kappaTilde) *
          Real.exp (-kappaTilde * x) =
        lin -
          (1 + |p.χ| *
            paperScaledSubsolutionK p Q kappa kappaTilde) *
            Real.exp (-kappaTilde * x) := by
    dsimp [lin]
    ring
  calc
    0 ≤ (D * paperSpeedDenominator c kappaTilde - 1 -
          |p.χ| * paperScaledSubsolutionK p Q kappa kappaTilde) *
          Real.exp (-kappaTilde * x) :=
      mul_nonneg hmargin.le (Real.exp_nonneg _)
    _ = lin -
          (1 + |p.χ| *
            paperScaledSubsolutionK p Q kappa kappaTilde) *
            Real.exp (-kappaTilde * x) := hleft
    _ ≤ lin - paperLemma42BadTerm p (q t) W x :=
      sub_le_sub_left hbad lin
    _ ≤ paperWaveOperator p c (q t) W x := hop_lower

/-- For nonpositive sensitivity, the patched lower barrier is a subsolution
away from its `C¹` splice on every slice of a scaled finite-time wave trap.
Unlike the normalized Lemma 4.2, the right branch uses
`paperScaledDMin`; hence no unscaled `paperDMin Q` is smuggled into the
conclusion. -/
theorem paperWaveOperator_lowerBarrierPlateau_nonneg_chiNonpos_scaled_away
    (p : CMParams) {Q T c kappa kappaTilde D t x : ℝ}
    (hcond : PaperLemma42ExactConditions p c kappa kappaTilde 1)
    (hQ : 1 ≤ Q)
    (hD : paperScaledDMin p Q kappa kappaTilde c < D)
    (hD1 : 1 ≤ D)
    (hplateau : ∀ y, lowerBarrierPlateau kappa kappaTilde D y ≤
      constantSubsolutionThreshold p.χ kappa kappaTilde D)
    {q : ℝ → ℝ → ℝ} (htrap : InTimeWaveTrapSet kappa Q T q)
    (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hx : x ≠ lowerBarrierXPlus kappa kappaTilde D) :
    0 ≤ paperWaveOperator p c (q t)
      (lowerBarrierPlateau kappa kappaTilde D) x := by
  rcases lt_or_gt_of_ne hx with hxlt | hxgt
  · let d := lowerBarrierRaw kappa kappaTilde D
        (lowerBarrierXPlus kappa kappaTilde D)
    have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
    have hd0 : 0 < d := by
      dsimp [d]
      exact lowerBarrierRaw_pos_at_xplus hcond.hκ0
        (sub_pos.mpr hcond.hgap) hDpos
    have hd :
        d ≤ constantSubsolutionThreshold p.χ kappa kappaTilde D := by
      simpa [d, lowerBarrierPlateau_eq_const_of_le
        (le_refl (lowerBarrierXPlus kappa kappaTilde D))] using
          hplateau (lowerBarrierXPlus kappa kappaTilde D)
    have hconst := paperWaveOperator_const_subsolution_nonneg_of_chi_nonpos
      p (c := c) (κ := kappa) (κtilde := kappaTilde) (D := D)
        hcond.hχ (htrap.slice_cunif ht) (fun y => htrap.nonneg ht y)
        hd0 hd x
    have heq := lowerBarrierPlateau_eventuallyEq_const_of_lt hxlt
    have hval :
        lowerBarrierPlateau kappa kappaTilde D x = d := by
      rw [lowerBarrierPlateau_eq_const_of_le hxlt.le]
    have hderiv :
        deriv (lowerBarrierPlateau kappa kappaTilde D) x = 0 := by
      rw [heq.deriv_eq]
      simp
    have hderiv2 :
        iteratedDeriv 2 (lowerBarrierPlateau kappa kappaTilde D) x = 0 := by
      rw [heq.iteratedDeriv_eq 2]
      simp only [iteratedDeriv_const, show (2 : ℕ) ≠ 0 from by norm_num,
        ite_false]
    have hconst2 : iteratedDeriv 2 (fun _ : ℝ => d) x = 0 := by
      simp only [iteratedDeriv_const, show (2 : ℕ) ≠ 0 from by norm_num,
        ite_false]
    have hopEq :
        paperWaveOperator p c (q t)
            (lowerBarrierPlateau kappa kappaTilde D) x =
          paperWaveOperator p c (q t) (fun _ => d) x := by
      unfold paperWaveOperator
      dsimp only
      rw [hval, hderiv, hderiv2, hconst2]
      simp
    rw [hopEq]
    exact hconst
  · have hregion :
        x ∈ Set.Ioi (lowerBarrierXMinus kappa kappaTilde D) := by
      exact lt_trans
        (lowerBarrierXMinus_lt_xplus hcond.hκ0
          (sub_pos.mpr hcond.hgap) (lt_of_lt_of_le zero_lt_one hD1)) hxgt
    have hraw := paperWaveOperator_lowerBarrierRaw_nonneg_chiNonpos_scaled
      p hcond hQ hD hD1 htrap ht hregion
    have heq := lowerBarrierPlateau_eventuallyEq_raw_of_gt hxgt
    have hval : lowerBarrierPlateau kappa kappaTilde D x =
        lowerBarrierRaw kappa kappaTilde D x :=
      lowerBarrierPlateau_eq_raw_of_xplus_lt hxgt
    have hderiv : deriv (lowerBarrierPlateau kappa kappaTilde D) x =
        deriv (lowerBarrierRaw kappa kappaTilde D) x := heq.deriv_eq
    have hderiv2 :
        iteratedDeriv 2 (lowerBarrierPlateau kappa kappaTilde D) x =
          iteratedDeriv 2 (lowerBarrierRaw kappa kappaTilde D) x :=
      heq.iteratedDeriv_eq 2
    unfold paperWaveOperator at hraw ⊢
    dsimp only
    rw [hval, hderiv, hderiv2]
    exact hraw

section AxiomAudit

#print axioms paperScaledSubsolutionK_nonneg
#print axioms paperDMin_one_le_paperScaledDMin
#print axioms paperScaledDMin_pos
#print axioms paperLemma42_KTerm_le_scaled_of_inTimeWaveTrapSet
#print axioms paperWaveOperator_lowerBarrierRaw_nonneg_chiNonpos_scaled
#print axioms
  paperWaveOperator_lowerBarrierPlateau_nonneg_chiNonpos_scaled_away

end AxiomAudit

end ShenWork.Paper1
