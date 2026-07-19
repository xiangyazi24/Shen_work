import ShenWork.Paper1.WavePositivePlateauComparison

/-!
# The positive constant plateau ledger at a general trap height

`paperWaveOperator_const_subsolution_nonneg_pos_MChi` requires the trap height
to be exactly `MChi p`.  That is unusable downstream: the χ>0 ceiling chain only
delivers `u ≤ MChi p + r` for a prescribed `r > 0` (the relaxing ceiling
approaches `MChi p` from above and never attains it in finite time), so the
exact trap is never available on a finite window.

The committed proof, however, has an explicit budget
`χ/(1-χ) + (1-2χ)/(2(1-χ)) < 1`, whose slack is positive precisely because
`χ < 1/2` is STRICT.  The resolver bound enters only through
`frozenElliptic ≤ Q ^ γ`, so the whole ledger goes through at any trap height
`Q` satisfying the sharp condition

  `χ * Q ^ γ < 1`,

which at `Q = MChi p` and the critical exponent is exactly `χ < 1/2`.  Since
`x ↦ x ^ γ` is continuous, every `Q = MChi p + r` with `r` small enough
qualifies — which is what the burn-in actually provides.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- The constant plateau is a frozen subsolution at ANY trap height `Q` with
`χ * Q ^ γ < 1`, provided the plateau value is capped by half the resulting
margin.  Generalizes `paperWaveOperator_const_subsolution_nonneg_pos_MChi`
(which is the case `Q = MChi p`, where the condition reads `χ < 1/2`). -/
theorem paperWaveOperator_const_subsolution_nonneg_pos_trap
    (p : CMParams) {c κ d Q : ℝ} {u : ℝ → ℝ}
    (hχ0 : 0 ≤ p.χ) (hχ1 : p.χ < 1)
    (hα : p.α = p.m + p.γ - 1)
    (hQ0 : 0 < Q)
    (hQχ : p.χ * Q ^ p.γ < 1)
    (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hdcap : (1 - p.χ) * d ≤ (1 - p.χ * Q ^ p.γ) / 2)
    (hu : InWaveTrapSet κ Q u) :
    ∀ x, 0 ≤ paperWaveOperator p c u (fun _ => d) x := by
  intro x
  rw [paperWaveOperator_const_eq p hu.cunif_bdd hu.nonneg x]
  apply mul_nonneg hd0.le
  have hden : 0 < 1 - p.χ := by linarith
  have hV0 : 0 ≤ frozenElliptic p u x :=
    frozenElliptic_nonneg_of_inWaveTrapSet p hu x
  have hVle : frozenElliptic p u x ≤ Q ^ p.γ :=
    frozenElliptic_le_rpow_of_inWaveTrapSet p hQ0 hu x
  have hdm1 : d ^ (p.m - 1) ≤ 1 :=
    Real.rpow_le_one hd0.le hd1 (sub_nonneg.mpr p.hm)
  have hdm10 : 0 ≤ d ^ (p.m - 1) :=
    Real.rpow_nonneg hd0.le _
  -- the chemotactic term is controlled by the trap height
  have hchem :
      p.χ * d ^ (p.m - 1) * frozenElliptic p u x ≤ p.χ * Q ^ p.γ := by
    calc
      p.χ * d ^ (p.m - 1) * frozenElliptic p u x ≤
          p.χ * 1 * (Q ^ p.γ) := by
        gcongr
      _ = p.χ * Q ^ p.γ := by ring
  -- the logistic term is controlled by the plateau cap
  have hdα : d ^ p.α ≤ d := by
    calc
      d ^ p.α ≤ d ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hd0 hd1 p.hα
      _ = d := Real.rpow_one d
  have hlogistic :
      (1 - p.χ) * d ^ p.α ≤ (1 - p.χ * Q ^ p.γ) / 2 :=
    (mul_le_mul_of_nonneg_left hdα hden.le).trans hdcap
  have hbudget :
      p.χ * Q ^ p.γ + (1 - p.χ * Q ^ p.γ) / 2 < 1 := by linarith
  have hpow : d ^ (p.m + p.γ - 1) = d ^ p.α := by rw [hα]
  rw [hpow]
  nlinarith [hchem, hlogistic, hbudget]

/-- At the exact critical ceiling the sharp trap condition is the paper's
`χ < 1/2`: with `α = m + γ - 1` one has `MChi ^ γ ≤ 1/(1-χ)`, so
`χ * MChi ^ γ ≤ χ/(1-χ) < 1` exactly when `χ < 1/2`.  Hence the generalized
ledger extends the committed one instead of weakening it. -/
theorem chiPos_trap_condition_of_chi_lt_half
    (p : CMParams) (hχ0 : 0 ≤ p.χ) (hχhalf : p.χ < 1 / 2)
    (hα : p.α = p.m + p.γ - 1) :
    p.χ * (MChi p) ^ p.γ < 1 := by
  have hχ1 : p.χ < 1 := by linarith
  have hden : 0 < 1 - p.χ := by linarith
  have hMγ : (MChi p) ^ p.γ ≤ 1 / (1 - p.χ) :=
    MChi_rpow_gamma_le_one_div_one_sub_chi p hχ0 hχ1 hα
  have hstep : p.χ * (MChi p) ^ p.γ ≤ p.χ * (1 / (1 - p.χ)) := by
    exact mul_le_mul_of_nonneg_left hMγ hχ0
  have hfinal : p.χ * (1 / (1 - p.χ)) < 1 := by
    rw [mul_one_div, div_lt_one hden]
    linarith
  exact hstep.trans_lt hfinal

/-- The trap condition is open in the height: if it holds at `Q₀` it holds at
every nearby larger height.  This is what lets the burn-in ceiling
`MChi p + r` be used in place of the unattainable exact `MChi p`. -/
theorem exists_trap_height_above_of_chi_mul_rpow_lt_one
    (p : CMParams) {Q₀ : ℝ} (hQ₀ : 0 < Q₀)
    (hχ0 : 0 ≤ p.χ) (hcond : p.χ * Q₀ ^ p.γ < 1) :
    ∃ r > 0, p.χ * (Q₀ + r) ^ p.γ < 1 := by
  have hγ0 : 0 < p.γ := lt_of_lt_of_le zero_lt_one p.hγ
  have hcont : ContinuousAt (fun s : ℝ => p.χ * (Q₀ + s) ^ p.γ) 0 := by
    have hbase : ContinuousAt (fun s : ℝ => Q₀ + s) 0 := by fun_prop
    have : ContinuousAt (fun y : ℝ => y ^ p.γ) (Q₀ + 0) := by
      simpa using Real.continuousAt_rpow_const _ _ (Or.inl (by simpa using hQ₀.ne'))
    exact (this.comp hbase).const_smul p.χ |>.congr (by
      filter_upwards with s using by simp [smul_eq_mul])
  have hstart : p.χ * (Q₀ + 0) ^ p.γ < 1 := by simpa using hcond
  have hev : ∀ᶠ s : ℝ in nhds 0, p.χ * (Q₀ + s) ^ p.γ < 1 :=
    hcont.eventually_lt_const hstart
  rcases Metric.eventually_nhds_iff.mp hev with ⟨ε, hε, hball⟩
  refine ⟨ε / 2, by linarith, ?_⟩
  exact hball (by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith)

section AxiomAudit

#print axioms paperWaveOperator_const_subsolution_nonneg_pos_trap
#print axioms chiPos_trap_condition_of_chi_lt_half
#print axioms exists_trap_height_above_of_chi_mul_rpow_lt_one

end AxiomAudit

end ShenWork.Paper1
