import ShenWork.Paper1.WholeLineWeightedRegularityDQSources

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-- A radius-uniform cap bound forces the full exponential square to be
integrable.  This is the direct obstruction to estimating a single wave
profile at or above its principal tail exponent. -/
theorem not_uniform_cap_bound_of_not_fullWeightedL2
    {eta : ℝ} (heta : 0 < eta) {w : ℝ → ℝ} (hw : Continuous w)
    (hnot : ¬ Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) * |w x| ^ 2)) :
    ¬ ∃ C : ℝ,
      (∀ n : ℕ,
        Integrable (fun x : ℝ =>
          capWeight eta (n : ℝ) x * |w x| ^ 2)) ∧
      ∀ n : ℕ,
        (∫ x : ℝ, capWeight eta (n : ℝ) x * |w x| ^ 2) ≤ C := by
  rintro ⟨C, hcap, hbound⟩
  exact hnot (fullWeightedL2_integrable_of_uniform_cap
    heta hw hcap hbound)

/-- Fixed spatial difference quotients retain the principal exponential
tail. -/
theorem spatialDifferenceQuotient_scaled_tendsto_of_wave_tail
    {c kappaOne h : ℝ} {U : ℝ → ℝ}
    (htail : HasWaveRightTailAsymptotic c kappaOne U)
    (hgap : kappa c < kappaOne) (hh : h ≠ 0) :
    Tendsto
      (fun x => Real.exp (kappa c * x) *
        spatialDifferenceQuotient h U x)
      atTop
      (nhds ((Real.exp (-(kappa c) * h) - 1) / h)) := by
  have hratio := htail.ratio_tendsto_one hgap
  have hshift : Tendsto
      (fun x => U (x + h) / Real.exp (-(kappa c) * (x + h)))
      atTop (nhds 1) := by
    exact hratio.comp (tendsto_atTop_add_const_right atTop h tendsto_id)
  have hconst : Tendsto
      (fun _ : ℝ => Real.exp (-(kappa c) * h))
      atTop (nhds (Real.exp (-(kappa c) * h))) := tendsto_const_nhds
  have hnum := (hconst.mul hshift).sub hratio
  have hdiv := hnum.div_const h
  convert hdiv using 1
  funext x
  unfold spatialDifferenceQuotient
  have hexpx : Real.exp (kappa c * x) =
      (Real.exp (-(kappa c) * x))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hexpshift : Real.exp (-(kappa c) * (x + h)) =
      Real.exp (-(kappa c) * x) * Real.exp (-(kappa c) * h) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexpx, hexpshift]
  field_simp [Real.exp_ne_zero, hh]
  ring

/-- A real function with a strictly positive tail limit cannot be integrable
on the whole line. -/
theorem not_integrable_of_tendsto_atTop_pos
    {f : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hlim : Tendsto f atTop (nhds L)) :
    ¬ Integrable f := by
  intro hf
  have hev : ∀ᶠ x in atTop, L / 2 < f x :=
    hlim.eventually (Ioi_mem_nhds (by linarith : L / 2 < L))
  obtain ⟨A, hA⟩ := eventually_atTop.1 hev
  have hconst : IntegrableOn (fun _ : ℝ => L / 2) (Ici A) := by
    refine Integrable.mono' hf.norm.integrableOn
      continuous_const.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < L / 2)]
    exact (hA x hx).le.trans (le_abs_self (f x))
  rw [integrableOn_const_iff] at hconst
  rcases hconst with hzero | hfinite
  · have : L / 2 = 0 := enorm_eq_zero.1 hzero
    linarith
  · exact (lt_top_iff_ne_top.1 hfinite) Real.volume_Ici

/-- At the principal wave exponent, a fixed nonzero difference quotient is
not square integrable.  The conclusion uses only the committed value-tail
normalization, not a derivative asymptotic. -/
theorem wave_spatialDifferenceQuotient_not_integrable_at_kappa
    {c kappaOne h : ℝ} {U : ℝ → ℝ}
    (hkappa : 0 < kappa c)
    (htail : HasWaveRightTailAsymptotic c kappaOne U)
    (hgap : kappa c < kappaOne) (hh : h ≠ 0) :
    ¬ Integrable (fun x : ℝ =>
      Real.exp (2 * kappa c * x) *
        |spatialDifferenceQuotient h U x| ^ 2) := by
  let L : ℝ := (Real.exp (-(kappa c) * h) - 1) / h
  have hLne : L ≠ 0 := by
    dsimp [L]
    apply div_ne_zero _ hh
    apply sub_ne_zero.mpr
    intro he
    have hz : -(kappa c) * h = 0 := (Real.exp_eq_one_iff _).mp he
    have hkne : kappa c ≠ 0 := ne_of_gt hkappa
    rcases mul_eq_zero.mp hz with hkzero | hhzero
    · exact (neg_ne_zero.mpr hkne) hkzero
    · exact hh hhzero
  have hscaled := spatialDifferenceQuotient_scaled_tendsto_of_wave_tail
    htail hgap hh
  have hsquare : Tendsto
      (fun x => |Real.exp (kappa c * x) *
        spatialDifferenceQuotient h U x| ^ 2)
      atTop (nhds (|L| ^ 2)) := by
    simpa only [L] using hscaled.abs.pow 2
  have hintegrand : (fun x : ℝ =>
      Real.exp (2 * kappa c * x) *
        |spatialDifferenceQuotient h U x| ^ 2) =
      fun x => |Real.exp (kappa c * x) *
        spatialDifferenceQuotient h U x| ^ 2 := by
    funext x
    rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_pow]
    have hexp : Real.exp (kappa c * x) ^ 2 =
        Real.exp (2 * kappa c * x) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hexp]
  rw [hintegrand]
  apply not_integrable_of_tendsto_atTop_pos (sq_pos_of_ne_zero (abs_ne_zero.mpr hLne))
  exact hsquare

#print axioms not_uniform_cap_bound_of_not_fullWeightedL2
#print axioms spatialDifferenceQuotient_scaled_tendsto_of_wave_tail
#print axioms not_integrable_of_tendsto_atTop_pos
#print axioms wave_spatialDifferenceQuotient_not_integrable_at_kappa

end ShenWork.Paper1
