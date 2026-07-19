import ShenWork.Paper1.WholeLineChiPosPlateauWindow
import ShenWork.Paper1.WholeLineWeightedRegularityChiNegPlateauPersistenceNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalSliceH0ChiPosNatural
import ShenWork.Paper1.WavePositiveLeftEndpoint

open Filter Function MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Persistence of a positive-sensitivity lower plateau

The late positive-sensitivity windows have the scaled upper bound
`min Q (Q * exp (-kappa*x))`.  The raw positive Lemma-4.2 ledger therefore
has to retain the exact resolver factor `Q^gamma`.  On the constant branch we
translate a slice by `log Q / kappa`; its scaled upper barrier then becomes
the standard `upperBarrier kappa Q`, so the general trap-height constant
theorem applies literally at height `Q`.
-/

/-- The admissible constant height in a scaled positive-sensitivity trap. -/
def chiPosTrapPlateauFloor (p : CMParams) (Q : ℝ) : ℝ :=
  min 1 ((1 - p.χ * Q ^ p.γ) / (2 * (1 - p.χ)))

theorem chiPosTrapPlateauFloor_pos
    (p : CMParams) {Q : ℝ} (hχ1 : p.χ < 1)
    (hQχ : p.χ * Q ^ p.γ < 1) :
    0 < chiPosTrapPlateauFloor p Q := by
  unfold chiPosTrapPlateauFloor
  apply lt_min zero_lt_one
  exact div_pos (by linarith) (mul_pos (by norm_num) (by linarith))

theorem chiPosTrapPlateauFloor_le_one (p : CMParams) (Q : ℝ) :
    chiPosTrapPlateauFloor p Q ≤ 1 :=
  min_le_left _ _

theorem chiPosTrapPlateauFloor_cap
    (p : CMParams) {Q d : ℝ} (hχ1 : p.χ < 1)
    (hd : d ≤ chiPosTrapPlateauFloor p Q) :
    (1 - p.χ) * d ≤ (1 - p.χ * Q ^ p.γ) / 2 := by
  have hden : 0 < 1 - p.χ := by linarith
  have hfrac :
      d ≤ (1 - p.χ * Q ^ p.γ) / (2 * (1 - p.χ)) :=
    hd.trans (min_le_right _ _)
  calc
    (1 - p.χ) * d ≤
        (1 - p.χ) *
          ((1 - p.χ * Q ^ p.γ) / (2 * (1 - p.χ))) :=
      mul_le_mul_of_nonneg_left hfrac hden.le
    _ = (1 - p.χ * Q ^ p.γ) / 2 := by
      field_simp [ne_of_gt hden]

/-! ## The positive scaled raw-tail ledger -/

theorem paperScaledSubsolutionK_nonneg_pos
    (p : CMParams) {Q c kappa kappaTilde : ℝ}
    (hcond : PositivePaperLemma42ExactConditions
      p c kappa kappaTilde 1)
    (hQ : 0 ≤ Q) :
    0 ≤ paperScaledSubsolutionK p Q kappa kappaTilde := by
  exact mul_nonneg (Real.rpow_nonneg hQ p.γ)
    (paperSubsolutionK_nonneg_of_positive_conditions hcond)

theorem paperDMin_one_le_paperScaledDMin_pos
    (p : CMParams) {Q c kappa kappaTilde : ℝ}
    (hcond : PositivePaperLemma42ExactConditions
      p c kappa kappaTilde 1)
    (hQ : 1 ≤ Q) :
    paperDMin p.χ 1 kappa kappaTilde p.m p.γ c ≤
      paperScaledDMin p Q kappa kappaTilde c := by
  have hQpow : 1 ≤ Q ^ p.γ :=
    Real.one_le_rpow hQ (by linarith [p.hγ])
  have hK0 :
      0 ≤ paperSubsolutionK 1 kappa kappaTilde p.m p.γ :=
    paperSubsolutionK_nonneg_of_positive_conditions hcond
  have hnum :
      1 + |p.χ| * paperSubsolutionK 1 kappa kappaTilde p.m p.γ ≤
        1 + |p.χ| * paperScaledSubsolutionK p Q kappa kappaTilde := by
    dsimp [paperScaledSubsolutionK]
    nlinarith [abs_nonneg p.χ,
      mul_le_mul_of_nonneg_right hQpow hK0]
  exact (div_le_div_iff_of_pos_right hcond.den_pos).2 hnum

theorem paperScaledDMin_pos_pos
    (p : CMParams) {Q c kappa kappaTilde : ℝ}
    (hcond : PositivePaperLemma42ExactConditions
      p c kappa kappaTilde 1)
    (hQ : 1 ≤ Q) :
    0 < paperScaledDMin p Q kappa kappaTilde c := by
  exact lt_of_lt_of_le (paperDMin_pos_of_positive_conditions hcond)
    (paperDMin_one_le_paperScaledDMin_pos p hcond hQ)

/-- The two adverse resolver terms in the positive ledger scale together by
exactly `Q^gamma` after normalizing a scaled trap slice by `Q`. -/
theorem paperLemma42_positive_KTerm_le_scaled_of_inTimeWaveTrapSet
    (p : CMParams) {Q T c kappa kappaTilde D t x : ℝ}
    (hcond : PositivePaperLemma42ExactConditions
      p c kappa kappaTilde 1)
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
          (lowerBarrierRaw kappa kappaTilde D x) ^ (p.m - 1) *
          frozenElliptic p (q t) x ≤
      paperScaledSubsolutionK p Q kappa kappaTilde *
        Real.exp (-kappaTilde * x) := by
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hDbase :
      paperDMin p.χ 1 kappa kappaTilde p.m p.γ c < D :=
    lt_of_le_of_lt
      (paperDMin_one_le_paperScaledDMin_pos p hcond hQ) hD
  have hnorm : InWaveTrapSet kappa 1 (fun y => q t y / Q) :=
    htrap.div_slice_inWaveTrapSet_one hQpos ht
  have hbase :=
    (PaperLemma42PositiveKTermEstimate_of_positive_conditions
      hcond hDbase hD1) (fun y => q t y / Q) hnorm x hx
  have hQpow0 : 0 ≤ Q ^ p.γ := Real.rpow_nonneg hQpos.le _
  rw [frozenElliptic_deriv_eq_rpow_mul_div_profile p hQpos
      (fun y => htrap.nonneg ht y) x,
    frozenElliptic_eq_rpow_mul_div_profile p hQpos
      (fun y => htrap.nonneg ht y) x,
    abs_mul, abs_of_nonneg hQpow0]
  dsimp [paperScaledSubsolutionK]
  calc
    p.m * (lowerBarrierRaw kappa kappaTilde D x) ^ (p.m - 1) *
          (Q ^ p.γ *
            |deriv (frozenElliptic p (fun y => q t y / Q)) x|) *
          |deriv (lowerBarrierRaw kappa kappaTilde D) x| +
        lowerBarrierRaw kappa kappaTilde D x *
          (lowerBarrierRaw kappa kappaTilde D x) ^ (p.m - 1) *
          (Q ^ p.γ * frozenElliptic p (fun y => q t y / Q) x) =
        Q ^ p.γ *
          (p.m * (lowerBarrierRaw kappa kappaTilde D x) ^ (p.m - 1) *
              |deriv (frozenElliptic p (fun y => q t y / Q)) x| *
              |deriv (lowerBarrierRaw kappa kappaTilde D) x| +
            lowerBarrierRaw kappa kappaTilde D x *
              (lowerBarrierRaw kappa kappaTilde D x) ^ (p.m - 1) *
              frozenElliptic p (fun y => q t y / Q) x) := by ring
    _ ≤ Q ^ p.γ *
          (paperSubsolutionK 1 kappa kappaTilde p.m p.γ *
            Real.exp (-kappaTilde * x)) :=
      mul_le_mul_of_nonneg_left hbase hQpow0
    _ = Q ^ p.γ * paperSubsolutionK 1 kappa kappaTilde p.m p.γ *
          Real.exp (-kappaTilde * x) := by ring

/-- Positive Paper-1 Lemma 4.2 on a slice of a common scaled trap. -/
theorem paperWaveOperator_lowerBarrierRaw_nonneg_chiPos_scaled
    (p : CMParams) {Q T c kappa kappaTilde D t x : ℝ}
    (hcond : PositivePaperLemma42ExactConditions
      p c kappa kappaTilde 1)
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
    lt_of_le_of_lt
      (paperDMin_one_le_paperScaledDMin_pos p hcond hQ) hD
  have hnorm : InWaveTrapSet kappa 1 (fun y => q t y / Q) :=
    htrap.div_slice_inWaveTrapSet_one hQpos ht
  have hlog :=
    (PaperLemma42LogisticEstimate_of_positive_conditions
      hcond hDbase hD1) (fun y => q t y / Q) hnorm x hx
  have hK := paperLemma42_positive_KTerm_le_scaled_of_inTimeWaveTrapSet
    p hcond hQ hD hD1 htrap ht hx
  set W : ℝ → ℝ := lowerBarrierRaw kappa kappaTilde D with hWdef
  set V : ℝ → ℝ := frozenElliptic p (q t) with hVdef
  have hW_pos : 0 < W x := by
    rw [hWdef]
    exact lowerBarrierRaw_pos_on_positive_paper_region hcond hDbase hx
  have hW_nonneg : 0 ≤ W x := hW_pos.le
  have hlog_nonneg : 0 ≤ W x * (W x) ^ p.α :=
    mul_nonneg hW_nonneg (Real.rpow_nonneg hW_nonneg _)
  have hlog_weight :
      (1 - |p.χ|) * (W x * (W x) ^ p.α) ≤
        Real.exp (-kappaTilde * x) := by
    have hmul :
        (1 - |p.χ|) * (W x * (W x) ^ p.α) ≤
          W x * (W x) ^ p.α := by
      have hcoef_le_one : 1 - |p.χ| ≤ 1 :=
        sub_le_self _ (abs_nonneg p.χ)
      nlinarith
    exact hmul.trans (by simpa only [W] using hlog)
  have hχK := mul_le_mul_of_nonneg_left hK (abs_nonneg p.χ)
  have hbad :
      paperLemma42PositiveBadTerm p (q t) W x ≤
        (1 + |p.χ| * paperScaledSubsolutionK p Q kappa kappaTilde) *
          Real.exp (-kappaTilde * x) := by
    dsimp [paperLemma42PositiveBadTerm]
    calc
      (1 - |p.χ|) * (W x * (W x) ^ p.α) +
          |p.χ| *
            (p.m * (W x) ^ (p.m - 1) *
                |deriv (frozenElliptic p (q t)) x| * |deriv W x| +
              W x * (W x) ^ (p.m - 1) * frozenElliptic p (q t) x)
          ≤ Real.exp (-kappaTilde * x) +
              |p.χ| *
                (paperScaledSubsolutionK p Q kappa kappaTilde *
                  Real.exp (-kappaTilde * x)) :=
        add_le_add hlog_weight hχK
      _ = (1 + |p.χ| *
              paperScaledSubsolutionK p Q kappa kappaTilde) *
            Real.exp (-kappaTilde * x) := by ring
  set lin : ℝ :=
    D * paperSpeedDenominator c kappaTilde * Real.exp (-kappaTilde * x)
  set chem : ℝ :=
    -p.χ * p.m * (W x) ^ (p.m - 1) * deriv V x * deriv W x
  set vBad : ℝ := |p.χ| * (W x * (W x) ^ (p.m - 1) * V x)
  set logistic : ℝ := W x * (W x) ^ p.α
  set derivBad : ℝ :=
    |p.χ| * (p.m * (W x) ^ (p.m - 1) *
      |deriv V x| * |deriv W x|)
  have hWpow_nonneg : 0 ≤ (W x) ^ (p.m - 1) :=
    Real.rpow_nonneg hW_nonneg _
  have hχ_abs : p.χ = |p.χ| := by
    rw [hcond.chi_abs_eq]
  have hcoef_nonneg :
      0 ≤ |p.χ| * (p.m * (W x) ^ (p.m - 1)) := by
    exact mul_nonneg (abs_nonneg p.χ)
      (mul_nonneg (le_trans zero_le_one p.hm) hWpow_nonneg)
  have hprod_upper :
      deriv V x * deriv W x ≤ |deriv V x| * |deriv W x| := by
    have h := le_abs_self (deriv V x * deriv W x)
    rwa [abs_mul] at h
  have hchem_lower : -derivBad ≤ chem := by
    have hmul := mul_le_mul_of_nonpos_left hprod_upper
      (neg_nonpos.mpr hcoef_nonneg)
    calc
      -derivBad =
          -(|p.χ| * (p.m * (W x) ^ (p.m - 1))) *
            (|deriv V x| * |deriv W x|) := by
          dsimp [derivBad]
          ring
      _ ≤ -(|p.χ| * (p.m * (W x) ^ (p.m - 1))) *
            (deriv V x * deriv W x) := hmul
      _ = chem := by
          dsimp [chem]
          rw [hχ_abs, abs_of_nonneg (abs_nonneg p.χ)]
          ring
  have hpow_alpha_raw :
      (lowerBarrierRaw kappa kappaTilde D x) ^ (p.m + p.γ - 1) =
        (lowerBarrierRaw kappa kappaTilde D x) ^ p.α := by
    rw [hcond.hα_eq]
  have hop :
      paperWaveOperator p c (q t) W x =
        lin + chem - vBad - (1 - |p.χ|) * logistic := by
    rw [hWdef]
    rw [paperWaveOperator_lowerBarrierRaw_eq_of_kappa_speed p (q t) x
      (ne_of_gt hcond.hκ0) hcond.hc]
    dsimp [lin, chem, vBad, logistic]
    rw [hVdef, hWdef, hχ_abs, hpow_alpha_raw,
      abs_of_nonneg (abs_nonneg p.χ)]
    ring_nf
  have hbad_eq :
      paperLemma42PositiveBadTerm p (q t) W x =
        (1 - |p.χ|) * logistic + derivBad + vBad := by
    dsimp [paperLemma42PositiveBadTerm, logistic, derivBad, vBad]
    rw [hVdef]
    ring
  have hop_lower :
      lin - paperLemma42PositiveBadTerm p (q t) W x ≤
        paperWaveOperator p c (q t) W x := by
    rw [hbad_eq, hop]
    nlinarith [hchem_lower]
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
    _ ≤ lin - paperLemma42PositiveBadTerm p (q t) W x :=
      sub_le_sub_left hbad lin
    _ ≤ paperWaveOperator p c (q t) W x := hop_lower

/-! ## The positive constant branch at the actual trap height -/

theorem scaledUpperBarrier_add_log_div_eq_upperBarrier
    {kappa Q : ℝ} (hkappa : 0 < kappa) (hQ : 0 < Q) (x : ℝ) :
    scaledUpperBarrier kappa Q (x + Real.log Q / kappa) =
      upperBarrier kappa Q x := by
  unfold scaledUpperBarrier upperBarrier
  congr 1
  have harg :
      -kappa * (x + Real.log Q / kappa) =
        -kappa * x - Real.log Q := by
    field_simp [ne_of_gt hkappa]
    ring
  rw [harg, Real.exp_sub, Real.exp_log hQ]
  field_simp [ne_of_gt hQ]

/-- Translation covariance with independently translated frozen profile and
test profile. -/
theorem paperWaveOperator_comp_add_const
    (p : CMParams) {c : ℝ} {u W : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu0 : ∀ x, 0 ≤ u x) (a x : ℝ) :
    paperWaveOperator p c (fun y => u (y + a)) (fun y => W (y + a)) x =
      paperWaveOperator p c u W (x + a) := by
  unfold paperWaveOperator
  simp only
  rw [congrFun (iteratedDeriv_comp_add_const 2 W a) x,
    deriv_comp_add_const W a x,
    frozenElliptic_comp_add_const p hu hu0 a x,
    frozenElliptic_deriv_comp_add_const p hu hu0 a x]

theorem InTimeWaveTrapSet.shifted_slice_inWaveTrapSet
    {kappa Q T t : ℝ} {q : ℝ → ℝ → ℝ}
    (hkappa : 0 < kappa) (hQ : 0 < Q)
    (htrap : InTimeWaveTrapSet kappa Q T q)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    InWaveTrapSet kappa Q
      (fun x => q t (x + Real.log Q / kappa)) := by
  constructor
  · exact isCUnifBdd_comp_add_const (htrap.slice_cunif ht)
      (Real.log Q / kappa)
  · intro x
    constructor
    · exact htrap.nonneg ht _
    · calc
        q t (x + Real.log Q / kappa) ≤
            scaledUpperBarrier kappa Q
              (x + Real.log Q / kappa) := htrap.le_scaledUpperBarrier ht _
        _ = upperBarrier kappa Q x :=
          scaledUpperBarrier_add_log_div_eq_upperBarrier hkappa hQ x

/-- The general-height constant ledger on a scaled trap slice.  Its proof
uses `paperWaveOperator_const_subsolution_nonneg_pos_trap` at height `Q`. -/
theorem paperWaveOperator_const_subsolution_nonneg_pos_scaled
    (p : CMParams) {Q T c kappa d t : ℝ}
    (hχ0 : 0 ≤ p.χ) (hχ1 : p.χ < 1)
    (hα : p.α = p.m + p.γ - 1)
    (hkappa : 0 < kappa) (hQ : 0 < Q)
    (hQχ : p.χ * Q ^ p.γ < 1)
    (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hdcap : (1 - p.χ) * d ≤ (1 - p.χ * Q ^ p.γ) / 2)
    {q : ℝ → ℝ → ℝ} (htrap : InTimeWaveTrapSet kappa Q T q)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ x, 0 ≤ paperWaveOperator p c (q t) (fun _ => d) x := by
  let a : ℝ := Real.log Q / kappa
  let qshift : ℝ → ℝ := fun y => q t (y + a)
  have hshift : InWaveTrapSet kappa Q qshift := by
    simpa only [qshift, a] using
      htrap.shifted_slice_inWaveTrapSet hkappa hQ ht
  have hconst := paperWaveOperator_const_subsolution_nonneg_pos_trap
    p (c := c) hχ0 hχ1 hα hQ hQχ hd0 hd1 hdcap hshift
  intro x
  have hs := hconst (x - a)
  have hcov := paperWaveOperator_comp_add_const p
    (c := c) (u := q t) (W := fun _ : ℝ => d)
    (htrap.slice_cunif ht) (fun y => htrap.nonneg ht y) a (x - a)
  rw [hcov] at hs
  simpa only [sub_add_cancel] using hs

/-! ## Patched positive lower barrier -/

theorem paperWaveOperator_lowerBarrierPlateau_nonneg_chiPos_scaled_away
    (p : CMParams) {Q T c kappa kappaTilde D t x : ℝ}
    (hcond : PositivePaperLemma42ExactConditions
      p c kappa kappaTilde 1)
    (hQ : 1 ≤ Q) (hQχ : p.χ * Q ^ p.γ < 1)
    (hD : paperScaledDMin p Q kappa kappaTilde c < D)
    (hD1 : 1 ≤ D)
    (hplateau : ∀ y, lowerBarrierPlateau kappa kappaTilde D y ≤
      chiPosTrapPlateauFloor p Q)
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
    have hd : d ≤ chiPosTrapPlateauFloor p Q := by
      simpa [d, lowerBarrierPlateau_eq_const_of_le
        (le_refl (lowerBarrierXPlus kappa kappaTilde D))] using
          hplateau (lowerBarrierXPlus kappa kappaTilde D)
    have hχ1 : p.χ < 1 := by linarith [hcond.chi_lt_half]
    have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
    have hconst := paperWaveOperator_const_subsolution_nonneg_pos_scaled
      p (c := c) hcond.hχ_nonneg hχ1 hcond.hα_eq hcond.hκ0 hQpos hQχ hd0
        (hd.trans (chiPosTrapPlateauFloor_le_one p Q))
        (chiPosTrapPlateauFloor_cap p hχ1 hd) htrap ht x
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
    have hraw := paperWaveOperator_lowerBarrierRaw_nonneg_chiPos_scaled
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

/-! ## One-window comparison and propagation -/

/-- A positive lower plateau initially below a canonical restart remains
below it throughout one closed positive-sensitivity window. -/
theorem
    wholeLineCauchyGlobal_coMovingRestart_ge_lowerBarrierPlateau_chiPos_scaled
    (p : CMParams) (hceiling : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {c t₀ T kappa kappaTilde D Q : ℝ}
    (ht₀ : 0 < t₀) (hT : 0 < T)
    (hcond : PositivePaperLemma42ExactConditions
      p c kappa kappaTilde 1)
    (hQ : 1 ≤ Q) (hQχ : p.χ * Q ^ p.γ < 1)
    (hD : paperScaledDMin p Q kappa kappaTilde c < D)
    (hD1 : 1 ≤ D)
    (hplateau : ∀ x, lowerBarrierPlateau kappa kappaTilde D x ≤
      chiPosTrapPlateauFloor p Q)
    (htrap : InTimeWaveTrapSet kappa Q T (fun t x =>
      wholeLineCauchyGlobalU p u₀ (t₀ + t)
        (x + c * (t₀ + t))))
    (hinit : ∀ x, lowerBarrierPlateau kappa kappaTilde D x ≤
      wholeLineCauchyGlobalU p u₀ t₀ (x + c * t₀)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      lowerBarrierPlateau kappa kappaTilde D x ≤
        wholeLineCauchyGlobalU p u₀ (t₀ + t)
          (x + c * (t₀ + t)) := by
  let A : ℝ → ℝ := lowerBarrierPlateau kappa kappaTilde D
  let w : ℝ → ℝ → ℝ := fun t x =>
    wholeLineCauchyGlobalU p u₀ (t₀ + t)
      (x + c * (t₀ + t))
  let tau : ℝ → ℝ := fun t => max t 0
  let we : ℝ → ℝ → ℝ := fun t x => w (tau t) x
  let C0 : ℝ :=
    reactionLip p.α Q + |p.χ| * (Q ^ p.γ) * rpowLip p.m Q +
      |p.χ| * rpowLip (p.m + p.γ) Q
  let C : ℝ := C0 +
    |p.χ| * p.m * (Q ^ p.γ) * kappaTilde * p.m *
      Q ^ (p.m - 1)
  let E : ℝ := 1 + |c| +
    |p.χ| * p.m * (Q ^ p.γ) * Q ^ (p.m - 1)
  let X : ℝ := lowerBarrierXPlus kappa kappaTilde D
  have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hgap : 0 < kappaTilde - kappa := sub_pos.mpr hcond.hgap
  have hkappaTilde0 : 0 ≤ kappaTilde := by
    linarith [hcond.hκ0, hcond.hgap]
  have hmg : 1 ≤ p.m + p.γ := by
    linarith [p.hm, p.hγ]
  have hC0_nonneg : 0 ≤ C0 := by
    dsimp only [C0]
    have hreact : 0 ≤ reactionLip p.α Q :=
      reactionLip_nonneg p.hα hQ0
    have hLm : 0 ≤ rpowLip p.m Q := rpowLip_nonneg p.hm hQ0
    have hLmg : 0 ≤ rpowLip (p.m + p.γ) Q :=
      rpowLip_nonneg hmg hQ0
    positivity
  have hcross_nonneg :
      0 ≤ |p.χ| * p.m * (Q ^ p.γ) * kappaTilde * p.m *
        Q ^ (p.m - 1) := by
    have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg hC0_nonneg hcross_nonneg
  have hE_nonneg : 0 ≤ E := by
    dsimp only [E]
    have hm0 : 0 ≤ p.m := le_trans zero_le_one p.hm
    positivity
  have hA_mem : ∀ x, A x ∈ Set.Icc (0 : ℝ) Q := by
    intro x
    constructor
    · exact (lowerBarrierPlateau_pos hcond.hκ0 hgap hDpos x).le
    · exact (hplateau x).trans
        ((chiPosTrapPlateauFloor_le_one p Q).trans hQ)
  have htau_eq : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) T → tau t = t := by
    intro t ht
    exact max_eq_left ht.1
  have hwe_eq : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) T → we t = w t := by
    intro t ht
    funext x
    simp only [we, htau_eq ht]
  have hwe_cont : Continuous (fun q : ℝ × ℝ => we q.1 q.2) := by
    rw [continuous_iff_continuousAt]
    intro q
    have hphys : 0 < t₀ + tau q.1 := by
      have htau0 : 0 ≤ tau q.1 := by
        dsimp only [tau]
        exact le_max_right _ _
      linarith
    have hjoint := wholeLineCauchyGlobalU_joint_hasFDerivAt_positive
      p hceiling u₀ hu₀ hphys
        (x := q.2 + c * (t₀ + tau q.1))
    have hmap : ContinuousAt
        (fun r : ℝ × ℝ =>
          (t₀ + tau r.1, r.2 + c * (t₀ + tau r.1))) q := by
      dsimp only [tau]
      fun_prop
    simpa [we, w, Function.comp_def] using
      hjoint.continuousAt.comp
        (f := fun r : ℝ × ℝ =>
          (t₀ + tau r.1, r.2 + c * (t₀ + tau r.1))) hmap
  have hdiff_cont : Continuous (fun q : ℝ × ℝ =>
      A q.2 - we q.1 q.2) := by
    exact ((lowerBarrierPlateau_continuous
      kappa kappaTilde D).comp continuous_snd).sub hwe_cont
  have htimeOp : ∀ ⦃t x : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      HasDerivAt (fun s : ℝ => we s x)
        (paperWaveOperator p c (we t) (we t) x) t := by
    intro t x ht
    have hphys : 0 < t₀ + t := by linarith [ht₀, ht.1]
    have hraw :=
      wholeLineCauchyGlobal_coMovingRestart_hasDerivAt_paperWaveOperator
        p hceiling u₀ hu₀ c t₀ hphys x
    have hev : (fun s : ℝ => we s x) =ᶠ[𝓝 t]
        fun s => w s x := by
      filter_upwards [Ioi_mem_nhds ht.1] with s hs
      change 0 < s at hs
      simp only [we, tau, max_eq_left hs.le]
    have hcongr := hraw.congr_of_eventuallyEq hev
    rw [hwe_eq ⟨ht.1.le, ht.2⟩]
    simpa only [w] using hcongr
  have hspace : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) T →
      ContDiff ℝ 2 (we t) := by
    intro t ht
    have hphys : 0 < t₀ + t := by linarith [ht₀, ht.1]
    rw [hwe_eq ⟨ht.1.le, ht.2⟩]
    exact wholeLineCauchyGlobal_coMovingRestart_contDiff_two
      p hceiling u₀ hu₀ c t₀ hphys
  have hcomparison :=
    stationary_C1splice_le_of_approx_contact_parabolic_comparison
      (T := T) (B := Q) (C := C) (E := E) (X := X)
      (A := A) (u := we) hT hC_nonneg hE_nonneg
      (by
        intro x hx
        dsimp only [A, X]
        rw [lowerBarrierPlateau_eq_const_of_le hx,
          lowerBarrierPlateau_eq_const_of_le le_rfl])
      (by
        dsimp only [A, X]
        exact lowerBarrierPlateau_hasDerivAt_xplus
          hcond.hκ0 hgap hDpos)
      (by
        intro x hx
        exact lowerBarrierPlateau_contDiffAt_two_of_ne_xplus hx)
      hdiff_cont
      (by
        intro t ht x
        rw [hwe_eq ht, abs_le]
        have hwt0 : 0 ≤ w t x := htrap.nonneg ht x
        have hwtQ : w t x ≤ Q := htrap.le_M ht x
        have hAx := hA_mem x
        constructor
        · linarith [hAx.1, hwtQ]
        · linarith [hAx.2, hwt0])
      (by
        intro x
        rw [hwe_eq (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) T from
          ⟨le_rfl, hT.le⟩)]
        simpa only [A, w, zero_add, add_zero] using hinit x)
      hspace
      (by
        intro t x ht
        exact ((hasDerivAt_const t (A x)).sub
          (htimeOp ht)).differentiableAt.hasDerivAt)
      (by
        intro eta heta t x ht hx hcontact hslopeRaw hsecondRaw
        have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
        have hslice : we t = w t := hwe_eq htIcc
        have hqC : IsCUnifBdd (we t) := by
          rw [hslice]
          exact htrap.slice_cunif htIcc
        have hqQ : ∀ y, we t y ∈ Set.Icc (0 : ℝ) Q := by
          intro y
          rw [hslice]
          exact ⟨htrap.nonneg htIcc y, htrap.le_M htIcc y⟩
        have hcontact' : we t x ≤ A x := by linarith
        have hA2 : ContDiffAt ℝ 2 A x :=
          lowerBarrierPlateau_contDiffAt_two_of_ne_xplus hx
        have hwe2 : ContDiff ℝ 2 (we t) := hspace ht
        have hslope : |deriv A x - deriv (we t) x| ≤ eta := by
          have heq : deriv (fun y => A y - we t y) x =
              deriv A x - deriv (we t) x :=
            deriv_sub (hA2.differentiableAt (by norm_num))
              (hwe2.differentiable (by norm_num) x)
          rw [heq] at hslopeRaw
          exact hslopeRaw.le
        have hsecond : iteratedDeriv 2 A x -
            iteratedDeriv 2 (we t) x ≤ eta := by
          have heq : deriv (deriv (fun y => A y - we t y)) x =
              iteratedDeriv 2 A x - iteratedDeriv 2 (we t) x := by
            calc
              deriv (deriv (fun y => A y - we t y)) x =
                  iteratedDeriv 2 (fun y => A y - we t y) x := by
                simp [iteratedDeriv_succ, iteratedDeriv_zero]
              _ = iteratedDeriv 2 A x - iteratedDeriv 2 (we t) x :=
                iteratedDeriv_fun_sub hA2 hwe2.contDiffAt
          rw [heq] at hsecondRaw
          exact hsecondRaw.le
        have hop :=
          paperWaveOperator_lowerBarrierPlateau_diff_le_of_approx_contact_abs
            p (c := c) (Q := Q) (M := Q) (kappa := kappa)
            (kappaTilde := kappaTilde) (D := D) (eta := eta)
            (x := x) (q := we t) hQ0 hQpos hqC hqQ hcond.hκ0
            hgap hDpos hx (hA_mem x).2 hcontact' hsecond hslope
        have hsubActual :=
          paperWaveOperator_lowerBarrierPlateau_nonneg_chiPos_scaled_away
            p hcond hQ hQχ hD hD1 hplateau htrap htIcc hx
        have hsub : 0 ≤ paperWaveOperator p c (we t) A x := by
          simpa only [A, hslice] using hsubActual
        have hop' : paperWaveOperator p c (we t) A x -
              paperWaveOperator p c (we t) (we t) x ≤
            C * (A x - we t x) + E * eta := by
          simpa only [A, C, C0, E] using hop
        have htimeDeriv := (hasDerivAt_const t (A x)).sub
          (htimeOp (t := t) (x := x) ht)
        have htimeEq : deriv (fun s : ℝ => A x - we s x) t =
            -paperWaveOperator p c (we t) (we t) x := by
          simpa using htimeDeriv.deriv
        rw [htimeEq]
        linarith [hsub, hop'])
      (by
        intro eta heta t ht hcontact hqx hsecondRaw
        have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
        have hslice : we t = w t := hwe_eq htIcc
        have hqC : IsCUnifBdd (we t) := by
          rw [hslice]
          exact htrap.slice_cunif htIcc
        have hqQ : ∀ y, we t y ∈ Set.Icc (0 : ℝ) Q := by
          intro y
          rw [hslice]
          exact ⟨htrap.nonneg htIcc y, htrap.le_M htIcc y⟩
        have hcontact' : we t X ≤ A X := by linarith
        have hwe2 : ContDiff ℝ 2 (we t) := hspace ht
        have hsecond : -iteratedDeriv 2 (we t) X ≤ eta := by
          have heq : iteratedDeriv 2 (we t) X =
              deriv (deriv (we t)) X := by
            simp [iteratedDeriv_succ, iteratedDeriv_zero]
          rw [heq]
          exact hsecondRaw.le
        have hop0 := paperWaveOperator_const_diff_le_of_approx_contact_abs
          p (c := c) (Q := Q) (M := Q) (d := A X) (eta := eta)
          (x := X) (q := we t) hQ0 hQpos heta.le hqC hqQ
          (hA_mem X) hcontact' hqx hsecond
        have hop0' :
            paperWaveOperator p c (we t) (fun _ : ℝ => A X) X -
                paperWaveOperator p c (we t) (we t) X ≤
              C0 * (A X - we t X) + E * eta := by
          simpa only [C0, E] using hop0
        have hC0C : C0 ≤ C := by
          dsimp only [C]
          exact le_add_of_nonneg_right hcross_nonneg
        have hgap0 : 0 ≤ A X - we t X := sub_nonneg.mpr hcontact'
        have hop : paperWaveOperator p c (we t) (fun _ : ℝ => A X) X -
              paperWaveOperator p c (we t) (we t) X ≤
            C * (A X - we t X) + E * eta := by
          exact hop0'.trans (add_le_add
            (mul_le_mul_of_nonneg_right hC0C hgap0) le_rfl)
        have hdpos : 0 < A X :=
          lowerBarrierPlateau_pos hcond.hκ0 hgap hDpos X
        have hχ1 : p.χ < 1 := by linarith [hcond.chi_lt_half]
        have hsub : 0 ≤
            paperWaveOperator p c (we t) (fun _ : ℝ => A X) X := by
          have hsubActual := paperWaveOperator_const_subsolution_nonneg_pos_scaled
            p (c := c) hcond.hχ_nonneg hχ1 hcond.hα_eq hcond.hκ0
              hQpos hQχ hdpos
              ((hplateau X).trans (chiPosTrapPlateauFloor_le_one p Q))
              (chiPosTrapPlateauFloor_cap p hχ1 (hplateau X))
              htrap htIcc X
          simpa only [hslice] using hsubActual
        have htimeDeriv := (hasDerivAt_const t (A X)).sub
          (htimeOp (t := t) (x := X) ht)
        have htimeEq : deriv (fun s : ℝ => A X - we s X) t =
            -paperWaveOperator p c (we t) (we t) X := by
          simpa using htimeDeriv.deriv
        rw [htimeEq]
        linarith [hsub, hop])
  intro t ht x
  have hresult := hcomparison t ht x
  rw [hwe_eq ht] at hresult
  simpa only [A, w] using hresult

/-- Closed-window induction propagates one positive-sensitivity plateau over
all late canonical windows. -/
theorem
    wholeLineCauchyGlobal_ge_lowerBarrierPlateau_on_all_late_windows_chiPos
    (p : CMParams) (hceiling : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {N : ℕ} {c kappa kappaTilde D Q : ℝ}
    (hcond : PositivePaperLemma42ExactConditions
      p c kappa kappaTilde 1)
    (hQ : 1 ≤ Q) (hQχ : p.χ * Q ^ p.γ < 1)
    (hD : paperScaledDMin p Q kappa kappaTilde c < D)
    (hD1 : 1 ≤ D)
    (hplateau : ∀ x, lowerBarrierPlateau kappa kappaTilde D x ≤
      chiPosTrapPlateauFloor p Q)
    (htrap : ∀ n : ℕ, N ≤ n →
      InTimeWaveTrapSet kappa Q
        (wholeLineCauchyGlobalStep p u₀)
        (fun r x => wholeLineCauchyGlobalU p u₀
          (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r)
          (x + c * (((n : ℝ) + 1) *
            wholeLineCauchyGlobalStep p u₀ + r))))
    (hseed : ∀ x, lowerBarrierPlateau kappa kappaTilde D x ≤
      wholeLineCauchyGlobalU p u₀
        (((N : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀)
        (x + c * (((N : ℝ) + 1) *
          wholeLineCauchyGlobalStep p u₀))) :
    ∀ n : ℕ, N ≤ n →
      ∀ r ∈ Set.Icc (0 : ℝ) (wholeLineCauchyGlobalStep p u₀), ∀ x,
        lowerBarrierPlateau kappa kappaTilde D x ≤
          wholeLineCauchyGlobalU p u₀
            (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r)
            (x + c * (((n : ℝ) + 1) *
              wholeLineCauchyGlobalStep p u₀ + r)) := by
  let step := wholeLineCauchyGlobalStep p u₀
  have hstep : 0 < step := by
    simpa only [step] using wholeLineCauchyGlobalStep_pos p u₀
  have hind : ∀ k : ℕ,
      ∀ r ∈ Set.Icc (0 : ℝ) step, ∀ x,
        lowerBarrierPlateau kappa kappaTilde D x ≤
          wholeLineCauchyGlobalU p u₀
            ((((N + k : ℕ) : ℝ) + 1) * step + r)
            (x + c * ((((N + k : ℕ) : ℝ) + 1) * step + r)) := by
    intro k
    induction k with
    | zero =>
        have ht₀ : 0 < ((N : ℝ) + 1) * step := by
          have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
          positivity
        have hwindow :=
          wholeLineCauchyGlobal_coMovingRestart_ge_lowerBarrierPlateau_chiPos_scaled
            p hceiling u₀ hu₀ ht₀ hstep hcond hQ hQχ hD hD1 hplateau
              (by simpa only [step] using htrap N le_rfl)
              (by simpa only [step] using hseed)
        simpa only [Nat.add_zero, step] using hwindow
    | succ k ih =>
        have hNkSucc : N ≤ N + k.succ := Nat.le_add_right N k.succ
        have hseam : ∀ x, lowerBarrierPlateau kappa kappaTilde D x ≤
            wholeLineCauchyGlobalU p u₀
              ((((N + k.succ : ℕ) : ℝ) + 1) * step)
              (x + c * ((((N + k.succ : ℕ) : ℝ) + 1) * step)) := by
          intro x
          have hend := ih step ⟨hstep.le, le_rfl⟩ x
          have htime :
              ((((N + k : ℕ) : ℝ) + 1) * step + step) =
                (((((N + k.succ : ℕ) : ℝ) + 1) * step)) := by
            push_cast
            ring
          simpa only [htime] using hend
        have ht₀ : 0 < (((N + k.succ : ℕ) : ℝ) + 1) * step := by
          have hNk0 : 0 ≤ ((N + k.succ : ℕ) : ℝ) := Nat.cast_nonneg _
          positivity
        have hwindow :=
          wholeLineCauchyGlobal_coMovingRestart_ge_lowerBarrierPlateau_chiPos_scaled
            p hceiling u₀ hu₀ ht₀ hstep hcond hQ hQχ hD hD1 hplateau
              (by simpa only [step] using htrap (N + k.succ) hNkSucc)
              hseam
        simpa only [step] using hwindow
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa only [step] using hind k

/-! ## A compatible positive-sensitivity profile seed -/

/-- Profile-only seed selection with the actual positive trap-height cap.
The auxiliary parameter is used solely to reuse the sign-free geometric seed
constructor and is discarded before the positive paper conditions are built. -/
theorem exists_chiPos_compatible_lowerBarrierPlateau_seed_of_profile_bounds
    (p : CMParams) (Bfun : ℝ → ℝ)
    {c Q kappa kappaOne eta cap C : ℝ} {w U : ℝ → ℝ}
    (hkappa : 0 < kappa) (hkappa_one : kappa < 1)
    (hkappaOne : kappa < kappaOne) (heta : kappa < eta)
    (hcap : kappa < cap)
    (_hQ : 1 ≤ Q) (hQtrap : p.χ * Q ^ p.γ < 1)
    (hcapRange :
      cap ≤ min ((1 + p.α) * kappa)
        (min (p.m * kappa + 1 / 2) 1))
    (hc : c = kappa + kappa⁻¹)
    (hχ0 : 0 ≤ p.χ)
    (hχsmall : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hα : p.α = p.m + p.γ - 1)
    (hwcont : Continuous w) (hwpos : ∀ x, 0 < w x)
    (hwleft : StrictlyPositiveAtLeft w)
    (hC : 0 ≤ C)
    (henv : ∀ x, |w x - U x| ≤ C * Real.exp (-eta * x))
    (htail : HasWaveRightTailAsymptotic c kappaOne U) :
    ∃ kappaTilde D : ℝ,
      kappa < kappaTilde ∧
      kappaTilde < kappaOne ∧
      kappaTilde < eta ∧
      kappaTilde < cap ∧
      kappaTilde < 2 * kappa ∧
      PositivePaperLemma42ExactConditions
        p c kappa kappaTilde 1 ∧
      1 ≤ D ∧
      Bfun kappaTilde < D ∧
      (∀ x, lowerBarrierPlateau kappa kappaTilde D x ≤
        chiPosTrapPlateauFloor p Q) ∧
      ∀ x, lowerBarrierPlateau kappa kappaTilde D x ≤ w x := by
  have hχhalf : p.χ < 1 / 2 :=
    hχsmall.trans_le (min_le_left _ _)
  have hχ1 : p.χ < 1 := by linarith
  let dcap : ℝ := chiPosTrapPlateauFloor p Q
  have hdcap : 0 < dcap := by
    simpa only [dcap] using
      chiPosTrapPlateauFloor_pos p hχ1 hQtrap
  let pAux : CMParams := {p with χ := -(1 / dcap)}
  have hauxchi : pAux.χ ≤ 0 := by
    dsimp [pAux]
    exact neg_nonpos.mpr (one_div_nonneg.mpr hdcap.le)
  obtain ⟨kappaTilde, D, hkappaTilde, hkappaTildeOne,
      hkappaTildeEta, hkappaTildeCap, hkappaTildeTwo,
      _hcondAux, hD1, _hDaux, hBfun, hthresholdAux, hseed⟩ :=
    exists_chiNonpos_compatible_lowerBarrierPlateau_seed_of_profile_bounds
      pAux Bfun hkappa hkappa_one hkappaOne heta hcap
        (Q := 1) le_rfl
        (by simpa only [pAux] using hcapRange) hc hauxchi
        (by simpa only [pAux] using hα.le)
        hwcont hwpos hwleft hC henv htail
  have hcond : PositivePaperLemma42ExactConditions
      p c kappa kappaTilde 1 :=
    { hκ0 := hkappa
      hκ1 := hkappa_one
      hgap := hkappaTilde
      hrange := hkappaTildeCap.le.trans hcapRange
      hM := le_rfl
      hc := hc
      hχ_nonneg := hχ0
      hχ_small := hχsmall
      hα_eq := hα }
  have hauxFrac : 1 / (1 + |pAux.χ|) ≤ dcap := by
    dsimp [pAux]
    rw [abs_neg, abs_of_pos (one_div_pos.mpr hdcap)]
    rw [div_le_iff₀ (by positivity : 0 < 1 + 1 / dcap)]
    field_simp [ne_of_gt hdcap]
    linarith
  have hplateau : ∀ x,
      lowerBarrierPlateau kappa kappaTilde D x ≤ dcap := by
    intro x
    exact (hthresholdAux x).trans
      ((min_le_left _ _).trans hauxFrac)
  exact ⟨kappaTilde, D, hkappaTilde, hkappaTildeOne,
    hkappaTildeEta, hkappaTildeCap, hkappaTildeTwo, hcond, hD1,
    hBfun, by simpa only [dcap] using hplateau, hseed⟩

/-- At any prescribed positive time, the positive-sensitivity canonical orbit
lies above a plateau compatible with the actual scaled-trap margin. -/
theorem
    wholeLineCauchyGlobal_exists_compatible_lowerBarrierPlateau_seed_at_time_chi_pos
    (p : CMParams) (hstable : StableWaveParameterRegime p)
    (hchi : 0 < p.χ) (hchi_half : p.χ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1)
    (Bfun : ℝ → ℝ) {Q c kappaOne eta cap t₀ : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hQ : 1 ≤ Q) (hQtrap : p.χ * Q ^ p.γ < 1)
    (hkappaOne : kappa c < kappaOne) (heta : kappa c < eta)
    (heta_one : eta < 1) (hcap : kappa c < cap)
    (hcapRange :
      cap ≤ min ((1 + p.α) * kappa c)
        (min (p.m * kappa c + 1 / 2) 1))
    (ht₀ : 0 < t₀)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (htail : HasWaveRightTailAsymptotic c kappaOne U)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hu₀left : StrictlyPositiveAtLeft u₀.1)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U) :
    ∃ kappaTilde D : ℝ,
      kappa c < kappaTilde ∧
      kappaTilde < kappaOne ∧
      kappaTilde < eta ∧
      kappaTilde < cap ∧
      kappaTilde < 2 * kappa c ∧
      PositivePaperLemma42ExactConditions
        p c (kappa c) kappaTilde 1 ∧
      1 ≤ D ∧
      Bfun kappaTilde < D ∧
      (∀ x, lowerBarrierPlateau (kappa c) kappaTilde D x ≤
        chiPosTrapPlateauFloor p Q) ∧
      ∀ x, lowerBarrierPlateau (kappa c) kappaTilde D x ≤
        coMovingPath c (wholeLineCauchyGlobalU p u₀) t₀ x := by
  have hceiling : WholeLineCauchyCeilingRegime p :=
    hstable.toWholeLineCauchyCeilingRegime
  have hbaseline : stabilitySpeedBaseline p ≤
      paper5CorrectedCStarStar p p.χ :=
    paper5CorrectedCStarStar_baseline_le p
  have hc_two : 2 < c :=
    two_lt_of_stabilitySpeedBaseline_lt hbaseline hc
  have hkappa : 0 < kappa c := kappa_pos_of_two_lt hc_two
  have hkappa_one : kappa c < 1 := kappa_lt_one_of_two_lt hc_two
  have hcκ : c = kappa c + (kappa c)⁻¹ :=
    (kappa_add_inv_eq_of_two_lt hc_two).symm
  have heta_pos : 0 < eta := hkappa.trans heta
  have hbranch := hstable.positive_branch_of_chi_nonneg hchi.le
  have hχsmall : p.χ < min (1 / 2 : ℝ) (chiStar p) :=
    lt_min hchi_half hbranch.1
  have hMChi : MChi p ≤ wholeLineCauchyGlobalClamp p u₀ := by
    have hparam : wholeLineCauchyParameterCeiling p = MChi p := by
      unfold wholeLineCauchyParameterCeiling
      rw [if_neg (not_lt.mpr (le_of_eq hbranch.2))]
    have hle : MChi p ≤ wholeLineCauchyStableCeiling p u₀ := by
      rw [← hparam]
      exact le_max_right _ _
    unfold wholeLineCauchyGlobalClamp
    linarith
  have hs : Paper5WaveStaticNaturalData p c U V :=
    paper5WaveStaticNaturalData_of_wave
      p (ne_of_gt hchi) hc hTW hbound hreg
  have hu2 : ContDiff ℝ 2
      (coMovingPath c (wholeLineCauchyGlobalU p u₀) t₀) :=
    wholeLineCauchyGlobalU_coMoving_contDiff_two_positive
      p hceiling u₀ hu₀ ht₀
  have hW2 : Integrable (fun x =>
      paper5WeightedPopulation eta
        (coMovingPath c (wholeLineCauchyGlobalU p u₀)) U t₀ x ^ 2) := by
    apply paper5WeightedPopulation_sq_integrable_of_weighted_difference
    exact
      wholeLineCauchyGlobal_fullWeightedL2_integrable_wave_chi_pos_of_initialCloseness
        (D := paper5ConcreteLu p)
        (E := paper5WaveSecondDerivativeBound p c)
        (Kflux := paper5WaveFluxBound p)
        (FD := paper5WaveFluxDerivativeBound p)
        (B := paper5WaveShiftedReactionBound p)
        p hstable hchi u₀ ht₀ heta_pos heta_one hTW hbound hreg hs.hD
          hs.hFD hs.hB hs.hUd hs.hUdd hs.hUddcont hs.hflux hs.hfluxd
          hs.hflux_has hs.hfluxd_cont hs.hreact hs.hreact_cont
          hs.hgrad_int hinitial
  have hrestart : Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
      |(wholeLineCauchyGlobalPreferredTranslatedDatum p u₀ c t₀).1 x -
        U x| ^ 2) := by
    exact
      wholeLineCauchyGlobalPreferredTranslatedDatum_fullWeightedL2_integrable_wave
        (D := paper5ConcreteLu p)
        (E := paper5WaveSecondDerivativeBound p c)
        (Kflux := paper5WaveFluxBound p)
        (FD := paper5WaveFluxDerivativeBound p)
        (B := paper5WaveShiftedReactionBound p)
        p u₀ (t := t₀) heta_pos heta_one hTW hbound hreg hMChi hs.hD
          hs.hFD hs.hB hs.hUd hs.hUdd hs.hUddcont hs.hflux hs.hfluxd
          hs.hflux_has hs.hfluxd_cont hs.hreact hs.hreact_cont
          hs.hgrad_int
          (by simpa only [WeightedL2InitialCloseness] using hinitial)
  have hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta
        (coMovingPath c (wholeLineCauchyGlobalU p u₀)) U t₀ x ^ 2) := by
    exact
      paper5WeightedPopulationX_sq_integrable_global_positive
        (Blog := 1) (D := paper5ConcreteLu p)
        (E := paper5WaveSecondDerivativeBound p c)
        (Kflux := paper5WaveFluxBound p)
        (FD := paper5WaveFluxDerivativeBound p)
        (B := paper5WaveShiftedReactionBound p)
        p hceiling u₀ hu₀ ht₀ hs.hBlog heta_pos heta_one hTW hbound
          hreg hMChi hs.hlog hs.hD hs.hFD hs.hB hs.hUd hs.hUdd
          hs.hUddcont hs.hflux hs.hfluxd hs.hflux_has hs.hfluxd_cont
          hs.hreact hs.hreact_cont hs.hgrad_int hrestart
  obtain ⟨C, hC, henv⟩ :=
    exists_weightedDifference_pointwise_envelope_of_H1
      hu2 (hreg.U_contDiff_two hTW) hW2 hWx2
  have hwpos : ∀ x,
      0 < coMovingPath c (wholeLineCauchyGlobalU p u₀) t₀ x := by
    intro x
    exact wholeLineCauchyGlobal_pos_of_posAtBot
      p hceiling u₀ hu₀ hu₀left ht₀ (x + c * t₀)
  let n := wholeLineCauchyGlobalIndex p u₀ t₀
  let q := wholeLineCauchyGlobalLocalTime p u₀ t₀
  let z : Set.Icc (0 : ℝ) (wholeLineCauchyGlobalSegmentTime p u₀) :=
    ⟨q, wholeLineCauchyGlobalLocalTime_nonneg p u₀ ht₀.le,
      (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht₀.le).le⟩
  have hglobalLeft : StrictlyPositiveAtLeft
      (wholeLineCauchyGlobalU p u₀ t₀) := by
    have hsegLeft :=
      (wholeLineCauchyGlobalDatum_segment_pos_and_left_of_posAtBot
        p hceiling u₀ hu₀ hu₀left n).2.2 z
    have heq' : wholeLineCauchyGlobalU p u₀ t₀ =
        (wholeLineCauchyGlobalSegment p u₀ n z).1 := by
      funext x
      have heq := congrArg (fun w : WholeLineBUC => w.1 x)
        (wholeLineCauchyGlobalBUC_eq_segment p u₀ ht₀.le)
      simpa [wholeLineCauchyGlobalU, n, q, z] using heq
    rw [heq']
    exact hsegLeft
  have hwleft : StrictlyPositiveAtLeft
      (coMovingPath c (wholeLineCauchyGlobalU p u₀) t₀) := by
    simpa only [coMovingPath] using hglobalLeft.shift (c * t₀)
  exact exists_chiPos_compatible_lowerBarrierPlateau_seed_of_profile_bounds
    p Bfun hkappa hkappa_one hkappaOne heta hcap hQ hQtrap hcapRange
      hcκ hchi.le hχsmall hcritical hu2.continuous hwpos hwleft hC henv
      htail

/-! ## Canonical positive-sensitivity persistence -/

/-- The canonical positive-sensitivity orbit admits one stationary positive
lower plateau on every sufficiently late closed restart window.  The same
height `Q > MChi p` is retained both in the scaled upper trap and in the
sharp condition `p.χ * Q^p.γ < 1` used by the two positive operator ledgers. -/
theorem
    wholeLineCauchyGlobal_exists_persistent_lowerBarrierPlateau_chi_pos_natural
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : 0 < p.χ) (hchi_half : p.χ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1)
    {c eta kappaOne : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hstrict : HasStrictWaveUpperTailBound p c U)
    (hkappaOne : kappa c < kappaOne)
    (_hkappaOne_one : kappaOne < 1)
    (htail : HasWaveRightTailAsymptotic c kappaOne U)
    (hroot : paper531RootMinus c
      (paper531ConcreteStabilityBudget p hregime).A
      (paper531ConcreteStabilityBudget p hregime).B < eta)
    (hetaCap : eta < stabilityWeightCap p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hu₀left : StrictlyPositiveAtLeft u₀.1)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U) :
    ∃ N : ℕ, ∃ kappaTilde D Q : ℝ,
      MChi p < Q ∧
      1 < Q ∧
      p.χ * Q ^ p.γ < 1 ∧
      kappa c < kappaTilde ∧
      kappaTilde < kappaOne ∧
      kappaTilde < eta ∧
      PositivePaperLemma42ExactConditions
        p c (kappa c) kappaTilde 1 ∧
      1 ≤ D ∧
      paperScaledDMin p Q (kappa c) kappaTilde c < D ∧
      (∀ x, lowerBarrierPlateau (kappa c) kappaTilde D x ≤
        chiPosTrapPlateauFloor p Q) ∧
      (∀ n : ℕ, N ≤ n →
        InTimeWaveTrapSet (kappa c) Q
          (wholeLineCauchyGlobalStep p u₀)
          (fun r x => wholeLineCauchyGlobalU p u₀
            (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r)
            (x + c * (((n : ℝ) + 1) *
              wholeLineCauchyGlobalStep p u₀ + r)))) ∧
      ∀ n : ℕ, N ≤ n →
        ∀ r ∈ Set.Icc (0 : ℝ) (wholeLineCauchyGlobalStep p u₀), ∀ x,
          lowerBarrierPlateau (kappa c) kappaTilde D x ≤
            wholeLineCauchyGlobalU p u₀
              (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r)
              (x + c * (((n : ℝ) + 1) *
                wholeLineCauchyGlobalStep p u₀ + r)) := by
  have hbaseline : stabilitySpeedBaseline p ≤
      paper5CorrectedCStarStar p p.χ :=
    paper5CorrectedCStarStar_baseline_le p
  have hc_two : 2 < c :=
    two_lt_of_stabilitySpeedBaseline_lt hbaseline hc
  have hkappa : 0 < kappa c := kappa_pos_of_two_lt hc_two
  have hkappa_one : kappa c < 1 := kappa_lt_one_of_two_lt hc_two
  have hkappa_eta : kappa c < eta :=
    ((paper531ConcreteStabilityBudget p hregime).kappa_le_rootMinus hc).trans_lt
      hroot
  have heta : 0 < eta := hkappa.trans hkappa_eta
  have heta_one : eta < 1 := by
    have hcap_one : stabilityWeightCap p ≤ 1 := by
      unfold stabilityWeightCap
      rw [div_le_one (by positivity)]
      exact le_add_of_nonneg_right
        (Real.rpow_nonneg (abs_nonneg _) _)
    exact hetaCap.trans_le hcap_one
  have hbound : HasWaveUpperTailBound p c U :=
    hstrict.hasWaveUpperTailBound
  obtain ⟨r, hr, hMChiQraw, hQoneraw, hQtrapraw, N, htrapraw⟩ :=
    wholeLineCauchyGlobal_exists_chiPos_plateau_window
      p hregime hchi hchi_half hcritical hc hTW hreg hbound hroot
        hetaCap u₀ hu₀ hinitial
  let Q : ℝ := MChi p + r
  have hMChiQ : MChi p < Q := by
    simpa only [Q] using hMChiQraw
  have hQone : 1 < Q := by
    simpa only [Q] using hQoneraw
  have hQ : 1 ≤ Q := hQone.le
  have hQtrap : p.χ * Q ^ p.γ < 1 := by
    simpa only [Q] using hQtrapraw
  have htrap : ∀ n : ℕ, N ≤ n →
      InTimeWaveTrapSet (kappa c) Q
        (wholeLineCauchyGlobalStep p u₀)
        (fun s x => wholeLineCauchyGlobalU p u₀
          (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + s)
          (x + c * (((n : ℝ) + 1) *
            wholeLineCauchyGlobalStep p u₀ + s))) := by
    simpa only [Q] using htrapraw
  let cap : ℝ := min ((1 + p.α) * kappa c)
    (min (p.m * kappa c + 1 / 2) 1)
  have hkappa_cap : kappa c < cap := by
    dsimp only [cap]
    apply lt_min
    · nlinarith [p.hα]
    · apply lt_min
      · nlinarith [p.hm, hkappa]
      · exact hkappa_one
  have hcapRange :
      cap ≤ min ((1 + p.α) * kappa c)
        (min (p.m * kappa c + 1 / 2) 1) := le_rfl
  let step := wholeLineCauchyGlobalStep p u₀
  have hstep : 0 < step := by
    simpa only [step] using wholeLineCauchyGlobalStep_pos p u₀
  let t₀ : ℝ := ((N : ℝ) + 1) * step
  have ht₀ : 0 < t₀ := by
    dsimp only [t₀]
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    positivity
  obtain ⟨kappaTilde, D, hkappaTilde, hkappaTildeOne,
      hkappaTildeEta, _hkappaTildeCap, _hkappaTildeTwo,
      hcond, hD1, hDscaled, hplateau, hseed⟩ :=
    wholeLineCauchyGlobal_exists_compatible_lowerBarrierPlateau_seed_at_time_chi_pos
      p hregime hchi hchi_half hcritical
      (fun kappaTilde =>
        paperScaledDMin p Q (kappa c) kappaTilde c)
      hc hQ hQtrap hkappaOne hkappa_eta heta_one hkappa_cap hcapRange
        ht₀ hTW hbound hreg htail u₀ hu₀ hu₀left hinitial
  have hseed' : ∀ x,
      lowerBarrierPlateau (kappa c) kappaTilde D x ≤
        wholeLineCauchyGlobalU p u₀
          (((N : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀)
          (x + c * (((N : ℝ) + 1) *
            wholeLineCauchyGlobalStep p u₀)) := by
    simpa only [coMovingPath, t₀, step] using hseed
  have hpersist :=
    wholeLineCauchyGlobal_ge_lowerBarrierPlateau_on_all_late_windows_chiPos
      p hregime.toWholeLineCauchyCeilingRegime u₀ hu₀ hcond hQ hQtrap
        hDscaled hD1 hplateau htrap hseed'
  exact ⟨N, kappaTilde, D, Q, hMChiQ, hQone, hQtrap,
    hkappaTilde, hkappaTildeOne, hkappaTildeEta, hcond, hD1,
    hDscaled, hplateau, htrap, hpersist⟩

section AxiomAudit

#print axioms paperWaveOperator_lowerBarrierRaw_nonneg_chiPos_scaled
#print axioms paperWaveOperator_const_subsolution_nonneg_pos_scaled
#print axioms
  paperWaveOperator_lowerBarrierPlateau_nonneg_chiPos_scaled_away
#print axioms
  wholeLineCauchyGlobal_coMovingRestart_ge_lowerBarrierPlateau_chiPos_scaled
#print axioms
  wholeLineCauchyGlobal_ge_lowerBarrierPlateau_on_all_late_windows_chiPos
#print axioms
  exists_chiPos_compatible_lowerBarrierPlateau_seed_of_profile_bounds
#print axioms
  wholeLineCauchyGlobal_exists_compatible_lowerBarrierPlateau_seed_at_time_chi_pos
#print axioms
  wholeLineCauchyGlobal_exists_persistent_lowerBarrierPlateau_chi_pos_natural

end AxiomAudit

end ShenWork.Paper1
