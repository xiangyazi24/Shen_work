import ShenWork.Paper1.WaveRotheSchauderData

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-- The paper's three-case constant in Lemma 4.2.  This is deliberately
separate from the older `subsolutionK`, whose supercritical branch is different. -/
def paperSubsolutionK (M κ κtilde m gamma : ℝ) : ℝ :=
  let prefactor := m * (κtilde + κ) + 1
  if gamma * κ = 1 then
    prefactor * (M ^ gamma + 3 / 4)
  else if gamma * κ < 1 then
    prefactor * (1 / (1 - gamma ^ 2 * κ ^ 2))
  else
    prefactor *
      ((M ^ gamma * (κ ^ 2 * gamma ^ 2 - 1) + gamma * κ) /
        (κ ^ 2 * gamma ^ 2 - 1))

def paperSpeedDenominator (c κtilde : ℝ) : ℝ :=
  c * κtilde - κtilde ^ 2 - 1

/-- The exact lower-barrier threshold `D_min` from the paper. -/
def paperDMin (χ M κ κtilde m gamma c : ℝ) : ℝ :=
  (1 + |χ| * paperSubsolutionK M κ κtilde m gamma) /
    paperSpeedDenominator c κtilde

/-- The exact hypotheses displayed in the paper for the negative-chemotaxis
lower-barrier estimate. -/
structure PaperLemma42ExactConditions
    (p : CMParams) (c κ κtilde M : ℝ) : Prop where
  hκ0 : 0 < κ
  hκ1 : κ < 1
  hgap : κ < κtilde
  hrange : κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1)
  hM : 1 ≤ M
  hc : c = κ + κ⁻¹
  hχ : p.χ ≤ 0

namespace PaperLemma42ExactConditions

theorem kappaTilde_le_one
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PaperLemma42ExactConditions p c κ κtilde M) :
    κtilde ≤ 1 := by
  exact le_trans h.hrange
    (le_trans (min_le_right _ _) (min_le_right _ _))

theorem den_pos
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PaperLemma42ExactConditions p c κ κtilde M) :
    0 < paperSpeedDenominator c κtilde := by
  simpa [paperSpeedDenominator] using
    lowerBarrierRaw_speed_denominator_pos h.hκ0 h.hκ1 h.hgap
      h.kappaTilde_le_one h.hc

end PaperLemma42ExactConditions

theorem paperSubsolutionK_eq_critical
    {M κ κtilde m gamma : ℝ} (hγκ : gamma * κ = 1) :
    paperSubsolutionK M κ κtilde m gamma =
      (m * (κtilde + κ) + 1) * (M ^ gamma + 3 / 4) := by
  simp [paperSubsolutionK, hγκ]

theorem paperSubsolutionK_eq_subcritical
    {M κ κtilde m gamma : ℝ} (hγκ : gamma * κ < 1) :
    paperSubsolutionK M κ κtilde m gamma =
      (m * (κtilde + κ) + 1) * (1 / (1 - gamma ^ 2 * κ ^ 2)) := by
  have hne : ¬ gamma * κ = 1 := ne_of_lt hγκ
  simp [paperSubsolutionK, hne, hγκ]

theorem paperSubsolutionK_eq_supercritical
    {M κ κtilde m gamma : ℝ} (hγκ : 1 < gamma * κ) :
    paperSubsolutionK M κ κtilde m gamma =
      (m * (κtilde + κ) + 1) *
        ((M ^ gamma * (κ ^ 2 * gamma ^ 2 - 1) + gamma * κ) /
          (κ ^ 2 * gamma ^ 2 - 1)) := by
  have hne : ¬ gamma * κ = 1 := ne_of_gt hγκ
  have hnlt : ¬ gamma * κ < 1 := not_lt.mpr hγκ.le
  simp [paperSubsolutionK, hne, hnlt]

theorem paperSubsolutionK_nonneg
    {M κ κtilde m gamma : ℝ}
    (hM : 0 ≤ M) (hκ : 0 ≤ κ) (hκtilde : 0 ≤ κtilde)
    (hm : 0 ≤ m) (hgamma : 0 ≤ gamma) :
    0 ≤ paperSubsolutionK M κ κtilde m gamma := by
  unfold paperSubsolutionK
  have hpref : 0 ≤ m * (κtilde + κ) + 1 := by
    have hmk : 0 ≤ m * (κtilde + κ) :=
      mul_nonneg hm (add_nonneg hκtilde hκ)
    linarith
  by_cases heq : gamma * κ = 1
  · rw [if_pos heq]
    exact mul_nonneg hpref
      (add_nonneg (Real.rpow_nonneg hM gamma) (by norm_num))
  · rw [if_neg heq]
    by_cases hlt : gamma * κ < 1
    · rw [if_pos hlt]
      have hgk_nonneg : 0 ≤ gamma * κ := mul_nonneg hgamma hκ
      have hden_pos : 0 < 1 - gamma ^ 2 * κ ^ 2 := by
        have hs : (gamma * κ) ^ 2 < 1 := by nlinarith
        nlinarith
      exact mul_nonneg hpref (one_div_pos.mpr hden_pos).le
    · rw [if_neg hlt]
      have hge : 1 ≤ gamma * κ := le_of_not_gt hlt
      have hgt : 1 < gamma * κ := by
        exact lt_of_le_of_ne hge (fun h => heq h.symm)
      have hden_pos : 0 < κ ^ 2 * gamma ^ 2 - 1 := by
        have hs : 1 < (gamma * κ) ^ 2 := by nlinarith
        nlinarith
      have hgk_nonneg : 0 ≤ gamma * κ := by linarith
      have hnum_nonneg :
          0 ≤ M ^ gamma * (κ ^ 2 * gamma ^ 2 - 1) + gamma * κ :=
        add_nonneg
          (mul_nonneg (Real.rpow_nonneg hM gamma) hden_pos.le)
          hgk_nonneg
      exact mul_nonneg hpref (div_nonneg hnum_nonneg hden_pos.le)

theorem paperSubsolutionK_nonneg_of_conditions
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PaperLemma42ExactConditions p c κ κtilde M) :
    0 ≤ paperSubsolutionK M κ κtilde p.m p.γ :=
  paperSubsolutionK_nonneg
    (le_trans zero_le_one h.hM) h.hκ0.le (le_trans h.hκ0.le h.hgap.le)
    (le_trans zero_le_one p.hm) (le_trans zero_le_one p.hγ)

theorem paperDMin_pos_of_conditions
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PaperLemma42ExactConditions p c κ κtilde M) :
    0 < paperDMin p.χ M κ κtilde p.m p.γ c := by
  unfold paperDMin
  have hnum_pos :
      0 < 1 + |p.χ| * paperSubsolutionK M κ κtilde p.m p.γ := by
    have hmul_nonneg :
        0 ≤ |p.χ| * paperSubsolutionK M κ κtilde p.m p.γ :=
      mul_nonneg (abs_nonneg p.χ) (paperSubsolutionK_nonneg_of_conditions h)
    linarith
  exact div_pos hnum_pos h.den_pos

theorem D_pos_of_paperDMin_lt
    {p : CMParams} {c κ κtilde M D : ℝ}
    (h : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D) :
    0 < D :=
  lt_trans (paperDMin_pos_of_conditions h) hD

theorem lowerBarrierRaw_pos_on_paper_region
    {p : CMParams} {c κ κtilde M D x : ℝ}
    (h : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hx : x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D)) :
    0 < lowerBarrierRaw κ κtilde D x := by
  exact lowerBarrierRaw_pos_of_xminus_lt
    (sub_pos.mpr h.hgap) (D_pos_of_paperDMin_lt h hD) hx

theorem lowerBarrierRaw_nonneg_on_paper_region
    {p : CMParams} {c κ κtilde M D x : ℝ}
    (h : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hx : x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D)) :
    0 ≤ lowerBarrierRaw κ κtilde D x :=
  (lowerBarrierRaw_pos_on_paper_region h hD hx).le

theorem lowerBarrierRaw_deriv_abs_le_on_paper_region
    {p : CMParams} {c κ κtilde M D x : ℝ}
    (h : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hx : x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D)) :
    |deriv (lowerBarrierRaw κ κtilde D) x| ≤
      (κ + κtilde) * Real.exp (-κ * x) := by
  have hDpos : 0 < D := D_pos_of_paperDMin_lt h hD
  have hκtilde_nonneg : 0 ≤ κtilde := (lt_trans h.hκ0 h.hgap).le
  have hraw_nonneg :
      0 ≤ lowerBarrierRaw κ κtilde D x :=
    lowerBarrierRaw_nonneg_on_paper_region h hD hx
  have hDexp_le :
      D * Real.exp (-κtilde * x) ≤ Real.exp (-κ * x) := by
    unfold lowerBarrierRaw at hraw_nonneg
    linarith
  rw [lowerBarrierRaw_deriv]
  have htri :
      |(-κ * Real.exp (-κ * x)) +
          (D * κtilde * Real.exp (-κtilde * x))| ≤
        κ * Real.exp (-κ * x) +
          D * κtilde * Real.exp (-κtilde * x) := by
    calc
      |(-κ * Real.exp (-κ * x)) +
          (D * κtilde * Real.exp (-κtilde * x))|
          ≤ |(-κ * Real.exp (-κ * x))| +
              |D * κtilde * Real.exp (-κtilde * x)| := abs_add_le _ _
      _ = κ * Real.exp (-κ * x) +
              D * κtilde * Real.exp (-κtilde * x) := by
          rw [abs_of_nonpos
            (mul_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.mpr h.hκ0.le) (Real.exp_pos _).le)]
          rw [abs_of_nonneg
            (mul_nonneg (mul_nonneg hDpos.le hκtilde_nonneg)
              (Real.exp_pos _).le)]
          ring
  have hsecond :
      D * κtilde * Real.exp (-κtilde * x) ≤
        κtilde * Real.exp (-κ * x) := by
    have hmul := mul_le_mul_of_nonneg_left hDexp_le hκtilde_nonneg
    nlinarith
  calc
    |(-κ * Real.exp (-κ * x)) +
        (D * κtilde * Real.exp (-κtilde * x))|
        ≤ κ * Real.exp (-κ * x) +
            D * κtilde * Real.exp (-κtilde * x) := htri
    _ ≤ κ * Real.exp (-κ * x) + κtilde * Real.exp (-κ * x) :=
        by
          have h := add_le_add_left hsecond (κ * Real.exp (-κ * x))
          simpa [add_comm, add_left_comm, add_assoc] using h
    _ = (κ + κtilde) * Real.exp (-κ * x) := by ring

/-- Scalar domination supplied by `D > D_min`; this is the last line of the
paper estimate and is independent of the elliptic bounds. -/
theorem paperDMin_margin_pos
    {χ M κ κtilde m gamma c D : ℝ}
    (hden : 0 < paperSpeedDenominator c κtilde)
    (hD : paperDMin χ M κ κtilde m gamma c < D) :
    0 < D * paperSpeedDenominator c κtilde - 1 -
      |χ| * paperSubsolutionK M κ κtilde m gamma := by
  dsimp [paperDMin] at hD
  have hlt :
      1 + |χ| * paperSubsolutionK M κ κtilde m gamma <
        D * paperSpeedDenominator c κtilde :=
    (div_lt_iff₀ hden).mp hD
  linarith

theorem paperDMin_margin_nonneg_exp
    {χ M κ κtilde m gamma c D x : ℝ}
    (hden : 0 < paperSpeedDenominator c κtilde)
    (hD : paperDMin χ M κ κtilde m gamma c < D) :
    0 ≤
      (D * paperSpeedDenominator c κtilde - 1 -
          |χ| * paperSubsolutionK M κ κtilde m gamma) *
        Real.exp (-κtilde * x) := by
  exact mul_nonneg (paperDMin_margin_pos hden hD).le (Real.exp_pos _).le

/-- Paper-operator expansion for the raw lower barrier.  The linear part is the
paper speed denominator; no frozen divergence operator is used here. -/
theorem paperWaveOperator_lowerBarrierRaw_eq_of_kappa_speed
    (p : CMParams) {c κ κtilde D : ℝ} (u : ℝ → ℝ) (x : ℝ)
    (hκ : κ ≠ 0) (hc : c = κ + κ⁻¹) :
    paperWaveOperator p c u (lowerBarrierRaw κ κtilde D) x =
      D * paperSpeedDenominator c κtilde * Real.exp (-κtilde * x)
        - p.χ * p.m * (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) *
          deriv (frozenElliptic p u) x * deriv (lowerBarrierRaw κ κtilde D) x
        + lowerBarrierRaw κ κtilde D x *
          (-p.χ * (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) *
              frozenElliptic p u x
            - ((lowerBarrierRaw κ κtilde D x) ^ p.α
              - p.χ * (lowerBarrierRaw κ κtilde D x) ^
                  (p.m + p.γ - 1))) := by
  unfold paperWaveOperator
  have hlin :
      iteratedDeriv 2 (lowerBarrierRaw κ κtilde D) x +
          c * deriv (lowerBarrierRaw κ κtilde D) x =
        D * paperSpeedDenominator c κtilde * Real.exp (-κtilde * x) -
          lowerBarrierRaw κ κtilde D x := by
    have h :=
      lowerBarrierRaw_linear_part_eq_speed_denominator (κ := κ)
        (κtilde := κtilde) (D := D) (c := c) (x := x) hκ hc
    simp [paperSpeedDenominator] at h ⊢
    linarith
  rw [hlin]
  ring

def paperLemma42BadTerm
    (p : CMParams) (u W : ℝ → ℝ) (x : ℝ) : ℝ :=
  W x * (W x) ^ p.α +
    |p.χ| *
      (p.m * (W x) ^ (p.m - 1) *
          |deriv (frozenElliptic p u) x| * |deriv W x| +
        W x * (W x) ^ (p.m + p.γ - 1))

/-- The remaining analytic estimate in Lemma 4.2: the logistic loss, the
`χ W^{m+γ}` loss, and the possible negative part of the derivative chemotaxis
term are bounded by the exact paper constant. -/
def PaperLemma42BadTermEstimate
    (p : CMParams) (_c κ κtilde M D : ℝ) : Prop :=
  ∀ u : ℝ → ℝ, InWaveTrapSet κ M u →
    ∀ x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D),
      paperLemma42BadTerm p u (lowerBarrierRaw κ κtilde D) x ≤
        (1 + |p.χ| * paperSubsolutionK M κ κtilde p.m p.γ) *
          Real.exp (-κtilde * x)

def PaperLemma42LogisticEstimate
    (p : CMParams) (_c κ κtilde M D : ℝ) : Prop :=
  ∀ u : ℝ → ℝ, InWaveTrapSet κ M u →
    ∀ x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D),
      lowerBarrierRaw κ κtilde D x *
          (lowerBarrierRaw κ κtilde D x) ^ p.α ≤
        Real.exp (-κtilde * x)

def PaperLemma42KTermEstimate
    (p : CMParams) (_c κ κtilde M D : ℝ) : Prop :=
  ∀ u : ℝ → ℝ, InWaveTrapSet κ M u →
    ∀ x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D),
      p.m * (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) *
            |deriv (frozenElliptic p u) x| *
            |deriv (lowerBarrierRaw κ κtilde D) x| +
          lowerBarrierRaw κ κtilde D x *
            (lowerBarrierRaw κ κtilde D x) ^ (p.m + p.γ - 1) ≤
        paperSubsolutionK M κ κtilde p.m p.γ * Real.exp (-κtilde * x)

theorem PaperLemma42BadTermEstimate_of_components
    {p : CMParams} {c κ κtilde M D : ℝ}
    (hlog : PaperLemma42LogisticEstimate p c κ κtilde M D)
    (hK : PaperLemma42KTermEstimate p c κ κtilde M D) :
    PaperLemma42BadTermEstimate p c κ κtilde M D := by
  intro u hu x hx
  have hlog_x := hlog u hu x hx
  have hK_x := hK u hu x hx
  have hχK := mul_le_mul_of_nonneg_left hK_x (abs_nonneg p.χ)
  calc
    paperLemma42BadTerm p u (lowerBarrierRaw κ κtilde D) x
        ≤ Real.exp (-κtilde * x) +
            |p.χ| *
              (paperSubsolutionK M κ κtilde p.m p.γ *
                Real.exp (-κtilde * x)) := by
          dsimp [paperLemma42BadTerm]
          exact add_le_add hlog_x hχK
    _ = (1 + |p.χ| * paperSubsolutionK M κ κtilde p.m p.γ) *
          Real.exp (-κtilde * x) := by
        ring

/-- The formal pointwise estimate supplied once the paper's `V,V_x` bounds
(4.7)-(4.8) discharge the bad-term estimate. -/
def PaperLemma42PointwiseEstimate
    (p : CMParams) (c κ κtilde M D : ℝ) : Prop :=
  ∀ u : ℝ → ℝ, InWaveTrapSet κ M u →
    ∀ x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D),
      (D * paperSpeedDenominator c κtilde - 1 -
          |p.χ| * paperSubsolutionK M κ κtilde p.m p.γ) *
        Real.exp (-κtilde * x) ≤
          paperWaveOperator p c u (lowerBarrierRaw κ κtilde D) x

theorem PaperLemma42PointwiseEstimate_of_badTermEstimate
    {p : CMParams} {c κ κtilde M D : ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hbad : PaperLemma42BadTermEstimate p c κ κtilde M D) :
    PaperLemma42PointwiseEstimate p c κ κtilde M D := by
  intro u hu x hx
  set W : ℝ → ℝ := lowerBarrierRaw κ κtilde D with hWdef
  set V : ℝ → ℝ := frozenElliptic p u with hVdef
  set lin : ℝ := D * paperSpeedDenominator c κtilde * Real.exp (-κtilde * x)
  set chem : ℝ := -p.χ * p.m * (W x) ^ (p.m - 1) * deriv V x * deriv W x
  set good : ℝ := W x * (-p.χ * (W x) ^ (p.m - 1) * V x)
  set logistic : ℝ := W x * (W x) ^ p.α
  set derivBad : ℝ :=
    |p.χ| * (p.m * (W x) ^ (p.m - 1) * |deriv V x| * |deriv W x|)
  set gammaBad : ℝ := |p.χ| * (W x * (W x) ^ (p.m + p.γ - 1))
  have hW_nonneg : 0 ≤ W x := by
    rw [hWdef]
    exact lowerBarrierRaw_nonneg_on_paper_region hcond hD hx
  have hWpow_nonneg : 0 ≤ (W x) ^ (p.m - 1) :=
    Real.rpow_nonneg hW_nonneg _
  have hV_nonneg : 0 ≤ V x := by
    rw [hVdef]
    exact frozenElliptic_nonneg p hu.nonneg x
  have hminus_chi : -p.χ = |p.χ| := by
    rw [abs_of_nonpos hcond.hχ]
  have hchi : p.χ = -|p.χ| := by
    linarith
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
      paperWaveOperator p c u W x =
        lin + chem + good - logistic - gammaBad := by
    rw [hWdef]
    rw [paperWaveOperator_lowerBarrierRaw_eq_of_kappa_speed p u x
      (ne_of_gt hcond.hκ0) hcond.hc]
    dsimp [lin, chem, good, logistic, gammaBad]
    rw [hVdef, hWdef]
    rw [hminus_chi, hchi]
    simp [abs_of_nonneg (abs_nonneg p.χ)]
    ring_nf
  have hbad_eq :
      paperLemma42BadTerm p u W x = logistic + derivBad + gammaBad := by
    dsimp [paperLemma42BadTerm, logistic, derivBad, gammaBad]
    rw [hVdef]
    ring
  have hop_lower :
      lin - paperLemma42BadTerm p u W x ≤ paperWaveOperator p c u W x := by
    rw [hbad_eq, hop]
    nlinarith [hchem_lower, hgood_nonneg]
  have hbad_x := hbad u hu x hx
  rw [← hWdef] at hbad_x
  have hleft :
      (D * paperSpeedDenominator c κtilde - 1 -
          |p.χ| * paperSubsolutionK M κ κtilde p.m p.γ) *
          Real.exp (-κtilde * x) =
        lin -
          (1 + |p.χ| * paperSubsolutionK M κ κtilde p.m p.γ) *
            Real.exp (-κtilde * x) := by
    dsimp [lin]
    ring
  rw [hleft]
  exact le_trans (sub_le_sub_left hbad_x lin) hop_lower

theorem PaperLemma_4_2_paperWaveOperator_from_pointwise_estimate
    {p : CMParams} {c κ κtilde M D : ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hpoint : PaperLemma42PointwiseEstimate p c κ κtilde M D)
    (u : ℝ → ℝ) (hu : InWaveTrapSet κ M u) :
    IsPaperFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
      (Set.Ioi (lowerBarrierXMinus κ κtilde D)) := by
  intro x hx
  exact le_trans
    (paperDMin_margin_nonneg_exp (χ := p.χ) (M := M) (κ := κ)
      (κtilde := κtilde) (m := p.m) (gamma := p.γ) (c := c) (D := D)
      (x := x) hcond.den_pos hD)
    (hpoint u hu x hx)

theorem PaperLemma_4_2_paperWaveOperator_from_components
    {p : CMParams} {c κ κtilde M D : ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hlog : PaperLemma42LogisticEstimate p c κ κtilde M D)
    (hK : PaperLemma42KTermEstimate p c κ κtilde M D)
    (u : ℝ → ℝ) (hu : InWaveTrapSet κ M u) :
    IsPaperFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
      (Set.Ioi (lowerBarrierXMinus κ κtilde D)) := by
  exact PaperLemma_4_2_paperWaveOperator_from_pointwise_estimate hcond hD
    (PaperLemma42PointwiseEstimate_of_badTermEstimate hcond hD
      (PaperLemma42BadTermEstimate_of_components hlog hK))
    u hu

theorem profileNontrivial_of_lowerBarrierRaw_tail_bound
    {p : CMParams} {c κ κtilde M D : ℝ} {U : ℝ → ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hUtail : ∀ x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D),
      lowerBarrierRaw κ κtilde D x ≤ U x) :
    ProfileNontrivial U := by
  let x₀ := lowerBarrierXPlus κ κtilde D
  have hDpos : 0 < D := D_pos_of_paperDMin_lt hcond hD
  have hx₀ : x₀ ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D) := by
    exact lowerBarrierXMinus_lt_xplus hcond.hκ0 (sub_pos.mpr hcond.hgap) hDpos
  have hraw_pos : 0 < lowerBarrierRaw κ κtilde D x₀ :=
    lowerBarrierRaw_pos_of_xminus_lt (sub_pos.mpr hcond.hgap) hDpos hx₀
  exact ⟨x₀, lt_of_lt_of_le hraw_pos (hUtail x₀ hx₀)⟩

theorem rotheOrbit_profileNontrivial_of_lowerBarrierRaw_stepInvariant
    {p : CMParams} {c κ κtilde M D : ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hbase : ∀ u, InLowerPinnedMonotoneTrap κ M
      (lowerBarrierRaw κ κtilde D) u →
        ∀ x, lowerBarrierRaw κ κtilde D x ≤ rotheSeq u 0 x)
    (hstep : RotheStepLowerInvariant κ M (lowerBarrierRaw κ κtilde D)
      rotheSeq) :
    ∀ u, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
      ∀ k, ProfileNontrivial (rotheSeq u k) := by
  intro u hu k
  have horbit :
      RotheOrbitLowerBound κ M (lowerBarrierRaw κ κtilde D) rotheSeq :=
    rotheOrbitLowerBound_of_stepLowerInvariant hbase hstep
  exact profileNontrivial_of_lowerBarrierRaw_tail_bound hcond hD
    (fun x _hx => horbit u hu k x)

/-! ## Axiom audit -/

section AxiomAudit
#print axioms paperSubsolutionK_eq_critical
#print axioms paperSubsolutionK_eq_subcritical
#print axioms paperSubsolutionK_eq_supercritical
#print axioms paperSubsolutionK_nonneg_of_conditions
#print axioms D_pos_of_paperDMin_lt
#print axioms lowerBarrierRaw_deriv_abs_le_on_paper_region
#print axioms paperDMin_margin_nonneg_exp
#print axioms paperWaveOperator_lowerBarrierRaw_eq_of_kappa_speed
#print axioms PaperLemma42BadTermEstimate_of_components
#print axioms PaperLemma42PointwiseEstimate_of_badTermEstimate
#print axioms PaperLemma_4_2_paperWaveOperator_from_pointwise_estimate
#print axioms PaperLemma_4_2_paperWaveOperator_from_components
#print axioms profileNontrivial_of_lowerBarrierRaw_tail_bound
#print axioms rotheOrbit_profileNontrivial_of_lowerBarrierRaw_stepInvariant
end AxiomAudit

end ShenWork.Paper1
