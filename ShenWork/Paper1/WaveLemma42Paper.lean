import ShenWork.Paper1.WaveLowerBarrierData
import ShenWork.Paper1.WaveRotheConcrete
import ShenWork.Paper1.WavePaperRotheProducer
import ShenWork.Paper1.WavePaperRouteA

open Filter Topology Set Real MeasureTheory intervalIntegral

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
  hα_le : p.α ≤ p.m + p.γ - 1

namespace PaperLemma42ExactConditions

private theorem one_sub_exp_neg_le_self (t : ℝ) :
    1 - Real.exp (-t) ≤ t := by
  have h := Real.add_one_le_exp (-t)
  linarith

private theorem upperBarrier_sub_le_of_le
    {κ M x y : ℝ} (hκ : 0 ≤ κ) (hM : 0 < M) (hxy : x ≤ y) :
    upperBarrier κ M x - upperBarrier κ M y ≤ κ * M * (y - x) := by
  let d : ℝ := y - x
  have hd : 0 ≤ d := sub_nonneg.mpr hxy
  have ht : 0 ≤ κ * d := mul_nonneg hκ hd
  have he_nonneg : 0 ≤ Real.exp (-(κ * d)) := (Real.exp_pos _).le
  have he_le_one : Real.exp (-(κ * d)) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr ht)
  have hone_sub_nonneg : 0 ≤ 1 - Real.exp (-(κ * d)) := sub_nonneg.mpr he_le_one
  have hone_sub_le : 1 - Real.exp (-(κ * d)) ≤ κ * d :=
    one_sub_exp_neg_le_self (κ * d)
  have hEy :
      Real.exp (-κ * y) =
        Real.exp (-κ * x) * Real.exp (-(κ * d)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [d]
    ring
  by_cases hxM : M ≤ Real.exp (-κ * x)
  · by_cases hyM : M ≤ Real.exp (-κ * y)
    · rw [upperBarrier_eq_M_of_le_exp hxM, upperBarrier_eq_M_of_le_exp hyM]
      nlinarith [mul_nonneg (mul_nonneg hκ hM.le) hd]
    · have hUy : upperBarrier κ M y = Real.exp (-κ * y) :=
        upperBarrier_eq_exp_of_exp_le (not_le.mp hyM).le
      rw [upperBarrier_eq_M_of_le_exp hxM, hUy]
      have hEy_ge : M * Real.exp (-(κ * d)) ≤ Real.exp (-κ * y) := by
        rw [hEy]
        exact mul_le_mul_of_nonneg_right hxM he_nonneg
      calc
        M - Real.exp (-κ * y)
            ≤ M - M * Real.exp (-(κ * d)) := by
              exact sub_le_sub_left hEy_ge M
        _ = M * (1 - Real.exp (-(κ * d))) := by ring
        _ ≤ M * (κ * d) :=
              mul_le_mul_of_nonneg_left hone_sub_le hM.le
        _ = κ * M * (y - x) := by
              dsimp [d]
              ring
  · have hUx : upperBarrier κ M x = Real.exp (-κ * x) :=
      upperBarrier_eq_exp_of_exp_le (not_le.mp hxM).le
    have hUy : upperBarrier κ M y = Real.exp (-κ * y) := by
      apply upperBarrier_eq_exp_of_exp_le
      have hmono : Real.exp (-κ * y) ≤ Real.exp (-κ * x) := by
        exact Real.exp_le_exp.mpr (by nlinarith)
      exact le_trans hmono (not_le.mp hxM).le
    rw [hUx, hUy]
    have hx_le_M : Real.exp (-κ * x) ≤ M := (not_le.mp hxM).le
    calc
      Real.exp (-κ * x) - Real.exp (-κ * y)
          = Real.exp (-κ * x) * (1 - Real.exp (-(κ * d))) := by
            rw [hEy]
            ring
      _ ≤ M * (1 - Real.exp (-(κ * d))) := by
            exact mul_le_mul_of_nonneg_right hx_le_M hone_sub_nonneg
      _ ≤ M * (κ * d) :=
            mul_le_mul_of_nonneg_left hone_sub_le hM.le
      _ = κ * M * (y - x) := by
            dsimp [d]
            ring

theorem upperBarrier_abs_sub_le_mul
    {κ M : ℝ} (hκ : 0 ≤ κ) (hM : 0 < M) :
    ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤
      κ * M * |x - y| := by
  intro x y
  by_cases hxy : x ≤ y
  · have hmono : upperBarrier κ M y ≤ upperBarrier κ M x :=
      upperBarrier_antitone hκ hxy
    rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
    calc
      upperBarrier κ M x - upperBarrier κ M y
          ≤ κ * M * (y - x) :=
            upperBarrier_sub_le_of_le hκ hM hxy
      _ = κ * M * |x - y| := by
            rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
            ring
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hmono : upperBarrier κ M x ≤ upperBarrier κ M y :=
      upperBarrier_antitone hκ hyx
    rw [abs_of_nonpos (sub_nonpos.mpr hmono)]
    calc
      -(upperBarrier κ M x - upperBarrier κ M y)
          = upperBarrier κ M y - upperBarrier κ M x := by ring
      _ ≤ κ * M * (x - y) :=
            upperBarrier_sub_le_of_le hκ hM hyx
      _ = κ * M * |x - y| := by
            rw [abs_of_nonneg (sub_nonneg.mpr hyx)]

theorem upperBarrier_barLip
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PaperLemma42ExactConditions p c κ κtilde M) :
    ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y| := by
  intro x y
  have hκM : κ * M ≤ M := by
    nlinarith [h.hκ0.le, h.hκ1.le, h.hM]
  calc
    |upperBarrier κ M x - upperBarrier κ M y|
        ≤ κ * M * |x - y| :=
          upperBarrier_abs_sub_le_mul h.hκ0.le
            (lt_of_lt_of_le zero_lt_one h.hM) x y
    _ ≤ M * |x - y| :=
          mul_le_mul_of_nonneg_right hκM (abs_nonneg _)

theorem kappaTilde_le_one
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PaperLemma42ExactConditions p c κ κtilde M) :
    κtilde ≤ 1 := by
  exact le_trans h.hrange
      (le_trans (min_le_right _ _) (min_le_right _ _))

theorem kappaTilde_le_one_plus_alpha_mul_kappa
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PaperLemma42ExactConditions p c κ κtilde M) :
    κtilde ≤ (p.α + 1) * κ := by
  have hle : κtilde ≤ (1 + p.α) * κ :=
    le_trans h.hrange (min_le_left _ _)
  convert hle using 1
  ring

theorem kappaTilde_le_m_gamma_mul_kappa
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PaperLemma42ExactConditions p c κ κtilde M) :
    κtilde ≤ (p.m + p.γ) * κ := by
  have hle := h.kappaTilde_le_one_plus_alpha_mul_kappa
  have hcoef : p.α + 1 ≤ p.m + p.γ := by linarith [h.hα_le]
  exact le_trans hle (mul_le_mul_of_nonneg_right hcoef h.hκ0.le)

theorem kappaTilde_le_m_kappa_add_half
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PaperLemma42ExactConditions p c κ κtilde M) :
    κtilde ≤ p.m * κ + 1 / 2 := by
  exact le_trans h.hrange
    (le_trans (min_le_right _ _) (min_le_left _ _))

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

def paperEllipticVxBound (M κ gamma x : ℝ) : ℝ :=
  if gamma * κ = 1 then
    (M ^ gamma + 3 / 4) * Real.exp (-(1 / 2) * x)
  else if gamma * κ < 1 then
    (1 / (1 - gamma ^ 2 * κ ^ 2)) * Real.exp (-(gamma * κ) * x)
  else
    ((M ^ gamma * (κ ^ 2 * gamma ^ 2 - 1) + gamma * κ) /
        (κ ^ 2 * gamma ^ 2 - 1)) * Real.exp (-x)

def PaperLemma42EllipticVxEstimate
    (p : CMParams) (κ M : ℝ) : Prop :=
  ∀ u : ℝ → ℝ, InWaveTrapSet κ M u →
    ∀ x, 0 ≤ x →
      |deriv (frozenElliptic p u) x| ≤
        paperEllipticVxBound M κ p.γ x

def PaperLemma42EllipticVEstimate
    (p : CMParams) (κ M : ℝ) : Prop :=
  ∀ u : ℝ → ℝ, InWaveTrapSet κ M u →
    ∀ x, 0 ≤ x →
      frozenElliptic p u x ≤ paperEllipticVxBound M κ p.γ x

/-- The frozen elliptic source box used in the paper's lower-barrier
construction.  All coefficient bounds are uniform over the monotone wave trap;
the right-tail field is the paper's genuine three-case estimate (subcritical,
critical resonance, and supercritical), not a spurious single
`min (γ * κ) 1` exponential bound. -/
structure PaperFrozenEllipticSourceBox
    (p : CMParams) (κ M : ℝ) : Prop where
  value_nonneg : ∀ u : ℝ → ℝ, InMonotoneWaveTrapSet κ M u →
    ∀ x, 0 ≤ frozenElliptic p u x
  value_le : ∀ u : ℝ → ℝ, InMonotoneWaveTrapSet κ M u →
    ∀ x, frozenElliptic p u x ≤ M ^ p.γ
  deriv_abs_le : ∀ u : ℝ → ℝ, InMonotoneWaveTrapSet κ M u →
    ∀ x, |deriv (frozenElliptic p u) x| ≤ M ^ p.γ
  second_deriv_abs_le : ∀ u : ℝ → ℝ, InMonotoneWaveTrapSet κ M u →
    ∀ x, |deriv (deriv (frozenElliptic p u)) x| ≤ 2 * M ^ p.γ
  antitone : ∀ u : ℝ → ℝ, InMonotoneWaveTrapSet κ M u →
    Antitone (frozenElliptic p u)
  right_tail_value : PaperLemma42EllipticVEstimate p κ M
  right_tail_deriv : PaperLemma42EllipticVxEstimate p κ M

private lemma integral_exp_neg_mul_interval_eq
    {δ x : ℝ} (hδ : 0 < δ) :
    (∫ y in (0 : ℝ)..x, Real.exp (-δ * y)) =
      (1 - Real.exp (-δ * x)) / δ := by
  have hderiv :
      ∀ y ∈ uIcc (0 : ℝ) x,
        HasDerivAt (fun z : ℝ => -Real.exp (-δ * z) / δ)
          (Real.exp (-δ * y)) y := by
    intro y _hy
    have hbase : HasDerivAt (fun z : ℝ => Real.exp (-δ * z))
        ((-δ) * Real.exp (-δ * y)) y := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_const y (-δ)).mul (hasDerivAt_id y)).exp)
    have hneg : HasDerivAt (fun z : ℝ => -Real.exp (-δ * z))
        (δ * Real.exp (-δ * y)) y := by
      simpa using hbase.neg
    have hdiv := hneg.div_const δ
    simpa [ne_of_gt hδ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using hdiv
  have hint :
      IntervalIntegrable (fun y : ℝ => Real.exp (-δ * y)) volume
        (0 : ℝ) x :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  field_simp [ne_of_gt hδ]
  norm_num
  ring

private lemma critical_linear_exp_bound {x : ℝ} (hx : 0 ≤ x) :
    1 / 2 * x * Real.exp (-x) + 1 / 4 * Real.exp (-x) ≤
      3 / 4 * Real.exp (-(1 / 2) * x) := by
  set t := x / 2 with ht
  have ht_nonneg : 0 ≤ t := by dsimp [t]; linarith
  have hx_eq : x = 2 * t := by dsimp [t]; ring
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by
    have h := add_one_le_exp (1 : ℝ)
    norm_num at h
    exact h
  have htwo_exp_neg_one : 2 * Real.exp (-1) ≤ (1 : ℝ) := by
    calc
      2 * Real.exp (-1) ≤ Real.exp 1 * Real.exp (-1) :=
        mul_le_mul_of_nonneg_right hexp1 (Real.exp_pos _).le
      _ = 1 := by
        rw [← Real.exp_add]
        norm_num
  have ht_exp_half : t * Real.exp (-t) ≤ (1 / 2 : ℝ) := by
    have hmain := Real.mul_exp_neg_le_exp_neg_one t
    nlinarith
  have hexp_order : Real.exp (-x) ≤ Real.exp (-t) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hxterm :
      1 / 2 * x * Real.exp (-x) ≤ 1 / 2 * Real.exp (-t) := by
    have hfactor : t * Real.exp (-x) ≤ 1 / 2 * Real.exp (-t) := by
      have hrewrite : Real.exp (-x) = Real.exp (-t) * Real.exp (-t) := by
        rw [hx_eq]
        rw [show -(2 * t) = -t + -t by ring, Real.exp_add]
      rw [hrewrite]
      calc
        t * (Real.exp (-t) * Real.exp (-t)) =
            (t * Real.exp (-t)) * Real.exp (-t) := by ring
        _ ≤ (1 / 2) * Real.exp (-t) :=
            mul_le_mul_of_nonneg_right ht_exp_half (Real.exp_pos _).le
    calc
      1 / 2 * x * Real.exp (-x) = t * Real.exp (-x) := by
        rw [hx_eq]
        ring
      _ ≤ 1 / 2 * Real.exp (-t) := hfactor
  have hconst :
      1 / 4 * Real.exp (-x) ≤ 1 / 4 * Real.exp (-t) :=
    mul_le_mul_of_nonneg_left hexp_order (by norm_num)
  have hsum :
      1 / 2 * x * Real.exp (-x) + 1 / 4 * Real.exp (-x) ≤
        3 / 4 * Real.exp (-t) := by
    linarith
  convert hsum using 1
  congr 1
  dsimp [t]
  ring

private theorem setIntegral_Ioi_exp_le_of_exp_le_general
    {a : ℝ} {f : ℝ → ℝ}
    (ha : 0 < a)
    (hf_exp : ∀ y, f y ≤ Real.exp (-a * y))
    (x : ℝ)
    (hint : IntegrableOn (fun y => Real.exp (-1 * y) * f y) (Set.Ioi x)) :
    ∫ y in Set.Ioi x, Real.exp (-1 * y) * f y ≤
      Real.exp (-(1 + a) * x) / (1 + a) := by
  have h1pa : 0 < 1 + a := by linarith
  have hneg : -(1 + a) < (0 : ℝ) := by linarith
  have hint_exp :
      IntegrableOn (fun y => Real.exp (-(1 + a) * y)) (Set.Ioi x) :=
    integrableOn_exp_mul_Ioi hneg x
  calc
    ∫ y in Set.Ioi x, Real.exp (-1 * y) * f y
        ≤ ∫ y in Set.Ioi x, Real.exp (-(1 + a) * y) := by
          apply MeasureTheory.setIntegral_mono hint hint_exp
          intro y
          calc
            Real.exp (-1 * y) * f y
                ≤ Real.exp (-1 * y) * Real.exp (-a * y) :=
              mul_le_mul_of_nonneg_left (hf_exp y) (Real.exp_nonneg _)
            _ = Real.exp (-(1 + a) * y) := by
              rw [← Real.exp_add]
              congr 1
              ring
    _ = -Real.exp (-(1 + a) * x) / (-(1 + a)) :=
        integral_exp_mul_Ioi hneg x
    _ = Real.exp (-(1 + a) * x) / (1 + a) := by
        field_simp

private lemma supercritical_coeff_bound {a B : ℝ}
    (ha : 1 < a) (hB : 0 ≤ B) :
    1 / 2 * (B + 1 / (a - 1)) + 1 / 2 * (1 / (1 + a)) ≤
      B + a / (a ^ 2 - 1) := by
  have hm : 0 < a - 1 := by linarith
  have hp : 0 < 1 + a := by linarith
  have hden : 0 < a ^ 2 - 1 := by nlinarith
  have hfrac :
      1 / 2 * (1 / (a - 1)) + 1 / 2 * (1 / (1 + a)) =
        a / (a ^ 2 - 1) := by
    field_simp [ne_of_gt hm, ne_of_gt hp, ne_of_gt hden]
    ring
  calc
    1 / 2 * (B + 1 / (a - 1)) + 1 / 2 * (1 / (1 + a))
        = 1 / 2 * B +
            (1 / 2 * (1 / (a - 1)) + 1 / 2 * (1 / (1 + a))) := by
          ring
    _ = 1 / 2 * B + a / (a ^ 2 - 1) := by rw [hfrac]
    _ ≤ B + a / (a ^ 2 - 1) := by linarith

private theorem frozenElliptic_le_paperVxBound_subcritical
    {p : CMParams} {κ M : ℝ} {u : ℝ → ℝ}
    (hκ : 0 < κ) (hsub : p.γ * κ < 1)
    (hu : InWaveTrapSet κ M u) (x : ℝ) :
    frozenElliptic p u x ≤
      (1 / (1 - p.γ ^ 2 * κ ^ 2)) *
        Real.exp (-(p.γ * κ) * x) := by
  have hγ_nonneg : 0 ≤ p.γ := by linarith [p.hγ]
  have hγ_pos : 0 < p.γ := by linarith [p.hγ]
  have hγκ_pos : 0 < p.γ * κ := mul_pos hγ_pos hκ
  have hf_cub := rpow_cunif_bdd_of_nonneg p hu.cunif_bdd hu.nonneg
  rcases hf_cub.2 with ⟨B, hB⟩
  have hB_nonneg : 0 ≤ B :=
    le_trans (abs_nonneg ((u 0) ^ p.γ)) (hB 0)
  have hiu :
      Integrable
        (fun y => Real.exp (-Real.sqrt (1 : ℝ) * |x - y|) *
          (u y) ^ p.γ) := by
    exact psi_kernel_mul_bounded_integrable
      (by norm_num : (0 : ℝ) < 1) hB_nonneg hB x
      hf_cub.1.aestronglyMeasurable
  have huexp :
      ∀ y, (u y) ^ p.γ ≤ Real.exp (-(p.γ * κ) * y) := by
    intro y
    calc
      (u y) ^ p.γ ≤ (Real.exp (-κ * y)) ^ p.γ :=
        Real.rpow_le_rpow (hu.nonneg y) (hu.le_exp y) hγ_nonneg
      _ = Real.exp (-(p.γ * κ) * y) := by
        rw [← Real.exp_mul]
        congr 1
        ring
  have hpsi :=
    Psi_le_exp_of_le hγκ_pos hsub huexp x hiu
  unfold frozenElliptic
  refine le_trans hpsi ?_
  have hden_eq : 1 - (p.γ * κ) ^ 2 = 1 - p.γ ^ 2 * κ ^ 2 := by ring
  rw [hden_eq]

private theorem frozenElliptic_le_paperVxBound_critical
    {p : CMParams} {κ M : ℝ} {u : ℝ → ℝ} {x : ℝ}
    (hcrit : p.γ * κ = 1) (hM : 1 ≤ M)
    (hu : InWaveTrapSet κ M u) (hx : 0 ≤ x) :
    frozenElliptic p u x ≤
      (M ^ p.γ + 3 / 4) * Real.exp (-(1 / 2) * x) := by
  let f : ℝ → ℝ := fun y => (u y) ^ p.γ
  have hγ_nonneg : 0 ≤ p.γ := by linarith [p.hγ]
  have hMγ_nonneg : 0 ≤ M ^ p.γ :=
    Real.rpow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hM) p.γ
  have hf_nonneg : ∀ y, 0 ≤ f y := by
    intro y
    exact Real.rpow_nonneg (hu.nonneg y) p.γ
  have hfM : ∀ y, f y ≤ M ^ p.γ := by
    intro y
    dsimp [f]
    exact hu.rpow_le_M hγ_nonneg y
  have hfexp : ∀ y, f y ≤ Real.exp (-(p.γ * κ) * y) := by
    intro y
    dsimp [f]
    calc
      (u y) ^ p.γ ≤ (Real.exp (-κ * y)) ^ p.γ :=
        Real.rpow_le_rpow (hu.nonneg y) (hu.le_exp y) hγ_nonneg
      _ = Real.exp (-(p.γ * κ) * y) := by
        rw [← Real.exp_mul]
        congr 1
        ring
  have hf_cub := rpow_cunif_bdd_of_nonneg p hu.cunif_bdd hu.nonneg
  have hL_int : ∀ t : ℝ,
      IntegrableOn (fun y => Real.exp (1 * y) * f y) (Set.Iic t) := by
    intro t
    have hbase : IntegrableOn (fun y : ℝ => Real.exp (1 * y)) (Set.Iic t) :=
      integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1) t
    have hdom : IntegrableOn
        (fun y : ℝ => Real.exp (1 * y) * M ^ p.γ) (Set.Iic t) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        hbase.mul_const (M ^ p.γ)
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        hf_cub.1).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (hf_nonneg y))]
      exact mul_le_mul_of_nonneg_left (hfM y) (Real.exp_nonneg _)
  have hR_int :
      IntegrableOn (fun y => Real.exp (-1 * y) * f y) (Set.Ioi x) := by
    have hdom :
        IntegrableOn (fun y : ℝ => Real.exp (-(1 + p.γ * κ) * y))
          (Set.Ioi x) :=
      integrableOn_exp_mul_Ioi (by linarith [hcrit] : -(1 + p.γ * κ) < (0 : ℝ)) x
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        hf_cub.1).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (hf_nonneg y))]
      calc
        Real.exp (-1 * y) * f y
            ≤ Real.exp (-1 * y) * Real.exp (-(p.γ * κ) * y) :=
          mul_le_mul_of_nonneg_left (hfexp y) (Real.exp_nonneg _)
        _ = Real.exp (-(1 + p.γ * κ) * y) := by
          rw [← Real.exp_add]
          congr 1
          ring
  set L := ∫ y in Set.Iic x, Real.exp (1 * y) * f y
  set L0 := ∫ y in Set.Iic (0 : ℝ), Real.exp (1 * y) * f y
  set I := ∫ y in (0 : ℝ)..x, Real.exp (1 * y) * f y
  set R := ∫ y in Set.Ioi x, Real.exp (-1 * y) * f y
  have hL0_bound : L0 ≤ M ^ p.γ := by
    dsimp [L0]
    have hdom0 : IntegrableOn
        (fun y : ℝ => Real.exp (1 * y) * M ^ p.γ) (Set.Iic (0 : ℝ)) := by
      have hbase : IntegrableOn (fun y : ℝ => Real.exp (1 * y)) (Set.Iic (0 : ℝ)) :=
        integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1) 0
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        hbase.mul_const (M ^ p.γ)
    calc
      ∫ y in Set.Iic (0 : ℝ), Real.exp (1 * y) * f y
          ≤ ∫ y in Set.Iic (0 : ℝ), Real.exp (1 * y) * M ^ p.γ := by
            apply MeasureTheory.setIntegral_mono (hL_int 0) hdom0
            intro y
            exact mul_le_mul_of_nonneg_left (hfM y) (Real.exp_nonneg _)
      _ = M ^ p.γ := by
        rw [MeasureTheory.integral_mul_const]
        rw [integral_exp_mul_Iic (by norm_num : (0 : ℝ) < 1) 0]
        norm_num
  have hcont_I : Continuous (fun y => Real.exp (1 * y) * f y) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hf_cub.1
  have hI_int :
      IntervalIntegrable (fun y => Real.exp (1 * y) * f y) volume
        (0 : ℝ) x :=
    hcont_I.intervalIntegrable _ _
  have hI_const :
      IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (0 : ℝ) x :=
    continuous_const.intervalIntegrable _ _
  have hI_bound : I ≤ x := by
    dsimp [I]
    calc
      ∫ y in (0 : ℝ)..x, Real.exp (1 * y) * f y
          ≤ ∫ _y in (0 : ℝ)..x, (1 : ℝ) := by
            apply intervalIntegral.integral_mono_on hx hI_int hI_const
            intro y _hy
            calc
              Real.exp (1 * y) * f y
                  ≤ Real.exp (1 * y) * Real.exp (-(p.γ * κ) * y) :=
                mul_le_mul_of_nonneg_left (hfexp y) (Real.exp_nonneg _)
              _ = 1 := by
                rw [hcrit]
                rw [← Real.exp_add]
                norm_num
      _ = x := by
        rw [intervalIntegral.integral_const]
        simp
  have hsplit := integral_Iic_sub_Iic
    (a := (0 : ℝ)) (b := x) (f := fun y => Real.exp (1 * y) * f y)
    (μ := volume) (hL_int 0) (hL_int x)
  have hL_eq : L = L0 + I := by
    dsimp [L, L0, I] at hsplit ⊢
    linarith
  have hL_bound : L ≤ M ^ p.γ + x := by
    rw [hL_eq]
    exact add_le_add hL0_bound hI_bound
  have hR_bound :
      R ≤ Real.exp (-2 * x) / 2 := by
    have h :=
      setIntegral_Ioi_exp_le_of_exp_le_general
        (by linarith [hcrit] : 0 < p.γ * κ) hfexp x hR_int
    dsimp [R] at h ⊢
    have hden : 1 + p.γ * κ = (2 : ℝ) := by linarith [hcrit]
    rw [hden] at h
    convert h using 1
  have hV :
      frozenElliptic p u x =
        1 / 2 * (Real.exp (-1 * x) * L + Real.exp (1 * x) * R) := by
    unfold frozenElliptic
    dsimp [L, R, f]
    exact Psi_kernel_splitting hf_cub hf_nonneg x
  have hLterm :
      Real.exp (-1 * x) * L ≤ Real.exp (-x) * (M ^ p.γ + x) := by
    convert mul_le_mul_of_nonneg_left hL_bound (Real.exp_nonneg _) using 1
    ring
  have hRterm :
      Real.exp (1 * x) * R ≤ Real.exp (-x) / 2 := by
    calc
      Real.exp (1 * x) * R
          ≤ Real.exp (1 * x) * (Real.exp (-2 * x) / 2) :=
        mul_le_mul_of_nonneg_left hR_bound (Real.exp_nonneg _)
      _ = Real.exp (-x) / 2 := by
        calc
          Real.exp (1 * x) * (Real.exp (-2 * x) / 2) =
              (Real.exp (1 * x) * Real.exp (-2 * x)) / 2 := by ring
          _ = Real.exp (-x) / 2 := by
            congr 1
            rw [← Real.exp_add]
            congr 1
            ring
  have hpre :
      frozenElliptic p u x ≤
        1 / 2 * (Real.exp (-x) * (M ^ p.γ + x) + Real.exp (-x) / 2) := by
    rw [hV]
    exact mul_le_mul_of_nonneg_left (add_le_add hLterm hRterm) (by norm_num)
  have hMterm :
      1 / 2 * (M ^ p.γ) * Real.exp (-x) ≤
        (M ^ p.γ) * Real.exp (-(1 / 2) * x) := by
    have hexp_le : Real.exp (-x) ≤ Real.exp (-(1 / 2) * x) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hnonneg : 0 ≤ (M ^ p.γ) * Real.exp (-x) :=
      mul_nonneg hMγ_nonneg (Real.exp_nonneg _)
    calc
      1 / 2 * (M ^ p.γ) * Real.exp (-x)
          = (1 / 2) * ((M ^ p.γ) * Real.exp (-x)) := by ring
      _ ≤ 1 * ((M ^ p.γ) * Real.exp (-x)) :=
        mul_le_mul_of_nonneg_right (by norm_num) hnonneg
      _ = (M ^ p.γ) * Real.exp (-x) := by ring
      _ ≤ (M ^ p.γ) * Real.exp (-(1 / 2) * x) :=
        mul_le_mul_of_nonneg_left hexp_le hMγ_nonneg
  calc
    frozenElliptic p u x
        ≤ 1 / 2 * (Real.exp (-x) * (M ^ p.γ + x) + Real.exp (-x) / 2) :=
      hpre
    _ = 1 / 2 * (M ^ p.γ) * Real.exp (-x) +
          (1 / 2 * x * Real.exp (-x) + 1 / 4 * Real.exp (-x)) := by
      ring
    _ ≤ (M ^ p.γ) * Real.exp (-(1 / 2) * x) +
          3 / 4 * Real.exp (-(1 / 2) * x) :=
      add_le_add hMterm (critical_linear_exp_bound hx)
    _ = (M ^ p.γ + 3 / 4) * Real.exp (-(1 / 2) * x) := by
      ring

private theorem frozenElliptic_le_paperVxBound_supercritical
    {p : CMParams} {κ M : ℝ} {u : ℝ → ℝ} {x : ℝ}
    (hsuper : 1 < p.γ * κ) (hM : 1 ≤ M)
    (hu : InWaveTrapSet κ M u) (hx : 0 ≤ x) :
    frozenElliptic p u x ≤
      ((M ^ p.γ * (κ ^ 2 * p.γ ^ 2 - 1) + p.γ * κ) /
          (κ ^ 2 * p.γ ^ 2 - 1)) * Real.exp (-x) := by
  let a : ℝ := p.γ * κ
  let f : ℝ → ℝ := fun y => (u y) ^ p.γ
  have ha : 1 < a := by dsimp [a]; exact hsuper
  have ha_pos : 0 < a := lt_trans zero_lt_one ha
  have hdelta_pos : 0 < a - 1 := by linarith
  have hden_pos : 0 < a ^ 2 - 1 := by nlinarith
  have hγ_nonneg : 0 ≤ p.γ := by linarith [p.hγ]
  have hMγ_nonneg : 0 ≤ M ^ p.γ :=
    Real.rpow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hM) p.γ
  have hf_nonneg : ∀ y, 0 ≤ f y := by
    intro y
    exact Real.rpow_nonneg (hu.nonneg y) p.γ
  have hfM : ∀ y, f y ≤ M ^ p.γ := by
    intro y
    dsimp [f]
    exact hu.rpow_le_M hγ_nonneg y
  have hfexp : ∀ y, f y ≤ Real.exp (-a * y) := by
    intro y
    dsimp [f, a]
    calc
      (u y) ^ p.γ ≤ (Real.exp (-κ * y)) ^ p.γ :=
        Real.rpow_le_rpow (hu.nonneg y) (hu.le_exp y) hγ_nonneg
      _ = Real.exp (-(p.γ * κ) * y) := by
        rw [← Real.exp_mul]
        congr 1
        ring
  have hf_cub := rpow_cunif_bdd_of_nonneg p hu.cunif_bdd hu.nonneg
  have hL_int : ∀ t : ℝ,
      IntegrableOn (fun y => Real.exp (1 * y) * f y) (Set.Iic t) := by
    intro t
    have hbase : IntegrableOn (fun y : ℝ => Real.exp (1 * y)) (Set.Iic t) :=
      integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1) t
    have hdom : IntegrableOn
        (fun y : ℝ => Real.exp (1 * y) * M ^ p.γ) (Set.Iic t) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        hbase.mul_const (M ^ p.γ)
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        hf_cub.1).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (hf_nonneg y))]
      exact mul_le_mul_of_nonneg_left (hfM y) (Real.exp_nonneg _)
  have hR_int :
      IntegrableOn (fun y => Real.exp (-1 * y) * f y) (Set.Ioi x) := by
    have hdom :
        IntegrableOn (fun y : ℝ => Real.exp (-(1 + a) * y)) (Set.Ioi x) :=
      integrableOn_exp_mul_Ioi (by linarith : -(1 + a) < (0 : ℝ)) x
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        hf_cub.1).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (hf_nonneg y))]
      calc
        Real.exp (-1 * y) * f y
            ≤ Real.exp (-1 * y) * Real.exp (-a * y) :=
          mul_le_mul_of_nonneg_left (hfexp y) (Real.exp_nonneg _)
        _ = Real.exp (-(1 + a) * y) := by
          rw [← Real.exp_add]
          congr 1
          ring
  set L := ∫ y in Set.Iic x, Real.exp (1 * y) * f y
  set L0 := ∫ y in Set.Iic (0 : ℝ), Real.exp (1 * y) * f y
  set I := ∫ y in (0 : ℝ)..x, Real.exp (1 * y) * f y
  set R := ∫ y in Set.Ioi x, Real.exp (-1 * y) * f y
  have hL0_bound : L0 ≤ M ^ p.γ := by
    dsimp [L0]
    have hdom0 : IntegrableOn
        (fun y : ℝ => Real.exp (1 * y) * M ^ p.γ) (Set.Iic (0 : ℝ)) := by
      have hbase : IntegrableOn (fun y : ℝ => Real.exp (1 * y)) (Set.Iic (0 : ℝ)) :=
        integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1) 0
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        hbase.mul_const (M ^ p.γ)
    calc
      ∫ y in Set.Iic (0 : ℝ), Real.exp (1 * y) * f y
          ≤ ∫ y in Set.Iic (0 : ℝ), Real.exp (1 * y) * M ^ p.γ := by
            apply MeasureTheory.setIntegral_mono (hL_int 0) hdom0
            intro y
            exact mul_le_mul_of_nonneg_left (hfM y) (Real.exp_nonneg _)
      _ = M ^ p.γ := by
        rw [MeasureTheory.integral_mul_const]
        rw [integral_exp_mul_Iic (by norm_num : (0 : ℝ) < 1) 0]
        norm_num
  have hcont_I : Continuous (fun y => Real.exp (1 * y) * f y) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hf_cub.1
  have hI_int :
      IntervalIntegrable (fun y => Real.exp (1 * y) * f y) volume
        (0 : ℝ) x :=
    hcont_I.intervalIntegrable _ _
  have hI_exp_int :
      IntervalIntegrable (fun y : ℝ => Real.exp (-(a - 1) * y)) volume
        (0 : ℝ) x :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hI_bound : I ≤ 1 / (a - 1) := by
    dsimp [I]
    have hmono :
        ∫ y in (0 : ℝ)..x, Real.exp (1 * y) * f y
            ≤ ∫ y in (0 : ℝ)..x, Real.exp (-(a - 1) * y) := by
      apply intervalIntegral.integral_mono_on hx hI_int hI_exp_int
      intro y _hy
      calc
        Real.exp (1 * y) * f y
            ≤ Real.exp (1 * y) * Real.exp (-a * y) :=
          mul_le_mul_of_nonneg_left (hfexp y) (Real.exp_nonneg _)
        _ = Real.exp (-(a - 1) * y) := by
          rw [← Real.exp_add]
          congr 1
          ring
    calc
      ∫ y in (0 : ℝ)..x, Real.exp (1 * y) * f y
          ≤ ∫ y in (0 : ℝ)..x, Real.exp (-(a - 1) * y) := hmono
      _ = (1 - Real.exp (-(a - 1) * x)) / (a - 1) :=
        integral_exp_neg_mul_interval_eq hdelta_pos
      _ ≤ 1 / (a - 1) := by
        have hnum : 1 - Real.exp (-(a - 1) * x) ≤ (1 : ℝ) := by
          linarith [Real.exp_nonneg (-(a - 1) * x)]
        exact div_le_div_of_nonneg_right hnum hdelta_pos.le
  have hsplit := integral_Iic_sub_Iic
    (a := (0 : ℝ)) (b := x) (f := fun y => Real.exp (1 * y) * f y)
    (μ := volume) (hL_int 0) (hL_int x)
  have hL_eq : L = L0 + I := by
    dsimp [L, L0, I] at hsplit ⊢
    linarith
  have hL_bound : L ≤ M ^ p.γ + 1 / (a - 1) := by
    rw [hL_eq]
    exact add_le_add hL0_bound hI_bound
  have hR_bound :
      R ≤ Real.exp (-(1 + a) * x) / (1 + a) := by
    dsimp [R]
    exact setIntegral_Ioi_exp_le_of_exp_le_general ha_pos hfexp x hR_int
  have hV :
      frozenElliptic p u x =
        1 / 2 * (Real.exp (-1 * x) * L + Real.exp (1 * x) * R) := by
    unfold frozenElliptic
    dsimp [L, R, f]
    exact Psi_kernel_splitting hf_cub hf_nonneg x
  have hLterm :
      Real.exp (-1 * x) * L ≤
        Real.exp (-x) * (M ^ p.γ + 1 / (a - 1)) := by
    convert mul_le_mul_of_nonneg_left hL_bound (Real.exp_nonneg _) using 1
    ring
  have hRterm :
      Real.exp (1 * x) * R ≤ Real.exp (-x) * (1 / (1 + a)) := by
    calc
      Real.exp (1 * x) * R
          ≤ Real.exp (1 * x) * (Real.exp (-(1 + a) * x) / (1 + a)) :=
        mul_le_mul_of_nonneg_left hR_bound (Real.exp_nonneg _)
      _ = Real.exp (-a * x) * (1 / (1 + a)) := by
        calc
          Real.exp (1 * x) * (Real.exp (-(1 + a) * x) / (1 + a)) =
              (Real.exp (1 * x) * Real.exp (-(1 + a) * x)) *
                (1 / (1 + a)) := by ring
          _ = Real.exp (-a * x) * (1 / (1 + a)) := by
            congr 1
            rw [← Real.exp_add]
            congr 1
            ring
      _ ≤ Real.exp (-x) * (1 / (1 + a)) := by
        have hexp_le : Real.exp (-a * x) ≤ Real.exp (-x) := by
          apply Real.exp_le_exp.mpr
          nlinarith
        exact mul_le_mul_of_nonneg_right hexp_le
          (by positivity : 0 ≤ (1 / (1 + a)))
  have hpre :
      frozenElliptic p u x ≤
        1 / 2 * (Real.exp (-x) * (M ^ p.γ + 1 / (a - 1)) +
          Real.exp (-x) * (1 / (1 + a))) := by
    rw [hV]
    exact mul_le_mul_of_nonneg_left (add_le_add hLterm hRterm) (by norm_num)
  have hcoeff :=
    supercritical_coeff_bound (a := a) (B := M ^ p.γ) ha hMγ_nonneg
  have hcoeff_exp :
      (1 / 2 * (M ^ p.γ + 1 / (a - 1)) + 1 / 2 * (1 / (1 + a))) *
          Real.exp (-x) ≤
        (M ^ p.γ + a / (a ^ 2 - 1)) * Real.exp (-x) :=
    mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _)
  have htarget_coeff :
      M ^ p.γ + a / (a ^ 2 - 1) =
        (M ^ p.γ * (κ ^ 2 * p.γ ^ 2 - 1) + p.γ * κ) /
          (κ ^ 2 * p.γ ^ 2 - 1) := by
    have hden_eq : a ^ 2 - 1 = κ ^ 2 * p.γ ^ 2 - 1 := by
      dsimp [a]
      ring
    rw [← hden_eq]
    field_simp [ne_of_gt hden_pos]
    ring
  calc
    frozenElliptic p u x
        ≤ 1 / 2 * (Real.exp (-x) * (M ^ p.γ + 1 / (a - 1)) +
          Real.exp (-x) * (1 / (1 + a))) := hpre
    _ = (1 / 2 * (M ^ p.γ + 1 / (a - 1)) + 1 / 2 * (1 / (1 + a))) *
          Real.exp (-x) := by
      ring
    _ ≤ (M ^ p.γ + a / (a ^ 2 - 1)) * Real.exp (-x) := hcoeff_exp
    _ = ((M ^ p.γ * (κ ^ 2 * p.γ ^ 2 - 1) + p.γ * κ) /
          (κ ^ 2 * p.γ ^ 2 - 1)) * Real.exp (-x) := by
      rw [htarget_coeff]

theorem PaperLemma42EllipticVxEstimate_of_conditions
    {p : CMParams} {c κ κtilde M : ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M) :
    PaperLemma42EllipticVxEstimate p κ M := by
  intro u hu x hx
  have hVx_abs := frozenElliptic_deriv_abs_le p hu.cunif_bdd hu.nonneg x
  refine le_trans hVx_abs ?_
  by_cases hcrit : p.γ * κ = 1
  · rw [paperEllipticVxBound, if_pos hcrit]
    exact frozenElliptic_le_paperVxBound_critical hcrit hcond.hM hu hx
  · by_cases hsub : p.γ * κ < 1
    · rw [paperEllipticVxBound, if_neg hcrit, if_pos hsub]
      exact frozenElliptic_le_paperVxBound_subcritical hcond.hκ0 hsub hu x
    · have hsuper : 1 < p.γ * κ :=
        lt_of_le_of_ne (le_of_not_gt hsub) (Ne.symm hcrit)
      rw [paperEllipticVxBound, if_neg hcrit, if_neg hsub]
      exact frozenElliptic_le_paperVxBound_supercritical hsuper hcond.hM hu hx

theorem PaperLemma42EllipticVEstimate_of_conditions
    {p : CMParams} {c κ κtilde M : ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M) :
    PaperLemma42EllipticVEstimate p κ M := by
  intro u hu x hx
  by_cases hcrit : p.γ * κ = 1
  · rw [paperEllipticVxBound, if_pos hcrit]
    exact frozenElliptic_le_paperVxBound_critical hcrit hcond.hM hu hx
  · by_cases hsub : p.γ * κ < 1
    · rw [paperEllipticVxBound, if_neg hcrit, if_pos hsub]
      exact frozenElliptic_le_paperVxBound_subcritical hcond.hκ0 hsub hu x
    · have hsuper : 1 < p.γ * κ :=
        lt_of_le_of_ne (le_of_not_gt hsub) (Ne.symm hcrit)
      rw [paperEllipticVxBound, if_neg hcrit, if_neg hsub]
      exact frozenElliptic_le_paperVxBound_supercritical hsuper hcond.hM hu hx

/-- The paper's frozen elliptic source box is automatic on the monotone wave
trap.  The value, first-derivative, second-derivative, and monotonicity fields
come directly from the whole-line kernel/ODE identities; the final two fields
are the three-case right-tail estimates for the value and derivative. -/
theorem paperFrozenEllipticSourceBox_of_conditions
    {p : CMParams} {c κ κtilde M : ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M) :
    PaperFrozenEllipticSourceBox p κ M := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hcond.hM
  refine
    { value_nonneg := ?_
      value_le := ?_
      deriv_abs_le := ?_
      second_deriv_abs_le := ?_
      antitone := ?_
      right_tail_value := PaperLemma42EllipticVEstimate_of_conditions hcond
      right_tail_deriv := PaperLemma42EllipticVxEstimate_of_conditions hcond }
  · intro u hu x
    exact frozenElliptic_nonneg p hu.nonneg x
  · intro u hu x
    exact frozenElliptic_le_rpow_of_inWaveTrapSet p hMpos hu.trap x
  · intro u hu x
    exact le_trans
      (frozenElliptic_deriv_abs_le p hu.trap.cunif_bdd hu.nonneg x)
      (frozenElliptic_le_rpow_of_inWaveTrapSet p hMpos hu.trap x)
  · intro u hu x
    rw [frozenElliptic_deriv_deriv_eq p hu.trap.cunif_bdd hu.nonneg x]
    have hV0 : 0 ≤ frozenElliptic p u x :=
      frozenElliptic_nonneg p hu.nonneg x
    have hV1 : frozenElliptic p u x ≤ M ^ p.γ :=
      frozenElliptic_le_rpow_of_inWaveTrapSet p hMpos hu.trap x
    have huγ0 : 0 ≤ (u x) ^ p.γ := Real.rpow_nonneg (hu.nonneg x) p.γ
    have huγ1 : (u x) ^ p.γ ≤ M ^ p.γ :=
      hu.trap.rpow_le_M (by linarith [p.hγ]) x
    calc
      |frozenElliptic p u x - (u x) ^ p.γ| ≤
          |frozenElliptic p u x| + |(u x) ^ p.γ| := abs_sub _ _
      _ = frozenElliptic p u x + (u x) ^ p.γ := by
        rw [abs_of_nonneg hV0, abs_of_nonneg huγ0]
      _ ≤ 2 * M ^ p.γ := by linarith
  · intro u hu
    exact frozenElliptic_antitone_of_monotone_trap p hu

theorem PaperLemma42LogisticEstimate_of_conditions
    {p : CMParams} {c κ κtilde M D : ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D) :
    PaperLemma42LogisticEstimate p c κ κtilde M D := by
  intro u hu x hx
  have hgap_pos : 0 < κtilde - κ := sub_pos.mpr hcond.hgap
  have hx_nonneg : 0 ≤ x := by
    exact le_trans
      (lowerBarrierXMinus_nonneg_of_one_le_D hgap_pos hD_ge_one) hx.le
  have hD_pos : 0 < D := D_pos_of_paperDMin_lt hcond hD
  have hW_pos :
      0 < lowerBarrierRaw κ κtilde D x :=
    lowerBarrierRaw_pos_of_xminus_lt hgap_pos hD_pos hx
  have hW_le_exp :
      lowerBarrierRaw κ κtilde D x ≤ Real.exp (-κ * x) :=
    lowerBarrierRaw_le_exp hD_pos.le
  have hα1_pos : 0 < p.α + 1 := by linarith [p.hα]
  have hpow :
      lowerBarrierRaw κ κtilde D x *
          (lowerBarrierRaw κ κtilde D x) ^ p.α =
        (lowerBarrierRaw κ κtilde D x) ^ (p.α + 1) := by
    calc
      lowerBarrierRaw κ κtilde D x *
          (lowerBarrierRaw κ κtilde D x) ^ p.α =
        (lowerBarrierRaw κ κtilde D x) ^ (1 : ℝ) *
          (lowerBarrierRaw κ κtilde D x) ^ p.α := by
          rw [Real.rpow_one]
      _ = (lowerBarrierRaw κ κtilde D x) ^ ((1 : ℝ) + p.α) := by
          rw [← Real.rpow_add hW_pos]
      _ = (lowerBarrierRaw κ κtilde D x) ^ (p.α + 1) := by
          congr 1
          ring
  rw [hpow]
  calc
    (lowerBarrierRaw κ κtilde D x) ^ (p.α + 1)
        ≤ (Real.exp (-κ * x)) ^ (p.α + 1) :=
      Real.rpow_le_rpow hW_pos.le hW_le_exp hα1_pos.le
    _ = Real.exp (-(p.α + 1) * κ * x) := by
      rw [← Real.exp_mul]
      congr 1
      ring
    _ ≤ Real.exp (-κtilde * x) := by
      apply Real.exp_le_exp.mpr
      have hκtilde_le := hcond.kappaTilde_le_one_plus_alpha_mul_kappa
      nlinarith

set_option maxHeartbeats 1000000 in
theorem PaperLemma42KTermEstimate_of_ellipticVxEstimate
    {p : CMParams} {c κ κtilde M D : ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hVx : PaperLemma42EllipticVxEstimate p κ M) :
    PaperLemma42KTermEstimate p c κ κtilde M D := by
  intro u hu x hx
  have hgap_pos : 0 < κtilde - κ := sub_pos.mpr hcond.hgap
  have hx_nonneg : 0 ≤ x := by
    exact le_trans
      (lowerBarrierXMinus_nonneg_of_one_le_D hgap_pos hD_ge_one) hx.le
  have hD_pos : 0 < D := D_pos_of_paperDMin_lt hcond hD
  have hW_pos :
      0 < lowerBarrierRaw κ κtilde D x :=
    lowerBarrierRaw_pos_of_xminus_lt hgap_pos hD_pos hx
  have hW_nonneg : 0 ≤ lowerBarrierRaw κ κtilde D x := hW_pos.le
  have hE_pos : 0 < Real.exp (-κ * x) := Real.exp_pos _
  have hE_nonneg : 0 ≤ Real.exp (-κ * x) := hE_pos.le
  have hEt_pos : 0 < Real.exp (-κtilde * x) := Real.exp_pos _
  have hEt_nonneg : 0 ≤ Real.exp (-κtilde * x) := hEt_pos.le
  have hW_le_exp :
      lowerBarrierRaw κ κtilde D x ≤ Real.exp (-κ * x) :=
    lowerBarrierRaw_le_exp hD_pos.le
  have hderiv_le :
      |deriv (lowerBarrierRaw κ κtilde D) x| ≤
        (κ + κtilde) * Real.exp (-κ * x) :=
    lowerBarrierRaw_deriv_abs_le_on_paper_region hcond hD hx
  have hVx_le := hVx u hu x hx_nonneg
  have hB_nonneg :
      0 ≤ paperEllipticVxBound M κ p.γ x :=
    le_trans (abs_nonneg _) hVx_le
  have hm_nonneg : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hγ_nonneg : 0 ≤ p.γ := le_trans zero_le_one p.hγ
  have hκsum_nonneg : 0 ≤ κ + κtilde := by
    have hκtilde_pos : 0 < κtilde := lt_trans hcond.hκ0 hcond.hgap
    nlinarith [hcond.hκ0, hκtilde_pos]
  have hm1_nonneg : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hmγ_pos : 0 < p.m + p.γ := by linarith [p.hm, p.hγ]
  have hWm1_le :
      (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) ≤
        (Real.exp (-κ * x)) ^ (p.m - 1) :=
    Real.rpow_le_rpow hW_nonneg hW_le_exp hm1_nonneg
  have hterm1_base :
      p.m * (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) *
            |deriv (frozenElliptic p u) x| *
            |deriv (lowerBarrierRaw κ κtilde D) x| ≤
        p.m * (κ + κtilde) *
          paperEllipticVxBound M κ p.γ x *
          (Real.exp (-κ * x)) ^ p.m := by
    calc
      p.m * (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) *
            |deriv (frozenElliptic p u) x| *
            |deriv (lowerBarrierRaw κ κtilde D) x|
          ≤ p.m * (Real.exp (-κ * x)) ^ (p.m - 1) *
              paperEllipticVxBound M κ p.γ x *
              ((κ + κtilde) * Real.exp (-κ * x)) := by
            gcongr
      _ = p.m * (κ + κtilde) *
          paperEllipticVxBound M κ p.γ x *
          (Real.exp (-κ * x)) ^ p.m := by
            have hEmul :
                (Real.exp (-κ * x)) ^ (p.m - 1) *
                    Real.exp (-κ * x) =
                  (Real.exp (-κ * x)) ^ p.m := by
              calc
                (Real.exp (-κ * x)) ^ (p.m - 1) *
                    Real.exp (-κ * x) =
                  (Real.exp (-κ * x)) ^ (p.m - 1) *
                    (Real.exp (-κ * x)) ^ (1 : ℝ) := by
                    rw [Real.rpow_one]
                _ = (Real.exp (-κ * x)) ^ ((p.m - 1) + 1) := by
                    rw [← Real.rpow_add hE_pos]
                _ = (Real.exp (-κ * x)) ^ p.m := by
                    congr 1
                    ring
            calc
              p.m * (Real.exp (-κ * x)) ^ (p.m - 1) *
                    paperEllipticVxBound M κ p.γ x *
                    ((κ + κtilde) * Real.exp (-κ * x)) =
                p.m * (κ + κtilde) *
                    paperEllipticVxBound M κ p.γ x *
                    ((Real.exp (-κ * x)) ^ (p.m - 1) *
                      Real.exp (-κ * x)) := by
                    ring
              _ = p.m * (κ + κtilde) *
                    paperEllipticVxBound M κ p.γ x *
                    (Real.exp (-κ * x)) ^ p.m := by
                    rw [hEmul]
  have hterm2_base :
      lowerBarrierRaw κ κtilde D x *
          (lowerBarrierRaw κ κtilde D x) ^ (p.m + p.γ - 1) ≤
        Real.exp (-(p.m + p.γ) * κ * x) := by
    have hexp_nonneg : 0 ≤ p.m + p.γ - 1 := by linarith [p.hm, p.hγ]
    have hpow :
        lowerBarrierRaw κ κtilde D x *
            (lowerBarrierRaw κ κtilde D x) ^ (p.m + p.γ - 1) =
          (lowerBarrierRaw κ κtilde D x) ^ (p.m + p.γ) := by
      calc
        lowerBarrierRaw κ κtilde D x *
            (lowerBarrierRaw κ κtilde D x) ^ (p.m + p.γ - 1) =
          (lowerBarrierRaw κ κtilde D x) ^ (1 : ℝ) *
            (lowerBarrierRaw κ κtilde D x) ^ (p.m + p.γ - 1) := by
            rw [Real.rpow_one]
        _ = (lowerBarrierRaw κ κtilde D x) ^
            ((1 : ℝ) + (p.m + p.γ - 1)) := by
            rw [← Real.rpow_add hW_pos]
        _ = (lowerBarrierRaw κ κtilde D x) ^ (p.m + p.γ) := by
            congr 1
            ring
    rw [hpow]
    calc
      (lowerBarrierRaw κ κtilde D x) ^ (p.m + p.γ)
          ≤ (Real.exp (-κ * x)) ^ (p.m + p.γ) :=
        Real.rpow_le_rpow hW_nonneg hW_le_exp hmγ_pos.le
      _ = Real.exp (-(p.m + p.γ) * κ * x) := by
        rw [← Real.exp_mul]
        congr 1
        ring
  have hterm2 :
      lowerBarrierRaw κ κtilde D x *
          (lowerBarrierRaw κ κtilde D x) ^ (p.m + p.γ - 1) ≤
        Real.exp (-κtilde * x) := by
    refine le_trans hterm2_base ?_
    apply Real.exp_le_exp.mpr
    have hκtilde_le := hcond.kappaTilde_le_m_gamma_mul_kappa
    nlinarith
  have hEpow_m :
      (Real.exp (-κ * x)) ^ p.m = Real.exp (-(p.m * κ) * x) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  set A := p.m * (κ + κtilde) with hAdef
  have hA_nonneg : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg hm_nonneg hκsum_nonneg
  by_cases hcrit : p.γ * κ = 1
  · set C := M ^ p.γ + 3 / 4 with hCdef
    have hC_nonneg : 0 ≤ C := by
      rw [hCdef]
      exact add_nonneg
        (Real.rpow_nonneg (le_trans zero_le_one hcond.hM) p.γ) (by norm_num)
    have hC_one : 1 ≤ C := by
      rw [hCdef]
      have hMγ : 1 ≤ M ^ p.γ :=
        Real.one_le_rpow hcond.hM (by linarith [p.hγ])
      linarith
    have hterm1 :
        p.m * (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) *
              |deriv (frozenElliptic p u) x| *
              |deriv (lowerBarrierRaw κ κtilde D) x| ≤
          A * C * Real.exp (-κtilde * x) := by
      rw [paperEllipticVxBound, if_pos hcrit] at hterm1_base
      refine le_trans hterm1_base ?_
      have hexp :
          (M ^ p.γ + 3 / 4) * Real.exp (-(1 / 2) * x) *
              (Real.exp (-κ * x)) ^ p.m =
            (M ^ p.γ + 3 / 4) *
              Real.exp (-(p.m * κ + 1 / 2) * x) := by
        calc
          (M ^ p.γ + 3 / 4) * Real.exp (-(1 / 2) * x) *
              (Real.exp (-κ * x)) ^ p.m =
            (M ^ p.γ + 3 / 4) *
              (Real.exp (-(1 / 2) * x) * Real.exp (-(p.m * κ) * x)) := by
              rw [hEpow_m]
              ring
          _ = (M ^ p.γ + 3 / 4) *
              Real.exp (-(p.m * κ + 1 / 2) * x) := by
              rw [← Real.exp_add]
              congr 1
              ring
      have hexp_le :
          Real.exp (-(p.m * κ + 1 / 2) * x) ≤
            Real.exp (-κtilde * x) := by
        apply Real.exp_le_exp.mpr
        have hκtilde_le := hcond.kappaTilde_le_m_kappa_add_half
        nlinarith
      calc
        A * ((M ^ p.γ + 3 / 4) * Real.exp (-(1 / 2) * x)) *
            (Real.exp (-κ * x)) ^ p.m =
          A * C * Real.exp (-(p.m * κ + 1 / 2) * x) := by
            calc
              A * ((M ^ p.γ + 3 / 4) * Real.exp (-(1 / 2) * x)) *
                  (Real.exp (-κ * x)) ^ p.m =
                A * ((M ^ p.γ + 3 / 4) * Real.exp (-(1 / 2) * x) *
                  (Real.exp (-κ * x)) ^ p.m) := by ring
              _ = A * ((M ^ p.γ + 3 / 4) *
                    Real.exp (-(p.m * κ + 1 / 2) * x)) := by
                    rw [hexp]
              _ = A * C * Real.exp (-(p.m * κ + 1 / 2) * x) := by
                    rw [hCdef]
                    ring
        _ ≤ A * C * Real.exp (-κtilde * x) :=
            mul_le_mul_of_nonneg_left hexp_le
              (mul_nonneg hA_nonneg hC_nonneg)
    have hKcrit :
        paperSubsolutionK M κ κtilde p.m p.γ = (A + 1) * C := by
      rw [paperSubsolutionK_eq_critical hcrit, hAdef, hCdef]
      ring
    rw [hKcrit]
    calc
      p.m * (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) *
            |deriv (frozenElliptic p u) x| *
            |deriv (lowerBarrierRaw κ κtilde D) x| +
          lowerBarrierRaw κ κtilde D x *
            (lowerBarrierRaw κ κtilde D x) ^ (p.m + p.γ - 1)
          ≤ A * C * Real.exp (-κtilde * x) +
              Real.exp (-κtilde * x) := add_le_add hterm1 hterm2
      _ ≤ A * C * Real.exp (-κtilde * x) +
              C * Real.exp (-κtilde * x) := by
            have hmulC :
                Real.exp (-κtilde * x) ≤
                  C * Real.exp (-κtilde * x) :=
              by
                simpa [one_mul] using
                  mul_le_mul_of_nonneg_right hC_one hEt_nonneg
            linarith
      _ = (A + 1) * C * Real.exp (-κtilde * x) := by ring
  · by_cases hsub : p.γ * κ < 1
    · set C := 1 / (1 - p.γ ^ 2 * κ ^ 2) with hCdef
      have hγκ_pos : 0 < p.γ * κ :=
        mul_pos (by linarith [p.hγ]) hcond.hκ0
      have hden_pos : 0 < 1 - p.γ ^ 2 * κ ^ 2 := by nlinarith
      have hC_nonneg : 0 ≤ C := by
        rw [hCdef]
        exact (one_div_pos.mpr hden_pos).le
      have hC_one : 1 ≤ C := by
        rw [hCdef]
        have hden_le_one : 1 - p.γ ^ 2 * κ ^ 2 ≤ 1 := by nlinarith
        exact one_le_one_div hden_pos hden_le_one
      have hterm1 :
          p.m * (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) *
                |deriv (frozenElliptic p u) x| *
                |deriv (lowerBarrierRaw κ κtilde D) x| ≤
            A * C * Real.exp (-κtilde * x) := by
        rw [paperEllipticVxBound, if_neg hcrit, if_pos hsub] at hterm1_base
        refine le_trans hterm1_base ?_
        have hexp :
            (1 / (1 - p.γ ^ 2 * κ ^ 2)) *
                Real.exp (-(p.γ * κ) * x) *
                (Real.exp (-κ * x)) ^ p.m =
              (1 / (1 - p.γ ^ 2 * κ ^ 2)) *
                Real.exp (-(p.m + p.γ) * κ * x) := by
          calc
            (1 / (1 - p.γ ^ 2 * κ ^ 2)) *
                Real.exp (-(p.γ * κ) * x) *
                (Real.exp (-κ * x)) ^ p.m =
              (1 / (1 - p.γ ^ 2 * κ ^ 2)) *
                (Real.exp (-(p.γ * κ) * x) *
                  Real.exp (-(p.m * κ) * x)) := by
                rw [hEpow_m]
                ring
            _ = (1 / (1 - p.γ ^ 2 * κ ^ 2)) *
                Real.exp (-(p.m + p.γ) * κ * x) := by
                rw [← Real.exp_add]
                congr 1
                ring
        have hexp_le :
            Real.exp (-(p.m + p.γ) * κ * x) ≤
              Real.exp (-κtilde * x) := by
          apply Real.exp_le_exp.mpr
          have hκtilde_le := hcond.kappaTilde_le_m_gamma_mul_kappa
          nlinarith
        calc
          A * (1 / (1 - p.γ ^ 2 * κ ^ 2) *
              Real.exp (-(p.γ * κ) * x)) *
              (Real.exp (-κ * x)) ^ p.m =
            A * C * Real.exp (-(p.m + p.γ) * κ * x) := by
              calc
                A * (1 / (1 - p.γ ^ 2 * κ ^ 2) *
                    Real.exp (-(p.γ * κ) * x)) *
                    (Real.exp (-κ * x)) ^ p.m =
                  A * (1 / (1 - p.γ ^ 2 * κ ^ 2) *
                    Real.exp (-(p.γ * κ) * x) *
                    (Real.exp (-κ * x)) ^ p.m) := by ring
                _ = A * (1 / (1 - p.γ ^ 2 * κ ^ 2) *
                    Real.exp (-(p.m + p.γ) * κ * x)) := by rw [hexp]
                _ = A * C * Real.exp (-(p.m + p.γ) * κ * x) := by
                    rw [hCdef]
                    ring
          _ ≤ A * C * Real.exp (-κtilde * x) :=
              mul_le_mul_of_nonneg_left hexp_le
                (mul_nonneg hA_nonneg hC_nonneg)
      have hKsub :
          paperSubsolutionK M κ κtilde p.m p.γ = (A + 1) * C := by
        rw [paperSubsolutionK_eq_subcritical hsub, hAdef, hCdef]
        ring
      rw [hKsub]
      calc
        p.m * (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) *
              |deriv (frozenElliptic p u) x| *
              |deriv (lowerBarrierRaw κ κtilde D) x| +
            lowerBarrierRaw κ κtilde D x *
              (lowerBarrierRaw κ κtilde D x) ^ (p.m + p.γ - 1)
            ≤ A * C * Real.exp (-κtilde * x) +
                Real.exp (-κtilde * x) := add_le_add hterm1 hterm2
        _ ≤ A * C * Real.exp (-κtilde * x) +
                C * Real.exp (-κtilde * x) := by
              have hmulC :
                  Real.exp (-κtilde * x) ≤
                    C * Real.exp (-κtilde * x) :=
                by
                  simpa [one_mul] using
                    mul_le_mul_of_nonneg_right hC_one hEt_nonneg
              linarith
        _ = (A + 1) * C * Real.exp (-κtilde * x) := by ring
    · have hsuper : 1 < p.γ * κ :=
        lt_of_le_of_ne (le_of_not_gt hsub) (Ne.symm hcrit)
      set C :=
        (M ^ p.γ * (κ ^ 2 * p.γ ^ 2 - 1) + p.γ * κ) /
          (κ ^ 2 * p.γ ^ 2 - 1) with hCdef
      have hden_pos : 0 < κ ^ 2 * p.γ ^ 2 - 1 := by
        have hγκ_nonneg : 0 ≤ p.γ * κ :=
          mul_nonneg hγ_nonneg hcond.hκ0.le
        have hs : 1 < (p.γ * κ) ^ 2 :=
          (one_lt_sq_iff₀ hγκ_nonneg).mpr hsuper
        have hsq : (p.γ * κ) ^ 2 = κ ^ 2 * p.γ ^ 2 := by ring
        rw [← hsq]
        exact sub_pos.mpr hs
      have hC_one : 1 ≤ C := by
        rw [hCdef]
        have hMγ : 1 ≤ M ^ p.γ :=
          Real.one_le_rpow hcond.hM hγ_nonneg
        rw [le_div_iff₀ hden_pos]
        have hden_le :
            1 * (κ ^ 2 * p.γ ^ 2 - 1) ≤
              M ^ p.γ * (κ ^ 2 * p.γ ^ 2 - 1) :=
          mul_le_mul_of_nonneg_right hMγ hden_pos.le
        have hγκ_nonneg : 0 ≤ p.γ * κ :=
          mul_nonneg hγ_nonneg hcond.hκ0.le
        exact le_trans hden_le (le_add_of_nonneg_right hγκ_nonneg)
      have hC_nonneg : 0 ≤ C := by
        exact le_trans (by norm_num : (0 : ℝ) ≤ 1) hC_one
      have hterm1 :
          p.m * (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) *
                |deriv (frozenElliptic p u) x| *
                |deriv (lowerBarrierRaw κ κtilde D) x| ≤
            A * C * Real.exp (-κtilde * x) := by
        rw [paperEllipticVxBound, if_neg hcrit, if_neg hsub] at hterm1_base
        refine le_trans hterm1_base ?_
        have hexp :
            ((M ^ p.γ * (κ ^ 2 * p.γ ^ 2 - 1) + p.γ * κ) /
                (κ ^ 2 * p.γ ^ 2 - 1)) *
                Real.exp (-x) * (Real.exp (-κ * x)) ^ p.m =
              ((M ^ p.γ * (κ ^ 2 * p.γ ^ 2 - 1) + p.γ * κ) /
                (κ ^ 2 * p.γ ^ 2 - 1)) *
                Real.exp (-(p.m * κ + 1) * x) := by
          calc
            ((M ^ p.γ * (κ ^ 2 * p.γ ^ 2 - 1) + p.γ * κ) /
                (κ ^ 2 * p.γ ^ 2 - 1)) *
                Real.exp (-x) * (Real.exp (-κ * x)) ^ p.m =
              ((M ^ p.γ * (κ ^ 2 * p.γ ^ 2 - 1) + p.γ * κ) /
                (κ ^ 2 * p.γ ^ 2 - 1)) *
                (Real.exp (-x) * Real.exp (-(p.m * κ) * x)) := by
                rw [hEpow_m]
                ring
            _ = ((M ^ p.γ * (κ ^ 2 * p.γ ^ 2 - 1) + p.γ * κ) /
                (κ ^ 2 * p.γ ^ 2 - 1)) *
                Real.exp (-(p.m * κ + 1) * x) := by
                rw [← Real.exp_add]
                congr 1
                ring
        have hexp_le :
            Real.exp (-(p.m * κ + 1) * x) ≤
              Real.exp (-κtilde * x) := by
          apply Real.exp_le_exp.mpr
          have hκtilde_le := hcond.kappaTilde_le_m_kappa_add_half
          have hle : κtilde ≤ p.m * κ + 1 := by linarith
          have hmul := mul_le_mul_of_nonneg_right hle hx_nonneg
          linarith
        calc
          A * (((M ^ p.γ * (κ ^ 2 * p.γ ^ 2 - 1) + p.γ * κ) /
              (κ ^ 2 * p.γ ^ 2 - 1)) * Real.exp (-x)) *
              (Real.exp (-κ * x)) ^ p.m =
            A * C * Real.exp (-(p.m * κ + 1) * x) := by
              calc
                A * (((M ^ p.γ * (κ ^ 2 * p.γ ^ 2 - 1) + p.γ * κ) /
                    (κ ^ 2 * p.γ ^ 2 - 1)) * Real.exp (-x)) *
                    (Real.exp (-κ * x)) ^ p.m =
                  A * (((M ^ p.γ * (κ ^ 2 * p.γ ^ 2 - 1) + p.γ * κ) /
                    (κ ^ 2 * p.γ ^ 2 - 1)) * Real.exp (-x) *
                    (Real.exp (-κ * x)) ^ p.m) := by ring
                _ = A * (((M ^ p.γ * (κ ^ 2 * p.γ ^ 2 - 1) + p.γ * κ) /
                    (κ ^ 2 * p.γ ^ 2 - 1)) *
                    Real.exp (-(p.m * κ + 1) * x)) := by rw [hexp]
                _ = A * C * Real.exp (-(p.m * κ + 1) * x) := by
                    rw [hCdef]
                    ring
          _ ≤ A * C * Real.exp (-κtilde * x) :=
              mul_le_mul_of_nonneg_left hexp_le
                (mul_nonneg hA_nonneg hC_nonneg)
      have hKsuper :
          paperSubsolutionK M κ κtilde p.m p.γ = (A + 1) * C := by
        rw [paperSubsolutionK_eq_supercritical hsuper, hAdef, hCdef]
        ring_nf
      rw [hKsuper]
      calc
        p.m * (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) *
              |deriv (frozenElliptic p u) x| *
              |deriv (lowerBarrierRaw κ κtilde D) x| +
            lowerBarrierRaw κ κtilde D x *
              (lowerBarrierRaw κ κtilde D x) ^ (p.m + p.γ - 1)
            ≤ A * C * Real.exp (-κtilde * x) +
                Real.exp (-κtilde * x) := add_le_add hterm1 hterm2
        _ ≤ A * C * Real.exp (-κtilde * x) +
                C * Real.exp (-κtilde * x) := by
              have hmulC :
                  Real.exp (-κtilde * x) ≤
                    C * Real.exp (-κtilde * x) :=
                by
                  simpa [one_mul] using
                    mul_le_mul_of_nonneg_right hC_one hEt_nonneg
              linarith
        _ = (A + 1) * C * Real.exp (-κtilde * x) := by ring

theorem PaperLemma42KTermEstimate_of_conditions
    {p : CMParams} {c κ κtilde M D : ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D) :
    PaperLemma42KTermEstimate p c κ κtilde M D :=
  PaperLemma42KTermEstimate_of_ellipticVxEstimate hcond hD hD_ge_one
    (paperFrozenEllipticSourceBox_of_conditions hcond).right_tail_deriv

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

theorem PaperLemma_4_2_paperWaveOperator_of_conditions
    {p : CMParams} {c κ κtilde M D : ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (u : ℝ → ℝ) (hu : InWaveTrapSet κ M u) :
    IsPaperFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
      (Set.Ioi (lowerBarrierXMinus κ κtilde D)) :=
  PaperLemma_4_2_paperWaveOperator_from_components hcond hD
    (PaperLemma42LogisticEstimate_of_conditions hcond hD hD_ge_one)
    (PaperLemma42KTermEstimate_of_conditions hcond hD hD_ge_one)
    u hu

/-- The non-step side data needed to compare one paper implicit iterate with the
raw lower barrier.  The step equation itself is supplied by the paper Rothe
producer; the paper subsolution is supplied by Lemma 4.2. -/
structure PaperLowerRawStepAux
    (p : CMParams) (c lam M κ κtilde D C_chem : ℝ)
    (La Lb : ℝ) (u W : ℝ → ℝ) : Prop where
  hCB : (1 / lam) * (reactionLip p.α M + C_chem) < 1
  φcont : Continuous (fun x => lowerBarrierRaw κ κtilde D x - W x)
  hbot : Tendsto (fun x => lowerBarrierRaw κ κtilde D x - W x) atBot (𝓝 La)
  hLa : La ≤ 0
  htop : Tendsto (fun x => lowerBarrierRaw κ κtilde D x - W x) atTop (𝓝 Lb)
  hLb : Lb ≤ 0
  region : ∀ x₀,
    IsMaxOn (fun x => lowerBarrierRaw κ κtilde D x - W x) Set.univ x₀ →
      x₀ ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D)
  paperDiff : ∀ x₀,
    IsMaxOn (fun x => lowerBarrierRaw κ κtilde D x - W x) Set.univ x₀ →
      paperWaveOperator p c u (lowerBarrierRaw κ κtilde D) x₀ -
          paperWaveOperator p c u W x₀
        ≤ (reactionLip p.α M + C_chem) *
            (lowerBarrierRaw κ κtilde D x₀ - W x₀)

theorem paperLowerBarrierStepData_lowerBarrierRaw_of_paperStep
    {p : CMParams} {c lam M κ κtilde D Λ C_chem La Lb : ℝ} {u Z W : ℝ → ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hu : InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u)
    (hprev : ∀ x, lowerBarrierRaw κ κtilde D x ≤ Z x)
    (hlam : 0 < lam)
    (hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x)
    (haux : PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u W) :
    PaperLowerBarrierStepData p c lam M κ Λ C_chem La Lb
      (Set.Ioi (lowerBarrierXMinus κ κtilde D)) u Z W
      (lowerBarrierRaw κ κtilde D) := by
  exact
    { hlam := hlam
      step_op := hstep
      hCB := haux.hCB
      AZ := hprev
      φcont := haux.φcont
      hbot := haux.hbot
      hLa := haux.hLa
      htop := haux.htop
      hLb := haux.hLb
      paperSub :=
        PaperLemma_4_2_paperWaveOperator_of_conditions hcond hD hD_ge_one
          u hu.bare.1
      region := haux.region
      paperDiff := haux.paperDiff }

theorem rotheStepLowerInvariant_lowerBarrierRaw_of_paperStepData
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hstepData : ∀ u,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
        ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤ rotheSeq u k x) →
          ∃ C_chem La Lb,
            (0 < lam) ∧
            (∀ x, paperImplicitStepOp p c (1 / lam) u
              (rotheSeq u (k + 1)) x = rotheSeq u k x) ∧
            PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
              (rotheSeq u (k + 1))) :
    RotheStepLowerInvariant κ M (lowerBarrierRaw κ κtilde D) rotheSeq := by
  apply rotheStepLowerInvariant_of_paperBarrierData
  intro u hu k hprev
  obtain ⟨C_chem, La, Lb, hlam, hstep, haux⟩ := hstepData u hu k hprev
  refine ⟨C_chem, La, Lb, Set.Ioi (lowerBarrierXMinus κ κtilde D), ?_⟩
  exact paperLowerBarrierStepData_lowerBarrierRaw_of_paperStep
    (Λ := Λ) hcond hD hD_ge_one hu hprev hlam hstep haux

theorem rotheSeqOfPaper_lowerBarrierRaw_stepInvariant
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hprodAll : ∀ u, PaperRotheStepProducer p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hauxData : ∀ u,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
        ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
          rotheSeqOfPaper p c lam M κ Λ u (hprodAll u) hκ hM k x) →
          ∃ C_chem La Lb,
            PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
              (rotheSeqOfPaper p c lam M κ Λ u (hprodAll u) hκ hM
                (k + 1))) :
    RotheStepLowerInvariant κ M (lowerBarrierRaw κ κtilde D)
      (fun u => rotheSeqOfPaper p c lam M κ Λ u (hprodAll u) hκ hM) := by
  refine rotheStepLowerInvariant_lowerBarrierRaw_of_paperStepData
    (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
    (κtilde := κtilde) (D := D) (Λ := Λ)
    hcond hD hD_ge_one ?_
  intro u hu k hprev
  obtain ⟨C_chem, La, Lb, haux⟩ := hauxData u hu k hprev
  have hfacts := rotheSeqOfPaper_stepFacts (hprodAll u) hκ hM k
  exact ⟨C_chem, La, Lb, (hprodAll u).hlam, hfacts.step_op, haux⟩

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

theorem rotheSeqOfPaper_profileNontrivial_of_lowerBarrierRaw
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hprodAll : ∀ u, PaperRotheStepProducer p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hauxData : ∀ u,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
        ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
          rotheSeqOfPaper p c lam M κ Λ u (hprodAll u) hκ hM k x) →
          ∃ C_chem La Lb,
            PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
              (rotheSeqOfPaper p c lam M κ Λ u (hprodAll u) hκ hM
                (k + 1))) :
    ∀ u, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
      ∀ k, ProfileNontrivial
        (rotheSeqOfPaper p c lam M κ Λ u (hprodAll u) hκ hM k) := by
  have hstep :
      RotheStepLowerInvariant κ M (lowerBarrierRaw κ κtilde D)
        (fun u => rotheSeqOfPaper p c lam M κ Λ u (hprodAll u) hκ hM) :=
    rotheSeqOfPaper_lowerBarrierRaw_stepInvariant hcond hD hD_ge_one
      hprodAll hκ hM hauxData
  exact rotheOrbit_profileNontrivial_of_lowerBarrierRaw_stepInvariant hcond hD
    (fun u hu => rotheSeqOfPaper_lowerPinned_base (hprodAll u) hκ hM hu)
    hstep

/-- The paper-step Rothe sequence with the scalar proofs bundled by
`PaperLemma42ExactConditions`.  This keeps the final paper wrapper's hypotheses
readable while still using the exact paper conditions, including `hα_le`. -/
def rotheSeqOfPaperFromCond
    (p : CMParams) (c lam M κ κtilde Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hprodAll : ∀ u, PaperRotheStepProducer p c lam M κ Λ u) :
    (ℝ → ℝ) → ℕ → ℝ → ℝ :=
  fun u => rotheSeqOfPaper p c lam M κ Λ u (hprodAll u)
    hcond.hκ0.le (le_trans zero_le_one hcond.hM)

/-- Paper-step producer strengthened with the lower-raw comparison payload.

The extra field is exactly the per-step data consumed by the paper
max-principle after Lemma 4.2 has supplied the raw lower subsolution. -/
structure PaperLowerRawStepProducer
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (u : ℝ → ℝ) : Prop where
  producer : PaperRotheStepProducer p c lam M κ Λ u
  lowerRawAux :
    InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
      ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
        rotheSeqOfPaper p c lam M κ Λ u producer hκ hM k x) →
        ∃ C_chem La Lb,
          PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
            (rotheSeqOfPaper p c lam M κ Λ u producer hκ hM (k + 1))

/-- Thinner lower-raw step producer: the paper Rothe step is supplied by the
bounded-source Green core, so Green tails and raw-convolution bookkeeping are
closed by `paperGreenStepInput_of_core`. -/
structure PaperLowerRawStepProducerCore
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (u : ℝ → ℝ) : Type where
  green : PaperGreenStepInputCore p c lam M κ Λ u
  lowerRawAux :
    InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
      ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
        rotheSeqOfPaper p c lam M κ Λ u
          (paperRotheStepProducer_of_greenCore green) hκ hM k x) →
        ∃ C_chem La Lb,
          PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
            (rotheSeqOfPaper p c lam M κ Λ u
              (paperRotheStepProducer_of_greenCore green) hκ hM (k + 1))

/-- Fill the old lower-raw step producer from the thinner Green core. -/
def paperLowerRawStepProducer_of_core
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ} {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    {u : ℝ → ℝ}
    (h : PaperLowerRawStepProducerCore p c lam M κ κtilde D Λ hκ hM u) :
    PaperLowerRawStepProducer p c lam M κ κtilde D Λ hκ hM u where
  producer := paperRotheStepProducer_of_greenCore h.green
  lowerRawAux := h.lowerRawAux

/-- Route-A version of the lower-raw step producer core.  The Rothe producer is
the one assembled from `PaperGreenStepInputRouteACore`; the raw lower-barrier
auxiliary data is stated against that exact paper Rothe sequence. -/
structure PaperLowerRawStepProducerRouteACore
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (u : ℝ → ℝ) : Type where
  green : PaperGreenStepInputRouteACore p c lam M κ Λ u
  lowerRawAux :
    InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
      ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
        rotheSeqOfPaper p c lam M κ Λ u
          (paperRotheStepProducer_of_routeA_greenCore green) hκ hM k x) →
        ∃ C_chem La Lb,
          PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
            (rotheSeqOfPaper p c lam M κ Λ u
              (paperRotheStepProducer_of_routeA_greenCore green) hκ hM (k + 1))

/-- Fill the live lower-raw producer from the Route-A per-step Green core and
the lower-raw auxiliary payload for the same induced paper Rothe sequence. -/
def paperLowerRawStepProducer_of_routeA
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ} {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    {u : ℝ → ℝ}
    (green : PaperGreenStepInputRouteACore p c lam M κ Λ u)
    (lowerRawAux :
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
        ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
          rotheSeqOfPaper p c lam M κ Λ u
            (paperRotheStepProducer_of_routeA_greenCore green) hκ hM k x) →
          ∃ C_chem La Lb,
            PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
              (rotheSeqOfPaper p c lam M κ Λ u
                (paperRotheStepProducer_of_routeA_greenCore green) hκ hM (k + 1))) :
    PaperLowerRawStepProducer p c lam M κ κtilde D Λ hκ hM u where
  producer := paperRotheStepProducer_of_routeA_greenCore green
  lowerRawAux := lowerRawAux

/-- Core-packaged form of `paperLowerRawStepProducer_of_routeA`. -/
def paperLowerRawStepProducer_of_routeA_core
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ} {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    {u : ℝ → ℝ}
    (h : PaperLowerRawStepProducerRouteACore p c lam M κ κtilde D Λ hκ hM u) :
    PaperLowerRawStepProducer p c lam M κ κtilde D Λ hκ hM u :=
  paperLowerRawStepProducer_of_routeA h.green h.lowerRawAux

/-- All live lower-raw producers from Route-A per-step Green cores. -/
theorem paperLowerRawStepProducer_all_of_routeA
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ} {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (hinput :
      ∀ u : ℝ → ℝ,
        PaperLowerRawStepProducerRouteACore p c lam M κ κtilde D Λ hκ hM u) :
    ∀ u : ℝ → ℝ,
      PaperLowerRawStepProducer p c lam M κ κtilde D Λ hκ hM u :=
  fun u => paperLowerRawStepProducer_of_routeA_core (hinput u)

/-- The paper Rothe parabolic floor: strengthened one-step production, the
base-barrier Lipschitz bound, fixed-step dependence, and uniform tail. -/
structure PaperLowerRawParabolicFloor
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Prop where
  producer :
    ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ hκ hM u
  barLip :
    ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|
  step :
    PaperRotheSeqStepDependence p c lam M κ Λ
      (fun u => (producer u).producer) hκ hM
  tail :
    PaperRotheTailUniform p c lam M κ Λ
      (fun u => (producer u).producer) hκ hM

/-- The paper Rothe parabolic floor with the base-barrier Lipschitz field
removed.  The missing scalar field is automatic under either paper Lemma 4.2
parameter package. -/
structure PaperLowerRawParabolicFloorNoBar
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Prop where
  producer :
    ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ hκ hM u
  step :
    PaperRotheSeqStepDependence p c lam M κ Λ
      (fun u => (producer u).producer) hκ hM
  tail :
    PaperRotheTailUniform p c lam M κ Λ
      (fun u => (producer u).producer) hκ hM

/-- Fill the full paper parabolic floor from the no-`barLip` floor under the
χ≤0 Lemma 4.2 parameter conditions. -/
def paperLowerRawParabolicFloor_of_noBar
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (h : PaperLowerRawParabolicFloorNoBar p c lam M κ κtilde D Λ hκ hM) :
    PaperLowerRawParabolicFloor p c lam M κ κtilde D Λ hκ hM where
  producer := h.producer
  barLip := hcond.upperBarrier_barLip
  step := h.step
  tail := h.tail

/-- Thinner paper Rothe parabolic floor after closing bounded-source Green
bookkeeping.  The remaining producer core still carries source construction,
sliding comparison data, comparison tails for the max principles, lower-raw aux
data, and the step/tail dependence floors. -/
structure PaperLowerRawParabolicFloorCore
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Type where
  producer :
    ∀ u, PaperLowerRawStepProducerCore p c lam M κ κtilde D Λ hκ hM u
  barLip :
    ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|
  step :
    PaperRotheSeqStepDependence p c lam M κ Λ
      (fun u => paperRotheStepProducer_of_greenCore ((producer u).green)) hκ hM
  tail :
    PaperRotheTailUniform p c lam M κ Λ
      (fun u => paperRotheStepProducer_of_greenCore ((producer u).green)) hκ hM

/-- Fill the old paper parabolic floor from the thinner core. -/
def paperLowerRawParabolicFloor_of_core
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ} {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (h : PaperLowerRawParabolicFloorCore p c lam M κ κtilde D Λ hκ hM) :
    PaperLowerRawParabolicFloor p c lam M κ κtilde D Λ hκ hM where
  producer := fun u => paperLowerRawStepProducer_of_core (h.producer u)
  barLip := h.barLip
  step := h.step
  tail := h.tail

/-- Core paper Rothe parabolic floor with the automatic base-barrier Lipschitz
field removed. -/
structure PaperLowerRawParabolicFloorCoreNoBar
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Type where
  producer :
    ∀ u, PaperLowerRawStepProducerCore p c lam M κ κtilde D Λ hκ hM u
  step :
    PaperRotheSeqStepDependence p c lam M κ Λ
      (fun u => paperRotheStepProducer_of_greenCore ((producer u).green)) hκ hM
  tail :
    PaperRotheTailUniform p c lam M κ Λ
      (fun u => paperRotheStepProducer_of_greenCore ((producer u).green)) hκ hM

/-- Fill the core paper parabolic floor from the no-`barLip` core under the
χ≤0 Lemma 4.2 parameter conditions. -/
def paperLowerRawParabolicFloorCore_of_noBar
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (h : PaperLowerRawParabolicFloorCoreNoBar
      p c lam M κ κtilde D Λ hκ hM) :
    PaperLowerRawParabolicFloorCore p c lam M κ κtilde D Λ hκ hM where
  producer := h.producer
  barLip := hcond.upperBarrier_barLip
  step := h.step
  tail := h.tail

/-- Route-A paper Rothe parabolic floor after the per-step Route-A producer has
been paired with the lower-raw auxiliary data. -/
structure PaperLowerRawParabolicFloorRouteACore
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Type where
  producer :
    ∀ u, PaperLowerRawStepProducerRouteACore p c lam M κ κtilde D Λ hκ hM u
  barLip :
    ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|
  step :
    PaperRotheSeqStepDependence p c lam M κ Λ
      (fun u => paperRotheStepProducer_of_routeA_greenCore ((producer u).green)) hκ hM
  tail :
    PaperRotheTailUniform p c lam M κ Λ
      (fun u => paperRotheStepProducer_of_routeA_greenCore ((producer u).green)) hκ hM

/-- Route-A paper Rothe parabolic floor with the base-barrier Lipschitz field
removed.  Under `PaperLemma42ExactConditions`, `upperBarrier` is automatically
`M`-Lipschitz, so callers do not need to carry this scalar side condition. -/
structure PaperLowerRawParabolicFloorRouteACoreNoBar
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Type where
  producer :
    ∀ u, PaperLowerRawStepProducerRouteACore p c lam M κ κtilde D Λ hκ hM u
  step :
    PaperRotheSeqStepDependence p c lam M κ Λ
      (fun u => paperRotheStepProducer_of_routeA_greenCore ((producer u).green)) hκ hM
  tail :
    PaperRotheTailUniform p c lam M κ Λ
      (fun u => paperRotheStepProducer_of_routeA_greenCore ((producer u).green)) hκ hM

/-- Fill the `barLip` field of the Route-A floor from the paper Lemma 4.2
parameter conditions. -/
def paperLowerRawParabolicFloorRouteACore_of_noBar
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (h : PaperLowerRawParabolicFloorRouteACoreNoBar
      p c lam M κ κtilde D Λ hκ hM) :
    PaperLowerRawParabolicFloorRouteACore
      p c lam M κ κtilde D Λ hκ hM where
  producer := h.producer
  barLip := hcond.upperBarrier_barLip
  step := h.step
  tail := h.tail

/-- Fill the live paper parabolic floor from the Route-A lower-raw core. -/
def paperLowerRawParabolicFloor_of_routeA_core
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ} {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (h : PaperLowerRawParabolicFloorRouteACore p c lam M κ κtilde D Λ hκ hM) :
    PaperLowerRawParabolicFloor p c lam M κ κtilde D Λ hκ hM where
  producer := fun u => paperLowerRawStepProducer_of_routeA_core (h.producer u)
  barLip := h.barLip
  step := h.step
  tail := h.tail

/-- The shared stationary-limit and left-flat convergence floor for a pinned
paper Rothe map. -/
structure PaperLowerPinnedStationaryFlatFloor
    (p : CMParams) (c κ M : ℝ) (φ : ℝ → ℝ)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ) : Prop where
  stationary :
    ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      rotheLimit (rotheSeq U) = U →
        ∀ x, frozenWaveOperator p c U U x = 0
  flat :
    ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U

/-- Build the existing stationary/flat floor from the sharper paper
Rothe-limit step consistency floor plus the regularity needed for the
committed paper=frozen operator identity. -/
theorem PaperLowerPinnedStationaryFlatFloor.of_stepConsistency
    (p : CMParams) (c lam κ M : ℝ) (φ : ℝ → ℝ)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hlam : 0 < lam)
    (hcons : PaperRotheLimitStepConsistency p c lam κ M φ rotheSeq)
    (hU_diff : ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      ∀ x, DifferentiableAt ℝ U x)
    (hV_diff : ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      ∀ x, DifferentiableAt ℝ (deriv (frozenElliptic p U)) x)
    (hU_rpow_diff : ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      ∀ x, DifferentiableAt ℝ (fun y => (U y) ^ p.m) x)
    (hflat : ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    PaperLowerPinnedStationaryFlatFloor p c κ M φ rotheSeq where
  stationary :=
    paperLowerPinned_stationary_of_stepConsistency p c lam κ M φ rotheSeq
      hlam hcons hU_diff hV_diff hU_rpow_diff
  flat := hflat

/-- Project the bulky per-step lower comparison data from the strengthened
paper-step producer.  Lemma 4.2 is then consumed by
`rotheSeqOfPaper_lowerBarrierRaw_stepInvariant`. -/
theorem hauxData_of_conditions
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (_hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (_hD_ge_one : 1 ≤ D)
    (hprodAll : ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ
      hcond.hκ0.le (le_trans zero_le_one hcond.hM) u) :
    ∀ u,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
        ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
          rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
            (fun v => (hprodAll v).producer) u k x) →
          ∃ C_chem La Lb,
            PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
              (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
                (fun v => (hprodAll v).producer) u (k + 1)) := by
  intro u hu k hprev
  simpa [rotheSeqOfPaperFromCond] using
    (hprodAll u).lowerRawAux hu k hprev

/-- ODE-realization frontier for the stationary strong maximum principle when
the paper parameters are presented as `CMParams` plus a speed. -/
def StationaryStrongMaxPrincipleODERealization
    (p : CMParams) (c κ M : ℝ) : Prop :=
  ∃ q : ShenWork.PDE.TravelingWaveODE.Params,
    q.toCMParams = p ∧ q.c = c ∧
      StationaryTravelingWaveODERealization q κ M

theorem hsmp_of_odeRealization
    {p : CMParams} {c κ M : ℝ}
    (hrealize : StationaryStrongMaxPrincipleODERealization p c κ M) :
    StationaryStrongMaxPrinciple p c κ M := by
  rcases hrealize with ⟨q, hp, hc, hq⟩
  rw [← hp, ← hc]
  exact stationaryStrongMaxPrinciple_of_odeRealization hq

/-- Paper-step χ≤0 existence on the raw lower-pinned trap.

The Schauder fixed point is selected inside
`InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D)`, so
non-triviality is discharged here from the genuine lower pin.  Positivity then
comes from the stationary strong maximum principle, and the left endpoint from
the flat/root-pin route. -/
theorem b1_chiNeg_existence_paper
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperRotheStepProducer p c lam M κ Λ u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
      (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond hprodAll))
    (hauxData : ∀ u,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
        ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
          rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond hprodAll u k x) →
          ∃ C_chem La Lb,
            PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
              (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond hprodAll u
                (k + 1)))
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple
        (InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D)))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond hprodAll U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hsmp : StationaryStrongMaxPrinciple p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U := by
  let zseq :=
    rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond hprodAll
  have hM0 : 0 ≤ M := le_trans zero_le_one hcond.hM
  have hcpos : 0 < c := by
    rw [hcond.hc]
    have hinv : 0 < κ⁻¹ := inv_pos.mpr hcond.hκ0
    nlinarith [hcond.hκ0, hinv]
  have hstep :
      RotheStepLowerInvariant κ M (lowerBarrierRaw κ κtilde D) zseq := by
    have haux' : ∀ u,
        InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
          ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
            rotheSeqOfPaper p c lam M κ Λ u (hprodAll u) hcond.hκ0.le hM0 k x) →
            ∃ C_chem La Lb,
              PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
                (rotheSeqOfPaper p c lam M κ Λ u (hprodAll u)
                  hcond.hκ0.le hM0 (k + 1)) := by
      simpa [zseq, rotheSeqOfPaperFromCond, hM0] using hauxData
    simpa [zseq, rotheSeqOfPaperFromCond, hM0] using
      rotheSeqOfPaper_lowerBarrierRaw_stepInvariant hcond hD hD_ge_one
        hprodAll hcond.hκ0.le hM0 haux'
  have hlower :
      RotheOrbitLowerBound κ M (lowerBarrierRaw κ κtilde D) zseq :=
    rotheOrbitLowerBound_of_stepLowerInvariant
      (fun u hu => by
        simpa [zseq, rotheSeqOfPaperFromCond, hM0] using
          rotheSeqOfPaper_lowerPinned_base (hprodAll u) hcond.hκ0.le hM0 hu)
      hstep
  have hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheOrbitData p c lam M κ zseq u := by
    intro u _hu
    simpa [zseq, rotheSeqOfPaperFromCond, hM0] using
      paperRotheOrbitData (p := p) (c := c) (lam := lam) (M := M)
        (κ := κ) (Λ := Λ) (u := u) hprodAll hcond.hκ0.le hM0
        hΛ0 hΛM hbarLip
  obtain ⟨U, hU, hfix⟩ :=
    paperLowerPinnedSchauder_fixedPoint p c lam M κ
      (lowerBarrierRaw κ κtilde D) hM0 zseq hŪbdd
      (helly_pointwise_selection M) hdep hdata hlower hprinciple
  have hstat : ∀ x, frozenWaveOperator p c U U x = 0 :=
    hstationary U hU (by simpa [zseq] using hfix)
  have hnontriv : ProfileNontrivial U :=
    profileNontrivial_of_lowerBarrierRaw_tail_bound hcond hD
      (fun x _hx => hU.lower x)
  have hpos : ∀ x, 0 < U x :=
    hsmp U hU.bare hstat hnontriv
  have hlim_neg : Tendsto U atBot (𝓝 1) :=
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_nontrivial
      hU.bare hsmp hnontriv (hflat U hU hstat) hstat
  have hlim_pos : Tendsto U atTop (𝓝 0) :=
    hU.bare.tendsto_atTop_zero hcond.hκ0
  exact ⟨U, hU,
    FrozenStationaryWaveProfile.mk_auto_limits hcpos hpos
      hU.bare.trap.cunif_bdd hstat hlim_neg hlim_pos⟩

/-- Variant with `hauxData` discharged into the named lower-raw paper-step
producer, and `hsmp` supplied through the ODE realization frontier. -/
theorem b1_chiNeg_existence_paper'
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ
      hcond.hκ0.le (le_trans zero_le_one hcond.hM) u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
      (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
        (fun u => (hprodAll u).producer)))
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple
        (InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D)))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
            (fun u => (hprodAll u).producer) U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hrealize : StationaryStrongMaxPrincipleODERealization p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U := by
  exact b1_chiNeg_existence_paper p c lam M κ κtilde D Λ hcond hD
    hD_ge_one hΛ0 hΛM (fun u => (hprodAll u).producer) hbarLip
    (upperBarrier_isBddFun (le_trans zero_le_one hcond.hM)) hdep
    (hauxData_of_conditions hcond hD hD_ge_one hprodAll) hprinciple
    hstationary (hsmp_of_odeRealization hrealize) hflat

/-- Headline χ≤0 paper existence with the lower-raw comparison, the paper
step/tail dependence frontier, and the stationary maximum principle routed
through named producer/ODE frontiers. -/
theorem b1_chiNeg_existence_paper_clean
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ
      hcond.hκ0.le (le_trans zero_le_one hcond.hM) u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hstep : PaperRotheSeqStepDependence p c lam M κ Λ
      (fun u => (hprodAll u).producer) hcond.hκ0.le
      (le_trans zero_le_one hcond.hM))
    (htail : PaperRotheTailUniform p c lam M κ Λ
      (fun u => (hprodAll u).producer) hcond.hκ0.le
      (le_trans zero_le_one hcond.hM))
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple
        (InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D)))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
            (fun u => (hprodAll u).producer) U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hrealize : StationaryStrongMaxPrincipleODERealization p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_paper' p c lam M κ κtilde D Λ hcond hD
    hD_ge_one hΛ0 hΛM hprodAll hbarLip
    (by
      simpa [rotheSeqOfPaperFromCond] using
        paperRotheContinuousDependence p c lam M κ Λ
          (fun u => (hprodAll u).producer) hcond.hκ0.le
          (le_trans zero_le_one hcond.hM) hstep htail)
    hprinciple hstationary
    hrealize hflat

/-- Minimal χ≤0 paper wrapper: the Rothe producer, fixed-step dependence,
uniform tail, and base-barrier Lipschitz bound are a single parabolic floor; the
stationary-limit and flat-left obligations are the shared convergence floor. -/
theorem b1_chiNeg_existence_paper_min
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hpar :
      PaperLowerRawParabolicFloor p c lam M κ κtilde D Λ
        hcond.hκ0.le (le_trans zero_le_one hcond.hM))
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple
        (InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D)))
    (hconv :
      PaperLowerPinnedStationaryFlatFloor p c κ M
        (lowerBarrierRaw κ κtilde D)
        (rotheSeqOfPaperFromCond p c lam M κ κtilde Λ hcond
          (fun u => (hpar.producer u).producer)))
    (hsmp : StationaryStrongMaxPrinciple p c κ M) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_paper p c lam M κ κtilde D Λ hcond hD
    hD_ge_one hΛ0 hΛM (fun u => (hpar.producer u).producer)
    hpar.barLip (upperBarrier_isBddFun (le_trans zero_le_one hcond.hM))
    (by
      simpa [rotheSeqOfPaperFromCond] using
        paperRotheContinuousDependence p c lam M κ Λ
          (fun u => (hpar.producer u).producer) hcond.hκ0.le
          (le_trans zero_le_one hcond.hM) hpar.step hpar.tail)
    (hauxData_of_conditions hcond hD hD_ge_one hpar.producer)
    hprinciple hconv.stationary hsmp hconv.flat

/-! ## Positive-sensitivity paper branch -/

/-- The exact positive-sensitivity hypotheses used by the paper lower-barrier
estimate and lower-pinned Rothe close. -/
structure PositivePaperLemma42ExactConditions
    (p : CMParams) (c κ κtilde M : ℝ) : Prop where
  hκ0 : 0 < κ
  hκ1 : κ < 1
  hgap : κ < κtilde
  hrange : κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1)
  hM : 1 ≤ M
  hc : c = κ + κ⁻¹
  hχ_nonneg : 0 ≤ p.χ
  hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p)
  hα_eq : p.α = p.m + p.γ - 1

namespace PositivePaperLemma42ExactConditions

theorem upperBarrier_barLip
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PositivePaperLemma42ExactConditions p c κ κtilde M) :
    ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y| := by
  intro x y
  have hκM : κ * M ≤ M := by
    nlinarith [h.hκ0.le, h.hκ1.le, h.hM]
  calc
    |upperBarrier κ M x - upperBarrier κ M y|
        ≤ κ * M * |x - y| :=
          PaperLemma42ExactConditions.upperBarrier_abs_sub_le_mul h.hκ0.le
            (lt_of_lt_of_le zero_lt_one h.hM) x y
    _ ≤ M * |x - y| :=
          mul_le_mul_of_nonneg_right hκM (abs_nonneg _)

/-- Fill the full paper parabolic floor from the no-`barLip` floor under the
χ≥0 Lemma 4.2 parameter conditions. -/
def paperLowerRawParabolicFloor_of_noBar
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (h : PaperLowerRawParabolicFloorNoBar p c lam M κ κtilde D Λ hκ hM) :
    PaperLowerRawParabolicFloor p c lam M κ κtilde D Λ hκ hM where
  producer := h.producer
  barLip := hcond.upperBarrier_barLip
  step := h.step
  tail := h.tail

/-- Fill the core paper parabolic floor from the no-`barLip` core under the
χ≥0 Lemma 4.2 parameter conditions. -/
def paperLowerRawParabolicFloorCore_of_noBar
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {hκ : 0 ≤ κ} {hM : 0 ≤ M}
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (h : PaperLowerRawParabolicFloorCoreNoBar
      p c lam M κ κtilde D Λ hκ hM) :
    PaperLowerRawParabolicFloorCore p c lam M κ κtilde D Λ hκ hM where
  producer := h.producer
  barLip := hcond.upperBarrier_barLip
  step := h.step
  tail := h.tail

theorem chi_lt_half
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PositivePaperLemma42ExactConditions p c κ κtilde M) :
    p.χ < (1 / 2 : ℝ) :=
  lt_of_lt_of_le h.hχ_small (min_le_left _ _)

theorem chi_lt_chiStar
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PositivePaperLemma42ExactConditions p c κ κtilde M) :
    p.χ < chiStar p :=
  lt_of_lt_of_le h.hχ_small (min_le_right _ _)

theorem chi_abs_eq
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PositivePaperLemma42ExactConditions p c κ κtilde M) :
    |p.χ| = p.χ :=
  abs_of_nonneg h.hχ_nonneg

theorem chi_abs_le_one
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PositivePaperLemma42ExactConditions p c κ κtilde M) :
    |p.χ| ≤ 1 := by
  rw [h.chi_abs_eq]
  linarith [h.chi_lt_half]

theorem one_sub_abs_chi_nonneg
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PositivePaperLemma42ExactConditions p c κ κtilde M) :
    0 ≤ 1 - |p.χ| := by
  linarith [h.chi_abs_le_one]

theorem kappaTilde_le_one
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PositivePaperLemma42ExactConditions p c κ κtilde M) :
    κtilde ≤ 1 := by
  exact le_trans h.hrange
      (le_trans (min_le_right _ _) (min_le_right _ _))

theorem kappaTilde_le_one_plus_alpha_mul_kappa
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PositivePaperLemma42ExactConditions p c κ κtilde M) :
    κtilde ≤ (p.α + 1) * κ := by
  have hle : κtilde ≤ (1 + p.α) * κ :=
    le_trans h.hrange (min_le_left _ _)
  convert hle using 1
  ring

theorem kappaTilde_le_m_gamma_mul_kappa
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PositivePaperLemma42ExactConditions p c κ κtilde M) :
    κtilde ≤ (p.m + p.γ) * κ := by
  have hle := h.kappaTilde_le_one_plus_alpha_mul_kappa
  rw [h.hα_eq] at hle
  convert hle using 1
  ring

theorem kappaTilde_le_m_kappa_add_half
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PositivePaperLemma42ExactConditions p c κ κtilde M) :
    κtilde ≤ p.m * κ + 1 / 2 := by
  exact le_trans h.hrange
    (le_trans (min_le_right _ _) (min_le_left _ _))

theorem den_pos
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PositivePaperLemma42ExactConditions p c κ κtilde M) :
    0 < paperSpeedDenominator c κtilde := by
  simpa [paperSpeedDenominator] using
    lowerBarrierRaw_speed_denominator_pos h.hκ0 h.hκ1 h.hgap
      h.kappaTilde_le_one h.hc

end PositivePaperLemma42ExactConditions

theorem paperSubsolutionK_nonneg_of_positive_conditions
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PositivePaperLemma42ExactConditions p c κ κtilde M) :
    0 ≤ paperSubsolutionK M κ κtilde p.m p.γ :=
  paperSubsolutionK_nonneg
    (le_trans zero_le_one h.hM) h.hκ0.le (le_trans h.hκ0.le h.hgap.le)
    (le_trans zero_le_one p.hm) (le_trans zero_le_one p.hγ)

theorem paperDMin_pos_of_positive_conditions
    {p : CMParams} {c κ κtilde M : ℝ}
    (h : PositivePaperLemma42ExactConditions p c κ κtilde M) :
    0 < paperDMin p.χ M κ κtilde p.m p.γ c := by
  unfold paperDMin
  have hnum_pos :
      0 < 1 + |p.χ| * paperSubsolutionK M κ κtilde p.m p.γ := by
    have hmul_nonneg :
        0 ≤ |p.χ| * paperSubsolutionK M κ κtilde p.m p.γ :=
      mul_nonneg (abs_nonneg p.χ)
        (paperSubsolutionK_nonneg_of_positive_conditions h)
    linarith
  exact div_pos hnum_pos h.den_pos

theorem D_pos_of_positive_paperDMin_lt
    {p : CMParams} {c κ κtilde M D : ℝ}
    (h : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D) :
    0 < D :=
  lt_trans (paperDMin_pos_of_positive_conditions h) hD

theorem lowerBarrierRaw_pos_on_positive_paper_region
    {p : CMParams} {c κ κtilde M D x : ℝ}
    (h : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hx : x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D)) :
    0 < lowerBarrierRaw κ κtilde D x := by
  exact lowerBarrierRaw_pos_of_xminus_lt
    (sub_pos.mpr h.hgap) (D_pos_of_positive_paperDMin_lt h hD) hx

theorem lowerBarrierRaw_nonneg_on_positive_paper_region
    {p : CMParams} {c κ κtilde M D x : ℝ}
    (h : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hx : x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D)) :
    0 ≤ lowerBarrierRaw κ κtilde D x :=
  (lowerBarrierRaw_pos_on_positive_paper_region h hD hx).le

theorem lowerBarrierRaw_deriv_abs_le_on_positive_paper_region
    {p : CMParams} {c κ κtilde M D x : ℝ}
    (h : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hx : x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D)) :
    |deriv (lowerBarrierRaw κ κtilde D) x| ≤
      (κ + κtilde) * Real.exp (-κ * x) := by
  have hDpos : 0 < D := D_pos_of_positive_paperDMin_lt h hD
  have hκtilde_nonneg : 0 ≤ κtilde := (lt_trans h.hκ0 h.hgap).le
  have hraw_nonneg :
      0 ≤ lowerBarrierRaw κ κtilde D x :=
    lowerBarrierRaw_nonneg_on_positive_paper_region h hD hx
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
          have hle := add_le_add_left hsecond (κ * Real.exp (-κ * x))
          simpa [add_comm, add_left_comm, add_assoc] using hle
    _ = (κ + κtilde) * Real.exp (-κ * x) := by ring

theorem PaperLemma42EllipticVEstimate_of_positive_conditions
    {p : CMParams} {c κ κtilde M : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M) :
    PaperLemma42EllipticVEstimate p κ M := by
  intro u hu x hx
  by_cases hcrit : p.γ * κ = 1
  · rw [paperEllipticVxBound, if_pos hcrit]
    exact frozenElliptic_le_paperVxBound_critical hcrit hcond.hM hu hx
  · by_cases hsub : p.γ * κ < 1
    · rw [paperEllipticVxBound, if_neg hcrit, if_pos hsub]
      exact frozenElliptic_le_paperVxBound_subcritical hcond.hκ0 hsub hu x
    · have hsuper : 1 < p.γ * κ :=
        lt_of_le_of_ne (le_of_not_gt hsub) (Ne.symm hcrit)
      rw [paperEllipticVxBound, if_neg hcrit, if_neg hsub]
      exact frozenElliptic_le_paperVxBound_supercritical hsuper hcond.hM hu hx

theorem PaperLemma42EllipticVxEstimate_of_positive_conditions
    {p : CMParams} {c κ κtilde M : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M) :
    PaperLemma42EllipticVxEstimate p κ M := by
  intro u hu x hx
  have hVx_abs := frozenElliptic_deriv_abs_le p hu.cunif_bdd hu.nonneg x
  refine le_trans hVx_abs ?_
  exact PaperLemma42EllipticVEstimate_of_positive_conditions hcond u hu x hx

theorem PaperLemma42LogisticEstimate_of_positive_conditions
    {p : CMParams} {c κ κtilde M D : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D) :
    PaperLemma42LogisticEstimate p c κ κtilde M D := by
  intro u hu x hx
  have hgap_pos : 0 < κtilde - κ := sub_pos.mpr hcond.hgap
  have hx_nonneg : 0 ≤ x := by
    exact le_trans
      (lowerBarrierXMinus_nonneg_of_one_le_D hgap_pos hD_ge_one) hx.le
  have hD_pos : 0 < D := D_pos_of_positive_paperDMin_lt hcond hD
  have hW_pos :
      0 < lowerBarrierRaw κ κtilde D x :=
    lowerBarrierRaw_pos_of_xminus_lt hgap_pos hD_pos hx
  have hW_le_exp :
      lowerBarrierRaw κ κtilde D x ≤ Real.exp (-κ * x) :=
    lowerBarrierRaw_le_exp hD_pos.le
  have hα1_pos : 0 < p.α + 1 := by linarith [p.hα]
  have hpow :
      lowerBarrierRaw κ κtilde D x *
          (lowerBarrierRaw κ κtilde D x) ^ p.α =
        (lowerBarrierRaw κ κtilde D x) ^ (p.α + 1) := by
    calc
      lowerBarrierRaw κ κtilde D x *
          (lowerBarrierRaw κ κtilde D x) ^ p.α =
        (lowerBarrierRaw κ κtilde D x) ^ (1 : ℝ) *
          (lowerBarrierRaw κ κtilde D x) ^ p.α := by
          rw [Real.rpow_one]
      _ = (lowerBarrierRaw κ κtilde D x) ^ ((1 : ℝ) + p.α) := by
          rw [← Real.rpow_add hW_pos]
      _ = (lowerBarrierRaw κ κtilde D x) ^ (p.α + 1) := by
          congr 1
          ring
  rw [hpow]
  calc
    (lowerBarrierRaw κ κtilde D x) ^ (p.α + 1)
        ≤ (Real.exp (-κ * x)) ^ (p.α + 1) :=
      Real.rpow_le_rpow hW_pos.le hW_le_exp hα1_pos.le
    _ = Real.exp (-(p.α + 1) * κ * x) := by
      rw [← Real.exp_mul]
      congr 1
      ring
    _ ≤ Real.exp (-κtilde * x) := by
      apply Real.exp_le_exp.mpr
      have hκtilde_le := hcond.kappaTilde_le_one_plus_alpha_mul_kappa
      nlinarith

private theorem paperPositiveK_combine
    {A C κ κtilde β m x : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hx : 0 ≤ x)
    (hle : κtilde ≤ m * κ + β) :
    A * (C * Real.exp (-β * x)) * (Real.exp (-κ * x)) ^ m +
        (C * Real.exp (-β * x)) * (Real.exp (-κ * x)) ^ m ≤
      (A + 1) * C * Real.exp (-κtilde * x) := by
  have hEpos : 0 < Real.exp (-κ * x) := Real.exp_pos _
  have hEpow :
      (Real.exp (-κ * x)) ^ m = Real.exp (-(m * κ) * x) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hexp :
      C * Real.exp (-β * x) * (Real.exp (-κ * x)) ^ m =
        C * Real.exp (-(m * κ + β) * x) := by
    calc
      C * Real.exp (-β * x) * (Real.exp (-κ * x)) ^ m =
          C * (Real.exp (-β * x) * Real.exp (-(m * κ) * x)) := by
          rw [hEpow]
          ring
      _ = C * Real.exp (-(m * κ + β) * x) := by
          rw [← Real.exp_add]
          congr 1
          ring
  have hcoef : 0 ≤ (A + 1) * C := by
    exact mul_nonneg (by linarith) hC
  have hexp_le :
      Real.exp (-(m * κ + β) * x) ≤ Real.exp (-κtilde * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    A * (C * Real.exp (-β * x)) * (Real.exp (-κ * x)) ^ m +
        (C * Real.exp (-β * x)) * (Real.exp (-κ * x)) ^ m
        = (A + 1) *
            (C * Real.exp (-β * x) * (Real.exp (-κ * x)) ^ m) := by
          ring
    _ = (A + 1) * (C * Real.exp (-(m * κ + β) * x)) := by rw [hexp]
    _ = (A + 1) * C * Real.exp (-(m * κ + β) * x) := by ring
    _ ≤ (A + 1) * C * Real.exp (-κtilde * x) :=
        mul_le_mul_of_nonneg_left hexp_le hcoef

def PaperLemma42PositiveKTermEstimate
    (p : CMParams) (_c κ κtilde M D : ℝ) : Prop :=
  ∀ u : ℝ → ℝ, InWaveTrapSet κ M u →
    ∀ x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D),
      p.m * (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) *
            |deriv (frozenElliptic p u) x| *
            |deriv (lowerBarrierRaw κ κtilde D) x| +
          lowerBarrierRaw κ κtilde D x *
            (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) *
            frozenElliptic p u x ≤
        paperSubsolutionK M κ κtilde p.m p.γ * Real.exp (-κtilde * x)

set_option maxHeartbeats 1000000 in
theorem PaperLemma42PositiveKTermEstimate_of_elliptic_estimates
    {p : CMParams} {c κ κtilde M D : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hV : PaperLemma42EllipticVEstimate p κ M)
    (hVx : PaperLemma42EllipticVxEstimate p κ M) :
    PaperLemma42PositiveKTermEstimate p c κ κtilde M D := by
  intro u hu x hx
  have hgap_pos : 0 < κtilde - κ := sub_pos.mpr hcond.hgap
  have hx_nonneg : 0 ≤ x := by
    exact le_trans
      (lowerBarrierXMinus_nonneg_of_one_le_D hgap_pos hD_ge_one) hx.le
  have hD_pos : 0 < D := D_pos_of_positive_paperDMin_lt hcond hD
  have hW_pos :
      0 < lowerBarrierRaw κ κtilde D x :=
    lowerBarrierRaw_pos_of_xminus_lt hgap_pos hD_pos hx
  have hW_nonneg : 0 ≤ lowerBarrierRaw κ κtilde D x := hW_pos.le
  have hE_pos : 0 < Real.exp (-κ * x) := Real.exp_pos _
  have hW_le_exp :
      lowerBarrierRaw κ κtilde D x ≤ Real.exp (-κ * x) :=
    lowerBarrierRaw_le_exp hD_pos.le
  have hderiv_le :
      |deriv (lowerBarrierRaw κ κtilde D) x| ≤
        (κ + κtilde) * Real.exp (-κ * x) :=
    lowerBarrierRaw_deriv_abs_le_on_positive_paper_region hcond hD hx
  have hV_le := hV u hu x hx_nonneg
  have hVx_le := hVx u hu x hx_nonneg
  have hB_nonneg :
      0 ≤ paperEllipticVxBound M κ p.γ x :=
    le_trans (frozenElliptic_nonneg p hu.nonneg x) hV_le
  have hm_nonneg : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hm1_nonneg : 0 ≤ p.m - 1 := by linarith [p.hm]
  have hκsum_nonneg : 0 ≤ κ + κtilde := by
    have hκtilde_pos : 0 < κtilde := lt_trans hcond.hκ0 hcond.hgap
    nlinarith [hcond.hκ0, hκtilde_pos]
  have hWm1_le :
      (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) ≤
        (Real.exp (-κ * x)) ^ (p.m - 1) :=
    Real.rpow_le_rpow hW_nonneg hW_le_exp hm1_nonneg
  have hterm1 :
      p.m * (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) *
            |deriv (frozenElliptic p u) x| *
            |deriv (lowerBarrierRaw κ κtilde D) x| ≤
        p.m * (κ + κtilde) *
          paperEllipticVxBound M κ p.γ x *
          (Real.exp (-κ * x)) ^ p.m := by
    have hEmul :
        (Real.exp (-κ * x)) ^ (p.m - 1) * Real.exp (-κ * x) =
          (Real.exp (-κ * x)) ^ p.m := by
      calc
        (Real.exp (-κ * x)) ^ (p.m - 1) * Real.exp (-κ * x)
            = (Real.exp (-κ * x)) ^ (p.m - 1) *
                (Real.exp (-κ * x)) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (Real.exp (-κ * x)) ^ ((p.m - 1) + 1) := by
            rw [← Real.rpow_add hE_pos]
        _ = (Real.exp (-κ * x)) ^ p.m := by
            congr 1
            ring
    calc
      p.m * (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) *
            |deriv (frozenElliptic p u) x| *
            |deriv (lowerBarrierRaw κ κtilde D) x|
          ≤ p.m * (Real.exp (-κ * x)) ^ (p.m - 1) *
              paperEllipticVxBound M κ p.γ x *
              ((κ + κtilde) * Real.exp (-κ * x)) := by
            gcongr
      _ = p.m * (κ + κtilde) *
          paperEllipticVxBound M κ p.γ x *
          (Real.exp (-κ * x)) ^ p.m := by
            calc
              p.m * (Real.exp (-κ * x)) ^ (p.m - 1) *
                    paperEllipticVxBound M κ p.γ x *
                    ((κ + κtilde) * Real.exp (-κ * x)) =
                  p.m * (κ + κtilde) *
                    paperEllipticVxBound M κ p.γ x *
                    ((Real.exp (-κ * x)) ^ (p.m - 1) *
                      Real.exp (-κ * x)) := by
                    ring
              _ = p.m * (κ + κtilde) *
                    paperEllipticVxBound M κ p.γ x *
                    (Real.exp (-κ * x)) ^ p.m := by
                    rw [hEmul]
  have hWm_le :
      (lowerBarrierRaw κ κtilde D x) ^ p.m ≤
        (Real.exp (-κ * x)) ^ p.m :=
    Real.rpow_le_rpow hW_nonneg hW_le_exp hm_nonneg
  have hWpow :
      lowerBarrierRaw κ κtilde D x *
          (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) =
        (lowerBarrierRaw κ κtilde D x) ^ p.m := by
    calc
      lowerBarrierRaw κ κtilde D x *
          (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) =
        (lowerBarrierRaw κ κtilde D x) ^ (1 : ℝ) *
          (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) := by
          rw [Real.rpow_one]
      _ = (lowerBarrierRaw κ κtilde D x) ^ ((1 : ℝ) + (p.m - 1)) := by
          rw [← Real.rpow_add hW_pos]
      _ = (lowerBarrierRaw κ κtilde D x) ^ p.m := by
          congr 1
          ring
  have hterm2 :
      lowerBarrierRaw κ κtilde D x *
            (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) *
            frozenElliptic p u x ≤
        paperEllipticVxBound M κ p.γ x *
          (Real.exp (-κ * x)) ^ p.m := by
    have hV_nonneg : 0 ≤ frozenElliptic p u x :=
      frozenElliptic_nonneg p hu.nonneg x
    rw [hWpow]
    calc
      (lowerBarrierRaw κ κtilde D x) ^ p.m * frozenElliptic p u x
          ≤ (Real.exp (-κ * x)) ^ p.m *
              paperEllipticVxBound M κ p.γ x := by
            gcongr
      _ = paperEllipticVxBound M κ p.γ x *
              (Real.exp (-κ * x)) ^ p.m := by ring
  set A := p.m * (κ + κtilde) with hAdef
  have hA_nonneg : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg hm_nonneg hκsum_nonneg
  have hpre :
      p.m * (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) *
            |deriv (frozenElliptic p u) x| *
            |deriv (lowerBarrierRaw κ κtilde D) x| +
          lowerBarrierRaw κ κtilde D x *
            (lowerBarrierRaw κ κtilde D x) ^ (p.m - 1) *
            frozenElliptic p u x ≤
        A * paperEllipticVxBound M κ p.γ x *
            (Real.exp (-κ * x)) ^ p.m +
          paperEllipticVxBound M κ p.γ x *
            (Real.exp (-κ * x)) ^ p.m := by
    rw [hAdef]
    exact add_le_add hterm1 hterm2
  by_cases hcrit : p.γ * κ = 1
  · set C := M ^ p.γ + 3 / 4 with hCdef
    have hC_nonneg : 0 ≤ C := by
      rw [hCdef]
      exact add_nonneg
        (Real.rpow_nonneg (le_trans zero_le_one hcond.hM) p.γ) (by norm_num)
    have hKcrit :
        paperSubsolutionK M κ κtilde p.m p.γ = (A + 1) * C := by
      rw [paperSubsolutionK_eq_critical hcrit, hAdef, hCdef]
      ring
    rw [paperEllipticVxBound, if_pos hcrit] at hpre
    refine le_trans hpre ?_
    rw [hKcrit]
    exact paperPositiveK_combine hA_nonneg hC_nonneg hx_nonneg
      hcond.kappaTilde_le_m_kappa_add_half
  · by_cases hsub : p.γ * κ < 1
    · set C := 1 / (1 - p.γ ^ 2 * κ ^ 2) with hCdef
      have hγκ_pos : 0 < p.γ * κ :=
        mul_pos (by linarith [p.hγ]) hcond.hκ0
      have hden_pos : 0 < 1 - p.γ ^ 2 * κ ^ 2 := by nlinarith
      have hC_nonneg : 0 ≤ C := by
        rw [hCdef]
        exact (one_div_pos.mpr hden_pos).le
      have hKsub :
          paperSubsolutionK M κ κtilde p.m p.γ = (A + 1) * C := by
        rw [paperSubsolutionK_eq_subcritical hsub, hAdef, hCdef]
        ring
      rw [paperEllipticVxBound, if_neg hcrit, if_pos hsub] at hpre
      refine le_trans hpre ?_
      rw [hKsub]
      have hle : κtilde ≤ p.m * κ + p.γ * κ := by
        have hmain := hcond.kappaTilde_le_m_gamma_mul_kappa
        nlinarith
      exact paperPositiveK_combine hA_nonneg hC_nonneg hx_nonneg
        hle
    · have hsuper : 1 < p.γ * κ :=
        lt_of_le_of_ne (le_of_not_gt hsub) (Ne.symm hcrit)
      set C :=
        (M ^ p.γ * (κ ^ 2 * p.γ ^ 2 - 1) + p.γ * κ) /
          (κ ^ 2 * p.γ ^ 2 - 1) with hCdef
      have hden_pos : 0 < κ ^ 2 * p.γ ^ 2 - 1 := by
        have hγκ_nonneg : 0 ≤ p.γ * κ :=
          mul_nonneg (le_trans zero_le_one p.hγ) hcond.hκ0.le
        have hs : 1 < (p.γ * κ) ^ 2 :=
          (one_lt_sq_iff₀ hγκ_nonneg).mpr hsuper
        have hsq : (p.γ * κ) ^ 2 = κ ^ 2 * p.γ ^ 2 := by ring
        rw [← hsq]
        exact sub_pos.mpr hs
      have hC_nonneg : 0 ≤ C := by
        rw [hCdef]
        have hnum_nonneg :
            0 ≤ M ^ p.γ * (κ ^ 2 * p.γ ^ 2 - 1) + p.γ * κ := by
          exact add_nonneg
            (mul_nonneg
              (Real.rpow_nonneg (le_trans zero_le_one hcond.hM) p.γ)
              hden_pos.le)
            (mul_nonneg (le_trans zero_le_one p.hγ) hcond.hκ0.le)
        exact div_nonneg hnum_nonneg hden_pos.le
      have hKsuper :
          paperSubsolutionK M κ κtilde p.m p.γ = (A + 1) * C := by
        rw [paperSubsolutionK_eq_supercritical hsuper, hAdef, hCdef]
        ring_nf
      rw [paperEllipticVxBound, if_neg hcrit, if_neg hsub] at hpre
      refine le_trans hpre ?_
      rw [hKsuper]
      have hle : κtilde ≤ p.m * κ + 1 := by
        have hhalf := hcond.kappaTilde_le_m_kappa_add_half
        linarith
      simpa [one_mul] using
        paperPositiveK_combine hA_nonneg hC_nonneg hx_nonneg hle

theorem PaperLemma42PositiveKTermEstimate_of_positive_conditions
    {p : CMParams} {c κ κtilde M D : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D) :
    PaperLemma42PositiveKTermEstimate p c κ κtilde M D :=
  PaperLemma42PositiveKTermEstimate_of_elliptic_estimates hcond hD hD_ge_one
    (PaperLemma42EllipticVEstimate_of_positive_conditions hcond)
    (PaperLemma42EllipticVxEstimate_of_positive_conditions hcond)

def paperLemma42PositiveBadTerm
    (p : CMParams) (u W : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 - |p.χ|) * (W x * (W x) ^ p.α) +
    |p.χ| *
      (p.m * (W x) ^ (p.m - 1) *
          |deriv (frozenElliptic p u) x| * |deriv W x| +
        W x * (W x) ^ (p.m - 1) * frozenElliptic p u x)

def PaperLemma42PositiveBadTermEstimate
    (p : CMParams) (_c κ κtilde M D : ℝ) : Prop :=
  ∀ u : ℝ → ℝ, InWaveTrapSet κ M u →
    ∀ x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D),
      paperLemma42PositiveBadTerm p u (lowerBarrierRaw κ κtilde D) x ≤
        (1 + |p.χ| * paperSubsolutionK M κ κtilde p.m p.γ) *
          Real.exp (-κtilde * x)

theorem PaperLemma42PositiveBadTermEstimate_of_components
    {p : CMParams} {c κ κtilde M D : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hlog : PaperLemma42LogisticEstimate p c κ κtilde M D)
    (hK : PaperLemma42PositiveKTermEstimate p c κ κtilde M D) :
    PaperLemma42PositiveBadTermEstimate p c κ κtilde M D := by
  intro u hu x hx
  have hlog_x := hlog u hu x hx
  have hK_x := hK u hu x hx
  set W : ℝ → ℝ := lowerBarrierRaw κ κtilde D
  have hW_nonneg : 0 ≤ W x := by
    change 0 ≤ lowerBarrierRaw κ κtilde D x
    exact lowerBarrierRaw_nonneg_on_positive_paper_region hcond hD hx
  have hlog_nonneg : 0 ≤ W x * (W x) ^ p.α :=
    mul_nonneg hW_nonneg (Real.rpow_nonneg hW_nonneg p.α)
  have hcoef_nonneg := hcond.one_sub_abs_chi_nonneg
  have hcoef_le_one : 1 - |p.χ| ≤ 1 := by
    exact sub_le_self _ (abs_nonneg p.χ)
  have hlog_weight :
      (1 - |p.χ|) * (W x * (W x) ^ p.α) ≤
        Real.exp (-κtilde * x) := by
    have hmul :
        (1 - |p.χ|) * (W x * (W x) ^ p.α) ≤
          W x * (W x) ^ p.α := by
      nlinarith
    exact le_trans hmul (by simpa [W] using hlog_x)
  have hχK := mul_le_mul_of_nonneg_left hK_x (abs_nonneg p.χ)
  calc
    paperLemma42PositiveBadTerm p u W x
        ≤ Real.exp (-κtilde * x) +
            |p.χ| *
              (paperSubsolutionK M κ κtilde p.m p.γ *
                Real.exp (-κtilde * x)) := by
          dsimp [paperLemma42PositiveBadTerm]
          exact add_le_add hlog_weight hχK
    _ = (1 + |p.χ| * paperSubsolutionK M κ κtilde p.m p.γ) *
          Real.exp (-κtilde * x) := by
        ring

def PaperLemma42PositivePointwiseEstimate
    (p : CMParams) (c κ κtilde M D : ℝ) : Prop :=
  ∀ u : ℝ → ℝ, InWaveTrapSet κ M u →
    ∀ x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D),
      (D * paperSpeedDenominator c κtilde - 1 -
          |p.χ| * paperSubsolutionK M κ κtilde p.m p.γ) *
        Real.exp (-κtilde * x) ≤
          paperWaveOperator p c u (lowerBarrierRaw κ κtilde D) x

theorem PaperLemma42PositivePointwiseEstimate_of_badTermEstimate
    {p : CMParams} {c κ κtilde M D : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hbad : PaperLemma42PositiveBadTermEstimate p c κ κtilde M D) :
    PaperLemma42PositivePointwiseEstimate p c κ κtilde M D := by
  intro u hu x hx
  set W : ℝ → ℝ := lowerBarrierRaw κ κtilde D with hWdef
  set V : ℝ → ℝ := frozenElliptic p u with hVdef
  set lin : ℝ := D * paperSpeedDenominator c κtilde * Real.exp (-κtilde * x)
  set chem : ℝ := -p.χ * p.m * (W x) ^ (p.m - 1) * deriv V x * deriv W x
  set vBad : ℝ := |p.χ| * (W x * (W x) ^ (p.m - 1) * V x)
  set logistic : ℝ := W x * (W x) ^ p.α
  set derivBad : ℝ :=
    |p.χ| * (p.m * (W x) ^ (p.m - 1) *
      |deriv V x| * |deriv W x|)
  have hW_pos : 0 < W x := by
    rw [hWdef]
    exact lowerBarrierRaw_pos_on_positive_paper_region hcond hD hx
  have hW_nonneg : 0 ≤ W x := hW_pos.le
  have hWpow_nonneg : 0 ≤ (W x) ^ (p.m - 1) :=
    Real.rpow_nonneg hW_nonneg _
  have hχ_abs : p.χ = |p.χ| := by
    rw [hcond.chi_abs_eq]
  have hcoef_nonneg :
      0 ≤ |p.χ| * (p.m * (W x) ^ (p.m - 1)) := by
    exact mul_nonneg (abs_nonneg p.χ)
      (mul_nonneg (le_trans zero_le_one p.hm) hWpow_nonneg)
  have hcoef_nonpos :
      -(|p.χ| * (p.m * (W x) ^ (p.m - 1))) ≤ 0 := by
    exact neg_nonpos.mpr hcoef_nonneg
  have hprod_upper :
      deriv V x * deriv W x ≤ |deriv V x| * |deriv W x| := by
    have h := le_abs_self (deriv V x * deriv W x)
    rwa [abs_mul] at h
  have hchem_lower : -derivBad ≤ chem := by
    have hmul := mul_le_mul_of_nonpos_left hprod_upper hcoef_nonpos
    calc
      -derivBad
          = -(|p.χ| * (p.m * (W x) ^ (p.m - 1))) *
              (|deriv V x| * |deriv W x|) := by
            dsimp [derivBad]
            ring
      _ ≤ -(|p.χ| * (p.m * (W x) ^ (p.m - 1))) *
              (deriv V x * deriv W x) := hmul
      _ = chem := by
            dsimp [chem]
            rw [hχ_abs]
            rw [abs_of_nonneg (abs_nonneg p.χ)]
            ring
  have hpow_alpha_raw :
      (lowerBarrierRaw κ κtilde D x) ^ (p.m + p.γ - 1) =
        (lowerBarrierRaw κ κtilde D x) ^ p.α := by
    rw [hcond.hα_eq]
  have hop :
      paperWaveOperator p c u W x =
        lin + chem - vBad - (1 - |p.χ|) * logistic := by
    rw [hWdef]
    rw [paperWaveOperator_lowerBarrierRaw_eq_of_kappa_speed p u x
      (ne_of_gt hcond.hκ0) hcond.hc]
    dsimp [lin, chem, vBad, logistic]
    rw [hVdef, hWdef]
    rw [hχ_abs, hpow_alpha_raw]
    rw [abs_of_nonneg (abs_nonneg p.χ)]
    ring_nf
  have hbad_eq :
      paperLemma42PositiveBadTerm p u W x =
        (1 - |p.χ|) * logistic + derivBad + vBad := by
    dsimp [paperLemma42PositiveBadTerm, logistic, derivBad, vBad]
    rw [hVdef]
    ring
  have hop_lower :
      lin - paperLemma42PositiveBadTerm p u W x ≤
        paperWaveOperator p c u W x := by
    rw [hbad_eq, hop]
    nlinarith [hchem_lower]
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

theorem PaperLemma_4_2_positive_paperWaveOperator_from_pointwise_estimate
    {p : CMParams} {c κ κtilde M D : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hpoint : PaperLemma42PositivePointwiseEstimate p c κ κtilde M D)
    (u : ℝ → ℝ) (hu : InWaveTrapSet κ M u) :
    IsPaperFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
      (Set.Ioi (lowerBarrierXMinus κ κtilde D)) := by
  intro x hx
  exact le_trans
    (paperDMin_margin_nonneg_exp (χ := p.χ) (M := M) (κ := κ)
      (κtilde := κtilde) (m := p.m) (gamma := p.γ) (c := c) (D := D)
      (x := x) hcond.den_pos hD)
    (hpoint u hu x hx)

theorem PaperLemma_4_2_positive_paperWaveOperator_from_components
    {p : CMParams} {c κ κtilde M D : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hlog : PaperLemma42LogisticEstimate p c κ κtilde M D)
    (hK : PaperLemma42PositiveKTermEstimate p c κ κtilde M D)
    (u : ℝ → ℝ) (hu : InWaveTrapSet κ M u) :
    IsPaperFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
      (Set.Ioi (lowerBarrierXMinus κ κtilde D)) := by
  exact PaperLemma_4_2_positive_paperWaveOperator_from_pointwise_estimate
    hcond hD
    (PaperLemma42PositivePointwiseEstimate_of_badTermEstimate hcond hD
      (PaperLemma42PositiveBadTermEstimate_of_components hcond hD hlog hK))
    u hu

theorem PaperLemma_4_2_positive_paperWaveOperator_of_conditions
    {p : CMParams} {c κ κtilde M D : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (u : ℝ → ℝ) (hu : InWaveTrapSet κ M u) :
    IsPaperFrozenSubSolutionOn p c u (lowerBarrierRaw κ κtilde D)
      (Set.Ioi (lowerBarrierXMinus κ κtilde D)) :=
  PaperLemma_4_2_positive_paperWaveOperator_from_components hcond hD
    (PaperLemma42LogisticEstimate_of_positive_conditions hcond hD hD_ge_one)
    (PaperLemma42PositiveKTermEstimate_of_positive_conditions
      hcond hD hD_ge_one)
    u hu

theorem paperLowerBarrierStepData_lowerBarrierRaw_of_positivePaperStep
    {p : CMParams} {c lam M κ κtilde D Λ C_chem La Lb : ℝ} {u Z W : ℝ → ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hu : InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u)
    (hprev : ∀ x, lowerBarrierRaw κ κtilde D x ≤ Z x)
    (hlam : 0 < lam)
    (hstep : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x)
    (haux : PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u W) :
    PaperLowerBarrierStepData p c lam M κ Λ C_chem La Lb
      (Set.Ioi (lowerBarrierXMinus κ κtilde D)) u Z W
      (lowerBarrierRaw κ κtilde D) := by
  exact
    { hlam := hlam
      step_op := hstep
      hCB := haux.hCB
      AZ := hprev
      φcont := haux.φcont
      hbot := haux.hbot
      hLa := haux.hLa
      htop := haux.htop
      hLb := haux.hLb
      paperSub :=
        PaperLemma_4_2_positive_paperWaveOperator_of_conditions
          hcond hD hD_ge_one u hu.bare.1
      region := haux.region
      paperDiff := haux.paperDiff }

theorem rotheStepLowerInvariant_lowerBarrierRaw_of_positivePaperStepData
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hstepData : ∀ u,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
        ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤ rotheSeq u k x) →
          ∃ C_chem La Lb,
            (0 < lam) ∧
            (∀ x, paperImplicitStepOp p c (1 / lam) u
              (rotheSeq u (k + 1)) x = rotheSeq u k x) ∧
            PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
              (rotheSeq u (k + 1))) :
    RotheStepLowerInvariant κ M (lowerBarrierRaw κ κtilde D) rotheSeq := by
  apply rotheStepLowerInvariant_of_paperBarrierData
  intro u hu k hprev
  obtain ⟨C_chem, La, Lb, hlam, hstep, haux⟩ := hstepData u hu k hprev
  refine ⟨C_chem, La, Lb, Set.Ioi (lowerBarrierXMinus κ κtilde D), ?_⟩
  exact paperLowerBarrierStepData_lowerBarrierRaw_of_positivePaperStep
    (Λ := Λ) hcond hD hD_ge_one hu hprev hlam hstep haux

theorem rotheSeqOfPaper_lowerBarrierRaw_positive_stepInvariant
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hprodAll : ∀ u, PaperRotheStepProducer p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hauxData : ∀ u,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
        ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
          rotheSeqOfPaper p c lam M κ Λ u (hprodAll u) hκ hM k x) →
          ∃ C_chem La Lb,
            PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
              (rotheSeqOfPaper p c lam M κ Λ u (hprodAll u) hκ hM
                (k + 1))) :
    RotheStepLowerInvariant κ M (lowerBarrierRaw κ κtilde D)
      (fun u => rotheSeqOfPaper p c lam M κ Λ u (hprodAll u) hκ hM) := by
  refine rotheStepLowerInvariant_lowerBarrierRaw_of_positivePaperStepData
    (p := p) (c := c) (lam := lam) (M := M) (κ := κ)
    (κtilde := κtilde) (D := D) (Λ := Λ)
    hcond hD hD_ge_one ?_
  intro u hu k hprev
  obtain ⟨C_chem, La, Lb, haux⟩ := hauxData u hu k hprev
  have hfacts := rotheSeqOfPaper_stepFacts (hprodAll u) hκ hM k
  exact ⟨C_chem, La, Lb, (hprodAll u).hlam, hfacts.step_op, haux⟩

theorem profileNontrivial_of_lowerBarrierRaw_positive_tail_bound
    {p : CMParams} {c κ κtilde M D : ℝ} {U : ℝ → ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hUtail : ∀ x ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D),
      lowerBarrierRaw κ κtilde D x ≤ U x) :
    ProfileNontrivial U := by
  let x₀ := lowerBarrierXPlus κ κtilde D
  have hDpos : 0 < D := D_pos_of_positive_paperDMin_lt hcond hD
  have hx₀ : x₀ ∈ Set.Ioi (lowerBarrierXMinus κ κtilde D) := by
    exact lowerBarrierXMinus_lt_xplus hcond.hκ0
      (sub_pos.mpr hcond.hgap) hDpos
  have hraw_pos : 0 < lowerBarrierRaw κ κtilde D x₀ :=
    lowerBarrierRaw_pos_of_xminus_lt (sub_pos.mpr hcond.hgap) hDpos hx₀
  exact ⟨x₀, lt_of_lt_of_le hraw_pos (hUtail x₀ hx₀)⟩

def rotheSeqOfPaperFromPositiveCond
    (p : CMParams) (c lam M κ κtilde Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hprodAll : ∀ u, PaperRotheStepProducer p c lam M κ Λ u) :
    (ℝ → ℝ) → ℕ → ℝ → ℝ :=
  fun u => rotheSeqOfPaper p c lam M κ Λ u (hprodAll u)
    hcond.hκ0.le (le_trans zero_le_one hcond.hM)

theorem hauxData_of_positive_conditions
    {p : CMParams} {c lam M κ κtilde D Λ : ℝ}
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (_hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (_hD_ge_one : 1 ≤ D)
    (hprodAll : ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ
      hcond.hκ0.le (le_trans zero_le_one hcond.hM) u) :
    ∀ u,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
        ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
          rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
            (fun v => (hprodAll v).producer) u k x) →
          ∃ C_chem La Lb,
            PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
              (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
                (fun v => (hprodAll v).producer) u (k + 1)) := by
  intro u hu k hprev
  simpa [rotheSeqOfPaperFromPositiveCond] using
    (hprodAll u).lowerRawAux hu k hprev

theorem b1_chiPos_existence_paper
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperRotheStepProducer p c lam M κ Λ u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
      (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond hprodAll))
    (hauxData : ∀ u,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
        ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
          rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
            hprodAll u k x) →
          ∃ C_chem La Lb,
            PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
              (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
                hprodAll u (k + 1)))
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple
        (InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D)))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
            hprodAll U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hsmp : StationaryStrongMaxPrinciple p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U := by
  let zseq :=
    rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond hprodAll
  have hM0 : 0 ≤ M := le_trans zero_le_one hcond.hM
  have hcpos : 0 < c := by
    rw [hcond.hc]
    have hinv : 0 < κ⁻¹ := inv_pos.mpr hcond.hκ0
    nlinarith [hcond.hκ0, hinv]
  have hstep :
      RotheStepLowerInvariant κ M (lowerBarrierRaw κ κtilde D) zseq := by
    have haux' : ∀ u,
        InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) u →
          ∀ k, (∀ x, lowerBarrierRaw κ κtilde D x ≤
            rotheSeqOfPaper p c lam M κ Λ u (hprodAll u) hcond.hκ0.le hM0 k x) →
            ∃ C_chem La Lb,
              PaperLowerRawStepAux p c lam M κ κtilde D C_chem La Lb u
                (rotheSeqOfPaper p c lam M κ Λ u (hprodAll u)
                  hcond.hκ0.le hM0 (k + 1)) := by
      simpa [zseq, rotheSeqOfPaperFromPositiveCond, hM0] using hauxData
    simpa [zseq, rotheSeqOfPaperFromPositiveCond, hM0] using
      rotheSeqOfPaper_lowerBarrierRaw_positive_stepInvariant hcond hD
        hD_ge_one hprodAll hcond.hκ0.le hM0 haux'
  have hlower :
      RotheOrbitLowerBound κ M (lowerBarrierRaw κ κtilde D) zseq :=
    rotheOrbitLowerBound_of_stepLowerInvariant
      (fun u hu => by
        simpa [zseq, rotheSeqOfPaperFromPositiveCond, hM0] using
          rotheSeqOfPaper_lowerPinned_base (hprodAll u) hcond.hκ0.le hM0 hu)
      hstep
  have hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
      PaperRotheOrbitData p c lam M κ zseq u := by
    intro u _hu
    simpa [zseq, rotheSeqOfPaperFromPositiveCond, hM0] using
      paperRotheOrbitData (p := p) (c := c) (lam := lam) (M := M)
        (κ := κ) (Λ := Λ) (u := u) hprodAll hcond.hκ0.le hM0
        hΛ0 hΛM hbarLip
  obtain ⟨U, hU, hfix⟩ :=
    paperLowerPinnedSchauder_fixedPoint p c lam M κ
      (lowerBarrierRaw κ κtilde D) hM0 zseq hŪbdd
      (helly_pointwise_selection M) hdep hdata hlower hprinciple
  have hstat : ∀ x, frozenWaveOperator p c U U x = 0 :=
    hstationary U hU (by simpa [zseq] using hfix)
  have hnontriv : ProfileNontrivial U :=
    profileNontrivial_of_lowerBarrierRaw_positive_tail_bound hcond hD
      (fun x _hx => hU.lower x)
  have hpos : ∀ x, 0 < U x :=
    hsmp U hU.bare hstat hnontriv
  have hlim_neg : Tendsto U atBot (𝓝 1) :=
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_nontrivial
      hU.bare hsmp hnontriv (hflat U hU hstat) hstat
  have hlim_pos : Tendsto U atTop (𝓝 0) :=
    hU.bare.tendsto_atTop_zero hcond.hκ0
  exact ⟨U, hU,
    FrozenStationaryWaveProfile.mk_auto_limits hcpos hpos
      hU.bare.trap.cunif_bdd hstat hlim_neg hlim_pos⟩

theorem b1_chiPos_existence_paper'
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ
      hcond.hκ0.le (le_trans zero_le_one hcond.hM) u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
      (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
        (fun u => (hprodAll u).producer)))
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple
        (InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D)))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
            (fun u => (hprodAll u).producer) U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hrealize : StationaryStrongMaxPrincipleODERealization p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U := by
  exact b1_chiPos_existence_paper p c lam M κ κtilde D Λ hcond hD
    hD_ge_one hΛ0 hΛM (fun u => (hprodAll u).producer) hbarLip
    (upperBarrier_isBddFun (le_trans zero_le_one hcond.hM)) hdep
    (hauxData_of_positive_conditions hcond hD hD_ge_one hprodAll) hprinciple
    hstationary (hsmp_of_odeRealization hrealize) hflat

theorem b1_chiPos_existence_paper_clean
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, PaperLowerRawStepProducer p c lam M κ κtilde D Λ
      hcond.hκ0.le (le_trans zero_le_one hcond.hM) u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hstep : PaperRotheSeqStepDependence p c lam M κ Λ
      (fun u => (hprodAll u).producer) hcond.hκ0.le
      (le_trans zero_le_one hcond.hM))
    (htail : PaperRotheTailUniform p c lam M κ Λ
      (fun u => (hprodAll u).producer) hcond.hκ0.le
      (le_trans zero_le_one hcond.hM))
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple
        (InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D)))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
        rotheLimit
          (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
            (fun u => (hprodAll u).producer) U) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hrealize : StationaryStrongMaxPrincipleODERealization p c κ M)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiPos_existence_paper' p c lam M κ κtilde D Λ hcond hD
    hD_ge_one hΛ0 hΛM hprodAll hbarLip
    (by
      simpa [rotheSeqOfPaperFromPositiveCond] using
        paperRotheContinuousDependence p c lam M κ Λ
          (fun u => (hprodAll u).producer) hcond.hκ0.le
          (le_trans zero_le_one hcond.hM) hstep htail)
    hprinciple hstationary
    hrealize hflat

/-- Minimal χ≥0 paper wrapper with the same carried floor shape as the χ≤0
branch. -/
theorem b1_chiPos_existence_paper_min
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hpar :
      PaperLowerRawParabolicFloor p c lam M κ κtilde D Λ
        hcond.hκ0.le (le_trans zero_le_one hcond.hM))
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple
        (InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D)))
    (hconv :
      PaperLowerPinnedStationaryFlatFloor p c κ M
        (lowerBarrierRaw κ κtilde D)
        (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
          (fun u => (hpar.producer u).producer)))
    (hsmp : StationaryStrongMaxPrinciple p c κ M) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiPos_existence_paper p c lam M κ κtilde D Λ hcond hD
    hD_ge_one hΛ0 hΛM (fun u => (hpar.producer u).producer)
    hpar.barLip (upperBarrier_isBddFun (le_trans zero_le_one hcond.hM))
    (by
      simpa [rotheSeqOfPaperFromPositiveCond] using
        paperRotheContinuousDependence p c lam M κ Λ
          (fun u => (hpar.producer u).producer) hcond.hκ0.le
          (le_trans zero_le_one hcond.hM) hpar.step hpar.tail)
    (hauxData_of_positive_conditions hcond hD hD_ge_one hpar.producer)
    hprinciple hconv.stationary hsmp hconv.flat

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
#print axioms PaperLemma42EllipticVxEstimate_of_conditions
#print axioms PaperLemma42EllipticVEstimate_of_conditions
#print axioms paperFrozenEllipticSourceBox_of_conditions
#print axioms PaperLemma42LogisticEstimate_of_conditions
#print axioms PaperLemma42KTermEstimate_of_conditions
#print axioms PaperLemma42BadTermEstimate_of_components
#print axioms PaperLemma42PointwiseEstimate_of_badTermEstimate
#print axioms PaperLemma_4_2_paperWaveOperator_from_pointwise_estimate
#print axioms PaperLemma_4_2_paperWaveOperator_from_components
#print axioms PaperLemma_4_2_paperWaveOperator_of_conditions
#print axioms paperLowerBarrierStepData_lowerBarrierRaw_of_paperStep
#print axioms paperLowerRawStepProducer_of_core
#print axioms paperLowerRawParabolicFloor_of_core
#print axioms rotheStepLowerInvariant_lowerBarrierRaw_of_paperStepData
#print axioms rotheSeqOfPaper_lowerBarrierRaw_stepInvariant
#print axioms profileNontrivial_of_lowerBarrierRaw_tail_bound
#print axioms rotheOrbit_profileNontrivial_of_lowerBarrierRaw_stepInvariant
#print axioms rotheSeqOfPaper_profileNontrivial_of_lowerBarrierRaw
#print axioms rotheSeqOfPaperFromCond
#print axioms PaperLowerPinnedStationaryFlatFloor.of_stepConsistency
#print axioms hauxData_of_conditions
#print axioms hsmp_of_odeRealization
#print axioms ShenWork.Paper1.b1_chiNeg_existence_paper
#print axioms b1_chiNeg_existence_paper'
#print axioms b1_chiNeg_existence_paper_clean
#print axioms b1_chiNeg_existence_paper_min
#print axioms PaperLemma42EllipticVEstimate_of_positive_conditions
#print axioms PaperLemma42EllipticVxEstimate_of_positive_conditions
#print axioms PaperLemma42LogisticEstimate_of_positive_conditions
#print axioms PaperLemma42PositiveKTermEstimate_of_positive_conditions
#print axioms PaperLemma42PositiveBadTermEstimate_of_components
#print axioms PaperLemma42PositivePointwiseEstimate_of_badTermEstimate
#print axioms PaperLemma_4_2_positive_paperWaveOperator_of_conditions
#print axioms rotheSeqOfPaper_lowerBarrierRaw_positive_stepInvariant
#print axioms profileNontrivial_of_lowerBarrierRaw_positive_tail_bound
#print axioms rotheSeqOfPaperFromPositiveCond
#print axioms hauxData_of_positive_conditions
#print axioms b1_chiPos_existence_paper
#print axioms b1_chiPos_existence_paper'
#print axioms b1_chiPos_existence_paper_clean
#print axioms b1_chiPos_existence_paper_min
end AxiomAudit

end ShenWork.Paper1

#print axioms ShenWork.Paper1.rotheOrbit_profileNontrivial_of_lowerBarrierRaw_stepInvariant
#print axioms ShenWork.Paper1.rotheSeqOfPaper_profileNontrivial_of_lowerBarrierRaw
#print axioms ShenWork.Paper1.b1_chiNeg_existence_paper
#print axioms ShenWork.Paper1.b1_chiNeg_existence_paper'
#print axioms ShenWork.Paper1.b1_chiNeg_existence_paper_clean

#print axioms ShenWork.Paper1.b1_chiNeg_existence_paper

#print axioms ShenWork.Paper1.b1_chiNeg_existence_paper_clean
#print axioms ShenWork.Paper1.b1_chiNeg_existence_paper_min

#print axioms ShenWork.Paper1.b1_chiPos_existence_paper
#print axioms ShenWork.Paper1.b1_chiPos_existence_paper_clean
#print axioms ShenWork.Paper1.b1_chiPos_existence_paper_min

#print axioms ShenWork.Paper1.b1_chiPos_existence_paper_clean
