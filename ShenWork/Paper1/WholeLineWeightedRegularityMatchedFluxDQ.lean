import ShenWork.Paper1.WholeLineWeightedRegularityDQSources
import ShenWork.Paper1.WholeLineWeightedRegularityFourProfileResolver
import ShenWork.Paper1.WholeLineWeightedRegularityFourProfilePower

open Filter MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

def fourProfileFluxQuotient (p : CMParams) (h : ℝ)
    (a2 b2 a1 b1 : ℝ → ℝ) (x : ℝ) : ℝ :=
  ((a2 x ^ p.m * deriv (frozenElliptic p a2) x -
      b2 x ^ p.m * deriv (frozenElliptic p b2) x) -
    (a1 x ^ p.m * deriv (frozenElliptic p a1) x -
      b1 x ^ p.m * deriv (frozenElliptic p b1) x)) / h

def fourProfilePerturbationQuotient (h : ℝ)
    (a2 b2 a1 b1 : ℝ → ℝ) (x : ℝ) : ℝ :=
  ((a2 x - b2 x) - (a1 x - b1 x)) / h

def fourProfilePerturbationSum
    (a2 b2 a1 b1 : ℝ → ℝ) (x : ℝ) : ℝ :=
  |a1 x - b1 x| + |a2 x - b2 x|

def fourProfilePowerLowerConstant (m M Brel DU : ℝ) : ℝ :=
  if m < 2 then m * Brel * M ^ (m - 1)
  else m * (m - 1) * M ^ (m - 2) * DU

def fourProfilePowerLinearConstant (m M : ℝ) : ℝ :=
  m * M ^ (m - 1)

/-- Pointwise matched flux quotient.  Unlike the two-profile estimate, its
right side contains no standalone wave difference quotient: wave increments
occur only as bounded coefficients multiplying perturbation fields. -/
theorem fourProfileFluxQuotient_abs_le
    (p : CMParams) {M Brel DU h : ℝ}
    (hM : 0 ≤ M) (hBrel : 0 ≤ Brel) (hDU : 0 ≤ DU) (hh : h ≠ 0)
    {a2 b2 a1 b1 : ℝ → ℝ}
    (ha2 : IsCUnifBdd a2) (hb2 : IsCUnifBdd b2)
    (ha2_mem : ∀ x, a2 x ∈ Set.Icc (0 : ℝ) M)
    (hb2_mem : ∀ x, b2 x ∈ Set.Icc (0 : ℝ) M)
    (ha1_mem : ∀ x, a1 x ∈ Set.Icc (0 : ℝ) M)
    (hb1_mem : ∀ x, b1 x ∈ Set.Icc (0 : ℝ) M)
    (hb2pos : ∀ x, 0 < b2 x) (hb1pos : ∀ x, 0 < b1 x)
    (hbase : ∀ x, |(b2 x - b1 x) / h| ≤ DU)
    (hbase_resolver : ∀ x,
      |(deriv (frozenElliptic p b2) x -
        deriv (frozenElliptic p b1) x) / h| ≤ 2 * M ^ p.γ)
    (hrelative : ∀ x, ∀ tau ∈ Set.Icc (0 : ℝ) 1,
      |(b2 x - b1 x) / h| ≤
        Brel * (tau * b2 x + (1 - tau) * b1 x)) :
    ∀ x,
      |fourProfileFluxQuotient p h a2 b2 a1 b1 x| ≤
        (3 * M ^ p.γ * fourProfilePowerLinearConstant p.m M) *
            |fourProfilePerturbationQuotient h a2 b2 a1 b1 x| +
        (3 * M ^ p.γ * fourProfilePowerLowerConstant p.m M Brel DU +
            2 * M ^ p.γ * fourProfilePowerLinearConstant p.m M) *
            fourProfilePerturbationSum a2 b2 a1 b1 x +
        (fourProfilePowerLinearConstant p.m M * DU) *
            |deriv (frozenElliptic p a2) x -
              deriv (frozenElliptic p b2) x| +
        M ^ p.m *
            |fourProfileResolverGradient p a2 a1 b2 b1 x / h| := by
  intro x
  let Am : ℝ := fourProfilePowerLinearConstant p.m M
  let Cm : ℝ := fourProfilePowerLowerConstant p.m M Brel DU
  let V : ℝ := M ^ p.γ
  let P2 : ℝ := a2 x ^ p.m - b2 x ^ p.m
  let P1 : ℝ := a1 x ^ p.m - b1 x ^ p.m
  let D2 : ℝ := deriv (frozenElliptic p a2) x -
    deriv (frozenElliptic p b2) x
  let G : ℝ := fourProfileResolverGradient p a2 a1 b2 b1 x / h
  let q : ℝ := fourProfilePerturbationQuotient h a2 b2 a1 b1 x
  let wsum : ℝ := fourProfilePerturbationSum a2 b2 a1 b1 x
  have hAm0 : 0 ≤ Am := by
    dsimp [Am, fourProfilePowerLinearConstant]
    exact mul_nonneg (le_trans zero_le_one p.hm)
      (Real.rpow_nonneg hM _)
  have hCm0 : 0 ≤ Cm := by
    dsimp [Cm, fourProfilePowerLowerConstant]
    split_ifs
    · exact mul_nonneg
        (mul_nonneg (le_trans zero_le_one p.hm) hBrel)
        (Real.rpow_nonneg hM _)
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (le_trans zero_le_one p.hm) (by linarith [p.hm]))
          (Real.rpow_nonneg hM _)) hDU
  have hV0 : 0 ≤ V := by
    dsimp [V]
    exact Real.rpow_nonneg hM _
  have hwsum0 : 0 ≤ wsum := by
    dsimp [wsum, fourProfilePerturbationSum]
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hPm : |(P2 - P1) / h| ≤ Am * |q| + Cm * wsum := by
    simpa only [P2, P1, q, wsum, Am, Cm,
      fourProfilePerturbationQuotient, fourProfilePerturbationSum,
      fourProfilePowerLinearConstant, fourProfilePowerLowerConstant] using
      paper5_four_profile_power_quotient_bound_of_one_le
        p.hm hM hBrel hDU (ha2_mem x) (hb2_mem x)
        (ha1_mem x) (hb1_mem x) (hb2pos x) (hb1pos x)
        (hbase x) (hrelative x)
  have hPmRhs0 : 0 ≤ Am * |q| + Cm * wsum :=
    add_nonneg (mul_nonneg hAm0 (abs_nonneg _))
      (mul_nonneg hCm0 hwsum0)
  have hP1 : |P1| ≤ Am * |a1 x - b1 x| := by
    dsimp [P1, Am, fourProfilePowerLinearConstant]
    exact abs_rpow_sub_rpow_le_of_mem_Icc p.hm hM
      (ha1_mem x) (hb1_mem x)
  have hBpow : |(b2 x ^ p.m - b1 x ^ p.m) / h| ≤ Am * DU := by
    rw [abs_div]
    have hp := abs_rpow_sub_rpow_le_of_mem_Icc p.hm hM
      (hb2_mem x) (hb1_mem x)
    have habsh : 0 < |h| := abs_pos.mpr hh
    apply (div_le_iff₀ habsh).2
    calc
      |b2 x ^ p.m - b1 x ^ p.m| ≤
          fourProfilePowerLinearConstant p.m M * |b2 x - b1 x| := hp
      _ = fourProfilePowerLinearConstant p.m M *
          (|(b2 x - b1 x) / h| * |h|) := by
        rw [abs_div]
        field_simp
      _ ≤ fourProfilePowerLinearConstant p.m M * (DU * |h|) := by
        gcongr
        exact hbase x
      _ = (Am * DU) * |h| := by simp only [Am]; ring
  have hrb2 : |deriv (frozenElliptic p b2) x| ≤ V := by
    simpa only [V] using frozenElliptic_deriv_abs_le_rpow_of_Icc
      p hM hb2 hb2_mem x
  have hrbq : |(deriv (frozenElliptic p b2) x -
      deriv (frozenElliptic p b1) x) / h| ≤ 2 * V := by
    simpa only [V] using hbase_resolver x
  have hD2 : |D2| ≤ 2 * V := by
    dsimp [D2]
    calc
      |deriv (frozenElliptic p a2) x - deriv (frozenElliptic p b2) x| ≤
          |deriv (frozenElliptic p a2) x| +
            |deriv (frozenElliptic p b2) x| := abs_sub _ _
      _ ≤ V + V := by
        apply add_le_add
        · simpa only [V] using
            (frozenElliptic_deriv_abs_le_rpow_of_Icc
              p hM ha2 ha2_mem x)
        · exact hrb2
      _ = 2 * V := by ring
  have ha1pow : |a1 x ^ p.m| ≤ M ^ p.m := by
    rw [abs_of_nonneg (Real.rpow_nonneg (ha1_mem x).1 _)]
    exact Real.rpow_le_rpow (ha1_mem x).1 (ha1_mem x).2
      (le_trans zero_le_one p.hm)
  have hApowEq : (a2 x ^ p.m - a1 x ^ p.m) / h =
      (P2 - P1) / h + (b2 x ^ p.m - b1 x ^ p.m) / h := by
    dsimp [P2, P1]
    ring
  have hsplit : fourProfileFluxQuotient p h a2 b2 a1 b1 x =
      ((P2 - P1) / h) * deriv (frozenElliptic p b2) x +
      P1 * ((deriv (frozenElliptic p b2) x -
        deriv (frozenElliptic p b1) x) / h) +
      ((a2 x ^ p.m - a1 x ^ p.m) / h) * D2 +
      a1 x ^ p.m * G := by
    dsimp [fourProfileFluxQuotient, P2, P1, D2, G,
      fourProfileResolverGradient]
    ring
  rw [hsplit]
  have hfour :
      |((P2 - P1) / h) * deriv (frozenElliptic p b2) x +
        P1 * ((deriv (frozenElliptic p b2) x -
          deriv (frozenElliptic p b1) x) / h) +
        ((a2 x ^ p.m - a1 x ^ p.m) / h) * D2 +
        a1 x ^ p.m * G| ≤
      |(P2 - P1) / h| * |deriv (frozenElliptic p b2) x| +
      |P1| * |(deriv (frozenElliptic p b2) x -
          deriv (frozenElliptic p b1) x) / h| +
      |(a2 x ^ p.m - a1 x ^ p.m) / h| * |D2| +
      |a1 x ^ p.m| * |G| := by
    have h1 := abs_add_le
      (((P2 - P1) / h) * deriv (frozenElliptic p b2) x)
      (P1 * ((deriv (frozenElliptic p b2) x -
        deriv (frozenElliptic p b1) x) / h))
    have h2 := abs_add_le
      (((P2 - P1) / h) * deriv (frozenElliptic p b2) x +
        P1 * ((deriv (frozenElliptic p b2) x -
          deriv (frozenElliptic p b1) x) / h))
      (((a2 x ^ p.m - a1 x ^ p.m) / h) * D2)
    have h3 := abs_add_le
      ((((P2 - P1) / h) * deriv (frozenElliptic p b2) x +
        P1 * ((deriv (frozenElliptic p b2) x -
          deriv (frozenElliptic p b1) x) / h)) +
        ((a2 x ^ p.m - a1 x ^ p.m) / h) * D2)
      (a1 x ^ p.m * G)
    simp only [abs_mul] at h1 h2 h3 ⊢
    linarith
  calc
    |((P2 - P1) / h) * deriv (frozenElliptic p b2) x +
        P1 * ((deriv (frozenElliptic p b2) x -
          deriv (frozenElliptic p b1) x) / h) +
        ((a2 x ^ p.m - a1 x ^ p.m) / h) * D2 +
        a1 x ^ p.m * G| ≤
      |(P2 - P1) / h| * |deriv (frozenElliptic p b2) x| +
      |P1| * |(deriv (frozenElliptic p b2) x -
          deriv (frozenElliptic p b1) x) / h| +
      |(a2 x ^ p.m - a1 x ^ p.m) / h| * |D2| +
      |a1 x ^ p.m| * |G| := hfour
    _ = |(P2 - P1) / h| * |deriv (frozenElliptic p b2) x| +
      |P1| * |(deriv (frozenElliptic p b2) x -
          deriv (frozenElliptic p b1) x) / h| +
      |((P2 - P1) / h + (b2 x ^ p.m - b1 x ^ p.m) / h)| * |D2| +
      |a1 x ^ p.m| * |G| := by
        rw [hApowEq]
    _ ≤ |(P2 - P1) / h| * |deriv (frozenElliptic p b2) x| +
      |P1| * |(deriv (frozenElliptic p b2) x -
          deriv (frozenElliptic p b1) x) / h| +
      (|(P2 - P1) / h| * |D2| +
        |(b2 x ^ p.m - b1 x ^ p.m) / h| * |D2|) +
      |a1 x ^ p.m| * |G| := by
        gcongr
        calc
          |(P2 - P1) / h + (b2 x ^ p.m - b1 x ^ p.m) / h| * |D2| ≤
              (|(P2 - P1) / h| +
                |(b2 x ^ p.m - b1 x ^ p.m) / h|) * |D2| :=
            mul_le_mul_of_nonneg_right
              (abs_add_le ((P2 - P1) / h)
                ((b2 x ^ p.m - b1 x ^ p.m) / h)) (abs_nonneg _)
          _ = |(P2 - P1) / h| * |D2| +
              |(b2 x ^ p.m - b1 x ^ p.m) / h| * |D2| := by ring
    _ ≤ (Am * |q| + Cm * wsum) * V +
        (Am * |a1 x - b1 x|) * (2 * V) +
        ((Am * |q| + Cm * wsum) * (2 * V) +
          (Am * DU) * |D2|) +
        M ^ p.m * |G| := by
      have ht1 : |(P2 - P1) / h| *
          |deriv (frozenElliptic p b2) x| ≤
          (Am * |q| + Cm * wsum) * V :=
        mul_le_mul hPm hrb2 (abs_nonneg _) hPmRhs0
      have ht2 : |P1| * |(deriv (frozenElliptic p b2) x -
          deriv (frozenElliptic p b1) x) / h| ≤
          (Am * |a1 x - b1 x|) * (2 * V) :=
        mul_le_mul hP1 hrbq (abs_nonneg _)
          (mul_nonneg hAm0 (abs_nonneg _))
      have ht3a : |(P2 - P1) / h| * |D2| ≤
          (Am * |q| + Cm * wsum) * (2 * V) :=
        mul_le_mul hPm hD2 (abs_nonneg _) hPmRhs0
      have ht3b : |(b2 x ^ p.m - b1 x ^ p.m) / h| * |D2| ≤
          (Am * DU) * |D2| :=
        mul_le_mul_of_nonneg_right hBpow (abs_nonneg _)
      have ht4 : |a1 x ^ p.m| * |G| ≤ M ^ p.m * |G| :=
        mul_le_mul_of_nonneg_right ha1pow (abs_nonneg _)
      apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · exact ht1
          · exact ht2
        · apply add_le_add
          · exact ht3a
          · exact ht3b
      · exact ht4
    _ ≤ (3 * M ^ p.γ * fourProfilePowerLinearConstant p.m M) * |q| +
        (3 * M ^ p.γ * fourProfilePowerLowerConstant p.m M Brel DU +
          2 * M ^ p.γ * fourProfilePowerLinearConstant p.m M) * wsum +
        (fourProfilePowerLinearConstant p.m M * DU) * |D2| +
        M ^ p.m * |G| := by
      have hw1 : |a1 x - b1 x| ≤ wsum := by
        dsimp [wsum, fourProfilePerturbationSum]
        exact le_add_of_nonneg_right (abs_nonneg _)
      have hcoef : 0 ≤ 2 * V * Am := by positivity
      have hmid : (Am * |a1 x - b1 x|) * (2 * V) ≤
          Am * wsum * (2 * V) := by
        gcongr
      calc
        (Am * |q| + Cm * wsum) * V +
              (Am * |a1 x - b1 x|) * (2 * V) +
            ((Am * |q| + Cm * wsum) * (2 * V) +
              Am * DU * |D2|) +
          M ^ p.m * |G| ≤
            (Am * |q| + Cm * wsum) * V +
              (Am * wsum) * (2 * V) +
            ((Am * |q| + Cm * wsum) * (2 * V) +
              Am * DU * |D2|) +
          M ^ p.m * |G| := by gcongr
        _ = _ := by
          dsimp [Am, Cm, V, q, wsum,
            fourProfilePowerLinearConstant, fourProfilePowerLowerConstant]
          ring

/-- Scaled four-profile resolver-gradient estimate.  This is the quotient
form needed after spatial differencing; the denominator cancels exactly and
does not enter the final constant. -/
theorem capWeight_fourProfile_resolverGradient_quotient_l2_bounded
    (p : CMParams) {M eta R Cq Cw h : ℝ}
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hh : h ≠ 0)
    {a2 a1 b2 b1 q w : ℝ → ℝ}
    (ha2 : IsCUnifBdd a2) (ha1 : IsCUnifBdd a1)
    (hb2 : IsCUnifBdd b2) (hb1 : IsCUnifBdd b1)
    (ha2_mem : ∀ x, a2 x ∈ Set.Icc (0 : ℝ) M)
    (ha1_mem : ∀ x, a1 x ∈ Set.Icc (0 : ℝ) M)
    (hb2_mem : ∀ x, b2 x ∈ Set.Icc (0 : ℝ) M)
    (hb1_mem : ∀ x, b1 x ∈ Set.Icc (0 : ℝ) M)
    (hq : Integrable (fun x => capWeight eta R x * |q x| ^ 2))
    (hw : Integrable (fun x => capWeight eta R x * |w x| ^ 2))
    (hsource : ∀ x,
      |fourProfilePowerSource p a2 a1 b2 b1 x / h| ^ 2 ≤
        Cq ^ 2 * |q x| ^ 2 + Cw ^ 2 * |w x| ^ 2) :
    Integrable (fun x => capWeight eta R x *
        |fourProfileResolverGradient p a2 a1 b2 b1 x / h| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
          |fourProfileResolverGradient p a2 a1 b2 b1 x / h| ^ 2) ≤
        (1 / (1 - eta)) ^ 2 *
          (Cq ^ 2 * (∫ x : ℝ, capWeight eta R x * |q x| ^ 2) +
            Cw ^ 2 * (∫ x : ℝ, capWeight eta R x * |w x| ^ 2)) := by
  have hsourceRaw : ∀ x,
      |fourProfilePowerSource p a2 a1 b2 b1 x| ^ 2 ≤
        (|h| * Cq) ^ 2 * |q x| ^ 2 +
          (|h| * Cw) ^ 2 * |w x| ^ 2 := by
    intro x
    have hmul := mul_le_mul_of_nonneg_left (hsource x) (sq_nonneg h)
    calc
      |fourProfilePowerSource p a2 a1 b2 b1 x| ^ 2 =
          h ^ 2 * |fourProfilePowerSource p a2 a1 b2 b1 x / h| ^ 2 := by
        rw [abs_div, div_pow, sq_abs h]
        field_simp
      _ ≤ h ^ 2 * (Cq ^ 2 * |q x| ^ 2 + Cw ^ 2 * |w x| ^ 2) := hmul
      _ = (|h| * Cq) ^ 2 * |q x| ^ 2 +
          (|h| * Cw) ^ 2 * |w x| ^ 2 := by
        rw [mul_pow, mul_pow, sq_abs h]
        ring_nf
  have hraw := capWeight_fourProfile_resolver_commutator_of_pointwise_source_bound
    p heta0 heta1 ha2 ha1 hb2 hb1
      ha2_mem ha1_mem hb2_mem hb1_mem hq hw hsourceRaw
  have hgrad := hraw.2
  have hint : Integrable (fun x => capWeight eta R x *
      |fourProfileResolverGradient p a2 a1 b2 b1 x / h| ^ 2) := by
    have hs := hgrad.1.const_mul (h⁻¹ ^ 2)
    refine hs.congr (Eventually.of_forall fun x => ?_)
    change h⁻¹ ^ 2 * (capWeight eta R x *
        |fourProfileResolverGradient p a2 a1 b2 b1 x| ^ 2) =
      capWeight eta R x *
        |fourProfileResolverGradient p a2 a1 b2 b1 x / h| ^ 2
    rw [abs_div, div_pow, sq_abs h]
    field_simp
  refine ⟨hint, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hgrad.2 (sq_nonneg h⁻¹)
  calc
    (∫ x : ℝ, capWeight eta R x *
        |fourProfileResolverGradient p a2 a1 b2 b1 x / h| ^ 2) =
        h⁻¹ ^ 2 * (∫ x : ℝ, capWeight eta R x *
          |fourProfileResolverGradient p a2 a1 b2 b1 x| ^ 2) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [abs_div, div_pow, sq_abs h]
      ring
    _ ≤ h⁻¹ ^ 2 * ((1 / (1 - eta)) ^ 2 *
        ((|h| * Cq) ^ 2 *
            (∫ x : ℝ, capWeight eta R x * |q x| ^ 2) +
          (|h| * Cw) ^ 2 *
            (∫ x : ℝ, capWeight eta R x * |w x| ^ 2))) := hmul
    _ = (1 / (1 - eta)) ^ 2 *
        (Cq ^ 2 * (∫ x : ℝ, capWeight eta R x * |q x| ^ 2) +
          Cw ^ 2 * (∫ x : ℝ, capWeight eta R x * |w x| ^ 2)) := by
      rw [mul_pow, mul_pow, sq_abs]
      field_simp

/-- Four-term cap-weighted square summation. -/
theorem capWeighted_fourTerm_l2_bounded
    {eta R C1 C2 C3 C4 : ℝ}
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    {out q1 q2 q3 q4 : ℝ → ℝ}
    (hout : Continuous out)
    (hq1 : Integrable (fun x => capWeight eta R x * |q1 x| ^ 2))
    (hq2 : Integrable (fun x => capWeight eta R x * |q2 x| ^ 2))
    (hq3 : Integrable (fun x => capWeight eta R x * |q3 x| ^ 2))
    (hq4 : Integrable (fun x => capWeight eta R x * |q4 x| ^ 2))
    (hpoint : ∀ x, |out x| ≤
      C1 * |q1 x| + C2 * |q2 x| + C3 * |q3 x| + C4 * |q4 x|) :
    Integrable (fun x => (capWeightSqrt eta R x * out x) ^ 2) ∧
      (∫ x : ℝ, (capWeightSqrt eta R x * out x) ^ 2) ≤
        4 * (C1 ^ 2 * (∫ x : ℝ, capWeight eta R x * |q1 x| ^ 2) +
          C2 ^ 2 * (∫ x : ℝ, capWeight eta R x * |q2 x| ^ 2) +
          C3 ^ 2 * (∫ x : ℝ, capWeight eta R x * |q3 x| ^ 2) +
          C4 ^ 2 * (∫ x : ℝ, capWeight eta R x * |q4 x| ^ 2)) := by
  let Q1 : ℝ → ℝ := fun x => capWeightSqrt eta R x * q1 x
  let Q2 : ℝ → ℝ := fun x => capWeightSqrt eta R x * q2 x
  let Q3 : ℝ → ℝ := fun x => capWeightSqrt eta R x * q3 x
  let Q4 : ℝ → ℝ := fun x => capWeightSqrt eta R x * q4 x
  let O : ℝ → ℝ := fun x => capWeightSqrt eta R x * out x
  have hQi (q : ℝ → ℝ)
      (hq : Integrable (fun x => capWeight eta R x * |q x| ^ 2)) :
      Integrable (fun x => (capWeightSqrt eta R x * q x) ^ 2) := by
    refine hq.congr (Eventually.of_forall fun x => ?_)
    exact (capWeightSqrt_mul_sq_eq eta R x (q x)).symm
  have hQ1 := hQi q1 hq1
  have hQ2 := hQi q2 hq2
  have hQ3 := hQi q3 hq3
  have hQ4 := hQi q4 hq4
  have hT1 : Integrable (fun x => C1 ^ 2 * Q1 x ^ 2) := by
    simpa only [Q1] using hQ1.const_mul (C1 ^ 2)
  have hT2 : Integrable (fun x => C2 ^ 2 * Q2 x ^ 2) := by
    simpa only [Q2] using hQ2.const_mul (C2 ^ 2)
  have hT3 : Integrable (fun x => C3 ^ 2 * Q3 x ^ 2) := by
    simpa only [Q3] using hQ3.const_mul (C3 ^ 2)
  have hT4 : Integrable (fun x => C4 ^ 2 * Q4 x ^ 2) := by
    simpa only [Q4] using hQ4.const_mul (C4 ^ 2)
  have hpointW : ∀ x, |O x| ≤
      C1 * |Q1 x| + C2 * |Q2 x| + C3 * |Q3 x| + C4 * |Q4 x| := by
    intro x
    have hw : 0 ≤ capWeightSqrt eta R x := (capWeightSqrt_pos eta R x).le
    dsimp [O, Q1, Q2, Q3, Q4]
    rw [abs_mul, abs_of_nonneg hw, abs_mul, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg hw]
    calc
      capWeightSqrt eta R x * |out x| ≤ capWeightSqrt eta R x *
          (C1 * |q1 x| + C2 * |q2 x| + C3 * |q3 x| + C4 * |q4 x|) :=
        mul_le_mul_of_nonneg_left (hpoint x) hw
      _ = C1 * (capWeightSqrt eta R x * |q1 x|) +
          C2 * (capWeightSqrt eta R x * |q2 x|) +
          C3 * (capWeightSqrt eta R x * |q3 x|) +
          C4 * (capWeightSqrt eta R x * |q4 x|) := by ring
  have hpointSq : ∀ x, O x ^ 2 ≤ 4 *
      (C1 ^ 2 * Q1 x ^ 2 + C2 ^ 2 * Q2 x ^ 2 +
        C3 ^ 2 * Q3 x ^ 2 + C4 ^ 2 * Q4 x ^ 2) := by
    intro x
    let a := C1 * |Q1 x|
    let b := C2 * |Q2 x|
    let c := C3 * |Q3 x|
    let d := C4 * |Q4 x|
    have ha : 0 ≤ a := mul_nonneg hC1 (abs_nonneg _)
    have hb : 0 ≤ b := mul_nonneg hC2 (abs_nonneg _)
    have hc : 0 ≤ c := mul_nonneg hC3 (abs_nonneg _)
    have hd : 0 ≤ d := mul_nonneg hC4 (abs_nonneg _)
    have hs := (sq_le_sq₀ (abs_nonneg _)
      (add_nonneg (add_nonneg (add_nonneg ha hb) hc) hd)).2 (hpointW x)
    have hsum : (a + b + c + d) ^ 2 ≤
        4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
        sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
    calc
      O x ^ 2 = |O x| ^ 2 := (sq_abs _).symm
      _ ≤ (a + b + c + d) ^ 2 := hs
      _ ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := hsum
      _ = 4 * (C1 ^ 2 * Q1 x ^ 2 + C2 ^ 2 * Q2 x ^ 2 +
          C3 ^ 2 * Q3 x ^ 2 + C4 ^ 2 * Q4 x ^ 2) := by
        dsimp [a, b, c, d]
        rw [mul_pow, mul_pow, mul_pow, mul_pow, sq_abs, sq_abs, sq_abs, sq_abs]
  have hmajor : Integrable (fun x => 4 *
      (C1 ^ 2 * Q1 x ^ 2 + C2 ^ 2 * Q2 x ^ 2 +
        C3 ^ 2 * Q3 x ^ 2 + C4 ^ 2 * Q4 x ^ 2)) := by
    exact (((hT1.add hT2).add hT3).add hT4).const_mul 4
  have hOcont : Continuous O :=
    (capWeightSqrt_continuous eta R).mul hout
  have hO : Integrable (fun x => O x ^ 2) := by
    refine Integrable.mono' hmajor (hOcont.pow 2).aestronglyMeasurable ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpointSq x
  refine ⟨by simpa only [O] using hO, ?_⟩
  calc
    (∫ x : ℝ, (capWeightSqrt eta R x * out x) ^ 2) =
        ∫ x : ℝ, O x ^ 2 := by rfl
    _ ≤ ∫ x : ℝ, 4 *
        (C1 ^ 2 * Q1 x ^ 2 + C2 ^ 2 * Q2 x ^ 2 +
          C3 ^ 2 * Q3 x ^ 2 + C4 ^ 2 * Q4 x ^ 2) :=
      integral_mono hO hmajor hpointSq
    _ = 4 * (C1 ^ 2 * (∫ x : ℝ, Q1 x ^ 2) +
        C2 ^ 2 * (∫ x : ℝ, Q2 x ^ 2) +
        C3 ^ 2 * (∫ x : ℝ, Q3 x ^ 2) +
        C4 ^ 2 * (∫ x : ℝ, Q4 x ^ 2)) := by
      have hsumint :
          (∫ x : ℝ, C1 ^ 2 * Q1 x ^ 2 + C2 ^ 2 * Q2 x ^ 2 +
              C3 ^ 2 * Q3 x ^ 2 + C4 ^ 2 * Q4 x ^ 2) =
            C1 ^ 2 * (∫ x : ℝ, Q1 x ^ 2) +
              C2 ^ 2 * (∫ x : ℝ, Q2 x ^ 2) +
              C3 ^ 2 * (∫ x : ℝ, Q3 x ^ 2) +
              C4 ^ 2 * (∫ x : ℝ, Q4 x ^ 2) := by
        calc
          (∫ x : ℝ, C1 ^ 2 * Q1 x ^ 2 + C2 ^ 2 * Q2 x ^ 2 +
              C3 ^ 2 * Q3 x ^ 2 + C4 ^ 2 * Q4 x ^ 2) =
              (∫ x : ℝ, C1 ^ 2 * Q1 x ^ 2 + C2 ^ 2 * Q2 x ^ 2 +
                C3 ^ 2 * Q3 x ^ 2) +
              ∫ x : ℝ, C4 ^ 2 * Q4 x ^ 2 :=
            integral_add ((hT1.add hT2).add hT3) hT4
          _ = ((∫ x : ℝ, C1 ^ 2 * Q1 x ^ 2 + C2 ^ 2 * Q2 x ^ 2) +
                ∫ x : ℝ, C3 ^ 2 * Q3 x ^ 2) +
              ∫ x : ℝ, C4 ^ 2 * Q4 x ^ 2 := by
            exact congrArg (fun z => z + ∫ x : ℝ, C4 ^ 2 * Q4 x ^ 2)
              (integral_add (hT1.add hT2) hT3)
          _ = (((∫ x : ℝ, C1 ^ 2 * Q1 x ^ 2) +
                ∫ x : ℝ, C2 ^ 2 * Q2 x ^ 2) +
                ∫ x : ℝ, C3 ^ 2 * Q3 x ^ 2) +
              ∫ x : ℝ, C4 ^ 2 * Q4 x ^ 2 := by
            exact congrArg
              (fun z => (z + ∫ x : ℝ, C3 ^ 2 * Q3 x ^ 2) +
                ∫ x : ℝ, C4 ^ 2 * Q4 x ^ 2)
              (integral_add hT1 hT2)
          _ = _ := by simp only [integral_const_mul]
      rw [integral_const_mul, hsumint]
    _ = 4 * (C1 ^ 2 * (∫ x : ℝ, capWeight eta R x * |q1 x| ^ 2) +
        C2 ^ 2 * (∫ x : ℝ, capWeight eta R x * |q2 x| ^ 2) +
        C3 ^ 2 * (∫ x : ℝ, capWeight eta R x * |q3 x| ^ 2) +
        C4 ^ 2 * (∫ x : ℝ, capWeight eta R x * |q4 x| ^ 2)) := by
      have hQ1eq : (∫ x : ℝ, Q1 x ^ 2) =
          ∫ x : ℝ, capWeight eta R x * |q1 x| ^ 2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x =>
          capWeightSqrt_mul_sq_eq eta R x _
      have hQ2eq : (∫ x : ℝ, Q2 x ^ 2) =
          ∫ x : ℝ, capWeight eta R x * |q2 x| ^ 2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x =>
          capWeightSqrt_mul_sq_eq eta R x _
      have hQ3eq : (∫ x : ℝ, Q3 x ^ 2) =
          ∫ x : ℝ, capWeight eta R x * |q3 x| ^ 2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x =>
          capWeightSqrt_mul_sq_eq eta R x _
      have hQ4eq : (∫ x : ℝ, Q4 x ^ 2) =
          ∫ x : ℝ, capWeight eta R x * |q4 x| ^ 2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x =>
          capWeightSqrt_mul_sq_eq eta R x _
      rw [hQ1eq, hQ2eq, hQ3eq, hQ4eq]

/-- The two perturbation endpoints which occur in a matched spatial
increment are cap-square integrable, with only the usual translation cost. -/
theorem capWeight_shifted_perturbationSum_l2_bounded
    {eta R h : ℝ} (heta : 0 ≤ eta)
    {u U : ℝ → ℝ} (hu : Continuous u) (hU : Continuous U)
    (hW : Integrable (fun x : ℝ =>
      capWeight eta R x * |u x - U x| ^ 2)) :
    Integrable (fun x : ℝ => capWeight eta R x *
        |fourProfilePerturbationSum
          (fun y => u (y + h)) (fun y => U (y + h)) u U x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
          |fourProfilePerturbationSum
            (fun y => u (y + h)) (fun y => U (y + h)) u U x| ^ 2) ≤
        2 * (1 + Real.exp (2 * eta * |h|)) *
          ∫ x : ℝ, capWeight eta R x * |u x - U x| ^ 2 := by
  let w : ℝ → ℝ := fun x => u x - U x
  let ws : ℝ → ℝ := fun x => w (x + h)
  let out : ℝ → ℝ := fun x => |w x| + |ws x|
  have hw : Continuous w := hu.sub hU
  have hshift := capWeight_shift_sq_integrable_and_integral_le
    (eta := eta) (R := R) (d := h) heta hw
      (by simpa only [w] using hW)
  have hout : Continuous out := hw.abs.add
    (hw.comp (continuous_id.add continuous_const)).abs
  have hcore := capWeighted_twoTerm_l2_bounded
    (eta := eta) (R := R) (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) ≤ 1) hout
      (by simpa only [w] using hW)
      (by simpa only [ws, w] using hshift.1)
      (fun x => by
        dsimp [out, ws, w]
        rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)),
          one_mul, one_mul])
  have hcore_int : Integrable (fun x : ℝ =>
      capWeight eta R x * |out x| ^ 2) := by
    refine hcore.1.congr (Eventually.of_forall fun x => ?_)
    exact capWeightSqrt_mul_sq_eq eta R x (out x)
  refine ⟨by simpa only [out, w, ws,
      fourProfilePerturbationSum] using hcore_int, ?_⟩
  have hcore_le :
      (∫ x : ℝ, capWeight eta R x * |out x| ^ 2) ≤
        2 * (∫ x : ℝ, capWeight eta R x * |w x| ^ 2) +
          2 * ∫ x : ℝ, capWeight eta R x * |ws x| ^ 2 := by
    calc
      (∫ x : ℝ, capWeight eta R x * |out x| ^ 2) =
          ∫ x : ℝ, (capWeightSqrt eta R x * out x) ^ 2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x =>
          (capWeightSqrt_mul_sq_eq eta R x (out x)).symm
      _ ≤ 2 * 1 ^ 2 *
            (∫ x : ℝ, capWeight eta R x * |w x| ^ 2) +
          2 * 1 ^ 2 *
            ∫ x : ℝ, capWeight eta R x * |ws x| ^ 2 := hcore.2
      _ = _ := by norm_num
  change (∫ x : ℝ, capWeight eta R x * |out x| ^ 2) ≤ _
  calc
    (∫ x : ℝ, capWeight eta R x * |out x| ^ 2) ≤
        2 * (∫ x : ℝ, capWeight eta R x * |w x| ^ 2) +
          2 * ∫ x : ℝ, capWeight eta R x * |ws x| ^ 2 := hcore_le
    _ ≤ 2 * (∫ x : ℝ, capWeight eta R x * |w x| ^ 2) +
          2 * (Real.exp (2 * eta * |h|) *
            ∫ x : ℝ, capWeight eta R x * |w x| ^ 2) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (by simpa only [ws, w] using hshift.2) (by norm_num))
    _ = 2 * (1 + Real.exp (2 * eta * |h|)) *
          ∫ x : ℝ, capWeight eta R x * |w x| ^ 2 := by ring
    _ = _ := by rfl

/-- Translation covariance plus the elliptic equation give the uniform
wave-resolver spatial quotient coefficient used by the matched flux bound. -/
theorem frozenElliptic_deriv_shift_quotient_abs_le
    (p : CMParams) {M h : ℝ} (hM : 0 ≤ M) (hh : h ≠ 0)
    {U : ℝ → ℝ} (hU : IsCUnifBdd U)
    (hU_mem : ∀ x, U x ∈ Set.Icc (0 : ℝ) M) :
    ∀ x,
      |(deriv (frozenElliptic p (fun y => U (y + h))) x -
          deriv (frozenElliptic p U) x) / h| ≤ 2 * M ^ p.γ := by
  intro x
  rw [frozenElliptic_deriv_comp_add_const p hU
    (fun y => (hU_mem y).1) h x, abs_div]
  have hlip := (frozenElliptic_deriv_lipschitz_of_Icc
    p hM hU hU_mem).dist_le_mul (x + h) x
  have hdist : dist (x + h) x = |h| := by
    rw [Real.dist_eq]
    congr 1
    ring
  rw [hdist, Real.coe_toNNReal _ (mul_nonneg (by norm_num)
    (Real.rpow_nonneg hM _))] at hlip
  have hhabs : 0 < |h| := abs_pos.mpr hh
  calc
    |deriv (frozenElliptic p U) (x + h) -
        deriv (frozenElliptic p U) x| / |h| ≤
        (2 * M ^ p.γ * |h|) / |h| :=
      div_le_div_of_nonneg_right hlip hhabs.le
    _ = 2 * M ^ p.γ := by field_simp

/-- Cap-square lift of the pointwise matched four-profile flux estimate. -/
theorem capWeighted_fourProfileFluxQuotient_l2_bounded
    (p : CMParams) {M Brel DU eta R h : ℝ}
    (hM : 0 ≤ M) (hBrel : 0 ≤ Brel) (hDU : 0 ≤ DU) (hh : h ≠ 0)
    {a2 b2 a1 b1 : ℝ → ℝ}
    (ha2 : IsCUnifBdd a2) (hb2 : IsCUnifBdd b2)
    (ha1 : IsCUnifBdd a1) (hb1 : IsCUnifBdd b1)
    (ha2_mem : ∀ x, a2 x ∈ Set.Icc (0 : ℝ) M)
    (hb2_mem : ∀ x, b2 x ∈ Set.Icc (0 : ℝ) M)
    (ha1_mem : ∀ x, a1 x ∈ Set.Icc (0 : ℝ) M)
    (hb1_mem : ∀ x, b1 x ∈ Set.Icc (0 : ℝ) M)
    (hb2pos : ∀ x, 0 < b2 x) (hb1pos : ∀ x, 0 < b1 x)
    (hbase : ∀ x, |(b2 x - b1 x) / h| ≤ DU)
    (hbase_resolver : ∀ x,
      |(deriv (frozenElliptic p b2) x -
        deriv (frozenElliptic p b1) x) / h| ≤ 2 * M ^ p.γ)
    (hrelative : ∀ x, ∀ tau ∈ Set.Icc (0 : ℝ) 1,
      |(b2 x - b1 x) / h| ≤
        Brel * (tau * b2 x + (1 - tau) * b1 x))
    (hq : Integrable (fun x => capWeight eta R x *
      |fourProfilePerturbationQuotient h a2 b2 a1 b1 x| ^ 2))
    (hwsum : Integrable (fun x => capWeight eta R x *
      |fourProfilePerturbationSum a2 b2 a1 b1 x| ^ 2))
    (hD2 : Integrable (fun x => capWeight eta R x *
      |deriv (frozenElliptic p a2) x -
        deriv (frozenElliptic p b2) x| ^ 2))
    (hG : Integrable (fun x => capWeight eta R x *
      |fourProfileResolverGradient p a2 a1 b2 b1 x / h| ^ 2)) :
    Integrable (fun x =>
        (capWeightSqrt eta R x *
          fourProfileFluxQuotient p h a2 b2 a1 b1 x) ^ 2) ∧
      (∫ x : ℝ, (capWeightSqrt eta R x *
          fourProfileFluxQuotient p h a2 b2 a1 b1 x) ^ 2) ≤
        4 * ((3 * M ^ p.γ * fourProfilePowerLinearConstant p.m M) ^ 2 *
            (∫ x : ℝ, capWeight eta R x *
              |fourProfilePerturbationQuotient h a2 b2 a1 b1 x| ^ 2) +
          (3 * M ^ p.γ * fourProfilePowerLowerConstant p.m M Brel DU +
              2 * M ^ p.γ * fourProfilePowerLinearConstant p.m M) ^ 2 *
            (∫ x : ℝ, capWeight eta R x *
              |fourProfilePerturbationSum a2 b2 a1 b1 x| ^ 2) +
          (fourProfilePowerLinearConstant p.m M * DU) ^ 2 *
            (∫ x : ℝ, capWeight eta R x *
              |deriv (frozenElliptic p a2) x -
                deriv (frozenElliptic p b2) x| ^ 2) +
          (M ^ p.m) ^ 2 *
            ∫ x : ℝ, capWeight eta R x *
              |fourProfileResolverGradient p a2 a1 b2 b1 x / h| ^ 2) := by
  let q : ℝ → ℝ := fourProfilePerturbationQuotient h a2 b2 a1 b1
  let w : ℝ → ℝ := fourProfilePerturbationSum a2 b2 a1 b1
  let d : ℝ → ℝ := fun x => deriv (frozenElliptic p a2) x -
    deriv (frozenElliptic p b2) x
  let g : ℝ → ℝ := fun x =>
    fourProfileResolverGradient p a2 a1 b2 b1 x / h
  let out : ℝ → ℝ := fourProfileFluxQuotient p h a2 b2 a1 b1
  let Cq : ℝ := 3 * M ^ p.γ * fourProfilePowerLinearConstant p.m M
  let Cw : ℝ := 3 * M ^ p.γ *
      fourProfilePowerLowerConstant p.m M Brel DU +
    2 * M ^ p.γ * fourProfilePowerLinearConstant p.m M
  let Cd : ℝ := fourProfilePowerLinearConstant p.m M * DU
  let Cg : ℝ := M ^ p.m
  have hAm : 0 ≤ fourProfilePowerLinearConstant p.m M := by
    exact mul_nonneg (le_trans zero_le_one p.hm) (Real.rpow_nonneg hM _)
  have hCm : 0 ≤ fourProfilePowerLowerConstant p.m M Brel DU := by
    dsimp [fourProfilePowerLowerConstant]
    split_ifs
    · exact mul_nonneg
        (mul_nonneg (le_trans zero_le_one p.hm) hBrel)
        (Real.rpow_nonneg hM _)
    · have hm1 : 0 ≤ p.m - 1 := by linarith [p.hm]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (le_trans zero_le_one p.hm) hm1)
          (Real.rpow_nonneg hM _)) hDU
  have hCq : 0 ≤ Cq := by dsimp [Cq]; positivity
  have hCw : 0 ≤ Cw := by dsimp [Cw]; positivity
  have hCd : 0 ≤ Cd := by dsimp [Cd]; positivity
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  have hflux (f : ℝ → ℝ) (hf : IsCUnifBdd f)
      (hfmem : ∀ x, f x ∈ Set.Icc (0 : ℝ) M) :
      Continuous (fun x => f x ^ p.m * deriv (frozenElliptic p f) x) := by
    exact (hf.1.rpow_const (fun _ => Or.inr (le_trans zero_le_one p.hm))).mul
      ((frozenElliptic_deriv_lipschitz_of_Icc p hM hf hfmem).continuous)
  have hout : Continuous out := by
    dsimp [out, fourProfileFluxQuotient]
    exact (((hflux a2 ha2 ha2_mem).sub (hflux b2 hb2 hb2_mem)).sub
      ((hflux a1 ha1 ha1_mem).sub (hflux b1 hb1 hb1_mem))).div_const h
  have hpoint : ∀ x, |out x| ≤
      Cq * |q x| + Cw * |w x| + Cd * |d x| + Cg * |g x| := by
    intro x
    have hw0 : 0 ≤ fourProfilePerturbationSum a2 b2 a1 b1 x :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    simpa only [out, q, w, d, g, Cq, Cw, Cd, Cg,
      abs_of_nonneg hw0] using
      fourProfileFluxQuotient_abs_le p hM hBrel hDU hh
        ha2 hb2 ha2_mem hb2_mem ha1_mem hb1_mem
        hb2pos hb1pos hbase hbase_resolver hrelative x
  simpa only [out, q, w, d, g, Cq, Cw, Cd, Cg] using
    capWeighted_fourTerm_l2_bounded hCq hCw hCd hCg hout hq hwsum hD2 hG hpoint

/-- The matched power quotient supplies the four-profile resolver quotient
with a perturbation-only cap-square bound. -/
theorem capWeight_fourProfileResolverGradient_quotient_l2_bounded_of_matched_power
    (p : CMParams) {M Brel DU eta R h : ℝ}
    (hM : 0 ≤ M) (hBrel : 0 ≤ Brel) (hDU : 0 ≤ DU)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hh : h ≠ 0)
    {a2 b2 a1 b1 : ℝ → ℝ}
    (ha2 : IsCUnifBdd a2) (hb2 : IsCUnifBdd b2)
    (ha1 : IsCUnifBdd a1) (hb1 : IsCUnifBdd b1)
    (ha2_mem : ∀ x, a2 x ∈ Set.Icc (0 : ℝ) M)
    (hb2_mem : ∀ x, b2 x ∈ Set.Icc (0 : ℝ) M)
    (ha1_mem : ∀ x, a1 x ∈ Set.Icc (0 : ℝ) M)
    (hb1_mem : ∀ x, b1 x ∈ Set.Icc (0 : ℝ) M)
    (hb2pos : ∀ x, 0 < b2 x) (hb1pos : ∀ x, 0 < b1 x)
    (hbase : ∀ x, |(b2 x - b1 x) / h| ≤ DU)
    (hrelative : ∀ x, ∀ tau ∈ Set.Icc (0 : ℝ) 1,
      |(b2 x - b1 x) / h| ≤
        Brel * (tau * b2 x + (1 - tau) * b1 x))
    (hq : Integrable (fun x => capWeight eta R x *
      |fourProfilePerturbationQuotient h a2 b2 a1 b1 x| ^ 2))
    (hwsum : Integrable (fun x => capWeight eta R x *
      |fourProfilePerturbationSum a2 b2 a1 b1 x| ^ 2)) :
    Integrable (fun x => capWeight eta R x *
        |fourProfileResolverGradient p a2 a1 b2 b1 x / h| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x *
          |fourProfileResolverGradient p a2 a1 b2 b1 x / h| ^ 2) ≤
        (1 / (1 - eta)) ^ 2 *
          ((2 * fourProfilePowerLinearConstant p.γ M) ^ 2 *
              (∫ x : ℝ, capWeight eta R x *
                |fourProfilePerturbationQuotient h a2 b2 a1 b1 x| ^ 2) +
            (2 * fourProfilePowerLowerConstant p.γ M Brel DU) ^ 2 *
              ∫ x : ℝ, capWeight eta R x *
                |fourProfilePerturbationSum a2 b2 a1 b1 x| ^ 2) := by
  let q : ℝ → ℝ := fourProfilePerturbationQuotient h a2 b2 a1 b1
  let w : ℝ → ℝ := fourProfilePerturbationSum a2 b2 a1 b1
  let Ag : ℝ := fourProfilePowerLinearConstant p.γ M
  let Cg : ℝ := fourProfilePowerLowerConstant p.γ M Brel DU
  have hAg : 0 ≤ Ag := by
    dsimp [Ag, fourProfilePowerLinearConstant]
    exact mul_nonneg (le_trans zero_le_one p.hγ) (Real.rpow_nonneg hM _)
  have hCg : 0 ≤ Cg := by
    dsimp [Cg, fourProfilePowerLowerConstant]
    split_ifs
    · exact mul_nonneg
        (mul_nonneg (le_trans zero_le_one p.hγ) hBrel)
        (Real.rpow_nonneg hM _)
    · have hg1 : 0 ≤ p.γ - 1 := by linarith [p.hγ]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (le_trans zero_le_one p.hγ) hg1)
          (Real.rpow_nonneg hM _)) hDU
  have hsourcePoint : ∀ x,
      |fourProfilePowerSource p a2 a1 b2 b1 x / h| ^ 2 ≤
        (2 * Ag) ^ 2 * |q x| ^ 2 + (2 * Cg) ^ 2 * |w x| ^ 2 := by
    intro x
    have hp := paper5_four_profile_power_quotient_bound_of_one_le
      p.hγ hM hBrel hDU (ha2_mem x) (hb2_mem x)
        (ha1_mem x) (hb1_mem x) (hb2pos x) (hb1pos x)
        (hbase x) (hrelative x)
    have hsrcEq : fourProfilePowerSource p a2 a1 b2 b1 x / h =
        ((a2 x ^ p.γ - b2 x ^ p.γ) -
          (a1 x ^ p.γ - b1 x ^ p.γ)) / h := by
      dsimp [fourProfilePowerSource]
      ring
    have hw0 : 0 ≤ w x := by
      dsimp [w, fourProfilePerturbationSum]
      exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hp' : |fourProfilePowerSource p a2 a1 b2 b1 x / h| ≤
        Ag * |q x| + Cg * |w x| := by
      rw [hsrcEq]
      simpa only [Ag, Cg, q, w, abs_of_nonneg hw0,
        fourProfilePowerLinearConstant,
        fourProfilePowerLowerConstant] using hp
    have hrhs0 : 0 ≤ Ag * |q x| + Cg * |w x| :=
      add_nonneg (mul_nonneg hAg (abs_nonneg _))
        (mul_nonneg hCg (abs_nonneg _))
    have hs := (sq_le_sq₀ (abs_nonneg _) hrhs0).2 hp'
    calc
      |fourProfilePowerSource p a2 a1 b2 b1 x / h| ^ 2 ≤
          (Ag * |q x| + Cg * |w x|) ^ 2 := hs
      _ ≤ 2 * ((Ag * |q x|) ^ 2 + (Cg * |w x|) ^ 2) := add_sq_le
      _ ≤ (2 * Ag) ^ 2 * |q x| ^ 2 +
          (2 * Cg) ^ 2 * |w x| ^ 2 := by
        have hq2 : 0 ≤ (Ag * |q x|) ^ 2 := sq_nonneg _
        have hw2 : 0 ≤ (Cg * |w x|) ^ 2 := sq_nonneg _
        rw [mul_pow, mul_pow]
        nlinarith
  simpa only [q, w, Ag, Cg] using
    capWeight_fourProfile_resolverGradient_quotient_l2_bounded
      p heta0 heta1 hh ha2 ha1 hb2 hb1
        ha2_mem ha1_mem hb2_mem hb1_mem hq hwsum hsourcePoint

/-- The genuine shifted four-profile flux quotient is cap-square integrable
from perturbation value and perturbation-quotient data alone.  In particular,
no cap-square integrability of the wave quotient is assumed. -/
theorem capWeighted_shiftedFourProfileFluxQuotient_l2_bounded
    (p : CMParams) {M Brel DU eta R h : ℝ}
    (hM : 0 ≤ M) (hBrel : 0 ≤ Brel) (hDU : 0 ≤ DU)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hh : h ≠ 0)
    {u U : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hU : IsCUnifBdd U)
    (hu_mem : ∀ x, u x ∈ Set.Icc (0 : ℝ) M)
    (hU_mem : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hUpos : ∀ x, 0 < U x)
    (hbase : ∀ x, |(U (x + h) - U x) / h| ≤ DU)
    (hrelative : ∀ x, ∀ tau ∈ Set.Icc (0 : ℝ) 1,
      |(U (x + h) - U x) / h| ≤
        Brel * (tau * U (x + h) + (1 - tau) * U x))
    (hW : Integrable (fun x => capWeight eta R x * |u x - U x| ^ 2))
    (hQ : Integrable (fun x => capWeight eta R x *
      |fourProfilePerturbationQuotient h
        (fun y => u (y + h)) (fun y => U (y + h)) u U x| ^ 2)) :
    Integrable (fun x => (capWeightSqrt eta R x *
        fourProfileFluxQuotient p h
          (fun y => u (y + h)) (fun y => U (y + h)) u U x) ^ 2) ∧
      (∫ x : ℝ, (capWeightSqrt eta R x *
          fourProfileFluxQuotient p h
            (fun y => u (y + h)) (fun y => U (y + h)) u U x) ^ 2) ≤
        4 * ((3 * M ^ p.γ * fourProfilePowerLinearConstant p.m M) ^ 2 *
            (∫ x : ℝ, capWeight eta R x *
              |fourProfilePerturbationQuotient h
                (fun y => u (y + h)) (fun y => U (y + h)) u U x| ^ 2) +
          (3 * M ^ p.γ * fourProfilePowerLowerConstant p.m M Brel DU +
              2 * M ^ p.γ * fourProfilePowerLinearConstant p.m M) ^ 2 *
            (∫ x : ℝ, capWeight eta R x *
              |fourProfilePerturbationSum
                (fun y => u (y + h)) (fun y => U (y + h)) u U x| ^ 2) +
          (fourProfilePowerLinearConstant p.m M * DU) ^ 2 *
            (∫ x : ℝ, capWeight eta R x *
              |deriv (frozenElliptic p (fun y => u (y + h))) x -
                deriv (frozenElliptic p (fun y => U (y + h))) x| ^ 2) +
          (M ^ p.m) ^ 2 *
            ∫ x : ℝ, capWeight eta R x *
              |fourProfileResolverGradient p
                (fun y => u (y + h)) u (fun y => U (y + h)) U x / h| ^ 2) := by
  let a2 : ℝ → ℝ := fun y => u (y + h)
  let b2 : ℝ → ℝ := fun y => U (y + h)
  let a1 : ℝ → ℝ := u
  let b1 : ℝ → ℝ := U
  let q : ℝ → ℝ := fourProfilePerturbationQuotient h a2 b2 a1 b1
  let w : ℝ → ℝ := fourProfilePerturbationSum a2 b2 a1 b1
  let Ag : ℝ := fourProfilePowerLinearConstant p.γ M
  let Cg : ℝ := fourProfilePowerLowerConstant p.γ M Brel DU
  have ha2 : IsCUnifBdd a2 := isCUnifBdd_comp_add_const hu h
  have hb2 : IsCUnifBdd b2 := isCUnifBdd_comp_add_const hU h
  have ha2_mem : ∀ x, a2 x ∈ Set.Icc (0 : ℝ) M := fun x => hu_mem (x + h)
  have hb2_mem : ∀ x, b2 x ∈ Set.Icc (0 : ℝ) M := fun x => hU_mem (x + h)
  have hWshift := capWeight_shift_sq_integrable_and_integral_le
    (eta := eta) (R := R) (d := h) heta0 (hu.1.sub hU.1) hW
  have hwsum := capWeight_shifted_perturbationSum_l2_bounded
    (eta := eta) (R := R) (h := h) heta0 hu.1 hU.1 hW
  have hD2 := capWeight_frozenElliptic_gradient_difference_l2_bounded
    p hM heta0 heta1 hb2 ha2 hb2_mem ha2_mem
      (by simpa only [a2, b2] using hWshift.1)
  have hAg : 0 ≤ Ag := by
    dsimp [Ag, fourProfilePowerLinearConstant]
    exact mul_nonneg (le_trans zero_le_one p.hγ) (Real.rpow_nonneg hM _)
  have hCg : 0 ≤ Cg := by
    dsimp [Cg, fourProfilePowerLowerConstant]
    split_ifs
    · exact mul_nonneg
        (mul_nonneg (le_trans zero_le_one p.hγ) hBrel)
        (Real.rpow_nonneg hM _)
    · have hg1 : 0 ≤ p.γ - 1 := by linarith [p.hγ]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (le_trans zero_le_one p.hγ) hg1)
          (Real.rpow_nonneg hM _)) hDU
  have hsourcePoint : ∀ x,
      |fourProfilePowerSource p a2 a1 b2 b1 x / h| ^ 2 ≤
        (2 * Ag) ^ 2 * |q x| ^ 2 + (2 * Cg) ^ 2 * |w x| ^ 2 := by
    intro x
    have hp := paper5_four_profile_power_quotient_bound_of_one_le
      p.hγ hM hBrel hDU (ha2_mem x) (hb2_mem x)
        (hu_mem x) (hU_mem x) (hUpos (x + h)) (hUpos x)
        (hbase x) (hrelative x)
    have hsrcEq : fourProfilePowerSource p a2 a1 b2 b1 x / h =
        ((a2 x ^ p.γ - b2 x ^ p.γ) -
          (a1 x ^ p.γ - b1 x ^ p.γ)) / h := by
      dsimp [fourProfilePowerSource]
      ring
    have hw0 : 0 ≤ w x := by
      dsimp [w, fourProfilePerturbationSum]
      exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hp' : |fourProfilePowerSource p a2 a1 b2 b1 x / h| ≤
        Ag * |q x| + Cg * |w x| := by
      rw [hsrcEq]
      simpa only [Ag, Cg, q, w, abs_of_nonneg hw0,
        fourProfilePowerLinearConstant,
        fourProfilePowerLowerConstant] using hp
    have hrhs0 : 0 ≤ Ag * |q x| + Cg * |w x| :=
      add_nonneg (mul_nonneg hAg (abs_nonneg _))
        (mul_nonneg hCg (abs_nonneg _))
    have hs := (sq_le_sq₀ (abs_nonneg _) hrhs0).2 hp'
    calc
      |fourProfilePowerSource p a2 a1 b2 b1 x / h| ^ 2 ≤
          (Ag * |q x| + Cg * |w x|) ^ 2 := hs
      _ ≤ 2 * ((Ag * |q x|) ^ 2 + (Cg * |w x|) ^ 2) := add_sq_le
      _ ≤ (2 * Ag) ^ 2 * |q x| ^ 2 +
          (2 * Cg) ^ 2 * |w x| ^ 2 := by
        have hq2 : 0 ≤ (Ag * |q x|) ^ 2 := sq_nonneg _
        have hw2 : 0 ≤ (Cg * |w x|) ^ 2 := sq_nonneg _
        rw [mul_pow, mul_pow]
        nlinarith
  have hG := capWeight_fourProfile_resolverGradient_quotient_l2_bounded
    p heta0 heta1 hh ha2 hu hb2 hU ha2_mem hu_mem hb2_mem hU_mem
      (by simpa only [q] using hQ)
      (by simpa only [w, a2, b2, a1, b1] using hwsum.1)
      hsourcePoint
  have hbaseResolver := frozenElliptic_deriv_shift_quotient_abs_le
    p hM hh hU hU_mem
  have hcore := capWeighted_fourProfileFluxQuotient_l2_bounded
    p hM hBrel hDU hh ha2 hb2 hu hU ha2_mem hb2_mem hu_mem hU_mem
      (fun x => hUpos (x + h)) hUpos
      (by simpa only [b2, b1] using hbase)
      (by simpa only [b2, b1] using hbaseResolver)
      (by simpa only [b2, b1] using hrelative)
      (by simpa only [q] using hQ)
      (by simpa only [w, a2, b2, a1, b1] using hwsum.1)
      hD2.1 hG.1
  simpa only [a2, b2, a1, b1] using hcore

/-- The shifted four-profile algebra is exactly the spatial difference
quotient of the genuine flux perturbation. -/
theorem shiftedFourProfileFluxQuotient_eq_genuineFluxDifferenceDQ
    (p : CMParams) {h : ℝ} {u U : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hU : IsCUnifBdd U)
    (hu0 : ∀ x, 0 ≤ u x) (hU0 : ∀ x, 0 ≤ U x) :
    fourProfileFluxQuotient p h
        (fun y => u (y + h)) (fun y => U (y + h)) u U =
      spatialDifferenceQuotient h
        (fun y => wholeLineChemotaxisFlux p u y -
          wholeLineChemotaxisFlux p U y) := by
  funext x
  rw [fourProfileFluxQuotient, spatialDifferenceQuotient,
    frozenElliptic_deriv_comp_add_const p hu hu0 h x,
    frozenElliptic_deriv_comp_add_const p hU hU0 h x]
  unfold wholeLineChemotaxisFlux
  rfl

/-- Explicit four-component cap-square majorant for the genuine matched
flux quotient.  Each non-quotient component is itself produced from the
value perturbation by the preceding shift/resolver theorems. -/
def shiftedFourProfileFluxBoundRHS (p : CMParams)
    (M Brel DU eta R h : ℝ) (u U : ℝ → ℝ) : ℝ :=
  4 * ((3 * M ^ p.γ * fourProfilePowerLinearConstant p.m M) ^ 2 *
          (∫ x : ℝ, capWeight eta R x *
            |fourProfilePerturbationQuotient h
              (fun y => u (y + h)) (fun y => U (y + h)) u U x| ^ 2) +
        (3 * M ^ p.γ * fourProfilePowerLowerConstant p.m M Brel DU +
            2 * M ^ p.γ * fourProfilePowerLinearConstant p.m M) ^ 2 *
          (∫ x : ℝ, capWeight eta R x *
            |fourProfilePerturbationSum
              (fun y => u (y + h)) (fun y => U (y + h)) u U x| ^ 2) +
        (fourProfilePowerLinearConstant p.m M * DU) ^ 2 *
          (∫ x : ℝ, capWeight eta R x *
            |deriv (frozenElliptic p (fun y => u (y + h))) x -
              deriv (frozenElliptic p (fun y => U (y + h))) x| ^ 2) +
        (M ^ p.m) ^ 2 *
          ∫ x : ℝ, capWeight eta R x *
            |fourProfileResolverGradient p
              (fun y => u (y + h)) u (fun y => U (y + h)) U x / h| ^ 2)

/-- Final genuine-flux form of the matched cap-`L²` quotient estimate.
Its hypotheses contain only value/perturbation quotient integrability; the
wave increment appears exclusively through finite pointwise coefficients. -/
theorem capWeighted_genuineFluxDifference_matchedSpatialDQ_l2_bounded
    (p : CMParams) {M Brel DU eta R h : ℝ}
    (hM : 0 ≤ M) (hBrel : 0 ≤ Brel) (hDU : 0 ≤ DU)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hh : h ≠ 0)
    {u U : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hU : IsCUnifBdd U)
    (hu_mem : ∀ x, u x ∈ Set.Icc (0 : ℝ) M)
    (hU_mem : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hUpos : ∀ x, 0 < U x)
    (hbase : ∀ x, |(U (x + h) - U x) / h| ≤ DU)
    (hrelative : ∀ x, ∀ tau ∈ Set.Icc (0 : ℝ) 1,
      |(U (x + h) - U x) / h| ≤
        Brel * (tau * U (x + h) + (1 - tau) * U x))
    (hW : Integrable (fun x => capWeight eta R x * |u x - U x| ^ 2))
    (hQ : Integrable (fun x => capWeight eta R x *
      |spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2)) :
    Integrable (fun x => (capWeightSqrt eta R x *
        spatialDifferenceQuotient h
          (fun y => wholeLineChemotaxisFlux p u y -
            wholeLineChemotaxisFlux p U y) x) ^ 2) ∧
      (∫ x : ℝ, (capWeightSqrt eta R x *
          spatialDifferenceQuotient h
            (fun y => wholeLineChemotaxisFlux p u y -
              wholeLineChemotaxisFlux p U y) x) ^ 2) ≤
        shiftedFourProfileFluxBoundRHS p M Brel DU eta R h u U := by
  have hQ' : Integrable (fun x => capWeight eta R x *
      |fourProfilePerturbationQuotient h
        (fun y => u (y + h)) (fun y => U (y + h)) u U x| ^ 2) := by
    simpa only [fourProfilePerturbationQuotient,
      spatialDifferenceQuotient] using hQ
  have hcore := capWeighted_shiftedFourProfileFluxQuotient_l2_bounded
    p hM hBrel hDU heta0 heta1 hh hu hU hu_mem hU_mem hUpos
      hbase hrelative hW hQ'
  have heq := shiftedFourProfileFluxQuotient_eq_genuineFluxDifferenceDQ
    (h := h) p hu hU (fun x => (hu_mem x).1) (fun x => (hU_mem x).1)
  rw [heq] at hcore
  simpa only [shiftedFourProfileFluxBoundRHS] using hcore

/-- Coefficient of the perturbation difference-quotient energy in the fully
collapsed matched flux estimate. -/
def matchedFluxQuotientQSquareConstant
    (p : CMParams) (M eta : ℝ) : ℝ :=
  let Am := fourProfilePowerLinearConstant p.m M
  let Ag := fourProfilePowerLinearConstant p.γ M
  let K := 1 / (1 - eta)
  let Cq := 3 * M ^ p.γ * Am
  let Cf := M ^ p.m
  4 * (Cq ^ 2 + Cf ^ 2 * K ^ 2 * (2 * Ag) ^ 2)

/-- Coefficient of the perturbation value energy in the fully collapsed
matched flux estimate. -/
def matchedFluxQuotientWSquareConstant
    (p : CMParams) (M Brel DU eta h : ℝ) : ℝ :=
  let Am := fourProfilePowerLinearConstant p.m M
  let Cm := fourProfilePowerLowerConstant p.m M Brel DU
  let Ag := fourProfilePowerLinearConstant p.γ M
  let Cg := fourProfilePowerLowerConstant p.γ M Brel DU
  let K := 1 / (1 - eta)
  let E := Real.exp (2 * eta * |h|)
  let S := 2 * (1 + E)
  let Cw := 3 * M ^ p.γ * Cm + 2 * M ^ p.γ * Am
  let Cd := Am * DU
  let Cf := M ^ p.m
  4 * (Cw ^ 2 * S + Cd ^ 2 * (K * Ag) ^ 2 * E +
    Cf ^ 2 * K ^ 2 * (2 * Cg) ^ 2 * S)

/-- The explicit four-component majorant collapses to a fixed linear
combination of perturbation quotient and perturbation value energies. -/
theorem shiftedFourProfileFluxBoundRHS_le_perturbation_energies
    (p : CMParams) {M Brel DU eta R h : ℝ}
    (hM : 0 ≤ M) (hBrel : 0 ≤ Brel) (hDU : 0 ≤ DU)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hh : h ≠ 0)
    {u U : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hU : IsCUnifBdd U)
    (hu_mem : ∀ x, u x ∈ Set.Icc (0 : ℝ) M)
    (hU_mem : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hUpos : ∀ x, 0 < U x)
    (hbase : ∀ x, |(U (x + h) - U x) / h| ≤ DU)
    (hrelative : ∀ x, ∀ tau ∈ Set.Icc (0 : ℝ) 1,
      |(U (x + h) - U x) / h| ≤
        Brel * (tau * U (x + h) + (1 - tau) * U x))
    (hW : Integrable (fun x => capWeight eta R x * |u x - U x| ^ 2))
    (hQ : Integrable (fun x => capWeight eta R x *
      |spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2)) :
    shiftedFourProfileFluxBoundRHS p M Brel DU eta R h u U ≤
      matchedFluxQuotientQSquareConstant p M eta *
          (∫ x : ℝ, capWeight eta R x *
            |spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2) +
        matchedFluxQuotientWSquareConstant p M Brel DU eta h *
          ∫ x : ℝ, capWeight eta R x * |u x - U x| ^ 2 := by
  let a2 : ℝ → ℝ := fun y => u (y + h)
  let b2 : ℝ → ℝ := fun y => U (y + h)
  let q : ℝ → ℝ := fourProfilePerturbationQuotient h a2 b2 u U
  let w : ℝ → ℝ := fourProfilePerturbationSum a2 b2 u U
  let IQ : ℝ := ∫ x : ℝ, capWeight eta R x * |q x| ^ 2
  let IW : ℝ := ∫ x : ℝ, capWeight eta R x * |u x - U x| ^ 2
  let Iws : ℝ := ∫ x : ℝ, capWeight eta R x * |w x| ^ 2
  let ID : ℝ := ∫ x : ℝ, capWeight eta R x *
    |deriv (frozenElliptic p a2) x - deriv (frozenElliptic p b2) x| ^ 2
  let IG : ℝ := ∫ x : ℝ, capWeight eta R x *
    |fourProfileResolverGradient p a2 u b2 U x / h| ^ 2
  let Am : ℝ := fourProfilePowerLinearConstant p.m M
  let Cm : ℝ := fourProfilePowerLowerConstant p.m M Brel DU
  let Ag : ℝ := fourProfilePowerLinearConstant p.γ M
  let Cg : ℝ := fourProfilePowerLowerConstant p.γ M Brel DU
  let K : ℝ := 1 / (1 - eta)
  let E : ℝ := Real.exp (2 * eta * |h|)
  let S : ℝ := 2 * (1 + E)
  let Cq : ℝ := 3 * M ^ p.γ * Am
  let Cw : ℝ := 3 * M ^ p.γ * Cm + 2 * M ^ p.γ * Am
  let Cd : ℝ := Am * DU
  let Cf : ℝ := M ^ p.m
  have ha2 : IsCUnifBdd a2 := isCUnifBdd_comp_add_const hu h
  have hb2 : IsCUnifBdd b2 := isCUnifBdd_comp_add_const hU h
  have ha2_mem : ∀ x, a2 x ∈ Set.Icc (0 : ℝ) M := fun x => hu_mem (x + h)
  have hb2_mem : ∀ x, b2 x ∈ Set.Icc (0 : ℝ) M := fun x => hU_mem (x + h)
  have hQ' : Integrable (fun x => capWeight eta R x * |q x| ^ 2) := by
    simpa only [q, a2, b2, fourProfilePerturbationQuotient,
      spatialDifferenceQuotient] using hQ
  have hWshift := capWeight_shift_sq_integrable_and_integral_le
    (eta := eta) (R := R) (d := h) heta0 (hu.1.sub hU.1) hW
  have hws := capWeight_shifted_perturbationSum_l2_bounded
    (eta := eta) (R := R) (h := h) heta0 hu.1 hU.1 hW
  have hD := capWeight_frozenElliptic_gradient_difference_l2_bounded
    p hM heta0 heta1 hb2 ha2 hb2_mem ha2_mem
      (by simpa only [a2, b2] using hWshift.1)
  have hG :=
    capWeight_fourProfileResolverGradient_quotient_l2_bounded_of_matched_power
      p hM hBrel hDU heta0 heta1 hh ha2 hb2 hu hU
        ha2_mem hb2_mem hu_mem hU_mem (fun x => hUpos (x + h)) hUpos
        (by simpa only [b2] using hbase)
        (by simpa only [b2] using hrelative)
        hQ' (by simpa only [w, a2, b2] using hws.1)
  have hws_le : Iws ≤ S * IW := by
    simpa only [Iws, S, IW, w, a2, b2] using hws.2
  have hD_le : ID ≤ (K * Ag) ^ 2 * E * IW := by
    calc
      ID ≤ (K * Ag) ^ 2 *
          (∫ x : ℝ, capWeight eta R x * |u (x + h) - U (x + h)| ^ 2) := by
        simpa only [ID, K, Ag, a2, b2,
          fourProfilePowerLinearConstant] using hD.2
      _ ≤ (K * Ag) ^ 2 * (E * IW) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [E, IW] using hWshift.2) (sq_nonneg _)
      _ = (K * Ag) ^ 2 * E * IW := by ring
  have hG_le : IG ≤ K ^ 2 *
      ((2 * Ag) ^ 2 * IQ + (2 * Cg) ^ 2 * Iws) := by
    simpa only [IG, K, Ag, Cg, IQ, Iws, q, w] using hG.2
  change 4 * (Cq ^ 2 * IQ + Cw ^ 2 * Iws + Cd ^ 2 * ID + Cf ^ 2 * IG) ≤ _
  calc
    4 * (Cq ^ 2 * IQ + Cw ^ 2 * Iws + Cd ^ 2 * ID + Cf ^ 2 * IG) ≤
        4 * (Cq ^ 2 * IQ + Cw ^ 2 * (S * IW) +
          Cd ^ 2 * ((K * Ag) ^ 2 * E * IW) +
          Cf ^ 2 * (K ^ 2 * ((2 * Ag) ^ 2 * IQ + (2 * Cg) ^ 2 * Iws))) := by
      gcongr
    _ ≤ 4 * (Cq ^ 2 * IQ + Cw ^ 2 * (S * IW) +
          Cd ^ 2 * ((K * Ag) ^ 2 * E * IW) +
          Cf ^ 2 * (K ^ 2 * ((2 * Ag) ^ 2 * IQ +
            (2 * Cg) ^ 2 * (S * IW)))) := by
      gcongr
    _ = matchedFluxQuotientQSquareConstant p M eta * IQ +
        matchedFluxQuotientWSquareConstant p M Brel DU eta h * IW := by
      dsimp [matchedFluxQuotientQSquareConstant,
        matchedFluxQuotientWSquareConstant, Am, Cm, Ag, Cg, K, E, S,
        Cq, Cw, Cd, Cf]
      ring
    _ = _ := by rfl

/-- Fully collapsed genuine-flux estimate.  The right side contains exactly
the perturbation quotient energy and perturbation value energy; there is no
standalone wave-quotient energy. -/
theorem capWeighted_genuineFluxDifference_matchedSpatialDQ_l2_bounded_by_perturbation_energies
    (p : CMParams) {M Brel DU eta R h : ℝ}
    (hM : 0 ≤ M) (hBrel : 0 ≤ Brel) (hDU : 0 ≤ DU)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hh : h ≠ 0)
    {u U : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hU : IsCUnifBdd U)
    (hu_mem : ∀ x, u x ∈ Set.Icc (0 : ℝ) M)
    (hU_mem : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hUpos : ∀ x, 0 < U x)
    (hbase : ∀ x, |(U (x + h) - U x) / h| ≤ DU)
    (hrelative : ∀ x, ∀ tau ∈ Set.Icc (0 : ℝ) 1,
      |(U (x + h) - U x) / h| ≤
        Brel * (tau * U (x + h) + (1 - tau) * U x))
    (hW : Integrable (fun x => capWeight eta R x * |u x - U x| ^ 2))
    (hQ : Integrable (fun x => capWeight eta R x *
      |spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2)) :
    Integrable (fun x => (capWeightSqrt eta R x *
        spatialDifferenceQuotient h
          (fun y => wholeLineChemotaxisFlux p u y -
            wholeLineChemotaxisFlux p U y) x) ^ 2) ∧
      (∫ x : ℝ, (capWeightSqrt eta R x *
          spatialDifferenceQuotient h
            (fun y => wholeLineChemotaxisFlux p u y -
              wholeLineChemotaxisFlux p U y) x) ^ 2) ≤
        matchedFluxQuotientQSquareConstant p M eta *
          (∫ x : ℝ, capWeight eta R x *
            |spatialDifferenceQuotient h (fun y => u y - U y) x| ^ 2) +
        matchedFluxQuotientWSquareConstant p M Brel DU eta h *
          ∫ x : ℝ, capWeight eta R x * |u x - U x| ^ 2 := by
  have hraw := capWeighted_genuineFluxDifference_matchedSpatialDQ_l2_bounded
    p hM hBrel hDU heta0 heta1 hh hu hU hu_mem hU_mem hUpos
      hbase hrelative hW hQ
  refine ⟨hraw.1, hraw.2.trans ?_⟩
  exact shiftedFourProfileFluxBoundRHS_le_perturbation_energies
    p hM hBrel hDU heta0 heta1 hh hu hU hu_mem hU_mem hUpos
      hbase hrelative hW hQ

#print axioms fourProfileFluxQuotient_abs_le
#print axioms capWeight_fourProfileResolverGradient_quotient_l2_bounded_of_matched_power
#print axioms capWeighted_genuineFluxDifference_matchedSpatialDQ_l2_bounded_by_perturbation_energies

end ShenWork.Paper1

