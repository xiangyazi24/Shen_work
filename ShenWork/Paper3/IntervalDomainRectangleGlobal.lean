import ShenWork.Paper3.IntervalDomainRectangleLogGap
import ShenWork.Paper3.IntervalDomainTheorem23PositiveEventual
import ShenWork.Paper3.IntervalDomainEntropyStrong2Persistence

/-!
# Rectangle global-attraction route on the unit interval

This file turns the concrete clamped-logarithmic Dini inequality into the
third and fourth strong-logistic branches of eventual global stability.  The
first layer is purely scalar: power gaps across the equilibrium are monotone
in the exponent, and their square is controlled when the target exponent is
at least twice the source exponent.
-/

open Filter Set Topology
open ShenWork.IntervalDomain ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- A pointwise signal floor bounds both sensitivity weights by the common
factor used in the fourth rectangle branch. -/
theorem intervalDomain_sensitivity_weights_le_of_signal_floor
    (p : CM2Params) {floor V : ℝ}
    (hfloor : 0 ≤ floor) (hV : floor ≤ V) :
    (1 + V) ^ (-p.β) ≤ (1 + floor) ^ (-p.β) ∧
      (1 + V) ^ (-p.β - 1) ≤ (1 + floor) ^ (-p.β) := by
  have hbase : 0 < 1 + floor := by linarith
  have hbaseV : 1 + floor ≤ 1 + V := by linarith
  have hβweight : (1 + V) ^ (-p.β) ≤ (1 + floor) ^ (-p.β) :=
    Real.rpow_le_rpow_of_nonpos hbase hbaseV (neg_nonpos.mpr p.hβ)
  have hβoneFloor :
      (1 + floor) ^ (-p.β - 1) ≤ (1 + floor) ^ (-p.β) := by
    exact Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ 1 + floor)
      (by linarith)
  have hβone :
      (1 + V) ^ (-p.β - 1) ≤ (1 + floor) ^ (-p.β - 1) :=
    Real.rpow_le_rpow_of_nonpos hbase hbaseV (by linarith [p.hβ])
  exact ⟨hβweight, hβone.trans hβoneFloor⟩

/-- The fourth threshold says precisely that the sensitivity reduced by the
eventual signal-floor factor lies below the third threshold. -/
theorem chi_mul_vABWeight_lt_chiStrong3_of_lt_chiStrong4
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b) {M0 : ℝ}
    (hχ : p.χ₀ < chiStrong4Formula p M0
      (positiveEquilibrium p ⟨ha, hb⟩).1) :
    p.χ₀ * (1 + vABLowerFormula p) ^ (-p.β) <
      chiStrong3Formula p M0
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  let uStar := (positiveEquilibrium p ⟨ha, hb⟩).1
  let vStar := (positiveEquilibrium p ⟨ha, hb⟩).2
  let base := 1 + vABLowerFormula p
  let factor := base ^ p.β
  have hbase : 0 < base := by
    dsimp [base]
    linarith [vABLowerFormula_pos p ha hb (by rw [hm])]
  have hfactor : 0 < factor := Real.rpow_pos_of_pos hbase _
  have hvStar : vStar = p.ν / p.μ * uStar ^ p.γ := by
    rfl
  have hsecond : p.χ₀ < factor *
      chiStrong3Formula p M0 uStar vStar := by
    have hmRight : chiStrong4Formula p M0 uStar ≤
        (1 + vABLowerFormula p) ^ p.β *
          chiStrong3Formula p M0 uStar
            (p.ν / p.μ * uStar ^ p.γ) := by
      unfold chiStrong4Formula
      exact min_le_right _ _
    have := hχ.trans_le (by simpa [uStar] using hmRight)
    simpa [factor, base, hvStar] using this
  have hdiv : p.χ₀ / factor <
      chiStrong3Formula p M0 uStar vStar := by
    rw [div_lt_iff₀ hfactor]
    simpa [mul_comm] using hsecond
  have hq : base ^ (-p.β) = factor⁻¹ := by
    rw [Real.rpow_neg hbase.le]
  simpa [uStar, vStar, base, factor, hq, div_eq_mul_inv] using hdiv

/-- If two positive numbers straddle one, their real-power gap is monotone in
the nonnegative exponent. -/
theorem rpow_gap_mono_exponent_of_straddles_one
    {L U q r : ℝ}
    (hL : 0 < L) (hL1 : L ≤ 1) (h1U : 1 ≤ U)
    (hqr : q ≤ r) :
    U ^ q - L ^ q ≤ U ^ r - L ^ r := by
  have hU := Real.rpow_le_rpow_of_exponent_le h1U hqr
  have hLo := Real.rpow_le_rpow_of_exponent_ge hL hL1 hqr
  linarith

/-- The square of a power gap across one is bounded by the gap at twice the
exponent. -/
theorem sq_rpow_gap_le_rpow_gap_two_mul_of_straddles_one
    {L U q : ℝ}
    (hL : 0 < L) (hL1 : L ≤ 1) (h1U : 1 ≤ U)
    (hq : 0 ≤ q) :
    (U ^ q - L ^ q) ^ 2 ≤ U ^ (2 * q) - L ^ (2 * q) := by
  have hUq : 1 ≤ U ^ q := Real.one_le_rpow h1U hq
  have hLq0 : 0 ≤ L ^ q := Real.rpow_nonneg hL.le _
  have hLqUq : L ^ q ≤ U ^ q := by
    exact Real.rpow_le_rpow hL.le (hL1.trans h1U) hq
  have hbasic : (U ^ q - L ^ q) ^ 2 ≤ (U ^ q) ^ 2 - (L ^ q) ^ 2 := by
    nlinarith [mul_nonneg hLq0 (sub_nonneg.mpr hLqUq)]
  have hUtwo : U ^ (2 * q) = (U ^ q) ^ 2 := by
    calc
      U ^ (2 * q) = U ^ (q * 2) := by ring_nf
      _ = (U ^ q) ^ (2 : ℝ) :=
        Real.rpow_mul (zero_le_one.trans h1U) q 2
      _ = (U ^ q) ^ 2 := Real.rpow_two _
  have hLtwo : L ^ (2 * q) = (L ^ q) ^ 2 := by
    calc
      L ^ (2 * q) = L ^ (q * 2) := by ring_nf
      _ = (L ^ q) ^ (2 : ℝ) := Real.rpow_mul hL.le q 2
      _ = (L ^ q) ^ 2 := Real.rpow_two _
  rwa [hUtwo, hLtwo]

/-- Combined square-gap comparison at any larger target exponent. -/
theorem sq_rpow_gap_le_rpow_gap_of_two_mul_le
    {L U q r : ℝ}
    (hL : 0 < L) (hL1 : L ≤ 1) (h1U : 1 ≤ U)
    (hq : 0 ≤ q) (hqr : 2 * q ≤ r) :
    (U ^ q - L ^ q) ^ 2 ≤ U ^ r - L ^ r := by
  exact (sq_rpow_gap_le_rpow_gap_two_mul_of_straddles_one
    hL hL1 h1U hq).trans
      (rpow_gap_mono_exponent_of_straddles_one
        hL hL1 h1U hqr)

/-- The explicit third paper threshold is exactly the positivity condition
for the scalar rectangle damping coefficient when `m = 1`. -/
theorem intervalDomain_strong3_decayCoefficient_pos_of_chi
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b) (chi : ℝ) {M0 : ℝ}
    (hχ : chi < chiStrong3Formula p M0
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2) :
    0 < p.a -
      chi * p.ν * (positiveEquilibrium p ⟨ha, hb⟩).1 ^ p.γ *
        (2 + p.β * (positiveEquilibrium p ⟨ha, hb⟩).2 * M0 ^ 2) := by
  let uStar := (positiveEquilibrium p ⟨ha, hb⟩).1
  let vStar := (positiveEquilibrium p ⟨ha, hb⟩).2
  have huStar : 0 < uStar := by
    simpa [uStar] using positiveEquilibrium_fst_pos p ⟨ha, hb⟩
  have hvStar : 0 < vStar := by
    simpa [vStar] using positiveEquilibrium_snd_pos p ⟨ha, hb⟩
  let A : ℝ := p.ν * uStar ^ p.γ
  let D : ℝ := 2 + p.β * vStar * M0 ^ 2
  have hA : 0 < A := by
    exact mul_pos p.hν (Real.rpow_pos_of_pos huStar _)
  have hD : 0 < D := by
    have hnonneg : 0 ≤ p.β * vStar * M0 ^ 2 :=
      mul_nonneg (mul_nonneg p.hβ hvStar.le) (sq_nonneg M0)
    dsimp [D]
    linarith
  have hχ' : chi < p.a / A * (1 / D) := by
    simpa [chiStrong3Formula, hm, uStar, vStar, A, D] using hχ
  have hmul : chi * A * D < p.a := by
    calc
      chi * A * D = chi * (A * D) := by ring
      _ < (p.a / A * (1 / D)) * (A * D) :=
        mul_lt_mul_of_pos_right hχ' (mul_pos hA hD)
      _ = p.a := by
        field_simp [hA.ne', hD.ne']
  dsimp [A, D] at hmul
  nlinarith

/-- The ordinary third-branch coefficient is the specialization to the
physical sensitivity `χ₀`. -/
theorem intervalDomain_strong3_decayCoefficient_pos
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b) {M0 : ℝ}
    (hχ : p.χ₀ < chiStrong3Formula p M0
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2) :
    0 < p.a -
      p.χ₀ * p.ν * (positiveEquilibrium p ⟨ha, hb⟩).1 ^ p.γ *
        (2 + p.β * (positiveEquilibrium p ⟨ha, hb⟩).2 * M0 ^ 2) := by
  exact intervalDomain_strong3_decayCoefficient_pos_of_chi
    p hm ha hb p.χ₀ hχ

/-- Under the third strong-logistic exponent condition, the concrete
rectangle vector field is bounded by a strictly negative multiple of the
normalized `alpha`-power gap. -/
theorem intervalDomain_rectangleLogGapSlopeBound_with_weight_le_strong3
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ : 1 ≤ p.γ)
    (hrel : p.α + 1 ≥ p.m + p.γ +
      (if p.β = 0 then 0 else p.γ))
    (q : ℝ) (hχweightpos : 0 < p.χ₀ * q)
    (hχ : p.χ₀ * q < chiStrong3Formula p
      (unitIntervalNormalizedResolverGradientConstant p)
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2)
    {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    let uStar := (positiveEquilibrium p ⟨ha, hb⟩).1
    let vStar := (positiveEquilibrium p ⟨ha, hb⟩).2
    let M0 := unitIntervalNormalizedResolverGradientConstant p
    let coefficient :=
      p.a - (p.χ₀ * q) * p.ν * uStar ^ p.γ *
        (2 + p.β * vStar * M0 ^ 2)
    intervalDomain_rectangleLogGapSlopeBound_with_weight p q uStar u t ≤
      -coefficient *
        ((intervalDomain_clampedUpper uStar u t / uStar) ^ p.α -
          (intervalDomain_clampedLower uStar u t / uStar) ^ p.α) := by
  let uStar := (positiveEquilibrium p ⟨ha, hb⟩).1
  let vStar := (positiveEquilibrium p ⟨ha, hb⟩).2
  let M0 := unitIntervalNormalizedResolverGradientConstant p
  let C := unitIntervalResolverGradientOscillationConstant p
  let U := intervalDomain_clampedUpper uStar u t
  let L := intervalDomain_clampedLower uStar u t
  let X := U / uStar
  let Y := L / uStar
  let Gγ := X ^ p.γ - Y ^ p.γ
  let Gα := X ^ p.α - Y ^ p.α
  have huStar : 0 < uStar := by
    simpa [uStar] using positiveEquilibrium_fst_pos p ⟨ha, hb⟩
  have hL : 0 < L := by
    exact intervalDomain_clampedLower_pos huStar hsol ht
  have hLu : L ≤ uStar :=
    (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
      uStar u t).1
  have huU : uStar ≤ U :=
    (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
      uStar u t).2
  have hY : 0 < Y := div_pos hL huStar
  have hY1 : Y ≤ 1 := (div_le_one huStar).2 hLu
  have hX1 : 1 ≤ X := (one_le_div huStar).2 huU
  have hX : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hγ_nonneg : 0 ≤ p.γ := hγ.trans' zero_le_one
  have hα_nonneg : 0 ≤ p.α := p.hα.le
  have hGα : 0 ≤ Gα := by
    dsimp [Gα]
    exact sub_nonneg.mpr
      (Real.rpow_le_rpow hY.le (hY1.trans hX1) hα_nonneg)
  have hγα : p.γ ≤ p.α := by
    by_cases hβ0 : p.β = 0
    · simp [hm, hβ0] at hrel
      linarith
    · simp [hm, hβ0] at hrel
      linarith [p.hγ]
  have hGγGα : Gγ ≤ Gα := by
    exact rpow_gap_mono_exponent_of_straddles_one
      hY hY1 hX1 hγα
  have hUfactor : U = uStar * X := by
    dsimp [X]
    field_simp [huStar.ne']
  have hLfactor : L = uStar * Y := by
    dsimp [Y]
    field_simp [huStar.ne']
  have hUγ : U ^ p.γ = uStar ^ p.γ * X ^ p.γ := by
    rw [hUfactor, Real.mul_rpow huStar.le hX.le]
  have hLγ : L ^ p.γ = uStar ^ p.γ * Y ^ p.γ := by
    rw [hLfactor, Real.mul_rpow huStar.le hY.le]
  have hUα : U ^ p.α = uStar ^ p.α * X ^ p.α := by
    rw [hUfactor, Real.mul_rpow huStar.le hX.le]
  have hLα : L ^ p.α = uStar ^ p.α * Y ^ p.α := by
    rw [hLfactor, Real.mul_rpow huStar.le hY.le]
  have hgapγ : U ^ p.γ - L ^ p.γ = uStar ^ p.γ * Gγ := by
    rw [hUγ, hLγ]
    dsimp [Gγ]
    ring
  have hgapα : U ^ p.α - L ^ p.α = uStar ^ p.α * Gα := by
    rw [hUα, hLα]
    dsimp [Gα]
    ring
  have hbuα : p.b * uStar ^ p.α = p.a := by
    rw [show uStar ^ p.α = p.a / p.b by
      simpa [uStar] using positiveEquilibrium_fst_rpow_alpha p ⟨ha, hb⟩]
    field_simp [hb.ne']
  have hM0sq : M0 ^ 2 = p.μ * C ^ 2 := by
    dsimp [M0, C, unitIntervalNormalizedResolverGradientConstant]
    rw [mul_pow, Real.sq_sqrt p.hμ.le]
  have hvrel : p.μ * vStar = p.ν * uStar ^ p.γ := by
    simpa [uStar, vStar] using
      positiveEquilibrium_elliptic_relation p ⟨ha, hb⟩
  have hvM0 : vStar * M0 ^ 2 = p.ν * uStar ^ p.γ * C ^ 2 := by
    calc
      vStar * M0 ^ 2 = vStar * (p.μ * C ^ 2) := by rw [hM0sq]
      _ = (p.μ * vStar) * C ^ 2 := by ring
      _ = (p.ν * uStar ^ p.γ) * C ^ 2 := by rw [hvrel]
      _ = p.ν * uStar ^ p.γ * C ^ 2 := by ring
  let A := p.ν * uStar ^ p.γ
  let D := 2 + p.β * vStar * M0 ^ 2
  have hA : 0 ≤ A := by
    exact (mul_pos p.hν (Real.rpow_pos_of_pos huStar _)).le
  have hlinear :
      2 * p.χ₀ * q * p.ν * (U ^ p.γ - L ^ p.γ) ≤
        (2 * (p.χ₀ * q) * A) * Gα := by
    rw [hgapγ]
    calc
      2 * p.χ₀ * q * p.ν * (uStar ^ p.γ * Gγ) =
          (2 * (p.χ₀ * q) * A) * Gγ := by
            dsimp [A]
            ring
      _ ≤ (2 * (p.χ₀ * q) * A) * Gα :=
        mul_le_mul_of_nonneg_left hGγGα
          (mul_nonneg (mul_nonneg (by norm_num) hχweightpos.le) hA)
  have hsquare :
      p.χ₀ * q * p.β *
          (C * (p.ν * (U ^ p.γ - L ^ p.γ))) ^ 2 ≤
        ((p.χ₀ * q) * p.β * (C * A) ^ 2) * Gα := by
    by_cases hβ0 : p.β = 0
    · simp [hβ0]
    · have htwoγα : 2 * p.γ ≤ p.α := by
        simp [hm, hβ0] at hrel
        linarith
      have hsq : Gγ ^ 2 ≤ Gα := by
        exact sq_rpow_gap_le_rpow_gap_of_two_mul_le
          hY hY1 hX1 hγ_nonneg htwoγα
      have hcoef : 0 ≤ (p.χ₀ * q) * p.β * (C * A) ^ 2 :=
        mul_nonneg (mul_nonneg hχweightpos.le p.hβ) (sq_nonneg _)
      rw [hgapγ]
      calc
        p.χ₀ * q * p.β *
            (C * (p.ν * (uStar ^ p.γ * Gγ))) ^ 2 =
            ((p.χ₀ * q) * p.β * (C * A) ^ 2) * Gγ ^ 2 := by
              dsimp [A]
              ring
        _ ≤ ((p.χ₀ * q) * p.β * (C * A) ^ 2) * Gα :=
          mul_le_mul_of_nonneg_left hsq hcoef
  have hcoefficient : 0 < p.a - (p.χ₀ * q) * A * D := by
    have hc := intervalDomain_strong3_decayCoefficient_pos_of_chi
      p hm ha hb (p.χ₀ * q) hχ
    dsimp [A, D, uStar, vStar, M0]
    nlinarith
  have hlogistic : p.b * (uStar ^ p.α * Gα) = p.a * Gα := by
    rw [← mul_assoc, hbuα]
  have hbetaVM0 : p.β * vStar * M0 ^ 2 = p.β * A * C ^ 2 := by
    calc
      p.β * vStar * M0 ^ 2 = p.β * (vStar * M0 ^ 2) := by ring
      _ = p.β * (p.ν * uStar ^ p.γ * C ^ 2) := by rw [hvM0]
      _ = p.β * A * C ^ 2 := by
        dsimp [A]
        ring
  have hfinal :
      intervalDomain_rectangleLogGapSlopeBound_with_weight p q uStar u t ≤
        -(p.a - (p.χ₀ * q) * A * D) * Gα := by
    rw [intervalDomain_rectangleLogGapSlopeBound_with_weight_eq]
    dsimp only
    change
      2 * p.χ₀ * q * p.ν * (U ^ p.γ - L ^ p.γ) +
          p.χ₀ * q * p.β *
            (C * (p.ν * (U ^ p.γ - L ^ p.γ))) ^ 2 -
          p.b * (U ^ p.α - L ^ p.α) ≤
        -(p.a - (p.χ₀ * q) * A * D) * Gα
    rw [hgapα, hlogistic]
    calc
      2 * p.χ₀ * q * p.ν * (U ^ p.γ - L ^ p.γ) +
            p.χ₀ * q * p.β *
              (C * (p.ν * (U ^ p.γ - L ^ p.γ))) ^ 2 -
            p.a * Gα ≤
          (2 * (p.χ₀ * q) * A) * Gα +
            ((p.χ₀ * q) * p.β * (C * A) ^ 2) * Gα -
            p.a * Gα := by linarith
      _ = ((p.χ₀ * q) * A * D - p.a) * Gα := by
        dsimp [D]
        rw [hbetaVM0]
        ring
      _ = -(p.a - (p.χ₀ * q) * A * D) * Gα := by ring
  dsimp only
  convert hfinal using 1 <;> ring

/-- Under the third strong-logistic exponent condition, the ordinary
rectangle vector field is bounded by a strictly negative multiple of the
normalized `alpha`-power gap. -/
theorem intervalDomain_rectangleLogGapSlopeBound_le_strong3
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ : 1 ≤ p.γ)
    (hrel : p.α + 1 ≥ p.m + p.γ +
      (if p.β = 0 then 0 else p.γ))
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong3Formula p
      (unitIntervalNormalizedResolverGradientConstant p)
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2)
    {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    let uStar := (positiveEquilibrium p ⟨ha, hb⟩).1
    let vStar := (positiveEquilibrium p ⟨ha, hb⟩).2
    let M0 := unitIntervalNormalizedResolverGradientConstant p
    let coefficient :=
      p.a - p.χ₀ * p.ν * uStar ^ p.γ *
        (2 + p.β * vStar * M0 ^ 2)
    intervalDomain_rectangleLogGapSlopeBound p uStar u t ≤
      -coefficient *
        ((intervalDomain_clampedUpper uStar u t / uStar) ^ p.α -
          (intervalDomain_clampedLower uStar u t / uStar) ^ p.α) := by
  have h := intervalDomain_rectangleLogGapSlopeBound_with_weight_le_strong3
    p hm ha hb hγ hrel 1 (by simpa using hχpos) (by simpa using hχ)
      hsol ht
  simpa [intervalDomain_rectangleLogGapSlopeBound_with_weight,
    intervalDomain_rectangleUpperLogSlopeBound_with_weight,
    intervalDomain_rectangleLowerLogSlopeBound_with_weight,
    intervalDomain_rectangleLogGapSlopeBound,
    intervalDomain_rectangleUpperLogSlopeBound,
    intervalDomain_rectangleLowerLogSlopeBound] using h

/-- A positive logarithmic gap between two numbers straddling one forces a
quantitative positive power gap. -/
theorem one_sub_exp_neg_mul_le_rpow_gap_of_straddles_one
    {L U alpha epsilon : ℝ}
    (hL : 0 < L) (hL1 : L ≤ 1) (h1U : 1 ≤ U)
    (halpha : 0 < alpha)
    (hlog : epsilon ≤ Real.log U - Real.log L) :
    1 - Real.exp (-alpha * epsilon) ≤ U ^ alpha - L ^ alpha := by
  let q : ℝ := L / U
  have hU : 0 < U := lt_of_lt_of_le zero_lt_one h1U
  have hq : 0 < q := div_pos hL hU
  have hq1 : q ≤ 1 := (div_le_one hU).2 (hL1.trans h1U)
  have hlogq : Real.log q ≤ -epsilon := by
    rw [Real.log_div hL.ne' hU.ne']
    linarith
  have hqpow : q ^ alpha ≤ Real.exp (-alpha * epsilon) := by
    rw [Real.rpow_def_of_pos hq]
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hlogq halpha.le
    nlinarith
  have hqpow1 : q ^ alpha ≤ 1 :=
    Real.rpow_le_one hq.le hq1 halpha.le
  have hUpow1 : 1 ≤ U ^ alpha :=
    Real.one_le_rpow h1U halpha.le
  have hLfactor : L = U * q := by
    dsimp [q]
    field_simp [hU.ne']
  have hLpow : L ^ alpha = U ^ alpha * q ^ alpha := by
    rw [hLfactor, Real.mul_rpow hU.le hq.le]
  calc
    1 - Real.exp (-alpha * epsilon) ≤ 1 - q ^ alpha := by linarith
    _ ≤ U ^ alpha * (1 - q ^ alpha) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hUpow1)
        (sub_nonneg.mpr hqpow1)]
    _ = U ^ alpha - L ^ alpha := by rw [hLpow]; ring

/-- A uniform negative upper bound in the one-sided Dini condition integrates
to a linear decrease on a compact window. -/
theorem le_sub_mul_of_dini_upper_bound
    {M g : ℝ → ℝ} {a b q t₁ t₂ : ℝ}
    (hcont : ContinuousOn M (Icc a b))
    (hDini : ∀ x ∈ Ico a b, ∀ r : ℝ, g x < r →
      ∃ᶠ z in nhdsWithin x (Ioi x),
        (z - x)⁻¹ * (M z - M x) < r)
    (hg : ∀ x ∈ Ico a b, g x ≤ -q)
    (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b)
    (ht : t₁ ≤ t₂) :
    M t₂ ≤ M t₁ - q * (t₂ - t₁) := by
  have hsub : Icc t₁ t₂ ⊆ Icc a b := by
    intro s hs
    exact ⟨ht₁.1.trans hs.1, hs.2.trans ht₂.2⟩
  have hfreq : ∀ x ∈ Ico t₁ t₂, ∀ r : ℝ, -q < r →
      ∃ᶠ z in nhdsWithin x (Ioi x),
        (z - x)⁻¹ * (M z - M x) < r := by
    intro x hx r hr
    have hx' : x ∈ Ico a b :=
      ⟨ht₁.1.trans hx.1, hx.2.trans_le ht₂.2⟩
    exact hDini x hx' r ((hg x hx').trans_lt hr)
  have hbound : ∀ x ∈ Ico t₁ t₂,
      (-q : ℝ) ≤ 0 * M x + -q := by
    intro x hx
    simp
  have hgron := le_gronwallBound_of_liminf_deriv_right_le
    (f := M) (f' := fun _ => -q)
    (δ := M t₁) (K := 0) (ε := -q) (a := t₁) (b := t₂)
    (hcont.mono hsub) hfreq (le_refl _) hbound
  have hlast := hgron t₂ (Set.right_mem_Icc.mpr ht)
  rw [gronwallBound_K0] at hlast
  dsimp at hlast
  linarith

/-- The rectangle logarithmic gap is nonincreasing on any positive-time tail
where both sensitivity weights are controlled by `q` and the corresponding
effective sensitivity satisfies the third threshold. -/
theorem intervalDomain_rectangleLogGap_antitone_of_weighted_strong3
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ : 1 ≤ p.γ)
    (hrel : p.α + 1 ≥ p.m + p.γ +
      (if p.β = 0 then 0 else p.γ))
    (start q : ℝ) (hstart : 0 < start) (hq : 0 ≤ q)
    (hχnonneg : 0 ≤ p.χ₀)
    (hχweightpos : 0 < p.χ₀ * q)
    (hχ : p.χ₀ * q < chiStrong3Formula p
      (unitIntervalNormalizedResolverGradientConstant p)
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hweights : ∀ t, start ≤ t → ∀ y ∈ Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (v t) y) ^ (-p.β) ≤ q ∧
        (1 + intervalDomainLift (v t) y) ^ (-p.β - 1) ≤ q) :
    AntitoneOn
      (intervalDomain_rectangleLogGap
        (positiveEquilibrium p ⟨ha, hb⟩).1 u)
      (Ici start) := by
  let uStar := (positiveEquilibrium p ⟨ha, hb⟩).1
  let vStar := (positiveEquilibrium p ⟨ha, hb⟩).2
  let M0 := unitIntervalNormalizedResolverGradientConstant p
  intro t₁ ht₁ t₂ ht₂ ht
  change start ≤ t₁ at ht₁
  change start ≤ t₂ at ht₂
  let T := t₂ + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have hab : Icc t₁ t₂ ⊆ Ioo (0 : ℝ) T := by
    intro s hs
    rcases hs with ⟨hs₁, hs₂⟩
    exact ⟨lt_of_lt_of_le hstart (ht₁.trans hs₁), by
      dsimp [T]
      exact lt_of_le_of_lt hs₂ (lt_add_one t₂)⟩
  have hsol := huv.classical T hT
  have huStar : 0 < uStar := by
    simpa [uStar] using positiveEquilibrium_fst_pos p ⟨ha, hb⟩
  have hcont := intervalDomain_rectangleLogGap_continuousOn
    huStar hsol hab
  have hdiniRaw := intervalDomain_rectangleLogGap_dini_with_weight
    hq
    (fun s hs y hy => (hweights s (ht₁.trans hs.1) y hy).1)
    (fun s hs y hy => (hweights s (ht₁.trans hs.1) y hy).2)
    hχnonneg
    huStar (positiveEquilibrium_logistic_zero p ⟨ha, hb⟩) hsol hab
  have hslope : ∀ x ∈ Ico t₁ t₂,
      intervalDomain_rectangleLogGapSlopeBound_with_weight
        p q uStar u x ≤ 0 := by
    intro x hx
    have hxpos : x ∈ Ioo (0 : ℝ) T := hab (Ico_subset_Icc_self hx)
    have hs := intervalDomain_rectangleLogGapSlopeBound_with_weight_le_strong3
      p hm ha hb hγ hrel q hχweightpos hχ hsol hxpos
    let U := intervalDomain_clampedUpper uStar u x
    let L := intervalDomain_clampedLower uStar u x
    have hL : 0 < L := intervalDomain_clampedLower_pos huStar hsol hxpos
    have hLu : L ≤ uStar :=
      (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
        uStar u x).1
    have huU : uStar ≤ U :=
      (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
        uStar u x).2
    have hgap : 0 ≤ (U / uStar) ^ p.α - (L / uStar) ^ p.α := by
      exact sub_nonneg.mpr (Real.rpow_le_rpow
        (div_pos hL huStar).le
        (div_le_div_of_nonneg_right (hLu.trans huU) huStar.le)
        p.hα.le)
    have hc : 0 < p.a - (p.χ₀ * q) * p.ν * uStar ^ p.γ *
        (2 + p.β * vStar * M0 ^ 2) := by
      simpa [uStar, vStar, M0] using
        intervalDomain_strong3_decayCoefficient_pos_of_chi
          p hm ha hb (p.χ₀ * q) hχ
    have hnonpos : -(p.a - (p.χ₀ * q) * p.ν * uStar ^ p.γ *
        (2 + p.β * vStar * M0 ^ 2)) *
          ((U / uStar) ^ p.α - (L / uStar) ^ p.α) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hgap
    have hs' : intervalDomain_rectangleLogGapSlopeBound_with_weight
          p q uStar u x ≤
        -(p.a - (p.χ₀ * q) * p.ν * uStar ^ p.γ *
          (2 + p.β * vStar * M0 ^ 2)) *
            ((U / uStar) ^ p.α - (L / uStar) ^ p.α) := by
      simpa [uStar, vStar, M0, U, L] using hs
    exact hs'.trans hnonpos
  have hdini : ∀ x ∈ Ico t₁ t₂, ∀ r : ℝ, 0 < r →
      ∃ᶠ z in nhdsWithin x (Ioi x),
        (z - x)⁻¹ *
          (intervalDomain_rectangleLogGap uStar u z -
            intervalDomain_rectangleLogGap uStar u x) < r := by
    intro x hx r hr
    exact hdiniRaw x hx r ((hslope x hx).trans_lt hr)
  exact ShenWork.Paper2.Lemma31Closure.mono_of_dini_window hcont hdini
    (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht) ht

/-- The ordinary strong-three logarithmic gap is nonincreasing after time
one. -/
theorem intervalDomain_rectangleLogGap_antitone_strong3
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ : 1 ≤ p.γ)
    (hrel : p.α + 1 ≥ p.m + p.γ +
      (if p.β = 0 then 0 else p.γ))
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong3Formula p
      (unitIntervalNormalizedResolverGradientConstant p)
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    AntitoneOn
      (intervalDomain_rectangleLogGap
        (positiveEquilibrium p ⟨ha, hb⟩).1 u)
      (Ici (1 : ℝ)) := by
  have hweights : ∀ t : ℝ, 1 ≤ t → ∀ y ∈ Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (v t) y) ^ (-p.β) ≤ 1 ∧
        (1 + intervalDomainLift (v t) y) ^ (-p.β - 1) ≤ 1 := by
    intro t ht y hy
    let T := t + 1
    have hT : 0 < T := by dsimp [T]; linarith
    have hv : 0 ≤ intervalDomainLift (v t) y := by
      rw [intervalDomainLift, dif_pos hy]
      exact (huv.classical T hT).v_nonneg
        (lt_of_lt_of_le zero_lt_one ht) (by dsimp [T]; linarith)
    have hbase : 1 ≤ 1 + intervalDomainLift (v t) y := by linarith
    exact ⟨
      Real.rpow_le_one_of_one_le_of_nonpos hbase (neg_nonpos.mpr p.hβ),
      Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith [p.hβ])⟩
  exact intervalDomain_rectangleLogGap_antitone_of_weighted_strong3
    p hm ha hb hγ hrel 1 1 zero_lt_one zero_le_one hχpos.le
      (by simpa using hχpos) (by simpa using hχ) huv hweights

/-- A weighted strong-three tail drives the clamped logarithmic gap to zero. -/
theorem intervalDomain_rectangleLogGap_tendsto_zero_of_weighted_strong3
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ : 1 ≤ p.γ)
    (hrel : p.α + 1 ≥ p.m + p.γ +
      (if p.β = 0 then 0 else p.γ))
    (start weight : ℝ) (hstart : 0 < start) (hweight_nonneg : 0 ≤ weight)
    (hχnonneg : 0 ≤ p.χ₀)
    (hχweightpos : 0 < p.χ₀ * weight)
    (hχ : p.χ₀ * weight < chiStrong3Formula p
      (unitIntervalNormalizedResolverGradientConstant p)
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hweights : ∀ t, start ≤ t → ∀ y ∈ Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (v t) y) ^ (-p.β) ≤ weight ∧
        (1 + intervalDomainLift (v t) y) ^ (-p.β - 1) ≤ weight) :
    Tendsto
      (intervalDomain_rectangleLogGap
        (positiveEquilibrium p ⟨ha, hb⟩).1 u)
      atTop (nhds 0) := by
  let uStar := (positiveEquilibrium p ⟨ha, hb⟩).1
  let vStar := (positiveEquilibrium p ⟨ha, hb⟩).2
  let M0 := unitIntervalNormalizedResolverGradientConstant p
  let G := intervalDomain_rectangleLogGap uStar u
  let c := p.a - (p.χ₀ * weight) * p.ν * uStar ^ p.γ *
    (2 + p.β * vStar * M0 ^ 2)
  have huStar : 0 < uStar := by
    simpa [uStar] using positiveEquilibrium_fst_pos p ⟨ha, hb⟩
  have hc : 0 < c := by
    simpa [c, uStar, vStar, M0] using
      intervalDomain_strong3_decayCoefficient_pos_of_chi
        p hm ha hb (p.χ₀ * weight) hχ
  have hnonneg : ∀ t : ℝ, start ≤ t → 0 ≤ G t := by
    intro t ht
    let T := t + 1
    have hT : 0 < T := by dsimp [T]; linarith
    have htT : t ∈ Ioo (0 : ℝ) T := by
      exact ⟨lt_of_lt_of_le hstart ht, by
        dsimp [T]
        exact lt_add_one t⟩
    exact intervalDomain_rectangleLogGap_nonneg huStar
      (huv.classical T hT) htT
  have hmono : AntitoneOn G (Ici start) := by
    simpa [G, uStar] using
      intervalDomain_rectangleLogGap_antitone_of_weighted_strong3
        p hm ha hb hγ hrel start weight hstart hweight_nonneg hχnonneg
          hχweightpos hχ huv hweights
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hexists : ∃ tau : ℝ, start ≤ tau ∧ G tau < epsilon := by
    by_contra hnone
    push Not at hnone
    let decay : ℝ := c * (1 - Real.exp (-p.α * epsilon))
    have hexp : Real.exp (-p.α * epsilon) < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith [mul_pos p.hα hepsilon]
    have hdecayPos : 0 < decay := by
      exact mul_pos hc (sub_pos.mpr hexp)
    let B : ℝ := start + (G start + 1) / decay
    have hGstart : 0 ≤ G start := hnonneg start le_rfl
    have hB : start ≤ B := by
      dsimp [B]
      exact le_add_of_nonneg_right
        (div_nonneg (by linarith) hdecayPos.le)
    let T := B + 1
    have hT : 0 < T := by dsimp [T]; linarith
    have hab : Icc start B ⊆ Ioo (0 : ℝ) T := by
      intro s hs
      rcases hs with ⟨hs₁, hs₂⟩
      exact ⟨lt_of_lt_of_le hstart hs₁, by
        dsimp [T]
        exact lt_of_le_of_lt hs₂ (lt_add_one B)⟩
    have hsol := huv.classical T hT
    have hcont : ContinuousOn G (Icc start B) := by
      simpa [G] using intervalDomain_rectangleLogGap_continuousOn
        huStar hsol hab
    have hdini : ∀ x ∈ Ico start B, ∀ r : ℝ,
        intervalDomain_rectangleLogGapSlopeBound_with_weight
            p weight uStar u x < r →
          ∃ᶠ z in nhdsWithin x (Ioi x),
            (z - x)⁻¹ * (G z - G x) < r := by
      simpa [G] using intervalDomain_rectangleLogGap_dini_with_weight
        hweight_nonneg
        (fun s hs y hy => (hweights s (hs.1) y hy).1)
        (fun s hs y hy => (hweights s (hs.1) y hy).2)
        hχnonneg huStar
          (positiveEquilibrium_logistic_zero p ⟨ha, hb⟩) hsol hab
    have hslope : ∀ x ∈ Ico start B,
        intervalDomain_rectangleLogGapSlopeBound_with_weight
          p weight uStar u x ≤ -decay := by
      intro x hx
      have hxpos : x ∈ Ioo (0 : ℝ) T := hab (Ico_subset_Icc_self hx)
      have hs := intervalDomain_rectangleLogGapSlopeBound_with_weight_le_strong3
        p hm ha hb hγ hrel weight hχweightpos hχ hsol hxpos
      let U := intervalDomain_clampedUpper uStar u x
      let L := intervalDomain_clampedLower uStar u x
      let X := U / uStar
      let Y := L / uStar
      let Gα := X ^ p.α - Y ^ p.α
      have hL : 0 < L := intervalDomain_clampedLower_pos huStar hsol hxpos
      have hLu : L ≤ uStar :=
        (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
          uStar u x).1
      have huU : uStar ≤ U :=
        (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
          uStar u x).2
      have hX : 1 ≤ X := (one_le_div huStar).2 huU
      have hY : 0 < Y := div_pos hL huStar
      have hY1 : Y ≤ 1 := (div_le_one huStar).2 hLu
      have hUpos : 0 < U := huStar.trans_le huU
      have hlogNorm : G x = Real.log X - Real.log Y := by
        dsimp [G, intervalDomain_rectangleLogGap, X, Y, U, L]
        rw [Real.log_div hUpos.ne' huStar.ne',
          Real.log_div hL.ne' huStar.ne']
        ring
      have hgapLower : 1 - Real.exp (-p.α * epsilon) ≤ Gα := by
        exact one_sub_exp_neg_mul_le_rpow_gap_of_straddles_one
          hY hY1 hX p.hα (by rw [← hlogNorm]; exact hnone x hx.1)
      have hs' : intervalDomain_rectangleLogGapSlopeBound_with_weight
          p weight uStar u x ≤
          -c * Gα := by
        simpa [uStar, vStar, M0, c, U, L, X, Y, Gα] using hs
      calc
        intervalDomain_rectangleLogGapSlopeBound_with_weight
            p weight uStar u x ≤
            -c * Gα := hs'
        _ ≤ -c * (1 - Real.exp (-p.α * epsilon)) :=
          mul_le_mul_of_nonpos_left hgapLower (neg_nonpos.mpr hc.le)
        _ = -decay := by dsimp [decay]; ring
    have hlinearDecay := le_sub_mul_of_dini_upper_bound
      hcont hdini hslope (t₁ := start) (t₂ := B)
      (Set.left_mem_Icc.mpr hB) (Set.right_mem_Icc.mpr hB) hB
    have hneg : G B ≤ -1 := by
      calc
        G B ≤ G start - decay * (B - start) := hlinearDecay
        _ = -1 := by
          dsimp [B]
          field_simp [hdecayPos.ne']
          ring
    have hGB := hnonneg B hB
    linarith
  obtain ⟨tau, htau, hclose⟩ := hexists
  refine ⟨tau, ?_⟩
  intro t httau
  have ht : start ≤ t := htau.trans httau
  have hGt : G t ≤ G tau :=
    hmono htau ht httau
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg t ht)]
  exact hGt.trans_lt hclose

/-- The ordinary strong-three clamped logarithmic gap converges to zero for
every positive global bounded orbit. -/
theorem intervalDomain_rectangleLogGap_tendsto_zero_strong3
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ : 1 ≤ p.γ)
    (hrel : p.α + 1 ≥ p.m + p.γ +
      (if p.β = 0 then 0 else p.γ))
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong3Formula p
      (unitIntervalNormalizedResolverGradientConstant p)
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    Tendsto
      (intervalDomain_rectangleLogGap
        (positiveEquilibrium p ⟨ha, hb⟩).1 u)
      atTop (nhds 0) := by
  have hweights : ∀ t : ℝ, 1 ≤ t → ∀ y ∈ Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (v t) y) ^ (-p.β) ≤ 1 ∧
        (1 + intervalDomainLift (v t) y) ^ (-p.β - 1) ≤ 1 := by
    intro t ht y hy
    let T := t + 1
    have hT : 0 < T := by dsimp [T]; linarith
    have hv : 0 ≤ intervalDomainLift (v t) y := by
      rw [intervalDomainLift, dif_pos hy]
      exact (huv.classical T hT).v_nonneg
        (lt_of_lt_of_le zero_lt_one ht) (by dsimp [T]; linarith)
    have hbase : 1 ≤ 1 + intervalDomainLift (v t) y := by linarith
    exact ⟨
      Real.rpow_le_one_of_one_le_of_nonpos hbase (neg_nonpos.mpr p.hβ),
      Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith [p.hβ])⟩
  exact intervalDomain_rectangleLogGap_tendsto_zero_of_weighted_strong3
    p hm ha hb hγ hrel 1 1 zero_lt_one zero_le_one hχpos.le
      (by simpa using hχpos) (by simpa using hχ) huv hweights

/-- In the fourth branch, the eventual `vABLower` signal floor reduces the
physical sensitivity to the weighted third-branch regime. -/
theorem intervalDomain_rectangleLogGap_tendsto_zero_strong4
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hβ : 1 ≤ p.β) (hγ : 1 ≤ p.γ)
    (hrel : p.α + 1 ≥ p.m + 2 * p.γ)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong4Formula p
      (unitIntervalNormalizedResolverGradientConstant p)
      (positiveEquilibrium p ⟨ha, hb⟩).1)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    Tendsto
      (intervalDomain_rectangleLogGap
        (positiveEquilibrium p ⟨ha, hb⟩).1 u)
      atTop (nhds 0) := by
  let floor := vABLowerFormula p
  let weight := (1 + floor) ^ (-p.β)
  have hfloor : 0 < floor := by
    simpa [floor] using vABLowerFormula_pos p ha hb (by rw [hm])
  have hweight : 0 < weight := by
    exact Real.rpow_pos_of_pos (by dsimp [floor]; linarith) _
  have hχbar : p.χ₀ < chiBarFormula p :=
    chi_lt_chiBarFormula_of_lt_chiStrong4Formula p hχ
  have hevFloor := intervalDomain_eventually_vABLower_of_chi_lt_chiBar
    p hm ha hb hβ hχpos hχbar huv
  rcases eventually_atTop.1 hevFloor with ⟨Tv, hTv⟩
  let start := max Tv 1
  have hstart : 0 < start :=
    lt_of_lt_of_le zero_lt_one (le_max_right Tv 1)
  have hTvStart : Tv ≤ start := le_max_left Tv 1
  have hβpos : 0 < p.β := lt_of_lt_of_le zero_lt_one hβ
  have hβne : p.β ≠ 0 := ne_of_gt hβpos
  have hrel3 : p.α + 1 ≥ p.m + p.γ +
      (if p.β = 0 then 0 else p.γ) := by
    simp [hβne]
    linarith
  have hχweighted : p.χ₀ * weight < chiStrong3Formula p
      (unitIntervalNormalizedResolverGradientConstant p)
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
    simpa [weight, floor] using
      chi_mul_vABWeight_lt_chiStrong3_of_lt_chiStrong4
        p hm ha hb hχ
  have hweights : ∀ t, start ≤ t → ∀ y ∈ Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (v t) y) ^ (-p.β) ≤ weight ∧
        (1 + intervalDomainLift (v t) y) ^ (-p.β - 1) ≤ weight := by
    intro t ht y hy
    have hpoint : floor ≤ intervalDomainLift (v t) y := by
      have hv := hTv t (hTvStart.trans ht) (⟨y, hy⟩ : intervalDomainPoint)
      simpa [floor, intervalDomainLift, hy] using hv
    simpa [weight] using intervalDomain_sensitivity_weights_le_of_signal_floor
      p hfloor.le hpoint
  exact intervalDomain_rectangleLogGap_tendsto_zero_of_weighted_strong3
    p hm ha hb hγ hrel3 start weight hstart hweight.le hχpos.le
      (mul_pos hχpos hweight) hχweighted huv hweights

/-- The physical sup distance to the equilibrium is squeezed by an explicit
continuous function of the clamped logarithmic gap. -/
theorem intervalDomain_supNorm_sub_equilibrium_le_logGapEnvelope
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huStar : 0 < uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    0 ≤ intervalDomain.supNorm (fun x => u t x - uStar) ∧
      intervalDomain.supNorm (fun x => u t x - uStar) ≤
        uStar *
          (Real.exp (intervalDomain_rectangleLogGap uStar u t) -
            Real.exp (-intervalDomain_rectangleLogGap uStar u t)) := by
  let U := intervalDomain_clampedUpper uStar u t
  let L := intervalDomain_clampedLower uStar u t
  let G := intervalDomain_rectangleLogGap uStar u t
  have hL : 0 < L := intervalDomain_clampedLower_pos huStar hsol ht
  have hLu : L ≤ uStar :=
    (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
      uStar u t).1
  have huU : uStar ≤ U :=
    (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
      uStar u t).2
  have hU : 0 < U := huStar.trans_le huU
  have hpoint : ∀ x : intervalDomainPoint, |u t x - uStar| ≤ U - L := by
    intro x
    have hx := intervalDomain_equilibriumChoiceValue_mem_clamped
      (uStar := uStar) hsol ht (Sum.inr x)
    simp only [intervalDomain_equilibriumChoiceValue_inr] at hx
    rw [abs_le]
    constructor <;> linarith
  have hsup : intervalDomain.supNorm (fun x => u t x - uStar) ≤ U - L :=
    intervalDomain_supNorm_le_of_pointwise_abs_le hpoint
  have hsup0 : 0 ≤ intervalDomain.supNorm (fun x => u t x - uStar) :=
    intervalDomain_supNorm_nonneg_of_pointwise_abs_bounded hpoint
  have hG : G = Real.log U - Real.log L := by
    rfl
  have hexpG : Real.exp G = U / L := by
    rw [hG, Real.exp_sub, Real.exp_log hU, Real.exp_log hL]
  have hexpNegG : Real.exp (-G) = L / U := by
    rw [hG]
    have hneg : -(Real.log U - Real.log L) =
        Real.log L - Real.log U := by ring
    rw [hneg, Real.exp_sub, Real.exp_log hL, Real.exp_log hU]
  have hUeq : U = L * Real.exp G := by
    rw [hexpG]
    field_simp [hL.ne']
  have hLeq : L = U * Real.exp (-G) := by
    rw [hexpNegG]
    field_simp [hU.ne']
  have hUupper : U ≤ uStar * Real.exp G := by
    rw [hUeq]
    exact mul_le_mul_of_nonneg_right hLu (Real.exp_pos _).le
  have hLlower : uStar * Real.exp (-G) ≤ L := by
    rw [hLeq]
    exact mul_le_mul_of_nonneg_right huU (Real.exp_pos _).le
  have henvelope : U - L ≤
      uStar * (Real.exp G - Real.exp (-G)) := by
    nlinarith
  exact ⟨hsup0, hsup.trans henvelope⟩

/-- Vanishing of the clamped logarithmic gap implies uniform convergence of
the population component, with no compactness package. -/
theorem intervalDomain_uniformConvergesInSup_of_rectangleLogGap
    (p : CM2Params) {uStar : ℝ} (huStar : 0 < uStar)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hgap : Tendsto (intervalDomain_rectangleLogGap uStar u)
      atTop (nhds 0)) :
    UniformConvergesInSup intervalDomain u uStar := by
  let G := intervalDomain_rectangleLogGap uStar u
  let B : ℝ → ℝ := fun t =>
    uStar * (Real.exp (G t) - Real.exp (-G t))
  have hexpG : Tendsto (fun t => Real.exp (G t)) atTop (nhds 1) := by
    have h := Real.continuous_exp.continuousAt.tendsto.comp hgap
    simpa [G] using h
  have hexpNegG : Tendsto (fun t => Real.exp (-G t)) atTop (nhds 1) := by
    have hneg : Tendsto (fun t => -G t) atTop (nhds 0) := by
      simpa [G] using hgap.neg
    have h := Real.continuous_exp.continuousAt.tendsto.comp hneg
    simpa using h
  have hB : Tendsto B atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℝ => uStar) atTop (nhds uStar) :=
      tendsto_const_nhds
    have h := hconst.mul (hexpG.sub hexpNegG)
    simpa [B] using h
  have hbounds : ∀ᶠ t : ℝ in atTop,
      0 ≤ intervalDomain.supNorm (fun x => u t x - uStar) ∧
        intervalDomain.supNorm (fun x => u t x - uStar) ≤ B t := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    let T := t + 1
    have hT : 0 < T := by dsimp [T]; linarith
    have htT : t ∈ Ioo (0 : ℝ) T := by
      exact ⟨lt_of_lt_of_le zero_lt_one ht, by
        dsimp [T]
        exact lt_add_one t⟩
    simpa [B, G] using
      intervalDomain_supNorm_sub_equilibrium_le_logGapEnvelope
        huStar (huv.classical T hT) htT
  unfold UniformConvergesInSup
  exact squeeze_zero' (hbounds.mono fun _ h => h.1)
    (hbounds.mono fun _ h => h.2) hB

/-- Concrete qualitative global-attractor producer for the third formula
branch.  Nonpositive sensitivity reuses Theorem 2.3; positive sensitivity is
the rectangle argument proved above. -/
theorem intervalDomain_strong3_globallyAsymptoticallyStableNonminimal
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ : 1 ≤ p.γ)
    (hrel : p.α + 1 ≥ p.m + p.γ +
      (if p.β = 0 then 0 else p.γ))
    (hχ : p.χ₀ < chiStrong3Formula p
      (unitIntervalNormalizedResolverGradientConstant p)
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2) :
    GloballyAsymptoticallyStableNonminimal intervalDomain p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  by_cases hχnonpos : p.χ₀ ≤ 0
  · exact intervalDomain_chiNonpos_globallyAsymptoticallyStableNonminimal
      p hm hχnonpos ha hb
  · have hχpos : 0 < p.χ₀ := lt_of_not_ge hχnonpos
    intro u v huv
    exact intervalDomain_uniformConvergesInSup_of_rectangleLogGap
      p (positiveEquilibrium_fst_pos p ⟨ha, hb⟩) huv
      (intervalDomain_rectangleLogGap_tendsto_zero_strong3
        p hm ha hb hγ hrel hχpos hχ huv)

/-- Unconditional third formula branch of faithful eventual Theorem 2.4 on
the implemented `m = 1` unit-interval equation. -/
theorem
    intervalDomain_eventuallyGloballyExponentiallyStableNonminimal_strong3
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ : 1 ≤ p.γ)
    (hrel : p.α + 1 ≥ p.m + p.γ +
      (if p.β = 0 then 0 else p.γ))
    (hχ : p.χ₀ < chiStrong3Formula p
      (unitIntervalNormalizedResolverGradientConstant p)
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    EventuallyGloballyExponentiallyStableNonminimal intervalDomain p
      intervalDomainSectorialStabilityNorms eq.1 eq.2 := by
  let eq := positiveEquilibrium p ⟨ha, hb⟩
  let M0 := unitIntervalNormalizedResolverGradientConstant p
  have hmge : 1 ≤ p.m := by rw [hm]
  have hcond : NonminimalGlobalStabilityFormulaCondition
      p eq.1 eq.2 M0 :=
    Or.inr (Or.inr (Or.inl
      ⟨hmge, hγ, hrel, by simpa [eq, M0] using hχ⟩))
  have hstable : LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
    simpa [eq] using hcond.linearlyStable_unitInterval p ha hb
  have hglobal : GloballyAsymptoticallyStableNonminimal
      intervalDomain p eq.1 eq.2 := by
    simpa [eq, M0] using
      intervalDomain_strong3_globallyAsymptoticallyStableNonminimal
        p hm ha hb hγ hrel hχ
  exact intervalDomain_eventuallyGloballyExponentiallyStableNonminimal_of_global
    p hm ha (by simpa [eq] using paper3ConstantEquilibrium_positive p ha hb)
      hstable hglobal

/-- Concrete qualitative global-attractor producer for the fourth formula
branch.  Positive sensitivity uses the eventual signal floor; nonpositive
sensitivity reuses Theorem 2.3. -/
theorem intervalDomain_strong4_globallyAsymptoticallyStableNonminimal
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hβ : 1 ≤ p.β) (hγ : 1 ≤ p.γ)
    (hrel : p.α + 1 ≥ p.m + 2 * p.γ)
    (hχ : p.χ₀ < chiStrong4Formula p
      (unitIntervalNormalizedResolverGradientConstant p)
      (positiveEquilibrium p ⟨ha, hb⟩).1) :
    GloballyAsymptoticallyStableNonminimal intervalDomain p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  by_cases hχnonpos : p.χ₀ ≤ 0
  · exact intervalDomain_chiNonpos_globallyAsymptoticallyStableNonminimal
      p hm hχnonpos ha hb
  · have hχpos : 0 < p.χ₀ := lt_of_not_ge hχnonpos
    intro u v huv
    exact intervalDomain_uniformConvergesInSup_of_rectangleLogGap
      p (positiveEquilibrium_fst_pos p ⟨ha, hb⟩) huv
      (intervalDomain_rectangleLogGap_tendsto_zero_strong4
        p hm ha hb hβ hγ hrel hχpos hχ huv)

/-- Unconditional fourth formula branch of faithful eventual Theorem 2.4 on
the implemented `m = 1` unit-interval equation. -/
theorem
    intervalDomain_eventuallyGloballyExponentiallyStableNonminimal_strong4
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hβ : 1 ≤ p.β) (hγ : 1 ≤ p.γ)
    (hrel : p.α + 1 ≥ p.m + 2 * p.γ)
    (hχ : p.χ₀ < chiStrong4Formula p
      (unitIntervalNormalizedResolverGradientConstant p)
      (positiveEquilibrium p ⟨ha, hb⟩).1) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    EventuallyGloballyExponentiallyStableNonminimal intervalDomain p
      intervalDomainSectorialStabilityNorms eq.1 eq.2 := by
  let eq := positiveEquilibrium p ⟨ha, hb⟩
  let M0 := unitIntervalNormalizedResolverGradientConstant p
  have hmge : 1 ≤ p.m := by rw [hm]
  have hcond : NonminimalGlobalStabilityFormulaCondition
      p eq.1 eq.2 M0 :=
    Or.inr (Or.inr (Or.inr
      ⟨hmge, hβ, hγ, hrel, by simpa [eq, M0] using hχ⟩))
  have hstable : LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
    simpa [eq] using hcond.linearlyStable_unitInterval p ha hb
  have hglobal : GloballyAsymptoticallyStableNonminimal
      intervalDomain p eq.1 eq.2 := by
    simpa [eq, M0] using
      intervalDomain_strong4_globallyAsymptoticallyStableNonminimal
        p hm ha hb hβ hγ hrel hχ
  exact intervalDomain_eventuallyGloballyExponentiallyStableNonminimal_of_global
    p hm ha (by simpa [eq] using paper3ConstantEquilibrium_positive p ha hb)
      hstable hglobal

#print axioms rpow_gap_mono_exponent_of_straddles_one
#print axioms sq_rpow_gap_le_rpow_gap_two_mul_of_straddles_one
#print axioms sq_rpow_gap_le_rpow_gap_of_two_mul_le
#print axioms intervalDomain_strong3_decayCoefficient_pos
#print axioms intervalDomain_strong3_decayCoefficient_pos_of_chi
#print axioms intervalDomain_rectangleLogGapSlopeBound_le_strong3
#print axioms intervalDomain_rectangleLogGapSlopeBound_with_weight_le_strong3
#print axioms one_sub_exp_neg_mul_le_rpow_gap_of_straddles_one
#print axioms le_sub_mul_of_dini_upper_bound
#print axioms intervalDomain_rectangleLogGap_antitone_strong3
#print axioms intervalDomain_rectangleLogGap_antitone_of_weighted_strong3
#print axioms intervalDomain_rectangleLogGap_tendsto_zero_strong3
#print axioms intervalDomain_rectangleLogGap_tendsto_zero_of_weighted_strong3
#print axioms intervalDomain_rectangleLogGap_tendsto_zero_strong4
#print axioms intervalDomain_supNorm_sub_equilibrium_le_logGapEnvelope
#print axioms intervalDomain_uniformConvergesInSup_of_rectangleLogGap
#print axioms
  intervalDomain_strong3_globallyAsymptoticallyStableNonminimal
#print axioms
  intervalDomain_eventuallyGloballyExponentiallyStableNonminimal_strong3
#print axioms intervalDomain_sensitivity_weights_le_of_signal_floor
#print axioms chi_mul_vABWeight_lt_chiStrong3_of_lt_chiStrong4
#print axioms intervalDomain_strong4_globallyAsymptoticallyStableNonminimal
#print axioms
  intervalDomain_eventuallyGloballyExponentiallyStableNonminimal_strong4

end

end ShenWork.Paper3
