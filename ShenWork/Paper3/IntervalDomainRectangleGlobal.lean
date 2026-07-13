import ShenWork.Paper3.IntervalDomainRectangleLogGap

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
theorem intervalDomain_strong3_decayCoefficient_pos
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b) {M0 : ℝ}
    (hχ : p.χ₀ < chiStrong3Formula p M0
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2) :
    0 < p.a -
      p.χ₀ * p.ν * (positiveEquilibrium p ⟨ha, hb⟩).1 ^ p.γ *
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
  have hχ' : p.χ₀ < p.a / A * (1 / D) := by
    simpa [chiStrong3Formula, hm, uStar, vStar, A, D] using hχ
  have hmul : p.χ₀ * A * D < p.a := by
    calc
      p.χ₀ * A * D = p.χ₀ * (A * D) := by ring
      _ < (p.a / A * (1 / D)) * (A * D) :=
        mul_lt_mul_of_pos_right hχ' (mul_pos hA hD)
      _ = p.a := by
        field_simp [hA.ne', hD.ne']
  dsimp [A, D] at hmul
  nlinarith

/-- Under the third strong-logistic exponent condition, the concrete
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
      2 * p.χ₀ * p.ν * (U ^ p.γ - L ^ p.γ) ≤
        (2 * p.χ₀ * A) * Gα := by
    rw [hgapγ]
    calc
      2 * p.χ₀ * p.ν * (uStar ^ p.γ * Gγ) =
          (2 * p.χ₀ * A) * Gγ := by
            dsimp [A]
            ring
      _ ≤ (2 * p.χ₀ * A) * Gα :=
        mul_le_mul_of_nonneg_left hGγGα
          (mul_nonneg (mul_nonneg (by norm_num) hχpos.le) hA)
  have hsquare :
      p.χ₀ * p.β *
          (C * (p.ν * (U ^ p.γ - L ^ p.γ))) ^ 2 ≤
        (p.χ₀ * p.β * (C * A) ^ 2) * Gα := by
    by_cases hβ0 : p.β = 0
    · simp [hβ0]
    · have htwoγα : 2 * p.γ ≤ p.α := by
        simp [hm, hβ0] at hrel
        linarith
      have hsq : Gγ ^ 2 ≤ Gα := by
        exact sq_rpow_gap_le_rpow_gap_of_two_mul_le
          hY hY1 hX1 hγ_nonneg htwoγα
      have hcoef : 0 ≤ p.χ₀ * p.β * (C * A) ^ 2 :=
        mul_nonneg (mul_nonneg hχpos.le p.hβ) (sq_nonneg _)
      rw [hgapγ]
      calc
        p.χ₀ * p.β *
            (C * (p.ν * (uStar ^ p.γ * Gγ))) ^ 2 =
            (p.χ₀ * p.β * (C * A) ^ 2) * Gγ ^ 2 := by
              dsimp [A]
              ring
        _ ≤ (p.χ₀ * p.β * (C * A) ^ 2) * Gα :=
          mul_le_mul_of_nonneg_left hsq hcoef
  have hcoefficient : 0 < p.a - p.χ₀ * A * D := by
    have hc := intervalDomain_strong3_decayCoefficient_pos p hm ha hb hχ
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
  have hfinal : intervalDomain_rectangleLogGapSlopeBound p uStar u t ≤
      -(p.a - p.χ₀ * A * D) * Gα := by
    rw [intervalDomain_rectangleLogGapSlopeBound_eq]
    dsimp only
    change
      2 * p.χ₀ * p.ν * (U ^ p.γ - L ^ p.γ) +
          p.χ₀ * p.β *
            (C * (p.ν * (U ^ p.γ - L ^ p.γ))) ^ 2 -
          p.b * (U ^ p.α - L ^ p.α) ≤
        -(p.a - p.χ₀ * A * D) * Gα
    rw [hgapα, hlogistic]
    calc
      2 * p.χ₀ * p.ν * (U ^ p.γ - L ^ p.γ) +
            p.χ₀ * p.β *
              (C * (p.ν * (U ^ p.γ - L ^ p.γ))) ^ 2 -
            p.a * Gα ≤
          (2 * p.χ₀ * A) * Gα +
            (p.χ₀ * p.β * (C * A) ^ 2) * Gα -
            p.a * Gα := by linarith
      _ = (p.χ₀ * A * D - p.a) * Gα := by
        dsimp [D]
        rw [hbetaVM0]
        ring
      _ = -(p.a - p.χ₀ * A * D) * Gα := by ring
  dsimp only
  convert hfinal using 1 <;> ring

#print axioms rpow_gap_mono_exponent_of_straddles_one
#print axioms sq_rpow_gap_le_rpow_gap_two_mul_of_straddles_one
#print axioms sq_rpow_gap_le_rpow_gap_of_two_mul_le
#print axioms intervalDomain_strong3_decayCoefficient_pos
#print axioms intervalDomain_rectangleLogGapSlopeBound_le_strong3

end

end ShenWork.Paper3
