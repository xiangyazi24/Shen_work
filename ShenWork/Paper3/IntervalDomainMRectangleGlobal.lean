import ShenWork.Paper3.IntervalDomainMRectangleLogGap
import ShenWork.Paper3.IntervalDomainRectangleGlobal
import ShenWork.Paper3.IntervalDomainMEntropyStrong2Global

/-!
# Rectangle global-attraction route for the faithful general-`m` equation

`intervalDomainM` counterpart of `IntervalDomainRectangleGlobal`, covering the
strictly attractive (`χ₀ > 0`) third and fourth strong-logistic branches.  The
scalar power-gap lemmas and the Grönwall/Dini window integrators are reused
verbatim from the `m = 1` file; the genuine `m > 1` content is the absorption
of the extra `U^(m-1)` / `L^(m-1)` chemotaxis prefactors into a single
normalized `α`-power gap, licensed by the strengthened branch exponent
conditions `α + 1 ≥ m + γ + (β≠0)γ` and `α + 1 ≥ m + 2γ`.

The neutral / repulsive case `χ₀ ≤ 0` is supplied as an explicit
per-branch hypothesis (`hchiNonpos`): its faithful general-`m` proof needs the
mass-floor + max-decay chain rebuilt for the `u^m` flux, a separate scoped
frontier (`DOCTRINE_thm24_fable.md`, item 7 note).
-/

open Filter Set Topology
open ShenWork.IntervalDomain ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- Scalar absorption: multiplying a straddling power gap by `X^s` is dominated
by the gap at the raised exponent.  This is the core `m > 1` inequality. -/
theorem rpow_mul_gap_le_gap_add
    {L U s a : ℝ}
    (hL : 0 < L) (hL1 : L ≤ 1) (h1U : 1 ≤ U)
    (hs : 0 ≤ s) (ha : 0 ≤ a) :
    U ^ s * (U ^ a - L ^ a) ≤ U ^ (a + s) - L ^ (a + s) := by
  have hU : 0 < U := lt_of_lt_of_le zero_lt_one h1U
  have hUadd : U ^ (a + s) = U ^ a * U ^ s := by
    rw [Real.rpow_add hU]
  have hLadd : L ^ (a + s) = L ^ a * L ^ s := by
    rw [Real.rpow_add hL]
  have hLsUs : L ^ s ≤ U ^ s :=
    Real.rpow_le_rpow hL.le (hL1.trans h1U) hs
  have hLa : 0 ≤ L ^ a := Real.rpow_nonneg hL.le _
  have hkey : 0 ≤ L ^ a * (U ^ s - L ^ s) :=
    mul_nonneg hLa (sub_nonneg.mpr hLsUs)
  rw [hUadd, hLadd]
  nlinarith

/-- The fourth threshold reduced by the eventual signal-floor factor lies
below the third threshold (general `m`). -/
theorem intervalDomainM_chi_mul_vABWeight_lt_chiStrong3_of_lt_chiStrong4
    (p : CM2Params) (hm : 1 ≤ p.m)
    (ha : 0 < p.a) (hb : 0 < p.b) {M0 : ℝ}
    (hχ : p.χ₀ < chiStrong4Formula p M0
      (positiveEquilibrium p ⟨ha, hb⟩).1) :
    p.χ₀ * (1 + vABLowerFormula p) ^ (-p.β) <
      chiStrong3Formula p M0
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  set uStar := (positiveEquilibrium p ⟨ha, hb⟩).1 with huStarDef
  set vStar := (positiveEquilibrium p ⟨ha, hb⟩).2 with hvStarDef
  set base := 1 + vABLowerFormula p with hbaseDef
  set factor := base ^ p.β with hfactorDef
  have hbase : 0 < base := by
    rw [hbaseDef]; linarith [vABLowerFormula_pos p ha hb hm]
  have hfactor : 0 < factor := Real.rpow_pos_of_pos hbase _
  have hvStar : vStar = p.ν / p.μ * uStar ^ p.γ := rfl
  have hsecond : p.χ₀ < factor *
      chiStrong3Formula p M0 uStar vStar := by
    have hmRight : chiStrong4Formula p M0 uStar ≤
        (1 + vABLowerFormula p) ^ p.β *
          chiStrong3Formula p M0 uStar
            (p.ν / p.μ * uStar ^ p.γ) := by
      unfold chiStrong4Formula
      exact min_le_right _ _
    have := hχ.trans_le (by simpa [huStarDef] using hmRight)
    simpa [factor, base, hvStar] using this
  have hdiv : p.χ₀ / factor <
      chiStrong3Formula p M0 uStar vStar := by
    rw [div_lt_iff₀ hfactor]
    simpa [mul_comm] using hsecond
  have hq : base ^ (-p.β) = factor⁻¹ := by
    rw [Real.rpow_neg hbase.le]
  simpa [huStarDef, hvStarDef, base, factor, hq, div_eq_mul_inv] using hdiv

/-- The general-`m` third paper threshold is the positivity condition for the
scalar rectangle damping coefficient (with `u*^(m+γ-1)`). -/
theorem intervalDomainM_strong3_decayCoefficient_pos_of_chi
    (p : CM2Params) (hm : 1 ≤ p.m)
    (ha : 0 < p.a) (hb : 0 < p.b) (chi : ℝ) {M0 : ℝ}
    (hχ : chi < chiStrong3Formula p M0
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2) :
    0 < p.a -
      chi * p.ν * (positiveEquilibrium p ⟨ha, hb⟩).1 ^ (p.m + p.γ - 1) *
        (2 + p.β * (positiveEquilibrium p ⟨ha, hb⟩).2 * M0 ^ 2) := by
  set uStar := (positiveEquilibrium p ⟨ha, hb⟩).1 with huStarDef
  set vStar := (positiveEquilibrium p ⟨ha, hb⟩).2 with hvStarDef
  have huStar : 0 < uStar := by
    rw [huStarDef]; exact positiveEquilibrium_fst_pos p ⟨ha, hb⟩
  have hvStar : 0 < vStar := by
    rw [hvStarDef]; exact positiveEquilibrium_snd_pos p ⟨ha, hb⟩
  set A : ℝ := p.ν * uStar ^ (p.m + p.γ - 1) with hADef
  set D : ℝ := 2 + p.β * vStar * M0 ^ 2 with hDDef
  have hA : 0 < A := mul_pos p.hν (Real.rpow_pos_of_pos huStar _)
  have hD : 0 < D := by
    have hnonneg : 0 ≤ p.β * vStar * M0 ^ 2 :=
      mul_nonneg (mul_nonneg p.hβ hvStar.le) (sq_nonneg M0)
    rw [hDDef]; linarith
  have hχ' : chi < p.a / A * (1 / D) := by
    simpa [chiStrong3Formula, huStarDef, hvStarDef, A, D] using hχ
  have hmul : chi * A * D < p.a := by
    calc
      chi * A * D = chi * (A * D) := by ring
      _ < (p.a / A * (1 / D)) * (A * D) :=
        mul_lt_mul_of_pos_right hχ' (mul_pos hA hD)
      _ = p.a := by field_simp [hA.ne', hD.ne']
  rw [hADef, hDDef] at hmul
  nlinarith

set_option maxHeartbeats 1600000 in
/-- Under the general-`m` third exponent condition, the faithful weighted
rectangle vector field is bounded by a strictly negative multiple of the
normalized `α`-power gap.  This is the core `m > 1` absorption step. -/
theorem intervalDomainM_rectangleLogGapSlopeBound_with_weight_le_strong3
    (p : CM2Params) (hm : 1 ≤ p.m)
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
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    let uStar := (positiveEquilibrium p ⟨ha, hb⟩).1
    let vStar := (positiveEquilibrium p ⟨ha, hb⟩).2
    let M0 := unitIntervalNormalizedResolverGradientConstant p
    let coefficient :=
      p.a - (p.χ₀ * q) * p.ν * uStar ^ (p.m + p.γ - 1) *
        (2 + p.β * vStar * M0 ^ 2)
    intervalDomainM_rectangleLogGapSlopeBound_with_weight p q uStar u t ≤
      -coefficient *
        ((intervalDomain_clampedUpper uStar u t / uStar) ^ p.α -
          (intervalDomain_clampedLower uStar u t / uStar) ^ p.α) := by
  set uStar := (positiveEquilibrium p ⟨ha, hb⟩).1 with huStarDef
  set vStar := (positiveEquilibrium p ⟨ha, hb⟩).2 with hvStarDef
  set M0 := unitIntervalNormalizedResolverGradientConstant p with hM0Def
  set C := unitIntervalResolverGradientOscillationConstant p with hCDef
  set U := intervalDomain_clampedUpper uStar u t with hUDef
  set L := intervalDomain_clampedLower uStar u t with hLDef
  set X := U / uStar with hXDef
  set Y := L / uStar with hYDef
  set Gγ := X ^ p.γ - Y ^ p.γ with hGγDef
  set Gα := X ^ p.α - Y ^ p.α with hGαDef
  have huStar : 0 < uStar := by
    rw [huStarDef]; exact positiveEquilibrium_fst_pos p ⟨ha, hb⟩
  have hLpos : 0 < L := by
    rw [hLDef]; exact intervalDomainM_clampedLower_pos huStar hsol ht
  have hLu : L ≤ uStar := by
    rw [hLDef]
    exact (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
      uStar u t).1
  have huU : uStar ≤ U := by
    rw [hUDef]
    exact (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
      uStar u t).2
  have hY : 0 < Y := div_pos hLpos huStar
  have hY1 : Y ≤ 1 := (div_le_one huStar).2 hLu
  have hX1 : 1 ≤ X := (one_le_div huStar).2 huU
  have hX : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hγ_nonneg : 0 ≤ p.γ := hγ.trans' zero_le_one
  have hm1 : 0 ≤ p.m - 1 := by linarith
  have hGα : 0 ≤ Gα := by
    rw [hGαDef]
    exact sub_nonneg.mpr (Real.rpow_le_rpow hY.le (hY1.trans hX1) p.hα.le)
  have hGγ : 0 ≤ Gγ := by
    rw [hGγDef]
    exact sub_nonneg.mpr (Real.rpow_le_rpow hY.le (hY1.trans hX1) hγ_nonneg)
  have hmγα : p.m + p.γ - 1 ≤ p.α := by
    by_cases hβ0 : p.β = 0
    · rw [if_pos hβ0] at hrel; linarith
    · rw [if_neg hβ0] at hrel; linarith [p.hγ]
  -- factorizations
  have hUfactor : U = uStar * X := by
    rw [hXDef]; field_simp [huStar.ne']
  have hLfactor : L = uStar * Y := by
    rw [hYDef]; field_simp [huStar.ne']
  have hUγ : U ^ p.γ = uStar ^ p.γ * X ^ p.γ := by
    rw [hUfactor, Real.mul_rpow huStar.le hX.le]
  have hLγ : L ^ p.γ = uStar ^ p.γ * Y ^ p.γ := by
    rw [hLfactor, Real.mul_rpow huStar.le hY.le]
  have hUα : U ^ p.α = uStar ^ p.α * X ^ p.α := by
    rw [hUfactor, Real.mul_rpow huStar.le hX.le]
  have hLα : L ^ p.α = uStar ^ p.α * Y ^ p.α := by
    rw [hLfactor, Real.mul_rpow huStar.le hY.le]
  have hUm : U ^ (p.m - 1) = uStar ^ (p.m - 1) * X ^ (p.m - 1) := by
    rw [hUfactor, Real.mul_rpow huStar.le hX.le]
  have hLm : L ^ (p.m - 1) = uStar ^ (p.m - 1) * Y ^ (p.m - 1) := by
    rw [hLfactor, Real.mul_rpow huStar.le hY.le]
  have hgapγ : U ^ p.γ - L ^ p.γ = uStar ^ p.γ * Gγ := by
    rw [hUγ, hLγ, hGγDef]; ring
  have hgapα : U ^ p.α - L ^ p.α = uStar ^ p.α * Gα := by
    rw [hUα, hLα, hGαDef]; ring
  have hbuα : p.b * uStar ^ p.α = p.a := by
    rw [show uStar ^ p.α = p.a / p.b by
      rw [huStarDef]; exact positiveEquilibrium_fst_rpow_alpha p ⟨ha, hb⟩]
    field_simp [hb.ne']
  have hM0sq : M0 ^ 2 = p.μ * C ^ 2 := by
    rw [hM0Def, hCDef, unitIntervalNormalizedResolverGradientConstant,
      mul_pow, Real.sq_sqrt p.hμ.le]
  have hvrel : p.μ * vStar = p.ν * uStar ^ p.γ := by
    rw [huStarDef, hvStarDef]
    exact positiveEquilibrium_elliptic_relation p ⟨ha, hb⟩
  have hvM0 : vStar * M0 ^ 2 = p.ν * uStar ^ p.γ * C ^ 2 := by
    calc vStar * M0 ^ 2 = (p.μ * vStar) * C ^ 2 := by rw [hM0sq]; ring
      _ = (p.ν * uStar ^ p.γ) * C ^ 2 := by rw [hvrel]
      _ = p.ν * uStar ^ p.γ * C ^ 2 := by ring
  -- rpow exponent arithmetic on uStar
  have hupγm : uStar ^ (p.m + p.γ - 1) = uStar ^ p.γ * uStar ^ (p.m - 1) := by
    rw [← Real.rpow_add huStar]; congr 1; ring
  have hup2γm : uStar ^ (p.m + p.γ - 1) * uStar ^ p.γ =
      uStar ^ (p.m + 2 * p.γ - 1) := by
    rw [← Real.rpow_add huStar]; congr 1; ring
  set A : ℝ := p.ν * uStar ^ (p.m + p.γ - 1) with hADef
  set D : ℝ := 2 + p.β * vStar * M0 ^ 2 with hDDef
  have hA : 0 ≤ A := (mul_pos p.hν (Real.rpow_pos_of_pos huStar _)).le
  have huγpos : 0 < uStar ^ p.γ := Real.rpow_pos_of_pos huStar _
  have humpos : 0 ≤ uStar ^ (p.m - 1) := (Real.rpow_pos_of_pos huStar _).le
  -- absorption: Term1
  have habsX : X ^ (p.m - 1) * Gγ ≤ X ^ (p.m + p.γ - 1) - Y ^ (p.m + p.γ - 1) := by
    have := rpow_mul_gap_le_gap_add hY hY1 hX1 hm1 hγ_nonneg
    rw [hGγDef]
    have hexp : p.γ + (p.m - 1) = p.m + p.γ - 1 := by ring
    rw [hexp] at this
    exact this
  have hXYm : Y ^ (p.m - 1) ≤ X ^ (p.m - 1) :=
    Real.rpow_le_rpow hY.le (hY1.trans hX1) hm1
  have habsY : Y ^ (p.m - 1) * Gγ ≤ X ^ (p.m + p.γ - 1) - Y ^ (p.m + p.γ - 1) :=
    (mul_le_mul_of_nonneg_right hXYm hGγ).trans habsX
  have hmono1 : X ^ (p.m + p.γ - 1) - Y ^ (p.m + p.γ - 1) ≤ Gα := by
    rw [hGαDef]
    exact rpow_gap_mono_exponent_of_straddles_one hY hY1 hX1 hmγα
  have hTerm1 : Gγ * (X ^ (p.m - 1) + Y ^ (p.m - 1)) ≤ 2 * Gα := by
    have h1 : X ^ (p.m - 1) * Gγ ≤ Gα := habsX.trans hmono1
    have h2 : Y ^ (p.m - 1) * Gγ ≤ Gα := habsY.trans hmono1
    nlinarith
  -- linear term bound
  have hlinear :
      p.χ₀ * q * p.ν * (U ^ p.γ - L ^ p.γ) *
          (U ^ (p.m - 1) + L ^ (p.m - 1)) ≤
        (2 * (p.χ₀ * q) * A) * Gα := by
    rw [hgapγ, hUm, hLm]
    have hfe :
        p.χ₀ * q * p.ν * (uStar ^ p.γ * Gγ) *
            (uStar ^ (p.m - 1) * X ^ (p.m - 1) +
              uStar ^ (p.m - 1) * Y ^ (p.m - 1)) =
          (p.χ₀ * q * A) *
            (Gγ * (X ^ (p.m - 1) + Y ^ (p.m - 1))) := by
      rw [hADef, hupγm]; ring
    rw [hfe]
    have hcoef : 0 ≤ p.χ₀ * q * A := mul_nonneg hχweightpos.le hA
    calc (p.χ₀ * q * A) * (Gγ * (X ^ (p.m - 1) + Y ^ (p.m - 1)))
        ≤ (p.χ₀ * q * A) * (2 * Gα) :=
          mul_le_mul_of_nonneg_left hTerm1 hcoef
      _ = (2 * (p.χ₀ * q) * A) * Gα := by ring
  -- square term bound (Term2 vanishes when β = 0)
  have hupnn : 0 ≤ uStar ^ (p.m - 1) * uStar ^ p.γ * uStar ^ p.γ :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg huStar.le _)
      (Real.rpow_nonneg huStar.le _)) (Real.rpow_nonneg huStar.le _)
  have hcoef : 0 ≤ p.χ₀ * q * p.β * p.ν ^ 2 * C ^ 2 *
      (uStar ^ (p.m - 1) * uStar ^ p.γ * uStar ^ p.γ) := by
    have hrest : 0 ≤ p.β * p.ν ^ 2 * C ^ 2 *
        (uStar ^ (p.m - 1) * uStar ^ p.γ * uStar ^ p.γ) :=
      mul_nonneg (mul_nonneg (mul_nonneg p.hβ (sq_nonneg _)) (sq_nonneg _)) hupnn
    have h := mul_nonneg hχweightpos.le hrest
    rwa [show p.χ₀ * q *
        (p.β * p.ν ^ 2 * C ^ 2 *
          (uStar ^ (p.m - 1) * uStar ^ p.γ * uStar ^ p.γ)) =
        p.χ₀ * q * p.β * p.ν ^ 2 * C ^ 2 *
          (uStar ^ (p.m - 1) * uStar ^ p.γ * uStar ^ p.γ) from by ring] at h
  have hupeq : uStar ^ (p.m - 1) * uStar ^ p.γ * uStar ^ p.γ =
      uStar ^ (p.m + 2 * p.γ - 1) := by
    rw [← Real.rpow_add huStar, ← Real.rpow_add huStar]; congr 1; ring
  have hTerm2coef : X ^ (p.m - 1) * Gγ ^ 2 ≤ Gα ∨ p.β = 0 := by
    by_cases hβ0 : p.β = 0
    · exact Or.inr hβ0
    · refine Or.inl ?_
      have hsq : Gγ ^ 2 ≤ X ^ (2 * p.γ) - Y ^ (2 * p.γ) := by
        rw [hGγDef]
        exact sq_rpow_gap_le_rpow_gap_two_mul_of_straddles_one
          hY hY1 hX1 hγ_nonneg
      have h2γm : 2 * p.γ + (p.m - 1) ≤ p.α := by
        rw [if_neg hβ0] at hrel; nlinarith [p.hγ]
      have habs2 : X ^ (p.m - 1) * (X ^ (2 * p.γ) - Y ^ (2 * p.γ)) ≤
          X ^ (2 * p.γ + (p.m - 1)) - Y ^ (2 * p.γ + (p.m - 1)) :=
        rpow_mul_gap_le_gap_add hY hY1 hX1 hm1 (by positivity)
      have hmono2 : X ^ (2 * p.γ + (p.m - 1)) - Y ^ (2 * p.γ + (p.m - 1)) ≤ Gα := by
        rw [hGαDef]
        exact rpow_gap_mono_exponent_of_straddles_one hY hY1 hX1 h2γm
      have hXmnn : 0 ≤ X ^ (p.m - 1) := (Real.rpow_pos_of_pos hX _).le
      calc X ^ (p.m - 1) * Gγ ^ 2
          ≤ X ^ (p.m - 1) * (X ^ (2 * p.γ) - Y ^ (2 * p.γ)) :=
            mul_le_mul_of_nonneg_left hsq hXmnn
        _ ≤ Gα := habs2.trans hmono2
  have hsquare :
      p.χ₀ * q * p.β * U ^ (p.m - 1) *
          (C * (p.ν * (U ^ p.γ - L ^ p.γ))) ^ 2 ≤
        (p.χ₀ * q * p.β * p.ν ^ 2 * C ^ 2 *
          uStar ^ (p.m + 2 * p.γ - 1)) * Gα := by
    rw [hgapγ, hUm]
    have hfe :
        p.χ₀ * q * p.β * (uStar ^ (p.m - 1) * X ^ (p.m - 1)) *
            (C * (p.ν * (uStar ^ p.γ * Gγ))) ^ 2 =
          (p.χ₀ * q * p.β * p.ν ^ 2 * C ^ 2 *
            (uStar ^ (p.m - 1) * uStar ^ p.γ * uStar ^ p.γ)) *
              (X ^ (p.m - 1) * Gγ ^ 2) := by ring
    rw [hfe]
    rcases hTerm2coef with hT2 | hβ0
    · calc
        (p.χ₀ * q * p.β * p.ν ^ 2 * C ^ 2 *
            (uStar ^ (p.m - 1) * uStar ^ p.γ * uStar ^ p.γ)) *
              (X ^ (p.m - 1) * Gγ ^ 2)
            ≤ (p.χ₀ * q * p.β * p.ν ^ 2 * C ^ 2 *
                (uStar ^ (p.m - 1) * uStar ^ p.γ * uStar ^ p.γ)) * Gα :=
              mul_le_mul_of_nonneg_left hT2 hcoef
        _ = (p.χ₀ * q * p.β * p.ν ^ 2 * C ^ 2 *
              uStar ^ (p.m + 2 * p.γ - 1)) * Gα := by rw [hupeq]
    · rw [hβ0]; simp
  -- combine
  have hbetaVM0 : p.β * vStar * M0 ^ 2 = p.β * p.ν * uStar ^ p.γ * C ^ 2 := by
    calc p.β * vStar * M0 ^ 2 = p.β * (vStar * M0 ^ 2) := by ring
      _ = p.β * (p.ν * uStar ^ p.γ * C ^ 2) := by rw [hvM0]
      _ = p.β * p.ν * uStar ^ p.γ * C ^ 2 := by ring
  have hcoeffExpand :
      (p.χ₀ * q) * A * D =
        2 * (p.χ₀ * q) * A +
          p.χ₀ * q * p.β * p.ν ^ 2 * C ^ 2 *
            uStar ^ (p.m + 2 * p.γ - 1) := by
    rw [hDDef, hbetaVM0, hADef]
    have : p.ν * uStar ^ (p.m + p.γ - 1) * (p.β * p.ν * uStar ^ p.γ * C ^ 2) =
        p.β * p.ν ^ 2 * C ^ 2 * (uStar ^ (p.m + p.γ - 1) * uStar ^ p.γ) := by ring
    rw [show p.χ₀ * q * (p.ν * uStar ^ (p.m + p.γ - 1)) *
        (2 + p.β * p.ν * uStar ^ p.γ * C ^ 2) =
        2 * (p.χ₀ * q) * (p.ν * uStar ^ (p.m + p.γ - 1)) +
        p.χ₀ * q * (p.ν * uStar ^ (p.m + p.γ - 1) *
          (p.β * p.ν * uStar ^ p.γ * C ^ 2)) by ring, this, hup2γm]
    ring
  have hlogistic : p.b * (U ^ p.α - L ^ p.α) = p.a * Gα := by
    rw [hgapα, ← mul_assoc, hbuα]
  have hfinal :
      intervalDomainM_rectangleLogGapSlopeBound_with_weight p q uStar u t ≤
        -(p.a - (p.χ₀ * q) * A * D) * Gα := by
    rw [intervalDomainM_rectangleLogGapSlopeBound_with_weight_eq]
    dsimp only
    have hstep :
        p.χ₀ * q * p.ν * (U ^ p.γ - L ^ p.γ) *
              (U ^ (p.m - 1) + L ^ (p.m - 1)) +
            p.χ₀ * q * p.β * U ^ (p.m - 1) *
              (C * (p.ν * (U ^ p.γ - L ^ p.γ))) ^ 2 -
            p.b * (U ^ p.α - L ^ p.α) ≤
          (2 * (p.χ₀ * q) * A) * Gα +
            (p.χ₀ * q * p.β * p.ν ^ 2 * C ^ 2 *
              uStar ^ (p.m + 2 * p.γ - 1)) * Gα -
            p.a * Gα := by
      rw [hlogistic]; linarith
    refine hstep.trans_eq ?_
    rw [hcoeffExpand]; ring
  dsimp only
  have hgoalEq :
      -(p.a - (p.χ₀ * q) * A * D) * Gα =
        -(p.a - p.χ₀ * q * p.ν * uStar ^ (p.m + p.γ - 1) *
          (2 + p.β * vStar * M0 ^ 2)) *
          ((U / uStar) ^ p.α - (L / uStar) ^ p.α) := by
    rw [hADef, hDDef, hGαDef, hXDef, hYDef]; ring
  rw [hgoalEq] at hfinal
  exact hfinal

/-- The rectangle logarithmic gap is nonincreasing on any positive-time tail
where both sensitivity weights are controlled by `q` and the corresponding
effective sensitivity satisfies the third threshold. -/
theorem intervalDomainM_rectangleLogGap_antitone_of_weighted_strong3
    (p : CM2Params) (hm : 1 ≤ p.m)
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
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
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
  have hcont := intervalDomainM_rectangleLogGap_continuousOn
    huStar hsol hab
  have hdiniRaw := intervalDomainM_rectangleLogGap_dini_with_weight
    hq
    (fun s hs y hy => (hweights s (ht₁.trans hs.1) y hy).1)
    (fun s hs y hy => (hweights s (ht₁.trans hs.1) y hy).2)
    hχnonneg
    huStar (positiveEquilibrium_logistic_zero p ⟨ha, hb⟩) hsol hab
  have hslope : ∀ x ∈ Ico t₁ t₂,
      intervalDomainM_rectangleLogGapSlopeBound_with_weight
        p q uStar u x ≤ 0 := by
    intro x hx
    have hxpos : x ∈ Ioo (0 : ℝ) T := hab (Ico_subset_Icc_self hx)
    have hs := intervalDomainM_rectangleLogGapSlopeBound_with_weight_le_strong3
      p hm ha hb hγ hrel q hχweightpos hχ hsol hxpos
    let U := intervalDomain_clampedUpper uStar u x
    let L := intervalDomain_clampedLower uStar u x
    have hL : 0 < L := intervalDomainM_clampedLower_pos huStar hsol hxpos
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
    have hc : 0 < p.a - (p.χ₀ * q) * p.ν * uStar ^ (p.m + p.γ - 1) *
        (2 + p.β * vStar * M0 ^ 2) := by
      simpa [uStar, vStar, M0] using
        intervalDomainM_strong3_decayCoefficient_pos_of_chi
          p hm ha hb (p.χ₀ * q) hχ
    have hnonpos : -(p.a - (p.χ₀ * q) * p.ν * uStar ^ (p.m + p.γ - 1) *
        (2 + p.β * vStar * M0 ^ 2)) *
          ((U / uStar) ^ p.α - (L / uStar) ^ p.α) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hgap
    have hs' : intervalDomainM_rectangleLogGapSlopeBound_with_weight
          p q uStar u x ≤
        -(p.a - (p.χ₀ * q) * p.ν * uStar ^ (p.m + p.γ - 1) *
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
theorem intervalDomainM_rectangleLogGap_antitone_strong3
    (p : CM2Params) (hm : 1 ≤ p.m)
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
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v) :
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
  exact intervalDomainM_rectangleLogGap_antitone_of_weighted_strong3
    p hm ha hb hγ hrel 1 1 zero_lt_one zero_le_one hχpos.le
      (by simpa using hχpos) (by simpa using hχ) huv hweights

/-- A weighted strong-three tail drives the clamped logarithmic gap to zero. -/
theorem intervalDomainM_rectangleLogGap_tendsto_zero_of_weighted_strong3
    (p : CM2Params) (hm : 1 ≤ p.m)
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
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
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
  let c := p.a - (p.χ₀ * weight) * p.ν * uStar ^ (p.m + p.γ - 1) *
    (2 + p.β * vStar * M0 ^ 2)
  have huStar : 0 < uStar := by
    simpa [uStar] using positiveEquilibrium_fst_pos p ⟨ha, hb⟩
  have hc : 0 < c := by
    simpa [c, uStar, vStar, M0] using
      intervalDomainM_strong3_decayCoefficient_pos_of_chi
        p hm ha hb (p.χ₀ * weight) hχ
  have hnonneg : ∀ t : ℝ, start ≤ t → 0 ≤ G t := by
    intro t ht
    let T := t + 1
    have hT : 0 < T := by dsimp [T]; linarith
    have htT : t ∈ Ioo (0 : ℝ) T := by
      exact ⟨lt_of_lt_of_le hstart ht, by
        dsimp [T]
        exact lt_add_one t⟩
    exact intervalDomainM_rectangleLogGap_nonneg huStar
      (huv.classical T hT) htT
  have hmono : AntitoneOn G (Ici start) := by
    simpa [G, uStar] using
      intervalDomainM_rectangleLogGap_antitone_of_weighted_strong3
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
      simpa [G] using intervalDomainM_rectangleLogGap_continuousOn
        huStar hsol hab
    have hdini : ∀ x ∈ Ico start B, ∀ r : ℝ,
        intervalDomainM_rectangleLogGapSlopeBound_with_weight
            p weight uStar u x < r →
          ∃ᶠ z in nhdsWithin x (Ioi x),
            (z - x)⁻¹ * (G z - G x) < r := by
      simpa [G] using intervalDomainM_rectangleLogGap_dini_with_weight
        hweight_nonneg
        (fun s hs y hy => (hweights s (hs.1) y hy).1)
        (fun s hs y hy => (hweights s (hs.1) y hy).2)
        hχnonneg huStar
          (positiveEquilibrium_logistic_zero p ⟨ha, hb⟩) hsol hab
    have hslope : ∀ x ∈ Ico start B,
        intervalDomainM_rectangleLogGapSlopeBound_with_weight
          p weight uStar u x ≤ -decay := by
      intro x hx
      have hxpos : x ∈ Ioo (0 : ℝ) T := hab (Ico_subset_Icc_self hx)
      have hs := intervalDomainM_rectangleLogGapSlopeBound_with_weight_le_strong3
        p hm ha hb hγ hrel weight hχweightpos hχ hsol hxpos
      let U := intervalDomain_clampedUpper uStar u x
      let L := intervalDomain_clampedLower uStar u x
      let X := U / uStar
      let Y := L / uStar
      let Gα := X ^ p.α - Y ^ p.α
      have hL : 0 < L := intervalDomainM_clampedLower_pos huStar hsol hxpos
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
      have hs' : intervalDomainM_rectangleLogGapSlopeBound_with_weight
          p weight uStar u x ≤
          -c * Gα := by
        simpa [uStar, vStar, M0, c, U, L, X, Y, Gα] using hs
      calc
        intervalDomainM_rectangleLogGapSlopeBound_with_weight
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
theorem intervalDomainM_rectangleLogGap_tendsto_zero_strong3
    (p : CM2Params) (hm : 1 ≤ p.m)
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
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v) :
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
  exact intervalDomainM_rectangleLogGap_tendsto_zero_of_weighted_strong3
    p hm ha hb hγ hrel 1 1 zero_lt_one zero_le_one hχpos.le
      (by simpa using hχpos) (by simpa using hχ) huv hweights

/-- In the fourth branch, the eventual general-`m` signal floor reduces the
physical sensitivity to the weighted third-branch regime.  Because the strict
threshold inequality has slack, a floor slightly below `vABLowerFormula`
(reached by the faithful Theorem 2.1(3) persistence) still keeps the reduced
sensitivity below the third threshold. -/
theorem intervalDomainM_rectangleLogGap_tendsto_zero_strong4
    (p : CM2Params) (hm : 1 ≤ p.m)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hβ : 1 ≤ p.β) (hγ : 1 ≤ p.γ)
    (hrel : p.α + 1 ≥ p.m + 2 * p.γ)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong4Formula p
      (unitIntervalNormalizedResolverGradientConstant p)
      (positiveEquilibrium p ⟨ha, hb⟩).1)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    Tendsto
      (intervalDomain_rectangleLogGap
        (positiveEquilibrium p ⟨ha, hb⟩).1 u)
      atTop (nhds 0) := by
  set uStar := (positiveEquilibrium p ⟨ha, hb⟩).1 with huStarDef
  set vStar := (positiveEquilibrium p ⟨ha, hb⟩).2 with hvStarDef
  set M0 := unitIntervalNormalizedResolverGradientConstant p with hM0Def
  set S := chiStrong3Formula p M0 uStar vStar with hSDef
  have hvAB : 0 < vABLowerFormula p := vABLowerFormula_pos p ha hb hm
  have hχbar : p.χ₀ < chiBarFormula p :=
    chi_lt_chiBarFormula_of_lt_chiStrong4Formula p hχ
  have hstrict : p.χ₀ * (1 + vABLowerFormula p) ^ (-p.β) < S := by
    rw [hSDef, huStarDef, hvStarDef, hM0Def]
    exact intervalDomainM_chi_mul_vABWeight_lt_chiStrong3_of_lt_chiStrong4
      p hm ha hb hχ
  have hβpos : 0 < p.β := lt_of_lt_of_le zero_lt_one hβ
  have hβne : p.β ≠ 0 := ne_of_gt hβpos
  have hrel3 : p.α + 1 ≥ p.m + p.γ +
      (if p.β = 0 then 0 else p.γ) := by
    rw [if_neg hβne]; linarith
  -- continuity slack: a floor strictly below vABLower still beats S
  have hcont : ContinuousAt (fun f => p.χ₀ * (1 + f) ^ (-p.β))
      (vABLowerFormula p) := by
    refine continuousAt_const.mul ?_
    refine ContinuousAt.rpow_const (continuousAt_const.add continuousAt_id) ?_
    exact Or.inl (by simpa using ne_of_gt (show (0:ℝ) < 1 + vABLowerFormula p by linarith))
  have hev : ∀ᶠ f in 𝓝 (vABLowerFormula p),
      p.χ₀ * (1 + f) ^ (-p.β) < S :=
    hcont.tendsto.eventually_lt tendsto_const_nhds hstrict
  have hposev : ∀ᶠ f in 𝓝 (vABLowerFormula p), (0 : ℝ) < f :=
    eventually_gt_nhds hvAB
  have hltev : ∀ᶠ f in 𝓝[<] (vABLowerFormula p), f < vABLowerFormula p :=
    eventually_mem_nhdsWithin.mono (fun _ h => h)
  obtain ⟨floor, ⟨hflchi, hfl0⟩, hflt⟩ :=
    ((((hev.filter_mono nhdsWithin_le_nhds).and
      (hposev.filter_mono nhdsWithin_le_nhds)).and hltev)).exists
  have hfloorPos : 0 < floor := hfl0
  have hfloorlt : floor < vABLowerFormula p := hflt
  set weight := (1 + floor) ^ (-p.β) with hweightDef
  have hweight : 0 < weight :=
    Real.rpow_pos_of_pos (by linarith) _
  have hχweight : p.χ₀ * weight < chiStrong3Formula p
      (unitIntervalNormalizedResolverGradientConstant p) uStar vStar := by
    rw [hweightDef, ← hM0Def, ← hSDef]; exact hflchi
  -- eventual pointwise floor via the faithful general-m persistence
  have hevFloor := intervalDomainM_strong2_eventually_floor
    p ha hb hm hβ hχpos hχbar huv (floor := floor) (Or.inr hfloorlt)
  rcases eventually_atTop.1 hevFloor with ⟨Tv, hTv⟩
  set start := max Tv 1 with hstartDef
  have hstart : 0 < start :=
    lt_of_lt_of_le zero_lt_one (le_max_right Tv 1)
  have hTvStart : Tv ≤ start := le_max_left Tv 1
  have hweights : ∀ t, start ≤ t → ∀ y ∈ Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (v t) y) ^ (-p.β) ≤ weight ∧
        (1 + intervalDomainLift (v t) y) ^ (-p.β - 1) ≤ weight := by
    intro t ht y hy
    have hpoint : floor ≤ intervalDomainLift (v t) y := by
      have hv := hTv t (hTvStart.trans ht) (⟨y, hy⟩ : intervalDomainPoint)
      simpa [intervalDomainLift, hy] using hv
    simpa [weight] using intervalDomain_sensitivity_weights_le_of_signal_floor
      p hfloorPos.le hpoint
  have hgoal := intervalDomainM_rectangleLogGap_tendsto_zero_of_weighted_strong3
    p hm ha hb hγ hrel3 start weight hstart hweight.le hχpos.le
      (mul_pos hχpos hweight) hχweight huv hweights
  simpa [huStarDef] using hgoal

/-- The physical sup distance to the equilibrium is squeezed by an explicit
continuous function of the clamped logarithmic gap. -/
theorem intervalDomainM_supNorm_sub_equilibrium_le_logGapEnvelope
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huStar : 0 < uStar)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    0 ≤ intervalDomainM.supNorm (fun x => u t x - uStar) ∧
      intervalDomainM.supNorm (fun x => u t x - uStar) ≤
        uStar *
          (Real.exp (intervalDomain_rectangleLogGap uStar u t) -
            Real.exp (-intervalDomain_rectangleLogGap uStar u t)) := by
  let U := intervalDomain_clampedUpper uStar u t
  let L := intervalDomain_clampedLower uStar u t
  let G := intervalDomain_rectangleLogGap uStar u t
  have hL : 0 < L := intervalDomainM_clampedLower_pos huStar hsol ht
  have hLu : L ≤ uStar :=
    (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
      uStar u t).1
  have huU : uStar ≤ U :=
    (intervalDomain_clampedLower_le_equilibrium_le_clampedUpper
      uStar u t).2
  have hU : 0 < U := huStar.trans_le huU
  have hpoint : ∀ x : intervalDomainPoint, |u t x - uStar| ≤ U - L := by
    intro x
    have hx := intervalDomainM_equilibriumChoiceValue_mem_clamped
      (uStar := uStar) hsol ht (Sum.inr x)
    simp only [intervalDomain_equilibriumChoiceValue_inr] at hx
    rw [abs_le]
    constructor <;> linarith
  have hsup : intervalDomainM.supNorm (fun x => u t x - uStar) ≤ U - L :=
    intervalDomain_supNorm_le_of_pointwise_abs_le hpoint
  have hsup0 : 0 ≤ intervalDomainM.supNorm (fun x => u t x - uStar) :=
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
theorem intervalDomainM_uniformConvergesInSup_of_rectangleLogGap
    (p : CM2Params) {uStar : ℝ} (huStar : 0 < uStar)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hgap : Tendsto (intervalDomain_rectangleLogGap uStar u)
      atTop (nhds 0)) :
    UniformConvergesInSup intervalDomainM u uStar := by
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
      0 ≤ intervalDomainM.supNorm (fun x => u t x - uStar) ∧
        intervalDomainM.supNorm (fun x => u t x - uStar) ≤ B t := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    let T := t + 1
    have hT : 0 < T := by dsimp [T]; linarith
    have htT : t ∈ Ioo (0 : ℝ) T := by
      exact ⟨lt_of_lt_of_le zero_lt_one ht, by
        dsimp [T]
        exact lt_add_one t⟩
    simpa [B, G] using
      intervalDomainM_supNorm_sub_equilibrium_le_logGapEnvelope
        huStar (huv.classical T hT) htT
  unfold UniformConvergesInSup
  exact squeeze_zero' (hbounds.mono fun _ h => h.1)
    (hbounds.mono fun _ h => h.2) hB



/-- The rectangle route converts qualitative global attraction into eventual
exponential `C¹` stability on the faithful general-`m` domain. -/
theorem intervalDomainM_eventualGlobal_of_globallyAsymptotic
    (p : CM2Params) {uStar vStar : ℝ}
    (ha : 0 < p.a)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hstable : LinearlyStable unitIntervalNeumannSpectrum p uStar vStar)
    (hglobal : GloballyAsymptoticallyStableNonminimal intervalDomainM p uStar vStar) :
    EventuallyGloballyExponentiallyStableNonminimal intervalDomainM p
      intervalDomainMSectorialStabilityNorms uStar vStar := by
  refine ⟨hglobal, ?_⟩
  intro u v huv
  have hconv : UniformConvergesInSup intervalDomainM u uStar := hglobal u v huv
  refine intervalDomainM_eventualC1_of_lateSupClose p ha heq hstable huv ?_
  intro eps heps
  rw [UniformConvergesInSup, Metric.tendsto_atTop] at hconv
  obtain ⟨N, hN⟩ := hconv eps heps
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  have h := hN (max N 1) (le_max_left _ _)
  rw [Real.dist_eq, sub_zero] at h
  show intervalDomainM.supNorm (fun x => u (max N 1) x - uStar) < eps
  exact (le_abs_self _).trans_lt h

/-- Concrete qualitative global-attractor producer for the third formula
branch, faithful general-`m`.  Strictly attractive sensitivity is the
rectangle argument; the neutral/repulsive case `χ₀ ≤ 0` is the supplied
frontier. -/
theorem intervalDomainM_strong3_globallyAsymptoticallyStableNonminimal
    (p : CM2Params) (hm : 1 ≤ p.m)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ : 1 ≤ p.γ)
    (hrel : p.α + 1 ≥ p.m + p.γ + (if p.β = 0 then 0 else p.γ))
    (hχ : p.χ₀ < chiStrong3Formula p
      (unitIntervalNormalizedResolverGradientConstant p)
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2)
    (hchiNonpos : p.χ₀ ≤ 0 →
      GloballyAsymptoticallyStableNonminimal intervalDomainM p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2) :
    GloballyAsymptoticallyStableNonminimal intervalDomainM p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  by_cases hχnonpos : p.χ₀ ≤ 0
  · exact hchiNonpos hχnonpos
  · have hχpos : 0 < p.χ₀ := lt_of_not_ge hχnonpos
    intro u v huv
    exact intervalDomainM_uniformConvergesInSup_of_rectangleLogGap
      p (positiveEquilibrium_fst_pos p ⟨ha, hb⟩) huv
      (intervalDomainM_rectangleLogGap_tendsto_zero_strong3
        p hm ha hb hγ hrel hχpos hχ huv)

/-- Concrete qualitative global-attractor producer for the fourth formula
branch, faithful general-`m`. -/
theorem intervalDomainM_strong4_globallyAsymptoticallyStableNonminimal
    (p : CM2Params) (hm : 1 ≤ p.m)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hβ : 1 ≤ p.β) (hγ : 1 ≤ p.γ)
    (hrel : p.α + 1 ≥ p.m + 2 * p.γ)
    (hχ : p.χ₀ < chiStrong4Formula p
      (unitIntervalNormalizedResolverGradientConstant p)
      (positiveEquilibrium p ⟨ha, hb⟩).1)
    (hchiNonpos : p.χ₀ ≤ 0 →
      GloballyAsymptoticallyStableNonminimal intervalDomainM p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2) :
    GloballyAsymptoticallyStableNonminimal intervalDomainM p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  by_cases hχnonpos : p.χ₀ ≤ 0
  · exact hchiNonpos hχnonpos
  · have hχpos : 0 < p.χ₀ := lt_of_not_ge hχnonpos
    intro u v huv
    exact intervalDomainM_uniformConvergesInSup_of_rectangleLogGap
      p (positiveEquilibrium_fst_pos p ⟨ha, hb⟩) huv
      (intervalDomainM_rectangleLogGap_tendsto_zero_strong4
        p hm ha hb hβ hγ hrel hχpos hχ huv)

/-- Unconditional-in-`χ₀>0` third branch of faithful eventual Theorem 2.4
(general `m`); `χ₀ ≤ 0` supplied as a frontier. -/
theorem intervalDomainM_eventuallyGloballyExponentiallyStableNonminimal_strong3
    (p : CM2Params) (hm : 1 ≤ p.m)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ : 1 ≤ p.γ)
    (hrel : p.α + 1 ≥ p.m + p.γ + (if p.β = 0 then 0 else p.γ))
    (hχ : p.χ₀ < chiStrong3Formula p
      (unitIntervalNormalizedResolverGradientConstant p)
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2)
    (hchiNonpos : p.χ₀ ≤ 0 →
      GloballyAsymptoticallyStableNonminimal intervalDomainM p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    EventuallyGloballyExponentiallyStableNonminimal intervalDomainM p
      intervalDomainMSectorialStabilityNorms eq.1 eq.2 := by
  let eq := positiveEquilibrium p ⟨ha, hb⟩
  let M0 := unitIntervalNormalizedResolverGradientConstant p
  have hcond : NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 :=
    Or.inr (Or.inr (Or.inl ⟨hm, hγ, hrel, by simpa [eq, M0] using hχ⟩))
  have hstable : LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
    simpa [eq] using hcond.linearlyStable_unitInterval p ha hb
  exact intervalDomainM_eventualGlobal_of_globallyAsymptotic p ha
    (by simpa [eq] using paper3ConstantEquilibrium_positive p ha hb) hstable
    (intervalDomainM_strong3_globallyAsymptoticallyStableNonminimal
      p hm ha hb hγ hrel hχ hchiNonpos)

/-- Unconditional-in-`χ₀>0` fourth branch of faithful eventual Theorem 2.4
(general `m`); `χ₀ ≤ 0` supplied as a frontier. -/
theorem intervalDomainM_eventuallyGloballyExponentiallyStableNonminimal_strong4
    (p : CM2Params) (hm : 1 ≤ p.m)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hβ : 1 ≤ p.β) (hγ : 1 ≤ p.γ)
    (hrel : p.α + 1 ≥ p.m + 2 * p.γ)
    (hχ : p.χ₀ < chiStrong4Formula p
      (unitIntervalNormalizedResolverGradientConstant p)
      (positiveEquilibrium p ⟨ha, hb⟩).1)
    (hchiNonpos : p.χ₀ ≤ 0 →
      GloballyAsymptoticallyStableNonminimal intervalDomainM p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    EventuallyGloballyExponentiallyStableNonminimal intervalDomainM p
      intervalDomainMSectorialStabilityNorms eq.1 eq.2 := by
  let eq := positiveEquilibrium p ⟨ha, hb⟩
  let M0 := unitIntervalNormalizedResolverGradientConstant p
  have hcond : NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 :=
    Or.inr (Or.inr (Or.inr ⟨hm, hβ, hγ, hrel, by simpa [eq, M0] using hχ⟩))
  have hstable : LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
    simpa [eq] using hcond.linearlyStable_unitInterval p ha hb
  exact intervalDomainM_eventualGlobal_of_globallyAsymptotic p ha
    (by simpa [eq] using paper3ConstantEquilibrium_positive p ha hb) hstable
    (intervalDomainM_strong4_globallyAsymptoticallyStableNonminimal
      p hm ha hb hβ hγ hrel hχ hchiNonpos)

#print axioms intervalDomainM_rectangleLogGapSlopeBound_with_weight_le_strong3
#print axioms intervalDomainM_rectangleLogGap_tendsto_zero_strong3
#print axioms intervalDomainM_rectangleLogGap_tendsto_zero_strong4
#print axioms intervalDomainM_uniformConvergesInSup_of_rectangleLogGap
#print axioms intervalDomainM_eventuallyGloballyExponentiallyStableNonminimal_strong3
#print axioms intervalDomainM_eventuallyGloballyExponentiallyStableNonminimal_strong4

end

end ShenWork.Paper3
