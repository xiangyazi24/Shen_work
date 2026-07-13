import ShenWork.Paper2.IntervalDomainTheorem13CriticalSeed

/-!
# Scalar threshold selection for Paper 2, Theorem 1.3

This file converts the literal critical thresholds (1.24)--(1.25) into a
finite exponent immediately to the right of `q_*`.  Alternative (iii) is
valid on the full stated parameter range.  Alternative (iv) requires the
additional exponent-domain condition `q_* > 2 - 2m`; this is exactly the
condition needed to invoke Proposition 2.2 at `(q_* + alpha) / gamma > 1`.
-/

open Filter Set Topology
open scoped Topology
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainTheorem13CriticalThreshold

open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainTheorem13CriticalConstants
open ShenWork.Paper2.IntervalDomainTheorem13CriticalSeed

lemma exists_right_of_continuousAt_lt
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousAt f a) (hab : f a < b) :
    ∃ x, a < x ∧ f x < b := by
  have hev : ∀ᶠ x in 𝓝[>] a, f x < b :=
    (hf.tendsto.mono_left inf_le_left).eventually (Iio_mem_nhds hab)
  have hright : ∀ᶠ x in 𝓝[>] a, a < x := self_mem_nhdsWithin
  have hboth : ∀ᶠ x in 𝓝[>] a, a < x ∧ f x < b := by
    filter_upwards [hright, hev] with x hx hfx
    exact ⟨hx, hfx⟩
  exact hboth.exists

lemma criticalCaseIIICoefficient_continuousAt
    (p : CM2Params) {P : ℝ}
    (hden : P - 1 + p.m ≠ 0)
    (hs : 1 < (P + p.α) / p.γ) :
    ContinuousAt (criticalCaseIIICoefficient p) P := by
  unfold criticalCaseIIICoefficient
  exact
    ((continuousAt_const.mul (continuousAt_id.sub continuousAt_const)).div
      (continuousAt_id.sub continuousAt_const |>.add continuousAt_const)
      hden).mul
      (continuousAt_const.add
        (continuousAt_const.mul
          (theorem13CriticalProfile_continuousAt p hs)))

lemma criticalCaseIVCoefficient_continuousAt
    (p : CM2Params) {P : ℝ}
    (hs : 1 < (P + p.α) / p.γ) :
    ContinuousAt (criticalCaseIVCoefficient p) P := by
  unfold criticalCaseIVCoefficient
  exact
    ((((continuousAt_id.sub continuousAt_const).mul continuousAt_const).div_const 4).mul
      continuousAt_const).mul (theorem13CriticalProfile_continuousAt p hs)

lemma case_iii_qstar_prop_exponent
    (p : CM2Params) (_hN : p.N = 1)
    (hcrit : p.α = p.m + p.γ - 1) :
    1 < (theorem13CriticalQStar p + p.α) / p.γ := by
  have hq : 1 ≤ theorem13CriticalQStar p :=
    one_le_theorem13CriticalQStar p
  rw [one_lt_div p.hγ]
  rw [hcrit]
  linarith [p.hm]

lemma case_iii_qstar_coefficient_lt
    (p : CM2Params) (hN : p.N = 1)
    (hb : 0 < p.b) (hchi : 0 < p.χ₀) (hbeta : 0 ≤ p.β)
    (hcrit : p.α = p.m + p.γ - 1)
    (hthreshold :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          ((positivePart ((p.N : ℝ) * p.α - 2) + 2 * p.m) * p.b) /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              (p.ν + Psi_beta p.β * theorem13CriticalK p))) :
    criticalCaseIIICoefficient p (theorem13CriticalQStar p) < p.b := by
  let d : ℝ := positivePart (p.α - 2)
  have hd : positivePart ((p.N : ℝ) * p.α - 2) = d := by
    simp [d, hN]
  rw [hd] at hthreshold
  have hs := case_iii_qstar_prop_exponent p hN hcrit
  have hK := theorem13CriticalK_eq_profile p hs
  have hqeq := theorem13CriticalQStar_eq_interval p hN
  by_cases hd0 : d = 0
  · have ha : p.α ≤ 2 := by
      have := positivePart_eq_zero_iff.mp (by simpa [d] using hd0)
      linarith
    have hmax : max 1 (p.α / 2) = 1 := max_eq_left (by linarith)
    rw [hqeq, hmax]
    simpa [criticalCaseIIICoefficient] using hb
  · have hdpos : 0 < d := lt_of_le_of_ne (positivePart_nonneg _) (Ne.symm hd0)
    have ha2 : 2 < p.α := by
      have := positivePart_pos_iff.mp (by simpa [d] using hdpos)
      linarith
    have hdeq : d = p.α - 2 := by
      dsimp [d]
      exact positivePart_eq_self_of_nonneg (by linarith)
    have hmax : max 1 (p.α / 2) = p.α / 2 := max_eq_right (by linarith)
    have hth := hthreshold.resolve_left hd0
    rw [hK] at hth
    have hpsi : 0 ≤ Psi_beta p.β := Psi_beta_nonneg hbeta
    have hprof : 0 < theorem13CriticalProfile p (theorem13CriticalQStar p) :=
      theorem13CriticalProfile_pos p hs
    have hA : 0 < p.ν + Psi_beta p.β *
        theorem13CriticalProfile p (theorem13CriticalQStar p) := by
      exact add_pos_of_pos_of_nonneg p.hν (mul_nonneg hpsi hprof.le)
    have hdm : 0 < d + 2 * p.m := by linarith [p.hm]
    have hmul := (lt_div_iff₀ (mul_pos hdpos hA)).mp hth
    have htarget :
        p.χ₀ * d / (d + 2 * p.m) *
            (p.ν + Psi_beta p.β *
              theorem13CriticalProfile p (theorem13CriticalQStar p)) < p.b := by
      rw [div_mul_eq_mul_div]
      exact (div_lt_iff₀ hdm).2 (by nlinarith)
    rw [hqeq, hmax]
    dsimp [criticalCaseIIICoefficient]
    rw [hqeq, hmax, hdeq] at htarget
    have hdenP : 0 < p.α / 2 - 1 + p.m := by linarith [p.hm]
    have hdenD : 0 < p.α - 2 + 2 * p.m := by linarith [p.hm]
    convert htarget using 1
    field_simp [hdenP.ne', hdenD.ne']

lemma case_iv_qstar_prop_exponent
    (p : CM2Params)
    (hvalid : 2 - 2 * p.m < theorem13CriticalQStar p)
    (hcrit : p.α = 2 * p.m + p.γ - 2) :
    1 < (theorem13CriticalQStar p + p.α) / p.γ := by
  rw [one_lt_div p.hγ]
  rw [hcrit]
  linarith

theorem exists_case_iii_seed_exponent
    (p : CM2Params) (hN : p.N = 1)
    (hb : 0 < p.b) (hchi : 0 < p.χ₀) (hbeta : 0 ≤ p.β)
    (hcrit : p.α = p.m + p.γ - 1)
    (hthreshold :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          ((positivePart ((p.N : ℝ) * p.α - 2) + 2 * p.m) * p.b) /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              (p.ν + Psi_beta p.β * theorem13CriticalK p))) :
    ∃ P, theorem13CriticalQStar p < P ∧
      criticalCaseIIICoefficient p P < p.b := by
  let qstar := theorem13CriticalQStar p
  have hs : 1 < (qstar + p.α) / p.γ :=
    case_iii_qstar_prop_exponent p hN hcrit
  have hden : qstar - 1 + p.m ≠ 0 := by
    have hq := one_le_theorem13CriticalQStar p
    exact ne_of_gt (by dsimp [qstar]; linarith [p.hm])
  have hcont : ContinuousAt (criticalCaseIIICoefficient p) qstar :=
    criticalCaseIIICoefficient_continuousAt p hden hs
  have hlt : criticalCaseIIICoefficient p qstar < p.b :=
    case_iii_qstar_coefficient_lt p hN hb hchi hbeta hcrit hthreshold
  exact exists_right_of_continuousAt_lt hcont hlt

theorem critical_case_iii_threshold_lp_seed
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hN : p.N = 1) (hb : 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hchi : 0 < p.χ₀) (hbeta : 0 ≤ p.β)
    (hcrit : p.α = p.m + p.γ - 1)
    (hthreshold :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          ((positivePart ((p.N : ℝ) * p.α - 2) + 2 * p.m) * p.b) /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              (p.ν + Psi_beta p.β * theorem13CriticalK p))) :
    ∃ P, theorem13CriticalQStar p < P ∧
      LpPowerBoundedBefore intervalDomainM P T u := by
  obtain ⟨P, hqP, hcoef⟩ := exists_case_iii_seed_exponent
    p hN hb hchi hbeta hcrit hthreshold
  have hP : 1 < P :=
    lt_of_le_of_lt (one_le_theorem13CriticalQStar p) hqP
  exact ⟨P, hqP, critical_case_iii_lp_power_bounded_before
    hu₀ hsol htrace hchi hbeta hcrit hP hcoef⟩

lemma case_iv_qstar_coefficient_lt
    (p : CM2Params) (hN : p.N = 1)
    (hb : 0 < p.b) (hchi : 0 < p.χ₀)
    (hbeta : (1 / 2 : ℝ) ≤ p.β)
    (hcrit : p.α = 2 * p.m + p.γ - 2)
    (hvalid : 2 - 2 * p.m < theorem13CriticalQStar p)
    (hthreshold :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ < Real.sqrt
          (8 * p.b /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              Theta_beta (2 * p.β - 1) * theorem13CriticalK p))) :
    criticalCaseIVCoefficient p (theorem13CriticalQStar p) < p.b := by
  let d : ℝ := positivePart (p.α - 2)
  have hd : positivePart ((p.N : ℝ) * p.α - 2) = d := by
    simp [d, hN]
  rw [hd] at hthreshold
  have hs := case_iv_qstar_prop_exponent p hvalid hcrit
  have hK := theorem13CriticalK_eq_profile p hs
  have hqeq := theorem13CriticalQStar_eq_interval p hN
  by_cases hd0 : d = 0
  · have ha : p.α ≤ 2 := by
      have := positivePart_eq_zero_iff.mp (by simpa [d] using hd0)
      linarith
    have hmax : max 1 (p.α / 2) = 1 := max_eq_left (by linarith)
    rw [hqeq, hmax]
    simpa [criticalCaseIVCoefficient] using hb
  · have hdpos : 0 < d := lt_of_le_of_ne (positivePart_nonneg _) (Ne.symm hd0)
    have ha2 : 2 < p.α := by
      have := positivePart_pos_iff.mp (by simpa [d] using hdpos)
      linarith
    have hdeq : d = p.α - 2 := by
      dsimp [d]
      exact positivePart_eq_self_of_nonneg (by linarith)
    have hmax : max 1 (p.α / 2) = p.α / 2 := max_eq_right (by linarith)
    have hth := hthreshold.resolve_left hd0
    rw [hK] at hth
    let theta : ℝ := Theta_beta (2 * p.β - 1)
    have hbeta' : 0 ≤ 2 * p.β - 1 := by linarith
    have htheta : 0 < theta := Theta_beta_pos_of_nonneg hbeta'
    have hprof : 0 < theorem13CriticalProfile p (theorem13CriticalQStar p) :=
      theorem13CriticalProfile_pos p hs
    have hden : 0 < d * theta *
        theorem13CriticalProfile p (theorem13CriticalQStar p) := by
      exact mul_pos (mul_pos hdpos htheta) hprof
    have hR : 0 < 8 * p.b /
        (d * theta * theorem13CriticalProfile p (theorem13CriticalQStar p)) :=
      div_pos (by positivity) hden
    have hsqrt_sq : (Real.sqrt
        (8 * p.b /
          (d * theta * theorem13CriticalProfile p
            (theorem13CriticalQStar p)))) ^ 2 =
        8 * p.b /
          (d * theta * theorem13CriticalProfile p
            (theorem13CriticalQStar p)) := by
      exact Real.sq_sqrt hR.le
    have hchisq : p.χ₀ ^ 2 < 8 * p.b /
        (d * theta * theorem13CriticalProfile p
          (theorem13CriticalQStar p)) := by
      nlinarith [Real.sqrt_nonneg
        (8 * p.b /
          (d * theta * theorem13CriticalProfile p
            (theorem13CriticalQStar p)))]
    have hmul := (lt_div_iff₀ hden).mp hchisq
    have htarget : d * p.χ₀ ^ 2 / 8 * theta *
        theorem13CriticalProfile p (theorem13CriticalQStar p) < p.b := by
      have : d * p.χ₀ ^ 2 * theta *
          theorem13CriticalProfile p (theorem13CriticalQStar p) < 8 * p.b := by
        nlinarith
      nlinarith
    rw [hqeq, hmax]
    dsimp [criticalCaseIVCoefficient]
    rw [hqeq, hmax, hdeq] at htarget
    dsimp [theta] at htarget
    convert htarget using 1
    ring

theorem exists_case_iv_seed_exponent
    (p : CM2Params) (hN : p.N = 1)
    (hb : 0 < p.b) (hchi : 0 < p.χ₀)
    (hbeta : (1 / 2 : ℝ) ≤ p.β)
    (hcrit : p.α = 2 * p.m + p.γ - 2)
    (hvalid : 2 - 2 * p.m < theorem13CriticalQStar p)
    (hthreshold :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ < Real.sqrt
          (8 * p.b /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              Theta_beta (2 * p.β - 1) * theorem13CriticalK p))) :
    ∃ P, theorem13CriticalQStar p < P ∧
      2 - 2 * p.m < P ∧ criticalCaseIVCoefficient p P < p.b := by
  let qstar := theorem13CriticalQStar p
  have hs : 1 < (qstar + p.α) / p.γ :=
    case_iv_qstar_prop_exponent p hvalid hcrit
  have hcont : ContinuousAt (criticalCaseIVCoefficient p) qstar :=
    criticalCaseIVCoefficient_continuousAt p hs
  have hlt : criticalCaseIVCoefficient p qstar < p.b :=
    case_iv_qstar_coefficient_lt p hN hb hchi hbeta hcrit hvalid hthreshold
  obtain ⟨P, hqP, hcoef⟩ := exists_right_of_continuousAt_lt hcont hlt
  exact ⟨P, hqP, hvalid.trans hqP, hcoef⟩

theorem critical_case_iv_threshold_lp_seed
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hN : p.N = 1) (hb : 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hchi : 0 < p.χ₀) (hbeta : (1 / 2 : ℝ) ≤ p.β)
    (hcrit : p.α = 2 * p.m + p.γ - 2)
    (hvalid : 2 - 2 * p.m < theorem13CriticalQStar p)
    (hthreshold :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ < Real.sqrt
          (8 * p.b /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              Theta_beta (2 * p.β - 1) * theorem13CriticalK p))) :
    ∃ P, theorem13CriticalQStar p < P ∧
      LpPowerBoundedBefore intervalDomainM P T u := by
  obtain ⟨P, hqP, hvalidP, hcoef⟩ := exists_case_iv_seed_exponent
    p hN hb hchi hbeta hcrit hvalid hthreshold
  have hP : 1 < P :=
    lt_of_le_of_lt (one_le_theorem13CriticalQStar p) hqP
  exact ⟨P, hqP, critical_case_iv_lp_power_bounded_before
    hu₀ hsol htrace hbeta hcrit hP hvalidP hcoef⟩

#print axioms exists_right_of_continuousAt_lt
#print axioms exists_case_iii_seed_exponent
#print axioms critical_case_iii_threshold_lp_seed
#print axioms exists_case_iv_seed_exponent
#print axioms critical_case_iv_threshold_lp_seed

end ShenWork.Paper2.IntervalDomainTheorem13CriticalThreshold
