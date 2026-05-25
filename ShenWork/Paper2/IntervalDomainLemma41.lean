/-
  ShenWork/Paper2/IntervalDomainLemma41.lean

  Lemma 4.1 (L^p mass-gradient interpolation) for intervalDomain [0,1].

  The target inequality:
    ∫₀¹ u^p ≤ ε ∫₀¹ u^{p-2}|u'|² + C_ε (∫₀¹ u)^p

  Proof strategy:

  Setting Y = ∫u^p, G = ∫u^{p-2}|u'|², M = ∫u:

  (1) ∫u^p ≤ sup(u)^{p-1} · ∫u           (pointwise bound)
  (2) Young: sup^{p-1} · M ≤ δ sup^p + C_δ M^p
  (3) Agmon on u^{p/2}: sup^p ≤ 2Y + p√(YG)  (chain rule + Agmon)
  (4) Combine: Y ≤ 2δY + δp√(YG) + C_δ M^p
  (5) Absorb via AM-GM: Y ≤ [δ²p²/(1-2δ)²]G + [2C_δ/(1-2δ)]M^p

  Step (5) is `interpolation_absorption`, proved algebraically below.
  Steps (1)-(3) involve rpow and are captured by `IntervalDomainInterpolation`.

  Status: conditional on `IntervalDomainInterpolation` ⟹ Lemma_4_1 intervalDomain.
  The analytical hypotheses are stated; the bridge is proved.
  No proof holes, no axioms.
-/
import ShenWork.Paper2.Statements

open ShenWork.Paper2
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainLemma41

/-! ### Algebraic lemmas -/

/-- Quadratic absorption: if `a ≤ b √a + c` with `a, b, c ≥ 0`,
then `a ≤ b² + 2c`.

Proof: Young gives `b √a ≤ b²/2 + a/2`, so `a ≤ b²/2 + a/2 + c`,
hence `a/2 ≤ b²/2 + c`. -/
theorem quadratic_absorption {a b c : ℝ}
    (ha : 0 ≤ a) (_hb : 0 ≤ b) (_hc : 0 ≤ c)
    (h : a ≤ b * Real.sqrt a + c) :
    a ≤ b ^ 2 + 2 * c := by
  -- Young: b √a ≤ b²/2 + a/2   (from (b - √a)² ≥ 0)
  have hyoung : b * Real.sqrt a ≤ b ^ 2 / 2 + a / 2 := by
    have := sq_nonneg (b - Real.sqrt a)
    rw [sub_sq, Real.sq_sqrt ha] at this
    nlinarith
  linarith

/-- Full interpolation absorption: if
  `Y ≤ 2δY + δp√(YG) + C Mᵖ`
with `0 < δ < 1/4`, `Y, G, Mᵖ ≥ 0`, `p > 0`, `C ≥ 0`,
then
  `Y ≤ (δ²p²/(1-2δ)²) G + (2C/(1-2δ)) Mᵖ`.

This combines rearrangement with `quadratic_absorption`. -/
theorem interpolation_absorption {Y G Mp δ pv C : ℝ}
    (hY : 0 ≤ Y) (hG : 0 ≤ G) (hMp : 0 ≤ Mp)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1 / 4) (hp : 0 < pv)
    (hC : 0 ≤ C)
    (hineq : Y ≤ 2 * δ * Y + δ * pv * Real.sqrt (Y * G) + C * Mp) :
    Y ≤ δ ^ 2 * pv ^ 2 / (1 - 2 * δ) ^ 2 * G +
      2 * C / (1 - 2 * δ) * Mp := by
  have h1_2δ : 0 < 1 - 2 * δ := by linarith
  -- Rearrange: (1 - 2δ) Y ≤ δp √(YG) + C Mp
  have h1 : (1 - 2 * δ) * Y ≤ δ * pv * Real.sqrt (Y * G) + C * Mp := by
    linarith
  -- Divide by (1 - 2δ): Y ≤ δp/(1-2δ) √(YG) + C/(1-2δ) Mp
  have h2 : Y ≤ δ * pv / (1 - 2 * δ) * Real.sqrt (Y * G) +
      C / (1 - 2 * δ) * Mp := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
      ← add_div, le_div_iff₀ h1_2δ]
    linarith
  -- Factor √(YG) = √Y · √G
  rw [Real.sqrt_mul hY] at h2
  -- Rearrange into the form: Y ≤ B · √Y + C'
  have h3 : Y ≤ (δ * pv / (1 - 2 * δ) * Real.sqrt G) * Real.sqrt Y +
      C / (1 - 2 * δ) * Mp := by
    linarith [mul_assoc (δ * pv / (1 - 2 * δ)) (Real.sqrt G) (Real.sqrt Y),
      mul_comm (Real.sqrt G) (Real.sqrt Y)]
  -- Apply quadratic absorption: Y ≤ B² + 2C'
  have h4 := quadratic_absorption hY
    (mul_nonneg (div_nonneg (mul_nonneg hδ_pos.le hp.le) h1_2δ.le)
      (Real.sqrt_nonneg G))
    (mul_nonneg (div_nonneg hC h1_2δ.le) hMp) h3
  -- Simplify B² = δ²p²/(1-2δ)² · G
  have h5 : (δ * pv / (1 - 2 * δ) * Real.sqrt G) ^ 2 =
      δ ^ 2 * pv ^ 2 / (1 - 2 * δ) ^ 2 * G := by
    rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hG]
  have h6 : 2 * (C / (1 - 2 * δ) * Mp) = 2 * C / (1 - 2 * δ) * Mp := by ring
  linarith

/-! ### Interpolation hypothesis for intervalDomain

The hypothesis captures the Gagliardo-Nirenberg interpolation inequality
on the unit interval with UNIFORM constant C_ε (independent of the function).
This is a genuine analytical theorem about [0,1], provable from
Agmon's inequality + chain rule for rpow + Young's inequality.

Proof roadmap for the interested reader:

  Given ε > 0 and p > 1, choose δ = min(1/8, √ε/(2p)).

  For any positive f on [0,1]:

  (i)   Apply `agmon_inequality_interval` to g = f^{p/2}:
        g(x)² ≤ 2∫g² + 2√(∫g²)√(∫g'²)

  (ii)  Chain rule: g' = (p/2) f^{p/2-1} f', so
        ∫g'² = (p/2)² ∫f^{p-2}|f'|², and g(x)² = f(x)^p.

  (iii) f(x)^p ≤ 2Y + p√(YG) for all x ∈ [0,1], where Y = ∫f^p, G = ∫f^{p-2}|f'|².

  (iv)  Integrate f^p = f · f^{p-1} ≤ f · (2Y + p√(YG))^{(p-1)/p}.
        Then Y ≤ M · (2Y + p√(YG))^{(p-1)/p}.

  (v)   Apply scaled Young's inequality to separate:
        Y ≤ 2δ(p-1)/p · Y + δ(p-1) √(YG) + C_δ M^p

  (vi)  Apply `interpolation_absorption` to conclude
        Y ≤ εG + C_ε M^p.

  Steps (i)-(iii) require smoothness of f^{p/2} (HasDerivAt.rpow)
  and integrability.  Step (v) requires `Real.rpow_le_rpow`.
  These are available in Mathlib but require careful type-level work. -/

/-- The L^p mass-gradient interpolation inequality on the unit interval
with uniform constant.  For any ε > 0 and p > 1, there exists C_ε > 0
such that for ALL positive functions f on [0,1]:

  ∫f^p ≤ ε ∫f^{p-2}|f'|² + C_ε (∫f)^p

The constant C_ε depends only on ε and p, not on f. -/
def IntervalDomainInterpolation : Prop :=
  ∀ (eps : ℝ), 0 < eps → ∀ (pExp : ℝ), 1 < pExp → ∃ Ceps > 0,
    ∀ (f : intervalDomainPoint → ℝ),
      (∀ x, x ∈ intervalDomain.inside → 0 < f x) →
        intervalDomain.integral (fun x => (f x) ^ pExp) ≤
          eps * intervalDomain.integral
              (fun x => (f x) ^ (pExp - 2) *
                (intervalDomain.gradNorm f x) ^ 2) +
            Ceps * (intervalDomain.integral f) ^ pExp

/-- **Lemma 4.1 for intervalDomain**, conditional on the 1D interpolation
inequality.

The bridge is purely structural: the classical solution provides
positivity of u(t,·) on the interior for each t ∈ (0,T), and the
uniform C_ε from the interpolation hypothesis serves as the
existential witness.

This is an honest conditional result (playbook §3.1 item 17, state ③:
conditioned on `IntervalDomainInterpolation`, which is an unproved
but genuine analytical front). -/
theorem Lemma_4_1_intervalDomain_of_interpolation
    (hGN : IntervalDomainInterpolation)
    (p : CM2Params) :
    Lemma_4_1 intervalDomain p := by
  intro u₀ _hu₀ T _hT u v hsol _htrace eps heps pExp hpExp
  -- Extract the uniform constant from the interpolation hypothesis
  obtain ⟨Ceps, hCeps_pos, hinterp⟩ := hGN eps heps pExp hpExp
  -- Provide the witness
  refine ⟨Ceps, hCeps_pos, ?_⟩
  -- At each time t ∈ (0, T), u(t, ·) is positive on the interior
  intro t ht_pos ht_lt
  exact hinterp (u t) (fun x hx => hsol.2.2.1 t x ht_pos ht_lt hx)

end ShenWork.Paper2.IntervalDomainLemma41

end
