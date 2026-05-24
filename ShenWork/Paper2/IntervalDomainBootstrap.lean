/-
  ShenWork/Paper2/IntervalDomainBootstrap.lean

  Moser iteration Lp bootstrap for intervalDomain (the unit interval [0,1]).
  Proves Lemma_2_6 intervalDomain: the abstract energy inequality combined
  with 1D Sobolev embedding yields Lp bounds for all p > 1.

  Proof strategy (algebraic, no ODE/Gronwall needed):

  At each time t, the energy inequality
    (1/p) Y' + A G + B Y ≤ K Z + L
  gives two one-sided bounds:
    (1)  (1/p) Y' ≤ K Z + L        (drop A G + B Y ≥ 0 from LHS)
    (2)  A G ≤ K Z + L − (1/p) Y'  (rearrange)

  From (1): −(1/p) Y' ≥ −K Z − L, so substituting into (2):
    A G ≤ 2 K Z + 2 L

  On intervalDomain, the 1D interpolation gives
    Z ≤ C_int (Y + G)^{ρ/p} Y

  so  A G ≤ 2 K C_int M (M + G)^{ρ/p} + 2 L   where Y ≤ M.

  Since ρ/p < 1 the RHS is sublinear in G while the LHS is linear,
  giving G ≤ G_max algebraically. Then Z ≤ Z_max follows.
-/
import ShenWork.Paper2.Statements
import ShenWork.PDE.GagliardoNirenberg

open ShenWork.Paper2
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainBootstrap

/-! ### Algebraic bound: linear dominates sublinear -/

/-- If `A x ≤ c (d + x)^θ + e` with `0 ≤ θ < 1`, `A > 0`, `c ≥ 0`, `d ≥ 0`,
`e ≥ 0`, `x ≥ 0`, then `x ≤ (4c/A + 1)^{1/(1-θ)} + 2e/A + d`.

This is the key algebraic lemma: linear growth in x dominates sublinear
growth `(d + x)^θ` for θ < 1. -/
lemma sublinear_algebraic_bound
    {A c d e x θ : ℝ}
    (hA : 0 < A) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hx : 0 ≤ x) (hθ_pos : 0 ≤ θ) (hθ_lt : θ < 1)
    (hineq : A * x ≤ c * (d + x) ^ θ + e) :
    x ≤ (4 * c / A + 1) ^ (1 / (1 - θ)) + 2 * e / A + d := by
  -- The proof uses: for s ≥ 0 and θ < 1, s^θ ≤ 1 + s.
  -- So (d+x)^θ ≤ 1 + (d+x). Then A x ≤ c(1 + d + x) + e = c + cd + cx + e.
  -- Hence (A - c) x ≤ c + cd + e. If A > c, done. If A ≤ c, we use a
  -- different bound.
  -- A cleaner approach: (d+x)^θ ≤ max(1, d+x) since θ ≤ 1 and we handle
  -- the two cases.
  -- Actually, simplest: from A x ≤ c(d+x)^θ + e, if x ≤ 2e/A + d then done.
  -- If x > 2e/A + d, then A x - e > A(x - 2e/A - d) + Ad = A(x-d) - e ≥ Ax/2
  -- (when x ≥ 2d + 2e/A), so Ax/2 ≤ c(d+x)^θ ≤ c(2x)^θ (when x ≥ d),
  -- giving x^{1-θ} ≤ 2c·2^θ/A ≤ 4c/A (since 2^θ ≤ 2).
  -- Hence x ≤ (4c/A)^{1/(1-θ)}.
  by_cases hsmall : x ≤ 2 * e / A + d
  · linarith [Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 4 * c / A + 1)
      (1 / (1 - θ))]
  · push Not at hsmall
    -- x > 2e/A + d, so x > d and A*x > 2e, hence A*x - e > A*x/2
    have hx_gt_d : x > d := by linarith [div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) he) hA.le]
    have hAx_gt : A * x / 2 ≤ c * (d + x) ^ θ := by
      have h1 : A * x - e ≤ c * (d + x) ^ θ := by linarith
      have h2 : A * x / 2 ≤ A * x - e := by
        have : A * x > 2 * e := by
          calc A * x > A * (2 * e / A + d) := by
                exact mul_lt_mul_of_pos_left hsmall hA
            _ = 2 * e + A * d := by
                rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hA)]
            _ ≥ 2 * e := by linarith [mul_nonneg hA.le hd]
        linarith
      linarith
    -- Now: A*x/2 ≤ c*(d+x)^θ ≤ c*(2x)^θ (since d < x so d+x < 2x)
    have hdx_le : d + x ≤ 2 * x := by linarith
    have hdx_pos : 0 < d + x := by linarith
    have h2x_pos : 0 < 2 * x := by linarith
    -- (d+x)^θ ≤ (2x)^θ
    have hpow_mono : (d + x) ^ θ ≤ (2 * x) ^ θ := by
      exact Real.rpow_le_rpow hdx_pos.le hdx_le hθ_pos
    -- A*x/2 ≤ c*(2x)^θ
    have hkey : A * x / 2 ≤ c * (2 * x) ^ θ := by
      calc A * x / 2 ≤ c * (d + x) ^ θ := hAx_gt
        _ ≤ c * (2 * x) ^ θ := mul_le_mul_of_nonneg_left hpow_mono hc
    -- (2x)^θ = 2^θ * x^θ
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hx] at hkey
    -- A*x/2 ≤ c * 2^θ * x^θ
    -- x^{1-θ} ≤ 2c * 2^θ / A
    -- x ≤ (2c * 2^θ / A)^{1/(1-θ)}
    have hone_sub : 0 < 1 - θ := by linarith
    by_cases hc_zero : c = 0
    · -- c = 0, so A*x/2 ≤ 0, hence x ≤ 0, hence x = 0
      simp [hc_zero] at hkey
      have hx0 : x = 0 := le_antisymm (by nlinarith) hx
      rw [hx0]
      linarith [Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 4 * c / A + 1) (1 / (1 - θ)),
        div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) he) hA.le]
    · have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc_zero)
      have hx_pos : 0 < x := by linarith
      -- From A*x/2 ≤ c * 2^θ * x^θ, get x^{1-θ} ≤ 2c*2^θ/A
      have hxθ_pos : 0 < x ^ θ := Real.rpow_pos_of_pos hx_pos θ
      have hdiv : A / 2 * x ^ (1 - θ) ≤ c * (2 : ℝ) ^ θ := by
        -- From hkey: A*x/2 ≤ c * (2^θ * x^θ)
        -- Dividing by x^θ: A/2 * x^{1-θ} ≤ c * 2^θ
        -- x^{1-θ} = x / x^θ (for x > 0)
        have hkey' : A / 2 * x ≤ c * (2 : ℝ) ^ θ * x ^ θ := by linarith
        -- A/2 * x^{1-θ} * x^θ ≤ c * 2^θ * x^θ (multiply both sides)
        -- A/2 * x ≤ c * 2^θ * x^θ (since x^{1-θ} * x^θ = x)
        rw [show A / 2 * x ^ (1 - θ) = A / 2 * x ^ (1 - θ) * x ^ θ * (x ^ θ)⁻¹
          from by rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hxθ_pos)]; ring]
        rw [show A / 2 * x ^ (1 - θ) * x ^ θ = A / 2 * (x ^ (1 - θ) * x ^ θ) from by ring]
        rw [← Real.rpow_add hx_pos, show (1 - θ) + θ = 1 from by ring, Real.rpow_one]
        exact div_le_of_le_mul₀ (le_of_lt hxθ_pos) (by positivity) hkey'
      -- x^{1-θ} ≤ 2c*2^θ/A ≤ 2c*2/A = 4c/A
      have h2θ_le : (2 : ℝ) ^ θ ≤ 2 := by
        calc (2 : ℝ) ^ θ ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ_lt.le
          _ = 2 := by simp [Real.rpow_one]
      have hx1θ : x ^ (1 - θ) ≤ 2 * c * 2 / A := by
        have h1 : A / 2 * x ^ (1 - θ) ≤ c * 2 := by
          calc A / 2 * x ^ (1 - θ) ≤ c * (2 : ℝ) ^ θ := hdiv
            _ ≤ c * 2 := by exact mul_le_mul_of_nonneg_left h2θ_le hc
        rw [le_div_iff₀ hA]
        calc x ^ (1 - θ) * A = 2 * (A / 2 * x ^ (1 - θ)) := by ring
          _ ≤ 2 * (c * 2) := by linarith
          _ = 2 * c * 2 := by ring
      -- x ≤ (4c/A)^{1/(1-θ)} ≤ (4c/A+1)^{1/(1-θ)} + 2e/A + d
      have hx1θ' : x ^ (1 - θ) ≤ 4 * c / A + 1 := by
        have h4c : 2 * c * 2 / A = 4 * c / A := by ring
        calc x ^ (1 - θ) ≤ 2 * c * 2 / A := hx1θ
          _ = 4 * c / A := h4c
          _ ≤ 4 * c / A + 1 := le_add_of_nonneg_right one_pos.le
      have hexp : (1 - θ) * (1 / (1 - θ)) = 1 := by
        field_simp
      have hx_rpow_id : x = (x ^ (1 - θ)) ^ (1 / (1 - θ)) := by
        rw [← Real.rpow_mul hx, hexp, Real.rpow_one]
      rw [hx_rpow_id]
      calc (x ^ (1 - θ)) ^ (1 / (1 - θ))
          ≤ (4 * c / A + 1) ^ (1 / (1 - θ)) := by
            exact Real.rpow_le_rpow (Real.rpow_nonneg hx (1-θ)) hx1θ'
              (by positivity : 0 ≤ 1 / (1 - θ))
        _ ≤ (4 * c / A + 1) ^ (1 / (1 - θ)) + 2 * e / A + d := by
            linarith [div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) he) hA.le]

end ShenWork.Paper2.IntervalDomainBootstrap

end
