import Mathlib

/-!
# Chemotaxis flux cosine-divergence bookkeeping (χ₀ < 0 crux, elementary IBP)

The HSpectral crux `SourceFromSolutionEnvelopePass` needs the divergence source
`S_chem = ∂ₓQ` to gain one order of coefficient decay over the flux `Q`.  The
mechanism is the elementary interval integration-by-parts

  ∫₀¹ Q'(x) cos(kπx) dx = [Q cos(kπx)]₀¹ + kπ ∫₀¹ Q(x) sin(kπx) dx,

so once the truncated flux `Q = ρ₊(u)·∂ₓR·(1+R)^{-β}` vanishes at the endpoints
(which it does, because `∂ₓR(0)=∂ₓR(1)=0` for the Neumann resolver `R`), the
boundary bracket dies and

  cosCoeff(Q', k) = kπ · sineCoeff(Q, k),   |cosCoeff(∂ₓQ,k)| ≤ kπ·|sineCoeff(Q,k)|.

This is the ChatGPT-verified (Q4352) bookkeeping, formalized here as standalone
`0`-sorry lemmas that the crux imports.  Self-contained: depends only on Mathlib.
-/

namespace ShenWork.Paper2.ChemFluxCosineDivergence

open Real MeasureTheory intervalIntegral

/-- **Interval IBP against `cos(kπ·)`** (general boundary form).

For `Q` differentiable on `[0,1]` with interval-integrable derivative,
`∫₀¹ Q'·cos(kπx) = [Q·cos(kπx)]₀¹ + kπ·∫₀¹ Q·sin(kπx)`. -/
theorem integral_deriv_mul_cos
    {Q Q' : ℝ → ℝ} {k : ℕ}
    (hQ : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Q (Q' x) x)
    (hQ' : IntervalIntegrable Q' volume 0 1) :
    (∫ x in (0 : ℝ)..1, Q' x * Real.cos (k * Real.pi * x))
      = (Q 1 * Real.cos (k * Real.pi) - Q 0 * Real.cos (k * Real.pi * 0))
        + (k * Real.pi) * ∫ x in (0 : ℝ)..1, Q x * Real.sin (k * Real.pi * x) := by
  -- v(x) = cos(kπx),  v'(x) = -(kπ)·sin(kπx)
  set c : ℝ := (k : ℝ) * Real.pi with hc
  have hv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun x => Real.cos (c * x)) (-(c * Real.sin (c * x))) x := by
    intro x _
    have hlin : HasDerivAt (fun x : ℝ => c * x) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    have h := (Real.hasDerivAt_cos (c * x)).comp x hlin
    -- h : HasDerivAt (Real.cos ∘ fun x => c*x) (-Real.sin (c*x) * c) x
    have heq : -Real.sin (c * x) * c = -(c * Real.sin (c * x)) := by ring
    rw [heq] at h
    exact h
  have hvcont : Continuous (fun x : ℝ => -(c * Real.sin (c * x))) := by
    fun_prop
  have hv' : IntervalIntegrable (fun x => -(c * Real.sin (c * x))) volume 0 1 :=
    hvcont.intervalIntegrable _ _
  -- IBP: ∫ Q · v' = Q·v |₀¹ - ∫ Q' · v
  have IBP := integral_mul_deriv_eq_deriv_mul hQ hv hQ' hv'
  -- LHS of IBP: ∫ Q x * (-(c·sin (c x))) = -(c) * ∫ Q·sin
  have hpull : (∫ x in (0 : ℝ)..1, Q x * -(c * Real.sin (c * x)))
      = -(c) * ∫ x in (0 : ℝ)..1, Q x * Real.sin (c * x) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x; ring
  rw [hpull] at IBP
  -- IBP : -c * ∫ Q sin = Q 1 * cos(c·1) - Q 0 * cos(c·0) - ∫ Q' cos(c·)
  -- solve for ∫ Q' cos
  have : (∫ x in (0 : ℝ)..1, Q' x * Real.cos (c * x))
      = (Q 1 * Real.cos (c * 1) - Q 0 * Real.cos (c * 0)) + c * ∫ x in (0 : ℝ)..1, Q x * Real.sin (c * x) := by
    linarith [IBP]
  simpa [hc, mul_one] using this

/-- **Endpoint vanishing of the truncated chemotaxis flux.**

`Q = u·(∂ₓR)·(1+R)^{-β}` vanishes wherever `∂ₓR` vanishes — in particular at the
Neumann endpoints `x=0,1` where the resolver satisfies `∂ₓR(0)=∂ₓR(1)=0`. -/
theorem chemFlux_zero_of_resolverGrad_zero
    {u R Rx : ℝ → ℝ} {β x : ℝ} (hRx : Rx x = 0) :
    u x * Rx x * (1 + R x) ^ (-β) = 0 := by
  simp [hRx]

/-- **The cosine-divergence identity with vanishing boundary** (the crux step).

If the flux `Q` vanishes at both endpoints (`Q 0 = Q 1 = 0`), the boundary bracket
dies and `∫₀¹ Q'·cos(kπx) = kπ·∫₀¹ Q·sin(kπx)`: the divergence source gains
exactly one factor of `k`. -/
theorem cosineCoeff_deriv_eq_kpi_sineCoeff
    {Q Q' : ℝ → ℝ} {k : ℕ}
    (hQ : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Q (Q' x) x)
    (hQ' : IntervalIntegrable Q' volume 0 1)
    (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0) :
    (∫ x in (0 : ℝ)..1, Q' x * Real.cos (k * Real.pi * x))
      = (k * Real.pi) * ∫ x in (0 : ℝ)..1, Q x * Real.sin (k * Real.pi * x) := by
  rw [integral_deriv_mul_cos hQ hQ', hQ0, hQ1]
  ring

/-- **Zero-mode: `∫₀¹ Q' = 0`** when `Q` vanishes at both endpoints (FTC). -/
theorem integral_deriv_zero_of_endpoints
    {Q Q' : ℝ → ℝ}
    (hQ : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Q (Q' x) x)
    (hQ' : IntervalIntegrable Q' volume 0 1)
    (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0) :
    (∫ x in (0 : ℝ)..1, Q' x) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hQ hQ', hQ0, hQ1, sub_zero]

/-- **Sine-coefficient IBP** (no-division form): for `Q` with `Q 0 = Q 1 = 0`,
`kπ · ∫₀¹ Q·sin(kπx) = ∫₀¹ Q'·cos(kπx)`.  IBP against `v = -cos(kπ·)`, `v' = kπ·sin`. -/
theorem kpi_mul_integral_mul_sin
    {Q Q' : ℝ → ℝ} {k : ℕ}
    (hQ : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Q (Q' x) x)
    (hQ' : IntervalIntegrable Q' volume 0 1)
    (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0) :
    (k * Real.pi) * (∫ x in (0 : ℝ)..1, Q x * Real.sin (k * Real.pi * x))
      = ∫ x in (0 : ℝ)..1, Q' x * Real.cos (k * Real.pi * x) := by
  set c : ℝ := (k : ℝ) * Real.pi with hc
  -- v(x) = -cos(c x),  v'(x) = c·sin(c x)
  have hv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun x => -Real.cos (c * x)) (c * Real.sin (c * x)) x := by
    intro x _
    have hlin : HasDerivAt (fun x : ℝ => c * x) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    have h := ((Real.hasDerivAt_cos (c * x)).comp x hlin).neg
    have heq : -(-Real.sin (c * x) * c) = c * Real.sin (c * x) := by ring
    rwa [heq] at h
  have hv' : IntervalIntegrable (fun x => c * Real.sin (c * x)) volume 0 1 :=
    (by fun_prop : Continuous (fun x => c * Real.sin (c * x))).intervalIntegrable _ _
  have IBP := integral_mul_deriv_eq_deriv_mul hQ hv hQ' hv'
  rw [hQ0, hQ1] at IBP
  -- IBP : ∫ Q x * (c*sin) = 0*(-cos c) - 0*(-cos 0) - ∫ Q' x * (-cos)
  have hpullL : (∫ x in (0 : ℝ)..1, Q x * (c * Real.sin (c * x)))
      = c * ∫ x in (0 : ℝ)..1, Q x * Real.sin (c * x) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext x; ring
  have hpullR : (∫ x in (0 : ℝ)..1, Q' x * -Real.cos (c * x))
      = - ∫ x in (0 : ℝ)..1, Q' x * Real.cos (c * x) := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext x; ring
  rw [hpullL, hpullR] at IBP
  simp only [zero_mul, sub_zero, zero_sub, neg_neg] at IBP
  exact IBP

/-- **Flux sine-coefficient decay** (order 1): with `Q 0 = Q 1 = 0` and `|Q'| ≤ B`,
`|∫₀¹ Q·sin(kπx)| ≤ B/(kπ)`.  Paired with `cosineCoeff_deriv_eq_kpi_sineCoeff`, this
is the flux half of the source-order ledger (`∂ₓQ` source ← flux `Q` sine decay). -/
theorem sineCoeff_abs_le_of_deriv_bound
    {Q Q' : ℝ → ℝ} {k : ℕ} {B : ℝ} (hk : 1 ≤ k)
    (hQ : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Q (Q' x) x)
    (hQ' : IntervalIntegrable Q' volume 0 1)
    (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0)
    (hB : ∀ x ∈ Set.uIcc (0 : ℝ) 1, |Q' x| ≤ B) :
    |∫ x in (0 : ℝ)..1, Q x * Real.sin (k * Real.pi * x)| ≤ B / (k * Real.pi) := by
  have hkpos : 0 < (k : ℝ) * Real.pi := by
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
    positivity
  -- pointwise norm bound on the integrand Q'·cos
  have hbd : ∀ x ∈ Set.uIoc (0 : ℝ) 1,
      ‖Q' x * Real.cos (k * Real.pi * x)‖ ≤ B := by
    intro x hx
    have hxIcc : x ∈ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
      exact Set.Ioc_subset_Icc_self hx
    have hb := hB x hxIcc
    rw [Real.norm_eq_abs, abs_mul]
    calc |Q' x| * |Real.cos (k * Real.pi * x)|
        ≤ B * 1 :=
          mul_le_mul hb (Real.abs_cos_le_one _) (abs_nonneg _)
            (le_trans (abs_nonneg _) hb)
      _ = B := mul_one B
  -- |∫ Q' cos| ≤ B
  have hcosbd : |∫ x in (0 : ℝ)..1, Q' x * Real.cos (k * Real.pi * x)| ≤ B := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    simpa [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h
  -- kπ·|∫Q sin| = |∫Q'cos| ≤ B  ⇒  |∫Q sin| ≤ B/(kπ)
  have hid := kpi_mul_integral_mul_sin (k := k) hQ hQ' hQ0 hQ1
  have habs : (k * Real.pi) * |∫ x in (0 : ℝ)..1, Q x * Real.sin (k * Real.pi * x)|
      = |∫ x in (0 : ℝ)..1, Q' x * Real.cos (k * Real.pi * x)| := by
    calc (k * Real.pi) * |∫ x in (0 : ℝ)..1, Q x * Real.sin (k * Real.pi * x)|
        = |k * Real.pi| * |∫ x in (0 : ℝ)..1, Q x * Real.sin (k * Real.pi * x)| := by
            rw [abs_of_pos hkpos]
      _ = |(k * Real.pi) * ∫ x in (0 : ℝ)..1, Q x * Real.sin (k * Real.pi * x)| :=
            (abs_mul _ _).symm
      _ = |∫ x in (0 : ℝ)..1, Q' x * Real.cos (k * Real.pi * x)| := by rw [hid]
  have hle : (k * Real.pi) * |∫ x in (0 : ℝ)..1, Q x * Real.sin (k * Real.pi * x)| ≤ B :=
    habs ▸ hcosbd
  rw [le_div_iff₀ hkpos, mul_comm]
  exact hle

end ShenWork.Paper2.ChemFluxCosineDivergence
