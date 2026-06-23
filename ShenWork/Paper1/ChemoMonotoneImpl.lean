/-
  ShenWork/Paper1/ChemoMonotoneImpl.lean

  **The chemotaxis-flux-defect SIGN brick (P1 #4-B core).**

  TARGET (the long-standing chemotaxis-monotonicity residual).  The carried
  obligation `RotheChemoMonotoneResidual` (WaveRotheOrder.lean:126) and its
  non-diagonal twin `crossSource_antitone_of_summands` (CrossSourceNonDiagonal.lean)
  both bottom out in ONE sign fact about the chemotaxis-flux defect

      `chemoDefect y := −(p.χ · deriv (stepFlux p u W) y)`,
      `stepFlux p u W y = (W y)^m · V'(y)`,    `V = frozenElliptic p u`.

  THE LEIBNIZ DECOMPOSITION (landed `crossFlux_deriv_eq_nondiagonal`, distinct
  `u`/`W` slots, with the elliptic ODE `V'' = V − u^γ`):

      `deriv (stepFlux p u W) y
         = W'(y)·m·(W y)^{m−1}·V'(y)  +  (W y)^m·(V(y) − (u y)^γ)`,

  hence with `−χ ≥ 0`,

      `chemoDefect y = (−χ)·[ W'·m·W^{m−1}·V'  +  W^m·(V − u^γ) ]`.

  WHAT CLOSES UNCONDITIONALLY (this file, axiom-clean, from LANDED signs only).
  The **first-order cross term has a determinate nonnegative sign**:

      `0 ≤ (−χ)·(W'(y)·m·(W y)^{m−1}·V'(y))`

  because  `−χ ≥ 0` (the negative-sensitivity branch `χ ≤ 0`),  `m ≥ 1 > 0`,
  `(W y)^{m−1} ≥ 0` (W trapped, `Real.rpow_nonneg`),  `W'(y) ≤ 0` (W antitone,
  `Antitone.deriv_nonpos`),  and  `V'(y) ≤ 0` (the LANDED
  `frozenElliptic_deriv_nonpos_of_monotone_trap`), so `W'·V' ≥ 0`.  Proved here
  as `chemoDefect_crossTerm_nonneg`, and the full defect is split into this
  signed cross term plus the second-order term as `chemoDefect_eq_crossTerm_add_secondOrder`.

  WHAT REMAINS (the precise residual, NOT faked here).  The **second-order term**

      `(−χ)·(W y)^m·(V(y) − (u y)^γ)`,    `V − u^γ = V''`,

  has GENUINELY INDETERMINATE sign on the trapped range (`V''` is the elliptic
  second derivative — it is NOT signed by trap membership: a profile `u` can have
  `V'' > 0` or `< 0` pointwise).  Therefore the FULL pointwise antitone/sign claim
  `Antitone chemoDefect` / `0 ≤ chemoDefect` is NOT provable from the landed signs
  alone — it is the genuine maximum-principle content, which the LANDED integrated
  route (`IntervalP1ChemoMonotone.lean`, `stepFlux_diff_ibp` + `greenConv_mono`)
  handles in `W'`-free INTEGRATED form via the flux-difference IBP, bypassing this
  pointwise residual.  This file therefore discharges the SIGNED half outright and
  names the second-order term as the exact remaining brick.

  No `sorry`/`axiom`/`native_decide`/`admit`.  New file only; edits nothing.
  Hypotheses are slot data (trap membership, `χ ≤ 0`, `W` differentiable), not the
  conclusion.  Touches only Paper1.
-/
import ShenWork.Paper1.CrossSourceNonDiagonal
import ShenWork.Paper1.WaveEllipticMono

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

variable {p : CMParams} {lam : ℝ} {u Z W : ℝ → ℝ}

/-! ## 1 — the signed first-order cross term and the (carried) second-order term -/

/-- The first-order **cross term** of the chemotaxis-flux defect:
`(−χ)·(W'·m·W^{m−1}·V')`. Its sign is determinate (proved nonneg below). -/
def chemoCrossTerm (p : CMParams) (u W : ℝ → ℝ) (y : ℝ) : ℝ :=
  (-p.χ) * (deriv W y * p.m * (W y) ^ (p.m - 1) * deriv (frozenElliptic p u) y)

/-- The **second-order term** of the chemotaxis-flux defect:
`(−χ)·W^m·(V − u^γ)` (`V − u^γ = V''`). Its sign is the genuine residual. -/
def chemoSecondOrder (p : CMParams) (u W : ℝ → ℝ) (y : ℝ) : ℝ :=
  (-p.χ) * ((W y) ^ p.m * (frozenElliptic p u y - (u y) ^ p.γ))

/-- **Leibniz split of the chemotaxis-flux defect.**
`−(χ·deriv(stepFlux p u W)) = chemoCrossTerm + chemoSecondOrder`, pointwise.
Pure consequence of the landed `crossFlux_deriv_eq_nondiagonal` (distinct `u`/`W`
slots + elliptic ODE `V'' = V − u^γ`); requires only `u` trapped and `W` `C¹`. -/
theorem chemoDefect_eq_crossTerm_add_secondOrder
    (hu_bdd : IsCUnifBdd u) (hu_nn : ∀ x, 0 ≤ u x) (hW : Differentiable ℝ W) (y : ℝ) :
    -(p.χ * deriv (stepFlux p u W) y)
      = chemoCrossTerm p u W y + chemoSecondOrder p u W y := by
  have hL := congrFun (crossFlux_deriv_eq_nondiagonal (p := p) hu_bdd hu_nn hW) y
  have hsf : stepFlux p u W = fun t => (W t) ^ p.m * deriv (frozenElliptic p u) t := rfl
  rw [hsf, hL]
  simp only [chemoCrossTerm, chemoSecondOrder]
  ring

/-! ## 2 — the determinate sign of the cross term (LANDED signs only) -/

/-- **The chemotaxis-flux defect's first-order cross term is nonnegative.**

For the negative-sensitivity branch `χ ≤ 0`, a monotone-wave-trapped antitone
profile `u` (giving `V' ≤ 0`), and a trapped antitone differentiable iterate `W`
(giving `W ≥ 0`, `W' ≤ 0`):

    `0 ≤ chemoCrossTerm p u W y = (−χ)·(W'·m·W^{m−1}·V')`.

Sign chain: `−χ ≥ 0`; `m ≥ 1 > 0`; `W^{m−1} ≥ 0`; `W' ≤ 0`, `V' ≤ 0` ⟹ `W'·V' ≥ 0`.
This is the genuinely-true half of the chemotaxis-monotonicity sign — the maximum
principle's first-order content — discharged from landed facts, no obligation
re-carried. -/
theorem chemoDefect_crossTerm_nonneg
    {κ M : ℝ}
    (hχ : p.χ ≤ 0)
    (huT : InMonotoneWaveTrapSet κ M u)
    (hWnn : ∀ x, 0 ≤ W x) (hWanti : Antitone W)
    (y : ℝ) :
    0 ≤ chemoCrossTerm p u W y := by
  have hnegχ : 0 ≤ -p.χ := by linarith
  have hVp : deriv (frozenElliptic p u) y ≤ 0 :=
    frozenElliptic_deriv_nonpos_of_monotone_trap p κ M u huT y
  have hWp : deriv W y ≤ 0 := Antitone.deriv_nonpos hWanti
  have hpow : (0 : ℝ) ≤ (W y) ^ (p.m - 1) := Real.rpow_nonneg (hWnn y) _
  have hm0 : (0 : ℝ) ≤ p.m := le_trans zero_le_one p.hm
  -- W'·V' ≥ 0 (product of two nonpositives)
  have hWV : 0 ≤ deriv W y * deriv (frozenElliptic p u) y :=
    mul_nonneg_of_nonpos_of_nonpos hWp hVp
  -- the bracket = (W'·V')·(m·W^{m−1}) ≥ 0
  have hbr : 0 ≤ deriv W y * p.m * (W y) ^ (p.m - 1) * deriv (frozenElliptic p u) y := by
    have : deriv W y * p.m * (W y) ^ (p.m - 1) * deriv (frozenElliptic p u) y
        = (deriv W y * deriv (frozenElliptic p u) y) * (p.m * (W y) ^ (p.m - 1)) := by ring
    rw [this]
    exact mul_nonneg hWV (mul_nonneg hm0 hpow)
  exact mul_nonneg hnegχ hbr

/-! ## 3 — honest accounting: the full defect sign reduces to the second-order term -/

/-- **The chemotaxis-flux-defect sign reduces to the second-order term's sign.**
Combining the Leibniz split with the proven cross-term nonnegativity:

    `chemoSecondOrder p u W y ≤ −(χ·deriv(stepFlux p u W) y)`,

i.e. the defect dominates its second-order term `(−χ)·W^m·(V − u^γ)`.  In
particular `0 ≤ −(χ·deriv(stepFlux))` (the maximum-principle sign of the
chemotaxis defect) follows AS SOON AS `0 ≤ chemoSecondOrder` — the single
remaining obligation `0 ≤ (−χ)·W^m·(V − u^γ)`, equivalently (since `−χ, W^m ≥ 0`,
and away from `χ = 0` / `W = 0`) the elliptic sign `V'' = V − u^γ ≥ 0`.  This is
the genuine residual the landed integrated route (`stepFlux_diff_ibp`) bypasses by
moving the derivative off the flux at the level of the whole Green map. -/
theorem chemoDefect_ge_secondOrder
    {κ M : ℝ}
    (hχ : p.χ ≤ 0)
    (huT : InMonotoneWaveTrapSet κ M u)
    (hWnn : ∀ x, 0 ≤ W x) (hWanti : Antitone W) (hW : Differentiable ℝ W)
    (y : ℝ) :
    chemoSecondOrder p u W y ≤ -(p.χ * deriv (stepFlux p u W) y) := by
  rw [chemoDefect_eq_crossTerm_add_secondOrder huT.trap.cunif_bdd
      (fun x => huT.nonneg x) hW y]
  have hcross := chemoDefect_crossTerm_nonneg hχ huT hWnn hWanti y
  linarith

/-- **Conditional full sign.**  IF the second-order term is nonnegative
(`0 ≤ (−χ)·W^m·(V − u^γ)` — the single named residual, the elliptic `V'' ≥ 0`
sign), THEN the chemotaxis-flux defect is nonnegative:
`0 ≤ −(χ·deriv(stepFlux p u W) y)`.  Non-circular: `hSO` is the genuinely-missing
second-order brick, strictly weaker than the conclusion (the cross-term half is
discharged unconditionally above). -/
theorem chemoDefect_nonneg_of_secondOrder_nonneg
    {κ M : ℝ}
    (hχ : p.χ ≤ 0)
    (huT : InMonotoneWaveTrapSet κ M u)
    (hWnn : ∀ x, 0 ≤ W x) (hWanti : Antitone W) (hW : Differentiable ℝ W)
    (hSO : ∀ y, 0 ≤ chemoSecondOrder p u W y)
    (y : ℝ) :
    0 ≤ -(p.χ * deriv (stepFlux p u W) y) := by
  rw [chemoDefect_eq_crossTerm_add_secondOrder huT.trap.cunif_bdd
      (fun x => huT.nonneg x) hW y]
  have hcross := chemoDefect_crossTerm_nonneg hχ huT hWnn hWanti y
  have := hSO y
  linarith

/-! ## Axiom audit -/

section AxiomAudit
#print axioms chemoDefect_eq_crossTerm_add_secondOrder
#print axioms chemoDefect_crossTerm_nonneg
#print axioms chemoDefect_ge_secondOrder
#print axioms chemoDefect_nonneg_of_secondOrder_nonneg
end AxiomAudit

end ShenWork.Paper1
