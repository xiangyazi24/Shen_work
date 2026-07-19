# χ>0 Left-Equilibrium Convergence — Fable Design (2026-07-18)

Goal: `wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_pos_natural`,
the ONE theorem separating us from P1 Thm 1.2 full (all other assembly pieces are
χ-general or already have χ>0 versions — verified against
WholeLineWeightedRegularityStabilityNatural.lean:81 wrapper).

## Paper ground truth (read from paper1.pdf today)

- Paper's left-tail route for Thm 1.2 (§5.2 end, p.~48): extract translation limit
  u* ≥ d₀ along xₙ → −∞, then "by Proposition 1.2, u* ≡ 1". Prop 1.2(2) (p.7 + §3.2 p.21-23)
  is the χ>0 stabilization via the **rectangle/ODE approach**: coupled ODE pair
    Ū' = χŪ^m(Ū^γ − U̲^γ) + Ū(1−Ū^α),   U̲' = χU̲^m(U̲^γ − Ū^γ) + U̲(1−U̲^α)
  squeezes inf/sup of u; (3.18) ODE convergence is CITED to [18, Lem 3.1-3.2];
  (3.17) invariance via translation-compactness + strong comparison.
- **Hypothesis mismatch (NEW finding, not in paper1_theorem12_statement_amendment.pdf):**
  Prop 1.2(2) assumes 0 < χ < 1/2; Thm 1.2 assumes 0 ≤ χ < χ* = min(1, (2m+2γ)/(m²+m+2γ)).
  For m = 1, χ* = 1 > 1/2. Linearization of the rectangle pair at (1,1): symmetric Jacobian,
  eigendirection (1,−1) has eigenvalue 2χγ − α ⇒ the squeeze converges iff **2χγ < α**.
  With α ≥ m+γ−1 ≥ γ (m≥1), χ < 1/2 ⇒ 2χγ < α, so the paper's flat 1/2 is exactly the
  sufficient simplification. For χ ∈ [α/(2γ), χ*) the paper's left-tail argument does not
  close ⇒ the χ>0 branch of the Lean headline carries the extra hypothesis
  `hsqueeze : 2 * p.χ * p.γ < p.α` (sharp) with corollary for flat χ < 1/2.
  Consistency check #2: for m = 1 the seed-floor KPP rate is 1 − χ·M^γ; at the critical
  exponent with M = MChi = (1−χ)^{−1/α}, positivity ⟺ χ(1−χ)^{−γ/α} < 1 ⟺ (m=1, α=γ) χ < 1/2.
  Three independent derivations agree.

## Lean route: buffered discrete rectangle squeeze (compactness-free)

Replace both compactness steps by the existing quantitative machinery:

1. **Seeds.** M₀ = MChi + ε from `wholeLineCauchyGlobal_uniformLimsupLe_MChi_of_chi_pos` (DONE).
   ℓ₀ = d from a χ>0 plateau/left-floor (mirror of χ<0 plateau; Codex sign-audit pending;
   fallback: modified-rate KPP floor with rate 1 − χM^γ − margin > 0 under hsqueeze).
2. **Half-line two-sided resolver bound.** For x ≤ x₀, with induction bounds
   ℓₙ ≤ u ≤ Mₙ on (−∞, x₀+R], buffer u ∈ [1−e, 1+e] on [x₀, x₀+R] (from weighted-L2 +
   modulus, χ-general, DONE), global 0 ≤ u ≤ Mglob:
     frozenElliptic u(x) ≤ Mₙ^γ + (Mglob^γ/2)e^{−R},
     frozenElliptic u(x) ≥ ℓₙ^γ(1 − e^{−R}/2) − 0.
   (kernel mass split at x₀+R; for x ≤ x₀ the outside mass ≤ e^{−R}/2.)
3. **Discrete alternation** (avoids 2D ODE asymptotics AND [18] citation):
   each half-step is a 1D explicit exponential barrier with restart, the exact pattern of
   `wholeLineCauchyChiPosCeiling` (supersolution via Bernoulli/nlinarith, slab comparison,
   segment induction — commit 8158948b/7ea4d1db machinery):
   - upper: Ū(t) = Eq⁺(ℓₙ) + (Mₙ − Eq⁺)e^{−λt} on the half-line slab, Eq⁺(ℓ) ≈ the root of
     χ M^m(M^γ − ℓ^γ + δ_R) + M(1−M^α) = 0 plus margin;
   - lower: symmetric with Eq⁻(Mₙ₊₁).
4. **Contraction lemma (pure algebra).** aₙ = Mₙ−1, bₙ = 1−ℓₙ:
   under hsqueeze and margins δ (tail e^{−R} + buffer e),
   aₙ₊₁ ≤ q(aₙ+bₙ)·(χγ/(α−χγ)) + Cδ with overall ratio r < 1 ⇒ gap → O(δ).
   NOTE: linearized ratio is local; the algebraic lemma must be proved on the actual range
   [d, MChi+ε] with explicit rpow inequalities (nlinarith + rpow_bernoulli pattern) — this
   is the one place where "linearization" must become a real global estimate. If the global
   ratio needs χ smaller than α/(2γ), fall back to flat χ < 1/2 and document.
5. **Final ε-quantifier.** Given ε: choose e, R, n with gap + Cδ < ε; combine lower+upper
   eventual bounds on (−∞, x₀]: |u − 1| < ε for t ≥ Tₙ. This IS
   UniformCoMovingLeftEquilibriumConvergence (same shape as χ<0 file lines 183-414).

## Assembly after that (mechanical)

Mirror `WholeLineWeightedRegularityChiNegStabilityNatural.lean` +
`WholeLineWeightedRegularityChiNonposHeadlineNatural.lean`:
`..._solution_weighted_and_uniformConvergence_chi_pos_natural` via the χ-general
`..._chi_nonpos_of_leftEquilibrium` pattern (only χ≤0 uses there: ceiling regime ←
`hregime.toWholeLineCauchyCeilingRegime`; weighted conv ← chi_pos version DONE).
Then the full Thm 1.2 headline combining χ≤0 + χ>0 branches (χ>0 branch with hsqueeze).

## UPDATE (post-Codex cross-check): unified affine recurrence — MAJOR SIMPLIFICATION

Codex independently confirmed 2χγ<α (counterexample m=α=γ=1, χ=3/4 vs chiStar=1) and
supplied the log-ratio burn-in. DECISION: primary hypothesis χ < 1/2 (paper Prop 1.2(2)
faithful); χ ∈ [1/2, χ*) recorded as genuinely open in paper (its §5 cites Prop 1.2
outside its proven range; Remark 1.3(2) oscillation warning).

The two-phase design (burn-in + local constants) collapses into ONE affine recurrence.
Key algebra (critical α = β := m+γ−1, m,γ ≥ 1, d ≤ ℓ ≤ 1 ≤ M ≤ G = MChi+r ≤ 2+r):

1. Termwise bounds (2-line, x^{m-1} monotone):
   M^{m-1}(M^γ−ℓ^γ) ≤ M^β−ℓ^β and ℓ^{m-1}(M^γ−ℓ^γ) ≤ M^β−ℓ^β.
2. Alternating step targets satisfy (up to defect δ = tails + buffer-e + margins):
   1 − ℓ_{k+1}^α ≤ χ·ℓ_{k+1}^{m-1}(M_k^γ − ℓ_{k+1}^γ) + Cδ ≤ χ(M_k^β − ℓ_{k+1}^β) + Cδ
   M_{k+1}^α − 1 ≤ χ·M_{k+1}^{m-1}(M_{k+1}^γ − ℓ_{k+1}^γ) + Cδ ≤ χ(M_k^β − ℓ_{k+1}^β) + Cδ
   Sum + ℓ_{k+1} ≥ ℓ_k, M_{k+1} ≤ M_k, α = β:
   **gap_{k+1} := M_{k+1}^α − ℓ_{k+1}^α ≤ 2χ·gap_k + Cδ** — geometric, ratio 2χ < 1,
   valid on the WHOLE rectangle (no localization needed). Fixed-pair uniqueness is the
   same 3 lines (M^α−ℓ^α ≤ 2χ(M^α−ℓ^α) ⇒ M = ℓ = 1).
3. Endgame: ℓ ≤ u ≤ M, α ≥ 1 ⇒ M−1 ≤ gap and 1−ℓ ≤ gap ⇒ |u−1| ≤ gap.
4. m=1 low-floor viability: floor-step rate function φ(x) = 1−x^α − χx^{m-1}(M^γ−x^γ)
   has φ(0) = 1 (m>1) or 1−χM^γ > 0 for M ≤ MChi+r under χ<1/2 (m=1, critical). The
   PDE contact estimate MUST keep the b^m factor (χb^m(b^γ−V) ≥ −χb^m·Dgap, NOT the
   constant-in-b Hminus of the codex §4 budget) — else the burn-in from small floors
   fails. Refactor item 2/3 budget hypotheses to the b^m-weighted form.
5. Consequence: ChiPosLocalSqueezeConstants (codex §5) is NOT needed. The Nat recurrence
   is affine from the start. Supercritical α > β works identically for Prop 1.2(2)
   (M^α−ℓ^α ≥ M^β−ℓ^β on ℓ≤1≤M).

## Seed floor (task 3, phase 3) — route settled

Finite-time survival from t=0 does NOT work: the co-moving half-line (−∞,x₀] at time t is
lab (−∞, x₀+ct]; the initial floor region Iic x₁ recedes at speed c in co-moving coords,
and compact wave-closeness only covers FIXED compacts — the growing middle region
[x₁−ct−spread, x₀] is uncovered. The seed genuinely needs the self-sustaining co-moving
plateau (as χ<0 did). Route: mirror the χ<0 plateau chain with the POSITIVE ledgers
(audit §1.4: constant ledger at height MChi under χ<1/2 =
`paperWaveOperator_const_subsolution_nonneg_pos_MChi`; raw ledger under χ<min(1/2,chiStar);
patched barrier `paperWaveOperator_lowerBarrierPlateau_nonneg_pos_away`; profile shape
χ-free). The trap-height-Q mismatch dissolves: after ceiling burn-in the global bound is
MChi+r (limsup theorem), so normalize the trap to height MChi+r — exactly the positive
ledgers' regime. The floor-extraction lemma
(`wholeLineCauchyGlobal_eventual_coMoving_left_floor_of_persistent_plateau`) is already
χ-free.

## Division of labor

- Codex (running): sign audit of plateau + buffered comparison; range bound
  `wholeLineCauchyGlobal_le_max_of_chi_pos`; independent squeeze design (cross-check).
- ChatGPT bridge: DOWN (mini offline since ~1 day; tailscaled on uisai2 was dead since
  07-10, restarted today). Retry when mini returns; ask for [18]'s Lem 3.1-3.2 content
  and an independent check of the 2χγ < α sharpness.
- Fable: this design; verify Codex output against it; the contraction algebra lemma is
  the crux — do NOT hand it off until the route is validated.
