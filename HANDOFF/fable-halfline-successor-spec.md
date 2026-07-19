# Successor construction for the χ>0 buffered half-line rectangle (Fable spec)

Target (the last piece of P1 Thm 1.2 for χ>0):

```
exists_next_chiPosHalfLineRectangle :
  ∀ δ > 0, ∀ old : ChiPosHalfLineRectangle p c u,
    Nonempty {new // ChiPosHalfLineRectangleStep p δ old new}
```

feeding `uniformCoMovingLeftEquilibriumConvergence_of_halfLine_successors`
(committed, WholeLineChiPosHalfLineRectangle.lean).

## Data available at the start of a round

- old rectangle: `ℓ ≤ u ≤ M` on `{t ≥ old.start} × {z ≤ old.cut}` (co-moving),
  with strict margins `chiPosFloorGap p M ℓ > 0`, `chiPosCeilingGap p ℓ M > 0`.
- global bound `G` with `0 ≤ u ≤ G` everywhere (χ>0 range bound, committed).
- buffer: for every `e > 0` there is `T_e` with `|u(t, z+ct) − U(z)| < e` on any
  FIXED compact `[a,b]`, for `t ≥ T_e` (weighted-L² + spatial modulus, χ-general,
  committed) — and `U(z) → 1` as `z → −∞`.

## (1) Choice of R = R(δ)

Kernel split at `z₀ + R` gives, for `z ≤ z₀`,
```
(1−τ)·ℓ^γ ≤ frozenElliptic u z ≤ (1−τ)·M^γ + τ·G^γ,   τ = e^{−R}/2.
```
The two budgets acquire the additive tail terms
```
floor side  : χ·M^m·τ·G^γ         (adverse when the resolver is too big)
ceiling side: χ·M^m·τ·ℓ^γ ≤ χ·M^m·τ·G^γ
```
so it suffices to pick `R` with
```
τ = e^{−R}/2 < δ / (2·χ·(1+G)^{m+γ}) .
```
Concretely `R := max 0 (log (2·χ·(1+G)^{m+γ}·2/δ))`; positivity of the argument
is automatic since `χ > 0`, `G ≥ 1`. R depends on δ (hence on ε) — pick it INSIDE
the successor, which is exactly what the abstract layer's `∀ δ > 0` allows.

## (2) The new cut

`new.cut := old.cut − (R + 1)`. Moving left is required (the buffer
`[new.cut, new.cut + R]` must sit inside the region where the old rectangle
already holds, i.e. `new.cut + R ≤ old.cut`) and is permitted by the structure
field `cut_le`. Because each round moves the cut by a δ-dependent but FINITE
amount and the endgame runs finitely many rounds, the final cut is finite —
this is why the abstract endgame takes `-(rectangles n).cut` as its `R` output.

## (3) Floor barrier and the b^m-weighted contact inequality

Barrier `b(t) = L̂ − (L̂ − ℓ)·e^{−λ t}` (committed family `chiZeroKPPFloor`),
target `L̂` chosen as the near-root of the floor residual with margin:
```
chiPosFloorGap p M L̂ ∈ (0, δ/2)      (exists by continuity + strict margin at ℓ)
```
At a lower contact `u = b(t) =: β ∈ [ℓ, L̂]`, using ONLY the resolver UPPER bound:
```
χ·β^m·(β^γ − V) ≥ −χ·β^m·(M^γ − β^γ) − χ·β^m·τ·G^γ
```
so the scalar sufficient condition is
```
b' ≤ b·(1 − b^α) − χ·b^m·(M^γ − b^γ) − χ·b^m·τ·G^γ
```
i.e. after dividing by `b > 0`, `b'/b ≤ F_M(b) − χ·b^{m−1}·τ·G^γ`, which is the
committed weighted form plus a τ-term. **The b^m factor must be retained**: the
constant-defect wrapper is unsatisfiable when `ℓ ≪ 1` and `m = 1`.
Rate: `λ := (ℓ·(1 − L̂^α) − H⁻)/(L̂ − ℓ + 1)` with
`H⁻ := χ·M^m·((M^γ − ℓ^γ) + τ·G^γ)`, matching `chiNegKPPFloorRate`'s shape.
The co-moving drift `c·u_z` enters ONLY through the first-order term of the
half-line maximum principle and vanishes at an interior contact point; it is
absorbed by the committed `leftHalfLineSlabSup_le_of_scalar_pde` machinery
exactly as in the χ≤0 buffered proof (that proof already carries `c`).

## (4) Ceiling barrier and the a^m-weighted contact inequality

Barrier `a(t) = M̂ + (M − M̂)·e^{−μ t}` (committed `chiPosTargetCeiling`), with
```
chiPosCeilingGap p L̂ M̂ ∈ (0, δ/2).
```
At an upper contact `u = a(t) =: A ∈ [M̂, M]`, using the resolver LOWER bound:
```
χ·A^m·(A^γ − V) ≤ χ·A^m·(A^γ − (1−τ)·L̂^γ)
                = χ·A^m·(A^γ − L̂^γ) + χ·A^m·τ·L̂^γ
```
so the scalar sufficient condition is
```
a' ≥ a·(1 − a^α) + χ·a^m·(a^γ − L̂^γ) + χ·a^m·τ·L̂^γ.
```
**The a^m factor must be retained here too** (Q99's correction to the phase-1
constant-defect wrapper): the committed
`leftHalfLine_le_of_buffered_chiPos_ceiling` uses a constant `Hplus` and must be
re-derived in the weighted form. Rate `μ := (M̂·(M̂^α − 1) − H⁺)/(M − M̂ + 1)`.

## (5) Lateral boundary condition and quantifier order

The barriers need `b(t) ≤ u ≤ a(t)` on the buffer `[new.cut, new.cut + R]` for
all `t` in the round. Supply it from the buffer machinery with
`e := min (1 − L̂) (M̂ − 1) / 2`, choosing the far-left position so that
`|U − 1| < e` there as well. Order inside the successor:
```
δ given → choose L̂, M̂ (targets, hence e) → choose R = R(δ) → choose the cut →
choose T_e from the buffer → new.start := max old.start T_e + (barrier settling time)
```
Each round's `new.start` is finite; the endgame only needs monotonicity in `n`.

## (6) Seed

`exists_initial_chiPosHalfLineRectangle` needs BOTH margins at round 0:
- ceiling: from the χ>0 burn-in (`wholeLineCauchyGlobal_uniformLimsupLe_MChi_of_chi_pos`,
  committed) take `M₀ := MChi p + r` with `r` small; `chiPosCeilingGap p ℓ₀ M₀ > 0`
  holds for `M₀ > MChi` (the model computation is in
  `WholeLineChiPosRectangleWitness.lean`).
- floor: needs a positive co-moving left floor `ℓ₀`. This is the ONE genuinely
  missing producer. Design fixed earlier: mirror the χ≤0 persistent plateau with
  the POSITIVE ledgers (`paperWaveOperator_const_subsolution_nonneg_pos_MChi`,
  `paperWaveOperator_lowerBarrierPlateau_nonneg_pos_away`), normalizing the trap
  height to `MChi + r` after burn-in so the ledgers' regime applies.
  Then `wholeLineCauchyGlobal_eventual_coMoving_left_floor_of_persistent_plateau`
  (χ-free, committed) extracts `d > 0` on a co-moving left half-line.
  Finally shrink `ℓ₀ := min d (root of the floor residual at M₀)` to get the
  strict floor margin.
