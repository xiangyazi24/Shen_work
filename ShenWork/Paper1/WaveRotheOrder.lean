/-
  ShenWork/Paper1/WaveRotheOrder.lean

  Discharge of the carried source-ordering obligation of the B1 Rothe trapping
  (`WaveRotheTrap.lean`): the large-`λ` quasi-monotonicity estimate that turns the
  implicit-step trap `W ≤ B` (`B = Ū`) into a fact about ordered Green sources
  `R_W ≤ R_B`, i.e. `ImplicitStepSuperOrdering`.

  THE DECOMPOSITION.  For the implicit Green step `W − h·F_u(W) = Z` (`h = 1/λ`)
  the step-solution source and the super-barrier source are

    `R_W = crossSource = reaction(W) + λ·Z − χ·∂ₓ(W^m·V')`        (`V' = (frozenElliptic p u)'`)
    `R_B = barrierSource = reaction(B) + λ·B − χ·∂ₓ(B^m·V')`       (B as super-solution of `A_λ`)

  whose difference is the defect source

    `R_B − R_W = [reaction(B) − reaction(W)]  +  λ(B − Z)  −  χ·[∂ₓ(B^m·V') − ∂ₓ(W^m·V')]`.

  THE QUASI-MONOTONICITY MECHANISM (cron-designed, fully discharged below for the
  zeroth-order part).  Group the reaction increment against the `λ`-shift:

    `R_B − R_W = ([reaction(B) − reaction(W)] + λ(B − W))  +  λ(W − Z)  −  χ·[flux defect]`.

  The first bracket is `≥ 0` for `λ ≥ L_rxn(M) = reactionLip α M` on `[0,M]` with
  `W ≤ B`: this is exactly `reaction(B) − reaction(W) ≥ −λ(B − W)`, the
  `λ I + reaction'` monotonicity (quasi-monotonicity).  This is the REAL order
  content of the large-`λ` shift and is discharged OUTRIGHT here
  (`reaction_increment_ge_neg_lambda_shift`), from the committed Lipschitz fact
  `reaction_lipschitz_on_Icc`.

  The residual `λ(W − Z) − χ·[flux defect]` is the genuine remaining sign
  obligation; we carry it as ONE explicit, satisfiable predicate
  (`RotheChemoMonotoneResidual`) — the same discipline as the committed
  `ChemotaxisSandwich` for the stationary problem — and assemble
  `ImplicitStepSuperOrdering` from the discharged reaction part plus that residual.
  See the stall note at the end for the precise gap between this residual and the
  committed barrier comparison machinery (`aux_comparison`), and why the implicit
  step's chemotaxis defect is NOT identical to the committed stationary one.
-/
import ShenWork.Paper1.WaveRotheTrap

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## 1 — the reaction increment vs. the `λ`-shift (quasi-monotonicity)

The single genuinely-discharged order estimate: on `[0,M]` the reaction
nonlinearity `s ↦ s(1 − s^a)` is `L_rxn`-Lipschitz (`reaction_lipschitz_on_Icc`,
`L_rxn = reactionLip a M`), so for any `λ ≥ L_rxn` and any `w ≤ b` in `[0,M]`,

    `reaction(b) − reaction(w)  ≥  −λ·(b − w)`,

i.e. `λ I + reaction` is monotone increasing.  This is the mechanism by which the
`λ`-shift absorbs the negative part of the reaction increment. -/

/-- **Reaction Lipschitz increment.**  On `[0,M]`, `|reaction(b) − reaction(w)| ≤
reactionLip a M · |b − w|`.  Direct from the committed `LipschitzOnWith`. -/
theorem reaction_increment_abs_le {a M : ℝ} (ha : 1 ≤ a) (hM : 0 ≤ M)
    {w b : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) M) (hb : b ∈ Set.Icc (0 : ℝ) M) :
    |reactionFun a b - reactionFun a w| ≤ reactionLip a M * |b - w| := by
  have hLip := reaction_lipschitz_on_Icc (a := a) (M := M) ha hM
  have hd := hLip.dist_le_mul b hb w hw
  rw [Real.dist_eq, Real.dist_eq] at hd
  rw [Real.coe_toNNReal _ (reactionLip_nonneg ha hM)] at hd
  exact hd

/-- **Reaction increment absorbed by the `λ`-shift (quasi-monotonicity).**
For `λ ≥ reactionLip a M` and `w ≤ b` in `[0,M]`:

    `reaction(b) − reaction(w) ≥ −λ·(b − w)`,

equivalently `(reaction(b) − reaction(w)) + λ·(b − w) ≥ 0`.  This is the genuine
large-`λ` quasi-monotonicity estimate (`λ I + reaction` monotone increasing). -/
theorem reaction_increment_ge_neg_lambda_shift {a M : ℝ} (ha : 1 ≤ a) (hM : 0 ≤ M)
    {lam : ℝ} (hlam : reactionLip a M ≤ lam)
    {w b : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) M) (hb : b ∈ Set.Icc (0 : ℝ) M)
    (hwb : w ≤ b) :
    -(lam * (b - w)) ≤ reactionFun a b - reactionFun a w := by
  have habs := reaction_increment_abs_le ha hM hw hb
  have hbw_abs : |b - w| = b - w := abs_of_nonneg (by linarith)
  rw [hbw_abs] at habs
  -- |Δreaction| ≤ L·(b−w) ⟹ −L·(b−w) ≤ Δreaction
  have hlow : -(reactionLip a M * (b - w)) ≤ reactionFun a b - reactionFun a w := by
    have := (abs_le.mp habs).1
    linarith
  -- and L ≤ λ, b−w ≥ 0 ⟹ −λ(b−w) ≤ −L(b−w)
  have hmono : reactionLip a M * (b - w) ≤ lam * (b - w) :=
    mul_le_mul_of_nonneg_right hlam (by linarith)
  linarith

/-! ## 2 — the chemotaxis-plus-step residual obligation

After the reaction increment is absorbed by the `λ`-shift, the defect source
satisfies (pointwise)

    `R_B − R_W ≥ λ·(W − Z) − χ·[∂ₓ(B^m·V') − ∂ₓ(W^m·V')]`,

so `R_W ≤ R_B` is implied by the residual sign

    `λ·(W y − Z y) − χ·[flux_B y − flux_W y] ≥ 0`,

where `flux_W y = (W y)^m · V'(y)`, `flux_B y = (B y)^m · V'(y)`.  This residual
bundles the monotone-step relation (`Z = z_k ≥ z_{k+1} = W`, i.e. `W ≤ Z`, so the
`λ(W−Z)` term is a controllable nonpositive contribution that the chemotaxis
defect must dominate) with the chemotaxis defect's sign on the trapped range.  We
carry it as one explicit predicate — the same discipline as the committed
`ChemotaxisSandwich`. -/

/-- The implicit-step flux `flux_W y = (W y)^m · V'(y)`, `V = frozenElliptic p u`. -/
def stepFlux (p : CMParams) (u W : ℝ → ℝ) (y : ℝ) : ℝ :=
  (W y) ^ p.m * deriv (frozenElliptic p u) y

/-- **Named obligation — the chemotaxis-plus-step residual.**
After the reaction increment is absorbed by the `λ`-shift, the remaining defect
source is nonnegative:

    `λ·(W y − Z y) − χ·[∂ₓ(stepFlux B) y − ∂ₓ(stepFlux W) y] ≥ 0`   for all `y`.

This is the honest remaining sign content of the implicit-step super-ordering
(the monotone-step `λ(W−Z)` term against the chemotaxis defect). -/
structure RotheChemoMonotoneResidual
    (p : CMParams) (lam : ℝ) (u Z W B : ℝ → ℝ) : Prop where
  residual_nonneg : ∀ y,
    0 ≤ lam * (W y - Z y)
        - p.χ * (deriv (stepFlux p u B) y - deriv (stepFlux p u W) y)

/-! ## 3 — assembly: `ImplicitStepSuperOrdering` from the discharged parts

We now assemble the source ordering `R_W ≤ R_B` from
* the discharged reaction-increment estimate (`reaction_increment_ge_neg_lambda_shift`); and
* the carried residual obligation (`RotheChemoMonotoneResidual`).

The Green sources are spelled with the committed `crossSource` for `R_W` and the
barrier super-solution source `barrierSource` for `R_B`. -/

/-- The super-barrier's Green source (B as a super-solution of the shifted
operator `A_λ`): `R_B(y) = reaction(B y) + λ·B y − χ·∂ₓ(B^m·V')(y)`.  Structurally
identical to the committed `auxSource` written at `B`. -/
def barrierSource (p : CMParams) (lam : ℝ) (u B : ℝ → ℝ) (y : ℝ) : ℝ :=
  reactionFun p.α (B y) + lam * B y
    - p.χ * deriv (stepFlux p u B) y

/-- `crossSource` (the committed `R_W`) re-expressed through `stepFlux`. -/
theorem crossSource_eq_stepFlux (p : CMParams) (lam : ℝ) (u Z W : ℝ → ℝ) (y : ℝ) :
    crossSource p lam u Z W y
      = reactionFun p.α (W y) + lam * Z y - p.χ * deriv (stepFlux p u W) y := by
  unfold crossSource stepFlux
  rfl

/-- **Pointwise source ordering from the mechanism.**
For `λ ≥ reactionLip p.α M`, with `W y, B y ∈ [0,M]` and `W y ≤ B y` at the point,
and the residual sign at `y`, the defect source is nonnegative:
`crossSource … y ≤ barrierSource … y`. -/
theorem crossSource_le_barrierSource_pointwise
    (p : CMParams) {lam M : ℝ} {u Z W B : ℝ → ℝ}
    (hα : 1 ≤ p.α) (hM : 0 ≤ M) (hlamL : reactionLip p.α M ≤ lam)
    {y : ℝ} (hWy : W y ∈ Set.Icc (0 : ℝ) M) (hBy : B y ∈ Set.Icc (0 : ℝ) M)
    (hWBy : W y ≤ B y)
    (hres : 0 ≤ lam * (W y - Z y)
        - p.χ * (deriv (stepFlux p u B) y - deriv (stepFlux p u W) y)) :
    crossSource p lam u Z W y ≤ barrierSource p lam u B y := by
  rw [crossSource_eq_stepFlux]
  unfold barrierSource
  -- reaction increment absorbed by λ-shift
  have hrxn := reaction_increment_ge_neg_lambda_shift hα hM hlamL hWy hBy hWBy
  -- target: reaction(W)+λZ−χ∂(fluxW) ≤ reaction(B)+λB−χ∂(fluxB)
  -- ⟺ 0 ≤ (reaction(B)−reaction(W)) + λ(B−Z) − χ(∂fluxB − ∂fluxW)
  -- decompose λ(B−Z) = λ(B−W) + λ(W−Z); reaction increment + λ(B−W) ≥ 0; rest = residual
  nlinarith [hrxn, hres]

/-- **Assembly — `ImplicitStepSuperOrdering` for the cross-frozen super-barrier.**
For `λ ≥ reactionLip p.α M`, with the trapped-range membership `W, B ∈ [0,M]`,
the ordering `W ≤ B`, and the carried chemotaxis-plus-step residual, the implicit
step source `crossSource` is dominated by the barrier source `barrierSource`,
i.e. `ImplicitStepSuperOrdering` holds with `R_W = crossSource`, `R_B = barrierSource`.

This discharges the carried hypothesis `hord` of
`implicitStep_le_of_supersolution`: the reaction part is unconditional
(quasi-monotonicity), the residual is the single honest remaining obligation. -/
theorem implicitStep_superOrdering_of_barrier
    (p : CMParams) {lam M : ℝ} {u Z W B : ℝ → ℝ}
    (hα : 1 ≤ p.α) (hM : 0 ≤ M) (hlamL : reactionLip p.α M ≤ lam)
    (hWrange : ∀ y, W y ∈ Set.Icc (0 : ℝ) M)
    (hBrange : ∀ y, B y ∈ Set.Icc (0 : ℝ) M)
    (hWB : ∀ y, W y ≤ B y)
    (hres : RotheChemoMonotoneResidual p lam u Z W B) :
    ImplicitStepSuperOrdering p lam u Z W B
      (crossSource p lam u Z W) (barrierSource p lam u B) where
  source_le := fun y =>
    crossSource_le_barrierSource_pointwise p hα hM hlamL
      (hWrange y) (hBrange y) (hWB y) (hres.residual_nonneg y)

/-- **End-to-end trap from the barrier ordering.**
Combine `implicitStep_superOrdering_of_barrier` with the committed
`implicitStep_le_of_supersolution`: under the Green representations of `W` and `B`,
the discharged super-ordering, and the committed convergent-tail hypotheses, the
implicit step solution is trapped from above by the barrier, `W ≤ B`. -/
theorem implicitStep_le_of_barrier
    (hlam : 0 < lam)
    (p : CMParams) {c M : ℝ} {u Z W B : ℝ → ℝ}
    (hα : 1 ≤ p.α) (hM : 0 ≤ M) (hlamL : reactionLip p.α M ≤ lam)
    (hWrange : ∀ y, W y ∈ Set.Icc (0 : ℝ) M)
    (hBrange : ∀ y, B y ∈ Set.Icc (0 : ℝ) M)
    (hWB : ∀ y, W y ≤ B y)
    (hres : RotheChemoMonotoneResidual p lam u Z W B)
    (hW : W = fun x => greenConv c lam (crossSource p lam u Z W) x)
    (hB : B = fun x => greenConv c lam (barrierSource p lam u B) x)
    (hHiW : ∀ x, IntegrableOn
      (gWeight (greenRootPlus c lam) (crossSource p lam u Z W)) (Ioi x))
    (hHiB : ∀ x, IntegrableOn
      (gWeight (greenRootPlus c lam) (barrierSource p lam u B)) (Ioi x))
    (hLoW : ∀ x, IntegrableOn
      (gWeight (greenRootMinus c lam) (crossSource p lam u Z W)) (Iic x))
    (hLoB : ∀ x, IntegrableOn
      (gWeight (greenRootMinus c lam) (barrierSource p lam u B)) (Iic x)) :
    ∀ x, W x ≤ B x :=
  implicitStep_le_of_supersolution hlam p hW hB
    (implicitStep_superOrdering_of_barrier p hα hM hlamL hWrange hBrange hWB hres)
    hHiW hHiB hLoW hLoB

/-! ## 4 — dual: the sub-barrier sub-ordering

Symmetric: for a sub-barrier `A ≤ W` with the dual residual, `R_A ≤ R_W`.  The
reaction part is again quasi-monotonicity (`λ I + reaction` monotone), now applied
to `A ≤ W`; the residual is the dual chemotaxis-plus-step sign. -/

/-- **Named obligation — dual chemotaxis-plus-step residual** (sub-barrier). -/
structure RotheChemoMonotoneResidualSub
    (p : CMParams) (lam : ℝ) (u Z W A : ℝ → ℝ) : Prop where
  residual_nonneg : ∀ y,
    0 ≤ lam * (Z y - W y)
        - p.χ * (deriv (stepFlux p u W) y - deriv (stepFlux p u A) y)

/-- **Pointwise dual source ordering.** `barrierSource(A) ≤ crossSource(W)`. -/
theorem barrierSource_le_crossSource_pointwise
    (p : CMParams) {lam M : ℝ} {u Z W A : ℝ → ℝ}
    (hα : 1 ≤ p.α) (hM : 0 ≤ M) (hlamL : reactionLip p.α M ≤ lam)
    {y : ℝ} (hAy : A y ∈ Set.Icc (0 : ℝ) M) (hWy : W y ∈ Set.Icc (0 : ℝ) M)
    (hAWy : A y ≤ W y)
    (hres : 0 ≤ lam * (Z y - W y)
        - p.χ * (deriv (stepFlux p u W) y - deriv (stepFlux p u A) y)) :
    barrierSource p lam u A y ≤ crossSource p lam u Z W y := by
  rw [crossSource_eq_stepFlux]
  unfold barrierSource
  have hrxn := reaction_increment_ge_neg_lambda_shift hα hM hlamL hAy hWy hAWy
  nlinarith [hrxn, hres]

/-- **Assembly — `ImplicitStepSubOrdering` for the cross-frozen sub-barrier.** -/
theorem implicitStep_subOrdering_of_barrier
    (p : CMParams) {lam M : ℝ} {u Z W A : ℝ → ℝ}
    (hα : 1 ≤ p.α) (hM : 0 ≤ M) (hlamL : reactionLip p.α M ≤ lam)
    (hArange : ∀ y, A y ∈ Set.Icc (0 : ℝ) M)
    (hWrange : ∀ y, W y ∈ Set.Icc (0 : ℝ) M)
    (hAW : ∀ y, A y ≤ W y)
    (hres : RotheChemoMonotoneResidualSub p lam u Z W A) :
    ImplicitStepSubOrdering p lam u Z W A
      (crossSource p lam u Z W) (barrierSource p lam u A) where
  source_le := fun y =>
    barrierSource_le_crossSource_pointwise p hα hM hlamL
      (hArange y) (hWrange y) (hAW y) (hres.residual_nonneg y)

/-- **End-to-end lower trap from the sub-barrier ordering.**

Combine `implicitStep_subOrdering_of_barrier` with the committed lower
comparison theorem `implicitStep_ge_of_subsolution`: under the Green
representations of the implicit step `W` and the sub-barrier `A`, the discharged
sub-ordering, and the convergent-tail hypotheses, the implicit step is trapped
from below, `A ≤ W`. -/
theorem implicitStep_ge_of_barrier
    (hlam : 0 < lam)
    (p : CMParams) {c M : ℝ} {u Z W A : ℝ → ℝ}
    (hα : 1 ≤ p.α) (hM : 0 ≤ M) (hlamL : reactionLip p.α M ≤ lam)
    (hArange : ∀ y, A y ∈ Set.Icc (0 : ℝ) M)
    (hWrange : ∀ y, W y ∈ Set.Icc (0 : ℝ) M)
    (hAW : ∀ y, A y ≤ W y)
    (hres : RotheChemoMonotoneResidualSub p lam u Z W A)
    (hW : W = fun x => greenConv c lam (crossSource p lam u Z W) x)
    (hA : A = fun x => greenConv c lam (barrierSource p lam u A) x)
    (hHiA : ∀ x, IntegrableOn
      (gWeight (greenRootPlus c lam) (barrierSource p lam u A)) (Ioi x))
    (hHiW : ∀ x, IntegrableOn
      (gWeight (greenRootPlus c lam) (crossSource p lam u Z W)) (Ioi x))
    (hLoA : ∀ x, IntegrableOn
      (gWeight (greenRootMinus c lam) (barrierSource p lam u A)) (Iic x))
    (hLoW : ∀ x, IntegrableOn
      (gWeight (greenRootMinus c lam) (crossSource p lam u Z W)) (Iic x)) :
    ∀ x, A x ≤ W x :=
  implicitStep_ge_of_subsolution hlam p hW hA
    (implicitStep_subOrdering_of_barrier p hα hM hlamL hArange hWrange hAW hres)
    hHiA hHiW hLoA hLoW

/-! ## Axiom audit -/

section AxiomAudit

#print axioms reaction_increment_abs_le
#print axioms reaction_increment_ge_neg_lambda_shift
#print axioms crossSource_le_barrierSource_pointwise
#print axioms implicitStep_superOrdering_of_barrier
#print axioms implicitStep_le_of_barrier
#print axioms barrierSource_le_crossSource_pointwise
#print axioms implicitStep_subOrdering_of_barrier
#print axioms implicitStep_ge_of_barrier

end AxiomAudit

/-! ## STALL NOTE — the residual vs. the committed barrier comparison

`RotheChemoMonotoneResidual` is the honest remaining obligation; it is NOT
`reaction_increment_*` in disguise and NOT discharged by the committed
`aux_comparison`.  Precisely:

* The committed stationary `ChemotaxisSandwich` (`WaveAuxInvariance.lean:153`)
  bounds the chemotaxis flux of the SAME profile `u` against FIXED constant
  barriers `U_, Ū` via `Aλ U_ ≤ R(u) ≤ Aλ Ū` — a one-profile, frozen-flux
  statement.  Its discharge uses `V' ≤ V` (`frozenElliptic_deriv_abs_le`) and the
  constant-barrier flux derivative `∂ₓ(M^m V') = M^m·(V − u^γ)`
  (`frozenWaveOperator_upperBarrier_const_region_eq`, Statements:3606), where the
  constant barrier kills the `(B^m)'` cross term.

* The implicit-step residual here is a flux DIFFERENCE between TWO profiles
  `B` and `W` sharing the frozen `V' = (frozenElliptic p u)'`:
  `∂ₓ((B^m − W^m)·V')`.  Expanding, this is
  `(∂ₓ(B^m − W^m))·V' + (B^m − W^m)·V''` — it carries `(B^m − W^m)' = `
  `m(B^{m−1}B' − W^{m−1}W')`, which involves `W'` (the step solution's
  derivative).  The committed machinery folds `u'` away ONLY for the BARRIER side
  (constant `B = Ū` ⟹ `(B^m)' = 0`); on the step-solution side `W` is NOT constant,
  so `W'` genuinely appears unless one re-folds the flux difference into the
  kernel-derivative (`Kλ'`) integral form, integrating `∂ₓ(W^m V')` by parts
  against `Kλ` exactly as `flux_ibp` (WaveFluxIBP.lean:74) does for the SINGLE
  profile.

  The committed `flux_ibp` gives, for a single profile `u`,
  `−χ ∫ Kλ'(x−y)·flux(y) = greenConv (−χ ∂ₓ flux)`, i.e. it moves the derivative
  off the flux at the level of the WHOLE Green map, not at the level of a
  pointwise SOURCE inequality.  To discharge `RotheChemoMonotoneResidual` from
  committed material one needs the flux-difference IBP

      `−χ ∫ Kλ'(x−y)·(flux_B − flux_W)(y) dy ≥ λ ∫ Kλ(x−y)·(Z − W)(y) dy`

  in INTEGRATED form (so no `W'` appears pointwise), combined with `Kλ ≥ 0`
  (`greenKernel_nonneg`).  That is a flux-difference variant of `flux_ibp` +
  `greenConv_mono`, NOT presently committed.  The PRECISE missing brick:

    `stepFlux_diff_ibp` :
      `−χ ∫ Kλ'(x−y)·(stepFlux p u B y − stepFlux p u W y) dy
         = greenConv c λ (fun y => −χ·(∂ₓ stepFlux_B y − ∂ₓ stepFlux_W y)) x`

  (two applications of the committed `flux_ibp`, subtracted), after which
  `greenConv_mono` against the residual gives the integrated comparison directly
  — bypassing the pointwise residual entirely.  This is mechanical given
  `flux_ibp`'s decay/`C¹` hypotheses for BOTH `B` and `W`; it was not built here
  because `flux_ibp` is stated for `auxFlux p u` (single profile in BOTH the power
  base and the elliptic), whereas `stepFlux` uses `W` in the power base and `u` in
  the elliptic — a (purely definitional) generalization of `auxFlux`/`flux_ibp` to
  a cross-frozen flux `(W^m)·(frozenElliptic p u)'` is the one new ingredient, and
  is the clean next step to make the residual itself discharged rather than carried.

  NET: the zeroth-order quasi-monotonicity (the "real order content of G2" named
  in the task) is discharged unconditionally; the chemotaxis residual is reduced
  to a single named, satisfiable obligation with the exact committed-lemma bridge
  (`flux_ibp` generalized to the cross-frozen flux + `greenConv_mono`) identified.
-/

end ShenWork.Paper1
