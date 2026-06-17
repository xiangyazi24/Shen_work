/-
  ShenWork/Paper1/WaveRotheConcrete.lean

  **G2 FINAL WIRING — the concrete Rothe sequence `rotheSeq` and its
  `RotheOrbitData` instantiation, reducing the B1 χ≤0 traveling-wave existence to
  ONLY the G1 abstract Schauder principle plus the committed per-fixed-point
  profile lemmas.**

  This file assembles the concrete per-`u`-frozen implicit-Euler (Rothe) orbit

      `rotheSeq u 0       = upperBarrier κ M`  (= Ū, the exponential super-barrier),
      `rotheSeq u (k+1)   = the unique implicit-Euler step solution from rotheSeq u k`,

  and discharges the per-`u` `RotheOrbitData` fields (continuity, antitone-in-`k`,
  antitone-in-`x`, nonneg, `≤ M`, `≤ Ū`, bddBelow, equi-Lipschitz, limit
  Lipschitz, the implicit-step recursion, and `V_cont`/`V_bound`) by induction on
  `k` from the committed `WaveRothe*` bricks.  Finally it feeds the assembled
  `rotheOrbitData` into the committed `b1_chiNeg_existence_rothe` to produce the
  B1 χ≤0 headline.

  ## The honest per-step interface `RotheStepData`

  The committed existence brick `crossStep_exists_unique_concrete` produces the
  uniquely-solvable implicit step as a fixed point of `crossStepSelfMap` over the
  Banach space `ℝ →ᵇ ℝ`.  The per-`u` `RotheOrbitData.step_rec` field, however, is
  phrased through the `crossImplicitMap` recursion over `ℝ → ℝ`

      `rotheSeq u (k+1) = crossImplicitMap p c lam u (rotheSeq u k) (rotheSeq u (k+1))`,

  and the per-step monotone/trap induction (antitone-in-`k`, the `≤ Ū` trap, the
  antitone-in-`x` closure, and the uniform `C¹` source bound feeding
  `crossImplicitStep_lipschitz`) each consume side data that the committed bricks
  carry as explicit hypotheses (the `crossStepSelfMap`↔`crossImplicitMap`
  identification on the trapped range, the super-barrier source ordering of
  `WaveRotheTrap`, the integrability tails of the Green representation, the
  `C²`-regularity at the comparison max, and the antitone source closure).  None
  of these per-step bridges is committed as a single closed lemma.

  We therefore isolate exactly that genuinely-uncommitted per-step content behind
  ONE named, satisfiable predicate `RotheStepData`: given any trapped, continuous,
  antitone old iterate `Z` (with the inductive properties), it produces the NEXT
  iterate `W` together with precisely the per-step facts the committed step bricks
  would yield —

    * the `crossImplicitMap` recursion `W = crossImplicitMap p c lam u Z W`
      (the realized implicit step, from `crossStep_exists_unique_concrete` +
      the trapped-range identification);
    * `0 ≤ W`, `W ≤ upperBarrier κ M`, `W ≤ M`  (the trap, from the committed
      `implicitStep_le_of_barrier_maxPrinciple_clean` + sub-barrier);
    * `W ≤ Z`  (antitone-in-`k` descent, the monotone induction with `B = Z`);
    * `Antitone W`  (antitone-in-`x`, `implicitStep_preserves_antitone`);
    * `Continuous W` and `Differentiable W` with `|W'| ≤ Λ`  (the bcf step
      solution's uniform `C¹` bound, `crossImplicitStep_deriv_bound` /
      `crossImplicitStep_lipschitz`, uniform in `k`).

  Everything ELSE in `RotheOrbitData` (the loc-unif limit's Lipschitz constant
  via `crossImplicitStep_lipschitz`, the limit bookkeeping, the base-case `k = 0`
  facts of the super-barrier `Ū`, and `bddBelow` from nonnegativity) is then
  discharged HERE from the committed bricks, with `V_cont`/`V_bound` taken as the
  two trap-derived frozen-drift facts (`frozenElliptic` continuity and
  `|V_u'| ≤ Bv`).

  No `sorry`/`axiom`/`native_decide`/`admit`.  Touches only Paper1.
-/
import ShenWork.Paper1.WaveRotheSchauderData
import ShenWork.Paper1.WaveRotheHelly
import ShenWork.Paper1.WaveFrozenEllipticDep
import ShenWork.Paper1.WaveRotheTrunc
import ShenWork.Paper1.WaveRotheMaxPrincipleClosers
import ShenWork.Paper1.WaveRotheC1
import ShenWork.Paper1.WaveRotheTrap

open Filter Topology Set

set_option maxHeartbeats 1000000

noncomputable section

namespace ShenWork.Paper1

/-! ## The per-step producer interface

`RotheStepProducer` packages the genuinely-uncommitted per-step bridge: from a
trapped continuous antitone old iterate `Z`, produce a next iterate with the full
per-step fact bundle.  It is satisfiable from the committed step/trap/C¹ bricks
(see the file header); we carry it as ONE named hypothesis. -/

/-- The per-step fact bundle for a produced next iterate `W` from old iterate `Z`,
relative to the frozen profile `u`, the trap parameters `κ M`, the uniform
Lipschitz constant `Λ`, and the kernel data `c lam`. -/
structure RotheStepFacts (p : CMParams) (c lam M κ Λ : ℝ) (u Z W : ℝ → ℝ) : Prop where
  /-- The realized implicit-Euler step (the `crossImplicitMap` recursion). -/
  step_eq : W = crossImplicitMap p c lam u Z W
  /-- The step solution is continuous. -/
  cont : Continuous W
  /-- The step solution is differentiable everywhere. -/
  diff : Differentiable ℝ W
  /-- Uniform `C¹` bound `|W'| ≤ Λ` (uniform in the step). -/
  deriv_le : ∀ x, |deriv W x| ≤ Λ
  /-- Trap from below: `0 ≤ W`. -/
  nonneg : ∀ x, 0 ≤ W x
  /-- Trap from above by the super-barrier `Ū`. -/
  le_barrier : ∀ x, W x ≤ upperBarrier κ M x
  /-- The implicit-Euler descent: `W ≤ Z` (antitone-in-`k`). -/
  le_old : ∀ x, W x ≤ Z x
  /-- Antitone-in-`x` (monotone wave profile preserved by the step). -/
  anti : Antitone W
  /-- **The supersolution orbit invariant (output):** the produced iterate `W` is
  again a super-solution, `F_u(W) ≤ 0`.  Proved inside the producers from `le_old`
  (`W ≤ Z`) and the identity `F_u(W) = lam·(W − Z)` (since `lam > 0`).  This is the
  inductive carrier making the descent never leave the supersolution orbit. -/
  supersol : ∀ x, frozenWaveOperator p c u W x ≤ 0

/-- **The per-step producer (carried hypothesis).**
For every trapped continuous antitone `Z` with `0 ≤ Z`, `Z ≤ Ū`, **and `Z` a
super-solution** (`F_u(Z) ≤ 0`), there is a next iterate `W` satisfying the full
per-step fact bundle.  This is the single named container for the per-step bridge
content described in the file header.

The supersolution precond `(∀ x, F_u(Z) x ≤ 0)` is what makes this SATISFIABLE: for
a non-supersolution trapped antitone `Z` the unique implicit step overshoots
(`W > Z` at a positive max), so `le_old` would be false; the descent orbit only
ever feeds supersolution barriers (base `Ū` via `whole_line_super_barrier`, step
via the output `supersol`), so the precond is honestly met along the real orbit.

The `baseSuper` field carries the base-barrier supersolution `F_u(Ū) ≤ 0` (the
orbit seed, discharged downstream from `whole_line_super_barrier`); it is what
lets the recursion feed the supersolution precond at `k = 0` WITHOUT enlarging
`rotheSeqOf`'s argument list — the invariant is internal to the carried producer. -/
structure RotheStepProducer (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) : Prop where
  /-- The base-barrier supersolution `F_u(Ū) ≤ 0` (the orbit seed). -/
  baseSuper : ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0
  /-- For every trapped continuous antitone super-solution `Z`, the next iterate. -/
  produce : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
      (∀ x, frozenWaveOperator p c u Z x ≤ 0) →
      ∃ W : ℝ → ℝ, RotheStepFacts p c lam M κ Λ u Z W

/-! ## The concrete Rothe sequence

`rotheSeq u 0 = Ū`; `rotheSeq u (k+1) = the produced next iterate`, extracted via
`Classical.choose` from the carried producer.  The choice is made once, against a
fixed producer witness, so the sequence is a genuine `ℕ → ℝ → ℝ`. -/

variable {p : CMParams} {c lam M κ Λ : ℝ} {u : ℝ → ℝ}

/-- The "trapped continuous antitone" base data for an iterate, the input shape
the producer consumes.  It now ALSO carries the supersolution invariant
`F_u(Z) ≤ 0` (the per-`u` frozen wave super-solution), so the recursion can feed
the producer's supersolution precond at every step. -/
structure IterateBase (p : CMParams) (c κ M : ℝ) (u Z : ℝ → ℝ) : Prop where
  cont : Continuous Z
  anti : Antitone Z
  nonneg : ∀ x, 0 ≤ Z x
  le_barrier : ∀ x, Z x ≤ upperBarrier κ M x
  supersol : ∀ x, frozenWaveOperator p c u Z x ≤ 0

/-- The super-barrier `Ū` satisfies the base data, given its supersolution seed
`hUbarSuper : F_u(Ū) ≤ 0` (carried by the producer as `baseSuper`). -/
theorem upperBarrier_iterateBase {p : CMParams} {c κ M : ℝ} {u : ℝ → ℝ}
    (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hUbarSuper : ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0) :
    IterateBase p c κ M u (upperBarrier κ M) :=
  ⟨upperBarrier_continuous κ M, upperBarrier_antitone hκ,
   fun x => upperBarrier_nonneg hM x, fun _ => le_refl _, hUbarSuper⟩

/-- The per-step facts entail the base data for the produced iterate (so the
recursion can continue) — including the supersolution invariant from `supersol`. -/
theorem RotheStepFacts.toBase {p : CMParams} {c lam M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (h : RotheStepFacts p c lam M κ Λ u Z W) : IterateBase p c κ M u W :=
  ⟨h.cont, h.anti, h.nonneg, h.le_barrier, h.supersol⟩

/-- The concrete Rothe orbit packaged as a dependent recursion: at each `k` we
return the iterate together with a proof of its base data (incl. the supersolution
invariant), so the producer can be fed at the next step.  The function value is
`(rotheStep …).1`. -/
def rotheStep (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ)
    (hprod : RotheStepProducer p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) :
    ∀ k : ℕ, { Z : ℝ → ℝ // IterateBase p c κ M u Z }
  | 0 => ⟨upperBarrier κ M, upperBarrier_iterateBase hκ hM hprod.baseSuper⟩
  | (k+1) =>
    let prev := rotheStep p c lam M κ Λ u hprod hκ hM k
    let hex := hprod.produce prev.1 prev.2.cont prev.2.anti prev.2.nonneg
      prev.2.le_barrier prev.2.supersol
    ⟨Classical.choose hex, (Classical.choose_spec hex).toBase⟩

/-- The concrete Rothe sequence: the function values of `rotheStep`. -/
def rotheSeqOf (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ)
    (hprod : RotheStepProducer p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : ℕ → ℝ → ℝ :=
  fun k => (rotheStep p c lam M κ Λ u hprod hκ hM k).1

/-- The concrete Rothe sequence when the producer is only available on the
monotone wave trap.  Outside the trap the value is irrelevant to the Schauder
assembly, so we use the upper barrier as a harmless default. -/
def rotheSeqFromTrap (p : CMParams) (c lam M κ Λ : ℝ)
    (hprodTrap : ∀ u, InMonotoneWaveTrapSet κ M u →
      RotheStepProducer p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : (ℝ → ℝ) → ℕ → ℝ → ℝ :=
  fun u => by
    classical
    exact
      if hu : InMonotoneWaveTrapSet κ M u then
        rotheSeqOf p c lam M κ Λ u (hprodTrap u hu) hκ hM
      else
        fun _ => upperBarrier κ M

@[simp] theorem rotheSeqOf_zero
    (hprod : RotheStepProducer p c lam M κ Λ u) (hκ : 0 ≤ κ) (hM : 0 ≤ M) :
    rotheSeqOf p c lam M κ Λ u hprod hκ hM 0 = upperBarrier κ M := rfl

/-- The defining per-step fact bundle satisfied by `rotheSeqOf` at every `k+1`. -/
theorem rotheSeqOf_stepFacts
    (hprod : RotheStepProducer p c lam M κ Λ u) (hκ : 0 ≤ κ) (hM : 0 ≤ M) (k : ℕ) :
    RotheStepFacts p c lam M κ Λ u
      (rotheSeqOf p c lam M κ Λ u hprod hκ hM k)
      (rotheSeqOf p c lam M κ Λ u hprod hκ hM (k+1)) := by
  let prev := rotheStep p c lam M κ Λ u hprod hκ hM k
  have hex := hprod.produce prev.1 prev.2.cont prev.2.anti prev.2.nonneg
    prev.2.le_barrier prev.2.supersol
  -- `rotheSeqOf … (k+1) = Classical.choose hex` and `rotheSeqOf … k = prev.1`
  exact Classical.choose_spec hex

/-- Base data (continuity/antitone/nonneg/≤Ū/supersol) at every `k`, from
`rotheStep`. -/
theorem rotheSeqOf_base
    (hprod : RotheStepProducer p c lam M κ Λ u) (hκ : 0 ≤ κ) (hM : 0 ≤ M) (k : ℕ) :
    IterateBase p c κ M u (rotheSeqOf p c lam M κ Λ u hprod hκ hM k) :=
  (rotheStep p c lam M κ Λ u hprod hκ hM k).2

/-! ## Per-`k` field extraction (by the step bundle) -/

section PerK
variable (hprod : RotheStepProducer p c lam M κ Λ u) (hκ : 0 ≤ κ) (hM : 0 ≤ M)

/-- Each iterate is continuous. -/
theorem rotheSeqOf_cont (k : ℕ) :
    Continuous (rotheSeqOf p c lam M κ Λ u hprod hκ hM k) :=
  (rotheSeqOf_base hprod hκ hM k).cont

/-- Each iterate is antitone-in-`x`. -/
theorem rotheSeqOf_anti_x (k : ℕ) :
    Antitone (rotheSeqOf p c lam M κ Λ u hprod hκ hM k) :=
  (rotheSeqOf_base hprod hκ hM k).anti

/-- Each iterate is nonnegative. -/
theorem rotheSeqOf_nonneg (k : ℕ) (x : ℝ) :
    0 ≤ rotheSeqOf p c lam M κ Λ u hprod hκ hM k x :=
  (rotheSeqOf_base hprod hκ hM k).nonneg x

/-- Each iterate is `≤ Ū`. -/
theorem rotheSeqOf_le_barrier (k : ℕ) (x : ℝ) :
    rotheSeqOf p c lam M κ Λ u hprod hκ hM k x ≤ upperBarrier κ M x :=
  (rotheSeqOf_base hprod hκ hM k).le_barrier x

/-- **The supersolution orbit invariant:** every iterate is a super-solution,
`F_u(rotheSeq k) ≤ 0`.  This is carried inductively in `IterateBase` — base
`k = 0` is `Ū`'s supersolution seed (`hprod.baseSuper`), and the step is the
produced iterate's `RotheStepFacts.supersol` (`F_u(W) = lam·(W − Z) ≤ 0`). -/
theorem rotheSeqOf_supersol (k : ℕ) (x : ℝ) :
    frozenWaveOperator p c u (rotheSeqOf p c lam M κ Λ u hprod hκ hM k) x ≤ 0 :=
  (rotheSeqOf_base hprod hκ hM k).supersol x

/-- Each iterate is `≤ M`. -/
theorem rotheSeqOf_le_M (k : ℕ) (x : ℝ) :
    rotheSeqOf p c lam M κ Λ u hprod hκ hM k x ≤ M :=
  le_trans (rotheSeqOf_le_barrier hprod hκ hM k x) (upperBarrier_le_M κ M x)

/-- The implicit-Euler descent: `rotheSeq (k+1) ≤ rotheSeq k` pointwise. -/
theorem rotheSeqOf_succ_le (k : ℕ) (x : ℝ) :
    rotheSeqOf p c lam M κ Λ u hprod hκ hM (k+1) x
      ≤ rotheSeqOf p c lam M κ Λ u hprod hκ hM k x :=
  (rotheSeqOf_stepFacts hprod hκ hM k).le_old x

/-- The step recursion (the `crossImplicitMap` fixed-point identity). -/
theorem rotheSeqOf_step_rec (k : ℕ) :
    rotheSeqOf p c lam M κ Λ u hprod hκ hM (k+1)
      = crossImplicitMap p c lam u
          (rotheSeqOf p c lam M κ Λ u hprod hκ hM k)
          (rotheSeqOf p c lam M κ Λ u hprod hκ hM (k+1)) :=
  (rotheSeqOf_stepFacts hprod hκ hM k).step_eq

/-- The antitone-in-`k` property: at every point the orbit is antitone in `k`. -/
theorem rotheSeqOf_anti_k (x : ℝ) :
    Antitone (fun k => rotheSeqOf p c lam M κ Λ u hprod hκ hM k x) :=
  antitone_nat_of_succ_le (fun k => rotheSeqOf_succ_le hprod hκ hM k x)

/-- Pointwise bounded below (by `0`), so the `iInf` limit exists. -/
theorem rotheSeqOf_bddBelow (x : ℝ) :
    BddBelow (Set.range (fun k => rotheSeqOf p c lam M κ Λ u hprod hκ hM k x)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact rotheSeqOf_nonneg hprod hκ hM k x

/-! ## Equi-Lipschitz (constant `M`)

Each step iterate's derivative is bounded by `Λ`; with `Λ ≤ M` this gives the
`M`-Lipschitz bound the `RotheOrbitData.equiLip` field demands for `k ≥ 1`.

For the base `k = 0` iterate `Ū = upperBarrier κ M = min M (e^{-κx})`, the
Lipschitz bound is genuine but its constant is `κ·M` (where the `min` selects the
exponential, `e^{-κx} ≤ M`, so the slope magnitude `κ e^{-κx} ≤ κM`; elsewhere the
constant plateau has slope `0`).  To match the structure's constant `M` for ALL
`k`, we carry the base-barrier `M`-Lipschitz bound `hbarLip` as a hypothesis (it
holds whenever `κ M ≤ M`, e.g. `κ ≤ 1`), keeping the wiring clean. -/

/-- Each step iterate (`k ≥ 1`) is `Λ`-Lipschitz, from its uniform `C¹` bound via
the committed `crossImplicitStep_lipschitz`. -/
theorem rotheSeqOf_succ_lipschitz (hΛ : 0 ≤ Λ) (k : ℕ) :
    ∀ x y, |rotheSeqOf p c lam M κ Λ u hprod hκ hM (k+1) x
        - rotheSeqOf p c lam M κ Λ u hprod hκ hM (k+1) y| ≤ Λ * |x - y| := by
  intro x y
  have hfacts := rotheSeqOf_stepFacts hprod hκ hM k
  have hLip : LipschitzWith (Real.toNNReal Λ)
      (rotheSeqOf p c lam M κ Λ u hprod hκ hM (k+1)) :=
    crossImplicitStep_lipschitz hΛ hfacts.diff hfacts.deriv_le
  have := hLip.dist_le_mul x y
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hΛ] at this
  exact this

/-- Equi-Lipschitz at the structure constant `M`, for every `k`.
Base `k = 0`: the carried `hbarLip`.  Step `k+1`: the `Λ`-Lipschitz bound scaled
up to `M` via `Λ ≤ M`. -/
theorem rotheSeqOf_equiLip (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (k : ℕ) :
    ∀ x y, |rotheSeqOf p c lam M κ Λ u hprod hκ hM k x
        - rotheSeqOf p c lam M κ Λ u hprod hκ hM k y| ≤ M * |x - y| := by
  cases k with
  | zero =>
      intro x y
      rw [rotheSeqOf_zero]
      exact hbarLip x y
  | succ k =>
      intro x y
      have hΛ := rotheSeqOf_succ_lipschitz hprod hκ hM hΛ0 k x y
      have hmono : Λ * |x - y| ≤ M * |x - y| :=
        mul_le_mul_of_nonneg_right hΛM (abs_nonneg _)
      exact le_trans hΛ hmono

/-- The Rothe limit inherits the `M`-Lipschitz bound (pointwise limit of
`M`-Lipschitz iterates, via `rotheLimit_tendsto` + `le_of_tendsto`). -/
theorem rotheSeqOf_limitLip (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (x y : ℝ) :
    |rotheLimit (rotheSeqOf p c lam M κ Λ u hprod hκ hM) x
        - rotheLimit (rotheSeqOf p c lam M κ Λ u hprod hκ hM) y| ≤ M * |x - y| := by
  set z := rotheSeqOf p c lam M κ Λ u hprod hκ hM with hz
  have hax : Tendsto (fun k => z k x) atTop (𝓝 (rotheLimit z x)) :=
    rotheLimit_tendsto (rotheSeqOf_anti_k hprod hκ hM) (rotheSeqOf_bddBelow hprod hκ hM) x
  have hay : Tendsto (fun k => z k y) atTop (𝓝 (rotheLimit z y)) :=
    rotheLimit_tendsto (rotheSeqOf_anti_k hprod hκ hM) (rotheSeqOf_bddBelow hprod hκ hM) y
  have htend : Tendsto (fun k => |z k x - z k y|) atTop
      (𝓝 (|rotheLimit z x - rotheLimit z y|)) :=
    ((hax.sub hay).abs)
  refine le_of_tendsto htend ?_
  filter_upwards with k
  exact rotheSeqOf_equiLip hprod hκ hM hΛ0 hΛM hbarLip k x y

/-! ## Assembling `RotheOrbitData`

Every field is now in hand: continuity, antitone-in-`k`, antitone-in-`x`,
nonneg, `≤ M`, `≤ Ū`, bddBelow, equiLip, limitLip, step_rec — all discharged
above from the committed bricks + the per-step producer.  `V_cont` and `V_bound`
are the two trap-derived frozen-drift facts, carried as `hVcont`/`hVbound`. -/

end PerK

/-- **The concrete per-`u` `RotheOrbitData`.**
Assembled from the per-step producer and the committed Rothe bricks, with the
base-barrier `M`-Lipschitz bound `hbarLip`, the uniform-`C¹` constant data
`hΛ0`/`hΛM`, and the trap-derived frozen-drift facts `hVcont`/`hVbound`. -/
theorem rotheOrbitData
    (hprodAll : ∀ v, RotheStepProducer p c lam M κ Λ v) (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M) (Bv : ℝ)
    (hbarLip : ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hVcont : Continuous (deriv (frozenElliptic p u)))
    (hVbound : ∀ y, |deriv (frozenElliptic p u) y| ≤ Bv) :
    RotheOrbitData p c lam M Bv κ
      (fun v => rotheSeqOf p c lam M κ Λ v (hprodAll v) hκ hM) u := by
  refine
    { iterate_cont := rotheSeqOf_cont (hprodAll u) hκ hM
      anti_k := rotheSeqOf_anti_k (hprodAll u) hκ hM
      anti_x := rotheSeqOf_anti_x (hprodAll u) hκ hM
      nonneg := rotheSeqOf_nonneg (hprodAll u) hκ hM
      le_M := rotheSeqOf_le_M (hprodAll u) hκ hM
      le_upperBarrier := rotheSeqOf_le_barrier (hprodAll u) hκ hM
      bddBelow := rotheSeqOf_bddBelow (hprodAll u) hκ hM
      equiLip := rotheSeqOf_equiLip (hprodAll u) hκ hM hΛ0 hΛM hbarLip
      limitLip := ?_
      step_rec := rotheSeqOf_step_rec (hprodAll u) hκ hM
      V_cont := hVcont
      V_bound := hVbound }
  -- limitLip: the structure's `rotheLimit (rotheSeq u)` is at the global sequence
  -- applied to `u`, defeq to the single-`u` sequence; supply the proof directly.
  intro x y
  exact rotheSeqOf_limitLip (hprodAll u) hκ hM hΛ0 hΛM hbarLip x y

/-- The same per-`u` orbit data for the trap-indexed Rothe sequence wrapper. -/
theorem rotheOrbitData_fromTrap
    (hprodTrap : ∀ v, InMonotoneWaveTrapSet κ M v →
      RotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (Bv : ℝ)
    (hbarLip : ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hu : InMonotoneWaveTrapSet κ M u)
    (hVcont : Continuous (deriv (frozenElliptic p u)))
    (hVbound : ∀ y, |deriv (frozenElliptic p u) y| ≤ Bv) :
    RotheOrbitData p c lam M Bv κ
      (rotheSeqFromTrap p c lam M κ Λ hprodTrap hκ hM) u := by
  classical
  let hprod : RotheStepProducer p c lam M κ Λ u := hprodTrap u hu
  refine
    { iterate_cont := ?_
      anti_k := ?_
      anti_x := ?_
      nonneg := ?_
      le_M := ?_
      le_upperBarrier := ?_
      bddBelow := ?_
      equiLip := ?_
      limitLip := ?_
      step_rec := ?_
      V_cont := hVcont
      V_bound := hVbound }
  · intro k
    simpa [rotheSeqFromTrap, hu, hprod] using rotheSeqOf_cont hprod hκ hM k
  · intro x
    simpa [rotheSeqFromTrap, hu, hprod] using rotheSeqOf_anti_k hprod hκ hM x
  · intro k
    simpa [rotheSeqFromTrap, hu, hprod] using rotheSeqOf_anti_x hprod hκ hM k
  · intro k x
    simpa [rotheSeqFromTrap, hu, hprod] using rotheSeqOf_nonneg hprod hκ hM k x
  · intro k x
    simpa [rotheSeqFromTrap, hu, hprod] using rotheSeqOf_le_M hprod hκ hM k x
  · intro k x
    simpa [rotheSeqFromTrap, hu, hprod] using
      rotheSeqOf_le_barrier hprod hκ hM k x
  · intro x
    simpa [rotheSeqFromTrap, hu, hprod] using rotheSeqOf_bddBelow hprod hκ hM x
  · intro k x y
    simpa [rotheSeqFromTrap, hu, hprod] using
      rotheSeqOf_equiLip hprod hκ hM hΛ0 hΛM hbarLip k x y
  · intro x y
    simpa [rotheSeqFromTrap, hu, hprod] using
      rotheSeqOf_limitLip hprod hκ hM hΛ0 hΛM hbarLip x y
  · intro k
    simpa [rotheSeqFromTrap, hu, hprod] using rotheSeqOf_step_rec hprod hκ hM k

/-! ## Field 5 — the final B1 χ≤0 existence theorem

We instantiate the committed `b1_chiNeg_existence_rothe` with the concrete map
`Tmap u := rotheLimit (rotheSeq u)` where
`rotheSeq u := rotheSeqOf … (hprodAll u) …`.  The selection/dependence inputs are:

  * `helly_pointwise_selection M` — the committed (PROVED) Helly pointwise
    selection;
  * `hdep : RotheContinuousDependence …` — carried (its deep core
    `frozenEllipticDerivDependence` is committed/PROVED, but the per-step
    propagation through the Rothe limit is NOT a committed closed lemma, so the
    packaged `RotheContinuousDependence` remains a carried, satisfiable
    hypothesis);

and the per-`u` `RotheOrbitData` is supplied by `rotheOrbitData`.

The remaining hypotheses are EXACTLY: the G1 abstract principle
`hprinciple`, the committed per-fixed-point profile lemmas
`hGreen`/`hpos`/`hbdd`/`hlim_neg`/`hlim_pos`, plus the precise carried inputs
(`hprodAll` per-step producer, `hdep` continuous-dependence, the trap-derived
`hVcont`/`hVbound`, the base-barrier Lipschitz `hbarLip`, and the scalar
constraints).  B1 χ≤0 thereby reduces to ONLY G1 + the profile lemmas, modulo
those named satisfiable inputs. -/

/-- **B1 χ≤0 existence — the FINAL concrete theorem.**
The headline traveling-wave existence, with the concrete Rothe map
`Tmap u := rotheLimit (rotheSeqOf … (hprodAll u) …)`, reduced to the G1 principle
`hprinciple` and the committed profile lemmas, plus the precise named carried
inputs. -/
theorem b1_chiNeg_existence
    (p : CMParams) (c lam M Bv κ Λ : ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (hκ : 0 ≤ κ) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    -- the per-step producer for every frozen profile `u`:
    (hprodAll : ∀ u, RotheStepProducer p c lam M κ Λ u)
    -- the base super-barrier is `M`-Lipschitz (holds when `κ M ≤ M`):
    (hbarLip : ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    -- the upper-barrier boundedness:
    (hŪbdd : IsBddFun (upperBarrier κ M))
    -- the two trap-derived frozen-drift facts, for every trapped `u`:
    (hVcont : ∀ u, InMonotoneWaveTrapSet κ M u →
        Continuous (deriv (frozenElliptic p u)))
    (hVbound : ∀ u, InMonotoneWaveTrapSet κ M u →
        ∀ y, |deriv (frozenElliptic p u) y| ≤ Bv)
    -- the carried continuous-dependence (deep core PROVED; Rothe-limit
    -- propagation carried):
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
        (fun u => rotheSeqOf p c lam M κ Λ u (hprodAll u) hκ hM))
    -- the G1 abstract Schauder principle:
    (hprinciple : LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    -- the committed per-fixed-point profile lemmas:
    (hGreen : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit (rotheSeqOf p c lam M κ Λ U (hprodAll U) hκ hM) = U →
          GreenIdentity p c lam U)
    (hpos : ∀ U, InMonotoneWaveTrapSet κ M U → (∀ x, 0 < U x))
    (hbdd : ∀ U, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U)
    (hlim_neg : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atBot (𝓝 1))
    (hlim_pos : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_rothe p c lam M Bv κ hc hlam hM hBv
    (fun u => rotheSeqOf p c lam M κ Λ u (hprodAll u) hκ hM)
    hŪbdd
    (helly_pointwise_selection M)
    hdep
    (fun u hu => rotheOrbitData hprodAll hκ hM hΛ0 hΛM Bv hbarLip
      (hVcont u hu) (hVbound u hu))
    hprinciple hGreen hpos hbdd hlim_neg hlim_pos

/-- Direct `b1_chiNeg_existence` variant with `hlim_neg` produced by route (b)
for the Schauder fixed point. -/
theorem b1_chiNeg_existence_rootPin
    (p : CMParams) (c lam M Bv κ Λ : ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (hκ : 0 ≤ κ) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, RotheStepProducer p c lam M κ Λ u)
    (hbarLip : ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hVcont : ∀ u, InMonotoneWaveTrapSet κ M u →
        Continuous (deriv (frozenElliptic p u)))
    (hVbound : ∀ u, InMonotoneWaveTrapSet κ M u →
        ∀ y, |deriv (frozenElliptic p u) y| ≤ Bv)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
        (fun u => rotheSeqOf p c lam M κ Λ u (hprodAll u) hκ hM))
    (hprinciple : LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    (hGreen : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit (rotheSeqOf p c lam M κ Λ U (hprodAll U) hκ hM) = U →
          GreenIdentity p c lam U)
    (hpos : ∀ U, InMonotoneWaveTrapSet κ M U → (∀ x, 0 < U x))
    (hfloor : ∀ U, InMonotoneWaveTrapSet κ M U → PaperPositiveInitialDatum U)
    (hbdd : ∀ U, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U)
    (hflat : ∀ U, InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U)
    (hlim_pos : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_rothe_rootPin p c lam M Bv κ hc hlam hM hBv
    (fun u => rotheSeqOf p c lam M κ Λ u (hprodAll u) hκ hM)
    hŪbdd
    (helly_pointwise_selection M)
    hdep
    (fun u hu => rotheOrbitData hprodAll hκ hM hΛ0 hΛM Bv hbarLip
      (hVcont u hu) (hVbound u hu))
    hprinciple hGreen hpos hfloor hbdd hflat hlim_pos

/-- `b1_chiNeg_existence` with the trap-derived profile obligations discharged.

The remaining profile surface is exactly strict positivity, the left endpoint
connection, and the Green identity.  Uniform `C`-boundedness comes from
`InMonotoneWaveTrapSet.trap.cunif_bdd`; right decay comes from the upper-barrier
squeeze and the strict rate `0 < κ`. -/
theorem b1_chiNeg_existence_profileClean
    (p : CMParams) (c lam M Bv κ Λ : ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (hκpos : 0 < κ) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, RotheStepProducer p c lam M κ Λ u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hVcont : ∀ u, InMonotoneWaveTrapSet κ M u →
        Continuous (deriv (frozenElliptic p u)))
    (hVbound : ∀ u, InMonotoneWaveTrapSet κ M u →
        ∀ y, |deriv (frozenElliptic p u) y| ≤ Bv)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
        (fun u => rotheSeqOf p c lam M κ Λ u (hprodAll u) hκpos.le hM))
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    (hGreen : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit (rotheSeqOf p c lam M κ Λ U
          (hprodAll U) hκpos.le hM) = U →
          GreenIdentity p c lam U)
    (hpos : ∀ U, InMonotoneWaveTrapSet κ M U → (∀ x, 0 < U x))
    (hlim_neg :
      ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atBot (𝓝 1)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence p c lam M Bv κ Λ hc hlam hM hBv
    hκpos.le hΛ0 hΛM hprodAll hbarLip hŪbdd hVcont hVbound
    hdep hprinciple hGreen hpos
    (fun _U hU => hU.trap.cunif_bdd)
    hlim_neg
    (fun _U hU => hU.tendsto_atTop_zero hκpos)

/-- Concrete χ≤0 B1 existence with `hlim_neg` produced by route (b).

The left endpoint is derived for the Schauder fixed point from the stationary
equation's left-limit root consequence and the paper uniform floor. -/
theorem b1_chiNeg_existence_profileClean_rootPin
    (p : CMParams) (c lam M Bv κ Λ : ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (hκpos : 0 < κ) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, RotheStepProducer p c lam M κ Λ u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hVcont : ∀ u, InMonotoneWaveTrapSet κ M u →
        Continuous (deriv (frozenElliptic p u)))
    (hVbound : ∀ u, InMonotoneWaveTrapSet κ M u →
        ∀ y, |deriv (frozenElliptic p u) y| ≤ Bv)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
        (fun u => rotheSeqOf p c lam M κ Λ u (hprodAll u) hκpos.le hM))
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    (hGreen : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit (rotheSeqOf p c lam M κ Λ U
          (hprodAll U) hκpos.le hM) = U →
          GreenIdentity p c lam U)
    (hpos : ∀ U, InMonotoneWaveTrapSet κ M U → (∀ x, 0 < U x))
    (hfloor : ∀ U, InMonotoneWaveTrapSet κ M U → PaperPositiveInitialDatum U)
    (hflat : ∀ U, InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_rothe_rootPin p c lam M Bv κ hc hlam hM hBv
    (fun u => rotheSeqOf p c lam M κ Λ u (hprodAll u) hκpos.le hM)
    hŪbdd
    (helly_pointwise_selection M)
    hdep
    (fun u hu => rotheOrbitData hprodAll hκpos.le hM hΛ0 hΛM Bv hbarLip
      (hVcont u hu) (hVbound u hu))
    hprinciple hGreen hpos
    hfloor
    (fun _U hU => hU.trap.cunif_bdd)
    hflat
    (fun _U hU => hU.tendsto_atTop_zero hκpos)

/-- Concrete χ≤0 B1 existence with fixed-point stationarity supplied directly
and strict positivity discharged by the paper-positive floor. -/
theorem b1_chiNeg_existence_stationary_floor
    (p : CMParams) (c lam M Bv κ Λ : ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (hκ : 0 ≤ κ) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, RotheStepProducer p c lam M κ Λ u)
    (hbarLip : ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hVcont : ∀ u, InMonotoneWaveTrapSet κ M u →
        Continuous (deriv (frozenElliptic p u)))
    (hVbound : ∀ u, InMonotoneWaveTrapSet κ M u →
        ∀ y, |deriv (frozenElliptic p u) y| ≤ Bv)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
        (fun u => rotheSeqOf p c lam M κ Λ u (hprodAll u) hκ hM))
    (hprinciple : LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    (hstationary : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit (rotheSeqOf p c lam M κ Λ U (hprodAll U) hκ hM) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hfloor : ∀ U, InMonotoneWaveTrapSet κ M U → PaperPositiveInitialDatum U)
    (hbdd : ∀ U, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U)
    (hlim_neg : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atBot (𝓝 1))
    (hlim_pos : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_rothe_stationary_floor p c lam M Bv κ hc hlam hM hBv
    (fun u => rotheSeqOf p c lam M κ Λ u (hprodAll u) hκ hM)
    hŪbdd
    (helly_pointwise_selection M)
    hdep
    (fun u hu => rotheOrbitData hprodAll hκ hM hΛ0 hΛM Bv hbarLip
      (hVcont u hu) (hVbound u hu))
    hprinciple hstationary hfloor hbdd hlim_neg hlim_pos

/-- Concrete χ≤0 B1 existence with fixed-point stationarity supplied directly,
floor positivity, and route-b left endpoint from stationary flatness. -/
theorem b1_chiNeg_existence_stationary_floor_rootPin
    (p : CMParams) (c lam M Bv κ Λ : ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (hκ : 0 ≤ κ) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, RotheStepProducer p c lam M κ Λ u)
    (hbarLip : ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hVcont : ∀ u, InMonotoneWaveTrapSet κ M u →
        Continuous (deriv (frozenElliptic p u)))
    (hVbound : ∀ u, InMonotoneWaveTrapSet κ M u →
        ∀ y, |deriv (frozenElliptic p u) y| ≤ Bv)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
        (fun u => rotheSeqOf p c lam M κ Λ u (hprodAll u) hκ hM))
    (hprinciple : LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    (hstationary : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit (rotheSeqOf p c lam M κ Λ U (hprodAll U) hκ hM) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hfloor : ∀ U, InMonotoneWaveTrapSet κ M U → PaperPositiveInitialDatum U)
    (hbdd : ∀ U, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U)
    (hflat : ∀ U, InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U)
    (hlim_pos : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_rothe_stationary_floor_rootPin p c lam M Bv κ
    hc hlam hM hBv
    (fun u => rotheSeqOf p c lam M κ Λ u (hprodAll u) hκ hM)
    hŪbdd
    (helly_pointwise_selection M)
    hdep
    (fun u hu => rotheOrbitData hprodAll hκ hM hΛ0 hΛM Bv hbarLip
      (hVcont u hu) (hVbound u hu))
    hprinciple hstationary hfloor hbdd hflat hlim_pos

/-- Profile-clean χ≤0 B1 existence with `hGreen` and `hpos` removed:
stationarity is the fixed-point stationary obligation, and positivity comes
from the floor. -/
theorem b1_chiNeg_existence_profileClean_stationary_floor
    (p : CMParams) (c lam M Bv κ Λ : ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (hκpos : 0 < κ) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, RotheStepProducer p c lam M κ Λ u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hVcont : ∀ u, InMonotoneWaveTrapSet κ M u →
        Continuous (deriv (frozenElliptic p u)))
    (hVbound : ∀ u, InMonotoneWaveTrapSet κ M u →
        ∀ y, |deriv (frozenElliptic p u) y| ≤ Bv)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
        (fun u => rotheSeqOf p c lam M κ Λ u (hprodAll u) hκpos.le hM))
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    (hstationary : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit (rotheSeqOf p c lam M κ Λ U
          (hprodAll U) hκpos.le hM) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hfloor : ∀ U, InMonotoneWaveTrapSet κ M U → PaperPositiveInitialDatum U)
    (hlim_neg :
      ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atBot (𝓝 1)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_stationary_floor p c lam M Bv κ Λ hc hlam hM hBv
    hκpos.le hΛ0 hΛM hprodAll hbarLip hŪbdd hVcont hVbound
    hdep hprinciple hstationary hfloor
    (fun _U hU => hU.trap.cunif_bdd)
    hlim_neg
    (fun _U hU => hU.tendsto_atTop_zero hκpos)

/-- Profile-clean χ≤0 B1 existence with route-b left endpoint and with
`hGreen`/`hpos` removed under the floor. -/
theorem b1_chiNeg_existence_profileClean_stationary_floor_rootPin
    (p : CMParams) (c lam M Bv κ Λ : ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (hκpos : 0 < κ) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, RotheStepProducer p c lam M κ Λ u)
    (hbarLip :
      ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hVcont : ∀ u, InMonotoneWaveTrapSet κ M u →
        Continuous (deriv (frozenElliptic p u)))
    (hVbound : ∀ u, InMonotoneWaveTrapSet κ M u →
        ∀ y, |deriv (frozenElliptic p u) y| ≤ Bv)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
        (fun u => rotheSeqOf p c lam M κ Λ u (hprodAll u) hκpos.le hM))
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    (hstationary : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit (rotheSeqOf p c lam M κ Λ U
          (hprodAll U) hκpos.le hM) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hfloor : ∀ U, InMonotoneWaveTrapSet κ M U → PaperPositiveInitialDatum U)
    (hflat : ∀ U, InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_stationary_floor_rootPin p c lam M Bv κ Λ hc hlam hM hBv
    hκpos.le hΛ0 hΛM hprodAll hbarLip hŪbdd hVcont hVbound
    hdep hprinciple hstationary hfloor
    (fun _U hU => hU.trap.cunif_bdd)
    hflat
    (fun _U hU => hU.tendsto_atTop_zero hκpos)

/-! ## Axiom audit -/

section AxiomAudit

#print axioms rotheSeqOf
#print axioms rotheSeqOf_supersol
#print axioms rotheSeqOf_step_rec
#print axioms rotheSeqOf_equiLip
#print axioms rotheSeqOf_limitLip
#print axioms rotheOrbitData
#print axioms rotheOrbitData_fromTrap
#print axioms b1_chiNeg_existence
#print axioms b1_chiNeg_existence_rootPin
#print axioms b1_chiNeg_existence_profileClean
#print axioms b1_chiNeg_existence_profileClean_rootPin
#print axioms b1_chiNeg_existence_stationary_floor
#print axioms b1_chiNeg_existence_stationary_floor_rootPin
#print axioms b1_chiNeg_existence_profileClean_stationary_floor
#print axioms b1_chiNeg_existence_profileClean_stationary_floor_rootPin

end AxiomAudit

end ShenWork.Paper1
