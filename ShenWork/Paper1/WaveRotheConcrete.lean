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

/-- Base of the lower-pinned induction: the concrete Rothe seed is the upper
barrier, and every pinned frozen input lies below that barrier. -/
theorem rotheSeqOf_lowerPinned_base
    {p : CMParams} {c lam M κ Λ : ℝ} {φ u : ℝ → ℝ}
    (hprod : RotheStepProducer p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hu : InLowerPinnedMonotoneTrap κ M φ u) :
    ∀ x, φ x ≤ rotheSeqOf p c lam M κ Λ u hprod hκ hM 0 x := by
  intro x
  rw [rotheSeqOf_zero]
  exact le_trans (hu.lower x) (hu.bare.le_upperBarrier x)

/-! ## The paper-step Rothe sequence

The committed `rotheSeqOf` above is the frozen implicit step.  The paper lower
barrier comparison uses the paper implicit operator instead, so we keep a
separate lightweight paper-step orbit.  It records only the trap shape and the
paper step equation; no frozen Schauder data is claimed for this orbit here. -/

/-! ## Exponential left-rate bookkeeping -/

/-- Exponential approach to a prescribed left limit. -/
def ExpLeftRate (sigma aL C : ℝ) (f : ℝ → ℝ) (ell : ℝ) : Prop :=
  ∀ x, |f x - ell| ≤ C * Real.exp (sigma * (x - aL))

/-- The exponential left-tail modulus used by the Route-A+ source box. -/
def expLeftOmega (sigma aL K : ℝ) : ℝ → ℝ :=
  fun A => K * Real.exp (sigma * (A - aL))

/-- A packaged exponential left-rate invariant for an orbit iterate. -/
def ExpLeftRateData (f : ℝ → ℝ) : Prop :=
  ∃ sigma aL C ell : ℝ, 0 < sigma ∧ ExpLeftRate sigma aL C f ell

namespace ExpLeftRate

theorem C_nonneg {sigma aL C : ℝ} {f : ℝ → ℝ} {ell : ℝ}
    (h : ExpLeftRate sigma aL C f ell) : 0 ≤ C := by
  have hx := h aL
  have hzero : sigma * (aL - aL) = 0 := by ring
  have hle : |f aL - ell| ≤ C := by
    simpa [ExpLeftRate, hzero] using hx
  exact le_trans (abs_nonneg _) hle

/-- An exponential left-rate bound gives the box's uniform left-tail Cauchy
field with the corresponding exponential modulus. -/
theorem leftTailCauchy {sigma aL C : ℝ} {f : ℝ → ℝ} {ell : ℝ}
    (hsigma : 0 ≤ sigma) (h : ExpLeftRate sigma aL C f ell) :
    ∀ A, A ≤ aL → ∀ x y, x ≤ A → y ≤ A →
      |f x - f y| ≤ 2 * C * Real.exp (sigma * (A - aL)) := by
  intro A hA x y hx hy
  have hC : 0 ≤ C := h.C_nonneg
  have hxexp :
      Real.exp (sigma * (x - aL)) ≤ Real.exp (sigma * (A - aL)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by linarith) hsigma
  have hyexp :
      Real.exp (sigma * (y - aL)) ≤ Real.exp (sigma * (A - aL)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by linarith) hsigma
  calc
    |f x - f y| = |(f x - ell) + (ell - f y)| := by ring_nf
    _ ≤ |f x - ell| + |ell - f y| := abs_add_le _ _
    _ = |f x - ell| + |f y - ell| := by rw [abs_sub_comm ell (f y)]
    _ ≤ C * Real.exp (sigma * (x - aL)) +
        C * Real.exp (sigma * (y - aL)) :=
      add_le_add (h x) (h y)
    _ ≤ C * Real.exp (sigma * (A - aL)) +
        C * Real.exp (sigma * (A - aL)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hxexp hC)
        (mul_le_mul_of_nonneg_left hyexp hC)
    _ = 2 * C * Real.exp (sigma * (A - aL)) := by ring

end ExpLeftRate

theorem expLeftOmega_nonneg {sigma aL K : ℝ} (hK : 0 ≤ K) :
    ∀ A, 0 ≤ expLeftOmega sigma aL K A := by
  intro A
  exact mul_nonneg hK (Real.exp_pos _).le

theorem expLeftOmega_tendsto_atBot {sigma aL K : ℝ} (hsigma : 0 < sigma) :
    Tendsto (expLeftOmega sigma aL K) atBot (𝓝 0) := by
  have hsub : Tendsto (fun A : ℝ => A - aL) atBot atBot := by
    simpa [sub_eq_add_neg] using
      tendsto_atBot_add_const_right atBot (-aL)
        (tendsto_id : Tendsto (fun A : ℝ => A) atBot atBot)
  have hlin : Tendsto (fun A : ℝ => sigma * (A - aL)) atBot atBot :=
    hsub.const_mul_atBot hsigma
  have hexp : Tendsto (fun A : ℝ => Real.exp (sigma * (A - aL))) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  simpa [expLeftOmega] using hexp.const_mul K

/-- If a function already has a left limit and a global bound, then an
exponential left-tail Cauchy modulus upgrades to an exponential left-rate bound.
This is the source-box bridge used after the fixed-source box supplies a genuine
left limit. -/
theorem leftTailCauchy_to_ExpLeftRate_of_tendsto
    {sigma aL K S : ℝ} {f : ℝ → ℝ} {ell : ℝ}
    (hsigma : 0 < sigma) (hK : 0 ≤ K) (hS : 0 ≤ S)
    (hbound : ∀ x, |f x| ≤ S)
    (hlim : Tendsto f atBot (𝓝 ell))
    (hcauchy : ∀ A, A ≤ aL → ∀ x y, x ≤ A → y ≤ A →
      |f x - f y| ≤ K * Real.exp (sigma * (A - aL))) :
    ExpLeftRate sigma aL (K + 2 * S) f ell := by
  intro x
  have hEll : |ell| ≤ S := by
    exact le_of_tendsto_of_tendsto hlim.abs tendsto_const_nhds
      (Eventually.of_forall hbound)
  have hcoef_nonneg : 0 ≤ K + 2 * S := by positivity
  by_cases hx : x ≤ aL
  · have htend :
        Tendsto (fun y : ℝ => |f x - f y|) atBot (𝓝 |f x - ell|) := by
      exact (tendsto_const_nhds.sub hlim).abs
    have hev :
        ∀ᶠ y in atBot,
          |f x - f y| ≤ K * Real.exp (sigma * (x - aL)) := by
      filter_upwards [eventually_le_atBot x] with y hy
      exact hcauchy x hx x y le_rfl hy
    have hleft :
        |f x - ell| ≤ K * Real.exp (sigma * (x - aL)) :=
      le_of_tendsto_of_tendsto htend tendsto_const_nhds hev
    have hmono :
        K * Real.exp (sigma * (x - aL)) ≤
          (K + 2 * S) * Real.exp (sigma * (x - aL)) := by
      have hKS : K ≤ K + 2 * S := by linarith
      exact mul_le_mul_of_nonneg_right hKS (Real.exp_pos _).le
    exact le_trans hleft hmono
  · have hxgt : aL < x := lt_of_not_ge hx
    have htri :
        |f x - ell| ≤ 2 * S := by
      calc
        |f x - ell| ≤ |f x| + |ell| := abs_sub _ _
        _ ≤ S + S := add_le_add (hbound x) hEll
        _ = 2 * S := by ring
    have hone :
        1 ≤ Real.exp (sigma * (x - aL)) := by
      exact Real.one_le_exp (mul_nonneg hsigma.le (sub_nonneg.mpr hxgt.le))
    calc
      |f x - ell| ≤ 2 * S := htri
      _ ≤ (K + 2 * S) := by linarith
      _ = (K + 2 * S) * 1 := by ring
      _ ≤ (K + 2 * S) * Real.exp (sigma * (x - aL)) :=
        mul_le_mul_of_nonneg_left hone hcoef_nonneg

/-- A bounded function that is exactly constant on a left half-line has a
positive exponential left-rate bound. -/
theorem expLeftRate_of_left_constant
    {sigma aL S : ℝ} {f : ℝ → ℝ} {ell : ℝ}
    (hsigma : 0 < sigma) (hS : 0 ≤ S)
    (hbound : ∀ x, |f x| ≤ S)
    (hleft : ∀ x, x ≤ aL → f x = ell) :
    ExpLeftRate sigma aL (2 * S) f ell := by
  intro x
  by_cases hx : x ≤ aL
  · rw [hleft x hx]
    rw [sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hS) (Real.exp_pos _).le
  · have hxlt : aL < x := lt_of_not_ge hx
    have hell : |ell| ≤ S := by
      simpa [hleft aL le_rfl] using hbound aL
    have htri : |f x - ell| ≤ 2 * S := by
      calc
        |f x - ell| ≤ |f x| + |ell| := abs_sub _ _
        _ ≤ S + S := add_le_add (hbound x) hell
        _ = 2 * S := by ring
    have hone : 1 ≤ Real.exp (sigma * (x - aL)) :=
      Real.one_le_exp (mul_nonneg hsigma.le (sub_nonneg.mpr hxlt.le))
    have hcoef : 0 ≤ 2 * S := by positivity
    calc
      |f x - ell| ≤ 2 * S := htri
      _ = 2 * S * 1 := by ring
      _ ≤ 2 * S * Real.exp (sigma * (x - aL)) :=
        mul_le_mul_of_nonneg_left hone hcoef

/-- The paper super-barrier has an exponential left-rate witness. -/
theorem upperBarrier_expLeftRateData {κ M : ℝ}
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) :
    ExpLeftRateData (upperBarrier κ M) := by
  by_cases hMzero : M = 0
  · refine
      ⟨1, 0, 0, 0, by norm_num, ?_⟩
    intro x
    have hU : upperBarrier κ M x = 0 := by
      subst M
      exact upperBarrier_eq_M_of_le_exp (Real.exp_pos _).le
    simp [ExpLeftRate, hU]
  have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMzero)
  by_cases hκpos : 0 < κ
  · let aL : ℝ := -Real.log M / κ
    refine
      ⟨κ, aL, 2 * M, M, hκpos, ?_⟩
    have hbound : ∀ x, |upperBarrier κ M x| ≤ M := by
      intro x
      rw [abs_of_nonneg (upperBarrier_nonneg hM x)]
      exact upperBarrier_le_M κ M x
    have hleft : ∀ x, x ≤ aL → upperBarrier κ M x = M := by
      intro x hx
      have hmul : Real.log M ≤ -κ * x := by
        have hxmul : κ * x ≤ -Real.log M := by
          rw [show -Real.log M = κ * aL by
            dsimp [aL]
            field_simp [ne_of_gt hκpos]]
          exact mul_le_mul_of_nonneg_left hx hκ
        linarith
      have hexp : M ≤ Real.exp (-κ * x) := by
        rw [← Real.exp_log hMpos]
        exact Real.exp_le_exp.mpr hmul
      exact upperBarrier_eq_M_of_le_exp hexp
    exact expLeftRate_of_left_constant hκpos hM hbound hleft
  · have hκzero : κ = 0 := le_antisymm (not_lt.mp hκpos) hκ
    refine
      ⟨1, 0, 0, min M 1, by norm_num, ?_⟩
    intro x
    have hU : upperBarrier κ M x = min M 1 := by
      subst κ
      simp [upperBarrier]
    simp [ExpLeftRate, hU]

/-- Per-step facts for the paper implicit orbit. -/
structure PaperRotheStepFacts
    (p : CMParams) (c lam M κ Λ : ℝ) (u Z W : ℝ → ℝ) : Prop where
  step_op : ∀ x, paperImplicitStepOp p c (1 / lam) u W x = Z x
  cont : Continuous W
  diff : Differentiable ℝ W
  deriv_le : ∀ x, |deriv W x| ≤ Λ
  left_rate : ExpLeftRateData W
  nonneg : ∀ x, 0 ≤ W x
  le_barrier : ∀ x, W x ≤ upperBarrier κ M x
  le_old : ∀ x, W x ≤ Z x
  anti : Antitone W

/-- The base shape needed to keep producing paper iterates. -/
structure PaperIterateBase (κ M : ℝ) (Z : ℝ → ℝ) : Prop where
  cont : Continuous Z
  anti : Antitone Z
  nonneg : ∀ x, 0 ≤ Z x
  le_barrier : ∀ x, Z x ≤ upperBarrier κ M x
  diff : Z = upperBarrier κ M ∨ Differentiable ℝ Z
  deriv_le : ∃ L : ℝ, 0 ≤ L ∧ ∀ x, |deriv Z x| ≤ L
  left_rate : ExpLeftRateData Z

theorem upperBarrier_deriv_abs_le_mul {κ M : ℝ}
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) :
    ∀ x, |deriv (upperBarrier κ M) x| ≤ κ * M := by
  intro x
  by_cases hconst : M < Real.exp (-κ * x)
  · rw [upperBarrier_deriv_eq_zero_of_const_lt hconst]
    simpa using mul_nonneg hκ hM
  · by_cases hexp : Real.exp (-κ * x) < M
    · rw [upperBarrier_deriv_eq_exp_of_lt hexp]
      have hE0 : 0 ≤ expDecay κ x := by
        unfold expDecay
        exact (Real.exp_pos _).le
      have hE_le : expDecay κ x ≤ M := by
        unfold expDecay
        simpa [neg_mul] using hexp.le
      rw [abs_mul, abs_neg, abs_of_nonneg hκ, abs_of_nonneg hE0]
      exact mul_le_mul_of_nonneg_left hE_le hκ
    · have heq : Real.exp (-κ * x) = M :=
        le_antisymm (not_lt.mp hconst) (not_lt.mp hexp)
      rcases eq_or_lt_of_le hκ with hκeq | hκpos
      · subst κ
        have hderiv0 : deriv (upperBarrier 0 M) x = 0 := by
          rw [show upperBarrier 0 M = fun _ : ℝ => min M 1 by
            funext y
            simp [upperBarrier]]
          exact deriv_const x (min M 1)
        rw [hderiv0]
        simp
      · rcases eq_or_lt_of_le hM with hMeq | hMpos
        · subst M
          have hpos : 0 < Real.exp (-κ * x) := Real.exp_pos _
          linarith
        · have hnot :
              ¬ DifferentiableAt ℝ (upperBarrier κ M) x :=
            not_differentiableAt_upperBarrier_of_interface
              (κ := κ) (M := M) (x := x) hκpos hMpos heq
          rw [deriv_zero_of_not_differentiableAt hnot]
          simpa using mul_nonneg hκ hM

theorem upperBarrier_paperIterateBase {κ M : ℝ}
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) :
    PaperIterateBase κ M (upperBarrier κ M) :=
  ⟨upperBarrier_continuous κ M, upperBarrier_antitone hκ,
   fun x => upperBarrier_nonneg hM x, fun _ => le_rfl,
   Or.inl rfl, ⟨κ * M, mul_nonneg hκ hM,
    upperBarrier_deriv_abs_le_mul hκ hM⟩,
   upperBarrier_expLeftRateData hκ hM⟩

theorem PaperRotheStepFacts.toBase
    {p : CMParams} {c lam M κ Λ : ℝ} {u Z W : ℝ → ℝ}
    (h : PaperRotheStepFacts p c lam M κ Λ u Z W) :
    PaperIterateBase κ M W :=
  ⟨h.cont, h.anti, h.nonneg, h.le_barrier, Or.inr h.diff,
    ⟨Λ, le_trans (abs_nonneg (deriv W 0)) (h.deriv_le 0), h.deriv_le⟩,
    h.left_rate⟩

/-- Producer for the paper implicit orbit.  This is intentionally separate from
`RotheStepProducer`, whose step equation is frozen. -/
structure PaperRotheStepProducer
    (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ) : Prop where
  hlam : 0 < lam
  produce : ∀ Z : ℝ → ℝ, Continuous Z → Antitone Z → (∀ x, 0 ≤ Z x) →
      (∀ x, Z x ≤ upperBarrier κ M x) →
      ∃ W : ℝ → ℝ, PaperRotheStepFacts p c lam M κ Λ u Z W
  produce_regular : ∀ Z : ℝ → ℝ, PaperIterateBase κ M Z →
      ∃ W : ℝ → ℝ, PaperRotheStepFacts p c lam M κ Λ u Z W

def paperRotheStep (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ)
    (hprod : PaperRotheStepProducer p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) :
    ∀ k : ℕ, { Z : ℝ → ℝ // PaperIterateBase κ M Z }
  | 0 => ⟨upperBarrier κ M, upperBarrier_paperIterateBase hκ hM⟩
  | (k+1) =>
    let prev := paperRotheStep p c lam M κ Λ u hprod hκ hM k
    let hex := hprod.produce_regular prev.1 prev.2
    ⟨Classical.choose hex, (Classical.choose_spec hex).toBase⟩

/-- The concrete paper-step Rothe sequence. -/
def rotheSeqOfPaper (p : CMParams) (c lam M κ Λ : ℝ) (u : ℝ → ℝ)
    (hprod : PaperRotheStepProducer p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : ℕ → ℝ → ℝ :=
  fun k => (paperRotheStep p c lam M κ Λ u hprod hκ hM k).1

@[simp] theorem rotheSeqOfPaper_zero
    (hprod : PaperRotheStepProducer p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) :
    rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM 0 = upperBarrier κ M := rfl

theorem rotheSeqOfPaper_stepFacts
    (hprod : PaperRotheStepProducer p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (k : ℕ) :
    PaperRotheStepFacts p c lam M κ Λ u
      (rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM k)
      (rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM (k + 1)) := by
  let prev := paperRotheStep p c lam M κ Λ u hprod hκ hM k
  have hex := hprod.produce_regular prev.1 prev.2
  exact Classical.choose_spec hex

theorem rotheSeqOfPaper_base
    (hprod : PaperRotheStepProducer p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (k : ℕ) :
    PaperIterateBase κ M (rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM k) :=
  (paperRotheStep p c lam M κ Λ u hprod hκ hM k).2

theorem rotheSeqOfPaper_lowerPinned_base
    {p : CMParams} {c lam M κ Λ : ℝ} {φ u : ℝ → ℝ}
    (hprod : PaperRotheStepProducer p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hu : InLowerPinnedMonotoneTrap κ M φ u) :
    ∀ x, φ x ≤ rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM 0 x := by
  intro x
  rw [rotheSeqOfPaper_zero]
  exact le_trans (hu.lower x) (hu.bare.le_upperBarrier x)

/-! ## Paper-step orbit data -/

/-- Per-`u` orbit data for the paper implicit-Euler sequence.  This is the
common subset of `RotheOrbitData` needed by the Schauder fixed-point argument:
trap invariance, compactness, local-uniform convergence and lower-pin transfer.
The stationary equation is supplied separately at the final fixed point. -/
structure PaperRotheOrbitData (p : CMParams) (c lam M κ : ℝ)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ) (u : ℝ → ℝ) : Prop where
  iterate_cont : ∀ k, Continuous (rotheSeq u k)
  anti_k : ∀ x, Antitone (fun k => rotheSeq u k x)
  anti_x : ∀ k, Antitone (rotheSeq u k)
  nonneg : ∀ k x, 0 ≤ rotheSeq u k x
  le_M : ∀ k x, rotheSeq u k x ≤ M
  le_upperBarrier : ∀ k x, rotheSeq u k x ≤ upperBarrier κ M x
  bddBelow : ∀ x, BddBelow (Set.range (fun k => rotheSeq u k x))
  equiLip : ∀ k, ∀ x y, |rotheSeq u k x - rotheSeq u k y| ≤ M * |x - y|
  limitLip : ∀ x y,
    |rotheLimit (rotheSeq u) x - rotheLimit (rotheSeq u) y| ≤ M * |x - y|

namespace PaperRotheOrbitData

variable {p : CMParams} {c lam M κ : ℝ}
  {rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ} {u : ℝ → ℝ}

theorem locallyUniform (hM : 0 ≤ M)
    (h : PaperRotheOrbitData p c lam M κ rotheSeq u) :
    LocallyUniformConverges (rotheSeq u) (rotheLimit (rotheSeq u)) :=
  rotheLimit_locallyUniform hM h.anti_k h.bddBelow h.equiLip h.limitLip

theorem limit_continuous (hM : 0 ≤ M)
    (h : PaperRotheOrbitData p c lam M κ rotheSeq u) :
    Continuous (rotheLimit (rotheSeq u)) :=
  rotheLimit_continuous h.iterate_cont (h.locallyUniform hM)

theorem limit_nonneg (h : PaperRotheOrbitData p c lam M κ rotheSeq u) :
    ∀ y, 0 ≤ rotheLimit (rotheSeq u) y :=
  fun y => rotheLimit_nonneg h.nonneg y

theorem limit_le_M (h : PaperRotheOrbitData p c lam M κ rotheSeq u) :
    ∀ y, rotheLimit (rotheSeq u) y ≤ M :=
  fun y => rotheLimit_le_of_le h.bddBelow h.le_M y

end PaperRotheOrbitData

section PaperPerK
variable (hprod : PaperRotheStepProducer p c lam M κ Λ u)
  (hκ : 0 ≤ κ) (hM : 0 ≤ M)

theorem rotheSeqOfPaper_cont (k : ℕ) :
    Continuous (rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM k) :=
  (rotheSeqOfPaper_base hprod hκ hM k).cont

theorem rotheSeqOfPaper_anti_x (k : ℕ) :
    Antitone (rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM k) :=
  (rotheSeqOfPaper_base hprod hκ hM k).anti

theorem rotheSeqOfPaper_nonneg (k : ℕ) (x : ℝ) :
    0 ≤ rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM k x :=
  (rotheSeqOfPaper_base hprod hκ hM k).nonneg x

theorem rotheSeqOfPaper_le_barrier (k : ℕ) (x : ℝ) :
    rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM k x ≤ upperBarrier κ M x :=
  (rotheSeqOfPaper_base hprod hκ hM k).le_barrier x

theorem rotheSeqOfPaper_le_M (k : ℕ) (x : ℝ) :
    rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM k x ≤ M :=
  le_trans (rotheSeqOfPaper_le_barrier hprod hκ hM k x)
    (upperBarrier_le_M κ M x)

theorem rotheSeqOfPaper_succ_le (k : ℕ) (x : ℝ) :
    rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM (k + 1) x
      ≤ rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM k x :=
  (rotheSeqOfPaper_stepFacts hprod hκ hM k).le_old x

theorem rotheSeqOfPaper_anti_k (x : ℝ) :
    Antitone (fun k => rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM k x) :=
  antitone_nat_of_succ_le (fun k => rotheSeqOfPaper_succ_le hprod hκ hM k x)

theorem rotheSeqOfPaper_bddBelow (x : ℝ) :
    BddBelow
      (Set.range (fun k => rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM k x)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact rotheSeqOfPaper_nonneg hprod hκ hM k x

theorem rotheSeqOfPaper_succ_lipschitz (hΛ : 0 ≤ Λ) (k : ℕ) :
    ∀ x y, |rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM (k + 1) x
        - rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM (k + 1) y|
          ≤ Λ * |x - y| := by
  intro x y
  have hfacts := rotheSeqOfPaper_stepFacts hprod hκ hM k
  have hLip : LipschitzWith (Real.toNNReal Λ)
      (rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM (k + 1)) :=
    crossImplicitStep_lipschitz hΛ hfacts.diff hfacts.deriv_le
  have := hLip.dist_le_mul x y
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hΛ] at this
  exact this

theorem rotheSeqOfPaper_equiLip (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (k : ℕ) :
    ∀ x y, |rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM k x
        - rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM k y|
          ≤ M * |x - y| := by
  cases k with
  | zero =>
      intro x y
      rw [rotheSeqOfPaper_zero]
      exact hbarLip x y
  | succ k =>
      intro x y
      have hΛ := rotheSeqOfPaper_succ_lipschitz hprod hκ hM hΛ0 k x y
      exact le_trans hΛ
        (mul_le_mul_of_nonneg_right hΛM (abs_nonneg _))

theorem rotheSeqOfPaper_limitLip (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (x y : ℝ) :
    |rotheLimit (rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM) x
        - rotheLimit (rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM) y|
          ≤ M * |x - y| := by
  set z := rotheSeqOfPaper p c lam M κ Λ u hprod hκ hM with hz
  have hax : Tendsto (fun k => z k x) atTop (𝓝 (rotheLimit z x)) :=
    rotheLimit_tendsto (rotheSeqOfPaper_anti_k hprod hκ hM)
      (rotheSeqOfPaper_bddBelow hprod hκ hM) x
  have hay : Tendsto (fun k => z k y) atTop (𝓝 (rotheLimit z y)) :=
    rotheLimit_tendsto (rotheSeqOfPaper_anti_k hprod hκ hM)
      (rotheSeqOfPaper_bddBelow hprod hκ hM) y
  have htend : Tendsto (fun k => |z k x - z k y|) atTop
      (𝓝 (|rotheLimit z x - rotheLimit z y|)) :=
    (hax.sub hay).abs
  refine le_of_tendsto htend ?_
  filter_upwards with k
  exact rotheSeqOfPaper_equiLip hprod hκ hM hΛ0 hΛM hbarLip k x y

end PaperPerK

theorem paperRotheOrbitData
    (hprodAll : ∀ v, PaperRotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hbarLip : ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|) :
    PaperRotheOrbitData p c lam M κ
      (fun v => rotheSeqOfPaper p c lam M κ Λ v (hprodAll v) hκ hM) u := by
  refine
    { iterate_cont := rotheSeqOfPaper_cont (hprodAll u) hκ hM
      anti_k := rotheSeqOfPaper_anti_k (hprodAll u) hκ hM
      anti_x := rotheSeqOfPaper_anti_x (hprodAll u) hκ hM
      nonneg := rotheSeqOfPaper_nonneg (hprodAll u) hκ hM
      le_M := rotheSeqOfPaper_le_M (hprodAll u) hκ hM
      le_upperBarrier := rotheSeqOfPaper_le_barrier (hprodAll u) hκ hM
      bddBelow := rotheSeqOfPaper_bddBelow (hprodAll u) hκ hM
      equiLip := rotheSeqOfPaper_equiLip (hprodAll u) hκ hM hΛ0 hΛM hbarLip
      limitLip := ?_ }
  intro x y
  exact rotheSeqOfPaper_limitLip (hprodAll u) hκ hM hΛ0 hΛM hbarLip x y

theorem paperTmap_maps_trap
    (p : CMParams) (c lam M κ : ℝ) (hM : 0 ≤ M)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
        PaperRotheOrbitData p c lam M κ rotheSeq u) :
    ∀ u, InMonotoneWaveTrapSet κ M u →
      InMonotoneWaveTrapSet κ M (rotheLimit (rotheSeq u)) := by
  intro u hu
  have h := hdata u hu
  exact rotheLimit_mem_trap (h.limit_continuous hM) h.bddBelow h.anti_x
    h.nonneg h.le_upperBarrier hŪbdd

theorem paperTmap_compactRange
    (p : CMParams) (c lam M κ : ℝ) (hM : 0 ≤ M)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hHelly : HellyPointwiseSelection M)
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
        PaperRotheOrbitData p c lam M κ rotheSeq u) :
    LocalUniformSequentiallyCompactRange
      (InMonotoneWaveTrapSet κ M) (fun u => rotheLimit (rotheSeq u)) := by
  intro seq hseq
  set gs : ℕ → ℝ → ℝ := fun n => rotheLimit (rotheSeq (seq n)) with hgs
  have hdat : ∀ n, PaperRotheOrbitData p c lam M κ rotheSeq (seq n) :=
    fun n => hdata (seq n) (hseq n)
  have hgsL : ∀ k, ∀ x y, |gs k x - gs k y| ≤ M * |x - y| := by
    intro k x y; exact (hdat k).limitLip x y
  have hgsB : ∀ k x, |gs k x| ≤ M := by
    intro k x
    rw [abs_le]
    exact ⟨by linarith [(hdat k).limit_nonneg x], (hdat k).limit_le_M x⟩
  obtain ⟨subseq, hsub, g, hpt, hgL⟩ := hHelly gs hgsL hgsB
  have hLU : LocallyUniformConverges (fun n => gs (subseq n)) g :=
    locallyUniform_of_helly_pointwise hM hpt hgsL hgL
  have hanti : Antitone g :=
    hLU.antitone_of_forall_antitone
      (fun n => rotheLimit_antitone (hdat (subseq n)).anti_x
        (hdat (subseq n)).bddBelow)
  have hnn : ∀ x, 0 ≤ g x :=
    fun x => hLU.nonneg_of_forall_nonneg
      (fun n => (hdat (subseq n)).limit_nonneg x)
  have hbar : ∀ x, g x ≤ upperBarrier κ M x :=
    fun x => hLU.le_of_forall_le
      (fun n => rotheLimit_le_of_le (hdat (subseq n)).bddBelow
        (hdat (subseq n)).le_upperBarrier x)
  have hleM : ∀ x, g x ≤ M :=
    fun x => hLU.le_of_forall_le (fun n => (hdat (subseq n)).limit_le_M x)
  have hgcont : Continuous g :=
    continuous_of_locallyUniform
      (fun n => (hdat (subseq n)).limit_continuous hM) hLU
  have hgbdd : IsBddFun g := by
    refine ⟨M, fun x => ?_⟩
    rw [abs_le]
    exact ⟨by linarith [hnn x], hleM x⟩
  refine ⟨subseq, hsub, g, ?_, ?_⟩
  · exact ⟨⟨⟨hgcont, hgbdd⟩, fun x => ⟨hnn x, hbar x⟩⟩, hanti⟩
  · simpa [hgs] using hLU

/-! ## Paper-step continuous-dependence frontier

The frozen branch does not close `RotheContinuousDependence` from the committed
producer alone: it names the fixed-step dependence and the uniform Rothe tail as
the exact remaining analytic inputs.  The paper branch has the same status. -/

/-- Fixed-step locally-uniform dependence of the paper Rothe orbit on the
frozen profile. -/
def PaperRotheSeqStepDependence
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hprodAll : ∀ v, PaperRotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Prop :=
  ∀ (seq : ℕ → ℝ → ℝ) (u : ℝ → ℝ),
    (hseq : ∀ n, InMonotoneWaveTrapSet κ M (seq n)) →
      (hu : InMonotoneWaveTrapSet κ M u) →
      LocallyUniformConverges seq u →
        ∀ k : ℕ,
          LocallyUniformConverges
            (fun n => rotheSeqOfPaper p c lam M κ Λ (seq n)
              (hprodAll (seq n)) hκ hM k)
            (rotheSeqOfPaper p c lam M κ Λ u (hprodAll u) hκ hM k)

/-- Uniform-in-profile tail convergence of the paper Rothe orbit to its
monotone `k`-limit on compact windows. -/
def PaperRotheTailUniform
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hprodAll : ∀ v, PaperRotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) : Prop :=
  ∀ R > 0, ∀ ε > 0,
    ∃ K : ℕ, ∀ v : ℝ → ℝ, InMonotoneWaveTrapSet κ M v →
      ∀ k : ℕ, K ≤ k → ∀ x ∈ Set.Icc (-R) R,
        |rotheSeqOfPaper p c lam M κ Λ v (hprodAll v) hκ hM k x
            - rotheLimit
              (rotheSeqOfPaper p c lam M κ Λ v (hprodAll v) hκ hM) x| < ε

/-- Paper-step dependence plus uniform Rothe tail give the
`RotheContinuousDependence` interface consumed by the Schauder wrapper. -/
theorem paperRotheContinuousDependence
    (p : CMParams) (c lam M κ Λ : ℝ)
    (hprodAll : ∀ v, PaperRotheStepProducer p c lam M κ Λ v)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hstep : PaperRotheSeqStepDependence p c lam M κ Λ hprodAll hκ hM)
    (htail : PaperRotheTailUniform p c lam M κ Λ hprodAll hκ hM) :
    RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
      (fun v => rotheSeqOfPaper p c lam M κ Λ v (hprodAll v) hκ hM) := by
  intro seq u hseq hu hconv
  set Z : (ℝ → ℝ) → ℕ → ℝ → ℝ :=
    fun v => rotheSeqOfPaper p c lam M κ Λ v (hprodAll v) hκ hM with hZ
  set L : (ℝ → ℝ) → ℝ → ℝ := fun v => rotheLimit (Z v) with hL
  intro R hR ε hε
  obtain ⟨K, hK⟩ := htail R hR (ε / 3) (by linarith)
  have hstepK :
      LocallyUniformConverges (fun n => Z (seq n) K) (Z u K) := by
    have hstepK' := hstep seq u hseq hu hconv K
    simpa [hZ] using hstepK'
  filter_upwards [hstepK R hR (ε / 3) (by linarith)] with n hn
  intro x hx
  have htailn : |Z (seq n) K x - L (seq n) x| < ε / 3 := by
    have htailn' := hK (seq n) (hseq n) K (le_refl K) x hx
    simpa [hZ, hL] using htailn'
  have htailu : |Z u K x - L u x| < ε / 3 := by
    have htailu' := hK u hu K (le_refl K) x hx
    simpa [hZ, hL] using htailu'
  have hmid : |Z (seq n) K x - Z u K x| < ε / 3 := hn x hx
  have hdecomp :
      L (seq n) x - L u x
        = -(Z (seq n) K x - L (seq n) x)
          + (Z (seq n) K x - Z u K x)
          + (Z u K x - L u x) := by ring
  calc |L (seq n) x - L u x|
      = |-(Z (seq n) K x - L (seq n) x)
          + (Z (seq n) K x - Z u K x)
          + (Z u K x - L u x)| := by rw [hdecomp]
    _ ≤ |-(Z (seq n) K x - L (seq n) x) + (Z (seq n) K x - Z u K x)|
          + |Z u K x - L u x| := abs_add_le _ _
    _ ≤ |-(Z (seq n) K x - L (seq n) x)| + |Z (seq n) K x - Z u K x|
          + |Z u K x - L u x| := by
          have := abs_add_le (-(Z (seq n) K x - L (seq n) x))
            (Z (seq n) K x - Z u K x)
          linarith
    _ = |Z (seq n) K x - L (seq n) x| + |Z (seq n) K x - Z u K x|
          + |Z u K x - L u x| := by rw [abs_neg]
    _ < ε / 3 + ε / 3 + ε / 3 := by
          have := htailn; have := hmid; have := htailu; linarith
    _ = ε := by ring

/-! ## Paper Rothe-limit stationary consistency frontier -/

/-- The algebraic bridge from a self paper implicit step to paper stationarity. -/
theorem paperWaveOperator_eq_zero_of_paperImplicitStepOp_self
    (p : CMParams) (c lam : ℝ) (U : ℝ → ℝ)
    (hlam : 0 < lam)
    (hstep : ∀ x, paperImplicitStepOp p c (1 / lam) U U x = U x) :
    ∀ x, paperWaveOperator p c U U x = 0 := by
  intro x
  have hx := hstep x
  rw [paperImplicitStepOp_apply] at hx
  have hmul : (1 / lam) * paperWaveOperator p c U U x = 0 := by
    linarith
  exact (mul_eq_zero.mp hmul).resolve_left (one_div_ne_zero (ne_of_gt hlam))

/-- At `W = U`, paper stationarity transfers to the frozen operator by the
committed paper=frozen identity. -/
theorem frozenWaveOperator_eq_zero_of_paperImplicitStepOp_self
    (p : CMParams) (c lam : ℝ) (U : ℝ → ℝ)
    (hlam : 0 < lam)
    (hU : IsCUnifBdd U) (hU_nonneg : ∀ x, 0 ≤ U x)
    (hU_diff : ∀ x, DifferentiableAt ℝ U x)
    (hV_diff : ∀ x, DifferentiableAt ℝ (deriv (frozenElliptic p U)) x)
    (hU_rpow_diff : ∀ x, DifferentiableAt ℝ (fun y => (U y) ^ p.m) x)
    (hstep : ∀ x, paperImplicitStepOp p c (1 / lam) U U x = U x) :
    ∀ x, frozenWaveOperator p c U U x = 0 := by
  intro x
  rw [← paperWaveOperator_eq_frozenWaveOperator_at_fixed_point p x hU hU_nonneg
    (hU_diff x) (hV_diff x) (hU_rpow_diff x)]
  exact paperWaveOperator_eq_zero_of_paperImplicitStepOp_self p c lam U hlam hstep x

/-- The exact convergence floor still missing for the paper Rothe scheme:
the limit fixed point must satisfy the self paper implicit-step identity. -/
def PaperRotheLimitStepConsistency
    (p : CMParams) (c lam κ M : ℝ) (φ : ℝ → ℝ)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ) : Prop :=
  ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
    rotheLimit (rotheSeq U) = U →
      ∀ x, paperImplicitStepOp p c (1 / lam) U U x = U x

theorem paperLowerPinned_stationary_of_stepConsistency
    (p : CMParams) (c lam κ M : ℝ) (φ : ℝ → ℝ)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hlam : 0 < lam)
    (hcons : PaperRotheLimitStepConsistency p c lam κ M φ rotheSeq)
    (hU_diff : ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      ∀ x, DifferentiableAt ℝ U x)
    (hV_diff : ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      ∀ x, DifferentiableAt ℝ (deriv (frozenElliptic p U)) x)
    (hU_rpow_diff : ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      ∀ x, DifferentiableAt ℝ (fun y => (U y) ^ p.m) x) :
    ∀ U, InLowerPinnedMonotoneTrap κ M φ U →
      rotheLimit (rotheSeq U) = U →
        ∀ x, frozenWaveOperator p c U U x = 0 := by
  intro U hU hfix
  exact frozenWaveOperator_eq_zero_of_paperImplicitStepOp_self p c lam U hlam
    hU.bare.trap.cunif_bdd hU.bare.nonneg (hU_diff U hU)
    (hV_diff U hU) (hU_rpow_diff U hU) (hcons U hU hfix)

theorem paperLowerPinnedSchauder_fixedPoint
    (p : CMParams) (c lam M κ : ℝ) (φ : ℝ → ℝ)
    (hM : 0 ≤ M)
    (rotheSeq : (ℝ → ℝ) → ℕ → ℝ → ℝ)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    (hHelly : HellyPointwiseSelection M)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
        rotheSeq)
    (hdata : ∀ u, InMonotoneWaveTrapSet κ M u →
        PaperRotheOrbitData p c lam M κ rotheSeq u)
    (hlower : RotheOrbitLowerBound κ M φ rotheSeq)
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple
        (InLowerPinnedMonotoneTrap κ M φ)) :
    ∃ U, InLowerPinnedMonotoneTrap κ M φ U ∧
      rotheLimit (rotheSeq U) = U := by
  let Tmap : (ℝ → ℝ) → ℝ → ℝ := fun u => rotheLimit (rotheSeq u)
  have hbareInv :
      ∀ u, InMonotoneWaveTrapSet κ M u → InMonotoneWaveTrapSet κ M (Tmap u) :=
    paperTmap_maps_trap p c lam M κ hM rotheSeq hŪbdd hdata
  have hlowerT :
      ∀ u, InLowerPinnedMonotoneTrap κ M φ u → ∀ x, φ x ≤ Tmap u x :=
    Tmap_lowerInvariant_of_rotheOrbitLowerBound hlower
  have hinv :
      ∀ u, InLowerPinnedMonotoneTrap κ M φ u →
        InLowerPinnedMonotoneTrap κ M φ (Tmap u) := by
    intro u hu
    exact ⟨hbareInv u hu.bare, hlowerT u hu⟩
  have hcont : LocalUniformContinuousOn (InLowerPinnedMonotoneTrap κ M φ) Tmap := by
    intro seq u hseq hu hconv
    exact hdep seq u (fun n => (hseq n).bare) hu.bare hconv
  have hcompactBare :
      LocalUniformSequentiallyCompactRange (InMonotoneWaveTrapSet κ M) Tmap :=
    paperTmap_compactRange p c lam M κ hM rotheSeq hHelly hdata
  have hcompact :
      LocalUniformSequentiallyCompactRange
        (InLowerPinnedMonotoneTrap κ M φ) Tmap := by
    intro seq hseq
    obtain ⟨subseq, hsubseq, U, hUbare, hconv⟩ :=
      hcompactBare seq (fun n => (hseq n).bare)
    refine ⟨subseq, hsubseq, U, ⟨hUbare, ?_⟩, hconv⟩
    intro x
    have hlimit :
        Tendsto (fun n => Tmap (seq (subseq n)) x) atTop (𝓝 (U x)) :=
      hconv.tendsto_at x
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlimit
      (Filter.Eventually.of_forall fun n =>
        hlowerT (seq (subseq n)) (hseq (subseq n)) x)
  exact hprinciple Tmap hinv hcont hcompact

/-- Lower-bound orbit for the concrete Rothe sequence, reduced to the honest
one-step lower-invariance obligation.  The base case is discharged here. -/
theorem rotheOrbitLowerBound_lowerBarrierPlateau
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hprodAll : ∀ u, RotheStepProducer p c lam M κ Λ u)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hstepLower :
      RotheStepLowerInvariant κ M (lowerBarrierPlateau κ κtilde D)
        (fun u => rotheSeqOf p c lam M κ Λ u
          (hprodAll u) hκ hM)) :
    RotheOrbitLowerBound κ M (lowerBarrierPlateau κ κtilde D)
      (fun u => rotheSeqOf p c lam M κ Λ u (hprodAll u) hκ hM) := by
  apply rotheOrbitLowerBound_of_stepLowerInvariant
  · intro u hu
    exact rotheSeqOf_lowerPinned_base (hprodAll u) hκ hM hu
  · exact hstepLower

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

/-- **AUDIT BANNER: vacuous on the bare monotone trap.**

This theorem carries
`LocalUniformNontrivialSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M)`.
That principle is false whenever the zero profile belongs to the bare trap; see
`not_localUniformNontrivialSchauderFixedPointPrinciple_bareTrap`.  Therefore this
wrapper is retained only as an audit artifact for the old non-trivial route.  Use
the lower-barrier pinned version below, where non-triviality comes from trap
membership rather than from a strengthened Schauder principle. -/
theorem b1_chiNeg_existence_stationary_nontrivial_rootPin
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
    (hprinciple :
      LocalUniformNontrivialSchauderFixedPointPrinciple
        (InMonotoneWaveTrapSet κ M))
    (hstationary : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit (rotheSeqOf p c lam M κ Λ U (hprodAll U) hκ hM) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hsmp : StationaryStrongMaxPrinciple p c κ M)
    (hbdd : ∀ U, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U)
    (hflat : ∀ U, InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U)
    (hlim_pos : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_rothe_stationary_nontrivial_rootPin p c lam M Bv κ
    hc hlam hM hBv
    (fun u => rotheSeqOf p c lam M κ Λ u (hprodAll u) hκ hM)
    hŪbdd
    (helly_pointwise_selection M)
    hdep
    (fun u hu => rotheOrbitData hprodAll hκ hM hΛ0 hΛM Bv hbarLip
      (hVcont u hu) (hVbound u hu))
    hprinciple hstationary hsmp hbdd hflat hlim_pos

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

/-- **AUDIT BANNER: vacuous on the bare monotone trap.**

This profile-clean wrapper still carries the false bare-trap principle
`LocalUniformNontrivialSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M)`.
The constant-zero map refutes that principle.  It is superseded by
`b1_chiNeg_existence_profileClean_stationary_lowerBarrierPinned_rootPin`, whose
fixed point is selected by the ordinary Schauder principle on a pinned trap and
is non-trivial because it lies above the positive plateau lower barrier. -/
theorem b1_chiNeg_existence_profileClean_stationary_nontrivial_rootPin
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
      LocalUniformNontrivialSchauderFixedPointPrinciple
        (InMonotoneWaveTrapSet κ M))
    (hstationary : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit (rotheSeqOf p c lam M κ Λ U
          (hprodAll U) hκpos.le hM) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hsmp : StationaryStrongMaxPrinciple p c κ M)
    (hflat : ∀ U, InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_stationary_nontrivial_rootPin
    p c lam M Bv κ Λ hc hlam hM hBv hκpos.le hΛ0 hΛM hprodAll
    hbarLip hŪbdd hVcont hVbound hdep hprinciple hstationary hsmp
    (fun _U hU => hU.trap.cunif_bdd)
    hflat
    (fun _U hU => hU.tendsto_atTop_zero hκpos)

/-- Concrete lower-barrier pinned χ≤0 B1 existence.

This is the corrected non-triviality route.  It uses the ordinary Schauder
principle on
`InLowerPinnedMonotoneTrap κ M (lowerBarrierPlateau κ κtilde D)`.  The zero
profile is excluded by the pinned trap, and the produced fixed point is
pointwise positive because it lies above `lowerBarrierPlateau`.

The remaining frontier is the one-step lower invariant `hstepLower`: each
implicit step preserves the lower plateau once the previous iterate is above it.
The base of the induction is discharged by `rotheSeqOf_lowerPinned_base`. -/
theorem b1_chiNeg_existence_stationary_lowerBarrierPinned_rootPin
    (p : CMParams) (c lam M Bv κ κtilde D Λ : ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (hκpos : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
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
    (hstepLower :
      RotheStepLowerInvariant κ M (lowerBarrierPlateau κ κtilde D)
        (fun u => rotheSeqOf p c lam M κ Λ u (hprodAll u) hκpos.le hM))
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple
        (InLowerPinnedMonotoneTrap κ M
          (lowerBarrierPlateau κ κtilde D)))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierPlateau κ κtilde D) U →
        rotheLimit (rotheSeqOf p c lam M κ Λ U
          (hprodAll U) hκpos.le hM) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierPlateau κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M
        (lowerBarrierPlateau κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_rothe_lowerPinned_stationary_rootPin
    p c lam M Bv κ (lowerBarrierPlateau κ κtilde D)
    hc hκpos hlam hM hBv
    (fun u => rotheSeqOf p c lam M κ Λ u (hprodAll u) hκpos.le hM)
    hŪbdd
    (helly_pointwise_selection M)
    hdep
    (fun u hu => rotheOrbitData hprodAll hκpos.le hM hΛ0 hΛM Bv
      hbarLip (hVcont u hu) (hVbound u hu))
    (rotheOrbitLowerBound_lowerBarrierPlateau p c lam M κ κtilde D Λ
      hprodAll hκpos.le hM hstepLower)
    hprinciple hstationary
    (lowerBarrierPlateau_pos hκpos hgap hD) hflat

/-- Profile-clean entry point for the lower-barrier pinned route.

This is the public replacement for
`b1_chiNeg_existence_profileClean_stationary_nontrivial_rootPin`: it carries no
bare-trap non-trivial Schauder principle. -/
theorem b1_chiNeg_existence_profileClean_stationary_lowerBarrierPinned_rootPin
    (p : CMParams) (c lam M Bv κ κtilde D Λ : ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (hκpos : 0 < κ) (hgap : 0 < κtilde - κ) (hD : 0 < D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
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
    (hstepLower :
      RotheStepLowerInvariant κ M (lowerBarrierPlateau κ κtilde D)
        (fun u => rotheSeqOf p c lam M κ Λ u (hprodAll u) hκpos.le hM))
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple
        (InLowerPinnedMonotoneTrap κ M
          (lowerBarrierPlateau κ κtilde D)))
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierPlateau κ κtilde D) U →
        rotheLimit (rotheSeqOf p c lam M κ Λ U
          (hprodAll U) hκpos.le hM) = U →
          ∀ x, frozenWaveOperator p c U U x = 0)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M (lowerBarrierPlateau κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M
        (lowerBarrierPlateau κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_stationary_lowerBarrierPinned_rootPin
    p c lam M Bv κ κtilde D Λ hc hlam hM hBv hκpos hgap hD
    hΛ0 hΛM hprodAll hbarLip hŪbdd hVcont hVbound hdep
    hstepLower hprinciple hstationary hflat

/-! ## Axiom audit -/

section AxiomAudit

#print axioms rotheSeqOf
#print axioms rotheSeqOfPaper
#print axioms rotheSeqOfPaper_stepFacts
#print axioms rotheSeqOfPaper_lowerPinned_base
#print axioms paperRotheOrbitData
#print axioms paperTmap_maps_trap
#print axioms paperTmap_compactRange
#print axioms paperRotheContinuousDependence
#print axioms paperWaveOperator_eq_zero_of_paperImplicitStepOp_self
#print axioms frozenWaveOperator_eq_zero_of_paperImplicitStepOp_self
#print axioms paperLowerPinned_stationary_of_stepConsistency
#print axioms paperLowerPinnedSchauder_fixedPoint
#print axioms rotheSeqOf_supersol
#print axioms rotheSeqOf_step_rec
#print axioms rotheSeqOf_equiLip
#print axioms rotheSeqOf_limitLip
#print axioms rotheOrbitLowerBound_lowerBarrierPlateau
#print axioms rotheOrbitData
#print axioms rotheOrbitData_fromTrap
#print axioms b1_chiNeg_existence
#print axioms b1_chiNeg_existence_rootPin
#print axioms b1_chiNeg_existence_profileClean
#print axioms b1_chiNeg_existence_profileClean_rootPin
#print axioms b1_chiNeg_existence_stationary_floor
#print axioms b1_chiNeg_existence_stationary_floor_rootPin
#print axioms b1_chiNeg_existence_stationary_nontrivial_rootPin
#print axioms b1_chiNeg_existence_profileClean_stationary_floor
#print axioms b1_chiNeg_existence_profileClean_stationary_nontrivial_rootPin
#print axioms b1_chiNeg_existence_stationary_lowerBarrierPinned_rootPin
#print axioms b1_chiNeg_existence_profileClean_stationary_lowerBarrierPinned_rootPin

end AxiomAudit

end ShenWork.Paper1

#print axioms ShenWork.Paper1.rotheOrbitLowerBound_lowerBarrierPlateau
#print axioms ShenWork.Paper1.stationaryStrongMaxPrinciple_of_odeUniqueness
