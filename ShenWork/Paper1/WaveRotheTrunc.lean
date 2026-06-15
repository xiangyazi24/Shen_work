/-
  ShenWork/Paper1/WaveRotheTrunc.lean

  Global-Lipschitz truncation of the genuine reaction nonlinearity, turning the
  ABSTRACT globally-Lipschitz source map `S` of `WaveRotheTrap.lean` (PART A)
  into a CONCRETE one built from the real chemotaxis reaction/flux.

  The committed reaction `reactionFun α s = s(1 − s^α)` and the power
  `s ↦ s^m` are only LOCALLY Lipschitz — `reaction_lipschitz_on_Icc` and
  `rpow_m_lipschitz_on_Icc` give it on `[0,M]`.  `BoundedContinuousFunction.comp`
  needs a GLOBAL `LipschitzWith`.  The bridge is the clamp

      `clampIcc M s = max 0 (min M s) ∈ [0,M]`   (for `0 ≤ M`),

  which is globally `LipschitzWith 1` (`lipschitzWith_min`/`lipschitzWith_max`
  algebra) and whose RANGE is exactly `[0,M]`, the set where the committed local
  facts live.  Hence

      `reactionTrunc α M = reactionFun α ∘ clampIcc M`,
      `rpowTrunc   m M = (· ^ m)     ∘ clampIcc M`

  are GLOBALLY Lipschitz (locally-Lipschitz-on-the-clamp-range ∘
  globally-Lipschitz-clamp = globally Lipschitz, `LipschitzOnWith.comp` with
  `MapsTo … univ (Icc 0 M)`), and they AGREE with the genuine nonlinearity on
  `[0,M]` (the clamp is the identity there).  Feeding these through
  `BoundedContinuousFunction.comp` produces the concrete source map
  `crossStepSourceConcrete`, whose Lipschitz constant instantiates
  `crossStepSelfMap_exists_unique` — the genuine (no longer abstract) per-step
  implicit Green step.  On the trapped range `[0,M]` the truncation is invisible,
  so the concrete fixed point solves the real implicit step.
-/
import ShenWork.Paper1.WaveRotheTrap

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction

noncomputable section

namespace ShenWork.Paper1

/-! ## The clamp `s ↦ max 0 (min M s)` -/

/-- Clamp a real to `[0,M]`: `clampIcc M s = max 0 (min M s)`. -/
def clampIcc (M s : ℝ) : ℝ := max 0 (min M s)

/-- The clamp is globally `LipschitzWith 1`. -/
theorem clampIcc_lipschitz (M : ℝ) : LipschitzWith 1 (clampIcc M) := by
  have hmin : LipschitzWith 1 (fun s : ℝ => min M s) :=
    LipschitzWith.const_min (LipschitzWith.id) M
  have hmax : LipschitzWith 1 (fun s : ℝ => max 0 (min M s)) :=
    LipschitzWith.const_max hmin 0
  exact hmax

/-- For `0 ≤ M`, the clamp lands in `[0,M]`. -/
theorem clampIcc_mem_Icc {M : ℝ} (hM : 0 ≤ M) (s : ℝ) :
    clampIcc M s ∈ Set.Icc (0 : ℝ) M := by
  unfold clampIcc
  constructor
  · exact le_max_left _ _
  · exact max_le hM (min_le_left _ _)

/-- The clamp maps `univ` into `[0,M]` (for `0 ≤ M`). -/
theorem clampIcc_mapsTo {M : ℝ} (hM : 0 ≤ M) :
    Set.MapsTo (clampIcc M) Set.univ (Set.Icc (0 : ℝ) M) :=
  fun s _ => clampIcc_mem_Icc hM s

/-- On `[0,M]` the clamp is the identity. -/
theorem clampIcc_eqOn_Icc {M : ℝ} (_hM : 0 ≤ M) :
    Set.EqOn (clampIcc M) id (Set.Icc (0 : ℝ) M) := by
  intro s hs
  rw [Set.mem_Icc] at hs
  obtain ⟨hs0, hsM⟩ := hs
  unfold clampIcc
  rw [min_eq_right hsM, max_eq_right hs0]
  rfl

/-! ## Brick 1 — globally-Lipschitz reaction truncation -/

/-- Globally-Lipschitz truncation of the reaction `s ↦ s(1 − s^α)`: clamp the
argument to `[0,M]` first. -/
def reactionTrunc (α M : ℝ) : ℝ → ℝ := fun s => reactionFun α (clampIcc M s)

/-- The reaction truncation agrees with the genuine reaction on `[0,M]`. -/
theorem reactionTrunc_eq_on_Icc {α M : ℝ} (hM : 0 ≤ M) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) M) :
    reactionTrunc α M s = reactionFun α s := by
  unfold reactionTrunc
  rw [clampIcc_eqOn_Icc hM hs]
  rfl

/-- **Brick 1.** The reaction truncation is GLOBALLY `LipschitzWith`, with
constant `toNNReal (reactionLip α M)` (the committed local constant; the clamp
contributes `1`). -/
theorem reactionTrunc_lipschitz {α M : ℝ} (ha : 1 ≤ α) (hM : 0 ≤ M) :
    LipschitzWith (Real.toNNReal (reactionLip α M)) (reactionTrunc α M) := by
  have hloc : LipschitzOnWith (Real.toNNReal (reactionLip α M)) (reactionFun α)
      (Set.Icc 0 M) := reaction_lipschitz_on_Icc ha hM
  have hclamp : LipschitzOnWith 1 (clampIcc M) Set.univ :=
    (lipschitzOnWith_univ).mpr (clampIcc_lipschitz M)
  -- locally-on-range ∘ globally-into-range = on univ
  have hcomp : LipschitzOnWith (Real.toNNReal (reactionLip α M) * 1)
      (reactionFun α ∘ clampIcc M) Set.univ :=
    hloc.comp hclamp (clampIcc_mapsTo hM)
  rw [mul_one] at hcomp
  rw [← lipschitzOnWith_univ]
  exact hcomp

/-! ## Brick 2 — globally-Lipschitz power truncation -/

/-- Globally-Lipschitz truncation of the power `s ↦ s^m`: clamp first. -/
def rpowTrunc (m M : ℝ) : ℝ → ℝ := fun s => (clampIcc M s) ^ m

/-- The power truncation agrees with `s ↦ s^m` on `[0,M]`. -/
theorem rpowTrunc_eq_on_Icc {m M : ℝ} (hM : 0 ≤ M) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) M) :
    rpowTrunc m M s = s ^ m := by
  unfold rpowTrunc
  rw [clampIcc_eqOn_Icc hM hs]
  rfl

/-- **Brick 2.** The power truncation is GLOBALLY `LipschitzWith`, with constant
`toNNReal (rpowLip m M)`. -/
theorem rpowTrunc_lipschitz {m M : ℝ} (hm : 1 ≤ m) (hM : 0 ≤ M) :
    LipschitzWith (Real.toNNReal (rpowLip m M)) (rpowTrunc m M) := by
  have hloc : LipschitzOnWith (Real.toNNReal (rpowLip m M)) (fun s => s ^ m)
      (Set.Icc 0 M) := rpow_m_lipschitz_on_Icc hm hM
  have hclamp : LipschitzOnWith 1 (clampIcc M) Set.univ :=
    (lipschitzOnWith_univ).mpr (clampIcc_lipschitz M)
  have hcomp : LipschitzOnWith (Real.toNNReal (rpowLip m M) * 1)
      ((fun s => s ^ m) ∘ clampIcc M) Set.univ :=
    hloc.comp hclamp (clampIcc_mapsTo hM)
  rw [mul_one] at hcomp
  rw [← lipschitzOnWith_univ]
  exact hcomp

/-! ## Brick 3 — the concrete source map

The concrete per-step source map is

    `S(W) = (reactionTrunc α M) ∘ W  +  lam • Z  +  ((rpowTrunc m M) ∘ W) * Vu'`,

with `Z : ℝ →ᵇ ℝ` the OLD iterate entering the linear `λ`-shift, and
`Vu' : ℝ →ᵇ ℝ` a bounded-continuous representative of `(frozenElliptic p u)'`
entering the chemotaxis flux.  Each composite `… ∘ W` is a genuine `ℝ →ᵇ ℝ` via
`BoundedContinuousFunction.comp` (legal precisely because of bricks 1–2's GLOBAL
Lipschitz truncations).  The whole assembly is built from the BCF `+`, `•`, `*`
algebra. -/

/-- The concrete per-step source map built from the global truncations. -/
def crossStepSourceConcrete (α m M lam : ℝ) (ha : 1 ≤ α) (hm : 1 ≤ m)
    (hM : 0 ≤ M) (Z Vu' : ℝ →ᵇ ℝ) : (ℝ →ᵇ ℝ) → (ℝ →ᵇ ℝ) :=
  fun W =>
    W.comp (reactionTrunc α M) (reactionTrunc_lipschitz ha hM)
      + lam • Z
      + (W.comp (rpowTrunc m M) (rpowTrunc_lipschitz hm hM)) * Vu'

@[simp] theorem crossStepSourceConcrete_apply (α m M lam : ℝ) (ha : 1 ≤ α)
    (hm : 1 ≤ m) (hM : 0 ≤ M) (Z Vu' : ℝ →ᵇ ℝ) (W : ℝ →ᵇ ℝ) (y : ℝ) :
    crossStepSourceConcrete α m M lam ha hm hM Z Vu' W y
      = reactionTrunc α M (W y) + lam * Z y
        + rpowTrunc m M (W y) * Vu' y := by
  unfold crossStepSourceConcrete
  simp only [BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.comp_apply, BoundedContinuousFunction.coe_smul,
    smul_eq_mul, BoundedContinuousFunction.mul_apply]

/-- **Brick 3 — global Lipschitz constant of the concrete source map.**
`S` is `LipschitzWith Ls` with the explicit assembled constant

    `Ls = toNNReal (reactionLip α M) + toNNReal (rpowLip m M) * ‖Vu'‖₊`,

the reaction-truncation constant plus the flux's `rpow`-truncation constant
scaled by the sup norm of `Vu'`.  (The `lam • Z` shift is constant in `W`, so it
drops out.) -/
theorem crossStepSourceConcrete_lipschitz (α m M lam : ℝ) (ha : 1 ≤ α)
    (hm : 1 ≤ m) (hM : 0 ≤ M) (Z Vu' : ℝ →ᵇ ℝ) :
    LipschitzWith
      (Real.toNNReal (reactionLip α M)
        + Real.toNNReal (rpowLip m M) * ‖Vu'‖₊)
      (crossStepSourceConcrete α m M lam ha hm hM Z Vu') := by
  refine LipschitzWith.of_dist_le_mul (fun W₁ W₂ => ?_)
  rw [BoundedContinuousFunction.dist_le_iff_of_nonempty]
  intro y
  -- pointwise difference
  rw [crossStepSourceConcrete_apply, crossStepSourceConcrete_apply]
  -- abbreviations
  set Lr : ℝ := (Real.toNNReal (reactionLip α M) : ℝ)
  set Lm : ℝ := (Real.toNNReal (rpowLip m M) : ℝ)
  set Lr_nn := Real.toNNReal (reactionLip α M)
  set Lm_nn := Real.toNNReal (rpowLip m M)
  -- reaction part bound: |reactionTrunc(W₁ y) − reactionTrunc(W₂ y)| ≤ Lr · dist W₁ W₂
  have hrxn : dist (reactionTrunc α M (W₁ y)) (reactionTrunc α M (W₂ y))
      ≤ Lr * dist W₁ W₂ := by
    have h1 : dist (reactionTrunc α M (W₁ y)) (reactionTrunc α M (W₂ y))
        ≤ Lr * dist (W₁ y) (W₂ y) :=
      (reactionTrunc_lipschitz ha hM).dist_le_mul (W₁ y) (W₂ y)
    refine h1.trans ?_
    have hLr0 : 0 ≤ Lr := (Real.toNNReal (reactionLip α M)).coe_nonneg
    exact mul_le_mul_of_nonneg_left
      (BoundedContinuousFunction.dist_coe_le_dist y) hLr0
  -- power part bound: |rpowTrunc(W₁ y) − rpowTrunc(W₂ y)| ≤ Lm · dist W₁ W₂
  have hpow : dist (rpowTrunc m M (W₁ y)) (rpowTrunc m M (W₂ y))
      ≤ Lm * dist W₁ W₂ := by
    have h1 : dist (rpowTrunc m M (W₁ y)) (rpowTrunc m M (W₂ y))
        ≤ Lm * dist (W₁ y) (W₂ y) :=
      (rpowTrunc_lipschitz hm hM).dist_le_mul (W₁ y) (W₂ y)
    refine h1.trans ?_
    have hLm0 : 0 ≤ Lm := (Real.toNNReal (rpowLip m M)).coe_nonneg
    exact mul_le_mul_of_nonneg_left
      (BoundedContinuousFunction.dist_coe_le_dist y) hLm0
  -- assemble.  The `lam * Z y` shift cancels.
  have hVu'_bound : |Vu' y| ≤ ‖Vu'‖ := by
    simpa [Real.norm_eq_abs] using Vu'.norm_coe_le_norm y
  have hVu'_nonneg : 0 ≤ ‖Vu'‖ := norm_nonneg _
  -- the flux pointwise difference:
  -- |rpowTrunc(W₁ y)·Vu' y − rpowTrunc(W₂ y)·Vu' y| = |Vu' y|·|Δrpow|
  have hflux : dist (rpowTrunc m M (W₁ y) * Vu' y) (rpowTrunc m M (W₂ y) * Vu' y)
      ≤ Lm * ‖Vu'‖ * dist W₁ W₂ := by
    rw [Real.dist_eq, ← sub_mul, abs_mul]
    have hΔ : |rpowTrunc m M (W₁ y) - rpowTrunc m M (W₂ y)| ≤ Lm * dist W₁ W₂ := by
      rw [← Real.dist_eq]; exact hpow
    calc |rpowTrunc m M (W₁ y) - rpowTrunc m M (W₂ y)| * |Vu' y|
        ≤ (Lm * dist W₁ W₂) * ‖Vu'‖ := by
          apply mul_le_mul hΔ hVu'_bound (abs_nonneg _)
          exact mul_nonneg ((Real.toNNReal (rpowLip m M)).coe_nonneg) dist_nonneg
      _ = Lm * ‖Vu'‖ * dist W₁ W₂ := by ring
  -- total: |(rxn₁ + λZ + flux₁) − (rxn₂ + λZ + flux₂)| ≤ |Δrxn| + |Δflux|
  have hrxn' : |reactionTrunc α M (W₁ y) - reactionTrunc α M (W₂ y)|
      ≤ Lr * dist W₁ W₂ := by rw [← Real.dist_eq]; exact hrxn
  have hflux' : |rpowTrunc m M (W₁ y) * Vu' y - rpowTrunc m M (W₂ y) * Vu' y|
      ≤ Lm * ‖Vu'‖ * dist W₁ W₂ := by rw [← Real.dist_eq]; exact hflux
  rw [Real.dist_eq]
  have hsplit :
      (reactionTrunc α M (W₁ y) + lam * Z y + rpowTrunc m M (W₁ y) * Vu' y)
        - (reactionTrunc α M (W₂ y) + lam * Z y + rpowTrunc m M (W₂ y) * Vu' y)
      = (reactionTrunc α M (W₁ y) - reactionTrunc α M (W₂ y))
        + (rpowTrunc m M (W₁ y) * Vu' y - rpowTrunc m M (W₂ y) * Vu' y) := by
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  -- (Lr + Lm‖Vu'‖) dist = Lr dist + Lm‖Vu'‖ dist; coe of NNReal sum/mul
  have hcoe : ((Lr_nn + Lm_nn * ‖Vu'‖₊ : NNReal) : ℝ) * dist W₁ W₂
      = Lr * dist W₁ W₂ + Lm * ‖Vu'‖ * dist W₁ W₂ := by
    rw [NNReal.coe_add, NNReal.coe_mul, coe_nnnorm]
    simp only [Lr, Lm, Lr_nn, Lm_nn]
    ring
  rw [hcoe]
  exact add_le_add hrxn' hflux'

/-! ## Brick 4 — the genuine (concrete) per-step implicit step

Instantiate `crossStepSelfMap_exists_unique` with `S = crossStepSourceConcrete`.
The smallness hypothesis is the kernel-`L¹`-norm × source-Lipschitz-constant `< 1`
(large-`λ` contraction), exactly the abstract hypothesis fed the concrete `Ls`. -/

/-- **Brick 4 — unique GENUINE implicit step (no longer abstract).**
For a continuous integrable kernel `K` with `(∫|K|) · Ls < 1` (large-`λ`
smallness, with `Ls` the assembled concrete source-map Lipschitz constant), the
composed per-step self-map built from the genuine truncated reaction/flux has a
unique fixed point — the uniquely-solvable implicit Green step.  On the trapped
range `[0,M]` the truncation is invisible (bricks 1–2 agree with the genuine
nonlinearity there), so this fixed point solves the real implicit step. -/
theorem crossStep_exists_unique_concrete {K : ℝ → ℝ}
    (hK_cont : Continuous K) (hK_int : Integrable K)
    {α m M lam : ℝ} (ha : 1 ≤ α) (hm : 1 ≤ m) (hM : 0 ≤ M)
    (Z Vu' : ℝ →ᵇ ℝ)
    (hsmall : Real.toNNReal (∫ z, |K z|)
        * (Real.toNNReal (reactionLip α M)
            + Real.toNNReal (rpowLip m M) * ‖Vu'‖₊) < 1) :
    ∃! W : ℝ →ᵇ ℝ,
      crossStepSelfMap hK_cont hK_int
        (crossStepSourceConcrete α m M lam ha hm hM Z Vu') W = W :=
  crossStepSelfMap_exists_unique hK_cont hK_int
    (crossStepSourceConcrete_lipschitz α m M lam ha hm hM Z Vu') hsmall

/-! ## Axiom audit -/

section AxiomAudit

#print axioms clampIcc_lipschitz
#print axioms reactionTrunc_eq_on_Icc
#print axioms reactionTrunc_lipschitz
#print axioms rpowTrunc_eq_on_Icc
#print axioms rpowTrunc_lipschitz
#print axioms crossStepSourceConcrete_lipschitz
#print axioms crossStep_exists_unique_concrete

end AxiomAudit

end ShenWork.Paper1
