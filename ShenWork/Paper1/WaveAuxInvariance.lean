/-
  ShenWork/Paper1/WaveAuxInvariance.lean

  L2 — the shifted-comparison invariance `T(K) ⊆ K` plus relative compactness
  for the Green auxiliary map `T = auxMap` (Shen, arXiv:2605.04401, §3).

  ROUTE (ChatGPT cron L2 design):

  (1) **Reusable shifted comparison** [FOUNDATIONAL, self-contained].  The
      Green convolution `greenConv c λ H = Kλ ∗ H` is MONOTONE in `H` because the
      kernel `Kλ ≥ 0` (committed `greenKernel_pos`) — equivalently because in the
      split-tail representation `greenConv = (1/δ)(e^{r₊x} tailHi + e^{r₋x} tailLo)`
      each weight `e^{−r y} ≥ 0` and the exponential prefactors are `≥ 0`.  Hence the
      maximum-principle comparison `Aλ φ ≤ Aλ ψ ⟹ φ ≤ ψ` via the
      variation-of-parameters representation `φ = greenConv (Aλ φ)`.

  (2) **Invariance `T(K) ⊆ K`** — the sandwich `U_ ≤ T(u) ≤ Ū`, GIVEN the shifted
      barrier inequalities `Aλ U_ ≤ R(u) ≤ Aλ Ū`.  Discharged by (1).  The
      chemotaxis half of those barrier inequalities is isolated as ONE named
      obligation `ChemotaxisSandwich` (see report); the local logistic half follows
      from the committed `frozenElliptic` bounds.

  (3) **Compactness** in a weighted-sup norm — `T(K)` relatively compact.  The
      `C¹`-gain `T(u)' = Kλ' ∗ R(u)` (NO `u'`) gives uniform local equicontinuity;
      with uniform boundedness and uniform tail smallness this yields weighted-sup
      total boundedness.  The concrete weighted total-boundedness metric step is
      carried as the named obligation `WeightedCompactness`.

  Parts (1) is closed outright; (2)/(3) are reduced to the two named obligations.
-/
import ShenWork.Paper1.WaveAuxMap
import ShenWork.Paper1.WaveGreenIdentity

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## (1) The reusable shifted comparison

`greenConv` is monotone in its source `H`.  We prove this from the split-tail
representation, where each tail integral is monotone in `H` (the weight
`e^{−r y}` and the exponential prefactors are nonnegative). -/

/-- The pointwise weight `gWeight r H y = e^{−r y}·H y` is monotone in `H`. -/
theorem gWeight_mono {r : ℝ} {H₁ H₂ : ℝ → ℝ} (hle : ∀ y, H₁ y ≤ H₂ y) (y : ℝ) :
    gWeight r H₁ y ≤ gWeight r H₂ y := by
  unfold gWeight
  exact mul_le_mul_of_nonneg_left (hle y) (Real.exp_pos _).le

/-- Monotonicity of the upper tail `tailHi r H x = ∫_{Ioi x} e^{−r y} H y` in `H`. -/
theorem tailHi_mono {r : ℝ} {H₁ H₂ : ℝ → ℝ} (hle : ∀ y, H₁ y ≤ H₂ y)
    (hI₁ : IntegrableOn (gWeight r H₁) (Ioi x))
    (hI₂ : IntegrableOn (gWeight r H₂) (Ioi x)) :
    tailHi r H₁ x ≤ tailHi r H₂ x := by
  unfold tailHi
  exact setIntegral_mono_on hI₁ hI₂ measurableSet_Ioi (fun y _ => gWeight_mono hle y)

/-- Monotonicity of the lower tail `tailLo r H x = ∫_{Iic x} e^{−r y} H y` in `H`. -/
theorem tailLo_mono {r : ℝ} {H₁ H₂ : ℝ → ℝ} (hle : ∀ y, H₁ y ≤ H₂ y)
    (hI₁ : IntegrableOn (gWeight r H₁) (Iic x))
    (hI₂ : IntegrableOn (gWeight r H₂) (Iic x)) :
    tailLo r H₁ x ≤ tailLo r H₂ x := by
  unfold tailLo
  exact setIntegral_mono_on hI₁ hI₂ measurableSet_Iic (fun y _ => gWeight_mono hle y)

/-- **Monotonicity of the Green convolution.**  If `H₁ ≤ H₂` pointwise (and both
sources have convergent two-sided exponential tails), then `greenConv c λ H₁ x ≤
greenConv c λ H₂ x`.  This is the `Kλ ≥ 0` maximum-principle ingredient, proved
through the explicit split-tail representation. -/
theorem greenConv_mono (hlam : 0 < lam) {H₁ H₂ : ℝ → ℝ} (hle : ∀ y, H₁ y ≤ H₂ y)
    (hHi₁ : IntegrableOn (gWeight (greenRootPlus c lam) H₁) (Ioi x))
    (hHi₂ : IntegrableOn (gWeight (greenRootPlus c lam) H₂) (Ioi x))
    (hLo₁ : IntegrableOn (gWeight (greenRootMinus c lam) H₁) (Iic x))
    (hLo₂ : IntegrableOn (gWeight (greenRootMinus c lam) H₂) (Iic x)) :
    greenConv c lam H₁ x ≤ greenConv c lam H₂ x := by
  unfold greenConv
  have hδ : (0 : ℝ) ≤ (greenDelta c lam)⁻¹ :=
    (inv_pos.mpr (greenDelta_pos (c := c) hlam)).le
  have hHi := tailHi_mono (r := greenRootPlus c lam) hle hHi₁ hHi₂
  have hLo := tailLo_mono (r := greenRootMinus c lam) hle hLo₁ hLo₂
  apply mul_le_mul_of_nonneg_left _ hδ
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left hHi (Real.exp_pos _).le
  · exact mul_le_mul_of_nonneg_left hLo (Real.exp_pos _).le

/-- **The comparison principle (variation-of-parameters form).**
If `φ` and `ψ` are the variation-of-parameters solutions of `Aλ φ = Rφ`,
`Aλ ψ = Rψ` — concretely `φ = greenConv c λ Rφ`, `ψ = greenConv c λ Rψ` — and the
sources are ordered `Rφ ≤ Rψ` with convergent tails, then `φ ≤ ψ` pointwise.

Here `greenConv c λ R` represents `Aλ⁻¹ R` (the `Kλ ≥ 0` resolvent); ordering of
sources transfers to ordering of solutions.  This is the sandwich engine for the
invariance `T(K) ⊆ K`: take `Rφ = Aλ U_`, `Rψ = R(u)` (and dually for `Ū`). -/
theorem aux_comparison (hlam : 0 < lam) {φ ψ Rφ Rψ : ℝ → ℝ}
    (hφ : φ = fun x => greenConv c lam Rφ x)
    (hψ : ψ = fun x => greenConv c lam Rψ x)
    (hle : ∀ y, Rφ y ≤ Rψ y)
    (hHiφ : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) Rφ) (Ioi x))
    (hHiψ : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) Rψ) (Ioi x))
    (hLoφ : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) Rφ) (Iic x))
    (hLoψ : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) Rψ) (Iic x)) :
    ∀ x, φ x ≤ ψ x := by
  intro x
  rw [hφ, hψ]
  exact greenConv_mono (c := c) hlam hle (hHiφ x) (hHiψ x) (hLoφ x) (hLoψ x)

/-! ## (2) Invariance `T(K) ⊆ K` — the sandwich

The trap set `K` we sandwich `u` between two barriers `U_ ≤ u ≤ Ū`.  Write the
divergence-form source `R(u) = −auxRHS p λ u = auxReaction p u + λ·u − χ·(auxFlux)'`.
The map value `T(u) = auxMap p c λ u = greenConv c λ (R(u))` (the committed
representation `hrepr`, i.e. `auxMap = −greenConv (auxRHS) = greenConv (R)`).

The invariance `U_ ≤ T(u) ≤ Ū` then follows from `aux_comparison` ONCE we know the
two SHIFTED barrier inequalities `Aλ U_ ≤ R(u) ≤ Aλ Ū`, i.e. the barriers are
super/sub-solutions of the shifted operator at every `u` in the trap.

`R(u)` splits as

* the LOCAL logistic part `auxReaction p u + λ·u`, controlled by the committed
  `frozenElliptic`/logistic bounds on `[0, M]` once `λ` is large; and
* the CHEMOTAXIS part `−χ·(auxFlux)' = −χ·((u^m)·V')'` with `V = frozenElliptic p u`,
  `χ ≤ 0`, `V' ≤ V` (committed `frozenElliptic_deriv_abs_le`), the genuinely hard
  Shen barrier algebra.

We carry the chemotaxis half of the two barrier inequalities as the SINGLE named
obligation `ChemotaxisSandwich`, and discharge the invariance from it via the
comparison engine. -/

/-- The divergence-form source `R(u) = −auxRHS = auxReaction + λ·u − χ·(auxFlux)'`. -/
def auxSource (p : CMParams) (lam : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  auxReaction p u x + lam * u x - p.χ * deriv (auxFlux p u) x

theorem auxSource_eq_neg_auxRHS (p : CMParams) (lam : ℝ) (u : ℝ → ℝ) (x : ℝ) :
    auxSource p lam u x = -auxRHS p lam u x := by
  unfold auxSource auxRHS; ring

/-- **Named obligation: the shifted barrier sandwich.**
The barriers `U_ ≤ Ū` are sub/super-solutions of the shifted operator `Aλ` at
every `u` in the trap `U_ ≤ u ≤ Ū`: `Aλ U_ ≤ R(u) ≤ Aλ Ū` pointwise, where
`Aλ w = greenConv⁻¹`-source, expressed through the representation sources
`RU_`, `RŪ` with `U_ = greenConv c λ RU_`, `Ū = greenConv c λ RŪ`.  Concretely
this is `RU_ ≤ auxSource p λ u ≤ RŪ`.

Discharging this from the committed estimates is the heavy chemotaxis algebra
(see report): the logistic half from `frozenElliptic_le_*`, the chemotaxis half
`−χ·((u^m)V')'` from `χ ≤ 0`, `V' ≤ V`, and the Shen negative-`χ` barrier bounds
`ShenUpperBoundNegative` + the `frozenElliptic` second-derivative sign. -/
structure ChemotaxisSandwich
    (p : CMParams) (lam : ℝ) (u U_ Ū RU_ RŪ : ℝ → ℝ) : Prop where
  lower : ∀ y, RU_ y ≤ auxSource p lam u y
  upper : ∀ y, auxSource p lam u y ≤ RŪ y

/-- **L2 invariance `T(K) ⊆ K`.**  Given the representation of `T(u)` and of the
barriers as variation-of-parameters solutions, plus the shifted barrier sandwich
(`ChemotaxisSandwich`) and convergent tails, the map value `T(u) = auxMap p c λ u`
stays in the trap: `U_ ≤ T(u) ≤ Ū` pointwise. -/
theorem auxMap_mem_trap (hlam : 0 < lam)
    (p : CMParams) {c : ℝ} (u U_ Ū RU_ RŪ : ℝ → ℝ)
    (hTu : auxMap p c lam u = fun x => greenConv c lam (auxSource p lam u) x)
    (hU_ : U_ = fun x => greenConv c lam RU_ x)
    (hŪ : Ū = fun x => greenConv c lam RŪ x)
    (hsand : ChemotaxisSandwich p lam u U_ Ū RU_ RŪ)
    (hHiU_ : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) RU_) (Ioi x))
    (hHiŪ : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) RŪ) (Ioi x))
    (hHiS : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) (auxSource p lam u)) (Ioi x))
    (hLoU_ : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) RU_) (Iic x))
    (hLoŪ : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) RŪ) (Iic x))
    (hLoS : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) (auxSource p lam u)) (Iic x)) :
    (∀ x, U_ x ≤ auxMap p c lam u x) ∧ (∀ x, auxMap p c lam u x ≤ Ū x) := by
  constructor
  · intro x
    have h := aux_comparison (c := c) hlam (φ := U_)
      (ψ := fun x => greenConv c lam (auxSource p lam u) x) (Rφ := RU_)
      (Rψ := auxSource p lam u) hU_ rfl hsand.lower hHiU_ hHiS hLoU_ hLoS x
    rw [hTu]; exact h
  · intro x
    have h := aux_comparison (c := c) hlam
      (φ := fun x => greenConv c lam (auxSource p lam u) x) (ψ := Ū)
      (Rφ := auxSource p lam u) (Rψ := RŪ) rfl hŪ hsand.upper hHiS hHiŪ hLoS hLoŪ x
    rw [hTu]; exact h

/-! ## (3) Compactness — weighted-sup total boundedness

We use an exponential weight `ρ` and the weighted-sup norm
`‖w‖_ρ = sup_x ρ(x)·|w(x)|`.  Relative compactness of `T(K)` follows from three
uniform controls on the image, all powered by the Green kernel `C¹` gain
`T(u)' = Kλ' ∗ R(u)` (which involves NO derivative of `u`):

* uniform boundedness        — `|T(u) x| ≤ Bsup` for all `u ∈ K`, `x`;
* uniform local equicontinuity — `|T(u) x − T(u) x'| ≤ Lip·|x − x'|`
  (the `C¹` gain, derivative bounded by `Bder`); and
* uniform tail smallness      — `ρ(x)·|T(u) x| → 0` uniformly in `u`.

Mathlib supplies Arzelà–Ascoli via `Equicontinuous` + `BddAbove`; the genuine
work is converting the three uniform controls into weighted-sup total
boundedness.  We isolate exactly that metric step as the named obligation
`WeightedCompactness`. -/

/-- Weighted-sup seminorm `‖w‖_ρ = sup_x ρ(x)·|w(x)|`, as an `iSup`. -/
def weightedSup (ρ w : ℝ → ℝ) : ℝ := ⨆ x, ρ x * |w x|

/-- **Named obligation: weighted total boundedness ⟹ relative compactness.**
The family `T(K) = { auxMap p c λ u | u ∈ K }`, viewed through the weighted-sup
seminorm `‖·‖_ρ`, is totally bounded: for every `ε > 0` there is a finite set of
centres `cs` such that every `T(u)` (with `u` in the trap, encoded by the carried
membership predicate `mem`) lies within `ε` of some centre.  Equivalently, the
image is relatively compact in the `‖·‖_ρ` metric.

Discharging this from the three uniform controls (uniform boundedness + the
`C¹`-gain local equicontinuity + uniform tail smallness) is the weighted
Arzelà–Ascoli step (see report). -/
structure WeightedCompactness
    (p : CMParams) (c lam : ℝ) (ρ : ℝ → ℝ) (mem : (ℝ → ℝ) → Prop) : Prop where
  totallyBounded : ∀ ε : ℝ, 0 < ε → ∃ cs : Finset (ℝ → ℝ),
    ∀ u, mem u → ∃ w ∈ cs, weightedSup ρ (fun x => auxMap p c lam u x - w x) ≤ ε

/-- **L2 compactness packaging.**  Relative compactness of `T(K)` in the weighted
seminorm is exactly the carried `WeightedCompactness` obligation; this lemma names
it as the deliverable consumed by the Schauder step (a fixed point of the now
compact, trap-preserving `T`). -/
theorem auxMap_image_totallyBounded
    (p : CMParams) (c lam : ℝ) (ρ : ℝ → ℝ) (mem : (ℝ → ℝ) → Prop)
    (hwc : WeightedCompactness p c lam ρ mem) (ε : ℝ) (hε : 0 < ε) :
    ∃ cs : Finset (ℝ → ℝ),
      ∀ u, mem u → ∃ w ∈ cs,
        weightedSup ρ (fun x => auxMap p c lam u x - w x) ≤ ε :=
  hwc.totallyBounded ε hε

end ShenWork.Paper1
