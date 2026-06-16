/-
  ShenWork/Paper1/WaveRotheClose.lean

  Closing the 3 carried hypotheses of `b1_chiNeg_existence`
  (`WaveRotheConcrete.lean`), tightening B1 χ≤0 traveling-wave existence to
  "modulo ONLY the G1 Schauder principle + committed profile lemmas".

  The three carried inputs of `b1_chiNeg_existence`:

    * `hVcont` : `∀ u, trap u → Continuous (deriv (frozenElliptic p u))`
    * `hprodAll` : `∀ u, RotheStepProducer p c lam M κ Λ u`
    * `hdep` : `RotheContinuousDependence p c lam (trap) rotheSeq`

  This file discharges what is closeable from the committed bricks.
-/
import ShenWork.Paper1.WaveFrozenEllipticDep
import ShenWork.Paper1.WaveRotheConcrete

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-! ## Item 1 — `hVcont` : continuity of the frozen elliptic drift derivative

`deriv (frozenElliptic p u) x = ½ ∫ frozenEllipticDerivKernel x y · (u y)^γ dy`
(committed `frozenElliptic_deriv_eq_kernel_integral`).  The derivative kernel is a
*shift* kernel `frozenEllipticDerivKernel x y = D(x − y)` with
`D(t) = if 0 ≤ t then -e^{-t} else e^{t}`, `|D t| ≤ e^{-|t|}`, so the integral is
a convolution `½ (D * u^γ)` with `D ∈ L¹` and `u^γ` bounded continuous —
continuous in `x` by continuity-under-the-integral. -/

/-- The shift form of the derivative kernel:
`D(t) = if 0 ≤ t then -e^{-t} else e^{t}`. -/
def frozenEllipticDerivKernelShift (t : ℝ) : ℝ :=
  if 0 ≤ t then -Real.exp (-t) else Real.exp t

theorem frozenEllipticDerivKernel_eq_shift (x y : ℝ) :
    frozenEllipticDerivKernel x y = frozenEllipticDerivKernelShift (x - y) := by
  unfold frozenEllipticDerivKernel frozenEllipticDerivKernelShift
  by_cases hyx : y ≤ x
  · have h0 : (0 : ℝ) ≤ x - y := by linarith
    simp only [hyx, if_true, h0]
  · have hx : x < y := lt_of_not_ge hyx
    have h0 : ¬ (0 : ℝ) ≤ x - y := by simp; linarith
    simp only [hyx, if_false, h0, if_false]
    congr 1; ring

theorem frozenEllipticDerivKernelShift_abs_le (t : ℝ) :
    |frozenEllipticDerivKernelShift t| ≤ Real.exp (-|t|) := by
  unfold frozenEllipticDerivKernelShift
  by_cases ht : 0 ≤ t
  · simp only [ht, if_true]
    rw [abs_neg, abs_of_pos (Real.exp_pos _), abs_of_nonneg ht]
  · simp only [ht, if_false]
    have htlt : t < 0 := lt_of_not_ge ht
    rw [abs_of_pos (Real.exp_pos _), abs_of_neg htlt]
    have : -(-t) = t := by ring
    rw [this]

/-- The shift kernel `D` is integrable (dominated by `e^{-|t|}`). -/
theorem frozenEllipticDerivKernelShift_integrable :
    Integrable frozenEllipticDerivKernelShift := by
  have hdom : Integrable (fun t : ℝ => Real.exp (-|0 - t|)) :=
    exp_neg_abs_sub_integrable 0
  have hdom' : Integrable (fun t : ℝ => Real.exp (-|t|)) := by
    have heq : (fun t : ℝ => Real.exp (-|0 - t|)) = fun t : ℝ => Real.exp (-|t|) := by
      funext t; congr 2; rw [zero_sub, abs_neg]
    rwa [heq] at hdom
  have hmeas : AEStronglyMeasurable frozenEllipticDerivKernelShift volume := by
    have hpiece : StronglyMeasurable
        ((Set.Ici (0 : ℝ)).piecewise
          (fun t : ℝ => -Real.exp (-t))
          (fun t : ℝ => Real.exp t)) :=
      StronglyMeasurable.piecewise measurableSet_Ici
        (by fun_prop : Continuous fun t : ℝ => -Real.exp (-t)).stronglyMeasurable
        (by fun_prop : Continuous fun t : ℝ => Real.exp t).stronglyMeasurable
    refine hpiece.aestronglyMeasurable.congr ?_
    filter_upwards with t
    unfold frozenEllipticDerivKernelShift Set.piecewise
    simp only [Set.mem_Ici]
  refine Integrable.mono' hdom' hmeas (Filter.Eventually.of_forall (fun t => ?_))
  rw [Real.norm_eq_abs]
  exact frozenEllipticDerivKernelShift_abs_le t

/-- The convolution value `½ ∫ D(x−y)·g(y) dy` of the shift kernel against a
bounded-continuous `g` is continuous in `x` (continuity under the integral). -/
theorem deriv_kernel_conv_continuous {g : ℝ → ℝ} (hg : IsCUnifBdd g) :
    Continuous (fun x => ∫ y, frozenEllipticDerivKernelShift (x - y) * g y) := by
  rcases hg.2 with ⟨Mg, hMg⟩
  have hMg0 : 0 ≤ Mg := le_trans (abs_nonneg (g 0)) (hMg 0)
  -- change of variables: ∫ y, D(x−y) g y = ∫ z, D z · g(x−z)
  have hEq : (fun x => ∫ y, frozenEllipticDerivKernelShift (x - y) * g y)
      = fun x => ∫ z, frozenEllipticDerivKernelShift z * g (x - z) := by
    funext x
    have h := integral_sub_left_eq_self
      (fun z => frozenEllipticDerivKernelShift z * g (x - z)) (volume : Measure ℝ) x
    simp only [sub_sub_cancel] at h
    exact h
  rw [hEq]
  have hDint := frozenEllipticDerivKernelShift_integrable
  refine continuous_of_dominated
    (F := fun x z => frozenEllipticDerivKernelShift z * g (x - z))
    (bound := fun z => Real.exp (-|z|) * Mg) ?_ ?_ ?_ ?_
  · -- AE strong measurability in z for each x
    intro x
    have hg_cont : Continuous (fun z => g (x - z)) := hg.1.comp (by fun_prop)
    exact hDint.aestronglyMeasurable.mul hg_cont.aestronglyMeasurable
  · -- pointwise bound by the x-independent dominator
    intro x
    refine Eventually.of_forall (fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (frozenEllipticDerivKernelShift_abs_le z) (hMg (x - z))
      (abs_nonneg _) (Real.exp_nonneg _)
  · -- the dominator is integrable
    have hexp : Integrable (fun z : ℝ => Real.exp (-|z|)) := by
      have hdom : Integrable (fun t : ℝ => Real.exp (-|0 - t|)) :=
        exp_neg_abs_sub_integrable 0
      have heq : (fun t : ℝ => Real.exp (-|0 - t|)) = fun t : ℝ => Real.exp (-|t|) := by
        funext t; congr 2; rw [zero_sub, abs_neg]
      rwa [heq] at hdom
    exact hexp.mul_const Mg
  · -- continuity in x for each fixed z
    refine Eventually.of_forall (fun z => ?_)
    exact continuous_const.mul (hg.1.comp (by fun_prop))

/-- **Item 1 (`hVcont`).**  The frozen elliptic drift derivative
`x ↦ deriv (frozenElliptic p u) x` is continuous, for any cunif-bounded
nonnegative profile `u`. -/
theorem frozenElliptic_deriv_continuous
    (p : CMParams) {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ x, 0 ≤ u x) :
    Continuous (deriv (frozenElliptic p u)) := by
  have hg : IsCUnifBdd (fun y => (u y) ^ p.γ) :=
    rpow_cunif_bdd_of_nonneg p hu hu_nonneg
  have hrep : deriv (frozenElliptic p u)
      = fun x => 1 / 2 * ∫ y, frozenEllipticDerivKernelShift (x - y) * (u y) ^ p.γ := by
    funext x
    rw [frozenElliptic_deriv_eq_kernel_integral p hu hu_nonneg]
    congr 1
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp only []
    rw [frozenEllipticDerivKernel_eq_shift]
  rw [hrep]
  exact continuous_const.mul (deriv_kernel_conv_continuous hg)

/-- **Item 1, trap-shaped.**  The `hVcont` input consumed by `b1_chiNeg_existence`. -/
theorem frozenElliptic_deriv_continuous_trap
    (p : CMParams) {κ M : ℝ} :
    ∀ u, InMonotoneWaveTrapSet κ M u →
      Continuous (deriv (frozenElliptic p u)) :=
  fun u hu => frozenElliptic_deriv_continuous p hu.trap.cunif_bdd hu.nonneg

/-! ## `b1_chiNeg_existence_clean` — `hVcont` discharged

`b1_chiNeg_existence` carries three uncommitted inputs: `hVcont`, the per-step
producer `hprodAll`, and the continuous dependence `hdep`.

Item 1 (`frozenElliptic_deriv_continuous_trap`) closes `hVcont` outright from the
committed kernel representation, so it drops out of the signature below.

The remaining carried inputs (`hprodAll`, `hdep`) are the genuinely-deep pieces:

  * `hprodAll : ∀ u, RotheStepProducer p c lam M κ Λ u` — the per-step bridge.
    The committed `crossStep_exists_unique_concrete` produces a unique
    *truncated* BCF step fixed point (`crossStepSelfMap` with the `[0,M]`
    truncated source `crossStepSourceConcrete`); the producer's
    `step_eq : W = crossImplicitMap …` is the *un-truncated* raw integral.
    Bridging requires (a) the `greenConvBCF`↔raw-`greenKernel` identity and
    (b) removal of the source truncation on the trapped range — and (b) rests on
    the max-principle trap bound, whose source-ordering obligations
    (`ImplicitStepSuperOrdering`) are themselves uncommitted, satisfiable
    hypotheses.  So discharging `hprodAll` would *introduce* fresh carried
    obligations rather than eliminate carried inputs; it is NOT closeable from
    the committed bricks without new satisfiable hypotheses.  Carried.

  * `hdep : RotheContinuousDependence …` — the (B)-propagation
    `u_n → u ⟹ Tmap u_n → Tmap u`.  Its deep core
    `frozenEllipticDerivDependence` IS committed, but propagating it through the
    Rothe limit (the per-step Green map's continuous dependence on `V'_u`, passed
    to the limit via dominated convergence with the uniform contraction
    constants) is not a committed closed lemma.  This is the one genuinely
    analytic propagation.  Carried.

`b1_chiNeg_existence_clean` therefore reduces B1 χ≤0 to EXACTLY:
the G1 principle `hprinciple`, the committed profile lemmas
(`hGreen`/`hpos`/`hbdd`/`hlim_neg`/`hlim_pos`), the scalar/trap side-conditions,
PLUS the two carried inputs `hprodAll` and `hdep`. -/

/-- **B1 χ≤0 existence — `hVcont` discharged.**
Identical to `b1_chiNeg_existence` but with the `hVcont` continuity input
supplied internally from item 1 (`frozenElliptic_deriv_continuous_trap`), so the
signature no longer carries it.  The remaining carried inputs are exactly
`hprodAll` (per-step producer) and `hdep` (continuous dependence). -/
theorem b1_chiNeg_existence_clean
    (p : CMParams) (c lam M Bv κ Λ : ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hM : 0 ≤ M) (hBv : 0 ≤ Bv)
    (hκ : 0 ≤ κ) (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hprodAll : ∀ u, RotheStepProducer p c lam M κ Λ u)
    (hbarLip : ∀ x y, |upperBarrier κ M x - upperBarrier κ M y| ≤ M * |x - y|)
    (hŪbdd : IsBddFun (upperBarrier κ M))
    -- only the bound stays carried; continuity is now internal (item 1):
    (hVbound : ∀ u, InMonotoneWaveTrapSet κ M u →
        ∀ y, |deriv (frozenElliptic p u) y| ≤ Bv)
    (hdep : RotheContinuousDependence p c lam (InMonotoneWaveTrapSet κ M)
        (fun u => rotheSeqOf p c lam M κ Λ u (hprodAll u) hκ hM))
    (hprinciple : LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet κ M))
    (hGreen : ∀ U, InMonotoneWaveTrapSet κ M U →
        rotheLimit (rotheSeqOf p c lam M κ Λ U (hprodAll U) hκ hM) = U →
          GreenIdentity p c lam U)
    (hpos : ∀ U, InMonotoneWaveTrapSet κ M U → (∀ x, 0 < U x))
    (hbdd : ∀ U, InMonotoneWaveTrapSet κ M U → IsCUnifBdd U)
    (hlim_neg : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atBot (𝓝 1))
    (hlim_pos : ∀ U, InMonotoneWaveTrapSet κ M U → Tendsto U atTop (𝓝 0)) :
    ∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence p c lam M Bv κ Λ hc hlam hM hBv hκ hΛ0 hΛM
    hprodAll hbarLip hŪbdd
    (frozenElliptic_deriv_continuous_trap p)
    hVbound hdep hprinciple hGreen hpos hbdd hlim_neg hlim_pos

section AxiomAudit

#print axioms frozenElliptic_deriv_continuous
#print axioms frozenElliptic_deriv_continuous_trap
#print axioms b1_chiNeg_existence_clean

end AxiomAudit

end ShenWork.Paper1
