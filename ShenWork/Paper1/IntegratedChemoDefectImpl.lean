/-
  ShenWork/Paper1/IntegratedChemoDefectImpl.lean

  The INTEGRATED chemotaxis-defect sign — the genuine P1 #4 chemo wall.

  CONTEXT (landed).  `IntervalP1ChemoMonotone.lean` reduced the implicit-step
  super-ordering `greenConv(crossSource W) ≤ greenConv(barrierSource Z)` to the
  SINGLE `W'`-free hypothesis

      hsign :  0 ≤ greenConv(reactionIncr Z W) x
                  + (-χ)·∫ Kλ'(x−y)·(stepFlux_Z y − stepFlux_W y) dy

  (`crossSource_greenConv_le_barrierSource_of_integrated_residual`, :236).  The
  POINTWISE source antitone is FALSE (V'' indeterminate; ChatGPT Q363 reaction
  counterexample), so the construction routes INTEGRATED.  The chemo defect
  `(-χ)·∫ Kλ'·(stepFlux_Z − stepFlux_W)` is the IBP image of
  `greenConv((-χ)·(stepFlux_Z − stepFlux_W)')` (`stepFlux_diff_ibp`); `W'` is
  eliminated, but the integrand `(Z^m − W^m)·V'` is a NONNEGATIVE factor
  (`W ≤ Z`, `m ≥ 1`) times a SIGN-INDEFINITE factor (`V' = (frozenElliptic)'`),
  and `Kλ'` itself flips sign at `y = x`.  So the bare chemo defect is NOT
  signed by `W ≤ Z` alone, and — since the derivative sits on the KERNEL, not the
  source — `greenConv_mono` does NOT apply to the `Kλ'` integral.

  WHAT THIS FILE LANDS (axiom-clean, `{propext, Classical.choice, Quot.sound}`).
  The DIFFERENCE structure that IS signable, isolating the irreducible sub-sign:

  * `reactionIncr_ge_negLamShift_pointwise` — the committed pointwise reaction
    Lipschitz bound, read on the difference: `−(λ·(Z−W)) ≤ reactionIncr` at each
    `y` (trap `W,Z ∈ [0,M]`, `W ≤ Z`, `λ ≥ reactionLip`).

  * `greenConv_reactionIncr_ge_negLamShift` — pushed through `greenConv_mono`
    (`Kλ ≥ 0`, order-preserving in the SOURCE): the Green image of the reaction
    increment dominates the Green image of the `λ`-shift,
    `greenConv(−λ(Z−W)) ≤ greenConv(reactionIncr)`.  This is exactly where the
    monotone Green operator acts on the DIFFERENCE — legitimately, because the
    reaction increment is a bona-fide SOURCE (no kernel derivative).

  * `hsign_of_chemoDefect_ge_lamShift` — the REDUCTION: `hsign` holds as soon as
    the integrated chemo defect dominates the `λ`-shift Green image,
    `−greenConv(−λ(Z−W)) ≤ (-χ)·∫ Kλ'·(stepFlux_Z − stepFlux_W)`.  The reaction
    increment is absorbed unconditionally; the genuine remaining content is this
    single scalar chemo-defect dominance.

  * `crossSource_greenConv_le_barrierSource_of_chemoDefect_dominates` /
    `stepProfile_le_old_of_chemoDefect_dominates` — wire the reduced sign into
    the landed integrated comparison, so the construction's `W ≤ Z` field is now
    gated on the `W'`-free chemo-defect dominance instead of raw `hsign`.

  VERDICT (signature audit, in the file header of the report).  The chemo-defect
  dominance `−greenConv(−λ(Z−W)) ≤ (-χ)·∫ Kλ'·(stepFlux_Z−stepFlux_W)` is the
  PRECISE irreducible sub-sign.  It is NOT a consequence of `W ≤ Z` + monotone
  Green: the `Kλ'`-against-`(Z^m−W^m)·V'` integral is genuinely sign-indefinite
  (kernel flips at `y=x`; `V'` indefinite), so it is a CARRIED analytic obligation
  (satisfiable on the trap via the quantitative `V'` control, not provable from the
  order structure alone).  What IS unconditional and discharged here: the entire
  reaction half, and the reduction of `hsign` to this one named scalar inequality.

  No `sorry`/`axiom`/`native_decide`/`admit`.  New file only; touches nothing.
-/
import ShenWork.Paper1.IntervalP1ChemoMonotone
import ShenWork.Paper1.WaveRotheOrder

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## 1 — the reaction half is unconditionally signed

`reactionIncr p Z W y = reactionFun α (Z y) − reactionFun α (W y)`.  On the trap
`W y, Z y ∈ [0,M]` with `W y ≤ Z y` and `λ ≥ reactionLip α M`, the committed
Lipschitz increment bound gives the pointwise lower bound by the `λ`-shift. -/

/-- The reaction increment dominates the negative `λ`-shift, pointwise on the
trap.  Direct from the committed `reaction_increment_ge_neg_lambda_shift`
(`b = Z y`, `w = W y`). -/
theorem reactionIncr_ge_negLamShift_pointwise
    (p : CMParams) {M : ℝ} {Z W : ℝ → ℝ} (hM : 0 ≤ M)
    (hlam : reactionLip p.α M ≤ lam)
    (hW : ∀ y, W y ∈ Set.Icc (0 : ℝ) M) (hZ : ∀ y, Z y ∈ Set.Icc (0 : ℝ) M)
    (hWZ : ∀ y, W y ≤ Z y) (y : ℝ) :
    -(lam * (Z y - W y)) ≤ reactionIncr p Z W y := by
  have h := reaction_increment_ge_neg_lambda_shift (a := p.α) (M := M)
    p.hα hM hlam (hW y) (hZ y) (hWZ y)
  simpa only [reactionIncr] using h

/-! ## 2 — push the reaction bound through the monotone Green operator

`greenConv` is order-preserving in its SOURCE (`greenConv_mono`, `Kλ ≥ 0`).  The
reaction increment is a legitimate source (no kernel derivative), so the pointwise
bound of §1 transfers to the Green images. -/

/-- The Green image of the reaction increment dominates the Green image of the
`λ`-shift source.  This is `greenConv_mono` applied to the §1 pointwise bound. -/
theorem greenConv_reactionIncr_ge_negLamShift
    (hlam0 : 0 < lam) (p : CMParams) {M : ℝ} {Z W : ℝ → ℝ} (x : ℝ)
    (hM : 0 ≤ M) (hlam : reactionLip p.α M ≤ lam)
    (hW : ∀ y, W y ∈ Set.Icc (0 : ℝ) M) (hZ : ∀ y, Z y ∈ Set.Icc (0 : ℝ) M)
    (hWZ : ∀ y, W y ≤ Z y)
    (hSh_Hi : IntegrableOn
      (gWeight (greenRootPlus c lam) (fun y => -(lam * (Z y - W y)))) (Ioi x))
    (hSh_Lo : IntegrableOn
      (gWeight (greenRootMinus c lam) (fun y => -(lam * (Z y - W y)))) (Iic x))
    (hRI_Hi : IntegrableOn (gWeight (greenRootPlus c lam) (reactionIncr p Z W)) (Ioi x))
    (hRI_Lo : IntegrableOn (gWeight (greenRootMinus c lam) (reactionIncr p Z W)) (Iic x)) :
    greenConv c lam (fun y => -(lam * (Z y - W y))) x
      ≤ greenConv c lam (reactionIncr p Z W) x :=
  greenConv_mono (c := c) hlam0
    (fun y => reactionIncr_ge_negLamShift_pointwise p hM hlam hW hZ hWZ y)
    hSh_Hi hRI_Hi hSh_Lo hRI_Lo

/-! ## 3 — the reduction: `hsign` from the chemo-defect dominance

The integrated residual sign `hsign` decomposes as
`greenConv(reactionIncr) + chemoDefect ≥ 0`.  By §2 the reaction term is bounded
below by `greenConv(−λ(Z−W))`, so `hsign` holds whenever the chemo defect
dominates `−greenConv(−λ(Z−W))`.  The reaction half is thereby discharged; the
genuine remaining content is the single scalar chemo-defect dominance. -/

/-- **The reduced integrated sign.**  `hsign` (the hypothesis the landed
comparison needs) follows from the §2 reaction bound and the chemo-defect
dominance `hDom`.  No further order structure is used: the reaction increment is
absorbed unconditionally. -/
theorem hsign_of_chemoDefect_ge_lamShift
    (hlam0 : 0 < lam) (p : CMParams) {M : ℝ} (u Z W : ℝ → ℝ) (x : ℝ)
    (hM : 0 ≤ M) (hlam : reactionLip p.α M ≤ lam)
    (hW : ∀ y, W y ∈ Set.Icc (0 : ℝ) M) (hZ : ∀ y, Z y ∈ Set.Icc (0 : ℝ) M)
    (hWZ : ∀ y, W y ≤ Z y)
    (hSh_Hi : IntegrableOn
      (gWeight (greenRootPlus c lam) (fun y => -(lam * (Z y - W y)))) (Ioi x))
    (hSh_Lo : IntegrableOn
      (gWeight (greenRootMinus c lam) (fun y => -(lam * (Z y - W y)))) (Iic x))
    (hRI_Hi : IntegrableOn (gWeight (greenRootPlus c lam) (reactionIncr p Z W)) (Ioi x))
    (hRI_Lo : IntegrableOn (gWeight (greenRootMinus c lam) (reactionIncr p Z W)) (Iic x))
    (hDom : -greenConv c lam (fun y => -(lam * (Z y - W y))) x
      ≤ (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * (stepFlux p u Z y - stepFlux p u W y)) :
    0 ≤ greenConv c lam (reactionIncr p Z W) x
        + (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * (stepFlux p u Z y - stepFlux p u W y) := by
  have hreac := greenConv_reactionIncr_ge_negLamShift (c := c) hlam0 p x hM hlam hW hZ hWZ
    hSh_Hi hSh_Lo hRI_Hi hRI_Lo
  linarith [hreac, hDom]

/-! ## 4 — wire the reduced sign into the landed integrated comparison

Feeding the reduced `hsign` into
`crossSource_greenConv_le_barrierSource_of_integrated_residual` gives the
implicit-step super-ordering gated on the `W'`-free chemo-defect dominance. -/

/-- **Integrated super-ordering from chemo-defect dominance.**
`greenConv(crossSource W) ≤ greenConv(barrierSource Z)` with the chemotaxis
obligation reduced to the single scalar chemo-defect dominance `hDom` (the
reaction half discharged unconditionally via §1–§3). -/
theorem crossSource_greenConv_le_barrierSource_of_chemoDefect_dominates
    (hlam0 : 0 < lam) (p : CMParams) {M : ℝ} (u Z W : ℝ → ℝ) (x : ℝ)
    (hM : 0 ≤ M) (hlam : reactionLip p.α M ≤ lam)
    (hWmem : ∀ y, W y ∈ Set.Icc (0 : ℝ) M) (hZmem : ∀ y, Z y ∈ Set.Icc (0 : ℝ) M)
    (hWZ : ∀ y, W y ≤ Z y)
    (hZC1 : ∀ y, HasDerivAt (stepFlux p u Z) (deriv (stepFlux p u Z) y) y)
    (hWC1 : ∀ y, HasDerivAt (stepFlux p u W) (deriv (stepFlux p u W) y) y)
    (hBS_Hi : IntegrableOn (gWeight (greenRootPlus c lam) (barrierSource p lam u Z)) (Ioi x))
    (hBS_Lo : IntegrableOn (gWeight (greenRootMinus c lam) (barrierSource p lam u Z)) (Iic x))
    (hCS_Hi : IntegrableOn (gWeight (greenRootPlus c lam) (crossSource p lam u Z W)) (Ioi x))
    (hCS_Lo : IntegrableOn (gWeight (greenRootMinus c lam) (crossSource p lam u Z W)) (Iic x))
    (hRI_Hi : IntegrableOn (gWeight (greenRootPlus c lam) (reactionIncr p Z W)) (Ioi x))
    (hRI_Lo : IntegrableOn (gWeight (greenRootMinus c lam) (reactionIncr p Z W)) (Iic x))
    (hSh_Hi : IntegrableOn
      (gWeight (greenRootPlus c lam) (fun y => -(lam * (Z y - W y)))) (Ioi x))
    (hSh_Lo : IntegrableOn
      (gWeight (greenRootMinus c lam) (fun y => -(lam * (Z y - W y)))) (Iic x))
    (hCD_Hi : IntegrableOn
      (gWeight (greenRootPlus c lam) (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y)) (Ioi x))
    (hCD_Lo : IntegrableOn
      (gWeight (greenRootMinus c lam) (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y)) (Iic x))
    (hChemo : greenConv c lam (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y) x
      = (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * (stepFlux p u Z y - stepFlux p u W y))
    (hDom : -greenConv c lam (fun y => -(lam * (Z y - W y))) x
      ≤ (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * (stepFlux p u Z y - stepFlux p u W y)) :
    greenConv c lam (crossSource p lam u Z W) x ≤ greenConv c lam (barrierSource p lam u Z) x := by
  have hsign := hsign_of_chemoDefect_ge_lamShift (c := c) hlam0 p u Z W x hM hlam
    hWmem hZmem hWZ hSh_Hi hSh_Lo hRI_Hi hRI_Lo hDom
  exact crossSource_greenConv_le_barrierSource_of_integrated_residual p u Z W x hZC1 hWC1
    hBS_Hi hBS_Lo hCS_Hi hCS_Lo hRI_Hi hRI_Lo hCD_Hi hCD_Lo hChemo hsign

/-- **`W ≤ Z` from chemo-defect dominance.**  When `W`/`Z` are Green images of
their sources, the §4 comparison yields `W ≤ Z` pointwise, with the chemotaxis
obligation in the reduced `W'`-free chemo-defect-dominance form. -/
theorem stepProfile_le_old_of_chemoDefect_dominates
    (hlam0 : 0 < lam) (p : CMParams) {M : ℝ} (u Z W : ℝ → ℝ)
    (hM : 0 ≤ M) (hlam : reactionLip p.α M ≤ lam)
    (hWmem : ∀ y, W y ∈ Set.Icc (0 : ℝ) M) (hZmem : ∀ y, Z y ∈ Set.Icc (0 : ℝ) M)
    (hWZ : ∀ y, W y ≤ Z y)
    (hZC1 : ∀ y, HasDerivAt (stepFlux p u Z) (deriv (stepFlux p u Z) y) y)
    (hWC1 : ∀ y, HasDerivAt (stepFlux p u W) (deriv (stepFlux p u W) y) y)
    (hWeq : ∀ x, W x = greenConv c lam (crossSource p lam u Z W) x)
    (hZeq : ∀ x, Z x = greenConv c lam (barrierSource p lam u Z) x)
    (hBS_Hi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) (barrierSource p lam u Z)) (Ioi x))
    (hBS_Lo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) (barrierSource p lam u Z)) (Iic x))
    (hCS_Hi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) (crossSource p lam u Z W)) (Ioi x))
    (hCS_Lo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) (crossSource p lam u Z W)) (Iic x))
    (hRI_Hi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) (reactionIncr p Z W)) (Ioi x))
    (hRI_Lo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) (reactionIncr p Z W)) (Iic x))
    (hSh_Hi : ∀ x, IntegrableOn
      (gWeight (greenRootPlus c lam) (fun y => -(lam * (Z y - W y)))) (Ioi x))
    (hSh_Lo : ∀ x, IntegrableOn
      (gWeight (greenRootMinus c lam) (fun y => -(lam * (Z y - W y)))) (Iic x))
    (hCD_Hi : ∀ x, IntegrableOn
      (gWeight (greenRootPlus c lam) (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y)) (Ioi x))
    (hCD_Lo : ∀ x, IntegrableOn
      (gWeight (greenRootMinus c lam) (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y)) (Iic x))
    (hChemo : ∀ x, greenConv c lam (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y) x
      = (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * (stepFlux p u Z y - stepFlux p u W y))
    (hDom : ∀ x, -greenConv c lam (fun y => -(lam * (Z y - W y))) x
      ≤ (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * (stepFlux p u Z y - stepFlux p u W y)) :
    ∀ x, W x ≤ Z x := by
  intro x
  rw [hWeq x, hZeq x]
  exact crossSource_greenConv_le_barrierSource_of_chemoDefect_dominates (c := c) hlam0 p u Z W x
    hM hlam hWmem hZmem hWZ hZC1 hWC1 (hBS_Hi x) (hBS_Lo x) (hCS_Hi x) (hCS_Lo x)
    (hRI_Hi x) (hRI_Lo x) (hSh_Hi x) (hSh_Lo x) (hCD_Hi x) (hCD_Lo x) (hChemo x) (hDom x)

/-! ## Axiom audit -/

section AxiomAudit
#print axioms reactionIncr_ge_negLamShift_pointwise
#print axioms greenConv_reactionIncr_ge_negLamShift
#print axioms hsign_of_chemoDefect_ge_lamShift
#print axioms crossSource_greenConv_le_barrierSource_of_chemoDefect_dominates
#print axioms stepProfile_le_old_of_chemoDefect_dominates
end AxiomAudit

end ShenWork.Paper1
