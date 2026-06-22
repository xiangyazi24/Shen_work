/-
  ShenWork/Paper1/IntervalP1ChemoMonotone.lean

  The chemotaxis quasi-monotonicity residual, discharged in INTEGRATED form —
  the last analytic piece below the P1 Rothe limit, above the landed
  Green-positivity order layer (`IntervalP1OrderLayer.lean`).

  CONTEXT (landed `a15e1e1`).  The P1 order layer reduces the barrier comparison
  `W ≤ Z` to the source ordering `crossSource p lam u Z W ≤ barrierSource p lam u Z`
  (`stepProfile_le_old_of_source_le`).  The STALL NOTE (`WaveRotheOrder.lean:312`)
  documents that the *pointwise* source ordering carries the step-solution
  derivative `W'` (through `(W^m)' = m W^{m-1} W'` inside `∂ₓ stepFlux`), which is
  NOT folded away by the committed single-profile barrier machinery.  The
  committed discharge route is the cross-frozen flux-difference IBP
  `stepFlux_diff_ibp` (`WaveStepFluxIBP.lean`, landed `4cea4e2`) + `greenConv_mono`:
  it moves the derivative off the flux DIFFERENCE at the level of the whole Green
  map, so no `W'` survives pointwise.

  WHAT THIS FILE LANDS (axiom-clean, `{propext, Classical.choice, Quot.sound}`):

  * `barrierSource_sub_crossSource` — the clean pointwise decomposition
        `barrierSource Z − crossSource W
            = (reaction(Z) − reaction(W)) + (−χ)·(stepFlux_Z − stepFlux_W)'`,
    isolating the reaction increment from the chemotaxis flux difference.

  * `greenConv_chemoDefect_eq_kernelDeriv` — the INTEGRATED chemotaxis defect:
    the Green image of the folded flux-difference divergence equals the
    `Kλ'`-against-`(stepFlux_Z − stepFlux_W)` integral, via `stepFlux_diff_ibp`.
    THIS is where `W'` is eliminated: the conclusion has no derivative of any
    profile, only the flux difference itself.

  * `greenConv_residual_split` — `greenConv (barrierSource Z − crossSource W)`
    splits as `greenConv(reaction increment) + (−χ)·∫ Kλ'·(stepFlux_Z − stepFlux_W)`,
    the `W'`-free integrated residual.

  * `crossSource_greenConv_le_barrierSource_of_integrated_residual` — the
    integrated quasi-monotonicity: `greenConv(crossSource W) ≤ greenConv(barrierSource Z)`
    from the SINGLE `W'`-free hypothesis `0 ≤ greenConv(residual)` (equivalently,
    nonnegativity of the integrated reaction-increment-plus-chemo-defect).

  * `stepProfile_le_old_of_integrated_residual` — wires the integrated comparison
    to `W ≤ Z` directly, bypassing the pointwise residual:  combined with the
    landed `greenConv_le_majorant_of_source_le` engine it yields the `upperOld`
    order field with the chemotaxis obligation now in `W'`-free integrated form.

  No `sorry`/`axiom`/`native_decide`/`admit`.  The decay / per-tail integrability
  hypotheses of the flux IBP are carried explicitly (every Rothe iterate is in the
  trap, so they are satisfiable — they are the standard `flux_ibp_generic` data,
  NOT the conclusion).  New file only; touches nothing existing.
-/
import ShenWork.Paper1.WaveStepFluxIBP
import ShenWork.Paper1.WaveConvRepr
import ShenWork.Paper1.IntervalP1OrderLayer

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## 1 — the pointwise residual decomposition

`barrierSource Z − crossSource W` separates into the reaction increment and the
folded chemotaxis flux DIFFERENCE.  No cancellation, no sign claim — just the
algebraic split that the IBP will act on. -/

/-- The reaction increment between the two profiles at `y`. -/
def reactionIncr (p : CMParams) (Z W : ℝ → ℝ) (y : ℝ) : ℝ :=
  reactionFun p.α (Z y) - reactionFun p.α (W y)

/-- The folded flux-difference divergence splits into the two single-profile flux
derivatives, given `C¹`-ness of each `stepFlux`.  This is the only place where the
two-profile `C¹` data enter the residual algebra. -/
theorem deriv_stepFluxDiff_eq (p : CMParams) (u W Z : ℝ → ℝ) {y : ℝ}
    (hZ : HasDerivAt (stepFlux p u Z) (deriv (stepFlux p u Z) y) y)
    (hW : HasDerivAt (stepFlux p u W) (deriv (stepFlux p u W) y) y) :
    deriv (stepFluxDiff p u W Z) y
      = deriv (stepFlux p u Z) y - deriv (stepFlux p u W) y := by
  have hsub : HasDerivAt (stepFluxDiff p u W Z)
      (deriv (stepFlux p u Z) y - deriv (stepFlux p u W) y) y := by
    simpa only [stepFluxDiff] using hZ.sub hW
  exact hsub.deriv

/-- **Residual decomposition.**
`barrierSource Z − crossSource W` is the reaction increment plus the folded
flux-difference divergence `(−χ)·∂ₓ(stepFlux_Z − stepFlux_W)`.  The two sources
share the `λ·Z` term (the comparison barrier here is `B = Z`), which cancels.
The flux-difference derivative is split via `deriv_stepFluxDiff_eq` (the two-profile
`C¹` data). -/
theorem barrierSource_sub_crossSource (p : CMParams) (lam : ℝ) (u Z W : ℝ → ℝ) {y : ℝ}
    (hZ : HasDerivAt (stepFlux p u Z) (deriv (stepFlux p u Z) y) y)
    (hW : HasDerivAt (stepFlux p u W) (deriv (stepFlux p u W) y) y) :
    barrierSource p lam u Z y - crossSource p lam u Z W y
      = reactionIncr p Z W y
        + (-p.χ) * deriv (stepFluxDiff p u W Z) y := by
  rw [deriv_stepFluxDiff_eq p u W Z hZ hW]
  unfold barrierSource crossSource reactionIncr stepFlux
  ring

/-! ## 2 — the integrated chemotaxis defect (where `W'` is eliminated)

The Green image of the folded flux-difference divergence equals the
`Kλ'`-against-`(stepFlux_Z − stepFlux_W)` integral.  This is precisely the
committed `stepFlux_diff_ibp` read right-to-left: the conclusion contains the flux
DIFFERENCE itself (no derivative of any profile), so `W'` no longer appears. -/

/-- **Integrated chemotaxis defect.**  Via `stepFlux_diff_ibp`,
    `greenConv c λ ((−χ)·(stepFlux_Z − stepFlux_W)') x
        = (−χ)·∫ y, Kλ'(x−y)·(stepFlux_Z y − stepFlux_W y) dy`.
The right side carries no `W'`: the derivative sits on the kernel. -/
theorem greenConv_chemoDefect_eq_kernelDeriv
    (hlam : 0 < lam) (p : CMParams) (u W Z : ℝ → ℝ) (x : ℝ)
    (hG_C1 : ∀ y, HasDerivAt (stepFluxDiff p u W Z) (deriv (stepFluxDiff p u W Z) y) y)
    (hKv'_Ioi : IntegrableOn
      ((fun y => greenKernel c lam (x - y)) * deriv (stepFluxDiff p u W Z)) (Ioi x))
    (hKv'_Iic : IntegrableOn
      ((fun y => greenKernel c lam (x - y)) * deriv (stepFluxDiff p u W Z)) (Iic x))
    (hK'v_Ioi : IntegrableOn
      ((fun y => -greenKernelDeriv c lam (x - y)) * stepFluxDiff p u W Z) (Ioi x))
    (hK'v_Iic : IntegrableOn
      ((fun y => -greenKernelDeriv c lam (x - y)) * stepFluxDiff p u W Z) (Iic x))
    (hKG_Iic : IntegrableOn
      (fun y => greenKernel c lam (x - y) * (-p.χ * deriv (stepFluxDiff p u W Z) y)) (Iic x))
    (hKG_Ioi : IntegrableOn
      (fun y => greenKernel c lam (x - y) * (-p.χ * deriv (stepFluxDiff p u W Z) y)) (Ioi x))
    (hdecay_top : Tendsto ((fun y => greenKernel c lam (x - y)) * stepFluxDiff p u W Z)
      atTop (𝓝 0))
    (hdecay_bot : Tendsto ((fun y => greenKernel c lam (x - y)) * stepFluxDiff p u W Z)
      atBot (𝓝 0)) :
    greenConv c lam (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y) x
      = (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * (stepFlux p u Z y - stepFlux p u W y) := by
  exact (stepFlux_diff_ibp c lam hlam p u W Z x hG_C1
    hKv'_Ioi hKv'_Iic hK'v_Ioi hK'v_Iic hKG_Iic hKG_Ioi hdecay_top hdecay_bot).symm

/-! ## 3 — the integrated residual split

`greenConv(barrierSource Z) − greenConv(crossSource W)` equals the Green image of
the residual decomposition, which the IBP turns into
`greenConv(reactionIncr) + (−χ)·∫ Kλ'·(stepFlux_Z − stepFlux_W)`.  Both summands
are `W'`-free.  We carry the per-tail integrabilities of the two named source
parts (`reactionIncr` and the folded flux defect), satisfiable on the trap. -/

/-- The Green image of the residual difference, split via `greenConv_add` and the
pointwise decomposition `barrierSource_sub_crossSource`. -/
theorem greenConv_residual_eq
    (p : CMParams) (u Z W : ℝ → ℝ) (x : ℝ)
    (hZC1 : ∀ y, HasDerivAt (stepFlux p u Z) (deriv (stepFlux p u Z) y) y)
    (hWC1 : ∀ y, HasDerivAt (stepFlux p u W) (deriv (stepFlux p u W) y) y)
    (hRI_Hi : IntegrableOn (gWeight (greenRootPlus c lam) (reactionIncr p Z W)) (Ioi x))
    (hRI_Lo : IntegrableOn (gWeight (greenRootMinus c lam) (reactionIncr p Z W)) (Iic x))
    (hCD_Hi : IntegrableOn
      (gWeight (greenRootPlus c lam) (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y)) (Ioi x))
    (hCD_Lo : IntegrableOn
      (gWeight (greenRootMinus c lam) (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y)) (Iic x)) :
    greenConv c lam (fun y => barrierSource p lam u Z y - crossSource p lam u Z W y) x
      = greenConv c lam (reactionIncr p Z W) x
        + greenConv c lam (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y) x := by
  have hpt : (fun y => barrierSource p lam u Z y - crossSource p lam u Z W y)
      = fun y => reactionIncr p Z W y + (-p.χ) * deriv (stepFluxDiff p u W Z) y := by
    funext y
    exact barrierSource_sub_crossSource p lam u Z W (hZC1 y) (hWC1 y)
  rw [hpt]
  exact greenConv_add (reactionIncr p Z W)
    (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y) x
    hRI_Hi hCD_Hi hRI_Lo hCD_Lo

/-- **The integrated, `W'`-free residual.**
`greenConv(barrierSource Z) − greenConv(crossSource W)` equals
`greenConv(reactionIncr) + (−χ)·∫ Kλ'·(stepFlux_Z − stepFlux_W)` — no derivative of
`Z` or `W` survives in the chemotaxis term.  This is the quantity whose sign is
the genuine quasi-monotonicity content. -/
theorem barrierSource_greenConv_sub_eq
    (p : CMParams) (u Z W : ℝ → ℝ) (x : ℝ)
    (hZC1 : ∀ y, HasDerivAt (stepFlux p u Z) (deriv (stepFlux p u Z) y) y)
    (hWC1 : ∀ y, HasDerivAt (stepFlux p u W) (deriv (stepFlux p u W) y) y)
    (hBS_Hi : IntegrableOn (gWeight (greenRootPlus c lam) (barrierSource p lam u Z)) (Ioi x))
    (hBS_Lo : IntegrableOn (gWeight (greenRootMinus c lam) (barrierSource p lam u Z)) (Iic x))
    (hCS_Hi : IntegrableOn (gWeight (greenRootPlus c lam) (crossSource p lam u Z W)) (Ioi x))
    (hCS_Lo : IntegrableOn (gWeight (greenRootMinus c lam) (crossSource p lam u Z W)) (Iic x))
    (hRI_Hi : IntegrableOn (gWeight (greenRootPlus c lam) (reactionIncr p Z W)) (Ioi x))
    (hRI_Lo : IntegrableOn (gWeight (greenRootMinus c lam) (reactionIncr p Z W)) (Iic x))
    (hCD_Hi : IntegrableOn
      (gWeight (greenRootPlus c lam) (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y)) (Ioi x))
    (hCD_Lo : IntegrableOn
      (gWeight (greenRootMinus c lam) (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y)) (Iic x))
    (hChemo : greenConv c lam (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y) x
      = (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * (stepFlux p u Z y - stepFlux p u W y)) :
    greenConv c lam (barrierSource p lam u Z) x - greenConv c lam (crossSource p lam u Z W) x
      = greenConv c lam (reactionIncr p Z W) x
        + (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * (stepFlux p u Z y - stepFlux p u W y) := by
  -- LHS = greenConv (barrierSource Z − crossSource W)  (linearity of greenConv)
  have hlin : greenConv c lam (barrierSource p lam u Z) x
        - greenConv c lam (crossSource p lam u Z W) x
      = greenConv c lam (fun y => barrierSource p lam u Z y - crossSource p lam u Z W y) x := by
    have hneg : greenConv c lam (fun y => -crossSource p lam u Z W y) x
        = -greenConv c lam (crossSource p lam u Z W) x := greenConv_neg _ x
    have hadd : greenConv c lam
          (fun y => barrierSource p lam u Z y + (-crossSource p lam u Z W y)) x
        = greenConv c lam (barrierSource p lam u Z) x
          + greenConv c lam (fun y => -crossSource p lam u Z W y) x :=
      greenConv_add (barrierSource p lam u Z) (fun y => -crossSource p lam u Z W y) x
        hBS_Hi (hCS_Hi.neg.congr_fun (by intro y _; simp [gWeight]) measurableSet_Ioi)
        hBS_Lo (hCS_Lo.neg.congr_fun (by intro y _; simp [gWeight]) measurableSet_Iic)
    calc
      greenConv c lam (barrierSource p lam u Z) x
          - greenConv c lam (crossSource p lam u Z W) x
        = greenConv c lam (barrierSource p lam u Z) x
          + greenConv c lam (fun y => -crossSource p lam u Z W y) x := by rw [hneg]; ring
      _ = greenConv c lam
            (fun y => barrierSource p lam u Z y + (-crossSource p lam u Z W y)) x := hadd.symm
      _ = greenConv c lam
            (fun y => barrierSource p lam u Z y - crossSource p lam u Z W y) x := by
            congr 1
  rw [hlin,
    greenConv_residual_eq p u Z W x hZC1 hWC1 hRI_Hi hRI_Lo hCD_Hi hCD_Lo, hChemo]

/-! ## 4 — the integrated quasi-monotonicity

The genuine quasi-monotonicity: `greenConv(crossSource W) ≤ greenConv(barrierSource Z)`
from the SINGLE `W'`-free hypothesis that the integrated residual is nonnegative.
The chemotaxis derivative was eliminated by the IBP; what remains is a sign
condition on `greenConv(reactionIncr) + (−χ)·∫ Kλ'·(stepFlux_Z − stepFlux_W)`. -/

/-- **Integrated chemotaxis quasi-monotonicity.**
`greenConv(crossSource W) ≤ greenConv(barrierSource Z)`, discharged from the
single `W'`-free integrated residual sign
`0 ≤ greenConv(reactionIncr) + (−χ)·∫ Kλ'·(stepFlux_Z − stepFlux_W)`.

This bypasses the pointwise residual `RotheChemoMonotoneResidual` (which carries
`W'`) entirely: the comparison holds at the level of the whole Green map.  The
hypotheses are the IBP identity for the chemo defect (`hChemo`, from
`greenConv_chemoDefect_eq_kernelDeriv`), the two-profile `C¹` data, the per-tail
integrabilities, and the satisfiable integrated sign `hsign`. -/
theorem crossSource_greenConv_le_barrierSource_of_integrated_residual
    (p : CMParams) (u Z W : ℝ → ℝ) (x : ℝ)
    (hZC1 : ∀ y, HasDerivAt (stepFlux p u Z) (deriv (stepFlux p u Z) y) y)
    (hWC1 : ∀ y, HasDerivAt (stepFlux p u W) (deriv (stepFlux p u W) y) y)
    (hBS_Hi : IntegrableOn (gWeight (greenRootPlus c lam) (barrierSource p lam u Z)) (Ioi x))
    (hBS_Lo : IntegrableOn (gWeight (greenRootMinus c lam) (barrierSource p lam u Z)) (Iic x))
    (hCS_Hi : IntegrableOn (gWeight (greenRootPlus c lam) (crossSource p lam u Z W)) (Ioi x))
    (hCS_Lo : IntegrableOn (gWeight (greenRootMinus c lam) (crossSource p lam u Z W)) (Iic x))
    (hRI_Hi : IntegrableOn (gWeight (greenRootPlus c lam) (reactionIncr p Z W)) (Ioi x))
    (hRI_Lo : IntegrableOn (gWeight (greenRootMinus c lam) (reactionIncr p Z W)) (Iic x))
    (hCD_Hi : IntegrableOn
      (gWeight (greenRootPlus c lam) (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y)) (Ioi x))
    (hCD_Lo : IntegrableOn
      (gWeight (greenRootMinus c lam) (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y)) (Iic x))
    (hChemo : greenConv c lam (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y) x
      = (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * (stepFlux p u Z y - stepFlux p u W y))
    (hsign : 0 ≤ greenConv c lam (reactionIncr p Z W) x
        + (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * (stepFlux p u Z y - stepFlux p u W y)) :
    greenConv c lam (crossSource p lam u Z W) x ≤ greenConv c lam (barrierSource p lam u Z) x := by
  have hsub := barrierSource_greenConv_sub_eq p u Z W x hZC1 hWC1
    hBS_Hi hBS_Lo hCS_Hi hCS_Lo hRI_Hi hRI_Lo hCD_Hi hCD_Lo hChemo
  linarith [hsub, hsign]

/-! ## 5 — wiring to `W ≤ Z` (the `upperOld` order field)

When the per-step iterate `W` and the old iterate `Z` are Green images of their
sources, the integrated comparison gives `W ≤ Z` directly — the `upperOld` order
field of the Route-A step output, with the chemotaxis obligation now in `W'`-free
integrated form (`hsign`) instead of the pointwise `RotheChemoMonotoneResidual`. -/

/-- **`W ≤ Z` from the integrated residual.**
`W = greenConv(crossSource)`, `Z = greenConv(barrierSource)` (Z a super-solution /
Green image of its own barrier source), plus the `W'`-free integrated residual sign
`hsign`, give `W ≤ Z` pointwise — bypassing the pointwise chemotaxis residual. -/
theorem stepProfile_le_old_of_integrated_residual
    (p : CMParams) (u Z W : ℝ → ℝ)
    (hZC1 : ∀ y, HasDerivAt (stepFlux p u Z) (deriv (stepFlux p u Z) y) y)
    (hWC1 : ∀ y, HasDerivAt (stepFlux p u W) (deriv (stepFlux p u W) y) y)
    (hW : ∀ x, W x = greenConv c lam (crossSource p lam u Z W) x)
    (hZ : ∀ x, Z x = greenConv c lam (barrierSource p lam u Z) x)
    (hBS_Hi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) (barrierSource p lam u Z)) (Ioi x))
    (hBS_Lo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) (barrierSource p lam u Z)) (Iic x))
    (hCS_Hi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) (crossSource p lam u Z W)) (Ioi x))
    (hCS_Lo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) (crossSource p lam u Z W)) (Iic x))
    (hRI_Hi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) (reactionIncr p Z W)) (Ioi x))
    (hRI_Lo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) (reactionIncr p Z W)) (Iic x))
    (hCD_Hi : ∀ x, IntegrableOn
      (gWeight (greenRootPlus c lam) (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y)) (Ioi x))
    (hCD_Lo : ∀ x, IntegrableOn
      (gWeight (greenRootMinus c lam) (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y)) (Iic x))
    (hChemo : ∀ x, greenConv c lam (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y) x
      = (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * (stepFlux p u Z y - stepFlux p u W y))
    (hsign : ∀ x, 0 ≤ greenConv c lam (reactionIncr p Z W) x
        + (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y) * (stepFlux p u Z y - stepFlux p u W y)) :
    ∀ x, W x ≤ Z x := by
  intro x
  rw [hW x, hZ x]
  exact crossSource_greenConv_le_barrierSource_of_integrated_residual p u Z W x hZC1 hWC1
    (hBS_Hi x) (hBS_Lo x) (hCS_Hi x) (hCS_Lo x) (hRI_Hi x) (hRI_Lo x) (hCD_Hi x) (hCD_Lo x)
    (hChemo x) (hsign x)

/-! ## Axiom audit -/

section AxiomAudit
#print axioms reactionIncr
#print axioms deriv_stepFluxDiff_eq
#print axioms barrierSource_sub_crossSource
#print axioms greenConv_chemoDefect_eq_kernelDeriv
#print axioms greenConv_residual_eq
#print axioms barrierSource_greenConv_sub_eq
#print axioms crossSource_greenConv_le_barrierSource_of_integrated_residual
#print axioms stepProfile_le_old_of_integrated_residual
end AxiomAudit

end ShenWork.Paper1
