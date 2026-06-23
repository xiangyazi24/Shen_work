/-
  ShenWork/Paper1/ChemoDefectDominatesImpl.lean

  Discharging `ChemoDefectDominates` (the carried χ ≤ 0 quasi-monotonicity that
  signs the chemotaxis defect of the implicit Rothe step, Chen–Ruan–Shen
  arXiv:2605.04401 §4.2) from the LANDED quasi-monotonicity machinery — the
  gradient-level (`w = uₓ`) sandwich plus the Green resolvent positivity, NOT the
  integrated `Kλ'` kernel (which, by the `ChemoReactionBalance` doctrine, is
  genuinely sign-indefinite even for χ ≤ 0).

  THE LANDED CHAIN (read top-down; everything here only RE-WIRES it):

  * `greenConv_chemoDefect_eq_kernelDeriv` (IBP, `IntervalP1ChemoMonotone`) gives
        chemoDefect := (−χ)·∫ Kλ'(x−y)·(stepFlux_Z − stepFlux_W) dy
                     = greenConv c λ (fun y => (−χ)·∂ₓ(stepFlux_Z − stepFlux_W) y) x,
    i.e. the integrated chemo defect is the Green image of the FOLDED flux
    difference divergence.  The IBP is what moves the derivative off the flux
    difference and onto the kernel — there is no `W'` on the right.

  * `greenConv_mono` (`WaveAuxInvariance`, the `Kλ ≥ 0` maximum principle) signs
    Green images from their SOURCES: `H₁ ≤ H₂` pointwise ⟹ greenConv H₁ ≤ greenConv H₂.

  Composing the two: `ChemoDefectDominates`, namely
        greenConv c λ (fun y => λ·(Z y − W y)) x  ≤  chemoDefect,
  is EXACTLY `greenConv (source_lo) ≤ greenConv (source_hi)` with
        source_lo y = λ·(Z y − W y),
        source_hi y = (−χ)·∂ₓ(stepFlux_Z − stepFlux_W) y,
  so by `greenConv_mono` it follows from the POINTWISE source ordering

        λ·(Z y − W y)  ≤  (−χ)·(∂ₓ stepFlux_Z y − ∂ₓ stepFlux_W y)     (∀ y).        (★)

  (★) is precisely the gradient-level chemotaxis quasi-monotonicity carried by the
  elliptic construction as `RotheChemoMonotoneResidual` (`WaveRotheOrder`) — the
  same content as the `ChemotaxisSandwich` barrier inequality `auxSource` carries,
  read on the DIFFERENCE.  It carries `∂ₓ(stepFlux Z − stepFlux W)` (the `W = uₓ`
  derivative the paper signs by the parabolic max principle); the IBP is what lets
  the elliptic order layer absorb that derivative at the level of the whole Green
  map instead of pointwise on the integrated `Kλ'` kernel.

  WHAT IS LANDED HERE (axiom-clean, `{propext, Classical.choice, Quot.sound}`):

  * `chemoDefectDominates_of_pointwise_residual` — `ChemoDefectDominates` from the
    SINGLE gradient-level pointwise residual (★) (plus the IBP identity and the
    per-tail integrabilities the landed `greenConv_mono` requires).  This is the
    genuine reduction: the integrated dominance is discharged from the elliptic
    sandwich's gradient-level sign, via `greenConv_chemoDefect_eq_kernelDeriv`
    (IBP) + `greenConv_mono` (resolvent positivity).

  * `chemoDefectDominates_of_rotheResidual` — the same, packaged to consume the
    landed `RotheChemoMonotoneResidual` structure directly (the named carried
    obligation of the order layer), exhibiting that the carried gradient-level
    sandwich IS the discharge.

  HONEST ACCOUNTING (the exact remaining gap).  `ChemoDefectDominates` is NOT
  discharged unconditionally.  The residual (★) is the paper's χ ≤ 0
  quasi-monotonicity, which the elliptic-Rothe route carries as a HYPOTHESIS: the
  paper signs `∂ₓ(stepFlux Z − stepFlux W)` by the PARABOLIC gradient (`w = uₓ`)
  maximum principle (eq. 4.13), an argument with no counterpart inside the
  elliptic frozen fixed-point construction.  So the elliptic construction carries
  the quasi-monotonicity as `RotheChemoMonotoneResidual` / `ChemotaxisSandwich`,
  and THIS file closes the precise remaining link `residual (★) ⟹ ChemoDefectDominates`
  via the landed `greenConv_mono` + IBP — turning the integrated, sign-indefinite
  `ChemoDefectDominates` into the gradient-level sandwich the construction already
  carries.  The bare integrated `ChemoDefectDominates` stays conditional on (★).

  No `sorry`/`axiom`/`native_decide`/`admit`.  New file only; touches nothing.
-/
import ShenWork.Paper1.ChemoReactionBalance
import ShenWork.Paper1.IntervalP1ChemoMonotone

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## 1 — `ChemoDefectDominates` from the gradient-level pointwise residual

The integrated dominance is `greenConv (λ(Z−W)) ≤ chemoDefect`.  Rewriting
`chemoDefect` as `greenConv ((−χ)·∂ₓ stepFluxDiff)` (the landed IBP identity
`greenConv_chemoDefect_eq_kernelDeriv`) turns it into a Green-image comparison
whose source ordering is exactly the gradient-level residual (★).  The landed
`greenConv_mono` (`Kλ ≥ 0` maximum principle) then closes it. -/

/-- **`ChemoDefectDominates` from the gradient-level residual.**

Given the landed IBP identity `hChemo` (`greenConv_chemoDefect_eq_kernelDeriv`,
which expresses the integrated chemo defect as the Green image of the folded flux
difference) and the pointwise gradient-level quasi-monotonicity residual, in the folded form
`greenConv_mono` consumes,

    `λ·(Z y − W y) ≤ (−χ)·∂ₓ(stepFlux_Z − stepFlux_W) y`     (∀ y),

the carried scalar condition `ChemoDefectDominates` holds.  Proof: rewrite the
chemo defect by the IBP, then apply `greenConv_mono` to the two sources, whose
pointwise ordering is exactly `hres`.  The
per-`x` per-tail integrabilities are the standard `greenConv_mono` data of the
two sources (satisfiable on the trap, NOT the conclusion). -/
theorem chemoDefectDominates_of_pointwise_residual
    (hlam : 0 < lam) (p : CMParams) (u Z W : ℝ → ℝ) (x : ℝ)
    (hChemo : greenConv c lam (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y) x
      = (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y)
          * (stepFlux p u Z y - stepFlux p u W y))
    (hLamHi : IntegrableOn (gWeight (greenRootPlus c lam) (fun y => lam * (Z y - W y))) (Ioi x))
    (hLamLo : IntegrableOn (gWeight (greenRootMinus c lam) (fun y => lam * (Z y - W y))) (Iic x))
    (hCDHi : IntegrableOn
      (gWeight (greenRootPlus c lam) (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y)) (Ioi x))
    (hCDLo : IntegrableOn
      (gWeight (greenRootMinus c lam) (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y)) (Iic x))
    (hres : ∀ y, lam * (Z y - W y)
      ≤ (-p.χ) * deriv (stepFluxDiff p u W Z) y) :
    ChemoDefectDominates c lam p u Z W x := by
  -- Green monotonicity: greenConv (λ(Z−W)) ≤ greenConv ((−χ)·∂ₓ stepFluxDiff).
  have hmono := greenConv_mono (c := c) hlam hres hLamHi hCDHi hLamLo hCDLo
  -- Rewrite the RHS via the IBP identity.
  unfold ChemoDefectDominates
  rw [← hChemo]
  exact hmono

/-! ## 2 — packaged for the landed `RotheChemoMonotoneResidual`

The pointwise residual (★) is precisely the order layer's carried obligation
`RotheChemoMonotoneResidual` (with barrier `B = Z`, and `Z` the supersolution):
its field is `0 ≤ λ·(W−Z) − χ·(∂ₓ stepFlux_Z − ∂ₓ stepFlux_W)`, i.e.
`λ·(Z−W) ≤ (−χ)·(∂ₓ stepFlux_Z − ∂ₓ stepFlux_W)`.  We package the reduction to
consume that structure directly, exhibiting that the elliptic construction's
carried gradient-level sandwich discharges the integrated `ChemoDefectDominates`. -/

/-- The `RotheChemoMonotoneResidual` field, read on `(B := Z)`, folded to the
`greenConv_mono` source form `λ(Z−W) ≤ (−χ)·∂ₓ stepFluxDiff`.  The split
`∂ₓ stepFluxDiff = ∂ₓ stepFlux_Z − ∂ₓ stepFlux_W` uses the carried two-profile
`C¹` data via the landed `deriv_stepFluxDiff_eq`; the residual sign then
rearranges by `nlinarith`. -/
theorem residual_of_rotheResidual
    (p : CMParams) (u Z W : ℝ → ℝ)
    (hZC1 : ∀ y, HasDerivAt (stepFlux p u Z) (deriv (stepFlux p u Z) y) y)
    (hWC1 : ∀ y, HasDerivAt (stepFlux p u W) (deriv (stepFlux p u W) y) y)
    (hres : RotheChemoMonotoneResidual p lam u Z W Z) (y : ℝ) :
    lam * (Z y - W y) ≤ (-p.χ) * deriv (stepFluxDiff p u W Z) y := by
  have hd : deriv (stepFluxDiff p u W Z) y
      = deriv (stepFlux p u Z) y - deriv (stepFlux p u W) y :=
    deriv_stepFluxDiff_eq p u W Z (hZC1 y) (hWC1 y)
  have h := hres.residual_nonneg y
  -- h : 0 ≤ λ·(W−Z) − χ·(∂ stepFlux_Z − ∂ stepFlux_W)
  rw [hd]; nlinarith [h]

/-- **`ChemoDefectDominates` from the landed `RotheChemoMonotoneResidual`.**

The elliptic order layer carries the gradient-level chemotaxis quasi-monotonicity
as `RotheChemoMonotoneResidual p λ u Z W Z` (barrier `B = Z`).  Together with the
landed IBP identity and the per-tail integrabilities, it discharges the integrated
`ChemoDefectDominates` via `greenConv_mono`.  This is the precise statement that
the construction's carried sandwich IS the discharge of the integrated dominance —
no separate integrated-kernel sign argument is needed. -/
theorem chemoDefectDominates_of_rotheResidual
    (hlam : 0 < lam) (p : CMParams) (u Z W : ℝ → ℝ) (x : ℝ)
    (hChemo : greenConv c lam (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y) x
      = (-p.χ) * ∫ y, greenKernelDeriv c lam (x - y)
          * (stepFlux p u Z y - stepFlux p u W y))
    (hLamHi : IntegrableOn (gWeight (greenRootPlus c lam) (fun y => lam * (Z y - W y))) (Ioi x))
    (hLamLo : IntegrableOn (gWeight (greenRootMinus c lam) (fun y => lam * (Z y - W y))) (Iic x))
    (hCDHi : IntegrableOn
      (gWeight (greenRootPlus c lam) (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y)) (Ioi x))
    (hCDLo : IntegrableOn
      (gWeight (greenRootMinus c lam) (fun y => (-p.χ) * deriv (stepFluxDiff p u W Z) y)) (Iic x))
    (hZC1 : ∀ y, HasDerivAt (stepFlux p u Z) (deriv (stepFlux p u Z) y) y)
    (hWC1 : ∀ y, HasDerivAt (stepFlux p u W) (deriv (stepFlux p u W) y) y)
    (hres : RotheChemoMonotoneResidual p lam u Z W Z) :
    ChemoDefectDominates c lam p u Z W x :=
  chemoDefectDominates_of_pointwise_residual hlam p u Z W x hChemo
    hLamHi hLamLo hCDHi hCDLo (residual_of_rotheResidual p u Z W hZC1 hWC1 hres)

/-! ## Axiom audit -/

section AxiomAudit
#print axioms chemoDefectDominates_of_pointwise_residual
#print axioms residual_of_rotheResidual
#print axioms chemoDefectDominates_of_rotheResidual
end AxiomAudit

end ShenWork.Paper1
