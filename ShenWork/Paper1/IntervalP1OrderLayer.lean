/-
  ShenWork/Paper1/IntervalP1OrderLayer.lean

  Foundational ORDER-layer bricks for the Chen-Ruan-Shen Paper-1 per-step
  parabolic solver, built on the already-committed Green-kernel positivity
  (`greenKernel_pos`) and Green monotonicity (`greenConv_mono`,
  `WaveAuxInvariance.lean`).

  CONTEXT.  The per-step iterate is `W = greenConv c lam R`, the
  variation-of-parameters solution of `W'' + cW' − λW = −R` (kernel `Kλ ≥ 0`,
  hence `greenConv` order-preserving in the source `R`).  The Route-A
  `PaperStepOutput` order layer (`PaperGreenStepInputRouteASuperRestProvider`)
  requires, for each trapped supersolution iterate `Z`, the barrier comparisons
  `W ≤ Z`, `W ≤ upperBarrier κ M`, and `0 ≤ W`.

  These are ALL consequences of Green monotonicity once the corresponding SOURCE
  ordering is in hand:
    * `0 ≤ W`            ⇐ `0 ≤ R`        (compare against the zero source);
    * `W ≤ B`            ⇐ `R ≤ R_B` and `greenConv R_B ≤ B`
                           (a Green-majorant for the comparison barrier `B`).

  This file lands the clean, non-circular, axiom-clean packaging that converts
  the order layer into explicit named SOURCE-ordering / Green-majorant
  obligations, so no future comparison proof re-mixes Green monotonicity,
  barrier comparison, and the chemotaxis quasi-monotonicity residual in one
  monolith.

  WHAT IS CLOSED HERE (axiom-clean, `greenConv_mono`-backed):
    * `greenConv_zero` — `greenConv c lam 0 = 0` (the zero source maps to `0`);
    * `greenConv_le_majorant_of_source_le` — the master comparison wrapper:
      `W = greenConv R_W`, `R_W ≤ R_B`, `greenConv R_B ≤ B` ⟹ `W ≤ B`;
    * `greenConv_le_of_source_le` — exact-barrier corollary (`B = greenConv R_B`);
    * `greenConv_nonneg_of_source_nonneg` — `0 ≤ R_W` ⟹ `0 ≤ W`.

  WHAT IS NOT CLOSED HERE (isolated above, honest accounting).  The brick does
  NOT discharge the source-ordering inputs `R_W ≤ R_B` (this is exactly the
  `RotheChemoMonotoneResidual` chemotaxis quasi-monotonicity, whose committed
  reduction is the flux-difference IBP `stepFlux_diff_ibp` + `greenConv_mono`,
  see the STALL NOTE in `WaveRotheOrder.lean`), nor the barrier-majorant
  `greenConv R_B ≤ B` for a non-Green supersolution barrier (a maximum-principle
  fact).  It packages them as the two clean obligations every comparison splits
  into, and discharges the lower bound `0 ≤ W` outright from `0 ≤ R_W`.
-/
import ShenWork.Paper1.WaveRotheOrder

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## The zero source maps to the zero profile -/

/-- The `gWeight` of the zero source is the zero function. -/
theorem gWeight_zero (r : ℝ) :
    gWeight r (fun _ : ℝ => 0) = fun _ : ℝ => 0 := by
  funext y
  simp [gWeight]

/-- The upper tail of the zero source vanishes. -/
@[simp] theorem tailHi_zero (r x : ℝ) :
    tailHi r (fun _ : ℝ => 0) x = 0 := by
  simp [tailHi, gWeight_zero]

/-- The lower tail of the zero source vanishes. -/
@[simp] theorem tailLo_zero (r x : ℝ) :
    tailLo r (fun _ : ℝ => 0) x = 0 := by
  simp [tailLo, gWeight_zero]

/-- **`greenConv` of the zero source is `0`.**  Both split tails of the zero
integrand vanish, so the variation-of-parameters profile is identically `0`. -/
@[simp] theorem greenConv_zero (c lam x : ℝ) :
    greenConv c lam (fun _ : ℝ => 0) x = 0 := by
  simp [greenConv]

/-- The zero source is integrable against either tail weight (the integrand is
identically `0`).  Stated per-tail to match `greenConv_mono`'s signature. -/
theorem gWeight_zero_integrableOn_Ioi (r x : ℝ) :
    IntegrableOn (gWeight r (fun _ : ℝ => 0)) (Ioi x) := by
  rw [gWeight_zero]; exact integrableOn_zero

theorem gWeight_zero_integrableOn_Iic (r x : ℝ) :
    IntegrableOn (gWeight r (fun _ : ℝ => 0)) (Iic x) := by
  rw [gWeight_zero]; exact integrableOn_zero

/-! ## The master comparison wrapper

`greenConv` is order-preserving in its source (`greenConv_mono`).  Composing the
source-ordering `R_W ≤ R_B` with a Green-majorant `greenConv R_B ≤ B` gives the
profile comparison `W ≤ B`, isolating the two genuine obligations. -/

/-- **Master Green-order comparison.**

If `W` is the Green convolution of `R_W`, the source `R_W` is pointwise below a
comparison source `R_B`, and the Green convolution of `R_B` is pointwise below a
barrier `B`, then `W ≤ B` pointwise.

The hard analytic content is isolated into the two clean obligations:
* the SOURCE ordering `R_W ≤ R_B` (the chemotaxis quasi-monotonicity residual),
* the Green-majorant `greenConv R_B ≤ B` (a max-principle fact, equality when
  `B` is itself a Green convolution).

Integrability is taken per-`x` in the exact `greenConv_mono` shape. -/
theorem greenConv_le_majorant_of_source_le
    (hlam : 0 < lam) {R_W R_B W B : ℝ → ℝ}
    (hRW_Hi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) R_W) (Ioi x))
    (hRB_Hi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) R_B) (Ioi x))
    (hRW_Lo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) R_W) (Iic x))
    (hRB_Lo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) R_B) (Iic x))
    (hW : ∀ x, W x = greenConv c lam R_W x)
    (hsrc : ∀ y, R_W y ≤ R_B y)
    (hBmaj : ∀ x, greenConv c lam R_B x ≤ B x) :
    ∀ x, W x ≤ B x := by
  intro x
  calc
    W x = greenConv c lam R_W x := hW x
    _ ≤ greenConv c lam R_B x :=
      greenConv_mono (c := c) hlam hsrc (hRW_Hi x) (hRB_Hi x) (hRW_Lo x) (hRB_Lo x)
    _ ≤ B x := hBmaj x

/-- **Exact-barrier corollary.**  When the comparison barrier `B` is itself the
Green convolution of `R_B`, the Green-majorant is an equality, so source
ordering transfers directly to profile ordering. -/
theorem greenConv_le_of_source_le
    (hlam : 0 < lam) {R_W R_B W B : ℝ → ℝ}
    (hRW_Hi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) R_W) (Ioi x))
    (hRB_Hi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) R_B) (Ioi x))
    (hRW_Lo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) R_W) (Iic x))
    (hRB_Lo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) R_B) (Iic x))
    (hW : ∀ x, W x = greenConv c lam R_W x)
    (hB : ∀ x, B x = greenConv c lam R_B x)
    (hsrc : ∀ y, R_W y ≤ R_B y) :
    ∀ x, W x ≤ B x :=
  greenConv_le_majorant_of_source_le (c := c) hlam
    hRW_Hi hRB_Hi hRW_Lo hRB_Lo hW hsrc
    (fun x => le_of_eq (hB x).symm)

/-! ## The lower bound `0 ≤ W` from a nonnegative source

This one discharges OUTRIGHT (no carried obligation beyond `0 ≤ R_W`): compare
the source `R_W` against the zero source, whose Green image is `0`. -/

/-- **`0 ≤ W` from `0 ≤ R_W`.**  The Green image of a nonnegative source is
nonnegative, by monotone comparison against the zero source (`greenConv 0 = 0`).
Integrability of the zero source is supplied internally. -/
theorem greenConv_nonneg_of_source_nonneg
    (hlam : 0 < lam) {R W : ℝ → ℝ}
    (hR_Hi : ∀ x, IntegrableOn (gWeight (greenRootPlus c lam) R) (Ioi x))
    (hR_Lo : ∀ x, IntegrableOn (gWeight (greenRootMinus c lam) R) (Iic x))
    (hW : ∀ x, W x = greenConv c lam R x)
    (hR_nonneg : ∀ y, 0 ≤ R y) :
    ∀ x, 0 ≤ W x := by
  intro x
  have hmono :
      greenConv c lam (fun _ : ℝ => 0) x ≤ greenConv c lam R x :=
    greenConv_mono (c := c) hlam hR_nonneg
      (gWeight_zero_integrableOn_Ioi (greenRootPlus c lam) x) (hR_Hi x)
      (gWeight_zero_integrableOn_Iic (greenRootMinus c lam) x) (hR_Lo x)
  rw [hW x]
  calc
    (0 : ℝ) = greenConv c lam (fun _ : ℝ => 0) x := (greenConv_zero c lam x).symm
    _ ≤ greenConv c lam R x := hmono

/-! ## Convenience: the three order goals as named obligations

The Route-A order layer needs `W ≤ Z`, `W ≤ upperBarrier κ M`, and `0 ≤ W` for
the per-step iterate `W = greenConv c lam (crossSource p lam u Z W)`.  The two
upper comparisons are instances of `greenConv_le_majorant_of_source_le`; the
lower one is `greenConv_nonneg_of_source_nonneg`.  We record the upper one
specialised to `B = Z` (`R_B = barrierSource p lam u Z`) so callers supply only
the chemotaxis source ordering and the barrier Green-majorant. -/

/-- **`W ≤ Z` from the cross/barrier source ordering and the `Z`-majorant.**

The per-step profile `W` (Green image of `crossSource`) lies below the old
iterate `Z`, provided the cross source is dominated by the barrier source of `Z`
(the chemotaxis quasi-monotonicity, `crossSource_le_barrierSource_pointwise`)
and `Z` Green-majorises its own barrier source.  This is the `upperOld` order
field of the Route-A step output, reduced to its two source-level obligations. -/
theorem stepProfile_le_old_of_source_le
    (hlam : 0 < lam) {p : CMParams} {u Z W : ℝ → ℝ}
    (hRW_Hi : ∀ x,
      IntegrableOn (gWeight (greenRootPlus c lam) (crossSource p lam u Z W)) (Ioi x))
    (hRB_Hi : ∀ x,
      IntegrableOn (gWeight (greenRootPlus c lam) (barrierSource p lam u Z)) (Ioi x))
    (hRW_Lo : ∀ x,
      IntegrableOn (gWeight (greenRootMinus c lam) (crossSource p lam u Z W)) (Iic x))
    (hRB_Lo : ∀ x,
      IntegrableOn (gWeight (greenRootMinus c lam) (barrierSource p lam u Z)) (Iic x))
    (hW : ∀ x, W x = greenConv c lam (crossSource p lam u Z W) x)
    (hsrc : ∀ y, crossSource p lam u Z W y ≤ barrierSource p lam u Z y)
    (hZmaj : ∀ x, greenConv c lam (barrierSource p lam u Z) x ≤ Z x) :
    ∀ x, W x ≤ Z x :=
  greenConv_le_majorant_of_source_le (c := c) hlam
    hRW_Hi hRB_Hi hRW_Lo hRB_Lo hW hsrc hZmaj

section AxiomAudit
#print axioms greenConv_zero
#print axioms greenConv_le_majorant_of_source_le
#print axioms greenConv_le_of_source_le
#print axioms greenConv_nonneg_of_source_nonneg
#print axioms stepProfile_le_old_of_source_le
end AxiomAudit

end ShenWork.Paper1
