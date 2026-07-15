import ShenWork.Paper1.Theorem12LogisticFiniteness

/-!
# Solution right-tail decay: barrier rate arithmetic + the isolated comparison residual

The finiteness step D needs `IntegrableOn (fun z => |u(t,·) − U|²) (Ioi a)`, and the committed bridge
`rightTailL2_of_exp_decay` reduces that to a POINTWISE solution decay `|u(t,z) − U z| ≤ C e^{−κ z}` (z ≥ a).
This file proves the barrier-rate arithmetic (the choice of `κ` making `ψ = C e^{−κ z}` a right-tail
supersolution for speeds `c > 2`) and records, precisely, the one piece of machinery the repo still lacks.

## The transform structure (why `κ = c/2` works)
With `w = u · e^{κ z}`, the moving-frame operator `∂_zz + c ∂_z + (·)(1 − ·^α)` conjugates so that near `u = 0`
`w` solves `w_t = w_zz + (c − 2κ) w_z + (κ² − c κ + 1) w + (favorable χ≤0 chemotaxis)`. Choosing `κ = c/2`
makes the zeroth-order coefficient `κ² − c κ + 1 = 1 − c²/4 < 0` for `c > 2`, so dropping that negative term
gives a pure DRIFT subsolution `w_t ≤ w_zz + |c − 2κ| |w_z|` — exactly the hypothesis of the committed
`wholeLineSlabSup_le_of_drift_subsolution`.
-/

open MeasureTheory Set

namespace ShenWork.Paper1

/-- The barrier rate `κ = c/2` gives a strictly negative zeroth-order coefficient for supersonic speeds
`c > 2`: `(c/2)² − c·(c/2) + 1 = 1 − c²/4 < 0`.  This is what makes `C e^{−(c/2) z}` a right-tail
supersolution of the linearised (near `u = 0`) moving-frame equation, so that the `w = u·e^{κz}` transform
lands in the drift-subsolution class of `wholeLineSlabSup_le_of_drift_subsolution`. -/
theorem tailBarrier_coeff_neg {c : ℝ} (hc : 2 < c) :
    (c / 2) ^ 2 - c * (c / 2) + 1 < 0 := by
  nlinarith [mul_pos (show (0 : ℝ) < c - 2 by linarith)
    (show (0 : ℝ) < c + 2 by linarith)]

/-- The drift coefficient of the transformed variable `w = u·e^{κz}` at `κ = c/2` is `c − 2κ = 0`: the
transport term is fully absorbed by the exponential shift, leaving a driftless subsolution. -/
theorem tailBarrier_drift_zero (c : ℝ) : c - 2 * (c / 2) = 0 := by ring

/-! ## The isolated remaining crux

`rightTailL2_of_exp_decay` (committed, `19bea46e`) already gives:

    pointwise `|u(t,z) − U z| ≤ C e^{−κ z}` for `z ≥ a`   ⟹   `IntegrableOn |u−U|² (Ioi a)`.

So the ONLY missing input to close step D (and hence `paperWeightedCoreIntegrability` and the weighted-L²
`Theorem 1.2`) is the pointwise solution decay itself.  The route is settled (above): transform
`w = u·e^{c z/2}`, obtain a driftless subsolution using `tailBarrier_coeff_neg`/`tailBarrier_drift_zero`,
and compare against the initial ceiling.

The one obstruction is that `wholeLineSlabSup_le_of_drift_subsolution` requires a GLOBAL a-priori bound
`w ≤ A` (its `hupper`), whereas `w = u·e^{κz}` is unbounded as `z → +∞` unless `u` already decays — the very
conclusion.  The genuine fix is a HALF-LINE / TRUNCATED-BARRIER drift comparison on `[a, ∞)` (a lateral
boundary at `z = a`, or a `capWeight`-style truncated exponential passed to the limit), which the repository
does not yet provide (`wholeLineSlabSup_le_of_drift_subsolution` is whole-line, constant-ceiling only).

This is the single Fable-worthy machinery build remaining for the weighted-L² `Theorem 1.2`, and it is
the same decaying/half-line parabolic-comparison family that hcore's wall-1 (strict positivity) and
wall-4 (entire-orbit rigidity) also require.
-/

end ShenWork.Paper1
