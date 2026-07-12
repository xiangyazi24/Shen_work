import ShenWork.PDE.CosineSpectrum
import ShenWork.PDE.IntervalNeumannFullKernel
import ShenWork.Paper2.IntervalParabolicDuhamelGains
import ShenWork.Paper2.IntervalSourceRepresentative
import ShenWork.Paper2.IntervalEvenDerivParity

/-!
# Global doubly-even C³ representative of the coupled solution slice (u-analogue of R)

The chemotaxis-divergence source's weak-`H²_N` witness needs, on the `u` factor, the
same thing `intervalResolverLiftR` supplies for the resolver `R`: a **global,
doubly-even, C³** function agreeing with the solution slice on `[0,1]`.

`intervalResolverLiftR` is NOT a reflection construction — it is the **cosine series**
`∑ coeff·cosineMode`, which is doubly-even automatically (`cos` is even and 2-periodic)
and `C⁴` from eigenvalue-weighted coefficient summability.  This file extracts that
mechanism as a REUSABLE generic `cosineSeriesLift` and instantiates it for the solution
slice `u s` via its cosine coefficients — mirroring the resolver template exactly.

* doubly-even: FREE (`cosineSeriesLift_doublyEven`) — porting the resolver's parity.
* `C³`: from a carried eigenvalue-square-summability hypothesis on the coefficients
  (`cosineSeriesLift_contDiff_three`) — this is the `u ∈ H³`-type regularity input.
* agreement on `[0,1]`: cosine reconstruction `∑ cosineCoeffs(f)·cosineMode = f`, carried
  as a named hypothesis (Fourier completeness of the Neumann cosine basis on `[0,1]`).
-/

namespace ShenWork.PDE.IntervalSolutionEvenRepresentative

open ShenWork.CosineSpectrum
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalDomain
open ShenWork.Paper2.ParabolicDuhamelGains
open ShenWork.Paper2.SourceRepresentative

/-- `cosineMode` is even about `0`. -/
theorem cosineMode_evenAboutZero (n : ℕ) (x : ℝ) :
    cosineMode n (-x) = cosineMode n x := by
  unfold cosineMode
  rw [show (n : ℝ) * Real.pi * (-x) = -((n : ℝ) * Real.pi * x) from by ring, Real.cos_neg]

/-- `cosineMode` is even about `1`: `cos(nπ(2−x)) = cos(nπx)` (period-2 + evenness). -/
theorem cosineMode_evenAboutOne (n : ℕ) (x : ℝ) :
    cosineMode n (2 - x) = cosineMode n x := by
  unfold cosineMode
  rw [show (n : ℝ) * Real.pi * (2 - x)
        = -((n : ℝ) * Real.pi * x) + ((n : ℤ) : ℝ) * (2 * Real.pi) from by push_cast; ring,
    Real.cos_add_int_mul_two_pi, Real.cos_neg]

/-- Generic **cosine-series lift** of a coefficient sequence — the mechanism behind
`intervalResolverLiftR`.  Doubly-even automatically; C³ from summability. -/
noncomputable def cosineSeriesLift (b : ℕ → ℝ) : ℝ → ℝ :=
  fun x => ∑' n : ℕ, b n * cosineMode n x

/-- The cosine-series lift is even about `0`. -/
theorem cosineSeriesLift_evenAboutZero (b : ℕ → ℝ) : EvenAboutZero (cosineSeriesLift b) := by
  intro x
  refine tsum_congr (fun n => ?_)
  rw [cosineMode_evenAboutZero]

/-- The cosine-series lift is even about `1`. -/
theorem cosineSeriesLift_evenAboutOne (b : ℕ → ℝ) : EvenAboutOne (cosineSeriesLift b) := by
  intro x
  refine tsum_congr (fun n => ?_)
  rw [cosineMode_evenAboutOne]

/-- **The cosine-series lift is doubly-even** (both Neumann endpoints) — free. -/
theorem cosineSeriesLift_doublyEven (b : ℕ → ℝ) : DoublyEven (cosineSeriesLift b) :=
  ⟨cosineSeriesLift_evenAboutZero b, cosineSeriesLift_evenAboutOne b⟩

/-- **The cosine-series lift is `C³`** from eigenvalue-square coefficient summability
(the `H³`-type regularity input). -/
theorem cosineSeriesLift_contDiff_three {b : ℕ → ℝ}
    (hb : Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n * (unitIntervalCosineEigenvalue n * |b n|))) :
    ContDiff ℝ 3 (cosineSeriesLift b) := by
  unfold cosineSeriesLift
  exact (cosineCoeffSeries_contDiff_four_of_eigenvalue_sq_summable hb).of_le (by norm_num)

/-- **The `u`-analogue of `intervalResolverLiftR`**: the global doubly-even cosine-series
representative of the solution slice `u s`, from its cosine coefficients. -/
noncomputable def intervalSolutionLiftU
    (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) : ℝ → ℝ :=
  cosineSeriesLift (cosineCoeffs (intervalDomainLift (u s)))

/-- `intervalSolutionLiftU` is doubly-even — free from the cosine basis. -/
theorem intervalSolutionLiftU_doublyEven
    (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) :
    DoublyEven (intervalSolutionLiftU u s) :=
  cosineSeriesLift_doublyEven _

/-- `intervalSolutionLiftU` is `C³` from the solution's eigenvalue-square coefficient
summability (the `u ∈ H³` regularity input on positive time). -/
theorem intervalSolutionLiftU_contDiff_three
    {u : ℝ → intervalDomainPoint → ℝ} {s : ℝ}
    (hb : Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          |cosineCoeffs (intervalDomainLift (u s)) n|))) :
    ContDiff ℝ 3 (intervalSolutionLiftU u s) :=
  cosineSeriesLift_contDiff_three hb

end ShenWork.PDE.IntervalSolutionEvenRepresentative
