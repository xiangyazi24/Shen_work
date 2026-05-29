/-
  ShenWork/PDE/IntervalParamDerivMeasurable.lean

  Joint measurability of a PARAMETRIZED spatial derivative from joint
  measurability of the function alone.

  ## The problem this file solves

  Mathlib's `measurable_deriv_with_param` requires GLOBAL joint continuity
  `Continuous f.uncurry` of the parametrized family.  For the interval-domain
  PDE work the relevant family is the zero-extended lift
  `(s, y) ↦ intervalDomainLift (u s) y`, which is only JOINTLY MEASURABLE
  (proved elsewhere) and is genuinely DISCONTINUOUS across the spatial
  endpoints `y ∈ {0,1}` (the zero extension jumps there).  So
  `measurable_deriv_with_param` does not apply.

  ## The surrogate

  We instead build a GLOBALLY MEASURABLE surrogate from joint measurability
  alone, using the sequential difference quotient

      `diffQuotLimsup g (s,y) := limsup_{n} (n+1) · (g (s, y + 1/(n+1)) − g (s,y))`.

  * It is measurable whenever `g` is measurable (`Measurable.limsup`).
  * At any point where `y' ↦ g (s, y')` has a derivative `d`, it EQUALS `d`
    (`HasDerivAt.tendsto_slope` along the sequence `y + 1/(n+1) → y` within
    `{≠ y}`, then `Tendsto.limsup_eq`).

  So the surrogate is a single globally-measurable function that agrees with
  the parametrized derivative field wherever the latter exists.  This is
  exactly what an a.e.-measurability argument needs: the spatial-endpoint
  jump set `{y ∈ {0,1}}` is Lebesgue-null and can be discarded.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.LiminfLimsup

open Filter MeasureTheory
open scoped Topology

namespace ShenWork.ParamDeriv

/-- Sequential difference-quotient `limsup` surrogate for the spatial
derivative of `y ↦ g (s, y)`:

    `diffQuotLimsup g (s,y) = limsup_{n} (n+1) · (g (s, y + 1/(n+1)) − g (s,y))`.

It is globally measurable when `g` is (see `measurable_diffQuotLimsup`) and
equals the genuine derivative wherever the latter exists
(`diffQuotLimsup_eq_of_hasDerivAt`). -/
noncomputable def diffQuotLimsup (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Filter.limsup
    (fun n : ℕ => ((n : ℝ) + 1) * (g (p.1, p.2 + 1 / ((n : ℝ) + 1)) - g p))
    Filter.atTop

/-- The difference-quotient `limsup` surrogate is globally measurable whenever
the underlying field `g : ℝ × ℝ → ℝ` is measurable. -/
theorem measurable_diffQuotLimsup {g : ℝ × ℝ → ℝ} (hg : Measurable g) :
    Measurable (diffQuotLimsup g) := by
  unfold diffQuotLimsup
  refine Measurable.limsup (fun n => ?_)
  -- `p ↦ (n+1) * (g (p.1, p.2 + 1/(n+1)) - g p)` is measurable.
  have hshift : Measurable (fun p : ℝ × ℝ => (p.1, p.2 + 1 / ((n : ℝ) + 1))) :=
    measurable_fst.prodMk (measurable_snd.add_const _)
  have h1 : Measurable (fun p : ℝ × ℝ => g (p.1, p.2 + 1 / ((n : ℝ) + 1))) :=
    hg.comp hshift
  exact (h1.sub hg).const_mul _

/-- Wherever the spatial slice `y' ↦ g (s, y')` is differentiable at `y` with
derivative `d`, the difference-quotient `limsup` surrogate returns `d`. -/
theorem diffQuotLimsup_eq_of_hasDerivAt {g : ℝ × ℝ → ℝ} {s y d : ℝ}
    (h : HasDerivAt (fun y' : ℝ => g (s, y')) d y) :
    diffQuotLimsup g (s, y) = d := by
  -- The slope along `y + 1/(n+1) → y` (within `{≠ y}`) tends to `d`.
  have hslope :
      Filter.Tendsto (slope (fun y' : ℝ => g (s, y')) y) (𝓝[≠] y) (𝓝 d) :=
    h.tendsto_slope
  -- The sequence `n ↦ y + 1/(n+1)` tends to `y` within `{≠ y}`.
  have hseq :
      Filter.Tendsto (fun n : ℕ => y + 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝[≠] y) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · -- tends to `y`
      have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have hsum :
          Filter.Tendsto (fun n : ℕ => y + 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 (y + 0)) :=
        (tendsto_const_nhds (α := ℕ) (x := y)).add h0
      simpa using hsum
    · -- eventually `≠ y`
      refine Filter.Eventually.of_forall (fun n => ?_)
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcontra
      have : (1 : ℝ) / ((n : ℝ) + 1) = 0 := by linarith [hcontra]
      linarith
  -- Compose: the sequence of slopes tends to `d`.
  have hcomp :
      Filter.Tendsto
        (fun n : ℕ => slope (fun y' : ℝ => g (s, y')) y (y + 1 / ((n : ℝ) + 1)))
        Filter.atTop (𝓝 d) :=
    hslope.comp hseq
  -- Rewrite the slope into the explicit difference-quotient form.
  have hrw :
      (fun n : ℕ => slope (fun y' : ℝ => g (s, y')) y (y + 1 / ((n : ℝ) + 1)))
        = (fun n : ℕ =>
            ((n : ℝ) + 1) * (g (s, y + 1 / ((n : ℝ) + 1)) - g (s, y))) := by
    funext n
    have hden : (y + 1 / ((n : ℝ) + 1)) - y = 1 / ((n : ℝ) + 1) := by ring
    rw [slope_def_field, hden, one_div, div_inv_eq_mul]
    ring
  rw [hrw] at hcomp
  -- `diffQuotLimsup g (s,y)` is the `limsup` of this convergent sequence.
  have : diffQuotLimsup g (s, y)
      = Filter.limsup
          (fun n : ℕ => ((n : ℝ) + 1) * (g (s, y + 1 / ((n : ℝ) + 1)) - g (s, y)))
          Filter.atTop := rfl
  rw [this]
  exact hcomp.limsup_eq

end ShenWork.ParamDeriv
