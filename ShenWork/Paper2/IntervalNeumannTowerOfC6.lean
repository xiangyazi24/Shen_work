/-
# Producer: a depth-`3` `NeumannTower` from a globally `C⁶`-Neumann function

The bridge `ShenWork.Paper2.EigenCubeTailFromTower.SourceEigenCubeTailFields_of_neumannTower`
CONSUMES a depth-`3` `ShenWork.IntervalIBPCoeffExtraction.NeumannTower (g) 3` for the
spatial source (and its time derivative).  This file is the PRODUCER of that tower from
the source's spatial regularity, supplied honestly as a *global* `C⁶` smoothness of a
representative `f : ℝ → ℝ` together with the Neumann boundary chain (the odd derivatives
`∂ₓ f`, `∂ₓ³ f`, `∂ₓ⁵ f` all vanish at the endpoints `0` and `1`).

ROUTE.  Set `g i := deriv^[2 i] f` (the `i`-fold spatial Laplacian `∂ₓ^{2i}`).  Then

  * `g 0 = f`                                   (`deriv^[0] = id`),
  * `g (i+1) = deriv (deriv (g i))`             (`deriv^[2i+2] = deriv ∘ deriv ∘ deriv^[2i]`),
  * each level `g i = ∂ₓ^{2i} f ∈ C²` for `i ≤ 2`  (from `f ∈ C⁶`, `ContDiff.iterate_deriv'`),
  * `deriv (g i) = ∂ₓ^{2i+1} f` is an ODD derivative, hence vanishes at `0, 1` by `hN`,
  * and `∂ₓ^{2i+1} f` is continuous (from `f ∈ C⁶`), so it tends to its boundary value `0`.

Only the *global* `C⁶` smoothness of the representative `f` is used, so the plain
(global) `deriv` in the `NeumannTower` definition is exactly the right derivative — no
`derivWithin`/closed-interval awkwardness arises.

No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalIBPCoeffExtraction

open Set Filter Topology
open ShenWork.IntervalIBPCoeffExtraction (NeumannTower)

namespace ShenWork.Paper2.NeumannTowerOfC6

noncomputable section

/-- The even-derivative tower of `f`: `gTower f i = ∂ₓ^{2i} f`. -/
def gTower (f : ℝ → ℝ) (i : ℕ) : ℝ → ℝ := deriv^[2 * i] f

@[simp] theorem gTower_zero (f : ℝ → ℝ) : gTower f 0 = f := by
  simp [gTower]

/-- The tower step: `gTower f (i+1) = deriv (deriv (gTower f i))`. -/
theorem gTower_step (f : ℝ → ℝ) (i : ℕ) :
    gTower f (i + 1) = deriv (deriv (gTower f i)) := by
  change deriv^[2 * (i + 1)] f = deriv (deriv (deriv^[2 * i] f))
  have h : 2 * (i + 1) = (2 * i) + 1 + 1 := by ring
  rw [h, Function.iterate_succ', Function.iterate_succ']
  rfl

/-- `deriv (gTower f i) = ∂ₓ^{2i+1} f`. -/
theorem deriv_gTower (f : ℝ → ℝ) (i : ℕ) :
    deriv (gTower f i) = deriv^[2 * i + 1] f := by
  change deriv (deriv^[2 * i] f) = deriv^[2 * i + 1] f
  rw [Function.iterate_succ']
  rfl

/-- Each tower level is `C²` (globally) when `f` is `C^{2+2i}`. -/
theorem contDiff_gTower {f : ℝ → ℝ} {i : ℕ} (hf : ContDiff ℝ (2 + 2 * i : ℕ) f) :
    ContDiff ℝ 2 (gTower f i) := by
  have := ContDiff.iterate_deriv' 2 (2 * i) hf
  simpa [gTower] using this

/-- `∂ₓ^{2i+1} f` is continuous when `f` is `C^{2i+1}`. -/
theorem continuous_deriv_gTower {f : ℝ → ℝ} {i : ℕ}
    (hf : ContDiff ℝ (2 * i + 1 : ℕ) f) :
    Continuous (deriv (gTower f i)) := by
  rw [deriv_gTower]
  have : ContDiff ℝ 0 (deriv^[2 * i + 1] f) := by
    have := ContDiff.iterate_deriv' 0 (2 * i + 1) (by simpa using hf)
    simpa using this
  exact this.continuous

/-- **Producer.**  From a *globally* `C⁶` representative `f : ℝ → ℝ` whose odd
derivatives `∂ₓ f`, `∂ₓ³ f`, `∂ₓ⁵ f` vanish at the endpoints `0` and `1`, build the
depth-`3` `NeumannTower g` with `g 0 = f`.  The hypotheses are exactly the source's
honest `C⁶`-Neumann spatial regularity. -/
theorem neumannTower_three_of_contDiff_six
    {f : ℝ → ℝ}
    (hf : ContDiff ℝ (6 : ℕ) f)
    (hN0 : ∀ i, i < 3 → deriv (gTower f i) 0 = 0)
    (hN1 : ∀ i, i < 3 → deriv (gTower f i) 1 = 0) :
    ∃ g, g 0 = f ∧ NeumannTower g 3 := by
  refine ⟨gTower f, gTower_zero f, ?_⟩
  -- For `i < 3`: `2 + 2*i ≤ 6` and `2*i + 1 ≤ 6`, so `f ∈ C⁶` covers every level.
  have hcd : ∀ i, i < 3 → ContDiff ℝ 2 (gTower f i) := by
    intro i hi
    refine contDiff_gTower (hf.of_le ?_)
    have : (2 + 2 * i : ℕ) ≤ 6 := by omega
    exact_mod_cast this
  have hcont : ∀ i, i < 3 → Continuous (deriv (gTower f i)) := by
    intro i hi
    refine continuous_deriv_gTower (hf.of_le ?_)
    have : (2 * i + 1 : ℕ) ≤ 6 := by omega
    exact_mod_cast this
  refine
    { step := fun i _ => gTower_step f i
      contDiff := fun i hi => (hcd i hi).contDiffOn
      tend0 := fun i hi => ?_
      tend1 := fun i hi => ?_
      bc0 := hN0
      bc1 := hN1 }
  · -- tendsto at `0` from continuity + boundary value `0`.
    have hc := (hcont i hi).continuousAt (x := (0 : ℝ))
    have : Tendsto (deriv (gTower f i)) (nhds 0) (nhds (deriv (gTower f i) 0)) := hc
    rw [hN0 i hi] at this
    exact this.mono_left nhdsWithin_le_nhds
  · have hc := (hcont i hi).continuousAt (x := (1 : ℝ))
    have : Tendsto (deriv (gTower f i)) (nhds 1) (nhds (deriv (gTower f i) 1)) := hc
    rw [hN1 i hi] at this
    exact this.mono_left nhdsWithin_le_nhds

end

end ShenWork.Paper2.NeumannTowerOfC6
