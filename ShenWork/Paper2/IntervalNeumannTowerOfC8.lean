/-
# Producer: a depth-`4` `NeumannTower` from a globally `C⁸`-Neumann function

This file is the order-`8` analog of
`ShenWork.Paper2.NeumannTowerOfC6.neumannTower_three_of_contDiff_six`: it builds the
depth-`4` `ShenWork.IntervalIBPCoeffExtraction.NeumannTower (gTower f) 4` from the
*global* `C⁸` smoothness of a representative `f : ℝ → ℝ` together with the Neumann
boundary chain (the odd derivatives `∂ₓ f`, `∂ₓ³ f`, `∂ₓ⁵ f`, `∂ₓ⁷ f` all vanish at the
endpoints `0` and `1`).

It reuses the committed even-derivative tower `gTower f i = ∂ₓ^{2i} f` and its lemmas
(`gTower_step`, `deriv_gTower`, `contDiff_gTower`, `continuous_deriv_gTower`) at one
level higher.  For `i < 4`: `2 + 2*i ≤ 8` and `2*i + 1 ≤ 8`, so `f ∈ C⁸` covers every
level.

The depth-`4` tower feeds `cosineCoeffs_decay` at `j = 4`, giving
`|cosineCoeffs (g 0) n| ≤ 2M/(nπ)^8` — the order-`8` decay needed for the eigen-cube
SUMMABILITY (`(nπ)^6 · |coeff| ≤ 2M/(nπ)^2`).

No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalNeumannTowerOfC6

open Set Filter Topology
open ShenWork.IntervalIBPCoeffExtraction (NeumannTower)
open ShenWork.Paper2.NeumannTowerOfC6
  (gTower gTower_zero gTower_step deriv_gTower contDiff_gTower continuous_deriv_gTower)

namespace ShenWork.Paper2.NeumannTowerOfC8

noncomputable section

/-- **Producer.**  From a *globally* `C⁸` representative `f : ℝ → ℝ` whose odd
derivatives `∂ₓ f`, `∂ₓ³ f`, `∂ₓ⁵ f`, `∂ₓ⁷ f` vanish at the endpoints `0` and `1`, build
the depth-`4` `NeumannTower (gTower f) 4`.  The hypotheses are exactly the source's
honest `C⁸`-Neumann spatial regularity. -/
theorem neumannTower_four_of_contDiff_eight
    {f : ℝ → ℝ}
    (hf : ContDiff ℝ (8 : ℕ) f)
    (hN0 : ∀ i, i < 4 → deriv (gTower f i) 0 = 0)
    (hN1 : ∀ i, i < 4 → deriv (gTower f i) 1 = 0) :
    NeumannTower (gTower f) 4 := by
  -- For `i < 4`: `2 + 2*i ≤ 8` and `2*i + 1 ≤ 8`, so `f ∈ C⁸` covers every level.
  have hcd : ∀ i, i < 4 → ContDiff ℝ 2 (gTower f i) := by
    intro i hi
    refine contDiff_gTower (hf.of_le ?_)
    have : (2 + 2 * i : ℕ) ≤ 8 := by omega
    exact_mod_cast this
  have hcont : ∀ i, i < 4 → Continuous (deriv (gTower f i)) := by
    intro i hi
    refine continuous_deriv_gTower (hf.of_le ?_)
    have : (2 * i + 1 : ℕ) ≤ 8 := by omega
    exact_mod_cast this
  refine
    { step := fun i _ => gTower_step f i
      contDiff := fun i hi => (hcd i hi).contDiffOn
      tend0 := fun i hi => ?_
      tend1 := fun i hi => ?_
      bc0 := hN0
      bc1 := hN1 }
  · have hc := (hcont i hi).continuousAt (x := (0 : ℝ))
    have hT : Tendsto (deriv (gTower f i)) (nhds 0) (nhds (deriv (gTower f i) 0)) := hc
    rw [hN0 i hi] at hT
    exact hT.mono_left nhdsWithin_le_nhds
  · have hc := (hcont i hi).continuousAt (x := (1 : ℝ))
    have hT : Tendsto (deriv (gTower f i)) (nhds 1) (nhds (deriv (gTower f i) 1)) := hc
    rw [hN1 i hi] at hT
    exact hT.mono_left nhdsWithin_le_nhds

end

end ShenWork.Paper2.NeumannTowerOfC8
