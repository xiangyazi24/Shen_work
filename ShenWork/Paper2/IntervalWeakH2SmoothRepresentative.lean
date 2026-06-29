import ShenWork.Paper2.IntervalDomainLogisticWeakH2Adapter
import ShenWork.Paper2.IntervalSourceRepresentative

/-!
# Weak `H²_N` certificates from smooth doubly-even representatives

This file packages a recurring endpoint-compatibility pattern: a globally smooth
function that is even about both endpoints has all odd endpoint derivatives equal
to zero.  For `C²` representatives this gives `IntervalWeakH2Neumann`; for `C⁴`
representatives it also gives the depth-two weak `H²` tower used for quartic
cosine-coefficient decay.
-/

open Filter Topology Set

noncomputable section

namespace ShenWork.Paper2.WeakH2SmoothRepresentative

open ShenWork.PDE.IntervalMildSourceDecayHelper
open ShenWork.Paper2.SourceRepresentative

/-- A global `C²` doubly-even representative has a weak `H²_N` certificate on
`[0,1]`. -/
noncomputable def intervalWeakH2Neumann_of_doublyEven
    {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G) (hDE : DoublyEven G) :
    IntervalWeakH2Neumann G := by
  have hcompat := higherNeumannCompatibility_of_doublyEven hDE
  have hbc0 : deriv G 0 = 0 := by
    simpa using hcompat.1 0 (by norm_num)
  have hbc1 : deriv G 1 = 0 := by
    simpa using hcompat.2 0 (by norm_num)
  have hderiv_cont : Continuous (deriv G) := hG.continuous_deriv (by norm_num)
  have htend0 : Tendsto (deriv G) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    have h := hderiv_cont.continuousAt (x := (0 : ℝ))
    simpa [hbc0] using h.mono_left nhdsWithin_le_nhds
  have htend1 : Tendsto (deriv G) (nhdsWithin (1 : ℝ) (Iio 1)) (nhds 0) := by
    have h := hderiv_cont.continuousAt (x := (1 : ℝ))
    simpa [hbc1] using h.mono_left nhdsWithin_le_nhds
  exact intervalWeakH2Neumann_of_contDiffOn hG.contDiffOn htend0 htend1 hbc0 hbc1

/-- Transfer the weak `H²_N` certificate from a smooth doubly-even representative
to any function agreeing with it on `[0,1]`. -/
noncomputable def intervalWeakH2Neumann_of_doublyEven_agree
    {f G : ℝ → ℝ} (hG : ContDiff ℝ 2 G) (hDE : DoublyEven G)
    (hGF : ∀ x ∈ Icc (0 : ℝ) 1, G x = f x) :
    IntervalWeakH2Neumann f :=
  (intervalWeakH2Neumann_of_doublyEven hG hDE).congr_on_Icc hGF

theorem intervalWeakH2Neumann_of_doublyEven_agree_secondDeriv
    {f G : ℝ → ℝ} (hG : ContDiff ℝ 2 G) (hDE : DoublyEven G)
    (hGF : ∀ x ∈ Icc (0 : ℝ) 1, G x = f x) :
    (intervalWeakH2Neumann_of_doublyEven_agree hG hDE hGF).secondDeriv =
      deriv (deriv G) := by
  dsimp [intervalWeakH2Neumann_of_doublyEven_agree,
    IntervalWeakH2Neumann.congr_on_Icc, intervalWeakH2Neumann_of_doublyEven,
    intervalWeakH2Neumann_of_contDiffOn]

/-- A global `C⁴` doubly-even representative gives the depth-two weak `H²_N`
tower: first for `G`, then for the weak second derivative of `G`. -/
noncomputable def intervalWeakH4Neumann_of_doublyEven
    {G : ℝ → ℝ} (hG : ContDiff ℝ 4 G) (hDE : DoublyEven G) :
    Σ hG2 : IntervalWeakH2Neumann G, IntervalWeakH2Neumann hG2.secondDeriv := by
  let hG2 : IntervalWeakH2Neumann G :=
    intervalWeakH2Neumann_of_doublyEven (hG.of_le (by norm_num)) hDE
  have hG3 : ContDiff ℝ 3 (deriv G) := by
    simpa using (hG.deriv' : ContDiff ℝ 3 (deriv G))
  have hGddC2 : ContDiff ℝ 2 (deriv (deriv G)) := by
    simpa using (hG3.deriv' : ContDiff ℝ 2 (deriv (deriv G)))
  have hGddDE : DoublyEven (deriv (deriv G)) := hDE.deriv_deriv
  have hGddH2 : IntervalWeakH2Neumann (deriv (deriv G)) :=
    intervalWeakH2Neumann_of_doublyEven hGddC2 hGddDE
  refine ⟨hG2, ?_⟩
  dsimp [hG2, intervalWeakH2Neumann_of_doublyEven,
    intervalWeakH2Neumann_of_contDiffOn]
  exact hGddH2

/-- The depth-two weak `H²_N` tower transfers to a function agreeing with a smooth
doubly-even `C⁴` representative on `[0,1]`.  The second-derivative layer remains
the representative's classical second derivative, which is exactly the
`secondDeriv` stored by the transferred certificate. -/
noncomputable def intervalWeakH4Neumann_of_doublyEven_agree
    {f G : ℝ → ℝ} (hG : ContDiff ℝ 4 G) (hDE : DoublyEven G)
    (hGF : ∀ x ∈ Icc (0 : ℝ) 1, G x = f x) :
    Σ hf : IntervalWeakH2Neumann f, IntervalWeakH2Neumann hf.secondDeriv := by
  let hG2 : IntervalWeakH2Neumann G :=
    intervalWeakH2Neumann_of_doublyEven (hG.of_le (by norm_num)) hDE
  let hf : IntervalWeakH2Neumann f := hG2.congr_on_Icc hGF
  have hG3 : ContDiff ℝ 3 (deriv G) := by
    simpa using (hG.deriv' : ContDiff ℝ 3 (deriv G))
  have hGddC2 : ContDiff ℝ 2 (deriv (deriv G)) := by
    simpa using (hG3.deriv' : ContDiff ℝ 2 (deriv (deriv G)))
  have hGddDE : DoublyEven (deriv (deriv G)) := hDE.deriv_deriv
  have hGddH2 : IntervalWeakH2Neumann (deriv (deriv G)) :=
    intervalWeakH2Neumann_of_doublyEven hGddC2 hGddDE
  refine ⟨hf, ?_⟩
  dsimp [hf, hG2, IntervalWeakH2Neumann.congr_on_Icc,
    intervalWeakH2Neumann_of_doublyEven, intervalWeakH2Neumann_of_contDiffOn]
  exact hGddH2

theorem intervalWeakH4Neumann_of_doublyEven_agree_fourthDeriv
    {f G : ℝ → ℝ} (hG : ContDiff ℝ 4 G) (hDE : DoublyEven G)
    (hGF : ∀ x ∈ Icc (0 : ℝ) 1, G x = f x) :
    (intervalWeakH4Neumann_of_doublyEven_agree hG hDE hGF).2.secondDeriv =
      deriv (deriv (deriv (deriv G))) := by
  dsimp [intervalWeakH4Neumann_of_doublyEven_agree,
    intervalWeakH2Neumann_of_doublyEven, intervalWeakH2Neumann_of_contDiffOn]

end ShenWork.Paper2.WeakH2SmoothRepresentative

end -- noncomputable section
