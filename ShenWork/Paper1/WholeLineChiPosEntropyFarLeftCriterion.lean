import ShenWork.Paper1.WholeLineChiPosEntropyLiouville
import ShenWork.Paper1.WholeLineCauchyLeftTailBridge

/-!
# Far-left convergence criterion from entropy compactness

This file isolates the sole compactness bridge left after the sharp nonlinear
entropy Liouville theorem.  A failure of uniform far-left convergence produces
times `t_n -> +infinity` and co-moving positions `z_n -> -infinity` at which
the population stays a fixed distance from one.  The interface below asks that
every such translation sequence have a subsequence converging at the origin to
an entire orbit carrying `ChiOneEntireWeightedEntropyData`.

The Liouville theorem makes that limit identically one, contradicting the bad
value at the origin.  Thus the compactness interface implies genuine
`UniformCoMovingLeftEquilibriumConvergence` on every range for which the
localized entropy loss is below one; in particular this is available for all
`0 <= chi < 4`.
-/

open Filter Topology Real

noncomputable section

namespace ShenWork.Paper1

/-- Exact translate-compactness payload needed by the entropy route.  Only
origin convergence is exposed to the consumer; the fact that the returned
entire orbit is the local limit of all translated derivatives is encapsulated
by its `ChiOneEntireWeightedEntropyData` certificate. -/
structure ChiOneFarLeftEntropyCompactness
    (chi c ell k : ℝ) (orbit : ℝ → ℝ → ℝ) : Prop where
  extract :
    ∀ (timeShift spaceShift : ℕ → ℝ),
      (∀ n : ℕ, (n : ℝ) ≤ timeShift n) →
      (∀ n : ℕ, spaceShift n ≤ -(n : ℝ)) →
      ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
        ∃ (u ux uxx ut r rx rxx : ℝ → ℝ → ℝ),
          ChiOneEntireWeightedEntropyData chi c ell k 0
            u ux uxx ut r rx rxx ∧
          Tendsto
            (fun n : ℕ =>
              coMovingPath c orbit (timeShift (subseq n))
                (spaceShift (subseq n)))
            atTop (𝓝 (u 0 0))

/-- Entropy rigidity turns the translate-compactness payload into actual
uniform far-left convergence. -/
theorem uniformCoMovingLeftEquilibriumConvergence_of_entropyCompactness
    {chi c ell k : ℝ} {orbit : ℝ → ℝ → ℝ}
    (hloss : chiOneWeightedEntropyLoss chi c ell k < 1)
    (Hcompact : ChiOneFarLeftEntropyCompactness chi c ell k orbit) :
    UniformCoMovingLeftEquilibriumConvergence c orbit := by
  classical
  by_contra hnot
  unfold UniformCoMovingLeftEquilibriumConvergence at hnot
  push_neg at hnot
  obtain ⟨epsilon, hepsilon, hbad⟩ := hnot
  have hwitness : ∀ n : ℕ, ∃ t z : ℝ,
      (n : ℝ) ≤ t ∧ z ≤ -(n : ℝ) ∧
        epsilon ≤ |coMovingPath c orbit t z - 1| := by
    intro n
    exact hbad (n : ℝ) (n : ℝ)
  choose timeShift spaceShift htime hspace hsep using hwitness
  obtain ⟨subseq, _hsubseq, u, ux, uxx, ut, r, rx, rxx, Hentire, hconv⟩ :=
    Hcompact.extract timeShift spaceShift htime hspace
  have hconvAbs : Tendsto
      (fun n : ℕ =>
        |coMovingPath c orbit (timeShift (subseq n))
            (spaceShift (subseq n)) - 1|)
      atTop (𝓝 |u 0 0 - 1|) :=
    (hconv.sub tendsto_const_nhds).abs
  have hlimit : epsilon ≤ |u 0 0 - 1| :=
    ge_of_tendsto hconvAbs
      (Eventually.of_forall fun n => hsep (subseq n))
  have hone : u 0 0 = 1 := Hentire.population_eq_one hloss 0 0
  rw [hone, sub_self, abs_zero] at hlimit
  linarith

/-- On the normalized full sub-Turing range, it is enough to construct the
translate-compactness package for slowly localized weights. -/
theorem uniformCoMovingLeftEquilibriumConvergence_chiOne_full_sharp_range_of_entropyCompactness
    {chi c ell : ℝ} {orbit : ℝ → ℝ → ℝ}
    (hchi : 0 ≤ chi) (hchi4 : chi < 4) (hell : 0 < ell)
    (Hcompact : ∀ k : ℝ, 0 < k → k < 1 →
      ChiOneFarLeftEntropyCompactness chi c ell k orbit) :
    UniformCoMovingLeftEquilibriumConvergence c orbit := by
  obtain ⟨k, hkpos, hk1, hloss⟩ :=
    exists_chiOne_localizationSlope_full_sharp_range hchi hchi4 hell
  exact uniformCoMovingLeftEquilibriumConvergence_of_entropyCompactness
    hloss (Hcompact k hkpos hk1)

section AxiomAudit

#print axioms uniformCoMovingLeftEquilibriumConvergence_of_entropyCompactness
#print axioms
  uniformCoMovingLeftEquilibriumConvergence_chiOne_full_sharp_range_of_entropyCompactness

end AxiomAudit

end ShenWork.Paper1
