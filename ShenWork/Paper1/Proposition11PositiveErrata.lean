import ShenWork.Paper1.WholeLineChiPosSupercriticalCeiling

/-!
# Proposition 1.1(2): transcription errata and the faithful hypothesis

The committed `Proposition_1_1` (Statements.lean) encodes the positive-branch
critical threshold as

  `χ < min ((m+γ-1)/(2m-1)) ((m+γ-1)/(γ-1))`.

The source (arXiv:2605.04401, p.7, Proposition 1.1(2)) states

  `0 < χ < min {(2m-1)/(m-1), (m+γ-1)/(γ-1)}`.

Two defects:

* the FIRST ratio is mis-transcribed — `(2m-1)/(m-1)` became `(m+γ-1)/(2m-1)`;
* both ratios are written with denominators that vanish at `m = 1` and `γ = 1`
  respectively.  The paper reads those as "no constraint from that term"
  (division by zero as `+∞`), whereas Lean's `x / 0 = 0` collapses the `min`
  to `0`, making the whole branch VACUOUS for `γ = 1` (and, with the
  mis-transcribed ratio, also degenerate at `m = 1/2`, outside the range).

`paper1PositiveCriticalThreshold` below is the faithful, division-free
encoding: clearing both denominators turns each constraint into a product
inequality which is automatically satisfied in the degenerate case, exactly
matching the paper's `+∞` convention.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- Faithful, division-free form of the paper's positive-critical threshold
`0 < χ < min {(2m-1)/(m-1), (m+γ-1)/(γ-1)}`.  At `m = 1` (resp. `γ = 1`) the
corresponding factor vanishes and the inequality holds vacuously, which is the
paper's `+∞` reading. -/
def paper1PositiveCriticalThreshold (p : CMParams) : Prop :=
  p.χ * (p.m - 1) < 2 * p.m - 1 ∧ p.χ * (p.γ - 1) < p.m + p.γ - 1

/-- For `m > 1` and `γ > 1` the division-free form is equivalent to the
paper's displayed pair of ratio bounds. -/
theorem paper1PositiveCriticalThreshold_iff_ratios
    {p : CMParams} (hm : 1 < p.m) (hγ : 1 < p.γ) :
    paper1PositiveCriticalThreshold p ↔
      (p.χ < (2 * p.m - 1) / (p.m - 1) ∧
        p.χ < (p.m + p.γ - 1) / (p.γ - 1)) := by
  have hm0 : 0 < p.m - 1 := by linarith
  have hγ0 : 0 < p.γ - 1 := by linarith
  unfold paper1PositiveCriticalThreshold
  rw [lt_div_iff₀ hm0, lt_div_iff₀ hγ0]

/-- The degenerate exponents impose no constraint, matching the source. -/
theorem paper1PositiveCriticalThreshold_of_m_eq_one_gamma_eq_one
    {p : CMParams} (hm : p.m = 1) (hγ : p.γ = 1) :
    paper1PositiveCriticalThreshold p := by
  unfold paper1PositiveCriticalThreshold
  rw [hm, hγ]
  norm_num

/-- The committed `Proposition_1_1` encoding is strictly different from the
paper's: at `m = 2, γ = 1` the paper permits every `χ < 3`, while the
committed `min` evaluates to `0` (because Lean's `x / 0 = 0`), so its
positive-critical branch is vacuous.  This exhibits the discrepancy. -/
theorem proposition11_committed_threshold_vacuous_at_gamma_one
    (m : ℝ) (hm : 1 ≤ m) :
    min ((m + 1 - 1) / (2 * m - 1)) ((m + 1 - 1) / ((1 : ℝ) - 1)) = 0 := by
  have hzero : (m + 1 - 1) / ((1 : ℝ) - 1) = 0 := by norm_num
  have hnonneg : 0 ≤ (m + 1 - 1) / (2 * m - 1) := by
    apply div_nonneg <;> linarith
  rw [hzero]
  exact min_eq_right hnonneg

/-- Meanwhile the faithful threshold is satisfied at `m = 2, γ = 1` for every
`χ < 3`, in particular for `χ = 2`, which the committed encoding excludes. -/
theorem paper1PositiveCriticalThreshold_witness_gamma_one
    (p : CMParams) (hm : p.m = 2) (hγ : p.γ = 1) (hχ : p.χ < 3)
    (hχ0 : 0 ≤ p.χ) :
    paper1PositiveCriticalThreshold p := by
  unfold paper1PositiveCriticalThreshold
  rw [hm, hγ]
  constructor <;> nlinarith

/-! ## What the current machinery discharges

The supercritical branch of Proposition 1.1(2) needs no smallness on `χ` at
all: the relaxing parameter ceiling of
`WholeLineChiPosSupercriticalCeiling` is a supersolution for every `χ ≥ 0`
once `m + γ - 1 < α`.  The critical branch is covered by the `MChi` ceiling
whenever `χ < chiStar p`.  The residual is the critical branch on the window
`chiStar p ≤ χ` still allowed by the faithful threshold, which the paper
obtains by a different argument and which is recorded here as open. -/

/-- The faithful threshold does NOT imply the ceiling-regime smallness
`χ < chiStar`: at `m = 1, γ = 2` (so `α = 2` in the critical branch) every
`χ < 2` is admissible for the paper, while `chiStar = 1`. -/
theorem paper1PositiveCriticalThreshold_not_implies_chiStar
    (p : CMParams) (hm : p.m = 1) (hγ : p.γ = 2) (hχ : p.χ = 3 / 2) :
    paper1PositiveCriticalThreshold p ∧ chiStar p ≤ p.χ := by
  constructor
  · unfold paper1PositiveCriticalThreshold
    rw [hm, hγ, hχ]
    norm_num
  · have : chiStar p ≤ 1 := chiStar_le_one p
    rw [hχ]
    linarith

section AxiomAudit

#print axioms paper1PositiveCriticalThreshold_iff_ratios
#print axioms proposition11_committed_threshold_vacuous_at_gamma_one
#print axioms paper1PositiveCriticalThreshold_witness_gamma_one
#print axioms paper1PositiveCriticalThreshold_not_implies_chiStar

end AxiomAudit

end ShenWork.Paper1
