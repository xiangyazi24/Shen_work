/-
  ShenWork/Paper2/IntervalMildPicardRegularity.lean

  Picard iterate C² regularity bridge for mild solutions.

  The regularity bootstrap for mild solutions has a circularity:
  - To prove C² of the solution, we need `DuhamelSourceTimeC1` for the source
  - But `DuhamelSourceTimeC1` of the source depends on C² of the solution

  This file breaks the circularity by proving key structural lemmas for the
  Picard regularity induction.

  **Core contribution**: If `g : ℝ → ℝ` is globally `C²` and positive on
  `[0,1]`, then:
  1. The logistic source `g(x)·(a − b·g(x)^α)` is `C²` on an open
     neighborhood of `[0,1]` (from `g > 0` there).
  2. Its Neumann boundary conditions follow from those of `g`.
  3. Assembling with `intervalWeakH2Neumann_of_contDiffOn` gives
     the `IntervalWeakH2Neumann` certificate.

  This applies directly to the semigroup (zeroth Picard iterate), which is
  globally `C²` by `intervalFullSemigroupOperator_contDiff_two_unconditional`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalMildRegularityBootstrap
import ShenWork.PDE.IntervalSemigroupNeumann

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalMildPicard
open ShenWork.IntervalSemigroupNeumann
open ShenWork.PDE.IntervalMildSourceDecayHelper
open ShenWork.IntervalMildRegularityBootstrap
open ShenWork.IntervalFullKernelInterchange
open ShenWork.IntervalResolverPositivity

noncomputable section

namespace ShenWork.IntervalMildPicardRegularity

/-! ## Logistic source C² regularity from globally C² solution

If `g : ℝ → ℝ` is globally `ContDiff ℝ 2` and positive on `[0,1]`, then
the logistic source `F(x) = g(x) · (a − b · g(x)^α)` is `ContDiff ℝ 2`
on an open neighborhood of `[0,1]` (since `g` is continuous and positive
on the compact `[0,1]`, `g > 0` extends to a neighborhood).

This gives `ContDiffOn ℝ 2 F (Icc 0 1)`, `deriv F 0 = 0`, `deriv F 1 = 0`,
and the one-sided Neumann limits — enough for `IntervalWeakH2Neumann`. -/

/-- The logistic source function: `F(x) = g(x) · (a − b · g(x)^α)`. -/
def logisticSourceFun (a b α : ℝ) (g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => g x * (a - b * g x ^ α)

/-- A globally `C²` function positive on a compact set is positive on an
open neighborhood of that set. -/
theorem exists_pos_neighborhood_of_compact_positive
    {g : ℝ → ℝ} (hg : Continuous g) {K : Set ℝ} (_hK : IsCompact K)
    (hpos : ∀ x ∈ K, 0 < g x) :
    ∃ U : Set ℝ, IsOpen U ∧ K ⊆ U ∧ ∀ x ∈ U, 0 < g x := by
  refine ⟨g ⁻¹' Set.Ioi 0, hg.isOpen_preimage _ isOpen_Ioi,
    fun x hx => ?_, fun x hx => hx⟩
  exact hpos x hx

/-- `ContDiffOn ℝ 2 (g ^ α)` on an open set where `g > 0`, from `g` globally C². -/
theorem contDiffOn_rpow_of_contDiff_pos
    {g : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (hg : ContDiff ℝ 2 g) (_hU : IsOpen U)
    (hpos : ∀ x ∈ U, 0 < g x) :
    ContDiffOn ℝ 2 (fun x => g x ^ α) U :=
  hg.contDiffOn.rpow_const_of_ne (fun x hx => ne_of_gt (hpos x hx))

/-- `ContDiffOn ℝ 2` for the logistic source on an open set where `g > 0`. -/
theorem logisticSourceFun_contDiffOn_of_contDiff_pos
    {a b α : ℝ} {g : ℝ → ℝ} {U : Set ℝ}
    (hg : ContDiff ℝ 2 g) (hU : IsOpen U)
    (hpos : ∀ x ∈ U, 0 < g x) :
    ContDiffOn ℝ 2 (logisticSourceFun a b α g) U := by
  unfold logisticSourceFun
  apply ContDiffOn.mul hg.contDiffOn
  apply ContDiffOn.sub contDiffOn_const
  exact (contDiffOn_rpow_of_contDiff_pos hg hU hpos).const_smul b

/-- `ContDiffOn ℝ 2` for the logistic source on `[0,1]` from globally C² + positive. -/
theorem logisticSourceFun_contDiffOn_Icc
    {a b α : ℝ} {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < g x) :
    ContDiffOn ℝ 2 (logisticSourceFun a b α g) (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨U, hUopen, hKU, hUpos⟩ :=
    exists_pos_neighborhood_of_compact_positive hg.continuous isCompact_Icc hpos
  exact (logisticSourceFun_contDiffOn_of_contDiff_pos hg hUopen hUpos).mono hKU

/-- Neumann BC at `x = 0` for the logistic source. -/
theorem logisticSourceFun_deriv_zero_at_zero
    {a b α : ℝ} {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < g x)
    (hdg0 : deriv g 0 = 0) :
    deriv (logisticSourceFun a b α g) 0 = 0 := by
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hg0_pos : 0 < g 0 := hpos 0 h0mem
  have hg0_ne : g 0 ≠ 0 := ne_of_gt hg0_pos
  -- g is differentiable everywhere
  have hg_diff : DifferentiableAt ℝ g 0 := hg.differentiable (by norm_num) 0
  -- g^α is differentiable at 0 (since g(0) > 0)
  have hgα_diff : DifferentiableAt ℝ (fun x => g x ^ α) 0 :=
    hg_diff.hasDerivAt.rpow_const (Or.inl hg0_ne) |>.differentiableAt
  -- F = g * (a - b * g^α), deriv F = deriv g * (a - b * g^α) + g * deriv(a - b * g^α)
  set h : ℝ → ℝ := fun x => a - b * g x ^ α with hh_def
  have hh_diff : DifferentiableAt ℝ h 0 :=
    (differentiableAt_const a).sub (hgα_diff.const_mul b)
  -- F = g * h where h = a - b * g^α
  -- deriv F 0 = deriv g 0 * h 0 + g 0 * deriv h 0
  have hF_deriv : HasDerivAt (logisticSourceFun a b α g)
      (deriv g 0 * h 0 + g 0 * deriv h 0) 0 := by
    have : logisticSourceFun a b α g = fun x => g x * h x := by
      ext x; simp [logisticSourceFun, hh_def]
    rw [this]
    exact hg_diff.hasDerivAt.mul hh_diff.hasDerivAt
  rw [hF_deriv.deriv, hdg0, zero_mul, zero_add]
  -- deriv(g^α)(0) = deriv g 0 * α * g(0)^(α-1) = 0
  have hdgα : HasDerivAt (fun x => g x ^ α)
      (deriv g 0 * α * g 0 ^ (α - 1)) 0 :=
    hg_diff.hasDerivAt.rpow_const (Or.inl hg0_ne)
  have hdgα_val : deriv (fun x => g x ^ α) 0 = 0 := by
    rw [hdgα.deriv, hdg0, zero_mul, zero_mul]
  -- deriv h 0 = 0 - b * deriv(g^α) 0 = -b * 0 = 0
  have hdh_hasDerivAt : HasDerivAt h
      (0 - b * (deriv g 0 * α * g 0 ^ (α - 1))) 0 := by
    exact (hasDerivAt_const 0 a).sub (hdgα.const_mul b)
  have hdh_val : deriv h 0 = 0 := by
    rw [hdh_hasDerivAt.deriv, hdg0, zero_mul, zero_mul, mul_zero,
        sub_zero]
  rw [hdh_val, mul_zero]

/-- Neumann BC at `x = 1` for the logistic source. -/
theorem logisticSourceFun_deriv_zero_at_one
    {a b α : ℝ} {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < g x)
    (hdg1 : deriv g 1 = 0) :
    deriv (logisticSourceFun a b α g) 1 = 0 := by
  have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hg1_pos : 0 < g 1 := hpos 1 h1mem
  have hg1_ne : g 1 ≠ 0 := ne_of_gt hg1_pos
  have hg_diff : DifferentiableAt ℝ g 1 := hg.differentiable (by norm_num) 1
  have hgα_diff : DifferentiableAt ℝ (fun x => g x ^ α) 1 :=
    hg_diff.hasDerivAt.rpow_const (Or.inl hg1_ne) |>.differentiableAt
  set h : ℝ → ℝ := fun x => a - b * g x ^ α with hh_def
  have hh_diff : DifferentiableAt ℝ h 1 :=
    (differentiableAt_const a).sub (hgα_diff.const_mul b)
  -- F = g * h where h = a - b * g^α
  -- deriv F 1 = deriv g 1 * h 1 + g 1 * deriv h 1 = 0 * h 1 + g 1 * deriv h 1
  have hF_deriv : HasDerivAt (logisticSourceFun a b α g)
      (deriv g 1 * h 1 + g 1 * deriv h 1) 1 := by
    have : logisticSourceFun a b α g = fun x => g x * h x := by
      ext x; simp [logisticSourceFun, hh_def]
    rw [this]
    exact hg_diff.hasDerivAt.mul hh_diff.hasDerivAt
  rw [hF_deriv.deriv, hdg1, zero_mul, zero_add]
  have hdgα : HasDerivAt (fun x => g x ^ α)
      (deriv g 1 * α * g 1 ^ (α - 1)) 1 :=
    hg_diff.hasDerivAt.rpow_const (Or.inl hg1_ne)
  have hdgα_val : deriv (fun x => g x ^ α) 1 = 0 := by
    rw [hdgα.deriv, hdg1, zero_mul, zero_mul]
  have hdh_hasDerivAt : HasDerivAt h
      (0 - b * (deriv g 1 * α * g 1 ^ (α - 1))) 1 := by
    exact (hasDerivAt_const 1 a).sub (hdgα.const_mul b)
  have hdh_val : deriv h 1 = 0 := by
    rw [hdh_hasDerivAt.deriv, hdg1, zero_mul, zero_mul, mul_zero,
        sub_zero]
  rw [hdh_val, mul_zero]

/-- One-sided Neumann limit at `x = 0` for the logistic source.

Since `g` is globally C² and positive on `[0,1]`, by continuity `g > 0` on
an open neighborhood of `[0,1]`.  On this neighborhood the logistic source
is C², hence C¹, hence its derivative is continuous.  Combined with
`deriv F 0 = 0`, the limit follows. -/
theorem logisticSourceFun_tendsto_deriv_left
    {a b α : ℝ} {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < g x)
    (hdg0 : deriv g 0 = 0) :
    Filter.Tendsto (deriv (logisticSourceFun a b α g))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨U, hUopen, hKU, hUpos⟩ :=
    exists_pos_neighborhood_of_compact_positive hg.continuous
      isCompact_Icc hpos
  have hF_C2 : ContDiffOn ℝ 2 (logisticSourceFun a b α g) U :=
    logisticSourceFun_contDiffOn_of_contDiff_pos
      (a := a) (b := b) (α := α) hg hUopen hUpos
  have hF_C1 : ContDiffOn ℝ 1 (logisticSourceFun a b α g) U :=
    hF_C2.of_le (by norm_num)
  have hd_cont :
      ContinuousOn (deriv (logisticSourceFun a b α g)) U :=
    hF_C1.continuousOn_deriv_of_isOpen hUopen (by norm_num)
  have h0mem : (0 : ℝ) ∈ U := hKU (by constructor <;> norm_num)
  have hd0 : deriv (logisticSourceFun a b α g) 0 = 0 :=
    logisticSourceFun_deriv_zero_at_zero hg hpos hdg0
  have hca : ContinuousAt (deriv (logisticSourceFun a b α g)) 0 :=
    hd_cont.continuousAt (hUopen.mem_nhds h0mem)
  -- ContinuousAt = Tendsto _ (nhds 0) (nhds (f 0)) = Tendsto _ (nhds 0) (nhds 0)
  rw [ContinuousAt, hd0] at hca
  exact hca.mono_left nhdsWithin_le_nhds

/-- One-sided Neumann limit at `x = 1` for the logistic source. -/
theorem logisticSourceFun_tendsto_deriv_right
    {a b α : ℝ} {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < g x)
    (hdg1 : deriv g 1 = 0) :
    Filter.Tendsto (deriv (logisticSourceFun a b α g))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  obtain ⟨U, hUopen, hKU, hUpos⟩ :=
    exists_pos_neighborhood_of_compact_positive hg.continuous
      isCompact_Icc hpos
  have hF_C2 : ContDiffOn ℝ 2 (logisticSourceFun a b α g) U :=
    logisticSourceFun_contDiffOn_of_contDiff_pos
      (a := a) (b := b) (α := α) hg hUopen hUpos
  have hF_C1 : ContDiffOn ℝ 1 (logisticSourceFun a b α g) U :=
    hF_C2.of_le (by norm_num)
  have hd_cont :
      ContinuousOn (deriv (logisticSourceFun a b α g)) U :=
    hF_C1.continuousOn_deriv_of_isOpen hUopen (by norm_num)
  have h1mem : (1 : ℝ) ∈ U := hKU (by constructor <;> norm_num)
  have hd1 : deriv (logisticSourceFun a b α g) 1 = 0 :=
    logisticSourceFun_deriv_zero_at_one hg hpos hdg1
  have hca : ContinuousAt (deriv (logisticSourceFun a b α g)) 1 :=
    hd_cont.continuousAt (hUopen.mem_nhds h1mem)
  rw [ContinuousAt, hd1] at hca
  exact hca.mono_left nhdsWithin_le_nhds

/-- Full package: `IntervalWeakH2Neumann` for the logistic source from
globally C², positive on [0,1], with Neumann BC. -/
noncomputable def logisticSourceFun_intervalWeakH2Neumann
    {a b α : ℝ} {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < g x)
    (hdg0 : deriv g 0 = 0) (hdg1 : deriv g 1 = 0) :
    IntervalWeakH2Neumann (logisticSourceFun a b α g) :=
  intervalWeakH2Neumann_of_contDiffOn
    (logisticSourceFun_contDiffOn_Icc hg hpos)
    (logisticSourceFun_tendsto_deriv_left hg hpos hdg0)
    (logisticSourceFun_tendsto_deriv_right hg hpos hdg1)
    (logisticSourceFun_deriv_zero_at_zero hg hpos hdg0)
    (logisticSourceFun_deriv_zero_at_one hg hpos hdg1)

/-- Coefficient decay for the logistic source: `|ĉₖ| ≤ C/(kπ)²` for `k ≥ 1`. -/
theorem logisticSourceFun_cosineCoeff_quadratic_decay
    {a b α : ℝ} {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < g x)
    (hdg0 : deriv g 0 = 0) (hdg1 : deriv g 1 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticSourceFun a b α g) k| ≤ C / ((k : ℝ) * Real.pi) ^ 2 :=
  intervalWeakH2Neumann_cosineCoeff_quadratic_decay
    (logisticSourceFun_intervalWeakH2Neumann hg hpos hdg0 hdg1)

/-! ## Application to the heat semigroup (zeroth Picard iterate)

The semigroup `S(t)f` is globally `ContDiff ℝ 2` (from
`intervalFullSemigroupOperator_contDiff_two_unconditional`) and satisfies
Neumann BC `deriv (S(t)f) 0 = 0`, `deriv (S(t)f) 1 = 0` (from
`intervalFullSemigroupOperator_neumann_at_zero/one`).

When the initial datum `u₀` is positive on `[0,1]`, the semigroup preserves
positivity: `S(t)(lift u₀)(x) > 0` for `x ∈ [0,1]` and `t > 0`.

Assembling these gives `IntervalWeakH2Neumann` and `1/k²` coefficient decay
for the logistic source `F(S(t)u₀)`. -/

/-- The semigroup is globally C². -/
theorem semigroup_contDiff_two
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs f n| ≤ M) :
    ContDiff ℝ 2 (fun x => intervalFullSemigroupOperator t f x) :=
  intervalFullSemigroupOperator_contDiff_two_unconditional
    t ht f hf hM
    (fun x => intervalNeumannFullKernel_cosineKernel_identity ht x)

/-- `IntervalWeakH2Neumann` for the logistic source applied to the semigroup.
This is the base case of the Picard regularity induction: the logistic source
`F(S(t)u₀)` satisfies H²-Neumann when `S(t)u₀ > 0` on `[0,1]`. -/
noncomputable def semigroup_logistic_intervalWeakH2Neumann
    {p : CM2Params} {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ n, |cosineCoeffs f n| ≤ M)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalFullSemigroupOperator t f x) :
    IntervalWeakH2Neumann
      (logisticSourceFun p.a p.b p.α
        (fun x => intervalFullSemigroupOperator t f x)) :=
  logisticSourceFun_intervalWeakH2Neumann
    (semigroup_contDiff_two ht hf hM) hpos
    (intervalFullSemigroupOperator_neumann_at_zero ht hf hM)
    (intervalFullSemigroupOperator_neumann_at_one ht hf hM)

/-- Coefficient decay for the logistic source applied to the semigroup. -/
theorem semigroup_logistic_cosineCoeff_quadratic_decay
    {p : CM2Params} {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ n, |cosineCoeffs f n| ≤ M)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalFullSemigroupOperator t f x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticSourceFun p.a p.b p.α
        (fun x => intervalFullSemigroupOperator t f x)) k|
        ≤ C / ((k : ℝ) * Real.pi) ^ 2 :=
  logisticSourceFun_cosineCoeff_quadratic_decay
    (semigroup_contDiff_two ht hf hM) hpos
    (intervalFullSemigroupOperator_neumann_at_zero ht hf hM)
    (intervalFullSemigroupOperator_neumann_at_one ht hf hM)

end ShenWork.IntervalMildPicardRegularity
