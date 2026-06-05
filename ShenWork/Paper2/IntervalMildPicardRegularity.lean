/-
  ShenWork/Paper2/IntervalMildPicardRegularity.lean

  Picard iterate C² regularity bridge for mild solutions.

  The regularity bootstrap for mild solutions has a circularity:
  - To prove C² of the solution, we need `DuhamelSourceTimeC1` for the source
  - But `DuhamelSourceTimeC1` of the source depends on C² of the solution

  This file breaks the circularity by proving key structural lemmas for the
  Picard regularity induction.

  **Core contributions**:

  (A) **Logistic source C² + H² Neumann from globally C², positive profile.**
  If `g : ℝ → ℝ` is globally `C²` and positive on `[0,1]`, then:
  1. The logistic source `g(x)·(a − b·g(x)^α)` is `C²` on an open
     neighborhood of `[0,1]` (from `g > 0` there).
  2. Its Neumann boundary conditions follow from those of `g`.
  3. Assembling with `intervalWeakH2Neumann_of_contDiffOn` gives
     the `IntervalWeakH2Neumann` certificate.
  Applied to the semigroup via `intervalFullSemigroupOperator_contDiff_two_unconditional`.

  (B) **Zeroth cosine coefficient bound.**
  `cosineCoeffs_zero_eq_integral`, `cosineCoeffs_zero_abs_le_of_bound`, and
  `logisticSourceFun_cosineCoeffs_zeroth_bound` give the `ha0_bound`
  hypothesis of `duhamelSourceTimeC1_of_H2Neumann_timeC1`.

  (C) **Time-Leibniz for cosine coefficients.**
  `cosineCoeffs_hasDerivAt_of_smooth_param`: if `f(s, ·)` is continuous and
  `∂_s f` exists and is jointly continuous on a compact slab, then
  `HasDerivAt (fun s => cosineCoeffs (f s) n) (cosineCoeffs (∂_s f τ) n) τ`.
  This gives the `hderiv` hypothesis of `duhamelSourceTimeC1_of_H2Neumann_timeC1`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalMildRegularityBootstrap
import ShenWork.PDE.IntervalSemigroupNeumann
import ShenWork.PDE.IntervalFullKernelBoundaryRegularity
import ShenWork.PDE.IntervalUnderIntegralLeibniz
import ShenWork.PDE.IntervalFullKernelBoundaryRegularity

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalMildPicard
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalSemigroupNeumann
open ShenWork.PDE.IntervalMildSourceDecayHelper
open ShenWork.IntervalMildRegularityBootstrap
open ShenWork.IntervalFullKernelInterchange
open ShenWork.IntervalResolverPositivity
open ShenWork.Paper2.IntervalDomainLpMonotonicity (intervalDomainInteriorMeasure)

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

/-! ## Zeroth cosine coefficient bound

The zeroth cosine coefficient `cosineCoeffs f 0 = ∫₀¹ f(x) dx`.  For continuous
`f` on `[0,1]`, `|cosineCoeffs f 0| ≤ sup_{[0,1]} |f|`. -/

/-- The zeroth cosine coefficient equals `∫₀¹ f(x) dx` (no factor of 2). -/
theorem cosineCoeffs_zero_eq_integral (f : ℝ → ℝ) :
    cosineCoeffs f 0 =
      (∫ x in (0 : ℝ)..1, f x) := by
  simp only [cosineCoeffs,
    ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff,
    ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff]
  simp only [Nat.cast_zero, zero_mul, Real.cos_zero]
  -- Goal is: `if True then (...).re else 2 * (...).re = ∫₀¹ f x`
  simp only [if_true]
  -- The integrand is `(↑(1:ℝ) : ℂ) * ↑(f x)`, simplify to `↑(f x)`
  have : (fun x : ℝ => ((1 : ℝ) : ℂ) * ((f x : ℝ) : ℂ)) =
      (fun x : ℝ => ((f x : ℝ) : ℂ)) := by
    funext x; rw [Complex.ofReal_one, one_mul]
  rw [this, intervalIntegral.integral_ofReal, Complex.ofReal_re]

/-- `|cosineCoeffs f 0| ≤ ∫₀¹ |f(x)| dx`. -/
theorem cosineCoeffs_zero_abs_le_integral_abs
    (f : ℝ → ℝ) :
    |cosineCoeffs f 0| ≤ ∫ x in (0 : ℝ)..1, |f x| := by
  rw [cosineCoeffs_zero_eq_integral]
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have := intervalIntegral.norm_integral_le_integral_norm h01 (f := f) (μ := volume)
  simp only [Real.norm_eq_abs] at this
  exact this

/-- `|cosineCoeffs f 0| ≤ B` when `f` is continuous on `[0,1]` and `|f(x)| ≤ B`
everywhere on `[0,1]`. -/
theorem cosineCoeffs_zero_abs_le_of_bound
    {f : ℝ → ℝ} {B : ℝ} (_hB : 0 ≤ B)
    (hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hbd : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ B) :
    |cosineCoeffs f 0| ≤ B := by
  have hf_int : IntervalIntegrable f volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hcont.integrableOn_compact isCompact_Icc
  calc |cosineCoeffs f 0|
      ≤ ∫ x in (0 : ℝ)..1, |f x| :=
        cosineCoeffs_zero_abs_le_integral_abs f
    _ ≤ ∫ _ in (0 : ℝ)..1, B := by
        apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
          (hf_int.norm) (intervalIntegrable_const)
        intro x hx
        exact hbd x (Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1) ▸ hx)
    _ = B := by simp

/-- The logistic source is bounded on `[0,1]` when the profile is bounded. -/
theorem logisticSourceFun_abs_le_of_bound
    {a b α : ℝ} {g : ℝ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hα : 0 < α) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbd : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ B)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < g x) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |logisticSourceFun a b α g x| ≤ B * (a + b * B ^ α) := by
  intro x hx
  simp only [logisticSourceFun]
  have hgx_pos : 0 < g x := hpos x hx
  have hgx_le : g x ≤ B := by
    have := hbd x hx
    rw [abs_of_pos hgx_pos] at this
    exact this
  have hgx_nn : 0 ≤ g x := hgx_pos.le
  -- |g(x) * (a - b * g(x)^α)|
  rw [abs_mul]
  -- |g(x)| = g(x) since g(x) > 0
  rw [abs_of_pos hgx_pos]
  -- |a - b * g(x)^α| ≤ a + b * g(x)^α ≤ a + b * B^α
  have hgα_nn : 0 ≤ g x ^ α := Real.rpow_nonneg hgx_nn α
  have hgα_le : g x ^ α ≤ B ^ α :=
    Real.rpow_le_rpow hgx_nn hgx_le hα.le
  have hbgα_nn : 0 ≤ b * g x ^ α := mul_nonneg hb hgα_nn
  have hbBα_nn : 0 ≤ b * B ^ α := mul_nonneg hb (Real.rpow_nonneg hB α)
  have hab_sum_nn : 0 ≤ a + b * g x ^ α := by linarith
  have haBα_nn : 0 ≤ a + b * B ^ α := by linarith
  have hbgα_le_bBα : b * g x ^ α ≤ b * B ^ α :=
    mul_le_mul_of_nonneg_left hgα_le hb
  have habs_le : |a - b * g x ^ α| ≤ a + b * g x ^ α := by
    rw [abs_le]
    constructor <;> linarith
  calc g x * |a - b * g x ^ α|
      ≤ g x * (a + b * g x ^ α) :=
        mul_le_mul_of_nonneg_left habs_le hgx_nn
    _ ≤ B * (a + b * B ^ α) :=
        mul_le_mul hgx_le (by linarith) hab_sum_nn hB

/-- Zeroth cosine coefficient bound for the logistic source applied to a
globally C², positive, bounded profile on `[0,1]`. -/
theorem logisticSourceFun_cosineCoeffs_zeroth_bound
    {a b α : ℝ} {g : ℝ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hα : 0 < α) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hg : ContDiff ℝ 2 g)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < g x)
    (hbd : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ B) :
    |cosineCoeffs (logisticSourceFun a b α g) 0| ≤ B * (a + b * B ^ α) := by
  apply cosineCoeffs_zero_abs_le_of_bound
    (by positivity : 0 ≤ B * (a + b * B ^ α))
  · exact (logisticSourceFun_contDiffOn_Icc hg hpos).continuousOn
  · exact logisticSourceFun_abs_le_of_bound hB hα ha hb hbd hpos

/-! ## cosineCoeffs as a real integral

The `cosineCoeffs` definition goes through a complex integral.  For real-valued
functions, we express it purely as a real interval integral so that the
real-valued Leibniz lemma `intervalIntegral_hasDerivAt_time_of_local` applies. -/

/-- For a real-valued `f`, the positive-mode cosine coefficient equals
`2 * ∫₀¹ cos(nπx) * f(x) dx`. -/
theorem cosineCoeffs_pos_eq_integral {f : ℝ → ℝ} {n : ℕ} (hn : n ≠ 0) :
    cosineCoeffs f n =
      2 * ∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f x := by
  simp only [cosineCoeffs,
    ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff,
    if_neg hn,
    ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff]
  congr 1
  rw [show (fun x : ℝ =>
        (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * ((f x : ℝ) : ℂ)) =
      fun x : ℝ => ((Real.cos ((n : ℝ) * Real.pi * x) * f x : ℝ) : ℂ) from by
    funext x; push_cast; ring]
  rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]

/-- Uniform formula: `cosineCoeffs f n = c(n) * ∫₀¹ cos(nπx) * f(x) dx`
where `c(0) = 1` and `c(n) = 2` for `n ≥ 1`. -/
theorem cosineCoeffs_eq_factor_mul_integral (f : ℝ → ℝ) (n : ℕ) :
    cosineCoeffs f n =
      (if n = 0 then 1 else 2) *
        ∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [cosineCoeffs_zero_eq_integral]
  · rw [if_neg (Nat.pos_iff_ne_zero.mp hn)]
    exact cosineCoeffs_pos_eq_integral (Nat.pos_iff_ne_zero.mp hn)

/-! ## Time-Leibniz for cosine coefficients

General lemma: if `f : ℝ → ℝ → ℝ` is a smooth parameter family (parameter `s`,
spatial variable `x`) such that:
- `f(s, ·)` is continuous on `[0,1]` for each `s` near `τ`,
- `∂_s f` exists at each `x ∈ (0,1)` for `s` in a ball around `τ`,
- `∂_s f` is jointly continuous on a compact slab,

then `HasDerivAt (fun s => cosineCoeffs (f s) n) (cosineCoeffs (∂_s f τ) n) τ`.

The proof reduces to the real Leibniz integral rule via the integral formula
for `cosineCoeffs`, then uses `exists_bound_of_continuousOn_slab` for the
dominated convergence bound. -/

/-- **Time-Leibniz for cosine coefficients.**

If `f : ℝ → ℝ → ℝ` satisfies:
1. `f(s,·)` is continuous on `[0,1]` for `s` near `τ`,
2. Each spatial point `x ∈ (0,1)` has `HasDerivAt (fun s => f s x) (f' s x) s`
   for all `s ∈ Metric.ball τ δ`,
3. `f'` is jointly continuous on `[τ-δ, τ+δ] × [0,1]`,

then `HasDerivAt (fun s => cosineCoeffs (f s) n) (cosineCoeffs (f' τ) n) τ`. -/
theorem cosineCoeffs_hasDerivAt_of_smooth_param
    {f f' : ℝ → ℝ → ℝ} {τ δ : ℝ} {n : ℕ} (hδ : 0 < δ)
    (hf_cont : ∀ᶠ s in 𝓝 τ, ContinuousOn (f s) (Set.Icc (0 : ℝ) 1))
    (h_diff : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      ∀ s ∈ Metric.ball τ δ,
        HasDerivAt (fun r => f r x) (f' s x) s)
    (h_cont_deriv : ContinuousOn (Function.uncurry f')
      (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasDerivAt (fun s => cosineCoeffs (f s) n)
      (cosineCoeffs (f' τ) n) τ := by
  -- Express cosineCoeffs via the real integral formula
  have hfactor : ∀ s, cosineCoeffs (f s) n =
      (if n = 0 then 1 else 2) *
        ∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f s x :=
    fun s => cosineCoeffs_eq_factor_mul_integral (f s) n
  -- Set up weighted integrand and its time derivative
  set g : ℝ → ℝ → ℝ := fun s x =>
    Real.cos ((n : ℝ) * Real.pi * x) * f s x
  set g' : ℝ → ℝ → ℝ := fun s x =>
    Real.cos ((n : ℝ) * Real.pi * x) * f' s x
  -- Abbreviation for the cosine weight
  have hcos_cont : Continuous (fun x : ℝ => Real.cos ((n : ℝ) * Real.pi * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id')
  -- Joint continuity of g' on the slab
  have hg'_cont_slab : ContinuousOn (Function.uncurry g')
      (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
    change ContinuousOn
      (fun p : ℝ × ℝ => Real.cos ((n : ℝ) * Real.pi * p.2) * f' p.1 p.2) _
    exact ContinuousOn.mul
      (hcos_cont.comp continuous_snd).continuousOn
      h_cont_deriv
  -- Get the dominated bound from slab continuity
  obtain ⟨bound, hbound_int, hbound⟩ :=
    ShenWork.IntervalUnderIntegralLeibniz.exists_bound_of_continuousOn_slab hδ hg'_cont_slab
  -- Apply the real Leibniz integral rule
  have hraw : HasDerivAt
      (fun s => ∫ x in (0 : ℝ)..1, g s x)
      (∫ x in (0 : ℝ)..1, g' τ x) τ := by
    apply ShenWork.IntervalUnderIntegralLeibniz.intervalIntegral_hasDerivAt_time_of_local hδ
    · -- (hF_meas) AEStronglyMeasurable for g s
      filter_upwards [hf_cont] with s hs
      have : ContinuousOn (g s) (Set.Ioo (0 : ℝ) 1) :=
        ContinuousOn.mul hcos_cont.continuousOn (hs.mono Set.Ioo_subset_Icc_self)
      exact this.aestronglyMeasurable measurableSet_Ioo
    · -- (hF_int) IntervalIntegrable for g τ at the base point
      have hτ_cont := hf_cont.self_of_nhds
      have : ContinuousOn (g τ) (Set.uIcc (0 : ℝ) 1) := by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact ContinuousOn.mul hcos_cont.continuousOn hτ_cont
      exact this.intervalIntegrable
    · -- (hF'_meas) AEStronglyMeasurable for g' τ
      have hf'τ_cont : ContinuousOn (f' τ) (Set.Icc (0 : ℝ) 1) := by
        -- f'(τ, ·) = (uncurry f') ∘ (Prod.mk τ), which is continuous on Icc 0 1
        -- since uncurry f' is continuous on the slab containing {τ} × Icc 0 1.
        have hτ_mem : τ ∈ Set.Icc (τ - δ) (τ + δ) := ⟨by linarith, by linarith⟩
        exact h_cont_deriv.comp
          (continuousOn_const.prodMk continuousOn_id)
          (fun x hx => Set.mk_mem_prod hτ_mem hx)
      have : ContinuousOn (g' τ) (Set.Ioo (0 : ℝ) 1) :=
        ContinuousOn.mul hcos_cont.continuousOn
          (hf'τ_cont.mono Set.Ioo_subset_Icc_self)
      exact this.aestronglyMeasurable measurableSet_Ioo
    · -- (h_bound) dominated bound
      exact hbound
    · -- (hbound_int) integrability of bound
      exact hbound_int
    · -- (h_diff) pointwise HasDerivAt on the ball
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2 ?_
      refine Filter.Eventually.of_forall (fun x hx s hs => ?_)
      change HasDerivAt (fun r => Real.cos ((n : ℝ) * Real.pi * x) * f r x)
        (Real.cos ((n : ℝ) * Real.pi * x) * f' s x) s
      have hconst : HasDerivAt (fun _ : ℝ => Real.cos ((n : ℝ) * Real.pi * x)) 0 s :=
        hasDerivAt_const s _
      have hf_deriv : HasDerivAt (fun r => f r x) (f' s x) s :=
        h_diff x hx s hs
      convert hconst.mul hf_deriv using 1
      ring
  -- Combine: cosineCoeffs(f s)(n) = factor * ∫ g, HasDerivAt lifts through const mul
  have hgoal : HasDerivAt
      (fun s => (if n = 0 then (1 : ℝ) else 2) *
        ∫ x in (0 : ℝ)..1, g s x)
      ((if n = 0 then (1 : ℝ) else 2) *
        ∫ x in (0 : ℝ)..1, g' τ x) τ :=
    hraw.const_mul _
  have hrw_src : (fun s => cosineCoeffs (f s) n) =
      (fun s => (if n = 0 then (1 : ℝ) else 2) *
        ∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f s x) := by
    funext s; exact hfactor s
  have hrw_tgt : cosineCoeffs (f' τ) n =
      (if n = 0 then (1 : ℝ) else 2) *
        ∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f' τ x :=
    cosineCoeffs_eq_factor_mul_integral (f' τ) n
  rw [hrw_src, hrw_tgt]
  exact hgoal

/-! ## DuhamelSourceTimeC1 assembly

The `duhamelSourceTimeC1_of_H2Neumann_timeC1` theorem requires six groups of
hypotheses.  We have proved (A) H² Neumann of the logistic source, (B) 1/k²
coefficient decay, (C) zeroth coefficient bound, and (D) the time-Leibniz for
cosine coefficients.

Below we package the remaining PROFILE hypotheses and prove that any globally C²
family satisfying them yields `DuhamelSourceTimeC1` for the logistic source
coefficients.  Then we show the semigroup satisfies these hypotheses (base case). -/

/-- Pointwise `HasDerivAt` for the logistic source in the time parameter.

If `f : ℝ → ℝ` is a time-parameterized value with `f σ > 0` and
`HasDerivAt f f' σ`, then:
  `d/dσ [f(r)·(a − b·f(r)^α)] = f'·(a − b·(1+α)·f(σ)^α)`. -/
theorem logisticSourceFun_hasDerivAt_time
    {a b α : ℝ} (_hα : 0 < α)
    {f : ℝ → ℝ} {f' σ : ℝ}
    (hf_pos : 0 < f σ)
    (hf_deriv : HasDerivAt f f' σ) :
    HasDerivAt (fun r => f r * (a - b * (f r) ^ α))
      (f' * (a - b * (1 + α) * (f σ) ^ α)) σ := by
  have hf_ne : f σ ≠ 0 := ne_of_gt hf_pos
  have hpow : HasDerivAt (fun r => (f r) ^ α)
      (f' * α * (f σ) ^ (α - 1)) σ :=
    hf_deriv.rpow_const (Or.inl hf_ne)
  have hh_deriv : HasDerivAt (fun r => a - b * (f r) ^ α)
      (0 - b * (f' * α * (f σ) ^ (α - 1))) σ :=
    (hasDerivAt_const σ a).sub (hpow.const_mul b)
  have hprod := hf_deriv.mul hh_deriv
  suffices heq : f' * (a - b * (f σ) ^ α) +
      f σ * (0 - b * (f' * α * (f σ) ^ (α - 1))) =
      f' * (a - b * (1 + α) * (f σ) ^ α) by
    rwa [heq] at hprod
  have hrpow : f σ * (f σ) ^ (α - 1) = (f σ) ^ α := by
    rw [mul_comm, ← Real.rpow_add_one hf_ne]
    congr 1; ring
  linear_combination f' * (-b * α) * hrpow

/-- `DuhamelSourceTimeC1` for the logistic source of a smooth profile family.

This theorem takes explicit PROFILE hypotheses and assembles them into the
full `DuhamelSourceTimeC1` structure via `duhamelSourceTimeC1_of_H2Neumann_timeC1`.

The caller is responsible for providing:
- Uniform H² decay and zeroth coefficient bound (from spatial regularity)
- Time derivative, its continuity, and its uniform bound
-/
noncomputable def logisticSource_duhamelSourceTimeC1
    {p : CM2Params}
    {g : ℝ → ℝ → ℝ}
    -- Spatial regularity at each time
    (hC2 : ∀ σ, ContDiff ℝ 2 (g σ))
    (hpos : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < g σ x)
    (hN0 : ∀ σ, deriv (g σ) 0 = 0)
    (hN1 : ∀ σ, deriv (g σ) 1 = 0)
    -- Uniform coefficient decay
    {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticSourceFun p.a p.b p.α (g σ)) k| ≤
        C / ((k : ℝ) * Real.pi) ^ 2)
    (ha0 : ∀ σ, 0 ≤ σ →
      |cosineCoeffs (logisticSourceFun p.a p.b p.α (g σ)) 0| ≤ C)
    -- Time derivative: HasDerivAt of each cosine coefficient
    {adot : ℝ → ℕ → ℝ}
    (hderiv : ∀ σ n, HasDerivAt
      (fun r => cosineCoeffs (logisticSourceFun p.a p.b p.α (g r)) n)
      (adot σ n) σ)
    (hadotcont : ∀ n, Continuous (fun σ => adot σ n))
    -- Uniform derivative bound
    {Mdot : ℝ}
    (hMdot : ∀ σ, 0 ≤ σ → ∀ n, |adot σ n| ≤ Mdot) :
    DuhamelSourceTimeC1
      (fun σ n => cosineCoeffs (logisticSourceFun p.a p.b p.α (g σ)) n) :=
  duhamelSourceTimeC1_of_H2Neumann_timeC1
    (fun σ hσ => logisticSourceFun_intervalWeakH2Neumann
      (hC2 σ) (hpos σ) (hN0 σ) (hN1 σ))
    hC hdecay hderiv hadotcont hMdot ha0

/-- On `[0,1]`, the domain-lifted logistic source is the scalar logistic
source applied to the lifted profile. -/
theorem logisticLifted_eq_logisticSourceFun_on_Icc
    (p : CM2Params) (w : intervalDomainPoint → ℝ) :
    Set.EqOn (logisticLifted p w)
      (logisticSourceFun p.a p.b p.α (intervalDomainLift w))
      (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  simp [logisticLifted, ShenWork.IntervalDomainExistence.intervalLogisticSource,
    logisticSourceFun, intervalDomainLift, hx]

/-- Half-step restart data specialized to the logistic source.

This packages exactly the profile-level hypotheses consumed by
`logisticSource_duhamelSourceTimeC1`, plus the algebraic restarted-series
agreement.  It is weaker than a generic H² source package: H²-Neumann of the
source itself is derived from the logistic structure. -/
structure GradientMildHalfStepLogisticSourceData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) where
  profile : ℝ → ℝ → ℝ → ℝ
  C : ℝ → ℝ
  hC : ∀ t, 0 < t → t < D.T → 0 ≤ C t
  hC2 : ∀ t, 0 < t → t < D.T →
    ∀ σ, ContDiff ℝ 2 (profile t σ)
  hpos : ∀ t, 0 < t → t < D.T →
    ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < profile t σ x
  hN0 : ∀ t, 0 < t → t < D.T →
    ∀ σ, deriv (profile t σ) 0 = 0
  hN1 : ∀ t, 0 < t → t < D.T →
    ∀ σ, deriv (profile t σ) 1 = 0
  hdecay : ∀ t, 0 < t → t < D.T →
    ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (logisticSourceFun p.a p.b p.α (profile t σ)) k| ≤
        C t / ((k : ℝ) * Real.pi) ^ 2
  ha0_bound : ∀ t, 0 < t → t < D.T →
    ∀ σ, 0 ≤ σ →
      |cosineCoeffs (logisticSourceFun p.a p.b p.α (profile t σ)) 0| ≤ C t
  adot : ℝ → ℝ → ℕ → ℝ
  hderiv : ∀ t, 0 < t → t < D.T →
    ∀ σ n, HasDerivAt
      (fun r : ℝ =>
        cosineCoeffs (logisticSourceFun p.a p.b p.α (profile t r)) n)
      (adot t σ n) σ
  hadotcont : ∀ t, 0 < t → t < D.T →
    ∀ n, Continuous (fun σ : ℝ => adot t σ n)
  Mdot : ℝ → ℝ
  hMdot : ∀ t, 0 < t → t < D.T →
    ∀ σ, 0 ≤ σ → ∀ n, |adot t σ n| ≤ Mdot t
  hagree : ∀ t, 0 < t → t < D.T →
    Set.EqOn (intervalDomainLift (D.u t))
      (fun x : ℝ =>
        ∑' n : ℕ,
          restartDuhamelCoeff (gradientMildHalfStepInitialCoeff D t)
            (fun σ n =>
              cosineCoeffs (logisticSourceFun p.a p.b p.α (profile t σ)) n)
            (t / 2) n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1)

/-- Logistic half-step source data produces the older restart package by using
`logisticSource_duhamelSourceTimeC1` for the source regularity field. -/
noncomputable def gradientMildHalfStepRestartData_of_logisticSourceData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (S : GradientMildHalfStepLogisticSourceData D) :
    GradientMildHalfStepRestartData D where
  a := fun t σ n =>
    cosineCoeffs (logisticSourceFun p.a p.b p.α (S.profile t σ)) n
  src := by
    intro t ht htT
    exact logisticSource_duhamelSourceTimeC1
      (p := p) (g := S.profile t)
      (S.hC2 t ht htT) (S.hpos t ht htT)
      (S.hN0 t ht htT) (S.hN1 t ht htT)
      (S.hC t ht htT) (S.hdecay t ht htT)
      (S.ha0_bound t ht htT) (S.hderiv t ht htT)
      (S.hadotcont t ht htT) (S.hMdot t ht htT)
  hagree := S.hagree

/-- Construct `HasRestartCosineRepresentations` directly from logistic
half-step source data and restarted-series agreement. -/
theorem hasRestartCosineRepresentations_of_gradientMildHalfStepLogisticSourceData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (S : GradientMildHalfStepLogisticSourceData D) :
    HasRestartCosineRepresentations D.T D.u :=
  hasRestartCosineRepresentations_of_gradientMildHalfStepRestartData D
    (gradientMildHalfStepRestartData_of_logisticSourceData D S)

/-- Logistic half-step source data discharges the closed-interval spatial `C²`
package, including endpoint derivative values. -/
theorem gradientMild_closedC2_endpointDerivs_of_halfStepLogisticSourceData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (S : GradientMildHalfStepLogisticSourceData D) :
    ∀ t, 0 < t → t < D.T →
      ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1)
        ∧ deriv (intervalDomainLift (D.u t)) 0 = 0
        ∧ deriv (intervalDomainLift (D.u t)) 1 = 0 :=
  gradientMild_closedC2_endpointDerivs_of_halfStepRestartData D
    (gradientMildHalfStepRestartData_of_logisticSourceData D S)

/-- Logistic half-step source data simultaneously gives closed-interval `C²`
endpoint data and the restart-cosine representation package. -/
theorem gradientMild_closedC2_endpointDerivs_and_hasRestart_of_halfStepLogisticSourceData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (S : GradientMildHalfStepLogisticSourceData D) :
    (∀ t, 0 < t → t < D.T →
      ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1)
        ∧ deriv (intervalDomainLift (D.u t)) 0 = 0
        ∧ deriv (intervalDomainLift (D.u t)) 1 = 0)
      ∧ HasRestartCosineRepresentations D.T D.u :=
  gradientMild_closedC2_endpointDerivs_and_hasRestart_of_halfStepRestartData D
    (gradientMildHalfStepRestartData_of_logisticSourceData D S)

/-! ## Picard iterate spatial regularity by induction

The regularity bootstrap for the full mild solution is closed once we
establish `HasRestartCosineRepresentations`.  The structural machinery
above converts this to **profile-level data** (`GradientMildHalfStepLogisticSourceData`).

Below we prove the KEY CHAIN:

  `DuhamelSourceTimeC1 of source` ->
  `duhamelSpectralCoeff_eigenvalue_summable` ->
  `cosineCoeffSeries_contDiff_two` ->
  C² of the Duhamel cosine series

and the base case (zeroth iterate = semigroup is C²). -/

/-- The logistic Duhamel cosine series is globally C² given
`DuhamelSourceTimeC1` of the source coefficients.  This is the
one-step chain from DuhamelSourceTimeC1 to C² via eigenvalue
summability -> cosine C² engine. -/
theorem duhamel_cosine_series_contDiff_two
    {a : ℝ → ℕ → ℝ} {t : ℝ} (ht : 0 < t)
    (src : DuhamelSourceTimeC1 a) :
    ContDiff ℝ 2 (fun x : ℝ =>
      ∑' n : ℕ, duhamelSpectralCoeff a t n * cosineMode n x) :=
  cosineCoeffSeries_contDiff_two (duhamelSpectralCoeff_eigenvalue_summable src ht)

/-- The restart (homogeneous + Duhamel) cosine series is globally C² given
bounded restart coefficients and `DuhamelSourceTimeC1` of the source.
This is `restartDuhamelCoeffSeries_contDiff_two` re-exported with the
explicit half-step interpretation. -/
theorem restart_cosine_series_contDiff_two
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC1 a) :
    ContDiff ℝ 2 (fun x : ℝ =>
      ∑' n : ℕ, restartDuhamelCoeff a₀ a τ n * cosineMode n x) :=
  restartDuhamelCoeffSeries_contDiff_two hτ ha₀ src

/-! ### Picard iterate slice regularity predicate -/

/-- A Picard iterate has C² slices: at each interior time, the lifted
spatial slice is `ContDiffOn ℝ 2` on `[0,1]` with Neumann BC. -/
def PicardIterateHasC2Slices (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (T : ℝ) (n : ℕ) : Prop :=
  ∀ t, 0 < t → t ≤ T →
    ContDiffOn ℝ 2 (intervalDomainLift (picardIter p u₀ n t)) (Set.Icc (0 : ℝ) 1)
    ∧ deriv (intervalDomainLift (picardIter p u₀ n t)) 0 = 0
    ∧ deriv (intervalDomainLift (picardIter p u₀ n t)) 1 = 0

/-! ### Base case: zeroth iterate (semigroup) is C² -/

/-- Cosine coefficients of a bounded continuous function on `[0,1]` are uniformly bounded. -/
theorem cosineCoeffs_abs_le_of_continuous_bounded
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    {B : ℝ} (hB : 0 ≤ B)
    (hfb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ B) :
    ∀ n, |cosineCoeffs f n| ≤ 2 * B := by
  intro n
  have hfC : ContinuousOn (fun x : ℝ => (f x : ℂ)) (Set.Icc (0 : ℝ) 1) :=
    Complex.continuous_ofReal.comp_continuousOn hf
  have hint : IntervalIntegrable (fun x : ℝ => (f x : ℂ))
      volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hcoeff :=
    ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff_abs_le_two_integral_norm
      hint n
  have hnorm_le : ∫ x in (0 : ℝ)..1, ‖(f x : ℂ)‖ ≤ B := by
    have hmono : ∫ x in (0 : ℝ)..1, ‖(f x : ℂ)‖ ≤
        ∫ x in (0 : ℝ)..1, B := by
      apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
        (hint.norm) (intervalIntegrable_const)
      intro x hx
      have : ‖(f x : ℂ)‖ = |f x| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      rw [this]
      exact hfb x hx
    calc
      ∫ x in (0 : ℝ)..1, ‖(f x : ℂ)‖ ≤ ∫ x in (0 : ℝ)..1, B := hmono
      _ = B := by simp
  calc |cosineCoeffs f n|
      ≤ 2 * ∫ x in (0 : ℝ)..1, ‖(f x : ℂ)‖ := hcoeff
    _ ≤ 2 * B := by nlinarith

/-- The zeroth Picard iterate (heat semigroup) has C² slices with Neumann BC
at every positive time. -/
theorem picardIterateHasC2Slices_zero
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hf_cont : Continuous (intervalDomainLift u₀))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x : intervalDomainPoint, |u₀ x| ≤ B)
    (T : ℝ) :
    PicardIterateHasC2Slices p u₀ T 0 := by
  intro t ht _htT
  set f := intervalDomainLift u₀
  have hf_cont' : Continuous f := by
    simpa [f] using hf_cont
  have hf_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ B := by
    intro x hx; simp only [f, intervalDomainLift, hx, dif_pos]; exact hbound ⟨x, hx⟩
  have hM : ∀ n, |cosineCoeffs f n| ≤ 2 * B :=
    cosineCoeffs_abs_le_of_continuous_bounded hf_cont'.continuousOn hB hf_bound
  -- Semigroup is globally C²
  have hC2 : ContDiff ℝ 2 (fun x => intervalFullSemigroupOperator t f x) :=
    semigroup_contDiff_two ht hf_cont' hM
  -- Agreement on [0,1]: lift(iter₀(t)) = S(t)(lift u₀)
  have hagree : Set.EqOn (intervalDomainLift (picardIter p u₀ 0 t))
      (fun x => intervalFullSemigroupOperator t f x) (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [intervalDomainLift, hx, dif_pos]
    rfl
  refine ⟨?_, ?_, ?_⟩
  -- C² on [0,1] by agreement with the globally C² semigroup
  · exact hC2.contDiffOn.congr hagree
  -- Neumann BC at x=0: unconditional for intervalDomainLift
  · exact ShenWork.IntervalFullKernelRegularity.deriv_intervalDomainLift_eq_zero_at_zero _
  -- Neumann BC at x=1: unconditional for intervalDomainLift
  · exact ShenWork.IntervalFullKernelRegularity.deriv_intervalDomainLift_eq_zero_at_one _

/-! ### Induction step: C² of iterate n → C² of iterate n+1

The induction step uses `RestartCosineRepresentation` from the bootstrap file.
Given:
- Bounded restart coefficients at the half-step (from Picard ball membership)
- `DuhamelSourceTimeC1` for the source (from C² of iterate n + logistic assembly)
- Spectral agreement: the iterate agrees with the restart cosine series on `[0,1]`
- Nonvanishing at endpoints (from positivity of iterates)

we get `ContDiffOn ℝ 2` + Neumann BC from `restartDuhamelSlice_conjunct7`.

The construction below packages this as a clean induction theorem. The spectral
agreement (`hagree`) remains a hypothesis — it follows from the spectral
interchange theorems but is technically involved for the gradient Duhamel form. -/

/-- The data needed to perform one step of the Picard regularity induction:
DuhamelSourceTimeC1 of the source, bounded restart coefficients, spectral
agreement on `[0,1]`, and nonvanishing at endpoints. -/
structure PicardRegularityStepData
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T : ℝ) (n : ℕ) where
  -- For each positive time t ≤ T, the half-step restart data:
  -- Bounded restart coefficients
  M_restart : ℝ
  ha₀_bound : ∀ t, 0 < t → t ≤ T →
    ∀ k, |ShenWork.IntervalNeumannFullKernel.cosineCoeffs
      (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))) k| ≤ M_restart
  -- DuhamelSourceTimeC1 for the source at each restart
  source : ℝ → ℝ → ℕ → ℝ
  src : ∀ t, 0 < t → t ≤ T → DuhamelSourceTimeC1 (source t)
  -- Spectral agreement on [0,1]
  hagree : ∀ t, 0 < t → t ≤ T →
    Set.EqOn (intervalDomainLift (picardIter p u₀ (n + 1) t))
      (fun x : ℝ =>
        ∑' k : ℕ,
          restartDuhamelCoeff
            (ShenWork.IntervalNeumannFullKernel.cosineCoeffs
              (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))))
            (source t) (t / 2) k * cosineMode k x)
      (Set.Icc (0 : ℝ) 1)
  -- Nonvanishing at endpoints (from positivity)
  hne0 : ∀ t, 0 < t → t ≤ T →
    intervalDomainLift (picardIter p u₀ (n + 1) t) 0 ≠ 0
  hne1 : ∀ t, 0 < t → t ≤ T →
    intervalDomainLift (picardIter p u₀ (n + 1) t) 1 ≠ 0

/-- **Picard regularity induction step.** Given the step data, the (n+1)-th
iterate has C² slices with Neumann BC. -/
theorem picardIterateHasC2Slices_succ
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ} {n : ℕ}
    (S : PicardRegularityStepData p u₀ T n) :
    PicardIterateHasC2Slices p u₀ T (n + 1) := by
  intro t ht htT
  have ht2 : 0 < t / 2 := by linarith
  exact restartDuhamelSlice_conjunct7
    ht2 (S.ha₀_bound t ht htT) (S.src t ht htT)
    (S.hagree t ht htT) (S.hne0 t ht htT) (S.hne1 t ht htT)

/-- **Full Picard regularity by induction.** Given step data at every level,
all iterates have C² slices. -/
theorem picardIterateHasC2Slices_all
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (hf_cont : Continuous (intervalDomainLift u₀))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x : intervalDomainPoint, |u₀ x| ≤ B)
    (steps : ∀ n, PicardRegularityStepData p u₀ T n) :
    ∀ n, PicardIterateHasC2Slices p u₀ T n := by
  intro n
  induction n with
  | zero => exact picardIterateHasC2Slices_zero hf_cont hB hbound T
  | succ n _ih => exact picardIterateHasC2Slices_succ (steps n)

/-! ### Restart coefficient bound from Picard ball membership

The Picard iterates satisfy `|u_n(t, x)| ≤ M` (ball membership) and have
continuous slices.  This gives `|cosineCoeffs(lift(u_n(t))) k| ≤ 2M`,
supplying the `ha₀_bound` field of `PicardRegularityStepData`. -/

/-- Restart coefficient bound: if the (n+1)-th iterate at the half-step
is bounded by M and has continuous slices, its cosine coefficients are
bounded by 2M. -/
theorem picardIter_cosineCoeffs_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {n : ℕ}
    {M : ℝ} (hM : 0 ≤ M)
    {t : ℝ} (ht : 0 < t)
    (hball : ∀ x : intervalDomainPoint,
      |picardIter p u₀ (n + 1) (t / 2) x| ≤ M)
    (hcont : Continuous (picardIter p u₀ (n + 1) (t / 2))) :
    ∀ k, |ShenWork.IntervalNeumannFullKernel.cosineCoeffs
      (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))) k| ≤ 2 * M := by
  set w := picardIter p u₀ (n + 1) (t / 2)
  set f := intervalDomainLift w
  have hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : Set.restrict (Set.Icc (0 : ℝ) 1) f = fun x : intervalDomainPoint => w x := by
      ext ⟨x, hx⟩; simp only [Set.restrict, f, intervalDomainLift, hx, dif_pos]; rfl
    rw [heq]; exact hcont
  have hf_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ M := by
    intro x hx
    simp only [f, intervalDomainLift, hx, dif_pos]
    exact hball ⟨x, hx⟩
  exact cosineCoeffs_abs_le_of_continuous_bounded hf_cont hM hf_bound

/-- Positivity of the iterate at boundary points gives the nonvanishing
conditions needed by the restart framework. -/
theorem picardIter_endpoint_ne_zero
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {n : ℕ}
    {t : ℝ}
    (hpos : ∀ x : intervalDomainPoint, 0 < picardIter p u₀ n t x) :
    intervalDomainLift (picardIter p u₀ n t) 0 ≠ 0
    ∧ intervalDomainLift (picardIter p u₀ n t) 1 ≠ 0 := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  constructor
  · simp only [intervalDomainLift, h0, dif_pos]
    exact ne_of_gt (hpos ⟨0, h0⟩)
  · simp only [intervalDomainLift, h1, dif_pos]
    exact ne_of_gt (hpos ⟨1, h1⟩)

end ShenWork.IntervalMildPicardRegularity
