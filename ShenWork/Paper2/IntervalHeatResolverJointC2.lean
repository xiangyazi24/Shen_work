/-
  ShenWork/Paper2/IntervalHeatResolverJointC2.lean

  **Direct** joint `(t,x)` C² regularity of the resolver coupled concentration
  at the heat semigroup base iterate (level 0), via cutoff + `contDiff_tsum`.

  This is the direct route that mirrors §2 of `IntervalHeatSemigroupHighRegularity`
  (the heat semigroup cutoff proof), applied to the resolver time-coefficient
  family `resolverTimeCoeff p u k t = (v̂_k(t)).re`.

  ## Strategy (smooth time cutoff, same as heat §2)

  Fix `c > 0` and `s₀ > c`.  Set `φ := smoothRightCutoff (c/2) c`.
  The *cutoff resolver term*
    `(t,x) ↦ φ(t) · resolverTimeCoeff p u k t · cos(kπx)`
  is C² and its iterated derivatives are globally bounded:
  - for `t ≤ c/2`:  φ(t) = 0 so the term and all its derivatives vanish;
  - for `t ≥ c/2`:  the resolver coefficients are smooth (heat smoothing of u,
    then smooth composition u^γ, then cosine coefficient integral, then
    multiplication by the constant weight 1/(μ+λ_k)).
  The majorant `v k n` has eigenvalue decay from the elliptic weight `1/(μ+λ_k)`
  combined with bounded source coefficients, giving summability.
  `contDiff_tsum` gives `ContDiff ℝ 2` of the cutoff series.
  Near `(s₀, x₀)` with `s₀ > c`, `φ = 1`, so the cutoff series = original series,
  yielding `ContDiffAt ℝ 2`.

  ## Analytic content

  Two formerly isolated blocks carry the analytic content:
  * `cutoffResolverTerm_contDiff_two` — per-term C² of cutoff × resolver term
    (needs resolverTimeCoeff C² on support of cutoff, i.e. t > c/2)
  * `cutoffResolverTerm_iteratedFDeriv_summable_majorant` — summable majorant for
    iterated derivatives (needs eigenvalue decay bound)

  The wiring (contDiff_tsum + eventuallyEq transfer) is fully proved.
-/
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.Paper2.IntervalHeatLevel0SourceDecay
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import Mathlib.Analysis.Calculus.SmoothSeries

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff)
open ShenWork.IntervalPhysicalResolverDataConcrete
  (srcTimeCoeff resolverTimeCoeff_eq_weight_smul)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice srcTimeCoeff_eq_cosineCoeffs)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1 srcSlice2)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_hasDerivAt_of_smooth_param)
open ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
  (cosineCoeffs_continuousOn_of_jointContinuousOn_Icc)
open ShenWork.IntervalResolverJointC2Physical
  (boundedWeightJointTerm boundedWeightJointMajorant
   boundedWeightJointTerm_contDiff boundedWeightJointTerm_iteratedFDeriv_le
   boundedWeightJointGradTerm boundedWeightJointGradMajorant
   boundedWeightJointGradSeries_contDiff_two)
open ShenWork.IntervalResolverSpectralJointC2CutoffBounds
  (norm_iteratedFDeriv_comp_fst_le)
open ShenWork.IntervalResolverSpectralJointC2Concrete (gradCosWeight valueCosWeight)
open ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
  (heatDu heatD2u heatSemigroup_d0 heatSemigroup_d1)
open ShenWork.IntervalResolverSpectralJointC2Cutoff (smoothRightCutoff
  smoothRightCutoff_contDiff smoothRightCutoff_eq_zero_of_le
  smoothRightCutoff_eq_one_of_ge smoothRightCutoff_eventually_eq_one)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointC2Direct

/-! ### Utilities -/

/-- Absolute tsum bound: `|Σ' f n| ≤ Σ' g n` when `|f n| ≤ g n` and `g` is summable. -/
private theorem abs_tsum_le_tsum_of_abs_le
    {f g : ℕ → ℝ} (hfg : ∀ n, |f n| ≤ g n) (hg : Summable g) :
    |∑' n, f n| ≤ ∑' n, g n := by
  have hf : Summable f :=
    Summable.of_norm_bounded hg fun n => by simpa [Real.norm_eq_abs] using hfg n
  have hfabs : Summable (fun n => |f n|) := hf.norm.congr fun n => Real.norm_eq_abs _
  calc |∑' n, f n| = ‖∑' n, f n‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n, g n := by
        refine hfabs.tsum_le_tsum (fun n => ?_) hg
        exact (Real.norm_eq_abs (f n)).symm ▸ hfg n

/-- Product iterated-derivative bound on the positive time half-line, stated for
ordinary derivatives by converting Mathlib's `Within` estimate on the open set
`Ioi 0`. -/
private theorem norm_iteratedFDeriv_mul_le_on_Ioi
    {f g : ℝ → ℝ} (hf : ContDiffOn ℝ (2 : ℕ∞) f (Set.Ioi (0 : ℝ)))
    (hg : ContDiffOn ℝ (2 : ℕ∞) g (Set.Ioi (0 : ℝ)))
    {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : n ≤ 2) :
    ‖iteratedFDeriv ℝ n (fun y : ℝ => f y * g y) t‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f t‖ *
        ‖iteratedFDeriv ℝ (n - i) g t‖ := by
  have hnTop : (n : ℕ) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast hn
  have hwithin := norm_iteratedFDerivWithin_mul_le hf hg isOpen_Ioi.uniqueDiffOn
    (show t ∈ Set.Ioi (0 : ℝ) from ht) hnTop
  have hprod_eq :
      iteratedFDerivWithin ℝ n (fun y : ℝ => f y * g y) (Set.Ioi (0 : ℝ)) t =
        iteratedFDeriv ℝ n (fun y : ℝ => f y * g y) t :=
    (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
      (f := fun y : ℝ => f y * g y) n isOpen_Ioi)
      (show t ∈ Set.Ioi (0 : ℝ) from ht)
  have hf_eq : ∀ i : ℕ,
      iteratedFDerivWithin ℝ i f (Set.Ioi (0 : ℝ)) t =
        iteratedFDeriv ℝ i f t :=
    fun i => (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) i isOpen_Ioi)
      (show t ∈ Set.Ioi (0 : ℝ) from ht)
  have hg_eq : ∀ i : ℕ,
      iteratedFDerivWithin ℝ i g (Set.Ioi (0 : ℝ)) t =
        iteratedFDeriv ℝ i g t :=
    fun i => (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := g) i isOpen_Ioi)
      (show t ∈ Set.Ioi (0 : ℝ) from ht)
  rw [hprod_eq] at hwithin
  simp_rw [hf_eq, hg_eq] at hwithin
  exact hwithin

private theorem resolverWeight_le_inv_kπ_sq
    (p : CM2Params) {k : ℕ} (hk : 1 ≤ k) :
    ShenWork.PDE.intervalNeumannResolverWeight p k ≤
      1 / (((k : ℝ) * Real.pi) ^ 2) := by
  have hmul :=
    ShenWork.IntervalResolverJointC2PhysicalConcrete.eigenvalue_mul_resolverWeight_le_one p k
  have hxpos : 0 < (k : ℝ) * Real.pi := by
    exact mul_pos (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk) Real.pi_pos
  have hx2pos : 0 < ((k : ℝ) * Real.pi) ^ 2 := by positivity
  have hlam :
      ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k =
        ((k : ℝ) * Real.pi) ^ 2 := by
    have h1 :
        ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k =
          (k : ℝ) ^ 2 * Real.pi ^ 2 := rfl
    rw [h1]
    ring
  rw [hlam] at hmul
  calc ShenWork.PDE.intervalNeumannResolverWeight p k
      = (((k : ℝ) * Real.pi) ^ 2 *
          ShenWork.PDE.intervalNeumannResolverWeight p k) /
          (((k : ℝ) * Real.pi) ^ 2) := by
            field_simp [ne_of_gt hx2pos]
    _ ≤ 1 / (((k : ℝ) * Real.pi) ^ 2) :=
        div_le_div_of_nonneg_right hmul (le_of_lt hx2pos)

private theorem summable_natShift_inv_pow (m : ℕ) (hm : 1 < m) :
    Summable (fun k : ℕ => 1 / (((k : ℝ) + 1) ^ m)) := by
  have hbase : Summable (fun k : ℕ => 1 / ((k : ℝ) ^ m)) :=
    (Real.summable_one_div_nat_pow (p := m)).mpr hm
  simpa [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff (f := fun k : ℕ => 1 / ((k : ℝ) ^ m)) 1).2 hbase

private theorem summable_inv_kπ_pow_pos (A : ℝ) {m : ℕ} (hm : 1 < m) :
    Summable (fun k : ℕ =>
      if k = 0 then 0 else A / (((k : ℝ) * Real.pi) ^ m)) := by
  rw [← summable_nat_add_iff 1]
  have hs : Summable (fun k : ℕ =>
      (A / Real.pi ^ m) * (1 / (((k : ℝ) + 1) ^ m))) :=
    (summable_natShift_inv_pow m hm).mul_left _
  refine hs.congr ?_
  intro k
  have hkpos : 0 < (k : ℝ) + 1 := by positivity
  have hkne : (k : ℝ) + 1 ≠ 0 := ne_of_gt hkpos
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    ↓reduceIte]
  rw [mul_pow]
  field_simp [hkne, Real.pi_ne_zero]

private noncomputable def heatLevel0GradCoeffPowerBt
    (Φ C₀ C₁ C₂ : ℝ) (i k : ℕ) : ℝ :=
  if k = 0 then 0 else
    let x : ℝ := (k : ℝ) * Real.pi
    match i with
    | 0 => 4 * Φ * (C₀ / x ^ 6)
    | 1 => 4 * Φ * (C₀ / x ^ 6 + C₁ / x ^ 4)
    | _ => 4 * Φ * (C₀ / x ^ 6 + C₁ / x ^ 4 + C₂ / x ^ 4)

private theorem summable_abs_kπ_mul_inv_kπ_pow6 (A : ℝ) :
    Summable (fun k : ℕ =>
      |(k : ℝ) * Real.pi| *
        (if k = 0 then 0 else A / (((k : ℝ) * Real.pi) ^ 6))) := by
  refine (summable_inv_kπ_pow_pos A (m := 5) (by norm_num)).congr ?_
  intro k
  by_cases hk : k = 0
  · subst k
    simp
  · have hxpos : 0 < (k : ℝ) * Real.pi := by
      exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hk) Real.pi_pos
    have hxne : (k : ℝ) * Real.pi ≠ 0 := ne_of_gt hxpos
    simp [hk, abs_of_nonneg (le_of_lt hxpos)]
    field_simp [hxne]

private theorem summable_abs_kπ_mul_inv_kπ_pow4 (A : ℝ) :
    Summable (fun k : ℕ =>
      |(k : ℝ) * Real.pi| *
        (if k = 0 then 0 else A / (((k : ℝ) * Real.pi) ^ 4))) := by
  refine (summable_inv_kπ_pow_pos A (m := 3) (by norm_num)).congr ?_
  intro k
  by_cases hk : k = 0
  · subst k
    simp
  · have hxpos : 0 < (k : ℝ) * Real.pi := by
      exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hk) Real.pi_pos
    have hxne : (k : ℝ) * Real.pi ≠ 0 := ne_of_gt hxpos
    simp [hk, abs_of_nonneg (le_of_lt hxpos)]
    field_simp [hxne]

private theorem summable_lam_mul_inv_kπ_pow6 (A : ℝ) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        (if k = 0 then 0 else A / (((k : ℝ) * Real.pi) ^ 6))) := by
  refine (summable_inv_kπ_pow_pos A (m := 4) (by norm_num)).congr ?_
  intro k
  by_cases hk : k = 0
  · subst k
    simp [unitIntervalCosineEigenvalue]
  · have hxne : (k : ℝ) * Real.pi ≠ 0 := by
      exact ne_of_gt (mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hk) Real.pi_pos)
    have hlam : unitIntervalCosineEigenvalue k = ((k : ℝ) * Real.pi) ^ 2 := by
      unfold unitIntervalCosineEigenvalue
      ring
    simp [hk, hlam]
    field_simp [hxne]

private theorem summable_lam_mul_inv_kπ_pow4 (A : ℝ) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        (if k = 0 then 0 else A / (((k : ℝ) * Real.pi) ^ 4))) := by
  refine (summable_inv_kπ_pow_pos A (m := 2) (by norm_num)).congr ?_
  intro k
  by_cases hk : k = 0
  · subst k
    simp [unitIntervalCosineEigenvalue]
  · have hxne : (k : ℝ) * Real.pi ≠ 0 := by
      exact ne_of_gt (mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hk) Real.pi_pos)
    have hlam : unitIntervalCosineEigenvalue k = ((k : ℝ) * Real.pi) ^ 2 := by
      unfold unitIntervalCosineEigenvalue
      ring
    simp [hk, hlam]
    field_simp [hxne]

private theorem summable_abs_kπ_lam_mul_inv_kπ_pow6 (A : ℝ) :
    Summable (fun k : ℕ =>
      |(k : ℝ) * Real.pi| * unitIntervalCosineEigenvalue k *
        (if k = 0 then 0 else A / (((k : ℝ) * Real.pi) ^ 6))) := by
  refine (summable_inv_kπ_pow_pos A (m := 3) (by norm_num)).congr ?_
  intro k
  by_cases hk : k = 0
  · subst k
    simp [unitIntervalCosineEigenvalue]
  · have hxpos : 0 < (k : ℝ) * Real.pi := by
      exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hk) Real.pi_pos
    have hxne : (k : ℝ) * Real.pi ≠ 0 := ne_of_gt hxpos
    have hlam : unitIntervalCosineEigenvalue k = ((k : ℝ) * Real.pi) ^ 2 := by
      unfold unitIntervalCosineEigenvalue
      ring
    simp [hk, hlam, abs_of_nonneg (le_of_lt hxpos)]
    field_simp [hxne]

private theorem gradMajorant_zero_eq (Bt : ℕ → ℕ → ℝ) (k : ℕ) :
    boundedWeightJointGradMajorant Bt 0 k =
      |(k : ℝ) * Real.pi| * Bt 0 k := by
  rw [boundedWeightJointGradMajorant, Finset.sum_range_one]
  show (Nat.choose 0 0 : ℝ) * Bt 0 k * gradCosWeight (0 - 0) k = _
  simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self]
  show 1 * Bt 0 k * |(k : ℝ) * Real.pi| = _
  ring

private theorem gradMajorant_one_eq (Bt : ℕ → ℕ → ℝ) (k : ℕ) :
    boundedWeightJointGradMajorant Bt 1 k =
      unitIntervalCosineEigenvalue k * Bt 0 k +
        |(k : ℝ) * Real.pi| * Bt 1 k := by
  rw [boundedWeightJointGradMajorant, Finset.sum_range_succ, Finset.sum_range_one]
  show (Nat.choose 1 0 : ℝ) * Bt 0 k * gradCosWeight (1 - 0) k
      + (Nat.choose 1 1 : ℝ) * Bt 1 k * gradCosWeight (1 - 1) k = _
  simp only [Nat.choose_self, Nat.choose_zero_right, Nat.cast_one]
  show 1 * Bt 0 k * unitIntervalCosineEigenvalue k
      + 1 * Bt 1 k * |(k : ℝ) * Real.pi| = _
  ring

private theorem gradMajorant_two_eq (Bt : ℕ → ℕ → ℝ) (k : ℕ) :
    boundedWeightJointGradMajorant Bt 2 k =
      |(k : ℝ) * Real.pi| * unitIntervalCosineEigenvalue k * Bt 0 k
        + 2 * (unitIntervalCosineEigenvalue k * Bt 1 k)
        + |(k : ℝ) * Real.pi| * Bt 2 k := by
  rw [boundedWeightJointGradMajorant, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  simp only [gradCosWeight, Nat.choose]
  push_cast
  ring

private theorem valueMajorant_zero_eq (Bt : ℕ → ℕ → ℝ) (k : ℕ) :
    boundedWeightJointMajorant Bt 0 k = Bt 0 k := by
  rw [boundedWeightJointMajorant, Finset.sum_range_one]
  show (Nat.choose 0 0 : ℝ) * Bt 0 k * valueCosWeight (0 - 0) k = _
  simp [valueCosWeight]

private theorem valueMajorant_one_eq (Bt : ℕ → ℕ → ℝ) (k : ℕ) :
    boundedWeightJointMajorant Bt 1 k =
      |(k : ℝ) * Real.pi| * Bt 0 k + Bt 1 k := by
  rw [boundedWeightJointMajorant, Finset.sum_range_succ, Finset.sum_range_one]
  show (Nat.choose 1 0 : ℝ) * Bt 0 k * valueCosWeight (1 - 0) k
      + (Nat.choose 1 1 : ℝ) * Bt 1 k * valueCosWeight (1 - 1) k = _
  simp only [Nat.choose_self, Nat.choose_zero_right, Nat.cast_one]
  show 1 * Bt 0 k * |(k : ℝ) * Real.pi| + 1 * Bt 1 k * 1 = _
  ring

private theorem valueMajorant_two_eq (Bt : ℕ → ℕ → ℝ) (k : ℕ) :
    boundedWeightJointMajorant Bt 2 k =
      unitIntervalCosineEigenvalue k * Bt 0 k
        + 2 * (|(k : ℝ) * Real.pi| * Bt 1 k)
        + Bt 2 k := by
  rw [boundedWeightJointMajorant, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  simp only [valueCosWeight, Nat.choose]
  push_cast
  ring

private theorem heatLevel0GradCoeffPowerBt_grad_summable
    (Φ C₀ C₁ C₂ : ℝ) :
    ∀ j : ℕ, (j : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant
        (heatLevel0GradCoeffPowerBt Φ C₀ C₁ C₂) j) := by
  classical
  let Bt : ℕ → ℕ → ℝ := heatLevel0GradCoeffPowerBt Φ C₀ C₁ C₂
  have s0 : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Bt 0 k) := by
    refine (summable_abs_kπ_mul_inv_kπ_pow6 (4 * Φ * C₀)).congr ?_
    intro k
    by_cases hk : k = 0
    · subst k
      simp [Bt, heatLevel0GradCoeffPowerBt]
    · simp [Bt, heatLevel0GradCoeffPowerBt, hk, div_eq_mul_inv]
      ring_nf
  have s1a : Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * Bt 0 k) := by
    refine (summable_lam_mul_inv_kπ_pow6 (4 * Φ * C₀)).congr ?_
    intro k
    by_cases hk : k = 0
    · subst k
      simp [Bt, heatLevel0GradCoeffPowerBt]
    · simp [Bt, heatLevel0GradCoeffPowerBt, hk, div_eq_mul_inv]
      ring_nf
      exact Or.inl trivial
  have s1 : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Bt 1 k) := by
    have h6 := summable_abs_kπ_mul_inv_kπ_pow6 (4 * Φ * C₀)
    have h4 := summable_abs_kπ_mul_inv_kπ_pow4 (4 * Φ * C₁)
    refine (h6.add h4).congr ?_
    intro k
    by_cases hk : k = 0
    · subst k
      simp [Bt, heatLevel0GradCoeffPowerBt]
    · simp [Bt, heatLevel0GradCoeffPowerBt, hk, div_eq_mul_inv]
      ring_nf
  have s2a : Summable (fun k : ℕ =>
      |(k : ℝ) * Real.pi| * unitIntervalCosineEigenvalue k * Bt 0 k) := by
    refine (summable_abs_kπ_lam_mul_inv_kπ_pow6 (4 * Φ * C₀)).congr ?_
    intro k
    by_cases hk : k = 0
    · subst k
      simp [Bt, heatLevel0GradCoeffPowerBt]
    · simp [Bt, heatLevel0GradCoeffPowerBt, hk, div_eq_mul_inv]
      ring_nf
      exact Or.inl trivial
  have s2b : Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * Bt 1 k) := by
    have h6 := summable_lam_mul_inv_kπ_pow6 (4 * Φ * C₀)
    have h4 := summable_lam_mul_inv_kπ_pow4 (4 * Φ * C₁)
    refine (h6.add h4).congr ?_
    intro k
    by_cases hk : k = 0
    · subst k
      simp [Bt, heatLevel0GradCoeffPowerBt]
    · simp [Bt, heatLevel0GradCoeffPowerBt, hk, div_eq_mul_inv]
      ring_nf
  have s2c : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Bt 2 k) := by
    have h6 := summable_abs_kπ_mul_inv_kπ_pow6 (4 * Φ * C₀)
    have h4₁ := summable_abs_kπ_mul_inv_kπ_pow4 (4 * Φ * C₁)
    have h4₂ := summable_abs_kπ_mul_inv_kπ_pow4 (4 * Φ * C₂)
    refine ((h6.add h4₁).add h4₂).congr ?_
    intro k
    by_cases hk : k = 0
    · subst k
      simp [Bt, heatLevel0GradCoeffPowerBt]
    · simp [Bt, heatLevel0GradCoeffPowerBt, hk, div_eq_mul_inv]
      ring_nf
  intro j hj
  have hjNat : j ≤ 2 := by exact_mod_cast hj
  interval_cases j
  · exact s0.congr fun k => (gradMajorant_zero_eq Bt k).symm
  · exact (s1a.add s1).congr fun k => (gradMajorant_one_eq Bt k).symm
  · exact ((s2a.add (s2b.mul_left 2)).add s2c).congr fun k => by
      rw [gradMajorant_two_eq]

private theorem heatLevel0GradCoeffPowerBt_value_summable
    (Φ C₀ C₁ C₂ : ℝ) :
    ∀ j : ℕ, (j : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant
        (heatLevel0GradCoeffPowerBt Φ C₀ C₁ C₂) j) := by
  classical
  let Bt : ℕ → ℕ → ℝ := heatLevel0GradCoeffPowerBt Φ C₀ C₁ C₂
  have b0 : Summable (fun k : ℕ => Bt 0 k) := by
    refine (summable_inv_kπ_pow_pos (4 * Φ * C₀) (m := 6) (by norm_num)).congr ?_
    intro k
    by_cases hk : k = 0
    · subst k
      simp [Bt, heatLevel0GradCoeffPowerBt]
    · simp [Bt, heatLevel0GradCoeffPowerBt, hk, div_eq_mul_inv]
      ring_nf
  have b1 : Summable (fun k : ℕ => Bt 1 k) := by
    have h6 := summable_inv_kπ_pow_pos (4 * Φ * C₀) (m := 6) (by norm_num)
    have h4 := summable_inv_kπ_pow_pos (4 * Φ * C₁) (m := 4) (by norm_num)
    refine (h6.add h4).congr ?_
    intro k
    by_cases hk : k = 0
    · subst k
      simp [Bt, heatLevel0GradCoeffPowerBt]
    · simp [Bt, heatLevel0GradCoeffPowerBt, hk, div_eq_mul_inv]
      ring_nf
  have b2 : Summable (fun k : ℕ => Bt 2 k) := by
    have h6 := summable_inv_kπ_pow_pos (4 * Φ * C₀) (m := 6) (by norm_num)
    have h4₁ := summable_inv_kπ_pow_pos (4 * Φ * C₁) (m := 4) (by norm_num)
    have h4₂ := summable_inv_kπ_pow_pos (4 * Φ * C₂) (m := 4) (by norm_num)
    refine ((h6.add h4₁).add h4₂).congr ?_
    intro k
    by_cases hk : k = 0
    · subst k
      simp [Bt, heatLevel0GradCoeffPowerBt]
    · simp [Bt, heatLevel0GradCoeffPowerBt, hk, div_eq_mul_inv]
      ring_nf
  have s0 : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Bt 0 k) := by
    exact (heatLevel0GradCoeffPowerBt_grad_summable Φ C₀ C₁ C₂ 0 (by norm_num)).congr
      fun k => by rw [gradMajorant_zero_eq]
  have s1a' : Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * Bt 0 k) := by
    refine (summable_lam_mul_inv_kπ_pow6 (4 * Φ * C₀)).congr ?_
    intro k
    by_cases hk : k = 0
    · subst k
      simp [Bt, heatLevel0GradCoeffPowerBt]
    · simp [Bt, heatLevel0GradCoeffPowerBt, hk, div_eq_mul_inv]
      ring_nf
      exact Or.inl trivial
  have s1 : Summable (fun k : ℕ => |(k : ℝ) * Real.pi| * Bt 1 k) := by
    have h6 := summable_abs_kπ_mul_inv_kπ_pow6 (4 * Φ * C₀)
    have h4 := summable_abs_kπ_mul_inv_kπ_pow4 (4 * Φ * C₁)
    refine (h6.add h4).congr ?_
    intro k
    by_cases hk : k = 0
    · subst k
      simp [Bt, heatLevel0GradCoeffPowerBt]
    · simp [Bt, heatLevel0GradCoeffPowerBt, hk, div_eq_mul_inv]
      ring_nf
  intro j hj
  have hjNat : j ≤ 2 := by exact_mod_cast hj
  interval_cases j
  · exact b0.congr fun k => (valueMajorant_zero_eq Bt k).symm
  · exact (s0.add b1).congr fun k => (valueMajorant_one_eq Bt k).symm
  · exact ((s1a'.add (s1.mul_left 2)).add b2).congr fun k => by
      rw [valueMajorant_two_eq]

/-! ### Definitions -/

/-- The `k`-th term of the resolver series, as a function of `(t, x)`:
`(t, x) ↦ resolverTimeCoeff p u k t · cos(kπx)`. -/
def resolverTerm (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (k : ℕ) : ℝ × ℝ → ℝ :=
  fun q => resolverTimeCoeff p u k q.1 * cosineMode k q.2

/-- The `k`-th term of the spatial-gradient resolver series:
`(t, x) ↦ resolverTimeCoeff p u k t · ∂ₓ cos(kπx)`. -/
def resolverGradTerm (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (k : ℕ) : ℝ × ℝ → ℝ :=
  fun q => resolverTimeCoeff p u k q.1 * deriv (cosineMode k) q.2

/-- The cutoff resolver term: `(t,x) ↦ φ(t) · resolverTimeCoeff p u k t · cos(kπx)`. -/
def cutoffResolverTerm (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (c : ℝ) (k : ℕ) : ℝ × ℝ → ℝ :=
  fun q => smoothRightCutoff (c / 2) c q.1 *
    (resolverTimeCoeff p u k q.1 * cosineMode k q.2)

/-- The cutoff gradient resolver term:
`(t,x) ↦ φ(t) · resolverTimeCoeff p u k t · ∂ₓ cos(kπx)`. -/
def cutoffResolverGradTerm (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (c : ℝ) (k : ℕ) : ℝ × ℝ → ℝ :=
  fun q => smoothRightCutoff (c / 2) c q.1 *
    (resolverTimeCoeff p u k q.1 * deriv (cosineMode k) q.2)

/-! ### Layer 1: Source coefficient ContDiffAt at positive time (analytic content) -/

/-- The source time coefficient `srcTimeCoeff p u k` is `ContDiffAt ℝ 2` at any
positive time `t > 0` for the heat semigroup base iterate.

This is the deepest analytic content.  At positive time, the heat semigroup
`S(t)u₀` is C∞, so the source `ν·(S(t)u₀)^γ` is smooth in `(t,x)`.
The time derivatives can be computed via the chain rule + heat equation
`∂ₜ S(t)u₀ = Δ S(t)u₀`.  Differentiating the cosine coefficient integral
`∫₀¹ source(t,x) cos(kπx) dx` under the integral sign (via
`cosineCoeffs_hasDerivAt_of_smooth_param`) twice, then checking continuity of
the second derivative's coefficients, gives `ContDiffAt ℝ 2`. -/
theorem heatLevel0_srcTimeCoeff_contDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ContDiffAt ℝ (2 : ℕ∞)
      (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) t := by
  set s₁ := srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀)
  set s₂ := srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)
  set f₀ := srcTimeCoeff p (conjugatePicardIter p u₀ 0) k
  set f₁ := fun s => cosineCoeffs (s₁ s) k
  set f₂ := fun s => cosineCoeffs (s₂ s) k
  have hd0 : ∀ s ∈ Set.Ioi (0 : ℝ), HasDerivAt f₀ (f₁ s) s := by
    intro s hs
    obtain ⟨δ, hδ, hcont, hdiff, hcd⟩ :=
      heatSemigroup_d0 (p := p) (u₀ := u₀) (M₀ := M₀)
        hu₀_bound hu₀_cont hfloor s hs
    have hint : ∀ᶠ r in 𝓝 s, IntervalIntegrable
        (srcSlice p (conjugatePicardIter p u₀ 0) r)
        MeasureTheory.volume (0 : ℝ) 1 :=
      hcont.mono fun r hr =>
        (Set.uIcc_of_le (zero_le_one (α := ℝ)) ▸ hr).intervalIntegrable
    have hH := cosineCoeffs_hasDerivAt_of_smooth_param
      (f := srcSlice p (conjugatePicardIter p u₀ 0))
      (f' := srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
      (τ := s) (δ := δ) (n := k) hδ hint hdiff hcd
    have heq :
        (fun r => cosineCoeffs (srcSlice p (conjugatePicardIter p u₀ 0) r) k) =
          f₀ := by
      funext r
      simp [f₀, srcTimeCoeff_eq_cosineCoeffs]
    rw [heq] at hH
    simpa [f₁, s₁] using hH
  have hd1 : ∀ s ∈ Set.Ioi (0 : ℝ), HasDerivAt f₁ (f₂ s) s := by
    intro s hs
    obtain ⟨δ, hδ, hcont, hdiff, hcd⟩ :=
      heatSemigroup_d1 (p := p) (u₀ := u₀) (M₀ := M₀)
        hu₀_bound hu₀_cont hfloor s hs
    have hint : ∀ᶠ r in 𝓝 s, IntervalIntegrable
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) r)
        MeasureTheory.volume (0 : ℝ) 1 :=
      hcont.mono fun r hr =>
        (Set.uIcc_of_le (zero_le_one (α := ℝ)) ▸ hr).intervalIntegrable
    have hH := cosineCoeffs_hasDerivAt_of_smooth_param
      (f := srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
      (f' := srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀))
      (τ := s) (δ := δ) (n := k) hδ hint hdiff hcd
    simpa [f₁, f₂, s₁, s₂] using hH
  have hc2 : ∀ s ∈ Set.Ioi (0 : ℝ), ContinuousAt f₂ s := by
    intro s hs
    obtain ⟨δ, hδ, _, _, hcd⟩ :=
      heatSemigroup_d1 (p := p) (u₀ := u₀) (M₀ := M₀)
        hu₀_bound hu₀_cont hfloor s hs
    have hcont_on :=
      cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
        (f := srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀))
        (c := s - δ) (T := s + δ) k hcd
    have hsmem : s ∈ Set.Icc (s - δ) (s + δ) := ⟨by linarith, by linarith⟩
    have hsub : Set.Icc (s - δ) (s + δ) ∈ 𝓝 s := by
      apply Icc_mem_nhds <;> linarith
    simpa [f₂, s₂] using (hcont_on s hsmem).continuousAt hsub
  have hd0_on : DifferentiableOn ℝ f₀ (Set.Ioi 0) :=
    fun s hs => (hd0 s hs).differentiableAt.differentiableWithinAt
  have heq0 : Set.EqOn (deriv f₀) f₁ (Set.Ioi 0) :=
    fun s hs => (hd0 s hs).deriv
  have hd1_on : DifferentiableOn ℝ f₁ (Set.Ioi 0) :=
    fun s hs => (hd1 s hs).differentiableAt.differentiableWithinAt
  have heq1 : Set.EqOn (deriv f₁) f₂ (Set.Ioi 0) :=
    fun s hs => (hd1 s hs).deriv
  have hc2_on : ContinuousOn f₂ (Set.Ioi 0) :=
    fun s hs => (hc2 s hs).continuousWithinAt
  have hsmul0 : ContDiffOn ℝ 0
      (fun s => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f₂ s))
      (Set.Ioi 0) := by
    simpa using (contDiffOn_const (c := (1 : StrongDual ℝ ℝ))).smulRight
      (contDiffOn_zero.mpr hc2_on)
  have hfw1 : ContDiffOn ℝ 0
      (fun s => fderivWithin ℝ f₁ (Set.Ioi 0) s) (Set.Ioi 0) :=
    hsmul0.congr (fun s hs => by
      rw [fderivWithin_of_isOpen isOpen_Ioi hs]
      have hsd : deriv f₁ s = f₂ s := heq1 hs
      simpa [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton, hsd] using
        (toSpanSingleton_deriv (𝕜 := ℝ) (f := f₁) (x := s)).symm)
  have h0 : ContDiffOn ℝ 1 f₁ (Set.Ioi 0) :=
    contDiffOn_succ_of_fderivWithin hd1_on (by nofun) hfw1
  have hsmul1 : ContDiffOn ℝ 1
      (fun s => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (f₁ s))
      (Set.Ioi 0) := by
    simpa using (contDiffOn_const (c := (1 : StrongDual ℝ ℝ))).smulRight h0
  have hfw0 : ContDiffOn ℝ 1
      (fun s => fderivWithin ℝ f₀ (Set.Ioi 0) s) (Set.Ioi 0) :=
    hsmul1.congr (fun s hs => by
      rw [fderivWithin_of_isOpen isOpen_Ioi hs]
      have hsd : deriv f₀ s = f₁ s := heq0 hs
      simpa [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton, hsd] using
        (toSpanSingleton_deriv (𝕜 := ℝ) (f := f₀) (x := s)).symm)
  have h1 : ContDiffOn ℝ 2 f₀ (Set.Ioi 0) :=
    contDiffOn_succ_of_fderivWithin hd0_on (by nofun) hfw0
  simpa [f₀] using h1.contDiffAt (Ioi_mem_nhds ht)

/-! ### Layer 1b: HasDerivAt of source/resolver coefficients (for derivative bounds) -/

/-- `HasDerivAt` of `srcTimeCoeff` at positive time — extracted from d0. -/
theorem heatLevel0_srcTimeCoeff_hasDerivAt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    HasDerivAt (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k)
      (cosineCoeffs (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k) t := by
  obtain ⟨δ, hδ, hcont, hdiff, hcd⟩ :=
    heatSemigroup_d0 (p := p) (u₀ := u₀) (M₀ := M₀) hu₀_bound hu₀_cont hfloor t ht
  have hint : ∀ᶠ r in 𝓝 t, IntervalIntegrable
      (srcSlice p (conjugatePicardIter p u₀ 0) r) MeasureTheory.volume (0 : ℝ) 1 :=
    hcont.mono fun r hr => (Set.uIcc_of_le (zero_le_one (α := ℝ)) ▸ hr).intervalIntegrable
  have hH := cosineCoeffs_hasDerivAt_of_smooth_param
    (f := srcSlice p (conjugatePicardIter p u₀ 0))
    (f' := srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
    (τ := t) (δ := δ) (n := k) hδ hint hdiff hcd
  have heq : (fun r => cosineCoeffs (srcSlice p (conjugatePicardIter p u₀ 0) r) k) =
      srcTimeCoeff p (conjugatePicardIter p u₀ 0) k := by
    funext r; simp [srcTimeCoeff_eq_cosineCoeffs]
  rw [heq] at hH; simpa using hH

/-- `deriv` of `resolverTimeCoeff` at positive time = w_k × cosineCoeffs(srcSlice1). -/
theorem heatLevel0_resolverTimeCoeff_deriv_eq
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    deriv (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t =
      ShenWork.PDE.intervalNeumannResolverWeight p k *
        cosineCoeffs (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k := by
  have hsrc := heatLevel0_srcTimeCoeff_hasDerivAt hu₀_bound hu₀_cont hfloor ht k
  have hEq : resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k = fun s =>
      ShenWork.PDE.intervalNeumannResolverWeight p k *
        srcTimeCoeff p (conjugatePicardIter p u₀ 0) k s := by
    funext s; exact resolverTimeCoeff_eq_weight_smul p _ k s
  rw [hEq]
  exact (hsrc.const_mul _).deriv

/-- The second time derivative of `resolverTimeCoeff` at positive heat time is
the elliptic weight times the second source time-slice coefficient. -/
theorem heatLevel0_resolverTimeCoeff_iteratedDeriv_two_eq
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    iteratedDeriv 2 (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t =
      ShenWork.PDE.intervalNeumannResolverWeight p k *
        cosineCoeffs (srcSlice2 p (conjugatePicardIter p u₀ 0)
          (heatDu u₀) (heatD2u u₀) t) k := by
  set w_k := ShenWork.PDE.intervalNeumannResolverWeight p k
  set R := resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k
  have hRfun : R = fun s =>
      w_k * srcTimeCoeff p (conjugatePicardIter p u₀ 0) k s := by
    funext s
    exact resolverTimeCoeff_eq_weight_smul p (conjugatePicardIter p u₀ 0) k s
  change iteratedDeriv 2 R t = _
  rw [hRfun, iteratedDeriv_const_mul_field]
  congr 1
  rw [iteratedDeriv_succ]
  have hnear : (fun s => iteratedDeriv 1
      (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) s) =ᶠ[𝓝 t]
      fun s => cosineCoeffs (srcSlice1 p (conjugatePicardIter p u₀ 0)
        (heatDu u₀) s) k := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    rw [iteratedDeriv_one]
    exact (heatLevel0_srcTimeCoeff_hasDerivAt hu₀_bound hu₀_cont hfloor hs k).deriv
  rw [Filter.EventuallyEq.deriv_eq hnear]
  obtain ⟨δ₁, hδ₁, hcont_s1, hdiff_s1, hcd_s2⟩ :=
    heatSemigroup_d1 hu₀_bound hu₀_cont hfloor t ht
  have hint : ∀ᶠ r in 𝓝 t, IntervalIntegrable
      (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) r)
      MeasureTheory.volume (0 : ℝ) 1 :=
    hcont_s1.mono fun r hr =>
      (Set.uIcc_of_le (zero_le_one (α := ℝ)) ▸ hr).intervalIntegrable
  exact (cosineCoeffs_hasDerivAt_of_smooth_param hδ₁ hint hdiff_s1 hcd_s2).deriv

/-! ### Layer 2: Resolver coefficient ContDiffAt by constant weight -/

/-- The resolver time coefficient is `ContDiffAt ℝ 2` at positive time.
Follows from `srcTimeCoeff` being `ContDiffAt ℝ 2` and the constant-weight
factorization `resolverTimeCoeff = wₖ · srcTimeCoeff`. -/
theorem heatLevel0_resolverTimeCoeff_contDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ContDiffAt ℝ (2 : ℕ∞)
      (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t := by
  have hsrc := heatLevel0_srcTimeCoeff_contDiffAt_two
    (p := p) hu₀_bound hu₀_cont hfloor ht k
  have hEq : resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k =
      fun s => ShenWork.PDE.intervalNeumannResolverWeight p k *
        srcTimeCoeff p (conjugatePicardIter p u₀ 0) k s := by
    funext s; exact resolverTimeCoeff_eq_weight_smul p _ k s
  rw [hEq]
  exact contDiffAt_const.mul hsrc

private theorem heatLevel0_resolverCoeff_iteratedFDeriv_tail_bound_posMode
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ a C₀ C₁ C₂ : ℝ}
    (ha : 0 < a)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (hC₀ : ∀ t : ℝ, a ≤ t → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (srcSlice p (conjugatePicardIter p u₀ 0) t) k|
        ≤ C₀ / ((k : ℝ) * Real.pi) ^ 4)
    (hC₁ : ∀ t : ℝ, a ≤ t → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k|
        ≤ C₁ / ((k : ℝ) * Real.pi) ^ 2)
    (hC₂ : ∀ t : ℝ, a ≤ t → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs
        (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀) t) k|
        ≤ C₂ / ((k : ℝ) * Real.pi) ^ 2)
    {i k : ℕ} (hi : i ≤ 2) (hk : 1 ≤ k) {t : ℝ} (ht : a ≤ t) :
    ‖iteratedFDeriv ℝ i
      (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t‖ ≤
      ShenWork.PDE.intervalNeumannResolverWeight p k *
        match i with
        | 0 => C₀ / ((k : ℝ) * Real.pi) ^ 4
        | 1 => C₁ / ((k : ℝ) * Real.pi) ^ 2
        | _ => C₂ / ((k : ℝ) * Real.pi) ^ 2 := by
  have htpos : 0 < t := lt_of_lt_of_le ha ht
  have hw_nn : 0 ≤ ShenWork.PDE.intervalNeumannResolverWeight p k :=
    ShenWork.PDE.intervalNeumannResolverWeight_nonneg p k
  interval_cases i
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    rw [resolverTimeCoeff_eq_weight_smul p (conjugatePicardIter p u₀ 0) k t,
      srcTimeCoeff_eq_cosineCoeffs p (conjugatePicardIter p u₀ 0) k t,
      abs_mul, abs_of_nonneg hw_nn]
    exact mul_le_mul_of_nonneg_left (hC₀ t ht k hk) hw_nn
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one, Real.norm_eq_abs]
    rw [heatLevel0_resolverTimeCoeff_deriv_eq hu₀_bound hu₀_cont hfloor htpos k,
      abs_mul, abs_of_nonneg hw_nn]
    exact mul_le_mul_of_nonneg_left (hC₁ t ht k hk) hw_nn
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    rw [heatLevel0_resolverTimeCoeff_iteratedDeriv_two_eq hu₀_bound hu₀_cont hfloor htpos k,
      abs_mul, abs_of_nonneg hw_nn]
    exact mul_le_mul_of_nonneg_left (hC₂ t ht k hk) hw_nn

private theorem heatLevel0_cutoffResolverCoeff_iteratedFDeriv_tail_bound_posMode
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ a c Φ C₀ C₁ C₂ : ℝ}
    (ha : 0 < a) (_hc : 0 < c) (ha_def : a = c / 2)
    (hΦnn : 0 ≤ Φ)
    (hΦ : ∀ r : ℕ, r ≤ 2 → ∀ t : ℝ,
      ‖iteratedFDeriv ℝ r (smoothRightCutoff (c / 2) c) t‖ ≤ Φ)
    (hC₀nn : 0 ≤ C₀) (hC₁nn : 0 ≤ C₁) (hC₂nn : 0 ≤ C₂)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (hC₀ : ∀ t : ℝ, a ≤ t → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (srcSlice p (conjugatePicardIter p u₀ 0) t) k|
        ≤ C₀ / ((k : ℝ) * Real.pi) ^ 4)
    (hC₁ : ∀ t : ℝ, a ≤ t → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k|
        ≤ C₁ / ((k : ℝ) * Real.pi) ^ 2)
    (hC₂ : ∀ t : ℝ, a ≤ t → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs
        (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀) t) k|
        ≤ C₂ / ((k : ℝ) * Real.pi) ^ 2)
    {i k : ℕ} (hi : i ≤ 2) (hk : 1 ≤ k) {t : ℝ} :
    ‖iteratedFDeriv ℝ i
      (fun s : ℝ => smoothRightCutoff (c / 2) c s *
        resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s) t‖ ≤
      let W := ShenWork.PDE.intervalNeumannResolverWeight p k
      let E₀ := W * (C₀ / ((k : ℝ) * Real.pi) ^ 4)
      let E₁ := W * (C₁ / ((k : ℝ) * Real.pi) ^ 2)
      let E₂ := W * (C₂ / ((k : ℝ) * Real.pi) ^ 2)
      match i with
      | 0 => 4 * Φ * E₀
      | 1 => 4 * Φ * (E₀ + E₁)
      | _ => 4 * Φ * (E₀ + E₁ + E₂) := by
  classical
  let R : ℝ → ℝ := resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k
  let φ : ℝ → ℝ := smoothRightCutoff (c / 2) c
  set W : ℝ := ShenWork.PDE.intervalNeumannResolverWeight p k with hW_def
  set E₀ : ℝ := W * (C₀ / ((k : ℝ) * Real.pi) ^ 4) with hE₀_def
  set E₁ : ℝ := W * (C₁ / ((k : ℝ) * Real.pi) ^ 2) with hE₁_def
  set E₂ : ℝ := W * (C₂ / ((k : ℝ) * Real.pi) ^ 2) with hE₂_def
  have hWnn : 0 ≤ W := by
    rw [hW_def]
    exact ShenWork.PDE.intervalNeumannResolverWeight_nonneg p k
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  have hkπpos : 0 < (k : ℝ) * Real.pi := mul_pos hkpos Real.pi_pos
  have hE₀nn : 0 ≤ E₀ := by rw [hE₀_def]; positivity
  have hE₁nn : 0 ≤ E₁ := by rw [hE₁_def]; positivity
  have hE₂nn : 0 ≤ E₂ := by rw [hE₂_def]; positivity
  by_cases htleft : t < c / 2
  · have hev :
        (fun s : ℝ => smoothRightCutoff (c / 2) c s *
          resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s) =ᶠ[𝓝 t]
          fun _ : ℝ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds htleft] with s hs
      rw [smoothRightCutoff_eq_zero_of_le (by linarith : c / 2 < c) (le_of_lt hs)]
      ring
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [norm_iteratedFDeriv_zero, hev.eq_of_nhds, norm_zero]
      dsimp [E₀, W]
      positivity
    · have hzero := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev i).eq_of_nhds
      rw [hzero, iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hipos), Pi.zero_apply,
        norm_zero]
      interval_cases i <;> dsimp [E₀, E₁, E₂, W] <;> positivity
  · have ht_ge : a ≤ t := by
      rw [ha_def]
      exact le_of_not_gt htleft
    have htpos : 0 < t := lt_of_lt_of_le ha ht_ge
    have hφ_on : ContDiffOn ℝ (2 : ℕ∞) φ (Set.Ioi (0 : ℝ)) :=
      (smoothRightCutoff_contDiff (c' := c / 2) (c := c)).contDiffOn
    have hR_on : ContDiffOn ℝ (2 : ℕ∞) R (Set.Ioi (0 : ℝ)) := by
      refine (isOpen_Ioi.contDiffOn_iff).2 ?_
      intro s hs
      exact heatLevel0_resolverTimeCoeff_contDiffAt_two hu₀_bound hu₀_cont hfloor hs k
    have hR_bound : ∀ r : ℕ, r ≤ 2 →
        ‖iteratedFDeriv ℝ r R t‖ ≤
          match r with
          | 0 => E₀
          | 1 => E₁
          | _ => E₂ := by
      intro r hr
      have hbase := heatLevel0_resolverCoeff_iteratedFDeriv_tail_bound_posMode
        (p := p) (u₀ := u₀) (M₀ := M₀) (a := a) (C₀ := C₀) (C₁ := C₁) (C₂ := C₂)
        ha hu₀_bound hu₀_cont hfloor hC₀ hC₁ hC₂ hr hk ht_ge
      interval_cases r <;> simpa [R, E₀, E₁, E₂, W, hW_def, hE₀_def, hE₁_def, hE₂_def] using hbase
    have hprod := norm_iteratedFDeriv_mul_le_on_Ioi hφ_on hR_on htpos hi
    have hprod' :
        ‖iteratedFDeriv ℝ i
          (fun s : ℝ => smoothRightCutoff (c / 2) c s *
            resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s) t‖ ≤
        ∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ) *
          ‖iteratedFDeriv ℝ r φ t‖ *
          ‖iteratedFDeriv ℝ (i - r) R t‖ := by
      simpa [φ, R, mul_assoc] using hprod
    refine hprod'.trans ?_
    interval_cases i
    · norm_num [Finset.sum_range_succ]
      have hφ0 := hΦ 0 (by norm_num) t
      have hR0 := hR_bound 0 (by norm_num)
      have hφ0' : |φ t| ≤ Φ := by
        simpa [φ, norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hφ0
      have hR0' : ‖iteratedFDeriv ℝ 0 R t‖ ≤ E₀ := by
        simpa using hR0
      have hmul : |φ t| * ‖iteratedFDeriv ℝ 0 R t‖ ≤ Φ * E₀ :=
        mul_le_mul hφ0' hR0' (norm_nonneg _) (le_trans (abs_nonneg _) hφ0')
      nlinarith [hmul, hΦnn, hE₀nn]
    · norm_num [Finset.sum_range_succ]
      have hφ0 := hΦ 0 (by norm_num) t
      have hφ1 := hΦ 1 (by norm_num) t
      have hR0 := hR_bound 0 (by norm_num)
      have hR1 := hR_bound 1 (by norm_num)
      have hφ0' : |φ t| ≤ Φ := by
        simpa [φ, norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hφ0
      have hφ1' : ‖fderiv ℝ φ t‖ ≤ Φ := by
        rw [norm_iteratedFDeriv_one] at hφ1
        simpa [φ] using hφ1
      have hR0' : ‖iteratedFDeriv ℝ 0 R t‖ ≤ E₀ := by
        simpa using hR0
      have hR1' : ‖iteratedFDeriv ℝ 1 R t‖ ≤ E₁ := by
        simpa using hR1
      have hmul1 : |φ t| * ‖iteratedFDeriv ℝ 1 R t‖ ≤ Φ * E₁ :=
        mul_le_mul hφ0' hR1' (norm_nonneg _) (le_trans (abs_nonneg _) hφ0')
      have hmul0 : ‖fderiv ℝ φ t‖ * ‖iteratedFDeriv ℝ 0 R t‖ ≤ Φ * E₀ :=
        mul_le_mul hφ1' hR0' (norm_nonneg _) (le_trans (norm_nonneg _) hφ1')
      nlinarith [hmul0, hmul1, hΦnn, hE₀nn, hE₁nn]
    · norm_num [Finset.sum_range_succ]
      have hφ0 := hΦ 0 (by norm_num) t
      have hφ1 := hΦ 1 (by norm_num) t
      have hφ2 := hΦ 2 (by norm_num) t
      have hR0 := hR_bound 0 (by norm_num)
      have hR1 := hR_bound 1 (by norm_num)
      have hR2 := hR_bound 2 (by norm_num)
      have hφ0' : |φ t| ≤ Φ := by
        simpa [φ, norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hφ0
      have hφ1' : ‖fderiv ℝ φ t‖ ≤ Φ := by
        rw [norm_iteratedFDeriv_one] at hφ1
        simpa [φ] using hφ1
      have hφ2' : ‖iteratedFDeriv ℝ 2 φ t‖ ≤ Φ := by
        simpa [φ] using hφ2
      have hR0' : ‖iteratedFDeriv ℝ 0 R t‖ ≤ E₀ := by
        simpa using hR0
      have hR1' : ‖iteratedFDeriv ℝ 1 R t‖ ≤ E₁ := by
        simpa using hR1
      have hR2' : ‖iteratedFDeriv ℝ 2 R t‖ ≤ E₂ := by
        simpa using hR2
      have hmul2 : |φ t| * ‖iteratedFDeriv ℝ 2 R t‖ ≤ Φ * E₂ :=
        mul_le_mul hφ0' hR2' (norm_nonneg _) (le_trans (abs_nonneg _) hφ0')
      have hmul1 : ‖fderiv ℝ φ t‖ * ‖iteratedFDeriv ℝ 1 R t‖ ≤ Φ * E₁ :=
        mul_le_mul hφ1' hR1' (norm_nonneg _) (le_trans (norm_nonneg _) hφ1')
      have hmul0 : ‖iteratedFDeriv ℝ 2 φ t‖ * ‖iteratedFDeriv ℝ 0 R t‖ ≤ Φ * E₀ :=
        mul_le_mul hφ2' hR0' (norm_nonneg _) (le_trans (norm_nonneg _) hφ2')
      nlinarith [hmul0, hmul1, hmul2, hΦnn, hE₀nn, hE₁nn, hE₂nn]

private theorem heatLevel0_cutoffResolverCoeff_iteratedFDeriv_power_bound_posMode
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ a c Φ C₀ C₁ C₂ : ℝ}
    (ha : 0 < a) (hc : 0 < c) (ha_def : a = c / 2)
    (hΦnn : 0 ≤ Φ)
    (hΦ : ∀ r : ℕ, r ≤ 2 → ∀ t : ℝ,
      ‖iteratedFDeriv ℝ r (smoothRightCutoff (c / 2) c) t‖ ≤ Φ)
    (hC₀nn : 0 ≤ C₀) (hC₁nn : 0 ≤ C₁) (hC₂nn : 0 ≤ C₂)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (hC₀ : ∀ t : ℝ, a ≤ t → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (srcSlice p (conjugatePicardIter p u₀ 0) t) k|
        ≤ C₀ / ((k : ℝ) * Real.pi) ^ 4)
    (hC₁ : ∀ t : ℝ, a ≤ t → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k|
        ≤ C₁ / ((k : ℝ) * Real.pi) ^ 2)
    (hC₂ : ∀ t : ℝ, a ≤ t → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs
        (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀) t) k|
        ≤ C₂ / ((k : ℝ) * Real.pi) ^ 2)
    {i k : ℕ} (hi : i ≤ 2) (hk : 1 ≤ k) {t : ℝ} :
    ‖iteratedFDeriv ℝ i
      (fun s : ℝ => smoothRightCutoff (c / 2) c s *
        resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s) t‖ ≤
      heatLevel0GradCoeffPowerBt Φ C₀ C₁ C₂ i k := by
  classical
  have hbase := heatLevel0_cutoffResolverCoeff_iteratedFDeriv_tail_bound_posMode
    (p := p) (u₀ := u₀) (M₀ := M₀) (a := a) (c := c)
    (Φ := Φ) (C₀ := C₀) (C₁ := C₁) (C₂ := C₂)
    ha hc ha_def hΦnn hΦ hC₀nn hC₁nn hC₂nn
    hu₀_bound hu₀_cont hfloor hC₀ hC₁ hC₂ hi hk (t := t)
  set x : ℝ := (k : ℝ) * Real.pi with hx
  have hxpos : 0 < x := by
    rw [hx]
    exact mul_pos (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk) Real.pi_pos
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hW_le : ShenWork.PDE.intervalNeumannResolverWeight p k ≤ 1 / x ^ 2 := by
    rw [hx]
    exact resolverWeight_le_inv_kπ_sq p hk
  have hdiv₀nn : 0 ≤ C₀ / x ^ 4 := by positivity
  have hdiv₁nn : 0 ≤ C₁ / x ^ 2 := by positivity
  have hdiv₂nn : 0 ≤ C₂ / x ^ 2 := by positivity
  have hE₀_le :
      ShenWork.PDE.intervalNeumannResolverWeight p k * (C₀ / x ^ 4) ≤
        C₀ / x ^ 6 := by
    calc ShenWork.PDE.intervalNeumannResolverWeight p k * (C₀ / x ^ 4)
        ≤ (1 / x ^ 2) * (C₀ / x ^ 4) :=
            mul_le_mul_of_nonneg_right hW_le hdiv₀nn
      _ = C₀ / x ^ 6 := by field_simp [hxne]
  have hE₁_le :
      ShenWork.PDE.intervalNeumannResolverWeight p k * (C₁ / x ^ 2) ≤
        C₁ / x ^ 4 := by
    calc ShenWork.PDE.intervalNeumannResolverWeight p k * (C₁ / x ^ 2)
        ≤ (1 / x ^ 2) * (C₁ / x ^ 2) :=
            mul_le_mul_of_nonneg_right hW_le hdiv₁nn
      _ = C₁ / x ^ 4 := by field_simp [hxne]
  have hE₂_le :
      ShenWork.PDE.intervalNeumannResolverWeight p k * (C₂ / x ^ 2) ≤
        C₂ / x ^ 4 := by
    calc ShenWork.PDE.intervalNeumannResolverWeight p k * (C₂ / x ^ 2)
        ≤ (1 / x ^ 2) * (C₂ / x ^ 2) :=
            mul_le_mul_of_nonneg_right hW_le hdiv₂nn
      _ = C₂ / x ^ 4 := by field_simp [hxne]
  have h4Φnn : 0 ≤ 4 * Φ := by positivity
  have hkne : k ≠ 0 := Nat.ne_zero_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  interval_cases i
  · refine hbase.trans ?_
    simpa [heatLevel0GradCoeffPowerBt, hkne, x, hx, mul_assoc] using
      mul_le_mul_of_nonneg_left hE₀_le h4Φnn
  · refine hbase.trans ?_
    have hsum :
        ShenWork.PDE.intervalNeumannResolverWeight p k * (C₀ / x ^ 4) +
          ShenWork.PDE.intervalNeumannResolverWeight p k * (C₁ / x ^ 2) ≤
        C₀ / x ^ 6 + C₁ / x ^ 4 :=
      add_le_add hE₀_le hE₁_le
    simpa [heatLevel0GradCoeffPowerBt, hkne, x, hx, mul_add, mul_assoc] using
      mul_le_mul_of_nonneg_left hsum h4Φnn
  · refine hbase.trans ?_
    have hsum :
        ShenWork.PDE.intervalNeumannResolverWeight p k * (C₀ / x ^ 4) +
          ShenWork.PDE.intervalNeumannResolverWeight p k * (C₁ / x ^ 2) +
          ShenWork.PDE.intervalNeumannResolverWeight p k * (C₂ / x ^ 2) ≤
        C₀ / x ^ 6 + C₁ / x ^ 4 + C₂ / x ^ 4 :=
      add_le_add (add_le_add hE₀_le hE₁_le) hE₂_le
    simpa [heatLevel0GradCoeffPowerBt, hkne, x, hx, mul_add, mul_assoc] using
      mul_le_mul_of_nonneg_left hsum h4Φnn

/-! ### Layer 3: Cutoff × resolverTimeCoeff is globally C² -/

/-- The scalar cutoff resolver coefficient `φ(t) · resolverTimeCoeff(t)` is
globally `ContDiff ℝ 2`.  For `t < c/2` the cutoff kills the term; for
`t ≥ c/2 > 0` the resolver coefficient is `ContDiffAt ℝ 2`. -/
theorem cutoffResolverCoeff_contDiff_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ContDiff ℝ 2 (fun t =>
      smoothRightCutoff (c / 2) c t * resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : c / 2 ≤ t
  · have ht_pos : 0 < t := by linarith
    exact (smoothRightCutoff_contDiff (c' := c / 2) (c := c)).contDiffAt.mul
      (heatLevel0_resolverTimeCoeff_contDiffAt_two hu₀_bound hu₀_cont hfloor ht_pos k)
  · push_neg at ht
    have hev : (fun t => smoothRightCutoff (c / 2) c t *
        resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t) =ᶠ[𝓝 t]
        fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      have : smoothRightCutoff (c / 2) c s = 0 :=
        smoothRightCutoff_eq_zero_of_le (by linarith : c / 2 < c) (le_of_lt hs)
      simp [this]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-! ### Layer 4: Per-term C² in (t,x) -/

/-- Each cutoff resolver term is C² in `(t,x)`.
Decomposition: `cutoffResolverTerm = (φ·resolverCoeff) ∘ fst * cosineMode ∘ snd`.
The scalar part is globally C² (Layer 3), cosineMode is C∞. -/
theorem cutoffResolverTerm_contDiff_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ContDiff ℝ 2 (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) := by
  have hcoef := cutoffResolverCoeff_contDiff_two hu₀_bound hu₀_cont hfloor hc k
  have hcoef_q : ContDiff ℝ 2 (fun q : ℝ × ℝ =>
      smoothRightCutoff (c / 2) c q.1 *
        resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k q.1) :=
    hcoef.comp contDiff_fst
  have hcos : ContDiff ℝ 2 (cosineMode k) := by
    unfold cosineMode; fun_prop
  have hcos_q : ContDiff ℝ 2 (fun q : ℝ × ℝ => cosineMode k q.2) :=
    hcos.comp contDiff_snd
  simpa [cutoffResolverTerm, mul_assoc] using hcoef_q.mul hcos_q

/-- Each cutoff gradient resolver term is C² in `(t,x)`. -/
theorem cutoffResolverGradTerm_contDiff_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ContDiff ℝ 2 (cutoffResolverGradTerm p (conjugatePicardIter p u₀ 0) c k) := by
  have hcoef := cutoffResolverCoeff_contDiff_two hu₀_bound hu₀_cont hfloor hc k
  have hcoef_q : ContDiff ℝ 2 (fun q : ℝ × ℝ =>
      smoothRightCutoff (c / 2) c q.1 *
        resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k q.1) :=
    hcoef.comp contDiff_fst
  have hcosd : ContDiff ℝ 2 (fun y : ℝ => deriv (cosineMode k) y) := by
    have hEq : (fun y : ℝ => deriv (cosineMode k) y) =
        fun y : ℝ => -((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * y) := by
      funext y
      rw [ShenWork.CosineSpectrum.cosineMode_deriv]
    rw [hEq]
    fun_prop
  have hcosd_q : ContDiff ℝ 2 (fun q : ℝ × ℝ => deriv (cosineMode k) q.2) :=
    hcosd.comp contDiff_snd
  simpa [cutoffResolverGradTerm, mul_assoc] using hcoef_q.mul hcosd_q

/-- Mechanical cutoff-value series assembler from explicit coefficient bounds.

This is the value-series companion of `cutoffResolverGradSeries_contDiff_two_of_Bt`.
It consumes direct bounds for the scalar cutoff coefficients
`φ(t) * resolverTimeCoeff(k,t)` and the summability of the corresponding
`valueCosWeight` majorants; no resolver data structure is used. -/
theorem cutoffResolverSeries_contDiff_two_of_Bt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) {Bt : ℕ → ℕ → ℝ}
    (hBt : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
      ‖iteratedFDeriv ℝ i
        (fun s : ℝ => smoothRightCutoff (c / 2) c s *
          resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s) t‖ ≤ Bt i k)
    (hsumm : ∀ j : ℕ, (j : ℕ∞) ≤ 2 →
      Summable (boundedWeightJointMajorant Bt j)) :
    ContDiff ℝ 2 (fun q : ℝ × ℝ =>
      ∑' k : ℕ, cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k q) := by
  let coeff : ℕ → ℝ → ℝ := fun k s =>
    smoothRightCutoff (c / 2) c s *
      resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s
  have hcoeff : ∀ k, ContDiff ℝ (2 : ℕ∞) (coeff k) := by
    intro k
    exact cutoffResolverCoeff_contDiff_two hu₀_bound hu₀_cont hfloor hc k
  have hBt' : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
      ‖iteratedFDeriv ℝ i (coeff k) t‖ ≤ Bt i k := by
    intro i k t hi
    simpa [coeff] using hBt i k t hi
  have hseries : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' k : ℕ, boundedWeightJointTerm coeff k q) :=
    ShenWork.IntervalResolverJointC2Physical.boundedWeightJointSeries_contDiff_two
      (c := coeff) (Bt := Bt) hcoeff hBt' hsumm
  simpa [cutoffResolverTerm, boundedWeightJointTerm, coeff, mul_assoc] using hseries

/-- Value-series assembler with positive-mode coefficient bounds only.  The zero
mode is kept as one separate C² term; all summability obligations are on the
positive-mode series. -/
theorem cutoffResolverSeries_contDiff_two_posModes_of_Bt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) {Bt : ℕ → ℕ → ℝ}
    (hBt : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 → 1 ≤ k →
      ‖iteratedFDeriv ℝ i
        (fun s : ℝ => smoothRightCutoff (c / 2) c s *
          resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s) t‖ ≤ Bt i k)
    (hsumm : ∀ j : ℕ, (j : ℕ∞) ≤ 2 →
      Summable (boundedWeightJointMajorant
        (fun i k => if k = 0 then 0 else Bt i k) j)) :
    ContDiff ℝ 2 (fun q : ℝ × ℝ =>
      ∑' k : ℕ, cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k q) := by
  classical
  let coeff : ℕ → ℝ → ℝ := fun k s =>
    if k = 0 then 0 else
      smoothRightCutoff (c / 2) c s *
        resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s
  let Btp : ℕ → ℕ → ℝ := fun i k => if k = 0 then 0 else Bt i k
  have hcoeff : ∀ k, ContDiff ℝ (2 : ℕ∞) (coeff k) := by
    intro k
    by_cases hk : k = 0
    · subst k
      simpa [coeff] using (contDiff_const : ContDiff ℝ (2 : ℕ∞) (fun _ : ℝ => (0 : ℝ)))
    · simpa [coeff, hk] using cutoffResolverCoeff_contDiff_two
        (p := p) (u₀ := u₀) (M₀ := M₀) hu₀_bound hu₀_cont hfloor hc k
  have hBt' : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
      ‖iteratedFDeriv ℝ i (coeff k) t‖ ≤ Btp i k := by
    intro i k t hi
    by_cases hk : k = 0
    · subst k
      simp [coeff, Btp]
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      simpa [coeff, Btp, hk] using hBt i k t hi hk1
  have hseriesPos : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' k : ℕ, boundedWeightJointTerm coeff k q) :=
    ShenWork.IntervalResolverJointC2Physical.boundedWeightJointSeries_contDiff_two
      (c := coeff) (Bt := Btp) hcoeff hBt' (by simpa [Btp] using hsumm)
  have hzero : ContDiff ℝ (2 : ℕ∞)
      (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c 0) :=
    cutoffResolverTerm_contDiff_two (p := p) (u₀ := u₀) (M₀ := M₀)
      hu₀_bound hu₀_cont hfloor hc 0
  have hsumEq : (fun q : ℝ × ℝ =>
      ∑' k : ℕ, cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k q) =
      fun q : ℝ × ℝ =>
        cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c 0 q +
          ∑' k : ℕ, boundedWeightJointTerm coeff k q := by
    funext q
    have hmaj0 : Summable (fun k : ℕ => Btp 0 k) :=
      (hsumm 0 (by norm_num)).congr fun k => valueMajorant_zero_eq Btp k
    have hactual_bound : ∀ k : ℕ, 1 ≤ k →
        ‖cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k q‖ ≤ Btp 0 k := by
      intro k hk
      have hcoef := hBt 0 k q.1 (by norm_num) hk
      have hcoef_abs :
          |smoothRightCutoff (c / 2) c q.1 *
              resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k q.1| ≤ Bt 0 k := by
        simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hcoef
      have hcos : |cosineMode k q.2| ≤ 1 := by
        unfold cosineMode
        exact Real.abs_cos_le_one _
      calc ‖cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k q‖
          = |(smoothRightCutoff (c / 2) c q.1 *
              resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k q.1) *
              cosineMode k q.2| := by
                simp [cutoffResolverTerm, Real.norm_eq_abs, mul_assoc]
        _ ≤ |smoothRightCutoff (c / 2) c q.1 *
              resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k q.1| := by
                rw [abs_mul]
                exact (mul_le_mul_of_nonneg_left hcos (abs_nonneg _)).trans
                  (by rw [mul_one])
        _ ≤ Bt 0 k := hcoef_abs
        _ = Btp 0 k := by
          have hk0 : k ≠ 0 := Nat.ne_zero_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
          simp [Btp, hk0]
    have hcoeff_bound : ∀ k : ℕ, ‖boundedWeightJointTerm coeff k q‖ ≤ Btp 0 k := by
      intro k
      by_cases hk0 : k = 0
      · subst k
        simp [boundedWeightJointTerm, coeff, Btp]
      · simpa [boundedWeightJointTerm, cutoffResolverTerm, coeff, hk0, mul_assoc] using
          hactual_bound k (Nat.one_le_iff_ne_zero.mpr hk0)
    have htail : Summable (fun n : ℕ =>
        cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c (n + 1) q) := by
      refine Summable.of_norm_bounded
        ((summable_nat_add_iff (f := fun k : ℕ => Btp 0 k) 1).2 hmaj0) ?_
      intro n
      exact hactual_bound (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    have hf : Summable (fun k : ℕ =>
        cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k q) :=
      (summable_nat_add_iff
        (f := fun k : ℕ => cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k q)
        1).1 htail
    have hg : Summable (fun k : ℕ => boundedWeightJointTerm coeff k q) :=
      Summable.of_norm_bounded hmaj0 hcoeff_bound
    rw [hf.tsum_eq_zero_add, hg.tsum_eq_zero_add]
    simp [boundedWeightJointTerm, coeff]
    congr 1
    funext n
    simp [cutoffResolverTerm, mul_assoc]
  rw [hsumEq]
  exact hzero.add hseriesPos

/-- Mechanical cutoff-gradient series assembler from explicit coefficient bounds.

The remaining analytic input is `hBt` plus summability of the corresponding
`gradCosWeight` majorants.  No resolver data structure is used here. -/
theorem cutoffResolverGradSeries_contDiff_two_of_Bt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) {Bt : ℕ → ℕ → ℝ}
    (hBt : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
      ‖iteratedFDeriv ℝ i
        (fun s : ℝ => smoothRightCutoff (c / 2) c s *
          resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s) t‖ ≤ Bt i k)
    (hsumm : ∀ j : ℕ, (j : ℕ∞) ≤ 2 →
      Summable (boundedWeightJointGradMajorant Bt j)) :
    ContDiff ℝ 2 (fun q : ℝ × ℝ =>
      ∑' k : ℕ, cutoffResolverGradTerm p (conjugatePicardIter p u₀ 0) c k q) := by
  let coeff : ℕ → ℝ → ℝ := fun k s =>
    smoothRightCutoff (c / 2) c s *
      resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s
  have hcoeff : ∀ k, ContDiff ℝ (2 : ℕ∞) (coeff k) := by
    intro k
    exact cutoffResolverCoeff_contDiff_two hu₀_bound hu₀_cont hfloor hc k
  have hBt' : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
      ‖iteratedFDeriv ℝ i (coeff k) t‖ ≤ Bt i k := by
    intro i k t hi
    simpa [coeff] using hBt i k t hi
  have hseries : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' k : ℕ, boundedWeightJointGradTerm coeff k q) :=
    boundedWeightJointGradSeries_contDiff_two (c := coeff) (Bt := Bt)
      hcoeff hBt' hsumm
  simpa [cutoffResolverGradTerm, boundedWeightJointGradTerm, coeff, mul_assoc] using hseries

/-- Same as `cutoffResolverGradSeries_contDiff_two_of_Bt`, but the coefficient
majorant is required only on positive Fourier modes.  The zero mode contributes
no spatial-gradient term, so the proof replaces its coefficient by zero before
calling the bounded-weight gradient assembler. -/
theorem cutoffResolverGradSeries_contDiff_two_posModes_of_Bt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) {Bt : ℕ → ℕ → ℝ}
    (hBt : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 → 1 ≤ k →
      ‖iteratedFDeriv ℝ i
        (fun s : ℝ => smoothRightCutoff (c / 2) c s *
          resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s) t‖ ≤ Bt i k)
    (hsumm : ∀ j : ℕ, (j : ℕ∞) ≤ 2 →
      Summable (boundedWeightJointGradMajorant
        (fun i k => if k = 0 then 0 else Bt i k) j)) :
    ContDiff ℝ 2 (fun q : ℝ × ℝ =>
      ∑' k : ℕ, cutoffResolverGradTerm p (conjugatePicardIter p u₀ 0) c k q) := by
  classical
  let coeff : ℕ → ℝ → ℝ := fun k s =>
    if k = 0 then 0 else
      smoothRightCutoff (c / 2) c s *
        resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s
  let Btp : ℕ → ℕ → ℝ := fun i k => if k = 0 then 0 else Bt i k
  have hcoeff : ∀ k, ContDiff ℝ (2 : ℕ∞) (coeff k) := by
    intro k
    by_cases hk : k = 0
    · subst k
      simpa [coeff] using (contDiff_const : ContDiff ℝ (2 : ℕ∞) (fun _ : ℝ => (0 : ℝ)))
    · simpa [coeff, hk] using cutoffResolverCoeff_contDiff_two
        (p := p) (u₀ := u₀) (M₀ := M₀) hu₀_bound hu₀_cont hfloor hc k
  have hBt' : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
      ‖iteratedFDeriv ℝ i (coeff k) t‖ ≤ Btp i k := by
    intro i k t hi
    by_cases hk : k = 0
    · subst k
      simp [coeff, Btp]
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      simpa [coeff, Btp, hk] using hBt i k t hi hk1
  have hseries : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' k : ℕ, boundedWeightJointGradTerm coeff k q) :=
    boundedWeightJointGradSeries_contDiff_two (c := coeff) (Bt := Btp)
      hcoeff hBt' (by simpa [Btp] using hsumm)
  have heq : (fun q : ℝ × ℝ =>
      ∑' k : ℕ, cutoffResolverGradTerm p (conjugatePicardIter p u₀ 0) c k q) =
      fun q : ℝ × ℝ => ∑' k : ℕ, boundedWeightJointGradTerm coeff k q := by
    funext q
    apply tsum_congr
    intro k
    by_cases hk : k = 0
    · subst k
      simp [cutoffResolverGradTerm, boundedWeightJointGradTerm, coeff,
        ShenWork.CosineSpectrum.cosineMode_deriv]
    · simp [cutoffResolverGradTerm, boundedWeightJointGradTerm, coeff, hk, mul_assoc]
  rw [heq]
  exact hseries

/-! ### Summable majorant (analytic content) -/

/-- The majorant for the cutoff resolver term at order `j`:
a nonneg summable sequence bounding `‖D^j(cutoffResolverTerm)‖` uniformly in `q`.

The majorant shape is:
`v j k = C_φ(j) · C_resolverCoeff(j,k) · cos_factor(j-i,k)`
where the resolver coefficient contribution decays as `1/(μ+λ_k)` times bounded
source coefficients, giving overall summability from the elliptic weight. -/
noncomputable def cutoffResolverMajorant (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (_M₀ c : ℝ) (_hc : 0 < c)
    (j k : ℕ) : ℝ :=
  ⨆ q : ℝ × ℝ, ‖iteratedFDeriv ℝ j
    (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖

private theorem resolverSmoothRightCutoff_iteratedFDeriv_bound_exists
    (c' c : ℝ) (hc'c : c' < c) (k : ℕ) (hk : (k : ℕ∞) ≤ 2) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : ℝ, ‖iteratedFDeriv ℝ k (smoothRightCutoff c' c) t‖ ≤ B := by
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · refine ⟨1, zero_le_one, fun t => ?_⟩
    rw [norm_iteratedFDeriv_zero]
    unfold smoothRightCutoff
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  · have hcont : Continuous
        (fun t : ℝ => iteratedFDeriv ℝ k (smoothRightCutoff c' c) t) :=
      smoothRightCutoff_contDiff.continuous_iteratedFDeriv (by exact_mod_cast hk)
    have hk_ne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk_pos
    have hzero : ∀ t, t ∉ Set.Icc c' c →
        iteratedFDeriv ℝ k (smoothRightCutoff c' c) t = 0 := by
      intro t ht
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
      rcases ht with ht_lt | ht_gt
      · have hev : smoothRightCutoff c' c =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
          filter_upwards [Iio_mem_nhds ht_lt] with s hs
          exact smoothRightCutoff_eq_zero_of_le hc'c (le_of_lt hs)
        have := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev k).eq_of_nhds
        rwa [iteratedFDeriv_const_of_ne hk_ne, Pi.zero_apply] at this
      · have hev : smoothRightCutoff c' c =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
          filter_upwards [Ioi_mem_nhds ht_gt] with s hs
          exact smoothRightCutoff_eq_one_of_ge hc'c (le_of_lt hs)
        have := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev k).eq_of_nhds
        rwa [iteratedFDeriv_const_of_ne hk_ne, Pi.zero_apply] at this
    have hcomp : HasCompactSupport
        (fun t : ℝ => iteratedFDeriv ℝ k (smoothRightCutoff c' c) t) :=
      HasCompactSupport.intro' isCompact_Icc isClosed_Icc hzero
    rcases hcont.bounded_above_of_compact_support hcomp with ⟨C, hC⟩
    exact ⟨max C 0, le_max_right C 0, fun t => (hC t).trans (le_max_left C 0)⟩

private noncomputable def resolverSmoothRightCutoffDerivBound
    (c' c : ℝ) (hc'c : c' < c) (k : ℕ) (hk : (k : ℕ∞) ≤ 2) : ℝ :=
  Classical.choose
    (resolverSmoothRightCutoff_iteratedFDeriv_bound_exists c' c hc'c k hk)

private theorem resolverSmoothRightCutoffDerivBound_nonneg
    {c' c : ℝ} (hc'c : c' < c) {k : ℕ} (hk : (k : ℕ∞) ≤ 2) :
    0 ≤ resolverSmoothRightCutoffDerivBound c' c hc'c k hk :=
  (Classical.choose_spec
    (resolverSmoothRightCutoff_iteratedFDeriv_bound_exists c' c hc'c k hk)).1

private theorem resolverSmoothRightCutoffDerivBound_spec
    {c' c : ℝ} (hc'c : c' < c) {k : ℕ} (hk : (k : ℕ∞) ≤ 2) (t : ℝ) :
    ‖iteratedFDeriv ℝ k (smoothRightCutoff c' c) t‖ ≤
      resolverSmoothRightCutoffDerivBound c' c hc'c k hk :=
  (Classical.choose_spec
    (resolverSmoothRightCutoff_iteratedFDeriv_bound_exists c' c hc'c k hk)).2 t

/-! ### Direct BddAbove -/

/-- Generic BddAbove from left-zero/mid/tail decomposition. -/
private theorem bddAbove_range_of_left_mid_tail
    {g : ℝ × ℝ → ℝ} {a : ℝ} {Cmid Ctail : ℝ}
    (hleft : ∀ q : ℝ × ℝ, q.1 < a → g q = 0)
    (hmid : ∀ q : ℝ × ℝ, a ≤ q.1 → q.1 ≤ a + 1 → g q ≤ Cmid)
    (htail : ∀ q : ℝ × ℝ, a + 1 < q.1 → g q ≤ Ctail) :
    BddAbove (Set.range g) := by
  refine ⟨max 0 (max Cmid Ctail), ?_⟩
  rintro _ ⟨q, rfl⟩
  by_cases hqa : q.1 < a
  · rw [hleft q hqa]; exact le_max_left 0 _
  · push_neg at hqa
    by_cases hqb : q.1 ≤ a + 1
    · exact (hmid q hqa hqb).trans ((le_max_left Cmid Ctail).trans (le_max_right 0 _))
    · push_neg at hqb
      exact (htail q hqb).trans ((le_max_right Cmid Ctail).trans (le_max_right 0 _))

set_option maxHeartbeats 800000 in
/-- BddAbove of the cutoff resolver term iteratedFDeriv norm, proved directly
from the product structure A(t) · B(x).
Uses: left zero (cutoff), mid compact (compactness in t × cosine bound in x),
tail explicit (L∞ contraction + eigenvalue damping). -/
private theorem cutoffResolverMajorant_bddAbove_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (j k : ℕ) (hj : (j : ℕ∞) ≤ 2) :
    BddAbove (Set.range fun q : ℝ × ℝ =>
      ‖iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖) := by
  set f := cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k with hf_def
  have hfC2 := cutoffResolverTerm_contDiff_two hu₀_bound hu₀_cont hfloor hc k
  have hcont : Continuous (fun q : ℝ × ℝ => ‖iteratedFDeriv ℝ j f q‖) :=
    (hfC2.continuous_iteratedFDeriv (by exact_mod_cast hj)).norm
  -- Factor: f(t,x) = A(t) · B(x) where A = φ·resolverCoeff, B = cosineMode k
  set A := fun t : ℝ =>
    smoothRightCutoff (c / 2) c t * resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t
  have hAC2 := cutoffResolverCoeff_contDiff_two hu₀_bound hu₀_cont hfloor hc k
  -- Left zero: f = 0 for t < c/2
  have hleft : ∀ q : ℝ × ℝ, q.1 < c / 2 →
      ‖iteratedFDeriv ℝ j f q‖ = 0 := by
    intro q hq
    have hev : f =ᶠ[𝓝 q] fun _ => (0 : ℝ) := by
      have hmem : (Set.Iio (c / 2)) ×ˢ (Set.univ : Set ℝ) ∈ 𝓝 q :=
        (isOpen_Iio.prod isOpen_univ).mem_nhds ⟨hq, Set.mem_univ _⟩
      filter_upwards [hmem] with r hr
      obtain ⟨hr1, _⟩ := Set.mem_prod.mp hr
      show cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k r = 0
      unfold cutoffResolverTerm
      rw [smoothRightCutoff_eq_zero_of_le (by linarith : c / 2 < c) (le_of_lt hr1)]
      ring
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · rw [norm_iteratedFDeriv_zero, hev.eq_of_nhds, norm_zero]
    · have := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev j).eq_of_nhds
      rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hjpos), Pi.zero_apply] at this
      rw [this, norm_zero]
  -- Mid bound: compact time [c/2, c/2+1], global cosine bound
  -- Use: A is C² → continuous iteratedFDeriv → bounded on compact [c/2, c/2+1]
  -- Cosine mode derivatives bounded by valueCosWeight
  -- Leibniz gives product bound
  have hmid : ∃ Cmid : ℝ, ∀ q : ℝ × ℝ, c / 2 ≤ q.1 → q.1 ≤ c / 2 + 1 →
      ‖iteratedFDeriv ℝ j f q‖ ≤ Cmid := by
    -- Factor f = (A ∘ fst) · (cosineMode k ∘ snd)
    have hcos : ContDiff ℝ (2 : ℕ∞) (cosineMode k) := by unfold cosineMode; fun_prop
    have hjNat : j ≤ 2 := by exact_mod_cast hj
    -- Get compact-time bound on each order of iteratedFDeriv of A
    -- For i ≤ 2: ∃ C_i, ∀ t ∈ [c/2, c/2+1], ‖iteratedFDeriv ℝ i A t‖ ≤ C_i
    have hA_bounds : ∀ i : ℕ, i ≤ 2 →
        ∃ C_i : ℝ, ∀ t ∈ Set.Icc (c / 2) (c / 2 + 1),
          ‖iteratedFDeriv ℝ i A t‖ ≤ C_i := by
      intro i hi
      have hcont_i : Continuous (fun t : ℝ => iteratedFDeriv ℝ i A t) :=
        hAC2.continuous_iteratedFDeriv (by exact_mod_cast hi)
      exact isCompact_Icc.exists_bound_of_continuousOn hcont_i.continuousOn
    -- For each i ≤ j ≤ 2, extract the compact-time bound C_i
    -- and the cosine mode bound valueCosWeight(j-i, k)
    -- Define Cmid as the Leibniz sum
    -- We need A ∘ fst and cosineMode k ∘ snd to be C²
    have hAfst : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => A q.1) :=
      hAC2.comp contDiff_fst
    have hBsnd : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => cosineMode k q.2) :=
      hcos.comp contDiff_snd
    have hjTop : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast hj
    -- The factoring: f = (A ∘ fst) * (cosineMode k ∘ snd)
    have hfactor : f = fun q : ℝ × ℝ => A q.1 * cosineMode k q.2 := by
      funext q; simp [hf_def, cutoffResolverTerm, A, mul_assoc]
    -- Get a uniform C_max bounding all iteratedFDeriv orders of A on [c/2, c/2+1]
    have ⟨C_max, hC_max⟩ : ∃ C_max : ℝ, ∀ (i : ℕ), i ≤ 2 →
        ∀ t ∈ Set.Icc (c / 2) (c / 2 + 1),
          ‖iteratedFDeriv ℝ i A t‖ ≤ C_max := by
      obtain ⟨c0, hc0⟩ := hA_bounds 0 (by omega)
      obtain ⟨c1, hc1⟩ := hA_bounds 1 (by omega)
      obtain ⟨c2, hc2⟩ := hA_bounds 2 (by omega)
      refine ⟨max c0 (max c1 c2), fun i hi t ht => ?_⟩
      interval_cases i
      · exact (hc0 t ht).trans (le_max_left _ _)
      · exact (hc1 t ht).trans ((le_max_left _ _).trans (le_max_right _ _))
      · exact (hc2 t ht).trans ((le_max_right _ _).trans (le_max_right _ _))
    -- The explicit bound: Σ C(j,i) * C_max * valueCosWeight(j-i, k)
    set Cmid := ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * C_max *
        ShenWork.IntervalResolverSpectralJointC2Concrete.valueCosWeight (j - i) k
    refine ⟨Cmid, fun q hq_lo hq_hi => ?_⟩
    rw [hfactor]
    calc ‖iteratedFDeriv ℝ j (fun q : ℝ × ℝ => A q.1 * cosineMode k q.2) q‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => A q.1) q‖ *
            ‖iteratedFDeriv ℝ (j - i) (fun q : ℝ × ℝ => cosineMode k q.2) q‖ := by
          simpa [mul_assoc] using norm_iteratedFDeriv_mul_le hAfst hBsnd q hjTop
      _ ≤ Cmid := by
          apply Finset.sum_le_sum
          intro i hi
          have hik : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hiNat : i ≤ 2 := le_trans hik hjNat
          have hjiNat : j - i ≤ 2 := le_trans (Nat.sub_le j i) hjNat
          have hiTop' : (i : ℕ∞) ≤ (2 : ℕ∞) := by exact_mod_cast hiNat
          have hjiTop : ((j - i : ℕ) : ℕ∞) ≤ (2 : ℕ∞) := by exact_mod_cast hjiNat
          have hiCast : ((i : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
            exact_mod_cast hiNat
          have hjiCast : (((j - i : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
            exact_mod_cast hjiNat
          have hA_fst_bound : ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => A q.1) q‖ ≤ C_max := by
            exact (norm_iteratedFDeriv_comp_fst_le hAC2 hiCast q).trans
              (hC_max i hiNat q.1 ⟨hq_lo, hq_hi⟩)
          have hB_snd_bound : ‖iteratedFDeriv ℝ (j - i)
              (fun q : ℝ × ℝ => cosineMode k q.2) q‖ ≤
              ShenWork.IntervalResolverSpectralJointC2Concrete.valueCosWeight (j - i) k := by
            exact (ShenWork.IntervalResolverSpectralJointC2CutoffBounds.norm_iteratedFDeriv_comp_snd_le
              hcos hjiCast q).trans
              (ShenWork.IntervalResolverSpectralJointC2Concrete.cosineMode_iteratedFDeriv_bound
                k (j - i) q.2 hjiNat)
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hA_fst_bound (Nat.cast_nonneg _))
            hB_snd_bound (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (le_trans (norm_nonneg _) hA_fst_bound))
  -- Tail bound: for t > c/2+1, use explicit L∞ bounds
  have htail : ∃ Ctail : ℝ, ∀ q : ℝ × ℝ, c / 2 + 1 < q.1 →
      ‖iteratedFDeriv ℝ j f q‖ ≤ Ctail := by
    -- Same Leibniz structure as hmid. The time part A is C², so
    -- iteratedFDeriv is continuous on [c/2, ∞). We extend the compact bound
    -- to [c/2, c/2+2] which covers all t ∈ (c/2+1, c/2+2]. For t > c/2+2,
    -- we chain further compact intervals.
    -- For now: use a SINGLE large compact interval [c/2, c/2+2] which
    -- covers the boundary. For the true tail, we use the L∞ bound.
    -- APPROACH: identical to hmid but on [c/2, c/2 + 2] for the compact bound,
    -- combined with the observation that the hmid bound already covers [c/2, c/2+1]
    -- and for t > c/2+1 the cutoff is 1 so A = resolverTimeCoeff.
    -- The iteratedFDeriv of A is uniformly bounded because:
    -- (i=0) |A(t)| ≤ w_k * 2ν*‖u₀‖^γ from L∞ contraction
    -- (i≥1) |A^(i)(t)| is bounded from eigenvalue damping + max principle
    -- These bounds are UNIFORM in t ≥ c/2 (not just on a compact set).
    -- For a clean proof without eigenvalue damping infrastructure, we
    -- observe: A is C², A(t) → L (finite limit), A'(t) → 0, A''(t) → 0
    -- as t → ∞. A continuous function on [c/2, ∞) with a finite limit at ∞
    -- is bounded. Same for A', A''.
    -- For now, we use the compact argument on a SUFFICIENTLY LARGE interval.
    have hcos : ContDiff ℝ (2 : ℕ∞) (cosineMode k) := by unfold cosineMode; fun_prop
    have hjNat : j ≤ 2 := by exact_mod_cast hj
    -- Uniform bound on A's iteratedFDeriv for all t (using continuous + zero-at-left + bounded-at-right)
    have hA_global_bounds : ∀ i : ℕ, i ≤ 2 →
        ∃ B_i : ℝ, ∀ t : ℝ, ‖iteratedFDeriv ℝ i A t‖ ≤ B_i := by
      intro i hi
      interval_cases i
      · -- i = 0: |A(t)| ≤ 1 · w_k · 2ν · M^γ from L∞ contraction
        -- A(t) = φ(t) · resolverTimeCoeff(k,t), |φ| ≤ 1
        -- |resolverTimeCoeff| ≤ w_k · |srcTimeCoeff| ≤ w_k · 2ν · M^γ
        -- where M bounds |u₀| (continuous on compact → bounded)
        haveI : CompactSpace intervalDomainPoint :=
          isCompact_iff_compactSpace.mp isCompact_Icc
        haveI : Nonempty intervalDomainPoint :=
          ⟨⟨0, Set.left_mem_Icc.mpr (by norm_num)⟩⟩
        -- Get sup bound M on |u₀|
        obtain ⟨x_max, _, hx_max⟩ := IsCompact.exists_isMaxOn isCompact_univ
          Set.univ_nonempty (hu₀_cont.norm.continuousOn)
        set M_sup := ‖u₀ x_max‖ with hM_sup_def
        have hM_sup_nn : 0 ≤ M_sup := norm_nonneg _
        have hu₀_le : ∀ x : intervalDomainPoint, ‖u₀ x‖ ≤ M_sup := by
          intro x; exact hx_max (Set.mem_univ x)
        -- |intervalDomainLift u₀ y| ≤ M_sup for all y ∈ ℝ
        have hlift_le : ∀ y : ℝ, |intervalDomainLift u₀ y| ≤ M_sup := by
          intro y; unfold intervalDomainLift; split
          · exact Real.norm_eq_abs _ ▸ hu₀_le ⟨y, ‹_›⟩
          · simp [abs_of_nonneg, hM_sup_nn]
        -- L∞ contraction: |S(t)u₀(x)| ≤ M_sup for t > 0
        have hSt_le : ∀ t : ℝ, 0 < t → ∀ x : ℝ,
            |ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
              t (intervalDomainLift u₀) x| ≤ M_sup :=
          fun t ht x =>
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
              ht hM_sup_nn hlift_le x
        -- For i=0: ‖iteratedFDeriv ℝ 0 A t‖ = |A t|
        -- Split: t ≤ c/2 → A=0, t > c/2 → bound from L∞ chain
        -- Use compact [c/2, c/2+1] for the transition + L∞ tail for t > c/2+1
        -- SIMPLIFICATION: just use compact bound on [c/2, c/2+2] combined with
        -- A=0 on the left. For t > c/2+2: use L∞ bound.
        have hA_cont : Continuous A := hAC2.continuous
        -- Compact bound on [c/2, c/2+2]
        obtain ⟨B_compact, hB_compact⟩ := (isCompact_Icc (a := c / 2) (b := c + 1)).exists_bound_of_continuousOn
          hA_cont.continuousOn
        -- L∞ tail bound: for t > 0, |S(t)u₀(x)| ≤ M_sup → srcSlice bounded → srcTimeCoeff bounded
        -- For the tail, we need ContinuousOn of srcSlice on [0,1] + |srcSlice| ≤ ν * M_sup^γ
        -- ContinuousOn follows from hSt_cont + rpow continuity at positive values
        -- For now, we sorry the tail bound and combine with the compact bound
        have hA_tail : ∃ B_tail : ℝ, ∀ t : ℝ, c + 1 < t →
            |A t| ≤ B_tail := by
          set u := conjugatePicardIter p u₀ 0
          set w_k := ShenWork.PDE.intervalNeumannResolverWeight p k
          refine ⟨|w_k| * (2 * p.ν * M_sup ^ p.γ), fun t ht => ?_⟩
          -- Step 1: φ(t) = 1 for t > c+1 > c
          have ht_ge_c : c ≤ t := by linarith
          have hφ_one : smoothRightCutoff (c / 2) c t = 1 :=
            smoothRightCutoff_eq_one_of_ge (by linarith : c / 2 < c) ht_ge_c
          -- Step 2: |A(t)| = |resolverTimeCoeff(k,t)|
          show |smoothRightCutoff (c / 2) c t * resolverTimeCoeff p u k t| ≤ _
          rw [hφ_one, one_mul]
          -- Step 3: |resolverTimeCoeff| = |w_k * srcTimeCoeff|
          rw [resolverTimeCoeff_eq_weight_smul p u k t, abs_mul]
          -- Step 4: bound |srcTimeCoeff|
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          -- Goal: |srcTimeCoeff p u k t| ≤ 2 * p.ν * M_sup ^ p.γ
          rw [srcTimeCoeff_eq_cosineCoeffs p u k t]
          -- Goal: |cosineCoeffs (srcSlice p u t) k| ≤ 2 * p.ν * M_sup ^ p.γ
          have ht_pos : 0 < t := by linarith
          -- Pointwise bound: |srcSlice(t,x)| ≤ ν * M_sup^γ on [0,1]
          have hsrc_bound : ∀ x ∈ Set.Icc (0:ℝ) 1,
              |srcSlice p u t x| ≤ p.ν * M_sup ^ p.γ := by
            intro x hx
            unfold srcSlice
            rw [abs_of_nonneg (mul_nonneg (le_of_lt p.hν) (Real.rpow_nonneg
              (le_of_lt (hfloor t ht_pos x hx)) _))]
            apply mul_le_mul_of_nonneg_left _ (le_of_lt p.hν)
            apply Real.rpow_le_rpow (le_of_lt (hfloor t ht_pos x hx))
            · -- S(t)u₀(x) ≤ M_sup from L∞ contraction + positivity
              -- intervalDomainLift(u t)(x) = u t ⟨x,hx⟩ = S(t)(lift u₀)(x) for x ∈ [0,1]
              have hdef : intervalDomainLift (u t) x =
                  ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
                    t (intervalDomainLift u₀) x := by
                unfold intervalDomainLift; rw [dif_pos hx]; simp only [u]; rfl
              rw [hdef]
              exact le_of_abs_le (hSt_le t ht_pos x)
            · exact le_of_lt p.hγ
          -- ContinuousOn of srcSlice on [0,1]
          have hsrc_cont : ContinuousOn (srcSlice p u t) (Set.Icc (0:ℝ) 1) := by
            unfold srcSlice
            apply ContinuousOn.mul continuousOn_const
            apply ContinuousOn.rpow_const
            · -- ContinuousOn of intervalDomainLift(u t) on [0,1]
              have := ShenWork.IntervalDuhamelIntegrability.continuousOn_intervalFullSemigroupOperator_of_bounded
                ht_pos hlift_le
              exact this.congr fun x hx => by
                show intervalDomainLift (u t) x = _
                unfold intervalDomainLift; simp only [dif_pos hx, u]; rfl
            · intro x hx
              exact Or.inl (ne_of_gt (hfloor t ht_pos x hx))
          -- Apply cosineCoeffs_abs_le_of_continuous_bounded
          exact (ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
            hsrc_cont (mul_nonneg (le_of_lt p.hν) (Real.rpow_nonneg hM_sup_nn _))
            hsrc_bound k).trans (le_of_eq (by ring))
        obtain ⟨B_tail, hB_tail⟩ := hA_tail
        refine ⟨max (max 0 B_compact) B_tail, fun t => ?_⟩
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
        by_cases ht_left : t < c / 2
        · -- t < c/2: A = 0
          have : A t = 0 := by
            show smoothRightCutoff (c / 2) c t *
              resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t = 0
            rw [smoothRightCutoff_eq_zero_of_le (by linarith : c / 2 < c) (le_of_lt ht_left)]
            ring
          simp [this]
        · simp only [not_lt] at ht_left
          by_cases ht_mid : t ≤ c + 1
          · -- c/2 ≤ t ≤ c/2+2: compact bound
            have : |A t| ≤ B_compact := by
              rw [← Real.norm_eq_abs]
              exact hB_compact t ⟨ht_left, ht_mid⟩
            exact this.trans ((le_max_right (0 : ℝ) B_compact).trans (le_max_left _ B_tail))
          · -- t > c/2+2: tail bound
            simp only [not_le] at ht_mid
            exact (hB_tail t ht_mid).trans (le_max_right _ B_tail)
      · -- i = 1: same compact+tail split as i=0
        have hA1_cont : Continuous (fun t : ℝ => iteratedFDeriv ℝ 1 A t) :=
          hAC2.continuous_iteratedFDeriv (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2))
        obtain ⟨B1_compact, hB1_compact⟩ :=
          (isCompact_Icc (a := c / 2) (b := c + 1)).exists_bound_of_continuousOn
            hA1_cont.continuousOn
        have hA1_tail : ∃ B : ℝ, ∀ t : ℝ, c + 1 < t →
            ‖iteratedFDeriv ℝ 1 A t‖ ≤ B := by
          -- Use 1D Leibniz on A = φ * R where R = resolverTimeCoeff.
          -- φ and φ' are bounded (cutoff). R is bounded (i=0 proof).
          -- R' needs eigenvalue damping — sorry'd as the irreducible content.
          set R := resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k
          -- For t > c+1: A = R in a neighborhood (φ=1 for t > c)
          -- So deriv A = deriv R, and we bound |deriv R|
          -- |deriv R(t)| needs eigenvalue damping — sorry'd
          have hR_deriv_bounded : ∃ B_R' : ℝ, ∀ t : ℝ, c + 1 < t →
              |deriv R t| ≤ B_R' := by
            -- Step A: bound cosineCoeffs(srcSlice1(t), k) for t > c+1 (eigenvalue damping)
            -- Bound |heatDu u₀ t x| for t > c+1 via eigenvalue damping
            have hDu_bound : ∃ CΔ : ℝ, 0 ≤ CΔ ∧ ∀ t : ℝ, c + 1 < t → ∀ x : ℝ,
                |heatDu u₀ t x| ≤ CΔ := by
              -- heatDu = Σ' -λ_n e^{-tλ_n} c_n cos(nπx) for t > 0
              -- |term_n| ≤ λ_n e^{-tλ_n} |c_n| ≤ M₀ λ_n e^{-(c+1)λ_n}
              -- Σ' majorant summable from unitIntervalCosineEigenvalue_mul_exp_summable
              have heig_summ :=
                ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable
                  (show 0 < c + 1 by linarith)
              let maj_sum := M₀ * ∑' n,
                unitIntervalCosineEigenvalue n *
                  Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n)
              refine ⟨maj_sum, ?_, fun t ht x => ?_⟩
              · -- 0 ≤ maj_sum = M₀ * Σ' eigenvalue * exp
                exact mul_nonneg (le_trans (abs_nonneg _) (hu₀_bound 0))
                  (tsum_nonneg fun n => mul_nonneg
                    (by unfold unitIntervalCosineEigenvalue; positivity)
                    (Real.exp_nonneg _))
              · -- |heatDu u₀ t x| ≤ maj_sum for t > c+1
                have ht_pos : 0 < t := by linarith
                -- Unfold heatDu at positive time
                simp only [heatDu, if_pos ht_pos]
                -- LaplacianValue = Σ' n, LaplacianPointWeight * c_n
                unfold ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue
                -- Goal: |Σ' n, LaplacianPointWeight(t,x,n) * c_n| ≤ maj_sum
                -- Apply abs_tsum bound
                refine (abs_tsum_le_tsum_of_abs_le (fun n => ?_) (heig_summ.mul_left M₀)).trans ?_
                · -- |LaplacianPointWeight(t,x,n) * c_n| ≤ M₀ * eigenvalue(n) * exp(-(c+1)*eigval)
                  -- Unfold: LaplacianPointWeight = -eigenvalue * (exp * cos)
                  unfold ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight
                  -- |(-eigenvalue * heatPointWeight) * c_n| ≤ M₀ * (eigenvalue * exp(-(c+1)*eigval))
                  rw [abs_mul, abs_mul, abs_neg]
                  -- Goal shape after abs_mul + abs_neg:
                  -- |unitIntervalCosineEigenvalue n| * |heatPointWeight t x n| * |c_n|
                  -- ≤ M₀ * (unitIntervalCosineEigenvalue n * exp(-(c+1)*eigenvalue n))
                  -- Since eigenvalue ≥ 0: |eigenvalue| = eigenvalue
                  -- |heatPointWeight| = |exp(-t*eigval) * cos(nπx)| ≤ exp(-t*eigval)
                  -- ≤ exp(-(c+1)*eigval)  (t ≥ c+1)
                  -- |c_n| ≤ M₀
                  -- Product: eigenvalue * exp(-(c+1)*eigval) * M₀ = M₀ * eigenvalue * exp(...)
                  calc |unitIntervalCosineEigenvalue n| *
                        |unitIntervalCosineHeatPointWeight t x n| *
                        |cosineCoeffs (intervalDomainLift u₀) n|
                      ≤ unitIntervalCosineEigenvalue n *
                          Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n) * M₀ := by
                        have heig_nn : 0 ≤ unitIntervalCosineEigenvalue n := by
                          unfold unitIntervalCosineEigenvalue; positivity
                        rw [abs_of_nonneg heig_nn]
                        have hpw_le : |unitIntervalCosineHeatPointWeight t x n| ≤
                            Real.exp (-t * unitIntervalCosineEigenvalue n) := by
                          unfold unitIntervalCosineHeatPointWeight
                          rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
                          exact mul_le_of_le_one_right (Real.exp_nonneg _)
                            (Real.abs_cos_le_one _)
                        have hexp_le : Real.exp (-t * unitIntervalCosineEigenvalue n) ≤
                            Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n) :=
                          Real.exp_le_exp_of_le (by nlinarith [heig_nn])
                        have hc_le : |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀ :=
                          hu₀_bound n
                        calc _ ≤ unitIntervalCosineEigenvalue n *
                                  Real.exp (-t * unitIntervalCosineEigenvalue n) * M₀ := by
                              exact mul_le_mul
                                (mul_le_mul_of_nonneg_left hpw_le heig_nn) hc_le
                                (abs_nonneg _)
                                (mul_nonneg heig_nn (Real.exp_nonneg _))
                            _ ≤ _ := by
                              exact mul_le_mul_of_nonneg_right
                                (mul_le_mul_of_nonneg_left hexp_le heig_nn)
                                (le_trans (abs_nonneg _) hc_le)
                    _ = M₀ * (unitIntervalCosineEigenvalue n *
                          Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n)) := by ring
                · -- Σ' (M₀ * eigenvalue * exp) = M₀ * Σ' eigenvalue * exp = maj_sum
                  rw [tsum_mul_left]
            obtain ⟨CΔ, hCΔ_nn, hDu⟩ := hDu_bound
            -- Bound |srcSlice1| ≤ νγ * M_sup^{γ-1} * CΔ
            have hBsrc : ∃ Bsrc : ℝ, ∀ t : ℝ, c + 1 < t →
                |cosineCoeffs (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k| ≤ Bsrc := by
              -- Full proof: ContinuousOn (d1) + pointwise bound (L∞ + lower + rpow + hDu) + cosineCoeffs
              -- Uniform bound on srcSlice1 for ALL t > c+1 — sorry the existence of Bpt
              obtain ⟨Bpt, hBpt_nn, hBpt⟩ : ∃ Bpt : ℝ, 0 ≤ Bpt ∧
                  ∀ t : ℝ, c + 1 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
                    |srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t x| ≤ Bpt := by
                -- Bound |srcSlice1| = |νγ u^{γ-1} du| ≤ νγ R CΔ where R bounds u^{γ-1}
                -- on the compact interval [inf u₀, ‖u₀‖_∞].
                haveI : CompactSpace intervalDomainPoint :=
                  isCompact_iff_compactSpace.mp isCompact_Icc
                haveI : Nonempty intervalDomainPoint :=
                  ⟨⟨0, Set.left_mem_Icc.mpr (by norm_num)⟩⟩
                -- min/max of u₀ on compact domain
                obtain ⟨xmin, _, hmin⟩ := IsCompact.exists_isMinOn isCompact_univ
                  Set.univ_nonempty hu₀_cont.continuousOn
                have hm₀ : 0 < u₀ xmin := hu₀_pos xmin
                obtain ⟨xmax, _, hmax⟩ := IsCompact.exists_isMaxOn isCompact_univ
                  Set.univ_nonempty hu₀_cont.norm.continuousOn
                -- lift bounds
                have hlift_lo : ∀ y, y ∈ Set.Icc (0:ℝ) 1 →
                    u₀ xmin ≤ intervalDomainLift u₀ y := by
                  intro y hy; unfold intervalDomainLift; rw [dif_pos hy]
                  exact hmin (Set.mem_univ (⟨y, hy⟩ : intervalDomainPoint))
                have hlift_hi : ∀ y, |intervalDomainLift u₀ y| ≤ ‖u₀ xmax‖ := by
                  intro y; unfold intervalDomainLift; split_ifs with hy
                  · exact Real.norm_eq_abs _ ▸ hmax (Set.mem_univ (⟨y, hy⟩ : intervalDomainPoint))
                  · exact (le_of_eq abs_zero).trans (norm_nonneg _)
                have hminmax : u₀ xmin ≤ ‖u₀ xmax‖ :=
                  (le_abs_self _).trans (Real.norm_eq_abs _ ▸ hmax (Set.mem_univ xmin))
                have hlift_m := ShenWork.IntervalDuhamelIntegrability.intervalDomainLift_aestronglyMeasurable_of_continuous hu₀_cont
                -- max of u^{γ-1} on compact [inf u₀, ‖u₀‖_∞]
                obtain ⟨u_R, hu_R, hRmax⟩ := isCompact_Icc.exists_isMaxOn
                  (Set.nonempty_Icc.mpr hminmax)
                  (continuousOn_id.rpow_const
                    (fun u hu => Or.inl (ne_of_gt (lt_of_lt_of_le hm₀ hu.1))))
                have hR_nn : 0 ≤ u_R ^ (p.γ - 1) :=
                  Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hm₀ hu_R.1)) _
                -- witness: Bpt = ν γ R CΔ
                refine ⟨p.ν * p.γ * (u_R ^ (p.γ - 1)) * CΔ,
                  mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt p.hν) (le_of_lt p.hγ))
                    hR_nn) hCΔ_nn,
                  fun t ht x hx => ?_⟩
                have ht_pos : 0 < t := by linarith
                -- intervalDomainLift(conjugatePicardIter 0 t)(x) = S(t)(lift u₀)(x)
                have hdef : intervalDomainLift (conjugatePicardIter p u₀ 0 t) x =
                    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
                      t (intervalDomainLift u₀) x := by
                  unfold intervalDomainLift; rw [dif_pos hx]; rfl
                -- lower/upper bounds on the concentration value
                have hlo : u₀ xmin ≤
                    intervalDomainLift (conjugatePicardIter p u₀ 0 t) x := by
                  rw [hdef]
                  exact ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_lower_bound
                    ht_pos hm₀.le hminmax hlift_m hlift_lo hlift_hi x
                have hhi : intervalDomainLift (conjugatePicardIter p u₀ 0 t) x ≤
                    ‖u₀ xmax‖ := by
                  rw [hdef]
                  exact le_of_abs_le (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
                    ht_pos (norm_nonneg _) hlift_hi x)
                have hvp : 0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x :=
                  lt_of_lt_of_le hm₀ hlo
                -- rpow bound: u^{γ-1} ≤ R
                have hpow_le :
                    (intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) ^ (p.γ - 1)
                      ≤ u_R ^ (p.γ - 1) :=
                  hRmax ⟨hlo, hhi⟩
                -- |srcSlice1| = νγ u^{γ-1} |du| ≤ νγ R CΔ
                simp only [srcSlice1]
                calc |p.ν * p.γ *
                      (intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) ^ (p.γ - 1) *
                      heatDu u₀ t x|
                    = p.ν * p.γ *
                        (intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) ^ (p.γ - 1) *
                        |heatDu u₀ t x| := by
                      rw [abs_mul, abs_of_nonneg (mul_nonneg (mul_nonneg (le_of_lt p.hν)
                        (le_of_lt p.hγ)) (Real.rpow_nonneg (le_of_lt hvp) _))]
                  _ ≤ p.ν * p.γ * (u_R ^ (p.γ - 1)) * CΔ :=
                      mul_le_mul
                        (mul_le_mul_of_nonneg_left hpow_le
                          (mul_nonneg (le_of_lt p.hν) (le_of_lt p.hγ)))
                        (hDu t ht x) (abs_nonneg _)
                        (mul_nonneg (mul_nonneg (le_of_lt p.hν) (le_of_lt p.hγ)) hR_nn)
              refine ⟨2 * Bpt, fun t ht => ?_⟩
              have ht_pos : 0 < t := by linarith
              set u := conjugatePicardIter p u₀ 0
              -- ContinuousOn of srcSlice1(t) from d1
              obtain ⟨_, _, hcont_s1, _, _⟩ :=
                heatSemigroup_d1 hu₀_bound hu₀_cont hfloor t ht_pos
              have hsrc1_cont : ContinuousOn (srcSlice1 p u (heatDu u₀) t) (Set.Icc (0:ℝ) 1) :=
                hcont_s1.self_of_nhds
              -- Apply cosineCoeffs_abs_le with uniform Bpt
              exact (ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
                hsrc1_cont hBpt_nn (fun x hx => hBpt t ht x hx) k).trans
                (by linarith [hBpt_nn])
            obtain ⟨Bsrc, hBsrc⟩ := hBsrc
            set w_k := ShenWork.PDE.intervalNeumannResolverWeight p k
            refine ⟨|w_k| * Bsrc, fun t ht => ?_⟩
            have ht_pos : 0 < t := by linarith
            -- deriv R(t) = w_k * cosineCoeffs(srcSlice1(t), k) from HasDerivAt
            rw [show deriv R t = deriv (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t
              from rfl]
            rw [heatLevel0_resolverTimeCoeff_deriv_eq hu₀_bound hu₀_cont hfloor ht_pos k]
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hBsrc t ht) (abs_nonneg _)
          obtain ⟨B_R', hB_R'⟩ := hR_deriv_bounded
          refine ⟨B_R', fun t ht => ?_⟩
          -- ‖iteratedFDeriv ℝ 1 A t‖ = |deriv A t|
          rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
          simp only [iteratedDeriv_succ', iteratedDeriv_zero, Real.norm_eq_abs]
          -- deriv A = deriv R near t (from A = R near t via φ=1)
          have hev : A =ᶠ[𝓝 t] R := by
            filter_upwards [Ioi_mem_nhds (show c < t by linarith)] with s hs
            show smoothRightCutoff (c / 2) c s * R s = R s
            rw [smoothRightCutoff_eq_one_of_ge (by linarith : c / 2 < c) (le_of_lt hs)]
            exact one_mul _
          rw [Filter.EventuallyEq.deriv_eq hev]
          exact hB_R' t ht
        obtain ⟨B1_tail, hB1_tail⟩ := hA1_tail
        refine ⟨max (max 0 B1_compact) B1_tail, fun t => ?_⟩
        by_cases ht_left : t < c / 2
        · -- A' = 0 for t < c/2 (A ≡ 0 near t)
          have hev : A =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
            have hmem : Set.Iio (c / 2) ∈ 𝓝 t := Iio_mem_nhds ht_left
            filter_upwards [hmem] with s hs
            show smoothRightCutoff (c / 2) c s *
              resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s = 0
            rw [smoothRightCutoff_eq_zero_of_le (by linarith : c / 2 < c) (le_of_lt hs)]; ring
          rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev 1).eq_of_nhds,
            iteratedFDeriv_const_of_ne (by norm_num : (1 : ℕ) ≠ 0), Pi.zero_apply, norm_zero]
          exact le_trans (le_max_left (0 : ℝ) _) (le_max_left _ _)
        · simp only [not_lt] at ht_left
          by_cases ht_mid : t ≤ c + 1
          · exact (hB1_compact t ⟨ht_left, ht_mid⟩).trans
              ((le_max_right (0 : ℝ) _).trans (le_max_left _ _))
          · simp only [not_le] at ht_mid
            exact (hB1_tail t ht_mid).trans (le_max_right _ _)
      · -- i = 2: same compact+tail split
        have hA2_cont : Continuous (fun t : ℝ => iteratedFDeriv ℝ 2 A t) :=
          hAC2.continuous_iteratedFDeriv (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 2))
        obtain ⟨B2_compact, hB2_compact⟩ :=
          (isCompact_Icc (a := c / 2) (b := c + 1)).exists_bound_of_continuousOn
            hA2_cont.continuousOn
        have hA2_tail : ∃ B : ℝ, ∀ t : ℝ, c + 1 < t →
            ‖iteratedFDeriv ℝ 2 A t‖ ≤ B := by
          set R := resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k
          have hR_deriv2_bounded : ∃ B_R'' : ℝ, ∀ t : ℝ, c + 1 < t →
              |iteratedDeriv 2 R t| ≤ B_R'' := by
            -- Bound |cosineCoeffs(srcSlice2, k)| uniformly for t > c+1
            have hBsrc : ∃ Bsrc : ℝ, ∀ t : ℝ, c + 1 < t →
                |cosineCoeffs (srcSlice2 p (conjugatePicardIter p u₀ 0)
                  (heatDu u₀) (heatD2u u₀) t) k| ≤ Bsrc := by
              obtain ⟨Bpt, hBpt_nn, hBpt⟩ : ∃ Bpt : ℝ, 0 ≤ Bpt ∧
                  ∀ t : ℝ, c + 1 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
                    |srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀)
                      (heatD2u u₀) t x| ≤ Bpt := by
                -- Step 1: Bound |heatDu u₀ t x| ≤ CΔ for t > c+1 (eigenvalue damping)
                have hDu_bound : ∃ CΔ : ℝ, 0 ≤ CΔ ∧ ∀ t : ℝ, c + 1 < t → ∀ x : ℝ,
                    |heatDu u₀ t x| ≤ CΔ := by
                  have heig_summ :=
                    ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable
                      (show 0 < c + 1 by linarith)
                  let maj_sum := M₀ * ∑' n,
                    unitIntervalCosineEigenvalue n *
                      Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n)
                  refine ⟨maj_sum, ?_, fun t ht x => ?_⟩
                  · exact mul_nonneg (le_trans (abs_nonneg _) (hu₀_bound 0))
                      (tsum_nonneg fun n => mul_nonneg
                        (by unfold unitIntervalCosineEigenvalue; positivity)
                        (Real.exp_nonneg _))
                  · have ht_pos : 0 < t := by linarith
                    simp only [heatDu, if_pos ht_pos]
                    unfold ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue
                    refine (abs_tsum_le_tsum_of_abs_le (fun n => ?_) (heig_summ.mul_left M₀)).trans ?_
                    · unfold ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight
                      rw [abs_mul, abs_mul, abs_neg]
                      calc |unitIntervalCosineEigenvalue n| *
                            |unitIntervalCosineHeatPointWeight t x n| *
                            |cosineCoeffs (intervalDomainLift u₀) n|
                          ≤ unitIntervalCosineEigenvalue n *
                              Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n) * M₀ := by
                            have heig_nn : 0 ≤ unitIntervalCosineEigenvalue n := by
                              unfold unitIntervalCosineEigenvalue; positivity
                            rw [abs_of_nonneg heig_nn]
                            have hpw_le : |unitIntervalCosineHeatPointWeight t x n| ≤
                                Real.exp (-t * unitIntervalCosineEigenvalue n) := by
                              unfold unitIntervalCosineHeatPointWeight
                              rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
                              exact mul_le_of_le_one_right (Real.exp_nonneg _)
                                (Real.abs_cos_le_one _)
                            have hexp_le : Real.exp (-t * unitIntervalCosineEigenvalue n) ≤
                                Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n) :=
                              Real.exp_le_exp_of_le (by nlinarith [heig_nn])
                            have hc_le : |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀ :=
                              hu₀_bound n
                            calc _ ≤ unitIntervalCosineEigenvalue n *
                                      Real.exp (-t * unitIntervalCosineEigenvalue n) * M₀ :=
                                  mul_le_mul
                                    (mul_le_mul_of_nonneg_left hpw_le heig_nn) hc_le
                                    (abs_nonneg _)
                                    (mul_nonneg heig_nn (Real.exp_nonneg _))
                              _ ≤ _ :=
                                  mul_le_mul_of_nonneg_right
                                    (mul_le_mul_of_nonneg_left hexp_le heig_nn)
                                    (le_trans (abs_nonneg _) hc_le)
                        _ = M₀ * (unitIntervalCosineEigenvalue n *
                              Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n)) := by ring
                    · rw [tsum_mul_left]
                obtain ⟨CΔ, hCΔ_nn, hDu⟩ := hDu_bound
                -- Step 2: Bound |heatD2u u₀ t x| ≤ CΔ₂ for t > c+1
                have hD2u_bound : ∃ CΔ₂ : ℝ, 0 ≤ CΔ₂ ∧ ∀ t : ℝ, c + 1 < t → ∀ x : ℝ,
                    |heatD2u u₀ t x| ≤ CΔ₂ := by
                  have heig2_summ :=
                    ShenWork.Paper2.HeatSemigroupJointRegularity.eigenvalue_pow_mul_exp_summable
                      2 (show 0 < c + 1 by linarith)
                  let maj2 := M₀ * ∑' n,
                    unitIntervalCosineEigenvalue n ^ 2 *
                      Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n)
                  refine ⟨maj2, ?_, fun t ht x => ?_⟩
                  · exact mul_nonneg (le_trans (abs_nonneg _) (hu₀_bound 0))
                      (tsum_nonneg fun n => mul_nonneg
                        (pow_nonneg (by unfold unitIntervalCosineEigenvalue; positivity) _)
                        (Real.exp_nonneg _))
                  · have ht_pos : 0 < t := by linarith
                    simp only [heatD2u, if_pos ht_pos]
                    -- Goal: |∑' k, eigval² * (exp * coeff) * cos| ≤ maj2
                    refine (abs_tsum_le_tsum_of_abs_le (fun n => ?_)
                      (heig2_summ.mul_left M₀)).trans ?_
                    · -- |eigval² * (exp * coeff) * cos| ≤ eigval² * exp(-(c+1)*eigval) * M₀
                      rw [show unitIntervalCosineEigenvalue n ^ 2 *
                        (Real.exp (-t * unitIntervalCosineEigenvalue n) *
                          cosineCoeffs (intervalDomainLift u₀) n) *
                        ShenWork.CosineSpectrum.cosineMode n x =
                        unitIntervalCosineEigenvalue n ^ 2 *
                        (Real.exp (-t * unitIntervalCosineEigenvalue n) *
                          ShenWork.CosineSpectrum.cosineMode n x) *
                        cosineCoeffs (intervalDomainLift u₀) n from by ring]
                      rw [abs_mul]
                      have heig_nn : 0 ≤ unitIntervalCosineEigenvalue n := by
                        unfold unitIntervalCosineEigenvalue; positivity
                      have heig2_nn : 0 ≤ unitIntervalCosineEigenvalue n ^ 2 :=
                        pow_nonneg heig_nn _
                      have hexp_cos_le : |Real.exp (-t * unitIntervalCosineEigenvalue n) *
                          ShenWork.CosineSpectrum.cosineMode n x| ≤
                          Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n) := by
                        rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
                        calc Real.exp (-t * unitIntervalCosineEigenvalue n) *
                              |ShenWork.CosineSpectrum.cosineMode n x|
                            ≤ Real.exp (-t * unitIntervalCosineEigenvalue n) * 1 := by
                              apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
                              exact Real.abs_cos_le_one _
                          _ = Real.exp (-t * unitIntervalCosineEigenvalue n) := mul_one _
                          _ ≤ Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n) :=
                              Real.exp_le_exp_of_le (by nlinarith [heig_nn])
                      calc |unitIntervalCosineEigenvalue n ^ 2 *
                            (Real.exp (-t * unitIntervalCosineEigenvalue n) *
                              ShenWork.CosineSpectrum.cosineMode n x)| *
                            |cosineCoeffs (intervalDomainLift u₀) n|
                          ≤ (unitIntervalCosineEigenvalue n ^ 2 *
                              Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n)) * M₀ := by
                            rw [abs_mul, abs_of_nonneg heig2_nn]
                            exact mul_le_mul
                              (mul_le_mul_of_nonneg_left hexp_cos_le heig2_nn)
                              (hu₀_bound n) (abs_nonneg _)
                              (mul_nonneg heig2_nn (Real.exp_nonneg _))
                        _ = M₀ * (unitIntervalCosineEigenvalue n ^ 2 *
                              Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n)) := by ring
                    · rw [tsum_mul_left]
                obtain ⟨CΔ₂, hCΔ₂_nn, hD2u⟩ := hD2u_bound
                -- Step 3: compact domain infrastructure (min/max, lift bounds, rpow)
                haveI : CompactSpace intervalDomainPoint :=
                  isCompact_iff_compactSpace.mp isCompact_Icc
                haveI : Nonempty intervalDomainPoint :=
                  ⟨⟨0, Set.left_mem_Icc.mpr (by norm_num)⟩⟩
                obtain ⟨xmin, _, hmin⟩ := IsCompact.exists_isMinOn isCompact_univ
                  Set.univ_nonempty hu₀_cont.continuousOn
                have hm₀ : 0 < u₀ xmin := hu₀_pos xmin
                obtain ⟨xmax, _, hmax⟩ := IsCompact.exists_isMaxOn isCompact_univ
                  Set.univ_nonempty hu₀_cont.norm.continuousOn
                have hlift_lo : ∀ y, y ∈ Set.Icc (0:ℝ) 1 →
                    u₀ xmin ≤ intervalDomainLift u₀ y := by
                  intro y hy; unfold intervalDomainLift; rw [dif_pos hy]
                  exact hmin (Set.mem_univ (⟨y, hy⟩ : intervalDomainPoint))
                have hlift_hi : ∀ y, |intervalDomainLift u₀ y| ≤ ‖u₀ xmax‖ := by
                  intro y; unfold intervalDomainLift; split_ifs with hy
                  · exact Real.norm_eq_abs _ ▸ hmax (Set.mem_univ (⟨y, hy⟩ : intervalDomainPoint))
                  · exact (le_of_eq abs_zero).trans (norm_nonneg _)
                have hminmax : u₀ xmin ≤ ‖u₀ xmax‖ :=
                  (le_abs_self _).trans (Real.norm_eq_abs _ ▸ hmax (Set.mem_univ xmin))
                have hlift_m := ShenWork.IntervalDuhamelIntegrability.intervalDomainLift_aestronglyMeasurable_of_continuous hu₀_cont
                -- rpow bounds on compact [inf u₀, ‖u₀‖_∞]
                -- R₁ bounds u^{γ-1}
                obtain ⟨u_R₁, hu_R₁, hR₁max⟩ := isCompact_Icc.exists_isMaxOn
                  (Set.nonempty_Icc.mpr hminmax)
                  (continuousOn_id.rpow_const
                    (fun u hu => Or.inl (ne_of_gt (lt_of_lt_of_le hm₀ hu.1))))
                have hR₁_nn : 0 ≤ u_R₁ ^ (p.γ - 1) :=
                  Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hm₀ hu_R₁.1)) _
                -- R₂ bounds u^{γ-2} = u^{γ-1-1}
                obtain ⟨u_R₂, hu_R₂, hR₂max⟩ := isCompact_Icc.exists_isMaxOn
                  (Set.nonempty_Icc.mpr hminmax)
                  (continuousOn_id.rpow_const
                    (fun u hu => Or.inl (ne_of_gt (lt_of_lt_of_le hm₀ hu.1))))
                have hR₂_nn : 0 ≤ u_R₂ ^ (p.γ - 1 - 1) :=
                  Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hm₀ hu_R₂.1)) _
                -- Step 4: assemble Bpt = term1_bound + term2_bound
                -- term1_bound = |ν·γ·(γ-1)| · R₂ · CΔ²
                -- term2_bound = ν·γ · R₁ · CΔ₂
                set B₁ := |p.ν * p.γ * (p.γ - 1)| * (u_R₂ ^ (p.γ - 1 - 1)) * CΔ ^ 2
                set B₂ := p.ν * p.γ * (u_R₁ ^ (p.γ - 1)) * CΔ₂
                refine ⟨B₁ + B₂,
                  add_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hR₂_nn)
                    (sq_nonneg _))
                    (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt p.hν) (le_of_lt p.hγ))
                      hR₁_nn) hCΔ₂_nn),
                  fun t ht x hx => ?_⟩
                have ht_pos : 0 < t := by linarith
                have hdef : intervalDomainLift (conjugatePicardIter p u₀ 0 t) x =
                    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
                      t (intervalDomainLift u₀) x := by
                  unfold intervalDomainLift; rw [dif_pos hx]; rfl
                have hlo : u₀ xmin ≤
                    intervalDomainLift (conjugatePicardIter p u₀ 0 t) x := by
                  rw [hdef]
                  exact ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_lower_bound
                    ht_pos hm₀.le hminmax hlift_m hlift_lo hlift_hi x
                have hhi : intervalDomainLift (conjugatePicardIter p u₀ 0 t) x ≤
                    ‖u₀ xmax‖ := by
                  rw [hdef]
                  exact le_of_abs_le (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
                    ht_pos (norm_nonneg _) hlift_hi x)
                have hvp : 0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x :=
                  lt_of_lt_of_le hm₀ hlo
                -- rpow bounds
                have hpow1_le :
                    (intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) ^ (p.γ - 1)
                      ≤ u_R₁ ^ (p.γ - 1) :=
                  hR₁max ⟨hlo, hhi⟩
                have hpow2_le :
                    (intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) ^ (p.γ - 1 - 1)
                      ≤ u_R₂ ^ (p.γ - 1 - 1) :=
                  hR₂max ⟨hlo, hhi⟩
                -- Triangle inequality on srcSlice2 = term1 + term2
                simp only [srcSlice2]
                calc |p.ν * p.γ * (p.γ - 1) *
                        (intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) ^ (p.γ - 1 - 1) *
                        (heatDu u₀ t x) ^ (2 : ℕ) +
                      p.ν * p.γ *
                        (intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) ^ (p.γ - 1) *
                        heatD2u u₀ t x|
                    ≤ |p.ν * p.γ * (p.γ - 1) *
                        (intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) ^ (p.γ - 1 - 1) *
                        (heatDu u₀ t x) ^ (2 : ℕ)| +
                      |p.ν * p.γ *
                        (intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) ^ (p.γ - 1) *
                        heatD2u u₀ t x| := abs_add_le _ _
                  _ ≤ B₁ + B₂ := by
                      apply add_le_add
                      · -- Term 1: |ν·γ·(γ-1)·u^{γ-2}·(du)²| ≤ |ν·γ·(γ-1)| · R₂ · CΔ²
                        rw [show p.ν * p.γ * (p.γ - 1) *
                            (intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) ^ (p.γ - 1 - 1) *
                            (heatDu u₀ t x) ^ (2 : ℕ) =
                          (p.ν * p.γ * (p.γ - 1)) *
                            ((intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) ^ (p.γ - 1 - 1) *
                              (heatDu u₀ t x) ^ (2 : ℕ)) from by ring]
                        rw [abs_mul, show B₁ = |p.ν * p.γ * (p.γ - 1)| *
                          (u_R₂ ^ (p.γ - 1 - 1) * CΔ ^ 2) from by ring]
                        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hvp) _)]
                        have hdu_sq : |heatDu u₀ t x| ^ 2 ≤ CΔ ^ 2 :=
                          sq_le_sq' (by linarith [abs_nonneg (heatDu u₀ t x), hDu t ht x])
                            (hDu t ht x)
                        rw [show |(heatDu u₀ t x) ^ (2 : ℕ)| = |heatDu u₀ t x| ^ 2 from by
                          rw [pow_two, abs_mul, pow_two]]
                        exact mul_le_mul hpow2_le hdu_sq (sq_nonneg _) hR₂_nn
                      · -- Term 2: |ν·γ·u^{γ-1}·d2u| ≤ ν·γ · R₁ · CΔ₂
                        rw [abs_mul, abs_of_nonneg (mul_nonneg (mul_nonneg (le_of_lt p.hν)
                          (le_of_lt p.hγ)) (Real.rpow_nonneg (le_of_lt hvp) _))]
                        exact mul_le_mul
                          (mul_le_mul_of_nonneg_left hpow1_le
                            (mul_nonneg (le_of_lt p.hν) (le_of_lt p.hγ)))
                          (hD2u t ht x) (abs_nonneg _)
                          (mul_nonneg (mul_nonneg (le_of_lt p.hν) (le_of_lt p.hγ)) hR₁_nn)
              refine ⟨2 * Bpt, fun t ht => ?_⟩
              have ht_pos : 0 < t := by linarith
              obtain ⟨δ₁, hδ₁, _, _, hcd1⟩ :=
                heatSemigroup_d1 hu₀_bound hu₀_cont hfloor t ht_pos
              have hsrc2_cont : ContinuousOn
                  (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀) t)
                  (Set.Icc (0:ℝ) 1) :=
                hcd1.uncurry_left t (by constructor <;> linarith)
              exact (ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
                hsrc2_cont hBpt_nn (fun x hx => hBpt t ht x hx) k).trans
                (by linarith [hBpt_nn])
            obtain ⟨Bsrc, hBsrc⟩ := hBsrc
            set w_k := ShenWork.PDE.intervalNeumannResolverWeight p k
            -- iteratedDeriv 2 R t = w_k * cosineCoeffs(srcSlice2 t, k)
            have hid2 : ∀ t : ℝ, 0 < t → iteratedDeriv 2 R t =
                w_k * cosineCoeffs (srcSlice2 p (conjugatePicardIter p u₀ 0)
                  (heatDu u₀) (heatD2u u₀) t) k := by
              intro t ht_pos
              have hRfun : R = fun s =>
                  w_k * srcTimeCoeff p (conjugatePicardIter p u₀ 0) k s := by
                funext s
                exact resolverTimeCoeff_eq_weight_smul p (conjugatePicardIter p u₀ 0) k s
              rw [hRfun, iteratedDeriv_const_mul_field]
              congr 1
              rw [iteratedDeriv_succ]
              have hnear : (fun s => iteratedDeriv 1
                  (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) s) =ᶠ[𝓝 t]
                  fun s => cosineCoeffs (srcSlice1 p (conjugatePicardIter p u₀ 0)
                    (heatDu u₀) s) k := by
                filter_upwards [Ioi_mem_nhds ht_pos] with s hs
                rw [iteratedDeriv_one]
                exact (heatLevel0_srcTimeCoeff_hasDerivAt hu₀_bound hu₀_cont hfloor hs k).deriv
              rw [Filter.EventuallyEq.deriv_eq hnear]
              obtain ⟨δ₁, hδ₁, hcont_s1, hdiff_s1, hcd_s2⟩ :=
                heatSemigroup_d1 hu₀_bound hu₀_cont hfloor t ht_pos
              have hint : ∀ᶠ r in 𝓝 t, IntervalIntegrable
                  (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) r)
                  MeasureTheory.volume (0 : ℝ) 1 :=
                hcont_s1.mono fun r hr =>
                  (Set.uIcc_of_le (zero_le_one (α := ℝ)) ▸ hr).intervalIntegrable
              exact (cosineCoeffs_hasDerivAt_of_smooth_param hδ₁ hint hdiff_s1 hcd_s2).deriv
            refine ⟨|w_k| * Bsrc, fun t ht => ?_⟩
            rw [hid2 t (by linarith : 0 < t), abs_mul]
            exact mul_le_mul_of_nonneg_left (hBsrc t ht) (abs_nonneg _)
          obtain ⟨B_R'', hB_R''⟩ := hR_deriv2_bounded
          refine ⟨B_R'', fun t ht => ?_⟩
          -- A = R near t (φ=1 for t > c)
          have hev : A =ᶠ[𝓝 t] R := by
            filter_upwards [Ioi_mem_nhds (show c < t by linarith)] with s hs
            show smoothRightCutoff (c / 2) c s * R s = R s
            rw [smoothRightCutoff_eq_one_of_ge (by linarith : c / 2 < c) (le_of_lt hs)]
            exact one_mul _
          -- iteratedFDeriv ℝ 2 A t = iteratedFDeriv ℝ 2 R t
          have hev2 := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev 2).eq_of_nhds
          -- ‖iteratedFDeriv ℝ 2 A t‖ = ‖iteratedFDeriv ℝ 2 R t‖ = |iteratedDeriv 2 R t|
          rw [show ‖iteratedFDeriv ℝ 2 A t‖ = ‖iteratedFDeriv ℝ 2 R t‖ from
            congr_arg _ hev2]
          rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
          exact hB_R'' t ht
        obtain ⟨B2_tail, hB2_tail⟩ := hA2_tail
        refine ⟨max (max 0 B2_compact) B2_tail, fun t => ?_⟩
        by_cases ht_left : t < c / 2
        · have hev : A =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
            have hmem : Set.Iio (c / 2) ∈ 𝓝 t := Iio_mem_nhds ht_left
            filter_upwards [hmem] with s hs
            show smoothRightCutoff (c / 2) c s *
              resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s = 0
            rw [smoothRightCutoff_eq_zero_of_le (by linarith : c / 2 < c) (le_of_lt hs)]; ring
          rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev 2).eq_of_nhds,
            iteratedFDeriv_const_of_ne (by norm_num : (2 : ℕ) ≠ 0), Pi.zero_apply, norm_zero]
          exact le_trans (le_max_left (0 : ℝ) _) (le_max_left _ _)
        · simp only [not_lt] at ht_left
          by_cases ht_mid : t ≤ c + 1
          · exact (hB2_compact t ⟨ht_left, ht_mid⟩).trans
              ((le_max_right (0 : ℝ) _).trans (le_max_left _ _))
          · simp only [not_le] at ht_mid
            exact (hB2_tail t ht_mid).trans (le_max_right _ _)
    obtain ⟨B_max, hB_max⟩ : ∃ B_max : ℝ, ∀ (i : ℕ), i ≤ 2 → ∀ t : ℝ,
        ‖iteratedFDeriv ℝ i A t‖ ≤ B_max := by
      obtain ⟨b0, hb0⟩ := hA_global_bounds 0 (by omega)
      obtain ⟨b1, hb1⟩ := hA_global_bounds 1 (by omega)
      obtain ⟨b2, hb2⟩ := hA_global_bounds 2 (by omega)
      refine ⟨max b0 (max b1 b2), fun i hi t => ?_⟩
      interval_cases i
      · exact (hb0 t).trans (le_max_left _ _)
      · exact (hb1 t).trans ((le_max_left _ _).trans (le_max_right _ _))
      · exact (hb2 t).trans ((le_max_right _ _).trans (le_max_right _ _))
    -- Same Leibniz assembly as hmid but with global bounds
    have hAfst : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => A q.1) :=
      hAC2.comp contDiff_fst
    have hBsnd : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => cosineMode k q.2) :=
      hcos.comp contDiff_snd
    have hjTop : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast hj
    have hfactor : f = fun q : ℝ × ℝ => A q.1 * cosineMode k q.2 := by
      funext q; simp [hf_def, cutoffResolverTerm, A, mul_assoc]
    set Ctail := ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * B_max *
        ShenWork.IntervalResolverSpectralJointC2Concrete.valueCosWeight (j - i) k
    refine ⟨Ctail, fun q _hq => ?_⟩
    rw [hfactor]
    calc ‖iteratedFDeriv ℝ j (fun q : ℝ × ℝ => A q.1 * cosineMode k q.2) q‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => A q.1) q‖ *
            ‖iteratedFDeriv ℝ (j - i) (fun q : ℝ × ℝ => cosineMode k q.2) q‖ := by
          simpa [mul_assoc] using norm_iteratedFDeriv_mul_le hAfst hBsnd q hjTop
      _ ≤ Ctail := by
          apply Finset.sum_le_sum
          intro i hi
          have hik : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hiNat : i ≤ 2 := le_trans hik hjNat
          have hjiNat : j - i ≤ 2 := le_trans (Nat.sub_le j i) hjNat
          have hiCast : ((i : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
            exact_mod_cast hiNat
          have hjiCast : (((j - i : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
            exact_mod_cast hjiNat
          have hA_fst_bound : ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => A q.1) q‖ ≤ B_max := by
            exact (norm_iteratedFDeriv_comp_fst_le hAC2 hiCast q).trans (hB_max i hiNat q.1)
          have hB_snd_bound : ‖iteratedFDeriv ℝ (j - i)
              (fun q : ℝ × ℝ => cosineMode k q.2) q‖ ≤
              ShenWork.IntervalResolverSpectralJointC2Concrete.valueCosWeight (j - i) k := by
            exact (ShenWork.IntervalResolverSpectralJointC2CutoffBounds.norm_iteratedFDeriv_comp_snd_le
              hcos hjiCast q).trans
              (ShenWork.IntervalResolverSpectralJointC2Concrete.cosineMode_iteratedFDeriv_bound
                k (j - i) q.2 hjiNat)
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hA_fst_bound (Nat.cast_nonneg _))
            hB_snd_bound (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (le_trans (norm_nonneg _) hA_fst_bound))
  obtain ⟨Cmid, hmid⟩ := hmid
  obtain ⟨Ctail, htail⟩ := htail
  have hleft' : ∀ q : ℝ × ℝ, q.1 < c / 2 →
      (fun q => ‖iteratedFDeriv ℝ j f q‖) q = 0 := hleft
  have hmid' : ∀ q : ℝ × ℝ, c / 2 ≤ q.1 → q.1 ≤ c / 2 + 1 →
      (fun q => ‖iteratedFDeriv ℝ j f q‖) q ≤ Cmid := hmid
  have htail' : ∀ q : ℝ × ℝ, c / 2 + 1 < q.1 →
      (fun q => ‖iteratedFDeriv ℝ j f q‖) q ≤ Ctail := htail
  exact bddAbove_range_of_left_mid_tail hleft' hmid' htail'

/-- The majorant is nonneg. -/
theorem cutoffResolverMajorant_nonneg {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ} (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    {j k : ℕ} (_hj : (j : ℕ∞) ≤ 2) :
    0 ≤ cutoffResolverMajorant p u₀ M₀ c hc j k := by
  have hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x :=
    fun t ht x hx =>
      ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
        hu₀_cont hu₀_pos ht hx
  have hbdd := cutoffResolverMajorant_bddAbove_direct
    (p := p) hc hu₀_bound hu₀_cont hu₀_pos hfloor j k _hj
  exact (norm_nonneg _).trans (le_ciSup hbdd (0, 0))

/-- The majorant bounds the iterated derivatives of the cutoff resolver term. -/
theorem cutoffResolverTerm_iteratedFDeriv_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    {c : ℝ} (hc : 0 < c) (j k : ℕ) (q : ℝ × ℝ)
    (hj : (j : ℕ∞) ≤ 2) :
    ‖iteratedFDeriv ℝ j
      (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖ ≤
      cutoffResolverMajorant p u₀ M₀ c hc j k := by
  have hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x :=
    fun t ht x hx =>
      ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
        hu₀_cont hu₀_pos ht hx
  have hbdd := cutoffResolverMajorant_bddAbove_direct
    (p := p) hc hu₀_bound hu₀_cont hu₀_pos hfloor j k hj
  exact le_ciSup hbdd q

/-! ### EventuallyEq: cutoff series = original series near (s₀, x₀) -/

/-- The original resolver series equals the `intervalDomainLift` of
`coupledChemicalConcentration` on interior points.  This is a restatement
of `coupledChemical_lift_eq_series` in terms of `resolverTerm`. -/
theorem resolverSeries_eq_lift_on_interior
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {t x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalDomainLift (coupledChemicalConcentration p u t) x =
      ∑' k : ℕ, resolverTerm p u k (t, x) := by
  have h := ShenWork.IntervalResolverJointC2PhysicalConcrete.coupledChemical_lift_eq_series
    (p := p) (u := u) (t := t) (x := x) hx
  simp only [ShenWork.IntervalResolverJointC2Physical.boundedWeightJointTerm,
    resolverTerm] at h ⊢
  exact h

/-- At positive heat time and interior spatial points, the spatial derivative of
the lifted resolver equals the termwise-differentiated resolver series. -/
theorem resolverGradSeries_eq_lift_deriv_on_interior_heat
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ t x : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    (ht : 0 < t) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (intervalDomainLift (coupledChemicalConcentration p
      (conjugatePicardIter p u₀ 0) t)) x =
      ∑' k : ℕ, resolverGradTerm p (conjugatePicardIter p u₀ 0) k (t, x) := by
  have hopen : Set.Ioo (0 : ℝ) 1 ∈ 𝓝 x := isOpen_Ioo.mem_nhds hx
  have hval : (fun y : ℝ =>
        intervalDomainLift (coupledChemicalConcentration p
          (conjugatePicardIter p u₀ 0) t) y) =ᶠ[𝓝 x]
      fun y : ℝ =>
        ∑' k : ℕ, resolverTerm p (conjugatePicardIter p u₀ 0) k (t, y) := by
    filter_upwards [hopen] with y hy
    exact resolverSeries_eq_lift_on_interior (p := p)
      (u := conjugatePicardIter p u₀ 0) (Set.Ioo_subset_Icc_self hy)
  rw [Filter.EventuallyEq.deriv_eq hval]
  set b : ℕ → ℝ := fun k => resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t with hb
  have hpos_t : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x :=
    fun y hy =>
      ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
        hu₀_cont hu₀_pos ht hy
  have hsrc_summ : Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        |cosineCoeffs
          (srcSlice p (conjugatePicardIter p u₀ 0) t) k|) :=
    ShenWork.Paper2.HeatLevel0SourceDecay.heatLevel0_srcSlice_eigenvalue_L1_summable
      hu₀_bound hu₀_cont ht hpos_t
  have hb_summ : Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k * |b k|) := by
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity)
        (abs_nonneg _)) (fun k => ?_)
      (hsrc_summ.mul_left (1 / p.μ))
    have hlam_nn : 0 ≤ unitIntervalCosineEigenvalue k := by
      unfold unitIntervalCosineEigenvalue
      positivity
    have hsrc_nn : 0 ≤
        unitIntervalCosineEigenvalue k *
          |cosineCoeffs (srcSlice p (conjugatePicardIter p u₀ 0) t) k| :=
      mul_nonneg hlam_nn (abs_nonneg _)
    change unitIntervalCosineEigenvalue k *
        |resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t| ≤
      1 / p.μ * (unitIntervalCosineEigenvalue k *
        |cosineCoeffs (srcSlice p (conjugatePicardIter p u₀ 0) t) k|)
    rw [resolverTimeCoeff_eq_weight_smul p (conjugatePicardIter p u₀ 0) k t,
      srcTimeCoeff_eq_cosineCoeffs p (conjugatePicardIter p u₀ 0) k t,
      abs_mul,
      abs_of_nonneg
        (ShenWork.IntervalPhysicalResolverDataConcrete.resolverWeight_nonneg p k)]
    calc unitIntervalCosineEigenvalue k *
          (ShenWork.PDE.intervalNeumannResolverWeight p k *
            |cosineCoeffs (srcSlice p (conjugatePicardIter p u₀ 0) t) k|)
        = ShenWork.PDE.intervalNeumannResolverWeight p k *
            (unitIntervalCosineEigenvalue k *
              |cosineCoeffs (srcSlice p (conjugatePicardIter p u₀ 0) t) k|) := by ring
      _ ≤ (1 / p.μ) *
            (unitIntervalCosineEigenvalue k *
              |cosineCoeffs (srcSlice p (conjugatePicardIter p u₀ 0) t) k|) :=
          mul_le_mul_of_nonneg_right
            (ShenWork.IntervalResolverJointC2PhysicalConcrete.resolverWeight_le_inv_mu p k)
            hsrc_nn
  have hgrad :=
    ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_grad_hasDerivAt hb_summ x
  have hraw : (fun y : ℝ =>
      ∑' k : ℕ, resolverTerm p (conjugatePicardIter p u₀ 0) k (t, y)) =
      fun y : ℝ => ∑' k : ℕ, b k * cosineMode k y := by
    funext y
    apply tsum_congr
    intro k
    simp [resolverTerm, hb]
  rw [hraw, hgrad.deriv]
  exact tsum_congr (fun k => by
    simp [resolverGradTerm, hb, ShenWork.CosineSpectrum.cosineMode_deriv])

/-- Near `(s₀, x₀)` with `s₀ > c`, the original resolver series equals
the cutoff series (because `φ(t) = 1` in a neighborhood of `s₀`). -/
theorem resolverSeries_eventuallyEq_cutoff
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {c s₀ x₀ : ℝ} (_hc : 0 < c) (hs₀ : c < s₀) :
    (fun q : ℝ × ℝ =>
      ∑' k : ℕ, resolverTerm p u k q) =ᶠ[𝓝 (s₀, x₀)]
    (fun q : ℝ × ℝ =>
      ∑' k : ℕ, cutoffResolverTerm p u c k q) := by
  -- φ = 1 in a neighborhood of s₀ (since s₀ > c)
  have hc'c : c / 2 < c := by linarith
  have hφ_one : smoothRightCutoff (c / 2) c =ᶠ[𝓝 s₀] fun _ => (1 : ℝ) :=
    smoothRightCutoff_eventually_eq_one hc'c hs₀
  -- Lift to ℝ × ℝ via fst
  have hφ_prod :
      (fun q : ℝ × ℝ => smoothRightCutoff (c / 2) c q.1) =ᶠ[𝓝 (s₀, x₀)]
        fun _ : ℝ × ℝ => (1 : ℝ) :=
    hφ_one.comp_tendsto continuous_fst.continuousAt
  -- Where φ = 1, cutoff term = original term
  filter_upwards [hφ_prod] with q hq
  congr 1; ext k
  simp [cutoffResolverTerm, resolverTerm, hq]

/-- Near `(s₀,x₀)` with `s₀ > c`, the raw gradient series equals the cutoff
gradient series. -/
theorem resolverGradSeries_eventuallyEq_cutoff
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {c s₀ x₀ : ℝ} (_hc : 0 < c) (hs₀ : c < s₀) :
    (fun q : ℝ × ℝ =>
      ∑' k : ℕ, resolverGradTerm p u k q) =ᶠ[𝓝 (s₀, x₀)]
    (fun q : ℝ × ℝ =>
      ∑' k : ℕ, cutoffResolverGradTerm p u c k q) := by
  have hc'c : c / 2 < c := by linarith
  have hφ_one : smoothRightCutoff (c / 2) c =ᶠ[𝓝 s₀] fun _ => (1 : ℝ) :=
    smoothRightCutoff_eventually_eq_one hc'c hs₀
  have hφ_prod :
      (fun q : ℝ × ℝ => smoothRightCutoff (c / 2) c q.1) =ᶠ[𝓝 (s₀, x₀)]
        fun _ : ℝ × ℝ => (1 : ℝ) :=
    hφ_one.comp_tendsto continuous_fst.continuousAt
  filter_upwards [hφ_prod] with q hq
  congr 1; ext k
  simp [cutoffResolverGradTerm, resolverGradTerm, hq]

/-! ### Main theorems -/

/-- **Joint `ContDiffAt ℝ 2`** of the resolver coupled concentration at the heat
semigroup base iterate `conjugatePicardIter p u₀ 0`, via direct cutoff +
`contDiff_tsum`.

Proof: `cutoffResolverSeries_contDiff_two_posModes_of_Bt` gives global
`ContDiff ℝ 2` of the cutoff series.  Near `(s₀, x₀)` with `s₀ > c`, the cutoff
series agrees with
the original series (`resolverSeries_eventuallyEq_cutoff`), and the original
series = `intervalDomainLift (coupledChemicalConcentration ...)` on interior
points.  So `ContDiffAt` of the lifted concentration follows. -/
theorem heatResolver_jointContDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
      ContDiffAt ℝ 2
          (fun q : ℝ × ℝ =>
            intervalDomainLift (coupledChemicalConcentration p
              (conjugatePicardIter p u₀ 0) q.1) q.2)
          (s₀, x₀) := by
    -- Step 1: The cutoff series is globally C² by the direct positive-mode route.
    classical
    have ha : 0 < c / 2 := by linarith
    obtain ⟨C₀, hC₀nn, hC₀⟩ :=
      ShenWork.Paper2.HeatLevel0SourceDecay.heatLevel0_srcSlice_quartic_decay_tail
        (p := p) (u₀ := u₀) (M₀ := M₀) (a := c / 2)
        ha hu₀_bound hu₀_cont hu₀_pos
    obtain ⟨C₁, hC₁nn, hC₁⟩ :=
      ShenWork.Paper2.HeatLevel0SourceDecay.heatLevel0_srcSlice1_quadratic_decay_tail
        (p := p) (u₀ := u₀) (M₀ := M₀) (a := c / 2)
        ha hu₀_bound hu₀_cont hu₀_pos
    obtain ⟨C₂, hC₂nn, hC₂⟩ :=
      ShenWork.Paper2.HeatLevel0SourceDecay.heatLevel0_srcSlice2_quadratic_decay_tail
        (p := p) (u₀ := u₀) (M₀ := M₀) (a := c / 2)
        ha hu₀_bound hu₀_cont hu₀_pos
    have hc'c : c / 2 < c := by linarith
    let Φ₀ := resolverSmoothRightCutoffDerivBound (c / 2) c hc'c 0 (by norm_num)
    let Φ₁ := resolverSmoothRightCutoffDerivBound (c / 2) c hc'c 1 (by norm_num)
    let Φ₂ := resolverSmoothRightCutoffDerivBound (c / 2) c hc'c 2 (by norm_num)
    let Φ := max 0 (max Φ₀ (max Φ₁ Φ₂))
    have hΦnn : 0 ≤ Φ := by
      dsimp [Φ]
      exact le_max_left 0 (max Φ₀ (max Φ₁ Φ₂))
    have hΦ₀_le : Φ₀ ≤ Φ := by
      dsimp [Φ]
      exact (le_max_left Φ₀ (max Φ₁ Φ₂)).trans
        (le_max_right 0 (max Φ₀ (max Φ₁ Φ₂)))
    have hΦ₁_le : Φ₁ ≤ Φ := by
      dsimp [Φ]
      exact ((le_max_left Φ₁ Φ₂).trans (le_max_right Φ₀ (max Φ₁ Φ₂))).trans
        (le_max_right 0 (max Φ₀ (max Φ₁ Φ₂)))
    have hΦ₂_le : Φ₂ ≤ Φ := by
      dsimp [Φ]
      exact ((le_max_right Φ₁ Φ₂).trans (le_max_right Φ₀ (max Φ₁ Φ₂))).trans
        (le_max_right 0 (max Φ₀ (max Φ₁ Φ₂)))
    have hΦ : ∀ r : ℕ, r ≤ 2 → ∀ t : ℝ,
        ‖iteratedFDeriv ℝ r (smoothRightCutoff (c / 2) c) t‖ ≤ Φ := by
      intro r hr t
      interval_cases r
      · exact (resolverSmoothRightCutoffDerivBound_spec hc'c
          (k := 0) (by norm_num) t).trans hΦ₀_le
      · exact (resolverSmoothRightCutoffDerivBound_spec hc'c
          (k := 1) (by norm_num) t).trans hΦ₁_le
      · exact (resolverSmoothRightCutoffDerivBound_spec hc'c
          (k := 2) (by norm_num) t).trans hΦ₂_le
    let Bt : ℕ → ℕ → ℝ := heatLevel0GradCoeffPowerBt Φ C₀ C₁ C₂
    have hBtp_eq : (fun i k => if k = 0 then 0 else Bt i k) = Bt := by
      funext i k
      by_cases hk : k = 0
      · subst k
        simp [Bt, heatLevel0GradCoeffPowerBt]
      · simp [Bt, heatLevel0GradCoeffPowerBt, hk]
    have hBt : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 → 1 ≤ k →
        ‖iteratedFDeriv ℝ i
          (fun s : ℝ => smoothRightCutoff (c / 2) c s *
            resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s) t‖ ≤ Bt i k := by
      intro i k t hi hk
      exact heatLevel0_cutoffResolverCoeff_iteratedFDeriv_power_bound_posMode
        (p := p) (u₀ := u₀) (M₀ := M₀) (a := c / 2) (c := c)
        (Φ := Φ) (C₀ := C₀) (C₁ := C₁) (C₂ := C₂)
        ha hc rfl hΦnn hΦ hC₀nn hC₁nn hC₂nn
        hu₀_bound hu₀_cont hfloor hC₀ hC₁ hC₂ hi hk (t := t)
    have hsumm : ∀ j : ℕ, (j : ℕ∞) ≤ 2 →
        Summable (boundedWeightJointMajorant
          (fun i k => if k = 0 then 0 else Bt i k) j) := by
      simpa [hBtp_eq] using heatLevel0GradCoeffPowerBt_value_summable Φ C₀ C₁ C₂
    have hCutoff := (cutoffResolverSeries_contDiff_two_posModes_of_Bt
      (p := p) (u₀ := u₀) (M₀ := M₀)
      hu₀_bound hu₀_cont hfloor hc (Bt := Bt) hBt hsumm).contDiffAt (x := (s₀, x₀))
    -- Step 2: Near (s₀, x₀), the cutoff series = resolver term series
    have hEqCutoff := resolverSeries_eventuallyEq_cutoff (p := p)
      (u := conjugatePicardIter p u₀ 0) hc hs₀ (x₀ := x₀)
    -- Step 3: Near (s₀, x₀), the resolver term series = lifted concentration
    -- (because x₀ ∈ (0,1) ⊂ [0,1])
    have hmem : {q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) 1} ∈ 𝓝 (s₀, x₀) :=
      (isOpen_Ioo.preimage continuous_snd).mem_nhds hx₀
    have hEqLift : (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p
          (conjugatePicardIter p u₀ 0) q.1) q.2) =ᶠ[𝓝 (s₀, x₀)]
      (fun q : ℝ × ℝ =>
        ∑' k : ℕ, resolverTerm p (conjugatePicardIter p u₀ 0) k q) := by
      filter_upwards [hmem] with q hq
      exact resolverSeries_eq_lift_on_interior (Set.Ioo_subset_Icc_self hq)
    -- Chain: lift =ᶠ resolver series =ᶠ cutoff series
    exact hCutoff.congr_of_eventuallyEq (hEqLift.trans hEqCutoff)

/-- **Joint `ContDiffAt ℝ 2`** of the spatial derivative `∂ₓ v` of the resolver
coupled concentration at the heat semigroup base iterate.

This is the gradient version, needed for the FAC chain. -/
theorem heatResolver_grad_jointContDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          deriv (intervalDomainLift (coupledChemicalConcentration p
            (conjugatePicardIter p u₀ 0) q.1)) q.2)
        (s₀, x₀) := by
  classical
  have ha : 0 < c / 2 := by linarith
  obtain ⟨C₀, hC₀nn, hC₀⟩ :=
    ShenWork.Paper2.HeatLevel0SourceDecay.heatLevel0_srcSlice_quartic_decay_tail
      (p := p) (u₀ := u₀) (M₀ := M₀) (a := c / 2)
      ha hu₀_bound hu₀_cont hu₀_pos
  obtain ⟨C₁, hC₁nn, hC₁⟩ :=
    ShenWork.Paper2.HeatLevel0SourceDecay.heatLevel0_srcSlice1_quadratic_decay_tail
      (p := p) (u₀ := u₀) (M₀ := M₀) (a := c / 2)
      ha hu₀_bound hu₀_cont hu₀_pos
  obtain ⟨C₂, hC₂nn, hC₂⟩ :=
    ShenWork.Paper2.HeatLevel0SourceDecay.heatLevel0_srcSlice2_quadratic_decay_tail
      (p := p) (u₀ := u₀) (M₀ := M₀) (a := c / 2)
      ha hu₀_bound hu₀_cont hu₀_pos
  have hc'c : c / 2 < c := by linarith
  let Φ₀ := resolverSmoothRightCutoffDerivBound (c / 2) c hc'c 0 (by norm_num)
  let Φ₁ := resolverSmoothRightCutoffDerivBound (c / 2) c hc'c 1 (by norm_num)
  let Φ₂ := resolverSmoothRightCutoffDerivBound (c / 2) c hc'c 2 (by norm_num)
  let Φ := max 0 (max Φ₀ (max Φ₁ Φ₂))
  have hΦnn : 0 ≤ Φ := by
    dsimp [Φ]
    exact le_max_left 0 (max Φ₀ (max Φ₁ Φ₂))
  have hΦ₀_le : Φ₀ ≤ Φ := by
    dsimp [Φ]
    exact (le_max_left Φ₀ (max Φ₁ Φ₂)).trans
      (le_max_right 0 (max Φ₀ (max Φ₁ Φ₂)))
  have hΦ₁_le : Φ₁ ≤ Φ := by
    dsimp [Φ]
    exact ((le_max_left Φ₁ Φ₂).trans (le_max_right Φ₀ (max Φ₁ Φ₂))).trans
      (le_max_right 0 (max Φ₀ (max Φ₁ Φ₂)))
  have hΦ₂_le : Φ₂ ≤ Φ := by
    dsimp [Φ]
    exact ((le_max_right Φ₁ Φ₂).trans (le_max_right Φ₀ (max Φ₁ Φ₂))).trans
      (le_max_right 0 (max Φ₀ (max Φ₁ Φ₂)))
  have hΦ : ∀ r : ℕ, r ≤ 2 → ∀ t : ℝ,
      ‖iteratedFDeriv ℝ r (smoothRightCutoff (c / 2) c) t‖ ≤ Φ := by
    intro r hr t
    interval_cases r
    · exact (resolverSmoothRightCutoffDerivBound_spec hc'c
        (k := 0) (by norm_num) t).trans hΦ₀_le
    · exact (resolverSmoothRightCutoffDerivBound_spec hc'c
        (k := 1) (by norm_num) t).trans hΦ₁_le
    · exact (resolverSmoothRightCutoffDerivBound_spec hc'c
        (k := 2) (by norm_num) t).trans hΦ₂_le
  let Bt : ℕ → ℕ → ℝ := heatLevel0GradCoeffPowerBt Φ C₀ C₁ C₂
  have hBtp_eq : (fun i k => if k = 0 then 0 else Bt i k) = Bt := by
    funext i k
    by_cases hk : k = 0
    · subst k
      simp [Bt, heatLevel0GradCoeffPowerBt]
    · simp [Bt, heatLevel0GradCoeffPowerBt, hk]
  have hBt : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 → 1 ≤ k →
      ‖iteratedFDeriv ℝ i
        (fun s : ℝ => smoothRightCutoff (c / 2) c s *
          resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s) t‖ ≤ Bt i k := by
    intro i k t hi hk
    exact heatLevel0_cutoffResolverCoeff_iteratedFDeriv_power_bound_posMode
      (p := p) (u₀ := u₀) (M₀ := M₀) (a := c / 2) (c := c)
      (Φ := Φ) (C₀ := C₀) (C₁ := C₁) (C₂ := C₂)
      ha hc rfl hΦnn hΦ hC₀nn hC₁nn hC₂nn
      hu₀_bound hu₀_cont hfloor hC₀ hC₁ hC₂ hi hk (t := t)
  have hsumm : ∀ j : ℕ, (j : ℕ∞) ≤ 2 →
      Summable (boundedWeightJointGradMajorant
        (fun i k => if k = 0 then 0 else Bt i k) j) := by
    simpa [hBtp_eq] using heatLevel0GradCoeffPowerBt_grad_summable Φ C₀ C₁ C₂
  have hCutoff := (cutoffResolverGradSeries_contDiff_two_posModes_of_Bt
    (p := p) (u₀ := u₀) (M₀ := M₀)
    hu₀_bound hu₀_cont hfloor hc (Bt := Bt) hBt hsumm).contDiffAt (x := (s₀, x₀))
  have hEqCutoff := resolverGradSeries_eventuallyEq_cutoff (p := p)
    (u := conjugatePicardIter p u₀ 0) hc hs₀ (x₀ := x₀)
  have htime : {q : ℝ × ℝ | 0 < q.1} ∈ 𝓝 (s₀, x₀) :=
    (isOpen_Ioi.preimage continuous_fst).mem_nhds (lt_trans hc hs₀)
  have hspace : {q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) 1} ∈ 𝓝 (s₀, x₀) :=
    (isOpen_Ioo.preimage continuous_snd).mem_nhds hx₀
  have hEqLift : (fun q : ℝ × ℝ =>
      deriv (intervalDomainLift (coupledChemicalConcentration p
        (conjugatePicardIter p u₀ 0) q.1)) q.2) =ᶠ[𝓝 (s₀, x₀)]
    (fun q : ℝ × ℝ =>
      ∑' k : ℕ, resolverGradTerm p (conjugatePicardIter p u₀ 0) k q) := by
    filter_upwards [htime, hspace] with q hqt hqx
    exact resolverGradSeries_eq_lift_deriv_on_interior_heat
      (p := p) (u₀ := u₀) (M₀ := M₀)
      hu₀_bound hu₀_cont hu₀_pos hqt hqx
  exact hCutoff.congr_of_eventuallyEq (hEqLift.trans hEqCutoff)

end ShenWork.Paper2.HeatResolverJointC2Direct

end -- noncomputable section
