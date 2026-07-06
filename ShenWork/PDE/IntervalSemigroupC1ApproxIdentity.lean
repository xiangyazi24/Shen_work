import ShenWork.PDE.IntervalSemigroupUniform
import ShenWork.PDE.IntervalFullKernelSourceIBP
import ShenWork.PDE.IntervalConjugateKernelMassDefect

/-!
# Conditional C1 approximate identity for the homogeneous initial leg

This module isolates the easy metric part of the homogeneous C1 initial
approach.  The real analytic input, a derivative-commutation/IBP theorem for
the full Neumann semigroup, is kept as an explicit hypothesis.
-/

open MeasureTheory Filter Topology
open scoped Topology

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel

namespace ShenWork.IntervalSemigroupC1ApproxIdentity

noncomputable section

/-- The full Neumann semigroup only reads the source on `[0,1]`. -/
theorem intervalFullSemigroupOperator_congr_on_Icc
    {f g : ℝ → ℝ}
    (hfg : ∀ y ∈ Set.Icc (0 : ℝ) 1, f y = g y)
    (t x : ℝ) :
    intervalFullSemigroupOperator t f x =
      intervalFullSemigroupOperator t g x := by
  unfold intervalFullSemigroupOperator
  apply MeasureTheory.integral_congr_ae
  have hmem : ∀ᵐ y ∂(intervalMeasure 1), y ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [intervalMeasure, intervalSet]
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
      (Filter.Eventually.of_forall fun y hy => hy)
  filter_upwards [hmem] with y hy
  rw [hfg y hy]

/-- Uniform value approximate identity on `[0,1]` for a candidate derivative
profile. -/
def InitialLegDerivativeValueApprox (df : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |intervalFullSemigroupOperator t df x - df x| < ε

/-- Explicit derivative-commutation/IBP hypothesis for the homogeneous initial
leg.  This is the analytic theorem still missing from the current source-side
toolbox. -/
def InitialLegDerivativeCommutes (f df : ℝ → ℝ) : Prop :=
  ∀ {t : ℝ}, 0 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
    deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x =
      intervalFullSemigroupOperator t df x

/-- Uniform approximate identity on `[0,1]` for the conjugate-kernel
representation of the homogeneous initial-leg derivative.  This is the
remaining analytic input after applying source-side kernel IBP. -/
def InitialLegConjugateDerivativeApprox (df : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |-(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y) - df x| < ε

/-- Oscillation part of the conjugate-kernel approximate identity: the kernel
applied to `df y - df x` tends uniformly to zero. -/
def InitialLegConjugateOscillationControl (df : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |-(∫ y in (0 : ℝ)..1,
          (df y - df x) * intervalNeumannConjugateKernel t x y)| < ε

/-- Mass-defect part of the conjugate-kernel approximate identity, weighted by
`df x`.  This is where the endpoint compatibility `df 0 = 0` and `df 1 = 0`
matters for the closed interval. -/
def InitialLegConjugateMassDefectControl (df : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |df x * (-(∫ y in (0 : ℝ)..1,
          intervalNeumannConjugateKernel t x y) - 1)| < ε

/-- Interior-strip version of the conjugate-kernel approximate identity.  The
endpoint boundary layer is deliberately excluded; this is the part expected
from the standard Dirichlet heat-kernel approximate identity away from the
absorbing endpoints. -/
def InitialLegConjugateDerivativeInteriorApprox (df : ℝ → ℝ) : Prop :=
  ∀ η, 0 < η → η < (1 / 2 : ℝ) → ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
    ∀ x ∈ Set.Icc η (1 - η),
      |-(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y) - df x| < ε

/-- Endpoint smallness of the derivative profile.  For the Dirichlet/conjugate
kernel route this is supplied by continuity plus the compatibility conditions
`df 0 = 0` and `df 1 = 0`. -/
def InitialLegDerivativeEndpointSmall (df : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ η > 0, η < (1 / 2 : ℝ) ∧
    ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≤ η ∨ 1 - η ≤ x → |df x| < ε

/-- Endpoint-layer vanishing of the conjugate-kernel operator.  This isolates
the real boundary-layer kernel estimate from the easy endpoint compatibility
of the derivative profile. -/
def InitialLegConjugateEndpointOperatorVanish (df : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ η > 0, η < (1 / 2 : ℝ) ∧ ∃ δ > 0,
    ∀ t, 0 < t → t < δ → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      x ≤ η ∨ 1 - η ≤ x →
        |-(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y)| < ε

/-- Endpoint-layer version of `InitialLegConjugateDerivativeApprox`. -/
def InitialLegConjugateDerivativeEndpointApprox (df : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ η > 0, η < (1 / 2 : ℝ) ∧ ∃ δ > 0,
    ∀ t, 0 < t → t < δ → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      x ≤ η ∨ 1 - η ≤ x →
        |-(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y) - df x| < ε

/-- Absolute first moment of the conjugate kernel, dominated pointwise by the
full Neumann kernel's first moment. -/
theorem conjugateKernel_abs_moment_le
    {t : ℝ} (ht : 0 < t) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ y in (0 : ℝ)..1,
        |y - x| * |intervalNeumannConjugateKernel t x y|)
      ≤ 4 * t / Real.sqrt (4 * Real.pi * t) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hKtilde_int : IntervalIntegrable
      (fun y : ℝ => |y - x| * |intervalNeumannConjugateKernel t x y|)
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h01]
    exact ((continuous_abs.comp (continuous_id.sub continuous_const)).continuousOn.mul
      (continuousOn_conjugateKernel_snd ht x).abs)
  have hKfull_int : IntervalIntegrable
      (fun y : ℝ => |y - x| * intervalNeumannFullKernel t x y)
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h01]
    exact ((continuous_abs.comp (continuous_id.sub continuous_const)).continuousOn.mul
      (continuousOn_intervalNeumannFullKernel_snd ht x))
  calc
    (∫ y in (0 : ℝ)..1, |y - x| * |intervalNeumannConjugateKernel t x y|)
        ≤ ∫ y in (0 : ℝ)..1, |y - x| * intervalNeumannFullKernel t x y :=
      intervalIntegral.integral_mono_on h01 hKtilde_int hKfull_int
        (fun y _ => mul_le_mul_of_nonneg_left (abs_conjugateKernel_le ht x y) (abs_nonneg _))
    _ ≤ 4 * t / Real.sqrt (4 * Real.pi * t) :=
      ShenWork.IntervalSemigroupUniform.intervalNeumannFullKernel_abs_moment_le ht x hx

/-- Continuous derivative profiles have vanishing conjugate-kernel oscillation
term.  The proof uses only the `L¹` mass bound and the absolute first-moment
bound for the conjugate kernel. -/
theorem initialLegConjugateOscillationControl_of_continuousOn
    {df : ℝ → ℝ}
    (hdf_cont : ContinuousOn df (Set.Icc (0 : ℝ) 1)) :
    InitialLegConjugateOscillationControl df := by
  intro ε hε
  obtain ⟨M, hM_pos, hdfM⟩ :
      ∃ M : ℝ, 0 < M ∧ ∀ y ∈ Set.Icc (0 : ℝ) 1, |df y| ≤ M := by
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hdf_cont
    refine ⟨max B 1, by positivity, fun y hy => ?_⟩
    exact (Real.norm_eq_abs (df y) ▸ hB y hy).trans (le_max_left B 1)
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous
    (s := Set.Icc (0 : ℝ) 1) hdf_cont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η, hη_pos, hηdf⟩ := huc (ε / 2) (by linarith)
  set C : ℝ := 2 * M / η
  have hC_pos : 0 < C := by positivity
  have hlinmod : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |df y - df x| ≤ ε / 2 + C * |y - x| := by
    intro x hx y hy
    by_cases hclose : dist y x < η
    · have h1 := hηdf y hy x hx hclose
      rw [Real.dist_eq] at h1
      linarith [mul_nonneg hC_pos.le (abs_nonneg (y - x))]
    · have hdist_ge : η ≤ dist y x := le_of_not_gt hclose
      have hyx : η ≤ |y - x| := by rwa [Real.dist_eq] at hdist_ge
      have hab : |df y - df x| ≤ 2 * M := by
        have hfy := abs_le.mp (hdfM y hy)
        have hfx := abs_le.mp (hdfM x hx)
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      linarith [mul_le_mul_of_nonneg_left hyx hC_pos.le,
        show C * η = 2 * M by simp [C]; field_simp]
  set τ : ℝ := (ε / (4 * C)) ^ 2
  have hτ_pos : 0 < τ := by positivity
  refine ⟨τ, hτ_pos, ?_⟩
  intro t ht htτ x hx
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  let K : ℝ → ℝ := fun y => intervalNeumannConjugateKernel t x y
  have hdf_u : ContinuousOn df (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le h01] using hdf_cont
  have hK_u : ContinuousOn K (Set.uIcc (0 : ℝ) 1) := by
    simpa [K, Set.uIcc_of_le h01] using continuousOn_conjugateKernel_snd ht x
  have hdist_u : ContinuousOn (fun y : ℝ => |y - x|) (Set.uIcc (0 : ℝ) 1) :=
    (continuous_abs.comp (continuous_id.sub continuous_const)).continuousOn
  have hprod_ii : IntervalIntegrable
      (fun y : ℝ => (df y - df x) * K y) MeasureTheory.volume 0 1 :=
    ((hdf_u.sub continuousOn_const).mul hK_u).intervalIntegrable
  have hKabs_ii : IntervalIntegrable
      (fun y : ℝ => |K y|) MeasureTheory.volume 0 1 :=
    hK_u.abs.intervalIntegrable
  have hmoment_ii : IntervalIntegrable
      (fun y : ℝ => |y - x| * |K y|) MeasureTheory.volume 0 1 :=
    (hdist_u.mul hK_u.abs).intervalIntegrable
  have hcoef_u : ContinuousOn (fun y : ℝ => ε / 2 + C * |y - x|)
      (Set.uIcc (0 : ℝ) 1) :=
    continuousOn_const.add (continuousOn_const.mul hdist_u)
  have hmod_ii : IntervalIntegrable
      (fun y : ℝ => (ε / 2 + C * |y - x|) * |K y|)
      MeasureTheory.volume 0 1 :=
    (hcoef_u.mul hK_u.abs).intervalIntegrable
  have hsplit :
      (∫ y in (0 : ℝ)..1, (ε / 2 + C * |y - x|) * |K y|)
        = (ε / 2) * (∫ y in (0 : ℝ)..1, |K y|)
          + C * (∫ y in (0 : ℝ)..1, |y - x| * |K y|) := by
    rw [show (fun y : ℝ => (ε / 2 + C * |y - x|) * |K y|) =
        fun y : ℝ => (ε / 2) * |K y| + C * (|y - x| * |K y|) from by
      funext y
      ring]
    rw [intervalIntegral.integral_add (hKabs_ii.const_mul (ε / 2))
      (hmoment_ii.const_mul C), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have htail_bound : C * (4 * t / Real.sqrt (4 * Real.pi * t)) < ε / 2 := by
    have h4pit_pos : 0 < 4 * Real.pi * t := by positivity
    have hpi_ge : 4 * t ≤ 4 * Real.pi * t := by nlinarith [Real.pi_gt_three]
    have hsqrt4t : Real.sqrt (4 * t) = 2 * Real.sqrt t := by
      have h4t_eq : (4 : ℝ) * t = (2 * Real.sqrt t) * (2 * Real.sqrt t) := by
        have := Real.mul_self_sqrt ht.le
        nlinarith
      rw [show (4 : ℝ) * t = (2 * Real.sqrt t) * (2 * Real.sqrt t) from h4t_eq,
        Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt t)]
    have hmoment_le : 4 * t / Real.sqrt (4 * Real.pi * t) ≤ 2 * Real.sqrt t := by
      rw [div_le_iff₀ (Real.sqrt_pos_of_pos h4pit_pos)]
      calc
        4 * t = 2 * Real.sqrt t * Real.sqrt (4 * t) := by
          rw [hsqrt4t]
          nlinarith [Real.mul_self_sqrt ht.le]
        _ ≤ 2 * Real.sqrt t * Real.sqrt (4 * Real.pi * t) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hpi_ge) (by positivity)
    have hsqrt_bound : Real.sqrt t < ε / (4 * C) := by
      rw [← Real.sqrt_sq (show (0 : ℝ) ≤ ε / (4 * C) by positivity)]
      exact Real.sqrt_lt_sqrt ht.le htτ
    calc
      C * (4 * t / Real.sqrt (4 * Real.pi * t))
          ≤ C * (2 * Real.sqrt t) :=
        mul_le_mul_of_nonneg_left hmoment_le hC_pos.le
      _ < C * (2 * (ε / (4 * C))) :=
        mul_lt_mul_of_pos_left (by linarith) hC_pos
      _ = ε / 2 := by field_simp; ring
  calc
    |-(∫ y in (0 : ℝ)..1, (df y - df x) * intervalNeumannConjugateKernel t x y)|
        = |∫ y in (0 : ℝ)..1, (df y - df x) * K y| := by
      simp [K]
    _ ≤ ∫ y in (0 : ℝ)..1, |(df y - df x) * K y| :=
      intervalIntegral.abs_integral_le_integral_abs h01
    _ ≤ ∫ y in (0 : ℝ)..1, (ε / 2 + C * |y - x|) * |K y| := by
      apply intervalIntegral.integral_mono_on h01 hprod_ii.abs hmod_ii
      intro y hy
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hlinmod x hx y hy) (abs_nonneg _)
    _ = (ε / 2) * (∫ y in (0 : ℝ)..1, |K y|)
          + C * (∫ y in (0 : ℝ)..1, |y - x| * |K y|) := hsplit
    _ ≤ (ε / 2) * 1 + C * (4 * t / Real.sqrt (4 * Real.pi * t)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (conjugateKernel_L1_bound ht x) (by linarith))
        (mul_le_mul_of_nonneg_left
          (by simpa [K] using conjugateKernel_abs_moment_le ht hx) hC_pos.le)
    _ < ε := by
      linarith

/-- Endpoint-small bounded profiles have vanishing conjugate-kernel operator on
endpoint x-layers. -/
theorem initialLegConjugateEndpointOperatorVanish_of_endpointSmall_bound
    {df : ℝ → ℝ} {M : ℝ}
    (hdf_cont : ContinuousOn df (Set.Icc (0 : ℝ) 1))
    (hM : 0 ≤ M)
    (hdf_bound : ∀ y ∈ Set.Icc (0 : ℝ) 1, |df y| ≤ M)
    (hsmall : InitialLegDerivativeEndpointSmall df) :
    InitialLegConjugateEndpointOperatorVanish df := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases hsmall (ε / 2) hε2 with ⟨ηs, hηs_pos, hηs_lt, hsη⟩
  let η : ℝ := ηs / 2
  have hη_pos : 0 < η := by positivity
  have hη_lt : η < (1 / 2 : ℝ) := by
    dsimp [η]
    linarith
  set C : ℝ := 2 * M / ηs + 1
  have hA_nonneg : 0 ≤ 2 * M / ηs := by positivity
  have hA_le_C : 2 * M / ηs ≤ C := by
    dsimp [C]
    linarith
  have hC_pos : 0 < C := by
    dsimp [C]
    linarith
  have hlinear_absorb :
      ∀ {x y : ℝ}, ηs / 2 ≤ |y - x| → M ≤ C * |y - x| := by
    intro x y hdist
    have hbase : M ≤ (2 * M / ηs) * |y - x| := by
      calc
        M = (2 * M / ηs) * (ηs / 2) := by
          field_simp [ne_of_gt hηs_pos]
        _ ≤ (2 * M / ηs) * |y - x| :=
          mul_le_mul_of_nonneg_left hdist hA_nonneg
    have hCdist : (2 * M / ηs) * |y - x| ≤ C * |y - x| :=
      mul_le_mul_of_nonneg_right hA_le_C (abs_nonneg _)
    exact le_trans hbase hCdist
  have hpoint :
      ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≤ η ∨ 1 - η ≤ x →
        ∀ y ∈ Set.Icc (0 : ℝ) 1, |df y| ≤ ε / 2 + C * |y - x| := by
    intro x hx hxend y hy
    rcases hxend with hxleft | hxright
    · by_cases hynear : y ≤ ηs
      · exact le_trans (le_of_lt (hsη y hy (Or.inl hynear)))
          (le_add_of_nonneg_right (mul_nonneg hC_pos.le (abs_nonneg _)))
      · have hygt : ηs < y := lt_of_not_ge hynear
        have hdist : ηs / 2 ≤ |y - x| := by
          have hnonneg : 0 ≤ y - x := by
            dsimp [η] at hxleft
            linarith
          rw [abs_of_nonneg hnonneg]
          dsimp [η] at hxleft
          linarith
        have hdfM := hdf_bound y hy
        have htail := hlinear_absorb (x := x) (y := y) hdist
        linarith [le_trans hdfM htail]
    · by_cases hynear : 1 - ηs ≤ y
      · exact le_trans (le_of_lt (hsη y hy (Or.inr hynear)))
          (le_add_of_nonneg_right (mul_nonneg hC_pos.le (abs_nonneg _)))
      · have hylt : y < 1 - ηs := lt_of_not_ge hynear
        have hdist : ηs / 2 ≤ |y - x| := by
          have hnonpos : y - x ≤ 0 := by
            dsimp [η] at hxright
            linarith
          rw [abs_of_nonpos hnonpos]
          dsimp [η] at hxright
          linarith
        have hdfM := hdf_bound y hy
        have htail := hlinear_absorb (x := x) (y := y) hdist
        linarith [le_trans hdfM htail]
  set τ : ℝ := (ε / (4 * C)) ^ 2
  have hτ_pos : 0 < τ := by positivity
  refine ⟨η, hη_pos, hη_lt, τ, hτ_pos, ?_⟩
  intro t ht htτ x hx hxend
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  let K : ℝ → ℝ := fun y => intervalNeumannConjugateKernel t x y
  have hdf_u : ContinuousOn df (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le h01] using hdf_cont
  have hK_u : ContinuousOn K (Set.uIcc (0 : ℝ) 1) := by
    simpa [K, Set.uIcc_of_le h01] using continuousOn_conjugateKernel_snd ht x
  have hdist_u : ContinuousOn (fun y : ℝ => |y - x|) (Set.uIcc (0 : ℝ) 1) :=
    (continuous_abs.comp (continuous_id.sub continuous_const)).continuousOn
  have hprod_ii : IntervalIntegrable
      (fun y : ℝ => df y * K y) MeasureTheory.volume 0 1 :=
    (hdf_u.mul hK_u).intervalIntegrable
  have hKabs_ii : IntervalIntegrable
      (fun y : ℝ => |K y|) MeasureTheory.volume 0 1 :=
    hK_u.abs.intervalIntegrable
  have hmoment_ii : IntervalIntegrable
      (fun y : ℝ => |y - x| * |K y|) MeasureTheory.volume 0 1 :=
    (hdist_u.mul hK_u.abs).intervalIntegrable
  have hcoef_u : ContinuousOn (fun y : ℝ => ε / 2 + C * |y - x|)
      (Set.uIcc (0 : ℝ) 1) :=
    continuousOn_const.add (continuousOn_const.mul hdist_u)
  have hmod_ii : IntervalIntegrable
      (fun y : ℝ => (ε / 2 + C * |y - x|) * |K y|)
      MeasureTheory.volume 0 1 :=
    (hcoef_u.mul hK_u.abs).intervalIntegrable
  have hsplit :
      (∫ y in (0 : ℝ)..1, (ε / 2 + C * |y - x|) * |K y|)
        = (ε / 2) * (∫ y in (0 : ℝ)..1, |K y|)
          + C * (∫ y in (0 : ℝ)..1, |y - x| * |K y|) := by
    rw [show (fun y : ℝ => (ε / 2 + C * |y - x|) * |K y|) =
        fun y : ℝ => (ε / 2) * |K y| + C * (|y - x| * |K y|) from by
      funext y
      ring]
    rw [intervalIntegral.integral_add (hKabs_ii.const_mul (ε / 2))
      (hmoment_ii.const_mul C), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have htail_bound : C * (4 * t / Real.sqrt (4 * Real.pi * t)) < ε / 2 := by
    have h4pit_pos : 0 < 4 * Real.pi * t := by positivity
    have hpi_ge : 4 * t ≤ 4 * Real.pi * t := by nlinarith [Real.pi_gt_three]
    have hsqrt4t : Real.sqrt (4 * t) = 2 * Real.sqrt t := by
      have h4t_eq : (4 : ℝ) * t = (2 * Real.sqrt t) * (2 * Real.sqrt t) := by
        have := Real.mul_self_sqrt ht.le
        nlinarith
      rw [show (4 : ℝ) * t = (2 * Real.sqrt t) * (2 * Real.sqrt t) from h4t_eq,
        Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt t)]
    have hmoment_le : 4 * t / Real.sqrt (4 * Real.pi * t) ≤ 2 * Real.sqrt t := by
      rw [div_le_iff₀ (Real.sqrt_pos_of_pos h4pit_pos)]
      calc
        4 * t = 2 * Real.sqrt t * Real.sqrt (4 * t) := by
          rw [hsqrt4t]
          nlinarith [Real.mul_self_sqrt ht.le]
        _ ≤ 2 * Real.sqrt t * Real.sqrt (4 * Real.pi * t) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hpi_ge) (by positivity)
    have hsqrt_bound : Real.sqrt t < ε / (4 * C) := by
      rw [← Real.sqrt_sq (show (0 : ℝ) ≤ ε / (4 * C) by positivity)]
      exact Real.sqrt_lt_sqrt ht.le htτ
    calc
      C * (4 * t / Real.sqrt (4 * Real.pi * t))
          ≤ C * (2 * Real.sqrt t) :=
        mul_le_mul_of_nonneg_left hmoment_le hC_pos.le
      _ < C * (2 * (ε / (4 * C))) :=
        mul_lt_mul_of_pos_left (by linarith) hC_pos
      _ = ε / 2 := by field_simp; ring
  calc
    |-(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y)|
        = |∫ y in (0 : ℝ)..1, df y * K y| := by
      simp [K]
    _ ≤ ∫ y in (0 : ℝ)..1, |df y * K y| :=
      intervalIntegral.abs_integral_le_integral_abs h01
    _ ≤ ∫ y in (0 : ℝ)..1, (ε / 2 + C * |y - x|) * |K y| := by
      apply intervalIntegral.integral_mono_on h01 hprod_ii.abs hmod_ii
      intro y hy
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hpoint x hx hxend y hy) (abs_nonneg _)
    _ = (ε / 2) * (∫ y in (0 : ℝ)..1, |K y|)
          + C * (∫ y in (0 : ℝ)..1, |y - x| * |K y|) := hsplit
    _ ≤ (ε / 2) * 1 + C * (4 * t / Real.sqrt (4 * Real.pi * t)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (conjugateKernel_L1_bound ht x) (by linarith))
        (mul_le_mul_of_nonneg_left
          (by simpa [K] using conjugateKernel_abs_moment_le ht hx) hC_pos.le)
    _ < ε := by
      linarith

/-- A filter-form uniform conjugate/Dirichlet approximate identity immediately
supplies the epsilon-delta hypothesis consumed by the C1 initial-leg reducer. -/
theorem initialLegConjugateDerivativeApprox_of_tendstoUniformlyOn
    {df : ℝ → ℝ}
    (hlim : TendstoUniformlyOn
      (fun t x : ℝ =>
        -(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y))
      df (𝓝[>] (0 : ℝ)) (Set.Icc (0 : ℝ) 1)) :
    InitialLegConjugateDerivativeApprox df := by
  intro ε hε
  rw [Metric.tendstoUniformlyOn_iff] at hlim
  have hev := hlim ε hε
  rw [Filter.eventually_iff, mem_nhdsGT_iff_exists_Ioo_subset] at hev
  rcases hev with ⟨δ, hδpos, hδsub⟩
  refine ⟨δ, hδpos, ?_⟩
  intro t ht htδ x hx
  let I : ℝ := ∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y
  have hdist := hδsub ⟨ht, htδ⟩ x hx
  change |(-I) - df x| < ε
  have hrewrite : |(-I) - df x| = |df x + I| := by
    have harg : (-I) - df x = -(df x + I) := by ring
    rw [harg, abs_neg]
  rw [hrewrite]
  simpa [I, Real.dist_eq, add_comm, add_left_comm, add_assoc] using hdist

/-- Split reducer for `InitialLegConjugateDerivativeApprox`.

This theorem is algebra plus interval-integral linearity.  Positivity, mass
convergence, and tail/concentration estimates for the Dirichlet kernel remain
the true analytic obligations behind the two split controls. -/
theorem initialLegConjugateDerivativeApprox_of_splitControls
    {df : ℝ → ℝ}
    (hdf_cont : ContinuousOn df (Set.Icc (0 : ℝ) 1))
    (hosc : InitialLegConjugateOscillationControl df)
    (hmass : InitialLegConjugateMassDefectControl df) :
    InitialLegConjugateDerivativeApprox df := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases hosc (ε / 2) hε2 with ⟨δo, hδo_pos, ho⟩
  rcases hmass (ε / 2) hε2 with ⟨δm, hδm_pos, hm⟩
  refine ⟨min δo δm, lt_min hδo_pos hδm_pos, ?_⟩
  intro t ht htδ x hx
  have hto : t < δo := lt_of_lt_of_le htδ (min_le_left _ _)
  have htm : t < δm := lt_of_lt_of_le htδ (min_le_right _ _)
  have ho' := ho t ht hto x hx
  have hm' := hm t ht htm x hx
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  let K : ℝ → ℝ := fun y => intervalNeumannConjugateKernel t x y
  have hdf_u : ContinuousOn df (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le h01] using hdf_cont
  have hK_u : ContinuousOn K (Set.uIcc (0 : ℝ) 1) := by
    simpa [K, Set.uIcc_of_le h01] using continuousOn_conjugateKernel_snd ht x
  have hosc_int : IntervalIntegrable
      (fun y : ℝ => (df y - df x) * K y) MeasureTheory.volume 0 1 :=
    ((hdf_u.sub continuousOn_const).mul hK_u).intervalIntegrable
  have hconst_int : IntervalIntegrable
      (fun y : ℝ => df x * K y) MeasureTheory.volume 0 1 :=
    (continuousOn_const.mul hK_u).intervalIntegrable
  have hsplit :
      -(∫ y in (0 : ℝ)..1, df y * K y) - df x =
        (-(∫ y in (0 : ℝ)..1, (df y - df x) * K y)) +
          df x * (-(∫ y in (0 : ℝ)..1, K y) - 1) := by
    have hfun :
        (fun y : ℝ => df y * K y) =
          fun y : ℝ => (df y - df x) * K y + df x * K y := by
      funext y
      ring
    rw [hfun]
    rw [intervalIntegral.integral_add hosc_int hconst_int]
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [show
      (-(∫ y in (0 : ℝ)..1,
          df y * intervalNeumannConjugateKernel t x y) - df x) =
        (-(∫ y in (0 : ℝ)..1,
          (df y - df x) * intervalNeumannConjugateKernel t x y)) +
          df x * (-(∫ y in (0 : ℝ)..1,
            intervalNeumannConjugateKernel t x y) - 1) by
        simpa [K] using hsplit]
  exact lt_of_le_of_lt (abs_add_le _ _) (by
    calc
      |-(∫ y in (0 : ℝ)..1,
          (df y - df x) * intervalNeumannConjugateKernel t x y)| +
          |df x * (-(∫ y in (0 : ℝ)..1,
            intervalNeumannConjugateKernel t x y) - 1)|
          < ε / 2 + ε / 2 := add_lt_add ho' hm'
      _ = ε := by ring)

/-- Continuity plus zero endpoint values supply the endpoint-small compatibility
needed by the Dirichlet/conjugate-kernel route. -/
theorem initialLegDerivativeEndpointSmall_of_continuousOn_zero
    {df : ℝ → ℝ}
    (hdf_cont : ContinuousOn df (Set.Icc (0 : ℝ) 1))
    (hdf_zero : df 0 = 0) (hdf_one : df 1 = 0) :
    InitialLegDerivativeEndpointSmall df := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hcont0 := Metric.continuousWithinAt_iff.mp
    (hdf_cont.continuousWithinAt (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1))
  have hcont1 := Metric.continuousWithinAt_iff.mp
    (hdf_cont.continuousWithinAt (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1))
  rcases hcont0 (ε / 2) hε2 with ⟨η0, hη0_pos, hη0⟩
  rcases hcont1 (ε / 2) hε2 with ⟨η1, hη1_pos, hη1⟩
  let η : ℝ := min (min (η0 / 2) (η1 / 2)) (1 / 4)
  have hη_pos : 0 < η := by
    dsimp [η]
    exact lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
  have hη_le_η0half : η ≤ η0 / 2 := by
    dsimp [η]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hη_le_η1half : η ≤ η1 / 2 := by
    dsimp [η]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hη_lt_η0 : η < η0 := by linarith
  have hη_lt_η1 : η < η1 := by linarith
  have hη_lt_half : η < (1 / 2 : ℝ) := by
    have hη_le_quarter : η ≤ (1 / 4 : ℝ) := by
      dsimp [η]
      exact min_le_right _ _
    linarith
  refine ⟨η, hη_pos, hη_lt_half, ?_⟩
  intro x hx hxend
  rcases hxend with hxleft | hxright
  · have hx_lt_η0 : x < η0 := lt_of_le_of_lt hxleft hη_lt_η0
    have hdist : dist x (0 : ℝ) < η0 := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
      exact hx_lt_η0
    have hval := hη0 hx hdist
    exact lt_trans (by simpa [Real.dist_eq, hdf_zero] using hval) (by linarith)
  · have hx_dist : dist x (1 : ℝ) < η1 := by
      rw [Real.dist_eq]
      have hxsub_nonpos : x - 1 ≤ 0 := by linarith [hx.2]
      rw [abs_of_nonpos hxsub_nonpos]
      have hnear : 1 - x ≤ η := by linarith
      linarith
    have hval := hη1 hx hx_dist
    exact lt_trans (by simpa [Real.dist_eq, hdf_one] using hval) (by linarith)

/-- Endpoint-layer operator vanishing plus endpoint-small derivative data give
the endpoint-layer approximate identity. -/
theorem initialLegConjugateDerivativeEndpointApprox_of_operatorVanish_endpointSmall
    {df : ℝ → ℝ}
    (hop : InitialLegConjugateEndpointOperatorVanish df)
    (hsmall : InitialLegDerivativeEndpointSmall df) :
    InitialLegConjugateDerivativeEndpointApprox df := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases hop (ε / 2) hε2 with ⟨ηop, hηop_pos, hηop_lt, δ, hδ_pos, hopη⟩
  rcases hsmall (ε / 2) hε2 with ⟨ηs, hηs_pos, hηs_lt, hsη⟩
  let η : ℝ := min ηop ηs
  have hη_pos : 0 < η := by
    dsimp [η]
    exact lt_min hηop_pos hηs_pos
  have hη_lt : η < (1 / 2 : ℝ) := by
    have hle : η ≤ ηop := by dsimp [η]; exact min_le_left _ _
    exact lt_of_le_of_lt hle hηop_lt
  refine ⟨η, hη_pos, hη_lt, δ, hδ_pos, ?_⟩
  intro t ht htδ x hx hxend
  have hxend_op : x ≤ ηop ∨ 1 - ηop ≤ x := by
    rcases hxend with hxleft | hxright
    · exact Or.inl (le_trans hxleft (by dsimp [η]; exact min_le_left _ _))
    · exact Or.inr (by
        have hle : η ≤ ηop := by dsimp [η]; exact min_le_left _ _
        linarith)
  have hxend_s : x ≤ ηs ∨ 1 - ηs ≤ x := by
    rcases hxend with hxleft | hxright
    · exact Or.inl (le_trans hxleft (by dsimp [η]; exact min_le_right _ _))
    · exact Or.inr (by
        have hle : η ≤ ηs := by dsimp [η]; exact min_le_right _ _
        linarith)
  have hop_bound := hopη t ht htδ x hx hxend_op
  have hs_bound := hsη x hx hxend_s
  have htri :
      |-(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y) - df x|
        ≤ |-(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y)| +
            |df x| := by
    exact abs_sub _ _
  calc
    |-(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y) - df x|
        ≤ |-(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y)| +
            |df x| := htri
    _ < ε / 2 + ε / 2 := add_lt_add hop_bound hs_bound
    _ = ε := by ring

/-- Continuous endpoint-compatible bounded profiles satisfy the endpoint-layer
conjugate approximate identity. -/
theorem initialLegConjugateDerivativeEndpointApprox_of_continuousOn_zero_bound
    {df : ℝ → ℝ} {M : ℝ}
    (hdf_cont : ContinuousOn df (Set.Icc (0 : ℝ) 1))
    (hdf_zero : df 0 = 0) (hdf_one : df 1 = 0)
    (hM : 0 ≤ M)
    (hdf_bound : ∀ y ∈ Set.Icc (0 : ℝ) 1, |df y| ≤ M) :
    InitialLegConjugateDerivativeEndpointApprox df := by
  have hsmall : InitialLegDerivativeEndpointSmall df :=
    initialLegDerivativeEndpointSmall_of_continuousOn_zero hdf_cont hdf_zero hdf_one
  exact initialLegConjugateDerivativeEndpointApprox_of_operatorVanish_endpointSmall
    (initialLegConjugateEndpointOperatorVanish_of_endpointSmall_bound
      hdf_cont hM hdf_bound hsmall)
    hsmall

/-- Continuous derivative profiles satisfy the conjugate-kernel approximate
identity uniformly on every interior strip. -/
theorem initialLegConjugateDerivativeInteriorApprox_of_continuousOn
    {df : ℝ → ℝ}
    (hdf_cont : ContinuousOn df (Set.Icc (0 : ℝ) 1)) :
    InitialLegConjugateDerivativeInteriorApprox df := by
  obtain ⟨M, hM_pos, hdfM⟩ :
      ∃ M : ℝ, 0 < M ∧ ∀ y ∈ Set.Icc (0 : ℝ) 1, |df y| ≤ M := by
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hdf_cont
    refine ⟨max B 1, by positivity, fun y hy => ?_⟩
    exact (Real.norm_eq_abs (df y) ▸ hB y hy).trans (le_max_left B 1)
  have hosc := initialLegConjugateOscillationControl_of_continuousOn hdf_cont
  intro η hη_pos _hη_lt ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases hosc (ε / 2) hε2 with ⟨δo, hδo_pos, ho⟩
  set δm : ℝ := (ε * η / (16 * M)) ^ 2 with hδm_def
  have hδm_pos : 0 < δm := by positivity
  refine ⟨min δo δm, lt_min hδo_pos hδm_pos, ?_⟩
  intro t ht htδ x hxint
  have hto : t < δo := lt_of_lt_of_le htδ (min_le_left _ _)
  have htm : t < δm := lt_of_lt_of_le htδ (min_le_right _ _)
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨le_trans hη_pos.le hxint.1, by linarith [hxint.2, hη_pos.le]⟩
  have ho' := ho t ht hto x hxIcc
  let R : ℝ := ∫ y in (0 : ℝ)..1, intervalNeumannReflectedKernelPart t x y
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    exact intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (fun y => reflectedKernelPart_nonneg ht x y)
  have hR_bound : R ≤ (2 * Real.sqrt t) / η := by
    dsimp [R]
    exact reflectedKernelPart_integral_le_two_sqrt_div ht hη_pos hxint
  have htarget_nonneg : 0 ≤ ε * η / (16 * M) := by positivity
  have hsqrt_bound : Real.sqrt t < ε * η / (16 * M) := by
    rw [← Real.sqrt_sq htarget_nonneg]
    rw [hδm_def] at htm
    exact Real.sqrt_lt_sqrt ht.le htm
  have hmass_small : M * (2 * R) < ε / 2 := by
    have hR2 : 2 * R ≤ 2 * ((2 * Real.sqrt t) / η) :=
      mul_le_mul_of_nonneg_left hR_bound (by norm_num)
    have hM2 : M * (2 * R) ≤ M * (2 * ((2 * Real.sqrt t) / η)) :=
      mul_le_mul_of_nonneg_left hR2 hM_pos.le
    have hprod : 4 * M * Real.sqrt t < ε * η / 4 := by
      calc
        4 * M * Real.sqrt t < 4 * M * (ε * η / (16 * M)) :=
          mul_lt_mul_of_pos_left hsqrt_bound (by positivity)
        _ = ε * η / 4 := by
          field_simp [ne_of_gt hM_pos]
          ring
    have hdiv : (4 * M * Real.sqrt t) / η < ε / 4 := by
      rw [div_lt_iff₀ hη_pos]
      calc
        4 * M * Real.sqrt t < ε * η / 4 := hprod
        _ = (ε / 4) * η := by ring
    have htail : M * (2 * ((2 * Real.sqrt t) / η)) < ε / 2 := by
      calc
        M * (2 * ((2 * Real.sqrt t) / η))
            = (4 * M * Real.sqrt t) / η := by
          field_simp [ne_of_gt hη_pos]
          ring
        _ < ε / 4 := hdiv
        _ < ε / 2 := by linarith
    exact lt_of_le_of_lt hM2 htail
  have hmass_term :
      |df x * (-(∫ y in (0 : ℝ)..1, intervalNeumannConjugateKernel t x y) - 1)|
        < ε / 2 := by
    have hid := conjugateKernel_massDefect_eq_neg_two_reflectedMass ht x
    calc
      |df x * (-(∫ y in (0 : ℝ)..1, intervalNeumannConjugateKernel t x y) - 1)|
          = |df x * (-2 * R)| := by
        rw [hid]
      _ = |df x| * (2 * R) := by
        rw [abs_mul]
        have hneg2R : |-2 * R| = 2 * R := by
          rw [abs_mul, abs_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0),
            abs_of_nonneg hR_nonneg]
          ring
        rw [hneg2R]
      _ ≤ M * (2 * R) :=
        mul_le_mul_of_nonneg_right (hdfM x hxIcc)
          (mul_nonneg (by norm_num) hR_nonneg)
      _ < ε / 2 := hmass_small
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  let K : ℝ → ℝ := fun y => intervalNeumannConjugateKernel t x y
  have hdf_u : ContinuousOn df (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le h01] using hdf_cont
  have hK_u : ContinuousOn K (Set.uIcc (0 : ℝ) 1) := by
    simpa [K, Set.uIcc_of_le h01] using continuousOn_conjugateKernel_snd ht x
  have hosc_int : IntervalIntegrable
      (fun y : ℝ => (df y - df x) * K y) MeasureTheory.volume 0 1 :=
    ((hdf_u.sub continuousOn_const).mul hK_u).intervalIntegrable
  have hconst_int : IntervalIntegrable
      (fun y : ℝ => df x * K y) MeasureTheory.volume 0 1 :=
    (continuousOn_const.mul hK_u).intervalIntegrable
  have hsplit :
      -(∫ y in (0 : ℝ)..1, df y * K y) - df x =
        (-(∫ y in (0 : ℝ)..1, (df y - df x) * K y)) +
          df x * (-(∫ y in (0 : ℝ)..1, K y) - 1) := by
    have hfun :
        (fun y : ℝ => df y * K y) =
          fun y : ℝ => (df y - df x) * K y + df x * K y := by
      funext y
      ring
    rw [hfun]
    rw [intervalIntegral.integral_add hosc_int hconst_int]
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [show
      (-(∫ y in (0 : ℝ)..1,
          df y * intervalNeumannConjugateKernel t x y) - df x) =
        (-(∫ y in (0 : ℝ)..1,
          (df y - df x) * intervalNeumannConjugateKernel t x y)) +
          df x * (-(∫ y in (0 : ℝ)..1,
            intervalNeumannConjugateKernel t x y) - 1) by
        simpa [K] using hsplit]
  exact lt_of_le_of_lt (abs_add_le _ _) (by
    calc
      |-(∫ y in (0 : ℝ)..1,
          (df y - df x) * intervalNeumannConjugateKernel t x y)| +
          |df x * (-(∫ y in (0 : ℝ)..1,
            intervalNeumannConjugateKernel t x y) - 1)|
          < ε / 2 + ε / 2 := add_lt_add ho' hmass_term
      _ = ε := by ring)

/-- Patching reducer: interior-strip convergence plus endpoint-layer convergence
prove the closed-interval conjugate-kernel approximate identity. -/
theorem initialLegConjugateDerivativeApprox_of_interior_endpoint
    {df : ℝ → ℝ}
    (hinterior : InitialLegConjugateDerivativeInteriorApprox df)
    (hendpoint : InitialLegConjugateDerivativeEndpointApprox df) :
    InitialLegConjugateDerivativeApprox df := by
  intro ε hε
  rcases hendpoint ε hε with ⟨η, hη_pos, hη_lt, δe, hδe_pos, he⟩
  rcases hinterior η hη_pos hη_lt ε hε with ⟨δi, hδi_pos, hi⟩
  let δ : ℝ := min δe δi
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min hδe_pos hδi_pos
  refine ⟨δ, hδ_pos, ?_⟩
  intro t ht htδ x hx
  have htδe : t < δe := lt_of_lt_of_le htδ (by dsimp [δ]; exact min_le_left _ _)
  have htδi : t < δi := lt_of_lt_of_le htδ (by dsimp [δ]; exact min_le_right _ _)
  by_cases hxleft : x ≤ η
  · exact he t ht htδe x hx (Or.inl hxleft)
  · by_cases hxright : 1 - η ≤ x
    · exact he t ht htδe x hx (Or.inr hxright)
    · have hxint : x ∈ Set.Icc η (1 - η) := by
        exact ⟨le_of_lt (lt_of_not_ge hxleft), le_of_lt (lt_of_not_ge hxright)⟩
      exact hi t ht htδi x hxint

/-- Continuous endpoint-compatible bounded profiles satisfy the full
closed-interval conjugate-kernel approximate identity. -/
theorem initialLegConjugateDerivativeApprox_of_continuousOn_zero_bound
    {df : ℝ → ℝ} {M : ℝ}
    (hdf_cont : ContinuousOn df (Set.Icc (0 : ℝ) 1))
    (hdf_zero : df 0 = 0) (hdf_one : df 1 = 0)
    (hM : 0 ≤ M)
    (hdf_bound : ∀ y ∈ Set.Icc (0 : ℝ) 1, |df y| ≤ M) :
    InitialLegConjugateDerivativeApprox df :=
  initialLegConjugateDerivativeApprox_of_interior_endpoint
    (initialLegConjugateDerivativeInteriorApprox_of_continuousOn hdf_cont)
    (initialLegConjugateDerivativeEndpointApprox_of_continuousOn_zero_bound
      hdf_cont hdf_zero hdf_one hM hdf_bound)

/-- A continuous real profile on `[0,1]` has a finite absolute bound. -/
theorem continuousOn_Icc_abs_bound
    {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Set.Icc (0 : ℝ) 1, |f y| ≤ M := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf_cont
  refine ⟨max B 0, le_max_right B 0, ?_⟩
  intro y hy
  exact (Real.norm_eq_abs (f y) ▸ hB y hy).trans (le_max_left B 0)

/-- A continuous real profile on `[0,1]` is interval-integrable. -/
theorem continuousOn_Icc_intervalIntegrable
    {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    IntervalIntegrable f MeasureTheory.volume (0 : ℝ) 1 := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hf_u : ContinuousOn f (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le h01] using hf_cont
  exact hf_u.intervalIntegrable

/-- Continuous endpoint-compatible derivative profiles satisfy the full
closed-interval conjugate-kernel approximate identity, with boundedness inferred
from compactness of `[0,1]`. -/
theorem initialLegConjugateDerivativeApprox_of_continuousOn_zero
    {df : ℝ → ℝ}
    (hdf_cont : ContinuousOn df (Set.Icc (0 : ℝ) 1))
    (hdf_zero : df 0 = 0) (hdf_one : df 1 = 0) :
    InitialLegConjugateDerivativeApprox df := by
  obtain ⟨M, hM, hdf_bound⟩ := continuousOn_Icc_abs_bound hdf_cont
  exact initialLegConjugateDerivativeApprox_of_continuousOn_zero_bound
    hdf_cont hdf_zero hdf_one hM hdf_bound

/-- Continuous endpoint-compatible derivative profiles have vanishing endpoint
operator layer, with boundedness inferred from compactness of `[0,1]`. -/
theorem initialLegConjugateEndpointOperatorVanish_of_continuousOn_zero
    {df : ℝ → ℝ}
    (hdf_cont : ContinuousOn df (Set.Icc (0 : ℝ) 1))
    (hdf_zero : df 0 = 0) (hdf_one : df 1 = 0) :
    InitialLegConjugateEndpointOperatorVanish df := by
  obtain ⟨M, hM, hdf_bound⟩ := continuousOn_Icc_abs_bound hdf_cont
  exact initialLegConjugateEndpointOperatorVanish_of_endpointSmall_bound
    hdf_cont hM hdf_bound
    (initialLegDerivativeEndpointSmall_of_continuousOn_zero
      hdf_cont hdf_zero hdf_one)

/-- Continuous endpoint-compatible derivative profiles satisfy the endpoint
layer conjugate approximate identity, with boundedness inferred from compactness
of `[0,1]`. -/
theorem initialLegConjugateDerivativeEndpointApprox_of_continuousOn_zero
    {df : ℝ → ℝ}
    (hdf_cont : ContinuousOn df (Set.Icc (0 : ℝ) 1))
    (hdf_zero : df 0 = 0) (hdf_one : df 1 = 0) :
    InitialLegConjugateDerivativeEndpointApprox df := by
  have hsmall : InitialLegDerivativeEndpointSmall df :=
    initialLegDerivativeEndpointSmall_of_continuousOn_zero hdf_cont hdf_zero hdf_one
  exact initialLegConjugateDerivativeEndpointApprox_of_operatorVanish_endpointSmall
    (initialLegConjugateEndpointOperatorVanish_of_continuousOn_zero
      hdf_cont hdf_zero hdf_one)
    hsmall

/-- If the derivative field commutes with the homogeneous semigroup leg and the
candidate derivative profile has value approximate identity, then the
homogeneous C1 initial approach follows. -/
theorem initialLegC1Approx_of_valueApprox_of_commute
    {f df : ℝ → ℝ}
    (happrox : InitialLegDerivativeValueApprox df)
    (hcomm : InitialLegDerivativeCommutes f df) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x - df x| < ε := by
  intro ε hε
  rcases happrox ε hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro t ht htδ x hx
  simpa [hcomm (t := t) ht x hx] using hδ t ht htδ x hx

/-- The public source-IBP identity reduces homogeneous C1 initial approach to
the conjugate-kernel approximate identity for the derivative profile. -/
theorem initialLegC1Approx_of_conjugateApprox_of_sourceIBP
    {f df : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    {Cf : ℝ} (hf_bound : ∀ y, |f y| ≤ Cf)
    (hf_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt f (df y) y)
    (hdf_int : IntervalIntegrable df MeasureTheory.volume 0 1)
    (happrox : InitialLegConjugateDerivativeApprox df) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x - df x| < ε := by
  intro ε hε
  rcases happrox ε hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro t ht htδ x hx
  have hderiv :
      deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x =
        -(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y) :=
    deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_source_integral
      (t := t) ht (Q := f) (Q' := df) hf_meas hf_bound hf_deriv hdf_int x
  rw [hderiv]
  exact hδ t ht htδ x hx

/-- Source-IBP reducer with the conjugate approximate identity produced from
continuity, endpoint compatibility, and boundedness of the derivative profile. -/
theorem initialLegC1Approx_of_sourceIBP_continuousOn_zero_bound
    {f df : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    {Cf : ℝ} (hf_bound : ∀ y, |f y| ≤ Cf)
    (hf_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt f (df y) y)
    (hdf_int : IntervalIntegrable df MeasureTheory.volume 0 1)
    (hdf_cont : ContinuousOn df (Set.Icc (0 : ℝ) 1))
    (hdf_zero : df 0 = 0) (hdf_one : df 1 = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hdf_bound : ∀ y ∈ Set.Icc (0 : ℝ) 1, |df y| ≤ M) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x - df x| < ε :=
  initialLegC1Approx_of_conjugateApprox_of_sourceIBP
    hf_meas hf_bound hf_deriv hdf_int
    (initialLegConjugateDerivativeApprox_of_continuousOn_zero_bound
      hdf_cont hdf_zero hdf_one hM hdf_bound)

/-- Source-IBP reducer with derivative-profile integrability and boundedness
inferred from continuity on `[0,1]`. -/
theorem initialLegC1Approx_of_sourceIBP_continuousOn_zero
    {f df : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    {Cf : ℝ} (hf_bound : ∀ y, |f y| ≤ Cf)
    (hf_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt f (df y) y)
    (hdf_cont : ContinuousOn df (Set.Icc (0 : ℝ) 1))
    (hdf_zero : df 0 = 0) (hdf_one : df 1 = 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x - df x| < ε :=
  initialLegC1Approx_of_conjugateApprox_of_sourceIBP
    hf_meas hf_bound hf_deriv
    (continuousOn_Icc_intervalIntegrable hdf_cont)
    (initialLegConjugateDerivativeApprox_of_continuousOn_zero
      hdf_cont hdf_zero hdf_one)

/-- Source-IBP reducer through a global C1 representative `Q` that agrees with
the desired source `f` on `[0,1]`.  This is the safer form for zero-extended
interval data, whose raw lift need not be globally differentiable at the
endpoints. -/
theorem initialLegC1Approx_of_conjugateApprox_of_Icc_repr
    {f Q dQ : ℝ → ℝ}
    (hfQ : ∀ y ∈ Set.Icc (0 : ℝ) 1, f y = Q y)
    (hQ_meas : AEStronglyMeasurable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ_bound : ∀ y, |Q y| ≤ CQ)
    (hQ_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Q (dQ y) y)
    (hdQ_int : IntervalIntegrable dQ MeasureTheory.volume 0 1)
    (happrox : InitialLegConjugateDerivativeApprox dQ) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x - dQ x| < ε := by
  intro ε hε
  rcases happrox ε hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro t ht htδ x hx
  have hfun :
      (fun z : ℝ => intervalFullSemigroupOperator t f z) =
        fun z : ℝ => intervalFullSemigroupOperator t Q z := by
    funext z
    exact intervalFullSemigroupOperator_congr_on_Icc hfQ t z
  rw [hfun]
  have hderiv :
      deriv (fun z : ℝ => intervalFullSemigroupOperator t Q z) x =
        -(∫ y in (0 : ℝ)..1, dQ y * intervalNeumannConjugateKernel t x y) :=
    deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_source_integral
      (t := t) ht (Q := Q) (Q' := dQ) hQ_meas hQ_bound hQ_deriv hdQ_int x
  rw [hderiv]
  exact hδ t ht htδ x hx

/-- Representative-form source-IBP reducer with the conjugate approximate
identity produced from local derivative compatibility data. -/
theorem initialLegC1Approx_of_Icc_repr_continuousOn_zero_bound
    {f Q dQ : ℝ → ℝ}
    (hfQ : ∀ y ∈ Set.Icc (0 : ℝ) 1, f y = Q y)
    (hQ_meas : AEStronglyMeasurable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ_bound : ∀ y, |Q y| ≤ CQ)
    (hQ_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Q (dQ y) y)
    (hdQ_int : IntervalIntegrable dQ MeasureTheory.volume 0 1)
    (hdQ_cont : ContinuousOn dQ (Set.Icc (0 : ℝ) 1))
    (hdQ_zero : dQ 0 = 0) (hdQ_one : dQ 1 = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hdQ_bound : ∀ y ∈ Set.Icc (0 : ℝ) 1, |dQ y| ≤ M) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x - dQ x| < ε :=
  initialLegC1Approx_of_conjugateApprox_of_Icc_repr
    hfQ hQ_meas hQ_bound hQ_deriv hdQ_int
    (initialLegConjugateDerivativeApprox_of_continuousOn_zero_bound
      hdQ_cont hdQ_zero hdQ_one hM hdQ_bound)

/-- Representative-form source-IBP reducer with derivative-profile
integrability and boundedness inferred from continuity on `[0,1]`. -/
theorem initialLegC1Approx_of_Icc_repr_continuousOn_zero
    {f Q dQ : ℝ → ℝ}
    (hfQ : ∀ y ∈ Set.Icc (0 : ℝ) 1, f y = Q y)
    (hQ_meas : AEStronglyMeasurable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ_bound : ∀ y, |Q y| ≤ CQ)
    (hQ_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Q (dQ y) y)
    (hdQ_cont : ContinuousOn dQ (Set.Icc (0 : ℝ) 1))
    (hdQ_zero : dQ 0 = 0) (hdQ_one : dQ 1 = 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x - dQ x| < ε :=
  initialLegC1Approx_of_conjugateApprox_of_Icc_repr
    hfQ hQ_meas hQ_bound hQ_deriv
    (continuousOn_Icc_intervalIntegrable hdQ_cont)
    (initialLegConjugateDerivativeApprox_of_continuousOn_zero
      hdQ_cont hdQ_zero hdQ_one)

/-- The existing uniform value approximate identity supplies
`InitialLegDerivativeValueApprox` for a globally continuous derivative
representative. -/
theorem derivativeValueApprox_of_continuous
    (df : ℝ → ℝ) (hdf : Continuous df) :
    InitialLegDerivativeValueApprox df := by
  intro ε hε
  have htend :=
    ShenWork.IntervalSemigroupUniform.intervalFullSemigroup_tendstoUniformlyOn df hdf
  rw [Metric.tendstoUniformlyOn_iff] at htend
  have hev := htend ε hε
  rw [Filter.eventually_iff, mem_nhdsGT_iff_exists_Ioo_subset] at hev
  rcases hev with ⟨δ, hδmem, hδsub⟩
  refine ⟨δ, hδmem, ?_⟩
  intro t ht htδ x hx
  have hdist := hδsub ⟨ht, htδ⟩ x hx
  simpa [Real.dist_eq, abs_sub_comm] using hdist

/-- Domain-facing conditional homogeneous C1 initial approach.  This is the
metric wrapper needed by the zero-start derivative route once the genuine
commutation/IBP theorem is supplied. -/
theorem intervalFullSemigroup_initialLegC1Approx_of_global_deriv_continuous_of_commute
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀x_cont : Continuous (fun x : ℝ => deriv (intervalDomainLift u₀) x))
    (hcomm : InitialLegDerivativeCommutes
      (intervalDomainLift u₀)
      (fun x : ℝ => deriv (intervalDomainLift u₀) x)) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ =>
            intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x -
          deriv (intervalDomainLift u₀) x| < ε :=
  initialLegC1Approx_of_valueApprox_of_commute
    (derivativeValueApprox_of_continuous
      (fun x : ℝ => deriv (intervalDomainLift u₀) x) hu₀x_cont)
    hcomm

/-- Domain-facing source-IBP reducer for the homogeneous C1 initial approach.
The derivative profile `du₀` is explicit, and the only convergence hypothesis is
the conjugate-kernel approximate identity for `du₀`. -/
theorem intervalFullSemigroup_initialLegC1Approx_of_conjugateApprox
    {u₀ : intervalDomainPoint → ℝ} {du₀ : ℝ → ℝ}
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {Cu₀ : ℝ} (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ Cu₀)
    (hu₀_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (intervalDomainLift u₀) (du₀ y) y)
    (hdu₀_int : IntervalIntegrable du₀ MeasureTheory.volume 0 1)
    (happrox : InitialLegConjugateDerivativeApprox du₀) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ =>
            intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x -
          du₀ x| < ε :=
  initialLegC1Approx_of_conjugateApprox_of_sourceIBP
    hu₀_meas hu₀_bound hu₀_deriv hdu₀_int happrox

/-- Domain-facing source-IBP reducer with no explicit conjugate-approximation
hypothesis: it is produced from continuity, endpoint compatibility, and
boundedness of the derivative profile. -/
theorem intervalFullSemigroup_initialLegC1Approx_of_sourceIBP_continuousOn_zero_bound
    {u₀ : intervalDomainPoint → ℝ} {du₀ : ℝ → ℝ}
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {Cu₀ : ℝ} (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ Cu₀)
    (hu₀_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (intervalDomainLift u₀) (du₀ y) y)
    (hdu₀_int : IntervalIntegrable du₀ MeasureTheory.volume 0 1)
    (hdu₀_cont : ContinuousOn du₀ (Set.Icc (0 : ℝ) 1))
    (hdu₀_zero : du₀ 0 = 0) (hdu₀_one : du₀ 1 = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hdu₀_bound : ∀ y ∈ Set.Icc (0 : ℝ) 1, |du₀ y| ≤ M) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ =>
            intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x -
          du₀ x| < ε :=
  initialLegC1Approx_of_sourceIBP_continuousOn_zero_bound
    hu₀_meas hu₀_bound hu₀_deriv hdu₀_int
    hdu₀_cont hdu₀_zero hdu₀_one hM hdu₀_bound

/-- Domain-facing source-IBP reducer with derivative-profile integrability and
boundedness inferred from continuity on `[0,1]`. -/
theorem intervalFullSemigroup_initialLegC1Approx_of_sourceIBP_continuousOn_zero
    {u₀ : intervalDomainPoint → ℝ} {du₀ : ℝ → ℝ}
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {Cu₀ : ℝ} (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ Cu₀)
    (hu₀_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (intervalDomainLift u₀) (du₀ y) y)
    (hdu₀_cont : ContinuousOn du₀ (Set.Icc (0 : ℝ) 1))
    (hdu₀_zero : du₀ 0 = 0) (hdu₀_one : du₀ 1 = 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ =>
            intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x -
          du₀ x| < ε :=
  initialLegC1Approx_of_sourceIBP_continuousOn_zero
    hu₀_meas hu₀_bound hu₀_deriv hdu₀_cont hdu₀_zero hdu₀_one

/-- Domain-facing representative form for interval initial data.  The global
representative `Q` supplies the differentiability required by source IBP, while
the semigroup still acts on the original zero-extended interval source. -/
theorem intervalFullSemigroup_initialLegC1Approx_of_Icc_repr_conjugateApprox
    {u₀ : intervalDomainPoint → ℝ} {Q du₀ : ℝ → ℝ}
    (hu₀Q : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift u₀ y = Q y)
    (hQ_meas : AEStronglyMeasurable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ_bound : ∀ y, |Q y| ≤ CQ)
    (hQ_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Q (du₀ y) y)
    (hdu₀_int : IntervalIntegrable du₀ MeasureTheory.volume 0 1)
    (happrox : InitialLegConjugateDerivativeApprox du₀) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ =>
            intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x -
          du₀ x| < ε :=
  initialLegC1Approx_of_conjugateApprox_of_Icc_repr
    hu₀Q hQ_meas hQ_bound hQ_deriv hdu₀_int happrox

/-- Domain-facing representative form with no explicit conjugate-approximation
hypothesis: the derivative profile's local continuity, endpoint compatibility,
and boundedness produce it. -/
theorem intervalFullSemigroup_initialLegC1Approx_of_Icc_repr_continuousOn_zero_bound
    {u₀ : intervalDomainPoint → ℝ} {Q du₀ : ℝ → ℝ}
    (hu₀Q : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift u₀ y = Q y)
    (hQ_meas : AEStronglyMeasurable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ_bound : ∀ y, |Q y| ≤ CQ)
    (hQ_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Q (du₀ y) y)
    (hdu₀_int : IntervalIntegrable du₀ MeasureTheory.volume 0 1)
    (hdu₀_cont : ContinuousOn du₀ (Set.Icc (0 : ℝ) 1))
    (hdu₀_zero : du₀ 0 = 0) (hdu₀_one : du₀ 1 = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hdu₀_bound : ∀ y ∈ Set.Icc (0 : ℝ) 1, |du₀ y| ≤ M) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ =>
            intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x -
          du₀ x| < ε :=
  initialLegC1Approx_of_Icc_repr_continuousOn_zero_bound
    hu₀Q hQ_meas hQ_bound hQ_deriv hdu₀_int
    hdu₀_cont hdu₀_zero hdu₀_one hM hdu₀_bound

/-- Domain-facing representative form with derivative-profile integrability
and boundedness inferred from continuity on `[0,1]`. -/
theorem intervalFullSemigroup_initialLegC1Approx_of_Icc_repr_continuousOn_zero
    {u₀ : intervalDomainPoint → ℝ} {Q du₀ : ℝ → ℝ}
    (hu₀Q : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift u₀ y = Q y)
    (hQ_meas : AEStronglyMeasurable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ_bound : ∀ y, |Q y| ≤ CQ)
    (hQ_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Q (du₀ y) y)
    (hdu₀_cont : ContinuousOn du₀ (Set.Icc (0 : ℝ) 1))
    (hdu₀_zero : du₀ 0 = 0) (hdu₀_one : du₀ 1 = 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ =>
            intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x -
          du₀ x| < ε :=
  initialLegC1Approx_of_Icc_repr_continuousOn_zero
    hu₀Q hQ_meas hQ_bound hQ_deriv hdu₀_cont hdu₀_zero hdu₀_one

end

end ShenWork.IntervalSemigroupC1ApproxIdentity
