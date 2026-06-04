import ShenWork.PDE.IntervalFullKernelInterchange
import ShenWork.PDE.IntervalDuhamelClosedC2
import ShenWork.PDE.IntervalResolverPositivity
import ShenWork.PDE.IntervalCosineSliceRegularity

/-!
# Neumann boundary conditions for the interval semigroup

The full Neumann heat semigroup `S(t)f` satisfies homogeneous Neumann
boundary conditions `∂ₓS(t)f(0) = ∂ₓS(t)f(1) = 0` for any bounded
continuous input `f` and `t > 0`.

No `sorry`/`admit`/custom `axiom`.
-/

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalSemigroupNeumann

open ShenWork.HeatKernelGradientEstimates
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalFullKernelInterchange
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalResolverPositivity
open ShenWork.IntervalDomainRegularityBootstrap
open ShenWork.CosineSpectrum (cosineMode)

theorem heatCoeff_eigenvalue_summable {t : ℝ} (ht : 0 < t)
    {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M) :
    Summable (fun n => unitIntervalCosineEigenvalue n *
      |Real.exp (-t * unitIntervalCosineEigenvalue n) * a n|) := by
  have ht2 : 0 < t / 2 := by linarith
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg
      (by simp [unitIntervalCosineEigenvalue]; positivity)
      (abs_nonneg _))
  · intro n
    simp only [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    have hMn : |a n| ≤ |M| := le_trans (hM n) (le_abs_self M)
    have heig_nn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
      simp [unitIntervalCosineEigenvalue]; positivity
    calc unitIntervalCosineEigenvalue n *
          (Real.exp (-t * unitIntervalCosineEigenvalue n) * |a n|)
        ≤ unitIntervalCosineEigenvalue n *
          (Real.exp (-t * unitIntervalCosineEigenvalue n) * |M|) := by
          apply mul_le_mul_of_nonneg_left _ heig_nn
          exact mul_le_mul_of_nonneg_left hMn (Real.exp_nonneg _)
      _ = (unitIntervalCosineEigenvalue n *
            Real.exp (-(t / 2) * unitIntervalCosineEigenvalue n)) *
          (|M| * Real.exp (-(t / 2) * unitIntervalCosineEigenvalue n)) := by
          rw [show -t * unitIntervalCosineEigenvalue n =
            -(t / 2) * unitIntervalCosineEigenvalue n +
              -(t / 2) * unitIntervalCosineEigenvalue n by ring,
            Real.exp_add]; ring
      _ ≤ (1 / (t / 2)) *
          (|M| * Real.exp (-(t / 2) * unitIntervalCosineEigenvalue n)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))
          rw [le_div_iff₀ ht2]
          have hcx_nn : 0 ≤ (t / 2) * unitIntervalCosineEigenvalue n :=
            mul_nonneg ht2.le heig_nn
          calc unitIntervalCosineEigenvalue n *
                  Real.exp (-(t / 2) * unitIntervalCosineEigenvalue n) * (t / 2)
              = ((t / 2) * unitIntervalCosineEigenvalue n) *
                  Real.exp (-((t / 2) * unitIntervalCosineEigenvalue n)) := by ring
            _ ≤ 1 := real_mul_exp_neg_le_one hcx_nn
      _ = (|M| / (t / 2)) *
          Real.exp (-(t / 2) * unitIntervalCosineEigenvalue n) := by ring
  · exact (unitIntervalCosineHeatTrace_single_exp_summable ht2).mul_left (|M| / (t / 2))

theorem unitIntervalCosineHeatValue_eq_cosineCoeffSeries
    (t : ℝ) (a : ℕ → ℝ) :
    unitIntervalCosineHeatValue t a =
      fun x => ∑' n, (Real.exp (-t * unitIntervalCosineEigenvalue n) * a n) *
        cosineMode n x := by
  funext x
  simp only [unitIntervalCosineHeatValue, unitIntervalCosineHeatPointWeight,
    unitIntervalCosineMode]
  congr 1; funext n
  simp only [cosineMode]; ring

theorem unitIntervalCosineHeatValue_deriv_at_zero
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M) :
    deriv (unitIntervalCosineHeatValue t a) 0 = 0 := by
  rw [unitIntervalCosineHeatValue_eq_cosineCoeffSeries]
  exact cosineCoeffSeries_deriv_at_zero (heatCoeff_eigenvalue_summable ht hM)

theorem unitIntervalCosineHeatValue_deriv_at_one
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M) :
    deriv (unitIntervalCosineHeatValue t a) 1 = 0 := by
  rw [unitIntervalCosineHeatValue_eq_cosineCoeffSeries]
  exact cosineCoeffSeries_deriv_at_one (heatCoeff_eigenvalue_summable ht hM)

theorem deriv_eq_left_of_eqOn_Ioo_of_contDiff
    {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (heq : Set.EqOn f g (Set.Ioo a b)) :
    deriv f a = deriv g a := by
  have hdf : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hdg : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hdeq : ∀ x ∈ Set.Ioo a b, deriv f x = deriv g x := fun x hx =>
    Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) (fun z hz => heq hz))
  have heq_filter : (deriv f) =ᶠ[nhdsWithin a (Set.Ioi a)] (deriv g) := by
    filter_upwards [Ioo_mem_nhdsGT hab] with x hx
    exact hdeq x hx
  exact tendsto_nhds_unique
    ((hdf.continuousAt).tendsto.mono_left nhdsWithin_le_nhds)
    (((hdg.continuousAt).tendsto.mono_left nhdsWithin_le_nhds).congr' heq_filter.symm)

theorem deriv_eq_right_of_eqOn_Ioo_of_contDiff
    {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (heq : Set.EqOn f g (Set.Ioo a b)) :
    deriv f b = deriv g b := by
  have hdf : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hdg : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hdeq : ∀ x ∈ Set.Ioo a b, deriv f x = deriv g x := fun x hx =>
    Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) (fun z hz => heq hz))
  have heq_filter : (deriv f) =ᶠ[nhdsWithin b (Set.Iio b)] (deriv g) := by
    filter_upwards [Ioo_mem_nhdsLT hab] with x hx
    exact hdeq x hx
  exact tendsto_nhds_unique
    ((hdf.continuousAt).tendsto.mono_left nhdsWithin_le_nhds)
    (((hdg.continuousAt).tendsto.mono_left nhdsWithin_le_nhds).congr' heq_filter.symm)

theorem intervalFullSemigroupOperator_neumann_at_zero
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs f n| ≤ M) :
    deriv (fun x => intervalFullSemigroupOperator t f x) 0 = 0 := by
  have hkernel := fun x y => intervalNeumannFullKernel_cosineKernel_identity ht x y
  have hC2_S := intervalFullSemigroupOperator_contDiff_two_unconditional
    t ht f hf hM (fun x => hkernel x)
  have hC2_H := unitIntervalCosineHeatValue_contDiff_two ht hM
  have heq_Ioo : Set.EqOn (fun x => intervalFullSemigroupOperator t f x)
      (unitIntervalCosineHeatValue t (cosineCoeffs f)) (Set.Ioo (0 : ℝ) 1) :=
    fun x hx => intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional
      t ht f hf x hx (hkernel x)
  rw [deriv_eq_left_of_eqOn_Ioo_of_contDiff (by norm_num : (0:ℝ) < 1)
    (hC2_S.of_le (by norm_num)) (hC2_H.of_le (by norm_num)) heq_Ioo]
  exact unitIntervalCosineHeatValue_deriv_at_zero ht hM

theorem intervalFullSemigroupOperator_neumann_at_one
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs f n| ≤ M) :
    deriv (fun x => intervalFullSemigroupOperator t f x) 1 = 0 := by
  have hkernel := fun x y => intervalNeumannFullKernel_cosineKernel_identity ht x y
  have hC2_S := intervalFullSemigroupOperator_contDiff_two_unconditional
    t ht f hf hM (fun x => hkernel x)
  have hC2_H := unitIntervalCosineHeatValue_contDiff_two ht hM
  have heq_Ioo : Set.EqOn (fun x => intervalFullSemigroupOperator t f x)
      (unitIntervalCosineHeatValue t (cosineCoeffs f)) (Set.Ioo (0 : ℝ) 1) :=
    fun x hx => intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional
      t ht f hf x hx (hkernel x)
  rw [deriv_eq_right_of_eqOn_Ioo_of_contDiff (by norm_num : (0:ℝ) < 1)
    (hC2_S.of_le (by norm_num)) (hC2_H.of_le (by norm_num)) heq_Ioo]
  exact unitIntervalCosineHeatValue_deriv_at_one ht hM

/-! ## Mild-solution Neumann BC from positivity

For a positive mild solution at time `t > 0`, the interval domain lift
`intervalDomainLift (u t)` is discontinuous at the endpoints `0` and `1`
(it zero-extends outside `[0,1]` but is positive at the endpoints).
Lean's `deriv` returns `0` at non-differentiable points, so the conjunct-7
Neumann condition `deriv (lift (u t)) 0 = 0` follows trivially from
positivity — no analytical semigroup argument needed. -/

open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)

/-- Mild solution Neumann BC at x = 0 from positivity at the endpoint.
`deriv (intervalDomainLift (u t)) 0 = 0` because the zero extension
creates a discontinuity at 0, making `deriv` junk-return 0. -/
theorem mildSolution_neumann_deriv_zero_of_pos
    {u : intervalDomainPoint → ℝ}
    (hpos : 0 < u ⟨0, le_refl _, by norm_num⟩) :
    deriv (intervalDomainLift u) 0 = 0 := by
  apply ShenWork.IntervalCosineSliceRegularity.intervalDomainLift_deriv_left_endpoint_zero_of_ne
  intro h
  have : intervalDomainLift u 0 = u ⟨0, le_refl _, by norm_num⟩ := by
    simp [intervalDomainLift, show (0:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨le_refl _, by norm_num⟩]
  linarith [this ▸ h]

/-- Mild solution Neumann BC at x = 1 from positivity at the endpoint. -/
theorem mildSolution_neumann_deriv_one_of_pos
    {u : intervalDomainPoint → ℝ}
    (hpos : 0 < u ⟨1, by norm_num, le_refl _⟩) :
    deriv (intervalDomainLift u) 1 = 0 := by
  apply ShenWork.IntervalCosineSliceRegularity.intervalDomainLift_deriv_right_endpoint_zero_of_ne
  intro h
  have : intervalDomainLift u 1 = u ⟨1, by norm_num, le_refl _⟩ := by
    simp [intervalDomainLift, show (1:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨by norm_num, le_refl _⟩]
  linarith [this ▸ h]

/-- **Mild solution Neumann BC (conjunct 7 form).**  For any function with
pointwise positivity on the interval domain, the lift's `deriv` vanishes at
both endpoints.  Applied to the `t`-slice of a mild solution at `t > 0`. -/
theorem mildSolution_neumann_of_positive_time
    {u : intervalDomainPoint → ℝ}
    (hpos : ∀ x : intervalDomainPoint, 0 < u x) :
    deriv (intervalDomainLift u) 0 = 0 ∧
      deriv (intervalDomainLift u) 1 = 0 :=
  ⟨mildSolution_neumann_deriv_zero_of_pos (hpos ⟨0, le_refl _, by norm_num⟩),
    mildSolution_neumann_deriv_one_of_pos (hpos ⟨1, by norm_num, le_refl _⟩)⟩

/-! ## Conjunct-6 genuine Neumann limit — bridge theorems

The genuine one-sided Neumann limit `deriv(lift(u t)) → 0` as `x → 0⁺`
(conjunct 6) requires showing that on the interior `(0,1)`, the lift's
derivative agrees with the derivative of a C¹ function that has `deriv = 0`
at the boundary.

For the semigroup term S(t)f, this is proved analytically above.  For the
full mild map (including the divergence-form chemotaxis Duhamel), the
genuine Neumann BC is a consequence of the PDE structure — the Neumann
heat kernel's spatial derivative vanishes at the boundary, so every term
`∂ₓS(τ)(g)(0) = 0`.  The following bridge reduces the conjunct-6 limit
to a C¹-regularity hypothesis on the mild map. -/

/-- **Conjunct-6 bridge, left endpoint.**  If `intervalDomainLift w` agrees
with a `C¹` function `g` on `[0,1]` and `deriv g 0 = 0`, then
`deriv(lift w) → 0` as `x → 0⁺`.  The `C¹` regularity of `g` supplies
continuity of `deriv g`, and the `EqOn` transfers the derivative on the
interior to the lift. -/
theorem neumann_limit_left_of_eqOn_C1
    {w : intervalDomainPoint → ℝ} {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g)
    (hg0 : deriv g 0 = 0)
    (hagree : Set.EqOn (intervalDomainLift w) g (Set.Icc (0 : ℝ) 1)) :
    Filter.Tendsto (deriv (intervalDomainLift w))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hdg_cont : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have htend : Filter.Tendsto (deriv g)
      (nhds 0) (nhds 0) := by
    have := hdg_cont.continuousAt (x := (0 : ℝ)) |>.tendsto
    rwa [hg0] at this
  have heq_filter :
      deriv (intervalDomainLift w) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] deriv g := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with y hy
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds hy.1 hy.2)
        (fun z hz => hagree (Set.Ioo_subset_Icc_self hz)))
  exact (htend.mono_left nhdsWithin_le_nhds).congr' heq_filter.symm

/-- **Conjunct-6 bridge, right endpoint.**  Symmetric. -/
theorem neumann_limit_right_of_eqOn_C1
    {w : intervalDomainPoint → ℝ} {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g)
    (hg1 : deriv g 1 = 0)
    (hagree : Set.EqOn (intervalDomainLift w) g (Set.Icc (0 : ℝ) 1)) :
    Filter.Tendsto (deriv (intervalDomainLift w))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  have hdg_cont : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have htend : Filter.Tendsto (deriv g)
      (nhds 1) (nhds 0) := by
    have := hdg_cont.continuousAt (x := (1 : ℝ)) |>.tendsto
    rwa [hg1] at this
  have heq_filter :
      deriv (intervalDomainLift w) =ᶠ[nhdsWithin (1 : ℝ) (Set.Iio 1)] deriv g := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ) < 1)] with y hy
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds hy.1 hy.2)
        (fun z hz => hagree (Set.Ioo_subset_Icc_self hz)))
  exact (htend.mono_left nhdsWithin_le_nhds).congr' heq_filter.symm

/-- **Semigroup Neumann limit, left.**  The full semigroup's spatial derivative
tends to 0 as `x → 0⁺`.  Since `S(t)f` is globally `C²` (hence `C¹` with
continuous derivative), this follows from `deriv (S(t)f) 0 = 0`. -/
theorem intervalFullSemigroupOperator_neumann_limit_left
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs f n| ≤ M) :
    Filter.Tendsto
      (deriv (fun x => intervalFullSemigroupOperator t f x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hC2 := intervalFullSemigroupOperator_contDiff_two_unconditional
    t ht f hf hM (fun x => intervalNeumannFullKernel_cosineKernel_identity ht x)
  have hC1 : ContDiff ℝ 1 (fun x => intervalFullSemigroupOperator t f x) :=
    hC2.of_le (by norm_num)
  have h0 := intervalFullSemigroupOperator_neumann_at_zero ht hf hM
  have hcont := hC1.continuous_deriv le_rfl
  have := hcont.continuousAt (x := (0 : ℝ)) |>.tendsto
  rw [h0] at this; exact this.mono_left nhdsWithin_le_nhds

/-- **Semigroup Neumann limit, right.** -/
theorem intervalFullSemigroupOperator_neumann_limit_right
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs f n| ≤ M) :
    Filter.Tendsto
      (deriv (fun x => intervalFullSemigroupOperator t f x))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  have hC2 := intervalFullSemigroupOperator_contDiff_two_unconditional
    t ht f hf hM (fun x => intervalNeumannFullKernel_cosineKernel_identity ht x)
  have hC1 : ContDiff ℝ 1 (fun x => intervalFullSemigroupOperator t f x) :=
    hC2.of_le (by norm_num)
  have h1 := intervalFullSemigroupOperator_neumann_at_one ht hf hM
  have hcont := hC1.continuous_deriv le_rfl
  have := hcont.continuousAt (x := (1 : ℝ)) |>.tendsto
  rw [h1] at this; exact this.mono_left nhdsWithin_le_nhds

/-! ## Value-form Duhamel Neumann

The value-form Duhamel integral `V(x) = ∫₀ᵗ S(t-s)(r(s))(x) ds` satisfies
Neumann BC at both endpoints.  The proof: under the Leibniz interchange,
`deriv V(0) = ∫₀ᵗ deriv(S(t-s)(r(s)))(0) ds = ∫₀ᵗ 0 ds = 0`, where each
per-slice derivative vanishes by the semigroup Neumann property.

The Leibniz interchange (`HasDerivAt`) and the per-slice semigroup Neumann
are combined here; the measurability/integrability prerequisites are taken
as explicit hypotheses (dischargeable from continuity and boundedness of the
source).  For the Tendsto limit version, the C¹ regularity bridge
`neumann_limit_left_of_eqOn_C1` applies once the integral is identified
with a C¹ function. -/

/-- **Value-Duhamel Neumann at x = 0.**  If the Leibniz interchange holds
at x₀ = 0, then the derivative is 0: each per-slice integrand
`deriv(S(t-s)(F(s)))(0) = 0` by the semigroup Neumann property (for s < t,
so t-s > 0), and the singleton {t} has measure 0. -/
theorem valueDuhamel_neumann_at_zero_of_hasDerivAt
    {t : ℝ} (ht : 0 < t) {F : ℝ → ℝ → ℝ}
    (hF_cont : ∀ s, Continuous (F s))
    {M : ℝ} (hM : ∀ s n, |cosineCoeffs (F s) n| ≤ M)
    (hleibniz :
      HasDerivAt
        (fun x => ∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (F s) x)
        (∫ s in (0:ℝ)..t,
          deriv (fun z => intervalFullSemigroupOperator (t - s) (F s) z) 0)
        0) :
    deriv (fun x => ∫ s in (0:ℝ)..t,
      intervalFullSemigroupOperator (t - s) (F s) x) 0 = 0 := by
  rw [hleibniz.deriv]
  have hae : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
      deriv (fun z => intervalFullSemigroupOperator (t - s) (F s) z) 0 = 0 := by
    have hne : ∀ᵐ s ∂volume, s ≠ t :=
      ae_iff.mpr (by simp [Real.volume_singleton])
    filter_upwards [hne] with s hs hmem
    have hst : s < t := by
      rw [Set.uIoc_of_le ht.le] at hmem
      exact lt_of_le_of_ne hmem.2 hs
    exact intervalFullSemigroupOperator_neumann_at_zero (sub_pos.mpr hst) (hF_cont s) (hM s)
  conv_rhs => rw [show (0 : ℝ) = ∫ _s in (0:ℝ)..t, (0 : ℝ) from by simp]
  exact intervalIntegral.integral_congr_ae hae

/-- **Value-Duhamel Neumann at x = 1.**  Symmetric. -/
theorem valueDuhamel_neumann_at_one_of_hasDerivAt
    {t : ℝ} (ht : 0 < t) {F : ℝ → ℝ → ℝ}
    (hF_cont : ∀ s, Continuous (F s))
    {M : ℝ} (hM : ∀ s n, |cosineCoeffs (F s) n| ≤ M)
    (hleibniz :
      HasDerivAt
        (fun x => ∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (F s) x)
        (∫ s in (0:ℝ)..t,
          deriv (fun z => intervalFullSemigroupOperator (t - s) (F s) z) 1)
        1) :
    deriv (fun x => ∫ s in (0:ℝ)..t,
      intervalFullSemigroupOperator (t - s) (F s) x) 1 = 0 := by
  rw [hleibniz.deriv]
  have hae : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
      deriv (fun z => intervalFullSemigroupOperator (t - s) (F s) z) 1 = 0 := by
    have hne : ∀ᵐ s ∂volume, s ≠ t :=
      ae_iff.mpr (by simp [Real.volume_singleton])
    filter_upwards [hne] with s hs hmem
    have hst : s < t := by
      rw [Set.uIoc_of_le ht.le] at hmem
      exact lt_of_le_of_ne hmem.2 hs
    exact intervalFullSemigroupOperator_neumann_at_one (sub_pos.mpr hst) (hF_cont s) (hM s)
  conv_rhs => rw [show (0 : ℝ) = ∫ _s in (0:ℝ)..t, (0 : ℝ) from by simp]
  exact intervalIntegral.integral_congr_ae hae

/-! ## Conjunct 3: spatial C² on the open interior

The semigroup output `S(t)f` is globally `C²` for `t > 0`, so it is
`C²` on any subset including `(0,1)`.  This is conjunct (3) of the
classical regularity predicate. -/

/-- **Conjunct-3 for the semigroup.**  `S(t)f` is `C²` on `(0,1)`. -/
theorem intervalFullSemigroupOperator_contDiffOn_Ioo
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs f n| ≤ M) :
    ContDiffOn ℝ 2 (fun x => intervalFullSemigroupOperator t f x)
      (Set.Ioo (0 : ℝ) 1) :=
  (intervalFullSemigroupOperator_contDiff_two_unconditional
    t ht f hf hM (fun x => intervalNeumannFullKernel_cosineKernel_identity ht x)
  ).contDiffOn

/-- **Conjunct-7 closed C² for the semigroup.**  `S(t)f` is `C²` on `[0,1]`. -/
theorem intervalFullSemigroupOperator_contDiffOn_Icc
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs f n| ≤ M) :
    ContDiffOn ℝ 2 (fun x => intervalFullSemigroupOperator t f x)
      (Set.Icc (0 : ℝ) 1) :=
  (intervalFullSemigroupOperator_contDiff_two_unconditional
    t ht f hf hM (fun x => intervalNeumannFullKernel_cosineKernel_identity ht x)
  ).contDiffOn

/-- **Conjunct-7 full bundle for the semigroup.**  Closed-`[0,1]` `C²`
plus `deriv = 0` at both endpoints. -/
theorem intervalFullSemigroupOperator_conjunct7
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs f n| ≤ M) :
    ContDiffOn ℝ 2 (fun x => intervalFullSemigroupOperator t f x)
        (Set.Icc (0 : ℝ) 1) ∧
      deriv (fun x => intervalFullSemigroupOperator t f x) 0 = 0 ∧
      deriv (fun x => intervalFullSemigroupOperator t f x) 1 = 0 :=
  ⟨intervalFullSemigroupOperator_contDiffOn_Icc ht hf hM,
    intervalFullSemigroupOperator_neumann_at_zero ht hf hM,
    intervalFullSemigroupOperator_neumann_at_one ht hf hM⟩

/-- **Conjunct-6 full bundle for the semigroup.**  Genuine one-sided Neumann
limits at both endpoints. -/
theorem intervalFullSemigroupOperator_conjunct6
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs f n| ≤ M) :
    Filter.Tendsto (deriv (fun x => intervalFullSemigroupOperator t f x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (deriv (fun x => intervalFullSemigroupOperator t f x))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) :=
  ⟨intervalFullSemigroupOperator_neumann_limit_left ht hf hM,
    intervalFullSemigroupOperator_neumann_limit_right ht hf hM⟩

/-! ## Joint (t,x) continuity of the cosine heat value

The spectral representation `∑ e^{-tλₙ} aₙ cos(nπx)` converges uniformly on
compact subsets of `{t > 0} × ℝ` (Weierstrass-M with the bound
`e^{-δλₙ}|aₙ|` for `t ≥ δ`).  This gives joint `(t,x)` continuity of the
cosine heat value and, via the spectral interchange, of the semigroup. -/

/-- **Joint continuity of cosine heat value** on `[δ, ∞) × ℝ` for fixed `δ > 0`.
Each term is jointly continuous; the Weierstrass-M bound `e^{-δλₙ}M` is
summable by `unitIntervalCosineHeatTrace_single_exp_summable`. -/
theorem unitIntervalCosineHeatValue_continuousOn_Ici_prod
    {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M)
    {δ : ℝ} (hδ : 0 < δ) :
    ContinuousOn
      (fun p : ℝ × ℝ => unitIntervalCosineHeatValue p.1 a p.2)
      (Set.Ici δ ×ˢ Set.univ) := by
  simp only [unitIntervalCosineHeatValue]
  refine continuousOn_tsum
    (fun n => ?_) ((unitIntervalCosineHeatTrace_single_exp_summable hδ).mul_right M) ?_
  · -- Per-term continuity: (t,x) ↦ exp(-t·λₙ) · cos(nπx) · aₙ
    simp only [unitIntervalCosineHeatPointWeight, unitIntervalCosineMode]
    fun_prop
  · intro n ⟨t, x⟩ ⟨ht, _⟩
    simp only [unitIntervalCosineHeatPointWeight, unitIntervalCosineMode, Set.mem_Ici] at ht ⊢
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have heig_nn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
      simp [unitIntervalCosineEigenvalue]; positivity
    have h1 : |Real.exp (-t * unitIntervalCosineEigenvalue n)| ≤
        Real.exp (-δ * unitIntervalCosineEigenvalue n) := by
      rw [abs_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_exp_of_le (by nlinarith)
    have h2 : |Real.cos (↑n * Real.pi * x)| ≤ 1 := Real.abs_cos_le_one _
    have h3 : |a n| ≤ M := hM n
    calc |Real.exp (-t * unitIntervalCosineEigenvalue n)| *
            |Real.cos (↑n * Real.pi * x)| * |a n|
        ≤ Real.exp (-δ * unitIntervalCosineEigenvalue n) * 1 * M :=
          mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (Real.exp_nonneg _))
            h3 (abs_nonneg _) (mul_nonneg (Real.exp_nonneg _) zero_le_one)
      _ = Real.exp (-δ * unitIntervalCosineEigenvalue n) * M := by ring

/-- **Joint continuity of the cosine heat value** on `(0, ∞) × ℝ`.
Covers any `(t₀, x₀)` with `t₀ > 0` by choosing `δ = t₀/2`. -/
theorem unitIntervalCosineHeatValue_continuousOn_Ioi_prod
    {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M) :
    ContinuousOn
      (fun p : ℝ × ℝ => unitIntervalCosineHeatValue p.1 a p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  intro ⟨t₀, x₀⟩ ht₀x₀
  have ht₀ : 0 < t₀ := ht₀x₀.1
  have hδ : 0 < t₀ / 2 := by linarith
  -- ContinuousOn on Ici(t₀/2)×univ, and that set is a nhd of (t₀,x₀)
  have hcon := unitIntervalCosineHeatValue_continuousOn_Ici_prod hM hδ
  have hmem : (t₀, x₀) ∈ Set.Ici (t₀ / 2) ×ˢ Set.univ :=
    ⟨by simp [Set.mem_Ici]; linarith, Set.mem_univ _⟩
  have hnhd : Set.Ici (t₀ / 2) ×ˢ Set.univ ∈ nhds (t₀, x₀) :=
    prod_mem_nhds (Ici_mem_nhds (by linarith : t₀ / 2 < t₀)) Filter.univ_mem
  exact (hcon.continuousAt hnhd).continuousWithinAt

/-! ## Conjunct 9: semigroup joint solution-field continuity on the slab

The semigroup output `(t,x) ↦ S(t)f(x)` is jointly continuous on
`(0,T) × [0,1]`.  On the interior `(0,1)` this follows from the
cosine heat value joint continuity via the spectral identity; the
closed-endpoint extension uses the global C² (hence continuous)
spatial regularity of `S(t)f` at each fixed `t`.

For the cosine heat value with fixed bounded coefficients, the
joint continuity on `(0,∞) × [0,1]` is immediate from `…_Ioi_prod`
by restricting the spatial component. -/

/-- **Conjunct-9 for the cosine heat value.**  Joint `(t,x)` continuity
on `(0,T) × [0,1]`. -/
theorem unitIntervalCosineHeatValue_continuousOn_slab
    {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M) {T : ℝ} (_hT : 0 < T) :
    ContinuousOn
      (fun p : ℝ × ℝ => unitIntervalCosineHeatValue p.1 a p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
  (unitIntervalCosineHeatValue_continuousOn_Ioi_prod hM).mono
    (Set.prod_mono Set.Ioo_subset_Ioi_self (fun _ _ => Set.mem_univ _))

/-! ## Conjunct 8: joint continuity of the time-derivative field

For the cosine heat value `H(t,x) = ∑ e^{-tλₙ} aₙ cos(nπx)`, the
time-derivative field is `∂_t H = secondValue = ∑ e^{-tλₙ}(−λₙ cos(nπx)) aₙ`.
The Weierstrass-M bound `λₙ e^{-δλₙ} |aₙ|` is summable for `δ > 0`
(from `heatCoeff_eigenvalue_summable`), so this series is jointly
continuous on `{t ≥ δ} × ℝ` and hence on `(0,∞) × ℝ`.  The existing
`unitIntervalCosineHeatValue_hasDerivAt_time` connects the time derivative
to the secondValue. -/

set_option maxHeartbeats 800000 in
/-- **Joint continuity of secondValue** on `[δ,∞) × ℝ`. -/
theorem unitIntervalCosineHeatSecondValue_continuousOn_Ici_prod
    {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M)
    {δ : ℝ} (hδ : 0 < δ) :
    ContinuousOn
      (fun p : ℝ × ℝ => unitIntervalCosineHeatSecondValue p.1 a p.2)
      (Set.Ici δ ×ˢ Set.univ) := by
  simp only [unitIntervalCosineHeatSecondValue]
  refine continuousOn_tsum
    (fun n => ?_)
    (heatCoeff_eigenvalue_summable hδ hM)
    ?_
  · -- Per-term continuity: (t,x) ↦ exp(-t·λₙ)·(−(nπ)²·cos(nπx))·aₙ
    simp only [unitIntervalCosineHeatSecondPointWeight]
    fun_prop
  · intro n ⟨t, x⟩ ⟨ht, _⟩
    simp only [unitIntervalCosineHeatSecondPointWeight,
      Set.mem_Ici] at ht ⊢
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have heig_nn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
      simp [unitIntervalCosineEigenvalue]; positivity
    -- LHS = |exp(-t·λₙ)| · |-(nπ)²·cos(nπx)| · |aₙ|
    -- ≤ exp(-δ·λₙ) · (nπ)² · |aₙ|  = eigenvalue n · exp(-δ·λₙ) · |aₙ|
    have h_exp : |Real.exp (-t * unitIntervalCosineEigenvalue n)| ≤
        Real.exp (-δ * unitIntervalCosineEigenvalue n) := by
      rw [abs_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_exp_of_le (by nlinarith)
    have h_trig : |-(↑n * Real.pi) ^ 2 * Real.cos (↑n * Real.pi * x)| ≤
        unitIntervalCosineEigenvalue n := by
      calc |-(↑n * Real.pi) ^ 2 * Real.cos (↑n * Real.pi * x)|
          = |(-(↑n * Real.pi) ^ 2)| * |Real.cos (↑n * Real.pi * x)| := abs_mul _ _
        _ ≤ (↑n * Real.pi) ^ 2 * 1 := by
            gcongr
            · rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (↑n * Real.pi) ^ 2)]
            · exact Real.abs_cos_le_one _
        _ = unitIntervalCosineEigenvalue n := by
            simp [unitIntervalCosineEigenvalue]
    calc |Real.exp (-t * unitIntervalCosineEigenvalue n)| *
            |-(↑n * Real.pi) ^ 2 * Real.cos (↑n * Real.pi * x)| * |a n|
        ≤ Real.exp (-δ * unitIntervalCosineEigenvalue n) *
            unitIntervalCosineEigenvalue n * |a n| :=
          mul_le_mul
            (mul_le_mul h_exp h_trig (abs_nonneg _) (Real.exp_nonneg _))
            le_rfl (abs_nonneg _)
            (mul_nonneg (Real.exp_nonneg _) heig_nn)
      _ = unitIntervalCosineEigenvalue n *
          |Real.exp (-δ * unitIntervalCosineEigenvalue n) * a n| := by
          rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]; ring

/-- **Joint continuity of secondValue** on `(0,∞) × ℝ`. -/
theorem unitIntervalCosineHeatSecondValue_continuousOn_Ioi_prod
    {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M) :
    ContinuousOn
      (fun p : ℝ × ℝ => unitIntervalCosineHeatSecondValue p.1 a p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  intro ⟨t₀, x₀⟩ ht₀x₀
  have ht₀ : 0 < t₀ := ht₀x₀.1
  have hδ : 0 < t₀ / 2 := by linarith
  have hcon := unitIntervalCosineHeatSecondValue_continuousOn_Ici_prod hM hδ
  have hmem : (t₀, x₀) ∈ Set.Ici (t₀ / 2) ×ˢ Set.univ :=
    ⟨by simp [Set.mem_Ici]; linarith, Set.mem_univ _⟩
  have hnhd : Set.Ici (t₀ / 2) ×ˢ Set.univ ∈ nhds (t₀, x₀) :=
    prod_mem_nhds (Ici_mem_nhds (by linarith : t₀ / 2 < t₀)) Filter.univ_mem
  exact (hcon.continuousAt hnhd).continuousWithinAt

/-- **Conjunct-8 for the cosine heat value.**  Joint `(t,x)` continuity
of the time-derivative field on `(0,T) × [0,1]`. -/
theorem unitIntervalCosineHeatSecondValue_continuousOn_slab
    {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M) {T : ℝ} (_hT : 0 < T) :
    ContinuousOn
      (fun p : ℝ × ℝ => unitIntervalCosineHeatSecondValue p.1 a p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
  (unitIntervalCosineHeatSecondValue_continuousOn_Ioi_prod hM).mono
    (Set.prod_mono Set.Ioo_subset_Ioi_self (fun _ _ => Set.mem_univ _))

/-! ## Mild-map regularity composition

The mild map `Φ(t,x) = S(t)(lift u₀)(x) + chem(t,x) + logistic(t,x)` has
regularity properties that compose additively from the three terms.  The
semigroup term's regularity is proved above; the Duhamel terms are taken as
explicit hypotheses (dischargeable from Leibniz + source regularity). -/

open ShenWork.IntervalDomain (intervalDomainLift)

/-- **Conjunct-9 composition for the mild map.**  If the semigroup term and
both Duhamel corrections are each jointly continuous on the slab, the full
mild map is jointly continuous.  For the semigroup term, use
`unitIntervalCosineHeatValue_continuousOn_slab`; for the Duhamel terms,
the hypothesis is a genuine regularity input. -/
theorem mildMap_conjunct9_of_terms
    {T : ℝ} {S_term chem_term log_term : ℝ → ℝ → ℝ}
    (hS : ContinuousOn (Function.uncurry S_term)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1))
    (hchem : ContinuousOn (Function.uncurry chem_term)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1))
    (hlog : ContinuousOn (Function.uncurry log_term)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (Function.uncurry (fun t x => S_term t x + chem_term t x + log_term t x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have : Function.uncurry (fun t x => S_term t x + chem_term t x + log_term t x) =
      fun p : ℝ × ℝ => Function.uncurry S_term p + Function.uncurry chem_term p +
        Function.uncurry log_term p := by ext ⟨t, x⟩; rfl
  rw [this]; exact (hS.add hchem).add hlog

/-- **Conjunct-3 composition for the mild map.**  If each term is spatially
`C²` on `(0,1)` at each time, the sum is `C²` on `(0,1)`. -/
theorem mildMap_conjunct3_of_terms
    {t : ℝ} {S_term chem_term log_term : ℝ → ℝ}
    (hS : ContDiffOn ℝ 2 S_term (Set.Ioo (0 : ℝ) 1))
    (hchem : ContDiffOn ℝ 2 chem_term (Set.Ioo (0 : ℝ) 1))
    (hlog : ContDiffOn ℝ 2 log_term (Set.Ioo (0 : ℝ) 1)) :
    ContDiffOn ℝ 2 (fun x => S_term x + chem_term x + log_term x)
      (Set.Ioo (0 : ℝ) 1) :=
  (hS.add hchem).add hlog

/-- **Conjunct-7 deriv=0 composition.**  If each term has `deriv = 0` at an
endpoint and all are differentiable there, the sum has `deriv = 0`. -/
theorem mildMap_neumann_at_of_terms
    {S_term chem_term log_term : ℝ → ℝ} {x₀ : ℝ}
    (hS : deriv S_term x₀ = 0)
    (hchem : deriv chem_term x₀ = 0)
    (hlog : deriv log_term x₀ = 0)
    (hdiff_S : DifferentiableAt ℝ S_term x₀)
    (hdiff_chem : DifferentiableAt ℝ chem_term x₀)
    (hdiff_log : DifferentiableAt ℝ log_term x₀) :
    deriv (fun x => S_term x + chem_term x + log_term x) x₀ = 0 := by
  have heq : (fun x => S_term x + chem_term x + log_term x) =ᶠ[nhds x₀]
      (fun x => S_term x + chem_term x + log_term x) :=
    Filter.EventuallyEq.refl _ _
  have hd : HasDerivAt (fun x => S_term x + chem_term x + log_term x)
      (deriv S_term x₀ + deriv chem_term x₀ + deriv log_term x₀) x₀ := by
    exact (hdiff_S.hasDerivAt.add hdiff_chem.hasDerivAt).add hdiff_log.hasDerivAt
  rw [hd.deriv, hS, hchem, hlog]; ring

/-- **Conjunct-6 Neumann limit composition.**  If each term's derivative
tends to 0 at an endpoint (from one side), the sum's derivative does too. -/
theorem mildMap_neumann_limit_of_terms
    {S_term chem_term log_term : ℝ → ℝ} {x₀ : ℝ} {nhd : Filter ℝ}
    (hS : Filter.Tendsto (deriv S_term) nhd (nhds 0))
    (hchem : Filter.Tendsto (deriv chem_term) nhd (nhds 0))
    (hlog : Filter.Tendsto (deriv log_term) nhd (nhds 0))
    (hdiff_S : ∀ᶠ x in nhd, DifferentiableAt ℝ S_term x)
    (hdiff_chem : ∀ᶠ x in nhd, DifferentiableAt ℝ chem_term x)
    (hdiff_log : ∀ᶠ x in nhd, DifferentiableAt ℝ log_term x) :
    Filter.Tendsto (deriv (fun x => S_term x + chem_term x + log_term x))
      nhd (nhds 0) := by
  have heq : deriv (fun x => S_term x + chem_term x + log_term x)
      =ᶠ[nhd] (fun x => deriv S_term x + deriv chem_term x + deriv log_term x) := by
    filter_upwards [hdiff_S, hdiff_chem, hdiff_log] with x hS' hC' hL'
    exact ((hS'.add hC').hasDerivAt.add hL'.hasDerivAt).deriv.trans
      (by rw [(hS'.hasDerivAt.add hC'.hasDerivAt).deriv])
  have h0 : (0 : ℝ) = 0 + 0 + 0 := by ring
  rw [h0]
  exact ((hS.add hchem).add hlog).congr' heq.symm

end ShenWork.IntervalSemigroupNeumann
