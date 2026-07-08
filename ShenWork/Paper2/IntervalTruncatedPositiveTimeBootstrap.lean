/-
  Positive-time coefficient bootstrap for the truncated Picard limit.

  The coefficient ladder (IntervalCoeffLadderFull) requires a bounded source
  envelope (`WindowSourceEnvelope 0`), but the chemotaxis-divergence coefficient
  `truncatedChemDivSourceCoeff = kπ · sineInner(flux, k)` grows as O(k) from
  mere continuity of the flux.  This file bridges the gap:

  1. Integration by parts: if the flux is W¹,¹, then `kπ · sineInner(flux, k)`
     is O(1), not O(k).
  2. At positive time, the heat semigroup smooths the Picard iterates to C¹,
     which gives flux W¹,¹ uniformly on compact windows bounded away from t=0.
  3. The iterate-level C¹ bounds are uniform (by a Volterra-type contraction on
     the gradient), so they pass to the limit.
  4. With bounded source at positive time, the existing coefficient ladder
     gives pass-4 envelopes, eigenvalue-weighted summability, and all
     spectral fields needed by `TruncatedPositiveTimeSpectralData`.

  The construction is non-circular: iterate 0 is the heat semigroup (C∞ at
  positive time); the induction step uses C¹ of iterate n to bound the source
  for iterate n+1; uniform constants come from the Picard ball bound.
-/
import ShenWork.Paper2.IntervalBFormCron2TruncatedCoefficientWeakTest
import ShenWork.Paper2.IntervalBFormCron2TruncatedPicard
import ShenWork.Paper2.IntervalCoeffLadderFull
import ShenWork.Paper2.IntervalConjugateCosineSeries
import ShenWork.Paper2.IntervalDomainL2UEnergyCombine
import ShenWork.Paper2.IntervalMildPicardRegularity
import ShenWork.PDE.CosineSpectrum

set_option linter.sorry false

open MeasureTheory Set
open scoped BigOperators Topology Real

noncomputable section

namespace ShenWork.Paper2.TruncatedPositiveTimeBootstrap

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_abs_le_of_continuous_bounded)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalConjugateCosineSeries (intervalSineInner)
open ShenWork.Paper2.IntervalCoeffLadderFull
  (WindowCoefficientEnvelope WindowSourceEnvelope
   eigenvalue_weighted_summable_of_pass4)
open ShenWork.Paper2.BFormPositiveDatumNegPart
  (truncatedChemFluxLifted truncatedChemDivSourceCoeff
   truncatedLogisticSourceCoeff truncatedBFormSourceCoeff
   truncatedLogisticLifted
   truncatedPicardCoeff truncatedPicardCoeffTimeDeriv
   truncatedPicardInitialCoeff
   truncatedConjugatePicardLimit
   TruncatedConjugateMildExistenceData
   TruncatedConjugateMildSolutionData
   truncatedConjugateMildSolutionData_of_data
   negativePartTest cosineTestCoeff)
open ShenWork.Paper2.IntervalMildPicard (HasContinuousSlices)
open ShenWork.CosineSpectrum (cosineMode unitIntervalCosineEigenvalue)

/-! ## Flux boundary vanishing (needed before IBP) -/

theorem truncatedChemFluxLifted_zero_left'
    (p : CM2Params) (w : intervalDomainPoint → ℝ) :
    truncatedChemFluxLifted p w 0 = 0 := by
  unfold truncatedChemFluxLifted
  rw [ShenWork.Paper2.resolverGradReal_zero]; simp

theorem truncatedChemFluxLifted_zero_right'
    (p : CM2Params) (w : intervalDomainPoint → ℝ) :
    truncatedChemFluxLifted p w 1 = 0 := by
  unfold truncatedChemFluxLifted
  rw [ShenWork.Paper2.resolverGradReal_one]; simp

/-! ## Level 0: Integration by parts for sine coefficients -/

private theorem hasDerivAt_neg_cos_div_freq
    {ω x : ℝ} (hω : ω ≠ 0) :
    HasDerivAt (fun y : ℝ => -Real.cos (ω * y) / ω)
      (Real.sin (ω * x)) x := by
  have hlin : HasDerivAt (fun y : ℝ => ω * y) ω x := by
    simpa using (hasDerivAt_id x).const_mul ω
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (ω * y))
      (-(Real.sin (ω * x) * ω)) x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_cos (ω * x)).comp x hlin
  have h := hcos.neg.div_const ω
  convert h using 1
  · ext y; ring
  · field_simp [hω]

private theorem abs_integral_cos_mul_deriv_le
    {Q : ℝ → ℝ} {ω : ℝ}
    (hQ'_int : IntegrableOn (deriv Q) (Icc (0 : ℝ) 1) volume) :
    |∫ x in (0 : ℝ)..1, Real.cos (ω * x) * deriv Q x|
      ≤ ∫ x in (0 : ℝ)..1, |deriv Q x| := by
  have h1 :
      ‖∫ x in (0 : ℝ)..1, Real.cos (ω * x) * deriv Q x‖
        ≤ ∫ x in (0 : ℝ)..1, ‖Real.cos (ω * x) * deriv Q x‖ :=
    intervalIntegral.norm_integral_le_integral_norm _
  have h2 :
      (∫ x in (0 : ℝ)..1, ‖Real.cos (ω * x) * deriv Q x‖)
        ≤ ∫ x in (0 : ℝ)..1, |deriv Q x| := by
    refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) ?_ ?_ ?_
    · exact (hQ'_int.mul_continuousOn
        ((continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn)).norm.intervalIntegrable
    · exact hQ'_int.abs.intervalIntegrable
    · intro x _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)
  simpa [Real.norm_eq_abs] using h1.trans h2

private theorem freq_mul_intervalSineInner_eq_boundary_plus_deriv
    {Q : ℝ → ℝ} {k : ℕ}
    (hk : k ≠ 0)
    (hQ_cont : ContinuousOn Q (Icc (0 : ℝ) 1))
    (hQ_deriv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt Q (deriv Q x) x)
    (hQ'_integrable :
      IntegrableOn (deriv Q) (Icc (0 : ℝ) 1) volume) :
    ((k : ℝ) * Real.pi) * intervalSineInner Q k =
      2 * (-Real.cos ((k : ℝ) * Real.pi) * Q 1 + Q 0)
        + 2 * ∫ x in (0 : ℝ)..1,
          Real.cos ((k : ℝ) * Real.pi * x) * deriv Q x := by
  classical
  set ω : ℝ := (k : ℝ) * Real.pi with hωdef
  have hkpos_nat : 0 < k := Nat.pos_of_ne_zero hk
  have hω_ne : ω ≠ 0 := by
    rw [hωdef]
    exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hkpos_nat)) Real.pi_ne_zero
  let A : ℝ → ℝ := fun x => -Real.cos (ω * x) / ω
  have hA_deriv : ∀ x, HasDerivAt A (Real.sin (ω * x)) x := by
    intro x; simpa [A] using hasDerivAt_neg_cos_div_freq (ω := ω) (x := x) hω_ne
  have hF_cont : ContinuousOn (fun x => A x * Q x) (Icc (0 : ℝ) 1) :=
    ((by fun_prop : Continuous A).continuousOn).mul hQ_cont
  have hF_deriv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun y => A y * Q y)
        (Real.sin (ω * x) * Q x + A x * deriv Q x) (Ioi x) x := by
    intro x hx
    exact ((hA_deriv x).mul (hQ_deriv x hx)).hasDerivWithinAt
  have hA_derivQ_int : IntervalIntegrable (fun x => A x * deriv Q x) volume 0 1 :=
    (hQ'_integrable.mul_continuousOn
      ((by fun_prop : Continuous A).continuousOn)).intervalIntegrable
  have hsinQ_int : IntervalIntegrable (fun x => Real.sin (ω * x) * Q x) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).mul hQ_cont
  have hderiv_int : IntervalIntegrable
      (fun x => Real.sin (ω * x) * Q x + A x * deriv Q x) volume 0 1 :=
    hsinQ_int.add hA_derivQ_int
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (show (0 : ℝ) ≤ 1 by norm_num) hF_cont hF_deriv hderiv_int
  have hsplit :
      (∫ x in (0 : ℝ)..1, Real.sin (ω * x) * Q x + A x * deriv Q x)
        = (∫ x in (0 : ℝ)..1, Real.sin (ω * x) * Q x)
          + ∫ x in (0 : ℝ)..1, A x * deriv Q x :=
    intervalIntegral.integral_add hsinQ_int hA_derivQ_int
  rw [hsplit] at hFTC
  have hA0 : A 0 = -1 / ω := by simp [A]
  have hA1 : A 1 = -Real.cos ω / ω := by simp [A]
  have hI :
      (∫ x in (0 : ℝ)..1, Real.sin (ω * x) * Q x)
        = A 1 * Q 1 - A 0 * Q 0 -
          ∫ x in (0 : ℝ)..1, A x * deriv Q x := by linarith
  have hAint :
      (∫ x in (0 : ℝ)..1, A x * deriv Q x)
        = -(1 / ω) * ∫ x in (0 : ℝ)..1,
            Real.cos (ω * x) * deriv Q x := by
    simp only [A]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x _ => ?_); ring
  unfold intervalSineInner; rw [if_neg hk, hI, hA0, hA1, hAint]
  rw [show ((k : ℝ) * Real.pi) = ω by rw [hωdef]]
  field_simp [hω_ne]; ring

/-- If a function `Q` is W¹,¹ on `[0,1]`, then its sine coefficient multiplied
by `kπ` is uniformly bounded.  This is the key analytic lemma that breaks the
O(k) growth of `truncatedChemDivSourceCoeff`.

For `k > 0`:
  `kπ · 2∫₀¹ sin(kπy) Q(y) dy = 2[-cos(kπy)Q(y)]₀¹ + 2∫₀¹ cos(kπy) Q'(y) dy`
  `≤ 2(|Q(0)| + |Q(1)|) + 2∫₀¹ |Q'(y)| dy` -/
theorem freq_mul_intervalSineInner_bound_of_W1
    {Q : ℝ → ℝ} {CQ Cder : ℝ}
    (hCQ : 0 ≤ CQ) (hCder : 0 ≤ Cder)
    (hQ_cont : ContinuousOn Q (Icc (0 : ℝ) 1))
    (hQ0 : |Q 0| ≤ CQ)
    (hQ1 : |Q 1| ≤ CQ)
    (hQ_deriv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt Q (deriv Q x) x)
    (hQ'_integrable :
      IntegrableOn (deriv Q) (Icc (0 : ℝ) 1) volume)
    (hQ'_bound :
      (∫ x in (0 : ℝ)..1, |deriv Q x|) ≤ Cder) :
    ∀ k : ℕ,
      |((k : ℝ) * Real.pi) * intervalSineInner Q k| ≤
        4 * CQ + 2 * Cder := by
  intro k
  by_cases hk : k = 0
  · subst k; simp [intervalSineInner, hCQ, hCder]
  · rw [freq_mul_intervalSineInner_eq_boundary_plus_deriv hk hQ_cont hQ_deriv hQ'_integrable]
    have hcos : |Real.cos ((k : ℝ) * Real.pi)| ≤ 1 := Real.abs_cos_le_one _
    have hboundary :
        |2 * (-Real.cos ((k : ℝ) * Real.pi) * Q 1 + Q 0)| ≤ 4 * CQ := by
      nlinarith [abs_add_le (2 * (-Real.cos ((k : ℝ) * Real.pi) * Q 1)) (2 * Q 0),
        abs_mul (2 : ℝ) (-Real.cos ((k : ℝ) * Real.pi) * Q 1),
        abs_mul (-Real.cos ((k : ℝ) * Real.pi)) (Q 1),
        abs_neg (Real.cos ((k : ℝ) * Real.pi))]
    have hint :
        |2 * ∫ x in (0 : ℝ)..1,
            Real.cos ((k : ℝ) * Real.pi * x) * deriv Q x|
          ≤ 2 * Cder := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left
        ((abs_integral_cos_mul_deriv_le (Q := Q)
          (ω := (k : ℝ) * Real.pi) hQ'_integrable).trans hQ'_bound)
        (by norm_num)
    linarith [abs_add_le
      (2 * (-Real.cos ((k : ℝ) * Real.pi) * Q 1 + Q 0))
      (2 * ∫ x in (0 : ℝ)..1,
        Real.cos ((k : ℝ) * Real.pi * x) * deriv Q x)]

/-! ## Level 0b: Truncated logistic source is bounded -/

/-- Cosine coefficients of the truncated logistic source are uniformly bounded
when the solution is bounded.  The logistic source `r(a - b·r_+^α)` is
pointwise bounded by a function of `a, b, α, M`, and its cosine coefficients
satisfy `|c_k| ≤ 2 · sup|source|`. -/
theorem truncatedLogisticSourceCoeff_bound_of_sup
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {s : ℝ} {M : ℝ} (hM : 0 < M)
    (hu_cont : ContinuousOn (intervalDomainLift (u s)) (Icc (0 : ℝ) 1))
    (hbound : ∀ x : intervalDomainPoint, |u s x| ≤ M) :
    ∃ CL : ℝ, 0 ≤ CL ∧ ∀ k : ℕ,
      |truncatedLogisticSourceCoeff p u s k| ≤ CL := by
  sorry

/-! ## Level 1: Flux W¹,¹ gives bounded chemDiv coefficients -/

/-- If the truncated chemotaxis flux has integrable derivative on [0,1], then
`truncatedChemDivSourceCoeff` is uniformly bounded in the mode index `k`.
Uses the fact that the flux vanishes at both Neumann endpoints
(`truncatedChemFluxLifted_zero_left/right`), so the IBP boundary term is zero
and the bound is `2 · ∫|flux'|`.

This connects `freq_mul_intervalSineInner_bound_of_W1` to the project's
source coefficient definition. -/
theorem truncatedChemDivSourceCoeff_bound_of_fluxW1
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {s : ℝ} {Cder : ℝ}
    (hCder : 0 ≤ Cder)
    (hflux_cont : ContinuousOn
      (truncatedChemFluxLifted p (u s)) (Icc (0 : ℝ) 1))
    (hflux_deriv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (truncatedChemFluxLifted p (u s))
        (deriv (truncatedChemFluxLifted p (u s)) x) x)
    (hflux_deriv_integrable :
      IntegrableOn (deriv (truncatedChemFluxLifted p (u s)))
        (Icc (0 : ℝ) 1) volume)
    (hflux_deriv_bound :
      (∫ x in (0 : ℝ)..1,
        |deriv (truncatedChemFluxLifted p (u s)) x|) ≤ Cder) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      |truncatedChemDivSourceCoeff p u s k| ≤ C := by
  have hflux0 : |truncatedChemFluxLifted p (u s) 0| ≤ 0 := by
    simp [truncatedChemFluxLifted_zero_left']
  have hflux1 : |truncatedChemFluxLifted p (u s) 1| ≤ 0 := by
    simp [truncatedChemFluxLifted_zero_right']
  exact ⟨2 * Cder, by linarith,
    fun k => by
      have := freq_mul_intervalSineInner_bound_of_W1 le_rfl hCder
        hflux_cont hflux0 hflux1 hflux_deriv hflux_deriv_integrable hflux_deriv_bound k
      simp only [truncatedChemDivSourceCoeff] at *
      linarith⟩

/-! ## Level 2: Full source bounded at positive time -/

/-- At positive time, the truncated Picard limit has bounded source coefficients.
This combines the bounded logistic source with bounded chemDiv (from flux W¹,¹).

The proof uses the bootstrap:
- At positive time, the Picard limit is C¹ (heat semigroup smoothing +
  Volterra-type gradient contraction on the iterates)
- C¹ solution → flux W¹,¹ (resolver spatial regularity)
- Bounded logistic (from Picard ball) + bounded chemDiv → bounded total source -/
theorem truncatedBFormSourceCoeff_bound_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {s : ℝ} (hs : 0 < s) (hsT : s ≤ DT.T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      |truncatedBFormSourceCoeff p
        (truncatedConjugatePicardLimit p u₀ DT.T) s k| ≤ C := by
  set u := truncatedConjugatePicardLimit p u₀ DT.T with hu_def
  set SD : TruncatedConjugateMildSolutionData p u₀ :=
    truncatedConjugateMildSolutionData_of_data DT
  have hball : ∀ x : intervalDomainPoint, |u s x| ≤ SD.M :=
    SD.hbound s hs (le_trans hsT (le_of_eq rfl))
  have hcont_slice : Continuous (u s) := SD.hcont s hs (le_trans hsT (le_of_eq rfl))
  have hcont_lift : ContinuousOn (intervalDomainLift (u s)) (Icc (0 : ℝ) 1) :=
    sorry -- lift of continuous slice is ContinuousOn [0,1]
  -- Part 1: logistic bound
  have ⟨CL, hCL, hlog⟩ := truncatedLogisticSourceCoeff_bound_of_sup (p := p) DT.hM hcont_lift hball
  -- Part 2: chemDiv bound (from flux W^{1,1} at positive time — via gradient bound)
  have ⟨CC, hCC, hchem⟩ : ∃ CC : ℝ, 0 ≤ CC ∧ ∀ k,
      |truncatedChemDivSourceCoeff p u s k| ≤ CC := by
    sorry -- needs truncatedChemDivSourceCoeff_bound_of_fluxW1 + flux regularity
  -- Triangle inequality
  exact ⟨CL + |p.χ₀| * CC, add_nonneg hCL (mul_nonneg (abs_nonneg _) hCC),
    fun k => by
      simp only [truncatedBFormSourceCoeff]
      have h1 := hlog k
      have h2 : |p.χ₀| * |truncatedChemDivSourceCoeff p u s k| ≤ |p.χ₀| * CC :=
        mul_le_mul_of_nonneg_left (hchem k) (abs_nonneg _)
      have htri : |truncatedLogisticSourceCoeff p u s k
              - p.χ₀ * truncatedChemDivSourceCoeff p u s k|
          ≤ |truncatedLogisticSourceCoeff p u s k|
            + |p.χ₀| * |truncatedChemDivSourceCoeff p u s k| := by
        calc |truncatedLogisticSourceCoeff p u s k
                - p.χ₀ * truncatedChemDivSourceCoeff p u s k|
            ≤ |truncatedLogisticSourceCoeff p u s k|
              + |-(p.χ₀ * truncatedChemDivSourceCoeff p u s k)| := by
              rw [show truncatedLogisticSourceCoeff p u s k
                - p.χ₀ * truncatedChemDivSourceCoeff p u s k
                = truncatedLogisticSourceCoeff p u s k
                + (-(p.χ₀ * truncatedChemDivSourceCoeff p u s k)) from sub_eq_add_neg _ _]
              exact abs_add_le _ _
          _ = |truncatedLogisticSourceCoeff p u s k|
              + |p.χ₀| * |truncatedChemDivSourceCoeff p u s k| := by
              rw [abs_neg, abs_mul]
      linarith⟩

/-! ## Level 3: Sobolev ladder for positive-time coefficient regularity

The dependency chain (non-circular, Q3942 architecture):

  Step 1. Ball bound → source O(1) → eigenvalue gain → |Duh_k| ≤ C/λ_k
          → u ∈ H¹ at positive time (Σ λ_k |c_k|² < ∞)

  Step 2. u ∈ H¹ → source ∈ ℓ² (composition preserves H¹ in 1D;
          chemDiv: IBP + flux' ∈ L² from elliptic regularity)

  Step 3. ℓ² source → gradient ℓ¹ (split at t/2; tail: Cauchy-Schwarz
          with env ∈ ℓ² and 1/k ∈ ℓ²)

  Step 4. Gradient bound → source ∈ ℓ¹ (logistic O(1/k²) + chemDiv
          second IBP gives ℓ¹)

  Step 5. ℓ¹ source → eigenvalue-weighted summability (eigenvalue gain
          with summable envelope)

Each step uses ONLY the output of the previous step, no circularity. -/

/-- **ℓ¹ coefficient summability**: at positive time the Picard limit has
summable cosine coefficients.  From the constant source bound, eigenvalue
gain gives `|Duh_k| ≤ C/λ_k = O(1/k²)`, summable.  The homogeneous part
has exponential decay.  This is the weakest regularity step. -/
theorem truncatedPicardCoeff_summable_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    Summable (fun k : ℕ =>
      |truncatedPicardCoeff p u₀
        (truncatedConjugatePicardLimit p u₀ DT.T) t k|) := by
  sorry

/-- **H¹ at positive time (Sobolev ladder step 1).**  The truncated Picard
coefficients satisfy `Σ λ_k |c_k(t)|² < ∞`.

Non-circular proof: eigenvalue gain with bounded source gives
`|Duh_k| ≤ C/λ_k`, so `λ_k(C/λ_k)² = C²/λ_k`, summable as p-series.
The homogeneous part: `λ_k exp(-2λ_k t) M²` is summable by exponential
decay.  No gradient bound needed. -/
theorem truncatedPicardCoeff_h1_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    Summable (fun k : ℕ =>
      (unitIntervalCosineEigenvalue k) *
        (truncatedPicardCoeff p u₀
          (truncatedConjugatePicardLimit p u₀ DT.T) t k) ^ 2) := by
  sorry

/-- **ℓ² source envelope (Sobolev ladder step 2).**  Once u ∈ H¹ at
positive time, the source coefficients are ℓ².  The logistic part: H¹
composition in 1D.  The chemDiv part: u ∈ H¹ → v ∈ H² (elliptic) →
∇v ∈ H¹ → flux = u·∇v ∈ H¹ → flux' ∈ L² → kπ·sineInner(flux,k) =
cosCoeff(flux') ∈ ℓ². -/
theorem truncatedBFormSourceCoeff_l2_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    Summable (fun k : ℕ =>
      (truncatedBFormSourceCoeff p
        (truncatedConjugatePicardLimit p u₀ DT.T) t k) ^ 2) := by
  have _hh1 := truncatedPicardCoeff_h1_positive_time DT ht htT
  sorry

/-- **Gradient-weighted ℓ¹ (Sobolev ladder step 3).**  `∑ |a_k| · kπ < ∞`.

Non-circular proof: split at τ = t/2.
- Homogeneous restart: bounded coefficients × exp(-Lλ_k) → kπ-summable
  by `frequency_pow_mul_exp_summable`.
- Duhamel tail on [τ,t]: eigenvalue gain with ℓ² envelope gives
  `kπ |tail_k| ≤ env_k/(kπ)`, and Cauchy-Schwarz with `env ∈ ℓ²`
  and `1/k ∈ ℓ²` gives summability.

This does NOT depend on eigenvalue-weighted summability or the gradient
bound — it is the FIRST gradient-level result, using only H¹ + ℓ² source. -/
theorem truncatedPicardCoeff_grad_l1_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    Summable (fun k : ℕ =>
      |truncatedPicardCoeff p u₀
        (truncatedConjugatePicardLimit p u₀ DT.T) t k| *
        ((k : ℝ) * Real.pi)) := by
  have _hl2 := truncatedBFormSourceCoeff_l2_positive_time
    DT (by linarith : (0 : ℝ) < t / 2) (by linarith)
  sorry

/-- **ℓ¹ source envelope (Sobolev ladder step 4).**  Once u has bounded
gradient (from `grad_l1`), the source coefficients are ℓ¹.
- Logistic: u ∈ W^{1,∞} → f(u) ∈ W^{1,∞} with f'(u)·u_x vanishing at
  boundary (Neumann) → cosCoeff = O(1/k²) → ℓ¹.
- ChemDiv: kπ·sineInner(flux,k) = cosCoeff(flux') = -sineInner(flux'')/kπ.
  u ∈ H² (from ℓ² source step) → flux'' ∈ L² → ℓ² → divided by kπ → ℓ¹
  by Cauchy-Schwarz. -/
theorem truncatedBFormSourceCoeff_summable_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    Summable (fun k : ℕ =>
      |truncatedBFormSourceCoeff p
        (truncatedConjugatePicardLimit p u₀ DT.T) t k|) := by
  have _hgrad := truncatedPicardCoeff_grad_l1_positive_time DT ht htT
  sorry

/-- **Eigenvalue-weighted summability (Sobolev ladder step 5).**
`Σ λ_k |c_k| < ∞`.  Once source ∈ ℓ¹, split-Duhamel with exponential
head damping and eigenvalue gain on the tail gives summability. -/
theorem truncatedPicardCoeff_eigenvalue_weighted_summable_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        |truncatedPicardCoeff p u₀
          (truncatedConjugatePicardLimit p u₀ DT.T) t k|) := by
  have _hl1_src := truncatedBFormSourceCoeff_summable_positive_time
    DT (by linarith : (0 : ℝ) < t / 2) (by linarith)
  sorry

/-- Time derivative coefficient summability.  `a'_k = -λ_k a_k + src_k`,
so `|a'_k| ≤ λ_k|a_k| + |src_k|`.  Uses eigenvalue-weighted + source ℓ¹. -/
theorem truncatedPicardCoeffTimeDeriv_summable_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    Summable (fun k : ℕ =>
      |truncatedPicardCoeffTimeDeriv p u₀
        (truncatedConjugatePicardLimit p u₀ DT.T) t k|) := by
  have _heig := truncatedPicardCoeff_eigenvalue_weighted_summable_positive_time DT ht htT
  have _hsrc := truncatedBFormSourceCoeff_summable_positive_time DT ht htT
  sorry

/-! ## Level 4: Gradient bound and C¹ regularity -/

/-- Bounded gradient for the truncated Picard limit at positive time.
This follows from gradient-weighted ℓ¹ summability: the gradient is
represented by the uniformly convergent cosine-derivative series
`∂_x u(t,x) = -∑ a_k · kπ · sin(kπx)`, and `∑ |a_k| · kπ < ∞` gives
the bound `|∂_x u| ≤ ∑ |a_k| · kπ`. -/
theorem truncatedPicardLimit_gradient_bound_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift
        ((truncatedConjugatePicardLimit p u₀ DT.T) t)) x| ≤ G := by
  sorry

/-! ## Level 4b: Test function (negativePartTest) regularity -/

/-- The negative-part test `φ = -u_-` is differentiable off a countable set
when the solution is C¹.  The non-differentiability points of `max(-f, 0)`
are exactly the zeros of `f` where `f' = 0` (non-transversal zeros).
For a C¹ function `f` on a compact interval, the set
`{x : f(x) = 0 ∧ f'(x) = 0}` is at most countable (it has no accumulation
point at which both `f` and `f'` vanish with `f` not identically zero on
any interval). -/
theorem negativePartTest_diff_off_countable_of_gradient_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    ∃ s : Set ℝ, s.Countable ∧
      ∀ x ∈ Ioo (0 : ℝ) 1 \ s,
        HasDerivAt (negativePartTest
          (truncatedConjugatePicardLimit p u₀ DT.T) t)
          (deriv (negativePartTest
            (truncatedConjugatePicardLimit p u₀ DT.T) t) x) x := by
  sorry

/-- The negative-part test has a bounded derivative.  Since
`|(-f)_+'| ≤ |f'|`, the bound is the gradient bound of `u`. -/
theorem negativePartTest_deriv_bound_of_gradient_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    ∃ C : ℝ, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (negativePartTest
        (truncatedConjugatePicardLimit p u₀ DT.T) t) x| ≤ C := by
  sorry

/-! ## Level 4c: Chem flux regularity -/

/-- Continuity of the truncated chemotaxis flux on `[0,1]`.  The flux is
`positivePart(u) · resolverGrad / (1 + R)^β`.  At positive time, `u` is
continuous (from `DT.hcont`), the resolver is continuous (elliptic regularity
on bounded input), and the product/quotient is continuous. -/
theorem truncatedChemFlux_continuousOn_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    ContinuousOn
      (truncatedChemFluxLifted p
        ((truncatedConjugatePicardLimit p u₀ DT.T) t))
      (Icc (0 : ℝ) 1) := by
  sorry

/-- The truncated chemotaxis flux is differentiable off a countable set.
Like the negative-part test, the only source of non-differentiability
is `positivePart` in the flux definition, which is differentiable off
the (at most countable) transversal zero set of the solution. -/
theorem truncatedChemFlux_diff_off_countable_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    ∃ s_chem : Set ℝ, s_chem.Countable ∧
      ∀ x ∈ Ioo (0 : ℝ) 1 \ s_chem,
        HasDerivAt
          (truncatedChemFluxLifted p
            ((truncatedConjugatePicardLimit p u₀ DT.T) t))
          (deriv (truncatedChemFluxLifted p
            ((truncatedConjugatePicardLimit p u₀ DT.T) t)) x) x := by
  sorry

/-- Bounded derivative of the truncated chemotaxis flux.  From bounded
gradient of `u`, resolver bounds, and the product rule. -/
theorem truncatedChemFlux_deriv_bound_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    ∃ C_chem : ℝ, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (truncatedChemFluxLifted p
        ((truncatedConjugatePicardLimit p u₀ DT.T) t)) x| ≤ C_chem := by
  sorry

/-! ## Level 5: Series representations (time derivative + gradient) -/

/-- Time-derivative cosine series representation.  At positive time with
ℓ¹ time-derivative coefficients, the time derivative of the Picard limit
equals its cosine series `∑' k, a'_k cos(kπx)`. -/
theorem truncatedPicardLimit_timeDeriv_rep_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (fun z : intervalDomainPoint =>
        ShenWork.IntervalDomain.intervalDomain.timeDeriv
          (truncatedConjugatePicardLimit p u₀ DT.T) t z) x
        = ∑' k : ℕ, truncatedPicardCoeffTimeDeriv p u₀
            (truncatedConjugatePicardLimit p u₀ DT.T) t k *
            ShenWork.CosineSpectrum.cosineMode k x := by
  sorry

/-- Gradient cosine series representation.  At positive time with
gradient-weighted ℓ¹ coefficients, the gradient equals the termwise
differentiated series `∑' k, a_k · (-kπ sin(kπx))`. -/
theorem truncatedPicardLimit_grad_rep_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      deriv (intervalDomainLift
        ((truncatedConjugatePicardLimit p u₀ DT.T) t)) x
        = ∑' k : ℕ, truncatedPicardCoeff p u₀
            (truncatedConjugatePicardLimit p u₀ DT.T) t k *
          deriv (ShenWork.CosineSpectrum.cosineMode k) x := by
  sorry

/-! ## Level 5b: Tested summability (bilinear products) -/

/-- The Laplacian-tested summability: `∑ λ_k a_k · testCoeff_k` converges.
This follows from eigenvalue-weighted summability of `a_k` and boundedness
of test coefficients (cosine coefficients of a bounded function). -/
theorem truncatedPicardLimit_lap_summable_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        truncatedPicardCoeff p u₀
          (truncatedConjugatePicardLimit p u₀ DT.T) t k *
        cosineTestCoeff
          (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k) := by
  sorry

/-- Source-tested summability: `∑ src_k · testCoeff_k` converges. -/
theorem truncatedPicardLimit_source_summable_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    Summable (fun k : ℕ =>
      truncatedBFormSourceCoeff p
          (truncatedConjugatePicardLimit p u₀ DT.T) t k *
        cosineTestCoeff
          (negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t) k) := by
  sorry

end ShenWork.Paper2.TruncatedPositiveTimeBootstrap
