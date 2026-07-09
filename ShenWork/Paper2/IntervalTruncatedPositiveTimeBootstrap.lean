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
import ShenWork.Paper2.IntervalCompactSliceGradientBounds
import ShenWork.Paper2.IntervalConjugateKernelIBP
import ShenWork.Paper2.IntervalConjugateCosineSeries
import ShenWork.Paper2.IntervalDomainL2UEnergyCombine
import ShenWork.Paper2.IntervalMildPicardRegularity
import ShenWork.Paper2.IntervalResolverWeakLapBound
import ShenWork.Paper2.IntervalResolverWeakODEBridge
import ShenWork.Paper2.IntervalTruncatedGradientWindow
import ShenWork.Paper2.IntervalTruncatedLeftProfileWiring
import ShenWork.Paper2.IntervalTruncatedPositiveTimeGradientAtoms
import ShenWork.PDE.CosineSpectrum
import ShenWork.Wiener.EWA.SourceRealizesRecords

open MeasureTheory Set Asymptotics
open scoped BigOperators Topology Real

noncomputable section

namespace ShenWork.Paper2.TruncatedPositiveTimeBootstrap

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure intervalSet)
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
   truncatedLogisticLocal truncatedLogisticLifted
   truncatedPicardCoeff truncatedPicardCoeffTimeDeriv
   truncatedPicardInitialCoeff
   truncatedConjugatePicardIter
   truncatedConjugatePicardIter_ball
   truncatedConjugatePicardIter_geometric
   truncatedConjugatePicardLimit
   truncatedConjugatePicardIter_pointwise_convergent
   TruncatedConjugateMildExistenceData
   TruncatedConjugateMildSolutionData
   truncatedConjugateMildSolutionData_of_data
   negativePartTest cosineTestCoeff)
open ShenWork.IntervalMildPicard (HasContinuousSlices HasJointMeasurability)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.CosineParsevalBridge (unitIntervalEvenReflection)
open ShenWork.HeatKernelGradientEstimates
  (unitIntervalNeumannCosineCoeff unitIntervalNeumannCosineCoeff_l2_bound)
open ShenWork.PDE.ResolventEstimate (coeffL2Energy coeffL2Norm)
open ShenWork.Paper3 (unitIntervalNeumannSpectrum)
open ShenWork.Paper2.TruncatedGradientWindow

/-! ## Helper: truncated logistic local bound -/

private theorem lift_continuousOn_Icc_of_continuous
    {g : intervalDomainPoint → ℝ} (hg : Continuous g) :
    ContinuousOn (intervalDomainLift g) (Set.Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have hres : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift g) = g := by
    funext z
    obtain ⟨z, hz⟩ := z
    show intervalDomainLift g z = g ⟨z, hz⟩
    rw [intervalDomainLift, dif_pos hz]
  rw [hres]
  exact hg

private theorem positivePart_le_abs' (r : ℝ) :
    positivePart r ≤ |r| := by
  by_cases hr : 0 ≤ r
  · simp [positivePart, hr, abs_of_nonneg hr]
  · have hr' : r ≤ 0 := le_of_not_ge hr
    simp [positivePart, hr', abs_of_nonpos hr']

private theorem truncatedLogisticLocal_abs_le_of_abs_le'
    (p : CM2Params) {M r : ℝ} (hM : 0 < M) (hr : |r| ≤ M) :
    |truncatedLogisticLocal p r| ≤
      M * (p.a + p.b * M ^ p.α) := by
  have hM_nonneg : 0 ≤ M := hM.le
  have hpp_nonneg : 0 ≤ positivePart r := positivePart_nonneg r
  have hpp_le_M : positivePart r ≤ M :=
    (positivePart_le_abs' r).trans hr
  have hpow_nonneg : 0 ≤ (positivePart r) ^ p.α :=
    Real.rpow_nonneg hpp_nonneg _
  have hpow_le : (positivePart r) ^ p.α ≤ M ^ p.α :=
    Real.rpow_le_rpow hpp_nonneg hpp_le_M p.hα.le
  have hinner :
      |p.a - p.b * (positivePart r) ^ p.α|
        ≤ p.a + p.b * M ^ p.α := by
    calc
      |p.a - p.b * (positivePart r) ^ p.α|
          ≤ |p.a| + |p.b * (positivePart r) ^ p.α| := abs_sub _ _
      _ = p.a + p.b * (positivePart r) ^ p.α := by
          rw [abs_of_nonneg p.ha, abs_mul, abs_of_nonneg p.hb,
            abs_of_nonneg hpow_nonneg]
      _ ≤ p.a + p.b * M ^ p.α := by
          exact add_le_add (le_refl p.a)
            (mul_le_mul_of_nonneg_left hpow_le p.hb)
  calc
    |truncatedLogisticLocal p r|
        = |r| * |p.a - p.b * (positivePart r) ^ p.α| := by
          simp [truncatedLogisticLocal, abs_mul]
    _ ≤ M * (p.a + p.b * M ^ p.α) :=
        mul_le_mul hr hinner (abs_nonneg _) hM_nonneg

/-- Product-rule envelope for the truncated chemotaxis flux.

This is the analytic frontier used by the positive-time gradient bootstrap:
bounded iterate, an iterate-gradient envelope, resolver-gradient envelope
`Γ`, and resolver weak-Laplacian envelope `H` give
`|Q'| ≤ M H + β M Γ² + Γ G`. -/
private theorem truncatedChemFluxLifted_deriv_abs_le_of_ball_grad
    (p : CM2Params) {w : intervalDomainPoint → ℝ}
    {M Γ H G : ℝ}
    (hM : 0 < M)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M)
    (hgrad : ∀ x : ℝ, |deriv (intervalDomainLift w) x| ≤ G)
    (y : ℝ)
    {dpos gp q qDen : ℝ}
    (hderiv :
      deriv (truncatedChemFluxLifted p w) y =
        dpos * resolverGradReal p w y * q
          + positivePart (intervalDomainLift w y) * gp * q
          - p.β * positivePart (intervalDomainLift w y)
              * (resolverGradReal p w y) ^ 2 * qDen)
    (hdpos : |dpos| ≤ |deriv (intervalDomainLift w) y|)
    (hgradR : |resolverGradReal p w y| ≤ Γ)
    (hgp : |gp| ≤ H)
    (hq : |q| ≤ 1)
    (hqDen : |qDen| ≤ 1) :
    (|deriv (truncatedChemFluxLifted p w) y| ≤
      (M * H + p.β * M * Γ ^ 2) + Γ * G) := by
  have hUpos_abs :
      |positivePart (intervalDomainLift w y)| ≤ M := by
    have hlift_abs : |intervalDomainLift w y| ≤ M := by
      by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
      · simp only [intervalDomainLift, dif_pos hy]
        exact hball ⟨y, hy⟩
      · simp only [intervalDomainLift, dif_neg hy, abs_zero]
        exact hM.le
    rw [abs_of_nonneg (positivePart_nonneg _)]
    exact (positivePart_le_abs' (intervalDomainLift w y)).trans hlift_abs
  have hdG : |dpos| ≤ G := hdpos.trans (hgrad y)
  have hG_nonneg : 0 ≤ G := (abs_nonneg dpos).trans hdG
  have hΓ_nonneg : 0 ≤ Γ :=
    (abs_nonneg (resolverGradReal p w y)).trans hgradR
  have hH_nonneg : 0 ≤ H := (abs_nonneg gp).trans hgp
  have hterm₁ :
      |dpos * resolverGradReal p w y * q| ≤ Γ * G := by
    have hprod :
        |dpos| * |resolverGradReal p w y| ≤ G * Γ :=
      mul_le_mul hdG hgradR (abs_nonneg _) hG_nonneg
    calc
      |dpos * resolverGradReal p w y * q|
          = |dpos| * |resolverGradReal p w y| * |q| := by
            rw [abs_mul, abs_mul]
      _ ≤ G * Γ * 1 :=
            mul_le_mul hprod hq (abs_nonneg _)
              (mul_nonneg hG_nonneg hΓ_nonneg)
      _ = Γ * G := by ring
  have hterm₂ :
      |positivePart (intervalDomainLift w y) * gp * q| ≤ M * H := by
    have hprod :
        |positivePart (intervalDomainLift w y)| * |gp| ≤ M * H :=
      mul_le_mul hUpos_abs hgp (abs_nonneg _) hM.le
    calc
      |positivePart (intervalDomainLift w y) * gp * q|
          = |positivePart (intervalDomainLift w y)| * |gp| * |q| := by
            rw [abs_mul, abs_mul]
      _ ≤ M * H * 1 :=
            mul_le_mul hprod hq (abs_nonneg _)
              (mul_nonneg hM.le hH_nonneg)
      _ = M * H := by ring
  have hgradR_sq : |resolverGradReal p w y| ^ 2 ≤ Γ ^ 2 := by
    nlinarith [hgradR, abs_nonneg (resolverGradReal p w y), hΓ_nonneg,
      sq_nonneg (Γ - |resolverGradReal p w y|)]
  have hterm₃ :
      |p.β * positivePart (intervalDomainLift w y)
          * (resolverGradReal p w y) ^ 2 * qDen|
        ≤ p.β * M * Γ ^ 2 := by
    have hβU :
        p.β * |positivePart (intervalDomainLift w y)| ≤ p.β * M :=
      mul_le_mul_of_nonneg_left hUpos_abs p.hβ
    have hβU_nonneg :
        0 ≤ p.β * |positivePart (intervalDomainLift w y)| :=
      mul_nonneg p.hβ (abs_nonneg _)
    have hβUg :
        p.β * |positivePart (intervalDomainLift w y)|
            * |resolverGradReal p w y| ^ 2
          ≤ p.β * M * Γ ^ 2 :=
      mul_le_mul hβU hgradR_sq (sq_nonneg _)
        (mul_nonneg p.hβ hM.le)
    have hβMg_nonneg : 0 ≤ p.β * M * Γ ^ 2 :=
      mul_nonneg (mul_nonneg p.hβ hM.le) (sq_nonneg _)
    have hsq_abs :
        |(resolverGradReal p w y) ^ 2|
          = |resolverGradReal p w y| ^ 2 := by
      rw [pow_two, abs_mul, pow_two]
    calc
      |p.β * positivePart (intervalDomainLift w y)
          * (resolverGradReal p w y) ^ 2 * qDen|
          = p.β * |positivePart (intervalDomainLift w y)|
              * |resolverGradReal p w y| ^ 2 * |qDen| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg p.hβ, hsq_abs]
      _ ≤ p.β * M * Γ ^ 2 * 1 :=
            mul_le_mul hβUg hqDen (abs_nonneg _) hβMg_nonneg
      _ = p.β * M * Γ ^ 2 := by ring
  set A : ℝ := dpos * resolverGradReal p w y * q
  set B : ℝ := positivePart (intervalDomainLift w y) * gp * q
  set C : ℝ :=
    p.β * positivePart (intervalDomainLift w y)
      * (resolverGradReal p w y) ^ 2 * qDen
  have htri : |A + B - C| ≤ |A| + |B| + |C| := by
    calc
      |A + B - C| = |(A + B) + -C| := by ring_nf
      _ ≤ |A + B| + |-C| := abs_add_le _ _
      _ = |A + B| + |C| := by rw [abs_neg]
      _ ≤ (|A| + |B|) + |C| := by
            simpa [add_assoc, add_comm, add_left_comm] using
              add_le_add_left (abs_add_le A B) |C|
      _ = |A| + |B| + |C| := by ring
  calc
    |deriv (truncatedChemFluxLifted p w) y|
        = |A + B - C| := by
          rw [hderiv]
    _ ≤ |A| + |B| + |C| := htri
    _ ≤ Γ * G + M * H + p.β * M * Γ ^ 2 := by
          exact add_le_add (add_le_add hterm₁ hterm₂) hterm₃
    _ = (M * H + p.β * M * Γ ^ 2) + Γ * G := by ring

private theorem truncatedChemFluxLifted_deriv_eq_zero_off_Ioo
    (p : CM2Params) (w : intervalDomainPoint → ℝ) {y : ℝ}
    (hy : y ∉ Set.Ioo (0 : ℝ) 1) :
    deriv (truncatedChemFluxLifted p w) y = 0 := by
  let F : intervalDomainPoint → ℝ := fun x =>
    positivePart (w x) * resolverGradReal p w x.1
      / (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) x.1) ^ p.β
  have hflux_eq : truncatedChemFluxLifted p w = intervalDomainLift F := by
    funext z
    by_cases hz : z ∈ Set.Icc (0 : ℝ) 1
    · simp [truncatedChemFluxLifted, F, intervalDomainLift, hz]
    · simp [truncatedChemFluxLifted, intervalDomainLift, hz, positivePart]
  let Uconst : ℝ → intervalDomainPoint → ℝ := fun _ => F
  rcases lt_or_ge y 0 with hy0 | hy0
  · have hzero :
        deriv (intervalDomainLift (Uconst 0)) y = 0 := by
      simpa [Uconst] using
        (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_on_Iio
          Uconst 0 hy0)
    simpa [hflux_eq, Uconst] using hzero
  rcases lt_or_ge 1 y with hy1 | hy1
  · have hzero :
        deriv (intervalDomainLift (Uconst 0)) y = 0 := by
      simpa [Uconst] using
        (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_on_Ioi
          Uconst 0 hy1)
    simpa [hflux_eq, Uconst] using hzero
  rcases eq_or_lt_of_le hy0 with hy_eq | hy_pos
  · subst y
    have hzero :
        deriv (intervalDomainLift (Uconst 0)) 0 = 0 := by
      simpa [Uconst] using
        (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_at_left
          Uconst 0)
    simpa [hflux_eq, Uconst] using hzero
  rcases eq_or_lt_of_le hy1 with hy_eq | hy_lt_one
  · subst y
    have hzero :
        deriv (intervalDomainLift (Uconst 0)) 1 = 0 := by
      simpa [Uconst] using
        (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_at_right
          Uconst 0)
    simpa [hflux_eq, Uconst] using hzero
  · exact False.elim (hy ⟨hy_pos, hy_lt_one⟩)

/-- Analytic product-rule package for the truncated chemotaxis flux on a bounded
continuous slice.

This is the named version of the local `hflux_terms` obligation used by the
positive-time gradient bootstrap.  It packages:
* the product/chain/quotient rule for
  `positivePart(lift w) * resolverGradReal p w / (1 + lift(R w))^β`;
* the `positivePart` Lipschitz derivative bound;
* resolver gradient and physical Hessian bounds from the absolute `M`-ball;
* denominator bounds from resolver nonnegativity.

ANALYTIC GAP: for the signed truncated Picard iterates used here the repository
does not currently expose the resolver nonnegativity / ODE-Hessian bridge under
only `|w| ≤ M`.  The nonnegative-source API is insufficient because these
iterates may be negative. -/
private theorem resolverGrad_abs_le_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M) (y : ℝ) :
    |resolverGradReal p w y| ≤
      Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
        * (2 * (p.ν * M ^ p.γ)) := by
  classical
  have hUcont : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) :=
    lift_continuousOn_Icc_of_continuous hw_cont
  have hM_nonneg : 0 ≤ M := hM.le
  let A : ℕ → ℂ := fun k =>
    ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k -
      ShenWork.PDE.intervalNeumannResolverSourceCoeff p (fun _ => 0) k
  let e : ℕ → ℝ := fun k => (A k).re
  let m : ℕ → ℝ := fun k =>
    (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * y)) /
      (p.μ + unitIntervalNeumannSpectrum.eigenvalue k)
  have hsrc :
      Summable fun k : ℕ =>
        ((ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k -
          ShenWork.PDE.intervalNeumannResolverSourceCoeff p (fun _ => 0) k).re) ^ 2 := by
    simpa [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      ShenWork.IntervalResolverWeakBounds.resolverSourceCoeff_re_sq_summable_of_continuousOn
        p hUcont
  have he_sq : Summable fun k : ℕ => (e k) ^ 2 := by
    simpa [e, A] using hsrc
  have hm_sq : Summable fun k : ℕ => (m k) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) ?_
      (ShenWork.PDE.intervalNeumannResolverGradWeight_sq_summable p)
    intro k
    have hden_pos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue k :=
      ShenWork.PDE.intervalNeumannResolver_denom_pos p k
    have hsin : (Real.sin ((k : ℝ) * Real.pi * y)) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]
      exact Real.abs_sin_le_one _
    have hgweq :
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2 =
          ((k : ℝ) * Real.pi) ^ 2 /
            (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) ^ 2 := by
      rw [ShenWork.PDE.intervalNeumannResolverGradWeight, div_pow]
    rw [hgweq]
    dsimp [m]
    rw [div_pow, mul_pow, neg_pow]
    have hkp : (0 : ℝ) ≤ ((k : ℝ) * Real.pi) ^ 2 := by positivity
    have hnum :
        (-1 : ℝ) ^ 2 * ((k : ℝ) * Real.pi) ^ 2 *
            (Real.sin ((k : ℝ) * Real.pi * y)) ^ 2 ≤
          ((k : ℝ) * Real.pi) ^ 2 := by
      have h1 : (-1 : ℝ) ^ 2 = 1 := by norm_num
      rw [h1, one_mul]
      nlinarith [hkp, hsin, sq_nonneg (Real.sin ((k : ℝ) * Real.pi * y))]
    gcongr
  have hterm : ∀ k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverCoeff p w k).re *
          (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * y)) =
        e k * m k := by
    intro k
    have hden : p.μ + unitIntervalNeumannSpectrum.eigenvalue k ≠ 0 :=
      ne_of_gt (ShenWork.PDE.intervalNeumannResolver_denom_pos p k)
    dsimp [e, A, m]
    rw [ShenWork.IntervalResolverGradientBridge.resolverCoeff_re_eq p w k]
    simp only [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero]
    field_simp [hden]
    rw [Complex.zero_re]
    ring
  have hsum_eq :
      resolverGradReal p w y = ∑' k : ℕ, e k * m k := by
    unfold resolverGradReal
    exact tsum_congr hterm
  have hCS :
      |∑' k : ℕ, e k * m k| ≤
        Real.sqrt (∑' k : ℕ, (e k) ^ 2) *
          Real.sqrt (∑' k : ℕ, (m k) ^ 2) :=
    real_abs_tsum_mul_le_sqrt_tsum_sq_mul_sqrt_tsum_sq he_sq hm_sq
  have hA_l2 :
      Real.sqrt (∑' k : ℕ, (e k) ^ 2) ≤ coeffL2Norm A := by
    rw [coeffL2Norm, coeffL2Energy]
    apply Real.sqrt_le_sqrt
    refine he_sq.tsum_le_tsum ?_
      (ShenWork.PDE.intervalNeumannResolverR_source_l2_summable p w (fun _ => 0) hsrc)
    intro k
    have : (e k) ^ 2 = (A k).re * (A k).re := by
      dsimp [e]
      ring
    rw [this]
    calc
      (A k).re * (A k).re ≤ Complex.normSq (A k) := Complex.re_sq_le_normSq _
      _ = ‖A k‖ ^ 2 := (Complex.sq_norm _).symm
  have hmW :
      Real.sqrt (∑' k : ℕ, (m k) ^ 2) ≤
        Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) := by
    apply Real.sqrt_le_sqrt
    refine hm_sq.tsum_le_tsum ?_
      (ShenWork.PDE.intervalNeumannResolverGradWeight_sq_summable p)
    intro k
    have hden_pos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue k :=
      ShenWork.PDE.intervalNeumannResolver_denom_pos p k
    have hsin : (Real.sin ((k : ℝ) * Real.pi * y)) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]
      exact Real.abs_sin_le_one _
    have hgweq :
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2 =
          ((k : ℝ) * Real.pi) ^ 2 /
            (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) ^ 2 := by
      rw [ShenWork.PDE.intervalNeumannResolverGradWeight, div_pow]
    rw [hgweq]
    dsimp [m]
    rw [div_pow, mul_pow, neg_pow]
    have hkp : (0 : ℝ) ≤ ((k : ℝ) * Real.pi) ^ 2 := by positivity
    have hnum :
        (-1 : ℝ) ^ 2 * ((k : ℝ) * Real.pi) ^ 2 *
            (Real.sin ((k : ℝ) * Real.pi * y)) ^ 2 ≤
          ((k : ℝ) * Real.pi) ^ 2 := by
      have h1 : (-1 : ℝ) ^ 2 = 1 := by norm_num
      rw [h1, one_mul]
      nlinarith [hkp, hsin, sq_nonneg (Real.sin ((k : ℝ) * Real.pi * y))]
    gcongr
  have hgcont : ContinuousOn
      (fun x : ℝ => p.ν * intervalDomainLift w x ^ p.γ) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.mul
      (hUcont.rpow_const (fun _ _ => Or.inr p.hγ.le))
  have hzero_cont : ContinuousOn
      (fun x : ℝ => p.ν * intervalDomainLift (fun _ : intervalDomainPoint => 0) x ^ p.γ)
      (Set.Icc (0 : ℝ) 1) := by
    simpa [intervalDomainLift, Real.zero_rpow p.hγ.ne'] using (continuousOn_const :
      ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc (0 : ℝ) 1))
  have hA_energy :
      coeffL2Energy A ≤
        4 * ∫ x in (0 : ℝ)..1,
          (p.ν * intervalDomainLift w x ^ p.γ) ^ 2 := by
    have hbase :=
      ShenWork.IntervalResolverWeakBounds.sourceCoeff_diff_energy_le_integral_of_continuousOn
        (p := p) (u₁ := w) (u₂ := fun _ : intervalDomainPoint => 0) hgcont hzero_cont
    simpa [A, ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero,
      intervalDomainLift, Real.zero_rpow p.hγ.ne'] using hbase
  have hsource_sq_le :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (p.ν * intervalDomainLift w x ^ p.γ) ^ 2 ≤
          (p.ν * M ^ p.γ) ^ 2 := by
    intro x hx
    have hlift_abs : |intervalDomainLift w x| ≤ M := by
      simp only [intervalDomainLift, dif_pos hx]
      exact hball ⟨x, hx⟩
    have hpow_abs :
        |intervalDomainLift w x ^ p.γ| ≤ M ^ p.γ :=
      (Real.abs_rpow_le_abs_rpow (intervalDomainLift w x) p.γ).trans
        (Real.rpow_le_rpow (abs_nonneg _) hlift_abs p.hγ.le)
    have hB_nonneg : 0 ≤ p.ν * M ^ p.γ :=
      mul_nonneg p.hν.le (Real.rpow_nonneg hM_nonneg _)
    have hsrc_abs :
        |p.ν * intervalDomainLift w x ^ p.γ| ≤ p.ν * M ^ p.γ := by
      rw [abs_mul, abs_of_pos p.hν]
      exact mul_le_mul_of_nonneg_left hpow_abs p.hν.le
    rw [← sq_abs]
    nlinarith [abs_nonneg (p.ν * intervalDomainLift w x ^ p.γ), hsrc_abs,
      hB_nonneg, sq_nonneg (p.ν * M ^ p.γ - |p.ν * intervalDomainLift w x ^ p.γ|)]
  have hsource_sq_cont : ContinuousOn
      (fun x : ℝ => (p.ν * intervalDomainLift w x ^ p.γ) ^ 2)
      (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hgcont.pow 2
  have hIle :
      (∫ x in (0 : ℝ)..1, (p.ν * intervalDomainLift w x ^ p.γ) ^ 2)
        ≤ (p.ν * M ^ p.γ) ^ 2 := by
    have hcI : IntervalIntegrable
        (fun _ : ℝ => (p.ν * M ^ p.γ) ^ 2) volume 0 1 :=
      (continuous_const).intervalIntegrable 0 1
    have hmono := intervalIntegral.integral_mono_on (by norm_num)
      hsource_sq_cont.intervalIntegrable hcI hsource_sq_le
    have hconst :
        (∫ _x in (0 : ℝ)..1, (p.ν * M ^ p.γ) ^ 2 ∂volume)
          = (p.ν * M ^ p.γ) ^ 2 := by
      rw [intervalIntegral.integral_const, sub_zero, one_smul]
    rwa [hconst] at hmono
  have hA_l2_bound : coeffL2Norm A ≤ 2 * (p.ν * M ^ p.γ) := by
    have hB_nonneg : 0 ≤ p.ν * M ^ p.γ :=
      mul_nonneg p.hν.le (Real.rpow_nonneg hM_nonneg _)
    have henergy_bound :
        coeffL2Energy A ≤ 4 * (p.ν * M ^ p.γ) ^ 2 :=
      hA_energy.trans (mul_le_mul_of_nonneg_left hIle (by norm_num))
    rw [coeffL2Norm]
    calc
      Real.sqrt (coeffL2Energy A)
          ≤ Real.sqrt (4 * (p.ν * M ^ p.γ) ^ 2) :=
            Real.sqrt_le_sqrt henergy_bound
      _ = 2 * (p.ν * M ^ p.γ) := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← mul_pow,
              Real.sqrt_sq (mul_nonneg (by norm_num) hB_nonneg)]
  rw [hsum_eq]
  have hcoeff_nn : 0 ≤ coeffL2Norm A := Real.sqrt_nonneg _
  have hW_nn :
      0 ≤ Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) :=
    Real.sqrt_nonneg _
  calc
    |∑' k : ℕ, e k * m k|
        ≤ Real.sqrt (∑' k : ℕ, (e k) ^ 2) *
            Real.sqrt (∑' k : ℕ, (m k) ^ 2) := hCS
    _ ≤ coeffL2Norm A *
          Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) :=
        mul_le_mul hA_l2 hmW (Real.sqrt_nonneg _) hcoeff_nn
    _ ≤ (2 * (p.ν * M ^ p.γ)) *
          Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) :=
        mul_le_mul_of_nonneg_right hA_l2_bound hW_nn
    _ = Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * M ^ p.γ)) := by ring

private theorem resolverValueSeries_abs_le_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M) (y : ℝ) :
    |∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverCoeff p w k).re *
        Real.cos ((k : ℝ) * Real.pi * y)| ≤
      Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2)
        * (2 * (p.ν * M ^ p.γ)) := by
  classical
  have hUcont : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) :=
    lift_continuousOn_Icc_of_continuous hw_cont
  have hM_nonneg : 0 ≤ M := hM.le
  let A : ℕ → ℂ := fun k =>
    ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k -
      ShenWork.PDE.intervalNeumannResolverSourceCoeff p (fun _ => 0) k
  let e : ℕ → ℝ := fun k => (A k).re
  let m : ℕ → ℝ := fun k =>
    Real.cos ((k : ℝ) * Real.pi * y) /
      (p.μ + unitIntervalNeumannSpectrum.eigenvalue k)
  have hsrc :
      Summable fun k : ℕ =>
        ((ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k -
          ShenWork.PDE.intervalNeumannResolverSourceCoeff p (fun _ => 0) k).re) ^ 2 := by
    simpa [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      ShenWork.IntervalResolverWeakBounds.resolverSourceCoeff_re_sq_summable_of_continuousOn
        p hUcont
  have he_sq : Summable fun k : ℕ => (e k) ^ 2 := by
    simpa [e, A] using hsrc
  have hm_sq : Summable fun k : ℕ => (m k) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) ?_
      (ShenWork.PDE.intervalNeumannResolverWeight_sq_summable p)
    intro k
    have hcos : (Real.cos ((k : ℝ) * Real.pi * y)) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]
      exact Real.abs_cos_le_one _
    have hweq :
        (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2 =
          1 / (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) ^ 2 := by
      rw [ShenWork.PDE.intervalNeumannResolverWeight]
      field_simp
    rw [hweq]
    dsimp [m]
    rw [div_pow]
    gcongr
  have hterm : ∀ k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverCoeff p w k).re *
          Real.cos ((k : ℝ) * Real.pi * y) =
        e k * m k := by
    intro k
    have hden : p.μ + unitIntervalNeumannSpectrum.eigenvalue k ≠ 0 :=
      ne_of_gt (ShenWork.PDE.intervalNeumannResolver_denom_pos p k)
    dsimp [e, A, m]
    rw [ShenWork.IntervalResolverGradientBridge.resolverCoeff_re_eq p w k]
    simp only [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero]
    field_simp [hden]
    rw [Complex.zero_re]
    ring
  have hsum_eq :
      (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverCoeff p w k).re *
          Real.cos ((k : ℝ) * Real.pi * y)) =
        ∑' k : ℕ, e k * m k :=
    tsum_congr hterm
  have hCS :
      |∑' k : ℕ, e k * m k| ≤
        Real.sqrt (∑' k : ℕ, (e k) ^ 2) *
          Real.sqrt (∑' k : ℕ, (m k) ^ 2) :=
    real_abs_tsum_mul_le_sqrt_tsum_sq_mul_sqrt_tsum_sq he_sq hm_sq
  have hA_l2 :
      Real.sqrt (∑' k : ℕ, (e k) ^ 2) ≤ coeffL2Norm A := by
    rw [coeffL2Norm, coeffL2Energy]
    apply Real.sqrt_le_sqrt
    refine he_sq.tsum_le_tsum ?_
      (ShenWork.PDE.intervalNeumannResolverR_source_l2_summable p w (fun _ => 0) hsrc)
    intro k
    have : (e k) ^ 2 = (A k).re * (A k).re := by
      dsimp [e]
      ring
    rw [this]
    calc
      (A k).re * (A k).re ≤ Complex.normSq (A k) := Complex.re_sq_le_normSq _
      _ = ‖A k‖ ^ 2 := (Complex.sq_norm _).symm
  have hmW :
      Real.sqrt (∑' k : ℕ, (m k) ^ 2) ≤
        Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) := by
    apply Real.sqrt_le_sqrt
    refine hm_sq.tsum_le_tsum ?_
      (ShenWork.PDE.intervalNeumannResolverWeight_sq_summable p)
    intro k
    have hcos : (Real.cos ((k : ℝ) * Real.pi * y)) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]
      exact Real.abs_cos_le_one _
    have hweq :
        (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2 =
          1 / (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) ^ 2 := by
      rw [ShenWork.PDE.intervalNeumannResolverWeight]
      field_simp
    rw [hweq]
    dsimp [m]
    rw [div_pow]
    gcongr
  have hgcont : ContinuousOn
      (fun x : ℝ => p.ν * intervalDomainLift w x ^ p.γ) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.mul
      (hUcont.rpow_const (fun _ _ => Or.inr p.hγ.le))
  have hzero_cont : ContinuousOn
      (fun x : ℝ => p.ν * intervalDomainLift (fun _ : intervalDomainPoint => 0) x ^ p.γ)
      (Set.Icc (0 : ℝ) 1) := by
    simpa [intervalDomainLift, Real.zero_rpow p.hγ.ne'] using (continuousOn_const :
      ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc (0 : ℝ) 1))
  have hA_energy :
      coeffL2Energy A ≤
        4 * ∫ x in (0 : ℝ)..1,
          (p.ν * intervalDomainLift w x ^ p.γ) ^ 2 := by
    have hbase :=
      ShenWork.IntervalResolverWeakBounds.sourceCoeff_diff_energy_le_integral_of_continuousOn
        (p := p) (u₁ := w) (u₂ := fun _ : intervalDomainPoint => 0) hgcont hzero_cont
    simpa [A, ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero,
      intervalDomainLift, Real.zero_rpow p.hγ.ne'] using hbase
  have hsource_sq_le :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (p.ν * intervalDomainLift w x ^ p.γ) ^ 2 ≤
          (p.ν * M ^ p.γ) ^ 2 := by
    intro x hx
    have hlift_abs : |intervalDomainLift w x| ≤ M := by
      simp only [intervalDomainLift, dif_pos hx]
      exact hball ⟨x, hx⟩
    have hpow_abs :
        |intervalDomainLift w x ^ p.γ| ≤ M ^ p.γ :=
      (Real.abs_rpow_le_abs_rpow (intervalDomainLift w x) p.γ).trans
        (Real.rpow_le_rpow (abs_nonneg _) hlift_abs p.hγ.le)
    have hB_nonneg : 0 ≤ p.ν * M ^ p.γ :=
      mul_nonneg p.hν.le (Real.rpow_nonneg hM_nonneg _)
    have hsrc_abs :
        |p.ν * intervalDomainLift w x ^ p.γ| ≤ p.ν * M ^ p.γ := by
      rw [abs_mul, abs_of_pos p.hν]
      exact mul_le_mul_of_nonneg_left hpow_abs p.hν.le
    rw [← sq_abs]
    nlinarith [abs_nonneg (p.ν * intervalDomainLift w x ^ p.γ), hsrc_abs,
      hB_nonneg, sq_nonneg (p.ν * M ^ p.γ - |p.ν * intervalDomainLift w x ^ p.γ|)]
  have hsource_sq_cont : ContinuousOn
      (fun x : ℝ => (p.ν * intervalDomainLift w x ^ p.γ) ^ 2)
      (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hgcont.pow 2
  have hIle :
      (∫ x in (0 : ℝ)..1, (p.ν * intervalDomainLift w x ^ p.γ) ^ 2)
        ≤ (p.ν * M ^ p.γ) ^ 2 := by
    have hcI : IntervalIntegrable
        (fun _ : ℝ => (p.ν * M ^ p.γ) ^ 2) volume 0 1 :=
      (continuous_const).intervalIntegrable 0 1
    have hmono := intervalIntegral.integral_mono_on (by norm_num)
      hsource_sq_cont.intervalIntegrable hcI hsource_sq_le
    have hconst :
        (∫ _x in (0 : ℝ)..1, (p.ν * M ^ p.γ) ^ 2 ∂volume)
          = (p.ν * M ^ p.γ) ^ 2 := by
      rw [intervalIntegral.integral_const, sub_zero, one_smul]
    rwa [hconst] at hmono
  have hA_l2_bound : coeffL2Norm A ≤ 2 * (p.ν * M ^ p.γ) := by
    have hB_nonneg : 0 ≤ p.ν * M ^ p.γ :=
      mul_nonneg p.hν.le (Real.rpow_nonneg hM_nonneg _)
    have henergy_bound :
        coeffL2Energy A ≤ 4 * (p.ν * M ^ p.γ) ^ 2 :=
      hA_energy.trans (mul_le_mul_of_nonneg_left hIle (by norm_num))
    rw [coeffL2Norm]
    calc
      Real.sqrt (coeffL2Energy A)
          ≤ Real.sqrt (4 * (p.ν * M ^ p.γ) ^ 2) :=
            Real.sqrt_le_sqrt henergy_bound
      _ = 2 * (p.ν * M ^ p.γ) := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← mul_pow,
              Real.sqrt_sq (mul_nonneg (by norm_num) hB_nonneg)]
  rw [hsum_eq]
  have hcoeff_nn : 0 ≤ coeffL2Norm A := Real.sqrt_nonneg _
  have hW_nn :
      0 ≤ Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) :=
    Real.sqrt_nonneg _
  calc
    |∑' k : ℕ, e k * m k|
        ≤ Real.sqrt (∑' k : ℕ, (e k) ^ 2) *
            Real.sqrt (∑' k : ℕ, (m k) ^ 2) := hCS
    _ ≤ coeffL2Norm A *
          Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) :=
        mul_le_mul hA_l2 hmW (Real.sqrt_nonneg _) hcoeff_nn
    _ ≤ (2 * (p.ν * M ^ p.γ)) *
          Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) :=
        mul_le_mul_of_nonneg_right hA_l2_bound hW_nn
    _ = Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
          (2 * (p.ν * M ^ p.γ)) := by ring

/-- Signed ODE bridge for the resolver gradient.  The nonnegative bridge exists
in `IntervalResolverWeakLapBound`; the signed Picard iterates need the same
elliptic derivative identity with only the source value bounded by the `M`-ball. -/
private theorem resolverGradReal_hasDerivAt_signed_ellipticBound_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M)
    {y : ℝ} (hyIoo : y ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ src : ℝ,
      HasDerivAt (fun z : ℝ => resolverGradReal p w z)
        (p.μ * (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverCoeff p w k).re *
            Real.cos ((k : ℝ) * Real.pi * y)) - src) y
      ∧ |src| ≤ p.ν * M ^ p.γ := by
  refine ⟨ShenWork.IntervalResolverWeakBounds.resolverSignedSourceReal p w y, ?_, ?_⟩
  · have hUcont : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) :=
      lift_continuousOn_Icc_of_continuous hw_cont
    have hder :=
      ShenWork.IntervalResolverWeakBounds.resolverGradReal_hasDerivAt_signedLap_of_continuousOn
        (p := p) (u := w) hUcont hyIoo
    simpa [ShenWork.IntervalResolverWeakBounds.resolverValueSeriesReal,
      ShenWork.IntervalResolverWeakBounds.resolverSignedSourceReal,
      unitIntervalCosineMode] using hder
  · have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hyIoo
    have hlift_abs : |intervalDomainLift w y| ≤ M := by
      simpa [intervalDomainLift, hyIcc] using hball ⟨y, hyIcc⟩
    have hpow_abs :
        |intervalDomainLift w y ^ p.γ| ≤ |intervalDomainLift w y| ^ p.γ :=
      Real.abs_rpow_le_abs_rpow _ _
    have hpow_le : |intervalDomainLift w y| ^ p.γ ≤ M ^ p.γ :=
      Real.rpow_le_rpow (abs_nonneg _) hlift_abs p.hγ.le
    calc
      |ShenWork.IntervalResolverWeakBounds.resolverSignedSourceReal p w y|
          = |p.ν * intervalDomainLift w y ^ p.γ| := by
              rfl
      _ = p.ν * |intervalDomainLift w y ^ p.γ| := by
              rw [abs_mul, abs_of_pos p.hν]
      _ ≤ p.ν * (|intervalDomainLift w y| ^ p.γ) :=
              mul_le_mul_of_nonneg_left hpow_abs p.hν.le
      _ ≤ p.ν * M ^ p.γ :=
              mul_le_mul_of_nonneg_left hpow_le p.hν.le

private theorem resolverGrad_deriv_abs_le_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M)
    {y : ℝ} (hyIoo : y ∈ Set.Ioo (0 : ℝ) 1) :
    |deriv (fun z : ℝ => resolverGradReal p w z) y| ≤
      p.μ * (Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2)
          * (2 * (p.ν * M ^ p.γ)))
        + p.ν * M ^ p.γ := by
  classical
  let V : ℝ := ∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverCoeff p w k).re *
      Real.cos ((k : ℝ) * Real.pi * y)
  have hV :
      |V| ≤
        Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2)
          * (2 * (p.ν * M ^ p.γ)) := by
    simpa [V] using resolverValueSeries_abs_le_of_abs_ball p hM hw_cont hball y
  obtain ⟨src, hderiv, hsrc⟩ :=
    resolverGradReal_hasDerivAt_signed_ellipticBound_of_abs_ball
      p hM hw_cont hball hyIoo
  have hderiv_eq :
      deriv (fun z : ℝ => resolverGradReal p w z) y = p.μ * V - src := by
    simpa [V] using hderiv.deriv
  rw [hderiv_eq]
  calc
    |p.μ * V - src| ≤ |p.μ * V| + |src| := abs_sub _ _
    _ = p.μ * |V| + |src| := by
        rw [abs_mul, abs_of_pos p.hμ]
    _ ≤ p.μ * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2)
            * (2 * (p.ν * M ^ p.γ)))
          + p.ν * M ^ p.γ :=
        add_le_add (mul_le_mul_of_nonneg_left hV p.hμ.le) hsrc

private theorem intervalDomainLift_pos_mem_Ioo_of_differentiableAt
    {w : intervalDomainPoint → ℝ} {y : ℝ}
    (hpos : 0 < intervalDomainLift w y)
    (hdiff : DifferentiableAt ℝ (intervalDomainLift w) y) :
    y ∈ Set.Ioo (0 : ℝ) 1 := by
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
    by_contra hy
    have hzero : intervalDomainLift w y = 0 := by
      simp [intervalDomainLift, hy]
    linarith
  have hy0 : y ≠ 0 := by
    intro hy_eq
    subst y
    have hne : intervalDomainLift w 0 ≠ 0 := ne_of_gt hpos
    have hcont : ContinuousAt (intervalDomainLift w) 0 := hdiff.continuousAt
    have hlim : Filter.Tendsto (intervalDomainLift w)
        (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds (intervalDomainLift w 0)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hzero : Filter.Tendsto (intervalDomainLift w)
        (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds 0) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      refine Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Set.Iio 0, self_mem_nhdsWithin, fun z hz => ?_⟩
      have hmem : z ∉ Set.Icc (0 : ℝ) 1 :=
        fun hmem => absurd hmem.1 (not_le.mpr hz)
      simp [intervalDomainLift, hmem]
    exact hne (tendsto_nhds_unique hlim hzero)
  have hy1 : y ≠ 1 := by
    intro hy_eq
    subst y
    have hne : intervalDomainLift w 1 ≠ 0 := ne_of_gt hpos
    have hcont : ContinuousAt (intervalDomainLift w) 1 := hdiff.continuousAt
    have hlim : Filter.Tendsto (intervalDomainLift w)
        (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (intervalDomainLift w 1)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hzero : Filter.Tendsto (intervalDomainLift w)
        (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds 0) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      refine Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Set.Ioi 1, self_mem_nhdsWithin, fun z hz => ?_⟩
      have hmem : z ∉ Set.Icc (0 : ℝ) 1 :=
        fun hmem => absurd hmem.2 (not_le.mpr hz)
      simp [intervalDomainLift, hmem]
    exact hne (tendsto_nhds_unique hlim hzero)
  exact ⟨lt_of_le_of_ne hyIcc.1 (Ne.symm hy0), lt_of_le_of_ne hyIcc.2 hy1⟩

private theorem resolverR_lift_nonneg_and_flux_deriv_zero_of_lift_nonpos_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (_hM : 0 < M) (_hw_cont : Continuous w)
    (_hball : ∀ x : intervalDomainPoint, |w x| ≤ M) (y : ℝ) :
    0 ≤ intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y
      ∧ (intervalDomainLift w y ≤ 0 →
        deriv (truncatedChemFluxLifted p w) y = 0) := by
  sorry

private theorem resolverR_lift_nonneg_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M) (y : ℝ) :
    0 ≤ intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y :=
  (resolverR_lift_nonneg_and_flux_deriv_zero_of_lift_nonpos_of_abs_ball
    (p := p) (w := w) (M := M) hM hw_cont hball y).1

private theorem truncatedChemFluxLifted_deriv_zero_of_lift_nonpos_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M) {y : ℝ}
    (hy_nonpos : intervalDomainLift w y ≤ 0) :
    deriv (truncatedChemFluxLifted p w) y = 0 :=
  (resolverR_lift_nonneg_and_flux_deriv_zero_of_lift_nonpos_of_abs_ball
    (p := p) (w := w) (M := M) hM hw_cont hball y).2 hy_nonpos

private theorem truncatedChemFluxLifted_deriv_product_rule_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M) (y : ℝ)
    (hdiff : 0 < intervalDomainLift w y →
      DifferentiableAt ℝ (intervalDomainLift w) y) :
    ∃ dpos gp : ℝ,
      deriv (truncatedChemFluxLifted p w) y =
        dpos * resolverGradReal p w y *
            (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ (-p.β)
          + positivePart (intervalDomainLift w y) * gp *
            (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ (-p.β)
          - p.β * positivePart (intervalDomainLift w y)
              * (resolverGradReal p w y) ^ 2 *
            (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ (-p.β - 1)
      ∧ |dpos| ≤ |deriv (intervalDomainLift w) y|
      ∧ gp = deriv (fun z : ℝ => resolverGradReal p w z) y := by
  classical
  by_cases hpos : 0 < intervalDomainLift w y
  · let R : ℝ → ℝ :=
      fun z => intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) z
    let g : ℝ → ℝ := fun z => resolverGradReal p w z
    let a : ℝ → ℝ := fun z => positivePart (intervalDomainLift w z)
    let q : ℝ → ℝ := fun z => (1 + R z) ^ (-p.β)
    have hdw : DifferentiableAt ℝ (intervalDomainLift w) y := hdiff hpos
    have hflux_eq : truncatedChemFluxLifted p w =
        fun z => a z * g z * q z := by
      funext z
      have hR_nonneg : 0 ≤ R z := by
        simpa [R] using resolverR_lift_nonneg_of_abs_ball
          (p := p) (w := w) (M := M) hM hw_cont hball z
      have hbase_nonneg : 0 ≤ 1 + R z := by linarith
      unfold truncatedChemFluxLifted
      rw [div_eq_mul_inv, ← Real.rpow_neg hbase_nonneg]
    have hpos_ev : ∀ᶠ z in nhds y, 0 < intervalDomainLift w z :=
      hdw.continuousAt.tendsto.eventually (isOpen_Ioi.mem_nhds hpos)
    have ha_eq : a =ᶠ[nhds y] intervalDomainLift w := by
      filter_upwards [hpos_ev] with z hz
      exact positivePart_eq_self_of_nonneg (le_of_lt hz)
    have ha_has : HasDerivAt a (deriv (intervalDomainLift w) y) y :=
      (Filter.EventuallyEq.hasDerivAt_iff ha_eq).2 hdw.hasDerivAt
    have hyIoo : y ∈ Set.Ioo (0 : ℝ) 1 :=
      intervalDomainLift_pos_mem_Ioo_of_differentiableAt hpos hdw
    obtain ⟨src, hg_raw, _hsrc⟩ :=
      resolverGradReal_hasDerivAt_signed_ellipticBound_of_abs_ball
        (p := p) (w := w) (M := M) hM hw_cont hball hyIoo
    have hg_has : HasDerivAt g (deriv g y) y := by
      simpa [g, hg_raw.deriv] using hg_raw
    have hUcont : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) :=
      lift_continuousOn_Icc_of_continuous hw_cont
    have hR_has : HasDerivAt R (g y) y := by
      simpa [R, g] using
        ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverR_lift_hasDerivAt_resolverGradReal_of_continuousOn
          (p := p) (u := w) hUcont hyIoo
    have hbase_has : HasDerivAt (fun z : ℝ => 1 + R z) (g y) y :=
      hR_has.const_add 1
    have hR_nonneg_y : 0 ≤ R y := by
      simpa [R] using resolverR_lift_nonneg_of_abs_ball
        (p := p) (w := w) (M := M) hM hw_cont hball y
    have hbase_pos : 0 < 1 + R y := by linarith
    have hq_has :
        HasDerivAt q (g y * (-p.β) * (1 + R y) ^ (-p.β - 1)) y := by
      simpa [q, sub_eq_add_neg] using
        hbase_has.rpow_const (p := -p.β) (Or.inl (ne_of_gt hbase_pos))
    have hag_has : HasDerivAt (fun z : ℝ => a z * g z)
        (deriv (intervalDomainLift w) y * g y + a y * deriv g y) y := by
      simpa using ha_has.mul hg_has
    have hprod_has : HasDerivAt (fun z : ℝ => a z * g z * q z)
        ((deriv (intervalDomainLift w) y * g y + a y * deriv g y) * q y
          + (a y * g y) * (g y * (-p.β) * (1 + R y) ^ (-p.β - 1))) y := by
      simpa only [Pi.mul_apply] using hag_has.mul hq_has
    refine ⟨deriv (intervalDomainLift w) y, deriv g y, ?_, le_rfl, rfl⟩
    rw [hflux_eq, hprod_has.deriv]
    simp [a, g, q, R]
    ring
  · have hy_nonpos : intervalDomainLift w y ≤ 0 := le_of_not_gt hpos
    refine ⟨0, deriv (fun z : ℝ => resolverGradReal p w z) y, ?_, ?_, rfl⟩
    · have hflux_zero :
          deriv (truncatedChemFluxLifted p w) y = 0 :=
        truncatedChemFluxLifted_deriv_zero_of_lift_nonpos_of_abs_ball
          (p := p) (w := w) (M := M) hM hw_cont hball hy_nonpos
      have hpp_zero : positivePart (intervalDomainLift w y) = 0 :=
        positivePart_eq_zero_of_nonpos hy_nonpos
      simp [hflux_zero, hpp_zero]
    · simp

private theorem truncatedChemFluxLifted_deriv_terms_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M) (y : ℝ)
    (hdiff : 0 < intervalDomainLift w y →
      DifferentiableAt ℝ (intervalDomainLift w) y) :
    ∃ dpos gp q qDen : ℝ,
      deriv (truncatedChemFluxLifted p w) y =
        dpos * resolverGradReal p w y * q
          + positivePart (intervalDomainLift w y) * gp * q
          - p.β * positivePart (intervalDomainLift w y)
              * (resolverGradReal p w y) ^ 2 * qDen
      ∧ |dpos| ≤ |deriv (intervalDomainLift w) y|
      ∧ |resolverGradReal p w y| ≤
          Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
            * (2 * (p.ν * M ^ p.γ))
      ∧ |gp| ≤
          p.μ * (Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2)
              * (2 * (p.ν * M ^ p.γ)))
            + p.ν * M ^ p.γ
      ∧ |q| ≤ 1
      ∧ |qDen| ≤ 1 := by
  classical
  let q : ℝ :=
    (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ (-p.β)
  let qDen : ℝ :=
    (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ (-p.β - 1)
  have hgrad_bound :
      |resolverGradReal p w y| ≤
        Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
          * (2 * (p.ν * M ^ p.γ)) :=
    resolverGrad_abs_le_of_abs_ball
      (p := p) (w := w) (M := M) hM hw_cont hball y
  have hR_nonneg :
      0 ≤ intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y :=
    resolverR_lift_nonneg_of_abs_ball
      (p := p) (w := w) (M := M) hM hw_cont hball y
  have hq_abs : |q| ≤ 1 := by
    have hbase : 1 ≤
        1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y := by
      linarith
    have hq_nonneg : 0 ≤ q := by
      exact Real.rpow_nonneg (by linarith : 0 ≤
        1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y) _
    have hq_le : q ≤ 1 := by
      dsimp [q]
      exact Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith [p.hβ])
    rw [abs_of_nonneg hq_nonneg]
    exact hq_le
  have hqDen_abs : |qDen| ≤ 1 := by
    have hbase : 1 ≤
        1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y := by
      linarith
    have hqDen_nonneg : 0 ≤ qDen := by
      exact Real.rpow_nonneg (by linarith : 0 ≤
        1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y) _
    have hqDen_le : qDen ≤ 1 := by
      dsimp [qDen]
      exact Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith [p.hβ])
    rw [abs_of_nonneg hqDen_nonneg]
    exact hqDen_le
  by_cases hpos : 0 < intervalDomainLift w y
  · obtain ⟨dpos, gp, hderiv, hdpos, hgp_eq⟩ :=
      truncatedChemFluxLifted_deriv_product_rule_of_abs_ball
        (p := p) (w := w) (M := M) hM hw_cont hball y hdiff
    refine ⟨dpos, gp, q, qDen, ?_, hdpos, hgrad_bound, ?_, hq_abs, hqDen_abs⟩
    · simpa [q, qDen] using hderiv
    · rw [hgp_eq]
      have hyIoo : y ∈ Set.Ioo (0 : ℝ) 1 :=
        intervalDomainLift_pos_mem_Ioo_of_differentiableAt hpos (hdiff hpos)
      exact resolverGrad_deriv_abs_le_of_abs_ball
        (p := p) (w := w) (M := M) hM hw_cont hball hyIoo
  · have hy_nonpos : intervalDomainLift w y ≤ 0 := le_of_not_gt hpos
    have hpp_zero : positivePart (intervalDomainLift w y) = 0 :=
      positivePart_eq_zero_of_nonpos hy_nonpos
    have hflux_zero :
        deriv (truncatedChemFluxLifted p w) y = 0 :=
      truncatedChemFluxLifted_deriv_zero_of_lift_nonpos_of_abs_ball
        (p := p) (w := w) (M := M) hM hw_cont hball hy_nonpos
    have hMpow_nonneg : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM.le _
    have hsrc_nonneg : 0 ≤ p.ν * M ^ p.γ :=
      mul_nonneg p.hν.le hMpow_nonneg
    have hvalue_nonneg :
        0 ≤ Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2)
          * (2 * (p.ν * M ^ p.γ)) :=
      mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num) hsrc_nonneg)
    have hgp_bound :
        |(0 : ℝ)| ≤
          p.μ * (Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2)
              * (2 * (p.ν * M ^ p.γ)))
            + p.ν * M ^ p.γ :=
      by
        rw [abs_zero]
        exact add_nonneg (mul_nonneg p.hμ.le hvalue_nonneg) hsrc_nonneg
    refine ⟨0, 0, q, qDen, ?_, ?_, hgrad_bound, hgp_bound, hq_abs, hqDen_abs⟩
    · simp [hflux_zero, hpp_zero]
    · simp

private theorem truncatedChemFluxLifted_continuousOn_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M) :
    ContinuousOn (truncatedChemFluxLifted p w) (Set.Icc (0 : ℝ) 1) := by
  classical
  have hUcont : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) :=
    lift_continuousOn_Icc_of_continuous hw_cont
  have hpos_cont : Continuous fun r : ℝ => positivePart r := by
    simpa [positivePart] using (continuous_id.max continuous_const)
  have hpp_cont :
      ContinuousOn (fun y : ℝ => positivePart (intervalDomainLift w y))
        (Set.Icc (0 : ℝ) 1) :=
    hpos_cont.continuousOn.comp hUcont (fun _ _ => Set.mem_univ _)
  have hgrad_cont :
      ContinuousOn (fun y : ℝ => resolverGradReal p w y)
        (Set.Icc (0 : ℝ) 1) :=
    (resolverGradReal_continuous_of_continuousOn p hUcont).continuousOn
  have hR_cont :
      ContinuousOn
        (intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w))
        (Set.Icc (0 : ℝ) 1) := by
    have hseries_cont : Continuous (fun y : ℝ =>
        ∑' k : ℕ, (ShenWork.PDE.intervalNeumannResolverCoeff p w k).re *
          unitIntervalCosineMode k y) :=
      ShenWork.IntervalDuhamelIntegrability.resolverValueReal_continuous_of_continuousOn
        p hUcont
    refine hseries_cont.continuousOn.congr ?_
    intro y hy
    simp [intervalDomainLift, hy, ShenWork.PDE.intervalNeumannResolverR]
  have hbase_cont :
      ContinuousOn
        (fun y : ℝ =>
          1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y)
        (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.add hR_cont
  have hden_cont :
      ContinuousOn
        (fun y : ℝ =>
          (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y) ^
            p.β)
        (Set.Icc (0 : ℝ) 1) :=
    hbase_cont.rpow_const (fun _ _ => Or.inr p.hβ)
  have hden_ne :
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y) ^
          p.β ≠ 0 := by
    intro y _hy
    have hR_nonneg :
        0 ≤ intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y :=
      resolverR_lift_nonneg_of_abs_ball
        (p := p) (w := w) (M := M) hM hw_cont hball y
    exact ne_of_gt (Real.rpow_pos_of_pos (by linarith) p.β)
  simpa [truncatedChemFluxLifted] using
    (hpp_cont.mul hgrad_cont).div hden_cont hden_ne

/-! ## Level 0: Positive-time spatial regularity (analytic black box)

The Picard limit is spatially Lipschitz at positive time.  This is the
analytic frontier: heat semigroup smoothing → Volterra gradient contraction
on the iterates → uniform Lipschitz constant → limit Lipschitz.

The downstream coefficient arguments (IBP, source bounds, Sobolev ladder)
consume ONLY this Lipschitz fact; they never touch the Volterra internals. -/

/-- At positive time, the lifted Picard-limit slice is Lipschitz on [0,1].
This is the key regularity black box that breaks the circularity between
source bounds and gradient bounds.  The proof is: iterate-level heat
smoothing gives each u_n Lipschitz at positive time, with constants uniform
in n (Volterra contraction), so the Picard limit inherits Lipschitz. -/
theorem truncatedPicardLimit_lipschitzOn_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T)
    (hcontr_grad : truncWindowB
      (Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
          * (2 * (p.ν * DT.M ^ p.γ)))
      p.χ₀ (t / 4) t < 1) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |intervalDomainLift
        ((truncatedConjugatePicardLimit p u₀ DT.T) t) x -
       intervalDomainLift
        ((truncatedConjugatePicardLimit p u₀ DT.T) t) y| ≤ G * |x - y| := by
  -- Step 1a: Uniform iterate gradient bound from gradient window contraction
  have hiter_grad : ∃ G : ℝ, 0 ≤ G ∧ ∀ n : ℕ,
      ∀ s, t / 2 ≤ s → s ≤ t →
        (∀ x : ℝ,
          |deriv (intervalDomainLift (truncatedConjugatePicardIter p u₀ n s)) x|
            ≤ G) ∧
          ∀ x ∈ Set.Ioo (0 : ℝ) 1,
            DifferentiableAt ℝ
              (intervalDomainLift (truncatedConjugatePicardIter p u₀ n s)) x := by
    let U : ℕ → ℝ → intervalDomainPoint → ℝ :=
      fun n s => truncatedConjugatePicardIter p u₀ n s
    -- Post-IBP source: logistic - χ₀ * flux' (flux DERIVATIVE, not raw flux).
    -- After IBP (intervalConjugateKernelOperator_eq_semigroup_deriv), the
    -- B-form iterate ∫B_N(t-s)(Q_n)ds becomes ∫S(t-s)(Q'_n)ds, so the
    -- combined source for the standard Duhamel gradient estimate is L_n - χ₀·Q'_n.
    let Src : ℕ → ℝ → ℝ → ℝ :=
      fun n s y =>
        truncatedLogisticLifted p (U n s) y
          - p.χ₀ * deriv (truncatedChemFluxLifted p (U n s)) y
    let a : ℝ := t / 4
    let lo : ℝ := t / 2
    let hi : ℝ := t
    let Mw : ℝ := DT.M
    let A_L : ℝ := DT.M * (p.a + p.b * DT.M ^ p.α)
    -- Resolver gradient envelope Γ_M = √(∑ gradWeight²) · 2νM^γ
    let Γ_M : ℝ := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
        * (2 * (p.ν * DT.M ^ p.γ))
    -- Resolver value envelope V_M = √(∑ resolverWeight²) · 2νM^γ
    let V_M : ℝ := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2)
        * (2 * (p.ν * DT.M ^ p.γ))
    -- Resolver second derivative bound H_M from elliptic equation R'' = μR - ρ(u):
    -- |R''| ≤ μ|R| + |ρ| ≤ μ·V_M + ν·M^γ
    let H_M : ℝ := p.μ * V_M + p.ν * DT.M ^ p.γ
    -- After-IBP flux derivative bound:
    -- |Q'| ≤ G · Γ_M + M · H_M + β · M · Γ_M²  (product rule)
    -- So A_F = M · H_M + β · M · Γ_M², B_F = Γ_M
    let A_F : ℝ := DT.M * H_M + p.β * DT.M * Γ_M ^ 2
    let B_F : ℝ := Γ_M
    -- Contraction coefficient: Cg · 2√(hi-a) · |χ₀| · Γ_M
    -- For the fixed point to exist, need truncWindowB < 1.
    -- Use the fixed-point formula Gw = truncWindowA / (1 - truncWindowB).
    have hΓ_M_nn : 0 ≤ Γ_M := mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by positivity) (mul_nonneg (le_of_lt p.hν)
        (Real.rpow_nonneg (le_of_lt DT.hM) _)))
    have hAL_nn : 0 ≤ A_L := mul_nonneg (le_of_lt DT.hM) (add_nonneg p.ha
      (mul_nonneg p.hb (Real.rpow_nonneg (le_of_lt DT.hM) _)))
    have hAF_nn : 0 ≤ A_F := by
      dsimp only [A_F]
      apply add_nonneg
      · exact mul_nonneg (le_of_lt DT.hM) (add_nonneg (mul_nonneg (le_of_lt p.hμ)
          (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by positivity)
            (mul_nonneg (le_of_lt p.hν) (Real.rpow_nonneg (le_of_lt DT.hM) _)))))
          (mul_nonneg (le_of_lt p.hν) (Real.rpow_nonneg (le_of_lt DT.hM) _)))
      · exact mul_nonneg (mul_nonneg p.hβ (le_of_lt DT.hM)) (sq_nonneg _)
    have hBcontr : truncWindowB B_F p.χ₀ a hi < 1 := hcontr_grad
    let Gw : ℝ := truncWindowFixedG Mw A_L A_F B_F p.χ₀ a lo hi
    have hGw_nn : 0 ≤ Gw := by
      dsimp only [Gw]
      simp only [truncWindowFixedG, truncWindowA]
      apply div_nonneg
      · apply add_nonneg
        · exact mul_nonneg (div_nonneg ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
            (Real.sqrt_nonneg _)) (le_of_lt DT.hM)
        · exact mul_nonneg (mul_nonneg ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
            (mul_nonneg (by positivity) (Real.sqrt_nonneg _)))
            (add_nonneg hAL_nn (mul_nonneg (abs_nonneg _) hAF_nn))
      · linarith
    have W : TruncatedGradientWindowWiring p U Src Mw A_L A_F B_F a lo hi Gw := by
      exact
        { hM_nonneg := le_of_lt DT.hM
          hAL_nonneg := hAL_nn
          hAF_nonneg := hAF_nn
          hBF_nonneg := hΓ_M_nn
          hG_nonneg := hGw_nn
          ha_lt_lo := by dsimp [a, lo]; linarith
          hlo_le_hi := by dsimp [lo, hi]; linarith
          hclosed := by
            dsimp only [Gw]
            exact affine_fixed_closes hBcontr
          hleft := by
            have hM : 0 ≤ Mw := le_of_lt DT.hM
            have ha : 0 < a := by dsimp [a]; linarith
            have hPaG : truncLeftProfile Mw A_L A_F B_F p.χ₀ lo a ≤ Gw := by
              dsimp only [Gw]
              exact truncLeftProfile_le_Gw hM hAL_nn hAF_nn hΓ_M_nn ha
                (by dsimp [lo, a]; ring) (by dsimp [hi, a]; ring) hBcontr
            have hleftContr : truncLeftB B_F p.χ₀ lo < 1 := by
              have hsqrt_le : Real.sqrt lo ≤ Real.sqrt (hi - a) :=
                Real.sqrt_le_sqrt (by dsimp [lo, hi, a]; linarith)
              have htwo_sqrt_le :
                  2 * Real.sqrt lo ≤ 2 * Real.sqrt (hi - a) :=
                mul_le_mul_of_nonneg_left hsqrt_le (by norm_num)
              have hK_nonneg :
                  0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant :=
                ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
              have hchiBF_nonneg : 0 ≤ |p.χ₀| * B_F :=
                mul_nonneg (abs_nonneg p.χ₀) hΓ_M_nn
              have hb_core :
                  ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
                      * (2 * Real.sqrt lo)
                    ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
                      * (2 * Real.sqrt (hi - a)) :=
                mul_le_mul_of_nonneg_left htwo_sqrt_le hK_nonneg
              have hb_le : truncLeftB B_F p.χ₀ lo ≤ truncWindowB B_F p.χ₀ a hi := by
                rw [truncLeftB, truncWindowB, truncLeftBeta]
                calc
                  ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
                        * (2 * Real.sqrt lo) * (|p.χ₀| * B_F)
                      ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
                        * (2 * Real.sqrt (hi - a)) * (|p.χ₀| * B_F) :=
                        mul_le_mul_of_nonneg_right hb_core hchiBF_nonneg
                  _ = ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
                        * (2 * Real.sqrt (hi - a)) * |p.χ₀| * B_F := by ring
              exact lt_of_le_of_lt hb_le hBcontr
            have base : IterGradLeftProfile U Mw A_L A_F B_F p.χ₀ lo 0 := by
              simpa [Mw] using
                truncatedConjugatePicardIter_zero_left_profile
                  (p := p) (u₀ := u₀) DT U (by intro n s; rfl)
                  hAL_nn hAF_nn hΓ_M_nn
                  (by dsimp [lo]; linarith) hleftContr
            have source : ∀ n, IterGradLeftProfile U Mw A_L A_F B_F p.χ₀ lo n →
                ∀ s, 0 < s → s ≤ lo → ∀ y,
                  |Src n s y| ≤ truncLeftSourceConst A_L A_F p.χ₀ +
                    truncLeftBeta B_F p.χ₀ * truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s := by
              intro n hprofile s hs_pos hs_lo y
              have hball_cont := truncatedConjugatePicardIter_ball p u₀
                DT.hbase_ball DT.hbase_cont DT.hmapsTo DT.hcont_preserved
                DT.hbase_meas DT.hmeas_preserved n
              have hs_T : s ≤ DT.T := by
                have hlo_t : lo ≤ t := by dsimp [lo]; linarith
                exact hs_lo.trans (hlo_t.trans htT)
              have hball : ∀ x, |U n s x| ≤ DT.M := hball_cont.1 s hs_pos hs_T
              have hK_nonneg :
                  0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant :=
                ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
              have hprofile_nonneg :
                  0 ≤ truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s := by
                unfold truncLeftProfile truncLeftSingularC
                exact add_nonneg
                  (div_nonneg (mul_nonneg hK_nonneg hM) (Real.sqrt_nonneg _))
                  (truncLeftD_nonneg hM hAL_nn hAF_nn hΓ_M_nn
                    (by dsimp [lo]; linarith) hleftContr)
              dsimp only [Src]
              have hlog :
                  |truncatedLogisticLifted p (U n s) y| ≤ A_L := by
                have hlift_bound : |intervalDomainLift (U n s) y| ≤ DT.M := by
                  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
                  · simp only [intervalDomainLift, dif_pos hy]
                    exact hball ⟨y, hy⟩
                  · simp only [intervalDomainLift, dif_neg hy, abs_zero]
                    exact le_of_lt DT.hM
                show |truncatedLogisticLocal p (intervalDomainLift (U n s) y)| ≤ _
                exact truncatedLogisticLocal_abs_le_of_abs_le' p DT.hM hlift_bound
              have hflux :
                  |deriv (truncatedChemFluxLifted p (U n s)) y| ≤
                    A_F + B_F *
                      truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s := by
                by_cases hyIoo : y ∈ Set.Ioo (0 : ℝ) 1
                · dsimp only [A_F, B_F]
                  have hflux_terms :
                      ∃ dpos gp q qDen : ℝ,
                        deriv (truncatedChemFluxLifted p (U n s)) y =
                          dpos * resolverGradReal p (U n s) y * q
                            + positivePart (intervalDomainLift (U n s) y) * gp * q
                            - p.β * positivePart (intervalDomainLift (U n s) y)
                                * (resolverGradReal p (U n s) y) ^ 2 * qDen
                        ∧ |dpos| ≤ |deriv (intervalDomainLift (U n s)) y|
                        ∧ |resolverGradReal p (U n s) y| ≤ Γ_M
                        ∧ |gp| ≤ H_M
                        ∧ |q| ≤ 1
                        ∧ |qDen| ≤ 1 := by
                    have hdiff_pos :
                        0 < intervalDomainLift (U n s) y →
                          DifferentiableAt ℝ (intervalDomainLift (U n s)) y := by
                      intro _hy_pos
                      exact (hprofile s hs_pos hs_lo).2 y hyIoo
                    simpa [Γ_M, H_M, V_M] using
                      truncatedChemFluxLifted_deriv_terms_of_abs_ball
                        (p := p) (w := U n s) (M := DT.M) DT.hM
                        (hball_cont.2 s hs_pos hs_T) hball y hdiff_pos
                  rcases hflux_terms with
                    ⟨dpos, gp, q, qDen, hderiv, hdpos, hgradR, hgp, hq, hqDen⟩
                  exact truncatedChemFluxLifted_deriv_abs_le_of_ball_grad
                    (p := p) (w := U n s) (M := DT.M) (Γ := Γ_M)
                    (H := H_M)
                    (G := truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s)
                    DT.hM hball (hprofile s hs_pos hs_lo).1 y
                    hderiv hdpos hgradR hgp hq hqDen
                · have hflux_zero :
                      deriv (truncatedChemFluxLifted p (U n s)) y = 0 :=
                    truncatedChemFluxLifted_deriv_eq_zero_off_Ioo
                      (p := p) (w := U n s) hyIoo
                  rw [hflux_zero, abs_zero]
                  exact add_nonneg hAF_nn (mul_nonneg hΓ_M_nn hprofile_nonneg)
              calc
                |truncatedLogisticLifted p (U n s) y
                    - p.χ₀ * deriv (truncatedChemFluxLifted p (U n s)) y|
                    ≤ |truncatedLogisticLifted p (U n s) y|
                      + |p.χ₀ * deriv (truncatedChemFluxLifted p (U n s)) y| := by
                      simpa using
                        (abs_sub_le (truncatedLogisticLifted p (U n s) y) 0
                          (p.χ₀ * deriv (truncatedChemFluxLifted p (U n s)) y))
                _ = |truncatedLogisticLifted p (U n s) y|
                      + |p.χ₀| * |deriv (truncatedChemFluxLifted p (U n s)) y| := by
                    rw [abs_mul]
                _ ≤ A_L + |p.χ₀| *
                      (A_F + B_F
                        * truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s) := by
                    exact add_le_add hlog
                      (mul_le_mul_of_nonneg_left hflux (abs_nonneg p.χ₀))
                _ = truncLeftSourceConst A_L A_F p.χ₀
                      + truncLeftBeta B_F p.χ₀
                        * truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s := by
                    simp [truncLeftSourceConst, truncLeftBeta]
                    ring
            have kernel : ∀ n, (∀ s, 0 < s → s ≤ lo → ∀ y,
                |Src n s y| ≤ truncLeftSourceConst A_L A_F p.χ₀ +
                  truncLeftBeta B_F p.χ₀ * truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s) →
                IterGradLeftProfile U Mw A_L A_F B_F p.χ₀ lo (n + 1) := by
              sorry
            exact IterGradOnWindow.of_left_profile hM ha
              (truncLeftProfile_all_of_wiring ⟨base, source, kernel⟩) hPaG
          hbase := by
            -- U 0 t' = S(t')(lift u₀). Use restart: S(t') = S(t'-a)(S(a)(u₀))
            -- where |S(a)(u₀)| ≤ M from hbase_ball at a = t/4 > 0.
            -- Then gradient of S(t'-a) applied to M-bounded input
            -- ≤ Cg / √(t'-a) * M ≤ Cg / √(lo-a) * M ≤ Gw.
            dsimp only [Gw, Mw]
            exact truncatedConjugatePicardIter_zero_window_gradient
              (p := p) (u₀ := u₀) DT U (by intro n s; rfl)
              hAL_nn hAF_nn hΓ_M_nn
              (by dsimp [a]; linarith)
              (by dsimp [a, lo]; linarith)
              (by dsimp [lo, hi]; linarith)
              htT hBcontr
          hsource_of_grad := by
            intro n hgrad s ha_s hs_hi y
            have hball_cont := truncatedConjugatePicardIter_ball p u₀
              DT.hbase_ball DT.hbase_cont DT.hmapsTo DT.hcont_preserved
              DT.hbase_meas DT.hmeas_preserved n
            have ha_pos : (0 : ℝ) < t / 4 := by linarith
            have hs_pos : 0 < s := lt_of_lt_of_le ha_pos ha_s
            have hs_T : s ≤ DT.T := le_trans hs_hi htT
            have hball : ∀ x, |U n s x| ≤ DT.M := hball_cont.1 s hs_pos hs_T
            apply abs_logistic_sub_chi_flux_le
            · -- |logistic| ≤ A_L (from ball bound + truncatedLogisticLocal_abs_le)
              have hlift_bound : |intervalDomainLift (U n s) y| ≤ DT.M := by
                by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
                · simp only [intervalDomainLift, dif_pos hy]
                  exact hball ⟨y, hy⟩
                · simp only [intervalDomainLift, dif_neg hy, abs_zero]
                  exact le_of_lt DT.hM
              show |truncatedLogisticLifted p (U n s) y| ≤ A_L
              show |truncatedLogisticLocal p (intervalDomainLift (U n s) y)| ≤ _
              exact truncatedLogisticLocal_abs_le_of_abs_le' p DT.hM hlift_bound
            · by_cases hyIoo : y ∈ Set.Ioo (0 : ℝ) 1
              · dsimp only [A_F, B_F]
                have hflux_terms :
                    ∃ dpos gp q qDen : ℝ,
                      deriv (truncatedChemFluxLifted p (U n s)) y =
                        dpos * resolverGradReal p (U n s) y * q
                          + positivePart (intervalDomainLift (U n s) y) * gp * q
                          - p.β * positivePart (intervalDomainLift (U n s) y)
                              * (resolverGradReal p (U n s) y) ^ 2 * qDen
                      ∧ |dpos| ≤ |deriv (intervalDomainLift (U n s)) y|
                      ∧ |resolverGradReal p (U n s) y| ≤ Γ_M
                      ∧ |gp| ≤ H_M
                      ∧ |q| ≤ 1
                      ∧ |qDen| ≤ 1 := by
                  have hdiff_pos :
                      0 < intervalDomainLift (U n s) y →
                        DifferentiableAt ℝ (intervalDomainLift (U n s)) y :=
                    fun _ => (hgrad s ha_s hs_hi).2 y hyIoo
                  simpa [Γ_M, H_M, V_M] using
                    truncatedChemFluxLifted_deriv_terms_of_abs_ball
                      (p := p) (w := U n s) (M := DT.M) DT.hM
                      (hball_cont.2 s hs_pos hs_T) hball y hdiff_pos
                rcases hflux_terms with
                  ⟨dpos, gp, q, qDen, hderiv, hdpos, hgradR, hgp, hq, hqDen⟩
                exact truncatedChemFluxLifted_deriv_abs_le_of_ball_grad
                  (p := p) (w := U n s) (M := DT.M) (Γ := Γ_M)
                  (H := H_M) (G := Gw) DT.hM hball
                  (hgrad s ha_s hs_hi).1 y hderiv hdpos hgradR hgp hq hqDen
              · rw [truncatedChemFluxLifted_deriv_eq_zero_off_Ioo (p := p) (w := U n s) hyIoo,
                    abs_zero]
                exact add_nonneg hAF_nn (mul_nonneg hΓ_M_nn hGw_nn)
          hkernel_step := by
            -- After IBP, the B-form iterate becomes standard Duhamel:
            -- ∫₀ᵗ S(t-s)(Src_n(s)) ds where Src = logistic - χ₀·flux'.
            -- The gradient bound follows from gradDuhamel_shifted_sup_bound.
            dsimp only [Mw]
            exact truncatedConjugatePicardIter_succ_window_gradient
              (p := p) (u₀ := u₀) DT U (by intro n s; rfl) Src
              (by intro n s y; rfl)
              hAL_nn hAF_nn hΓ_M_nn hGw_nn
              (by dsimp [a]; linarith)
              (by dsimp [a, lo]; linarith)
              (by dsimp [lo, hi]; linarith)
              htT }
    exact ⟨Gw, hGw_nn, fun n s hslo hshi =>
      truncatedGradientWindow_all W n s hslo hshi⟩
  -- Step 1b: MVT — uniform gradient ≤ G → uniform Lipschitz ≤ G on [0,1]
  have hiter_lip : ∃ G : ℝ, 0 ≤ G ∧ ∀ n : ℕ,
      ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
        |intervalDomainLift (truncatedConjugatePicardIter p u₀ n t) x -
         intervalDomainLift (truncatedConjugatePicardIter p u₀ n t) y|
          ≤ G * |x - y| := by
    obtain ⟨G, hG_nn, hgrad⟩ := hiter_grad
    refine ⟨G, hG_nn, fun n x hx y hy => ?_⟩
    have ht_half : t / 2 ≤ t := half_le_self ht.le
    have hgt := hgrad n t ht_half le_rfl
    -- MVT: Lipschitz on Ioo 0 1 → extend to Icc 0 1 via LipschitzOnWith.closure
    set f := intervalDomainLift (truncatedConjugatePicardIter p u₀ n t) with hf_def
    -- DifferentiableAt on interior (from semigroup C² smoothing)
    have hda : ∀ z ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ f z := by
      intro z hz
      simpa [hf_def] using hgt.2 z hz
    -- Lipschitz on Ioo from MVT (Convex.lipschitzOnWith)
    have hlip_open : LipschitzOnWith ⟨G, hG_nn⟩ f (Set.Ioo (0 : ℝ) 1) :=
      Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Ioo (0 : ℝ) 1)
        (fun z hz => (hda z hz).hasDerivAt.hasDerivWithinAt)
        (fun z _ => by exact_mod_cast (hgt.1 z))
    -- ContinuousOn on Icc (from lift_continuousOn_Icc + Picard ball bound)
    have hcont_n : Continuous (truncatedConjugatePicardIter p u₀ n t) :=
      (truncatedConjugatePicardIter_ball p u₀ DT.hbase_ball DT.hbase_cont
        DT.hmapsTo DT.hcont_preserved DT.hbase_meas DT.hmeas_preserved n).2
        t ht htT
    have hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
      ShenWork.EWA.lift_continuousOn_Icc hcont_n
    -- Extend Lipschitz from Ioo to Icc = closure(Ioo)
    have hlip_closed : LipschitzOnWith ⟨G, hG_nn⟩ f (Set.Icc (0 : ℝ) 1) := by
      rw [← closure_Ioo (zero_ne_one' ℝ)]
      exact hlip_open.closure (by rwa [closure_Ioo (zero_ne_one' ℝ)])
    -- Convert LipschitzOnWith to the desired pointwise bound
    have hdist := hlip_closed.dist_le_mul _ hx _ hy
    rwa [Real.dist_eq, Real.dist_eq, NNReal.coe_mk] at hdist
  obtain ⟨G, hG_nn, hiter⟩ := hiter_lip
  refine ⟨G, hG_nn, fun x hx y hy => ?_⟩
  -- Step 2: Derive pointwise convergence from DT's geometric bound
  have hball_cont := fun n =>
    truncatedConjugatePicardIter_ball p u₀ DT.hbase_ball DT.hbase_cont
      DT.hmapsTo DT.hcont_preserved DT.hbase_meas DT.hmeas_preserved n
  have hball := fun n => (hball_cont n).1
  have hcont_iterates := fun n => (hball_cont n).2
  have hmeas_iterates : ∀ n,
      ShenWork.IntervalMildPicard.HasJointMeasurability
        (truncatedConjugatePicardIter p u₀ n) := by
    intro n
    induction n with
    | zero => exact DT.hbase_meas
    | succ n ih => exact DT.hmeas_preserved _ ih
  have hgeom := truncatedConjugatePicardIter_geometric p u₀ DT.hK_nn hball
    hcont_iterates hmeas_iterates DT.hcontr DT.hC₀ DT.hbase_diff
  have hconv := truncatedConjugatePicardIter_pointwise_convergent
    p u₀ DT.hK DT.hK_nn DT.hC₀ (fun n => hgeom n) t ht htT
  -- Step 3: Pointwise tendsto of lifted iterates at x and y
  have hlim_x : Filter.Tendsto
      (fun n => intervalDomainLift (truncatedConjugatePicardIter p u₀ n t) x)
      Filter.atTop (nhds (intervalDomainLift
        ((truncatedConjugatePicardLimit p u₀ DT.T) t) x)) := by
    unfold intervalDomainLift truncatedConjugatePicardLimit
    simp only [dif_pos hx, ht, htT, and_self, ite_true]
    exact tendsto_nhds_limUnder (hconv ⟨x, hx⟩)
  have hlim_y : Filter.Tendsto
      (fun n => intervalDomainLift (truncatedConjugatePicardIter p u₀ n t) y)
      Filter.atTop (nhds (intervalDomainLift
        ((truncatedConjugatePicardLimit p u₀ DT.T) t) y)) := by
    unfold intervalDomainLift truncatedConjugatePicardLimit
    simp only [dif_pos hy, ht, htT, and_self, ite_true]
    exact tendsto_nhds_limUnder (hconv ⟨y, hy⟩)
  -- Step 4: Limit passage via le_of_tendsto
  have hlim_diff : Filter.Tendsto
      (fun n => |intervalDomainLift (truncatedConjugatePicardIter p u₀ n t) x -
                 intervalDomainLift (truncatedConjugatePicardIter p u₀ n t) y|)
      Filter.atTop (nhds (|intervalDomainLift
        ((truncatedConjugatePicardLimit p u₀ DT.T) t) x -
       intervalDomainLift
        ((truncatedConjugatePicardLimit p u₀ DT.T) t) y|)) :=
    (hlim_x.sub hlim_y).abs
  exact le_of_tendsto hlim_diff (Filter.Eventually.of_forall (fun n => hiter n x hx y hy))

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
  field_simp [hω]

set_option maxHeartbeats 1000000 in
private theorem abs_integral_cos_mul_deriv_le
    {Q : ℝ → ℝ} {ω : ℝ}
    (hQ'_int : IntegrableOn (deriv Q) (Icc (0 : ℝ) 1) volume) :
    |∫ x in (0 : ℝ)..1, Real.cos (ω * x) * deriv Q x|
      ≤ ∫ x in (0 : ℝ)..1, |deriv Q x| := by
  have hcos_cont : ContinuousOn (fun x : ℝ => Real.cos (ω * x))
      (Icc (0 : ℝ) 1) := by
    fun_prop
  have hprod_int : IntervalIntegrable
      (fun x : ℝ => Real.cos (ω * x) * deriv Q x) volume 0 1 := by
    have hprod_on : IntegrableOn
        (fun x : ℝ => deriv Q x * Real.cos (ω * x))
        (Icc (0 : ℝ) 1) volume :=
      hQ'_int.mul_continuousOn hcos_cont isCompact_Icc
    have hprod_on_u : IntegrableOn
        (fun x : ℝ => deriv Q x * Real.cos (ω * x))
        (uIcc (0 : ℝ) 1) volume := by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact hprod_on
    convert hprod_on_u.intervalIntegrable using 1
    ext x
    ring
  have h1 :
      ‖∫ x in (0 : ℝ)..1, Real.cos (ω * x) * deriv Q x‖
        ≤ ∫ x in (0 : ℝ)..1, ‖Real.cos (ω * x) * deriv Q x‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)
  have h2 :
      (∫ x in (0 : ℝ)..1, ‖Real.cos (ω * x) * deriv Q x‖)
        ≤ ∫ x in (0 : ℝ)..1, |deriv Q x| := by
    refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) ?_ ?_ ?_
    · exact hprod_int.norm
    · have hder_abs_on : IntegrableOn (fun x : ℝ => |deriv Q x|)
          (uIcc (0 : ℝ) 1) volume := by
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact hQ'_int.abs
      exact hder_abs_on.intervalIntegrable
    · intro x _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)
  simpa [Real.norm_eq_abs] using h1.trans h2

set_option maxHeartbeats 1000000 in
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
    by
      have hA_on : IntegrableOn (fun x => deriv Q x * A x)
          (Icc (0 : ℝ) 1) volume :=
        hQ'_integrable.mul_continuousOn
          ((by fun_prop : Continuous A).continuousOn) isCompact_Icc
      have hA_on_u : IntegrableOn (fun x => deriv Q x * A x)
          (uIcc (0 : ℝ) 1) volume := by
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact hA_on
      convert hA_on_u.intervalIntegrable using 1
      ext x
      ring
  have hsinQ_int : IntervalIntegrable (fun x => Real.sin (ω * x) * Q x) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((by fun_prop : Continuous (fun x : ℝ => Real.sin (ω * x))).continuousOn).mul hQ_cont
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
  · subst k
    have hnonneg : 0 ≤ 4 * CQ + 2 * Cder := by nlinarith
    simpa [intervalSineInner] using hnonneg
  · rw [freq_mul_intervalSineInner_eq_boundary_plus_deriv hk hQ_cont hQ_deriv hQ'_integrable]
    have hcos : |Real.cos ((k : ℝ) * Real.pi)| ≤ 1 := Real.abs_cos_le_one _
    have hboundary :
        |2 * (-Real.cos ((k : ℝ) * Real.pi) * Q 1 + Q 0)| ≤ 4 * CQ := by
      have hcosQ : |(-Real.cos ((k : ℝ) * Real.pi)) * Q 1| ≤ CQ := by
        rw [abs_mul, abs_neg]
        calc
          |Real.cos ((k : ℝ) * Real.pi)| * |Q 1| ≤ 1 * CQ :=
            mul_le_mul hcos hQ1 (abs_nonneg _) (by norm_num)
          _ = CQ := by ring
      have hsum :
          |(-Real.cos ((k : ℝ) * Real.pi)) * Q 1 + Q 0| ≤ 2 * CQ := by
        calc
          |(-Real.cos ((k : ℝ) * Real.pi)) * Q 1 + Q 0|
              ≤ |(-Real.cos ((k : ℝ) * Real.pi)) * Q 1| + |Q 0| :=
                abs_add_le _ _
          _ ≤ CQ + CQ := add_le_add hcosQ hQ0
          _ = 2 * CQ := by ring
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      calc
        2 * |(-Real.cos ((k : ℝ) * Real.pi)) * Q 1 + Q 0|
            ≤ 2 * (2 * CQ) :=
              mul_le_mul_of_nonneg_left hsum (by norm_num)
        _ = 4 * CQ := by ring
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

private theorem positivePart_le_abs (r : ℝ) :
    positivePart r ≤ |r| := by
  by_cases hr : 0 ≤ r
  · simp [positivePart, hr, abs_of_nonneg hr]
  · have hr' : r ≤ 0 := le_of_not_ge hr
    simp [positivePart, hr', abs_of_nonpos hr']

private theorem truncatedLogisticLocal_abs_le_of_abs_le
    (p : CM2Params) {M r : ℝ} (hM : 0 < M) (hr : |r| ≤ M) :
    |truncatedLogisticLocal p r| ≤
      M * (p.a + p.b * M ^ p.α) := by
  have hM_nonneg : 0 ≤ M := hM.le
  have hpp_nonneg : 0 ≤ positivePart r := positivePart_nonneg r
  have hpp_le_M : positivePart r ≤ M :=
    (positivePart_le_abs r).trans hr
  have hpow_nonneg : 0 ≤ (positivePart r) ^ p.α :=
    Real.rpow_nonneg hpp_nonneg _
  have hpow_le : (positivePart r) ^ p.α ≤ M ^ p.α :=
    Real.rpow_le_rpow hpp_nonneg hpp_le_M p.hα.le
  have hA_nonneg : 0 ≤ p.a + p.b * M ^ p.α :=
    add_nonneg p.ha
      (mul_nonneg p.hb (Real.rpow_nonneg hM_nonneg _))
  have hinner :
      |p.a - p.b * (positivePart r) ^ p.α|
        ≤ p.a + p.b * M ^ p.α := by
    calc
      |p.a - p.b * (positivePart r) ^ p.α|
          ≤ |p.a| + |p.b * (positivePart r) ^ p.α| := abs_sub _ _
      _ = p.a + p.b * (positivePart r) ^ p.α := by
          rw [abs_of_nonneg p.ha, abs_mul, abs_of_nonneg p.hb,
            abs_of_nonneg hpow_nonneg]
      _ ≤ p.a + p.b * M ^ p.α := by
          exact add_le_add (le_refl p.a)
            (mul_le_mul_of_nonneg_left hpow_le p.hb)
  calc
    |truncatedLogisticLocal p r|
        = |r| * |p.a - p.b * (positivePart r) ^ p.α| := by
          simp [truncatedLogisticLocal, abs_mul]
    _ ≤ M * (p.a + p.b * M ^ p.α) :=
        mul_le_mul hr hinner (abs_nonneg _) hM_nonneg

private theorem truncatedLogisticLifted_continuousOn_of_lift_continuousOn
    (p : CM2Params) {w : intervalDomainPoint → ℝ}
    (hw : ContinuousOn (intervalDomainLift w) (Icc (0 : ℝ) 1)) :
    ContinuousOn (truncatedLogisticLifted p w) (Icc (0 : ℝ) 1) := by
  have hpos : ContinuousOn
      (fun y : ℝ => positivePart (intervalDomainLift w y))
      (Icc (0 : ℝ) 1) := by
    intro x hx
    simpa [positivePart] using (hw x hx).max continuousWithinAt_const
  have hpow : ContinuousOn
      (fun y : ℝ => (positivePart (intervalDomainLift w y)) ^ p.α)
      (Icc (0 : ℝ) 1) :=
    hpos.rpow_const (fun _ _ => Or.inr p.hα.le)
  simpa [truncatedLogisticLifted, truncatedLogisticLocal] using
    hw.mul (continuousOn_const.sub (continuousOn_const.mul hpow))

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
  set B : ℝ := M * (p.a + p.b * M ^ p.α) with hBdef
  have hB_nonneg : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg hM.le
      (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg hM.le _)))
  have hsrc_cont :
      ContinuousOn (truncatedLogisticLifted p (u s)) (Icc (0 : ℝ) 1) :=
    truncatedLogisticLifted_continuousOn_of_lift_continuousOn p hu_cont
  have hsrc_bound :
      ∀ x ∈ Icc (0 : ℝ) 1,
        |truncatedLogisticLifted p (u s) x| ≤ B := by
    intro x hx
    have hx_bound : |intervalDomainLift (u s) x| ≤ M := by
      simpa [intervalDomainLift, hx] using hbound ⟨x, hx⟩
    simpa [B, hBdef, truncatedLogisticLifted] using
      truncatedLogisticLocal_abs_le_of_abs_le p hM hx_bound
  have hcoeff :=
    cosineCoeffs_abs_le_of_continuous_bounded hsrc_cont hB_nonneg hsrc_bound
  refine ⟨2 * B, mul_nonneg (by norm_num) hB_nonneg, ?_⟩
  intro k
  simpa [truncatedLogisticSourceCoeff] using hcoeff k

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
private theorem truncatedBFormSourceCoeff_bound_positive_time_window_core
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ, 0 < σ → σ ≤ t → ∀ k : ℕ,
      |truncatedBFormSourceCoeff p
        (truncatedConjugatePicardLimit p u₀ DT.T) σ k| ≤ C := by
  set u := truncatedConjugatePicardLimit p u₀ DT.T with hu_def
  set SD : TruncatedConjugateMildSolutionData p u₀ :=
    truncatedConjugateMildSolutionData_of_data DT
  let B : ℝ := SD.M * (p.a + p.b * SD.M ^ p.α)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg SD.hM.le
      (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg SD.hM.le _)))
  -- Part 1: logistic bound
  have hlog : ∀ σ, 0 < σ → σ ≤ t → ∀ k : ℕ,
      |truncatedLogisticSourceCoeff p u σ k| ≤ 2 * B := by
    intro σ hσ hσt k
    have hball : ∀ x : intervalDomainPoint, |u σ x| ≤ SD.M :=
      SD.hbound σ hσ (le_trans hσt (le_trans htT (le_of_eq rfl)))
    have hcont_slice : Continuous (u σ) :=
      SD.hcont σ hσ (le_trans hσt (le_trans htT (le_of_eq rfl)))
    have hcont_lift : ContinuousOn (intervalDomainLift (u σ)) (Icc (0 : ℝ) 1) := by
      rw [continuousOn_iff_continuous_restrict]
      have hres : Set.restrict (Icc (0 : ℝ) 1) (intervalDomainLift (u σ)) = u σ := by
        funext ⟨z, hz⟩
        show intervalDomainLift (u σ) z = u σ ⟨z, hz⟩
        rw [intervalDomainLift, dif_pos hz]
      rw [hres]; exact hcont_slice
    have hsrc_cont :
        ContinuousOn (truncatedLogisticLifted p (u σ)) (Icc (0 : ℝ) 1) :=
      truncatedLogisticLifted_continuousOn_of_lift_continuousOn p hcont_lift
    have hsrc_bound :
        ∀ x ∈ Icc (0 : ℝ) 1,
          |truncatedLogisticLifted p (u σ) x| ≤ B := by
      intro x hx
      have hx_bound : |intervalDomainLift (u σ) x| ≤ SD.M := by
        simpa [intervalDomainLift, hx] using hball ⟨x, hx⟩
      simpa [B, truncatedLogisticLifted] using
        truncatedLogisticLocal_abs_le_of_abs_le p SD.hM hx_bound
    have hcoeff :=
      cosineCoeffs_abs_le_of_continuous_bounded hsrc_cont hB_nonneg hsrc_bound
    simpa [truncatedLogisticSourceCoeff] using hcoeff k
  -- Part 2: chemDiv bound (Lipschitz → flux W^{1,1} → IBP → bounded)
  have ⟨CC, hCC, hchem⟩ : ∃ CC : ℝ, 0 ≤ CC ∧
      ∀ σ, 0 < σ → σ ≤ t → ∀ k,
        |truncatedChemDivSourceCoeff p u σ k| ≤ CC := by
    have _hlip := truncatedPicardLimit_lipschitzOn_positive_time DT ht htT sorry
    sorry
  -- Triangle inequality
  exact ⟨2 * B + |p.χ₀| * CC,
    add_nonneg (mul_nonneg (by norm_num) hB_nonneg) (mul_nonneg (abs_nonneg _) hCC),
    fun σ hσ hσt k => by
      simp only [truncatedBFormSourceCoeff]
      have h1 := hlog σ hσ hσt k
      have h2 : |p.χ₀| * |truncatedChemDivSourceCoeff p u σ k| ≤ |p.χ₀| * CC :=
        mul_le_mul_of_nonneg_left (hchem σ hσ hσt k) (abs_nonneg _)
      have htri : |truncatedLogisticSourceCoeff p u σ k
              - p.χ₀ * truncatedChemDivSourceCoeff p u σ k|
          ≤ |truncatedLogisticSourceCoeff p u σ k|
            + |p.χ₀| * |truncatedChemDivSourceCoeff p u σ k| := by
        calc |truncatedLogisticSourceCoeff p u σ k
                - p.χ₀ * truncatedChemDivSourceCoeff p u σ k|
            ≤ |truncatedLogisticSourceCoeff p u σ k|
              + |-(p.χ₀ * truncatedChemDivSourceCoeff p u σ k)| := by
              rw [show truncatedLogisticSourceCoeff p u σ k
                - p.χ₀ * truncatedChemDivSourceCoeff p u σ k
                = truncatedLogisticSourceCoeff p u σ k
                + (-(p.χ₀ * truncatedChemDivSourceCoeff p u σ k)) from sub_eq_add_neg _ _]
              exact abs_add_le _ _
          _ = |truncatedLogisticSourceCoeff p u σ k|
              + |p.χ₀| * |truncatedChemDivSourceCoeff p u σ k| := by
              rw [abs_neg, abs_mul]
      linarith⟩

theorem truncatedBFormSourceCoeff_bound_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {s : ℝ} (hs : 0 < s) (hsT : s ≤ DT.T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      |truncatedBFormSourceCoeff p
        (truncatedConjugatePicardLimit p u₀ DT.T) s k| ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    truncatedBFormSourceCoeff_bound_positive_time_window_core DT hs hsT
  exact ⟨C, hC, hbound s hs le_rfl⟩

private theorem summable_one_div_unitIntervalCosineEigenvalue :
    Summable (fun k : ℕ => 1 / unitIntervalCosineEigenvalue k) := by
  rw [← summable_nat_add_iff 1]
  have hp2 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    simpa using
      (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).2 hbase
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hp2
  · exact one_div_nonneg.mpr (by
      unfold unitIntervalCosineEigenvalue
      positivity)
  · have hk : k + 1 ≠ 0 := by omega
    have hle :=
      ShenWork.Paper2.IntervalCoeffLadderFull.one_div_unitIntervalCosineEigenvalue_le_one_div_nat_sq hk
    simpa [Nat.cast_add, Nat.cast_one] using hle

private theorem localRestartCoeff_h1_summable_of_bounds
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {t M₀ E : ℝ}
    (ht : 0 < t) (hM₀ : 0 ≤ M₀) (ha₀ : ∀ k, |a₀ k| ≤ M₀)
    (hE : 0 ≤ E)
    (hsrc : ∀ s, 0 ≤ s → s ≤ t → ∀ k, |a s k| ≤ E) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k * (localRestartCoeff a₀ a t k) ^ 2) := by
  let lam : ℕ → ℝ := fun k => unitIntervalCosineEigenvalue k
  let hom : ℕ → ℝ := fun k => Real.exp (-t * lam k) * a₀ k
  let duh : ℕ → ℝ :=
    fun k => ShenWork.IntervalDuhamelClosedC2.duhamelSpectralCoeff a t k
  have hhom : Summable (fun k : ℕ => lam k * (hom k) ^ 2) := by
    have hbase :
        Summable (fun k : ℕ =>
          M₀ ^ 2 * (lam k * Real.exp (-(2 * t) * lam k))) :=
      (ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable
          (τ := 2 * t) (by linarith)).mul_left (M₀ ^ 2)
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hbase
    · exact mul_nonneg
        (by
          dsimp [lam]
          unfold unitIntervalCosineEigenvalue
          positivity)
        (sq_nonneg _)
    · have hlam : 0 ≤ lam k := by
        dsimp [lam]
        unfold unitIntervalCosineEigenvalue
        positivity
      have hexp_nonneg : 0 ≤ Real.exp (-t * lam k) := Real.exp_nonneg _
      have habs : |hom k| ≤ Real.exp (-t * lam k) * M₀ := by
        dsimp [hom]
        rw [abs_mul, abs_of_nonneg hexp_nonneg]
        exact mul_le_mul_of_nonneg_left (ha₀ k) hexp_nonneg
      have hright_nonneg : 0 ≤ Real.exp (-t * lam k) * M₀ :=
        mul_nonneg hexp_nonneg hM₀
      have hsquare :
          (hom k) ^ 2 ≤ (Real.exp (-t * lam k) * M₀) ^ 2 := by
        rw [← sq_abs (hom k)]
        exact (sq_le_sq₀ (abs_nonneg (hom k)) hright_nonneg).mpr habs
      calc
        lam k * (hom k) ^ 2
            ≤ lam k * (Real.exp (-t * lam k) * M₀) ^ 2 :=
              mul_le_mul_of_nonneg_left hsquare hlam
        _ = M₀ ^ 2 * (lam k * Real.exp (-(2 * t) * lam k)) := by
              have hexp_sq :
                  (Real.exp (-t * lam k)) ^ 2 =
                    Real.exp (-(2 * t) * lam k) := by
                rw [pow_two, ← Real.exp_add]
                congr 1
                ring
              rw [mul_pow, hexp_sq]
              ring
  have hduh : Summable (fun k : ℕ => lam k * (duh k) ^ 2) := by
    have hbase : Summable (fun k : ℕ => E ^ 2 * (1 / lam k)) :=
      summable_one_div_unitIntervalCosineEigenvalue.mul_left (E ^ 2)
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hbase
    · exact mul_nonneg
        (by
          dsimp [lam]
          unfold unitIntervalCosineEigenvalue
          positivity)
        (sq_nonneg _)
    · by_cases hk : k = 0
      · subst k
        simp [lam, unitIntervalCosineEigenvalue]
      · have hlam_pos : 0 < lam k := by
          dsimp [lam]
          unfold unitIntervalCosineEigenvalue
          have hkpos : (0 : ℝ) < (k : ℝ) :=
            Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
          positivity
        have hduh_abs : |duh k| ≤ E / lam k := by
          dsimp [duh, lam]
          exact
            ShenWork.Paper2.IntervalCoeffLadderPassBasic.duhamelSpectralCoeff_abs_le_div_eigenvalue
                (a := a) ht hk (E := E)
                (fun s hs hst => hsrc s hs hst k)
        have hright_nonneg : 0 ≤ E / lam k :=
          div_nonneg hE hlam_pos.le
        have hsquare : (duh k) ^ 2 ≤ (E / lam k) ^ 2 := by
          rw [← sq_abs (duh k)]
          exact (sq_le_sq₀ (abs_nonneg (duh k)) hright_nonneg).mpr hduh_abs
        calc
          lam k * (duh k) ^ 2
              ≤ lam k * (E / lam k) ^ 2 :=
                mul_le_mul_of_nonneg_left hsquare hlam_pos.le
          _ = E ^ 2 * (1 / lam k) := by
                field_simp [ne_of_gt hlam_pos]
  have hsum :
      Summable (fun k : ℕ =>
        2 * (lam k * (hom k) ^ 2) + 2 * (lam k * (duh k) ^ 2)) :=
    (hhom.mul_left 2).add (hduh.mul_left 2)
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hsum
  · exact mul_nonneg
      (by
        unfold unitIntervalCosineEigenvalue
        positivity)
      (sq_nonneg _)
  · have hlam : 0 ≤ lam k := by
      dsimp [lam]
      unfold unitIntervalCosineEigenvalue
      positivity
    have hsq : (hom k + duh k) ^ 2 ≤ 2 * (hom k) ^ 2 + 2 * (duh k) ^ 2 := by
      nlinarith [sq_nonneg (hom k - duh k)]
    calc
      lam k * (localRestartCoeff a₀ a t k) ^ 2
          = lam k * (hom k + duh k) ^ 2 := by
            rfl
      _ ≤ lam k * (2 * (hom k) ^ 2 + 2 * (duh k) ^ 2) :=
            mul_le_mul_of_nonneg_left hsq hlam
      _ = 2 * (lam k * (hom k) ^ 2) + 2 * (lam k * (duh k) ^ 2) := by
            ring

private theorem truncatedPicardInitialCoeff_abs_le_two_M
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀) :
    ∀ k : ℕ, |truncatedPicardInitialCoeff u₀ k| ≤ 2 * DT.M := by
  intro k
  have hmeasC :
      AEStronglyMeasurable
        (fun x => ((intervalDomainLift u₀ x : ℝ) : ℂ))
        (intervalMeasure 1) := by
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable DT.hbase_lift_meas
  have hintCμ :
      Integrable (fun x => ((intervalDomainLift u₀ x : ℝ) : ℂ))
        (intervalMeasure 1) := by
    exact Integrable.of_bound hmeasC DT.M
      (Filter.Eventually.of_forall fun y => by
        simpa [Complex.normSq, Complex.normSq_apply, Real.norm_eq_abs]
          using DT.hbase_lift_bound y)
  have hintOnC :
      IntegrableOn (fun x => ((intervalDomainLift u₀ x : ℝ) : ℂ))
        (Icc (0 : ℝ) 1) volume := by
    simpa [intervalMeasure, intervalSet] using hintCμ
  have hintC :
      IntervalIntegrable (fun x => ((intervalDomainLift u₀ x : ℝ) : ℂ))
        volume (0 : ℝ) 1 := by
    exact
      (intervalIntegrable_iff_integrableOn_Icc_of_le
        (by norm_num : (0 : ℝ) ≤ 1)).2 hintOnC
  have hcoeff :=
    ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff_abs_le_two_integral_norm hintC k
  have hnorm_le :
      ∫ x in (0 : ℝ)..1, ‖((intervalDomainLift u₀ x : ℝ) : ℂ)‖ ≤ DT.M := by
    have hmono :
        ∫ x in (0 : ℝ)..1, ‖((intervalDomainLift u₀ x : ℝ) : ℂ)‖
          ≤ ∫ _x in (0 : ℝ)..1, DT.M := by
      apply intervalIntegral.integral_mono_on
        (by norm_num : (0 : ℝ) ≤ 1) hintC.norm intervalIntegrable_const
      intro x _hx
      have hxbound := DT.hbase_lift_bound x
      simpa [Complex.normSq, Complex.normSq_apply, Real.norm_eq_abs] using hxbound
    calc
      ∫ x in (0 : ℝ)..1, ‖((intervalDomainLift u₀ x : ℝ) : ℂ)‖
          ≤ ∫ _x in (0 : ℝ)..1, DT.M := hmono
      _ = DT.M := by simp
  unfold truncatedPicardInitialCoeff
  dsimp [cosineCoeffs]
  exact hcoeff.trans
    (mul_le_mul_of_nonneg_left hnorm_le (by norm_num : (0 : ℝ) ≤ 2))

theorem truncatedBFormSourceCoeff_bound_on_positive_time_interval
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, 0 ≤ s → s ≤ t → ∀ k : ℕ,
      |truncatedBFormSourceCoeff p
        (truncatedConjugatePicardLimit p u₀ DT.T) s k| ≤ C := by
  obtain ⟨C, hC, hpos⟩ :=
    truncatedBFormSourceCoeff_bound_positive_time_window_core DT ht htT
  refine ⟨C, hC, ?_⟩
  intro s hs hst k
  by_cases hs0 : s = 0
  · subst s
    have hzero :
        truncatedBFormSourceCoeff p
          (truncatedConjugatePicardLimit p u₀ DT.T) 0 k = 0 := by
      simp [truncatedBFormSourceCoeff, truncatedLogisticSourceCoeff,
        truncatedChemDivSourceCoeff, truncatedConjugatePicardLimit,
        truncatedLogisticLifted, truncatedLogisticLocal, truncatedChemFluxLifted,
        intervalSineInner, intervalDomainLift]
    simpa [hzero] using hC
  · have hspos : 0 < s := by
      rcases lt_or_eq_of_le hs with hlt | heq
      · exact hlt
      · exact False.elim (hs0 heq.symm)
    exact hpos s hspos hst k

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
  obtain ⟨E, hE, hsrc⟩ :=
    truncatedBFormSourceCoeff_bound_on_positive_time_interval DT ht htT
  have hM₀ : 0 ≤ 2 * DT.M :=
    mul_nonneg (by norm_num) DT.hM.le
  have hrestart :=
    localRestartCoeff_h1_summable_of_bounds
      (a₀ := truncatedPicardInitialCoeff u₀)
      (a := truncatedBFormSourceCoeff p
        (truncatedConjugatePicardLimit p u₀ DT.T))
      (t := t) (M₀ := 2 * DT.M) (E := E)
      ht hM₀ (truncatedPicardInitialCoeff_abs_le_two_M DT) hE
      (fun s hs0 hst k => hsrc s hs0 hst k)
  simpa [truncatedPicardCoeff] using hrestart

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

/-- **ℓ¹ coefficient summability**: at positive time the Picard limit has
summable cosine coefficients.  This follows from the stronger eigenvalue
weighted summability because `λ_k ≥ 1` for all positive modes, while the
zero mode is a single term. -/
theorem truncatedPicardCoeff_summable_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    Summable (fun k : ℕ =>
      |truncatedPicardCoeff p u₀
        (truncatedConjugatePicardLimit p u₀ DT.T) t k|) := by
  let U := truncatedConjugatePicardLimit p u₀ DT.T
  have hweighted :
      Summable (fun k : ℕ =>
        unitIntervalCosineEigenvalue k *
          |truncatedPicardCoeff p u₀ U t k|) := by
    simpa [U] using
      truncatedPicardCoeff_eigenvalue_weighted_summable_positive_time
        (DT := DT) ht htT
  exact
    (ShenWork.IntervalDuhamelClosedC2.cosineCoeff_summable_of_eigenvalue_summable
      (b := fun k : ℕ => truncatedPicardCoeff p u₀ U t k) hweighted).2

/-- Time derivative coefficient summability.  `a'_k = -λ_k a_k + src_k`,
so `|a'_k| ≤ λ_k|a_k| + |src_k|`.  Uses eigenvalue-weighted + source ℓ¹. -/
theorem truncatedPicardCoeffTimeDeriv_summable_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    Summable (fun k : ℕ =>
      |truncatedPicardCoeffTimeDeriv p u₀
        (truncatedConjugatePicardLimit p u₀ DT.T) t k|) := by
  have heig := truncatedPicardCoeff_eigenvalue_weighted_summable_positive_time DT ht htT
  have hsrc := truncatedBFormSourceCoeff_summable_positive_time DT ht htT
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) (heig.add hsrc)
  simp only [truncatedPicardCoeffTimeDeriv]
  have hlam : 0 ≤ unitIntervalCosineEigenvalue k := by
    unfold unitIntervalCosineEigenvalue
    positivity
  calc
    |-(unitIntervalCosineEigenvalue k) *
          truncatedPicardCoeff p u₀
            (truncatedConjugatePicardLimit p u₀ DT.T) t k
        + truncatedBFormSourceCoeff p
            (truncatedConjugatePicardLimit p u₀ DT.T) t k|
        ≤ |-(unitIntervalCosineEigenvalue k) *
            truncatedPicardCoeff p u₀
              (truncatedConjugatePicardLimit p u₀ DT.T) t k|
          + |truncatedBFormSourceCoeff p
              (truncatedConjugatePicardLimit p u₀ DT.T) t k| := abs_add_le _ _
    _ = unitIntervalCosineEigenvalue k *
          |truncatedPicardCoeff p u₀
            (truncatedConjugatePicardLimit p u₀ DT.T) t k|
        + |truncatedBFormSourceCoeff p
            (truncatedConjugatePicardLimit p u₀ DT.T) t k| := by
          rw [abs_mul, abs_neg, abs_of_nonneg hlam]

private theorem intervalDomainLift_continuousAt_of_continuous_of_mem_Ioo
    {w : intervalDomainPoint → ℝ} (hw : Continuous w)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousAt (intervalDomainLift w) x := by
  have hUcont : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) :=
    lift_continuousOn_Icc_of_continuous hw
  have hIcc_nhds : Set.Icc (0 : ℝ) 1 ∈ 𝓝 x :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hx) Set.Ioo_subset_Icc_self
  exact hUcont.continuousAt hIcc_nhds

private theorem deriv_negativePartLift_eq_neg_of_neg
    {w : intervalDomainPoint → ℝ} {x : ℝ}
    (hw : ContinuousAt (intervalDomainLift w) x)
    (hneg : intervalDomainLift w x < 0) :
    deriv (BFormPositiveDatumNegPart.negativePartLift w) x =
      -deriv (intervalDomainLift w) x := by
  have hmem : intervalDomainLift w x ∈ Set.Iio (0 : ℝ) := hneg
  have hnhds : Set.Iio (0 : ℝ) ∈ 𝓝 (intervalDomainLift w x) :=
    isOpen_Iio.mem_nhds hmem
  have hev_neg : ∀ᶠ y in 𝓝 x, intervalDomainLift w y ∈ Set.Iio (0 : ℝ) :=
    hw hnhds
  have hev : BFormPositiveDatumNegPart.negativePartLift w =ᶠ[𝓝 x]
      fun y : ℝ => -intervalDomainLift w y :=
    hev_neg.mono (fun y hy =>
      BFormPositiveDatumNegPart.negativePart_eq_neg_of_nonpos hy.le)
  rw [hev.deriv_eq]
  simp

private theorem deriv_neg_negativePartLift_eq_zero_of_zero
    {w : intervalDomainPoint → ℝ} {x : ℝ}
    (hzero : intervalDomainLift w x = 0) :
    deriv (fun y : ℝ => -BFormPositiveDatumNegPart.negativePartLift w y) x = 0 := by
  have hmax :
      IsLocalMax (fun y : ℝ => -BFormPositiveDatumNegPart.negativePartLift w y) x := by
    unfold IsLocalMax IsMaxFilter
    filter_upwards [] with y
    have hnn : 0 ≤ BFormPositiveDatumNegPart.negativePartLift w y := by
      exact BFormPositiveDatumNegPart.negativePart_nonneg _
    have hxval : -BFormPositiveDatumNegPart.negativePartLift w x = 0 := by
      simp [BFormPositiveDatumNegPart.negativePartLift, hzero,
        BFormPositiveDatumNegPart.negativePart_eq_zero_of_nonneg]
    calc
      -BFormPositiveDatumNegPart.negativePartLift w y ≤ 0 := by linarith
      _ = -BFormPositiveDatumNegPart.negativePartLift w x := by rw [hxval]
  exact hmax.deriv_eq_zero

private theorem deriv_neg_negativePartLift_eq_zero_at_zero
    (w : intervalDomainPoint → ℝ) :
    deriv (fun y : ℝ => -BFormPositiveDatumNegPart.negativePartLift w y)
      (0 : ℝ) = 0 := by
  let φ : ℝ → ℝ := fun y => -BFormPositiveDatumNegPart.negativePartLift w y
  by_cases hdiff : DifferentiableAt ℝ φ (0 : ℝ)
  · have hev0 : φ =ᶠ[nhdsWithin (0 : ℝ) (Set.Iio 0)] (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
	      have hnot : y ∉ Set.Icc (0 : ℝ) 1 := fun hyIcc => not_le_of_gt hy hyIcc.1
	      have hLift : intervalDomainLift w y = 0 := by
	        simp [intervalDomainLift, hnot]
	      have hNegLift : BFormPositiveDatumNegPart.negativePartLift w y = 0 := by
	        rw [BFormPositiveDatumNegPart.negativePartLift, hLift]
	        simp [BFormPositiveDatumNegPart.negativePart_eq_zero_of_nonneg]
	      simp [φ, hNegLift]
    have hval : φ (0 : ℝ) = 0 := by
      have hL : Filter.Tendsto φ
          (nhdsWithin (0 : ℝ) (Set.Iio 0)) (𝓝 0) :=
        (Filter.tendsto_congr' hev0).mpr tendsto_const_nhds
      have hC : Filter.Tendsto φ
          (nhdsWithin (0 : ℝ) (Set.Iio 0)) (𝓝 (φ 0)) :=
        hdiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      exact tendsto_nhds_unique hC hL
    have hconst : HasDerivWithinAt φ 0 (Set.Iio (0 : ℝ)) 0 :=
      (hasDerivWithinAt_const (c := (0 : ℝ))
        (s := Set.Iio (0 : ℝ)) (x := (0 : ℝ))).congr_of_eventuallyEq
          hev0 hval
    have hderiv : HasDerivWithinAt φ (deriv φ 0) (Set.Iio (0 : ℝ)) 0 :=
      hdiff.hasDerivAt.hasDerivWithinAt
    exact (uniqueDiffWithinAt_Iio 0).eq_deriv _ hderiv hconst
  · exact deriv_zero_of_not_differentiableAt hdiff

private theorem deriv_neg_negativePartLift_eq_zero_at_one
    (w : intervalDomainPoint → ℝ) :
    deriv (fun y : ℝ => -BFormPositiveDatumNegPart.negativePartLift w y)
      (1 : ℝ) = 0 := by
  let φ : ℝ → ℝ := fun y => -BFormPositiveDatumNegPart.negativePartLift w y
  by_cases hdiff : DifferentiableAt ℝ φ (1 : ℝ)
  · have hev1 : φ =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
	      have hnot : y ∉ Set.Icc (0 : ℝ) 1 := fun hyIcc => not_le_of_gt hy hyIcc.2
	      have hLift : intervalDomainLift w y = 0 := by
	        simp [intervalDomainLift, hnot]
	      have hNegLift : BFormPositiveDatumNegPart.negativePartLift w y = 0 := by
	        rw [BFormPositiveDatumNegPart.negativePartLift, hLift]
	        simp [BFormPositiveDatumNegPart.negativePart_eq_zero_of_nonneg]
	      simp [φ, hNegLift]
    have hval : φ (1 : ℝ) = 0 := by
      have hL : Filter.Tendsto φ
          (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 0) :=
        (Filter.tendsto_congr' hev1).mpr tendsto_const_nhds
      have hC : Filter.Tendsto φ
          (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 (φ 1)) :=
        hdiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      exact tendsto_nhds_unique hC hL
    have hconst : HasDerivWithinAt φ 0 (Set.Ioi (1 : ℝ)) 1 :=
      (hasDerivWithinAt_const (c := (0 : ℝ))
        (s := Set.Ioi (1 : ℝ)) (x := (1 : ℝ))).congr_of_eventuallyEq
          hev1 hval
    have hderiv : HasDerivWithinAt φ (deriv φ 1) (Set.Ioi (1 : ℝ)) 1 :=
      hdiff.hasDerivAt.hasDerivWithinAt
    exact (uniqueDiffWithinAt_Ioi 1).eq_deriv _ hderiv hconst
  · exact deriv_zero_of_not_differentiableAt hdiff

private theorem deriv_neg_negativePartLift_abs_le_lift_deriv
    {w : intervalDomainPoint → ℝ} {x : ℝ}
    (hw : ContinuousAt (intervalDomainLift w) x) :
    |deriv (fun y : ℝ => -BFormPositiveDatumNegPart.negativePartLift w y) x|
      ≤ |deriv (intervalDomainLift w) x| := by
  by_cases hpos : 0 < intervalDomainLift w x
  · have hderiv :=
      BFormPositiveDatumNegPart.deriv_negativePartLift_eq_zero_of_pos
        (u := intervalDomainLift w) hw hpos
    have hφ :
        deriv (fun y : ℝ => -BFormPositiveDatumNegPart.negativePartLift w y) x = 0 := by
      simp [BFormPositiveDatumNegPart.negativePartLift, hderiv]
    rw [hφ, abs_zero]
    exact abs_nonneg _
  · by_cases hneg : intervalDomainLift w x < 0
    · have hderiv := deriv_negativePartLift_eq_neg_of_neg hw hneg
      have hφ :
          deriv (fun y : ℝ => -BFormPositiveDatumNegPart.negativePartLift w y) x =
            deriv (intervalDomainLift w) x := by
        simp [hderiv]
      rw [hφ]
    · have hzero : intervalDomainLift w x = 0 :=
        le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      have hφ := deriv_neg_negativePartLift_eq_zero_of_zero (w := w) hzero
      rw [hφ, abs_zero]
      exact abs_nonneg _

/-! ## Level 5: Series representations (time derivative + gradient) -/

/-- Level-5 reconstruction package for the truncated positive-time route.

This is the analytic bridge from the truncated mild fixed point plus the
Sobolev ladder to the two pointwise cosine-series representatives consumed
below.  It packages the local restart representation of the Picard limit, the
termwise time differentiation of the restart coefficients, and the spatial
termwise differentiation of the positive-time cosine series. -/
private theorem truncatedPicardLimit_level5_series_reconstruction_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    (∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (fun z : intervalDomainPoint =>
        ShenWork.IntervalDomain.intervalDomain.timeDeriv
          (truncatedConjugatePicardLimit p u₀ DT.T) t z) x
        = ∑' k : ℕ, truncatedPicardCoeffTimeDeriv p u₀
            (truncatedConjugatePicardLimit p u₀ DT.T) t k *
            ShenWork.CosineSpectrum.cosineMode k x)
    ∧
    (∀ x ∈ Icc (0 : ℝ) 1,
      deriv (intervalDomainLift
        ((truncatedConjugatePicardLimit p u₀ DT.T) t)) x
        = ∑' k : ℕ, truncatedPicardCoeff p u₀
            (truncatedConjugatePicardLimit p u₀ DT.T) t k *
          deriv (ShenWork.CosineSpectrum.cosineMode k) x)
    ∧
    (∀ x ∈ Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ
        (intervalDomainLift
          ((truncatedConjugatePicardLimit p u₀ DT.T) t)) x) := by
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
  let c : ℕ → ℝ := fun k =>
    truncatedPicardCoeff p u₀
      (truncatedConjugatePicardLimit p u₀ DT.T) t k
  let w : ℕ → ℝ := fun k => |c k| * ((k : ℝ) * Real.pi)
  have hsum_w : Summable w := by
    simpa [w, c] using truncatedPicardCoeff_grad_l1_positive_time DT ht htT
  have hw_nonneg : ∀ k, 0 ≤ w k := by
    intro k
    exact mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) Real.pi_pos.le)
  refine ⟨∑' k : ℕ, w k, tsum_nonneg hw_nonneg, ?_⟩
  intro x hx
  have hrep :=
    (truncatedPicardLimit_level5_series_reconstruction_positive_time
      DT ht htT).2.1 x hx
  rw [hrep]
  have hterm_le : ∀ k : ℕ,
      ‖c k * deriv (ShenWork.CosineSpectrum.cosineMode k) x‖ ≤ w k := by
    intro k
    have hderiv_abs :
        |deriv (ShenWork.CosineSpectrum.cosineMode k) x|
          ≤ (k : ℝ) * Real.pi := by
      rw [ShenWork.CosineSpectrum.cosineMode_deriv]
      rw [abs_mul, abs_neg]
      calc |(k : ℝ) * Real.pi| *
            |Real.sin ((k : ℝ) * Real.pi * x)|
          ≤ ((k : ℝ) * Real.pi) * 1 := by
              gcongr
              · rw [abs_of_nonneg (by positivity)]
              · exact Real.abs_sin_le_one _
        _ = (k : ℝ) * Real.pi := by ring
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left hderiv_abs (abs_nonneg _)
  have hsum_norm : Summable
      (fun k : ℕ => ‖c k * deriv (ShenWork.CosineSpectrum.cosineMode k) x‖) :=
    hsum_w.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le
  rw [← Real.norm_eq_abs]
  exact le_trans (norm_tsum_le_tsum_norm hsum_norm)
    (Summable.tsum_le_tsum hterm_le hsum_norm hsum_w)

/-! ## Level 4b: Test function (negativePartTest) regularity -/

private theorem neg_negativePart_eq_sub_positivePart (r : ℝ) :
    -BFormPositiveDatumNegPart.negativePart r = r - positivePart r := by
  by_cases hr : 0 ≤ r
  · rw [BFormPositiveDatumNegPart.negativePart_eq_zero_of_nonneg hr,
      positivePart_eq_self_of_nonneg hr]
    ring
  · have hr_nonpos : r ≤ 0 := le_of_not_ge hr
    rw [BFormPositiveDatumNegPart.negativePart_eq_neg_of_nonpos hr_nonpos,
      positivePart_eq_zero_of_nonpos hr_nonpos]
    ring

private theorem positivePart_comp_hasDerivAt_zero_of_hasDerivAt_zero
    {f : ℝ → ℝ} {x : ℝ}
    (hf : HasDerivAt f 0 x) (hfx : f x = 0) :
    HasDerivAt (fun y : ℝ => positivePart (f y)) 0 x := by
  rw [hasDerivAt_iff_isLittleO]
  have hf_little :
      (fun y : ℝ => f y) =o[𝓝 x] fun y : ℝ => y - x := by
    simpa [hfx] using hf.isLittleO
  have hpp_bigO :
      (fun y : ℝ => positivePart (f y)) =O[𝓝 x] fun y : ℝ => f y := by
    refine Asymptotics.IsBigO.of_bound' (Filter.Eventually.of_forall ?_)
    intro y
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    simpa [abs_of_nonneg (positivePart_nonneg (f y))] using
      positivePart_le_abs' (f y)
  have hpp_little :
      (fun y : ℝ => positivePart (f y)) =o[𝓝 x] fun y : ℝ => y - x :=
    hpp_bigO.trans_isLittleO hf_little
  simpa [hfx, positivePart_eq_zero_of_nonpos (le_refl (0 : ℝ))] using hpp_little

private theorem positivePart_comp_hasDerivAt_of_hasDerivAt_not_bad
    {f : ℝ → ℝ} {x f' : ℝ}
    (hf : HasDerivAt f f' x)
    (hnot_bad : f x = 0 → f' = 0) :
    ∃ d : ℝ, HasDerivAt (fun y : ℝ => positivePart (f y)) d x := by
  by_cases hpos : 0 < f x
  · have hpos_ev : ∀ᶠ y in 𝓝 x, 0 < f y :=
      hf.continuousAt.tendsto.eventually (isOpen_Ioi.mem_nhds hpos)
    have hev : (fun y : ℝ => positivePart (f y)) =ᶠ[𝓝 x] f := by
      filter_upwards [hpos_ev] with y hy
      exact positivePart_eq_self_of_nonneg hy.le
    exact ⟨f', hf.congr_of_eventuallyEq hev⟩
  · by_cases hneg : f x < 0
    · have hneg_ev : ∀ᶠ y in 𝓝 x, f y < 0 :=
        hf.continuousAt.tendsto.eventually (isOpen_Iio.mem_nhds hneg)
      have hev : (fun y : ℝ => positivePart (f y)) =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
        filter_upwards [hneg_ev] with y hy
        exact positivePart_eq_zero_of_nonpos hy.le
      exact ⟨0, (hasDerivAt_const (x := x) (c := (0 : ℝ))).congr_of_eventuallyEq hev⟩
    · have hzero : f x = 0 :=
        le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      have hf0 : HasDerivAt f 0 x := by
        simpa [hnot_bad hzero] using hf
      exact ⟨0, positivePart_comp_hasDerivAt_zero_of_hasDerivAt_zero hf0 hzero⟩

private theorem neg_negativePartLift_hasDerivAt_of_lift_hasDerivAt_not_bad
    {w : intervalDomainPoint → ℝ} {x : ℝ}
    (hw : HasDerivAt (intervalDomainLift w)
      (deriv (intervalDomainLift w) x) x)
    (hnot_bad :
      intervalDomainLift w x = 0 → deriv (intervalDomainLift w) x = 0) :
    HasDerivAt (fun y : ℝ =>
        -BFormPositiveDatumNegPart.negativePartLift w y)
      (deriv (fun y : ℝ =>
        -BFormPositiveDatumNegPart.negativePartLift w y) x) x := by
  obtain ⟨dpp, hpp⟩ :=
    positivePart_comp_hasDerivAt_of_hasDerivAt_not_bad hw hnot_bad
  have hEq :
      (fun y : ℝ => -BFormPositiveDatumNegPart.negativePartLift w y)
        =
      fun y : ℝ => intervalDomainLift w y - positivePart (intervalDomainLift w y) := by
    funext y
    simp [BFormPositiveDatumNegPart.negativePartLift,
      neg_negativePart_eq_sub_positivePart]
  have hφ : HasDerivAt
      (fun y : ℝ => -BFormPositiveDatumNegPart.negativePartLift w y)
      (deriv (intervalDomainLift w) x - dpp) x := by
    rw [hEq]
    exact hw.sub hpp
  rw [hφ.deriv]
  exact hφ

private def transversalZeroSet (f : ℝ → ℝ) : Set ℝ :=
  {x : ℝ | x ∈ Set.Ioo (0 : ℝ) 1 ∧ f x = 0 ∧ deriv f x ≠ 0}

private theorem transversalZeroSet_countable_of_differentiableAt
    {f : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ f x) :
    (transversalZeroSet f).Countable := by
  let S : Set ℝ := transversalZeroSet f
  have hdisc : IsDiscrete S := by
    rw [isDiscrete_iff_nhdsNE]
    intro x hx
    rw [← Filter.mem_iff_inf_principal_compl]
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := hx.1
    have hxderiv : deriv f x ≠ 0 := hx.2.2
    have hev : ∀ᶠ z in 𝓝[≠] x, f z ≠ (0 : ℝ) :=
      (hf x hxIoo).hasDerivAt.eventually_ne hxderiv
    filter_upwards [hev] with z hz hzS
    exact hz hzS.2.1
  simpa [S] using
    (HereditarilyLindelofSpace.isLindelof S).countable_of_isDiscrete hdisc

/-- The negative-part test `φ = -u_-` is differentiable off a countable set
when the solution is C¹.  The non-differentiability points of `max(-f, 0)`
that must be removed are the transversal zeros `f = 0`, `f' ≠ 0`; these are
isolated.  At a zero with `f' = 0`, `max/min` is differentiable with derivative
zero by the `o(x - x₀)` estimate. -/
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
  let w : intervalDomainPoint → ℝ :=
    (truncatedConjugatePicardLimit p u₀ DT.T) t
  have hdiff_Ioo :
      ∀ x ∈ Ioo (0 : ℝ) 1,
        DifferentiableAt ℝ (intervalDomainLift w) x := by
    intro x hx
    simpa [w] using
      (truncatedPicardLimit_level5_series_reconstruction_positive_time
        DT ht htT).2.2 x hx
  let s : Set ℝ := transversalZeroSet (intervalDomainLift w)
  refine ⟨s, ?_, ?_⟩
  · exact transversalZeroSet_countable_of_differentiableAt
      (f := intervalDomainLift w) hdiff_Ioo
  · intro x hx
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := hx.1
    have hx_not_s : x ∉ s := hx.2
    have hw_has :
        HasDerivAt (intervalDomainLift w)
          (deriv (intervalDomainLift w) x) x :=
      (hdiff_Ioo x hxIoo).hasDerivAt
    have hnot_bad :
        intervalDomainLift w x = 0 →
          deriv (intervalDomainLift w) x = 0 := by
      intro hzero
      by_contra hne
      exact hx_not_s ⟨hxIoo, hzero, hne⟩
    simpa [negativePartTest, w] using
      neg_negativePartLift_hasDerivAt_of_lift_hasDerivAt_not_bad
        (w := w) hw_has hnot_bad

/-- The negative-part test has a bounded derivative.  Since
`|(-f)_+'| ≤ |f'|`, the bound is the gradient bound of `u`. -/
theorem negativePartTest_deriv_bound_of_gradient_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    ∃ C : ℝ, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (negativePartTest
        (truncatedConjugatePicardLimit p u₀ DT.T) t) x| ≤ C := by
  let w : intervalDomainPoint → ℝ :=
    (truncatedConjugatePicardLimit p u₀ DT.T) t
  obtain ⟨G, hG_nonneg, hG⟩ :=
    truncatedPicardLimit_gradient_bound_positive_time DT ht htT
  have hw_cont : Continuous w :=
    (truncatedConjugateMildSolutionData_of_data DT).hcont t ht htT
  refine ⟨G, ?_⟩
  intro x hx
  rcases lt_or_eq_of_le hx.1 with hx0 | hx0
  · rcases lt_or_eq_of_le hx.2 with hx1 | hx1
    · have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
      have hwx : ContinuousAt (intervalDomainLift w) x :=
        intervalDomainLift_continuousAt_of_continuous_of_mem_Ioo hw_cont hxIoo
      have hneg :
          |deriv (fun y : ℝ =>
              -BFormPositiveDatumNegPart.negativePartLift w y) x|
            ≤ |deriv (intervalDomainLift w) x| :=
        deriv_neg_negativePartLift_abs_le_lift_deriv hwx
      have hbase : |deriv (intervalDomainLift w) x| ≤ G := by
        exact hG x hx
      change
        |deriv (fun y : ℝ =>
            -BFormPositiveDatumNegPart.negativePartLift w y) x| ≤ G
      exact hneg.trans hbase
    · have hx1' : x = 1 := hx1
      subst x
      change
        |deriv (fun y : ℝ =>
            -BFormPositiveDatumNegPart.negativePartLift w y) 1| ≤ G
      rw [deriv_neg_negativePartLift_eq_zero_at_one, abs_zero]
      exact hG_nonneg
  · have hx0' : x = 0 := hx0.symm
    subst x
    change
      |deriv (fun y : ℝ =>
          -BFormPositiveDatumNegPart.negativePartLift w y) 0| ≤ G
    rw [deriv_neg_negativePartLift_eq_zero_at_zero, abs_zero]
    exact hG_nonneg

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
  let SD : TruncatedConjugateMildSolutionData p u₀ :=
    truncatedConjugateMildSolutionData_of_data DT
  exact
    truncatedChemFluxLifted_continuousOn_of_abs_ball
      (p := p) (w := (truncatedConjugatePicardLimit p u₀ DT.T) t)
      (M := SD.M) SD.hM
      (SD.hcont t ht htT)
      (SD.hbound t ht htT)

private theorem truncatedChemFluxLifted_hasDerivAt_of_lift_hasDerivAt_not_bad
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M) {y : ℝ}
    (hyIoo : y ∈ Set.Ioo (0 : ℝ) 1)
    (hw_has : HasDerivAt (intervalDomainLift w)
      (deriv (intervalDomainLift w) y) y)
    (hnot_bad :
      intervalDomainLift w y = 0 → deriv (intervalDomainLift w) y = 0) :
    HasDerivAt (truncatedChemFluxLifted p w)
      (deriv (truncatedChemFluxLifted p w) y) y := by
  classical
  let R : ℝ → ℝ :=
    fun z => intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) z
  let g : ℝ → ℝ := fun z => resolverGradReal p w z
  let a : ℝ → ℝ := fun z => positivePart (intervalDomainLift w z)
  let q : ℝ → ℝ := fun z => (1 + R z) ^ (-p.β)
  have hflux_eq : truncatedChemFluxLifted p w =
      fun z => a z * g z * q z := by
    funext z
    have hR_nonneg : 0 ≤ R z := by
      simpa [R] using resolverR_lift_nonneg_of_abs_ball
        (p := p) (w := w) (M := M) hM hw_cont hball z
    have hbase_nonneg : 0 ≤ 1 + R z := by linarith
    unfold truncatedChemFluxLifted
    rw [div_eq_mul_inv, ← Real.rpow_neg hbase_nonneg]
  obtain ⟨dpos, ha_has⟩ :=
    positivePart_comp_hasDerivAt_of_hasDerivAt_not_bad hw_has hnot_bad
  obtain ⟨_src, hg_raw, _hsrc⟩ :=
    resolverGradReal_hasDerivAt_signed_ellipticBound_of_abs_ball
      (p := p) (w := w) (M := M) hM hw_cont hball hyIoo
  have hg_has : HasDerivAt g (deriv g y) y := by
    simpa [g, hg_raw.deriv] using hg_raw
  have hUcont : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) :=
    lift_continuousOn_Icc_of_continuous hw_cont
  have hR_has : HasDerivAt R (g y) y := by
    simpa [R, g] using
      ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverR_lift_hasDerivAt_resolverGradReal_of_continuousOn
        (p := p) (u := w) hUcont hyIoo
  have hbase_has : HasDerivAt (fun z : ℝ => 1 + R z) (g y) y :=
    hR_has.const_add 1
  have hR_nonneg_y : 0 ≤ R y := by
    simpa [R] using resolverR_lift_nonneg_of_abs_ball
      (p := p) (w := w) (M := M) hM hw_cont hball y
  have hbase_pos : 0 < 1 + R y := by linarith
  have hq_has :
      HasDerivAt q (g y * (-p.β) * (1 + R y) ^ (-p.β - 1)) y := by
    simpa [q, sub_eq_add_neg] using
      hbase_has.rpow_const (p := -p.β) (Or.inl (ne_of_gt hbase_pos))
  have hag_has : HasDerivAt (fun z : ℝ => a z * g z)
      (dpos * g y + a y * deriv g y) y := by
    simpa using ha_has.mul hg_has
  have hprod_has : HasDerivAt (fun z : ℝ => a z * g z * q z)
      ((dpos * g y + a y * deriv g y) * q y
        + (a y * g y) * (g y * (-p.β) * (1 + R y) ^ (-p.β - 1))) y := by
    simpa only [Pi.mul_apply] using hag_has.mul hq_has
  have hflux_has : HasDerivAt (truncatedChemFluxLifted p w)
      ((dpos * g y + a y * deriv g y) * q y
        + (a y * g y) * (g y * (-p.β) * (1 + R y) ^ (-p.β - 1))) y := by
    rw [hflux_eq]
    exact hprod_has
  rw [hflux_has.deriv]
  exact hflux_has

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
  let w : intervalDomainPoint → ℝ :=
    (truncatedConjugatePicardLimit p u₀ DT.T) t
  let SD : TruncatedConjugateMildSolutionData p u₀ :=
    truncatedConjugateMildSolutionData_of_data DT
  have hdiff_Ioo :
      ∀ x ∈ Ioo (0 : ℝ) 1,
        DifferentiableAt ℝ (intervalDomainLift w) x := by
    intro x hx
    simpa [w] using
      (truncatedPicardLimit_level5_series_reconstruction_positive_time
        DT ht htT).2.2 x hx
  have hball : ∀ x : intervalDomainPoint, |w x| ≤ SD.M := by
    intro x
    simpa [w, SD] using SD.hbound t ht htT x
  have hw_cont : Continuous w := by
    simpa [w, SD] using SD.hcont t ht htT
  let s_chem : Set ℝ := transversalZeroSet (intervalDomainLift w)
  refine ⟨s_chem, ?_, ?_⟩
  · exact transversalZeroSet_countable_of_differentiableAt
      (f := intervalDomainLift w) hdiff_Ioo
  · intro x hx
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := hx.1
    have hx_not_s : x ∉ s_chem := hx.2
    have hw_has :
        HasDerivAt (intervalDomainLift w)
          (deriv (intervalDomainLift w) x) x :=
      (hdiff_Ioo x hxIoo).hasDerivAt
    have hnot_bad :
        intervalDomainLift w x = 0 →
          deriv (intervalDomainLift w) x = 0 := by
      intro hzero
      by_contra hne
      exact hx_not_s ⟨hxIoo, hzero, hne⟩
    simpa [w] using
      truncatedChemFluxLifted_hasDerivAt_of_lift_hasDerivAt_not_bad
        (p := p) (w := w) (M := SD.M) SD.hM hw_cont hball
        hxIoo hw_has hnot_bad

/-- Bounded derivative of the truncated chemotaxis flux.  From bounded
gradient of `u`, resolver bounds, and the product rule. -/
theorem truncatedChemFlux_deriv_bound_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    ∃ C_chem : ℝ, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (truncatedChemFluxLifted p
        ((truncatedConjugatePicardLimit p u₀ DT.T) t)) x| ≤ C_chem := by
  classical
  let w : intervalDomainPoint → ℝ :=
    (truncatedConjugatePicardLimit p u₀ DT.T) t
  let SD : TruncatedConjugateMildSolutionData p u₀ :=
    truncatedConjugateMildSolutionData_of_data DT
  obtain ⟨G, hG_nonneg, hG_Icc⟩ :=
    truncatedPicardLimit_gradient_bound_positive_time DT ht htT
  have hdiff_Ioo :
      ∀ x ∈ Ioo (0 : ℝ) 1,
        DifferentiableAt ℝ (intervalDomainLift w) x := by
    intro x hx
    simpa [w] using
      (truncatedPicardLimit_level5_series_reconstruction_positive_time
        DT ht htT).2.2 x hx
  have hball : ∀ x : intervalDomainPoint, |w x| ≤ SD.M := by
    intro x
    simpa [w, SD] using SD.hbound t ht htT x
  have hw_cont : Continuous w := by
    simpa [w, SD] using SD.hcont t ht htT
  have hgrad_all : ∀ x : ℝ, |deriv (intervalDomainLift w) x| ≤ G := by
    intro x
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · simpa [w] using hG_Icc x hx
    · have hx_out : x < 0 ∨ 1 < x := by
        by_cases hx0 : 0 ≤ x
        · right
          exact lt_of_not_ge (fun hx1 : x ≤ 1 => hx ⟨hx0, hx1⟩)
        · left
          exact lt_of_not_ge hx0
      rcases hx_out with hxlt | hxgt
      · let Uconst : ℝ → intervalDomainPoint → ℝ := fun _ => w
        have hzero : deriv (intervalDomainLift w) x = 0 := by
          simpa [Uconst] using
            (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_on_Iio
              Uconst 0 hxlt)
        rw [hzero, abs_zero]
        exact hG_nonneg
      · let Uconst : ℝ → intervalDomainPoint → ℝ := fun _ => w
        have hzero : deriv (intervalDomainLift w) x = 0 := by
          simpa [Uconst] using
            (ShenWork.Paper2.CompactSliceGradientBounds.deriv_lift_eq_zero_on_Ioi
              Uconst 0 hxgt)
        rw [hzero, abs_zero]
        exact hG_nonneg
  let Γ_M : ℝ := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
      * (2 * (p.ν * SD.M ^ p.γ))
  let V_M : ℝ := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2)
      * (2 * (p.ν * SD.M ^ p.γ))
  let H_M : ℝ := p.μ * V_M + p.ν * SD.M ^ p.γ
  let C_chem : ℝ := (SD.M * H_M + p.β * SD.M * Γ_M ^ 2) + Γ_M * G
  have hΓ_M_nonneg : 0 ≤ Γ_M := by
    dsimp [Γ_M]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg (le_of_lt p.hν) (Real.rpow_nonneg SD.hM.le _)))
  have hV_M_nonneg : 0 ≤ V_M := by
    dsimp [V_M]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg (le_of_lt p.hν) (Real.rpow_nonneg SD.hM.le _)))
  have hH_M_nonneg : 0 ≤ H_M := by
    dsimp [H_M]
    exact add_nonneg
      (mul_nonneg (le_of_lt p.hμ) hV_M_nonneg)
      (mul_nonneg (le_of_lt p.hν) (Real.rpow_nonneg SD.hM.le _))
  have hC_nonneg : 0 ≤ C_chem := by
    dsimp [C_chem]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg SD.hM.le hH_M_nonneg)
        (mul_nonneg (mul_nonneg p.hβ SD.hM.le) (sq_nonneg Γ_M)))
      (mul_nonneg hΓ_M_nonneg hG_nonneg)
  refine ⟨C_chem, ?_⟩
  intro x hx
  change |deriv (truncatedChemFluxLifted p w) x| ≤ C_chem
  by_cases hxIoo : x ∈ Ioo (0 : ℝ) 1
  · have hdiff_pos :
        0 < intervalDomainLift w x →
          DifferentiableAt ℝ (intervalDomainLift w) x := by
      intro _hpos
      exact hdiff_Ioo x hxIoo
    obtain ⟨dpos, gp, q, qDen, hderiv, hdpos, hgradR, hgp, hq, hqDen⟩ :
        ∃ dpos gp q qDen : ℝ,
          deriv (truncatedChemFluxLifted p w) x =
            dpos * resolverGradReal p w x * q
              + positivePart (intervalDomainLift w x) * gp * q
              - p.β * positivePart (intervalDomainLift w x)
                  * (resolverGradReal p w x) ^ 2 * qDen
          ∧ |dpos| ≤ |deriv (intervalDomainLift w) x|
          ∧ |resolverGradReal p w x| ≤ Γ_M
          ∧ |gp| ≤ H_M
          ∧ |q| ≤ 1
          ∧ |qDen| ≤ 1 := by
      simpa [Γ_M, V_M, H_M] using
        truncatedChemFluxLifted_deriv_terms_of_abs_ball
          (p := p) (w := w) (M := SD.M) SD.hM
          hw_cont hball x hdiff_pos
    simpa [C_chem] using
      truncatedChemFluxLifted_deriv_abs_le_of_ball_grad
        (p := p) (w := w) (M := SD.M) (Γ := Γ_M)
        (H := H_M) (G := G)
        SD.hM hball hgrad_all x
        hderiv hdpos hgradR hgp hq hqDen
  · have hzero :
        deriv (truncatedChemFluxLifted p w) x = 0 :=
      truncatedChemFluxLifted_deriv_eq_zero_off_Ioo
        (p := p) (w := w) hxIoo
    rw [hzero, abs_zero]
    exact hC_nonneg

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
  exact
    (truncatedPicardLimit_level5_series_reconstruction_positive_time
      DT ht htT).1

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
  exact
    (truncatedPicardLimit_level5_series_reconstruction_positive_time
      DT ht htT).2.1

/-! ## Level 5b: Tested summability (bilinear products) -/

private theorem negativePartTest_abs_le_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |negativePartTest (truncatedConjugatePicardLimit p u₀ DT.T) t x| ≤ DT.M := by
  intro x hx
  have hbound :=
    (truncatedConjugateMildSolutionData_of_data DT).hbound t ht htT ⟨x, hx⟩
  have hval :
      intervalDomainLift ((truncatedConjugatePicardLimit p u₀ DT.T) t) x =
        (truncatedConjugatePicardLimit p u₀ DT.T) t ⟨x, hx⟩ := by
    simp [intervalDomainLift, hx]
  simp only [negativePartTest, BFormPositiveDatumNegPart.negativePartLift, abs_neg]
  rw [hval]
  set r := (truncatedConjugatePicardLimit p u₀ DT.T) t ⟨x, hx⟩ with hr
  have hneg : |BFormPositiveDatumNegPart.negativePart r| ≤ |r| := by
    by_cases hr_nonneg : 0 ≤ r
    · simp [BFormPositiveDatumNegPart.negativePart_eq_zero_of_nonneg hr_nonneg]
    · have hr_nonpos : r ≤ 0 := le_of_lt (lt_of_not_ge hr_nonneg)
      simp [BFormPositiveDatumNegPart.negativePart_eq_neg_of_nonpos hr_nonpos, abs_neg]
  exact hneg.trans hbound

private theorem cosineTestCoeff_abs_le_of_bound
    {φ : ℝ → ℝ} {B : ℝ}
    (hφ : ∀ x ∈ Set.Icc (0 : ℝ) 1, |φ x| ≤ B) :
    ∀ k : ℕ, |cosineTestCoeff φ k| ≤ B := by
  intro k
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := B)
    (f := fun x : ℝ => cosineMode k x * φ x)
    (fun x hx => by
      rw [Real.norm_eq_abs, abs_mul]
      have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
        have hx_uIcc : x ∈ Set.uIcc (0 : ℝ) 1 := Set.uIoc_subset_uIcc hx
        rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx_uIcc
      have hcos : |cosineMode k x| ≤ 1 := by
        simpa [cosineMode] using
          Real.abs_cos_le_one ((k : ℝ) * Real.pi * x)
      calc
        |cosineMode k x| * |φ x| ≤ 1 * |φ x| :=
          mul_le_mul_of_nonneg_right hcos (abs_nonneg _)
        _ ≤ B := by simpa using hφ x hxIcc)
  simpa [cosineTestCoeff, Real.norm_eq_abs] using hnorm

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
  let U := truncatedConjugatePicardLimit p u₀ DT.T
  change Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        truncatedPicardCoeff p u₀ U t k *
        cosineTestCoeff (negativePartTest U t) k)
  have hcoeff :=
    truncatedPicardCoeff_eigenvalue_weighted_summable_positive_time DT ht htT
  have htest : ∀ k : ℕ, |cosineTestCoeff (negativePartTest U t) k| ≤ DT.M :=
    cosineTestCoeff_abs_le_of_bound
      (negativePartTest_abs_le_positive_time (DT := DT) ht htT)
  have hmajor : Summable (fun k : ℕ =>
      (unitIntervalCosineEigenvalue k *
        |truncatedPicardCoeff p u₀ U t k|) * DT.M) := by
    simpa [U] using hcoeff.mul_right DT.M
  have habs : Summable (fun k : ℕ =>
      |unitIntervalCosineEigenvalue k *
        truncatedPicardCoeff p u₀ U t k *
        cosineTestCoeff (negativePartTest U t) k|) := by
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) hmajor
    have hlam : 0 ≤ unitIntervalCosineEigenvalue k := by
      unfold unitIntervalCosineEigenvalue
      positivity
    calc
      |unitIntervalCosineEigenvalue k *
          truncatedPicardCoeff p u₀ U t k *
          cosineTestCoeff (negativePartTest U t) k|
          =
        (unitIntervalCosineEigenvalue k *
          |truncatedPicardCoeff p u₀ U t k|) *
          |cosineTestCoeff (negativePartTest U t) k| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hlam]
      _ ≤ (unitIntervalCosineEigenvalue k *
          |truncatedPicardCoeff p u₀ U t k|) * DT.M :=
            mul_le_mul_of_nonneg_left (htest k)
              (mul_nonneg hlam (abs_nonneg _))
  refine Summable.of_norm ?_
  simpa [Real.norm_eq_abs] using habs

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
  let U := truncatedConjugatePicardLimit p u₀ DT.T
  change Summable (fun k : ℕ =>
      truncatedBFormSourceCoeff p U t k *
        cosineTestCoeff (negativePartTest U t) k)
  have hsrc := truncatedBFormSourceCoeff_summable_positive_time DT ht htT
  have htest : ∀ k : ℕ, |cosineTestCoeff (negativePartTest U t) k| ≤ DT.M :=
    cosineTestCoeff_abs_le_of_bound
      (negativePartTest_abs_le_positive_time (DT := DT) ht htT)
  have hmajor : Summable (fun k : ℕ =>
      |truncatedBFormSourceCoeff p U t k| * DT.M) := by
    simpa [U] using hsrc.mul_right DT.M
  have habs : Summable (fun k : ℕ =>
      |truncatedBFormSourceCoeff p U t k *
        cosineTestCoeff (negativePartTest U t) k|) := by
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) hmajor
    calc
      |truncatedBFormSourceCoeff p U t k *
        cosineTestCoeff (negativePartTest U t) k|
          =
        |truncatedBFormSourceCoeff p U t k| *
          |cosineTestCoeff (negativePartTest U t) k| := by
            rw [abs_mul]
      _ ≤ |truncatedBFormSourceCoeff p U t k| * DT.M :=
            mul_le_mul_of_nonneg_left (htest k) (abs_nonneg _)
  refine Summable.of_norm ?_
  simpa [Real.norm_eq_abs] using habs

end ShenWork.Paper2.TruncatedPositiveTimeBootstrap
