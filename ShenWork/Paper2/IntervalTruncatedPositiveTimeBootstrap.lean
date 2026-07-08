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
import ShenWork.Paper2.IntervalTruncatedGradientWindow
import ShenWork.Paper2.IntervalTruncatedLeftProfileWiring
import ShenWork.Paper2.IntervalTruncatedPositiveTimeGradientAtoms
import ShenWork.PDE.CosineSpectrum
import ShenWork.Wiener.EWA.SourceRealizesRecords

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
open ShenWork.Paper2.TruncatedGradientWindow

/-! ## Helper: truncated logistic local bound -/

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
    |deriv (truncatedChemFluxLifted p w) y| ≤
      (M * H + p.β * M * Γ ^ 2) + Γ * G := by
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
    (_hM : 0 < M) (_hw_cont : Continuous w)
    (_hball : ∀ x : intervalDomainPoint, |w x| ≤ M) (y : ℝ) :
    |resolverGradReal p w y| ≤
      Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
        * (2 * (p.ν * M ^ p.γ)) := by
  sorry

private theorem resolverGrad_deriv_abs_le_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (_hM : 0 < M) (_hw_cont : Continuous w)
    (_hball : ∀ x : intervalDomainPoint, |w x| ≤ M) (y : ℝ) :
    |deriv (fun z : ℝ => resolverGradReal p w z) y| ≤
      p.μ * (Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2)
          * (2 * (p.ν * M ^ p.γ)))
        + p.ν * M ^ p.γ := by
  sorry

private theorem resolverR_lift_nonneg_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (_hM : 0 < M) (_hw_cont : Continuous w)
    (_hball : ∀ x : intervalDomainPoint, |w x| ≤ M) (y : ℝ) :
    0 ≤ intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y := by
  sorry

private theorem truncatedChemFluxLifted_deriv_product_rule_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (_hM : 0 < M) (_hw_cont : Continuous w)
    (_hball : ∀ x : intervalDomainPoint, |w x| ≤ M) (y : ℝ) :
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
  sorry

private theorem truncatedChemFluxLifted_deriv_terms_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M) (y : ℝ) :
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
  obtain ⟨dpos, gp, hderiv, hdpos, hgp_eq⟩ :=
    truncatedChemFluxLifted_deriv_product_rule_of_abs_ball
      (p := p) (w := w) (M := M) hM hw_cont hball y
  let q : ℝ :=
    (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ (-p.β)
  let qDen : ℝ :=
    (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ (-p.β - 1)
  refine ⟨dpos, gp, q, qDen, ?_, hdpos, ?_, ?_, ?_, ?_⟩
  · simpa [q, qDen] using hderiv
  · exact resolverGrad_abs_le_of_abs_ball
      (p := p) (w := w) (M := M) hM hw_cont hball y
  · rw [hgp_eq]
    exact resolverGrad_deriv_abs_le_of_abs_ball
      (p := p) (w := w) (M := M) hM hw_cont hball y
  · have hR_nonneg :
        0 ≤ intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y :=
      resolverR_lift_nonneg_of_abs_ball
        (p := p) (w := w) (M := M) hM hw_cont hball y
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
  · have hR_nonneg :
        0 ≤ intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y :=
      resolverR_lift_nonneg_of_abs_ball
        (p := p) (w := w) (M := M) hM hw_cont hball y
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
              dsimp only [Mw]
              exact truncatedConjugatePicardIter_zero_left_profile
                (p := p) (u₀ := u₀) DT U (by intro n s; rfl)
                hAL_nn hAF_nn hΓ_M_nn
                (by dsimp [lo]; linarith) hleftContr
            have source : ∀ n, IterGradLeftProfile U Mw A_L A_F B_F p.χ₀ lo n →
                ∀ s, 0 < s → s ≤ lo → ∀ y,
                  |Src n s y| ≤ truncLeftSourceConst A_L A_F p.χ₀ +
                    truncLeftBeta B_F p.χ₀ * truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s := by
              sorry
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
            · -- |flux'| ≤ A_F + B_F * G (product rule on truncatedChemFluxLifted)
              -- Uses: |positivePart'| ≤ 1, IterGradOnWindow giving |u'| ≤ G,
              -- resolver gradient ≤ Γ_M, resolver second deriv ≤ H_M,
              -- (1+R)^β ≥ 1
              dsimp only [A_F, B_F]
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
                simpa [Γ_M, H_M, V_M] using
                  truncatedChemFluxLifted_deriv_terms_of_abs_ball
                    (p := p) (w := U n s) (M := DT.M) DT.hM
                    (hball_cont.2 s hs_pos hs_T) hball y
              rcases hflux_terms with
                ⟨dpos, gp, q, qDen, hderiv, hdpos, hgradR, hgp, hq, hqDen⟩
              exact truncatedChemFluxLifted_deriv_abs_le_of_ball_grad
                (p := p) (w := U n s) (M := DT.M) (Γ := Γ_M)
                (H := H_M) (G := Gw) DT.hM hball
                (hgrad s ha_s hs_hi).1 y hderiv hdpos hgradR hgp hq hqDen
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
  have hcont_lift : ContinuousOn (intervalDomainLift (u s)) (Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have hres : Set.restrict (Icc (0 : ℝ) 1) (intervalDomainLift (u s)) = u s := by
      funext ⟨z, hz⟩
      show intervalDomainLift (u s) z = u s ⟨z, hz⟩
      rw [intervalDomainLift, dif_pos hz]
    rw [hres]; exact hcont_slice
  -- Part 1: logistic bound
  have ⟨CL, hCL, hlog⟩ := truncatedLogisticSourceCoeff_bound_of_sup (p := p) DT.hM hcont_lift hball
  -- Part 2: chemDiv bound (Lipschitz → flux W^{1,1} → IBP → bounded)
  have ⟨CC, hCC, hchem⟩ : ∃ CC : ℝ, 0 ≤ CC ∧ ∀ k,
      |truncatedChemDivSourceCoeff p u s k| ≤ CC := by
    have _hlip := truncatedPicardLimit_lipschitzOn_positive_time DT hs hsT sorry
    sorry
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
