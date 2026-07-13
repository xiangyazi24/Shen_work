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
import ShenWork.Paper2.IntervalTruncatedGradientWindowChain
import ShenWork.Paper2.IntervalTruncatedChemFluxBound
import ShenWork.Paper2.IntervalTruncatedLeftProfileWiring
import ShenWork.Paper2.IntervalTruncatedPositiveTimeGradientAtoms
import ShenWork.Paper2.IntervalTruncatedWindowLipschitzLimit
import ShenWork.Paper2.IntervalTransversalZeroSet
import ShenWork.PDE.CosineSpectrum

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

private theorem intervalDomainLift_continuousAt_of_continuous_of_mem_Ioo'
    {w : intervalDomainPoint → ℝ} (hw : Continuous w)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousAt (intervalDomainLift w) x := by
  have hUcont : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) :=
    lift_continuousOn_Icc_of_continuous hw
  have hIcc_nhds : Set.Icc (0 : ℝ) 1 ∈ 𝓝 x :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hx) Set.Ioo_subset_Icc_self
  exact hUcont.continuousAt hIcc_nhds

private theorem hasDerivAt_mul_zero_of_continuousAt_zero_hasDerivAt_zero
    {a b : ℝ → ℝ} {x b' : ℝ}
    (ha : ContinuousAt a x) (hax : a x = 0)
    (hb : HasDerivAt b b' x) (hbx : b x = 0) :
    HasDerivAt (fun y : ℝ => a y * b y) 0 x := by
  rw [hasDerivAt_iff_isLittleO]
  have ha_o : a =o[𝓝 x] (fun _ : ℝ => (1 : ℝ)) := by
    refine (isLittleO_one_iff ℝ).2 ?_
    rw [← hax]
    exact ha
  have hb_O : b =O[𝓝 x] fun y : ℝ => y - x := by
    simpa [hbx] using hb.isBigO_sub
  have hmul : (fun y : ℝ => a y * b y) =o[𝓝 x] fun y : ℝ => y - x := by
    simpa using ha_o.mul_isBigO hb_O
  simpa [hax, hbx] using hmul

private theorem positivePart_le_abs' (r : ℝ) :
    positivePart r ≤ |r| := by
  by_cases hr : 0 ≤ r
  · simp [positivePart, hr, abs_of_nonneg hr]
  · have hr' : r ≤ 0 := le_of_not_ge hr
    simp [positivePart, hr', abs_of_nonpos hr']

private theorem positivePart_slice_continuous
    {w : intervalDomainPoint → ℝ} (hw_cont : Continuous w) :
    Continuous (fun x => positivePart (w x)) := by
  simpa [positivePart] using hw_cont.max continuous_const

private theorem positivePart_slice_abs_le_of_abs_ball
    {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M) :
    ∀ x : intervalDomainPoint, |positivePart (w x)| ≤ M := by
  intro x
  rw [abs_of_nonneg (positivePart_nonneg (w x))]
  exact (positivePart_le_abs' (w x)).trans (hball x)

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
    {M Γ H G Q QDen : ℝ}
    (hM : 0 < M)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M)
    (hgrad : ∀ x : ℝ, |deriv (intervalDomainLift w) x| ≤ G)
    (y : ℝ)
    {dpos gp q qDen : ℝ}
    (hderiv :
      deriv (truncatedChemFluxLifted p w) y =
        dpos * resolverGradReal p (fun x => positivePart (w x)) y * q
          + positivePart (intervalDomainLift w y) * gp * q
          - p.β * positivePart (intervalDomainLift w y)
              * (resolverGradReal p (fun x => positivePart (w x)) y) ^ 2 * qDen)
    (hdpos : |dpos| ≤ |deriv (intervalDomainLift w) y|)
    (hgradR : |resolverGradReal p (fun x => positivePart (w x)) y| ≤ Γ)
    (hgp : |gp| ≤ H)
    (hq : |q| ≤ Q)
    (hqDen : |qDen| ≤ QDen) :
    (|deriv (truncatedChemFluxLifted p w) y| ≤
      (M * H * Q + p.β * M * Γ ^ 2 * QDen) + Γ * G * Q) := by
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
    (abs_nonneg (resolverGradReal p (fun x => positivePart (w x)) y)).trans hgradR
  have hH_nonneg : 0 ≤ H := (abs_nonneg gp).trans hgp
  have hterm₁ :
      |dpos * resolverGradReal p (fun x => positivePart (w x)) y * q| ≤
        Γ * G * Q := by
    have hprod :
        |dpos| * |resolverGradReal p (fun x => positivePart (w x)) y| ≤ G * Γ :=
      mul_le_mul hdG hgradR (abs_nonneg _) hG_nonneg
    calc
      |dpos * resolverGradReal p (fun x => positivePart (w x)) y * q|
          = |dpos| * |resolverGradReal p (fun x => positivePart (w x)) y| * |q| := by
            rw [abs_mul, abs_mul]
      _ ≤ G * Γ * Q :=
            mul_le_mul hprod hq (abs_nonneg _)
              (mul_nonneg hG_nonneg hΓ_nonneg)
      _ = Γ * G * Q := by ring
  have hterm₂ :
      |positivePart (intervalDomainLift w y) * gp * q| ≤ M * H * Q := by
    have hprod :
        |positivePart (intervalDomainLift w y)| * |gp| ≤ M * H :=
      mul_le_mul hUpos_abs hgp (abs_nonneg _) hM.le
    calc
      |positivePart (intervalDomainLift w y) * gp * q|
          = |positivePart (intervalDomainLift w y)| * |gp| * |q| := by
            rw [abs_mul, abs_mul]
      _ ≤ M * H * Q :=
            mul_le_mul hprod hq (abs_nonneg _)
              (mul_nonneg hM.le hH_nonneg)
      _ = M * H * Q := by ring
  have hgradR_sq :
      |resolverGradReal p (fun x => positivePart (w x)) y| ^ 2 ≤ Γ ^ 2 := by
    nlinarith [hgradR,
      abs_nonneg (resolverGradReal p (fun x => positivePart (w x)) y), hΓ_nonneg,
      sq_nonneg (Γ - |resolverGradReal p (fun x => positivePart (w x)) y|)]
  have hterm₃ :
      |p.β * positivePart (intervalDomainLift w y)
          * (resolverGradReal p (fun x => positivePart (w x)) y) ^ 2 * qDen|
        ≤ p.β * M * Γ ^ 2 * QDen := by
    have hβU :
        p.β * |positivePart (intervalDomainLift w y)| ≤ p.β * M :=
      mul_le_mul_of_nonneg_left hUpos_abs p.hβ
    have hβU_nonneg :
        0 ≤ p.β * |positivePart (intervalDomainLift w y)| :=
      mul_nonneg p.hβ (abs_nonneg _)
    have hβUg :
        p.β * |positivePart (intervalDomainLift w y)|
            * |resolverGradReal p (fun x => positivePart (w x)) y| ^ 2
          ≤ p.β * M * Γ ^ 2 :=
      mul_le_mul hβU hgradR_sq (sq_nonneg _)
        (mul_nonneg p.hβ hM.le)
    have hβMg_nonneg : 0 ≤ p.β * M * Γ ^ 2 :=
      mul_nonneg (mul_nonneg p.hβ hM.le) (sq_nonneg _)
    have hsq_abs :
        |(resolverGradReal p (fun x => positivePart (w x)) y) ^ 2|
          = |resolverGradReal p (fun x => positivePart (w x)) y| ^ 2 := by
      rw [pow_two, abs_mul, pow_two]
    calc
      |p.β * positivePart (intervalDomainLift w y)
          * (resolverGradReal p (fun x => positivePart (w x)) y) ^ 2 * qDen|
          = p.β * |positivePart (intervalDomainLift w y)|
              * |resolverGradReal p (fun x => positivePart (w x)) y| ^ 2 * |qDen| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg p.hβ, hsq_abs]
      _ ≤ p.β * M * Γ ^ 2 * QDen :=
            mul_le_mul hβUg hqDen (abs_nonneg _) hβMg_nonneg
      _ = p.β * M * Γ ^ 2 * QDen := by ring
  set A : ℝ := dpos * resolverGradReal p (fun x => positivePart (w x)) y * q
  set B : ℝ := positivePart (intervalDomainLift w y) * gp * q
  set C : ℝ :=
    p.β * positivePart (intervalDomainLift w y)
      * (resolverGradReal p (fun x => positivePart (w x)) y) ^ 2 * qDen
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
    _ ≤ Γ * G * Q + M * H * Q + p.β * M * Γ ^ 2 * QDen := by
          exact add_le_add (add_le_add hterm₁ hterm₂) hterm₃
    _ = (M * H * Q + p.β * M * Γ ^ 2 * QDen) + Γ * G * Q := by ring

private theorem truncatedChemFluxLifted_deriv_eq_zero_off_Ioo
    (p : CM2Params) (w : intervalDomainPoint → ℝ) {y : ℝ}
    (hy : y ∉ Set.Ioo (0 : ℝ) 1) :
    deriv (truncatedChemFluxLifted p w) y = 0 := by
  let F : intervalDomainPoint → ℝ := fun x =>
    positivePart (w x) * resolverGradReal p (fun z => positivePart (w z)) x.1
      / (1 + intervalDomainLift
          (ShenWork.PDE.intervalNeumannResolverR p
            (fun z => positivePart (w z))) x.1) ^ p.β
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
  `positivePart(lift w) * resolverGradReal p wPos / (1 + lift(R wPos))^β`;
* the `positivePart` Lipschitz derivative bound;
* resolver gradient and physical Hessian bounds from the absolute `M`-ball;
* denominator bounds from unconditional resolver nonnegativity for
  `wPos := positivePart ∘ w`. -/
private theorem resolverGrad_abs_le_of_abs_ball_legacy
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

private theorem resolverValueSeries_abs_le_of_abs_ball_legacy
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

private theorem resolverR_lift_abs_le_of_abs_ball_legacy
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M)
    (y : ℝ) :
    |intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y| ≤
      Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2)
          * (2 * (p.ν * M ^ p.γ)) := by
  classical
  let V : ℝ := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2)
      * (2 * (p.ν * M ^ p.γ))
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · simpa [V, intervalDomainLift, hy, ShenWork.PDE.intervalNeumannResolverR,
      unitIntervalCosineMode] using
      resolverValueSeries_abs_le_of_abs_ball
        (p := p) (w := w) (M := M) hM hw_cont hball y
  · simp [V, intervalDomainLift, hy]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM.le _)))

private theorem resolverR_lift_one_add_pos_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ}
    (hw_cont : Continuous w)
    (y : ℝ) :
    0 < 1 + intervalDomainLift
      (ShenWork.PDE.intervalNeumannResolverR p
        (fun x => positivePart (w x))) y := by
  have hR_nonneg :=
    resolverR_positivePart_lift_nonneg_of_continuous p hw_cont y
  linarith

private theorem resolverR_lift_one_add_nonneg_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ}
    (hw_cont : Continuous w)
    (y : ℝ) :
    0 ≤ 1 + intervalDomainLift
      (ShenWork.PDE.intervalNeumannResolverR p
        (fun x => positivePart (w x))) y :=
  (resolverR_lift_one_add_pos_of_abs_ball
    (p := p) (w := w) hw_cont y).le

private theorem truncatedChemFluxLifted_deriv_zero_of_lift_nonpos_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M)
    {y : ℝ}
    (hy_nonpos : intervalDomainLift w y ≤ 0) :
    deriv (truncatedChemFluxLifted p w) y = 0 := by
  classical
  let wPos : intervalDomainPoint → ℝ := fun x => positivePart (w x)
  have hwPos_cont : Continuous wPos := by
    simpa [wPos] using positivePart_slice_continuous hw_cont
  have hwPos_ball : ∀ x : intervalDomainPoint, |wPos x| ≤ M := by
    simpa [wPos] using positivePart_slice_abs_le_of_abs_ball hball
  by_cases hyIoo : y ∈ Set.Ioo (0 : ℝ) 1
  · have hw_lift_cont :
        ContinuousAt (intervalDomainLift w) y :=
      intervalDomainLift_continuousAt_of_continuous_of_mem_Ioo' hw_cont hyIoo
    by_cases hy_neg : intervalDomainLift w y < 0
    · have hneg_ev :
          ∀ᶠ z in 𝓝 y, intervalDomainLift w z < 0 :=
        hw_lift_cont.tendsto.eventually (isOpen_Iio.mem_nhds hy_neg)
      have hflux_zero_ev :
          truncatedChemFluxLifted p w =ᶠ[𝓝 y] fun _ : ℝ => 0 := by
        filter_upwards [hneg_ev] with z hz
        simp [truncatedChemFluxLifted, positivePart_eq_zero_of_nonpos hz.le]
      rw [hflux_zero_ev.deriv_eq]
      simp
    · have hy_zero : intervalDomainLift w y = 0 :=
        le_antisymm hy_nonpos (le_of_not_gt hy_neg)
      let R : ℝ → ℝ :=
        fun z => intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p wPos) z
      let g : ℝ → ℝ := fun z => resolverGradReal p wPos z
      let a : ℝ → ℝ := fun z => positivePart (intervalDomainLift w z)
      let den : ℝ → ℝ := fun z => (1 + R z) ^ p.β
      let A : ℝ → ℝ := fun z => g z / den z
      have hflux_eq : truncatedChemFluxLifted p w =
          fun z : ℝ => a z * A z := by
        funext z
        simp [truncatedChemFluxLifted, a, A, den, g, R, wPos, mul_div_assoc]
      have hbase_pos : 0 < 1 + R y := by
        simpa [R] using resolverR_lift_one_add_pos_of_abs_ball
          (p := p) (w := w) hw_cont y
      obtain ⟨_src, hg_raw, _hsrc⟩ :=
        resolverGradReal_hasDerivAt_signed_ellipticBound_of_abs_ball
          (p := p) (w := wPos) (M := M) hM hwPos_cont hwPos_ball hyIoo
      have hg_has : HasDerivAt g (deriv g y) y := by
        simpa [g, hg_raw.deriv] using hg_raw
      have hUcont : ContinuousOn (intervalDomainLift wPos) (Set.Icc (0 : ℝ) 1) :=
        lift_continuousOn_Icc_of_continuous hwPos_cont
      have hR_has : HasDerivAt R (g y) y := by
        simpa [R, g] using
          ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverR_lift_hasDerivAt_resolverGradReal_of_continuousOn
            (p := p) (u := wPos) hUcont hyIoo
      have hbase_has : HasDerivAt (fun z : ℝ => 1 + R z) (g y) y :=
        hR_has.const_add 1
      have hden_has : HasDerivAt den
          (g y * p.β * (1 + R y) ^ (p.β - 1)) y := by
        simpa [den, sub_eq_add_neg] using
          hbase_has.rpow_const (p := p.β) (Or.inl (ne_of_gt hbase_pos))
      have hden_ne : den y ≠ 0 := by
        dsimp [den]
        exact ne_of_gt (Real.rpow_pos_of_pos hbase_pos p.β)
      have hA_has_exists : ∃ A' : ℝ, HasDerivAt A A' y := by
        exact ⟨_, hg_has.div hden_has hden_ne⟩
      obtain ⟨A', hA_has⟩ := hA_has_exists
      have hA_cont : ContinuousAt A y := hA_has.continuousAt
      by_cases hA_pos : 0 < A y
      · have hA_pos_ev : ∀ᶠ z in 𝓝 y, 0 < A z :=
          hA_cont.tendsto.eventually (isOpen_Ioi.mem_nhds hA_pos)
        have hmin : IsLocalMin (truncatedChemFluxLifted p w) y := by
          unfold IsLocalMin IsMinFilter
          filter_upwards [hA_pos_ev] with z hz
          have hz_nonneg : 0 ≤ truncatedChemFluxLifted p w z := by
            rw [hflux_eq]
            exact mul_nonneg (positivePart_nonneg _) hz.le
          have hy_val : truncatedChemFluxLifted p w y = 0 := by
            rw [hflux_eq]
            simp [a, hy_zero,
              positivePart_eq_zero_of_nonpos (le_refl (0 : ℝ))]
          linarith
        exact hmin.deriv_eq_zero
      · by_cases hA_neg : A y < 0
        · have hA_neg_ev : ∀ᶠ z in 𝓝 y, A z < 0 :=
            hA_cont.tendsto.eventually (isOpen_Iio.mem_nhds hA_neg)
          have hmax : IsLocalMax (truncatedChemFluxLifted p w) y := by
            unfold IsLocalMax IsMaxFilter
            filter_upwards [hA_neg_ev] with z hz
            have hz_nonpos : truncatedChemFluxLifted p w z ≤ 0 := by
              rw [hflux_eq]
              exact mul_nonpos_of_nonneg_of_nonpos (positivePart_nonneg _) hz.le
            have hy_val : truncatedChemFluxLifted p w y = 0 := by
              rw [hflux_eq]
              simp [a, hy_zero,
                positivePart_eq_zero_of_nonpos (le_refl (0 : ℝ))]
            linarith
          exact hmax.deriv_eq_zero
        · have hA_zero : A y = 0 :=
            le_antisymm (le_of_not_gt hA_pos) (le_of_not_gt hA_neg)
          have ha_cont : ContinuousAt a y := by
            have hpos_cont : Continuous fun r : ℝ => positivePart r := by
              simpa [positivePart] using (continuous_id.max continuous_const)
            exact hpos_cont.continuousAt.comp hw_lift_cont
          have ha_zero : a y = 0 := by
            simp [a, hy_zero,
              positivePart_eq_zero_of_nonpos (le_refl (0 : ℝ))]
          have hprod_has :
              HasDerivAt (fun z : ℝ => a z * A z) 0 y :=
            hasDerivAt_mul_zero_of_continuousAt_zero_hasDerivAt_zero
              ha_cont ha_zero hA_has hA_zero
          have hflux_has :
              HasDerivAt (truncatedChemFluxLifted p w) 0 y := by
            rw [hflux_eq]
            exact hprod_has
          exact hflux_has.deriv
  · exact truncatedChemFluxLifted_deriv_eq_zero_off_Ioo
      (p := p) (w := w) hyIoo

private theorem truncatedChemFluxLifted_deriv_product_rule_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M)
    (y : ℝ)
    (hdiff : 0 < intervalDomainLift w y →
      DifferentiableAt ℝ (intervalDomainLift w) y) :
    ∃ dpos gp : ℝ,
      deriv (truncatedChemFluxLifted p w) y =
        dpos * resolverGradReal p (fun x => positivePart (w x)) y *
            (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p
              (fun x => positivePart (w x))) y) ^ (-p.β)
          + positivePart (intervalDomainLift w y) * gp *
            (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p
              (fun x => positivePart (w x))) y) ^ (-p.β)
          - p.β * positivePart (intervalDomainLift w y)
              * (resolverGradReal p (fun x => positivePart (w x)) y) ^ 2 *
            (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p
              (fun x => positivePart (w x))) y) ^ (-p.β - 1)
      ∧ |dpos| ≤ |deriv (intervalDomainLift w) y|
      ∧ gp = deriv
        (fun z : ℝ => resolverGradReal p (fun x => positivePart (w x)) z) y := by
  classical
  let wPos : intervalDomainPoint → ℝ := fun x => positivePart (w x)
  have hwPos_cont : Continuous wPos := by
    simpa [wPos] using positivePart_slice_continuous hw_cont
  have hwPos_ball : ∀ x : intervalDomainPoint, |wPos x| ≤ M := by
    simpa [wPos] using positivePart_slice_abs_le_of_abs_ball hball
  by_cases hpos : 0 < intervalDomainLift w y
  · let R : ℝ → ℝ :=
      fun z => intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p wPos) z
    let g : ℝ → ℝ := fun z => resolverGradReal p wPos z
    let a : ℝ → ℝ := fun z => positivePart (intervalDomainLift w z)
    let q : ℝ → ℝ := fun z => (1 + R z) ^ (-p.β)
    have hdw : DifferentiableAt ℝ (intervalDomainLift w) y := hdiff hpos
    have hflux_eq : truncatedChemFluxLifted p w =
        fun z => a z * g z * q z := by
      funext z
      have hbase_nonneg : 0 ≤ 1 + R z := by
        simpa [R] using resolverR_lift_one_add_nonneg_of_abs_ball
          (p := p) (w := w) hw_cont z
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
        (p := p) (w := wPos) (M := M) hM hwPos_cont hwPos_ball hyIoo
    have hg_has : HasDerivAt g (deriv g y) y := by
      simpa [g, hg_raw.deriv] using hg_raw
    have hUcont : ContinuousOn (intervalDomainLift wPos) (Set.Icc (0 : ℝ) 1) :=
      lift_continuousOn_Icc_of_continuous hwPos_cont
    have hR_has : HasDerivAt R (g y) y := by
      simpa [R, g] using
        ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverR_lift_hasDerivAt_resolverGradReal_of_continuousOn
          (p := p) (u := wPos) hUcont hyIoo
    have hbase_has : HasDerivAt (fun z : ℝ => 1 + R z) (g y) y :=
      hR_has.const_add 1
    have hbase_pos : 0 < 1 + R y := by
      simpa [R] using resolverR_lift_one_add_pos_of_abs_ball
        (p := p) (w := w) hw_cont y
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
    refine ⟨0, deriv (fun z : ℝ => resolverGradReal p wPos z) y, ?_, ?_, ?_⟩
    · have hflux_zero :
          deriv (truncatedChemFluxLifted p w) y = 0 :=
        truncatedChemFluxLifted_deriv_zero_of_lift_nonpos_of_abs_ball
          (p := p) (w := w) (M := M) hM hw_cont hball hy_nonpos
      have hpp_zero : positivePart (intervalDomainLift w y) = 0 :=
        positivePart_eq_zero_of_nonpos hy_nonpos
      simp [hflux_zero, hpp_zero]
    · simp
    · rfl

private theorem truncatedChemFluxLifted_deriv_terms_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M)
    (y : ℝ)
    (hdiff : 0 < intervalDomainLift w y →
      DifferentiableAt ℝ (intervalDomainLift w) y) :
    ∃ dpos gp q qDen : ℝ,
      deriv (truncatedChemFluxLifted p w) y =
        dpos * resolverGradReal p (fun x => positivePart (w x)) y * q
          + positivePart (intervalDomainLift w y) * gp * q
          - p.β * positivePart (intervalDomainLift w y)
              * (resolverGradReal p (fun x => positivePart (w x)) y) ^ 2 * qDen
      ∧ |dpos| ≤ |deriv (intervalDomainLift w) y|
      ∧ |resolverGradReal p (fun x => positivePart (w x)) y| ≤
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
  let wPos : intervalDomainPoint → ℝ := fun x => positivePart (w x)
  have hwPos_cont : Continuous wPos := by
    simpa [wPos] using positivePart_slice_continuous hw_cont
  have hwPos_ball : ∀ x : intervalDomainPoint, |wPos x| ≤ M := by
    simpa [wPos] using positivePart_slice_abs_le_of_abs_ball hball
  let q : ℝ :=
    (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p wPos) y) ^ (-p.β)
  let qDen : ℝ :=
    (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p wPos) y) ^
      (-p.β - 1)
  have hbase_pos :
      0 < 1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p wPos) y := by
    simpa [wPos] using
    resolverR_lift_one_add_pos_of_abs_ball
      (p := p) (w := w) hw_cont y
  have hbase_one :
      1 ≤ 1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p wPos) y := by
    have hR_nonneg :=
      resolverR_positivePart_lift_nonneg_of_continuous p hw_cont y
    simpa [wPos] using (show
      1 ≤ 1 + intervalDomainLift
        (ShenWork.PDE.intervalNeumannResolverR p
          (fun x => positivePart (w x))) y by linarith)
  have hgrad_bound :
      |resolverGradReal p wPos y| ≤
        Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
          * (2 * (p.ν * M ^ p.γ)) :=
    resolverGrad_abs_le_of_abs_ball
      (p := p) (w := wPos) (M := M) hM hwPos_cont hwPos_ball y
  have hq_abs : |q| ≤ 1 := by
    have hq_nonneg : 0 ≤ q := by
      exact Real.rpow_nonneg hbase_pos.le _
    have hq_le : q ≤ 1 := by
      dsimp [q]
      exact Real.rpow_le_one_of_one_le_of_nonpos hbase_one (by linarith [p.hβ])
    rw [abs_of_nonneg hq_nonneg]
    exact hq_le
  have hqDen_abs : |qDen| ≤ 1 := by
    have hqDen_nonneg : 0 ≤ qDen := by
      exact Real.rpow_nonneg hbase_pos.le _
    have hqDen_le : qDen ≤ 1 := by
      dsimp [qDen]
      exact Real.rpow_le_one_of_one_le_of_nonpos hbase_one (by linarith [p.hβ])
    rw [abs_of_nonneg hqDen_nonneg]
    exact hqDen_le
  by_cases hpos : 0 < intervalDomainLift w y
  · obtain ⟨dpos, gp, hderiv, hdpos, hgp_eq⟩ :=
      truncatedChemFluxLifted_deriv_product_rule_of_abs_ball
        (p := p) (w := w) (M := M) hM hw_cont hball y hdiff
    refine ⟨dpos, gp, q, qDen, ?_, hdpos, ?_, ?_, hq_abs, hqDen_abs⟩
    · simpa [q, qDen, wPos] using hderiv
    · simpa [wPos] using hgrad_bound
    · rw [hgp_eq]
      have hyIoo : y ∈ Set.Ioo (0 : ℝ) 1 :=
        intervalDomainLift_pos_mem_Ioo_of_differentiableAt hpos (hdiff hpos)
      simpa [wPos] using resolverGrad_deriv_abs_le_of_abs_ball
        (p := p) (w := wPos) (M := M) hM hwPos_cont hwPos_ball hyIoo
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
    refine ⟨0, 0, q, qDen, ?_, ?_, ?_, hgp_bound, hq_abs, hqDen_abs⟩
    · simp [hflux_zero, hpp_zero]
    · simp
    · simpa [wPos] using hgrad_bound

private theorem truncatedChemFluxLifted_deriv_abs_le_of_abs_ball_grad'
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M G : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M)
    (hgrad : ∀ x : ℝ, |deriv (intervalDomainLift w) x| ≤ G)
    (y : ℝ)
    (hdiff : 0 < intervalDomainLift w y →
      DifferentiableAt ℝ (intervalDomainLift w) y) :
    |deriv (truncatedChemFluxLifted p w) y| ≤
      (M *
          (p.μ * (Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2)
              * (2 * (p.ν * M ^ p.γ))) + p.ν * M ^ p.γ)
        + p.β * M *
          (Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
              * (2 * (p.ν * M ^ p.γ))) ^ 2)
        + (Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
              * (2 * (p.ν * M ^ p.γ))) * G := by
  let Γ : ℝ := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
        * (2 * (p.ν * M ^ p.γ))
  let V : ℝ := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2)
        * (2 * (p.ν * M ^ p.γ))
  let H : ℝ := p.μ * V + p.ν * M ^ p.γ
  obtain ⟨dpos, gp, q, qDen, hderiv, hdpos, hgradR, hgp, hq, hqDen⟩ :=
    truncatedChemFluxLifted_deriv_terms_of_abs_ball
      p hM hw_cont hball y hdiff
  simpa [Γ, V, H] using
    (truncatedChemFluxLifted_deriv_abs_le_of_ball_grad
      (p := p) (w := w) (M := M) (Γ := Γ) (H := H) (G := G)
      (Q := 1) (QDen := 1) hM hball hgrad y hderiv hdpos
      (by simpa [Γ] using hgradR) (by simpa [H, V] using hgp)
      hq hqDen)

private theorem truncatedChemFluxLifted_continuousOn_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M) :
    ContinuousOn (truncatedChemFluxLifted p w) (Set.Icc (0 : ℝ) 1) := by
  classical
  let wPos : intervalDomainPoint → ℝ := fun x => positivePart (w x)
  have hwPos_cont : Continuous wPos := by
    simpa [wPos] using positivePart_slice_continuous hw_cont
  have hUcont : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) :=
    lift_continuousOn_Icc_of_continuous hw_cont
  have hUPoscont : ContinuousOn (intervalDomainLift wPos) (Set.Icc (0 : ℝ) 1) :=
    lift_continuousOn_Icc_of_continuous hwPos_cont
  have hpos_cont : Continuous fun r : ℝ => positivePart r := by
    simpa [positivePart] using (continuous_id.max continuous_const)
  have hpp_cont :
      ContinuousOn (fun y : ℝ => positivePart (intervalDomainLift w y))
        (Set.Icc (0 : ℝ) 1) :=
    hpos_cont.continuousOn.comp hUcont (fun _ _ => Set.mem_univ _)
  have hgrad_cont :
      ContinuousOn (fun y : ℝ => resolverGradReal p wPos y)
        (Set.Icc (0 : ℝ) 1) :=
    (resolverGradReal_continuous_of_continuousOn p hUPoscont).continuousOn
  have hR_cont :
      ContinuousOn
        (intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p wPos))
        (Set.Icc (0 : ℝ) 1) := by
    have hseries_cont : Continuous (fun y : ℝ =>
        ∑' k : ℕ, (ShenWork.PDE.intervalNeumannResolverCoeff p wPos k).re *
          unitIntervalCosineMode k y) :=
      ShenWork.IntervalDuhamelIntegrability.resolverValueReal_continuous_of_continuousOn
        p hUPoscont
    refine hseries_cont.continuousOn.congr ?_
    intro y hy
    simp [intervalDomainLift, hy, ShenWork.PDE.intervalNeumannResolverR]
  have hbase_cont :
      ContinuousOn
        (fun y : ℝ =>
          1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p wPos) y)
        (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.add hR_cont
  have hden_cont :
      ContinuousOn
        (fun y : ℝ =>
          (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p wPos) y) ^
            p.β)
        (Set.Icc (0 : ℝ) 1) :=
    hbase_cont.rpow_const (fun _ _ => Or.inr p.hβ)
  have hden_ne :
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p wPos) y) ^
          p.β ≠ 0 := by
    intro y _hy
    have hbase_pos :
        0 < 1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p wPos) y := by
      simpa [wPos] using
      resolverR_lift_one_add_pos_of_abs_ball
        (p := p) (w := w) hw_cont y
    exact ne_of_gt (Real.rpow_pos_of_pos hbase_pos p.β)
  simpa [truncatedChemFluxLifted, wPos] using
    (hpp_cont.mul hgrad_cont).div hden_cont hden_ne

private theorem truncatedChemFluxLifted_hasDerivAt_off_transversal_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M)
    (hdiff : ∀ y ∈ Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (intervalDomainLift w) y) :
    ∀ y ∈ Ioo (0 : ℝ) 1 \
        picardTransversalZeroSet (intervalDomainLift w),
      HasDerivAt (truncatedChemFluxLifted p w)
        (deriv (truncatedChemFluxLifted p w) y) y := by
  classical
  intro y hy
  have hyIoo : y ∈ Ioo (0 : ℝ) 1 := hy.1
  have hy_not_bad :
      intervalDomainLift w y = 0 → deriv (intervalDomainLift w) y = 0 := by
    intro hzero
    by_contra hne
    exact hy.2 ⟨hyIoo, hzero, hne⟩
  have hw_has : HasDerivAt (intervalDomainLift w)
      (deriv (intervalDomainLift w) y) y :=
    (hdiff y hyIoo).hasDerivAt
  let wPos : intervalDomainPoint → ℝ := fun x => positivePart (w x)
  have hwPos_cont : Continuous wPos := by
    simpa [wPos] using positivePart_slice_continuous hw_cont
  have hwPos_ball : ∀ x : intervalDomainPoint, |wPos x| ≤ M := by
    simpa [wPos] using positivePart_slice_abs_le_of_abs_ball hball
  let R : ℝ → ℝ :=
    fun z => intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p wPos) z
  let g : ℝ → ℝ := fun z => resolverGradReal p wPos z
  let a : ℝ → ℝ := fun z => positivePart (intervalDomainLift w z)
  let q : ℝ → ℝ := fun z => (1 + R z) ^ (-p.β)
  have hflux_eq : truncatedChemFluxLifted p w =
      fun z => a z * g z * q z := by
    funext z
    have hbase_nonneg : 0 ≤ 1 + R z := by
      simpa [R] using resolverR_lift_one_add_nonneg_of_abs_ball
        (p := p) (w := w) hw_cont z
    unfold truncatedChemFluxLifted
    rw [div_eq_mul_inv, ← Real.rpow_neg hbase_nonneg]
  obtain ⟨dpos, ha_has⟩ :=
    positivePart_comp_hasDerivAt_of_hasDerivAt_not_bad hw_has hy_not_bad
  obtain ⟨_src, hg_raw, _hsrc⟩ :=
    resolverGradReal_hasDerivAt_signed_ellipticBound_of_abs_ball
      (p := p) (w := wPos) (M := M) hM hwPos_cont hwPos_ball hyIoo
  have hg_has : HasDerivAt g (deriv g y) y := by
    simpa [g, hg_raw.deriv] using hg_raw
  have hUcont : ContinuousOn (intervalDomainLift wPos) (Icc (0 : ℝ) 1) :=
    lift_continuousOn_Icc_of_continuous hwPos_cont
  have hR_has : HasDerivAt R (g y) y := by
    simpa [R, g] using
      ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverR_lift_hasDerivAt_resolverGradReal_of_continuousOn
        (p := p) (u := wPos) hUcont hyIoo
  have hbase_has : HasDerivAt (fun z : ℝ => 1 + R z) (g y) y :=
    hR_has.const_add 1
  have hbase_pos : 0 < 1 + R y := by
    simpa [R] using resolverR_lift_one_add_pos_of_abs_ball
      (p := p) (w := w) hw_cont y
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

private theorem truncatedChemFluxLifted_ibpRegularity_of_abs_ball
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M C : ℝ}
    (hM : 0 < M) (hw_cont : Continuous w)
    (hball : ∀ x : intervalDomainPoint, |w x| ≤ M)
    (hdiff : ∀ y ∈ Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (intervalDomainLift w) y)
    (hderiv_bound : ∀ y ∈ Icc (0 : ℝ) 1,
      |deriv (truncatedChemFluxLifted p w) y| ≤ C) :
    ShenWork.Paper2.IntervalConjugateKernelIBP.IntervalIBPRegularity
      (truncatedChemFluxLifted p w) := by
  let bad := picardTransversalZeroSet (intervalDomainLift w)
  refine ⟨bad, ?_, ?_, ?_, ?_⟩
  · simpa [bad] using
      picardTransversalZeroSet_countable_of_differentiableAt hdiff
  · exact truncatedChemFluxLifted_continuousOn_of_abs_ball
      p hM hw_cont hball
  · simpa [bad] using
      truncatedChemFluxLifted_hasDerivAt_off_transversal_of_abs_ball
        p hM hw_cont hball hdiff
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)]
    refine Integrable.mono' (integrable_const C)
      ((measurable_deriv _).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    rw [Real.norm_eq_abs]
    exact hderiv_bound y ⟨hy.1.le, hy.2⟩

private theorem truncatedWindowedSource_measurable_of_abs_ball
    (p : CM2Params)
    {w : ℝ → intervalDomainPoint → ℝ}
    {Src : ℕ → ℝ → ℝ → ℝ} {n : ℕ} {a hi M : ℝ}
    (hM : 0 < M)
    (hw_joint : Measurable (fun q : ℝ × ℝ =>
      intervalDomainLift (w q.1) q.2))
    (hw_cont : ∀ s, a ≤ s → s ≤ hi → Continuous (w s))
    (hball : ∀ s, a ≤ s → s ≤ hi →
      ∀ x : intervalDomainPoint, |w s x| ≤ M)
    (hdiff : ∀ s, a ≤ s → s ≤ hi → ∀ y ∈ Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (intervalDomainLift (w s)) y)
    (hSrc : ∀ s y,
      Src n s y = truncatedLogisticLifted p (w s) y
        - p.χ₀ * deriv (truncatedChemFluxLifted p (w s)) y) :
    Measurable (Function.uncurry (truncatedWindowedSource Src n a hi)) := by
  apply truncatedWindowedSource_measurable_of_truncated_formula hw_joint
  · intro s has hshi y hyIoo hpos
    apply truncatedChemFluxLifted_hasDerivAt_off_transversal_of_abs_ball
      p hM (hw_cont s has hshi) (hball s has hshi)
      (hdiff s has hshi) y
    exact ⟨hyIoo, fun hybad => (ne_of_gt hpos) hybad.2.1⟩
  · intro s has hshi y _hyIoo hnonpos
    exact truncatedChemFluxLifted_deriv_zero_of_lift_nonpos_of_abs_ball
      p hM (hw_cont s has hshi) (hball s has hshi) hnonpos
  · exact hSrc

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
theorem truncatedPicardLimit_lipschitzOn_positive_time_of_contraction
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T)
    (hcontr : truncWindowB
      (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
            * (2 * (p.ν * DT.M ^ p.γ)))
      p.χ₀ (t / 4) t < 1) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |intervalDomainLift
        ((truncatedConjugatePicardLimit p u₀ DT.T) t) x -
       intervalDomainLift
        ((truncatedConjugatePicardLimit p u₀ DT.T) t) y| ≤ G * |x - y| := by
  have hmeas_iterates_grad : ∀ k,
      HasJointMeasurability (truncatedConjugatePicardIter p u₀ k) := by
    intro k
    induction k with
    | zero => exact DT.hbase_meas
    | succ k ih => exact DT.hmeas_preserved _ ih
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
    -- |Q'| ≤ G · Γ_M + M · H_M + β · M · Γ_M².
    -- So A_F = M · H_M + β · M · Γ_M² and B_F = Γ_M.
    let A_F : ℝ := DT.M * H_M + p.β * DT.M * Γ_M ^ 2
    let B_F : ℝ := Γ_M
    -- Contraction coefficient: Cg · 2√(hi-a) · |χ₀| · Γ_M
    -- For the fixed point to exist, need truncWindowB < 1.
    -- Use the fixed-point formula Gw = truncWindowA / (1 - truncWindowB).
    have hΓ_M_nn : 0 ≤ Γ_M := mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by positivity) (mul_nonneg (le_of_lt p.hν)
        (Real.rpow_nonneg (le_of_lt DT.hM) _)))
    have hV_M_nn : 0 ≤ V_M := mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by positivity) (mul_nonneg (le_of_lt p.hν)
        (Real.rpow_nonneg (le_of_lt DT.hM) _)))
    have hH_M_nn : 0 ≤ H_M := by
      dsimp only [H_M]
      exact add_nonneg (mul_nonneg p.hμ.le hV_M_nn)
        (mul_nonneg p.hν.le (Real.rpow_nonneg DT.hM.le _))
    have hBF_nn : 0 ≤ B_F := by
      simpa [B_F] using hΓ_M_nn
    have hAL_nn : 0 ≤ A_L := mul_nonneg (le_of_lt DT.hM) (add_nonneg p.ha
      (mul_nonneg p.hb (Real.rpow_nonneg (le_of_lt DT.hM) _)))
    have hAF_nn : 0 ≤ A_F := by
      dsimp only [A_F]
      apply add_nonneg
      · exact mul_nonneg DT.hM.le hH_M_nn
      · exact mul_nonneg (mul_nonneg p.hβ DT.hM.le) (sq_nonneg _)
    have hBcontr : truncWindowB B_F p.χ₀ a hi < 1 := hcontr
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
          hBF_nonneg := hBF_nn
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
              exact truncLeftProfile_le_Gw hM hAL_nn hAF_nn hBF_nn ha
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
                mul_nonneg (abs_nonneg p.χ₀) hBF_nn
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
                  hAL_nn hAF_nn hBF_nn
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
                  (truncLeftD_nonneg hM hAL_nn hAF_nn hBF_nn
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
                · have hdiff_pos :
                      0 < intervalDomainLift (U n s) y →
                        DifferentiableAt ℝ (intervalDomainLift (U n s)) y := by
                    intro _hy_pos
                    exact (hprofile s hs_pos hs_lo).2 y hyIoo
                  have hb :=
                    truncatedChemFluxLifted_deriv_abs_le_of_abs_ball_grad'
                      (p := p) (w := U n s) (M := DT.M)
                      (G := truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s)
                      DT.hM (hball_cont.2 s hs_pos hs_T) hball
                      (hprofile s hs_pos hs_lo).1 y hdiff_pos
                  convert hb using 1 <;>
                    (dsimp only [A_F, B_F, Γ_M, H_M, V_M] <;> ring)
                · have hflux_zero :
                      deriv (truncatedChemFluxLifted p (U n s)) y = 0 :=
                    truncatedChemFluxLifted_deriv_eq_zero_off_Ioo
                      (p := p) (w := U n s) hyIoo
                  rw [hflux_zero, abs_zero]
                  exact add_nonneg hAF_nn (mul_nonneg hBF_nn hprofile_nonneg)
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
            have kernel : ∀ n,
                IterGradLeftProfile U Mw A_L A_F B_F p.χ₀ lo n →
                (∀ s, 0 < s → s ≤ lo → ∀ y,
                  |Src n s y| ≤ truncLeftSourceConst A_L A_F p.χ₀ +
                    truncLeftBeta B_F p.χ₀ *
                      truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s) →
                IterGradLeftProfile U Mw A_L A_F B_F p.χ₀ lo (n + 1) := by
              intro n _hprev hsrc
              have hball_cont_n := truncatedConjugatePicardIter_ball p u₀
                DT.hbase_ball DT.hbase_cont DT.hmapsTo DT.hcont_preserved
                DT.hbase_meas DT.hmeas_preserved n
              have hU_joint : Measurable (fun q : ℝ × ℝ =>
                  intervalDomainLift (U n q.1) q.2) := by
                simpa [U, HasJointMeasurability] using hmeas_iterates_grad n
              have hsource_meas : ∀ (a' τ' : ℝ), 0 < a' → a' < τ' → τ' ≤ lo →
                  Measurable
                    (Function.uncurry (truncatedWindowedSource Src n a' τ')) := by
                intro a' τ' ha' _haτ hτ'lo
                apply truncatedWindowedSource_measurable_of_abs_ball
                  (p := p) (w := fun s => U n s) (M := DT.M)
                  DT.hM hU_joint
                · intro s has hsτ
                  have hspos : 0 < s := ha'.trans_le has
                  have hslo : s ≤ lo := hsτ.trans hτ'lo
                  have hsT : s ≤ DT.T := by
                    have hlo_t : lo ≤ t := by dsimp [lo]; linarith
                    exact hslo.trans (hlo_t.trans htT)
                  exact hball_cont_n.2 s hspos hsT
                · intro s has hsτ x
                  have hspos : 0 < s := ha'.trans_le has
                  have hslo : s ≤ lo := hsτ.trans hτ'lo
                  have hsT : s ≤ DT.T := by
                    have hlo_t : lo ≤ t := by dsimp [lo]; linarith
                    exact hslo.trans (hlo_t.trans htT)
                  exact hball_cont_n.1 s hspos hsT x
                · intro s has hsτ y hyIoo
                  exact (_hprev s (ha'.trans_le has) (hsτ.trans hτ'lo)).2 y hyIoo
                · intro s y
                  rfl
              have hflux_reg : ∀ s, 0 < s → s ≤ lo →
                  ShenWork.Paper2.IntervalConjugateKernelIBP.IntervalIBPRegularity
                    (truncatedChemFluxLifted p (U n s)) := by
                intro s hspos hslo
                have hsT : s ≤ DT.T := by
                  have hlo_t : lo ≤ t := by dsimp [lo]; linarith
                  exact hslo.trans (hlo_t.trans htT)
                have hw_cont := hball_cont_n.2 s hspos hsT
                have hball := hball_cont_n.1 s hspos hsT
                have hgrad_s := _hprev s hspos hslo
                have hprofile_nonneg :
                    0 ≤ truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s :=
                  (abs_nonneg (deriv (intervalDomainLift (U n s)) 0)).trans
                    (hgrad_s.1 0)
                have hC_nonneg : 0 ≤ A_F + B_F *
                    truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s :=
                  add_nonneg hAF_nn (mul_nonneg hBF_nn hprofile_nonneg)
                have hderiv_bound : ∀ y ∈ Icc (0 : ℝ) 1,
                    |deriv (truncatedChemFluxLifted p (U n s)) y| ≤
                      A_F + B_F *
                        truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s := by
                  intro y _hy
                  by_cases hyIoo : y ∈ Ioo (0 : ℝ) 1
                  · have hdiff_pos : 0 < intervalDomainLift (U n s) y →
                        DifferentiableAt ℝ (intervalDomainLift (U n s)) y :=
                      fun _ => hgrad_s.2 y hyIoo
                    have hb :=
                      truncatedChemFluxLifted_deriv_abs_le_of_abs_ball_grad'
                        (p := p) (w := U n s) (M := DT.M)
                        (G := truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s)
                        DT.hM hw_cont hball hgrad_s.1 y hdiff_pos
                    convert hb using 1 <;>
                      (dsimp only [Mw, A_F, B_F, Γ_M, H_M, V_M] <;>
                        ring)
                  · rw [truncatedChemFluxLifted_deriv_eq_zero_off_Ioo
                      (p := p) (w := U n s) hyIoo, abs_zero]
                    exact hC_nonneg
                exact truncatedChemFluxLifted_ibpRegularity_of_abs_ball
                  p DT.hM hw_cont hball hgrad_s.2 hderiv_bound
              simpa [Mw] using
                ((truncatedConjugatePicardIter_succ_left_profile
                  (p := p) (u₀ := u₀) DT U (by intro n s; rfl) Src
                  (by intro n s y; rfl)
                  hAL_nn hAF_nn hBF_nn
                  (by dsimp [lo]; linarith)
                  (by dsimp [lo]; linarith)
                  hleftContr) n hsource_meas hflux_reg hsrc)
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
              hAL_nn hAF_nn hBF_nn
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
              · have hgrad_s := hgrad s ha_s hs_hi
                have hdiff_pos : 0 < intervalDomainLift (U n s) y →
                    DifferentiableAt ℝ (intervalDomainLift (U n s)) y :=
                  fun _ => hgrad_s.2 y hyIoo
                have hb :=
                  truncatedChemFluxLifted_deriv_abs_le_of_abs_ball_grad'
                    (p := p) (w := U n s) (M := DT.M) (G := Gw)
                    DT.hM (hball_cont.2 s hs_pos hs_T) hball
                    hgrad_s.1 y hdiff_pos
                convert hb using 1 <;>
                  (dsimp only [A_F, B_F, Γ_M, H_M, V_M] <;>
                    ring)
              · rw [truncatedChemFluxLifted_deriv_eq_zero_off_Ioo (p := p) (w := U n s) hyIoo,
                    abs_zero]
                exact add_nonneg hAF_nn (mul_nonneg hBF_nn hGw_nn)
          hkernel_step := by
            -- After IBP, the B-form iterate becomes standard Duhamel:
            -- ∫₀ᵗ S(t-s)(Src_n(s)) ds where Src = logistic - χ₀·flux'.
            -- The gradient bound follows from gradDuhamel_shifted_sup_bound.
            intro n _hprev hsrc
            have hball_cont_n := truncatedConjugatePicardIter_ball p u₀
              DT.hbase_ball DT.hbase_cont DT.hmapsTo DT.hcont_preserved
              DT.hbase_meas DT.hmeas_preserved n
            have hU_joint : Measurable (fun q : ℝ × ℝ =>
                intervalDomainLift (U n q.1) q.2) := by
              simpa [U, HasJointMeasurability] using hmeas_iterates_grad n
            have hsource_meas : ∀ τ' : ℝ, 0 < a → a < τ' → τ' ≤ hi →
                Measurable
                  (Function.uncurry (truncatedWindowedSource Src n a τ')) := by
              intro τ' ha' _haτ hτ'hi
              apply truncatedWindowedSource_measurable_of_abs_ball
                (p := p) (w := fun s => U n s) (M := DT.M)
                DT.hM hU_joint
              · intro s has hsτ
                have hspos : 0 < s := ha'.trans_le has
                have hshi : s ≤ hi := hsτ.trans hτ'hi
                have hsT : s ≤ DT.T := by simpa [hi] using hshi.trans htT
                exact hball_cont_n.2 s hspos hsT
              · intro s has hsτ x
                have hspos : 0 < s := ha'.trans_le has
                have hshi : s ≤ hi := hsτ.trans hτ'hi
                have hsT : s ≤ DT.T := by simpa [hi] using hshi.trans htT
                exact hball_cont_n.1 s hspos hsT x
              · intro s has hsτ y hyIoo
                exact (_hprev s has (hsτ.trans hτ'hi)).2 y hyIoo
              · intro s y
                rfl
            have hflux_reg : ∀ s, a ≤ s → s ≤ hi →
                ShenWork.Paper2.IntervalConjugateKernelIBP.IntervalIBPRegularity
                  (truncatedChemFluxLifted p (U n s)) := by
              intro s has hshi
              have ha_pos_window : 0 < a := by dsimp [a]; linarith
              have hspos : 0 < s := ha_pos_window.trans_le has
              have hsT : s ≤ DT.T := by simpa [hi] using hshi.trans htT
              have hw_cont := hball_cont_n.2 s hspos hsT
              have hball := hball_cont_n.1 s hspos hsT
              have hgrad_s := _hprev s has hshi
              have hC_nonneg : 0 ≤ A_F + B_F * Gw :=
                add_nonneg hAF_nn (mul_nonneg hBF_nn hGw_nn)
              have hderiv_bound : ∀ y ∈ Icc (0 : ℝ) 1,
                  |deriv (truncatedChemFluxLifted p (U n s)) y| ≤
                    A_F + B_F * Gw := by
                intro y _hy
                by_cases hyIoo : y ∈ Ioo (0 : ℝ) 1
                · have hdiff_pos : 0 < intervalDomainLift (U n s) y →
                      DifferentiableAt ℝ (intervalDomainLift (U n s)) y :=
                    fun _ => hgrad_s.2 y hyIoo
                  have hb :=
                    truncatedChemFluxLifted_deriv_abs_le_of_abs_ball_grad'
                      (p := p) (w := U n s) (M := DT.M) (G := Gw)
                      DT.hM hw_cont hball hgrad_s.1 y hdiff_pos
                  convert hb using 1 <;>
                    (dsimp only [Mw, A_F, B_F, Γ_M, H_M, V_M] <;> ring)
                · rw [truncatedChemFluxLifted_deriv_eq_zero_off_Ioo
                    (p := p) (w := U n s) hyIoo, abs_zero]
                  exact hC_nonneg
              exact truncatedChemFluxLifted_ibpRegularity_of_abs_ball
                p DT.hM hw_cont hball hgrad_s.2 hderiv_bound
            dsimp only [Mw]
            exact (truncatedConjugatePicardIter_succ_window_gradient
              (p := p) (u₀ := u₀) DT U (by intro n s; rfl) Src
              (by intro n s y; rfl)
              hAL_nn hAF_nn hBF_nn hGw_nn
              (by dsimp [a]; linarith)
              (by dsimp [a, lo]; linarith)
              (by dsimp [lo, hi]; linarith)
              htT) n hsource_meas hflux_reg hsrc }
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
      lift_continuousOn_Icc_of_continuous hcont_n
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

/-- On a whole terminal positive-time window, the lifted truncated
Picard-limit slices share one Lipschitz constant on `[0,1]`.  The proof starts
from the near-zero left profile and chains finitely many equal-width
contracting restart windows up to `t`; the last chained window is retained in
the conclusion instead of being evaluated only at its right endpoint. -/
theorem truncatedPicardLimit_lipschitzOn_positive_window
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    ∃ lo G : ℝ, 0 < lo ∧ lo < t ∧ 0 ≤ G ∧
      ∀ s, lo ≤ s → s ≤ t →
        ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
          |intervalDomainLift
            ((truncatedConjugatePicardLimit p u₀ DT.T) s) x -
           intervalDomainLift
            ((truncatedConjugatePicardLimit p u₀ DT.T) s) y| ≤ G * |x - y| := by
  have hmeas_iterates_grad : ∀ k,
      HasJointMeasurability (truncatedConjugatePicardIter p u₀ k) := by
    intro k
    induction k with
    | zero => exact DT.hbase_meas
    | succ k ih => exact DT.hmeas_preserved _ ih
  let U : ℕ → ℝ → intervalDomainPoint → ℝ :=
    fun n s => truncatedConjugatePicardIter p u₀ n s
  let Src : ℕ → ℝ → ℝ → ℝ :=
    fun n s y =>
      truncatedLogisticLifted p (U n s) y
        - p.χ₀ * deriv (truncatedChemFluxLifted p (U n s)) y
  let Mw : ℝ := DT.M
  let A_L : ℝ := DT.M * (p.a + p.b * DT.M ^ p.α)
  let Γ_M : ℝ := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2)
      * (2 * (p.ν * DT.M ^ p.γ))
  let V_M : ℝ := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2)
      * (2 * (p.ν * DT.M ^ p.γ))
  let H_M : ℝ := p.μ * V_M + p.ν * DT.M ^ p.γ
  let A_F : ℝ := DT.M * H_M + p.β * DT.M * Γ_M ^ 2
  let B_F : ℝ := Γ_M
  have hΓ_M_nn : 0 ≤ Γ_M := mul_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (by positivity) (mul_nonneg (le_of_lt p.hν)
      (Real.rpow_nonneg (le_of_lt DT.hM) _)))
  have hV_M_nn : 0 ≤ V_M := mul_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (by positivity) (mul_nonneg (le_of_lt p.hν)
      (Real.rpow_nonneg (le_of_lt DT.hM) _)))
  have hH_M_nn : 0 ≤ H_M := by
    dsimp only [H_M]
    exact add_nonneg (mul_nonneg p.hμ.le hV_M_nn)
      (mul_nonneg p.hν.le (Real.rpow_nonneg DT.hM.le _))
  have hBF_nn : 0 ≤ B_F := by
    simpa [B_F] using hΓ_M_nn
  have hAL_nn : 0 ≤ A_L := mul_nonneg (le_of_lt DT.hM) (add_nonneg p.ha
    (mul_nonneg p.hb (Real.rpow_nonneg (le_of_lt DT.hM) _)))
  have hAF_nn : 0 ≤ A_F := by
    dsimp only [A_F]
    exact add_nonneg (mul_nonneg DT.hM.le hH_M_nn)
      (mul_nonneg (mul_nonneg p.hβ DT.hM.le) (sq_nonneg _))
  let C : EqualStepGradientWindowChain t B_F p.χ₀ :=
    Classical.choice (exists_equalStepGradientWindowChain ht hBF_nn)
  let a : ℝ := C.a 0
  let lo : ℝ := C.lo 0
  let hi : ℝ := C.hi 0
  have ha : 0 < a := by
    dsimp only [a]
    exact C.a_pos 0
  have hlo_pos : 0 < lo := by
    exact ha.trans (by
      dsimp only [a, lo]
      exact C.a_lt_lo 0)
  have hlo_t : lo ≤ t := by
    dsimp only [lo]
    exact (C.lo_le_hi 0).trans (C.hi_le_target (Nat.zero_le C.N))
  have hloT : lo ≤ DT.T := hlo_t.trans htT
  have hBcontr : truncWindowB B_F p.χ₀ a hi < 1 := by
    dsimp only [a, hi]
    exact C.window_contraction 0
  let Gw : ℝ := truncWindowFixedG Mw A_L A_F B_F p.χ₀ a lo hi
  have hGw_nn : 0 ≤ Gw := by
    dsimp only [Gw]
    simp only [truncWindowFixedG, truncWindowA]
    apply div_nonneg
    · apply add_nonneg
      · exact mul_nonneg
          (div_nonneg
            ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
            (Real.sqrt_nonneg _)) (le_of_lt DT.hM)
      · exact mul_nonneg
          (mul_nonneg
            ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
            (mul_nonneg (by positivity) (Real.sqrt_nonneg _)))
          (add_nonneg hAL_nn (mul_nonneg (abs_nonneg _) hAF_nn))
    · linarith
  have hleft_zero : ∀ n : ℕ, IterGradOnWindow U a lo n Gw := by
    have hM : 0 ≤ Mw := le_of_lt DT.hM
    have hPaG : truncLeftProfile Mw A_L A_F B_F p.χ₀ lo a ≤ Gw := by
      dsimp only [Gw]
      exact truncLeftProfile_le_Gw hM hAL_nn hAF_nn hBF_nn ha
        (by
          dsimp only [lo, a]
          rw [C.lo_zero, C.a_zero])
        (by
          dsimp only [hi, a]
          rw [C.hi_zero, C.a_zero])
        hBcontr
    have hleftContr : truncLeftB B_F p.χ₀ lo < 1 := by
      have hlo_span : lo ≤ hi - a := by
        dsimp only [lo, hi, a]
        rw [C.lo_zero, C.hi_sub_a]
        nlinarith [C.h_pos]
      have hsqrt_le : Real.sqrt lo ≤ Real.sqrt (hi - a) :=
        Real.sqrt_le_sqrt hlo_span
      have htwo_sqrt_le :
          2 * Real.sqrt lo ≤ 2 * Real.sqrt (hi - a) :=
        mul_le_mul_of_nonneg_left hsqrt_le (by norm_num)
      have hK_nonneg :
          0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant :=
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
      have hchiBF_nonneg : 0 ≤ |p.χ₀| * B_F :=
        mul_nonneg (abs_nonneg p.χ₀) hBF_nn
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
          hAL_nn hAF_nn hBF_nn hlo_pos hleftContr
    have source : ∀ n, IterGradLeftProfile U Mw A_L A_F B_F p.χ₀ lo n →
        ∀ s, 0 < s → s ≤ lo → ∀ y,
          |Src n s y| ≤ truncLeftSourceConst A_L A_F p.χ₀ +
            truncLeftBeta B_F p.χ₀ *
              truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s := by
      intro n hprofile s hs_pos hs_lo y
      have hball_cont := truncatedConjugatePicardIter_ball p u₀
        DT.hbase_ball DT.hbase_cont DT.hmapsTo DT.hcont_preserved
        DT.hbase_meas DT.hmeas_preserved n
      have hs_T : s ≤ DT.T := hs_lo.trans hloT
      have hball : ∀ x, |U n s x| ≤ DT.M := hball_cont.1 s hs_pos hs_T
      have hK_nonneg :
          0 ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant :=
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
      have hprofile_nonneg :
          0 ≤ truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s := by
        unfold truncLeftProfile truncLeftSingularC
        exact add_nonneg
          (div_nonneg (mul_nonneg hK_nonneg hM) (Real.sqrt_nonneg _))
          (truncLeftD_nonneg hM hAL_nn hAF_nn hBF_nn hlo_pos.le hleftContr)
      dsimp only [Src]
      have hlog : |truncatedLogisticLifted p (U n s) y| ≤ A_L := by
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
            A_F + B_F * truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s := by
        by_cases hyIoo : y ∈ Set.Ioo (0 : ℝ) 1
        · have hdiff_pos :
              0 < intervalDomainLift (U n s) y →
                DifferentiableAt ℝ (intervalDomainLift (U n s)) y := by
            intro _hy_pos
            exact (hprofile s hs_pos hs_lo).2 y hyIoo
          have hb :=
            truncatedChemFluxLifted_deriv_abs_le_of_abs_ball_grad'
              (p := p) (w := U n s) (M := DT.M)
              (G := truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s)
              DT.hM (hball_cont.2 s hs_pos hs_T) hball
              (hprofile s hs_pos hs_lo).1 y hdiff_pos
          convert hb using 1 <;>
            (dsimp only [A_F, B_F, Γ_M, H_M, V_M] <;> ring)
        · have hflux_zero :
              deriv (truncatedChemFluxLifted p (U n s)) y = 0 :=
            truncatedChemFluxLifted_deriv_eq_zero_off_Ioo
              (p := p) (w := U n s) hyIoo
          rw [hflux_zero, abs_zero]
          exact add_nonneg hAF_nn (mul_nonneg hBF_nn hprofile_nonneg)
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
              (A_F + B_F * truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s) := by
            exact add_le_add hlog
              (mul_le_mul_of_nonneg_left hflux (abs_nonneg p.χ₀))
        _ = truncLeftSourceConst A_L A_F p.χ₀
              + truncLeftBeta B_F p.χ₀ *
                truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s := by
            simp [truncLeftSourceConst, truncLeftBeta]
            ring
    have kernel : ∀ n,
        IterGradLeftProfile U Mw A_L A_F B_F p.χ₀ lo n →
        (∀ s, 0 < s → s ≤ lo → ∀ y,
          |Src n s y| ≤ truncLeftSourceConst A_L A_F p.χ₀ +
            truncLeftBeta B_F p.χ₀ *
              truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s) →
        IterGradLeftProfile U Mw A_L A_F B_F p.χ₀ lo (n + 1) := by
      intro n hprev hsrc
      have hball_cont_n := truncatedConjugatePicardIter_ball p u₀
        DT.hbase_ball DT.hbase_cont DT.hmapsTo DT.hcont_preserved
        DT.hbase_meas DT.hmeas_preserved n
      have hU_joint : Measurable (fun q : ℝ × ℝ =>
          intervalDomainLift (U n q.1) q.2) := by
        simpa [U, HasJointMeasurability] using hmeas_iterates_grad n
      have hsource_meas : ∀ (a' τ' : ℝ), 0 < a' → a' < τ' → τ' ≤ lo →
          Measurable (Function.uncurry (truncatedWindowedSource Src n a' τ')) := by
        intro a' τ' ha' _haτ hτ'lo
        apply truncatedWindowedSource_measurable_of_abs_ball
          (p := p) (w := fun s => U n s) (M := DT.M)
          DT.hM hU_joint
        · intro s has hsτ
          have hspos : 0 < s := ha'.trans_le has
          have hslo : s ≤ lo := hsτ.trans hτ'lo
          exact hball_cont_n.2 s hspos (hslo.trans hloT)
        · intro s has hsτ x
          have hspos : 0 < s := ha'.trans_le has
          have hslo : s ≤ lo := hsτ.trans hτ'lo
          exact hball_cont_n.1 s hspos (hslo.trans hloT) x
        · intro s has hsτ y hyIoo
          exact (hprev s (ha'.trans_le has) (hsτ.trans hτ'lo)).2 y hyIoo
        · intro s y
          rfl
      have hflux_reg : ∀ s, 0 < s → s ≤ lo →
          ShenWork.Paper2.IntervalConjugateKernelIBP.IntervalIBPRegularity
            (truncatedChemFluxLifted p (U n s)) := by
        intro s hspos hslo
        have hsT : s ≤ DT.T := hslo.trans hloT
        have hw_cont := hball_cont_n.2 s hspos hsT
        have hball := hball_cont_n.1 s hspos hsT
        have hgrad_s := hprev s hspos hslo
        have hprofile_nonneg :
            0 ≤ truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s :=
          (abs_nonneg (deriv (intervalDomainLift (U n s)) 0)).trans
            (hgrad_s.1 0)
        have hC_nonneg :
            0 ≤ A_F + B_F * truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s :=
          add_nonneg hAF_nn (mul_nonneg hBF_nn hprofile_nonneg)
        have hderiv_bound : ∀ y ∈ Icc (0 : ℝ) 1,
            |deriv (truncatedChemFluxLifted p (U n s)) y| ≤
              A_F + B_F * truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s := by
          intro y _hy
          by_cases hyIoo : y ∈ Ioo (0 : ℝ) 1
          · have hdiff_pos :
                0 < intervalDomainLift (U n s) y →
                  DifferentiableAt ℝ (intervalDomainLift (U n s)) y :=
              fun _ => hgrad_s.2 y hyIoo
            have hb :=
              truncatedChemFluxLifted_deriv_abs_le_of_abs_ball_grad'
                (p := p) (w := U n s) (M := DT.M)
                (G := truncLeftProfile Mw A_L A_F B_F p.χ₀ lo s)
                DT.hM hw_cont hball hgrad_s.1 y hdiff_pos
            convert hb using 1 <;>
              (dsimp only [Mw, A_F, B_F, Γ_M, H_M, V_M] <;> ring)
          · rw [truncatedChemFluxLifted_deriv_eq_zero_off_Ioo
                (p := p) (w := U n s) hyIoo, abs_zero]
            exact hC_nonneg
        exact truncatedChemFluxLifted_ibpRegularity_of_abs_ball
          p DT.hM hw_cont hball hgrad_s.2 hderiv_bound
      simpa [Mw] using
        ((truncatedConjugatePicardIter_succ_left_profile
          (p := p) (u₀ := u₀) DT U (by intro n s; rfl) Src
          (by intro n s y; rfl)
          hAL_nn hAF_nn hBF_nn hlo_pos hloT hleftContr)
          n hsource_meas hflux_reg hsrc)
    exact IterGradOnWindow.of_left_profile hM ha
      (truncLeftProfile_all_of_wiring ⟨base, source, kernel⟩) hPaG
  have hbuild : ∀ k, k ≤ C.N →
      (∀ n : ℕ, IterGradOnWindow U (C.a k) (C.lo k) n Gw) →
        TruncatedGradientWindowWiring
          p U Src Mw A_L A_F B_F (C.a k) (C.lo k) (C.hi k) Gw := by
    intro k hk hleft_k
    have hak_pos : 0 < C.a k := C.a_pos k
    have haklo : C.a k < C.lo k := C.a_lt_lo k
    have hlokhi : C.lo k ≤ C.hi k := C.lo_le_hi k
    have hhikT : C.hi k ≤ DT.T := (C.hi_le_target hk).trans htT
    have hBcontr_k : truncWindowB B_F p.χ₀ (C.a k) (C.hi k) < 1 :=
      C.window_contraction k
    exact
      { hM_nonneg := le_of_lt DT.hM
        hAL_nonneg := hAL_nn
        hAF_nonneg := hAF_nn
        hBF_nonneg := hBF_nn
        hG_nonneg := hGw_nn
        ha_lt_lo := haklo
        hlo_le_hi := hlokhi
        hclosed := by
          rw [C.affine_eq_zero k]
          dsimp only [Gw]
          exact affine_fixed_closes hBcontr
        hleft := hleft_k
        hbase := by
          have hraw := truncatedConjugatePicardIter_zero_window_gradient
            (p := p) (u₀ := u₀) DT U (by intro n s; rfl)
            hAL_nn hAF_nn hBF_nn hak_pos haklo hlokhi hhikT hBcontr_k
          rw [C.fixedG_eq_zero k] at hraw
          simpa only [Mw, Gw, a, lo, hi] using hraw
        hsource_of_grad := by
          intro n hgrad s ha_s hs_hi y
          have hball_cont := truncatedConjugatePicardIter_ball p u₀
            DT.hbase_ball DT.hbase_cont DT.hmapsTo DT.hcont_preserved
            DT.hbase_meas DT.hmeas_preserved n
          have hs_pos : 0 < s := hak_pos.trans_le ha_s
          have hs_T : s ≤ DT.T := hs_hi.trans hhikT
          have hball : ∀ x, |U n s x| ≤ DT.M :=
            hball_cont.1 s hs_pos hs_T
          apply abs_logistic_sub_chi_flux_le
          · have hlift_bound : |intervalDomainLift (U n s) y| ≤ DT.M := by
              by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
              · simp only [intervalDomainLift, dif_pos hy]
                exact hball ⟨y, hy⟩
              · simp only [intervalDomainLift, dif_neg hy, abs_zero]
                exact le_of_lt DT.hM
            show |truncatedLogisticLifted p (U n s) y| ≤ A_L
            show |truncatedLogisticLocal p (intervalDomainLift (U n s) y)| ≤ _
            exact truncatedLogisticLocal_abs_le_of_abs_le' p DT.hM hlift_bound
          · by_cases hyIoo : y ∈ Set.Ioo (0 : ℝ) 1
            · have hgrad_s := hgrad s ha_s hs_hi
              have hdiff_pos :
                  0 < intervalDomainLift (U n s) y →
                    DifferentiableAt ℝ (intervalDomainLift (U n s)) y :=
                fun _ => hgrad_s.2 y hyIoo
              have hb :=
                truncatedChemFluxLifted_deriv_abs_le_of_abs_ball_grad'
                  (p := p) (w := U n s) (M := DT.M) (G := Gw)
                  DT.hM (hball_cont.2 s hs_pos hs_T) hball
                  hgrad_s.1 y hdiff_pos
              convert hb using 1 <;>
                (dsimp only [A_F, B_F, Γ_M, H_M, V_M] <;> ring)
            · rw [truncatedChemFluxLifted_deriv_eq_zero_off_Ioo
                  (p := p) (w := U n s) hyIoo, abs_zero]
              exact add_nonneg hAF_nn (mul_nonneg hBF_nn hGw_nn)
        hkernel_step := by
          intro n hprev hsrc
          have hball_cont_n := truncatedConjugatePicardIter_ball p u₀
            DT.hbase_ball DT.hbase_cont DT.hmapsTo DT.hcont_preserved
            DT.hbase_meas DT.hmeas_preserved n
          have hU_joint : Measurable (fun q : ℝ × ℝ =>
              intervalDomainLift (U n q.1) q.2) := by
            simpa [U, HasJointMeasurability] using hmeas_iterates_grad n
          have hsource_meas : ∀ τ' : ℝ,
              0 < C.a k → C.a k < τ' → τ' ≤ C.hi k →
                Measurable (Function.uncurry
                  (truncatedWindowedSource Src n (C.a k) τ')) := by
            intro τ' ha' _haτ hτ'hi
            apply truncatedWindowedSource_measurable_of_abs_ball
              (p := p) (w := fun s => U n s) (M := DT.M)
              DT.hM hU_joint
            · intro s has hsτ
              have hspos : 0 < s := ha'.trans_le has
              have hshi : s ≤ C.hi k := hsτ.trans hτ'hi
              exact hball_cont_n.2 s hspos (hshi.trans hhikT)
            · intro s has hsτ x
              have hspos : 0 < s := ha'.trans_le has
              have hshi : s ≤ C.hi k := hsτ.trans hτ'hi
              exact hball_cont_n.1 s hspos (hshi.trans hhikT) x
            · intro s has hsτ y hyIoo
              exact (hprev s has (hsτ.trans hτ'hi)).2 y hyIoo
            · intro s y
              rfl
          have hflux_reg : ∀ s, C.a k ≤ s → s ≤ C.hi k →
              ShenWork.Paper2.IntervalConjugateKernelIBP.IntervalIBPRegularity
                (truncatedChemFluxLifted p (U n s)) := by
            intro s has hshi
            have hspos : 0 < s := hak_pos.trans_le has
            have hsT : s ≤ DT.T := hshi.trans hhikT
            have hw_cont := hball_cont_n.2 s hspos hsT
            have hball := hball_cont_n.1 s hspos hsT
            have hgrad_s := hprev s has hshi
            have hC_nonneg : 0 ≤ A_F + B_F * Gw :=
              add_nonneg hAF_nn (mul_nonneg hBF_nn hGw_nn)
            have hderiv_bound : ∀ y ∈ Icc (0 : ℝ) 1,
                |deriv (truncatedChemFluxLifted p (U n s)) y| ≤
                  A_F + B_F * Gw := by
              intro y _hy
              by_cases hyIoo : y ∈ Ioo (0 : ℝ) 1
              · have hdiff_pos :
                    0 < intervalDomainLift (U n s) y →
                      DifferentiableAt ℝ (intervalDomainLift (U n s)) y :=
                  fun _ => hgrad_s.2 y hyIoo
                have hb :=
                  truncatedChemFluxLifted_deriv_abs_le_of_abs_ball_grad'
                    (p := p) (w := U n s) (M := DT.M) (G := Gw)
                    DT.hM hw_cont hball hgrad_s.1 y hdiff_pos
                convert hb using 1 <;>
                  (dsimp only [Mw, A_F, B_F, Γ_M, H_M, V_M] <;> ring)
              · rw [truncatedChemFluxLifted_deriv_eq_zero_off_Ioo
                    (p := p) (w := U n s) hyIoo, abs_zero]
                exact hC_nonneg
            exact truncatedChemFluxLifted_ibpRegularity_of_abs_ball
              p DT.hM hw_cont hball hgrad_s.2 hderiv_bound
          dsimp only [Mw]
          exact (truncatedConjugatePicardIter_succ_window_gradient
            (p := p) (u₀ := u₀) DT U (by intro n s; rfl) Src
            (by intro n s y; rfl)
            hAL_nn hAF_nn hBF_nn hGw_nn hak_pos haklo hlokhi hhikT)
            n hsource_meas hflux_reg hsrc }
  have hall : ∀ k, k ≤ C.N → ∀ n : ℕ,
      IterGradOnWindow U (C.lo k) (C.hi k) n Gw :=
    truncatedGradientWindow_chain_all
      (p := p) (U := U) (Src := Src)
      (M := Mw) (A_L := A_L) (A_F := A_F) (B_F := B_F) (G := Gw)
      (N := C.N) (a := fun k => C.a k) (lo := fun k => C.lo k)
      (hi := fun k => C.hi k)
      (fun k _ => C.next_a k) (fun k _ => C.overlap k)
      (by simpa [a, lo] using hleft_zero) hbuild
  have hlast : ∀ n : ℕ,
      IterGradOnWindow
        (fun n s => truncatedConjugatePicardIter p u₀ n s)
        (C.lo C.N) (C.hi C.N) n Gw := by
    simpa [U] using hall C.N le_rfl
  have hlast_lo_pos : 0 < C.lo C.N :=
    (C.a_pos C.N).trans (C.a_lt_lo C.N)
  have hlast_lo_t : C.lo C.N < t := by
    calc
      C.lo C.N < ((C.N : ℝ) + 4) * C.h := by
        dsimp [EqualStepGradientWindowChain.lo]
        nlinarith [C.h_pos]
      _ = t := C.target
  refine ⟨C.lo C.N, Gw, hlast_lo_pos, hlast_lo_t, hGw_nn, ?_⟩
  intro s hlos hst x hx y hy
  exact truncatedPicardLimit_lipschitzOn_of_window_grad
    DT (hlast_lo_pos.trans_le hlos) (hst.trans htT) hlos
      (by simpa [C.hi_last] using hst) hGw_nn hlast x hx y hy

/-- At every positive time, the lifted truncated Picard-limit slice is
Lipschitz on `[0,1]`. -/
theorem truncatedPicardLimit_lipschitzOn_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |intervalDomainLift
        ((truncatedConjugatePicardLimit p u₀ DT.T) t) x -
       intervalDomainLift
        ((truncatedConjugatePicardLimit p u₀ DT.T) t) y| ≤ G * |x - y| := by
  obtain ⟨lo, G, _hlo, hlot, hG, hwindow⟩ :=
    truncatedPicardLimit_lipschitzOn_positive_window DT ht htT
  exact ⟨G, hG, hwindow t hlot.le le_rfl⟩

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


#print axioms truncatedPicardLimit_lipschitzOn_positive_time
#print axioms truncatedChemFlux_continuousOn_positive_time

end ShenWork.Paper2.TruncatedPositiveTimeBootstrap
