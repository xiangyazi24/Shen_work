import ShenWork.Paper2.IntervalGradientSourceIBPOpen
import ShenWork.PDE.IntervalSemigroupNeumann
import ShenWork.PDE.IntervalFullKernelSpectralClean
import ShenWork.PDE.IntervalCoupledSourceTimeC1
import ShenWork.PDE.IntervalChemDivAEMeasurable
import ShenWork.PDE.IntervalSpectralSubtypeAdapter
import ShenWork.Paper2.IntervalDivergenceModeIdentity
import ShenWork.Paper2.IntervalMildPicardThreshold
import ShenWork.Paper2.IntervalGradientDuhamelMap

open MeasureTheory intervalIntegral
open scoped Topology

noncomputable section

namespace ShenWork.Paper2.IntervalGradientSourceBridgeOpen

open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalFullKernelSpectralClean
open ShenWork.IntervalSemigroupNeumann
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalDomain
  (intervalMeasure intervalDomain intervalDomainPoint intervalDomainLift
    intervalDomainChemotaxisDiv intervalDomainConstExtend constExtend_continuous
    constExtend_eq_lift_on_Icc)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalSpectralSubtypeAdapter
  (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont)
open ShenWork.IntervalMildPicardThreshold (unitClip unitClip_continuous unitClip_of_mem)
open ShenWork.Paper2.IntervalDivergenceModeIdentity
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceLift coupledLogisticSourceCoeffs
    coupledLogisticSourceLift resolver_lift_deriv_eq_resolverGradReal_of_sourceDecay)

/-- The sine-basis heat value on `[0,1]`, with the same heat eigenvalues as the
Neumann cosine side.  Mode `0` contributes zero because `sin 0 = 0`. -/
def unitIntervalSineHeatValue (t : ℝ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ,
    Real.exp (-t * unitIntervalCosineEigenvalue n) *
      Real.sin ((n : ℝ) * Real.pi * x) * a n

theorem sineCoeffs_eqOn_Icc {f g : ℝ → ℝ}
    (h : Set.EqOn f g (Set.Icc (0 : ℝ) 1)) :
    sineCoeffs f = sineCoeffs g := by
  funext n
  simp only [sineCoeffs]
  split_ifs with hn
  · rfl
  · congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    change Real.sin ((n : ℝ) * Real.pi * x) * f x =
      Real.sin ((n : ℝ) * Real.pi * x) * g x
    rw [h hx]

private theorem continuous_subtype_of_continuousOn_Icc {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    Continuous (fun x : intervalDomainPoint => f x.1) := by
  rw [← continuousOn_univ]
  exact hf.comp continuous_subtype_val.continuousOn (fun x _ => x.2)

/-- The globally bounded primitive used to feed the full-kernel derivative
theorem.  It agrees with the usual primitive `∫₀ˣ f` on `[0,1]`, but clips the
upper endpoint outside `[0,1]`, so it remains bounded on all of `ℝ`. -/
def clippedPrimitive (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..(unitClip x).1, f y

private theorem clippedPrimitive_eq_intervalPrimitive_on_Icc
    {f : ℝ → ℝ} {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    clippedPrimitive f x = ∫ y in (0 : ℝ)..x, f y := by
  simp [clippedPrimitive, unitClip_of_mem hx]

private theorem intervalPrimitive_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (fun z : ℝ => ∫ y in (0 : ℝ)..z, f y) (f x) x :=
  intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable (0 : ℝ) x)
    (hf.stronglyMeasurableAtFilter volume (𝓝 x))
    hf.continuousAt

private theorem intervalPrimitive_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous fun z : ℝ => ∫ y in (0 : ℝ)..z, f y :=
  continuous_iff_continuousAt.mpr fun x =>
    (intervalPrimitive_hasDerivAt hf x).continuousAt

theorem clippedPrimitive_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (clippedPrimitive f) := by
  have hval : Continuous fun x : ℝ => (unitClip x).1 :=
    continuous_subtype_val.comp unitClip_continuous
  exact (intervalPrimitive_continuous hf).comp hval

theorem clippedPrimitive_hasDerivWithinAt_Ioi
    {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (clippedPrimitive f) (f x) (Set.Ioi x) x := by
  have hbase := (intervalPrimitive_hasDerivAt hf x).hasDerivWithinAt (s := Set.Ioi x)
  have heq :
      clippedPrimitive f =ᶠ[nhdsWithin x (Set.Ioi x)]
        (fun z : ℝ => ∫ y in (0 : ℝ)..z, f y) := by
    filter_upwards [nhdsWithin_le_nhds (IsOpen.mem_nhds isOpen_Ioo hx)] with z hz
    exact clippedPrimitive_eq_intervalPrimitive_on_Icc (Set.Ioo_subset_Icc_self hz)
  exact hbase.congr_of_eventuallyEq heq
    (clippedPrimitive_eq_intervalPrimitive_on_Icc (Set.Ioo_subset_Icc_self hx))

/-- `sqrt ((nπ)^2) = nπ` in the repository's interval normalization. -/
theorem sqrt_unitIntervalCosineEigenvalue_eq_kpi (n : ℕ) :
    Real.sqrt (unitIntervalCosineEigenvalue n) = (n : ℝ) * Real.pi := by
  have hnonneg : 0 ≤ (n : ℝ) * Real.pi := by positivity
  unfold unitIntervalCosineEigenvalue
  rw [Real.sqrt_sq hnonneg]

/-- Spatial derivative of the cosine heat value, expressed as a sine heat value
with the expected `-sqrt(λ_n)` multiplier. -/
theorem deriv_unitIntervalCosineHeatValue_eq_sineHeat_weighted
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) (x : ℝ) :
    deriv (fun z : ℝ => unitIntervalCosineHeatValue t a z) x =
      unitIntervalSineHeatValue t
        (fun n => -Real.sqrt (unitIntervalCosineEigenvalue n) * a n) x := by
  have hb : Summable (fun n => unitIntervalCosineEigenvalue n *
      |Real.exp (-t * unitIntervalCosineEigenvalue n) * a n|) :=
    heatCoeff_eigenvalue_summable ht hM
  rw [unitIntervalCosineHeatValue_eq_cosineCoeffSeries]
  rw [(cosineCoeffSeries_grad_hasDerivAt hb x).deriv]
  unfold unitIntervalSineHeatValue
  refine tsum_congr (fun n => ?_)
  simp only
  rw [sqrt_unitIntervalCosineEigenvalue_eq_kpi n]
  ring_nf

/-- Sine coefficients of an open/right derivative: `sin` has zero boundary
values, so no endpoint condition on `Q` is needed. -/
theorem sineCoeffs_deriv_right_eq_neg_sqrtLambda_cosineCoeffs
    {Q Q' : ℝ → ℝ}
    (hQcont : ContinuousOn Q (Set.Icc (0 : ℝ) 1))
    (hQderiv : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt Q (Q' y) (Set.Ioi y) y)
    (hQ'_int : IntervalIntegrable Q' volume 0 1) (n : ℕ) :
    sineCoeffs Q' n =
      -Real.sqrt (unitIntervalCosineEigenvalue n) * cosineCoeffs Q n := by
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · simp [sineCoeffs, unitIntervalCosineEigenvalue]
  · have hn : n ≠ 0 := Nat.pos_iff_ne_zero.mp hnpos
    have h01 : (0 : ℝ) ≤ 1 := by norm_num
    set S : ℝ → ℝ := fun y => Real.sin ((n : ℝ) * Real.pi * y) with hS
    set S' : ℝ → ℝ := fun y => (n : ℝ) * Real.pi *
      Real.cos ((n : ℝ) * Real.pi * y) with hS'
    have hScont : ContinuousOn S (Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le h01]
      rw [hS]
      fun_prop
    have hQcont' : ContinuousOn Q (Set.uIcc (0 : ℝ) 1) := by
      rwa [Set.uIcc_of_le h01]
    have hSderiv :
        ∀ y ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
          HasDerivWithinAt S (S' y) (Set.Ioi y) y := by
      intro y _hy
      have hinner : HasDerivAt (fun z : ℝ => (n : ℝ) * Real.pi * z)
          ((n : ℝ) * Real.pi) y := by
        simpa using (hasDerivAt_id y).const_mul ((n : ℝ) * Real.pi)
      have hsin : HasDerivAt S (S' y) y := by
        rw [hS, hS']
        convert (Real.hasDerivAt_sin ((n : ℝ) * Real.pi * y)).comp y hinner using 1
        ring
      exact hsin.hasDerivWithinAt
    have hQderiv' :
        ∀ y ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
          HasDerivWithinAt Q (Q' y) (Set.Ioi y) y := by
      intro y hy
      rw [min_eq_left h01, max_eq_right h01] at hy
      exact hQderiv y hy
    have hS'_int : IntervalIntegrable S' volume 0 1 := by
      apply Continuous.intervalIntegrable
      rw [hS']
      fun_prop
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
      hScont hQcont' hSderiv hQderiv' hS'_int hQ'_int
    have hraw :
        (∫ y in (0 : ℝ)..1,
            Real.sin ((n : ℝ) * Real.pi * y) * Q' y)
          = -((n : ℝ) * Real.pi) *
              ∫ y in (0 : ℝ)..1,
                Real.cos ((n : ℝ) * Real.pi * y) * Q y := by
      change (∫ y in (0 : ℝ)..1, S y * Q' y)
          = -((n : ℝ) * Real.pi) *
              ∫ y in (0 : ℝ)..1,
                Real.cos ((n : ℝ) * Real.pi * y) * Q y
      have hboundary : S 1 * Q 1 - S 0 * Q 0 = 0 := by
        rw [hS]
        simp only [mul_one, mul_zero, Real.sin_zero, zero_mul, sub_zero]
        rw [Real.sin_nat_mul_pi]
        simp
      have hS'int :
          (∫ y in (0 : ℝ)..1, S' y * Q y)
            = (n : ℝ) * Real.pi *
                ∫ y in (0 : ℝ)..1,
                  Real.cos ((n : ℝ) * Real.pi * y) * Q y := by
        rw [hS', ← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr (fun y _hy => ?_)
        ring
      rw [hibp, hboundary, zero_sub, hS'int]
      ring
    rw [sineCoeffs_pos hn,
      ShenWork.IntervalMildPicardRegularity.cosineCoeffs_pos_eq_integral hn,
      hraw, sqrt_unitIntervalCosineEigenvalue_eq_kpi n]
    ring

/-- The open gradient-source spectral bridge: the spatial derivative of the full
Neumann semigroup applied to `Q` is the sine heat value of the open derivative
`Q'`.  This is the spectral form of the Task294 kernel IBP identity. -/
theorem deriv_intervalFullSemigroupOperator_eq_sineHeatValue_open
    {t : ℝ} (ht : 0 < t)
    {Q Q' : ℝ → ℝ}
    (hQcont : Continuous Q)
    (hQderiv : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt Q (Q' y) (Set.Ioi y) y)
    (hQ'_int : IntervalIntegrable Q' volume 0 1)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs Q n| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (fun z : ℝ => intervalFullSemigroupOperator t Q z) x =
      unitIntervalSineHeatValue t (sineCoeffs Q') x := by
  have heq_eventual :
      (fun z : ℝ => intervalFullSemigroupOperator t Q z)
        =ᶠ[nhds x]
      (fun z : ℝ => unitIntervalCosineHeatValue t (cosineCoeffs Q) z) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with z hz
    exact intervalFullSemigroupOperator_eq_cosineHeatValue_Icc ht hQcont hM
      (Set.Ioo_subset_Icc_self hz)
  rw [heq_eventual.deriv_eq]
  rw [deriv_unitIntervalCosineHeatValue_eq_sineHeat_weighted ht hM x]
  unfold unitIntervalSineHeatValue
  refine tsum_congr (fun n => ?_)
  rw [sineCoeffs_deriv_right_eq_neg_sqrtLambda_cosineCoeffs
    hQcont.continuousOn hQderiv hQ'_int n]

/-- Kernel-to-sine bridge for the gradient source leg.  Combining Task294's open
IBP formula with the spectral derivative bridge identifies the Ktilde source
integral with the sine heat value of the derivative source. -/
theorem neg_conjugateKernel_source_integral_eq_sineHeatValue_open
    {t : ℝ} (ht : 0 < t)
    {Q Q' : ℝ → ℝ}
    (hQ_meas : AEStronglyMeasurable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ_bound : ∀ y, |Q y| ≤ CQ)
    (hQcont : Continuous Q)
    (hQderiv : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt Q (Q' y) (Set.Ioi y) y)
    (hQ'_int : IntervalIntegrable Q' volume 0 1)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs Q n| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    -(∫ y in (0 : ℝ)..1,
        Q' y * intervalNeumannConjugateKernel t x y)
      = unitIntervalSineHeatValue t (sineCoeffs Q') x := by
  have hker :=
    deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_source_integral_open
      ht hQ_meas hQ_bound hQcont.continuousOn hQderiv hQ'_int x
  rw [← hker]
  exact deriv_intervalFullSemigroupOperator_eq_sineHeatValue_open ht hQcont
    hQderiv hQ'_int hM hx

/-- Direct Ktilde-to-sine value theorem for continuous source data, on the open
spatial interval.  This is the value-form version of the Task294 gradient-source
IBP bridge: the conjugate-kernel source integral is exactly the sine heat value
of the source's sine coefficients.

The proof uses a clipped primitive `Q = ∫₀^{clip x} f`: it is globally bounded,
continuous, and has right derivative `f` on `(0,1)`, so the open gradient-source
bridge above applies without any closed-endpoint derivative hypothesis. -/
theorem ktilde_source_integral_eq_sineHeatValue_open
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    -(∫ y in (0 : ℝ)..1,
        f y * intervalNeumannConjugateKernel t x y)
      = unitIntervalSineHeatValue t (sineCoeffs f) x := by
  set Q : ℝ → ℝ := clippedPrimitive f with hQdef
  have hQcont : Continuous Q := by
    rw [hQdef]
    exact clippedPrimitive_continuous hf
  have hQmeas : AEStronglyMeasurable Q (intervalMeasure 1) :=
    hQcont.aestronglyMeasurable
  have hQderiv : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt Q (f y) (Set.Ioi y) y := by
    intro y hy
    rw [hQdef]
    exact clippedPrimitive_hasDerivWithinAt_Ioi hf hy
  have hf_int : IntervalIntegrable f volume 0 1 :=
    hf.intervalIntegrable 0 1
  set P : ℝ → ℝ := fun z : ℝ => ∫ y in (0 : ℝ)..z, f y with hPdef
  have hPcont : Continuous P := by
    rw [hPdef]
    exact intervalPrimitive_continuous hf
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (hPcont.continuousOn (s := Set.Icc (0 : ℝ) 1))
  have hQ_bound_global : ∀ y : ℝ, |Q y| ≤ |B| := by
    intro y
    have hyclip : (unitClip y).1 ∈ Set.Icc (0 : ℝ) 1 := (unitClip y).2
    have hQeq : Q y = P (unitClip y).1 := by
      rw [hQdef, hPdef]
      rfl
    rw [hQeq]
    exact le_trans (by simpa [Real.norm_eq_abs] using hB (unitClip y).1 hyclip)
      (le_abs_self B)
  have hQ_bound_Icc : ∀ y ∈ Set.Icc (0 : ℝ) 1, |Q y| ≤ |B| := by
    intro y _hy
    exact hQ_bound_global y
  have hQ_coeff_bound : ∀ n, |cosineCoeffs Q n| ≤ 2 * |B| :=
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      hQcont.continuousOn (abs_nonneg B) hQ_bound_Icc
  exact neg_conjugateKernel_source_integral_eq_sineHeatValue_open
    ht hQmeas hQ_bound_global hQcont hQderiv hf_int hQ_coeff_bound hx

/-- Continuous-on-`[0,1]` Ktilde-to-sine value theorem.

This is the satisfiable form for zero-extended interval sources: the kernel
integral and sine coefficients only see `[0,1]`, so a constant extension of the
subtype slice supplies the global-continuity input required by the older theorem. -/
theorem ktilde_source_integral_eq_sineHeatValue_open_of_continuousOn
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    -(∫ y in (0 : ℝ)..1,
        f y * intervalNeumannConjugateKernel t x y)
      = unitIntervalSineHeatValue t (sineCoeffs f) x := by
  let F : intervalDomainPoint → ℝ := fun y => f y.1
  let fext : ℝ → ℝ := intervalDomainConstExtend F
  have hFcont : Continuous F := continuous_subtype_of_continuousOn_Icc hf
  have hfext : Continuous fext := by
    change Continuous (intervalDomainConstExtend F)
    exact constExtend_continuous hFcont
  have hEq : Set.EqOn f fext (Set.Icc (0 : ℝ) 1) := by
    intro y hy
    change f y = intervalDomainConstExtend F y
    rw [constExtend_eq_lift_on_Icc hy]
    simp [intervalDomainLift, F, hy]
  have hint :
      (∫ y in (0 : ℝ)..1,
          f y * intervalNeumannConjugateKernel t x y)
        =
      ∫ y in (0 : ℝ)..1,
          fext y * intervalNeumannConjugateKernel t x y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
    change f y * intervalNeumannConjugateKernel t x y =
      fext y * intervalNeumannConjugateKernel t x y
    rw [hEq hy]
  have hsine : sineCoeffs f = sineCoeffs fext := sineCoeffs_eqOn_Icc hEq
  rw [hint, hsine]
  exact ktilde_source_integral_eq_sineHeatValue_open ht hfext hx

/-- Classical-solution producer for the open chemotaxis-flux derivative input
used by the slice bridge below.  The derivative theorem is the existing
physical flux statement; this lemma only rewrites its `deriv (lift resolver)`
factor to `resolverGradReal` on the open interval. -/
theorem chemFluxLifted_hasDerivWithinAt_coupledChemDivSourceLift_open_of_classical
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u
      (coupledChemicalConcentration p u))
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (chemFluxLifted p (u s))
        (coupledChemDivSourceLift p u s y) (Set.Ioi y) y := by
  intro y hy
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
  let Y : intervalDomainPoint := ⟨y, hyIcc⟩
  have hflux :
      HasDerivAt
        (fun y' : ℝ =>
          intervalDomainLift (u s) y' *
            deriv (intervalDomainLift (coupledChemicalConcentration p u s)) y' /
            (1 + intervalDomainLift (coupledChemicalConcentration p u s) y') ^ p.β)
        (intervalDomainChemotaxisDiv p (u s)
          (coupledChemicalConcentration p u s) Y) y :=
    solution_chemotaxisFlux_hasDerivAt
      (p := p) (T := T) (u := u)
      (v := coupledChemicalConcentration p u) hsol hs (y := Y) hy
  have hdecay : SourceCoeffQuadraticDecay p (u s) :=
    sourceCoeffQuadraticDecay_of_solution hsol hs
  have heq_fun :
      chemFluxLifted p (u s) =ᶠ[𝓝 y]
        (fun y' : ℝ =>
          intervalDomainLift (u s) y' *
            deriv (intervalDomainLift (coupledChemicalConcentration p u s)) y' /
            (1 + intervalDomainLift (coupledChemicalConcentration p u s) y') ^ p.β) := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo hy] with z hz
    have hgradR :
        deriv (intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (u s))) z =
          resolverGradReal p (u s) z := by
      simpa [coupledChemicalConcentration] using
        resolver_lift_deriv_eq_resolverGradReal_of_sourceDecay
          (p := p) (u := u s) hdecay hz
    unfold chemFluxLifted
    simp [coupledChemicalConcentration]
    rw [hgradR]
  have hvalue :
      intervalDomainChemotaxisDiv p (u s) (coupledChemicalConcentration p u s) Y =
        coupledChemDivSourceLift p u s y := by
    change intervalDomainChemotaxisDiv p (u s) (coupledChemicalConcentration p u s) Y =
      intervalDomainLift
        (fun x => intervalDomainChemotaxisDiv p (u s)
          (coupledChemicalConcentration p u s) x) y
    simp [intervalDomainLift, hyIcc, Y]
  have hchem :
      HasDerivAt (chemFluxLifted p (u s))
        (coupledChemDivSourceLift p u s y) y := by
    have h := hflux.congr_of_eventuallyEq heq_fun
    rwa [hvalue] at h
  exact hchem.hasDerivWithinAt

/-- Per-slice gradient-source bridge for the actual weak Duhamel flux and
logistic source.  The chemotaxis gradient leg is converted through the open
Ktilde/sine bridge, while the logistic leg remains the standard Neumann cosine
heat value. -/
theorem gradient_source_bridge_slice_open
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {r x s : ℝ} (hr : 0 < r) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hchem_cont : Continuous (chemFluxLifted p (u s)))
    {Cchem : ℝ}
    (hchem_bound : ∀ y : ℝ, |chemFluxLifted p (u s) y| ≤ Cchem)
    (hQderiv : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (chemFluxLifted p (u s))
        (coupledChemDivSourceLift p u s y) (Set.Ioi y) y)
    (hdiv_cont : Continuous (coupledChemDivSourceLift p u s))
    (hlog_cont : Continuous (logisticLifted p (u s)))
    {Mlog : ℝ}
    (hlog_bound : ∀ n, |cosineCoeffs (logisticLifted p (u s)) n| ≤ Mlog) :
    (-p.χ₀) *
        deriv (fun z : ℝ =>
          intervalFullSemigroupOperator r (chemFluxLifted p (u s)) z) x
      + intervalFullSemigroupOperator r (logisticLifted p (u s)) x
      =
    (-p.χ₀) *
        unitIntervalSineHeatValue r
          (sineCoeffs (coupledChemDivSourceLift p u s)) x
      + unitIntervalCosineHeatValue r
          (coupledLogisticSourceCoeffs p u s) x := by
  have hgrad_kernel :=
    deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_source_integral_open
      hr hchem_cont.aestronglyMeasurable hchem_bound hchem_cont.continuousOn
      hQderiv (hdiv_cont.intervalIntegrable 0 1) x
  have hktilde :=
    ktilde_source_integral_eq_sineHeatValue_open
      (t := r) hr (f := coupledChemDivSourceLift p u s) hdiv_cont hx
  have hgrad :
      deriv (fun z : ℝ =>
        intervalFullSemigroupOperator r (chemFluxLifted p (u s)) z) x =
        unitIntervalSineHeatValue r
          (sineCoeffs (coupledChemDivSourceLift p u s)) x := by
    rw [hgrad_kernel, hktilde]
  have hlog :
      intervalFullSemigroupOperator r (logisticLifted p (u s)) x =
        unitIntervalCosineHeatValue r
          (cosineCoeffs (logisticLifted p (u s))) x :=
    intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
      hr hlog_cont hlog_bound (Set.Ioo_subset_Icc_self hx)
  have hlog_coeff :
      coupledLogisticSourceCoeffs p u s =
        cosineCoeffs (logisticLifted p (u s)) := by
    funext n
    simp [coupledLogisticSourceCoeffs, coupledLogisticSourceLift, logisticLifted]
  rw [hgrad, hlog, ← hlog_coeff]

/-- Satisfiable continuous-on-`[0,1]` version of the per-slice gradient-source
bridge.  This avoids the false global-continuity requirement on zero-extended
interval data while keeping the same mixed sine/cosine conclusion. -/
theorem gradient_source_bridge_slice_open_continuousOn
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {r x s : ℝ} (hr : 0 < r) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hchem_meas : AEStronglyMeasurable (chemFluxLifted p (u s)) (intervalMeasure 1))
    (hchem_cont : ContinuousOn (chemFluxLifted p (u s)) (Set.Icc (0 : ℝ) 1))
    {Cchem : ℝ}
    (hchem_bound : ∀ y : ℝ, |chemFluxLifted p (u s) y| ≤ Cchem)
    (hQderiv : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (chemFluxLifted p (u s))
        (coupledChemDivSourceLift p u s y) (Set.Ioi y) y)
    (hdiv_cont : ContinuousOn (coupledChemDivSourceLift p u s) (Set.Icc (0 : ℝ) 1))
    (hlog_cont : Continuous (intervalLogisticSource p (u s)))
    {Mlog : ℝ}
    (hlog_bound : ∀ n, |cosineCoeffs (logisticLifted p (u s)) n| ≤ Mlog) :
    (-p.χ₀) *
        deriv (fun z : ℝ =>
          intervalFullSemigroupOperator r (chemFluxLifted p (u s)) z) x
      + intervalFullSemigroupOperator r (logisticLifted p (u s)) x
      =
    (-p.χ₀) *
        unitIntervalSineHeatValue r
          (sineCoeffs (coupledChemDivSourceLift p u s)) x
      + unitIntervalCosineHeatValue r
          (coupledLogisticSourceCoeffs p u s) x := by
  have hdiv_int :
      IntervalIntegrable (coupledChemDivSourceLift p u s) volume (0 : ℝ) 1 :=
    (by
      rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] :
        ContinuousOn (coupledChemDivSourceLift p u s) (Set.uIcc (0 : ℝ) 1)
    ).intervalIntegrable
  have hgrad_kernel :=
    deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_source_integral_open
      hr hchem_meas hchem_bound hchem_cont hQderiv hdiv_int x
  have hktilde :=
    ktilde_source_integral_eq_sineHeatValue_open_of_continuousOn
      (t := r) hr (f := coupledChemDivSourceLift p u s) hdiv_cont hx
  have hgrad :
      deriv (fun z : ℝ =>
        intervalFullSemigroupOperator r (chemFluxLifted p (u s)) z) x =
        unitIntervalSineHeatValue r
          (sineCoeffs (coupledChemDivSourceLift p u s)) x := by
    rw [hgrad_kernel, hktilde]
  have hlog_bound' :
      ∀ n, |cosineCoeffs (intervalDomainLift (intervalLogisticSource p (u s))) n|
        ≤ Mlog := by
    simpa [logisticLifted] using hlog_bound
  have hlog :
      intervalFullSemigroupOperator r (logisticLifted p (u s)) x =
        unitIntervalCosineHeatValue r
          (cosineCoeffs (logisticLifted p (u s))) x := by
    have hraw :=
      intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
        (t := r) hr (f := intervalLogisticSource p (u s)) hlog_cont
        hlog_bound' (Set.Ioo_subset_Icc_self hx)
    simpa [logisticLifted] using hraw
  have hlog_coeff :
      coupledLogisticSourceCoeffs p u s =
        cosineCoeffs (logisticLifted p (u s)) := by
    funext n
    simp [coupledLogisticSourceCoeffs, coupledLogisticSourceLift, logisticLifted]
  rw [hgrad, hlog, ← hlog_coeff]

end ShenWork.Paper2.IntervalGradientSourceBridgeOpen
