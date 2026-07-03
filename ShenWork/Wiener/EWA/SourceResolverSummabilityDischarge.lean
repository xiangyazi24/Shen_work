import ShenWork.Wiener.EWA.SourceCenterFloorHeat
import ShenWork.Wiener.EWA.SourceChiNegUncondWire
import ShenWork.Wiener.EWA.SourceInversion
import ShenWork.Wiener.EWA.SourceEvalBridge
import ShenWork.Wiener.WeightedL1EvalDeriv
import ShenWork.Paper2.IntervalDomainResolverStrictPos
import ShenWork.PDE.IntervalSemigroupNeumann
import ShenWork.Paper2.IntervalPicardLimitRestartWeak
import ShenWork.Wiener.EWA.SourceL1ContOnBridge
import ShenWork.Wiener.EWA.ChemDivEval
import ShenWork.Paper2.IntervalDomainPdeUWiring
import ShenWork.Wiener.EWA.SourcePerSliceClose

/-!
# Discharge `hsource` (ResolverSourceSummable) from EWA structure

## Heat center (Theorem 1)

`resolverSourceSummable_of_heat` proves ℓ¹ summability of the
resolver source coefficients for the heat center — derived from
the EWA structure via `summable_abs_of_slice_eq`.

## General even-real element (Theorem 3)

`resolverSourceSummable_of_evenReal` proves the same for ANY
even-real EWA element `U` with uniform floor — in particular
for the Picard fixed point `u_star`. This discharges `hsumR`
in the v2 chain.

## Strengthened center floor (Theorem 2)

`vdEWA_center_floor_heat_discharged` drops the `hsource`
hypothesis from `vdEWA_center_floor_heat`.
-/

open scoped BigOperators
open Set
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint)
open ShenWork.PDE (intervalNeumannResolverSourceCoeff
  intervalNeumannResolverCoeff intervalNeumannResolver_denom_pos)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

theorem resolverSourceSummable_of_heat
    (p : CM2Params) (u₀ : ℝ → ℝ) (hu₀ : Continuous u₀)
    {δ : ℝ} (hδpos : 0 < δ)
    (hfloor : ∀ y, δ ≤ u₀ y)
    (hsumc : Summable (fun k => |cosineCoeffs u₀ k|))
    (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀)))
    (uR : ℝ → intervalDomainPoint → ℝ)
    (huR : uR = fun t pt =>
      unitIntervalCosineHeatValue t (cosineCoeffs u₀) pt.1)
    (τ : TimeDom T) :
    ResolverSourceSummable p (uR τ.1) := by
  set c₀ : ℕ → ℝ := cosineCoeffs u₀ with hc₀
  set u₀E : WA 1 :=
    ⟨ofCosineCoeffs c₀, hmem⟩ with hu₀E
  have hheatER : EvenRealEWA (heatEWA (T := T) u₀E) :=
    heatEWA_evenReal c₀ hmem
  have hER : EvenRealEWA
      (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        ((p.ν : ℂ) • realPowEWA
          (heatEWA (T := T) u₀E) p.γ)) :=
    ((realPowEWA_evenReal FnegEWA_evenReal_Hyp_proved
        hheatER p.γ).smul_real p.ν).incl (by omega)
  have hheatFloor :
      UniformFloor (heatEWA (T := T) u₀E) δ :=
    heatEWA_uniformFloor hu₀ hfloor hsumc hmem
  have hheatReal : ∀ (τ' : TimeDom T) (x : WA.Circ),
      (evalST τ' x (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (heatEWA (T := T) u₀E))).im = 0 := by
    intro τ' x
    induction x using QuotientAddGroup.induction_on with
    | _ x =>
      rw [heatEWA_evalST_eq_cosineHeatValue
        c₀ hsumc hmem τ' x, Complex.ofReal_im]
  have hlift : ∀ (t : ℝ) (y : ℝ),
      y ∈ Set.Icc (0 : ℝ) 1 →
      intervalDomainLift (uR t) y =
        unitIntervalCosineHeatValue t c₀ y := by
    intro t y hy
    rw [intervalDomainLift, dif_pos hy, huR]
  have hRealize : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (x : WA.Circ)
        (GWA.incl (by omega : (0 : ℕ) ≤ 1)
          ((p.ν : ℂ) • realPowEWA
            (heatEWA (T := T) u₀E) p.γ))
        = ((p.ν * intervalDomainLift (uR τ.1) x ^ p.γ
            : ℝ) : ℂ) := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hx.1.le, hx.2.le⟩
    have hincl_smul :
        GWA.incl (by omega : (0 : ℕ) ≤ 1)
          ((p.ν : ℂ) • realPowEWA
            (heatEWA (T := T) u₀E) p.γ)
        = (p.ν : ℂ) • GWA.incl (by omega : (0 : ℕ) ≤ 1)
            (realPowEWA
              (heatEWA (T := T) u₀E) p.γ) := by
      rw [← GWA.gIncl_apply, map_smul,
        GWA.gIncl_apply]
    rw [hincl_smul, evalST_smul]
    rw [realPowEWA_eval p.hγ.le hδpos hheatFloor
      hheatReal τ (x : WA.Circ)]
    rw [heatEWA_evalST_eq_cosineHeatValue
      c₀ hsumc hmem τ x, Complex.ofReal_re]
    rw [hlift (τ : ℝ) x hxIcc]
    push_cast
    ring
  have hWslice :
      (sliceWA τ (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        ((p.ν : ℂ) • realPowEWA
          (heatEWA (T := T) u₀E) p.γ))).toFun
      = ofCosineCoeffs
          (resolverSourceReCoeff p (uR τ.1)) :=
    slice_smul_realPow_eq_source p uR
      (heatEWA (T := T) u₀E) τ hER hRealize
  exact summable_abs_of_slice_eq hWslice

theorem vdEWA_center_floor_heat_discharged
    (p : CM2Params) (u₀ : ℝ → ℝ) (hu₀ : Continuous u₀)
    {δ : ℝ} (hδpos : 0 < δ)
    (hfloor : ∀ y, δ ≤ u₀ y) (hνpos : 0 ≤ p.ν)
    (hsumc : Summable (fun k => |cosineCoeffs u₀ k|))
    (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀))) :
    UniformFloor (1 + vdEWA p.μ p.ν p.γ p.hμ
      (heatEWA (T := T)
        (⟨ofCosineCoeffs (cosineCoeffs u₀),
          hmem⟩ : WA 1))) 1 := by
  set uR : ℝ → intervalDomainPoint → ℝ :=
    fun t pt =>
      unitIntervalCosineHeatValue t (cosineCoeffs u₀) pt.1
  have hsource : ∀ τ : TimeDom T,
      ResolverSourceSummable p (uR τ.1) :=
    resolverSourceSummable_of_heat p u₀ hu₀
      hδpos hfloor hsumc hmem uR rfl
  exact vdEWA_center_floor_heat p u₀ hu₀ hδpos hfloor
    hνpos hsumc hmem uR rfl hsource

#print axioms resolverSourceSummable_of_heat
#print axioms vdEWA_center_floor_heat_discharged

theorem resolverSourceSummable_of_evenReal
    (p : CM2Params) (U : EWA T 1)
    (hER_U : EvenRealEWA U)
    {δ : ℝ} (hδpos : 0 < δ)
    (hfloor : UniformFloor U δ)
    (τ : TimeDom T) :
    ResolverSourceSummable p (realSlice U τ.1) := by
  have hER : EvenRealEWA
      (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        ((p.ν : ℂ) • realPowEWA U p.γ)) :=
    ((realPowEWA_evenReal FnegEWA_evenReal_Hyp_proved
        hER_U p.γ).smul_real p.ν).incl (by omega)
  have hUReal :=
    evalST_incl_im_zero_of_evenReal hER_U
  have hRealize : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (x : WA.Circ)
        (GWA.incl (by omega : (0 : ℕ) ≤ 1)
          ((p.ν : ℂ) • realPowEWA U p.γ))
        = ((p.ν *
            intervalDomainLift (realSlice U τ.1) x
              ^ p.γ : ℝ) : ℂ) := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hx.1.le, hx.2.le⟩
    have hincl_smul :
        GWA.incl (by omega : (0 : ℕ) ≤ 1)
          ((p.ν : ℂ) • realPowEWA U p.γ)
        = (p.ν : ℂ) •
            GWA.incl (by omega : (0 : ℕ) ≤ 1)
              (realPowEWA U p.γ) := by
      rw [← GWA.gIncl_apply, map_smul,
        GWA.gIncl_apply]
    rw [hincl_smul, evalST_smul]
    rw [realPowEWA_eval p.hγ.le hδpos hfloor
      hUReal τ (x : WA.Circ)]
    have hbase :=
      realSlice_evalST_realizes U τ x hxIcc
        (hUReal τ (x : WA.Circ))
    rw [hbase, Complex.ofReal_re]
    push_cast
    ring
  have hWslice :
      (sliceWA τ (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        ((p.ν : ℂ) • realPowEWA U p.γ))).toFun
      = ofCosineCoeffs
          (resolverSourceReCoeff p
            (realSlice U τ.1)) :=
    slice_smul_realPow_eq_source p (realSlice U)
      U τ hER hRealize
  exact summable_abs_of_slice_eq hWslice

#print axioms resolverSourceSummable_of_evenReal

theorem resolverGradSummable_of_sourceSummable
    (p : CM2Params) (u : intervalDomainPoint → ℝ)
    (hsum : ResolverSourceSummable p u) :
    Summable (fun k : ℕ =>
      |(intervalNeumannResolverCoeff p u k).re|
        * ((k : ℝ) * Real.pi)) := by
  have hμ := p.hμ
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (abs_nonneg _)
      (mul_nonneg (Nat.cast_nonneg k) Real.pi_nonneg))
    (fun k => ?_)
    (hsum.div_const (2 * Real.sqrt p.μ))
  have hden : 0 < p.μ + ((k : ℝ) * Real.pi) ^ 2 := by
    positivity
  rw [← resolverOutputCoeff_eq_resolverCoeff_re p u k,
    abs_div, abs_of_pos hden]
  have hkpi_nn : (0 : ℝ) ≤ (k : ℝ) * Real.pi :=
    mul_nonneg (Nat.cast_nonneg k) Real.pi_nonneg
  have key : (k : ℝ) * Real.pi / (p.μ + ((k : ℝ) * Real.pi) ^ 2)
      ≤ 1 / (2 * Real.sqrt p.μ) := by
    rw [div_le_div_iff₀ hden (by positivity)]
    nlinarith [sq_nonneg (Real.sqrt p.μ - (k : ℝ) * Real.pi),
      Real.sq_sqrt hμ.le]
  calc |resolverSourceReCoeff p u k|
        / (p.μ + ((k : ℝ) * Real.pi) ^ 2)
        * ((k : ℝ) * Real.pi)
      = |resolverSourceReCoeff p u k|
        * ((k : ℝ) * Real.pi
          / (p.μ + ((k : ℝ) * Real.pi) ^ 2)) := by
          ring
    _ ≤ |resolverSourceReCoeff p u k|
        * (1 / (2 * Real.sqrt p.μ)) :=
          mul_le_mul_of_nonneg_left key (abs_nonneg _)
    _ = |resolverSourceReCoeff p u k|
        / (2 * Real.sqrt p.μ) := by ring

theorem resolverGradSummable_of_evenReal
    (p : CM2Params) (U : EWA T 1)
    (hER_U : EvenRealEWA U)
    {δ : ℝ} (hδpos : 0 < δ)
    (hfloor : UniformFloor U δ)
    (τ : TimeDom T) :
    Summable (fun k : ℕ =>
      |(intervalNeumannResolverCoeff p
        (realSlice U τ.1) k).re|
        * ((k : ℝ) * Real.pi)) :=
  resolverGradSummable_of_sourceSummable p
    (realSlice U τ.1)
    (resolverSourceSummable_of_evenReal p U
      hER_U hδpos hfloor τ)

#print axioms resolverGradSummable_of_sourceSummable
#print axioms resolverGradSummable_of_evenReal

/-! ### Resolver gradient second-derivative majorant from ℓ¹ source summability

The second derivative of the resolver gradient requires
`Summable (fun k => |resolverCoeff k| * (kπ)²)`.
Since `resolverCoeff k = sourceCoeff k / (μ + (kπ)²)`, we have
`|resolverCoeff k| * (kπ)² ≤ |sourceCoeff k|`, so ℓ¹ source
summability implies the majorant. This bypasses `SourceCoeffQuadraticDecay`. -/

open ShenWork.Paper3 (unitIntervalNeumannSpectrum) in
open ShenWork.IntervalResolverGradientBridge (resolverCoeff_re_eq) in
theorem resolverGrad2Summable_of_sourceSummable
    (p : CM2Params) (u : intervalDomainPoint → ℝ)
    (hsumR : ResolverSourceSummable p u) :
    Summable (fun k : ℕ =>
      |(intervalNeumannResolverCoeff p u k).re| * ((k : ℝ) * Real.pi) ^ 2) := by
  have hle : ∀ k : ℕ,
      |(intervalNeumannResolverCoeff p u k).re| * ((k : ℝ) * Real.pi) ^ 2
        ≤ |resolverSourceReCoeff p u k| := by
    intro k
    have hden_pos := intervalNeumannResolver_denom_pos p k
    rw [resolverCoeff_re_eq, abs_div, abs_of_pos hden_pos, resolverSourceReCoeff,
      div_mul_eq_mul_div]
    rw [div_le_iff₀ hden_pos]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hlam : unitIntervalNeumannSpectrum.eigenvalue k = (k : ℝ) ^ 2 * Real.pi ^ 2 := rfl
    rw [hlam]
    have : ((k : ℝ) * Real.pi) ^ 2 = (k : ℝ) ^ 2 * Real.pi ^ 2 := by ring
    rw [this]; linarith [p.hμ.le]
  exact Summable.of_nonneg_of_le (fun k => by positivity) hle hsumR

#print axioms resolverGrad2Summable_of_sourceSummable

open ShenWork.Paper2 (resolverGradReal resolverGrad2Real) in
open ShenWork.IntervalResolverGradientBridge
  (resolverGrad_hasDerivAt_grad2) in
theorem resolverGradReal_hasDerivAt_of_sourceSummable
    (p : CM2Params) (u : intervalDomainPoint → ℝ)
    (hsumR : ResolverSourceSummable p u) (z : ℝ) :
    HasDerivAt (fun y : ℝ => resolverGradReal p u y)
      (resolverGrad2Real p u z) z :=
  resolverGrad_hasDerivAt_grad2
    (resolverGrad2Summable_of_sourceSummable p u hsumR) z

#print axioms resolverGradReal_hasDerivAt_of_sourceSummable

/-! ### Source function family (f-family) from WA evaluation

The source function `f(t, y) = ν · (evalAt (y:Circ) (sliceWA τ (incl U))).re ^ γ`
is continuous, nonneg, and its cosine coefficients match the resolver source.
This breaks the circular dependency in the v2 chain: previously, `realSlice`
continuity required `hrealizes + hsumE`, which required the f-family. Now
it follows directly from the Wiener algebra structure (WA 0 elements are
continuous functions on the circle). -/

theorem evalAt_re_continuous (b : WA 0) :
    Continuous (fun y : ℝ => (WA.evalAt (y : WA.Circ) b).re) :=
  Complex.continuous_re.comp
    ((WA.evalLin b).continuous.comp continuous_quotient_mk')

theorem sliceWA_incl_eq_toZero_sliceWA (U : EWA T 1) (τ : TimeDom T) :
    sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1) U) = WA.toZero (sliceWA τ U) := by
  apply WA.ext; funext n
  rw [coeff_sliceWA_incl, WA.toZero_toFun]

theorem intervalDomainLift_differentiableAt_of_EWA
    (U : EWA T 1) (τ : TimeDom T)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (intervalDomainLift (realSlice U τ.1)) x := by
  have hnhds : Set.Ioo (0 : ℝ) 1 ∈ nhds x := isOpen_Ioo.mem_nhds hx
  have hc := WA.evalC_hasDerivAt_wD (sliceWA τ U) x
  have hdaC : DifferentiableAt ℝ
      (fun y : ℝ => WA.evalC (WA.toZero (sliceWA τ U)) (y : WA.Circ)) x :=
    hc.differentiableAt
  have hda : DifferentiableAt ℝ
      (fun y : ℝ => (WA.evalC (WA.toZero (sliceWA τ U)) (y : WA.Circ)).re) x :=
    Complex.reCLM.differentiableAt.comp x hdaC
  refine hda.congr_of_eventuallyEq ?_
  filter_upwards [hnhds] with y hy
  show intervalDomainLift (realSlice U τ.1) y
    = (Complex.reCLM ∘ (fun z : ℝ =>
        WA.evalC (WA.toZero (sliceWA τ U)) (z : WA.Circ))) y
  simp only [Function.comp, Complex.reCLM_apply]
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
  simp only [intervalDomainLift, dif_pos hyIcc,
    realSlice, dif_pos τ.2, evalST_apply]
  rw [WA.evalAt_apply, ← WA.evalC_apply, sliceWA_incl_eq_toZero_sliceWA]

#print axioms sliceWA_incl_eq_toZero_sliceWA
#print axioms intervalDomainLift_differentiableAt_of_EWA

theorem sourceFn_continuous (p : CM2Params) (U : EWA T 1)
    {δ : ℝ} (hδpos : 0 < δ) (hfloor : UniformFloor U δ)
    (τ : TimeDom T) :
    Continuous (fun y : ℝ =>
      p.ν * (WA.evalAt (y : WA.Circ)
        (sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1) U))).re
          ^ p.γ) := by
  have hbase := evalAt_re_continuous
    (sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1) U))
  have hne : ∀ y : ℝ,
      (WA.evalAt (y : WA.Circ)
        (sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1) U))).re ≠ 0 := by
    intro y
    have hf := hfloor τ (y : WA.Circ)
    exact ne_of_gt (lt_of_lt_of_le hδpos hf)
  exact continuous_const.mul
    (hbase.rpow_const (fun y => Or.inl (hne y)))

theorem sourceFn_nonneg (p : CM2Params) (U : EWA T 1)
    (hνnn : 0 ≤ p.ν)
    {δ : ℝ} (hδpos : 0 < δ) (hfloor : UniformFloor U δ)
    (τ : TimeDom T) (y : ℝ) :
    0 ≤ p.ν * (WA.evalAt (y : WA.Circ)
      (sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1) U))).re
        ^ p.γ :=
  mul_nonneg hνnn (Real.rpow_nonneg
    (le_trans hδpos.le (hfloor τ (y : WA.Circ))) p.γ)

theorem sourceFn_coeff (p : CM2Params) (U : EWA T 1)
    (τ : TimeDom T) (k : ℕ) :
    cosineCoeffs (fun y : ℝ =>
      p.ν * (WA.evalAt (y : WA.Circ)
        (sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1) U))).re
          ^ p.γ) k
      = (intervalNeumannResolverSourceCoeff p
          (realSlice U τ.1) k).re := by
  rw [show (intervalNeumannResolverSourceCoeff p
      (realSlice U τ.1) k).re
    = resolverSourceReCoeff p (realSlice U τ.1) k from rfl,
    resolverSourceReCoeff_eq_cosineCoeffs]
  refine cosineCoeffs_congr_on_Icc (fun y hy => ?_) k
  simp only [realSlice, dif_pos τ.2, intervalDomainLift,
    dif_pos hy, evalST_apply]

theorem summable_sq_of_summable_abs {a : ℕ → ℝ}
    (hℓ1 : Summable (fun k => |a k|)) :
    Summable (fun k => (a k) ^ 2) := by
  have htend := hℓ1.tendsto_atTop_zero
  have hev : ∀ᶠ k in Filter.atTop, |a k| < 1 := by
    simpa using htend.eventually
      (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have htail : Summable (fun k => (a (k + N)) ^ 2) :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _)
      (fun k => by
        have hk := (hN (k + N) (by omega)).le
        rw [← sq_abs, sq]
        exact mul_le_of_le_one_left (abs_nonneg _) hk)
      ((summable_nat_add_iff N).mpr hℓ1)
  exact (summable_nat_add_iff N).mp htail

theorem sourceFn_sq_summable (p : CM2Params) (U : EWA T 1)
    (hER_U : EvenRealEWA U)
    {δ : ℝ} (hδpos : 0 < δ) (hfloor : UniformFloor U δ)
    (τ : TimeDom T) :
    Summable (fun k => (cosineCoeffs (fun y : ℝ =>
      p.ν * (WA.evalAt (y : WA.Circ)
        (sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1) U))).re
          ^ p.γ) k) ^ 2) := by
  have hcoeff : ∀ k, cosineCoeffs (fun y =>
      p.ν * (WA.evalAt (y : WA.Circ)
        (sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1) U))).re
          ^ p.γ) k
    = resolverSourceReCoeff p (realSlice U τ.1) k := by
    intro k
    simp only [sourceFn_coeff, resolverSourceReCoeff]
  simp_rw [hcoeff]
  exact summable_sq_of_summable_abs
    (resolverSourceSummable_of_evenReal p U hER_U hδpos hfloor τ)

/-! ### Discharge h_src_cont_log (wLog continuity) from EWA evaluation -/

open ShenWork.IntervalDomainExistence (intervalLogisticSource) in
theorem wLog_continuous_of_floor (p : CM2Params) (U : EWA T 1)
    {δ : ℝ} (hδpos : 0 < δ) (hfloor : UniformFloor U δ)
    (τ : TimeDom T) :
    Continuous (wLog p U τ.1) := by
  unfold wLog intervalLogisticSource
  have hbase : Continuous (fun x : intervalDomainPoint =>
      realSlice U τ.1 x) := by
    have heq : (fun x : intervalDomainPoint => realSlice U τ.1 x) =
        (fun x : intervalDomainPoint =>
          (WA.evalAt ((x.1 : ℝ) : WA.Circ)
            (sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1) U))).re) := by
      funext x
      simp only [realSlice, dif_pos τ.2, evalST_apply]
    rw [heq]
    exact (evalAt_re_continuous
      (sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1) U))).comp
        continuous_subtype_val
  have hpos : ∀ x : intervalDomainPoint, 0 < realSlice U τ.1 x := by
    intro x
    have hf := hfloor τ ((x.1 : ℝ) : WA.Circ)
    simp only [realSlice, dif_pos τ.2, evalST_apply] at hf ⊢
    exact lt_of_lt_of_le hδpos hf
  have hpow : Continuous (fun x : intervalDomainPoint =>
      (realSlice U τ.1 x) ^ p.α) :=
    hbase.rpow_const (fun x => Or.inl (ne_of_gt (hpos x)))
  exact hbase.mul (continuous_const.sub (continuous_const.mul hpow))

/-! ### Discharge h_flux_diff from EWA structure (breaks the circularity)

The existing `chemFluxLifted_differentiableAt_of_decay` requires `hsumE + hrealizes`
(via `SourceCoeffQuadraticDecay`), creating a circular dependency with `realizes_clean`.
This version proves `chemFluxLifted` differentiability directly from:
- WA 1 → `intervalDomainLift (realSlice u_star τ)` is C¹ (term-by-term differentiation)
- `ResolverSourceSummable` → resolver gradient second-derivative majorant is ℓ¹
  → `resolverGradReal` is C¹
- `resolverGradSummable` → resolver R cosine series has abs-convergent derivative
  → `intervalDomainLift (resolverR)` is DifferentiableAt
- `UniformFloor` → resolver R positivity → `rpow` on positive base is DifferentiableAt
No cosine series representation (`hrealizes`) or eigenvalue-weighted summability
(`hsumE`) needed — breaking the circular dependency. -/

/-! ### Resolver lift differentiability from EWA -/

open ShenWork.PDE (intervalNeumannResolverR) in
open ShenWork.IntervalResolverGradientBridge (resolverR_hasDerivAt_grad) in
theorem liftResolverR_differentiableAt_of_EWA
    (p : CM2Params) (U : EWA T 1)
    (hER : EvenRealEWA U)
    {δ : ℝ} (hδpos : 0 < δ)
    (hfloor : UniformFloor U δ)
    (τ : TimeDom T)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (intervalDomainLift (intervalNeumannResolverR p (realSlice U τ.1))) x := by
  set w := realSlice U τ.1
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  have hnhds : Set.Ioo (0 : ℝ) 1 ∈ nhds x := isOpen_Ioo.mem_nhds hx
  have hsumR : ResolverSourceSummable p w :=
    resolverSourceSummable_of_evenReal p U hER hδpos hfloor τ
  have hgrad : Summable (fun k : ℕ =>
      |(intervalNeumannResolverCoeff p w k).re| * ((k : ℝ) * Real.pi)) :=
    resolverGradSummable_of_sourceSummable p w hsumR
  have hda := resolverR_hasDerivAt_grad hgrad x hxIcc
  refine hda.differentiableAt.congr_of_eventuallyEq ?_
  filter_upwards [hnhds] with y hy
  exact liftResolver_eq_cos p w (Set.Ioo_subset_Icc_self hy)

/-! ### Resolver R positivity from EWA -/

open ShenWork.PDE (intervalNeumannResolverR) in
open ShenWork.IntervalDomainResolverStrictPos (resolverR_pos_of_representation
  cosineCoeffs_const) in
open ShenWork.IntervalPicardLimitCoeffConv (cosineCoeffs_sub_eq) in
theorem resolverR_pos_of_EWA
    (p : CM2Params) (U : EWA T 1)
    (hER : EvenRealEWA U)
    {δ : ℝ} (hδpos : 0 < δ)
    (hfloor : UniformFloor U δ)
    (τ : TimeDom T)
    (xp : intervalDomainPoint) :
    0 < intervalNeumannResolverR p (realSlice U τ.1) xp := by
  set w := realSlice U τ.1
  set a := sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1) U)
  have hlift_w : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift w y = (WA.evalAt (y : WA.Circ) a).re := by
    intro y hy
    simp only [intervalDomainLift, dif_pos hy]
    show realSlice U τ.1 ⟨y, hy⟩ = (WA.evalAt (y : WA.Circ) a).re
    simp only [realSlice, dif_pos τ.2, evalST_apply, a]
  have hcc_lift_eq : ∀ k,
      cosineCoeffs (fun y => p.ν * intervalDomainLift w y ^ p.γ) k
        = cosineCoeffs (fun y => p.ν * (WA.evalAt (y : WA.Circ) a).re ^ p.γ) k := by
    intro k
    exact cosineCoeffs_congr_on_Icc (fun y hy => by rw [hlift_w y hy]) k
  have hâ_src := sourceFn_sq_summable p U hER hδpos hfloor τ
  have hâ : Summable (fun k =>
      (cosineCoeffs (fun y => p.ν * intervalDomainLift w y ^ p.γ) k) ^ 2) :=
    hâ_src.congr (fun k => by rw [hcc_lift_eq k])
  have hgco : ContinuousOn (fun y => p.ν * intervalDomainLift w y ^ p.γ)
      (Set.Icc (0 : ℝ) 1) :=
    (sourceFn_continuous p U hδpos hfloor τ).continuousOn.congr
      (fun y hy => by rw [hlift_w y hy])
  have hĝ : Summable (fun k =>
      (cosineCoeffs (fun y => p.ν * intervalDomainLift w y ^ p.γ
        - p.ν * δ ^ p.γ) k) ^ 2) := by
    have hsplit : ∀ k,
        cosineCoeffs (fun y => p.ν * intervalDomainLift w y ^ p.γ
          - p.ν * δ ^ p.γ) k
          = cosineCoeffs (fun y => p.ν * intervalDomainLift w y ^ p.γ) k
            - cosineCoeffs (fun _ => p.ν * δ ^ p.γ) k := by
      intro k
      exact cosineCoeffs_sub_eq hgco continuousOn_const k
    have hupd : (fun k =>
        (cosineCoeffs (fun y => p.ν * intervalDomainLift w y ^ p.γ
          - p.ν * δ ^ p.γ) k) ^ 2)
        = Function.update
            (fun k => (cosineCoeffs (fun y => p.ν * intervalDomainLift w y ^ p.γ) k) ^ 2) 0
            ((cosineCoeffs (fun y => p.ν * intervalDomainLift w y ^ p.γ
              - p.ν * δ ^ p.γ) 0) ^ 2) := by
      funext k
      by_cases hk : k = 0
      · subst hk; rw [Function.update_self]
      · rw [Function.update_of_ne hk, hsplit k, cosineCoeffs_const, if_neg hk, sub_zero]
    rw [hupd]
    exact hâ.update 0 _
  have hsrc_coeff : ∀ k,
      cosineCoeffs (fun x => p.ν * intervalDomainLift w x ^ p.γ) k
        = (intervalNeumannResolverSourceCoeff p w k).re := by
    intro k; rw [hcc_lift_eq k]; exact sourceFn_coeff p U τ k
  exact resolverR_pos_of_representation p
    (hcs_cont := evalAt_re_continuous a)
    (hagree := hlift_w)
    (hm_pos := hδpos)
    (hcs_lb := by
      intro y hy
      have hf := hfloor τ ((y : ℝ) : WA.Circ)
      show δ ≤ (WA.evalAt (y : WA.Circ) a).re
      simp only [a]
      simp only [dif_pos τ.2, evalST_apply] at hf ⊢
      exact hf)
    (hcs_ub := by
      intro y hy
      show (WA.evalAt (y : WA.Circ) a).re ≤ ‖a‖
      exact le_of_abs_le (le_trans (Complex.abs_re_le_norm _)
        (le_trans (ContinuousMap.norm_coe_le_norm (WA.evalLin a) _) (WA.evalLin_norm_le a))))
    (hsrc_coeff := hsrc_coeff)
    (hâ := hâ)
    (hĝ := hĝ)
    xp

/-! ### Assembly: chemFluxLifted differentiableAt from EWA -/

open ShenWork.Paper2 (resolverGradReal) in
open ShenWork.PDE (intervalNeumannResolverR) in
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted) in
theorem chemFluxLifted_differentiableAt_of_EWA
    (p : CM2Params) (U : EWA T 1)
    (hER : EvenRealEWA U)
    {δ : ℝ} (hδpos : 0 < δ)
    (hfloor : UniformFloor U δ)
    (hνnn : 0 ≤ p.ν)
    (τ : TimeDom T)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (chemFluxLifted p (realSlice U τ.1)) x := by
  set w := realSlice U τ.1 with hw_def
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  have hsumR : ResolverSourceSummable p w :=
    resolverSourceSummable_of_evenReal p U hER hδpos hfloor τ
  have hdu : DifferentiableAt ℝ (intervalDomainLift w) x :=
    intervalDomainLift_differentiableAt_of_EWA U τ hx
  have hdg : DifferentiableAt ℝ (fun y : ℝ => resolverGradReal p w y) x :=
    (resolverGradReal_hasDerivAt_of_sourceSummable p w hsumR x).differentiableAt
  have hdv : DifferentiableAt ℝ (intervalDomainLift (intervalNeumannResolverR p w)) x :=
    liftResolverR_differentiableAt_of_EWA p U hER hδpos hfloor τ hx
  have hvpos : 0 < intervalNeumannResolverR p w ⟨x, hxIcc⟩ :=
    resolverR_pos_of_EWA p U hER hδpos hfloor τ ⟨x, hxIcc⟩
  have hbase_pos : (0 : ℝ) < 1 + intervalDomainLift (intervalNeumannResolverR p w) x := by
    simp only [intervalDomainLift, dif_pos hxIcc]; linarith
  have hdbase : DifferentiableAt ℝ
      (fun y : ℝ => 1 + intervalDomainLift (intervalNeumannResolverR p w) y) x :=
    (differentiableAt_const _).add hdv
  have hdpow : DifferentiableAt ℝ
      (fun y : ℝ => (1 + intervalDomainLift (intervalNeumannResolverR p w) y) ^ p.β) x :=
    hdbase.rpow_const (Or.inl (ne_of_gt hbase_pos))
  have hnum : DifferentiableAt ℝ
      (fun y : ℝ => intervalDomainLift w y * resolverGradReal p w y) x := hdu.mul hdg
  have hden_ne : ((1 + intervalDomainLift (intervalNeumannResolverR p w) x) ^ p.β) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hbase_pos _)
  exact hnum.div hdpow hden_ne

#print axioms chemFluxLifted_differentiableAt_of_EWA

/-! ### Wiring: auto-discharge hsumR, hgrad, f-family, wLog into realizes_evalST_discharged -/

open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted) in
theorem realizes_evalST_auto (p : CM2Params) (u₀cos : ℕ → ℝ)
    (hsumc : Summable (fun k => |u₀cos k|)) (hmem : MemW 1 (ofCosineCoeffs u₀cos))
    (hT : (0 : ℝ) ≤ T) (hTpos : 0 < T)
    {ρ L_Q L_G : ℝ} (u_star : EWA T 1)
    (hfix : u_star = picardEWA p p.μ p.ν p.γ p.hμ hT
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1) u_star)
    (hρ : 0 ≤ ρ)
    (hself : MapsTo
      (picardEWA p p.μ p.ν p.γ p.hμ hT (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1))
      (Metric.closedBall (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ)
      (Metric.closedBall (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ))
    (hLipQ : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ‖chemFluxEWA p.μ p.ν p.β p.γ p.hμ a - chemFluxEWA p.μ p.ν p.β p.γ p.hμ b‖
        ≤ L_Q * ‖a - b‖)
    (hLipG : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ‖growthEWA p.α p.a p.b a - growthEWA p.α p.a p.b b‖ ≤ L_G * ‖a - b‖)
    (hKnn : (0 : ℝ) ≤ |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T)
    (hK : |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T < 1)
    (hmem_star : u_star ∈ Metric.closedBall (heatEWA (T := T)
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ)
    (hβpos : 0 < p.β) (hαnn : 0 ≤ p.α) (hμle1 : p.μ ≤ 1)
    (hfloor : UniformFloor u_star T)
    (hνnn : 0 ≤ p.ν)
    (t : ℝ) (htlo : 0 < t) (hthi : t ≤ T) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x := by
  have hER : EvenRealEWA u_star :=
    picardEWA_evenReal_fixedPoint p p.hμ hT u₀cos hmem hρ hself hLipQ hLipG hKnn hK
      u_star hmem_star hfix
  have h_flux_diff : ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (chemFluxLifted p (realSlice u_star τ.1)) x :=
    fun τ x hx => chemFluxLifted_differentiableAt_of_EWA p u_star hER hTpos hfloor hνnn τ hx
  set f : ℝ → ℝ → ℝ := fun s y =>
    if h : s ∈ Set.Icc (0 : ℝ) T then
      p.ν * (WA.evalAt (y : WA.Circ)
        (sliceWA ⟨s, h⟩ (GWA.incl (by omega : (0:ℕ) ≤ 1) u_star))).re ^ p.γ
    else 0
  have hsumR : ∀ σ : TimeDom T, ResolverSourceSummable p (realSlice u_star σ.1) :=
    fun σ => resolverSourceSummable_of_evenReal p u_star hER hTpos hfloor σ
  have hgrad : ∀ (τ : TimeDom T),
      Summable fun k : ℕ =>
        |(intervalNeumannResolverCoeff p (realSlice u_star τ.1) k).re|
          * ((k : ℝ) * Real.pi) :=
    fun τ => resolverGradSummable_of_evenReal p u_star hER hTpos hfloor τ
  have hf_cont : ∀ σ : TimeDom T, Continuous (f σ.1) := by
    intro σ
    simp only [f, dif_pos σ.2]
    exact sourceFn_continuous p u_star hTpos hfloor σ
  have hf_nonneg : ∀ (σ : TimeDom T) (y : ℝ), 0 ≤ f σ.1 y := by
    intro σ y
    simp only [f, dif_pos σ.2]
    exact sourceFn_nonneg p u_star hνnn hTpos hfloor σ y
  have hf_coeff : ∀ (σ : TimeDom T) (k : ℕ),
      cosineCoeffs (f σ.1) k =
        (intervalNeumannResolverSourceCoeff p (realSlice u_star σ.1) k).re := by
    intro σ k
    have : f σ.1 = (fun (y : ℝ) =>
        p.ν * (WA.evalAt (y : WA.Circ)
          (sliceWA σ (GWA.incl (by omega : (0:ℕ) ≤ 1) u_star))).re ^ p.γ) := by
      funext y; simp only [f, dif_pos σ.2]
    rw [this, sourceFn_coeff]
  have hf2 : ∀ σ : TimeDom T, Summable (fun k => (cosineCoeffs (f σ.1) k) ^ 2) := by
    intro σ
    have hcoeff : ∀ k, cosineCoeffs (f σ.1) k =
        resolverSourceReCoeff p (realSlice u_star σ.1) k := by
      intro k
      simp only [hf_coeff σ k, resolverSourceReCoeff]
    simp_rw [hcoeff]
    exact summable_sq_of_summable_abs (hsumR σ)
  have h_src_cont_log : ∀ (τ : TimeDom T), Continuous (wLog p u_star τ.1) :=
    fun τ => wLog_continuous_of_floor p u_star hTpos hfloor τ
  exact realizes_evalST_discharged p u₀cos hsumc hmem hT hTpos u_star hfix hρ hself
    hLipQ hLipG hKnn hK hmem_star hβpos hαnn hμle1 rfl hfloor hsumR hgrad f hf_cont
    hf_nonneg hf_coeff hf2 h_flux_diff h_src_cont_log t htlo hthi

/-! ### Eigenvalue summability from L1ContOn (Group D)

`fullSourceCoeff = heat_part + (-χ₀)*duhamel_chem + duhamel_log`.
Each leg is eigenvalue-summable: heat from exp decay, Duhamel legs from
`eigenvalue_mul_abs_duhamelSpectralCoeff_le_envelope` + summable envelope.
Triangle inequality assembles `hsumE`. -/

open ShenWork.IntervalSemigroupNeumann (heatCoeff_eigenvalue_summable) in
open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1ContOn) in
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff) in
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs) in
theorem hsumE_of_L1ContOn (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ)
    {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
    (hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    Summable (fun n => unitIntervalCosineEigenvalue n *
      |fullSourceCoeff p u u₀cos t n|) := by
  have hC : Summable (fun n => unitIntervalCosineEigenvalue n *
      |duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n|) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity) (abs_nonneg _))
      (fun n => eigenvalue_mul_abs_duhamelSpectralCoeff_le_envelope hchem ht htT n)
      hchem.henv_summable
  have hL : Summable (fun n => unitIntervalCosineEigenvalue n *
      |duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n|) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity) (abs_nonneg _))
      (fun n => eigenvalue_mul_abs_duhamelSpectralCoeff_le_envelope hlog ht htT n)
      hlog.henv_summable
  have hH : Summable (fun n => unitIntervalCosineEigenvalue n *
      |Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n|) :=
    heatCoeff_eigenvalue_summable ht hu0bd
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity) (abs_nonneg _))
    (fun n => ?_)
    (hH.add ((hC.mul_left |p.χ₀|).add hL))
  simp only [fullSourceCoeff]
  have hnn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  have htri : |Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n
      + (-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n
      + duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n|
    ≤ |Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n|
      + |(-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n|
      + |duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n| := by
    have h1 := abs_add_le
      (Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n)
      ((-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n)
    have h2 := abs_add_le
      (Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n
        + (-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n)
      (duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n)
    linarith
  calc unitIntervalCosineEigenvalue n *
        |Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n
         + (-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n
         + duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n|
      ≤ unitIntervalCosineEigenvalue n *
        (|Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n|
         + |(-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n|
         + |duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n|) :=
        mul_le_mul_of_nonneg_left htri hnn
    _ = unitIntervalCosineEigenvalue n *
          |Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n|
        + (unitIntervalCosineEigenvalue n *
          |(-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n|
        + unitIntervalCosineEigenvalue n *
          |duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n|) := by ring
    _ = unitIntervalCosineEigenvalue n *
          |Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n|
        + (|p.χ₀| * (unitIntervalCosineEigenvalue n *
          |duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n|)
        + unitIntervalCosineEigenvalue n *
          |duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n|) := by
        congr 1; simp only [abs_mul, abs_neg]; ring

#print axioms hsumE_of_L1ContOn
#print axioms evalAt_re_continuous
#print axioms sourceFn_continuous
#print axioms sourceFn_nonneg
#print axioms sourceFn_coeff
#print axioms sourceFn_sq_summable
#print axioms wLog_continuous_of_floor
#print axioms realizes_evalST_auto
#print axioms hsumE_of_L1ContOn

/-! ### L1ContOn auto-discharge (Group B)

Wire the DuhamelSourceL1ContOn hypotheses for logistic and chemDiv sources
from EWA data alone. Uses eval bridges + slab realization. -/

open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1ContOn) in
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledLogisticSourceCoeffs coupledLogisticSourceLift) in
noncomputable def logisticSourceL1ContOn_auto (p : CM2Params)
    (u_star : EWA T 1) {δ : ℝ} (hδpos : 0 < δ)
    (hER : EvenRealEWA u_star) (hfloor : UniformFloor u_star δ)
    (hα : 0 ≤ p.α) (hT : 0 ≤ T) :
    DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p (realSlice u_star)) T :=
  logisticSourceL1ContOn_of_EWA p (realSlice u_star) u_star hT hER
    (fun τ x hx =>
      evalST_growthEWA_eq_logisticLifted p u_star (realSlice u_star τ.1) τ x
        (Set.Ioo_subset_Icc_self hx)
        (realSlice_h_u_slab hER τ x (Set.Ioo_subset_Icc_self hx))
        (realSlice_h_uα_slab p hδpos hER hfloor hα τ x (Set.Ioo_subset_Icc_self hx)))

#print axioms logisticSourceL1ContOn_auto

open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1ContOn) in
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledChemDivSourceLift) in
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted) in
noncomputable def chemDivSourceL1ContOn_auto (p : CM2Params)
    (u_star : EWA T 1) {δ : ℝ} (hδpos : 0 < δ)
    (hER : EvenRealEWA u_star) (hTpos : 0 < T)
    (hfloor : UniformFloor u_star δ)
    (hβpos : 0 < p.β) (hνnn : 0 ≤ p.ν) (hμle1 : p.μ ≤ 1) :
    DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p (realSlice u_star)) T := by
  have hT : (0 : ℝ) ≤ T := le_of_lt hTpos
  have hsum : ∀ σ : TimeDom T, ResolverSourceSummable p (realSlice u_star σ.1) :=
    fun σ => resolverSourceSummable_of_evenReal p u_star hER hδpos hfloor σ
  have hgrad : ∀ (τ : TimeDom T),
      Summable fun k : ℕ =>
        |(intervalNeumannResolverCoeff p (realSlice u_star τ.1) k).re| *
          ((k : ℝ) * Real.pi) :=
    fun τ => resolverGradSummable_of_evenReal p u_star hER hδpos hfloor τ
  set f : ℝ → ℝ → ℝ := fun s y =>
    if h : s ∈ Set.Icc (0 : ℝ) T then
      p.ν * (WA.evalAt (y : WA.Circ)
        (sliceWA ⟨s, h⟩ (GWA.incl (by omega : (0:ℕ) ≤ 1) u_star))).re ^ p.γ
    else 0
  have hf_cont : ∀ σ : TimeDom T, Continuous (f σ.1) := by
    intro σ; simp only [f, dif_pos σ.2]
    exact sourceFn_continuous p u_star hδpos hfloor σ
  have hf_nonneg : ∀ (σ : TimeDom T) (y : ℝ), 0 ≤ f σ.1 y := by
    intro σ y; simp only [f, dif_pos σ.2]
    exact sourceFn_nonneg p u_star hνnn hδpos hfloor σ y
  have hf_coeff : ∀ (σ : TimeDom T) (k : ℕ),
      cosineCoeffs (f σ.1) k =
        (intervalNeumannResolverSourceCoeff p (realSlice u_star σ.1) k).re := by
    intro σ k
    have : f σ.1 = (fun (y : ℝ) =>
        p.ν * (WA.evalAt (y : WA.Circ)
          (sliceWA σ (GWA.incl (by omega : (0:ℕ) ≤ 1) u_star))).re ^ p.γ) := by
      funext y; simp only [f, dif_pos σ.2]
    rw [this, sourceFn_coeff]
  have hf2 : ∀ σ : TimeDom T, Summable (fun k => (cosineCoeffs (f σ.1) k) ^ 2) := by
    intro σ
    have hcoeff : ∀ k, cosineCoeffs (f σ.1) k =
        resolverSourceReCoeff p (realSlice u_star σ.1) k := by
      intro k; simp only [hf_coeff σ k, resolverSourceReCoeff]
    simp_rw [hcoeff]
    exact summable_sq_of_summable_abs (hsum σ)
  have h_flux_nbhd := realSlice_h_flux_slab p hδpos hβpos hER hfloor
      hsum hgrad hμle1 f hf_cont hf_nonneg hf_coeff hf2
  have h_flux_diff : ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (chemFluxLifted p (realSlice u_star τ.1)) x :=
    fun τ x hx => chemFluxLifted_differentiableAt_of_EWA p u_star hER hδpos hfloor hνnn τ hx
  exact chemDivSourceL1ContOn_of_EWA (μ := p.μ) (ν := p.ν) (γ := p.γ) p.hμ p
    (realSlice u_star) u_star hT hER
    (fun τ x hx =>
      evalST_chemDivEWA_eq_coupledChemDivSourceLift (μ := p.μ) (ν := p.ν) (γ := p.γ) p.hμ p
        (realSlice u_star) u_star τ x hx (Set.Ioo_subset_Icc_self hx)
        (hgrad τ) (h_flux_nbhd τ) (h_flux_diff τ x hx))

#print axioms chemDivSourceL1ContOn_auto

/-! ### Group F: `hlogInv` bypassing `hlogNE0/1`

The existing route `realSlice_hlogInv_of_bankedU` (in `SourceSliceC2Neumann.lean`)
requires `hlogNE0/1` (endpoint nonvanishing of logistic source) for the
C²-Neumann → IBP → Fourier summability chain.

This bypass uses the L1ContOn envelope summability (from `logisticSourceL1ContOn_auto`)
to get cosine coefficient ℓ¹ summability directly, then bridges to the Fourier
summability via `fourierCoeff_reflCircle_summable_of_cosineCoeff_abs`, feeding
into `logistic_source_inversion`. No endpoint data is needed. -/

open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledLogisticSourceCoeffs coupledLogisticSourceLift) in
open ShenWork.IntervalDomainExistence
  (intervalDomainPoint intervalDomainLift intervalLogisticSource
   intervalDomainConstExtend constExtend_eq_lift_on_Icc constExtend_continuous) in
open ShenWork.IntervalCosineInversion (reflCircle cosineCoeffs) in
theorem realSlice_hlogInv_of_L1ContOn (p : CM2Params)
    (u_star : EWA T 1)
    {δ : ℝ} (hδpos : 0 < δ)
    (hER : EvenRealEWA u_star)
    (hfloor : UniformFloor u_star δ)
    (hα : 0 ≤ p.α) (hT : 0 ≤ T)
    (u₀cos : ℕ → ℝ)
    (hsumE : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|))
    (hrealizes : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      (∑' n, coupledLogisticSourceCoeffs p (realSlice u_star) t n *
        cosineMode n x.1)
        = realSlice u_star t x
            * (p.a - p.b * (realSlice u_star t x) ^ p.α) := by
  intro t ht x hx
  set s : intervalDomainPoint → ℝ := intervalLogisticSource p (realSlice u_star t)
  set g : ℝ → ℝ := intervalDomainConstExtend s
  have hcont_s : Continuous s :=
    realSlice_wLog_continuous p u_star u₀cos hα hsumE hrealizes ht
  have hcont_g : Continuous g := constExtend_continuous hcont_s
  have hgeq : Set.EqOn g (coupledLogisticSourceLift p (realSlice u_star) t)
      (Set.Icc (0 : ℝ) 1) := by
    intro y hy
    show intervalDomainConstExtend s y = coupledLogisticSourceLift p (realSlice u_star) t y
    exact constExtend_eq_lift_on_Icc hy
  have hL1 := logisticSourceL1ContOn_auto p u_star hδpos hER hfloor hα hT
  have hcos_abs : Summable (fun k : ℕ => |cosineCoeffs g k|) := by
    have heq : ∀ k, cosineCoeffs g k =
        coupledLogisticSourceCoeffs p (realSlice u_star) t k := by
      intro k
      rw [cosineCoeffs_congr_on_Icc hgeq k]
      rfl
    simp_rw [heq]
    exact Summable.of_nonneg_of_le (fun k => abs_nonneg _)
      (fun k => hL1.henv_bound t (le_of_lt ht.1) (le_of_lt ht.2) k)
      hL1.henv_summable
  have hfourier : Summable (fun n : ℤ =>
      fourierCoeff (reflCircle g) n) :=
    ShenWork.Paper2.PdeUWiring.fourierCoeff_reflCircle_summable_of_cosineCoeff_abs
      hcont_g hcos_abs
  exact logistic_source_inversion p (realSlice u_star) t g hcont_g hgeq hfourier hx

#print axioms realSlice_hlogInv_of_L1ContOn

end ShenWork.EWA
