import ShenWork.Paper2.IntervalChiNegH1PhysicalInitialRHS
import ShenWork.Paper2.IntervalChiNegH1PhysicalClassicalContinuity
import ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer
import ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents
import ShenWork.PDE.GagliardoNirenberg

/-!
# Spatial Young reducers for the physical H¹ RHS

This file uses source-side spatial Cauchy/Young estimates to discharge the
three product-estimate fields in the component-square zero-window interface.
It does not consume downstream RHS integrability, derivative integrability,
the strict/initial route, or bounded-before data.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability
open ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars
open ShenWork.Paper2.IntervalChiNegH1PhysicalInitialRHS
open ShenWork.Paper2.IntervalChiNegH1PhysicalClassicalContinuity
open ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer
open ShenWork.Paper2.IntervalChiNegH1LapComponentContinuity
open ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents
open ShenWork.IntervalDomainExistence.P3MoserGradientIntegrability
open ShenWork.GagliardoNirenberg

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1PhysicalYoungSpatial

/-- Fixed-time spatial Young estimate for the physical taxis scalar. -/
theorem H1PhysicalTaxisX_norm_le_half_lapL2sq_add_half_taxisPartSq_of_spatial
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {τ : ℝ}
    (huxx_sq : IntervalIntegrable
      (fun x => (liftDeriv2 u τ x) ^ 2) volume (0 : ℝ) 1)
    (hpart_sq : IntervalIntegrable
      (fun x => (H1PhysicalChemTaxisPart p u v τ x) ^ 2) volume (0 : ℝ) 1)
    (hprod : IntervalIntegrable
      (fun x => |liftDeriv2 u τ x * H1PhysicalChemTaxisPart p u v τ x|)
      volume (0 : ℝ) 1) :
    ‖H1PhysicalTaxisX p u v τ‖ ≤
      ((1 : ℝ) / 2) * lapL2sq u τ +
        ((1 : ℝ) / 2) * H1PhysicalTaxisPartSq p u v τ := by
  have hYoung :=
    ShenWork.GagliardoNirenberg.norm_integral_mul_le_half_sq_sum
      (L := (1 : ℝ))
      (f := fun x => liftDeriv2 u τ x)
      (g := fun x => H1PhysicalChemTaxisPart p u v τ x)
      (by norm_num : 0 < (1 : ℝ)) huxx_sq hpart_sq hprod
  simpa [H1PhysicalTaxisX, H1PhysicalTaxisPartSq, lapL2sq] using hYoung

/-- Fixed-time spatial Young estimate for the physical uvxx scalar. -/
theorem H1PhysicalUvxxX_norm_le_half_lapL2sq_add_half_uvxxPartSq_of_spatial
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {τ : ℝ}
    (huxx_sq : IntervalIntegrable
      (fun x => (liftDeriv2 u τ x) ^ 2) volume (0 : ℝ) 1)
    (hpart_sq : IntervalIntegrable
      (fun x => (H1PhysicalChemUvxxPart p u v τ x) ^ 2) volume (0 : ℝ) 1)
    (hprod : IntervalIntegrable
      (fun x => |liftDeriv2 u τ x * H1PhysicalChemUvxxPart p u v τ x|)
      volume (0 : ℝ) 1) :
    ‖H1PhysicalUvxxX p u v τ‖ ≤
      ((1 : ℝ) / 2) * lapL2sq u τ +
        ((1 : ℝ) / 2) * H1PhysicalUvxxPartSq p u v τ := by
  have hYoung :=
    ShenWork.GagliardoNirenberg.norm_integral_mul_le_half_sq_sum
      (L := (1 : ℝ))
      (f := fun x => liftDeriv2 u τ x)
      (g := fun x => H1PhysicalChemUvxxPart p u v τ x)
      (by norm_num : 0 < (1 : ℝ)) huxx_sq hpart_sq hprod
  simpa [H1PhysicalUvxxX, H1PhysicalUvxxPartSq, lapL2sq] using hYoung

/-- Fixed-time spatial Young estimate for the physical reaction scalar. -/
theorem H1PhysicalReactX_norm_le_half_lapL2sq_add_half_reactPartSq_of_spatial
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ : ℝ}
    (huxx_sq : IntervalIntegrable
      (fun x => (liftDeriv2 u τ x) ^ 2) volume (0 : ℝ) 1)
    (hpart_sq : IntervalIntegrable
      (fun x => (H1PhysicalLogisticReactionPart p u τ x) ^ 2)
        volume (0 : ℝ) 1)
    (hprod : IntervalIntegrable
      (fun x => |liftDeriv2 u τ x * H1PhysicalLogisticReactionPart p u τ x|)
      volume (0 : ℝ) 1) :
    ‖H1PhysicalReactX p u τ‖ ≤
      ((1 : ℝ) / 2) * lapL2sq u τ +
        ((1 : ℝ) / 2) * H1PhysicalReactPartSq p u τ := by
  have hYoung :=
    ShenWork.GagliardoNirenberg.norm_integral_mul_le_half_sq_sum
      (L := (1 : ℝ))
      (f := fun x => liftDeriv2 u τ x)
      (g := fun x => H1PhysicalLogisticReactionPart p u τ x)
      (by norm_num : 0 < (1 : ℝ)) huxx_sq hpart_sq hprod
  simpa [H1PhysicalReactX, H1PhysicalReactPartSq, lapL2sq] using hYoung

/-- Source-side spatial-integrability data sufficient for the component-square
zero-window interface.  The time-window integrability and RHS measurability
fields are the same as in `H1PhysicalRHSComponentSquareZeroDataBefore`; the new
fields are the per-time spatial integrability assumptions needed to apply the
generic interval-integral Young estimate. -/
def H1PhysicalRHSComponentSquareSpatialYoungDataBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T : ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ ∧ δ < T ∧
    AEStronglyMeasurable
      (H1IdentityRHSValue p u
        (H1PhysicalTaxisX p u v)
        (H1PhysicalUvxxX p u v)
        (H1PhysicalReactX p u))
      (volume.restrict (Set.Ioc (0 : ℝ) δ)) ∧
    IntervalIntegrable (lapL2sq u) volume (0 : ℝ) δ ∧
    IntervalIntegrable (H1PhysicalTaxisPartSq p u v) volume (0 : ℝ) δ ∧
    IntervalIntegrable (H1PhysicalUvxxPartSq p u v) volume (0 : ℝ) δ ∧
    IntervalIntegrable (H1PhysicalReactPartSq p u) volume (0 : ℝ) δ ∧
    (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
      IntervalIntegrable (fun x => (liftDeriv2 u r x) ^ 2)
        volume (0 : ℝ) 1) ∧
    (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
      IntervalIntegrable
        (fun x => (H1PhysicalChemTaxisPart p u v r x) ^ 2)
        volume (0 : ℝ) 1) ∧
    (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
      IntervalIntegrable
        (fun x => (H1PhysicalChemUvxxPart p u v r x) ^ 2)
        volume (0 : ℝ) 1) ∧
    (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
      IntervalIntegrable
        (fun x => (H1PhysicalLogisticReactionPart p u r x) ^ 2)
        volume (0 : ℝ) 1) ∧
    (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
      IntervalIntegrable
        (fun x => |liftDeriv2 u r x *
          H1PhysicalChemTaxisPart p u v r x|)
        volume (0 : ℝ) 1) ∧
    (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
      IntervalIntegrable
        (fun x => |liftDeriv2 u r x *
          H1PhysicalChemUvxxPart p u v r x|)
        volume (0 : ℝ) 1) ∧
    (∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
      IntervalIntegrable
        (fun x => |liftDeriv2 u r x *
          H1PhysicalLogisticReactionPart p u r x|)
        volume (0 : ℝ) 1)

private theorem squareProfile_intervalIntegrable_of_continuousOn_zeroSlab
    {part : ℝ → ℝ → ℝ} {δ : ℝ}
    (hδ_nonneg : 0 ≤ δ)
    (hCont :
      ContinuousOn (Function.uncurry part)
        (Set.Icc (0 : ℝ) δ ×ˢ Set.Icc (0 : ℝ) 1)) :
    IntervalIntegrable
      (fun t => ∫ x in (0 : ℝ)..1, (part t x) ^ 2) volume
      (0 : ℝ) δ := by
  have hSq :
      ContinuousOn (Function.uncurry (fun t x => (part t x) ^ 2))
        (Set.Icc (0 : ℝ) δ ×ˢ Set.Icc (0 : ℝ) 1) := by
    simpa [Function.uncurry] using hCont.pow 2
  have hProfile :
      ContinuousOn (fun t => ∫ x in (0 : ℝ)..1, (part t x) ^ 2)
        (Set.Icc (0 : ℝ) δ) :=
    continuousOn_intervalIntegral_zero_one_of_continuousOn_Icc_prod hSq
  exact hProfile.intervalIntegrable_of_Icc hδ_nonneg

private theorem H1PhysicalChemTaxisPart_continuousOn_zeroSlab_of_primitives
    {p : CM2Params} {T δ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (H : H1ZeroStartPhysicalPrimitiveDataBefore p u v T)
    (hδ_nonneg : 0 ≤ δ) (hδ_before : δ < T) :
    ContinuousOn (Function.uncurry (H1PhysicalChemTaxisPart p u v))
      (Set.Icc (0 : ℝ) δ ×ˢ Set.Icc (0 : ℝ) 1) := by
  let S : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) δ ×ˢ Set.Icc (0 : ℝ) 1
  have hvS :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x)) S := by
    simpa [S] using H.v_cont0 (b := δ) hδ_nonneg hδ_before
  have huxS :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (u t)) x)) S := by
    simpa [S] using H.ux_cont0 (b := δ) hδ_nonneg hδ_before
  have hvxS :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (v t)) x)) S := by
    simpa [S] using H.vx_cont0 (b := δ) hδ_nonneg hδ_before
  have hvnnS :
      ∀ z ∈ S,
        0 ≤
          Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z := by
    intro z hz
    exact H.v_nonneg0 (b := δ) hδ_nonneg hδ_before z (by simpa [S] using hz)
  have hbase :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          1 +
            Function.uncurry
              (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) S :=
    continuousOn_const.add hvS
  have hbase_pos :
      ∀ z ∈ S,
        0 <
          1 +
            Function.uncurry
              (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z := by
    intro z hz
    have hvz := hvnnS z hz
    linarith
  have hden :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (1 +
            Function.uncurry
              (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^ p.β) S :=
    hbase.rpow_const
      (fun z hz => Or.inl (ne_of_gt (hbase_pos z hz)))
  have hden_ne :
      ∀ z ∈ S,
        (1 +
          Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^
          p.β ≠ 0 := by
    intro z hz
    exact ne_of_gt (Real.rpow_pos_of_pos (hbase_pos z hz) _)
  simpa [S, H1PhysicalChemTaxisPart, Function.uncurry] using
    (huxS.mul hvxS).div hden hden_ne

private theorem H1PhysicalChemUvxxPart_continuousOn_zeroSlab_of_primitives
    {p : CM2Params} {T δ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (H : H1ZeroStartPhysicalPrimitiveDataBefore p u v T)
    (hδ_nonneg : 0 ≤ δ) (hδ_before : δ < T) :
    ContinuousOn (Function.uncurry (H1PhysicalChemUvxxPart p u v))
      (Set.Icc (0 : ℝ) δ ×ˢ Set.Icc (0 : ℝ) 1) := by
  let S : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) δ ×ˢ Set.Icc (0 : ℝ) 1
  have huS :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x)) S := by
    simpa [S] using H.u_cont0 (b := δ) hδ_nonneg hδ_before
  have hvS :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x)) S := by
    simpa [S] using H.v_cont0 (b := δ) hδ_nonneg hδ_before
  have hvxS :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (v t)) x)) S := by
    simpa [S] using H.vx_cont0 (b := δ) hδ_nonneg hδ_before
  have huposS :
      ∀ z ∈ S,
        0 <
          Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z := by
    intro z hz
    exact H.u_pos0 (b := δ) hδ_nonneg hδ_before z (by simpa [S] using hz)
  have hvnnS :
      ∀ z ∈ S,
        0 ≤
          Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z := by
    intro z hz
    exact H.v_nonneg0 (b := δ) hδ_nonneg hδ_before z (by simpa [S] using hz)
  have hu_gamma :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z) ^ p.γ) S :=
    huS.rpow_const (fun z hz => Or.inl (ne_of_gt (huposS z hz)))
  have hvxxRep :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          p.μ *
              Function.uncurry
                (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z -
            p.ν *
              (Function.uncurry
                (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z) ^
                p.γ) S :=
    (hvS.const_mul p.μ).sub (hu_gamma.const_mul p.ν)
  have hbase :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          1 +
            Function.uncurry
              (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) S :=
    continuousOn_const.add hvS
  have hbase_pos :
      ∀ z ∈ S,
        0 <
          1 +
            Function.uncurry
              (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z := by
    intro z hz
    have hvz := hvnnS z hz
    linarith
  have hdenβ :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (1 +
            Function.uncurry
              (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^ p.β) S :=
    hbase.rpow_const
      (fun z hz => Or.inl (ne_of_gt (hbase_pos z hz)))
  have hdenβ1 :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (1 +
            Function.uncurry
              (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^
            (p.β + 1)) S :=
    hbase.rpow_const
      (fun z hz => Or.inl (ne_of_gt (hbase_pos z hz)))
  have hdenβ_ne :
      ∀ z ∈ S,
        (1 +
          Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^
          p.β ≠ 0 := by
    intro z hz
    exact ne_of_gt (Real.rpow_pos_of_pos (hbase_pos z hz) _)
  have hdenβ1_ne :
      ∀ z ∈ S,
        (1 +
          Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^
          (p.β + 1) ≠ 0 := by
    intro z hz
    exact ne_of_gt (Real.rpow_pos_of_pos (hbase_pos z hz) _)
  have hterm1 := (huS.mul hvxxRep).div hdenβ hdenβ_ne
  have hterm2 := ((huS.const_mul p.β).mul (hvxS.pow 2)).div hdenβ1 hdenβ1_ne
  simpa [S, H1PhysicalChemUvxxPart, Function.uncurry] using hterm1.sub hterm2

private theorem H1PhysicalLogisticReactionPart_continuousOn_zeroSlab_of_primitives
    {p : CM2Params} {T δ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (H : H1ZeroStartPhysicalPrimitiveDataBefore p u v T)
    (hδ_nonneg : 0 ≤ δ) (hδ_before : δ < T) :
    ContinuousOn (Function.uncurry (H1PhysicalLogisticReactionPart p u))
      (Set.Icc (0 : ℝ) δ ×ˢ Set.Icc (0 : ℝ) 1) := by
  let S : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) δ ×ˢ Set.Icc (0 : ℝ) 1
  have huS :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x)) S := by
    simpa [S] using H.u_cont0 (b := δ) hδ_nonneg hδ_before
  have huposS :
      ∀ z ∈ S,
        0 <
          Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z := by
    intro z hz
    exact H.u_pos0 (b := δ) hδ_nonneg hδ_before z (by simpa [S] using hz)
  have hu_alpha :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z) ^ p.α) S :=
    huS.rpow_const (fun z hz => Or.inl (ne_of_gt (huposS z hz)))
  simpa [S, H1PhysicalLogisticReactionPart, Function.uncurry] using
    huS.mul (continuousOn_const.sub (hu_alpha.const_mul p.b))

/-- Zero-start primitive continuity gives time integrability of the four
square profiles carried by the spatial Young route.  This is still a
zero-start analytic input; it is not a consequence of strict-positive-time
classical continuity alone. -/
theorem H1PhysicalSquareProfilesTimeIntegrableBefore_of_zeroStartPrimitiveData
    {p : CM2Params} {T δ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (H : H1ZeroStartPhysicalPrimitiveDataBefore p u v T)
    (hδ_pos : 0 < δ) (hδ_before : δ < T) :
    IntervalIntegrable (lapL2sq u) volume (0 : ℝ) δ ∧
    IntervalIntegrable (H1PhysicalTaxisPartSq p u v) volume (0 : ℝ) δ ∧
    IntervalIntegrable (H1PhysicalUvxxPartSq p u v) volume (0 : ℝ) δ ∧
    IntervalIntegrable (H1PhysicalReactPartSq p u) volume (0 : ℝ) δ := by
  have hδ_nonneg : 0 ≤ δ := hδ_pos.le
  have hLap_cont :
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc (0 : ℝ) δ) :=
    lapL2sq_continuousOn_before_of_zeroSlabRepresentativeBefore
      (H1LiftDeriv2ZeroSlabRepBefore_of_zeroStartPrimitiveData
        (p := p) (u := u) (v := v) (T := T) H)
      (a := (0 : ℝ)) (b := δ) le_rfl hδ_nonneg hδ_before
  have hLap_time :
      IntervalIntegrable (lapL2sq u) volume (0 : ℝ) δ :=
    hLap_cont.intervalIntegrable_of_Icc hδ_nonneg
  have hTaxisSq_time :
      IntervalIntegrable (H1PhysicalTaxisPartSq p u v) volume (0 : ℝ) δ := by
    simpa [H1PhysicalTaxisPartSq] using
      squareProfile_intervalIntegrable_of_continuousOn_zeroSlab
        (part := H1PhysicalChemTaxisPart p u v)
        hδ_nonneg
        (H1PhysicalChemTaxisPart_continuousOn_zeroSlab_of_primitives
          (p := p) (T := T) (δ := δ) (u := u) (v := v)
          H hδ_nonneg hδ_before)
  have hUvxxSq_time :
      IntervalIntegrable (H1PhysicalUvxxPartSq p u v) volume (0 : ℝ) δ := by
    simpa [H1PhysicalUvxxPartSq] using
      squareProfile_intervalIntegrable_of_continuousOn_zeroSlab
        (part := H1PhysicalChemUvxxPart p u v)
        hδ_nonneg
        (H1PhysicalChemUvxxPart_continuousOn_zeroSlab_of_primitives
          (p := p) (T := T) (δ := δ) (u := u) (v := v)
          H hδ_nonneg hδ_before)
  have hReactSq_time :
      IntervalIntegrable (H1PhysicalReactPartSq p u) volume (0 : ℝ) δ := by
    simpa [H1PhysicalReactPartSq] using
      squareProfile_intervalIntegrable_of_continuousOn_zeroSlab
        (part := H1PhysicalLogisticReactionPart p u)
        hδ_nonneg
        (H1PhysicalLogisticReactionPart_continuousOn_zeroSlab_of_primitives
          (p := p) (T := T) (δ := δ) (u := u) (v := v)
          H hδ_nonneg hδ_before)
  exact ⟨hLap_time, hTaxisSq_time, hUvxxSq_time, hReactSq_time⟩

/-- Square-integrability plus product measurability supplies the product
integrability fields in `H1PhysicalRHSComponentSquareSpatialYoungDataBefore`.
The product measurability hypotheses are explicit: square integrability of the
two factors alone is not a measurability theorem. -/
theorem H1PhysicalRHSComponentSquareSpatialYoungDataBefore_of_squareData_and_productMeas
    {p : CM2Params} {T δ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hδ_pos : 0 < δ) (hδ_before : δ < T)
    (hRHS_meas :
      AEStronglyMeasurable
        (H1IdentityRHSValue p u
          (H1PhysicalTaxisX p u v)
          (H1PhysicalUvxxX p u v)
          (H1PhysicalReactX p u))
        (volume.restrict (Set.Ioc (0 : ℝ) δ)))
    (hLap_time :
      IntervalIntegrable (lapL2sq u) volume (0 : ℝ) δ)
    (hTaxisSq_time :
      IntervalIntegrable (H1PhysicalTaxisPartSq p u v) volume (0 : ℝ) δ)
    (hUvxxSq_time :
      IntervalIntegrable (H1PhysicalUvxxPartSq p u v) volume (0 : ℝ) δ)
    (hReactSq_time :
      IntervalIntegrable (H1PhysicalReactPartSq p u) volume (0 : ℝ) δ)
    (hLap_space :
      ∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
        IntervalIntegrable (fun x => (liftDeriv2 u r x) ^ 2)
          volume (0 : ℝ) 1)
    (hTaxisSq_space :
      ∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
        IntervalIntegrable
          (fun x => (H1PhysicalChemTaxisPart p u v r x) ^ 2)
          volume (0 : ℝ) 1)
    (hUvxxSq_space :
      ∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
        IntervalIntegrable
          (fun x => (H1PhysicalChemUvxxPart p u v r x) ^ 2)
          volume (0 : ℝ) 1)
    (hReactSq_space :
      ∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
        IntervalIntegrable
          (fun x => (H1PhysicalLogisticReactionPart p u r x) ^ 2)
          volume (0 : ℝ) 1)
    (hTaxisProd_meas :
      ∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
        AEStronglyMeasurable
          (fun x => |liftDeriv2 u r x *
            H1PhysicalChemTaxisPart p u v r x|)
          (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hUvxxProd_meas :
      ∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
        AEStronglyMeasurable
          (fun x => |liftDeriv2 u r x *
            H1PhysicalChemUvxxPart p u v r x|)
          (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hReactProd_meas :
      ∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) δ),
        AEStronglyMeasurable
          (fun x => |liftDeriv2 u r x *
            H1PhysicalLogisticReactionPart p u r x|)
          (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    H1PhysicalRHSComponentSquareSpatialYoungDataBefore p u v T := by
  refine
    ⟨δ, hδ_pos, hδ_before, hRHS_meas,
      hLap_time, hTaxisSq_time, hUvxxSq_time, hReactSq_time,
      hLap_space, hTaxisSq_space, hUvxxSq_space, hReactSq_space,
      ?_, ?_, ?_⟩
  · filter_upwards [hLap_space, hTaxisSq_space, hTaxisProd_meas]
      with r hLap hTaxisSq hProdMeas
    exact
      intervalIntegrable_abs_mul_of_sq_integrable_of_aestronglyMeasurable
        (a := (0 : ℝ)) (b := 1)
        (f := fun x => liftDeriv2 u r x)
        (g := fun x => H1PhysicalChemTaxisPart p u v r x)
        (by norm_num : (0 : ℝ) ≤ 1)
        hLap hTaxisSq hProdMeas
  · filter_upwards [hLap_space, hUvxxSq_space, hUvxxProd_meas]
      with r hLap hUvxxSq hProdMeas
    exact
      intervalIntegrable_abs_mul_of_sq_integrable_of_aestronglyMeasurable
        (a := (0 : ℝ)) (b := 1)
        (f := fun x => liftDeriv2 u r x)
        (g := fun x => H1PhysicalChemUvxxPart p u v r x)
        (by norm_num : (0 : ℝ) ≤ 1)
        hLap hUvxxSq hProdMeas
  · filter_upwards [hLap_space, hReactSq_space, hReactProd_meas]
      with r hLap hReactSq hProdMeas
    exact
      intervalIntegrable_abs_mul_of_sq_integrable_of_aestronglyMeasurable
        (a := (0 : ℝ)) (b := 1)
        (f := fun x => liftDeriv2 u r x)
        (g := fun x => H1PhysicalLogisticReactionPart p u r x)
        (by norm_num : (0 : ℝ) ≤ 1)
        hLap hReactSq hProdMeas

/-- Classical strict-slab regularity supplies the measurability and a.e.
spatial square-integrability inputs for the spatial Young data.  The four
time-integrability fields remain explicit source assumptions. -/
theorem
    H1PhysicalRHSComponentSquareSpatialYoungDataBefore_of_classical_squareTimeIntegrable
    {p : CM2Params} {T δ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hδ_pos : 0 < δ) (hδ_before : δ < T)
    (hLap_time :
      IntervalIntegrable (lapL2sq u) volume (0 : ℝ) δ)
    (hTaxisSq_time :
      IntervalIntegrable (H1PhysicalTaxisPartSq p u v) volume (0 : ℝ) δ)
    (hUvxxSq_time :
      IntervalIntegrable (H1PhysicalUvxxPartSq p u v) volume (0 : ℝ) δ)
    (hReactSq_time :
      IntervalIntegrable (H1PhysicalReactPartSq p u) volume (0 : ℝ) δ) :
    H1PhysicalRHSComponentSquareSpatialYoungDataBefore p u v T := by
  have hRHS_meas :
      AEStronglyMeasurable
        (H1IdentityRHSValue p u
          (H1PhysicalTaxisX p u v)
          (H1PhysicalUvxxX p u v)
          (H1PhysicalReactX p u))
        (volume.restrict (Set.Ioc (0 : ℝ) δ)) :=
    H1PhysicalRHSValue_aestronglyMeasurableBefore_of_classicalSolution
      (p := p) (T := T) (δ := δ) (u := u) (v := v)
      hsol hδ_pos hδ_before
  rcases
    H1PhysicalRHSSpatialSquareIntegrableBefore_of_classicalSolution
      (p := p) (T := T) (δ := δ) (u := u) (v := v)
      hsol hδ_pos hδ_before
    with ⟨hLap_space, hTaxisSq_space, hUvxxSq_space, hReactSq_space⟩
  rcases
    H1PhysicalRHSAbsProductsMeasBefore_of_classicalSolution
      (p := p) (T := T) (δ := δ) (u := u) (v := v)
      hsol hδ_pos hδ_before
    with ⟨hTaxisProd_meas, hUvxxProd_meas, hReactProd_meas⟩
  exact
    H1PhysicalRHSComponentSquareSpatialYoungDataBefore_of_squareData_and_productMeas
      (p := p) (T := T) (δ := δ) (u := u) (v := v)
      hδ_pos hδ_before hRHS_meas
      hLap_time hTaxisSq_time hUvxxSq_time hReactSq_time
      hLap_space hTaxisSq_space hUvxxSq_space hReactSq_space
      hTaxisProd_meas hUvxxProd_meas hReactProd_meas

/-- Classical strict-slab regularity plus zero-start primitive continuity
supplies the spatial Young data.  The zero-start primitive package is an
explicit analytic input; this is not an unconditional classical-solution
producer. -/
theorem
    H1PhysicalRHSComponentSquareSpatialYoungDataBefore_of_classical_zeroStartPrimitiveData
    {p : CM2Params} {T δ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (H : H1ZeroStartPhysicalPrimitiveDataBefore p u v T)
    (hδ_pos : 0 < δ) (hδ_before : δ < T) :
    H1PhysicalRHSComponentSquareSpatialYoungDataBefore p u v T := by
  rcases
    H1PhysicalSquareProfilesTimeIntegrableBefore_of_zeroStartPrimitiveData
      (p := p) (T := T) (δ := δ) (u := u) (v := v)
      H hδ_pos hδ_before
    with ⟨hLap_time, hTaxisSq_time, hUvxxSq_time, hReactSq_time⟩
  exact
    H1PhysicalRHSComponentSquareSpatialYoungDataBefore_of_classical_squareTimeIntegrable
      (p := p) (T := T) (δ := δ) (u := u) (v := v)
      hsol hδ_pos hδ_before
      hLap_time hTaxisSq_time hUvxxSq_time hReactSq_time

/-- Spatial Young data lower to the component-square zero-window interface. -/
theorem H1PhysicalRHSComponentSquareZeroDataBefore_of_spatialYoungData
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSComponentSquareSpatialYoungDataBefore p u v T) :
    H1PhysicalRHSComponentSquareZeroDataBefore p u v T := by
  rcases h with
    ⟨δ, hδ_pos, hδ_before, hRHS_meas,
      hLap_time, hTaxisSq_time, hUvxxSq_time, hReactSq_time,
      hLap_space, hTaxisSq_space, hUvxxSq_space, hReactSq_space,
      hTaxisProd_space, hUvxxProd_space, hReactProd_space⟩
  refine
    ⟨δ, hδ_pos, hδ_before, hRHS_meas,
      hLap_time, hTaxisSq_time, hUvxxSq_time, hReactSq_time,
      ?_, ?_, ?_⟩
  · filter_upwards [hLap_space, hTaxisSq_space, hTaxisProd_space]
      with r hLap hTaxisSq hTaxisProd
    exact H1PhysicalTaxisX_norm_le_half_lapL2sq_add_half_taxisPartSq_of_spatial
      hLap hTaxisSq hTaxisProd
  · filter_upwards [hLap_space, hUvxxSq_space, hUvxxProd_space]
      with r hLap hUvxxSq hUvxxProd
    exact H1PhysicalUvxxX_norm_le_half_lapL2sq_add_half_uvxxPartSq_of_spatial
      hLap hUvxxSq hUvxxProd
  · filter_upwards [hLap_space, hReactSq_space, hReactProd_space]
      with r hLap hReactSq hReactProd
    exact H1PhysicalReactX_norm_le_half_lapL2sq_add_half_reactPartSq_of_spatial
      hLap hReactSq hReactProd

/-- Spatial Young data lower all the way to Task93's Young-style scalar
majorant interface. -/
theorem H1PhysicalRHSYoungScalarZeroMajorantsBefore_of_spatialYoungData
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSComponentSquareSpatialYoungDataBefore p u v T) :
    H1PhysicalRHSYoungScalarZeroMajorantsBefore p u v T :=
  H1PhysicalRHSYoungScalarZeroMajorantsBefore_of_componentSquareZeroData
    (H1PhysicalRHSComponentSquareZeroDataBefore_of_spatialYoungData h)

#print axioms
  H1PhysicalTaxisX_norm_le_half_lapL2sq_add_half_taxisPartSq_of_spatial
#print axioms
  H1PhysicalUvxxX_norm_le_half_lapL2sq_add_half_uvxxPartSq_of_spatial
#print axioms
  H1PhysicalReactX_norm_le_half_lapL2sq_add_half_reactPartSq_of_spatial
#print axioms
  H1PhysicalRHSComponentSquareSpatialYoungDataBefore_of_squareData_and_productMeas
#print axioms
  H1PhysicalRHSComponentSquareSpatialYoungDataBefore_of_classical_squareTimeIntegrable
#print axioms H1PhysicalSquareProfilesTimeIntegrableBefore_of_zeroStartPrimitiveData
#print axioms
  H1PhysicalRHSComponentSquareSpatialYoungDataBefore_of_classical_zeroStartPrimitiveData
#print axioms
  H1PhysicalRHSComponentSquareZeroDataBefore_of_spatialYoungData
#print axioms H1PhysicalRHSYoungScalarZeroMajorantsBefore_of_spatialYoungData

end ShenWork.Paper2.IntervalChiNegH1PhysicalYoungSpatial
