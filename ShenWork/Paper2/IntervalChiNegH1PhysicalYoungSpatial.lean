import ShenWork.Paper2.IntervalChiNegH1PhysicalInitialRHS
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
  H1PhysicalRHSComponentSquareZeroDataBefore_of_spatialYoungData
#print axioms H1PhysicalRHSYoungScalarZeroMajorantsBefore_of_spatialYoungData

end ShenWork.Paper2.IntervalChiNegH1PhysicalYoungSpatial
