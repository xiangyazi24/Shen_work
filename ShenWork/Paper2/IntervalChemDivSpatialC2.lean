/-
  ShenWork/Paper2/IntervalChemDivSpatialC2.lean

  Spatial C² of chemDivLift from u C⁴ + resolver v C⁴ + positivity.
  This is the genuine infrastructure gap blocking the B-form source tower.

  Chain: u C⁴, v C⁴, (1+v) > 0 on [0,1]
    → flux = u · v' / (1+v)^β is C³ on [0,1]
    → chemDivLift = ∂_x(flux) = deriv(flux) is C² on [0,1]
    → chemDivSource_weakH2_of_spatialC2 gives H² data
    → coupledChemDivSource_quadraticDecay_of_uniformH2 gives coefficient decay
    → summable envelope for DuhamelSourceTimeC1On
-/
import ShenWork.Paper2.IntervalBFormSpectralHchem
import ShenWork.PDE.IntervalChemDivFluxFACSourceDecay

open Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalDomainChemotaxisDiv)
open ShenWork.IntervalBFormSpectral (chemDivLift)

noncomputable section

namespace ShenWork.Paper2.ChemDivSpatialC2

/-! ## The flux function: u · v' / (1+v)^β -/

/-- The chemotaxis flux function whose spatial derivative is the chemDiv source.
`φ(y) = lift(u)(y) · deriv(lift(v))(y) / (1 + lift(v)(y))^β` -/
def chemFluxFun (β : ℝ) (u v : ℝ → ℝ) (y : ℝ) : ℝ :=
  u y * deriv v y / (1 + v y) ^ β

/-! ## C³ of the flux from C⁴ of u and v

The key composition: if u, v are C⁴ on [0,1] and (1+v) > 0 on [0,1],
then the flux u · v' / (1+v)^β is C³ on [0,1].

Proof sketch:
- v' = deriv v is C³ (one derivative of C⁴)
- u · v' is C³ (product of C⁴ and C³)
- (1+v)^β is C⁴ with positive base (composition of C⁴ with smooth rpow)
- u · v' / (1+v)^β is C³ (division by nonvanishing C⁴ denominator)
-/

theorem chemFlux_contDiffOn_three
    {β : ℝ} {u v : ℝ → ℝ}
    (hu : ContDiffOn ℝ 4 u (Icc (0 : ℝ) 1))
    (hv : ContDiffOn ℝ 4 v (Icc (0 : ℝ) 1))
    (hv_pos : ∀ x ∈ Icc (0 : ℝ) 1, (0 : ℝ) < 1 + v x)
    (hβ : 0 ≤ β) :
    ContDiffOn ℝ 3 (chemFluxFun β u v) (Icc (0 : ℝ) 1) := by
  sorry
  -- SORRY: ~60 lines. Uses ContDiffOn.mul, ContDiffOn.div, ContDiffOn.rpow_const
  -- (or ContDiffOn.pow for integer β), deriv_contDiffOn for v' from v C⁴.
  -- The positivity of (1+v) ensures the rpow/div are smooth.
  -- Mathlib's ContDiffOn.div needs the denominator to be nonvanishing,
  -- which follows from hv_pos.

/-! ## C² of chemDivLift from C³ of flux -/

/-- The chemDiv source lift is C² on [0,1] when the flux is C³.
chemDivLift = intervalDomainLift (chemotaxisDiv ...) = deriv(flux) on [0,1]. -/
theorem chemDivLift_contDiffOn_two
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (hu : ContDiffOn ℝ 4 (intervalDomainLift u) (Icc (0 : ℝ) 1))
    (hv : ContDiffOn ℝ 4 (intervalDomainLift v) (Icc (0 : ℝ) 1))
    (hv_pos : ∀ x ∈ Icc (0 : ℝ) 1, (0 : ℝ) < 1 + intervalDomainLift v x) :
    ContDiffOn ℝ 2 (chemDivLift p u v) (Icc (0 : ℝ) 1) := by
  sorry
  -- SORRY: ~30 lines. The chemDivLift is deriv(flux) on [0,1] by definition.
  -- flux is C³ from chemFlux_contDiffOn_three.
  -- C³ of flux on Icc → deriv(flux) is C² on Int(Icc) = Ioo.
  -- Need ContDiffOn ℝ 2 on the CLOSED Icc: use that flux is C³ on Icc
  -- (a convex set) so deriv is C² on Icc by ContDiffOn.deriv.

/-! ## Neumann BCs for chemDiv source -/

/-- The chemDiv source has homogeneous Neumann BCs on [0,1] when u and v
are Neumann-type functions (cosine series = even reflections). -/
theorem chemDivLift_neumann_bc
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (hu_C2 : ContDiffOn ℝ 2 (intervalDomainLift u) (Icc (0 : ℝ) 1))
    (hv_C2 : ContDiffOn ℝ 2 (intervalDomainLift v) (Icc (0 : ℝ) 1))
    (hu_N0 : deriv (intervalDomainLift u) 0 = 0)
    (hu_N1 : deriv (intervalDomainLift u) 1 = 0)
    (hv_N0 : deriv (intervalDomainLift v) 0 = 0)
    (hv_N1 : deriv (intervalDomainLift v) 1 = 0) :
    deriv (chemDivLift p u v) 0 = 0 ∧
    deriv (chemDivLift p u v) 1 = 0 := by
  sorry
  -- SORRY: ~40 lines. chemDivLift = deriv(flux) where flux = u·v'/(1+v)^β.
  -- deriv(chemDivLift) = deriv(deriv(flux)) = flux''.
  -- At x=0: flux(y) = u(y)·v'(y)/(1+v(y))^β.
  -- v'(0) = 0 (Neumann BC on v) → flux(0) = u(0)·0/(...) = 0.
  -- So flux is zero at x=0 regardless of u. And flux' = chemDiv.
  -- The Neumann BC deriv(chemDiv)(0) = 0 follows from the symmetry of
  -- the cosine representation (even extension → odd derivatives vanish at 0).

/-! ## Full weak H² Neumann data for chemDiv source -/

theorem chemDivSource_weakH2_of_uv_C4
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (hu : ContDiffOn ℝ 4 (intervalDomainLift u) (Icc (0 : ℝ) 1))
    (hv : ContDiffOn ℝ 4 (intervalDomainLift v) (Icc (0 : ℝ) 1))
    (hv_pos : ∀ x ∈ Icc (0 : ℝ) 1, (0 : ℝ) < 1 + intervalDomainLift v x)
    (hu_N0 : deriv (intervalDomainLift u) 0 = 0)
    (hu_N1 : deriv (intervalDomainLift u) 1 = 0)
    (hv_N0 : deriv (intervalDomainLift v) 0 = 0)
    (hv_N1 : deriv (intervalDomainLift v) 1 = 0) :
    IntervalWeakH2Neumann (chemDivLift p u v) := by
  have hC2 := chemDivLift_contDiffOn_two hu hv hv_pos
  have ⟨hN0, hN1⟩ := chemDivLift_neumann_bc
    (hu.of_le (by norm_num)) (hv.of_le (by norm_num))
    hu_N0 hu_N1 hv_N0 hv_N1
  exact ShenWork.PDE.IntervalChemDivFluxFACSourceDecay.chemDivSource_weakH2_of_spatialC2
    hC2
    (by rw [hN0]; exact tendsto_nhdsWithin_of_tendsto_nhds (tendsto_const_nhds))
    (by rw [hN1]; exact tendsto_nhdsWithin_of_tendsto_nhds (tendsto_const_nhds))
    hN0 hN1

#print axioms chemDivSource_weakH2_of_uv_C4

end ShenWork.Paper2.ChemDivSpatialC2
