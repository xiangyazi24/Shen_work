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
import ShenWork.PDE.IntervalChemDivAEMeasurable

open Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalDomainChemotaxisDiv)
open ShenWork.PDE.IntervalMildSourceDecayHelper (IntervalWeakH2Neumann)
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

theorem chemFlux_contDiff_three
    {β : ℝ} {u v : ℝ → ℝ}
    (hu : ContDiff ℝ 4 u)
    (hv : ContDiff ℝ 4 v)
    (hv_pos : ∀ x, (0 : ℝ) < 1 + v x)
    (hβnn : 0 ≤ β) :
    ContDiff ℝ 3 (chemFluxFun β u v) := by
  unfold chemFluxFun
  have hv3 : ContDiff ℝ 3 (deriv v) := by
    have : ContDiff ℝ (3 + 1) v := hv.of_le (by norm_num)
    exact this.deriv'
  have hu3 : ContDiff ℝ 3 u := hu.of_le (by norm_num)
  have hprod : ContDiff ℝ 3 (fun y => u y * deriv v y) := hu3.mul hv3
  have hdenom_pos : ∀ x, (1 + v x) ^ β ≠ 0 := by
    intro x
    exact ne_of_gt (Real.rpow_pos_of_pos (hv_pos x) β)
  have hv3' : ContDiff ℝ 3 v := hv.of_le (by norm_num)
  have hdenom : ContDiff ℝ 3 (fun y => (1 + v y) ^ β) := by
    have h1v : ContDiff ℝ 3 (fun y => 1 + v y) := contDiff_const.add hv3'
    exact h1v.rpow_const_of_ne (fun x => ne_of_gt (hv_pos x))
  exact hprod.div hdenom (fun x => hdenom_pos x)

theorem chemFlux_contDiffOn_three_of_global
    {β : ℝ} {u v : ℝ → ℝ}
    (hu : ContDiff ℝ 4 u)
    (hv : ContDiff ℝ 4 v)
    (hv_pos : ∀ x, (0 : ℝ) < 1 + v x)
    (hβnn : 0 ≤ β) :
    ContDiffOn ℝ 3 (chemFluxFun β u v) (Icc (0 : ℝ) 1) :=
  (chemFlux_contDiff_three hu hv hv_pos hβnn).contDiffOn

-- General ContDiffOn version omitted — use chemFlux_contDiffOn_three_of_global
-- for the heat semigroup case (global C⁴ inputs).

/-! ## C² of chemDivLift from C³ of flux -/

/-- Global C² of `deriv(chemFluxFun)` from global C⁴ of u,v. -/
theorem chemFluxDeriv_contDiff_two
    {β : ℝ} {u v : ℝ → ℝ}
    (hu : ContDiff ℝ 4 u) (hv : ContDiff ℝ 4 v)
    (hv_pos : ∀ x, (0 : ℝ) < 1 + v x) (hβnn : 0 ≤ β) :
    ContDiff ℝ 2 (deriv (chemFluxFun β u v)) := by
  have h3 : ContDiff ℝ (2 + 1) (chemFluxFun β u v) := by
    exact (chemFlux_contDiff_three hu hv hv_pos hβnn).of_le (by norm_num)
  exact h3.deriv'

/-- For GLOBAL C⁴ u, v (e.g. heat semigroup cosine series), chemDivLift is C² on [0,1].
The key: chemDivLift = deriv(chemFluxFun) on [0,1] by definition unfolding,
and deriv(chemFluxFun) is GLOBALLY C² from chemFluxDeriv_contDiff_two. -/
theorem chemDivLift_contDiffOn_two_of_global
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (hu : ContDiff ℝ 4 (intervalDomainLift u))
    (hv : ContDiff ℝ 4 (intervalDomainLift v))
    (hv_pos : ∀ x, (0 : ℝ) < 1 + intervalDomainLift v x) :
    ContDiffOn ℝ 2 (chemDivLift p u v) (Icc (0 : ℝ) 1) := by
  have hglobal := chemFluxDeriv_contDiff_two hu hv hv_pos p.hβ
  have h_eq : ∀ x ∈ Icc (0 : ℝ) 1,
      chemDivLift p u v x =
        deriv (chemFluxFun p.β (intervalDomainLift u) (intervalDomainLift v)) x := by
    intro x hx
    unfold chemDivLift intervalDomainLift
    rw [dif_pos hx]
    unfold intervalDomainChemotaxisDiv
    unfold chemFluxFun
    rfl
  exact hglobal.contDiffOn.congr h_eq

-- General chemDivLift_contDiffOn_two omitted — use _of_global for heat semigroup.

/-! ## Neumann BCs for chemDiv source -/

/-- The chemDiv source has homogeneous Neumann BCs on [0,1] when u and v
are Neumann-type functions (cosine series = even reflections). -/
theorem chemDivLift_neumann_bc
    (p : CM2Params) (u v : intervalDomainPoint → ℝ) :
    deriv (chemDivLift p u v) 0 = 0 ∧
    deriv (chemDivLift p u v) 1 = 0 := by
  simp only [chemDivLift]
  exact ⟨ShenWork.intervalDomainLift_deriv_at_zero_eq_zero _,
    ShenWork.intervalDomainLift_deriv_at_one_eq_zero _⟩
  -- SORRY: ~40 lines. chemDivLift = deriv(flux) where flux = u·v'/(1+v)^β.
  -- deriv(chemDivLift) = deriv(deriv(flux)) = flux''.
  -- At x=0: flux(y) = u(y)·v'(y)/(1+v(y))^β.
  -- v'(0) = 0 (Neumann BC on v) → flux(0) = u(0)·0/(...) = 0.
  -- So flux is zero at x=0 regardless of u. And flux' = chemDiv.
  -- The Neumann BC deriv(chemDiv)(0) = 0 follows from the symmetry of
  -- the cosine representation (even extension → odd derivatives vanish at 0).

/-! ## Full weak H² Neumann data for chemDiv source -/

noncomputable def chemDivSource_weakH2_of_uv_C4_global
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (hu : ContDiff ℝ 4 (intervalDomainLift u))
    (hv : ContDiff ℝ 4 (intervalDomainLift v))
    (hv_pos : ∀ x, (0 : ℝ) < 1 + intervalDomainLift v x) :
    IntervalWeakH2Neumann (chemDivLift p u v) := by
  -- Strategy: build H2 for the GLOBAL function deriv(chemFluxFun) (which is smooth
  -- everywhere, no endpoint issues), then transfer via congr_on_Icc.
  set F := deriv (chemFluxFun p.β (intervalDomainLift u) (intervalDomainLift v))
  have hF_C2 : ContDiff ℝ 2 F := chemFluxDeriv_contDiff_two hu hv hv_pos p.hβ
  sorry
  -- Route: build H2 for global F = deriv(chemFluxFun) via
  -- intervalWeakH2Neumann_of_contDiffOn (smooth → tendsto trivial),
  -- then congr_on_Icc to transfer to chemDivLift (agreement on [0,1]).
  -- Remaining sorry: deriv F 0 = 0 (Neumann BC of the global function at 0)
  -- + the agreement bridge (chemDivLift = F on [0,1], proved in the C2 theorem above)

-- General chemDivSource_weakH2_of_uv_C4 omitted — use _global for heat semigroup.

#print axioms chemDivSource_weakH2_of_uv_C4_global

end ShenWork.Paper2.ChemDivSpatialC2
