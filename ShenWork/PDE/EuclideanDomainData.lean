/-
  ShenWork/PDE/EuclideanDomainData.lean

  The measure-theoretic and whole-space differential data attached to a
  bounded open subset of a finite-dimensional Euclidean space.

  The point type is the closure of the open set, rather than the open set
  itself.  This is forced by the abstract Paper2 interface: positivity is
  stated on every point of the closed domain and the Neumann condition is
  stated on `D.boundary`.  The volume integral is nevertheless restricted to
  the open set.
-/
import ShenWork.PDE.BoundedDomainData
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

open MeasureTheory Set

open scoped InnerProductSpace Laplacian

noncomputable section

namespace ShenWork.EuclideanDomain

/-- The ambient `N`-dimensional real Euclidean space. -/
abbrev Ambient (N : ℕ) := EuclideanSpace ℝ (Fin N)

/-- Geometric data available before developing a smooth-boundary API.

`boundaryNormal` is deliberately bundled as data.  Mathlib currently has no
construction which produces an outward normal field from a smooth bounded
subset of Euclidean space.  Its unit-length law is recorded here; an
outwardness theorem, trace theory, and Green's formula are not claimed.
-/
structure EuclideanDomainData (N : ℕ) where
  Ω : Set (Ambient N)
  isOpen_Ω : IsOpen Ω
  isBounded_Ω : Bornology.IsBounded Ω
  volume_pos : 0 < (volume Ω).toReal
  boundaryNormal : ∀ x : Ambient N, x ∈ frontier Ω → Ambient N
  boundaryNormal_unit :
    ∀ (x : Ambient N) (hx : x ∈ frontier Ω), ‖boundaryNormal x hx‖ = 1

namespace EuclideanDomainData

variable {N : ℕ} (D : EuclideanDomainData N)

/-- The closed-domain point type used by the Paper2/Paper3 statement layer. -/
abbrev Point := ↥(closure D.Ω)

/-- Lebesgue measure restricted to the open domain. -/
def domainMeasure : Measure (Ambient N) :=
  volume.restrict D.Ω

/-- Extend a function on the closed domain by zero to the ambient space. -/
def lift (f : D.Point → ℝ) : Ambient N → ℝ :=
  by
    classical
    exact fun x => if hx : x ∈ closure D.Ω then f ⟨x, hx⟩ else 0

/-- The domain integral.  Although functions live on `closure Ω`, only `Ω`
is integrated. -/
def integral (f : D.Point → ℝ) : ℝ :=
  ∫ x, D.lift f x ∂D.domainMeasure

/-- The closed-domain supremum norm used by the abstract interface. -/
def supNorm (f : D.Point → ℝ) : ℝ :=
  sSup (Set.range fun x : D.Point => |f x|)

/-- The closed-domain infimum used by the abstract interface. -/
def infValue (f : D.Point → ℝ) : ℝ :=
  sInf (Set.range f)

/-- The standard orthonormal coordinate vector. -/
def basisVector (i : Fin N) : Ambient N :=
  EuclideanSpace.basisFun (Fin N) ℝ i

/-- The gradient represented in the standard orthonormal basis.

The derivative is taken after the same zero extension used by the interval
instance.  On the open interior this agrees locally with the original
function whenever the latter has a differentiable ambient representative.
-/
def gradient (f : D.Point → ℝ) (x : Ambient N) : Ambient N :=
  ∑ i : Fin N,
    (fderiv ℝ (D.lift f) x (basisVector i)) • basisVector i

/-- Norm of the ambient Frechet derivative of a closed-domain function. -/
def gradNorm (f : D.Point → ℝ) (x : D.Point) : ℝ :=
  ‖fderiv ℝ (D.lift f) x.1‖

/-- The Euclidean Laplacian of the zero extension. -/
def laplacian (f : D.Point → ℝ) (x : D.Point) : ℝ :=
  Δ (D.lift f) x.1

/-- Divergence in the standard orthonormal basis. -/
def divergence (_D : EuclideanDomainData N)
    (F : Ambient N → Ambient N) (x : Ambient N) : ℝ :=
  ∑ i : Fin N,
    inner ℝ (fderiv ℝ F x (basisVector i)) (basisVector i)

/-- The paper-faithful chemotactic flux in ambient coordinates. -/
def chemotaxisFlux (p : CM2Params) (u v : D.Point → ℝ) :
    Ambient N → Ambient N :=
  fun x =>
    ((D.lift u x) ^ p.m / (1 + D.lift v x) ^ p.β) • D.gradient v x

/-- Divergence of the paper-faithful chemotactic flux. -/
def chemotaxisDiv (p : CM2Params) (u v : D.Point → ℝ)
    (x : D.Point) : ℝ :=
  D.divergence (D.chemotaxisFlux p u v) x.1

/-- The absolute cross-diffusion term produced by testing with
`u ^ (pExp - 1)`. -/
def crossDiffusionEnergyTerm (p : CM2Params) (pExp : ℝ)
    (u v : D.Point → ℝ) : ℝ :=
  ∫ x,
    (D.lift u x) ^ (pExp + p.m - 2) *
        ‖fderiv ℝ (D.lift u) x‖ * ‖fderiv ℝ (D.lift v) x‖ /
      (1 + D.lift v x) ^ p.β
    ∂D.domainMeasure

/-- The bundled unit normal on boundary points and zero away from the
boundary. -/
def normalVector (x : D.Point) : Ambient N :=
  by
    classical
    exact if hx : x.1 ∈ frontier D.Ω then D.boundaryNormal x.1 hx else 0

/-- Directional derivative along the bundled boundary normal.

This supplies the type required by `BoundedDomainData`; proving that the
bundled direction is the geometric outward normal, and proving trace/Green
identities for it, remain boundary-theory obligations.
-/
def normalDeriv (f : D.Point → ℝ) (x : D.Point) : ℝ :=
  fderivWithin ℝ (D.lift f) (closure D.Ω) x.1 (D.normalVector x)

/-- Interior spatial `C²` and pointwise time `C¹` regularity.  Boundary trace
regularity is intentionally not folded into this predicate. -/
def classicalRegularity (T : ℝ) (u v : ℝ → D.Point → ℝ) : Prop :=
  (∀ t ∈ Set.Ioo (0 : ℝ) T,
      ContDiffOn ℝ 2 (D.lift (u t)) D.Ω ∧
        ContDiffOn ℝ 2 (D.lift (v t)) D.Ω) ∧
    (∀ x : D.Point,
      ContDiffOn ℝ 1 (fun t : ℝ => u t x) (Set.Ioo (0 : ℝ) T) ∧
        ContDiffOn ℝ 1 (fun t : ℝ => v t x) (Set.Ioo (0 : ℝ) T))

/-- Concrete bounded-domain data associated with `D`.

All whole-space differential fields are explicit Mathlib definitions.  The
normal derivative uses `D.boundaryNormal`, whose geometric outwardness is not
provided by Mathlib and is therefore not asserted here.
-/
def toBoundedDomainData : Paper2.BoundedDomainData where
  Point := D.Point
  inside := {x : D.Point | x.1 ∈ D.Ω}
  boundary := {x : D.Point | x.1 ∈ frontier D.Ω}
  volume := (volume D.Ω).toReal
  supNorm := D.supNorm
  infValue := D.infValue
  integral := D.integral
  gradNorm := D.gradNorm
  timeDeriv := fun u t x => deriv (fun s : ℝ => u s x) t
  laplacian := D.laplacian
  chemotaxisDiv := D.chemotaxisDiv
  crossDiffusionEnergyTerm := D.crossDiffusionEnergyTerm
  normalDeriv := D.normalDeriv
  initialAdmissible := fun u₀ =>
    BddAbove (Set.range fun x => |u₀ x|) ∧ Continuous u₀
  classicalRegularity := D.classicalRegularity

/-- Short instance-facing name, parallel to `intervalDomain`. -/
abbrev euclideanDomain : Paper2.BoundedDomainData :=
  D.toBoundedDomainData

@[simp] theorem euclideanDomain_Point : D.euclideanDomain.Point = D.Point := rfl

@[simp] theorem mem_euclideanDomain_inside (x : D.Point) :
    x ∈ D.euclideanDomain.inside ↔ x.1 ∈ D.Ω :=
  Iff.rfl

@[simp] theorem mem_euclideanDomain_boundary (x : D.Point) :
    x ∈ D.euclideanDomain.boundary ↔ x.1 ∈ frontier D.Ω :=
  Iff.rfl

theorem inside_isOpen :
    IsOpen {x : D.Point | x.1 ∈ D.Ω} :=
  D.isOpen_Ω.preimage continuous_subtype_val

theorem boundary_isClosed :
    IsClosed {x : D.Point | x.1 ∈ frontier D.Ω} :=
  isClosed_frontier.preimage continuous_subtype_val

/-- Boundedness of `Ω` makes the closed point space compact in finite
dimension. -/
theorem closure_isCompact : IsCompact (closure D.Ω) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_closure D.isBounded_Ω.closure

@[simp] theorem euclideanDomain_volume :
    D.euclideanDomain.volume = (volume D.Ω).toReal :=
  rfl

theorem euclideanDomain_volume_pos : 0 < D.euclideanDomain.volume :=
  D.volume_pos

theorem volume_lt_top : volume D.Ω < ⊤ :=
  D.isBounded_Ω.measure_lt_top

theorem domainMeasure_univ_lt_top : D.domainMeasure Set.univ < ⊤ := by
  rw [domainMeasure, Measure.restrict_apply_univ]
  exact D.volume_lt_top

instance domainMeasure_isFiniteMeasure : IsFiniteMeasure D.domainMeasure :=
  ⟨D.domainMeasure_univ_lt_top⟩

theorem normalVector_unit_of_mem_boundary {x : D.Point}
    (hx : x ∈ D.euclideanDomain.boundary) : ‖D.normalVector x‖ = 1 := by
  have hx' : x.1 ∈ frontier D.Ω := hx
  simp only [normalVector, dif_pos hx']
  exact D.boundaryNormal_unit x.1 hx'

end EuclideanDomainData

end ShenWork.EuclideanDomain

end
