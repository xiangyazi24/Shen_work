import ShenWork.Paper1.BrouwerCube
import ShenWork.Paper1.Statements

namespace ShenWork.Paper1

open Filter Topology
open ShenWork.Paper1.Freudenthal

noncomputable section

/-- Finite order-cube approximation data for producing local-uniform approximate
fixed points.  The finite map `Tfin N` is the projected wave map on a cube,
`lift N` turns a cube vector into a profile in the trap, and `residual_le`
converts a finite approximate fixed point into a local-uniform residual bound. -/
structure LocalUniformCubeApproxData
    (trap : (ℝ → ℝ) → Prop)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ) where
  dim : ℕ → ℕ
  Tfin : ∀ N, (Fin (dim N) → ℝ) → Fin (dim N) → ℝ
  lift : ∀ N, (Fin (dim N) → ℝ) → ℝ → ℝ
  eps : ℕ → ℝ
  localError : ℕ → ℝ → ℝ
  eps_pos : ∀ N, 0 < eps N
  maps : ∀ N, Set.MapsTo (Tfin N) (unitCube (dim N)) (unitCube (dim N))
  cont : ∀ N, ContinuousOn (Tfin N) (unitCube (dim N))
  lift_trap : ∀ N a, a ∈ unitCube (dim N) → trap (lift N a)
  localError_nonneg : ∀ N R, 0 ≤ localError N R
  localError_tendsto :
    ∀ R > 0, Tendsto (fun N => localError N R) atTop (𝓝 0)
  residual_le :
    ∀ N a, a ∈ unitCube (dim N) →
      ‖Tfin N a - a‖ ≤ eps N →
        ∀ R > 0, ∀ x, x ∈ Set.Icc (-R) R →
          |Tmap (lift N a) x - lift N a x| ≤ localError N R

/-- Finite cube Brouwer supplies the approximate fixed sequence required by the
existing local-uniform compactness bridge. -/
theorem localUniformApproxFixedPointSequences_of_cubeApproxData
    {trap : (ℝ → ℝ) → Prop}
    (H : ∀ Tmap : (ℝ → ℝ) → ℝ → ℝ,
      (∀ u, trap u → trap (Tmap u)) →
      LocalUniformContinuousOn trap Tmap →
      LocalUniformSequentiallyCompactRange trap Tmap →
        LocalUniformCubeApproxData trap Tmap) :
    LocalUniformApproxFixedPointSequences trap := by
  intro Tmap hmap hcont hcompact
  let D := H Tmap hmap hcont hcompact
  let a : ∀ N, Fin (D.dim N) → ℝ := fun N =>
    Classical.choose
      (Freudenthal.brouwer_cube_approx (D.maps N) (D.cont N)
        (D.eps N) (D.eps_pos N))
  have ha : ∀ N, a N ∈ unitCube (D.dim N) := by
    intro N
    exact (Classical.choose_spec
      (Freudenthal.brouwer_cube_approx (D.maps N) (D.cont N)
        (D.eps N) (D.eps_pos N))).1
  have hclose : ∀ N, ‖D.Tfin N (a N) - a N‖ ≤ D.eps N := by
    intro N
    exact (Classical.choose_spec
      (Freudenthal.brouwer_cube_approx (D.maps N) (D.cont N)
        (D.eps N) (D.eps_pos N))).2
  refine ⟨fun N => D.lift N (a N), ?_, ?_⟩
  · intro N
    exact D.lift_trap N (a N) (ha N)
  · intro R hR η hη
    have hlim := D.localError_tendsto R hR
    obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp hlim η hη
    have hev : ∀ᶠ N in atTop, dist (D.localError N R) 0 < η :=
      Filter.eventually_atTop.mpr ⟨N0, hN0⟩
    filter_upwards [hev] with N hN x hx
    have hNabs : |D.localError N R - 0| < η := by
      simpa [Real.dist_eq] using hN
    have herr : D.localError N R < η := by
      simpa [sub_zero, abs_of_nonneg (D.localError_nonneg N R)] using hNabs
    exact lt_of_le_of_lt (D.residual_le N (a N) (ha N) (hclose N) R hR x hx)
      herr

/-- The committed bridge from approximate fixed sequences discharges the abstract
local-uniform Schauder principle once finite cube approximation data are supplied. -/
theorem localUniformSchauderFixedPointPrinciple_of_cubeApproxData
    {trap : (ℝ → ℝ) → Prop}
    (H : ∀ Tmap : (ℝ → ℝ) → ℝ → ℝ,
      (∀ u, trap u → trap (Tmap u)) →
      LocalUniformContinuousOn trap Tmap →
      LocalUniformSequentiallyCompactRange trap Tmap →
        LocalUniformCubeApproxData trap Tmap) :
    LocalUniformSchauderFixedPointPrinciple trap :=
  localUniformSchauderFixedPointPrinciple_of_approx_fixed_sequences
    (localUniformApproxFixedPointSequences_of_cubeApproxData H)

#print axioms localUniformApproxFixedPointSequences_of_cubeApproxData
#print axioms localUniformSchauderFixedPointPrinciple_of_cubeApproxData

end

end ShenWork.Paper1
