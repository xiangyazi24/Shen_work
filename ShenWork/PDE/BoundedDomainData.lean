import ShenWork.Paper2.Defs

noncomputable section

namespace ShenWork.Paper2

/-- Abstract data for the smooth bounded Neumann domain used in Paper2.

  The differential operators are intentionally bundled here: the statement layer
  can express the paper PDE now, while later analytic work can instantiate these
  fields for a concrete smooth bounded domain in `ℝ^N`.
-/
structure BoundedDomainData where
  Point : Type
  inside : Set Point
  boundary : Set Point
  volume : ℝ
  supNorm : (Point → ℝ) → ℝ
  infValue : (Point → ℝ) → ℝ
  integral : (Point → ℝ) → ℝ
  gradNorm : (Point → ℝ) → Point → ℝ
  timeDeriv : (ℝ → Point → ℝ) → ℝ → Point → ℝ
  laplacian : (Point → ℝ) → Point → ℝ
  chemotaxisDiv : CM2Params → (Point → ℝ) → (Point → ℝ) → Point → ℝ
  crossDiffusionEnergyTerm : CM2Params → ℝ → (Point → ℝ) → (Point → ℝ) → ℝ
  normalDeriv : (Point → ℝ) → Point → ℝ
  initialAdmissible : (Point → ℝ) → Prop
  classicalRegularity : ℝ → (ℝ → Point → ℝ) → (ℝ → Point → ℝ) → Prop

end ShenWork.Paper2

end
