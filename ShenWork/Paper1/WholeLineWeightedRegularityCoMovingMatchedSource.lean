import ShenWork.Paper1.WholeLineWeightedRegularityMatchedSourceMild
import ShenWork.Paper1.WholeLineWeightedRegularityPositiveRestartDQ

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Genuine matched sources on a canonical co-moving slice

The canonical restart stores its nonlinear sources in laboratory
coordinates and evaluates them at `x + c * s`.  Translation covariance of
the frozen elliptic resolver identifies those expressions with the genuine
flux and shifted reaction of the co-moving population slice.  The final two
theorems instantiate the cap-weighted matched-source mild estimates directly
on such a slice.
-/

/-- Translation covariance of the genuine chemotaxis flux. -/
theorem wholeLineChemotaxisFlux_comp_add_const
    (p : CMParams) {u : ℝ → ℝ}
    (hu : IsCUnifBdd u) (hu0 : ∀ x, 0 ≤ u x) (a y : ℝ) :
    wholeLineChemotaxisFlux p (fun x => u (x + a)) y =
      wholeLineChemotaxisFlux p u (y + a) := by
  unfold wholeLineChemotaxisFlux
  rw [frozenElliptic_deriv_comp_add_const p hu hu0 a y]

/-- Translation covariance of the shifted logistic reaction. -/
theorem wholeLineCauchyShiftedReaction_comp_add_const
    (p : CMParams) (u : ℝ → ℝ) (a y : ℝ) :
    wholeLineCauchyShiftedReaction p (fun x => u (x + a)) y =
      wholeLineCauchyShiftedReaction p u (y + a) := by
  rfl

/-- On the physical strip, the canonical co-moving flux source is exactly
the genuine flux of the co-moving population slice. -/
theorem wholeLineCauchyCoMovingFluxSource_eq_genuineFlux_of_strip
    (p : CMParams) (c : ℝ) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (U : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (U z).1 x ∈ Set.Icc (0 : ℝ) M) (s : ℝ) :
    wholeLineCauchyCoMovingFluxSource p c hM hT U s =
      wholeLineChemotaxisFlux p (fun x =>
        (wholeLineBUCTrajectoryExtend hT U s).1 (x + c * s)) := by
  rw [wholeLineCauchyCoMovingFluxSource_eq_physical_of_strip
    p c hM hT U hstrip s]
  funext x
  symm
  apply wholeLineChemotaxisFlux_comp_add_const
  · exact WholeLineBUC.isCUnifBdd
      (wholeLineBUCTrajectoryExtend hT U s)
  · intro y
    change 0 ≤ (U (Set.projIcc 0 T hT s)).1 y
    exact (hstrip (Set.projIcc 0 T hT s) y).1

/-- On the physical strip, the canonical co-moving reaction source is
exactly the shifted reaction of the co-moving population slice. -/
theorem wholeLineCauchyCoMovingReactionSource_eq_genuineReaction_of_strip
    (p : CMParams) (c : ℝ) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (U : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (U z).1 x ∈ Set.Icc (0 : ℝ) M) (s : ℝ) :
    wholeLineCauchyCoMovingReactionSource p c hM hT U s =
      wholeLineCauchyShiftedReaction p (fun x =>
        (wholeLineBUCTrajectoryExtend hT U s).1 (x + c * s)) := by
  rw [wholeLineCauchyCoMovingReactionSource_eq_physical_of_strip
    p c hM hT U hstrip s]
  funext x
  symm
  exact wholeLineCauchyShiftedReaction_comp_add_const p
    (wholeLineBUCTrajectoryExtend hT U s).1 (c * s) x

/-- Fixed-time canonical co-moving specialization of the genuine matched
flux raw-DQ heat-gradient estimate. -/
theorem exists_capWeightedMovingHeatGradient_coMovingFluxRawDQL2_le_kernel
    (p : CMParams) {M T s Brel DU eta R h c tau L X F : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hBrel : 0 ≤ Brel) (hDU : 0 ≤ DU)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hh : h ≠ 0)
    (htau : 0 < tau) (htauL : tau ≤ L) (hX : 0 ≤ X) (hF : 0 ≤ F)
    (Traj : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (Traj z).1 x ∈ Set.Icc (0 : ℝ) M)
    {W : ℝ → ℝ}
    (hWcb : IsCUnifBdd W)
    (hWmem : ∀ x, W x ∈ Set.Icc (0 : ℝ) M)
    (hWpos : ∀ x, 0 < W x)
    (hbase : ∀ x, |(W (x + h) - W x) / h| ≤ DU)
    (hrelative : ∀ x, ∀ theta ∈ Set.Icc (0 : ℝ) 1,
      |(W (x + h) - W x) / h| ≤
        Brel * (theta * W (x + h) + (1 - theta) * W x))
    (hvalue : Integrable (fun x => capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) - W x| ^ 2))
    (hraw : Integrable (fun x => capWeight eta R x *
      |eta * ((wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) - W x) +
        spatialDifferenceQuotient h (fun y =>
          (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) - W y) x| ^ 2))
    (hraw_energy :
      (∫ x : ℝ, capWeight eta R x *
        |eta * ((wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) - W x) +
          spatialDifferenceQuotient h (fun y =>
            (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) - W y) x| ^ 2) ≤
        X ^ 2)
    (hvalue_energy :
      (∫ x : ℝ, capWeight eta R x *
        |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) - W x| ^ 2) ≤
        F ^ 2) :
    let G := fun y => wholeLineCauchyCoMovingFluxSource
      p c hM hT Traj s y - wholeLineChemotaxisFlux p W y
    let Fq := fun y => eta * G y + spatialDifferenceQuotient h G y
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x => capWeightSqrt eta R x *
        paper5MovingFrameHeatGradOp c tau Fq x) ∧
      ‖Z‖ ≤
        (2 * capMildGrowthBound eta c L * eta +
          (2 * capMildGrowthBound eta c L *
            (2 / Real.sqrt (4 * Real.pi))) *
              tau ^ (-(1 / 2 : ℝ))) *
          (Real.sqrt (matchedFluxRawQSquareConstant p M eta) * X +
            Real.sqrt
              (matchedFluxRawWSquareConstant p M Brel DU eta h) * F) := by
  dsimp only
  let us : ℝ → ℝ := fun x =>
    (wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s)
  have hus : IsCUnifBdd us := by
    exact isCUnifBdd_comp_add_const
      (WholeLineBUC.isCUnifBdd (wholeLineBUCTrajectoryExtend hT Traj s))
      (c * s)
  have hus_mem : ∀ x, us x ∈ Set.Icc (0 : ℝ) M := by
    intro x
    change (Traj (Set.projIcc 0 T hT s)).1 (x + c * s) ∈
      Set.Icc (0 : ℝ) M
    exact hstrip (Set.projIcc 0 T hT s) (x + c * s)
  have hsource :
      wholeLineCauchyCoMovingFluxSource p c hM hT Traj s =
        wholeLineChemotaxisFlux p us := by
    simpa only [us] using
      wholeLineCauchyCoMovingFluxSource_eq_genuineFlux_of_strip
        p c hM hT Traj hstrip s
  have hcore :=
    exists_capWeightedMovingHeatGradient_genuineFluxRawDQL2_le_kernel
      p (c := c) (u := us) (U := W)
        hM hBrel hDU heta0 heta1 hh htau htauL hX hF
        hus hWcb hus_mem hWmem hWpos hbase hrelative
        hvalue hraw hraw_energy hvalue_energy
  dsimp only [us] at hcore
  simpa only [hsource] using hcore

/-- Fixed-time canonical co-moving specialization of the genuine matched
reaction raw-DQ heat estimate. -/
theorem exists_capWeightedMovingHeat_coMovingReactionRawDQL2_le_kernel
    (p : CMParams) {M T s eta R h DU c tau L X F : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (heta0 : 0 ≤ eta) (hDU : 0 ≤ DU) (hh : h ≠ 0)
    (htau : 0 < tau) (htauL : tau ≤ L) (hX : 0 ≤ X) (hF : 0 ≤ F)
    (Traj : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (Traj z).1 x ∈ Set.Icc (0 : ℝ) M)
    {W : ℝ → ℝ}
    (hWcb : IsCUnifBdd W)
    (hWmem : ∀ x, W x ∈ Set.Icc (0 : ℝ) M)
    (hWquot : ∀ x, |spatialDifferenceQuotient h W x| ≤ DU)
    (hvalue : Integrable (fun x => capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) - W x| ^ 2))
    (hraw : Integrable (fun x => capWeight eta R x *
      |eta * ((wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) - W x) +
        spatialDifferenceQuotient h (fun y =>
          (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) - W y) x| ^ 2))
    (hraw_energy :
      (∫ x : ℝ, capWeight eta R x *
        |eta * ((wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) - W x) +
          spatialDifferenceQuotient h (fun y =>
            (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) - W y) x| ^ 2) ≤
        X ^ 2)
    (hvalue_energy :
      (∫ x : ℝ, capWeight eta R x *
        |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) - W x| ^ 2) ≤
        F ^ 2) :
    let G := fun y => wholeLineCauchyCoMovingReactionSource
      p c hM hT Traj s y - wholeLineCauchyShiftedReaction p W y
    let Fq := fun y => eta * G y + spatialDifferenceQuotient h G y
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x => capWeightSqrt eta R x *
        paper5MovingFrameHeatOp c tau Fq x) ∧
      ‖Z‖ ≤ 2 * capMildGrowthBound eta c L *
        (Real.sqrt (matchedShiftedReactionRawQSquareConstant p M) * X +
          Real.sqrt
            (matchedShiftedReactionRawWSquareConstant p M eta DU) * F) := by
  dsimp only
  let us : ℝ → ℝ := fun x =>
    (wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s)
  have hus : IsCUnifBdd us := by
    exact isCUnifBdd_comp_add_const
      (WholeLineBUC.isCUnifBdd (wholeLineBUCTrajectoryExtend hT Traj s))
      (c * s)
  have hus_mem : ∀ x, us x ∈ Set.Icc (0 : ℝ) M := by
    intro x
    change (Traj (Set.projIcc 0 T hT s)).1 (x + c * s) ∈
      Set.Icc (0 : ℝ) M
    exact hstrip (Set.projIcc 0 T hT s) (x + c * s)
  have hsource :
      wholeLineCauchyCoMovingReactionSource p c hM hT Traj s =
        wholeLineCauchyShiftedReaction p us := by
    simpa only [us] using
      wholeLineCauchyCoMovingReactionSource_eq_genuineReaction_of_strip
        p c hM hT Traj hstrip s
  have hcore :=
    exists_capWeightedMovingHeat_genuineShiftedReactionRawDQL2_le_kernel
      p (c := c) (u := us) (U := W)
        hM heta0 hDU hh htau htauL hX hF
        hus hWcb hus_mem hWmem hWquot
        hvalue hraw hraw_energy hvalue_energy
  dsimp only [us] at hcore
  simpa only [hsource] using hcore

#print axioms wholeLineChemotaxisFlux_comp_add_const
#print axioms wholeLineCauchyShiftedReaction_comp_add_const
#print axioms wholeLineCauchyCoMovingFluxSource_eq_genuineFlux_of_strip
#print axioms wholeLineCauchyCoMovingReactionSource_eq_genuineReaction_of_strip
#print axioms
  exists_capWeightedMovingHeatGradient_coMovingFluxRawDQL2_le_kernel
#print axioms
  exists_capWeightedMovingHeat_coMovingReactionRawDQL2_le_kernel

end ShenWork.Paper1
