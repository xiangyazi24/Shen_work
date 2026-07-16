import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorRestartNatural
import ShenWork.Paper1.WholeLineWeightedRegularityRestart
import ShenWork.Paper1.WholeLineWeightedRegularityForcingL2Trajectory
import ShenWork.Paper1.WholeLineWeightedRegularityCoMovingMatchedSource

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# The actual weighted perturbation in the damped generator restart

The canonical fixed-point restart is written with the modified heat
generator.  This file supplies the two concrete seams needed to view that
restart in the Hilbert-space form consumed by the damping-removal argument:

* transfer the spatial derivative from the heat kernel to a classical
  weighted flux source;
* lift a pointwise damped restart of the actual weighted population to
  `WholeLineRealL2`.

Neither seam assumes a weighted second derivative or membership in the
generator domain.
-/

/-- For a bounded classical source, the spatial derivative of the
conjugated moving heat orbit may be transferred from the Gaussian kernel to
the source. -/
theorem weightedMovingHeatGradientEta_eq_weightedMovingHeatEta_deriv_of_bounded
    {eta c lag x CQ DQ : ℝ} {Q Qx : ℝ → ℝ}
    (hlag : 0 < lag)
    (hQ : ∀ y, |Q y| ≤ CQ)
    (hQx : ∀ y, |Qx y| ≤ DQ)
    (hQderiv : ∀ y, HasDerivAt Q (Qx y) y)
    (hQx_cont : Continuous Qx) :
    weightedMovingHeatGradientEta eta c lag Q x =
      weightedMovingHeatEta eta c lag Qx x := by
  have hderiv : deriv Q = Qx := by
    funext y
    exact (hQderiv y).deriv
  have h := wholeLineDriftHeatGradOp_eq_heatOp_deriv
    (d := c - 2 * eta) (t := lag) (x := x) hlag hQ
      (fun y => by rw [hderiv]; exact hQx y)
      (fun y => by simpa [hderiv] using hQderiv y)
      (by simpa [hderiv] using hQx_cont)
  unfold wholeLineDriftHeatGradOp wholeLineDriftHeatOp at h
  have hbase :
      wholeLineCauchyHeatGradOp lag Q
          (x + (c - 2 * eta) * lag) =
        wholeLineCauchyMovingHeatOp (c - 2 * eta) lag (deriv Q) x := by
    exact mul_left_cancel₀ (Real.exp_ne_zero lag) h
  unfold wholeLineCauchyMovingHeatOp wholeLineCauchyHeatGradOp
    wholeLineCauchyHeatOp modifiedSemigroup heatSemigroup at hbase
  rw [integral_const_mul] at hbase
  have hconv :
      (∫ y : ℝ,
          deriv (fun z : ℝ => heatKernel lag (z - y))
            (x + (c - 2 * eta) * lag) * Q y) =
        ∫ y : ℝ, heatKernel lag
          (x + (c - 2 * eta) * lag - y) * deriv Q y := by
    exact mul_left_cancel₀ (Real.exp_ne_zero (-lag)) hbase
  have h' :
      (∫ y : ℝ, deriv (fun z : ℝ => heatKernel lag z)
          (x + (c - 2 * eta) * lag - y) * Q y) =
        ∫ y : ℝ, heatKernel lag
          (x + (c - 2 * eta) * lag - y) * Qx y := by
    rw [← hderiv]
    convert hconv using 1
    apply integral_congr_ae
    filter_upwards with y
    rw [deriv_heatKernel_translated_left hlag
      (x + (c - 2 * eta) * lag) y,
      deriv_heatKernel hlag]
  unfold weightedMovingHeatGradientEta weightedMovingHeatEta
  simpa only [weightedMovingHeatMarkovKernel] using
    congrArg (fun z : ℝ => weightedMovingHeatGrowth eta c lag * z) h'

/-- One damped source integrand in the split canonical restart is exactly
the heat orbit of `Z + F`, once the weighted flux derivative and shifted
reaction have been identified with that sum. -/
theorem paper5Weighted_splitRestartTerm_eq_damped_generatorTerm
    (p : CMParams) {eta c lag x CQ DQ : ℝ}
    {Q Qx R Z F : ℝ → ℝ}
    (hlag : 0 < lag)
    (hQ : ∀ y, |Q y| ≤ CQ)
    (hQx : ∀ y, |Qx y| ≤ DQ)
    (hQderiv : ∀ y, HasDerivAt Q (Qx y) y)
    (hQx_cont : Continuous Qx)
    (hsource : ∀ y, -p.χ * (Qx y - eta * Q y) + R y = Z y + F y)
    (hQ_heat : Integrable (fun y : ℝ =>
      weightedMovingHeatMarkovKernel eta c lag x y * Q y))
    (hQx_heat : Integrable (fun y : ℝ =>
      weightedMovingHeatMarkovKernel eta c lag x y * Qx y))
    (hR_heat : Integrable (fun y : ℝ =>
      weightedMovingHeatMarkovKernel eta c lag x y * R y)) :
    (-p.χ) * paper5WeightedDivergenceRestartTerm eta c lag Q x +
        paper5WeightedValueRestartTerm eta c lag R x =
      Real.exp (-lag) *
        weightedMovingHeatEta eta c lag (fun y => Z y + F y) x := by
  have hgrad :=
    weightedMovingHeatGradientEta_eq_weightedMovingHeatEta_deriv_of_bounded
      (eta := eta) (c := c) (x := x) hlag hQ hQx hQderiv hQx_cont
  have hlinear :
      -p.χ * (weightedMovingHeatEta eta c lag Qx x -
          eta * weightedMovingHeatEta eta c lag Q x) +
          weightedMovingHeatEta eta c lag R x =
        weightedMovingHeatEta eta c lag (fun y => Z y + F y) x := by
    unfold weightedMovingHeatEta
    rw [show (fun y : ℝ =>
          weightedMovingHeatMarkovKernel eta c lag x y * (Z y + F y)) =
        fun y => weightedMovingHeatMarkovKernel eta c lag x y *
          (-p.χ * (Qx y - eta * Q y) + R y) by
      funext y
      rw [hsource y]]
    have hQ_scaled : Integrable (fun y : ℝ =>
        weightedMovingHeatMarkovKernel eta c lag x y * (eta * Q y)) := by
      convert hQ_heat.const_mul eta using 1
      funext y
      ring
    have hdiff : Integrable (fun y : ℝ =>
        weightedMovingHeatMarkovKernel eta c lag x y *
          (Qx y - eta * Q y)) := by
      convert hQx_heat.sub hQ_scaled using 1
      funext y
      simp only [Pi.sub_apply]
      ring
    have hnegdiff : Integrable (fun y : ℝ =>
        (-p.χ) * (weightedMovingHeatMarkovKernel eta c lag x y *
          (Qx y - eta * Q y))) := hdiff.const_mul (-p.χ)
    have hetaIntegral :
        (∫ y : ℝ, weightedMovingHeatMarkovKernel eta c lag x y *
            (eta * Q y)) =
          eta * ∫ y : ℝ,
            weightedMovingHeatMarkovKernel eta c lag x y * Q y := by
      rw [show (fun y : ℝ =>
            weightedMovingHeatMarkovKernel eta c lag x y * (eta * Q y)) =
          fun y => eta *
            (weightedMovingHeatMarkovKernel eta c lag x y * Q y) by
        funext y
        ring,
        integral_const_mul]
    have hdiffIntegral :
        (∫ y : ℝ, weightedMovingHeatMarkovKernel eta c lag x y *
            (Qx y - eta * Q y)) =
          (∫ y : ℝ,
              weightedMovingHeatMarkovKernel eta c lag x y * Qx y) -
            eta * ∫ y : ℝ,
              weightedMovingHeatMarkovKernel eta c lag x y * Q y := by
      rw [show (fun y : ℝ =>
            weightedMovingHeatMarkovKernel eta c lag x y *
              (Qx y - eta * Q y)) =
          fun y =>
            weightedMovingHeatMarkovKernel eta c lag x y * Qx y -
              weightedMovingHeatMarkovKernel eta c lag x y * (eta * Q y) by
        funext y
        ring,
        integral_sub hQx_heat hQ_scaled, hetaIntegral]
    have htotalIntegral :
        (∫ y : ℝ, weightedMovingHeatMarkovKernel eta c lag x y *
            (-p.χ * (Qx y - eta * Q y) + R y)) =
          -p.χ *
              ((∫ y : ℝ,
                  weightedMovingHeatMarkovKernel eta c lag x y * Qx y) -
                eta * ∫ y : ℝ,
                  weightedMovingHeatMarkovKernel eta c lag x y * Q y) +
            ∫ y : ℝ,
              weightedMovingHeatMarkovKernel eta c lag x y * R y := by
      rw [show (fun y : ℝ =>
            weightedMovingHeatMarkovKernel eta c lag x y *
              (-p.χ * (Qx y - eta * Q y) + R y)) =
          fun y => (-p.χ) *
              (weightedMovingHeatMarkovKernel eta c lag x y *
                (Qx y - eta * Q y)) +
            weightedMovingHeatMarkovKernel eta c lag x y * R y by
        funext y
        ring,
        integral_add hnegdiff hR_heat, integral_const_mul, hdiffIntegral]
    rw [htotalIntegral]
    ring
  unfold paper5WeightedDivergenceRestartTerm paper5WeightedValueRestartTerm
  rw [hgrad]
  rw [← hlinear]
  ring

/-- Algebraic source seam behind the damped restart.  The shifted reaction
contains exactly one copy of the population difference; the remaining
reaction and differentiated-flux terms are the physical generator forcing.
-/
theorem paper5Weighted_conjugated_shiftedSource_eq_population_add_forcing
    (p : CMParams) {eta x : ℝ}
    {u U Phi Psi : ℝ → ℝ}
    (hPhi : DifferentiableAt ℝ Phi x)
    (hPsi : DifferentiableAt ℝ Psi x) :
    -p.χ *
          (deriv (fun y => Real.exp (eta * y) * (Phi y - Psi y)) x -
            eta * (Real.exp (eta * x) * (Phi x - Psi x))) +
        Real.exp (eta * x) *
          (wholeLineCauchyShiftedReaction p u x -
            wholeLineCauchyShiftedReaction p U x) =
      Real.exp (eta * x) * (u x - U x) +
        Real.exp (eta * x) *
          (-p.χ * (deriv Phi x - deriv Psi x) +
            (reactionFun p.α (u x) - reactionFun p.α (U x))) := by
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (eta * y))
      (eta * Real.exp (eta * x)) x := by
    convert (Real.hasDerivAt_exp (eta * x)).comp x
      ((hasDerivAt_const x eta).mul (hasDerivAt_id x)) using 1
    all_goals ring
  have hdiff : HasDerivAt (fun y => Phi y - Psi y)
      (deriv Phi x - deriv Psi x) x :=
    hPhi.hasDerivAt.sub hPsi.hasDerivAt
  have hprod : HasDerivAt
      (fun y => Real.exp (eta * y) * (Phi y - Psi y))
      (eta * Real.exp (eta * x) * (Phi x - Psi x) +
        Real.exp (eta * x) * (deriv Phi x - deriv Psi x)) x := by
    simpa only [Pi.mul_apply] using hexp.mul hdiff
  rw [hprod.deriv]
  unfold wholeLineCauchyShiftedReaction wholeLineLogisticSource
  ring

/-- Physical co-moving specialization of the algebraic source seam. -/
theorem paper5Weighted_physicalShiftedSource_eq_population_add_generatorForcing
    (p : CMParams) {eta c t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hPhi : DifferentiableAt ℝ
      (fun y => (coMovingPath c u t y) ^ p.m *
        deriv (coMovingPath c v t) y) x)
    (hPsi : DifferentiableAt ℝ
      (fun y => (U y) ^ p.m * deriv V y) x) :
    -p.χ *
          (deriv (fun y => Real.exp (eta * y) *
              ((coMovingPath c u t y) ^ p.m *
                  deriv (coMovingPath c v t) y -
                (U y) ^ p.m * deriv V y)) x -
            eta * (Real.exp (eta * x) *
              ((coMovingPath c u t x) ^ p.m *
                  deriv (coMovingPath c v t) x -
                (U x) ^ p.m * deriv V x))) +
        Real.exp (eta * x) *
          (wholeLineCauchyShiftedReaction p (coMovingPath c u t) x -
            wholeLineCauchyShiftedReaction p U x) =
      paper5WeightedPopulation eta (coMovingPath c u) U t x +
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V t x := by
  simpa only [paper5WeightedPopulation, paper5WeightedGeneratorForcing]
    using paper5Weighted_conjugated_shiftedSource_eq_population_add_forcing
      p (eta := eta) (x := x) hPhi hPsi

/-- Canonical fixed-point source specialization.  This theorem performs the
only algebra needed between the split restart sources and the raw physical
generator forcing; the strip hypothesis removes the Picard clamps. -/
theorem paper5Weighted_canonicalSplitSource_eq_population_add_rawForcing
    (p : CMParams) {M T eta c s x : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (Traj : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (Traj z).1 y ∈ Set.Icc (0 : ℝ) M)
    (Uw Vw : ℝ → ℝ)
    (hPhi : DifferentiableAt ℝ
      (wholeLineCauchyCoMovingFluxSource p c hM hT Traj s) x)
    (hPsi : DifferentiableAt ℝ
      (wholeLineTravelingWaveFlux p Uw Vw) x) :
    -p.χ *
          (deriv
              (paper5WeightedFluxDifferenceSource p eta c hM hT
                Traj Uw Vw s) x -
            eta * paper5WeightedFluxDifferenceSource p eta c hM hT
              Traj Uw Vw s x) +
        paper5WeightedReactionDifferenceSource p eta c hM hT
          Traj Uw s x =
      Real.exp (eta * x) *
          ((wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
            Uw x) +
        Real.exp (eta * x) *
          paper5CanonicalGeneratorForcingRaw p c hM hT
            Traj Uw Vw s x := by
  let us : ℝ → ℝ := fun y =>
    (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s)
  let Phi : ℝ → ℝ :=
    wholeLineCauchyCoMovingFluxSource p c hM hT Traj s
  let Psi : ℝ → ℝ := wholeLineTravelingWaveFlux p Uw Vw
  have hcore :=
    paper5Weighted_conjugated_shiftedSource_eq_population_add_forcing
      p (eta := eta) (x := x) (u := us) (U := Uw)
        (Phi := Phi) (Psi := Psi) hPhi hPsi
  have hreact :
      wholeLineCauchyCoMovingReactionSource p c hM hT Traj s =
        wholeLineCauchyShiftedReaction p us := by
    simpa only [us] using
      wholeLineCauchyCoMovingReactionSource_eq_genuineReaction_of_strip
        p c hM hT Traj hstrip s
  have hPhiDeriv :
      deriv Phi x =
        deriv (wholeLineCauchyFluxSourceTrajectory p hM hT Traj s).1
          (x + c * s) := by
    dsimp only [Phi]
    unfold wholeLineCauchyCoMovingFluxSource
    rw [deriv_comp_add_const]
  have hQfun :
      paper5WeightedFluxDifferenceSource p eta c hM hT
          Traj Uw Vw s =
        fun y => Real.exp (eta * y) * (Phi y - Psi y) := by
    funext y
    unfold paper5WeightedFluxDifferenceSource
      paper5WeightedCanonicalFluxSource
      paper5WeightedTravelingWaveFluxSource
    dsimp only [Phi, Psi]
    ring
  have hRfun :
      paper5WeightedReactionDifferenceSource p eta c hM hT
          Traj Uw s =
        fun y => Real.exp (eta * y) *
          (wholeLineCauchyShiftedReaction p us y -
            wholeLineCauchyShiftedReaction p Uw y) := by
    funext y
    unfold paper5WeightedReactionDifferenceSource
      paper5WeightedCanonicalReactionSource
      paper5WeightedTravelingWaveReactionSource
    rw [hreact]
    ring
  rw [hQfun, hRfun]
  rw [hPhiDeriv] at hcore
  simpa only [paper5CanonicalGeneratorForcingRaw,
    wholeLineTravelingWaveFlux, us, Phi, Psi] using hcore

/-- The preceding raw identity with its forcing converted to the canonical
expanded `L²` trajectory's scalar representative. -/
theorem paper5Weighted_canonicalSplitSource_eq_population_add_generatorForcing
    (p : CMParams) {M T eta c s x : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (Traj : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (Traj z).1 y ∈ Set.Icc (0 : ℝ) M)
    (Uw Vw : ℝ → ℝ)
    (hPhi : DifferentiableAt ℝ
      (wholeLineCauchyCoMovingFluxSource p c hM hT Traj s) x)
    (hPsi : DifferentiableAt ℝ
      (wholeLineTravelingWaveFlux p Uw Vw) x) :
    (let u : ℝ → ℝ → ℝ := fun t y =>
        (wholeLineBUCTrajectoryExtend hT Traj t).1 y;
     let v : ℝ → ℝ → ℝ := fun t => frozenElliptic p (u t);
     -p.χ *
          (deriv
              (paper5WeightedFluxDifferenceSource p eta c hM hT
                Traj Uw Vw s) x -
            eta * paper5WeightedFluxDifferenceSource p eta c hM hT
              Traj Uw Vw s x) +
        paper5WeightedReactionDifferenceSource p eta c hM hT
          Traj Uw s x =
      paper5WeightedPopulation eta (coMovingPath c u) Uw s x +
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) Uw Vw
          (t := s) (x := x)) := by
  dsimp only
  have hraw := paper5Weighted_canonicalSplitSource_eq_population_add_rawForcing
    p hM hT Traj hstrip Uw Vw hPhi hPsi (eta := eta) (c := c)
      (s := s) (x := x)
  have hforcing :=
    paper5CanonicalGeneratorForcingRaw_exp_eq_weighted
      (eta := eta) (c := c) (s := s)
      p hM hT Traj Uw Vw (hstrip (Set.projIcc 0 T hT s)) x
  rw [hraw]
  rw [hforcing]
  rfl

/-- Every positive-lag integrand in the canonical split restart is the
damped moving-heat orbit of the actual weighted population plus the
physical generator forcing.  The assumptions are source-side spatial
regularity and heat integrability; in particular, no weighted population
derivative is used. -/
theorem paper5Weighted_canonicalSplitRestartTerm_eq_damped_generatorTerm
    (p : CMParams) {M T eta c s lag x CQ DQ : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (Traj : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (Traj z).1 y ∈ Set.Icc (0 : ℝ) M)
    (Uw Vw : ℝ → ℝ)
    (hlag : 0 < lag)
    (hQ : ∀ y,
      |paper5WeightedFluxDifferenceSource p eta c hM hT
          Traj Uw Vw s y| ≤ CQ)
    (hQx : ∀ y,
      |deriv (paper5WeightedFluxDifferenceSource p eta c hM hT
          Traj Uw Vw s) y| ≤ DQ)
    (hQderiv : ∀ y, HasDerivAt
      (paper5WeightedFluxDifferenceSource p eta c hM hT
        Traj Uw Vw s)
      (deriv (paper5WeightedFluxDifferenceSource p eta c hM hT
        Traj Uw Vw s) y) y)
    (hQx_cont : Continuous
      (deriv (paper5WeightedFluxDifferenceSource p eta c hM hT
        Traj Uw Vw s)))
    (hPhi : ∀ y, DifferentiableAt ℝ
      (wholeLineCauchyCoMovingFluxSource p c hM hT Traj s) y)
    (hPsi : ∀ y, DifferentiableAt ℝ
      (wholeLineTravelingWaveFlux p Uw Vw) y)
    (hQ_heat : Integrable (fun y : ℝ =>
      weightedMovingHeatMarkovKernel eta c lag x y *
        paper5WeightedFluxDifferenceSource p eta c hM hT
          Traj Uw Vw s y))
    (hQx_heat : Integrable (fun y : ℝ =>
      weightedMovingHeatMarkovKernel eta c lag x y *
        deriv (paper5WeightedFluxDifferenceSource p eta c hM hT
          Traj Uw Vw s) y))
    (hR_heat : Integrable (fun y : ℝ =>
      weightedMovingHeatMarkovKernel eta c lag x y *
        paper5WeightedReactionDifferenceSource p eta c hM hT
          Traj Uw s y)) :
    (let u : ℝ → ℝ → ℝ := fun t y =>
        (wholeLineBUCTrajectoryExtend hT Traj t).1 y;
     let v : ℝ → ℝ → ℝ := fun t => frozenElliptic p (u t);
     (-p.χ) * paper5WeightedDivergenceRestartTerm eta c lag
          (paper5WeightedFluxDifferenceSource p eta c hM hT
            Traj Uw Vw s) x +
        paper5WeightedValueRestartTerm eta c lag
          (paper5WeightedReactionDifferenceSource p eta c hM hT
            Traj Uw s) x =
      Real.exp (-lag) * weightedMovingHeatEta eta c lag
        (fun y =>
          paper5WeightedPopulation eta (coMovingPath c u) Uw s y +
            paper5WeightedGeneratorForcing p eta
              (coMovingPath c u) (coMovingPath c v) Uw Vw
              (t := s) (x := y)) x) := by
  dsimp only
  apply paper5Weighted_splitRestartTerm_eq_damped_generatorTerm
    p hlag hQ hQx hQderiv hQx_cont
  · intro y
    exact paper5Weighted_canonicalSplitSource_eq_population_add_generatorForcing
      p hM hT Traj hstrip Uw Vw (hPhi y) (hPsi y)
        (eta := eta) (c := c) (s := s) (x := y)
  · exact hQ_heat
  · exact hQx_heat
  · exact hR_heat

/-- A pointwise damped restart lifts to `WholeLineRealL2`.  This is the
damped analogue of
`weightedMovingHeatL2Semigroup_mild_restart_eq_of_pointwise`; it keeps the
same local space-time Fubini interface and does not ask for a generator
realization. -/
theorem weightedMovingHeatL2Semigroup_damped_mild_restart_eq_of_pointwise
    {eta c a r : ℝ} (har : a < r)
    {z g : ℝ → ℝ → ℝ}
    {Z G : ℝ → WholeLineRealL2}
    (hZa : (((Z a : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] z a))
    (hZr : (((Z r : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] z r))
    (hGrep : ∀ q ∈ Set.Ioc a r,
      (((G q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] g q))
    (hDint : IntervalIntegrable
      (fun q => Real.exp (-(r - q)) •
        weightedMovingHeatL2Semigroup eta c (r - q) (G q))
      volume a r)
    (hlocal : ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun w : ℝ × ℝ => A.indicator
          (fun x => Real.exp (-(r - w.1)) *
            weightedMovingHeatEta eta c (r - w.1) (g w.1) x) w.2)
        ((volume.restrict (Set.Ioc a r)).prod volume))
    (hpoint : ∀ᵐ x ∂volume,
      z r x = Real.exp (-(r - a)) *
          weightedMovingHeatEta eta c (r - a) (z a) x +
        ∫ q in a..r, Real.exp (-(r - q)) *
          weightedMovingHeatEta eta c (r - q) (g q) x) :
    Z r = Real.exp (-(r - a)) •
        weightedMovingHeatL2Semigroup eta c (r - a) (Z a) +
      ∫ q in a..r, Real.exp (-(r - q)) •
        weightedMovingHeatL2Semigroup eta c (r - q) (G q) := by
  have hlag : 0 < r - a := sub_pos.mpr har
  have hheatHom :
      (((weightedMovingHeatL2Semigroup eta c (r - a) (Z a) :
          WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        weightedMovingHeatEta eta c (r - a) (z a)) := by
    rw [weightedMovingHeatL2Semigroup_of_pos hlag]
    exact (weightedMovingHeatL2Fun_coe_ae hlag (Z a)).trans
      (Eventually.of_forall fun x =>
        weightedMovingHeatEta_congr_ae hZa x)
  have hhom :
      (((Real.exp (-(r - a)) •
          weightedMovingHeatL2Semigroup eta c (r - a) (Z a) :
            WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        fun x => Real.exp (-(r - a)) *
          weightedMovingHeatEta eta c (r - a) (z a) x) := by
    filter_upwards [Lp.coeFn_smul (Real.exp (-(r - a)))
        (weightedMovingHeatL2Semigroup eta c (r - a) (Z a)),
      hheatHom] with x hxsmul hxheat
    rw [hxsmul]
    simp only [Pi.smul_apply, smul_eq_mul, hxheat]
  let D : ℝ → WholeLineRealL2 := fun q =>
    Real.exp (-(r - q)) •
      weightedMovingHeatL2Semigroup eta c (r - q) (G q)
  let d : ℝ → ℝ → ℝ := fun q x =>
    Real.exp (-(r - q)) *
      weightedMovingHeatEta eta c (r - q) (g q) x
  have hDrep : ∀ᵐ q ∂(volume.restrict (Set.Ioc a r)),
      (((D q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] d q) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (Measure.ae_ne volume r).filter_mono ae_restrict_le]
      with q hq hqr
    have hqpos : 0 < r - q := sub_pos.mpr (lt_of_le_of_ne hq.2 hqr)
    have hheat :
        (((weightedMovingHeatL2Semigroup eta c (r - q) (G q) :
            WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
          weightedMovingHeatEta eta c (r - q) (g q)) := by
      rw [weightedMovingHeatL2Semigroup_of_pos hqpos]
      exact (weightedMovingHeatL2Fun_coe_ae hqpos (G q)).trans
        (Eventually.of_forall fun x =>
          weightedMovingHeatEta_congr_ae (hGrep q hq) x)
    filter_upwards [Lp.coeFn_smul (Real.exp (-(r - q)))
        (weightedMovingHeatL2Semigroup eta c (r - q) (G q)),
      hheat] with x hxsmul hxheat
    dsimp only [D, d]
    rw [hxsmul]
    simp only [Pi.smul_apply, smul_eq_mul, hxheat]
  have hduhamel :
      (((∫ q in a..r, D q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        fun x => ∫ q in a..r, d q x) := by
    apply wholeLineRealL2_intervalIntegral_coe_ae_of_local_prod_integrable
      har.le
    · simpa only [D] using hDint
    · exact hDrep
    · intro A hA hAfin
      simpa only [d] using hlocal A hA hAfin
  apply Lp.ext
  filter_upwards [hZr,
    Lp.coeFn_add
      (Real.exp (-(r - a)) •
        weightedMovingHeatL2Semigroup eta c (r - a) (Z a))
      (∫ q in a..r, D q),
    hhom, hduhamel, hpoint] with x hzr hadd hhomx hduhamelx hpointx
  rw [hzr, hadd]
  simp only [Pi.add_apply]
  rw [hhomx, hduhamelx]
  simpa only [D, d] using hpointx

/-- Canonical-total specialization of the damped pointwise lift. -/
theorem weightedMovingHeatL2Semigroup_damped_mild_restart_eq_of_pointwise_total
    {eta c a r : ℝ} (har : a < r)
    {z g : ℝ → ℝ → ℝ}
    (hz_meas : ∀ q ∈ Set.Icc a r,
      AEStronglyMeasurable (z q) volume)
    (hz_sq : ∀ q ∈ Set.Icc a r,
      Integrable (fun x : ℝ => z q x ^ 2) volume)
    (hg_meas : ∀ q ∈ Set.Ioc a r,
      AEStronglyMeasurable (g q) volume)
    (hg_sq : ∀ q ∈ Set.Ioc a r,
      Integrable (fun x : ℝ => g q x ^ 2) volume)
    (hDint : IntervalIntegrable
      (fun q => Real.exp (-(r - q)) •
        weightedMovingHeatL2Semigroup eta c (r - q)
          (wholeLineRealL2Total (g q))) volume a r)
    (hlocal : ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun w : ℝ × ℝ => A.indicator
          (fun x => Real.exp (-(r - w.1)) *
            weightedMovingHeatEta eta c (r - w.1) (g w.1) x) w.2)
        ((volume.restrict (Set.Ioc a r)).prod volume))
    (hpoint : ∀ᵐ x ∂volume,
      z r x = Real.exp (-(r - a)) *
          weightedMovingHeatEta eta c (r - a) (z a) x +
        ∫ q in a..r, Real.exp (-(r - q)) *
          weightedMovingHeatEta eta c (r - q) (g q) x) :
    wholeLineRealL2Total (z r) =
      Real.exp (-(r - a)) •
        weightedMovingHeatL2Semigroup eta c (r - a)
          (wholeLineRealL2Total (z a)) +
      ∫ q in a..r, Real.exp (-(r - q)) •
        weightedMovingHeatL2Semigroup eta c (r - q)
          (wholeLineRealL2Total (g q)) := by
  apply weightedMovingHeatL2Semigroup_damped_mild_restart_eq_of_pointwise
    har
  · exact wholeLineRealL2Total_coe_ae _
      (hz_meas a ⟨le_rfl, har.le⟩)
      (hz_sq a ⟨le_rfl, har.le⟩)
  · exact wholeLineRealL2Total_coe_ae _
      (hz_meas r ⟨har.le, le_rfl⟩)
      (hz_sq r ⟨har.le, le_rfl⟩)
  · intro q hq
    exact wholeLineRealL2Total_coe_ae _ (hg_meas q hq) (hg_sq q hq)
  · exact hDint
  · exact hlocal
  · exact hpoint

/-- Convert the two source legs in the canonical split restart into the
single `Z + F` history.  The endpoint has zero time measure, so the
positive-lag integrand identity is only required on `Ioo a r`. -/
theorem paper5Weighted_damped_restart_pointwise_of_split
    (p : CMParams) {eta c a r : ℝ} (har : a < r)
    {z qsrc rsrc f : ℝ → ℝ → ℝ}
    (hsplit : ∀ x,
      z r x = Real.exp (-(r - a)) *
          weightedMovingHeatEta eta c (r - a) (z a) x +
        (-p.χ) * (∫ q in a..r,
          paper5WeightedDivergenceRestartTerm eta c (r - q)
            (qsrc q) x) +
        ∫ q in a..r,
          paper5WeightedValueRestartTerm eta c (r - q) (rsrc q) x)
    (hdiv_int : ∀ x, IntervalIntegrable
      (fun q => paper5WeightedDivergenceRestartTerm eta c (r - q)
        (qsrc q) x) volume a r)
    (hval_int : ∀ x, IntervalIntegrable
      (fun q => paper5WeightedValueRestartTerm eta c (r - q)
        (rsrc q) x) volume a r)
    (hterm : ∀ q ∈ Set.Ioo a r, ∀ x,
      (-p.χ) * paper5WeightedDivergenceRestartTerm eta c (r - q)
            (qsrc q) x +
          paper5WeightedValueRestartTerm eta c (r - q) (rsrc q) x =
        Real.exp (-(r - q)) *
          weightedMovingHeatEta eta c (r - q)
            (fun y => z q y + f q y) x) :
    ∀ x,
      z r x = Real.exp (-(r - a)) *
          weightedMovingHeatEta eta c (r - a) (z a) x +
        ∫ q in a..r, Real.exp (-(r - q)) *
          weightedMovingHeatEta eta c (r - q)
            (fun y => z q y + f q y) x := by
  intro x
  have hsource_int : IntervalIntegrable
      (fun q => (-p.χ) *
          paper5WeightedDivergenceRestartTerm eta c (r - q) (qsrc q) x +
        paper5WeightedValueRestartTerm eta c (r - q) (rsrc q) x)
      volume a r :=
    (hdiv_int x).const_mul (-p.χ) |>.add (hval_int x)
  have hsource_eq :
      (∫ q in a..r,
        ((-p.χ) *
            paper5WeightedDivergenceRestartTerm eta c (r - q) (qsrc q) x +
          paper5WeightedValueRestartTerm eta c (r - q) (rsrc q) x)) =
        ∫ q in a..r, Real.exp (-(r - q)) *
          weightedMovingHeatEta eta c (r - q)
            (fun y => z q y + f q y) x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume r] with q hqr hq
    rw [Set.uIoc_of_le har.le] at hq
    exact hterm q ⟨hq.1, lt_of_le_of_ne hq.2 hqr⟩ x
  rw [hsplit x]
  calc
    (Real.exp (-(r - a)) *
          weightedMovingHeatEta eta c (r - a) (z a) x +
        (-p.χ) * (∫ q in a..r,
          paper5WeightedDivergenceRestartTerm eta c (r - q)
            (qsrc q) x)) +
        ∫ q in a..r,
          paper5WeightedValueRestartTerm eta c (r - q) (rsrc q) x =
      Real.exp (-(r - a)) *
          weightedMovingHeatEta eta c (r - a) (z a) x +
        ((∫ q in a..r, (-p.χ) *
            paper5WeightedDivergenceRestartTerm eta c (r - q)
              (qsrc q) x) +
          ∫ q in a..r,
            paper5WeightedValueRestartTerm eta c (r - q) (rsrc q) x) := by
        rw [intervalIntegral.integral_const_mul]
        ring
    _ = Real.exp (-(r - a)) *
          weightedMovingHeatEta eta c (r - a) (z a) x +
        ∫ q in a..r,
          ((-p.χ) * paper5WeightedDivergenceRestartTerm eta c (r - q)
              (qsrc q) x +
            paper5WeightedValueRestartTerm eta c (r - q) (rsrc q) x) := by
      rw [intervalIntegral.integral_add
        ((hdiv_int x).const_mul (-p.χ)) (hval_int x)]
    _ = _ := by rw [hsource_eq]

/-- Canonical specialization of the split-to-damped pointwise restart.
All source identities are discharged internally from the fixed-point strip;
the remaining hypotheses are precisely the scalar history integrability and
source-side spatial bounds needed to move the flux derivative through the
Gaussian. -/
theorem paper5Weighted_canonicalPopulation_damped_restart_pointwise_of_split
    (p : CMParams) {M T eta c a r : ℝ} {CQ DQ : ℝ → ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (Traj : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (Traj z).1 y ∈ Set.Icc (0 : ℝ) M)
    (Uw Vw : ℝ → ℝ) (har : a < r)
    (hsplit : ∀ x,
      let u : ℝ → ℝ → ℝ := fun t y =>
        (wholeLineBUCTrajectoryExtend hT Traj t).1 y
      paper5WeightedPopulation eta (coMovingPath c u) Uw r x =
        Real.exp (-(r - a)) *
          weightedMovingHeatEta eta c (r - a)
            (paper5WeightedPopulation eta (coMovingPath c u) Uw a) x +
        (-p.χ) * (∫ q in a..r,
          paper5WeightedDivergenceRestartTerm eta c (r - q)
            (paper5WeightedFluxDifferenceSource p eta c hM hT
              Traj Uw Vw q) x) +
        ∫ q in a..r,
          paper5WeightedValueRestartTerm eta c (r - q)
            (paper5WeightedReactionDifferenceSource p eta c hM hT
              Traj Uw q) x)
    (hdiv_int : ∀ x, IntervalIntegrable
      (fun q => paper5WeightedDivergenceRestartTerm eta c (r - q)
        (paper5WeightedFluxDifferenceSource p eta c hM hT
          Traj Uw Vw q) x) volume a r)
    (hval_int : ∀ x, IntervalIntegrable
      (fun q => paper5WeightedValueRestartTerm eta c (r - q)
        (paper5WeightedReactionDifferenceSource p eta c hM hT
          Traj Uw q) x) volume a r)
    (hQ : ∀ q ∈ Set.Ioo a r, ∀ y,
      |paper5WeightedFluxDifferenceSource p eta c hM hT
          Traj Uw Vw q y| ≤ CQ q)
    (hQx : ∀ q ∈ Set.Ioo a r, ∀ y,
      |deriv (paper5WeightedFluxDifferenceSource p eta c hM hT
          Traj Uw Vw q) y| ≤ DQ q)
    (hQderiv : ∀ q ∈ Set.Ioo a r, ∀ y, HasDerivAt
      (paper5WeightedFluxDifferenceSource p eta c hM hT
        Traj Uw Vw q)
      (deriv (paper5WeightedFluxDifferenceSource p eta c hM hT
        Traj Uw Vw q) y) y)
    (hQx_cont : ∀ q ∈ Set.Ioo a r, Continuous
      (deriv (paper5WeightedFluxDifferenceSource p eta c hM hT
        Traj Uw Vw q)))
    (hPhi : ∀ q ∈ Set.Ioo a r, ∀ y, DifferentiableAt ℝ
      (wholeLineCauchyCoMovingFluxSource p c hM hT Traj q) y)
    (hPsi : ∀ y, DifferentiableAt ℝ
      (wholeLineTravelingWaveFlux p Uw Vw) y)
    (hQ_heat : ∀ q ∈ Set.Ioo a r, ∀ x, Integrable (fun y : ℝ =>
      weightedMovingHeatMarkovKernel eta c (r - q) x y *
        paper5WeightedFluxDifferenceSource p eta c hM hT
          Traj Uw Vw q y))
    (hQx_heat : ∀ q ∈ Set.Ioo a r, ∀ x, Integrable (fun y : ℝ =>
      weightedMovingHeatMarkovKernel eta c (r - q) x y *
        deriv (paper5WeightedFluxDifferenceSource p eta c hM hT
          Traj Uw Vw q) y))
    (hR_heat : ∀ q ∈ Set.Ioo a r, ∀ x, Integrable (fun y : ℝ =>
      weightedMovingHeatMarkovKernel eta c (r - q) x y *
        paper5WeightedReactionDifferenceSource p eta c hM hT
          Traj Uw q y)) :
    (let u : ℝ → ℝ → ℝ := fun t y =>
        (wholeLineBUCTrajectoryExtend hT Traj t).1 y;
     let v : ℝ → ℝ → ℝ := fun t => frozenElliptic p (u t);
     ∀ x,
      paper5WeightedPopulation eta (coMovingPath c u) Uw r x =
        Real.exp (-(r - a)) *
          weightedMovingHeatEta eta c (r - a)
            (paper5WeightedPopulation eta (coMovingPath c u) Uw a) x +
        ∫ q in a..r, Real.exp (-(r - q)) *
          weightedMovingHeatEta eta c (r - q)
            (fun y =>
              paper5WeightedPopulation eta (coMovingPath c u) Uw q y +
                paper5WeightedGeneratorForcing p eta
                  (coMovingPath c u) (coMovingPath c v) Uw Vw
                  (t := q) (x := y)) x) := by
  dsimp only at hsplit ⊢
  apply paper5Weighted_damped_restart_pointwise_of_split p har hsplit
    hdiv_int hval_int
  intro q hq x
  exact paper5Weighted_canonicalSplitRestartTerm_eq_damped_generatorTerm
    p hM hT Traj hstrip Uw Vw (sub_pos.mpr hq.2)
      (hQ q hq) (hQx q hq) (hQderiv q hq) (hQx_cont q hq)
      (hPhi q hq) hPsi (hQ_heat q hq x) (hQx_heat q hq x)
      (hR_heat q hq x)

/-- The actual scalar weighted-population restart, once written in damped
`Z + F` form, has exactly the Hilbert-space shape required by
`weightedMovingHeat_fullGenerator_restart_of_damped_*`.  The initial datum
is the actual value slice `W(a)`, not a derivative slice. -/
theorem paper5WeightedPopulation_damped_restart_L2_of_pointwise
    {eta c a r : ℝ} (har : a < r)
    {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {f : ℝ → ℝ → ℝ} {F : ℝ → WholeLineRealL2}
    (hW_meas : ∀ q ∈ Set.Icc a r,
      AEStronglyMeasurable (paper5WeightedPopulation eta u U q) volume)
    (hW_sq : ∀ q ∈ Set.Icc a r, Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta u U q x ^ 2) volume)
    (hFrep : ∀ q ∈ Set.Ioc a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q))
    (hDint : IntervalIntegrable
      (fun q => Real.exp (-(r - q)) •
        weightedMovingHeatL2Semigroup eta c (r - q)
          (wholeLineRealL2Total
              (paper5WeightedPopulation eta u U q) + F q))
      volume a r)
    (hlocal : ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun w : ℝ × ℝ => A.indicator
          (fun x => Real.exp (-(r - w.1)) *
            weightedMovingHeatEta eta c (r - w.1)
              (fun y => paper5WeightedPopulation eta u U w.1 y +
                f w.1 y) x) w.2)
        ((volume.restrict (Set.Ioc a r)).prod volume))
    (hpoint : ∀ᵐ x ∂volume,
      paper5WeightedPopulation eta u U r x =
        Real.exp (-(r - a)) *
          weightedMovingHeatEta eta c (r - a)
            (paper5WeightedPopulation eta u U a) x +
        ∫ q in a..r, Real.exp (-(r - q)) *
          weightedMovingHeatEta eta c (r - q)
            (fun y => paper5WeightedPopulation eta u U q y + f q y) x) :
    wholeLineRealL2Total (paper5WeightedPopulation eta u U r) =
      Real.exp (-(r - a)) •
        weightedMovingHeatL2Semigroup eta c (r - a)
          (wholeLineRealL2Total (paper5WeightedPopulation eta u U a)) +
      ∫ q in a..r, Real.exp (-(r - q)) •
        weightedMovingHeatL2Semigroup eta c (r - q)
          (wholeLineRealL2Total (paper5WeightedPopulation eta u U q) +
            F q) := by
  apply weightedMovingHeatL2Semigroup_damped_mild_restart_eq_of_pointwise
    (z := paper5WeightedPopulation eta u U)
    (g := fun q y => paper5WeightedPopulation eta u U q y + f q y)
    (Z := fun q => wholeLineRealL2Total
      (paper5WeightedPopulation eta u U q))
    (G := fun q => wholeLineRealL2Total
      (paper5WeightedPopulation eta u U q) + F q) har
  · exact wholeLineRealL2Total_coe_ae _
      (hW_meas a ⟨le_rfl, har.le⟩) (hW_sq a ⟨le_rfl, har.le⟩)
  · exact wholeLineRealL2Total_coe_ae _
      (hW_meas r ⟨har.le, le_rfl⟩) (hW_sq r ⟨har.le, le_rfl⟩)
  · intro q hq
    filter_upwards [Lp.coeFn_add
        (wholeLineRealL2Total (paper5WeightedPopulation eta u U q)) (F q),
      wholeLineRealL2Total_coe_ae _
        (hW_meas q ⟨hq.1.le, hq.2⟩) (hW_sq q ⟨hq.1.le, hq.2⟩),
      hFrep q hq] with x hadd hW hF
    rw [hadd]
    simp only [Pi.add_apply, hW, hF]
  · exact hDint
  · exact hlocal
  · exact hpoint

/-- Damping removal for the actual weighted population on a short positive
window.  Scalar pointwise restarts are first lifted to `WholeLineRealL2`;
the ambient uniform-forcing theorem then identifies the state itself with
the undamped full-generator candidate.  Thus the datum is the value slice
`W(a)`, and the conclusion is an equality for the actual state rather than
merely a damped auxiliary equation. -/
theorem paper5WeightedPopulation_eq_fullGeneratorCandidate_of_damped_pointwise_on_window
    {eta c L R a r K : ℝ}
    {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {f : ℝ → ℝ → ℝ} {F : ℝ → WholeLineRealL2}
    (hLa : L < a) (har : a ≤ r) (hrR : r < R)
    (hK : 0 ≤ K)
    (hF : ∀ q ∈ Set.Icc L R, ‖F q‖ ≤ K)
    (hhist_meas : ∀ t : ℝ, AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      (volume.restrict (Set.uIoc L R)))
    (hWcont : ContinuousOn
      (fun q => wholeLineRealL2Total
        (paper5WeightedPopulation eta u U q)) (Set.Icc a r))
    (hW_meas : ∀ q ∈ Set.Icc a r,
      AEStronglyMeasurable (paper5WeightedPopulation eta u U q) volume)
    (hW_sq : ∀ q ∈ Set.Icc a r, Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta u U q x ^ 2) volume)
    (hFrep : ∀ q ∈ Set.Ioc a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q))
    (hDint : ∀ t ∈ Set.Icc a r, IntervalIntegrable
      (fun q => Real.exp (-(t - q)) •
        weightedMovingHeatL2Semigroup eta c (t - q)
          (wholeLineRealL2Total
              (paper5WeightedPopulation eta u U q) + F q))
      volume a t)
    (hlocal : ∀ t ∈ Set.Ioc a r, ∀ A : Set ℝ, MeasurableSet A →
      (volume : Measure ℝ) A < ⊤ →
      Integrable
        (fun w : ℝ × ℝ => A.indicator
          (fun x => Real.exp (-(t - w.1)) *
            weightedMovingHeatEta eta c (t - w.1)
              (fun y => paper5WeightedPopulation eta u U w.1 y +
                f w.1 y) x) w.2)
        ((volume.restrict (Set.Ioc a t)).prod volume))
    (hpoint : ∀ t ∈ Set.Ioc a r, ∀ᵐ x ∂volume,
      paper5WeightedPopulation eta u U t x =
        Real.exp (-(t - a)) *
          weightedMovingHeatEta eta c (t - a)
            (paper5WeightedPopulation eta u U a) x +
        ∫ q in a..t, Real.exp (-(t - q)) *
          weightedMovingHeatEta eta c (t - q)
            (fun y => paper5WeightedPopulation eta u U q y + f q y) x)
    (hshort :
      Real.exp (|eta ^ 2 - c * eta| * (r - a)) * (r - a) < 1) :
    ∀ t ∈ Set.Icc a r,
      wholeLineRealL2Total (paper5WeightedPopulation eta u U t) =
        weightedMovingHeatFullGeneratorCandidate eta c a
          (wholeLineRealL2Total (paper5WeightedPopulation eta u U a)) F t := by
  let Z : ℝ → WholeLineRealL2 := fun q =>
    wholeLineRealL2Total (paper5WeightedPopulation eta u U q)
  have hZdamped : ∀ t ∈ Set.Icc a r,
      Z t = Real.exp (-(t - a)) •
          weightedMovingHeatL2Semigroup eta c (t - a) (Z a) +
        ∫ q in a..t, Real.exp (-(t - q)) •
          weightedMovingHeatL2Semigroup eta c (t - q) (Z q + F q) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | hat
    · simp only [Z, sub_self, neg_zero, Real.exp_zero, one_smul,
        weightedMovingHeatL2Semigroup_zero,
        ContinuousLinearMap.one_apply,
        intervalIntegral.integral_same, add_zero]
    · exact paper5WeightedPopulation_damped_restart_L2_of_pointwise
        (eta := eta) (c := c) (u := u) (U := U) (f := f) (F := F)
        hat
        (fun q hq => hW_meas q ⟨hq.1, hq.2.trans ht.2⟩)
        (fun q hq => hW_sq q ⟨hq.1, hq.2.trans ht.2⟩)
        (fun q hq => hFrep q ⟨hq.1, hq.2.trans ht.2⟩)
        (hDint t ht) (hlocal t ⟨hat, ht.2⟩)
        (hpoint t ⟨hat, ht.2⟩)
  have hstate :=
    weightedMovingHeat_fullGenerator_restart_of_damped_uniform_forcing_ambient_of_short
      (eta := eta) (c := c) (Z := Z) (F := F)
      hLa har hrR hK hF hhist_meas hWcont hDint hZdamped hshort
  intro t ht
  simpa only [Z, weightedMovingHeatFullGeneratorCandidate] using hstate t ht

section AxiomAudit

#print axioms
  weightedMovingHeatGradientEta_eq_weightedMovingHeatEta_deriv_of_bounded
#print axioms paper5Weighted_splitRestartTerm_eq_damped_generatorTerm
#print axioms
  paper5Weighted_canonicalSplitSource_eq_population_add_rawForcing
#print axioms
  paper5Weighted_canonicalSplitSource_eq_population_add_generatorForcing
#print axioms
  paper5Weighted_canonicalSplitRestartTerm_eq_damped_generatorTerm
#print axioms
  weightedMovingHeatL2Semigroup_damped_mild_restart_eq_of_pointwise
#print axioms
  weightedMovingHeatL2Semigroup_damped_mild_restart_eq_of_pointwise_total
#print axioms paper5Weighted_damped_restart_pointwise_of_split
#print axioms
  paper5Weighted_canonicalPopulation_damped_restart_pointwise_of_split
#print axioms paper5WeightedPopulation_damped_restart_L2_of_pointwise
#print axioms
  paper5WeightedPopulation_eq_fullGeneratorCandidate_of_damped_pointwise_on_window

end AxiomAudit

end ShenWork.Paper1
