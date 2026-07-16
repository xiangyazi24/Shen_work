import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorForcingNatural
import ShenWork.Paper1.WholeLineWeightedRegularityPositiveWindowForcing

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Natural exact-weight continuity of the physical generator forcing

This file packages the physical generator forcing itself as a clamped
`WholeLineRealL2` trajectory on a compact positive-time window.  The
continuity input is scalar strong `L²` convergence at the same exponential
weight; no stronger exponential weight and no pointwise spatial dominator
are used.
-/

/-- Clamp a time-dependent family to a fixed closed interval. -/
def paper5PositiveWindowClamp {E : Type*} {a b : ℝ} (hab : a ≤ b)
    (f : ℝ → E) (s : ℝ) : E :=
  f (Set.projIcc a b hab s)

/-- The physical generator forcing, clamped in time to a closed positive
window and realized canonically in `L²(ℝ)`. -/
def paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
    (p : CMParams) (eta c : ℝ)
    (u v : ℝ → ℝ → ℝ) (U V : ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b) : ℝ → WholeLineRealL2 :=
  wholeLineRealL2PositiveWindowTrajectory hab
    (paper5WeightedGeneratorForcing p eta
      (coMovingPath c u) (coMovingPath c v) U V)

/-- The natural clamped trajectory represents the physical forcing almost
everywhere at every time in the physical window. -/
theorem paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_coe_ae
    (p : CMParams) (eta c : ℝ)
    (u v : ℝ → ℝ → ℝ) (U V : ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b)
    (hF_meas : ∀ q ∈ Set.Icc a b,
      AEStronglyMeasurable
        (paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q) volume)
    (hF_sq : ∀ q ∈ Set.Icc a b,
      Integrable (fun x : ℝ =>
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q x ^ 2) volume)
    {q : ℝ} (hq : q ∈ Set.Icc a b) :
    (((paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
          p eta c u v U V hab q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V q) := by
  exact wholeLineRealL2PositiveWindowTrajectory_coe_ae_of_mem
    hab hF_meas hF_sq hq

/-- Scalar exact-weight strong `L²` continuity of the physical forcing on
the closed window yields a continuous canonical Hilbert trajectory. -/
theorem paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_continuous
    (p : CMParams) (eta c : ℝ)
    (u v : ℝ → ℝ → ℝ) (U V : ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b)
    (hF_meas : ∀ q ∈ Set.Icc a b,
      AEStronglyMeasurable
        (paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q) volume)
    (hF_sq : ∀ q ∈ Set.Icc a b,
      Integrable (fun x : ℝ =>
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q x ^ 2) volume)
    (hF_strong : ∀ q ∈ Set.Icc a b,
      Tendsto (fun r => ∫ x : ℝ,
        (paper5WeightedGeneratorForcing p eta
              (coMovingPath c u) (coMovingPath c v) U V r x -
            paper5WeightedGeneratorForcing p eta
              (coMovingPath c u) (coMovingPath c v) U V q x) ^ 2)
        (nhdsWithin q (Set.Icc a b)) (nhds 0)) :
    Continuous
      (paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
        p eta c u v U V hab) := by
  exact wholeLineRealL2PositiveWindowTrajectory_continuous
    hab hF_meas hF_sq hF_strong

/-- The same natural trajectory is Bochner integrable on every finite
oriented time interval. -/
theorem paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_intervalIntegrable
    (p : CMParams) (eta c : ℝ)
    (u v : ℝ → ℝ → ℝ) (U V : ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b)
    (hF_meas : ∀ q ∈ Set.Icc a b,
      AEStronglyMeasurable
        (paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q) volume)
    (hF_sq : ∀ q ∈ Set.Icc a b,
      Integrable (fun x : ℝ =>
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q x ^ 2) volume)
    (hF_strong : ∀ q ∈ Set.Icc a b,
      Tendsto (fun r => ∫ x : ℝ,
        (paper5WeightedGeneratorForcing p eta
              (coMovingPath c u) (coMovingPath c v) U V r x -
            paper5WeightedGeneratorForcing p eta
              (coMovingPath c u) (coMovingPath c v) U V q x) ^ 2)
        (nhdsWithin q (Set.Icc a b)) (nhds 0))
    (s t : ℝ) :
    IntervalIntegrable
      (paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
        p eta c u v U V hab) volume s t :=
  (paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_continuous
    p eta c u v U V hab hF_meas hF_sq hF_strong).intervalIntegrable s t

/-! ## Resolver continuity at the exact weight -/

/-- Strong exact-weight `L²` continuity of the population trajectory is
transferred by the frozen elliptic resolver to both the signal and its
weighted first derivative.  This is the time-dependent form of Lemma 5.3;
the reference profile cancels from every difference. -/
theorem paper5WeightedSignal_strongL2At_of_population_strongL2At
    (p : CMParams) {M eta t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    {l : Filter ℝ}
    (hM : 1 ≤ M) (heta : 0 < eta) (heta1 : eta < 1)
    (huC : ∀ s, IsCUnifBdd (u s))
    (huM : ∀ s x, u s x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : ∀ s, v s = frozenElliptic p (u s))
    (hvDiff : ∀ s, Differentiable ℝ (v s))
    (hVDiff : Differentiable ℝ V)
    (hWdiff : ∀ᶠ s in l, Integrable (fun x : ℝ =>
      (paper5WeightedPopulation eta u U s x -
        paper5WeightedPopulation eta u U t x) ^ 2) volume)
    (hWzero : Tendsto (fun s => ∫ x : ℝ,
      (paper5WeightedPopulation eta u U s x -
        paper5WeightedPopulation eta u U t x) ^ 2) l (nhds 0)) :
    (∀ᶠ s in l, Integrable (fun x : ℝ =>
      (paper5WeightedSignal eta v V s x -
        paper5WeightedSignal eta v V t x) ^ 2) volume) ∧
      Tendsto (fun s => ∫ x : ℝ,
        (paper5WeightedSignal eta v V s x -
          paper5WeightedSignal eta v V t x) ^ 2) l (nhds 0) ∧
      (∀ᶠ s in l, Integrable (fun x : ℝ =>
        (paper5WeightedSignalX eta v V s x -
          paper5WeightedSignalX eta v V t x) ^ 2) volume) ∧
      Tendsto (fun s => ∫ x : ℝ,
        (paper5WeightedSignalX eta v V s x -
          paper5WeightedSignalX eta v V t x) ^ 2) l (nhds 0) := by
  let RV : ℝ := paper5WeightedResolverVFactor p M eta
  let RVx : ℝ := paper5WeightedResolverVxFactor p M eta
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hRV : 0 ≤ RV := by
    dsimp only [RV, paper5WeightedResolverVFactor]
    exact div_nonneg
      (mul_nonneg (sq_nonneg p.γ) (Real.rpow_nonneg hM0 _))
      (sq_nonneg (1 - eta))
  have hetaSq : eta ^ 2 < 1 := by
    have hprod : 0 < (1 - eta) * (1 + eta) :=
      mul_pos (sub_pos.mpr heta1) (by linarith)
    nlinarith
  have hRVx : 0 ≤ RVx := by
    dsimp only [RVx, paper5WeightedResolverVxFactor]
    exact div_nonneg
      (mul_nonneg (sq_nonneg p.γ) (Real.rpow_nonneg hM0 _))
      (sub_nonneg.mpr hetaSq.le)
  have hdata : ∀ᶠ s in l,
      Integrable (fun x : ℝ =>
        (paper5WeightedSignal eta v V s x -
          paper5WeightedSignal eta v V t x) ^ 2) volume ∧
      Integrable (fun x : ℝ =>
        (paper5WeightedSignalX eta v V s x -
          paper5WeightedSignalX eta v V t x) ^ 2) volume ∧
      (∫ x : ℝ,
        (paper5WeightedSignal eta v V s x -
          paper5WeightedSignal eta v V t x) ^ 2) ≤
        RV * (∫ x : ℝ,
          (paper5WeightedPopulation eta u U s x -
            paper5WeightedPopulation eta u U t x) ^ 2) ∧
      (∫ x : ℝ,
        (paper5WeightedSignalX eta v V s x -
          paper5WeightedSignalX eta v V t x) ^ 2) ≤
        RVx * (∫ x : ℝ,
          (paper5WeightedPopulation eta u U s x -
            paper5WeightedPopulation eta u U t x) ^ 2) := by
    filter_upwards [hWdiff] with s hs
    have hclose : Integrable (fun x : ℝ =>
        Real.exp (2 * eta * x) * |u s x - u t x| ^ 2) volume := by
      refine hs.congr (Eventually.of_forall fun x => ?_)
      unfold paper5WeightedPopulation
      change
        (Real.exp (eta * x) * (u s x - U x) -
            Real.exp (eta * x) * (u t x - U x)) ^ 2 =
          Real.exp (2 * eta * x) * |u s x - u t x| ^ 2
      rw [show
          (Real.exp (eta * x) * (u s x - U x) -
              Real.exp (eta * x) * (u t x - U x)) =
            Real.exp (eta * x) * (u s x - u t x) by ring,
        mul_pow, sq_abs]
      congr 1
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hraw := weighted_frozenElliptic_difference_l2_data
      p hM heta heta1 (huC t) (huC s) (huM t) (huM s) hclose
    dsimp only at hraw
    have hvalue : ∀ x,
        Real.exp (eta * x) *
            (frozenElliptic p (u s) x - frozenElliptic p (u t) x) =
          paper5WeightedSignal eta v V s x -
            paper5WeightedSignal eta v V t x := by
      intro x
      unfold paper5WeightedSignal
      rw [hvEq s, hvEq t]
      ring
    let R : ℝ → ℝ := fun x => Real.exp (eta * x) *
      (frozenElliptic p (u s) x - frozenElliptic p (u t) x)
    have hR : R = fun x =>
        paper5WeightedSignal eta v V s x -
          paper5WeightedSignal eta v V t x := by
      funext x
      exact hvalue x
    have hderiv : ∀ x, deriv R x =
        paper5WeightedSignalX eta v V s x -
          paper5WeightedSignalX eta v V t x := by
      intro x
      rw [hR]
      change deriv
          (paper5WeightedSignal eta v V s -
            paper5WeightedSignal eta v V t) x = _
      rw [deriv_sub
          ((paper5WeightedSignal_space_hasDerivAt
            (hvDiff s x) (hVDiff x)).differentiableAt)
          ((paper5WeightedSignal_space_hasDerivAt
            (hvDiff t x) (hVDiff x)).differentiableAt),
        (paper5WeightedSignal_space_hasDerivAt
          (hvDiff s x) (hVDiff x)).deriv,
        (paper5WeightedSignal_space_hasDerivAt
          (hvDiff t x) (hVDiff x)).deriv]
    have hWpoint : ∀ x,
        Real.exp (eta * x) * (u s x - u t x) =
          paper5WeightedPopulation eta u U s x -
            paper5WeightedPopulation eta u U t x := by
      intro x
      unfold paper5WeightedPopulation
      ring
    have hZint : Integrable (fun x : ℝ =>
        (paper5WeightedSignal eta v V s x -
          paper5WeightedSignal eta v V t x) ^ 2) volume := by
      refine hraw.1.congr (Eventually.of_forall fun x => ?_)
      exact congrArg (fun y : ℝ => y ^ 2) (hvalue x)
    have hZxint : Integrable (fun x : ℝ =>
        (paper5WeightedSignalX eta v V s x -
          paper5WeightedSignalX eta v V t x) ^ 2) volume := by
      refine hraw.2.1.congr (Eventually.of_forall fun x => ?_)
      change deriv R x ^ 2 = _
      rw [hderiv]
    have hZle : (∫ x : ℝ,
        (paper5WeightedSignal eta v V s x -
          paper5WeightedSignal eta v V t x) ^ 2) ≤
        RV * (∫ x : ℝ,
          (paper5WeightedPopulation eta u U s x -
            paper5WeightedPopulation eta u U t x) ^ 2) := by
      simpa only [RV, paper5WeightedResolverVFactor, hvalue, hWpoint,
        sq_abs] using hraw.2.2.1
    have hZxle : (∫ x : ℝ,
        (paper5WeightedSignalX eta v V s x -
          paper5WeightedSignalX eta v V t x) ^ 2) ≤
        RVx * (∫ x : ℝ,
          (paper5WeightedPopulation eta u U s x -
            paper5WeightedPopulation eta u U t x) ^ 2) := by
      have hx := hraw.2.2.2
      change (∫ x : ℝ, deriv R x ^ 2) ≤ _ at hx
      simpa only [RVx, paper5WeightedResolverVxFactor, hderiv, hWpoint,
        sq_abs] using hx
    exact ⟨hZint, hZxint, hZle, hZxle⟩
  have hZzero : Tendsto (fun s => ∫ x : ℝ,
      (paper5WeightedSignal eta v V s x -
        paper5WeightedSignal eta v V t x) ^ 2) l (nhds 0) := by
    exact squeeze_zero'
      (Eventually.of_forall fun s => integral_nonneg fun x => sq_nonneg _)
      (hdata.mono fun _ hs => hs.2.2.1)
      (by simpa using hWzero.const_mul RV)
  have hZxzero : Tendsto (fun s => ∫ x : ℝ,
      (paper5WeightedSignalX eta v V s x -
        paper5WeightedSignalX eta v V t x) ^ 2) l (nhds 0) := by
    exact squeeze_zero'
      (Eventually.of_forall fun s => integral_nonneg fun x => sq_nonneg _)
      (hdata.mono fun _ hs => hs.2.2.2)
      (by simpa using hWzero.const_mul RVx)
  exact ⟨hdata.mono fun _ hs => hs.1, hZzero,
    hdata.mono fun _ hs => hs.2.1, hZxzero⟩

/-- Static exact-weight square-integrability of the signal and its weighted
first derivative for an arbitrary frozen-resolver trajectory. -/
theorem paper5WeightedSignal_sq_integrable_of_population_sq_integrable
    (p : CMParams) {M eta t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hM : 1 ≤ M) (heta : 0 < eta) (heta1 : eta < 1)
    (huC : IsCUnifBdd (u t)) (hUC : IsCUnifBdd U)
    (huM : ∀ x, u t x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : v t = frozenElliptic p (u t))
    (hVEq : V = frozenElliptic p U)
    (hvDiff : Differentiable ℝ (v t))
    (hVDiff : Differentiable ℝ V)
    (hW : Integrable (fun x =>
      paper5WeightedPopulation eta u U t x ^ 2) volume) :
    Integrable (fun x => paper5WeightedSignal eta v V t x ^ 2) volume ∧
      Integrable (fun x =>
        paper5WeightedSignalX eta v V t x ^ 2) volume := by
  have hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) * |u t x - U x| ^ 2) volume := by
    refine hW.congr (Eventually.of_forall fun x => ?_)
    unfold paper5WeightedPopulation
    change (Real.exp (eta * x) * (u t x - U x)) ^ 2 =
      Real.exp (2 * eta * x) * |u t x - U x| ^ 2
    rw [mul_pow, sq_abs]
    congr 1
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hraw := weighted_frozenElliptic_difference_l2_data
    p hM heta heta1 hUC huC hUM huM hclose
  dsimp only at hraw
  have hvalue : ∀ x,
      Real.exp (eta * x) *
          (frozenElliptic p (u t) x - frozenElliptic p U x) =
        paper5WeightedSignal eta v V t x := by
    intro x
    unfold paper5WeightedSignal
    rw [hvEq, hVEq]
  let R : ℝ → ℝ := fun x => Real.exp (eta * x) *
    (frozenElliptic p (u t) x - frozenElliptic p U x)
  have hR : R = paper5WeightedSignal eta v V t := by
    funext x
    exact hvalue x
  have hderiv : ∀ x, deriv R x =
      paper5WeightedSignalX eta v V t x := by
    intro x
    rw [hR, (paper5WeightedSignal_space_hasDerivAt
      (hvDiff x) (hVDiff x)).deriv]
  constructor
  · refine hraw.1.congr (Eventually.of_forall fun x => ?_)
    exact congrArg (fun y : ℝ => y ^ 2) (hvalue x)
  · refine hraw.2.1.congr (Eventually.of_forall fun x => ?_)
    change deriv R x ^ 2 = _
    rw [hderiv]

/-! ## Exact-weight forcing continuity from `H⁰/H¹` trajectories -/

/-- At a fixed time, exact-weight strong `L²` continuity of the population
and its first weighted spatial derivative, together with uniform-in-space
continuity moduli for the three dynamic coefficients, gives strong `L²`
continuity of the expanded generator forcing.  The two signal trajectories
are produced internally by the elliptic resolver. -/
theorem paper5WeightedGeneratorForcingExpandedTrajectory_strongL2At_of_population_H1
    (p : CMParams) {M eta t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    {K1 K2 K3 K4 KR : ℝ} {D1 D2 DR : ℝ → ℝ}
    (hM : 1 ≤ M) (heta : 0 < eta) (heta1 : eta < 1)
    (huC : ∀ s, IsCUnifBdd (u s)) (hUC : IsCUnifBdd U)
    (huM : ∀ s x, u s x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : ∀ s, v s = frozenElliptic p (u s))
    (hVEq : V = frozenElliptic p U)
    (hv2 : ∀ s, ContDiff ℝ 2 (v s))
    (hV2 : ContDiff ℝ 2 V)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hK3 : 0 ≤ K3) (hK4 : 0 ≤ K4) (hKR : 0 ≤ KR)
    (hD1_nonneg : ∀ᶠ s in 𝓝 t, 0 ≤ D1 s)
    (hD2_nonneg : ∀ᶠ s in 𝓝 t, 0 ≤ D2 s)
    (hDR_nonneg : ∀ᶠ s in 𝓝 t, 0 ≤ DR s)
    (hD1 : Tendsto D1 (𝓝 t) (𝓝 0))
    (hD2 : Tendsto D2 (𝓝 t) (𝓝 0))
    (hDR : Tendsto DR (𝓝 t) (𝓝 0))
    (hB1_bound : ∀ᶠ s in 𝓝 t, ∀ x,
      |paper5B1 p u v s x| ≤ K1)
    (hB1_diff : ∀ᶠ s in 𝓝 t, ∀ x,
      |paper5B1 p u v s x - paper5B1 p u v t x| ≤ D1 s)
    (hB2_bound : ∀ᶠ s in 𝓝 t, ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta u v U s x| ≤ K2)
    (hB2_diff : ∀ᶠ s in 𝓝 t, ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta u v U s x -
          paper5WeightedFluxPopulationCoefficient p eta u v U t x| ≤ D2 s)
    (hB3_bound : ∀ x, |paper5B3 p U x| ≤ K3)
    (hB4_bound : ∀ x,
      |paper5WeightedFluxSignalCoefficient p eta U x| ≤ K4)
    (hR_bound : ∀ᶠ s in 𝓝 t, ∀ x,
      |1 - paper5A (1 + p.α) u U s x| ≤ KR)
    (hR_diff : ∀ᶠ s in 𝓝 t, ∀ x,
      |(1 - paper5A (1 + p.α) u U s x) -
          (1 - paper5A (1 + p.α) u U t x)| ≤ DR s)
    (hB1_meas : ∀ s,
      AEStronglyMeasurable (paper5B1 p u v s) volume)
    (hB2_meas : ∀ s, AEStronglyMeasurable
      (paper5WeightedFluxPopulationCoefficient p eta u v U s) volume)
    (hB3_meas : AEStronglyMeasurable (paper5B3 p U) volume)
    (hB4_meas : AEStronglyMeasurable
      (paper5WeightedFluxSignalCoefficient p eta U) volume)
    (hR_meas : ∀ s, AEStronglyMeasurable
      (fun x => 1 - paper5A (1 + p.α) u U s x) volume)
    (hW_meas : ∀ s, AEStronglyMeasurable
      (paper5WeightedPopulation eta u U s) volume)
    (hWx_meas : ∀ s, AEStronglyMeasurable
      (paper5WeightedPopulationX eta u U s) volume)
    (hW_t : Integrable (fun x =>
      paper5WeightedPopulation eta u U t x ^ 2) volume)
    (hWx_t : Integrable (fun x =>
      paper5WeightedPopulationX eta u U t x ^ 2) volume)
    (hW_diff : ∀ᶠ s in 𝓝 t, Integrable (fun x =>
      (paper5WeightedPopulation eta u U s x -
        paper5WeightedPopulation eta u U t x) ^ 2) volume)
    (hWx_diff : ∀ᶠ s in 𝓝 t, Integrable (fun x =>
      (paper5WeightedPopulationX eta u U s x -
        paper5WeightedPopulationX eta u U t x) ^ 2) volume)
    (hW_zero : Tendsto (fun s => ∫ x : ℝ,
      (paper5WeightedPopulation eta u U s x -
        paper5WeightedPopulation eta u U t x) ^ 2) (𝓝 t) (𝓝 0))
    (hWx_zero : Tendsto (fun s => ∫ x : ℝ,
      (paper5WeightedPopulationX eta u U s x -
        paper5WeightedPopulationX eta u U t x) ^ 2) (𝓝 t) (𝓝 0)) :
    (∀ᶠ s in 𝓝 t, Integrable (fun x =>
      (paper5WeightedGeneratorForcingExpandedTrajectory p eta u v U
          (paper5WeightedPopulation eta u U)
          (paper5WeightedPopulationX eta u U)
          (paper5WeightedSignal eta v V)
          (paper5WeightedSignalX eta v V) s x -
        paper5WeightedGeneratorForcingExpandedTrajectory p eta u v U
          (paper5WeightedPopulation eta u U)
          (paper5WeightedPopulationX eta u U)
          (paper5WeightedSignal eta v V)
          (paper5WeightedSignalX eta v V) t x) ^ 2) volume) ∧
      Tendsto (fun s => ∫ x : ℝ,
        (paper5WeightedGeneratorForcingExpandedTrajectory p eta u v U
            (paper5WeightedPopulation eta u U)
            (paper5WeightedPopulationX eta u U)
            (paper5WeightedSignal eta v V)
            (paper5WeightedSignalX eta v V) s x -
          paper5WeightedGeneratorForcingExpandedTrajectory p eta u v U
            (paper5WeightedPopulation eta u U)
            (paper5WeightedPopulationX eta u U)
            (paper5WeightedSignal eta v V)
            (paper5WeightedSignalX eta v V) t x) ^ 2)
        (𝓝 t) (𝓝 0) := by
  have hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) * |u t x - U x| ^ 2) volume := by
    refine hW_t.congr (Eventually.of_forall fun x => ?_)
    unfold paper5WeightedPopulation
    change (Real.exp (eta * x) * (u t x - U x)) ^ 2 =
      Real.exp (2 * eta * x) * |u t x - U x| ^ 2
    rw [mul_pow, sq_abs]
    congr 1
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsignalStatic :=
    paper5WeightedSignal_sq_integrable_of_population_sq_integrable
      p hM heta heta1 (huC t) hUC (huM t) hUM (hvEq t) hVEq
        ((hv2 t).differentiable (by norm_num))
        (hV2.differentiable (by norm_num)) hW_t
  have hsignalStrong :=
    paper5WeightedSignal_strongL2At_of_population_strongL2At
      p hM heta heta1 huC huM hvEq
        (fun s => (hv2 s).differentiable (by norm_num))
        (hV2.differentiable (by norm_num))
        hW_diff hW_zero
  have hZ_meas : ∀ s, AEStronglyMeasurable
      (paper5WeightedSignal eta v V s) volume := by
    intro s
    exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul
        ((hv2 s).continuous.sub hV2.continuous)).aestronglyMeasurable
  have hZx_meas : ∀ s, AEStronglyMeasurable
      (paper5WeightedSignalX eta v V s) volume := by
    intro s
    have hexp : Continuous (fun x : ℝ => Real.exp (eta * x)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hvx : Continuous (deriv (v s)) :=
      (hv2 s).continuous_deriv (by norm_num)
    have hVx : Continuous (deriv V) := hV2.continuous_deriv (by norm_num)
    exact ((continuous_const.mul
        ((hexp.mul ((hv2 s).continuous.sub hV2.continuous)))).add
      (hexp.mul (hvx.sub hVx))).aestronglyMeasurable
  have hflux_meas : ∀ s, AEStronglyMeasurable
      (paper5WeightedFluxDerivativeExpandedTrajectory p eta u v U
        (paper5WeightedPopulation eta u U)
        (paper5WeightedPopulationX eta u U)
        (paper5WeightedSignal eta v V)
        (paper5WeightedSignalX eta v V) s) volume := by
    intro s
    exact paper5WeightedFluxDerivativeExpandedTrajectory_aestronglyMeasurable
      p eta s (hB1_meas s) (hB2_meas s) hB3_meas hB4_meas
        (hW_meas s) (hWx_meas s) (hZ_meas s) (hZx_meas s)
  have hreact_meas : ∀ s, AEStronglyMeasurable
      (paper5WeightedReactionExpandedTrajectory p u U
        (paper5WeightedPopulation eta u U) s) volume := by
    intro s
    exact paper5WeightedReactionExpandedTrajectory_aestronglyMeasurable
      p s (hR_meas s) (hW_meas s)
  have hflux := paper5WeightedFluxDerivativeExpandedTrajectory_strongL2At
    p eta hK1 hK2 hK3 hK4 hD1_nonneg hD2_nonneg hD1 hD2
      hB1_bound hB1_diff hB2_bound hB2_diff hB3_bound hB4_bound
      hB1_meas hB2_meas hB3_meas hB4_meas hW_meas hWx_meas
      hZ_meas hZx_meas hW_t hWx_t hsignalStatic.1
      hsignalStatic.2 hW_diff hWx_diff hsignalStrong.1
      hsignalStrong.2.2.1 hW_zero hWx_zero hsignalStrong.2.1
      hsignalStrong.2.2.2
  have hreact := paper5WeightedReactionExpandedTrajectory_strongL2At
    p hKR hDR_nonneg hDR hR_bound hR_diff hR_meas hW_meas
      hW_t hW_diff hW_zero
  exact paper5WeightedGeneratorForcingExpandedTrajectory_strongL2At_of_flux_reaction
    p eta hflux_meas hreact_meas hflux.1 hreact.1 hflux.2 hreact.2

/-- Closed-window form of the preceding producer.  The stated `W` and `Wx`
hypotheses are genuine strong `L²` continuity assumptions for the clamped
trajectories; no second derivative, generator, or time derivative occurs.
The coefficient hypotheses are uniform-in-space continuity moduli in their
native BUC form. -/
theorem paper5WeightedGeneratorForcingExpandedActualTrajectory_strongL2Within_of_population_H1
    (p : CMParams) {M eta a b : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hab : a ≤ b)
    {K1 K2 K3 K4 KR : ℝ}
    {D1 D2 DR : ℝ → ℝ → ℝ}
    (hM : 1 ≤ M) (heta : 0 < eta) (heta1 : eta < 1)
    (huC : ∀ q ∈ Set.Icc a b, IsCUnifBdd (u q))
    (hUC : IsCUnifBdd U)
    (huM : ∀ q ∈ Set.Icc a b, ∀ x, u q x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : ∀ q ∈ Set.Icc a b, v q = frozenElliptic p (u q))
    (hVEq : V = frozenElliptic p U)
    (hu2 : ∀ q ∈ Set.Icc a b, ContDiff ℝ 2 (u q))
    (hv2 : ∀ q ∈ Set.Icc a b, ContDiff ℝ 2 (v q))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hK3 : 0 ≤ K3) (hK4 : 0 ≤ K4) (hKR : 0 ≤ KR)
    (hD1_nonneg : ∀ q ∈ Set.Icc a b,
      ∀ᶠ s in 𝓝 q, 0 ≤ D1 q s)
    (hD2_nonneg : ∀ q ∈ Set.Icc a b,
      ∀ᶠ s in 𝓝 q, 0 ≤ D2 q s)
    (hDR_nonneg : ∀ q ∈ Set.Icc a b,
      ∀ᶠ s in 𝓝 q, 0 ≤ DR q s)
    (hD1 : ∀ q ∈ Set.Icc a b, Tendsto (D1 q) (𝓝 q) (𝓝 0))
    (hD2 : ∀ q ∈ Set.Icc a b, Tendsto (D2 q) (𝓝 q) (𝓝 0))
    (hDR : ∀ q ∈ Set.Icc a b, Tendsto (DR q) (𝓝 q) (𝓝 0))
    (hB1_bound : ∀ q ∈ Set.Icc a b, ∀ᶠ s in 𝓝 q, ∀ x,
      |paper5B1 p (paper5PositiveWindowClamp hab u)
          (paper5PositiveWindowClamp hab v) s x| ≤ K1)
    (hB1_diff : ∀ q ∈ Set.Icc a b, ∀ᶠ s in 𝓝 q, ∀ x,
      |paper5B1 p (paper5PositiveWindowClamp hab u)
            (paper5PositiveWindowClamp hab v) s x -
          paper5B1 p (paper5PositiveWindowClamp hab u)
            (paper5PositiveWindowClamp hab v) q x| ≤ D1 q s)
    (hB2_bound : ∀ q ∈ Set.Icc a b, ∀ᶠ s in 𝓝 q, ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta
          (paper5PositiveWindowClamp hab u)
          (paper5PositiveWindowClamp hab v) U s x| ≤ K2)
    (hB2_diff : ∀ q ∈ Set.Icc a b, ∀ᶠ s in 𝓝 q, ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta
            (paper5PositiveWindowClamp hab u)
            (paper5PositiveWindowClamp hab v) U s x -
          paper5WeightedFluxPopulationCoefficient p eta
            (paper5PositiveWindowClamp hab u)
            (paper5PositiveWindowClamp hab v) U q x| ≤ D2 q s)
    (hB3_bound : ∀ x, |paper5B3 p U x| ≤ K3)
    (hB4_bound : ∀ x,
      |paper5WeightedFluxSignalCoefficient p eta U x| ≤ K4)
    (hR_bound : ∀ q ∈ Set.Icc a b, ∀ᶠ s in 𝓝 q, ∀ x,
      |1 - paper5A (1 + p.α) (paper5PositiveWindowClamp hab u) U s x| ≤ KR)
    (hR_diff : ∀ q ∈ Set.Icc a b, ∀ᶠ s in 𝓝 q, ∀ x,
      |(1 - paper5A (1 + p.α)
            (paper5PositiveWindowClamp hab u) U s x) -
          (1 - paper5A (1 + p.α)
            (paper5PositiveWindowClamp hab u) U q x)| ≤ DR q s)
    (hB1_meas : ∀ s, AEStronglyMeasurable
      (paper5B1 p (paper5PositiveWindowClamp hab u)
        (paper5PositiveWindowClamp hab v) s) volume)
    (hB2_meas : ∀ s, AEStronglyMeasurable
      (paper5WeightedFluxPopulationCoefficient p eta
        (paper5PositiveWindowClamp hab u)
        (paper5PositiveWindowClamp hab v) U s) volume)
    (hB3_meas : AEStronglyMeasurable (paper5B3 p U) volume)
    (hB4_meas : AEStronglyMeasurable
      (paper5WeightedFluxSignalCoefficient p eta U) volume)
    (hR_meas : ∀ s, AEStronglyMeasurable
      (fun x => 1 - paper5A (1 + p.α)
        (paper5PositiveWindowClamp hab u) U s x) volume)
    (hW_sq : ∀ q ∈ Set.Icc a b, Integrable (fun x =>
      paper5WeightedPopulation eta u U q x ^ 2) volume)
    (hWx_sq : ∀ q ∈ Set.Icc a b, Integrable (fun x =>
      paper5WeightedPopulationX eta u U q x ^ 2) volume)
    (hW_strong : ∀ q ∈ Set.Icc a b,
      (∀ᶠ s in 𝓝 q, Integrable (fun x =>
        (paper5WeightedPopulation eta
              (paper5PositiveWindowClamp hab u) U s x -
            paper5WeightedPopulation eta
              (paper5PositiveWindowClamp hab u) U q x) ^ 2) volume) ∧
      Tendsto (fun s => ∫ x : ℝ,
        (paper5WeightedPopulation eta
              (paper5PositiveWindowClamp hab u) U s x -
            paper5WeightedPopulation eta
              (paper5PositiveWindowClamp hab u) U q x) ^ 2)
        (𝓝 q) (𝓝 0))
    (hWx_strong : ∀ q ∈ Set.Icc a b,
      (∀ᶠ s in 𝓝 q, Integrable (fun x =>
        (paper5WeightedPopulationX eta
              (paper5PositiveWindowClamp hab u) U s x -
            paper5WeightedPopulationX eta
              (paper5PositiveWindowClamp hab u) U q x) ^ 2) volume) ∧
      Tendsto (fun s => ∫ x : ℝ,
        (paper5WeightedPopulationX eta
              (paper5PositiveWindowClamp hab u) U s x -
            paper5WeightedPopulationX eta
              (paper5PositiveWindowClamp hab u) U q x) ^ 2)
        (𝓝 q) (𝓝 0)) :
    ∀ q ∈ Set.Icc a b,
      Tendsto (fun r => ∫ x : ℝ,
        (paper5WeightedGeneratorForcingExpandedTrajectory p eta u v U
              (paper5WeightedPopulation eta u U)
              (paper5WeightedPopulationX eta u U)
              (paper5WeightedSignal eta v V)
              (paper5WeightedSignalX eta v V) r x -
            paper5WeightedGeneratorForcingExpandedTrajectory p eta u v U
              (paper5WeightedPopulation eta u U)
              (paper5WeightedPopulationX eta u U)
              (paper5WeightedSignal eta v V)
              (paper5WeightedSignalX eta v V) q x) ^ 2)
        (nhdsWithin q (Set.Icc a b)) (nhds 0) := by
  let uc : ℝ → ℝ → ℝ := paper5PositiveWindowClamp hab u
  let vc : ℝ → ℝ → ℝ := paper5PositiveWindowClamp hab v
  have htau_mem : ∀ s,
      (Set.projIcc a b hab s : ℝ) ∈ Set.Icc a b :=
    fun s => (Set.projIcc a b hab s).2
  have hucC : ∀ s, IsCUnifBdd (uc s) :=
    fun s => huC _ (htau_mem s)
  have hucM : ∀ s x, uc s x ∈ Set.Icc (0 : ℝ) M :=
    fun s x => huM _ (htau_mem s) x
  have hvcEq : ∀ s, vc s = frozenElliptic p (uc s) := by
    intro s
    exact hvEq _ (htau_mem s)
  have hvc2 : ∀ s, ContDiff ℝ 2 (vc s) :=
    fun s => hv2 _ (htau_mem s)
  have hW_meas : ∀ s, AEStronglyMeasurable
      (paper5WeightedPopulation eta uc U s) volume := by
    intro s
    exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul
        ((hu2 _ (htau_mem s)).continuous.sub hU2.continuous)).aestronglyMeasurable
  have hWx_meas : ∀ s, AEStronglyMeasurable
      (paper5WeightedPopulationX eta uc U s) volume := by
    intro s
    have hexp : Continuous (fun x : ℝ => Real.exp (eta * x)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hux : Continuous (deriv (uc s)) :=
      (hu2 _ (htau_mem s)).continuous_deriv (by norm_num)
    have hUx : Continuous (deriv U) := hU2.continuous_deriv (by norm_num)
    exact ((continuous_const.mul
        (hexp.mul ((hu2 _ (htau_mem s)).continuous.sub hU2.continuous))).add
      (hexp.mul (hux.sub hUx))).aestronglyMeasurable
  intro q hq
  have hucq : uc q = u q := by
    dsimp only [uc, paper5PositiveWindowClamp]
    simpa using congrArg (fun z : Set.Icc a b => u z.1)
      (Set.projIcc_of_mem hab hq)
  have hvcq : vc q = v q := by
    dsimp only [vc, paper5PositiveWindowClamp]
    simpa using congrArg (fun z : Set.Icc a b => v z.1)
      (Set.projIcc_of_mem hab hq)
  have hWq : Integrable (fun x =>
      paper5WeightedPopulation eta uc U q x ^ 2) volume := by
    simpa only [paper5WeightedPopulation, hucq] using hW_sq q hq
  have hWxq : Integrable (fun x =>
      paper5WeightedPopulationX eta uc U q x ^ 2) volume := by
    simpa only [paper5WeightedPopulationX, paper5WeightedPopulation,
      hucq] using hWx_sq q hq
  have hcStrong :=
    paper5WeightedGeneratorForcingExpandedTrajectory_strongL2At_of_population_H1
      p hM heta heta1 hucC hUC hucM hUM hvcEq hVEq hvc2 hV2
        hK1 hK2 hK3 hK4 hKR
        (hD1_nonneg q hq) (hD2_nonneg q hq) (hDR_nonneg q hq)
        (hD1 q hq) (hD2 q hq) (hDR q hq)
        (hB1_bound q hq) (hB1_diff q hq)
        (hB2_bound q hq) (hB2_diff q hq) hB3_bound hB4_bound
        (hR_bound q hq) (hR_diff q hq) hB1_meas hB2_meas
        hB3_meas hB4_meas hR_meas hW_meas hWx_meas
        hWq hWxq (hW_strong q hq).1 (hWx_strong q hq).1
        (hW_strong q hq).2 (hWx_strong q hq).2
  refine (hcStrong.2.mono_left
    (show nhdsWithin q (Set.Icc a b) ≤ nhds q from inf_le_left)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hucr : uc r = u r := by
    dsimp only [uc, paper5PositiveWindowClamp]
    simpa using congrArg (fun z : Set.Icc a b => u z.1)
      (Set.projIcc_of_mem hab hr)
  have hvcr : vc r = v r := by
    dsimp only [vc, paper5PositiveWindowClamp]
    simpa using congrArg (fun z : Set.Icc a b => v z.1)
      (Set.projIcc_of_mem hab hr)
  simp only [paper5WeightedGeneratorForcingExpandedTrajectory,
    paper5WeightedFluxDerivativeExpandedTrajectory,
    paper5WeightedFluxDerivativeExpanded,
    paper5WeightedReactionExpandedTrajectory,
    paper5B1, paper5B2, paper5CorrectedChemZeroCoefficient, paper5A,
    paper5WeightedPopulation, paper5WeightedPopulationX,
    paper5WeightedSignal, paper5WeightedSignalX,
    hucq, hvcq, hucr, hvcr]

/-! ## Physical positive-window closure -/

/-- Strong `L²` continuity of the expanded actual forcing transfers to the
physical forcing on a classical positive-time window. -/
theorem paper5WeightedGeneratorForcing_strongL2Within_of_expanded
    (p : CMParams) {T eta c a b : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hbT : b < T)
    (hsol : IsClassicalSolution p T u v)
    (hTW : IsTravelingWave p c U V)
    (hu2 : ∀ q ∈ Set.Icc a b, ContDiff ℝ 2 (coMovingPath c u q))
    (hv2 : ∀ q ∈ Set.Icc a b, ContDiff ℝ 2 (coMovingPath c v q))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (hu : ∀ q ∈ Set.Icc a b, ∀ x, 0 ≤ coMovingPath c u q x)
    (hstrong : ∀ q ∈ Set.Icc a b,
      Tendsto (fun r => ∫ x : ℝ,
        (paper5WeightedGeneratorForcingExpandedActualTrajectory
              p eta c u v U V r x -
            paper5WeightedGeneratorForcingExpandedActualTrajectory
              p eta c u v U V q x) ^ 2)
        (nhdsWithin q (Set.Icc a b)) (nhds 0)) :
    ∀ q ∈ Set.Icc a b,
      Tendsto (fun r => ∫ x : ℝ,
        (paper5WeightedGeneratorForcing p eta
              (coMovingPath c u) (coMovingPath c v) U V r x -
            paper5WeightedGeneratorForcing p eta
              (coMovingPath c u) (coMovingPath c v) U V q x) ^ 2)
        (nhdsWithin q (Set.Icc a b)) (nhds 0) := by
  intro q hq
  have hq0 : 0 < q := ha.trans_le hq.1
  have hqT : q < T := hq.2.trans_lt hbT
  have hqEq :
      paper5WeightedGeneratorForcingExpandedActualTrajectory
          p eta c u v U V q =
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q := by
    exact paper5WeightedGeneratorForcingExpandedTrajectory_fun_eq_generatorForcing
      p hsol hq0 hqT hTW (hu q hq)
        ((hu2 q hq).of_le (by norm_num)) (hv2 q hq)
        (hU2.of_le (by norm_num)) hV2
  refine (hstrong q hq).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : 0 < r := ha.trans_le hr.1
  have hrT : r < T := hr.2.trans_lt hbT
  have hrEq :
      paper5WeightedGeneratorForcingExpandedActualTrajectory
          p eta c u v U V r =
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V r := by
    exact paper5WeightedGeneratorForcingExpandedTrajectory_fun_eq_generatorForcing
      p hsol hr0 hrT hTW (hu r hr)
        ((hu2 r hr).of_le (by norm_num)) (hv2 r hr)
        (hU2.of_le (by norm_num)) hV2
  rw [hrEq, hqEq]

/-- Natural static `H⁰/H¹` data and expanded scalar strong continuity give
the complete physical forcing trajectory package: continuity, its physical
almost-everywhere representative on the window, and Bochner integrability
on every finite oriented interval. -/
theorem paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_data
    (p : CMParams) {M T eta c a b : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hchi : p.χ ≠ 0)
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (heta : 0 < eta) (hetaCap : eta < stabilityWeightCap p)
    (hab : a ≤ b) (ha : 0 < a) (hbT : b < T)
    (hsol : IsClassicalSolution p T u v)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hMChiM : MChi p ≤ M)
    (hu2 : ∀ q ∈ Set.Icc a b, ContDiff ℝ 2 (coMovingPath c u q))
    (hv2 : ∀ q ∈ Set.Icc a b, ContDiff ℝ 2 (coMovingPath c v q))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (huM : ∀ q ∈ Set.Icc a b, ∀ x,
      coMovingPath c u q x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : ∀ q ∈ Set.Icc a b,
      coMovingPath c v q = frozenElliptic p (coMovingPath c u q))
    (hclose : ∀ q ∈ Set.Icc a b, Integrable (fun x =>
      Real.exp (2 * eta * x) * |coMovingPath c u q x - U x| ^ 2))
    (hWx2 : ∀ q ∈ Set.Icc a b, Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U q x ^ 2))
    (hExpandedStrong : ∀ q ∈ Set.Icc a b,
      Tendsto (fun r => ∫ x : ℝ,
        (paper5WeightedGeneratorForcingExpandedActualTrajectory
              p eta c u v U V r x -
            paper5WeightedGeneratorForcingExpandedActualTrajectory
              p eta c u v U V q x) ^ 2)
        (nhdsWithin q (Set.Icc a b)) (nhds 0)) :
    Continuous
        (paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
          p eta c u v U V hab) ∧
      (∀ q ∈ Set.Icc a b,
        (((paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
              p eta c u v U V hab q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
          paper5WeightedGeneratorForcing p eta
            (coMovingPath c u) (coMovingPath c v) U V q)) ∧
      ∀ s t : ℝ, IntervalIntegrable
        (paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
          p eta c u v U V hab) volume s t := by
  have hF_meas : ∀ q ∈ Set.Icc a b,
      AEStronglyMeasurable
        (paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q) volume := by
    intro q hq
    exact paper5WeightedGeneratorForcing_aestronglyMeasurable_of_classical_slices
      p (eta := eta) hsol (ha.trans_le hq.1) (hq.2.trans_lt hbT) hTW
        (hu2 q hq) (hv2 q hq) hU2 hV2
  have hF_sq : ∀ q ∈ Set.Icc a b, Integrable (fun x : ℝ =>
      paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V q x ^ 2) volume := by
    intro q hq
    exact (paper5WeightedGeneratorForcing_data_of_population_H1_natural
      p hchi hc heta hetaCap hsol (ha.trans_le hq.1) (hq.2.trans_lt hbT)
        hTW hreg hbound hMChiM (hu2 q hq) (hv2 q hq) hU2 hV2
        (huM q hq) (hvEq q hq) (hclose q hq) (hWx2 q hq)).1
  have hF_strong := paper5WeightedGeneratorForcing_strongL2Within_of_expanded
    p hab ha hbT hsol hTW hu2 hv2 hU2 hV2
      (fun q hq x => (huM q hq x).1) hExpandedStrong
  refine ⟨
    paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_continuous
      p eta c u v U V hab hF_meas hF_sq hF_strong,
    ?_, ?_⟩
  · intro q hq
    exact paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_coe_ae
      p eta c u v U V hab hF_meas hF_sq hq
  · intro s t
    exact paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_intervalIntegrable
      p eta c u v U V hab hF_meas hF_sq hF_strong s t

section AxiomAudit

#print axioms
  paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_coe_ae
#print axioms
  paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_continuous
#print axioms
  paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_intervalIntegrable
#print axioms paper5WeightedSignal_strongL2At_of_population_strongL2At
#print axioms paper5WeightedSignal_sq_integrable_of_population_sq_integrable
#print axioms
  paper5WeightedGeneratorForcingExpandedTrajectory_strongL2At_of_population_H1
#print axioms
  paper5WeightedGeneratorForcingExpandedActualTrajectory_strongL2Within_of_population_H1
#print axioms paper5WeightedGeneratorForcing_strongL2Within_of_expanded
#print axioms
  paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_data

end AxiomAudit

end ShenWork.Paper1
