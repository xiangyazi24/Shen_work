import ShenWork.Paper2.IntervalParabolicDuhamelGainNonCircular
import ShenWork.PDE.IntervalResolverSpatialC2

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.PDE
  (intervalNeumannResolverCoeff intervalNeumannResolverR
    intervalNeumannResolverSourceCoeff)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.Paper3 (unitIntervalNeumannSpectrum)
open ShenWork.Paper2.ParabolicGainInduction
open ShenWork.Paper2.ParabolicDuhamelGainNonCircular
open ShenWork.Paper2.SpatialC6Certificate

noncomputable section

namespace ShenWork.Paper2.ChiNegConcreteSpectralAdapters

/-- Direct constructor for one Duhamel gain slice from source-weight packages.
This avoids routing through the downstream C2-coefficient package. -/
def duhamelGainSliceData_of_spatialWeights
    {k : ℕ} {g w : intervalDomainPoint → ℝ}
    {a : ℝ → ℕ → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (eqOn : Set.EqOn (intervalDomainLift w)
      (fun x : ℝ =>
        ∫ s in (0 : ℝ)..τ, unitIntervalCosineHeatValue (τ - s) (a s) x)
      (Set.Icc (0 : ℝ) 1))
    (lowSource : k = 2 ∨ k = 3 →
      SpatialSlice (k - 1) g → DuhamelSourceSpatialWeightOne a)
    (highSource : k = 4 ∨ k = 5 →
      SpatialSlice (k - 1) g → DuhamelSourceSpatialWeightTwo a) :
    DuhamelGainSliceData k g w where
  a := a
  τ := τ
  hτ := hτ
  eqOn := eqOn
  lowSource := lowSource
  highSource := highSource

/-- The diagonal Neumann resolvent gains one eigenvalue weight: two source
weights imply three resolved weights. -/
theorem resolverCoeff_eigenCube_summable_of_sourceEigenSq_summable
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hsrc : Summable fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          |(intervalNeumannResolverSourceCoeff p u n).re|)) :
    Summable fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            |(intervalNeumannResolverCoeff p u n).re|)) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) ?_ hsrc
  · have hlam_nonneg : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    exact mul_nonneg hlam_nonneg
      (mul_nonneg hlam_nonneg
        (mul_nonneg hlam_nonneg (abs_nonneg _)))
  · intro n
    set lam := unitIntervalCosineEigenvalue n with hlam
    have hlam_nonneg : 0 ≤ lam := by
      rw [hlam]
      unfold unitIntervalCosineEigenvalue
      positivity
    have hden_pos : 0 < p.μ + lam :=
      add_pos_of_pos_of_nonneg p.hμ hlam_nonneg
    have hden_ge : lam ≤ p.μ + lam := by linarith [p.hμ]
    have hratio : lam / (p.μ + lam) ≤ 1 := by
      rw [div_le_iff₀ hden_pos]
      simpa using hden_ge
    have hres :
        |(intervalNeumannResolverCoeff p u n).re| =
          |(intervalNeumannResolverSourceCoeff p u n).re| / (p.μ + lam) := by
      have heig : unitIntervalNeumannSpectrum.eigenvalue n = lam := by
        rw [hlam]
        rw [show unitIntervalNeumannSpectrum.eigenvalue n =
          (n : ℝ) ^ 2 * Real.pi ^ 2 from rfl, unitIntervalCosineEigenvalue]
        ring
      rw [ShenWork.IntervalResolverGradientBridge.resolverCoeff_re_eq, heig]
      rw [abs_div, abs_of_pos hden_pos]
    rw [hres]
    have hsrc_nonneg :
        0 ≤ lam * (lam * |(intervalNeumannResolverSourceCoeff p u n).re|) := by
      positivity
    simpa [hlam] using
      (calc
        lam * (lam *
            (lam *
              (|(intervalNeumannResolverSourceCoeff p u n).re| /
                (p.μ + lam))))
            = (lam / (p.μ + lam)) *
                (lam * (lam *
                  |(intervalNeumannResolverSourceCoeff p u n).re|)) := by
                field_simp [ne_of_gt hden_pos]
        _ ≤ 1 *
            (lam * (lam *
              |(intervalNeumannResolverSourceCoeff p u n).re|)) :=
                mul_le_mul_of_nonneg_right hratio hsrc_nonneg
        _ = lam * (lam *
              |(intervalNeumannResolverSourceCoeff p u n).re|) := by
                ring)

/-- A sixth-order resolved-coefficient summability estimate gives all
`resolverAhead` spatial slices requested by the non-circular ladder. -/
theorem resolverAhead_of_resolverCoeff_eigenCube_summable
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hcube : Summable fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            |(intervalNeumannResolverCoeff p u n).re|))) :
    ∀ k, 2 ≤ k → k < 6 →
      SpatialSlice (k + 1) (intervalNeumannResolverR p u) := by
  intro k _hk2 hk6
  have hcd6 : ContDiff ℝ 6
      (fun x : ℝ => ∑' n : ℕ,
        (intervalNeumannResolverCoeff p u n).re * cosineMode n x) :=
    cosineCoeffSeries_contDiff_six_of_eigenvalue_cube_summable hcube
  have hseries6 : ContDiffOn ℝ (6 : ℕ∞)
      (fun x : ℝ => ∑' n : ℕ,
        (intervalNeumannResolverCoeff p u n).re * cosineMode n x)
      (Set.Icc (0 : ℝ) 1) :=
    hcd6.contDiffOn
  have hk_six : k + 1 ≤ 6 := Nat.succ_le_of_lt hk6
  have hseries :
      ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞)
        (fun x : ℝ => ∑' n : ℕ,
          (intervalNeumannResolverCoeff p u n).re * cosineMode n x)
        (Set.Icc (0 : ℝ) 1) :=
    hseries6.of_le (by exact_mod_cast hk_six)
  simpa [SpatialSlice] using hseries.congr (fun x hx => by
    have hval :
        intervalDomainLift (intervalNeumannResolverR p u) x =
          intervalNeumannResolverR p u ⟨x, hx⟩ := by
      simp [intervalDomainLift, hx]
    rw [hval]
    exact (ShenWork.IntervalResolverSpatialC2.resolverR_eq_cosineSeries
      (p := p) (u := u) ⟨x, hx⟩).symm)

#print axioms duhamelGainSliceData_of_spatialWeights
#print axioms resolverCoeff_eigenCube_summable_of_sourceEigenSq_summable
#print axioms resolverAhead_of_resolverCoeff_eigenCube_summable

end ShenWork.Paper2.ChiNegConcreteSpectralAdapters
