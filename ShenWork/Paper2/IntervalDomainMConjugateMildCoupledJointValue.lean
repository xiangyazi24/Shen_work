import ShenWork.Paper2.IntervalDomainMConjugateMildJointValue
import ShenWork.Paper2.IntervalResolverWeightedTimeSeries
import ShenWork.Paper2.IntervalMildRegularityFrontierAssembly
import ShenWork.Paper2.IntervalDomainPositiveWindowK1OnEndpoint
import ShenWork.PDE.IntervalCoupledClassicalCorePAR

open MeasureTheory Set Filter Topology
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration)
open ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
  (cosineCoeffs_continuousOn_of_jointContinuousOn_Icc)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_abs_le_of_continuous_bounded)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.PDE
  (intervalNeumannResolverSourceCoeff intervalNeumannResolverWeight)

/-- The canonical elliptic power source attached to the faithful mild solution
is jointly continuous on the strict-positive-time closed spatial slab. -/
theorem conjugateMildM_resolverPowerSource_jointContinuousOn
    {p : CM2Params} {u0 : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u0)
    (hu0_bound : ∀ y, |intervalDomainLift u0 y| ≤ D.M)
    (hu0_meas : AEStronglyMeasurable
      (intervalDomainLift u0) (intervalMeasure 1)) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) ↦
          p.ν * intervalDomainLift (D.u t) x ^ p.γ))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hu := conjugateMildM_jointValue_u D hu0_bound hu0_meas
  exact continuousOn_const.mul
    (hu.rpow_const (fun _ _ => Or.inr p.hγ.le))

/-- Every canonical resolver source coefficient is continuous throughout the
faithful solution's strict-positive-time interval. -/
theorem conjugateMildM_resolverSourceCoeff_continuousOn_Ioo
    {p : CM2Params} {u0 : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u0)
    (hu0_bound : ∀ y, |intervalDomainLift u0 y| ≤ D.M)
    (hu0_meas : AEStronglyMeasurable
      (intervalDomainLift u0) (intervalMeasure 1))
    (k : ℕ) :
    ContinuousOn
      (fun s : ℝ => (intervalNeumannResolverSourceCoeff p (D.u s) k).re)
      (Set.Ioo (0 : ℝ) D.T) := by
  have hsource := conjugateMildM_resolverPowerSource_jointContinuousOn
    D hu0_bound hu0_meas
  intro s hs
  let a : ℝ := s / 2
  let b : ℝ := (s + D.T) / 2
  have ha : 0 < a := by
    dsimp [a]
    linarith [hs.1]
  have hbT : b < D.T := by
    dsimp [b]
    linarith [hs.2]
  have has : a < s := by
    dsimp [a]
    linarith [hs.1]
  have hsb : s < b := by
    dsimp [b]
    linarith [hs.2]
  have hsab : s ∈ Set.Icc a b := ⟨has.le, hsb.le⟩
  have hsub :
      Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1 ⊆
        Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro q hq
    obtain ⟨ht, hx⟩ := Set.mem_prod.mp hq
    exact Set.mem_prod.mpr
      ⟨⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hbT⟩, hx⟩
  have hcoeffCos : ContinuousOn
      (fun r : ℝ => cosineCoeffs
        (fun x : ℝ => p.ν * intervalDomainLift (D.u r) x ^ p.γ) k)
      (Set.Icc a b) :=
    cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
      (f := fun r x => p.ν * intervalDomainLift (D.u r) x ^ p.γ)
      (c := a) (T := b) k (hsource.mono hsub)
  have hcoeff : ContinuousOn
      (fun r : ℝ => (intervalNeumannResolverSourceCoeff p (D.u r) k).re)
      (Set.Icc a b) := by
    simpa [intervalNeumannResolverSourceCoeff, cosineCoeffs,
      Complex.ofReal_re] using hcoeffCos
  have hlocal : Set.Ioo a b ∈ 𝓝 s := Ioo_mem_nhds has hsb
  have hnh : Set.Icc a b ∈ 𝓝[Set.Ioo (0 : ℝ) D.T] s := by
    have hinter : Set.Ioo (0 : ℝ) D.T ∩ Set.Ioo a b ∈
        𝓝[Set.Ioo (0 : ℝ) D.T] s :=
      inter_mem_nhdsWithin _ hlocal
    exact mem_of_superset hinter (by
      intro y hy
      exact ⟨hy.2.1.le, hy.2.2.le⟩)
  exact (hcoeff.continuousWithinAt hsab).mono_of_mem_nhdsWithin hnh

/-- The canonical resolver source modes have one uniform bound on the whole
strict-positive-time interval. -/
theorem conjugateMildM_resolverSourceCoeff_uniform_bound
    {p : CM2Params} {u0 : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u0)
    (hu0_bound : ∀ y, |intervalDomainLift u0 y| ≤ D.M)
    (hu0_meas : AEStronglyMeasurable
      (intervalDomainLift u0) (intervalMeasure 1)) :
    ∀ s ∈ Set.Ioo (0 : ℝ) D.T, ∀ k,
      |(intervalNeumannResolverSourceCoeff p (D.u s) k).re| ≤
        2 * (p.ν * D.M ^ p.γ) := by
  have hsource := conjugateMildM_resolverPowerSource_jointContinuousOn
    D hu0_bound hu0_meas
  intro s hs k
  have hsec : ContinuousOn
      (fun x : ℝ => p.ν * intervalDomainLift (D.u s) x ^ p.γ)
      (Set.Icc (0 : ℝ) 1) := by
    have hmaps : Set.MapsTo (fun x : ℝ => ((s, x) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1)
        (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) :=
      fun x hx => Set.mem_prod.mpr ⟨hs, hx⟩
    have hcomp := hsource.comp
      (continuousOn_const.prodMk continuousOn_id) hmaps
    simpa [Function.uncurry] using hcomp
  have hBnn : 0 ≤ p.ν * D.M ^ p.γ :=
    mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _)
  have hsrcBound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |p.ν * intervalDomainLift (D.u s) x ^ p.γ| ≤
        p.ν * D.M ^ p.γ := by
    intro x hx
    have hpos : 0 < intervalDomainLift (D.u s) x := by
      simp only [intervalDomainLift, dif_pos hx]
      exact D.hc.trans_le (D.hfloor s hs.1 hs.2.le ⟨x, hx⟩)
    have hubAbs : |intervalDomainLift (D.u s) x| ≤ D.M := by
      simpa [intervalDomainLift, hx] using
        D.hbound s hs.1 hs.2.le ⟨x, hx⟩
    have hub : intervalDomainLift (D.u s) x ≤ D.M := by
      simpa [abs_of_pos hpos] using hubAbs
    have hpow : intervalDomainLift (D.u s) x ^ p.γ ≤ D.M ^ p.γ :=
      Real.rpow_le_rpow hpos.le hub p.hγ.le
    rw [abs_mul, abs_of_pos p.hν,
      abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
    exact mul_le_mul_of_nonneg_left hpow p.hν.le
  have hcos := cosineCoeffs_abs_le_of_continuous_bounded
    hsec hBnn hsrcBound k
  simpa [intervalNeumannResolverSourceCoeff, cosineCoeffs,
    Complex.ofReal_re] using hcos

/-- The actual elliptically coupled chemical concentration is jointly
continuous on the strict-positive-time closed spatial slab. -/
theorem conjugateMildM_jointValue_v
    {p : CM2Params} {u0 : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u0)
    (hu0_bound : ∀ y, |intervalDomainLift u0 y| ≤ D.M)
    (hu0_meas : AEStronglyMeasurable
      (intervalDomainLift u0) (intervalMeasure 1)) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) ↦
          intervalDomainLift (coupledChemicalConcentration p D.u t) x))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hseries := resolverWeightedCosineSeries_continuousOn_prod_Icc
    p
    (a := fun s k => (intervalNeumannResolverSourceCoeff p (D.u s) k).re)
    (A := 2 * (p.ν * D.M ^ p.γ))
    (fun k => conjugateMildM_resolverSourceCoeff_continuousOn_Ioo
      D hu0_bound hu0_meas k)
    (conjugateMildM_resolverSourceCoeff_uniform_bound
      D hu0_bound hu0_meas)
  refine hseries.congr (fun q hq => ?_)
  obtain ⟨ht, hx⟩ := Set.mem_prod.mp hq
  have hphysical :=
    ShenWork.Paper2.RegularityFrontierAssembly.mildChemicalConcentration_eq_sourceWeight_series
      p D.u q.1 ⟨q.2, hx⟩
  simpa [Function.uncurry, intervalDomainLift, hx,
    coupledChemicalConcentration,
    ShenWork.IntervalMildToClassical.mildChemicalConcentration] using
      hphysical

/-- The faithful mild solution and its actual elliptic resolver discharge
exactly the two halves of `IntervalClassicalRegularityAtoms.jointValue`. -/
theorem conjugateMildM_coupled_jointValue
    {p : CM2Params} {u0 : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u0)
    (hu0_bound : ∀ y, |intervalDomainLift u0 y| ≤ D.M)
    (hu0_meas : AEStronglyMeasurable
      (intervalDomainLift u0) (intervalMeasure 1)) :
    ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (D.u t) x))
        (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) ∧
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            intervalDomainLift (coupledChemicalConcentration p D.u t) x))
        (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) :=
  ⟨conjugateMildM_jointValue_u D hu0_bound hu0_meas,
    conjugateMildM_jointValue_v D hu0_bound hu0_meas⟩

end ShenWork.Paper2

#print axioms ShenWork.Paper2.conjugateMildM_resolverPowerSource_jointContinuousOn
#print axioms ShenWork.Paper2.conjugateMildM_resolverSourceCoeff_continuousOn_Ioo
#print axioms ShenWork.Paper2.conjugateMildM_resolverSourceCoeff_uniform_bound
#print axioms ShenWork.Paper2.conjugateMildM_jointValue_v
#print axioms ShenWork.Paper2.conjugateMildM_coupled_jointValue
