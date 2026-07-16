/- Joint positive-time continuity of a faithful general-`m` Laplacian representative. -/
import ShenWork.Paper3.IntervalDomainMClassicalRestartMildData
import ShenWork.Paper3.IntervalDomainStrongSliceMembershipGeneralM
import ShenWork.Paper2.IntervalDomainMConjugateMildChemDivJointContinuity

namespace ShenWork.Paper3

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainMMinPersistence
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1LiftDeriv2Transfer
open ShenWork.IntervalCoupledRegularityBootstrap

noncomputable section

/-- On every compact strict-positive-time slab, the faithful general-`m`
population Laplacian has a jointly continuous closed-spatial-interval
representative which agrees with the literal second derivative in the spatial
interior. -/
theorem exists_paper3UxxPhysicalRepGeneralM_continuousOn_strictSlab
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {T a b : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    ∃ F : ℝ → ℝ → ℝ,
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) ∧
      ∀ t ∈ Set.Icc a b, ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        F t x = liftDeriv2 u t x := by
  let a₀ : ℝ := a / 2
  let h : ℝ := (b + T - a) / 2
  have ha₀ : 0 < a₀ := by
    dsimp [a₀]
    linarith
  have hh : 0 < h := by
    dsimp [h]
    linarith
  have ha₀hT : a₀ + h < T := by
    dsimp [a₀, h]
    linarith
  obtain ⟨D, hDT, hDu⟩ :=
    intervalDomainM_classicalRestartMildData_exists p hsol ha₀ hh ha₀hT
  have hu₀_bound : ∀ y, |intervalDomainLift (u a₀) y| ≤ D.M := by
    intro y
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · simpa [intervalDomainLift, hy] using D.datum_bound ⟨y, hy⟩
    · simp [intervalDomainLift, hy, D.hM.le]
  have hu₀_cont : Continuous (u a₀) :=
    solutionSlice_continuous hsol ⟨ha₀, by linarith⟩
  have hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift (u a₀)) (intervalMeasure 1) :=
    (ShenWork.IntervalMildPicardThreshold.intervalDomainLift_measurable_of_continuous'
      hu₀_cont).aestronglyMeasurable
  let chemRep : ℝ → ℝ → ℝ := fun t x =>
    conjugateMildMChemDivJointRep p D.u (t - a₀) x
  let F : ℝ → ℝ → ℝ :=
    liftDeriv2PhysicalRHSWithChemRep p u chemRep
  have hrange : ∀ t ∈ Set.Icc a b,
      t - a₀ ∈ Set.Ioo (0 : ℝ) D.T := by
    intro t ht
    constructor
    · dsimp [a₀]
      linarith [ht.1]
    · rw [hDT]
      dsimp [a₀, h]
      linarith [ht.2]
  have hchem : ContinuousOn (Function.uncurry chemRep)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
    have hjoint := conjugateMildMChemDivJointRep_jointContinuousOn
      D hu₀_bound hu₀_meas
    have hmap : Continuous
        (fun q : ℝ × ℝ => (q.1 - a₀, q.2)) :=
      (continuous_fst.sub continuous_const).prodMk continuous_snd
    have hmaps : Set.MapsTo (fun q : ℝ × ℝ => (q.1 - a₀, q.2))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)
        (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
      intro q hq
      exact ⟨hrange q.1 hq.1, hq.2⟩
    simpa [chemRep, Function.comp_def, Function.uncurry] using
      hjoint.comp hmap.continuousOn hmaps
  have htime : ContinuousOn
      (Function.uncurry (fun t x => liftTimeDeriv u t x))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
    refine hsol.regularity.2.2.2.2.2.1.1.mono (Set.prod_mono ?_ Subset.rfl)
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hbT⟩
  have hu : ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
    refine hsol.regularity.2.2.2.2.2.2.1.mono (Set.prod_mono ?_ Subset.rfl)
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hbT⟩
  have hupos : ∀ q ∈ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (u q.1) q.2 := by
    intro q hq
    rw [intervalDomainLift, dif_pos hq.2]
    exact hsol.u_pos' (lt_of_lt_of_le ha hq.1.1)
      (lt_of_le_of_lt hq.1.2 hbT)
  have hupow : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2 ^ p.α)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    hu.rpow_const (fun q hq => Or.inl (hupos q hq).ne')
  have hreact : ContinuousOn
      (Function.uncurry
        (fun t x => intervalDomainLift (u t) x *
          (p.a - p.b * intervalDomainLift (u t) x ^ p.α)))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
    simpa [Function.uncurry] using
      hu.mul (continuousOn_const.sub (hupow.const_mul p.b))
  have hF : ContinuousOn (Function.uncurry F)
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
    exact liftDeriv2PhysicalRHSWithChemRep_continuousOn_of_components
      htime hchem hreact
  refine ⟨F, hF, ?_⟩
  intro t ht x hx
  have htT : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hbT⟩
  have hr := hrange t ht
  have hrIcc : t - a₀ ∈ Set.Icc (0 : ℝ) h := by
    rw [hDT] at hr
    exact ⟨hr.1.le, hr.2.le⟩
  have htraj : D.u (t - a₀) = u t := by
    rw [hDu, classicalRestartTrajectoryM_eq hrIcc]
    congr 1
    ring
  have hV : intervalDomainLift
      (coupledChemicalConcentration p D.u (t - a₀)) x =
        intervalDomainLift (v t) x := by
    have hv := solution_v_eq_resolver_pointwiseM hsol htT hx
    change intervalDomainLift
      (ShenWork.PDE.intervalNeumannResolverR p (D.u (t - a₀))) x = _
    rw [htraj]
    simpa [intervalDomainLift, Set.Ioo_subset_Icc_self hx] using hv
  have hDV : deriv (intervalDomainLift
      (coupledChemicalConcentration p D.u (t - a₀))) x =
        deriv (intervalDomainLift (v t)) x := by
    have hD := conjugateMildM_coupledChemical_deriv_eq_resolverGradReal_Icc
      D hu₀_bound hu₀_meas hr.1 hr.2.le
        (Set.Ioo_subset_Icc_self hx)
    have hv := solution_lift_v_deriv_eq_resolverGrad_IccM hsol htT
      (Set.Ioo_subset_Icc_self hx)
    rw [htraj] at hD
    exact hD.trans hv.symm
  have hchemEq : chemRep t x =
      classicalChemDivMPhysicalRep p u v t x := by
    dsimp [chemRep]
    unfold conjugateMildMChemDivJointRep classicalChemDivMPhysicalRep
    dsimp only
    rw [htraj, hV, hDV]
  calc
    F t x = paper3UxxPhysicalRepGeneralM p u v t x := by
      simp [F, paper3UxxPhysicalRepGeneralM,
        liftDeriv2PhysicalRHSWithChemRep, hchemEq]
    _ = liftDeriv2 u t x :=
      paper3UxxPhysicalRepGeneralM_eq_liftDeriv2_interior hsol htT hx

#print axioms exists_paper3UxxPhysicalRepGeneralM_continuousOn_strictSlab

end

end ShenWork.Paper3
