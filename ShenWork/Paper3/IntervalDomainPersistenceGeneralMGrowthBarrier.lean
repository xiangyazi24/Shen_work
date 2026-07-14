import ShenWork.Paper3.IntervalDomainPersistenceGeneralMGrowthDini
import ShenWork.Paper3.IntervalDomainPersistenceGeneralMSupport
import ShenWork.Paper3.ScalarPositiveBarrierDini

open Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainMMinPersistence

namespace ShenWork.Paper3

noncomputable section

/-- A tail ceiling supplies the baseline Dini field, while a smaller ceiling
only at contacts with a positive constant supplies strict inward motion.
Consequently the faithful general-`m` spatial minimum never crosses that
constant downwards. -/
theorem intervalDomainM_spatialMin_ge_of_contact_small_ceiling
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v)
    {T0 Mbase Msmall c : ℝ}
    (hT0 : 0 < T0) (hMbase : 0 ≤ Mbase) (hMsmall : 0 ≤ Msmall)
    (hc : 0 < c) (hgrowth : 0 < generalMMinGrowthRate p Msmall)
    (hbase : ∀ t, T0 ≤ t → ∀ y,
      |intervalDomainLift (u t) y| ≤ Mbase)
    (hsmall : ∀ t, T0 ≤ t → intervalDomainSpatialMin u t = c →
      ∀ y, |intervalDomainLift (u t) y| ≤ Msmall)
    (hinit : c ≤ intervalDomainSpatialMin u T0) :
    ∀ t, T0 ≤ t → c ≤ intervalDomainSpatialMin u t := by
  have hbaseD : RightLowerDiniGE (intervalDomainSpatialMin u)
      (fun z => generalMMinGrowthRate p Mbase * z) (Set.Ici T0) := by
    apply intervalDomainM_generalMGrowthRightLowerDiniGE_on hm hsol
      (I := Set.Ici T0) (M := Mbase)
    · intro t ht
      exact lt_of_lt_of_le hT0 ht
    · exact hMbase
    · intro t ht
      exact hbase t ht
  have hcontactD : RightLowerDiniGE (intervalDomainSpatialMin u)
      (fun z => generalMMinGrowthRate p Msmall * z)
      {t : ℝ | T0 ≤ t ∧ intervalDomainSpatialMin u t = c} := by
    apply intervalDomainM_generalMGrowthRightLowerDiniGE_on hm hsol
      (I := {t : ℝ | T0 ≤ t ∧ intervalDomainSpatialMin u t = c})
      (M := Msmall)
    · intro t ht
      exact lt_of_lt_of_le hT0 ht.1
    · exact hMsmall
    · intro t ht
      exact hsmall t ht.1 ht.2
  intro t ht
  have hcont := intervalDomainM_spatialMin_continuousOn
    hsol hT0 ht
  exact positive_constant_barrier_of_contact_RightLowerDiniGE
    (z := intervalDomainSpatialMin u)
    (k := generalMMinGrowthRate p Msmall)
    (kbase := generalMMinGrowthRate p Mbase)
    hc hgrowth hcont hinit hbaseD hcontactD t
      (Set.right_mem_Icc.mpr ht)

end

end ShenWork.Paper3

#print axioms
  ShenWork.Paper3.intervalDomainM_spatialMin_ge_of_contact_small_ceiling
