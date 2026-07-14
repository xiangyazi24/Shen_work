import ShenWork.Paper3.IntervalDomainGlobalTailHolderM
import ShenWork.Paper3.IntervalDomainPersistenceGeneralMGrowthBarrier
import ShenWork.Paper3.IntervalDomainPersistenceGeneralMElliptic
import ShenWork.Paper3.IntervalDomainPersistencePart1StatementObstruction

open Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainMMinPersistence

namespace ShenWork.Paper3

noncomputable section

/-- The sole compactness/strong-maximum input needed by the faithful
positive-logistic first-crossing argument: on the orbit tail, a sufficiently
small spatial minimum forces the whole slice below any prescribed ceiling. -/
def IntervalDomainMContactSmallCeiling
    (u : ℝ → intervalDomain.Point → ℝ) : Prop :=
  ∀ eps > 0, ∃ T > 0, ∃ delta > 0,
    ∀ t, T ≤ t → intervalDomainSpatialMin u t ≤ delta →
      ∀ y, |intervalDomainLift (u t) y| ≤ eps

/-- The compactness leaf together with the faithful ceiling-conditioned Dini
estimate yields a genuine eventual pointwise floor for `u`. -/
theorem intervalDomainM_eventually_u_lower_of_contactSmallCeiling
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (ha : 0 < p.a) (hm : 1 ≤ p.m)
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hsmall : IntervalDomainMContactSmallCeiling u) :
    ∃ c > 0, ∀ᶠ t in atTop, ∀ x : intervalDomain.Point, c ≤ u t x := by
  obtain ⟨Msmall, hMsmall, hgrowth⟩ :=
    exists_pos_generalMMinGrowthRate p hm ha
  obtain ⟨Tsmall, hTsmall, delta, hdelta, hsmall'⟩ :=
    hsmall Msmall hMsmall
  obtain ⟨Ttail, Mbase, _G, hTtail, hMbase, _hG, hsup, _hholder⟩ :=
    intervalDomainM_globalBounded_eventual_holder p hsol
  let T0 : ℝ := max Tsmall Ttail
  have hT0 : 0 < T0 := hTsmall.trans_le (le_max_left _ _)
  have hTsmallT0 : Tsmall ≤ T0 := le_max_left _ _
  have hTtailT0 : Ttail ≤ T0 := le_max_right _ _
  have hbase : ∀ t, T0 ≤ t → ∀ y,
      |intervalDomainLift (u t) y| ≤ Mbase := by
    intro t ht y
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · have htpos : 0 < t := lt_of_lt_of_le hT0 ht
      have hclass := hsol.classical.classical (T := t + 1) (by linarith)
      exact (intervalDomainM_abs_lift_le_supNorm hclass
        ⟨htpos, by linarith⟩ hy).trans
          (hsup t (hTtailT0.trans ht))
    · simp [intervalDomainLift, hy, hMbase.le]
  have hminT0 : 0 < intervalDomainSpatialMin u T0 :=
    intervalDomainM_spatialMin_pos hsol hT0
  let c : ℝ := min (delta / 2) (intervalDomainSpatialMin u T0 / 2)
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min (half_pos hdelta) (half_pos hminT0)
  have hc_delta : c ≤ delta := by
    calc
      c ≤ delta / 2 := min_le_left _ _
      _ ≤ delta := by linarith
  have hc_init : c ≤ intervalDomainSpatialMin u T0 := by
    calc
      c ≤ intervalDomainSpatialMin u T0 / 2 := min_le_right _ _
      _ ≤ intervalDomainSpatialMin u T0 := by linarith
  have hcontact : ∀ t, T0 ≤ t → intervalDomainSpatialMin u t = c →
      ∀ y, |intervalDomainLift (u t) y| ≤ Msmall := by
    intro t ht hmin
    apply hsmall' t (hTsmallT0.trans ht)
    rw [hmin]
    exact hc_delta
  have hfloor : ∀ t, T0 ≤ t → c ≤ intervalDomainSpatialMin u t :=
    intervalDomainM_spatialMin_ge_of_contact_small_ceiling hm hsol
      hT0 hMbase.le hMsmall.le hc hgrowth hbase hcontact hc_init
  refine ⟨c, hc, ?_⟩
  have H := intervalDomainM_generalM_compactMinFamily (p := p) (v := v) hsol
  filter_upwards [eventually_ge_atTop T0] with t ht x
  have htpos : 0 < t := lt_of_lt_of_le hT0 ht
  have hzle := H.z_le t x.1 x.2
  have hmin_le : intervalDomainSpatialMin u t ≤ u t x := by
    simpa [intervalDomainActualLinearDanskinF, htpos,
      intervalDomainLift] using hzle
  exact (hfloor t ht).trans hmin_le

/-- Faithful positive-logistic branch of corrected Paper 3 Theorem 2.1(1),
reduced to the concrete contact-small-ceiling compactness producer. -/
theorem intervalDomainM_positiveLogistic_part1_of_contactSmallCeiling
    (p : CM2Params) (ha : 0 < p.a) (_hb : 0 < p.b) (hm : 1 ≤ p.m)
    (hcompact : ∀ u v : ℝ → intervalDomain.Point → ℝ,
      PositiveGlobalBoundedSolution intervalDomainM p u v →
        IntervalDomainMContactSmallCeiling u) :
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      PositiveGlobalBoundedSolution intervalDomainM p u v →
        ∃ deltaU > 0,
          deltaU ≤ liminfInfValue intervalDomainM u ∧
          p.ν / p.μ * (liminfInfValue intervalDomainM u) ^ p.γ ≤
            liminfInfValue intervalDomainM v := by
  intro u v hsol
  obtain ⟨deltaU, hdeltaU, huPoint⟩ :=
    intervalDomainM_eventually_u_lower_of_contactSmallCeiling
      ha hm hsol (hcompact u v hsol)
  have huLowerLegacy : EventuallyLowerBound intervalDomain u deltaU :=
    intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower
      hdeltaU huPoint
  have huLowerM : EventuallyLowerBound intervalDomainM u deltaU := by
    simpa [EventuallyLowerBound, intervalDomain, intervalDomainM] using
      huLowerLegacy
  have huLiminf : deltaU ≤ liminfInfValue intervalDomainM u :=
    liminf_ge_of_eventuallyLowerBound
      (intervalDomainM_infValue_isCoboundedUnder hsol) huLowerM
  have huLiminfPos : 0 < liminfInfValue intervalDomainM u :=
    hdeltaU.trans_le huLiminf
  have hvLiminf := intervalDomainM_liminf_v_ge_of_u_liminf_lower
    hsol huLiminfPos (le_refl _)
  exact ⟨deltaU, hdeltaU, huLiminf, hvLiminf⟩

end

end ShenWork.Paper3

#print axioms
  ShenWork.Paper3.intervalDomainM_eventually_u_lower_of_contactSmallCeiling
#print axioms
  ShenWork.Paper3.intervalDomainM_positiveLogistic_part1_of_contactSmallCeiling
