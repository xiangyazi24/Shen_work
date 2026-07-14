import ShenWork.Paper3.GeneralMScalarDiniExact
import ShenWork.Paper3.IntervalDomainPersistenceGeneralMElliptic

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

/-- Paper 3 Theorem 2.1(3), faithfully using the `u^m` interval flux. -/
theorem intervalDomainM_part3_liminfUV_proven
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ} {T0 : ℝ}
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : 1 < p.m) (hβ : 1 ≤ p.β)
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hT0 : 0 < T0) :
    theorem21Part3LowerU p ≤ liminfInfValue intervalDomainM u ∧
      p.ν / p.μ * theorem21Part3LowerU p ^ p.γ ≤
        liminfInfValue intervalDomainM v := by
  have hDini : GeneralMSpatialMinimumDini p u :=
    intervalDomainM_generalMSpatialMinimumDini hχ0.le hβ hsol
  have hD : RightLowerDiniGE (intervalDomainSpatialMin u)
      (generalMLogisticRhs p) (Set.Ioi (0 : ℝ)) :=
    hDini.to_RightLowerDiniGE
      (intervalDomainM_spatialMin_slope_isBoundedUnder hsol)
  have huSpatial : theorem21Part3LowerU p ≤
      Filter.liminf (intervalDomainSpatialMin u) atTop :=
    generalM_liminf_ge_of_RightLowerDiniGE
      ha hb hχ0 hm hβ
      (fun T hT0T => intervalDomainM_spatialMin_continuousOn hsol hT0 hT0T)
      hD hT0 (intervalDomainM_spatialMin_pos hsol hT0)
      (by
        simpa [intervalDomainSpatialMin, intervalDomainM] using
          intervalDomainM_infValue_isCoboundedUnder hsol)
  have hu : theorem21Part3LowerU p ≤ liminfInfValue intervalDomainM u := by
    simpa [liminfInfValue, intervalDomainSpatialMin, intervalDomainM] using
      huSpatial
  have hlowerPos : 0 < theorem21Part3LowerU p := by
    simpa [theorem21Part3LowerU] using
      theorem_2_1_part3_lowerU_pos p ha hb hχ0 hm hβ
  exact ⟨hu,
    intervalDomainM_liminf_v_ge_of_u_liminf_lower hsol hlowerPos hu⟩

theorem intervalDomainM_uniformPersistencePart3Raw_proven
    {p : CM2Params} :
    UniformPersistencePart3Raw intervalDomainM p := by
  intro ha hb hχ0 hm hβ u v hsol
  simpa [theorem21Part3LowerU] using
    intervalDomainM_part3_liminfUV_proven
      ha hb hχ0 hm hβ hsol (T0 := 1) one_pos

theorem Theorem_2_1_part3_intervalDomainM_proven
    (p : CM2Params) :
    Theorem_2_1_part3 intervalDomainM p := by
  exact intervalDomainM_uniformPersistencePart3Raw_proven

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomainM_part3_liminfUV_proven
#print axioms ShenWork.Paper3.intervalDomainM_uniformPersistencePart3Raw_proven
#print axioms ShenWork.Paper3.Theorem_2_1_part3_intervalDomainM_proven
