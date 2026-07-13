/-
  Joint positive-time continuity of the physical post-IBP chemotaxis source.

  The only missing component in the product-rule representative is the joint
  continuity of the resolver gradient.  It is obtained without source-time
  regularity or a classical-solution package: joint continuity of the resolver
  value and the weak bounded-data spatial Holder estimate feed the generic
  parametric secant-slope bridge.
-/
import ShenWork.Paper2.IntervalDomainMConjugateMildJointSpatialDerivativeClosed
import ShenWork.Paper2.IntervalDomainMConjugateMildCoupledJointValue
import ShenWork.Paper2.IntervalDomainMConjugateMildClosedSpatial
import ShenWork.Paper2.IntervalDomainMConjugateMildPositiveTimeFluxC1eta
import ShenWork.Paper2.IntervalJointContinuityUniformTrace

open MeasureTheory Filter Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainChemotaxisDivM intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap (chemFluxMLifted)
open ShenWork.IntervalResolverWeakBounds
  (intervalNeumannResolverGradHolderWeight
    intervalNeumannResolverR_lift_hasDerivAt_resolverGradReal_of_continuousOn
    resolverGradReal_holder_Icc_of_bounded_smallTheta)

/-- On the whole physical closed interval, the ordinary derivative of the
actual coupled resolver value agrees with the weak resolver-gradient series.
The interior is the weak continuous-source derivative bridge; at the two
endpoints both sides are zero. -/
theorem conjugateMildM_coupledChemical_deriv_eq_resolverGradReal_Icc
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    deriv (intervalDomainLift (coupledChemicalConcentration p D.u t)) x =
      resolverGradReal p (D.u t) x := by
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · subst x
    rw [(conjugateMildM_coupledChemical_closedC2_endpointDerivs
      D hu₀_bound hu₀_meas ht htT).2.1, resolverGradReal_zero]
  · rcases eq_or_lt_of_le hx.2 with hx1 | hx1
    · subst x
      rw [(conjugateMildM_coupledChemical_closedC2_endpointDerivs
        D hu₀_bound hu₀_meas ht htT).2.2, resolverGradReal_one]
    · have hUcont : ContinuousOn (intervalDomainLift (D.u t))
          (Set.Icc (0 : ℝ) 1) := by
        rw [continuousOn_iff_continuous_restrict]
        have heq : Set.restrict (Set.Icc (0 : ℝ) 1)
            (intervalDomainLift (D.u t)) = D.u t := by
          ext ⟨z, hz⟩
          simp [Set.restrict, intervalDomainLift, hz]
          rfl
        rw [heq]
        exact D.hcont t ht htT
      have hraw :=
        intervalNeumannResolverR_lift_hasDerivAt_resolverGradReal_of_continuousOn
          p hUcont ⟨hx0, hx1⟩
      simpa [coupledChemicalConcentration] using hraw.deriv

/-- The ordinary spatial derivative of the actual coupled chemical
concentration is jointly continuous at strict positive times, including both
spatial endpoints. -/
theorem conjugateMildM_jointSpatialDeriv_v_closed
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1)) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) ↦
          deriv (intervalDomainLift
            (coupledChemicalConcentration p D.u t)) x))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  let K : ℝ :=
    (2 : ℝ) ^ (1 - (1 / 4 : ℝ)) *
      Real.sqrt (∑' k : ℕ,
        (intervalNeumannResolverGradHolderWeight p (1 / 4 : ℝ) k) ^ 2) *
      (2 * (p.ν * D.M ^ p.γ))
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
        (Real.sqrt_nonneg _))
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _)))
  apply parametricSpatialDeriv_jointContinuousOn_of_uniformHolder
    (K := K) (theta := (1 / 4 : ℝ)) hK (by norm_num)
  · exact conjugateMildM_jointValue_v D hu₀_bound hu₀_meas
  · intro t ht
    exact (conjugateMildM_coupledChemical_contDiffOn_two_interior
      D hu₀_bound hu₀_meas ht.1 ht.2.le).differentiableOn (by norm_num)
  · intro t ht x hx y hy
    rw [conjugateMildM_coupledChemical_deriv_eq_resolverGradReal_Icc
      D hu₀_bound hu₀_meas ht.1 ht.2.le hx,
      conjugateMildM_coupledChemical_deriv_eq_resolverGradReal_Icc
        D hu₀_bound hu₀_meas ht.1 ht.2.le hy]
    have hUcont : ContinuousOn (intervalDomainLift (D.u t))
        (Set.Icc (0 : ℝ) 1) := by
      rw [continuousOn_iff_continuous_restrict]
      have heq : Set.restrict (Set.Icc (0 : ℝ) 1)
          (intervalDomainLift (D.u t)) = D.u t := by
        ext ⟨z, hz⟩
        simp [Set.restrict, intervalDomainLift, hz]
        rfl
      rw [heq]
      exact D.hcont t ht.1 ht.2.le
    have hlb : ∀ z ∈ Set.Icc (0 : ℝ) 1,
        0 ≤ intervalDomainLift (D.u t) z := by
      intro z hz
      simpa [intervalDomainLift, hz] using
        D.hc.le.trans (D.hfloor t ht.1 ht.2.le ⟨z, hz⟩)
    have hub : ∀ z ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift (D.u t) z ≤ D.M := by
      intro z hz
      have h := D.hbound t ht.1 ht.2.le ⟨z, hz⟩
      simpa [intervalDomainLift, hz] using (abs_le.mp h).2
    dsimp [K]
    exact resolverGradReal_holder_Icc_of_bounded_smallTheta
      p (by norm_num) (by norm_num) hUcont hlb hub hx hy
  · intro t ht
    exact (conjugateMildM_coupledChemical_closedC2_endpointDerivs
      D hu₀_bound hu₀_meas ht.1 ht.2.le).2.1
  · intro t ht
    exact (conjugateMildM_coupledChemical_closedC2_endpointDerivs
      D hu₀_bound hu₀_meas ht.1 ht.2.le).2.2

/-- Ordinary-derivative product-rule representative of the physical
post-integration-by-parts source `Q_x`.  Its endpoint values are the continuous
physical extensions of the interior source. -/
def conjugateMildMChemDivJointRep (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  let U := intervalDomainLift (u t)
  let V := intervalDomainLift (coupledChemicalConcentration p u t)
  (p.m * U x ^ (p.m - 1) * deriv U x) * deriv V x *
      (1 + V x) ^ (-p.β) +
    U x ^ p.m * (p.μ * V x - p.ν * U x ^ p.γ) *
      (1 + V x) ^ (-p.β) -
    p.β * U x ^ p.m * (deriv V x) ^ 2 *
      (1 + V x) ^ (-p.β - 1)

/-- The physical `Q_x` representative is jointly continuous on the whole
strict-positive-time closed spatial slab. -/
theorem conjugateMildMChemDivJointRep_jointContinuousOn
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1)) :
    ContinuousOn
      (Function.uncurry (conjugateMildMChemDivJointRep p D.u))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  let S := Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1
  have hu : ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) ↦ intervalDomainLift (D.u t) x)) S :=
    conjugateMildM_jointValue_u D hu₀_bound hu₀_meas
  have hdu : ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) ↦ deriv (intervalDomainLift (D.u t)) x)) S :=
    conjugateMildM_jointSpatialDeriv_closed D hu₀_bound hu₀_meas
  have hv : ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) ↦
          intervalDomainLift (coupledChemicalConcentration p D.u t) x)) S :=
    conjugateMildM_jointValue_v D hu₀_bound hu₀_meas
  have hdv : ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) ↦ deriv
          (intervalDomainLift (coupledChemicalConcentration p D.u t)) x)) S :=
    conjugateMildM_jointSpatialDeriv_v_closed D hu₀_bound hu₀_meas
  have hv_nonneg : ∀ q ∈ S,
      0 ≤ intervalDomainLift
        (coupledChemicalConcentration p D.u q.1) q.2 := by
    intro q hq
    obtain ⟨ht, hx⟩ := Set.mem_prod.mp hq
    have h := ShenWork.IntervalMildToClassical.mildChemical_nonneg
      (T := D.T) p (u := D.u)
        (fun s hs hsT y => D.hc.le.trans (D.hfloor s hs hsT y)) D.hcont
        ht.1 ht.2.le ⟨q.2, hx⟩
    simpa [coupledChemicalConcentration,
      ShenWork.IntervalMildToClassical.mildChemicalConcentration,
      intervalDomainLift, hx] using h
  have hbase : ContinuousOn
      (fun q : ℝ × ℝ => 1 + intervalDomainLift
        (coupledChemicalConcentration p D.u q.1) q.2) S :=
    continuousOn_const.add hv
  have hden : ContinuousOn
      (fun q : ℝ × ℝ =>
        (1 + intervalDomainLift
          (coupledChemicalConcentration p D.u q.1) q.2) ^ (-p.β)) S :=
    hbase.rpow_const (fun q hq => Or.inl (by
      have := hv_nonneg q hq
      linarith))
  have hden_one : ContinuousOn
      (fun q : ℝ × ℝ =>
        (1 + intervalDomainLift
          (coupledChemicalConcentration p D.u q.1) q.2) ^ (-p.β - 1)) S :=
    hbase.rpow_const (fun q hq => Or.inl (by
      have := hv_nonneg q hq
      linarith))
  have hu_pow : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (D.u q.1) q.2 ^ p.γ) S :=
    hu.rpow_const (fun _ _ => Or.inr p.hγ.le)
  have hu_pos : ∀ q ∈ S, 0 < intervalDomainLift (D.u q.1) q.2 := by
    intro q hq
    obtain ⟨ht, hx⟩ := Set.mem_prod.mp hq
    simpa [intervalDomainLift, hx] using
      D.hc.trans_le (D.hfloor q.1 ht.1 ht.2.le ⟨q.2, hx⟩)
  have hu_m : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (D.u q.1) q.2 ^ p.m) S :=
    hu.rpow_const (fun _ _ => Or.inr p.hm.le)
  have hu_m1 : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (D.u q.1) q.2 ^ (p.m - 1)) S :=
    hu.rpow_const (fun q hq => Or.inl (hu_pos q hq).ne')
  have hphysical : ContinuousOn
      (fun q : ℝ × ℝ =>
        p.μ * intervalDomainLift
            (coupledChemicalConcentration p D.u q.1) q.2 -
          p.ν * intervalDomainLift (D.u q.1) q.2 ^ p.γ) S :=
    (continuousOn_const.mul hv).sub (continuousOn_const.mul hu_pow)
  have hterm1 : ContinuousOn
      (fun q : ℝ × ℝ =>
        (p.m * intervalDomainLift (D.u q.1) q.2 ^ (p.m - 1) *
          deriv (intervalDomainLift (D.u q.1)) q.2) *
          deriv (intervalDomainLift
            (coupledChemicalConcentration p D.u q.1)) q.2 *
          (1 + intervalDomainLift
            (coupledChemicalConcentration p D.u q.1) q.2) ^ (-p.β)) S :=
    (((continuousOn_const.mul hu_m1).mul hdu).mul hdv).mul hden
  have hterm2 : ContinuousOn
      (fun q : ℝ × ℝ =>
        intervalDomainLift (D.u q.1) q.2 ^ p.m *
          (p.μ * intervalDomainLift
              (coupledChemicalConcentration p D.u q.1) q.2 -
            p.ν * intervalDomainLift (D.u q.1) q.2 ^ p.γ) *
          (1 + intervalDomainLift
            (coupledChemicalConcentration p D.u q.1) q.2) ^ (-p.β)) S :=
    (hu_m.mul hphysical).mul hden
  have hterm3 : ContinuousOn
      (fun q : ℝ × ℝ =>
        p.β * intervalDomainLift (D.u q.1) q.2 ^ p.m *
          (deriv (intervalDomainLift
            (coupledChemicalConcentration p D.u q.1)) q.2) ^ 2 *
          (1 + intervalDomainLift
            (coupledChemicalConcentration p D.u q.1) q.2) ^ (-p.β - 1)) S :=
    (((continuousOn_const.mul hu_m).mul (hdv.pow 2)).mul hden_one)
  simpa [S, conjugateMildMChemDivJointRep, Function.uncurry] using
    (hterm1.add hterm2).sub hterm3

/-- At every positive-time interior point, the representative is exactly the
ordinary derivative of the actual weak chemotaxis flux. -/
theorem deriv_chemFluxMLifted_eq_conjugateMildMChemDivJointRep_interior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {t x : ℝ} (ht : 0 < t) (htT : t ≤ D.T)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (chemFluxMLifted p (D.u t)) x =
      conjugateMildMChemDivJointRep p D.u t x := by
  have hcomponents := conjugateMildM_chemFlux_deriv_eq_components
    D hu₀_bound hu₀_meas ht htT hx
  dsimp only at hcomponents
  rw [hcomponents,
    conjugateMildM_resolverGrad_deriv_eq_physical D ht htT hx]
  have hvx := conjugateMildM_coupledChemical_deriv_eq_resolverGradReal_Icc
    D hu₀_bound hu₀_meas ht htT (Set.Ioo_subset_Icc_self hx)
  rw [← hvx]
  simp only [conjugateMildMChemDivJointRep, coupledChemicalConcentration]
  ring

/-- The literal physical divergence source agrees on the open spatial
interval with the jointly continuous representative. -/
theorem intervalDomainMChemotaxisDiv_eq_conjugateMildMChemDivJointRep_interior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {t x : ℝ} (ht : 0 < t) (htT : t ≤ D.T)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomainChemotaxisDivM p (D.u t)
        (coupledChemicalConcentration p D.u t)
        ⟨x, Set.Ioo_subset_Icc_self hx⟩ =
      conjugateMildMChemDivJointRep p D.u t x := by
  have heq :
      (fun y : ℝ => intervalDomainLift (D.u t) y ^ p.m *
          deriv (intervalDomainLift
            (coupledChemicalConcentration p D.u t)) y /
          (1 + intervalDomainLift
            (coupledChemicalConcentration p D.u t) y) ^ p.β)
        =ᶠ[𝓝 x] chemFluxMLifted p (D.u t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    rw [conjugateMildM_coupledChemical_deriv_eq_resolverGradReal_Icc
      D hu₀_bound hu₀_meas ht htT (Set.Ioo_subset_Icc_self hy)]
    rfl
  unfold intervalDomainChemotaxisDivM
  rw [heq.deriv_eq]
  exact deriv_chemFluxMLifted_eq_conjugateMildMChemDivJointRep_interior
    D hu₀_bound hu₀_meas ht htT hx

/-- Function-level form of the physical-source agreement.  This has exactly
the lifted source shape used by the coupled Duhamel layer, but does not import
or assume any source-time regularity package. -/
theorem conjugateMildM_chemDivSourceLift_eq_jointRep_Ioo
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    Set.EqOn
      (intervalDomainLift (fun X : intervalDomainPoint =>
        intervalDomainChemotaxisDivM p (D.u t)
          (coupledChemicalConcentration p D.u t) X))
      (conjugateMildMChemDivJointRep p D.u t)
      (Set.Ioo (0 : ℝ) 1) := by
  intro x hx
  have hxIcc := Set.Ioo_subset_Icc_self hx
  simp only [intervalDomainLift, dif_pos hxIcc]
  exact intervalDomainMChemotaxisDiv_eq_conjugateMildMChemDivJointRep_interior
    D hu₀_bound hu₀_meas ht htT hx

/-- Joint continuity gives the spatially uniform time trace required by the
generic Duhamel differentiation theorem at every strict target time. -/
theorem conjugateMildMChemDivJointRep_uniformTrace
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t < D.T) :
    TendstoUniformlyOn (conjugateMildMChemDivJointRep p D.u)
      (conjugateMildMChemDivJointRep p D.u t) (𝓝 t)
      (Set.Icc (0 : ℝ) 1) :=
  jointContinuousOn_Ioo_prod_Icc_tendstoUniformlyOn
    (conjugateMildMChemDivJointRep_jointContinuousOn
      D hu₀_bound hu₀_meas) ⟨ht, htT⟩

/-- On every positive-time late strip, the representative has exactly the
interior spatial Holder control consumed by the generic Duhamel theorem.  No
uniform bound as the lower cutoff tends to zero is asserted. -/
theorem conjugateMildMChemDivJointRep_positiveTime_holder_uniform
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ eta H : ℝ, 0 < eta ∧ eta < 1 ∧ 0 ≤ H ∧
      ∀ t, τ ≤ t → t ≤ D.T →
        ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
          |conjugateMildMChemDivJointRep p D.u t x -
            conjugateMildMChemDivJointRep p D.u t y| ≤
              H * |x - y| ^ eta := by
  obtain ⟨eta, H, heta0, heta1, hH, hholder⟩ :=
    conjugateMildM_chemFlux_deriv_positiveTime_holder_uniform
      D hu₀_bound hu₀_meas hτ
  refine ⟨eta, H, heta0, heta1, hH, ?_⟩
  intro t hτt htT x hx y hy
  have ht : 0 < t := hτ.trans_le hτt
  rw [← deriv_chemFluxMLifted_eq_conjugateMildMChemDivJointRep_interior
      D hu₀_bound hu₀_meas ht htT hx,
    ← deriv_chemFluxMLifted_eq_conjugateMildMChemDivJointRep_interior
      D hu₀_bound hu₀_meas ht htT hy]
  exact hholder t hτt htT x hx y hy

end ShenWork.Paper2

#print axioms ShenWork.Paper2.conjugateMildM_coupledChemical_deriv_eq_resolverGradReal_Icc
#print axioms ShenWork.Paper2.conjugateMildM_jointSpatialDeriv_v_closed
#print axioms ShenWork.Paper2.conjugateMildMChemDivJointRep_jointContinuousOn
#print axioms ShenWork.Paper2.deriv_chemFluxMLifted_eq_conjugateMildMChemDivJointRep_interior
#print axioms ShenWork.Paper2.intervalDomainMChemotaxisDiv_eq_conjugateMildMChemDivJointRep_interior
#print axioms ShenWork.Paper2.conjugateMildM_chemDivSourceLift_eq_jointRep_Ioo
#print axioms ShenWork.Paper2.conjugateMildMChemDivJointRep_uniformTrace
#print axioms ShenWork.Paper2.conjugateMildMChemDivJointRep_positiveTime_holder_uniform
