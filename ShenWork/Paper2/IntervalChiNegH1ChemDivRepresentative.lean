import ShenWork.Paper2.IntervalChiNegH1LiftDeriv2Transfer
import ShenWork.PDE.IntervalCoupledClassicalBallEstimates
import ShenWork.PDE.P3MoserDxJointContinuity

/-!
# Physical chemotaxis-divergence representative for the H¹ route

This file isolates the endpoint-safe representative for the chemotaxis
divergence term.  It proves closed-spatial-slab continuity for the physical
product-rule expression, but deliberately leaves the interior product-rule
equality with the literal lifted `chemotaxisDiv` as a separate frontier.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.PDE
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer
open ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer
open ShenWork.Paper2.IntervalChiNegH1LiftDeriv2Transfer
open ShenWork.IntervalCoupledClassicalBallEstimates
open ShenWork.IntervalResolverLaplacianBridge

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative

/-- Physical product-rule representative for
`∂ₓ (u * v_x / (1+v)^β)`, with `v_xx` replaced by the elliptic reaction
representative `μ v - ν u^γ`.

This is intended for closed spatial slabs as a continuous representative.  It
is not a claim about endpoint equality with the literal lifted
`intervalDomain.chemotaxisDiv`. -/
abbrev liftChemotaxisDivPhysicalRep (p : CM2Params)
    (u v : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  deriv (intervalDomainLift (u t)) x *
      deriv (intervalDomainLift (v t)) x /
    (1 + intervalDomainLift (v t) x) ^ p.β +
  intervalDomainLift (u t) x *
      (p.μ * intervalDomainLift (v t) x -
        p.ν * (intervalDomainLift (u t) x) ^ p.γ) /
    (1 + intervalDomainLift (v t) x) ^ p.β -
  p.β * intervalDomainLift (u t) x *
      (deriv (intervalDomainLift (v t)) x) ^ 2 /
    (1 + intervalDomainLift (v t) x) ^ (p.β + 1)

/-- On the open spatial interior, the resolver-based chemotaxis-divergence
representative from the classical ball estimates is the physical product-rule
representative used by the H¹ route. -/
theorem intervalChemDivRepr_eq_liftChemotaxisDivPhysicalRep_interior
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T t x : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    intervalChemDivRepr p (u t) (v t) ⟨x, Set.Ioo_subset_Icc_self hx⟩ =
      liftChemotaxisDivPhysicalRep p u v t x := by
  classical
  let X : intervalDomainPoint := ⟨x, Set.Ioo_subset_Icc_self hx⟩
  have hgrad :
      deriv (intervalDomainLift (v t)) x = resolverGradReal p (u t) x :=
    solution_lift_v_deriv_eq_resolverGrad hsol ht hx
  have hdecay : SourceCoeffQuadraticDecay p (u t) :=
    sourceCoeffQuadraticDecay_of_solution hsol ht
  have hR :
      intervalNeumannResolverR p (u t) X =
        intervalDomainLift (v t) x := by
    simpa [X] using
      solution_v_eq_resolver_pointwise_unconditional hsol ht hx
  have hsource :
      intervalNeumannResolverSourceValue p (u t) X =
        p.ν * (intervalDomainLift (u t) x) ^ p.γ := by
    simpa [X] using
      sourceValue_eq_source (p := p) (T := T) (u := u) (v := v)
        hsol ht X
  have hrlap :
      intervalNeumannResolverRLap p (u t) X =
        p.μ * intervalDomainLift (v t) x -
          p.ν * (intervalDomainLift (u t) x) ^ p.γ := by
    rw [intervalNeumannResolverRLap_elliptic_identity hdecay X, hR, hsource]
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  have hv_nonneg : 0 ≤ intervalDomainLift (v t) x :=
    solution_lift_v_nonneg_Icc hsol ht x hxIcc
  have hbase_pos : 0 < 1 + intervalDomainLift (v t) x := by
    linarith
  have hneg_beta :
      (1 + intervalDomainLift (v t) x) ^ (-p.β) =
        ((1 + intervalDomainLift (v t) x) ^ p.β)⁻¹ :=
    Real.rpow_neg hbase_pos.le p.β
  have hneg_beta_one :
      (1 + intervalDomainLift (v t) x) ^ (-p.β - 1) =
        ((1 + intervalDomainLift (v t) x) ^ (p.β + 1))⁻¹ := by
    have h := Real.rpow_neg hbase_pos.le (p.β + 1)
    have hexp : -(p.β + 1) = -p.β - 1 := by ring
    rwa [hexp] at h
  change intervalChemDivRepr p (u t) (v t) X =
    liftChemotaxisDivPhysicalRep p u v t x
  unfold intervalChemDivRepr liftChemotaxisDivPhysicalRep
  rw [← hgrad, hrlap, hneg_beta, hneg_beta_one]
  simp only [X, div_eq_mul_inv]

/-- The literal lifted interval-domain chemotaxis divergence is the interval
point formula on the interval branch. -/
theorem lift_chemotaxisDiv_eq_intervalDomainChemotaxisDiv
    {p : CM2Params} {u v : intervalDomainPoint → ℝ} {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalDomainLift
        (fun X : intervalDomainPoint =>
          intervalDomain.chemotaxisDiv p u v X) x =
      intervalDomainChemotaxisDiv p u v ⟨x, hx⟩ := by
  simp [intervalDomain, intervalDomainLift, hx]

/-- Interior pointwise equality between the literal lifted chemotaxis-divergence
term and the physical representative. -/
theorem lift_chemotaxisDiv_eq_liftChemotaxisDivPhysicalRep_interior
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T t x : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomainLift
        (fun X : intervalDomainPoint =>
          intervalDomain.chemotaxisDiv p (u t) (v t) X) x =
      liftChemotaxisDivPhysicalRep p u v t x := by
  let X : intervalDomainPoint := ⟨x, Set.Ioo_subset_Icc_self hx⟩
  calc
    intervalDomainLift
        (fun X : intervalDomainPoint =>
          intervalDomain.chemotaxisDiv p (u t) (v t) X) x
        = intervalDomainChemotaxisDiv p (u t) (v t) X := by
          simpa [X] using
            lift_chemotaxisDiv_eq_intervalDomainChemotaxisDiv
              (p := p) (u := u t) (v := v t)
              (x := x) (Set.Ioo_subset_Icc_self hx)
    _ = intervalChemDivRepr p (u t) (v t) X := by
          exact intervalDomainChemotaxisDiv_eq_chemDivRepr_interior
            (p := p) (T := T) (u := u) (v := v) hsol ht hx
    _ = liftChemotaxisDivPhysicalRep p u v t x := by
          exact intervalChemDivRepr_eq_liftChemotaxisDivPhysicalRep_interior
            (p := p) (T := T) (u := u) (v := v) hsol ht hx

/-- Strict-slab interior `EqOn` between the literal lifted chemotaxis-divergence
term and the physical representative.  The spatial set is open, so this avoids
the endpoint ordinary-derivative trap. -/
theorem lift_chemotaxisDiv_eq_liftChemotaxisDivPhysicalRep_strictSlab_interior
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T a b : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ha : 0 < a) (_hab : a ≤ b) (hbT : b < T) :
    Set.EqOn
      (Function.uncurry
        (fun t x =>
          intervalDomainLift
            (fun X : intervalDomainPoint =>
              intervalDomain.chemotaxisDiv p (u t) (v t) X) x))
      (Function.uncurry (liftChemotaxisDivPhysicalRep p u v))
      (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1) := by
  intro z hz
  rcases z with ⟨t, x⟩
  rcases hz with ⟨htab, hx⟩
  have ht : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le ha htab.1, lt_of_le_of_lt htab.2 hbT⟩
  exact lift_chemotaxisDiv_eq_liftChemotaxisDivPhysicalRep_interior
    (p := p) (T := T) (u := u) (v := v) hsol ht hx

/-- Classical solutions supply closed-spatial strict-slab continuity of the
physical chemotaxis-divergence representative. -/
theorem liftChemotaxisDivPhysicalRep_continuousOn_strictSlab_of_classicalSolution
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T a b : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ha : 0 < a) (_hab : a ≤ b) (hbT : b < T) :
    ContinuousOn (Function.uncurry (liftChemotaxisDivPhysicalRep p u v))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hsub :
      Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1 ⊆
        Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 := by
    refine Set.prod_mono ?_ (Subset.rfl)
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hbT⟩
  have hreg := hsol.regularity
  change intervalDomainClassicalRegularity T u v at hreg
  have hu_all :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hreg.2.2.2.2.2.2.1
  have hv_all :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hreg.2.2.2.2.2.2.2
  have hu :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    hu_all.mono hsub
  have hv :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    hv_all.mono hsub
  have hux :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (u t)) x))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    (intervalDomain_dx_u_jointlyContinuous (params := p)
      (T := T) (u := u) (v := v) hsol).mono hsub
  have hvx :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (v t)) x))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    (intervalDomain_dx_v_jointlyContinuous (params := p)
      (T := T) (u := u) (v := v) hsol).mono hsub
  have hvxxRep :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            p.μ * intervalDomainLift (v t) x -
              p.ν * (intervalDomainLift (u t) x) ^ p.γ))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    (intervalDomain_v_xx_reaction_jointContinuous (params := p)
      (T := T) (u := u) (v := v) hsol).mono hsub
  have hbase :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          1 +
            Function.uncurry
              (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.add hv
  have hbase_pos :
      ∀ z ∈ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1,
        0 <
          1 +
            Function.uncurry
              (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z := by
    intro z hz
    rcases z with ⟨t, x⟩
    rcases hz with ⟨ht, hx⟩
    simp only [Function.uncurry_apply_pair]
    rw [intervalDomainLift, dif_pos hx]
    have hv_nonneg : 0 ≤ v t ⟨x, hx⟩ :=
      hsol.v_nonneg (lt_of_lt_of_le ha ht.1) (lt_of_le_of_lt ht.2 hbT)
    linarith
  have hden_beta :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (1 +
            Function.uncurry
              (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^ p.β)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    hbase.rpow_const
      (fun z hz => Or.inl (ne_of_gt (hbase_pos z hz)))
  have hden_beta_ne :
      ∀ z ∈ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1,
        (1 +
          Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^
            p.β ≠ 0 := by
    intro z hz
    exact ne_of_gt (Real.rpow_pos_of_pos (hbase_pos z hz) _)
  have hden_beta_one :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (1 +
            Function.uncurry
              (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^
            (p.β + 1))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    hbase.rpow_const
      (fun z hz => Or.inl (ne_of_gt (hbase_pos z hz)))
  have hden_beta_one_ne :
      ∀ z ∈ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1,
        (1 +
          Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^
            (p.β + 1) ≠ 0 := by
    intro z hz
    exact ne_of_gt (Real.rpow_pos_of_pos (hbase_pos z hz) _)
  have hterm1 :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          Function.uncurry
              (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (u t)) x) z *
            Function.uncurry
              (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (v t)) x) z /
            (1 +
              Function.uncurry
                (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^ p.β)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    (hux.mul hvx).div hden_beta hden_beta_ne
  have hterm2 :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          Function.uncurry
              (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z *
            Function.uncurry
              (fun (t : ℝ) (x : ℝ) =>
                p.μ * intervalDomainLift (v t) x -
                  p.ν * (intervalDomainLift (u t) x) ^ p.γ) z /
            (1 +
              Function.uncurry
                (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^ p.β)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    (hu.mul hvxxRep).div hden_beta hden_beta_ne
  have hterm3 :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (p.β *
              Function.uncurry
                (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z) *
            (Function.uncurry
              (fun (t : ℝ) (x : ℝ) =>
                deriv (intervalDomainLift (v t)) x) z) ^ 2 /
            (1 +
              Function.uncurry
                (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^
              (p.β + 1))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    ((hu.const_mul p.β).mul (hvx.pow 2)).div hden_beta_one hden_beta_one_ne
  simpa [liftChemotaxisDivPhysicalRep, Function.uncurry] using
    (hterm1.add hterm2).sub hterm3

/-- The L¹ H¹ frontier with the concrete physical chemotaxis-divergence
representative now needs only the interior equality against the representative
RHS supplied by `IntervalChiNegH1LiftDeriv2Transfer`. -/
theorem H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep_interiorEq
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hEqInterior : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry
          (liftDeriv2PhysicalRHSWithChemRep p u
            (liftChemotaxisDivPhysicalRep p u v)))
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    H1UxxL1ContBefore u T := by
  refine H1UxxL1ContBefore_of_classical_chemRep_interiorEq
    (p := p) (u := u) (v := v)
    (chemRep := liftChemotaxisDivPhysicalRep p u v) (T := T)
    hsol ?_ hEqInterior
  intro a b ha hab hbT
  exact liftChemotaxisDivPhysicalRep_continuousOn_strictSlab_of_classicalSolution
    (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT

/-- Concrete specialization of the abstract seam: if the literal lifted
chemotaxis-divergence term agrees with the physical representative on the open
spatial interior, then the old physical-RHS equality route produces the H¹ L¹
frontier. -/
theorem H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep_eq_physicalRHS_interiorEq
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hChemEqInterior : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry
          (fun t x =>
            intervalDomainLift
              (fun X : intervalDomainPoint =>
                intervalDomain.chemotaxisDiv p (u t) (v t) X) x))
        (Function.uncurry (liftChemotaxisDivPhysicalRep p u v))
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1))
    (hEqPhysicalInterior : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry (liftDeriv2PhysicalRHS p u v))
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    H1UxxL1ContBefore u T := by
  refine H1UxxL1ContBefore_of_classical_chemRep_eq_physicalRHS_interiorEq
    (p := p) (u := u) (v := v)
    (chemRep := liftChemotaxisDivPhysicalRep p u v) (T := T)
    hsol ?_ hChemEqInterior hEqPhysicalInterior
  intro a b ha hab hbT
  exact liftChemotaxisDivPhysicalRep_continuousOn_strictSlab_of_classicalSolution
    (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT

/-- The concrete chemotaxis-divergence interior equality is now supplied
directly by the resolver representative bridge.  The remaining H¹ L¹ input is
only the separate interior equality between `liftDeriv2` and the physical RHS. -/
theorem H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep_physicalRHS_interiorEq
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hEqPhysicalInterior : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry (liftDeriv2PhysicalRHS p u v))
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    H1UxxL1ContBefore u T := by
  refine
    H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep_eq_physicalRHS_interiorEq
      (p := p) (u := u) (v := v) (T := T) hsol ?_ hEqPhysicalInterior
  intro a b ha hab hbT
  exact lift_chemotaxisDiv_eq_liftChemotaxisDivPhysicalRep_strictSlab_interior
    (p := p) (u := u) (v := v) (T := T) hsol ha hab hbT

section AxiomAudit

#print axioms intervalChemDivRepr_eq_liftChemotaxisDivPhysicalRep_interior
#print axioms lift_chemotaxisDiv_eq_intervalDomainChemotaxisDiv
#print axioms lift_chemotaxisDiv_eq_liftChemotaxisDivPhysicalRep_interior
#print axioms lift_chemotaxisDiv_eq_liftChemotaxisDivPhysicalRep_strictSlab_interior
#print axioms liftChemotaxisDivPhysicalRep_continuousOn_strictSlab_of_classicalSolution
#print axioms H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep_interiorEq
#print axioms H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep_eq_physicalRHS_interiorEq
#print axioms H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep_physicalRHS_interiorEq

end AxiomAudit

end ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative
