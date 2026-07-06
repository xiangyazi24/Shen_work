import ShenWork.Paper2.IntervalChiNegH1ZeroSlabPhysicalRHS

/-!
# Zero-start primitive component reducer for the H¹ physical RHS route

This file sits one level below `H1ZeroStartPhysicalRHSDataBefore`: primitive
zero-start continuity of `u`, `v`, `u_x`, and `v_x` algebraically supplies the
physical chemotaxis-divergence representative.  The genuinely analytic inputs
remain the zero-start time derivative continuity and the interior PDE equality
for `liftDeriv2`.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1LiftDeriv2Transfer
open ShenWork.Paper2.IntervalChiNegH1LapComponentContinuity
open ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative
open ShenWork.Paper2.IntervalChiNegH1ZeroSlabPhysicalRHS

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents

/-- Primitive zero-start data sufficient to build the algebraic physical
chemotaxis-divergence and reaction components on every zero-start slab.

The two fields not reduced here are the real construction-level obligations:
zero-start continuity of `liftTimeDeriv u` and the endpoint-including interior
equality between `liftDeriv2` and the physical RHS. -/
structure H1ZeroStartPhysicalPrimitiveDataBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop where
  u_cont0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)
  v_cont0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)
  ux_cont0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (u t)) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)
  vx_cont0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (v t)) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)
  u_pos0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ∀ z ∈ Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1,
      0 <
        Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z
  v_nonneg0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ∀ z ∈ Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1,
      0 ≤
        Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z
  time_cont0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn
      (Function.uncurry (fun t x => liftTimeDeriv u t x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)
  eqInterior0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    Set.EqOn
      (Function.uncurry (fun t x => liftDeriv2 u t x))
      (Function.uncurry
          (liftDeriv2PhysicalRHSWithChemRep p u
            (liftChemotaxisDivPhysicalRep p u v)))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Ioo (0 : ℝ) 1)

/-- Zero-start primitive closed-slab continuity and positivity data, separated
from the initial-time PDE seam. -/
structure H1ZeroStartPhysicalPrimitiveContinuityBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop where
  u_cont0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)
  v_cont0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)
  ux_cont0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (u t)) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)
  vx_cont0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (v t)) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)
  u_pos0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ∀ z ∈ Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1,
      0 <
        Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z
  v_nonneg0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ∀ z ∈ Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1,
      0 ≤
        Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z

/-- The initial-time PDE seam needed by the zero-start physical H¹ route:
closed-slab time-derivative continuity and endpoint-including interior
agreement of literal `liftDeriv2` with the physical representative. -/
structure H1ZeroStartPhysicalPDESeamBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop where
  time_cont0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn
      (Function.uncurry (fun t x => liftTimeDeriv u t x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)
  eqInterior0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    Set.EqOn
      (Function.uncurry (fun t x => liftDeriv2 u t x))
      (Function.uncurry
        (liftDeriv2PhysicalRHSWithChemRep p u
          (liftChemotaxisDivPhysicalRep p u v)))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Ioo (0 : ℝ) 1)

/-- Reassemble the original zero-start primitive package from the separated
continuity/positivity data and the initial-time PDE seam. -/
theorem H1ZeroStartPhysicalPrimitiveDataBefore_of_continuity_and_pdeSeam
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hcont : H1ZeroStartPhysicalPrimitiveContinuityBefore p u v T)
    (hseam : H1ZeroStartPhysicalPDESeamBefore p u v T) :
    H1ZeroStartPhysicalPrimitiveDataBefore p u v T where
  u_cont0 := hcont.u_cont0
  v_cont0 := hcont.v_cont0
  ux_cont0 := hcont.ux_cont0
  vx_cont0 := hcont.vx_cont0
  u_pos0 := hcont.u_pos0
  v_nonneg0 := hcont.v_nonneg0
  time_cont0 := hseam.time_cont0
  eqInterior0 := hseam.eqInterior0

/-- Zero-start continuity of the physical chemotaxis-divergence representative
from primitive zero-start continuity of `u`, `v`, `u_x`, and `v_x`.

This is the zero-start analogue of
`liftChemotaxisDivPhysicalRep_continuousOn_strictSlab_of_classicalSolution`,
with all strict-time classical-regularity extraction replaced by explicit
primitive hypotheses. -/
theorem liftChemotaxisDivPhysicalRep_continuousOn_zeroSlab_of_primitives
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {b : ℝ}
    (hu : ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hv : ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hux : ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (u t)) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hvx : ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (v t)) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hupos : ∀ z ∈ Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1,
      0 <
        Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z)
    (hvnn : ∀ z ∈ Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1,
      0 ≤
        Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) :
    ContinuousOn
      (Function.uncurry (liftChemotaxisDivPhysicalRep p u v))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) := by
  let S : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1
  have huS :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x)) S := by
    simpa [S] using hu
  have hvS :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x)) S := by
    simpa [S] using hv
  have huxS :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (u t)) x)) S := by
    simpa [S] using hux
  have hvxS :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (v t)) x)) S := by
    simpa [S] using hvx
  have huposS :
      ∀ z ∈ S,
        0 <
          Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z := by
    intro z hz
    exact hupos z (by simpa [S] using hz)
  have hvnnS :
      ∀ z ∈ S,
        0 ≤
          Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z := by
    intro z hz
    exact hvnn z (by simpa [S] using hz)
  have hu_gamma :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z) ^ p.γ) S :=
    huS.rpow_const (fun z hz => Or.inl (ne_of_gt (huposS z hz)))
  have hvxxRep :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          p.μ *
              Function.uncurry
                (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z -
            p.ν *
              (Function.uncurry
                (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z) ^
                p.γ) S :=
    (hvS.const_mul p.μ).sub (hu_gamma.const_mul p.ν)
  have hbase :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          1 +
            Function.uncurry
              (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) S :=
    continuousOn_const.add hvS
  have hbase_pos :
      ∀ z ∈ S,
        0 <
          1 +
            Function.uncurry
              (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z := by
    intro z hz
    have hvz := hvnnS z hz
    linarith
  have hden_beta :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (1 +
            Function.uncurry
              (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^ p.β) S :=
    hbase.rpow_const
      (fun z hz => Or.inl (ne_of_gt (hbase_pos z hz)))
  have hden_beta_ne :
      ∀ z ∈ S,
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
            (p.β + 1)) S :=
    hbase.rpow_const
      (fun z hz => Or.inl (ne_of_gt (hbase_pos z hz)))
  have hden_beta_one_ne :
      ∀ z ∈ S,
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
                (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^ p.β) S :=
    (huxS.mul hvxS).div hden_beta hden_beta_ne
  have hterm2 :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          Function.uncurry
              (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z *
            (p.μ *
                Function.uncurry
                  (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z -
              p.ν *
                (Function.uncurry
                  (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x) z) ^
                  p.γ) /
            (1 +
              Function.uncurry
                (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x) z) ^ p.β) S :=
    (huS.mul hvxxRep).div hden_beta hden_beta_ne
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
              (p.β + 1)) S :=
    ((huS.const_mul p.β).mul (hvxS.pow 2)).div hden_beta_one hden_beta_one_ne
  simpa [S, liftChemotaxisDivPhysicalRep, Function.uncurry] using
    (hterm1.add hterm2).sub hterm3

/-- Primitive zero-start fields produce the explicit zero-start physical RHS
data package from `IntervalChiNegH1ZeroSlabPhysicalRHS`. -/
theorem H1ZeroStartPhysicalRHSDataBefore_of_zeroStartPrimitiveData
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (H : H1ZeroStartPhysicalPrimitiveDataBefore p u v T) :
    H1ZeroStartPhysicalRHSDataBefore p u v T :=
  H1ZeroStartPhysicalRHSDataBefore_of_lift_continuous_positive
    (p := p) (u := u) (v := v) (T := T)
    H.time_cont0
    (fun {b} hb hbT =>
      liftChemotaxisDivPhysicalRep_continuousOn_zeroSlab_of_primitives
        (p := p) (u := u) (v := v) (b := b)
        (H.u_cont0 (b := b) hb hbT)
        (H.v_cont0 (b := b) hb hbT)
        (H.ux_cont0 (b := b) hb hbT)
        (H.vx_cont0 (b := b) hb hbT)
        (H.u_pos0 (b := b) hb hbT)
        (H.v_nonneg0 (b := b) hb hbT))
    H.u_cont0 H.u_pos0 H.eqInterior0

/-- Primitive zero-start fields produce the before-`T` zero-slab representative
frontier for the concrete physical RHS. -/
theorem H1LiftDeriv2ZeroSlabRepBefore_of_zeroStartPrimitiveData
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (H : H1ZeroStartPhysicalPrimitiveDataBefore p u v T) :
    H1LiftDeriv2ZeroSlabRepresentativeBefore u T
      (liftDeriv2PhysicalRHSWithChemRep p u
        (liftChemotaxisDivPhysicalRep p u v)) :=
  H1LiftDeriv2ZeroSlabRepBefore_of_zeroStartPhysicalRHSData
    (p := p) (u := u) (v := v) (T := T)
    (H1ZeroStartPhysicalRHSDataBefore_of_zeroStartPrimitiveData
      (p := p) (u := u) (v := v) (T := T) H)

section AxiomAudit

#print axioms H1ZeroStartPhysicalPrimitiveDataBefore_of_continuity_and_pdeSeam
#print axioms liftChemotaxisDivPhysicalRep_continuousOn_zeroSlab_of_primitives
#print axioms H1ZeroStartPhysicalRHSDataBefore_of_zeroStartPrimitiveData
#print axioms H1LiftDeriv2ZeroSlabRepBefore_of_zeroStartPrimitiveData

end AxiomAudit

end ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents
