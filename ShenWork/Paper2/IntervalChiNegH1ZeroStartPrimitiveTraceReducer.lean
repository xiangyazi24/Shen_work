import ShenWork.Paper2.IntervalChiNegH1ZeroStartInitializedPrimitive
import ShenWork.PDE.P3MoserDxJointContinuity

/-!
# Zero-face trace reducer for the initialized zero-start primitive source

This file records the honest source-side reduction from strict positive-time
classical regularity plus explicit zero-face traces to the closed zero-slab
primitive C¹/sign guard.  It does not construct those zero-face traces for the
B-form/Picard solution.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents

/-- Closed zero-slab primitive C¹/sign data, together with the actual
initialized zero slices, packages the source-facing initialized primitive
record.  This is only a constructor reducer: it does not produce any zero-face
continuity. -/
theorem H1ZeroStartInitializedPrimitiveC1SignSource_of_zeroSlices_closedPrimitive
    {u₀ v₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hu_zero : u (0 : ℝ) = u₀)
    (hv_zero : v (0 : ℝ) = v₀)
    (hclosed : H1ZeroStartClosedPrimitiveC1SignBefore u v T) :
    H1ZeroStartInitializedPrimitiveC1SignSource u₀ v₀ u v T where
  u_zero := hu_zero
  v_zero := hv_zero
  u_cont0 := hclosed.u_cont0
  v_cont0 := hclosed.v_cont0
  ux_cont0 := hclosed.ux_cont0
  vx_cont0 := hclosed.vx_cont0
  u_pos0 := hclosed.u_pos0
  v_nonneg0 := hclosed.v_nonneg0

/-- Glue strict-positive-time continuity to a closed zero slab when continuity
is supplied separately at every zero-time face point.

This is purely topological: it does not turn pointwise right limits into
zero-face continuity.  The `hzero` input is already `ContinuousWithinAt` on the
closed slab. -/
lemma continuousOn_zeroClosedSlab_of_strictTime_and_zeroFace
    {T b : ℝ} {F : ℝ × ℝ → ℝ}
    (_hb0 : 0 ≤ b)
    (hbT : b < T)
    (hstrict : ContinuousOn F (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1))
    (hzero : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt F
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) (0, x)) :
    ContinuousOn F (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) := by
  intro z hz
  rcases z with ⟨t, x⟩
  rcases hz with ⟨htb, hx⟩
  by_cases ht0 : t = 0
  · subst t
    exact hzero x hx
  · have htpos : 0 < t := by
      have htne : (0 : ℝ) ≠ t := by
        intro h
        exact ht0 h.symm
      exact lt_of_le_of_ne htb.1 htne
    have hzStrict : (t, x) ∈ Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 :=
      ⟨⟨htpos, lt_of_le_of_lt htb.2 hbT⟩, hx⟩
    have hposN : Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) ∈ 𝓝 (t, x) :=
      (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨htpos, trivial⟩
    have hlocal :
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) ∩
            (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))
          ⊆ Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 := by
      rintro ⟨s, y⟩ ⟨⟨hsb, hy⟩, hspos, _⟩
      exact ⟨⟨hspos, lt_of_le_of_lt hsb.2 hbT⟩, hy⟩
    have hwithin :
        ContinuousWithinAt F
          ((Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) ∩
            (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) (t, x) :=
      (hstrict (t, x) hzStrict).mono hlocal
    have hmem :
        ((Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) ∩
            (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) ∈
          𝓝[Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1] (t, x) :=
      Filter.inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds hposN)
    exact hwithin.mono_of_mem_nhdsWithin hmem

/-- Explicit zero-face primitive C¹/sign traces for an already initialized
candidate pair.  These are analytic frontier inputs, not consequences of
`InitialTrace` or of pointwise value limits. -/
structure H1ZeroStartPrimitiveC1ZeroFaceTrace
    (u v : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop where
  u_zeroFace : ∀ {b : ℝ}, 0 ≤ b → b < T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
    ContinuousWithinAt
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) (0, x)
  v_zeroFace : ∀ {b : ℝ}, 0 ≤ b → b < T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
    ContinuousWithinAt
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) (0, x)
  ux_zeroFace : ∀ {b : ℝ}, 0 ≤ b → b < T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
    ContinuousWithinAt
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (u t)) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) (0, x)
  vx_zeroFace : ∀ {b : ℝ}, 0 ≤ b → b < T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
    ContinuousWithinAt
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (v t)) x))
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1) (0, x)
  u_zero_pos : ∀ x : intervalDomainPoint, 0 < u (0 : ℝ) x
  v_zero_nonneg : ∀ x : intervalDomainPoint, 0 ≤ v (0 : ℝ) x

/-- Strict-time classical regularity plus explicit zero-face primitive traces
supplies the initialized zero-start primitive C¹/sign guard.

This is a reducer only: the zero-face trace record remains the source-facing
frontier for a general B-form/Picard construction. -/
theorem H1ZeroStartInitializedPrimitiveC1SignSource_of_classical_zeroFace
    {p : CM2Params} {u₀ v₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hu0 : u (0 : ℝ) = u₀)
    (hv0 : v (0 : ℝ) = v₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hface : H1ZeroStartPrimitiveC1ZeroFaceTrace u v T) :
    H1ZeroStartInitializedPrimitiveC1SignSource u₀ v₀ u v T where
  u_zero := hu0
  v_zero := hv0
  u_cont0 := by
    intro b hb0 hbT
    have hreg := hsol.regularity
    change intervalDomainClassicalRegularity T u v at hreg
    have hstrict :
        ContinuousOn
          (Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
          (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
      hreg.2.2.2.2.2.2.1
    exact continuousOn_zeroClosedSlab_of_strictTime_and_zeroFace
      (T := T) (b := b) hb0 hbT hstrict (hface.u_zeroFace hb0 hbT)
  v_cont0 := by
    intro b hb0 hbT
    have hreg := hsol.regularity
    change intervalDomainClassicalRegularity T u v at hreg
    have hstrict :
        ContinuousOn
          (Function.uncurry
            (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
          (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
      hreg.2.2.2.2.2.2.2
    exact continuousOn_zeroClosedSlab_of_strictTime_and_zeroFace
      (T := T) (b := b) hb0 hbT hstrict (hface.v_zeroFace hb0 hbT)
  ux_cont0 := by
    intro b hb0 hbT
    have hstrict :
        ContinuousOn
          (Function.uncurry
            (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (u t)) x))
          (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
      intervalDomain_dx_u_jointlyContinuous
        (params := p) (T := T) (u := u) (v := v) hsol
    exact continuousOn_zeroClosedSlab_of_strictTime_and_zeroFace
      (T := T) (b := b) hb0 hbT hstrict (hface.ux_zeroFace hb0 hbT)
  vx_cont0 := by
    intro b hb0 hbT
    have hstrict :
        ContinuousOn
          (Function.uncurry
            (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (v t)) x))
          (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
      intervalDomain_dx_v_jointlyContinuous
        (params := p) (T := T) (u := u) (v := v) hsol
    exact continuousOn_zeroClosedSlab_of_strictTime_and_zeroFace
      (T := T) (b := b) hb0 hbT hstrict (hface.vx_zeroFace hb0 hbT)
  u_pos0 := by
    intro b _hb0 hbT z hz
    rcases z with ⟨t, x⟩
    rcases hz with ⟨htb, hx⟩
    let X : intervalDomainPoint := ⟨x, hx⟩
    by_cases ht0 : t = 0
    · subst t
      simpa [Function.uncurry, intervalDomainLift, hx, X] using
        hface.u_zero_pos X
    · have htpos : 0 < t := by
        have htne : (0 : ℝ) ≠ t := by
          intro h
          exact ht0 h.symm
        exact lt_of_le_of_ne htb.1 htne
      have htT : t < T := lt_of_le_of_lt htb.2 hbT
      simpa [Function.uncurry, intervalDomainLift, hx, X] using
        hsol.u_pos' (x := X) htpos htT
  v_nonneg0 := by
    intro b _hb0 hbT z hz
    rcases z with ⟨t, x⟩
    rcases hz with ⟨htb, hx⟩
    let X : intervalDomainPoint := ⟨x, hx⟩
    by_cases ht0 : t = 0
    · subst t
      simpa [Function.uncurry, intervalDomainLift, hx, X] using
        hface.v_zero_nonneg X
    · have htpos : 0 < t := by
        have htne : (0 : ℝ) ≠ t := by
          intro h
          exact ht0 h.symm
        exact lt_of_le_of_ne htb.1 htne
      have htT : t < T := lt_of_le_of_lt htb.2 hbT
      simpa [Function.uncurry, intervalDomainLift, hx, X] using
        hsol.v_nonneg (x := X) htpos htT

section AxiomAudit

#print axioms H1ZeroStartInitializedPrimitiveC1SignSource_of_zeroSlices_closedPrimitive
#print axioms continuousOn_zeroClosedSlab_of_strictTime_and_zeroFace
#print axioms H1ZeroStartInitializedPrimitiveC1SignSource_of_classical_zeroFace

end AxiomAudit

end ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents
