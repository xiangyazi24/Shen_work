import ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer
import ShenWork.PDE.P3MoserGradientContinuityFromDx

/-!
# Strict-window continuity of the H¹ Laplacian component

This file discharges the positive-time part of the `lapL2sq` component
continuity frontier from the scalar `liftDeriv2` joint-continuity hypothesis.
Continuity at `t = 0` is kept as an explicit zero-right frontier; the wrappers
below only combine that frontier with strict positive-time continuity.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer
open ShenWork.IntervalDomainExistence.P3MoserGradientIntegrability

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1LapComponentContinuity

/-- Explicit endpoint-lap continuity frontier.  This is H²/lap-trace data, not
H¹-energy endpoint data. -/
structure H1LapComponentEndpointContinuousBefore
    (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop where
  lap_cont0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc (0 : ℝ) b)

/-- The atomic zero-right continuity frontier for the Laplacian component.  This
is the missing H²/lap-trace input at time zero; it is deliberately weaker than
the full endpoint-window package above. -/
structure H1LapComponentZeroRightContinuous
    (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  lap_cont0 : ContinuousWithinAt (fun τ => lapL2sq u τ) (Set.Ici (0 : ℝ)) 0

/-- Zero-start slab representative/equality frontier for `liftDeriv2` before
`T`.  This packages the remaining H²/laplacian trace input without asserting a
physical producer for it. -/
structure H1LiftDeriv2ZeroSlabRepresentativeBefore
    (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) (F : ℝ → ℝ → ℝ) : Prop where
  cont0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    ContinuousOn (Function.uncurry F)
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)
  eqInterior0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
    Set.EqOn
      (Function.uncurry (fun t x => liftDeriv2 u t x))
      (Function.uncurry F)
      (Set.Icc (0 : ℝ) b ×ˢ Set.Ioo (0 : ℝ) 1)

/-- A single zero-start slab representative for `liftDeriv2`.  This is the
minimal local H²/lap-trace frontier needed to obtain zero-right continuity of
`lapL2sq`. -/
structure H1LiftDeriv2ZeroSlabRepresentative
    (u : ℝ → intervalDomainPoint → ℝ) (F : ℝ → ℝ → ℝ) (b : ℝ) : Prop where
  hb0 : 0 < b
  hFcont :
    ContinuousOn (Function.uncurry F)
      (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1)
  hEqInterior :
    Set.EqOn
      (Function.uncurry (fun t x => liftDeriv2 u t x))
      (Function.uncurry F)
      (Set.Icc (0 : ℝ) b ×ˢ Set.Ioo (0 : ℝ) 1)

/-- Existential packaging of the single-slab zero-start representative
frontier. -/
def H1LiftDeriv2HasZeroSlabRepresentative
    (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∃ (F : ℝ → ℝ → ℝ) (b : ℝ),
    H1LiftDeriv2ZeroSlabRepresentative u F b

/-- Closed-slab joint continuity of `u_xx` implies closed-window continuity of
the squared Laplacian component on that same slab. -/
theorem lapL2sq_continuousOn_Icc_of_liftDeriv2_jointContinuousOn
    {u : ℝ → intervalDomainPoint → ℝ} {a b : ℝ}
    (hcont :
      ContinuousOn (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b) := by
  let F : ℝ → ℝ → ℝ := fun τ x => (liftDeriv2 u τ x) ^ 2
  have hFcont :
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
    simpa [F, Function.uncurry] using hcont.pow 2
  have hint :=
    continuousOn_intervalIntegral_zero_one_of_continuousOn_Icc_prod hFcont
  simpa [F, lapL2sq, liftDeriv2] using hint

/-- A continuous closed-slab representative that agrees with `liftDeriv2` on
the open spatial interior also gives `lapL2sq` continuity.  Endpoint equality
is unnecessary because the endpoint mismatch is ignored by interval-integral
a.e. congruence. -/
theorem lapL2sq_continuousOn_Icc_of_strictSlab_interior_eq_continuous
    {u : ℝ → intervalDomainPoint → ℝ} {F : ℝ → ℝ → ℝ} {a b : ℝ}
    (hFcont :
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior :
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b) := by
  let G : ℝ → ℝ := fun τ => ∫ x in (0 : ℝ)..1, (F τ x) ^ 2
  have hFsq_cont :
      ContinuousOn (Function.uncurry (fun τ x => (F τ x) ^ 2))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
    simpa [Function.uncurry] using hFcont.pow 2
  have hGcont : ContinuousOn G (Set.Icc a b) := by
    have hint :=
      continuousOn_intervalIntegral_zero_one_of_continuousOn_Icc_prod
        hFsq_cont
    simpa [G] using hint
  refine hGcont.congr ?_
  intro τ hτ
  dsimp [G]
  change
    (∫ x in (0 : ℝ)..1, (liftDeriv2 u τ x) ^ 2) =
      ∫ x in (0 : ℝ)..1, (F τ x) ^ 2
  refine intervalIntegral.integral_congr_ae ?_
  have hne1 : ∀ᵐ x : ℝ ∂volume, x ≠ (1 : ℝ) := by
    rw [MeasureTheory.ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  filter_upwards [hne1] with x hx_ne1 hxmem
  rw [Set.uIoc_of_le zero_le_one] at hxmem
  have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hxmem.1, lt_of_le_of_ne hxmem.2 hx_ne1⟩
  have hEqτ := hEqInterior (x := (τ, x)) (Set.mem_prod.mpr ⟨hτ, hxIoo⟩)
  simp only [Function.uncurry_apply_pair] at hEqτ
  exact congrArg (fun y : ℝ => y ^ 2) hEqτ

/-- The scalar strict-slab regularity package gives `lapL2sq` continuity on
every strict closed time window `[a,b] ⊂ (0,T)`. -/
theorem lapL2sq_continuousOn_strictWindow_of_liftDeriv2_jointContinuousBefore
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (h : H1LiftDeriv2JointContinuousBefore u T) :
    ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b) := by
  intro a b ha hab hbT
  exact lapL2sq_continuousOn_Icc_of_liftDeriv2_jointContinuousOn
    (h.cont ha hab hbT)

/-- Strict-window version of
`lapL2sq_continuousOn_Icc_of_strictSlab_interior_eq_continuous`. -/
theorem lapL2sq_continuousOn_strictWindow_of_strictSlab_interior_eq_continuous
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b) := by
  intro a b ha hab hbT
  exact lapL2sq_continuousOn_Icc_of_strictSlab_interior_eq_continuous
    (hF (a := a) (b := b) ha hab hbT)
    (hEqInterior (a := a) (b := b) ha hab hbT)

/-- Endpoint-lap continuity plus strict positive-time lap continuity gives the
full `0 ≤ a` lap-continuity field expected by closed-window RHS packages. -/
theorem lapL2sq_continuousOn_before_of_endpoint_and_strict
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (h0 : H1LapComponentEndpointContinuousBefore u T)
    (hstrict : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b)) :
    ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b) := by
  intro a b ha hab hbT
  by_cases ha_pos : 0 < a
  · exact hstrict ha_pos hab hbT
  · have ha_eq : a = 0 := le_antisymm (le_of_not_gt ha_pos) ha
    subst a
    exact h0.lap_cont0 (b := b) hab hbT

/-- Endpoint-window lap continuity alone gives closed-window lap continuity on
every `[a,b]` with `0 ≤ a`, by restriction from `[0,b]`. -/
theorem lapL2sq_continuousOn_before_of_endpoint
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (h0 : H1LapComponentEndpointContinuousBefore u T) :
    ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b) := by
  intro a b ha hab hbT
  have hb_nonneg : 0 ≤ b := le_trans ha hab
  exact (h0.lap_cont0 (b := b) hb_nonneg hbT).mono (by
    intro τ hτ
    exact ⟨le_trans ha hτ.1, hτ.2⟩)

/-- Zero-right continuity at time zero plus strict positive-time continuity
gives continuity on every zero-starting window `[0,b]`. -/
theorem lapL2sq_continuousOn_Icc_zero_of_zeroRight_and_strict
    {u : ℝ → intervalDomainPoint → ℝ} {T b : ℝ}
    (h0 : H1LapComponentZeroRightContinuous u)
    (hstrict : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b))
    (_hb_nonneg : 0 ≤ b) (hbT : b < T) :
    ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc (0 : ℝ) b) := by
  intro τ hτ
  by_cases hτ_zero : τ = 0
  · subst τ
    exact h0.lap_cont0.mono (by
      intro y hy
      exact hy.1)
  · have hτ_pos : 0 < τ := lt_of_le_of_ne hτ.1 (Ne.symm hτ_zero)
    have hhalf_pos : 0 < τ / 2 := by linarith
    have hhalf_le_b : τ / 2 ≤ b := by linarith [hτ.2]
    have hτ_mem : τ ∈ Set.Icc (τ / 2) b := ⟨by linarith, hτ.2⟩
    have hcont :
        ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc (τ / 2) b) :=
      hstrict hhalf_pos hhalf_le_b hbT
    have hnhds : Set.Icc (τ / 2) b ∈ 𝓝[Set.Icc (0 : ℝ) b] τ := by
      have hopen : Set.Ioi (τ / 2) ∈ 𝓝 τ := Ioi_mem_nhds (by linarith)
      have hself : Set.Icc (0 : ℝ) b ∈ 𝓝[Set.Icc (0 : ℝ) b] τ :=
        self_mem_nhdsWithin
      have hinter :
          Set.Ioi (τ / 2) ∩ Set.Icc (0 : ℝ) b ∈
            𝓝[Set.Icc (0 : ℝ) b] τ :=
        Filter.inter_mem (Filter.mem_inf_of_left hopen) hself
      refine Filter.mem_of_superset hinter ?_
      intro y hy
      exact ⟨le_of_lt hy.1, hy.2.2⟩
    exact (hcont.continuousWithinAt hτ_mem).mono_of_mem_nhdsWithin hnhds

/-- Package the zero-right frontier plus strict positive-time continuity into
the endpoint-window frontier consumed by the bridge layer. -/
theorem H1LapComponentEndpointContinuousBefore_of_zeroRight_and_strict
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (h0 : H1LapComponentZeroRightContinuous u)
    (hstrict : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b)) :
    H1LapComponentEndpointContinuousBefore u T :=
  { lap_cont0 := fun hb_nonneg hbT =>
      lapL2sq_continuousOn_Icc_zero_of_zeroRight_and_strict
        h0 hstrict hb_nonneg hbT }

/-- Endpoint-window frontier from zero-right continuity and the existing
`liftDeriv2` strict-window joint-continuity package. -/
theorem H1LapComponentEndpointContinuousBefore_of_zeroRight_and_liftDeriv2_jointContinuousBefore
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (h0 : H1LapComponentZeroRightContinuous u)
    (huxx : H1LiftDeriv2JointContinuousBefore u T) :
    H1LapComponentEndpointContinuousBefore u T :=
  H1LapComponentEndpointContinuousBefore_of_zeroRight_and_strict
    h0 (lapL2sq_continuousOn_strictWindow_of_liftDeriv2_jointContinuousBefore
      huxx)

/-- Endpoint-window frontier from zero-right continuity and a strict positive-time
continuous representative of `liftDeriv2`. -/
theorem H1LapComponentEndpointContinuousBefore_of_zeroRight_and_strictSlab_interior_eq_continuous
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ} {F : ℝ → ℝ → ℝ}
    (h0 : H1LapComponentZeroRightContinuous u)
    (hF : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    H1LapComponentEndpointContinuousBefore u T :=
  H1LapComponentEndpointContinuousBefore_of_zeroRight_and_strict
    h0 (lapL2sq_continuousOn_strictWindow_of_strictSlab_interior_eq_continuous
      hF hEqInterior)

/-- A zero-start slab representative gives zero-right continuity of
`lapL2sq`.  This is only a reducer: the H² trace input is the zero-slab
continuity/equality of the representative. -/
theorem lapL2sq_continuousWithinAt_zero_of_zeroSlab_interior_eq_continuous
    {u : ℝ → intervalDomainPoint → ℝ} {F : ℝ → ℝ → ℝ} {b : ℝ}
    (hb0 : 0 < b)
    (hFcont :
      ContinuousOn (Function.uncurry F)
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior :
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc (0 : ℝ) b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    ContinuousWithinAt (fun τ => lapL2sq u τ) (Set.Ici (0 : ℝ)) 0 := by
  have hIcc :
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc (0 : ℝ) b) :=
    lapL2sq_continuousOn_Icc_of_strictSlab_interior_eq_continuous
      hFcont hEqInterior
  have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) b := ⟨le_rfl, hb0.le⟩
  have hwithin :
      ContinuousWithinAt (fun τ => lapL2sq u τ) (Set.Icc (0 : ℝ) b) 0 :=
    hIcc.continuousWithinAt hmem
  have hsets : Set.Icc (0 : ℝ) b =ᶠ[𝓝 (0 : ℝ)] Set.Ici (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hb0] with y hy
    apply propext
    constructor
    · intro hyIcc
      exact hyIcc.1
    · intro hyIci
      have hylt : y < b := hy
      exact ⟨hyIci, hylt.le⟩
  exact hwithin.congr_set hsets

/-- Record version of
`lapL2sq_continuousWithinAt_zero_of_zeroSlab_interior_eq_continuous`. -/
theorem H1LapComponentZeroRightContinuous_of_zeroSlab_interior_eq_continuous
    {u : ℝ → intervalDomainPoint → ℝ} {F : ℝ → ℝ → ℝ} {b : ℝ}
    (hb0 : 0 < b)
    (hFcont :
      ContinuousOn (Function.uncurry F)
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior :
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc (0 : ℝ) b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    H1LapComponentZeroRightContinuous u :=
  { lap_cont0 :=
      lapL2sq_continuousWithinAt_zero_of_zeroSlab_interior_eq_continuous
        hb0 hFcont hEqInterior }

/-- A single zero-start representative slab produces zero-right lap-component
continuity. -/
theorem H1LapComponentZeroRightContinuous_of_zeroSlabRepresentative
    {u : ℝ → intervalDomainPoint → ℝ} {F : ℝ → ℝ → ℝ} {b : ℝ}
    (h : H1LiftDeriv2ZeroSlabRepresentative u F b) :
    H1LapComponentZeroRightContinuous u :=
  H1LapComponentZeroRightContinuous_of_zeroSlab_interior_eq_continuous
    h.hb0 h.hFcont h.hEqInterior

/-- Existential single-slab zero-start representative package reduced to the
zero-right lap-component frontier. -/
theorem H1LapComponentZeroRightContinuous_of_hasZeroSlabRepresentative
    {u : ℝ → intervalDomainPoint → ℝ}
    (h : H1LiftDeriv2HasZeroSlabRepresentative u) :
    H1LapComponentZeroRightContinuous u := by
  rcases h with ⟨F, b, h⟩
  exact H1LapComponentZeroRightContinuous_of_zeroSlabRepresentative h

/-- A single zero-start representative slab plus positive-time `liftDeriv2`
joint continuity gives the endpoint-window lap frontier. -/
theorem
    H1LapEndpointBefore_of_hasZeroSlabRep_and_liftDeriv2
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (h0 : H1LiftDeriv2HasZeroSlabRepresentative u)
    (huxx : H1LiftDeriv2JointContinuousBefore u T) :
    H1LapComponentEndpointContinuousBefore u T :=
  H1LapComponentEndpointContinuousBefore_of_zeroRight_and_liftDeriv2_jointContinuousBefore
    (H1LapComponentZeroRightContinuous_of_hasZeroSlabRepresentative h0)
    huxx

/-- A single zero-start representative slab plus a strict positive-time
representative family gives the endpoint-window lap frontier. -/
theorem
    H1LapEndpointBefore_of_hasZeroSlabRep_and_strictSlab
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ} {F : ℝ → ℝ → ℝ}
    (h0 : H1LiftDeriv2HasZeroSlabRepresentative u)
    (hF : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    H1LapComponentEndpointContinuousBefore u T :=
  H1LapComponentEndpointContinuousBefore_of_zeroRight_and_strictSlab_interior_eq_continuous
    (H1LapComponentZeroRightContinuous_of_hasZeroSlabRepresentative h0)
    hF hEqInterior

/-- A zero-start representative family directly supplies the endpoint-window
frontier.  The family hypotheses are the remaining H²/lap-trace data. -/
theorem H1LapComponentEndpointContinuousBefore_of_zeroSlab_interior_eq_continuous
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ} {F : ℝ → ℝ → ℝ}
    (hF0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn (Function.uncurry F)
        (Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEq0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc (0 : ℝ) b ×ˢ Set.Ioo (0 : ℝ) 1)) :
    H1LapComponentEndpointContinuousBefore u T :=
  { lap_cont0 := fun hb_nonneg hbT =>
      lapL2sq_continuousOn_Icc_of_strictSlab_interior_eq_continuous
        (hF0 hb_nonneg hbT) (hEq0 hb_nonneg hbT) }

/-- Record wrapper for a zero-start `liftDeriv2` representative family. -/
theorem H1LapComponentEndpointContinuousBefore_of_zeroSlabRepresentativeBefore
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ} {F : ℝ → ℝ → ℝ}
    (h : H1LiftDeriv2ZeroSlabRepresentativeBefore u T F) :
    H1LapComponentEndpointContinuousBefore u T :=
  H1LapComponentEndpointContinuousBefore_of_zeroSlab_interior_eq_continuous
    (F := F)
    (fun {b} hb_nonneg hbT => h.cont0 (b := b) hb_nonneg hbT)
    (fun {b} hb_nonneg hbT => h.eqInterior0 (b := b) hb_nonneg hbT)

/-- Closed-window lap continuity from a zero-start `liftDeriv2` representative
family, by first producing the endpoint-window frontier. -/
theorem lapL2sq_continuousOn_before_of_zeroSlabRepresentativeBefore
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ} {F : ℝ → ℝ → ℝ}
    (h : H1LiftDeriv2ZeroSlabRepresentativeBefore u T F) :
    ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b) :=
  lapL2sq_continuousOn_before_of_endpoint
    (H1LapComponentEndpointContinuousBefore_of_zeroSlabRepresentativeBefore h)

#print axioms lapL2sq_continuousOn_Icc_of_liftDeriv2_jointContinuousOn
#print axioms lapL2sq_continuousOn_Icc_of_strictSlab_interior_eq_continuous
#print axioms lapL2sq_continuousOn_strictWindow_of_liftDeriv2_jointContinuousBefore
#print axioms lapL2sq_continuousOn_strictWindow_of_strictSlab_interior_eq_continuous
#print axioms lapL2sq_continuousOn_before_of_endpoint_and_strict
#print axioms lapL2sq_continuousOn_before_of_endpoint
#print axioms lapL2sq_continuousOn_Icc_zero_of_zeroRight_and_strict
#print axioms H1LapComponentEndpointContinuousBefore_of_zeroRight_and_strict
#print axioms
  H1LapComponentEndpointContinuousBefore_of_zeroRight_and_liftDeriv2_jointContinuousBefore
#print axioms
  H1LapComponentEndpointContinuousBefore_of_zeroRight_and_strictSlab_interior_eq_continuous
#print axioms lapL2sq_continuousWithinAt_zero_of_zeroSlab_interior_eq_continuous
#print axioms H1LapComponentZeroRightContinuous_of_zeroSlab_interior_eq_continuous
#print axioms H1LapComponentZeroRightContinuous_of_zeroSlabRepresentative
#print axioms H1LapComponentZeroRightContinuous_of_hasZeroSlabRepresentative
#print axioms
  H1LapEndpointBefore_of_hasZeroSlabRep_and_liftDeriv2
#print axioms
  H1LapEndpointBefore_of_hasZeroSlabRep_and_strictSlab
#print axioms
  H1LapComponentEndpointContinuousBefore_of_zeroSlab_interior_eq_continuous
#print axioms H1LapComponentEndpointContinuousBefore_of_zeroSlabRepresentativeBefore
#print axioms lapL2sq_continuousOn_before_of_zeroSlabRepresentativeBefore

end ShenWork.Paper2.IntervalChiNegH1LapComponentContinuity
