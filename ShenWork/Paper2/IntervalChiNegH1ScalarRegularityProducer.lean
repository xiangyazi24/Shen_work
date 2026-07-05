import ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer
import ShenWork.Paper2.IntervalChiNegH1EnergyIdentity

/-!
# H¹ scalar regularity producer

This file packages the honest part of the H¹ scalar regularity frontier:
`u_xx` L¹-continuity in time gives closed-window continuity of `H1energy`,
provided the time-zero right-continuity is supplied explicitly.  Derivative
interval-integrability remains a separate scalar FTC input.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1AverageWiring
open ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer

/-- Closed-window joint continuity of the lifted second spatial derivative.

This is a deliberately strong scalar regularity input: it is exactly the
Heine-Cantor hypothesis needed to discharge the L¹ time-continuity frontier for
`u_xx`, without using PDE-specific physical estimates. -/
structure H1LiftDeriv2JointContinuousBefore
    (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop where
  cont : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
    ContinuousOn (Function.uncurry (fun t x => liftDeriv2 u t x))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)

/-- Joint continuity of `u_xx` on every strict closed time slab gives the
L¹-continuity frontier used by the finite-difference H¹ identity producer. -/
theorem H1UxxL1ContBefore_of_liftDeriv2_jointContinuousBefore
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (h : H1LiftDeriv2JointContinuousBefore u T) :
    H1UxxL1ContBefore u T := by
  rw [H1UxxL1ContBefore]
  intro τ hτ0 hτT ε hε
  let η : ℝ := min (τ / 2) ((T - τ) / 2)
  have hηpos : 0 < η := by
    dsimp [η]
    exact lt_min (half_pos hτ0) (half_pos (sub_pos.mpr hτT))
  let a : ℝ := τ - η
  let b : ℝ := τ + η
  have ha_pos : 0 < a := by
    dsimp [a, η]
    have hle : min (τ / 2) ((T - τ) / 2) ≤ τ / 2 := min_le_left _ _
    linarith [half_pos hτ0]
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith [hηpos.le]
  have hbT : b < T := by
    dsimp [b, η]
    have hle : min (τ / 2) ((T - τ) / 2) ≤ (T - τ) / 2 := min_le_right _ _
    linarith
  have hτI : τ ∈ Set.Icc a b := by
    constructor <;> dsimp [a, b] <;> linarith [hηpos.le]
  have hcont : ContinuousOn (Function.uncurry (fun t x => liftDeriv2 u t x))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    h.cont ha_pos hab hbT
  have hcompact : IsCompact (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have huc : UniformContinuousOn
      (Function.uncurry (fun t x => liftDeriv2 u t x))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    hcompact.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δu, hδu_pos, hmod⟩ := huc ε hε
  refine ⟨min δu η, lt_min hδu_pos hηpos, ?_⟩
  intro s hsclose _hsIoo
  have hsδu : |s - τ| < δu := lt_of_lt_of_le hsclose (min_le_left _ _)
  have hsη : |s - τ| < η := lt_of_lt_of_le hsclose (min_le_right _ _)
  have hsI : s ∈ Set.Icc a b := by
    have hsabs := abs_lt.mp hsη
    constructor <;> dsimp [a, b] <;> linarith
  have hslice_s : ContinuousOn (fun x => liftDeriv2 u s x) (Set.Icc (0 : ℝ) 1) := by
    have hmaps : Set.MapsTo (fun x : ℝ => ((s, x) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
      intro x hx
      exact Set.mem_prod.mpr ⟨hsI, hx⟩
    have hpair : ContinuousOn (fun x : ℝ => ((s, x) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const.prodMk continuousOn_id
    have hcomp := hcont.comp hpair hmaps
    simpa [Function.comp_def, Function.uncurry] using hcomp
  have hslice_τ : ContinuousOn (fun x => liftDeriv2 u τ x) (Set.Icc (0 : ℝ) 1) := by
    have hmaps : Set.MapsTo (fun x : ℝ => ((τ, x) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
      intro x hx
      exact Set.mem_prod.mpr ⟨hτI, hx⟩
    have hpair : ContinuousOn (fun x : ℝ => ((τ, x) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const.prodMk continuousOn_id
    have hcomp := hcont.comp hpair hmaps
    simpa [Function.comp_def, Function.uncurry] using hcomp
  have hdiff_cont : ContinuousOn
      (fun x => ‖liftDeriv2 u s x - liftDeriv2 u τ x‖)
      (Set.Icc (0 : ℝ) 1) :=
    (hslice_s.sub hslice_τ).norm
  have hleft_int : IntervalIntegrable
      (fun x => ‖liftDeriv2 u s x - liftDeriv2 u τ x‖) volume 0 1 :=
    hdiff_cont.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hright_int : IntervalIntegrable (fun _x : ℝ => ε) volume 0 1 :=
    intervalIntegrable_const
  have hpoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖liftDeriv2 u s x - liftDeriv2 u τ x‖ ≤ ε := by
    intro x hx
    have hp_s : ((s, x) : ℝ × ℝ) ∈ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1 :=
      Set.mem_prod.mpr ⟨hsI, hx⟩
    have hp_τ : ((τ, x) : ℝ × ℝ) ∈ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1 :=
      Set.mem_prod.mpr ⟨hτI, hx⟩
    have hdist : dist ((s, x) : ℝ × ℝ) ((τ, x) : ℝ × ℝ) < δu := by
      rw [Prod.dist_eq]
      simp only [dist_self]
      rw [max_eq_left dist_nonneg]
      simpa [Real.dist_eq] using hsδu
    have hlt := hmod (s, x) hp_s (τ, x) hp_τ hdist
    simpa [Function.uncurry, dist_eq_norm] using le_of_lt hlt
  have hmono := intervalIntegral.integral_mono_on
    (by norm_num : (0 : ℝ) ≤ 1) hleft_int hright_int hpoint
  simpa [liftDeriv2, intervalIntegral.integral_const] using hmono

/-- `u_xx` L¹ time-continuity gives `ContinuousOn` of the H¹ energy on every
closed pre-horizon interval, once the right-continuity at `t = 0` is supplied.
-/
theorem H1energy_continuousOn_before_of_uxxL1Cont
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hcont0 : ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) 0) :
    ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn (H1energy u) (Set.Icc a b) := by
  intro a b ha _hab hb x hx
  by_cases hx0 : x = 0
  · subst x
    have hsub : Set.Icc a b ⊆ Set.Ici (0 : ℝ) := by
      intro y hy
      exact le_trans ha hy.1
    exact hcont0.mono_left (nhdsWithin_mono 0 hsub)
  · have hx_nonneg : 0 ≤ x := le_trans ha hx.1
    have hxpos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx0)
    have hxT : x < T := lt_of_le_of_lt hx.2 hb
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) T := ⟨hxpos, hxT⟩
    have huxx_raw := hUxxL1 x hxpos hxT
    have huxx :
        ∀ ε > 0, ∃ δ > 0,
          ∀ s, |s - x| < δ → s ∈ Set.Ioo (0 : ℝ) T →
            ∫ y in (0 : ℝ)..1,
              ‖liftDeriv2 u s y - liftDeriv2 u x y‖ ≤ ε := by
      simpa [H1UxxL1ContBefore, liftDeriv2] using huxx_raw
    exact
      (H1energy_hasDerivAt_of_uxxL1Cont hsol hxIoo huxx).continuousAt.continuousWithinAt

/-- Package separately supplied scalar continuity and derivative-integrability
fields into the H¹ scalar regularity record. -/
theorem H1ScalarRegularityBefore_of_hcont_and_hderivInt
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hcont : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn (H1energy u) (Set.Icc a b))
    (hderivInt : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      IntervalIntegrable (fun r => deriv (H1energy u) r) volume a b) :
    H1ScalarRegularityBefore u T where
  hcont := hcont
  hderivInt := hderivInt

/-- Direct scalar-regularity producer from the proved H¹ energy continuity
bridge plus the still-carried derivative-integrability field. -/
theorem H1ScalarRegularityBefore_of_uxxL1Cont_and_hderivInt
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hcont0 : ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) 0)
    (hderivInt : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      IntervalIntegrable (fun r => deriv (H1energy u) r) volume a b) :
    H1ScalarRegularityBefore u T :=
  H1ScalarRegularityBefore_of_hcont_and_hderivInt
    (H1energy_continuousOn_before_of_uxxL1Cont hsol hUxxL1 hcont0)
    hderivInt

/-- Direct scalar-DI producer after the H¹ continuity bridge, still carrying
derivative-integrability and the pointwise identity/RHS-bound package. -/
theorem H1ScalarDIOnBefore_of_identityRHSBound_uxxL1Cont
    {p : CM2Params} {T A B : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hcont0 : ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) 0)
    (hderivInt : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      IntervalIntegrable (fun r => deriv (H1energy u) r) volume a b)
    (hId : H1IdentityRHSBoundBefore p u T A B) :
    H1ScalarDIOnBefore u T A B :=
  H1ScalarDIOnBefore_of_identityRHSBound
    (H1ScalarRegularityBefore_of_uxxL1Cont_and_hderivInt
      hsol hUxxL1 hcont0 hderivInt)
    hId

#print axioms H1energy_continuousOn_before_of_uxxL1Cont
#print axioms H1UxxL1ContBefore_of_liftDeriv2_jointContinuousBefore
#print axioms H1ScalarRegularityBefore_of_hcont_and_hderivInt
#print axioms H1ScalarRegularityBefore_of_uxxL1Cont_and_hderivInt
#print axioms H1ScalarDIOnBefore_of_identityRHSBound_uxxL1Cont

end ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer
