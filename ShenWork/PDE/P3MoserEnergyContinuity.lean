import ShenWork.PDE.IntervalDomainAPrioriGlobal
import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
import ShenWork.Paper2.IntervalDomainLpTimeLeibniz

/-!
# Energy continuity from classical solution joint continuity

This file proves `ContinuousOn (fun t => intervalDomain.integral (fun x => (u t x) ^ p)) S`
for `S ⊆ Ioo 0 T` from:
- Conjunct (9) of `intervalDomainClassicalRegularity`: joint continuity of
  `(t,x) ↦ intervalDomainLift (u t) x` on `Ioo 0 T ×ˢ Icc 0 1`
- Positivity: `u t x > 0` for interior times

The key Mathlib tool is `intervalIntegral.continuousWithinAt_of_dominated_interval`.
-/

open MeasureTheory Set Filter
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

local instance : TopologicalSpace intervalDomain.Point :=
  inferInstanceAs (TopologicalSpace intervalDomainPoint)

/-- Extract conjunct (9) from the classical solution: joint continuity of the
solution field on `Ioo 0 T ×ˢ Icc 0 1`. -/
theorem intervalDomain_solution_jointContinuousOn
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  hsol.2.1.2.2.2.2.2.2.1

/-- Joint continuity of `(t,x) ↦ (intervalDomainLift (u t) x) ^ p` on
`Ioo 0 T ×ˢ Icc 0 1` for a positive classical solution. -/
theorem intervalDomain_power_jointContinuousOn
    {params : CM2Params} {T p : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ContinuousOn
      (fun tx : ℝ × ℝ => (intervalDomainLift (u tx.1) tx.2) ^ p)
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
  have hj := intervalDomain_solution_jointContinuousOn hsol
  have hj' : ContinuousOn
      (fun tx : ℝ × ℝ => intervalDomainLift (u tx.1) tx.2)
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := hj
  exact ContinuousOn.rpow hj' continuousOn_const
    (fun ⟨t, x⟩ ⟨ht, hx⟩ =>
      Or.inl (ne_of_gt (intervalDomain_solution_lift_u_pos hsol ht.1 ht.2 hx)))

/-- On a compact sub-slab `[a,b] × [0,1] ⊆ (0,T) × [0,1]`, the integrand
`(intervalDomainLift (u t) x) ^ p` is bounded. -/
theorem intervalDomain_power_bounded_on_slab
    {params : CM2Params} {T p a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ha : 0 < a) (hb : b < T) (hab : a ≤ b) :
    ∃ C, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖(intervalDomainLift (u t) x) ^ p‖ ≤ C := by
  have hcompact : IsCompact (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hsub : Icc a b ×ˢ Icc (0 : ℝ) 1 ⊆ Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1 :=
    prod_mono (Icc_subset_Ioo ha hb) Subset.rfl
  have hcont := (intervalDomain_power_jointContinuousOn hsol (p := p)).mono hsub
  have hcont_norm : ContinuousOn
      (fun tx : ℝ × ℝ => ‖(intervalDomainLift (u tx.1) tx.2) ^ p‖)
      (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    continuous_norm.comp_continuousOn hcont
  have hne : (Icc a b ×ˢ Icc (0 : ℝ) 1).Nonempty :=
    ⟨⟨a, 0⟩, ⟨le_refl a, hab⟩, ⟨le_refl 0, zero_le_one⟩⟩
  rcases hcompact.exists_isMaxOn hne hcont_norm with ⟨⟨t₀, x₀⟩, _, hmax⟩
  exact ⟨‖(intervalDomainLift (u t₀) x₀) ^ p‖,
    fun t ht x hx => hmax (show (t, x) ∈ Icc a b ×ˢ Icc (0 : ℝ) 1 from ⟨ht, hx⟩)⟩

/-- Energy continuity on the open interior `(0,T)`: the map
`t ↦ ∫₀¹ u(t,x)^p dx` is continuous on `Ioo 0 T` for a positive classical
interval-domain solution.

Uses `intervalIntegral.continuousWithinAt_of_dominated_interval` with the
compact-slab bound from `intervalDomain_power_bounded_on_slab`. -/
theorem intervalDomain_energyContinuousOn_Ioo
    {params : CM2Params} {T p : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ContinuousOn
      (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
      (Ioo (0 : ℝ) T) := by
  rw [ContinuousOn]
  intro t₀ ht₀
  have hderiv :
      HasDerivAt (fun s => intervalDomainPowerEnergy p u s)
        (∫ y in (0 : ℝ)..1, intervalDomainPowerDeriv p u t₀ y) t₀ :=
    intervalDomainPowerEnergy_hasDerivAt (q := p) hsol ht₀
  have henergy :
      (fun t => intervalDomain.integral (fun x => (u t x) ^ p)) =
        fun t => intervalDomainPowerEnergy p u t := by
    funext t
    unfold intervalDomainPowerEnergy
    change intervalDomainIntegral (fun x => (u t x) ^ p) = _
    unfold intervalDomainIntegral
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le (zero_le_one)] at hy
    simp [intervalDomainLift, hy]
  rw [henergy]
  exact hderiv.continuousAt.continuousWithinAt

/-- Endpoint continuity data needed to upgrade the already-proved interior
energy continuity to the closed interval `[0,T]`.

This is honest: `IsPaper2ClassicalSolution` currently controls interior times,
while the closed regularity field also asks about the values at `0` and `T`. -/
structure IntervalDomainPowerEnergyEndpointContinuity
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  atZero :
    ∀ p, p0 ≤ p →
      ContinuousWithinAt
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T) 0
  atRight :
    ∀ p, p0 ≤ p →
      ContinuousWithinAt
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T) T

/-- The remaining left-endpoint power-energy continuity residual.

`InitialTrace intervalDomain u₀ u` only controls positive times and does not
identify the stored value `u 0` with `u₀`, so this is kept as an explicit
closed-time endpoint compatibility input. -/
def IntervalDomainInitialPowerEnergyContinuityAtZero
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    ContinuousWithinAt
      (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
      (Set.Icc (0 : ℝ) T) 0

/-- Deleted-right trace convergence of power energies to the prescribed initial
datum energy.  This deliberately does not constrain the stored slice `u 0`. -/
def IntervalDomainInitialTracePowerEnergyTendsto
    (u₀ : intervalDomain.Point → ℝ)
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    Tendsto
      (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
      (nhdsWithin 0 (Set.Ioc (0 : ℝ) T))
      (nhds (intervalDomain.integral (fun x => (u₀ x) ^ p)))

/-- Exact zero-slice compatibility needed by the power-energy endpoint.  The
stronger pointwise condition `u 0 = u₀` implies this, but the Moser endpoint only
uses equality of all relevant power energies. -/
def IntervalDomainInitialPowerEnergyCompatibleAtZero
    (u₀ : intervalDomain.Point → ℝ)
    (u : ℝ → intervalDomain.Point → ℝ) (p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    intervalDomain.integral (fun x => (u 0 x) ^ p) =
      intervalDomain.integral (fun x => (u₀ x) ^ p)

/-- Pointwise zero-slice compatibility is a sufficient source of the energy-level
compatibility package. -/
theorem intervalDomain_initialPowerEnergyCompatibleAtZero_of_eq
    {p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (h0 : u 0 = u₀) :
    IntervalDomainInitialPowerEnergyCompatibleAtZero u₀ u p0 := by
  intro p _hp
  rw [h0]

/-- Replace only the stored zero-time slice of a trajectory by the prescribed
initial datum.  Positive-time PDE/classical statements are unaffected. -/
def intervalDomainWithInitialSlice
    (u₀ : intervalDomain.Point → ℝ)
    (u : ℝ → intervalDomain.Point → ℝ) :
    ℝ → intervalDomain.Point → ℝ :=
  fun t x => if t = 0 then u₀ x else u t x

/-- The re-anchored trajectory agrees with the raw trajectory at every
strictly positive time. -/
theorem intervalDomainWithInitialSlice_eq_raw_of_pos
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    {t : ℝ} (ht : 0 < t) :
    intervalDomainWithInitialSlice u₀ u t = u t := by
  funext x
  simp [intervalDomainWithInitialSlice, ne_of_gt ht]

/-- Pointwise form of `intervalDomainWithInitialSlice_eq_raw_of_pos`. -/
theorem intervalDomainWithInitialSlice_eq_raw_of_pos_apply
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    {t : ℝ} (ht : 0 < t) (x : intervalDomain.Point) :
    intervalDomainWithInitialSlice u₀ u t x = u t x := by
  simpa using congrFun
    (intervalDomainWithInitialSlice_eq_raw_of_pos
      (u₀ := u₀) (u := u) ht) x

/-- The re-anchored trajectory has exact zero-slice power-energy
compatibility. -/
theorem intervalDomain_initialPowerEnergyCompatibleAtZero_withInitialSlice
    {p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ} :
    IntervalDomainInitialPowerEnergyCompatibleAtZero u₀
      (intervalDomainWithInitialSlice u₀ u) p0 := by
  intro p _hp
  simp [intervalDomainWithInitialSlice]

/-- Re-anchoring at `t = 0` preserves the deleted-right initial trace. -/
theorem intervalDomain_initialTrace_withInitialSlice
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (htrace : InitialTrace intervalDomain u₀ u) :
    InitialTrace intervalDomain u₀
      (intervalDomainWithInitialSlice u₀ u) := by
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := htrace ε hε
  refine ⟨δ, hδ, ?_⟩
  intro t ht0 htδ
  have ht_ne : t ≠ 0 := ne_of_gt ht0
  simpa [intervalDomainWithInitialSlice, ht_ne] using hsmall t ht0 htδ

/-- Re-anchoring at `t = 0` preserves interval-domain classical solutions,
because the predicate is local on the strict time slab `(0,T)`. -/
theorem intervalDomain_classical_withInitialSlice
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    IsPaper2ClassicalSolution intervalDomain params T
      (intervalDomainWithInitialSlice u₀ u) v := by
  exact
    (classicalSolutionLocalityUnderIooAgreement_intervalDomain params)
      hsol.T_pos hsol (by
        intro t ht0 _htT x
        have ht_ne : t ≠ 0 := ne_of_gt ht0
        simp [intervalDomainWithInitialSlice, ht_ne])

/-- Re-anchoring at `t = 0` preserves global interval-domain classical
solutions. -/
theorem intervalDomain_globalClassical_withInitialSlice
    {params : CM2Params}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v) :
    IsPaper2GlobalClassicalSolution intervalDomain params
      (intervalDomainWithInitialSlice u₀ u) v := by
  intro T hT
  exact
    (classicalSolutionLocalityUnderIooAgreement_intervalDomain params)
      hT (hglobal.classical hT) (by
        intro t ht0 _htT x
        have ht_ne : t ≠ 0 := ne_of_gt ht0
        simp [intervalDomainWithInitialSlice, ht_ne])

/-- Raw gradient time-integrability transfers to the re-anchored
representative.  The two time integrands differ only at `t = 0`, a null time
for the restricted Lebesgue measure on `Set.uIcc 0 T`. -/
theorem intervalDomain_gradientTimeIntegrable_withInitialSlice_of_raw
    {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hraw :
      ∀ p, p0 ≤ p →
        IntegrableOn
          (fun t =>
            intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => (u t y) ^ (p / 2)) x) ^ 2))
          (Set.uIcc (0 : ℝ) T) volume) :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y =>
                ((intervalDomainWithInitialSlice u₀ u) t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume := by
  intro p hp
  have hraw' :
      Integrable
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (volume.restrict (Set.uIcc (0 : ℝ) T)) :=
    hraw p hp
  have hae :
      (fun t =>
        intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y =>
              ((intervalDomainWithInitialSlice u₀ u) t y) ^ (p / 2)) x) ^ 2))
        =ᵐ[volume.restrict (Set.uIcc (0 : ℝ) T)]
      (fun t =>
        intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y => (u t y) ^ (p / 2)) x) ^ 2)) := by
    change
      ∀ᵐ t ∂(volume.restrict (Set.uIcc (0 : ℝ) T)),
        intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y =>
              ((intervalDomainWithInitialSlice u₀ u) t y) ^ (p / 2)) x) ^ 2) =
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2)
    rw [ae_restrict_iff' measurableSet_uIcc]
    have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ (0 : ℝ) := by
      simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
    filter_upwards [hne] with t ht_ne _ht_mem
    have hslice :
        (fun y : intervalDomain.Point =>
            ((intervalDomainWithInitialSlice u₀ u) t y) ^ (p / 2)) =
          (fun y : intervalDomain.Point => (u t y) ^ (p / 2)) := by
      funext y
      simp [intervalDomainWithInitialSlice, ht_ne]
    simp [hslice]
  change
    Integrable
      (fun t =>
        intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y =>
              ((intervalDomainWithInitialSlice u₀ u) t y) ^ (p / 2)) x) ^ 2))
      (volume.restrict (Set.uIcc (0 : ℝ) T))
  exact hraw'.congr hae.symm

/-- Continuity of the concrete interval-domain lift on `[0,1]` from subtype
continuity.  The full zero extension need not be continuous on all of `ℝ`. -/
theorem intervalDomain_lift_continuousOn_Icc_of_continuous
    {f : intervalDomain.Point → ℝ} (hf : Continuous f) :
    ContinuousOn (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift f) = f := by
    funext ⟨y, hy⟩
    simp only [Set.restrict_apply, intervalDomainLift]
    rw [dif_pos hy]
    exact congr_arg f (Subtype.ext rfl)
  rw [heq]
  exact hf

/-- For a bounded slice, the concrete interval-domain sup norm dominates every
pointwise absolute value. -/
theorem intervalDomain_abs_le_supNorm_of_bddAbove
    {f : intervalDomain.Point → ℝ}
    (hbdd : BddAbove (Set.range (fun x : intervalDomain.Point => |f x|))) :
    ∀ x : intervalDomain.Point, |f x| ≤ intervalDomain.supNorm f := by
  intro x
  change |f x| ≤ intervalDomainSupNorm f
  unfold intervalDomainSupNorm
  exact le_csSup hbdd ⟨x, rfl⟩

/-- If the concrete sup norm is strictly below `ε`, then every pointwise
absolute value is strictly below `ε`. -/
theorem intervalDomain_pointwise_abs_lt_of_supNorm_lt
    {f : intervalDomain.Point → ℝ} {ε : ℝ}
    (hbdd : BddAbove (Set.range (fun x : intervalDomain.Point => |f x|)))
    (hsup : intervalDomain.supNorm f < ε) :
    ∀ x : intervalDomain.Point, |f x| < ε := by
  intro x
  exact lt_of_le_of_lt
    (intervalDomain_abs_le_supNorm_of_bddAbove hbdd x) hsup

/-- If two slices are bounded in absolute value, so is their difference. -/
theorem bddAbove_abs_sub_of_bddAbove_abs
    {X : Type*} {f g : X → ℝ}
    (hf : BddAbove (Set.range (fun x : X => |f x|)))
    (hg : BddAbove (Set.range (fun x : X => |g x|))) :
    BddAbove (Set.range (fun x : X => |f x - g x|)) := by
  obtain ⟨Mf, hMf⟩ := hf
  obtain ⟨Mg, hMg⟩ := hg
  refine ⟨Mf + Mg, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hf_le : |f x| ≤ Mf := hMf ⟨x, rfl⟩
  have hg_le : |g x| ≤ Mg := hMg ⟨x, rfl⟩
  calc
    |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
    _ ≤ Mf + Mg := add_le_add hf_le hg_le

/-- Paper-positive interval-domain data are bounded in absolute value. -/
theorem intervalDomain_bddAbove_abs_of_paperPositiveInitialDatum
    {u₀ : intervalDomain.Point → ℝ}
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀) :
    BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)) := by
  have hAdm := PaperPositiveInitialDatum.admissible hdatum
  change BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)) ∧
      Continuous u₀ at hAdm
  exact hAdm.1

/-- Paper-positive initial data have integrable real powers on the concrete
interval domain. -/
theorem intervalDomain_u0_rpow_intervalIntegrable_of_paperPositive
    {u₀ : intervalDomain.Point → ℝ} {p : ℝ}
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀) :
    IntervalIntegrable
      (intervalDomainLift (fun x : intervalDomain.Point => (u₀ x) ^ p))
      volume 0 1 := by
  have hAdm := PaperPositiveInitialDatum.admissible hdatum
  have hcont_u₀ : Continuous u₀ := by
    change BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)) ∧
        Continuous u₀ at hAdm
    exact hAdm.2
  obtain ⟨η, hη, hfloor⟩ := PaperPositiveInitialDatum.floor hdatum
  have hcont_lift : ContinuousOn (intervalDomainLift u₀) (Set.Icc (0 : ℝ) 1) :=
    intervalDomain_lift_continuousOn_Icc_of_continuous hcont_u₀
  have hne :
      ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift u₀ y ≠ 0 := by
    intro y hy
    let x : intervalDomain.Point := ⟨y, hy⟩
    have hpos : 0 < u₀ x := lt_of_lt_of_le hη (hfloor x)
    have hlift : intervalDomainLift u₀ y = u₀ x := by
      simp [intervalDomainLift, x, hy]
    exact ne_of_gt (by simpa [hlift] using hpos)
  have hcont_power : ContinuousOn
      (fun y => (intervalDomainLift u₀ y) ^ p) (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact hcont_lift.rpow_const (fun y hy => Or.inl (hne y hy))
  have hcont_lift_power : ContinuousOn
      (intervalDomainLift (fun x : intervalDomain.Point => (u₀ x) ^ p))
      (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one] at hcont_power ⊢
    refine hcont_power.congr ?_
    intro y hy
    simp [intervalDomainLift, hy]
  exact hcont_lift_power.intervalIntegrable

/-- On a compact interval bounded away from zero, `r ↦ r ^ p` is uniformly
continuous for every real exponent `p`. -/
theorem real_rpow_uniformContinuousOn_Icc_of_pos_left
    {p a b : ℝ} (ha : 0 < a) :
    UniformContinuousOn (fun r : ℝ => r ^ p) (Set.Icc a b) := by
  have hcont : ContinuousOn (fun r : ℝ => r ^ p) (Set.Icc a b) := by
    exact continuousOn_id.rpow_const
      (fun r hr => Or.inl (ne_of_gt (lt_of_lt_of_le ha hr.1)))
  exact isCompact_Icc.uniformContinuousOn_of_continuous hcont

/-- On the concrete unit interval, a uniform pointwise bound controls the
absolute difference of integrals. -/
theorem intervalDomain_integral_sub_abs_le_of_pointwise_abs_le
    {f g : intervalDomain.Point → ℝ} {ε : ℝ}
    (_hε : 0 ≤ ε)
    (hf_int : IntervalIntegrable (intervalDomainLift f) volume 0 1)
    (hg_int : IntervalIntegrable (intervalDomainLift g) volume 0 1)
    (hpoint : ∀ x : intervalDomain.Point, |f x - g x| ≤ ε) :
    |intervalDomain.integral f - intervalDomain.integral g| ≤ ε := by
  change |intervalDomainIntegral f - intervalDomainIntegral g| ≤ ε
  unfold intervalDomainIntegral
  rw [← intervalIntegral.integral_sub hf_int hg_int]
  have hnorm :
      ‖∫ y in (0 : ℝ)..1,
          (intervalDomainLift f y - intervalDomainLift g y)‖ ≤
        ε * |(1 : ℝ) - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le zero_le_one] at hy
      exact ⟨le_of_lt hy.1, hy.2⟩
    let x : intervalDomain.Point := ⟨y, hyIcc⟩
    have hf_lift : intervalDomainLift f y = f x := by
      simp [intervalDomainLift, x, hyIcc]
    have hg_lift : intervalDomainLift g y = g x := by
      simp [intervalDomainLift, x, hyIcc]
    simpa [Real.norm_eq_abs, hf_lift, hg_lift] using hpoint x
  simpa [Real.norm_eq_abs] using hnorm

/-- The trace-difference slice is bounded at every positive time. -/
theorem intervalDomain_traceDiff_slice_abs_bddAbove_of_global
    {params : CM2Params} {t : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (ht0 : 0 < t)
    (hu₀_bdd : BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|))) :
    BddAbove (Set.range
      (fun x : intervalDomain.Point => |u t x - u₀ x|)) := by
  have hTpos : 0 < t + 1 := by linarith
  have hsol : IsPaper2ClassicalSolution intervalDomain params (t + 1) u v :=
    hglobal.classical hTpos
  have htmem : t ∈ Set.Ioo (0 : ℝ) (t + 1) := by
    exact ⟨ht0, by linarith⟩
  have hut_bdd : BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|)) :=
    intervalDomain_solution_slice_abs_bddAbove hsol htmem
  exact bddAbove_abs_sub_of_bddAbove_abs hut_bdd hu₀_bdd

/-- Initial trace gives pointwise control of `u t - u₀` at small positive times. -/
theorem intervalDomain_initialTrace_pointwise_abs_lt
    {params : CM2Params} {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (htrace : InitialTrace intervalDomain u₀ u)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hu₀_bdd : BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x : intervalDomain.Point, |u t x - u₀ x| < ε := by
  obtain ⟨δ, hδ, hδsmall⟩ := InitialTrace.eventually_small htrace hε
  refine ⟨δ, hδ, ?_⟩
  intro t ht0 htδ x
  have hdiff_bdd :
      BddAbove (Set.range
        (fun x : intervalDomain.Point => |u t x - u₀ x|)) :=
    intervalDomain_traceDiff_slice_abs_bddAbove_of_global
      (params := params) (t := t) (u₀ := u₀) (u := u) (v := v)
      hglobal ht0 hu₀_bdd
  exact intervalDomain_pointwise_abs_lt_of_supNorm_lt hdiff_bdd
    (hδsmall t ht0 htδ) x

/-- Deleted-right convergence of power energies to the prescribed initial-datum
energy, derived from the initial trace, paper-positive datum, and positive-time
classical regularity. -/
theorem intervalDomain_initialTracePowerEnergyTendsto_of_paperPositive
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v) :
    IntervalDomainInitialTracePowerEnergyTendsto u₀ u T p0 := by
  intro p _hp
  obtain ⟨η, hη, hfloor⟩ := PaperPositiveInitialDatum.floor hdatum
  have hη2 : 0 < η / 2 := by linarith
  have hu₀_bdd :
      BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)) :=
    intervalDomain_bddAbove_abs_of_paperPositiveInitialDatum hdatum
  obtain ⟨Mraw, hMraw⟩ := hu₀_bdd
  let M : ℝ := max (max Mraw 1) η + 1
  have hu₀_abs_le_M : ∀ x : intervalDomain.Point, |u₀ x| ≤ M := by
    intro x
    have hxraw : |u₀ x| ≤ Mraw := hMraw ⟨x, rfl⟩
    have hMraw_le : Mraw ≤ max Mraw 1 := le_max_left _ _
    have hmax_le : max Mraw 1 ≤ max (max Mraw 1) η := le_max_left _ _
    dsimp [M]
    linarith
  have hu₀_le_M : ∀ x : intervalDomain.Point, u₀ x ≤ M := by
    intro x
    exact le_trans (le_abs_self _) (hu₀_abs_le_M x)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have huc :
      UniformContinuousOn (fun r : ℝ => r ^ p) (Set.Icc (η / 2) (M + 1)) :=
    real_rpow_uniformContinuousOn_Icc_of_pos_left hη2
  obtain ⟨δpow, hδpow, hpow⟩ :=
    Metric.uniformContinuousOn_iff.mp huc (ε / 2) hε2
  let traceRad : ℝ := min (min (η / 2) 1) (δpow / 2)
  have hδpow2 : 0 < δpow / 2 := by linarith
  have htraceRad : 0 < traceRad := by
    dsimp [traceRad]
    exact lt_min (lt_min hη2 (by norm_num)) hδpow2
  obtain ⟨δtrace, hδtrace_pos, hδtrace⟩ :=
    intervalDomain_initialTrace_pointwise_abs_lt
      (params := params) (u₀ := u₀) (u := u) (v := v)
      htrace hglobal (⟨Mraw, hMraw⟩ :
        BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
      htraceRad
  let δ : ℝ := min δtrace T
  have hδ : 0 < δ := lt_min hδtrace_pos hT
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball]
  refine ⟨δ, hδ, ?_⟩
  intro t htball htIoc
  have htdist : dist t 0 < δ := by
    simpa [Metric.mem_ball] using htball
  have ht0 : 0 < t := htIoc.1
  have htδ : t < δ := by
    rw [Real.dist_eq] at htdist
    simpa [sub_zero, abs_of_nonneg ht0.le] using htdist
  have htδtrace : t < δtrace := lt_of_lt_of_le htδ (min_le_left _ _)
  have hpoint_close :
      ∀ x : intervalDomain.Point, |u t x - u₀ x| < traceRad :=
    hδtrace t ht0 htδtrace
  have hpow_point :
      ∀ x : intervalDomain.Point,
        |(u t x) ^ p - (u₀ x) ^ p| ≤ ε / 2 := by
    intro x
    have hclose := hpoint_close x
    have htr_eta : traceRad ≤ η / 2 := by
      dsimp [traceRad]
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    have htr_one : traceRad ≤ 1 := by
      dsimp [traceRad]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    have htr_pow : traceRad ≤ δpow := by
      dsimp [traceRad]
      have hhalf : δpow / 2 ≤ δpow := by linarith
      exact le_trans (min_le_right _ _) hhalf
    have hut_lower : η / 2 ≤ u t x := by
      have hleft := (abs_lt.mp hclose).1
      linarith [hfloor x, htr_eta]
    have hut_upper : u t x ≤ M + 1 := by
      have hright := (abs_lt.mp hclose).2
      linarith [hu₀_le_M x, htr_one]
    have hu₀_mem : u₀ x ∈ Set.Icc (η / 2) (M + 1) := by
      constructor
      · linarith [hfloor x]
      · linarith [hu₀_le_M x]
    have hut_mem : u t x ∈ Set.Icc (η / 2) (M + 1) :=
      ⟨hut_lower, hut_upper⟩
    have hdist_power_arg : dist (u t x) (u₀ x) < δpow := by
      rw [Real.dist_eq]
      exact lt_of_lt_of_le hclose htr_pow
    have hpd :
        dist ((u t x) ^ p) ((u₀ x) ^ p) < ε / 2 :=
      hpow (u t x) hut_mem (u₀ x) hu₀_mem hdist_power_arg
    rw [Real.dist_eq] at hpd
    exact le_of_lt hpd
  have hsolt : IsPaper2ClassicalSolution intervalDomain params (t + 1) u v :=
    hglobal.classical (by linarith : 0 < t + 1)
  have hut_int :
      IntervalIntegrable
        (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ p))
        volume 0 1 :=
    intervalDomain_u_rpow_intervalIntegrable_of_regularity
      (q := p) hsolt ht0 (by linarith : t < t + 1)
  have hu₀_int :
      IntervalIntegrable
        (intervalDomainLift (fun x : intervalDomain.Point => (u₀ x) ^ p))
        volume 0 1 :=
    intervalDomain_u0_rpow_intervalIntegrable_of_paperPositive hdatum
  have hIntClose :
      |intervalDomain.integral (fun x : intervalDomain.Point => (u t x) ^ p) -
        intervalDomain.integral (fun x : intervalDomain.Point => (u₀ x) ^ p)| ≤
        ε / 2 :=
    intervalDomain_integral_sub_abs_le_of_pointwise_abs_le
      (by linarith : 0 ≤ ε / 2) hut_int hu₀_int hpow_point
  rw [Real.dist_eq]
  linarith

/-- Deleted-right convergence to the initial-datum energy plus zero-slice
energy compatibility gives the current left-endpoint power-energy continuity
residual. -/
theorem
    intervalDomain_initialPowerEnergyContinuityAtZero_of_traceTendsto_compat
    {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hlim : IntervalDomainInitialTracePowerEnergyTendsto u₀ u T p0)
    (hcompat : IntervalDomainInitialPowerEnergyCompatibleAtZero u₀ u p0) :
    IntervalDomainInitialPowerEnergyContinuityAtZero u T p0 := by
  intro p hp
  let F : ℝ → ℝ := fun t =>
    intervalDomain.integral (fun x => (u t x) ^ p)
  have hlimF :
      Tendsto F
        (nhdsWithin 0 (Set.Ioc (0 : ℝ) T)) (nhds (F 0)) := by
    have hlimp := hlim p hp
    have hcompatp := hcompat p hp
    simpa [F, hcompatp] using hlimp
  rw [ContinuousWithinAt]
  rw [Filter.Tendsto] at hlimF ⊢
  intro S hS
  have hS0 : F 0 ∈ S := mem_of_mem_nhds hS
  have hIoc :
      {t : ℝ | F t ∈ S} ∈ nhdsWithin 0 (Set.Ioc (0 : ℝ) T) :=
    hlimF hS
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hIoc with
    ⟨U, hU, hUsub⟩
  refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨U, hU, ?_⟩
  intro t ht
  rcases ht with ⟨htU, htIcc⟩
  by_cases ht0 : t = 0
  · subst t
    exact hS0
  · have htIoc : t ∈ Set.Ioc (0 : ℝ) T := by
      exact
        ⟨lt_of_le_of_ne htIcc.1 (fun h : (0 : ℝ) = t => ht0 h.symm),
          htIcc.2⟩
    exact hUsub ⟨htU, htIoc⟩

/-- Initial power-energy continuity at zero for the re-anchored representative:
the raw trajectory supplies the deleted-right trace and positive-time global
classical branch, while the zero slice is fixed by construction. -/
theorem
    intervalDomain_initialPowerEnergyContinuityAtZero_of_trace_paperPositive_global_withInitialSlice
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v) :
    IntervalDomainInitialPowerEnergyContinuityAtZero
      (intervalDomainWithInitialSlice u₀ u) T p0 := by
  exact
    intervalDomain_initialPowerEnergyContinuityAtZero_of_traceTendsto_compat
      (intervalDomain_initialTracePowerEnergyTendsto_of_paperPositive
        hT
        (intervalDomain_initialTrace_withInitialSlice htrace)
        hdatum
        (intervalDomain_globalClassical_withInitialSlice hglobal))
      intervalDomain_initialPowerEnergyCompatibleAtZero_withInitialSlice

/-- Closed-interval energy continuity from the interior classical-solution
continuity theorem plus explicit endpoint continuity data. -/
theorem intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hend : IntervalDomainPowerEnergyEndpointContinuity u T p0) :
    ∀ p, p0 ≤ p →
      ContinuousOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T) := by
  intro p hp
  rw [ContinuousOn]
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    exact hend.atZero p hp
  by_cases htT : t = T
  · subst t
    exact hend.atRight p hp
  have htIoo : t ∈ Set.Ioo (0 : ℝ) T := by
    exact
      ⟨lt_of_le_of_ne ht.1 (fun h => ht0 h.symm),
       lt_of_le_of_ne ht.2 htT⟩
  have hcontWithin :
      ContinuousWithinAt
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Ioo (0 : ℝ) T) t :=
    intervalDomain_energyContinuousOn_Ioo (p := p) hsol t htIoo
  exact
    (hcontWithin.continuousAt (isOpen_Ioo.mem_nhds htIoo)).continuousWithinAt

/-- On the concrete interval domain, the abstract integrated-Moser energy
agrees with the interval-domain power energy used by the time-Leibniz theorem. -/
theorem intervalDomain_integratedMoserEnergy_eq_powerEnergy
    (p : ℝ) (u : ℝ → intervalDomain.Point → ℝ) :
    (fun t : ℝ => integratedMoserEnergy intervalDomain u p t) =
      fun t : ℝ => intervalDomainPowerEnergy p u t := by
  funext t
  unfold integratedMoserEnergy intervalDomainPowerEnergy
  change intervalDomainIntegral (fun x => (u t x) ^ p) =
    ∫ y in (0 : ℝ)..1, (intervalDomainLift (u t) y) ^ p
  unfold intervalDomainIntegral
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le zero_le_one] at hy
  simp [intervalDomainLift, hy]

/-- Explicit RHS derivative profile for the interval-domain power energy. -/
def intervalDomainPowerEnergyDerivIntegral
    (q : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (s : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1, intervalDomainPowerDeriv q u s y

/-- On a strict time window, the explicit interval-domain power-energy
derivative profile is continuous. -/
theorem intervalDomainPowerEnergyDerivIntegral_continuousOn_strictWindow
    {params : CM2Params} {T q a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ha : 0 < a) (_hab : a ≤ b) (hb : b < T) :
    ContinuousOn
      (fun s => intervalDomainPowerEnergyDerivIntegral q u s)
      (Set.Icc a b) := by
  intro s₀ hs₀
  set I : Set ℝ := Set.Icc a b with hIdef
  set K : Set (ℝ × ℝ) := I ×ˢ Set.Icc (0 : ℝ) 1 with hKdef
  set F : ℝ → ℝ → ℝ :=
    fun s y => intervalDomainPowerDeriv q u s y with hFdef
  have htime_sub : I ⊆ Set.Ioo (0 : ℝ) T := by
    rw [hIdef]
    exact Icc_subset_Ioo ha hb
  have hjoint_open :
      ContinuousOn
        (Function.uncurry (intervalDomainPowerDeriv q u))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    intervalDomainPowerDeriv_continuousOn (q := q) hsol
  have hFcont :
      ContinuousOn
        (Function.uncurry F)
        K := by
    rw [hFdef, hKdef]
    exact hjoint_open.mono (Set.prod_mono htime_sub Subset.rfl)
  have hKcompact : IsCompact K := by
    rw [hKdef, hIdef]
    exact isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hKcompact.bddAbove_image hFcont.norm
  set B' : ℝ := max B 0 with hB'def
  have hFbd : ∀ s ∈ I, ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖F s x‖ ≤ B' := by
    intro s hs x hx
    have hmem : (s, x) ∈ K := by
      rw [hKdef]
      exact Set.mem_prod.mpr ⟨hs, hx⟩
    have hBx : ‖Function.uncurry F (s, x)‖ ≤ B :=
      hB (Set.mem_image_of_mem _ hmem)
    have hBle : B ≤ B' := by
      rw [hB'def]
      exact le_max_left _ _
    have hle : ‖Function.uncurry F (s, x)‖ ≤ B' := le_trans hBx hBle
    simpa [Function.uncurry] using hle
  have hslice_cont :
      ∀ s ∈ I, ContinuousOn (F s) (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    have hmaps : Set.MapsTo (fun x : ℝ => ((s, x) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) K := by
      intro x hx
      rw [hKdef]
      exact Set.mem_prod.mpr ⟨hs, hx⟩
    have hpair_cont : ContinuousOn (fun x : ℝ => ((s, x) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const.prodMk continuousOn_id
    have hcomp : ContinuousOn
        ((Function.uncurry F) ∘ fun x : ℝ => ((s, x) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) :=
      hFcont.comp hpair_cont hmaps
    simpa [Function.comp_def, Function.uncurry] using hcomp
  have hint_cont :
      ContinuousWithinAt
        (fun s => ∫ x in (0 : ℝ)..1, F s x)
        I s₀ := by
    refine intervalIntegral.continuousWithinAt_of_dominated_interval
      (bound := fun _x : ℝ => B') ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs_cont_uIcc : ContinuousOn (F s) (Set.uIcc (0 : ℝ) 1) := by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact hslice_cont s hs
      exact
        (hs_cont_uIcc.mono Set.uIoc_subset_uIcc).aestronglyMeasurable
          measurableSet_uIoc
    · filter_upwards [self_mem_nhdsWithin] with s hs
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      exact hFbd s hs x ⟨hx.1.le, hx.2⟩
    · refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      have hparam_cont :
          ContinuousWithinAt (fun s => F s x) I s₀ := by
        have hmaps : Set.MapsTo (fun s : ℝ => ((s, x) : ℝ × ℝ)) I K := by
          intro s hs
          rw [hKdef]
          exact Set.mem_prod.mpr ⟨hs, hxIcc⟩
        have hpair_cont : ContinuousOn (fun s : ℝ => ((s, x) : ℝ × ℝ)) I :=
          continuousOn_id.prodMk continuousOn_const
        have hcomp : ContinuousOn
            ((Function.uncurry F) ∘ fun s : ℝ => ((s, x) : ℝ × ℝ)) I :=
          hFcont.comp hpair_cont hmaps
        simpa [Function.comp_def, Function.uncurry] using
          hcomp.continuousWithinAt hs₀
      exact hparam_cont
  simpa [intervalDomainPowerEnergyDerivIntegral, F, hIdef] using hint_cont

/-- At strict interior times, the derivative of the abstract Moser energy is
the explicit interval-domain power-derivative integral. -/
theorem intervalDomain_integratedMoserEnergy_deriv_eq_powerDerivIntegral
    {params : CM2Params} {T q s : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hs0 : 0 < s) (hsT : s < T) :
    deriv (fun τ => integratedMoserEnergy intervalDomain u q τ) s =
      intervalDomainPowerEnergyDerivIntegral q u s := by
  have hpow :=
    intervalDomainPowerEnergy_hasDerivAt
      (q := q) hsol ⟨hs0, hsT⟩
  have hYeq := intervalDomain_integratedMoserEnergy_eq_powerEnergy q u
  change
    deriv (fun τ => integratedMoserEnergy intervalDomain u q τ) s =
      intervalDomainPowerEnergyDerivIntegral q u s
  rw [hYeq]
  simpa [intervalDomainPowerEnergyDerivIntegral] using hpow.deriv

/-- Concrete interval-domain producer for the abstract Moser-energy window FTC.

This reduces the FTC package to endpoint energy continuity plus integrability
of the time derivative of the Moser energy.  The derivative integrability is a
real analytic input; continuity alone would not prove this package. -/
theorem
    intervalDomain_integratedMoserEnergyWindowFTC_of_classical_endpoint_derivIntegrable
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hend : IntervalDomainPowerEnergyEndpointContinuity u T p0)
    (hderivInt :
      IntegratedMoserEnergyDerivativeWindowIntegrability
        intervalDomain u T p0) :
    IntegratedMoserEnergyWindowFTC intervalDomain u T p0 := by
  refine ⟨hderivInt, ?_⟩
  intro p hp t1 ht1 t2 ht2
  let Y : ℝ → ℝ := fun τ => integratedMoserEnergy intervalDomain u p τ
  have hab : t1 ≤ t2 := ht2.1
  have hY_cont : ContinuousOn Y (Set.Icc t1 t2) := by
    have hclosed :
        ContinuousOn
          (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
          (Set.Icc (0 : ℝ) T) :=
      intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity
        hsol hend p hp
    have hsub : Set.Icc t1 t2 ⊆ Set.Icc (0 : ℝ) T := by
      intro s hs
      exact ⟨le_trans ht1.1 hs.1, le_trans hs.2 ht2.2⟩
    simpa [Y, integratedMoserEnergy] using hclosed.mono hsub
  have hY_deriv :
      ∀ s ∈ Set.Ioo t1 t2,
        HasDerivAt Y (deriv Y s) s := by
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt ht1.1 hs.1
    have hsT : s < T := lt_of_lt_of_le hs.2 ht2.2
    have hpow :=
      intervalDomainPowerEnergy_hasDerivAt
        (q := p) hsol ⟨hs0, hsT⟩
    have hYeq := intervalDomain_integratedMoserEnergy_eq_powerEnergy p u
    change
      HasDerivAt
        (fun τ => integratedMoserEnergy intervalDomain u p τ)
        (deriv (fun τ => integratedMoserEnergy intervalDomain u p τ) s) s
    rw [hYeq]
    simpa [hpow.deriv] using hpow
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (a := t1) (b := t2) (f := Y)
      (f' := fun s : ℝ => deriv Y s)
      hab hY_cont hY_deriv (hderivInt p hp t1 ht1 t2 ht2)
  simpa [Y] using hFTC

/-- Local data sufficient to produce the abstract Moser-energy window FTC on the
interval domain.

This is a genuine split of `IntegratedMoserEnergyWindowFTC`: endpoint power
energy continuity and derivative-window integrability can be produced or
refined independently. -/
structure IntervalDomainIntegratedMoserEnergyWindowFTCLocalData
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  endpointEnergy : IntervalDomainPowerEnergyEndpointContinuity u T p0
  derivativeWindowIntegrability :
    IntegratedMoserEnergyDerivativeWindowIntegrability intervalDomain u T p0

/-- Produce the abstract Moser-energy window FTC from packaged local data. -/
theorem intervalDomain_integratedMoserEnergyWindowFTC_of_localData
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdata : IntervalDomainIntegratedMoserEnergyWindowFTCLocalData u T p0) :
    IntegratedMoserEnergyWindowFTC intervalDomain u T p0 :=
  intervalDomain_integratedMoserEnergyWindowFTC_of_classical_endpoint_derivIntegrable
    hsol hdata.endpointEnergy hdata.derivativeWindowIntegrability

/-- Strict-window derivative integrability for the Moser energy, reduced to
continuity of the explicit power-derivative integral profile.

This is deliberately strict: `0 < a` and `b < T` ensure every point of the
integration interval is an interior time. -/
theorem
    intervalDomain_deriv_intervalIntegrable_strictWindow_of_powerDerivIntegral_continuousOn
    {params : CM2Params} {T q a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < T)
    (hF_cont :
      ContinuousOn
        (fun s => intervalDomainPowerEnergyDerivIntegral q u s)
        (Set.Icc a b)) :
    IntervalIntegrable
      (fun s => deriv (fun τ => integratedMoserEnergy intervalDomain u q τ) s)
      volume a b := by
  have hF_int :
      IntervalIntegrable
        (fun s => intervalDomainPowerEnergyDerivIntegral q u s)
        volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  refine hF_int.congr ?_
  intro s hs
  rw [Set.uIoc_of_le hab] at hs
  have hs0 : 0 < s := lt_trans ha hs.1
  have hsT : s < T := lt_of_le_of_lt hs.2 hb
  exact (intervalDomain_integratedMoserEnergy_deriv_eq_powerDerivIntegral
    (params := params) (T := T) (q := q) (u := u) (v := v)
    hsol hs0 hsT).symm

/-- Strict-window derivative integrability for interval-domain Moser energies. -/
theorem intervalDomain_deriv_intervalIntegrable_of_strictWindow
    {params : CM2Params} {T q a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    IntervalIntegrable
      (fun s => deriv (fun τ => integratedMoserEnergy intervalDomain u q τ) s)
      volume a b :=
  intervalDomain_deriv_intervalIntegrable_strictWindow_of_powerDerivIntegral_continuousOn
    (params := params) (T := T) (q := q) (a := a) (b := b)
    (u := u) (v := v) hsol ha hab hb
    (intervalDomainPowerEnergyDerivIntegral_continuousOn_strictWindow
      (params := params) (T := T) (q := q) (a := a) (b := b)
      (u := u) (v := v) hsol ha hab hb)

/-- Strict-interior version of
`IntegratedMoserEnergyDerivativeWindowIntegrability`.  It intentionally does
not include windows touching `0` or `T`. -/
def IntegratedMoserEnergyDerivativeStrictWindowIntegrability
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q → ∀ a b, 0 < a → a ≤ b → b < T →
    IntervalIntegrable
      (fun s => deriv (fun τ => integratedMoserEnergy D u q τ) s)
      volume a b

/-- A classical interval-domain solution supplies strict-window derivative
integrability of every Moser energy. -/
theorem
    intervalDomain_integratedMoserEnergyDerivativeStrictWindowIntegrability_of_classical
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    IntegratedMoserEnergyDerivativeStrictWindowIntegrability
      intervalDomain u T p0 := by
  intro q _hq a b ha hab hb
  exact intervalDomain_deriv_intervalIntegrable_of_strictWindow
    (params := params) (T := T) (q := q) (a := a) (b := b)
    (u := u) (v := v) hsol ha hab hb

/-- Initial-window derivative-integrability residual for Moser energies.

This is exactly the part not supplied by strict-window integrability: windows
whose left endpoint is `0`. -/
def IntegratedMoserEnergyDerivativeInitialWindowIntegrability
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ b ∈ Set.Icc (0 : ℝ) T,
      IntervalIntegrable
        (fun s => deriv (fun τ => integratedMoserEnergy D u q τ) s)
        volume 0 b

/-- PDE-shaped initial-window residual: integrability near `t = 0` of the
explicit time-Leibniz RHS for the interval-domain power energy. -/
def IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ b ∈ Set.Icc (0 : ℝ) T,
      IntervalIntegrable
        (fun s => intervalDomainPowerEnergyDerivIntegral q u s)
        volume 0 b

/-- PDE-shaped initial-window residual for the weighted time term in the
interval-domain Lp chain rule. -/
def IntervalDomainLpWeightedTimeTermInitialWindowIntegrability
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ b ∈ Set.Icc (0 : ℝ) T,
      IntervalIntegrable
        (fun s =>
          q * intervalDomain.integral
            (intervalDomainLpEnergyWeightedTimeTerm q u s))
        volume 0 b

/-- Initial-window integrability residual for the three PDE terms in the
weighted Lp time identity. -/
def IntervalDomainLpPDETermInitialWindowIntegrability
    (params : CM2Params) (u v : ℝ → intervalDomain.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ b ∈ Set.Icc (0 : ℝ) T,
      IntervalIntegrable
        (fun s => q * intervalDomainLpDiffusionIntegral q u s)
        volume 0 b ∧
      IntervalIntegrable
        (fun s =>
          q * (params.χ₀ *
            intervalDomainLpChemotaxisIntegral params q u v s))
        volume 0 b ∧
      IntervalIntegrable
        (fun s => q * intervalDomainLpLogisticIntegral params q u s)
        volume 0 b

/-- Thinner initial-window residual for the PDE side of the weighted Lp time
identity: only the combined diffusion/chemotaxis/logistic scalar profile must be
integrable near `t = 0`. -/
def IntervalDomainLpPDECombinedInitialWindowIntegrability
    (params : CM2Params) (u v : ℝ → intervalDomain.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ b ∈ Set.Icc (0 : ℝ) T,
      IntervalIntegrable
        (fun s =>
          q * intervalDomainLpDiffusionIntegral q u s -
            q * (params.χ₀ *
              intervalDomainLpChemotaxisIntegral params q u v s) +
            q * intervalDomainLpLogisticIntegral params q u s)
        volume 0 b

/-- Positive-left-start time integrability of the three scalar PDE terms in the
weighted Lp time identity.  It intentionally excludes windows starting at `0`. -/
def IntervalDomainLpPDETermPositiveStartWindowIntegrability
    (params : CM2Params) (u v : ℝ → intervalDomain.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ a b, 0 < a → a ≤ b → b ≤ T →
      IntervalIntegrable
        (fun s => q * intervalDomainLpDiffusionIntegral q u s)
        volume a b ∧
      IntervalIntegrable
        (fun s =>
          q * (params.χ₀ *
            intervalDomainLpChemotaxisIntegral params q u v s))
        volume a b ∧
      IntervalIntegrable
        (fun s => q * intervalDomainLpLogisticIntegral params q u s)
        volume a b

/-- Continuity package for the three scalar PDE term profiles on positive-start
closed time windows. -/
def IntervalDomainLpPDETermPositiveStartWindowContinuity
    (params : CM2Params) (u v : ℝ → intervalDomain.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ a b, 0 < a → a ≤ b → b ≤ T →
      ContinuousOn
        (fun s => q * intervalDomainLpDiffusionIntegral q u s)
        (Set.Icc a b) ∧
      ContinuousOn
        (fun s =>
          q * (params.χ₀ *
            intervalDomainLpChemotaxisIntegral params q u v s))
        (Set.Icc a b) ∧
      ContinuousOn
        (fun s => q * intervalDomainLpLogisticIntegral params q u s)
        (Set.Icc a b)

/-- Continuity package for the two harder scalar PDE term profiles on
positive-start closed time windows.  The logistic component is produced below
from global classical regularity. -/
def IntervalDomainLpDiffusionChemotaxisPositiveStartWindowContinuity
    (params : CM2Params) (u v : ℝ → intervalDomain.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ a b, 0 < a → a ≤ b → b ≤ T →
      ContinuousOn
        (fun s => q * intervalDomainLpDiffusionIntegral q u s)
        (Set.Icc a b) ∧
      ContinuousOn
        (fun s =>
          q * (params.χ₀ *
            intervalDomainLpChemotaxisIntegral params q u v s))
        (Set.Icc a b)

/-- Joint continuity of the two non-logistic lifted Lp PDE integrands on
positive-start closed time windows.  This is the precise space-time regularity
input behind scalar continuity of the diffusion and chemotaxis profiles. -/
def IntervalDomainLpDiffusionChemotaxisPositiveStartIntegrandJointContinuity
    (params : CM2Params) (u v : ℝ → intervalDomain.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ a b, 0 < a → a ≤ b → b ≤ T →
      ContinuousOn
        (Function.uncurry
          (fun s y =>
            intervalDomainLift
              (fun x =>
                intervalDomainLpDiffusionTest q u s x *
                  intervalDomain.laplacian (u s) x)
              y))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) ∧
      ContinuousOn
        (Function.uncurry
          (fun s y =>
            intervalDomainLift
              (fun x =>
                intervalDomainLpDiffusionTest q u s x *
                  intervalDomain.chemotaxisDiv params (u s) (v s) x)
              y))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)

/-- Dominated-continuity bridge for interval integrals over the fixed unit
interval. -/
theorem intervalIntegral_continuousOn_of_jointContinuousOn_unitInterval
    {F : ℝ → ℝ → ℝ} {a b : ℝ}
    (hFcont :
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun s => ∫ y in (0 : ℝ)..1, F s y) (Set.Icc a b) := by
  classical
  set I : Set ℝ := Set.Icc a b with hIdef
  have hFcontI :
      ContinuousOn (Function.uncurry F) (I ×ˢ Set.Icc (0 : ℝ) 1) := by
    simpa [I, hIdef] using hFcont
  have hKcompact : IsCompact (I ×ˢ Set.Icc (0 : ℝ) 1) := by
    rw [hIdef]
    exact isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hKcompact.bddAbove_image hFcontI.norm
  set B' : ℝ := max B 0 with hB'def
  have hFbd : ∀ s ∈ I, ∀ y ∈ Set.Icc (0 : ℝ) 1, ‖F s y‖ ≤ B' := by
    intro s hs y hy
    have hBy : ‖Function.uncurry F (s, y)‖ ≤ B :=
      hB (Set.mem_image_of_mem _ (Set.mem_prod.mpr ⟨hs, hy⟩))
    exact le_trans hBy (le_max_left _ _)
  have hslice_cont : ∀ s ∈ I, ContinuousOn (F s) (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    have hmaps : Set.MapsTo (fun y : ℝ => ((s, y) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) (I ×ˢ Set.Icc (0 : ℝ) 1) := by
      intro y hy
      exact Set.mem_prod.mpr ⟨hs, hy⟩
    have hpair_cont : ContinuousOn (fun y : ℝ => ((s, y) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const.prodMk continuousOn_id
    have hcomp : ContinuousOn
        ((Function.uncurry F) ∘ fun y : ℝ => ((s, y) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) :=
      hFcontI.comp hpair_cont hmaps
    simpa [Function.comp_def, Function.uncurry] using hcomp
  have hcontI :
      ContinuousOn (fun s => ∫ y in (0 : ℝ)..1, F s y) I := by
    intro s₀ hs₀
    refine intervalIntegral.continuousWithinAt_of_dominated_interval
      (bound := fun _y : ℝ => B') ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs_cont_uIcc : ContinuousOn (F s) (Set.uIcc (0 : ℝ) 1) := by
        rw [Set.uIcc_of_le zero_le_one]
        exact hslice_cont s hs
      exact
        (hs_cont_uIcc.mono Set.uIoc_subset_uIcc).aestronglyMeasurable
          measurableSet_uIoc
    · filter_upwards [self_mem_nhdsWithin] with s hs
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      rw [Set.uIoc_of_le zero_le_one] at hy
      exact hFbd s hs y ⟨hy.1.le, hy.2⟩
    · refine Filter.Eventually.of_forall (fun y hy => ?_)
      rw [Set.uIoc_of_le zero_le_one] at hy
      have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
      have hparam_cont : ContinuousWithinAt (fun s => F s y) I s₀ := by
        have hmaps : Set.MapsTo (fun s : ℝ => ((s, y) : ℝ × ℝ))
            I (I ×ˢ Set.Icc (0 : ℝ) 1) := by
          intro s hs
          exact Set.mem_prod.mpr ⟨hs, hyIcc⟩
        have hpair_cont : ContinuousOn (fun s : ℝ => ((s, y) : ℝ × ℝ)) I :=
          continuousOn_id.prodMk continuousOn_const
        have hcomp : ContinuousOn
            ((Function.uncurry F) ∘ fun s : ℝ => ((s, y) : ℝ × ℝ)) I :=
          hFcontI.comp hpair_cont hmaps
        simpa [Function.comp_def, Function.uncurry] using
          hcomp.continuousWithinAt hs₀
      exact hparam_cont
  simpa [I, hIdef] using hcontI

/-- Joint continuity of the lifted diffusion integrand gives continuity of the
diffusion scalar profile on a positive-start window. -/
theorem intervalDomain_lpDiffusionIntegral_continuousOn_positiveStart_of_integrandJoint
    {q a b : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hjoint :
      ContinuousOn
        (Function.uncurry
          (fun s y =>
            intervalDomainLift
              (fun x =>
                intervalDomainLpDiffusionTest q u s x *
                  intervalDomain.laplacian (u s) x)
              y))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn
      (fun s => q * intervalDomainLpDiffusionIntegral q u s)
      (Set.Icc a b) := by
  set F : ℝ → ℝ → ℝ :=
    fun s y =>
      intervalDomainLift
        (fun x =>
          intervalDomainLpDiffusionTest q u s x *
            intervalDomain.laplacian (u s) x)
        y with hFdef
  have hFcont :
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
    simpa [F, hFdef] using hjoint
  have hint_cont :
      ContinuousOn (fun s => ∫ y in (0 : ℝ)..1, F s y) (Set.Icc a b) :=
    intervalIntegral_continuousOn_of_jointContinuousOn_unitInterval hFcont
  have hprofile :
      ContinuousOn (fun s => intervalDomainLpDiffusionIntegral q u s)
        (Set.Icc a b) := by
    refine hint_cont.congr (fun s _hs => ?_)
    unfold intervalDomainLpDiffusionIntegral
    change intervalDomainIntegral
        (fun x =>
          intervalDomainLpDiffusionTest q u s x *
            intervalDomain.laplacian (u s) x) =
      ∫ y in (0 : ℝ)..1, F s y
    unfold intervalDomainIntegral
    rfl
  exact continuousOn_const.mul hprofile

/-- Joint continuity of the lifted chemotaxis integrand gives continuity of the
chemotaxis scalar profile on a positive-start window. -/
theorem
    intervalDomain_lpChemotaxisIntegral_continuousOn_positiveStart_of_integrandJoint
    {params : CM2Params} {q a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hjoint :
      ContinuousOn
        (Function.uncurry
          (fun s y =>
            intervalDomainLift
              (fun x =>
                intervalDomainLpDiffusionTest q u s x *
                  intervalDomain.chemotaxisDiv params (u s) (v s) x)
              y))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn
      (fun s =>
        q * (params.χ₀ * intervalDomainLpChemotaxisIntegral params q u v s))
      (Set.Icc a b) := by
  set F : ℝ → ℝ → ℝ :=
    fun s y =>
      intervalDomainLift
        (fun x =>
          intervalDomainLpDiffusionTest q u s x *
            intervalDomain.chemotaxisDiv params (u s) (v s) x)
        y with hFdef
  have hFcont :
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
    simpa [F, hFdef] using hjoint
  have hint_cont :
      ContinuousOn (fun s => ∫ y in (0 : ℝ)..1, F s y) (Set.Icc a b) :=
    intervalIntegral_continuousOn_of_jointContinuousOn_unitInterval hFcont
  have hprofile :
      ContinuousOn (fun s => intervalDomainLpChemotaxisIntegral params q u v s)
        (Set.Icc a b) := by
    refine hint_cont.congr (fun s _hs => ?_)
    unfold intervalDomainLpChemotaxisIntegral
    change intervalDomainIntegral
        (fun x =>
          intervalDomainLpDiffusionTest q u s x *
            intervalDomain.chemotaxisDiv params (u s) (v s) x) =
      ∫ y in (0 : ℝ)..1, F s y
    unfold intervalDomainIntegral
    rfl
  exact continuousOn_const.mul (continuousOn_const.mul hprofile)

/-- Lifted integrand joint continuity produces the scalar diffusion/chemotaxis
positive-start continuity package. -/
theorem
    intervalDomain_lpDiffusionChemotaxisPositiveStartWindowContinuity_of_integrandJoint
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hjoint :
      IntervalDomainLpDiffusionChemotaxisPositiveStartIntegrandJointContinuity
        params u v T p0) :
    IntervalDomainLpDiffusionChemotaxisPositiveStartWindowContinuity
      params u v T p0 := by
  intro q hq a b ha hab hbT
  rcases hjoint q hq a b ha hab hbT with ⟨hD, hC⟩
  exact
    ⟨intervalDomain_lpDiffusionIntegral_continuousOn_positiveStart_of_integrandJoint
        (q := q) (a := a) (b := b) (u := u) hD,
      intervalDomain_lpChemotaxisIntegral_continuousOn_positiveStart_of_integrandJoint
        (params := params) (q := q) (a := a) (b := b)
        (u := u) (v := v) hC⟩

/-- Positive-start continuity of the logistic scalar term in the Lp PDE energy
identity. -/
theorem intervalDomain_lpLogisticIntegral_continuousOn_positiveStart_of_global_classical
    {params : CM2Params} {T q a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T) :
    ContinuousOn
      (fun s => q * intervalDomainLpLogisticIntegral params q u s)
      (Set.Icc a b) := by
  classical
  set I : Set ℝ := Set.Icc a b with hIdef
  have hTplus : 0 < T + 1 := by
    linarith
  have hsol : IsPaper2ClassicalSolution intervalDomain params (T + 1) u v :=
    hglobal.classical hTplus
  have htime_sub : I ⊆ Set.Ioo (0 : ℝ) (T + 1) := by
    intro s hs
    rw [hIdef] at hs
    exact
      ⟨lt_of_lt_of_le ha hs.1,
        lt_of_le_of_lt (le_trans hs.2 hbT) (by linarith)⟩
  set F : ℝ → ℝ → ℝ := fun s y =>
    (intervalDomainLift (u s) y) ^ (q - 2) *
      intervalDomainLift (u s) y *
        (intervalDomainLift (u s) y *
          (params.a - params.b * (intervalDomainLift (u s) y) ^ params.α))
    with hFdef
  have hU :
      ContinuousOn
        (fun z : ℝ × ℝ => intervalDomainLift (u z.1) z.2)
        (I ×ˢ Set.Icc (0 : ℝ) 1) := by
    have hUopen := intervalDomain_solution_jointContinuousOn hsol
    simpa [Function.uncurry] using
      hUopen.mono (Set.prod_mono htime_sub Subset.rfl)
  have hpow_qm2 :
      ContinuousOn
        (fun z : ℝ × ℝ => (intervalDomainLift (u z.1) z.2) ^ (q - 2))
        (I ×ˢ Set.Icc (0 : ℝ) 1) := by
    have hpow_open :=
      intervalDomain_power_jointContinuousOn
        (T := T + 1) (p := q - 2) (u := u) (v := v) hsol
    simpa [Function.uncurry] using
      hpow_open.mono (Set.prod_mono htime_sub Subset.rfl)
  have hpow_alpha :
      ContinuousOn
        (fun z : ℝ × ℝ => (intervalDomainLift (u z.1) z.2) ^ params.α)
        (I ×ˢ Set.Icc (0 : ℝ) 1) := by
    have hpow_open :=
      intervalDomain_power_jointContinuousOn
        (T := T + 1) (p := params.α) (u := u) (v := v) hsol
    simpa [Function.uncurry] using
      hpow_open.mono (Set.prod_mono htime_sub Subset.rfl)
  have htest :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (intervalDomainLift (u z.1) z.2) ^ (q - 2) *
            intervalDomainLift (u z.1) z.2)
        (I ×ˢ Set.Icc (0 : ℝ) 1) :=
    hpow_qm2.mul hU
  have hreact :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          intervalDomainLift (u z.1) z.2 *
            (params.a - params.b *
              (intervalDomainLift (u z.1) z.2) ^ params.α))
        (I ×ˢ Set.Icc (0 : ℝ) 1) :=
    hU.mul (continuousOn_const.sub (continuousOn_const.mul hpow_alpha))
  have hFcont :
      ContinuousOn (Function.uncurry F) (I ×ˢ Set.Icc (0 : ℝ) 1) := by
    simpa [F, Function.uncurry] using htest.mul hreact
  have hKcompact : IsCompact (I ×ˢ Set.Icc (0 : ℝ) 1) := by
    rw [hIdef]
    exact isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hKcompact.bddAbove_image hFcont.norm
  set B' : ℝ := max B 0 with hB'def
  have hFbd : ∀ s ∈ I, ∀ y ∈ Set.Icc (0 : ℝ) 1, ‖F s y‖ ≤ B' := by
    intro s hs y hy
    have hBy : ‖Function.uncurry F (s, y)‖ ≤ B :=
      hB (Set.mem_image_of_mem _ (Set.mem_prod.mpr ⟨hs, hy⟩))
    exact le_trans hBy (le_max_left _ _)
  have hslice_cont : ∀ s ∈ I, ContinuousOn (F s) (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    have hmaps : Set.MapsTo (fun y : ℝ => ((s, y) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) (I ×ˢ Set.Icc (0 : ℝ) 1) := by
      intro y hy
      exact Set.mem_prod.mpr ⟨hs, hy⟩
    have hpair_cont : ContinuousOn (fun y : ℝ => ((s, y) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const.prodMk continuousOn_id
    have hcomp : ContinuousOn
        ((Function.uncurry F) ∘ fun y : ℝ => ((s, y) : ℝ × ℝ))
        (Set.Icc (0 : ℝ) 1) :=
      hFcont.comp hpair_cont hmaps
    simpa [Function.comp_def, Function.uncurry] using hcomp
  have hlog_eq :
      ∀ s ∈ I,
        intervalDomainLpLogisticIntegral params q u s =
          ∫ y in (0 : ℝ)..1, F s y := by
    intro s hs
    have hsIoo : s ∈ Set.Ioo (0 : ℝ) (T + 1) := htime_sub hs
    unfold intervalDomainLpLogisticIntegral
    change intervalDomainIntegral
        (fun x =>
          intervalDomainLpDiffusionTest q u s x *
            (u s x * (params.a - params.b * (u s x) ^ params.α))) =
      ∫ y in (0 : ℝ)..1, F s y
    unfold intervalDomainIntegral
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hy
    have hpos : 0 < u s (⟨y, hy⟩ : intervalDomain.Point) :=
      hsol.u_pos' (x := (⟨y, hy⟩ : intervalDomain.Point)) hsIoo.1 hsIoo.2
    simp [F, intervalDomainLift, intervalDomainLpDiffusionTest, Set.mem_Icc,
      hy.1, hy.2,
      abs_of_pos hpos]
  have hint_cont :
      ContinuousOn (fun s => ∫ y in (0 : ℝ)..1, F s y) I := by
    intro s₀ hs₀
    refine intervalIntegral.continuousWithinAt_of_dominated_interval
      (bound := fun _y : ℝ => B') ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs_cont_uIcc : ContinuousOn (F s) (Set.uIcc (0 : ℝ) 1) := by
        rw [Set.uIcc_of_le zero_le_one]
        exact hslice_cont s hs
      exact
        (hs_cont_uIcc.mono Set.uIoc_subset_uIcc).aestronglyMeasurable
          measurableSet_uIoc
    · filter_upwards [self_mem_nhdsWithin] with s hs
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      rw [Set.uIoc_of_le zero_le_one] at hy
      exact hFbd s hs y ⟨hy.1.le, hy.2⟩
    · refine Filter.Eventually.of_forall (fun y hy => ?_)
      rw [Set.uIoc_of_le zero_le_one] at hy
      have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
      have hparam_cont : ContinuousWithinAt (fun s => F s y) I s₀ :=
        (hFcont.comp
          (continuousOn_id.prodMk continuousOn_const)
          (fun s hs => Set.mem_prod.mpr ⟨hs, hyIcc⟩)).continuousWithinAt hs₀
      simpa [F, Function.uncurry] using hparam_cont
  have hlog_cont :
      ContinuousOn (fun s => intervalDomainLpLogisticIntegral params q u s) I := by
    exact hint_cont.congr (fun s hs => hlog_eq s hs)
  have hscaled :
      ContinuousOn
        (fun s => q * intervalDomainLpLogisticIntegral params q u s) I :=
    continuousOn_const.mul hlog_cont
  simpa [I, hIdef] using hscaled

/-- The full positive-start continuity package reduces to the diffusion and
chemotaxis scalar profiles; the logistic profile is produced from global
classical regularity. -/
theorem
    intervalDomain_lpPDETermPositiveStartWindowContinuity_of_diffusionChemotaxis_global_logistic
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hdc :
      IntervalDomainLpDiffusionChemotaxisPositiveStartWindowContinuity
        params u v T p0) :
    IntervalDomainLpPDETermPositiveStartWindowContinuity params u v T p0 := by
  intro q hq a b ha hab hbT
  rcases hdc q hq a b ha hab hbT with ⟨hD, hC⟩
  exact
    ⟨hD, hC,
      intervalDomain_lpLogisticIntegral_continuousOn_positiveStart_of_global_classical
        (params := params) (T := T) (q := q) (a := a) (b := b)
        (u := u) (v := v) hglobal ha hab hbT⟩

/-- Full positive-start PDE scalar continuity from lifted diffusion/chemotaxis
integrand joint continuity plus the global-classical logistic producer. -/
theorem
    intervalDomain_lpPDETermPositiveStartWindowContinuity_of_integrandJoint_global_logistic
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hjoint :
      IntervalDomainLpDiffusionChemotaxisPositiveStartIntegrandJointContinuity
        params u v T p0) :
    IntervalDomainLpPDETermPositiveStartWindowContinuity params u v T p0 :=
  intervalDomain_lpPDETermPositiveStartWindowContinuity_of_diffusionChemotaxis_global_logistic
    (params := params) (T := T) (p0 := p0) (u := u) (v := v) hglobal
    (intervalDomain_lpDiffusionChemotaxisPositiveStartWindowContinuity_of_integrandJoint
      (params := params) (T := T) (p0 := p0) (u := u) (v := v) hjoint)

/-- Positive-start continuity of the scalar PDE profiles gives positive-start
interval integrability. -/
theorem intervalDomain_lpPDETermPositiveStartWindowIntegrability_of_continuity
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hcont :
      IntervalDomainLpPDETermPositiveStartWindowContinuity params u v T p0) :
    IntervalDomainLpPDETermPositiveStartWindowIntegrability params u v T p0 := by
  intro q hq a b ha hab hbT
  rcases hcont q hq a b ha hab hbT with ⟨hD, hC, hL⟩
  refine ⟨?_, ?_, ?_⟩
  · apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  · apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  · apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]

/-- Closed-window integrability package for the three scalar PDE terms. -/
def IntervalDomainLpPDETermClosedWindowIntegrability
    (params : CM2Params) (u v : ℝ → intervalDomain.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
      IntervalIntegrable
        (fun s => q * intervalDomainLpDiffusionIntegral q u s)
        volume t1 t2 ∧
      IntervalIntegrable
        (fun s =>
          q * (params.χ₀ *
            intervalDomainLpChemotaxisIntegral params q u v s))
        volume t1 t2 ∧
      IntervalIntegrable
        (fun s => q * intervalDomainLpLogisticIntegral params q u s)
        volume t1 t2

/-- Split closed-window PDE-term integrability into the initial edge and
positive-left-start windows. -/
theorem
    intervalDomain_lpPDETermClosedWindowIntegrability_of_initial_and_positiveStart
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hinit :
      IntervalDomainLpPDETermInitialWindowIntegrability params u v T p0)
    (hpos :
      IntervalDomainLpPDETermPositiveStartWindowIntegrability params u v T p0) :
    IntervalDomainLpPDETermClosedWindowIntegrability params u v T p0 := by
  intro q hq t1 ht1 t2 ht2
  by_cases ht10 : t1 = 0
  · subst t1
    exact hinit q hq t2 ht2
  · have ht1_pos : 0 < t1 :=
      lt_of_le_of_ne ht1.1 (fun h : (0 : ℝ) = t1 => ht10 h.symm)
    exact hpos q hq t1 t2 ht1_pos ht2.1 ht2.2

/-- At each positive global-classical time, the weighted Lp time term equals the
sum of the PDE component integrals, after scaling by `q`. -/
theorem intervalDomain_weightedTimeTerm_eq_pdeTerms_scaled_of_global_pos
    {params : CM2Params} {q s : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hs0 : 0 < s) :
    q * intervalDomain.integral
        (intervalDomainLpEnergyWeightedTimeTerm q u s) =
      q * intervalDomainLpDiffusionIntegral q u s -
        q * (params.χ₀ *
          intervalDomainLpChemotaxisIntegral params q u v s) +
        q * intervalDomainLpLogisticIntegral params q u s := by
  have hTpos : 0 < s + 1 := by
    linarith
  have hsol :
      IsPaper2ClassicalSolution intervalDomain params (s + 1) u v :=
    hglobal.classical hTpos
  have hpde :=
    intervalDomain_lp_energy_hPDEIntegral_of_regularity
      (params := params) (T := s + 1) (t := s) (pExp := q)
      (u := u) (v := v) hsol hs0 (by linarith)
  rw [hpde]
  ring

/-- Alias for the positive-time weighted-term identity emphasizing that the
right hand side is the already-combined PDE scalar profile. -/
theorem intervalDomain_weightedTimeTerm_eq_pdeCombined_scaled_of_global_pos
    {params : CM2Params} {q s : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hs0 : 0 < s) :
    q * intervalDomain.integral
        (intervalDomainLpEnergyWeightedTimeTerm q u s) =
      q * intervalDomainLpDiffusionIntegral q u s -
        q * (params.χ₀ *
          intervalDomainLpChemotaxisIntegral params q u v s) +
        q * intervalDomainLpLogisticIntegral params q u s :=
  intervalDomain_weightedTimeTerm_eq_pdeTerms_scaled_of_global_pos
    (params := params) (q := q) (s := s) (u := u) (v := v)
    hglobal hs0

/-- The componentwise initial-window residual implies the thinner combined
PDE-side residual. -/
theorem intervalDomain_lpPDECombinedInitialWindowIntegrability_of_terms
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hterms :
      IntervalDomainLpPDETermInitialWindowIntegrability params u v T p0) :
    IntervalDomainLpPDECombinedInitialWindowIntegrability params u v T p0 := by
  intro q hq b hb
  rcases hterms q hq b hb with ⟨hDiff, hChem, hLog⟩
  exact IntervalIntegrable.add (IntervalIntegrable.sub hDiff hChem) hLog

/-- Combined initial-window integrability of the PDE side gives initial-window
integrability of the weighted Lp time term. -/
theorem
    intervalDomain_weightedTimeTermInitialWindowIntegrability_of_pdeCombined_initial
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hcombined :
      IntervalDomainLpPDECombinedInitialWindowIntegrability params u v T p0) :
    IntervalDomainLpWeightedTimeTermInitialWindowIntegrability u T p0 := by
  intro q hq b hb
  have hRHS :
      IntervalIntegrable
        (fun s =>
          q * intervalDomainLpDiffusionIntegral q u s -
            q * (params.χ₀ *
              intervalDomainLpChemotaxisIntegral params q u v s) +
            q * intervalDomainLpLogisticIntegral params q u s)
        volume 0 b :=
    hcombined q hq b hb
  refine hRHS.congr ?_
  intro s hs
  rw [Set.uIoc_of_le hb.1] at hs
  exact
    (intervalDomain_weightedTimeTerm_eq_pdeTerms_scaled_of_global_pos
      (params := params) (q := q) (s := s) (u := u) (v := v)
      hglobal hs.1).symm

/-- Initial-window integrability of the weighted Lp time term gives the thinner
combined PDE-side residual.  This is the reverse bridge to
`intervalDomain_weightedTimeTermInitialWindowIntegrability_of_pdeCombined_initial`;
the endpoint value at `0` is irrelevant because interval integrability over
`0..b` is checked on `Ioc 0 b`. -/
theorem
    intervalDomain_lpPDECombinedInitialWindowIntegrability_of_weightedTimeTerm_initial
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hweighted :
      IntervalDomainLpWeightedTimeTermInitialWindowIntegrability u T p0) :
    IntervalDomainLpPDECombinedInitialWindowIntegrability params u v T p0 := by
  intro q hq b hb
  have hW :
      IntervalIntegrable
        (fun s =>
          q * intervalDomain.integral
            (intervalDomainLpEnergyWeightedTimeTerm q u s))
        volume 0 b :=
    hweighted q hq b hb
  refine hW.congr ?_
  intro s hs
  rw [Set.uIoc_of_le hb.1] at hs
  exact
    intervalDomain_weightedTimeTerm_eq_pdeCombined_scaled_of_global_pos
      (params := params) (q := q) (s := s) (u := u) (v := v)
      hglobal hs.1

/-- Component initial-window integrability of the PDE terms gives
initial-window integrability of the weighted Lp time term. -/
theorem intervalDomain_weightedTimeTermInitialWindowIntegrability_of_pdeTerm_initial
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hterms :
      IntervalDomainLpPDETermInitialWindowIntegrability params u v T p0) :
    IntervalDomainLpWeightedTimeTermInitialWindowIntegrability u T p0 :=
  intervalDomain_weightedTimeTermInitialWindowIntegrability_of_pdeCombined_initial
    (params := params) (T := T) (p0 := p0) (u := u) (v := v) hglobal
    (intervalDomain_lpPDECombinedInitialWindowIntegrability_of_terms
      (params := params) (T := T) (p0 := p0) (u := u) (v := v) hterms)

/-- Under positivity of the time slice, the explicit power-energy derivative
profile is the weighted Lp time term. -/
theorem intervalDomainPowerEnergyDerivIntegral_eq_scaled_weighted_of_pos
    (q s : ℝ) (u : ℝ → intervalDomain.Point → ℝ)
    (hpos : ∀ x : intervalDomain.Point, 0 < u s x) :
    intervalDomainPowerEnergyDerivIntegral q u s =
      q * intervalDomain.integral
        (intervalDomainLpEnergyWeightedTimeTerm q u s) := by
  calc
    intervalDomainPowerEnergyDerivIntegral q u s =
        ∫ y in (0 : ℝ)..1, intervalDomainPowerDeriv q u s y := by
      rfl
    _ = intervalDomain.integral
          (fun x => q * (u s x) ^ (q - 1) * intervalDomain.timeDeriv u s x) :=
      intervalDomainPowerDeriv_integral_eq_timeTerm q u s
    _ = q * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm q u s) :=
      intervalDomainPowerTimeTerm_eq_scaled_weighted q s u hpos

/-- Weighted-time-term initial-window integrability implies the explicit
power-derivative initial-window residual, provided all positive-time slices are
positive. -/
theorem
    intervalDomain_powerDerivIntegralInitialWindowIntegrability_of_weightedTimeTerm_initial_of_pos
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hpos : ∀ s, 0 < s → ∀ x : intervalDomain.Point, 0 < u s x)
    (hwt : IntervalDomainLpWeightedTimeTermInitialWindowIntegrability u T p0) :
    IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability u T p0 := by
  intro q hq b hb
  have hwtInt :
      IntervalIntegrable
        (fun s =>
          q * intervalDomain.integral
            (intervalDomainLpEnergyWeightedTimeTerm q u s))
        volume 0 b :=
    hwt q hq b hb
  refine hwtInt.congr ?_
  intro s hs
  rw [Set.uIoc_of_le hb.1] at hs
  exact
    (intervalDomainPowerEnergyDerivIntegral_eq_scaled_weighted_of_pos
      q s u (hpos s hs.1)).symm

/-- Global classical solutions supply the positivity needed to convert the
weighted-time-term residual into the explicit power-derivative residual. -/
theorem
    intervalDomain_powerDerivIntegralInitialWindowIntegrability_of_weightedTimeTerm_initial
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hwt : IntervalDomainLpWeightedTimeTermInitialWindowIntegrability u T p0) :
    IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability u T p0 := by
  refine
    intervalDomain_powerDerivIntegralInitialWindowIntegrability_of_weightedTimeTerm_initial_of_pos
      (T := T) (p0 := p0) (u := u) ?_ hwt
  intro s hs x
  have hTpos : 0 < s + 1 := by
    linarith
  have hsol :
      IsPaper2ClassicalSolution intervalDomain params (s + 1) u v :=
    hglobal.classical hTpos
  exact hsol.u_pos' (x := x) hs (by linarith)

/-- At every positive time, global classical regularity identifies the
derivative of the abstract integrated Moser energy with the explicit
interval-domain power-derivative integral. -/
theorem
    intervalDomain_integratedMoserEnergy_deriv_eq_powerDerivIntegral_of_global_pos
    {params : CM2Params} {q s : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hs0 : 0 < s) :
    deriv (fun τ => integratedMoserEnergy intervalDomain u q τ) s =
      intervalDomainPowerEnergyDerivIntegral q u s := by
  have hTpos : 0 < s + 1 := by
    linarith
  have hsol :
      IsPaper2ClassicalSolution intervalDomain params (s + 1) u v :=
    hglobal.classical hTpos
  exact
    intervalDomain_integratedMoserEnergy_deriv_eq_powerDerivIntegral
      (params := params) (T := s + 1) (q := q) (s := s)
      (u := u) (v := v) hsol hs0 (by linarith)

/-- Explicit initial-window integrability of the Leibniz RHS gives
initial-window integrability of the actual Moser-energy derivative. -/
theorem
    intervalDomain_moserDerivativeInitialWindowIntegrability_of_powerDerivIntegral
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hpowInit :
      IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability u T p0) :
    IntegratedMoserEnergyDerivativeInitialWindowIntegrability
      intervalDomain u T p0 := by
  intro q hq b hb
  have hpowInt :
      IntervalIntegrable
        (fun s => intervalDomainPowerEnergyDerivIntegral q u s)
        volume 0 b :=
    hpowInit q hq b hb
  refine hpowInt.congr ?_
  intro s hs
  rw [Set.uIoc_of_le hb.1] at hs
  exact
    (intervalDomain_integratedMoserEnergy_deriv_eq_powerDerivIntegral_of_global_pos
      (params := params) (q := q) (s := s) (u := u) (v := v)
      hglobal hs.1).symm

/-- Derivative integrability for all windows in `[0,T]` whose left endpoint is
strictly positive. -/
def IntegratedMoserEnergyDerivativePositiveStartWindowIntegrability
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ a b, 0 < a → a ≤ b → b ≤ T →
      IntervalIntegrable
        (fun s => deriv (fun τ => integratedMoserEnergy D u q τ) s)
        volume a b

/-- The full derivative-integrability package is a case split between
initial windows and windows with positive left endpoint. -/
theorem
    integratedMoserEnergyDerivativeWindowIntegrability_of_initial_and_positiveStart
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T p0 : ℝ}
    (hinit : IntegratedMoserEnergyDerivativeInitialWindowIntegrability D u T p0)
    (hpos :
      IntegratedMoserEnergyDerivativePositiveStartWindowIntegrability D u T p0) :
    IntegratedMoserEnergyDerivativeWindowIntegrability D u T p0 := by
  intro q hq t1 ht1 t2 ht2
  by_cases ht10 : t1 = 0
  · subst t1
    exact hinit q hq t2 ht2
  · have ht1_pos : 0 < t1 := by
      exact lt_of_le_of_ne ht1.1 (fun h : (0 : ℝ) = t1 => ht10 h.symm)
    exact hpos q hq t1 t2 ht1_pos ht2.1 ht2.2

/-- A global classical interval-domain solution supplies every derivative
integrability window whose left endpoint is strictly positive.

The right endpoint `T` is handled by applying the strict-window theorem on the
longer horizon `T + 1`. -/
theorem
    intervalDomain_derivativePositiveStartWindowIntegrability_of_global_classical
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v) :
    IntegratedMoserEnergyDerivativePositiveStartWindowIntegrability
      intervalDomain u T p0 := by
  intro q _hq a b ha hab hbT
  have hT_pos : 0 < T := lt_of_lt_of_le ha (le_trans hab hbT)
  have hTplus_pos : 0 < T + 1 := by
    linarith
  have hsolLong :
      IsPaper2ClassicalSolution intervalDomain params (T + 1) u v :=
    hglobal.classical hTplus_pos
  have hb_lt_Tplus : b < T + 1 := by
    linarith
  exact
    intervalDomain_deriv_intervalIntegrable_of_strictWindow
      (params := params) (T := T + 1) (q := q) (a := a) (b := b)
      (u := u) (v := v) hsolLong ha hab hb_lt_Tplus

/-- Full closed-window derivative integrability from global classical regularity
plus the honest left-endpoint derivative-integrability residual. -/
theorem intervalDomain_derivativeWindowIntegrability_of_global_classical_initial
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hinit :
      IntegratedMoserEnergyDerivativeInitialWindowIntegrability
        intervalDomain u T p0) :
    IntegratedMoserEnergyDerivativeWindowIntegrability intervalDomain u T p0 :=
  integratedMoserEnergyDerivativeWindowIntegrability_of_initial_and_positiveStart
    hinit
    (intervalDomain_derivativePositiveStartWindowIntegrability_of_global_classical
      (params := params) (T := T) (p0 := p0) (u := u) (v := v) hglobal)

/-- Full closed-window derivative integrability from global classical
regularity plus explicit initial-window integrability of the time-Leibniz RHS. -/
theorem intervalDomain_derivativeWindowIntegrability_of_global_powerDerivIntegral
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hpowInit :
      IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability u T p0) :
    IntegratedMoserEnergyDerivativeWindowIntegrability intervalDomain u T p0 :=
  intervalDomain_derivativeWindowIntegrability_of_global_classical_initial
    (params := params) (T := T) (p0 := p0) (u := u) (v := v)
    hglobal
    (intervalDomain_moserDerivativeInitialWindowIntegrability_of_powerDerivIntegral
      (params := params) (T := T) (p0 := p0) (u := u) (v := v)
      hglobal hpowInit)

/-- Full closed-window derivative integrability from global classical regularity
plus initial-window integrability of the weighted Lp time term. -/
theorem intervalDomain_derivativeWindowIntegrability_of_global_weightedTimeTerm
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hwt :
      IntervalDomainLpWeightedTimeTermInitialWindowIntegrability u T p0) :
    IntegratedMoserEnergyDerivativeWindowIntegrability intervalDomain u T p0 :=
  intervalDomain_derivativeWindowIntegrability_of_global_powerDerivIntegral
    (params := params) (T := T) (p0 := p0) (u := u) (v := v)
    hglobal
    (intervalDomain_powerDerivIntegralInitialWindowIntegrability_of_weightedTimeTerm_initial
      (params := params) (T := T) (p0 := p0) (u := u) (v := v)
      hglobal hwt)

/-- Full closed-window derivative integrability from global classical regularity
plus initial-window integrability of the PDE component terms. -/
theorem intervalDomain_derivativeWindowIntegrability_of_global_pdeTerms
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hterms :
      IntervalDomainLpPDETermInitialWindowIntegrability params u v T p0) :
    IntegratedMoserEnergyDerivativeWindowIntegrability intervalDomain u T p0 :=
  intervalDomain_derivativeWindowIntegrability_of_global_weightedTimeTerm
    (params := params) (T := T) (p0 := p0) (u := u) (v := v)
    hglobal
    (intervalDomain_weightedTimeTermInitialWindowIntegrability_of_pdeTerm_initial
      (params := params) (T := T) (p0 := p0) (u := u) (v := v)
      hglobal hterms)

/-- Endpoint power-energy continuity from a left-endpoint residual and a global
classical solution.

The right endpoint `T` is an interior time for the longer horizon `T + 1`, so
its continuity follows from `intervalDomain_energyContinuousOn_Ioo`.  The left
endpoint remains an explicit residual because the current classical-solution
record is an interior-time regularity statement. -/
theorem intervalDomain_powerEnergyEndpointContinuity_of_atZero_and_global_classical
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hzero :
      ∀ p, p0 ≤ p →
        ContinuousWithinAt
          (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
          (Set.Icc (0 : ℝ) T) 0) :
    IntervalDomainPowerEnergyEndpointContinuity u T p0 := by
  refine ⟨hzero, ?_⟩
  intro p hp
  have hTplus : 0 < T + 1 := by
    linarith
  have hsolLong :
      IsPaper2ClassicalSolution intervalDomain params (T + 1) u v :=
    hglobal.classical hTplus
  have hIoo :
      ContinuousOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Ioo (0 : ℝ) (T + 1)) :=
    intervalDomain_energyContinuousOn_Ioo (p := p) hsolLong
  have hTmem : T ∈ Set.Ioo (0 : ℝ) (T + 1) := by
    exact ⟨hT, by linarith⟩
  have hcontAt :
      ContinuousAt
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p)) T :=
    hIoo.continuousAt (isOpen_Ioo.mem_nhds hTmem)
  exact hcontAt.continuousWithinAt

/-- Endpoint power-energy continuity from the named left-endpoint residual and a
global classical solution. -/
theorem intervalDomain_powerEnergyEndpointContinuity_of_initialPowerEnergyContinuity
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hzero : IntervalDomainInitialPowerEnergyContinuityAtZero u T p0) :
    IntervalDomainPowerEnergyEndpointContinuity u T p0 :=
  intervalDomain_powerEnergyEndpointContinuity_of_atZero_and_global_classical
    hglobal hT hzero

/-- Concrete interval-domain producer for the abstract Moser-energy window FTC
from global classical regularity, endpoint energy continuity, and explicit
initial-window integrability of the time-Leibniz RHS. -/
theorem intervalDomain_integratedMoserEnergyWindowFTC_of_global_endpoint_powerInit
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hend : IntervalDomainPowerEnergyEndpointContinuity u T p0)
    (hpowInit :
      IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability u T p0) :
    IntegratedMoserEnergyWindowFTC intervalDomain u T p0 :=
  intervalDomain_integratedMoserEnergyWindowFTC_of_classical_endpoint_derivIntegrable
    (params := params) (T := T) (p0 := p0) (u := u) (v := v)
    (hglobal.classical hT) hend
    (intervalDomain_derivativeWindowIntegrability_of_global_powerDerivIntegral
      (params := params) (T := T) (p0 := p0) (u := u) (v := v)
      hglobal hpowInit)

/-- Same window-FTC producer with only the left endpoint energy-continuity
residual exposed; right endpoint continuity follows from global classical
regularity on the longer horizon. -/
theorem intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_powerInit
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hzero : IntervalDomainInitialPowerEnergyContinuityAtZero u T p0)
    (hpowInit :
      IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability u T p0) :
    IntegratedMoserEnergyWindowFTC intervalDomain u T p0 :=
  intervalDomain_integratedMoserEnergyWindowFTC_of_global_endpoint_powerInit
    (params := params) (T := T) (p0 := p0) (u := u) (v := v)
    hglobal hT
    (intervalDomain_powerEnergyEndpointContinuity_of_initialPowerEnergyContinuity
      (params := params) (T := T) (p0 := p0) (u := u) (v := v)
      hglobal hT hzero)
    hpowInit

/-- Same window-FTC producer, with the left-endpoint derivative residual stated
as weighted Lp time-term integrability. -/
theorem intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_weightedTimeTerm
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hzero : IntervalDomainInitialPowerEnergyContinuityAtZero u T p0)
    (hwt : IntervalDomainLpWeightedTimeTermInitialWindowIntegrability u T p0) :
    IntegratedMoserEnergyWindowFTC intervalDomain u T p0 :=
  intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_powerInit
    (params := params) (T := T) (p0 := p0) (u := u) (v := v)
    hglobal hT hzero
    (intervalDomain_powerDerivIntegralInitialWindowIntegrability_of_weightedTimeTerm_initial
      (params := params) (T := T) (p0 := p0) (u := u) (v := v)
      hglobal hwt)

/-- Same window-FTC producer, with the left-endpoint derivative residual stated
as initial-window integrability of the combined PDE-side scalar profile. -/
theorem intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_pdeCombined
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hzero : IntervalDomainInitialPowerEnergyContinuityAtZero u T p0)
    (hcombined :
      IntervalDomainLpPDECombinedInitialWindowIntegrability params u v T p0) :
    IntegratedMoserEnergyWindowFTC intervalDomain u T p0 :=
  intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_weightedTimeTerm
    (params := params) (T := T) (p0 := p0) (u := u) (v := v)
    hglobal hT hzero
    (intervalDomain_weightedTimeTermInitialWindowIntegrability_of_pdeCombined_initial
      (params := params) (T := T) (p0 := p0) (u := u) (v := v)
      hglobal hcombined)

/-- Same window-FTC producer, with the left-endpoint derivative residual stated
as initial-window integrability of the PDE component terms. -/
theorem intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_pdeTerms
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hzero : IntervalDomainInitialPowerEnergyContinuityAtZero u T p0)
    (hterms :
      IntervalDomainLpPDETermInitialWindowIntegrability params u v T p0) :
    IntegratedMoserEnergyWindowFTC intervalDomain u T p0 :=
  intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_weightedTimeTerm
    (params := params) (T := T) (p0 := p0) (u := u) (v := v)
    hglobal hT hzero
    (intervalDomain_weightedTimeTermInitialWindowIntegrability_of_pdeTerm_initial
      (params := params) (T := T) (p0 := p0) (u := u) (v := v)
      hglobal hterms)

/-- Global-classical initial-window PDE data sufficient for the local
Moser-energy FTC data package.  The left endpoint energy continuity and the
initial-window PDE integrability remain explicit residuals. -/
structure IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData
    (params : CM2Params) (u v : ℝ → intervalDomain.Point → ℝ)
    (T p0 : ℝ) : Prop where
  atZero : IntervalDomainInitialPowerEnergyContinuityAtZero u T p0
  pdeCombinedInitial :
    IntervalDomainLpPDECombinedInitialWindowIntegrability params u v T p0

/-- Convert the global-classical initial-window PDE package into local FTC
data: the right endpoint is supplied by global classical regularity on a longer
horizon, and the derivative-window integrability is reduced to the combined
PDE initial-window residual. -/
theorem
    intervalDomain_integratedMoserEnergyWindowFTCLocalData_of_globalPDEInitialData
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hdata :
      IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData
        params u v T p0) :
    IntervalDomainIntegratedMoserEnergyWindowFTCLocalData u T p0 where
  endpointEnergy :=
    intervalDomain_powerEnergyEndpointContinuity_of_initialPowerEnergyContinuity
      (params := params) (T := T) (p0 := p0) (u := u) (v := v)
      hglobal hT hdata.atZero
  derivativeWindowIntegrability :=
    intervalDomain_derivativeWindowIntegrability_of_global_weightedTimeTerm
      (params := params) (T := T) (p0 := p0) (u := u) (v := v)
      hglobal
      (intervalDomain_weightedTimeTermInitialWindowIntegrability_of_pdeCombined_initial
        (params := params) (T := T) (p0 := p0) (u := u) (v := v)
        hglobal hdata.pdeCombinedInitial)

/-- Direct FTC producer from global-classical initial-window PDE data. -/
theorem intervalDomain_integratedMoserEnergyWindowFTC_of_globalPDEInitialData
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hdata :
      IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData
        params u v T p0) :
    IntegratedMoserEnergyWindowFTC intervalDomain u T p0 :=
  intervalDomain_integratedMoserEnergyWindowFTC_of_localData
    (params := params) (T := T) (p0 := p0) (u := u) (v := v)
    (hglobal.classical hT)
    (intervalDomain_integratedMoserEnergyWindowFTCLocalData_of_globalPDEInitialData
      (params := params) (T := T) (p0 := p0) (u := u) (v := v)
      hglobal hT hdata)

#print axioms intervalDomain_solution_jointContinuousOn
#print axioms intervalDomain_power_jointContinuousOn
#print axioms intervalDomain_power_bounded_on_slab
#print axioms intervalDomain_energyContinuousOn_Ioo
#print axioms intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity
#print axioms intervalDomain_integratedMoserEnergy_eq_powerEnergy
#print axioms intervalDomain_integratedMoserEnergy_deriv_eq_powerDerivIntegral
#print axioms intervalDomainPowerEnergyDerivIntegral_continuousOn_strictWindow
#print axioms
  intervalDomain_lpLogisticIntegral_continuousOn_positiveStart_of_global_classical
#print axioms
  intervalDomain_lpPDETermPositiveStartWindowContinuity_of_diffusionChemotaxis_global_logistic
#print axioms
  intervalDomain_lpPDETermPositiveStartWindowIntegrability_of_continuity
#print axioms
  intervalDomain_lpPDETermClosedWindowIntegrability_of_initial_and_positiveStart
#print axioms
  intervalDomain_integratedMoserEnergyWindowFTC_of_classical_endpoint_derivIntegrable
#print axioms
  intervalDomain_integratedMoserEnergyWindowFTC_of_localData
#print axioms
  intervalDomain_deriv_intervalIntegrable_strictWindow_of_powerDerivIntegral_continuousOn
#print axioms intervalDomain_deriv_intervalIntegrable_of_strictWindow
#print axioms
  intervalDomain_integratedMoserEnergyDerivativeStrictWindowIntegrability_of_classical
#print axioms
  intervalDomain_integratedMoserEnergy_deriv_eq_powerDerivIntegral_of_global_pos
#print axioms
  intervalDomain_moserDerivativeInitialWindowIntegrability_of_powerDerivIntegral
#print axioms
  integratedMoserEnergyDerivativeWindowIntegrability_of_initial_and_positiveStart
#print axioms
  intervalDomain_derivativePositiveStartWindowIntegrability_of_global_classical
#print axioms
  intervalDomain_derivativeWindowIntegrability_of_global_classical_initial
#print axioms
  intervalDomain_derivativeWindowIntegrability_of_global_powerDerivIntegral
#print axioms
  intervalDomain_derivativeWindowIntegrability_of_global_weightedTimeTerm
#print axioms
  intervalDomain_derivativeWindowIntegrability_of_global_pdeTerms
#print axioms
  intervalDomain_weightedTimeTerm_eq_pdeCombined_scaled_of_global_pos
#print axioms
  intervalDomain_lpPDECombinedInitialWindowIntegrability_of_terms
#print axioms
  intervalDomain_weightedTimeTermInitialWindowIntegrability_of_pdeCombined_initial
#print axioms
  intervalDomain_lpPDECombinedInitialWindowIntegrability_of_weightedTimeTerm_initial
#print axioms intervalDomain_lift_continuousOn_Icc_of_continuous
#print axioms intervalDomain_abs_le_supNorm_of_bddAbove
#print axioms intervalDomain_pointwise_abs_lt_of_supNorm_lt
#print axioms bddAbove_abs_sub_of_bddAbove_abs
#print axioms intervalDomain_bddAbove_abs_of_paperPositiveInitialDatum
#print axioms intervalDomain_u0_rpow_intervalIntegrable_of_paperPositive
#print axioms real_rpow_uniformContinuousOn_Icc_of_pos_left
#print axioms intervalDomain_integral_sub_abs_le_of_pointwise_abs_le
#print axioms intervalDomain_traceDiff_slice_abs_bddAbove_of_global
#print axioms intervalDomain_initialTrace_pointwise_abs_lt
#print axioms intervalDomain_initialTracePowerEnergyTendsto_of_paperPositive
#print axioms
  intervalDomain_initialPowerEnergyCompatibleAtZero_of_eq
#print axioms intervalDomainWithInitialSlice_eq_raw_of_pos
#print axioms intervalDomainWithInitialSlice_eq_raw_of_pos_apply
#print axioms
  intervalDomain_initialPowerEnergyCompatibleAtZero_withInitialSlice
#print axioms intervalDomain_initialTrace_withInitialSlice
#print axioms intervalDomain_classical_withInitialSlice
#print axioms intervalDomain_globalClassical_withInitialSlice
#print axioms intervalDomain_gradientTimeIntegrable_withInitialSlice_of_raw
#print axioms
  intervalDomain_initialPowerEnergyContinuityAtZero_of_traceTendsto_compat
#print axioms
  intervalDomain_initialPowerEnergyContinuityAtZero_of_trace_paperPositive_global_withInitialSlice
#print axioms
  intervalDomain_powerEnergyEndpointContinuity_of_atZero_and_global_classical
#print axioms
  intervalDomain_powerEnergyEndpointContinuity_of_initialPowerEnergyContinuity
#print axioms
  intervalDomain_integratedMoserEnergyWindowFTC_of_global_endpoint_powerInit
#print axioms
  intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_powerInit
#print axioms
  intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_weightedTimeTerm
#print axioms
  intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_pdeCombined
#print axioms
  intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_pdeTerms
#print axioms
  intervalDomain_integratedMoserEnergyWindowFTCLocalData_of_globalPDEInitialData
#print axioms
  intervalDomain_integratedMoserEnergyWindowFTC_of_globalPDEInitialData

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

end
