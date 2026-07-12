import ShenWork.Paper2.IntervalDomainMClassicalRestart
import ShenWork.Paper2.IntervalDomainL2StaticVDifference
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Globally continuous restart sources for the faithful interval equation

On a compact positive-time window we clamp time and space into the window,
then reconstruct the chemical gradient from the elliptic equation.  This gives
globally continuous representatives of the faithful flux and logistic source.
They agree with the physical fields on the restart rectangle and are suitable
for the measurable/Fubini semigroup API.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

/-- Clamp relative time into `[0,h]`. -/
def restartTimeClamp (h r : ℝ) : ℝ := min h (max 0 r)

lemma restartTimeClamp_continuous (h : ℝ) :
    Continuous (restartTimeClamp h) := by
  unfold restartTimeClamp
  fun_prop

lemma restartTimeClamp_mem {h : ℝ} (hh : 0 ≤ h) (r : ℝ) :
    restartTimeClamp h r ∈ Icc (0 : ℝ) h := by
  unfold restartTimeClamp
  constructor
  · exact le_min hh (le_max_left _ _)
  · exact min_le_left _ _

lemma restartTimeClamp_eq_self {h r : ℝ} (hr : r ∈ Icc (0 : ℝ) h) :
    restartTimeClamp h r = r := by
  unfold restartTimeClamp
  rw [max_eq_right hr.1, min_eq_right hr.2]

/-- Globally defined clamped solution representative on a restart window. -/
def restartField (a h : ℝ)
    (w : ℝ → intervalDomainPoint → ℝ) (r x : ℝ) : ℝ :=
  intervalDomainLift (w (a + restartTimeClamp h r)) (clamp01 x)

lemma restartField_eq_physical
    {a h r x : ℝ} {w : ℝ → intervalDomainPoint → ℝ}
    (hr : r ∈ Icc (0 : ℝ) h) (hx : x ∈ Icc (0 : ℝ) 1) :
    restartField a h w r x = intervalDomainLift (w (a + r)) x := by
  simp [restartField, restartTimeClamp_eq_self hr, clamp01_eq_self hx]

theorem restartField_continuous
    {p : CM2Params} {T a h : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (w : ℝ → intervalDomainPoint → ℝ) (hw : w = u ∨ w = v) :
    Continuous (Function.uncurry (restartField a h w)) := by
  have htime : ∀ r : ℝ, a + restartTimeClamp h r ∈ Ioo (0 : ℝ) T := by
    intro r
    have hr := restartTimeClamp_mem hh r
    exact ⟨add_pos_of_pos_of_nonneg ha hr.1,
      lt_of_le_of_lt (by simpa [add_comm] using add_le_add_left hr.2 a) hahT⟩
  have hmap : Set.MapsTo
      (fun z : ℝ × ℝ =>
        (a + restartTimeClamp h z.1, clamp01 z.2)) Set.univ
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
    intro z _
    exact ⟨htime z.1, clamp01_mem z.2⟩
  have harg : Continuous (fun z : ℝ × ℝ =>
      (a + restartTimeClamp h z.1, clamp01 z.2)) := by
    exact (continuous_const.add
      ((restartTimeClamp_continuous h).comp continuous_fst)).prodMk
        (clamp01_continuous.comp continuous_snd)
  rcases hw with hw | hw
  · have hc := hsol.regularity.2.2.2.2.2.2.1
    have hcomp : ContinuousOn
        ((Function.uncurry (fun t x => intervalDomainLift (u t) x)) ∘
          fun z : ℝ × ℝ =>
            (a + restartTimeClamp h z.1, clamp01 z.2)) Set.univ :=
      hc.comp harg.continuousOn hmap
    have hout := continuousOn_univ.mp hcomp
    simpa [hw, Function.comp_def, restartField, Function.uncurry] using hout
  · have hc := hsol.regularity.2.2.2.2.2.2.2
    have hcomp : ContinuousOn
        ((Function.uncurry (fun t x => intervalDomainLift (v t) x)) ∘
          fun z : ℝ × ℝ =>
            (a + restartTimeClamp h z.1, clamp01 z.2)) Set.univ :=
      hc.comp harg.continuousOn hmap
    have hout := continuousOn_univ.mp hcomp
    simpa [hw, Function.comp_def, restartField, Function.uncurry] using hout

/-- Clamped elliptic right-hand side `μv - νu^γ`. -/
def restartChemRhs (p : CM2Params) (a h : ℝ)
    (u v : ℝ → intervalDomainPoint → ℝ) (r x : ℝ) : ℝ :=
  p.μ * restartField a h v r x -
    p.ν * (restartField a h u r x) ^ p.γ

theorem restartChemRhs_continuous
    {p : CM2Params} {T a h : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T) :
    Continuous (Function.uncurry (restartChemRhs p a h u v)) := by
  have hu := restartField_continuous hsol ha hh hahT u (Or.inl rfl)
  have hv := restartField_continuous hsol ha hh hahT v (Or.inr rfl)
  have hupow : Continuous
      (fun z : ℝ × ℝ => (restartField a h u z.1 z.2) ^ p.γ) :=
    hu.rpow_const (fun _ => Or.inr p.hγ.le)
  exact (continuous_const.mul hv).sub (continuous_const.mul hupow)

/-- Reconstructed clamped chemical gradient. -/
def restartChemGrad (p : CM2Params) (a h : ℝ)
    (u v : ℝ → intervalDomainPoint → ℝ) (r x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..clamp01 x, restartChemRhs p a h u v r y

theorem restartChemGrad_continuous
    {p : CM2Params} {T a h : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T) :
    Continuous (Function.uncurry (restartChemGrad p a h u v)) := by
  have hrhs := restartChemRhs_continuous hsol ha hh hahT
  have hf : Continuous (Function.uncurry
      (fun z : ℝ × ℝ => fun y : ℝ => restartChemRhs p a h u v z.1 y)) := by
    exact hrhs.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hparam : Continuous (fun z : ℝ × ℝ =>
      ∫ y in (0 : ℝ)..clamp01 z.2,
        restartChemRhs p a h u v z.1 y) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) hf (clamp01_continuous.comp continuous_snd)
  simpa [restartChemGrad, Function.uncurry] using hparam

/-- On the physical restart rectangle, the reconstructed primitive is exactly
the spatial derivative of the classical chemical slice. -/
theorem restartChemGrad_eq_deriv
    {p : CM2Params} {T a h r x : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hr : r ∈ Icc (0 : ℝ) h) (hx : x ∈ Icc (0 : ℝ) 1) :
    restartChemGrad p a h u v r x =
      deriv (intervalDomainLift (v (a + r))) x := by
  let τ : ℝ := a + r
  let V : ℝ → ℝ := intervalDomainLift (v τ)
  have hτ0 : 0 < τ := by dsimp [τ]; exact add_pos_of_pos_of_nonneg ha hr.1
  have hτT : τ < T := by
    dsimp [τ]
    exact lt_of_le_of_lt
      (by simpa [add_comm] using add_le_add_left hr.2 a) hahT
  have hτ : τ ∈ Ioo (0 : ℝ) T := ⟨hτ0, hτT⟩
  have hV2 : ContDiffOn ℝ 2 V (Icc (0 : ℝ) 1) := by
    simpa [V, τ] using (hsol.regularity.2.2.2.2.1 τ hτ).2.1
  have hd0 : derivWithin V (Icc (0 : ℝ) 1) 0 = 0 := by
    simpa [V, τ] using derivWithin_left_zero hsol hτ0 hτT v (Or.inr rfl)
  have hd1 : derivWithin V (Icc (0 : ℝ) 1) 1 = 0 := by
    simpa [V, τ] using derivWithin_right_zero hsol hτ0 hτT v (Or.inr rfl)
  have hV1 : ContDiffOn ℝ 1 (deriv V) (Icc (0 : ℝ) 1) :=
    deriv_lift_contDiffOn_one_Icc hV2 hd0 hd1
  have hcont : ContinuousOn (deriv V) (Icc (0 : ℝ) x) :=
    hV1.continuousOn.mono (fun y hy => ⟨hy.1, hy.2.trans hx.2⟩)
  have hderiv : ∀ y ∈ Ioo (0 : ℝ) x,
      HasDerivWithinAt (deriv V) (restartChemRhs p a h u v r y)
        (Ioi y) y := by
    intro y hy
    have hy01 : y ∈ Ioo (0 : ℝ) 1 := ⟨hy.1, hy.2.trans_le hx.2⟩
    have hdiff : DifferentiableAt ℝ (deriv V) y :=
      ((ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
        isOpen_Ioo (hV2.mono Ioo_subset_Icc_self) hy01).2).differentiableAt
    have hpde := v_xx_eq_reaction_lift hsol hτ0 hτT hy01.1 hy01.2
    have heq : deriv (deriv V) y = restartChemRhs p a h u v r y := by
      rw [hpde]
      simp only [restartChemRhs]
      rw [restartField_eq_physical hr (Ioo_subset_Icc_self hy01),
        restartField_eq_physical hr (Ioo_subset_Icc_self hy01)]
    exact (hdiff.hasDerivAt.congr_deriv heq).hasDerivWithinAt
  have hrhsCont : Continuous (restartChemRhs p a h u v r) :=
    (restartChemRhs_continuous hsol ha hh hahT).uncurry_left r
  have hrhsInt : IntervalIntegrable (restartChemRhs p a h u v r)
      volume 0 x := hrhsCont.intervalIntegrable (μ := volume) 0 x
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    hx.1 hcont hderiv hrhsInt
  have hV0 : deriv V 0 = 0 := by
    simpa [V, τ] using (hsol.regularity.2.2.2.2.1 τ hτ).2.2.1
  rw [restartChemGrad, clamp01_eq_self hx, hFTC, hV0, sub_zero]

/-- Faithful clamped chemotactic flux on a restart window. -/
def restartFluxM (p : CM2Params) (a h : ℝ)
    (u v : ℝ → intervalDomainPoint → ℝ) (r x : ℝ) : ℝ :=
  (restartField a h u r x) ^ p.m * restartChemGrad p a h u v r x /
    (1 + restartField a h v r x) ^ p.β

/-- Clamped logistic source on a restart window. -/
def restartLogisticM (p : CM2Params) (a h : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (r x : ℝ) : ℝ :=
  restartField a h u r x *
    (p.a - p.b * (restartField a h u r x) ^ p.α)

lemma restartField_u_pos
    {p : CM2Params} {T a h : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T) (r x : ℝ) :
    0 < restartField a h u r x := by
  have hr := restartTimeClamp_mem hh r
  have ht0 : 0 < a + restartTimeClamp h r :=
    add_pos_of_pos_of_nonneg ha hr.1
  have htT : a + restartTimeClamp h r < T :=
    lt_of_le_of_lt
      (by simpa [add_comm] using add_le_add_left hr.2 a) hahT
  have hx := clamp01_mem x
  simpa [restartField, intervalDomainLift, hx] using
    hsol.u_pos' ht0 htT (x := (⟨clamp01 x, hx⟩ : intervalDomainPoint))

lemma restartField_v_nonneg
    {p : CM2Params} {T a h : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T) (r x : ℝ) :
    0 ≤ restartField a h v r x := by
  have hr := restartTimeClamp_mem hh r
  have ht0 : 0 < a + restartTimeClamp h r :=
    add_pos_of_pos_of_nonneg ha hr.1
  have htT : a + restartTimeClamp h r < T :=
    lt_of_le_of_lt
      (by simpa [add_comm] using add_le_add_left hr.2 a) hahT
  have hx := clamp01_mem x
  simpa [restartField, intervalDomainLift, hx] using
    hsol.v_nonneg ht0 htT (x := (⟨clamp01 x, hx⟩ : intervalDomainPoint))

theorem restartFluxM_continuous
    {p : CM2Params} {T a h : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T) :
    Continuous (Function.uncurry (restartFluxM p a h u v)) := by
  have hu := restartField_continuous hsol ha hh hahT u (Or.inl rfl)
  have hv := restartField_continuous hsol ha hh hahT v (Or.inr rfl)
  have hg := restartChemGrad_continuous hsol ha hh hahT
  have humpow : Continuous
      (fun z : ℝ × ℝ => (restartField a h u z.1 z.2) ^ p.m) :=
    hu.rpow_const (fun _ => Or.inr p.hm.le)
  have hdenbase : Continuous
      (fun z : ℝ × ℝ => 1 + restartField a h v z.1 z.2) :=
    continuous_const.add hv
  have hden : Continuous
      (fun z : ℝ × ℝ => (1 + restartField a h v z.1 z.2) ^ p.β) :=
    hdenbase.rpow_const (fun _ => Or.inr p.hβ)
  have hden_ne : ∀ z : ℝ × ℝ,
      (1 + restartField a h v z.1 z.2) ^ p.β ≠ 0 := by
    intro z
    exact ne_of_gt (Real.rpow_pos_of_pos (by
      linarith [restartField_v_nonneg hsol ha hh hahT z.1 z.2]) _)
  exact (humpow.mul hg).div hden hden_ne

theorem restartLogisticM_continuous
    {p : CM2Params} {T a h : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T) :
    Continuous (Function.uncurry (restartLogisticM p a h u)) := by
  have hu := restartField_continuous hsol ha hh hahT u (Or.inl rfl)
  have hupow : Continuous
      (fun z : ℝ × ℝ => (restartField a h u z.1 z.2) ^ p.α) :=
    hu.rpow_const (fun _ => Or.inr p.hα.le)
  exact hu.mul (continuous_const.sub (continuous_const.mul hupow))

theorem restartFluxM_eq_physical
    {p : CM2Params} {T a h r x : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hr : r ∈ Icc (0 : ℝ) h) (hx : x ∈ Icc (0 : ℝ) 1) :
    restartFluxM p a h u v r x = intervalFluxM p (u (a + r)) (v (a + r)) x := by
  rw [restartFluxM, intervalFluxM,
    restartField_eq_physical hr hx, restartField_eq_physical hr hx,
    restartChemGrad_eq_deriv hsol ha hh hahT hr hx]

theorem restartLogisticM_eq_physical
    {p : CM2Params} {a h r x : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hr : r ∈ Icc (0 : ℝ) h) (hx : x ∈ Icc (0 : ℝ) 1) :
    restartLogisticM p a h u r x = logisticLiftedM p (u (a + r)) x := by
  rw [restartLogisticM, logisticLiftedM,
    restartField_eq_physical hr hx]
  simp [intervalDomainLift, hx]

lemma restartTimeClamp_idem {h : ℝ} (hh : 0 ≤ h) (r : ℝ) :
    restartTimeClamp h (restartTimeClamp h r) = restartTimeClamp h r :=
  restartTimeClamp_eq_self (restartTimeClamp_mem hh r)

lemma clamp01_idem (x : ℝ) : clamp01 (clamp01 x) = clamp01 x :=
  clamp01_eq_self (clamp01_mem x)

lemma restartField_clamp
    {a h : ℝ} (hh : 0 ≤ h)
    (w : ℝ → intervalDomainPoint → ℝ) (r x : ℝ) :
    restartField a h w r x =
      restartField a h w (restartTimeClamp h r) (clamp01 x) := by
  simp [restartField, restartTimeClamp_idem hh, clamp01_idem]

lemma restartChemRhs_clamp
    (p : CM2Params) {a h : ℝ} (hh : 0 ≤ h)
    (u v : ℝ → intervalDomainPoint → ℝ) (r x : ℝ) :
    restartChemRhs p a h u v r x =
      restartChemRhs p a h u v (restartTimeClamp h r) (clamp01 x) := by
  unfold restartChemRhs
  rw [restartField_clamp hh u r x, restartField_clamp hh v r x]

lemma restartField_timeClamp
    {a h : ℝ} (hh : 0 ≤ h)
    (w : ℝ → intervalDomainPoint → ℝ) (r x : ℝ) :
    restartField a h w r x =
      restartField a h w (restartTimeClamp h r) x := by
  simp only [restartField, restartTimeClamp_idem hh]

lemma restartChemRhs_timeClamp
    (p : CM2Params) {a h : ℝ} (hh : 0 ≤ h)
    (u v : ℝ → intervalDomainPoint → ℝ) (r x : ℝ) :
    restartChemRhs p a h u v r x =
      restartChemRhs p a h u v (restartTimeClamp h r) x := by
  unfold restartChemRhs
  rw [restartField_timeClamp hh u r x, restartField_timeClamp hh v r x]

lemma restartChemGrad_clamp
    (p : CM2Params) {a h : ℝ} (hh : 0 ≤ h)
    (u v : ℝ → intervalDomainPoint → ℝ) (r x : ℝ) :
    restartChemGrad p a h u v r x =
      restartChemGrad p a h u v (restartTimeClamp h r) (clamp01 x) := by
  unfold restartChemGrad
  rw [clamp01_idem]
  refine intervalIntegral.integral_congr (fun y _ => ?_)
  exact restartChemRhs_timeClamp p hh u v r y

lemma restartFluxM_clamp
    (p : CM2Params) {a h : ℝ} (hh : 0 ≤ h)
    (u v : ℝ → intervalDomainPoint → ℝ) (r x : ℝ) :
    restartFluxM p a h u v r x =
      restartFluxM p a h u v (restartTimeClamp h r) (clamp01 x) := by
  unfold restartFluxM
  rw [restartField_clamp hh u r x, restartField_clamp hh v r x,
    restartChemGrad_clamp p hh u v r x]

lemma restartLogisticM_clamp
    (p : CM2Params) {a h : ℝ} (hh : 0 ≤ h)
    (u : ℝ → intervalDomainPoint → ℝ) (r x : ℝ) :
    restartLogisticM p a h u r x =
      restartLogisticM p a h u (restartTimeClamp h r) (clamp01 x) := by
  unfold restartLogisticM
  rw [restartField_clamp hh u r x]

/-- A continuous two-variable field which factors through the compact restart
rectangle has a global absolute bound. -/
theorem exists_abs_bound_of_continuous_restart_clamp
    {h : ℝ} (hh : 0 ≤ h) {F : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F))
    (hclamp : ∀ r x, F r x = F (restartTimeClamp h r) (clamp01 x)) :
    ∃ C ≥ 0, ∀ r x, |F r x| ≤ C := by
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKne : K.Nonempty :=
    ⟨(0, 0), ⟨⟨le_rfl, hh⟩, ⟨le_rfl, by norm_num⟩⟩⟩
  have habs : Continuous (fun z : ℝ × ℝ => |F z.1 z.2|) := hF.abs
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hKne habs.continuousOn
  refine ⟨|F z.1 z.2|, abs_nonneg _, ?_⟩
  intro r x
  rw [hclamp r x]
  have hm := hmax (show (restartTimeClamp h r, clamp01 x) ∈ K from
    ⟨restartTimeClamp_mem hh r, clamp01_mem x⟩)
  exact hm

theorem exists_restartFluxM_bound
    {p : CM2Params} {T a h : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T) :
    ∃ C ≥ 0, ∀ r x, |restartFluxM p a h u v r x| ≤ C :=
  exists_abs_bound_of_continuous_restart_clamp hh
    (restartFluxM_continuous hsol ha hh hahT)
    (restartFluxM_clamp p hh u v)

theorem exists_restartLogisticM_bound
    {p : CM2Params} {T a h : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T) :
    ∃ C ≥ 0, ∀ r x, |restartLogisticM p a h u r x| ≤ C :=
  exists_abs_bound_of_continuous_restart_clamp hh
    (restartLogisticM_continuous hsol ha hh hahT)
    (restartLogisticM_clamp p hh u)

#print axioms restartChemGrad_eq_deriv
#print axioms restartFluxM_continuous
#print axioms exists_restartFluxM_bound

end ShenWork.Paper2.IntervalDomainM
