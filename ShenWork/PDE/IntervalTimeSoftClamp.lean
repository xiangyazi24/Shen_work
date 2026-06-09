import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# A C¹ soft clamp for time localization

This file constructs a continuously differentiable "soft clamp" function
`φ : ℝ → ℝ` together with its derivative profile `ψ : ℝ → ℝ`, parametrized by
four reals `c' < c ≤ d < d'`.  The derivative profile `ψ` is a smooth bump that
equals `1` on `[c, d]`, vanishes outside `(c', d')`, and takes values in
`[0, 1]`.  The clamp `φ` is the antiderivative `φ x = c + ∫_c^x ψ`, so that:

* `φ' = ψ` everywhere (FTC for continuous integrands);
* `φ = id` on `[c, d]` (because `ψ = 1` on that range);
* `φ` is monotone (because `ψ ≥ 0`);
* `φ` maps `ℝ` into the compact interval `[c', d']`.

Downstream this is composed with the Picard-limit time argument to turn
time-localized regularity data into globally typed witnesses: the relevant
restart Duhamel integrals only read the family on a compact range where
`φ = id`.

The smooth building block is `Real.smoothTransition` from Mathlib, which is
`0` for `x ≤ 0`, `1` for `x ≥ 1`, monotone, with range in `[0, 1]`.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

namespace ShenWork.IntervalTimeSoftClamp

variable (c' c d d' : ℝ)

/-- The derivative profile: a smooth bump equal to `1` on `[c, d]`, supported in
`[c', d']`, with range in `[0, 1]`.  The left edge ramps up on `[c', c]`, the
right edge ramps down on `[d, d']`. -/
def ψ (x : ℝ) : ℝ :=
  Real.smoothTransition ((x - c') / (c - c')) * Real.smoothTransition ((d' - x) / (d' - d))

/-- The soft clamp itself: the antiderivative of `ψ` anchored at `c`. -/
def φ (x : ℝ) : ℝ := c + ∫ t in c..x, ψ c' c d d' t

variable {c' c d d'}

/-- The left ramp factor of `ψ`. -/
private def ψleft (x : ℝ) : ℝ := Real.smoothTransition ((x - c') / (c - c'))

/-- The right ramp factor of `ψ`. -/
private def ψright (x : ℝ) : ℝ := Real.smoothTransition ((d' - x) / (d' - d))

private theorem ψ_eq (x : ℝ) : ψ c' c d d' x = ψleft (c' := c') (c := c) x * ψright (d := d) (d' := d') x :=
  rfl

theorem ψ_continuous : Continuous (ψ c' c d d') := by
  unfold ψ
  fun_prop

theorem ψ_nonneg (x : ℝ) : 0 ≤ ψ c' c d d' x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem ψ_le_one (x : ℝ) : ψ c' c d d' x ≤ 1 := by
  have h1 : Real.smoothTransition ((x - c') / (c - c')) ≤ 1 := Real.smoothTransition.le_one _
  have h2 : Real.smoothTransition ((d' - x) / (d' - d)) ≤ 1 := Real.smoothTransition.le_one _
  have h2' : (0 : ℝ) ≤ Real.smoothTransition ((d' - x) / (d' - d)) := Real.smoothTransition.nonneg _
  calc ψ c' c d d' x
      = Real.smoothTransition ((x - c') / (c - c')) * Real.smoothTransition ((d' - x) / (d' - d)) := rfl
    _ ≤ 1 * 1 := by
        apply mul_le_mul h1 h2 h2' zero_le_one
    _ = 1 := by ring

/-- On `[c, d]` both ramp factors are saturated, so `ψ = 1`. -/
theorem ψ_eq_one_on (hc' : c' < c) (hd' : d < d') {x : ℝ} (hx : x ∈ Set.Icc c d) :
    ψ c' c d d' x = 1 := by
  obtain ⟨hxc, hxd⟩ := hx
  have hcc' : (0 : ℝ) < c - c' := sub_pos.mpr hc'
  have hdd' : (0 : ℝ) < d' - d := sub_pos.mpr hd'
  -- left factor argument ≥ 1
  have hL : (1 : ℝ) ≤ (x - c') / (c - c') := by
    rw [le_div_iff₀ hcc']
    have : c' ≤ x := le_trans hc'.le hxc
    nlinarith [hxc]
  -- right factor argument ≥ 1
  have hR : (1 : ℝ) ≤ (d' - x) / (d' - d) := by
    rw [le_div_iff₀ hdd']
    nlinarith [hxd]
  have h1 := Real.smoothTransition.one_of_one_le hL
  have h2 := Real.smoothTransition.one_of_one_le hR
  show Real.smoothTransition ((x - c') / (c - c')) * Real.smoothTransition ((d' - x) / (d' - d)) = 1
  rw [h1, h2, mul_one]

/-- Below `c'` the left ramp factor vanishes, hence `ψ = 0`. -/
theorem ψ_eq_zero_left (hc' : c' < c) {x : ℝ} (hx : x ≤ c') : ψ c' c d d' x = 0 := by
  have hcc' : (0 : ℝ) < c - c' := sub_pos.mpr hc'
  have hL : (x - c') / (c - c') ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ hcc'.le
    linarith
  have h1 := Real.smoothTransition.zero_of_nonpos hL
  show Real.smoothTransition ((x - c') / (c - c')) * Real.smoothTransition ((d' - x) / (d' - d)) = 0
  rw [h1, zero_mul]

/-- Above `d'` the right ramp factor vanishes, hence `ψ = 0`. -/
theorem ψ_eq_zero_right (hd' : d < d') {x : ℝ} (hx : d' ≤ x) : ψ c' c d d' x = 0 := by
  have hdd' : (0 : ℝ) < d' - d := sub_pos.mpr hd'
  have hR : (d' - x) / (d' - d) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ hdd'.le
    linarith
  have h2 := Real.smoothTransition.zero_of_nonpos hR
  show Real.smoothTransition ((x - c') / (c - c')) * Real.smoothTransition ((d' - x) / (d' - d)) = 0
  rw [h2, mul_zero]

/-- **FTC**: the clamp has derivative `ψ` everywhere. -/
theorem hasDerivAt_φ (x : ℝ) : HasDerivAt (φ c' c d d') (ψ c' c d d' x) x := by
  have h := ((ψ_continuous (c' := c') (c := c) (d := d) (d' := d')).integral_hasStrictDerivAt c x).hasDerivAt
  -- h : HasDerivAt (fun u => ∫ t in c..u, ψ ... t) (ψ ... x) x
  simpa only [φ] using (h.const_add c)

theorem φ_continuous : Continuous (φ c' c d d') :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_φ x).continuousAt

/-- `ψ ≥ 0` makes `φ` monotone (the antiderivative of a nonnegative function). -/
theorem φ_monotone : Monotone (φ c' c d d') := by
  have hdiff : Differentiable ℝ (φ c' c d d') := fun x => (hasDerivAt_φ x).differentiableAt
  refine monotone_of_deriv_nonneg hdiff (fun x => ?_)
  rw [(hasDerivAt_φ x).deriv]
  exact ψ_nonneg x

/-- On `[c, d]`, `φ` is the identity, because `ψ = 1` on the relevant subrange. -/
theorem φ_eq_id_on (hc' : c' < c) (hd' : d < d') {x : ℝ} (hx : x ∈ Set.Icc c d) :
    φ c' c d d' x = x := by
  obtain ⟨hxc, hxd⟩ := hx
  have hint : (∫ t in c..x, ψ c' c d d' t) = ∫ t in c..x, (1 : ℝ) := by
    apply integral_congr
    intro t ht
    rw [uIcc_of_le hxc] at ht
    obtain ⟨htc, htx⟩ := ht
    exact ψ_eq_one_on hc' hd' ⟨htc, le_trans htx hxd⟩
  rw [φ, hint, intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one]
  ring

/-- The image of `φ` lies in the compact interval `[c', d']`. -/
theorem φ_mem_range (hc' : c' < c) (hcd : c ≤ d) (hd' : d < d') (x : ℝ) :
    φ c' c d d' x ∈ Set.Icc c' d' := by
  have hcd' : c ≤ d' := le_trans hcd (le_of_lt hd')
  -- integrability of ψ and of the constant comparators
  have hψint : ∀ a b : ℝ, IntervalIntegrable (ψ c' c d d') volume a b := fun a b =>
    (ψ_continuous).intervalIntegrable a b
  constructor
  · -- lower bound c' ≤ φ x
    rcases le_total c x with hcx | hxc
    · -- x ≥ c : ∫_c^x ψ ≥ 0, so φ x ≥ c ≥ c'
      have hnn : (0 : ℝ) ≤ ∫ t in c..x, ψ c' c d d' t :=
        integral_nonneg hcx (fun u _ => ψ_nonneg u)
      have : c' ≤ c := le_of_lt hc'
      rw [φ]; linarith
    · -- x ≤ c : φ x = c - ∫_x^c ψ ; bound ∫_x^c ψ ≤ ∫_{c'}^c 1 = c - c'
      -- so φ x ≥ c - (c - c') = c'
      have hsym : (∫ t in c..x, ψ c' c d d' t) = - ∫ t in x..c, ψ c' c d d' t := by
        rw [integral_symm]
      -- ∫_x^c ψ ≤ ∫_{min x c'}^c ψ over a larger interval ... bound directly
      -- Split: on [x, c], ψ = 0 for t ≤ c', and ψ ≤ 1 always.
      -- ∫_x^c ψ ≤ ∫_x^c (indicator), bound by c - c' via: ∫_x^c ψ ≤ ∫_{c'}^c 1 if x ≤ c'
      -- Handle two subcases on position of x relative to c'.
      have hub : (∫ t in x..c, ψ c' c d d' t) ≤ c - c' := by
        rcases le_total x c' with hxc' | hc'x
        · -- x ≤ c' : ψ = 0 on [x, c'] and ψ ≤ 1 on [c', c]
          have hsplit : (∫ t in x..c, ψ c' c d d' t)
              = (∫ t in x..c', ψ c' c d d' t) + ∫ t in c'..c, ψ c' c d d' t :=
            (integral_add_adjacent_intervals (hψint x c') (hψint c' c)).symm
          have hleft0 : (∫ t in x..c', ψ c' c d d' t) = 0 := by
            rw [← integral_zero (a := x) (b := c')]
            apply integral_congr
            intro t ht
            rw [uIcc_of_le hxc'] at ht
            exact ψ_eq_zero_left hc' ht.2
          have hright : (∫ t in c'..c, ψ c' c d d' t) ≤ ∫ t in c'..c, (1 : ℝ) := by
            apply integral_mono_on (le_of_lt hc') (hψint c' c) (intervalIntegrable_const)
            intro t _
            exact ψ_le_one t
          rw [hsplit, hleft0, zero_add]
          calc (∫ t in c'..c, ψ c' c d d' t)
              ≤ ∫ t in c'..c, (1 : ℝ) := hright
            _ = c - c' := by rw [intervalIntegral.integral_const]; simp
        · -- c' ≤ x ≤ c : ψ ≤ 1 on [x, c], ∫_x^c ψ ≤ c - x ≤ c - c'
          have hle : (∫ t in x..c, ψ c' c d d' t) ≤ ∫ t in x..c, (1 : ℝ) := by
            apply integral_mono_on hxc (hψint x c) (intervalIntegrable_const)
            intro t _
            exact ψ_le_one t
          calc (∫ t in x..c, ψ c' c d d' t)
              ≤ ∫ t in x..c, (1 : ℝ) := hle
            _ = c - x := by rw [intervalIntegral.integral_const]; simp
            _ ≤ c - c' := by linarith
      rw [φ, hsym]; linarith
  · -- upper bound φ x ≤ d'
    rcases le_total c x with hcx | hxc
    · -- x ≥ c : bound ∫_c^x ψ ≤ d' - c using ψ ≤ 1 and ψ = 0 beyond d'
      have hub : (∫ t in c..x, ψ c' c d d' t) ≤ d' - c := by
        rcases le_total x d' with hxd' | hd'x
        · -- c ≤ x ≤ d' : ψ ≤ 1, ∫_c^x ψ ≤ x - c ≤ d' - c
          have hle : (∫ t in c..x, ψ c' c d d' t) ≤ ∫ t in c..x, (1 : ℝ) := by
            apply integral_mono_on hcx (hψint c x) (intervalIntegrable_const)
            intro t _
            exact ψ_le_one t
          calc (∫ t in c..x, ψ c' c d d' t)
              ≤ ∫ t in c..x, (1 : ℝ) := hle
            _ = x - c := by rw [intervalIntegral.integral_const]; simp
            _ ≤ d' - c := by linarith
        · -- x ≥ d' : split at d' ; ψ ≤ 1 on [c, d'], ψ = 0 on [d', x]
          have hsplit : (∫ t in c..x, ψ c' c d d' t)
              = (∫ t in c..d', ψ c' c d d' t) + ∫ t in d'..x, ψ c' c d d' t :=
            (integral_add_adjacent_intervals (hψint c d') (hψint d' x)).symm
          have hright0 : (∫ t in d'..x, ψ c' c d d' t) = 0 := by
            rw [← integral_zero (a := d') (b := x)]
            apply integral_congr
            intro t ht
            rw [uIcc_of_le hd'x] at ht
            exact ψ_eq_zero_right hd' ht.1
          have hleft : (∫ t in c..d', ψ c' c d d' t) ≤ ∫ t in c..d', (1 : ℝ) := by
            apply integral_mono_on hcd' (hψint c d') (intervalIntegrable_const)
            intro t _
            exact ψ_le_one t
          rw [hsplit, hright0, add_zero]
          calc (∫ t in c..d', ψ c' c d d' t)
              ≤ ∫ t in c..d', (1 : ℝ) := hleft
            _ = d' - c := by rw [intervalIntegral.integral_const]; simp
      rw [φ]; linarith
    · -- x ≤ c : φ x = c - ∫_x^c ψ ≤ c ≤ d'
      have hsym : (∫ t in c..x, ψ c' c d d' t) = - ∫ t in x..c, ψ c' c d d' t := by
        rw [integral_symm]
      have hnn : (0 : ℝ) ≤ ∫ t in x..c, ψ c' c d d' t :=
        integral_nonneg hxc (fun u _ => ψ_nonneg u)
      have : c ≤ d' := hcd'
      rw [φ, hsym]; linarith

/-- Bundled existence statement packaging the soft-clamp properties for
downstream use. -/
theorem exists_softClamp (c' c d d' : ℝ) (h1 : c' < c) (h2 : c ≤ d) (h3 : d < d') :
    ∃ φ ψ : ℝ → ℝ, (∀ x, HasDerivAt φ (ψ x) x) ∧ Continuous ψ ∧
      (∀ x, 0 ≤ ψ x) ∧ (∀ x, ψ x ≤ 1) ∧
      (∀ x ∈ Set.Icc c d, φ x = x) ∧ (∀ x, φ x ∈ Set.Icc c' d') := by
  refine ⟨φ c' c d d', ψ c' c d d', ?_, ψ_continuous, ψ_nonneg, ψ_le_one, ?_, ?_⟩
  · exact fun x => hasDerivAt_φ x
  · intro x hx; exact φ_eq_id_on h1 h3 hx
  · intro x; exact φ_mem_range h1 h2 h3 x

end ShenWork.IntervalTimeSoftClamp
