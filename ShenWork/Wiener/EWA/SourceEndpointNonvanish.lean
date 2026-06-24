import ShenWork.Wiener.EWA.SourcePositivity

/-!
# EWA χ₀<0 Route-A′ — ENDPOINT NONVANISHING of the realized slice

The χ₀<0 classical-regularity assembly `realSlice_classicalRegularity`
(`SourceClassicalRegularity.lean:120`) carries two endpoint-nonvanishing
hypotheses for the `u`-slice (needed by conjunct (5),
`intervalDomainCosineSlice_conjunct7`):

  `huNE0 : ∀ t ∈ Set.Ioo (0:ℝ) T, intervalDomainLift (realSlice u_star t) 0 ≠ 0`
  `huNE1 : ∀ t ∈ Set.Ioo (0:ℝ) T, intervalDomainLift (realSlice u_star t) 1 ≠ 0`

These are immediate from the LANDED strict positivity `realSlice_pos`
(`SourcePositivity.lean:51`):  `0 < realSlice u_star t x` for every interior
time `t ∈ [0,T]` and every `x : intervalDomainPoint`.  The endpoint points
`0` and `1` are *genuine* members of `intervalDomainPoint = Subtype (Icc 0 1)`
(`IntervalDomain.lean:2746`), so positivity already holds AT the endpoints —
there is no boundary-limit gap.  The lift at an `Icc 0 1` point is by
definition the point-function value there
(`intervalDomainLift f x = f ⟨x,hx⟩` for `x ∈ Icc 0 1`,
`IntervalDomain.lean:2750`), so `lift … 0 = realSlice … t ⟨0,_⟩ > 0`
and `lift … 1 = realSlice … t ⟨1,_⟩ > 0`, whence `≠ 0` by `ne_of_gt`.

This mirrors exactly the `v`-side endpoint argument (`hpos0`/`hpos1`) already
inlined in `realSlice_classicalRegularity`, lifted out as named `u`-side lemmas
so the carried `huNE0`/`huNE1` can be discharged by `realSlice_pos`.

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- Membership of the left endpoint `0` in the interval-domain base set. -/
private theorem zero_mem_Icc01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor <;> norm_num

/-- Membership of the right endpoint `1` in the interval-domain base set. -/
private theorem one_mem_Icc01 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor <;> norm_num

/-- **`u`-side endpoint nonvanishing at `0` (χ₀<0).**  From source positivity
`realSlice_pos`, the realized-slice lift is nonzero at the left endpoint `0` for
every interior time `t ∈ Ioo 0 T`.  Matches the carried `huNE0` of
`realSlice_classicalRegularity`. -/
theorem realSlice_lift_endpoint0_ne_zero {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    {u_star : EWA T 1} (hu : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (realSlice u_star t) 0 ≠ 0 := by
  intro t ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) T := Set.Ioo_subset_Icc_self ht
  have hpos : 0 < realSlice u_star t ⟨0, zero_mem_Icc01⟩ :=
    realSlice_pos hδρ hheat hu htIcc ⟨0, zero_mem_Icc01⟩
  have hlift : intervalDomainLift (realSlice u_star t) 0
      = realSlice u_star t ⟨0, zero_mem_Icc01⟩ := by
    rw [intervalDomainLift, dif_pos zero_mem_Icc01]
  rw [hlift]
  exact ne_of_gt hpos

/-- **`u`-side endpoint nonvanishing at `1` (χ₀<0).**  From source positivity
`realSlice_pos`, the realized-slice lift is nonzero at the right endpoint `1` for
every interior time `t ∈ Ioo 0 T`.  Matches the carried `huNE1` of
`realSlice_classicalRegularity`. -/
theorem realSlice_lift_endpoint1_ne_zero {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    {u_star : EWA T 1} (hu : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (realSlice u_star t) 1 ≠ 0 := by
  intro t ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) T := Set.Ioo_subset_Icc_self ht
  have hpos : 0 < realSlice u_star t ⟨1, one_mem_Icc01⟩ :=
    realSlice_pos hδρ hheat hu htIcc ⟨1, one_mem_Icc01⟩
  have hlift : intervalDomainLift (realSlice u_star t) 1
      = realSlice u_star t ⟨1, one_mem_Icc01⟩ := by
    rw [intervalDomainLift, dif_pos one_mem_Icc01]
  rw [hlift]
  exact ne_of_gt hpos

end ShenWork.EWA
