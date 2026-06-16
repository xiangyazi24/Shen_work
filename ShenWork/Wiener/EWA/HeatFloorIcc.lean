import ShenWork.Wiener.EWA.HeatFloor

/-!
# EWA brick (χ₀<0 Route A′) — the `[0,1]`-FLOOR strengthening of the heat-floor.

The committed heat-floor `heatEWA_uniformFloor` (`ShenWork.Wiener.EWA.HeatFloor`)
consumes a *full-real-line* positivity floor `hfloor : ∀ y : ℝ, δ ≤ u₀ y` on the
real-space source.  This was the form available *before* the faithfulness fix to
`PaperPositiveInitialDatum`, which carried only interior-positivity and hence no
floor at all (obstruction (b)).

The fixed data class `PaperPositiveInitialDatum intervalDomain u₀` now carries a
**uniform positivity floor on the CLOSED domain**
`∃ η > 0, ∀ x : intervalDomain.Point, η ≤ u₀ x`, i.e. `η ≤ u₀ x` for every
`x ∈ Icc 0 1` (the `Point` type is `Subtype (Icc 0 1)`).  This file shows that the
floor is needed *only on `[0,1]`*: the heat-kernel floor
`intervalFullSemigroupOperator_ge_floor` integrates against the Neumann kernel over
`intervalMeasure 1 = volume.restrict (Icc 0 1)`, whose support is `[0,1]`, so the
pointwise monotonicity step only ever evaluates `δ ≤ u₀ y` at `y ∈ [0,1]`.  We
therefore re-derive the entire floor chain with the strictly weaker hypothesis

  `hfloorIcc : ∀ y ∈ Set.Icc (0:ℝ) 1, δ ≤ u₀ y`

down to `heatEWA_uniformFloor_Icc`, which is exactly the form the closed-domain
floor of `PaperPositiveInitialDatum` supplies.

**Frontier consequence.**  With this brick, obstruction (b) (the uniform interior
floor for the EWA heat positivity) is *fully discharged from the now-available
closed-domain floor*: the `hheat` input of the χ₀<0 EWA fixed point is produced for
any floor-datum.  The ONLY residual datum-level gap for the EWA route is
obstruction (a) — the Wiener-ℓ¹ / absolute cosine summability `Summable |c₀ k|`
and the corresponding `MemW` membership — which the C(Ω̄)+floor class does NOT
supply (a merely continuous floored datum need not be absolutely cosine-summable).

No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/

open scoped BigOperators
open Set
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalFullKernelInterchange
open ShenWork.IntervalResolverPositivity

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### (B′) Heat-kernel floor from a floor on `[0,1]` only. -/

/-- **`[0,1]`-floor strengthening of `intervalFullSemigroupOperator_ge_floor`.**
The full Neumann semigroup integrates against `intervalMeasure 1`, supported on
`Icc 0 1`; the monotonicity step `∫ K·u₀ ≥ ∫ K·δ` therefore only needs the floor
`δ ≤ u₀ y` for `y ∈ [0,1]`, supplied here a.e. on the restricted measure. -/
theorem intervalFullSemigroupOperator_ge_floor_Icc {t : ℝ} (ht : 0 < t)
    {u₀ : ℝ → ℝ} (hu₀ : Continuous u₀) {δ : ℝ}
    (hfloor : ∀ y ∈ Set.Icc (0 : ℝ) 1, δ ≤ u₀ y) (x : ℝ) :
    δ ≤ intervalFullSemigroupOperator t u₀ x := by
  have hKint : MeasureTheory.Integrable
      (fun y => intervalNeumannFullKernel t x y)
      (ShenWork.IntervalDomain.intervalMeasure 1) :=
    intervalNeumannFullKernel_integrable ht x
  have hmass : (∫ y, intervalNeumannFullKernel t x y
      ∂(ShenWork.IntervalDomain.intervalMeasure 1)) = 1 :=
    intervalNeumannFullKernel_intervalMeasure_integral_eq_one ht x
  have hconst : (∫ y, intervalNeumannFullKernel t x y * δ
      ∂(ShenWork.IntervalDomain.intervalMeasure 1)) = δ := by
    rw [MeasureTheory.integral_mul_const, hmass, one_mul]
  have hKu : MeasureTheory.Integrable
      (fun y => intervalNeumannFullKernel t x y * u₀ y)
      (ShenWork.IntervalDomain.intervalMeasure 1) := by
    have hcont : ContinuousOn
        (fun y => intervalNeumannFullKernel t x y * u₀ y) (Set.Icc (0 : ℝ) 1) :=
      (continuousOn_intervalNeumannFullKernel_snd ht x).mul hu₀.continuousOn
    simp only [ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet]
    exact hcont.integrableOn_Icc
  -- a.e. (on `volume.restrict (Icc 0 1)`) pointwise inequality `K·δ ≤ K·u₀`,
  -- using the floor only on `Icc 0 1`.
  have hae : (fun y => intervalNeumannFullKernel t x y * δ)
      ≤ᵐ[ShenWork.IntervalDomain.intervalMeasure 1]
      (fun y => intervalNeumannFullKernel t x y * u₀ y) := by
    simp only [ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun y hy => mul_le_mul_of_nonneg_left (hfloor y hy)
        (intervalNeumannFullKernel_nonneg ht x y))
  have hmono : (∫ y, intervalNeumannFullKernel t x y * δ
        ∂(ShenWork.IntervalDomain.intervalMeasure 1))
      ≤ ∫ y, intervalNeumannFullKernel t x y * u₀ y
        ∂(ShenWork.IntervalDomain.intervalMeasure 1) :=
    MeasureTheory.integral_mono_ae (hKint.mul_const δ) hKu hae
  show δ ≤ ∫ y, intervalNeumannFullKernel t x y * u₀ y
      ∂(ShenWork.IntervalDomain.intervalMeasure 1)
  calc δ = ∫ y, intervalNeumannFullKernel t x y * δ
        ∂(ShenWork.IntervalDomain.intervalMeasure 1) := hconst.symm
    _ ≤ _ := hmono

/-- **`[0,1]`-floor on the cosine spectral heat value** (`t>0`, interior `x`). -/
theorem cosineHeatValue_ge_floor_Icc01 {t : ℝ} (ht : 0 < t)
    {u₀ : ℝ → ℝ} (hu₀ : Continuous u₀) {δ : ℝ}
    (hfloor : ∀ y ∈ Set.Icc (0 : ℝ) 1, δ ≤ u₀ y)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    δ ≤ unitIntervalCosineHeatValue t (cosineCoeffs u₀) x := by
  rw [← intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional t ht u₀ hu₀ x hx
        (fun y => intervalNeumannFullKernel_cosineKernel_identity ht x y)]
  exact intervalFullSemigroupOperator_ge_floor_Icc ht hu₀ hfloor x

/-- **`[0,1]`-floor on `Icc 0 1` for `t > 0`** (closed-preimage extension to the
boundary). -/
theorem cosineHeatValue_ge_floor_IccDom_pos {t : ℝ} (ht : 0 < t)
    {u₀ : ℝ → ℝ} (hu₀ : Continuous u₀) {δ : ℝ}
    (hfloor : ∀ y ∈ Set.Icc (0 : ℝ) 1, δ ≤ u₀ y)
    (hsum : Summable (fun k => |cosineCoeffs u₀ k|))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    δ ≤ unitIntervalCosineHeatValue t (cosineCoeffs u₀) x := by
  have hcont : Continuous (fun x => unitIntervalCosineHeatValue t (cosineCoeffs u₀) x) :=
    cosineHeatValue_continuous hsum ht.le
  have hclosed : IsClosed
      ((fun x => unitIntervalCosineHeatValue t (cosineCoeffs u₀) x) ⁻¹' Set.Ici δ) :=
    isClosed_Ici.preimage hcont
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆
      (fun x => unitIntervalCosineHeatValue t (cosineCoeffs u₀) x) ⁻¹' Set.Ici δ :=
    fun y hy => cosineHeatValue_ge_floor_Icc01 ht hu₀ hfloor hy
  have hIcc : Set.Icc (0 : ℝ) 1 ⊆
      (fun x => unitIntervalCosineHeatValue t (cosineCoeffs u₀) x) ⁻¹' Set.Ici δ := by
    rw [← closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact hclosed.closure_subset_iff.mpr hsub
  exact hIcc hx

/-- **`[0,1]`-floor on `Icc 0 1` for ALL `t ≥ 0`** (continuity in `t` to `t = 0`). -/
theorem cosineHeatValue_ge_floor_IccDom {t : ℝ} (ht : 0 ≤ t)
    {u₀ : ℝ → ℝ} (hu₀ : Continuous u₀) {δ : ℝ}
    (hfloor : ∀ y ∈ Set.Icc (0 : ℝ) 1, δ ≤ u₀ y)
    (hsum : Summable (fun k => |cosineCoeffs u₀ k|))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    δ ≤ unitIntervalCosineHeatValue t (cosineCoeffs u₀) x := by
  rcases lt_or_eq_of_le ht with htpos | hteq
  · exact cosineHeatValue_ge_floor_IccDom_pos htpos hu₀ hfloor hsum hx
  · subst hteq
    have hcontOn : ContinuousOn (fun s => unitIntervalCosineHeatValue s (cosineCoeffs u₀) x)
        (Set.Ici 0) := cosineHeatValue_continuousOn_t hsum x
    have hcwa : ContinuousWithinAt
        (fun s => unitIntervalCosineHeatValue s (cosineCoeffs u₀) x) (Set.Ici 0) 0 :=
      hcontOn 0 Set.self_mem_Ici
    have htend : Filter.Tendsto
        (fun s => unitIntervalCosineHeatValue s (cosineCoeffs u₀) x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (unitIntervalCosineHeatValue 0 (cosineCoeffs u₀) x)) :=
      hcwa.tendsto.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact cosineHeatValue_ge_floor_IccDom_pos hs hu₀ hfloor hsum hx

/-- **`[0,1]`-floor for ALL real `x` and ALL `t ≥ 0`** (period-`2` shift + evenness
reduce any real `x` to a representative in `[0,1]`; the floor is consumed only
there). -/
theorem cosineHeatValue_ge_floor_Icc_all {t : ℝ} (ht : 0 ≤ t)
    {u₀ : ℝ → ℝ} (hu₀ : Continuous u₀) {δ : ℝ}
    (hfloor : ∀ y ∈ Set.Icc (0 : ℝ) 1, δ ≤ u₀ y)
    (hsum : Summable (fun k => |cosineCoeffs u₀ k|)) (x : ℝ) :
    δ ≤ unitIntervalCosineHeatValue t (cosineCoeffs u₀) x := by
  set m : ℤ := round (x / 2) with hm
  set y : ℝ := x - 2 * m with hy
  have hVxy : unitIntervalCosineHeatValue t (cosineCoeffs u₀) x
      = unitIntervalCosineHeatValue t (cosineCoeffs u₀) y := by
    rw [hy, ← cosineHeatValue_add_int_two (cosineCoeffs u₀) t m (x - 2 * m)]
    congr 1; ring
  have hyabs : |y| ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨abs_nonneg _, ?_⟩
    have hround : |x / 2 - (m : ℝ)| ≤ 1 / 2 := by rw [hm]; exact abs_sub_round (x / 2)
    rw [hy]
    have hb : |x - 2 * (m : ℝ)| ≤ 1 := by
      rw [show x - 2 * (m : ℝ) = 2 * (x / 2 - (m : ℝ)) from by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      nlinarith [hround]
    exact hb
  have hVy : unitIntervalCosineHeatValue t (cosineCoeffs u₀) y
      = unitIntervalCosineHeatValue t (cosineCoeffs u₀) |y| := by
    rcases abs_choice y with h | h
    · rw [h]
    · rw [h, cosineHeatValue_neg]
  rw [hVxy, hVy]
  exact cosineHeatValue_ge_floor_IccDom ht hu₀ hfloor hsum hyabs

/-! ### (F′) The `UniformFloor` from a `[0,1]`-only floor. -/

/-- **THE HEAT-FLOOR from a floor on `[0,1]` only.**  For the realized cosine datum
`u₀E = ⟨ofCosineCoeffs (cosineCoeffs u₀), _⟩` of a continuous source `u₀` whose values
on `[0,1]` are `≥ δ`, the heat element satisfies `UniformFloor (heatEWA u₀E) δ`. -/
theorem heatEWA_uniformFloor_Icc {u₀ : ℝ → ℝ} (hu₀ : Continuous u₀) {δ : ℝ}
    (hfloor : ∀ y ∈ Set.Icc (0 : ℝ) 1, δ ≤ u₀ y)
    (hsum : Summable (fun k => |cosineCoeffs u₀ k|))
    (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀))) :
    UniformFloor (heatEWA (T := T)
      (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)) δ := by
  intro τ x
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
    rw [heatEWA_evalST_eq_cosineHeatValue (cosineCoeffs u₀) hsum hmem τ x,
      Complex.ofReal_re]
    exact cosineHeatValue_ge_floor_Icc_all τ.2.1 hu₀ hfloor hsum x

/-! ### (G) Bridge to the faithfulness-fixed `PaperPositiveInitialDatum` floor.

The closed-domain floor carried by `PaperPositiveInitialDatum intervalDomain u₀p`
(`∃ η > 0, ∀ x : intervalDomain.Point, η ≤ u₀p x`, where the `Point` type is
`Subtype (Icc 0 1)`) is *exactly* the `[0,1]`-floor consumed by
`heatEWA_uniformFloor_Icc` once the datum is lifted to a real-space source by
`intervalDomainLift`.  The lift is `0` outside `[0,1]`, so it does NOT carry a
global real-line floor — which is precisely why the `[0,1]`-only strengthening
above is the right interface, and why obstruction (b) was a genuine gap before the
floor was made available. -/

/-- The lift of a `Point`-floored datum has the `[0,1]` real-floor.  If
`η ≤ u₀p x` for every `x : intervalDomainPoint`, then
`η ≤ intervalDomainLift u₀p y` for every `y ∈ Icc 0 1` (the lift is the datum
value there). -/
theorem intervalDomainLift_floor_Icc
    {u₀p : ShenWork.IntervalDomain.intervalDomainPoint → ℝ} {η : ℝ}
    (hfloor : ∀ x : ShenWork.IntervalDomain.intervalDomainPoint, η ≤ u₀p x)
    (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    η ≤ ShenWork.IntervalDomain.intervalDomainLift u₀p y := by
  rw [ShenWork.IntervalDomain.intervalDomainLift, dif_pos hy]
  exact hfloor ⟨y, hy⟩

/-- **The closed-domain floor of `PaperPositiveInitialDatum` discharges the EWA
heat-floor.**  For a `Point`-floored datum `u₀p` lifted to a continuous real-space
source `u₀` that agrees with the lift on `[0,1]` (the standard cosine-realization
source), the EWA heat element satisfies `UniformFloor (heatEWA u₀E) η`.

The continuity and Wiener-summability hypotheses `hu₀`, `hsum`, `hmem` are the
*remaining* obstruction (a): a merely continuous floored datum need not have an
absolutely-summable cosine spectrum.  This theorem isolates that obstruction (a)
is the SOLE residual datum-level input, the closed-domain floor (b) being now
fully consumed. -/
theorem paperFloorDatum_heatEWA_uniformFloor
    {u₀p : ShenWork.IntervalDomain.intervalDomainPoint → ℝ} {η : ℝ}
    (hPointFloor : ∀ x : ShenWork.IntervalDomain.intervalDomainPoint, η ≤ u₀p x)
    {u₀ : ℝ → ℝ} (hu₀ : Continuous u₀)
    (hagree : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ShenWork.IntervalDomain.intervalDomainLift u₀p y = u₀ y)
    (hsum : Summable (fun k => |cosineCoeffs u₀ k|))
    (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀))) :
    UniformFloor (heatEWA (T := T)
      (⟨ofCosineCoeffs (cosineCoeffs u₀), hmem⟩ : WA 1)) η := by
  refine heatEWA_uniformFloor_Icc hu₀ (fun y hy => ?_) hsum hmem
  rw [← hagree y hy]
  exact intervalDomainLift_floor_Icc hPointFloor y hy

end ShenWork.EWA

#print axioms ShenWork.EWA.intervalFullSemigroupOperator_ge_floor_Icc
#print axioms ShenWork.EWA.heatEWA_uniformFloor_Icc
#print axioms ShenWork.EWA.paperFloorDatum_heatEWA_uniformFloor
