/-
  ShenWork/Paper2/IntervalSourceBridgeOpen.lean

  SATISFIABLE (open / within-interval) source-bridge for the χ₀<0 leg.

  ## Why this file exists

  The landed closed-endpoint bridge in `IntervalChiNegFinalClose.lean`
  (`source_bridge_slice_of_divMode` / `divMode_of_sliceC1`) carries

    `hderiv : ∀ y ∈ uIcc 0 1, HasDerivAt (chemFluxLifted p (u s))
                (coupledChemDivSourceLift p u s y) y`,

  i.e. an *ambient* two-sided `HasDerivAt` on the CLOSED interval, INCLUDING the
  endpoints `x = 0` and `x = 1`.  This hypothesis is **FALSE** for the actual
  lifted flux: `chemFluxLifted` is built from `intervalDomainLift`, a
  zero-extension that is identically `0` off `[0,1]`.  A genuine two-sided
  `HasDerivAt` at `x = 1` (resp. `x = 0`) would force the right (resp. left)
  difference quotient — computed against the extension value `0` — to match the
  left (resp. right) difference quotient computed inside `[0,1]`; together with
  `chemFluxLifted _ 1 = 0` this pins the derivative there to the one of the
  constant-`0` extension, contradicting the generic interior chemDiv value.
  So no producer can ever discharge the closed `hderiv`; the bridge is blocked
  by an unsatisfiable hypothesis.

  ## The fix (this file)

  The divergence-mode IBP `∫₀¹ Q'·cos(kπx) = kπ·∫₀¹ Q·sin(kπx)` does **not**
  need the ambient endpoint derivative.  By the right-derivative FTC-2
  (`integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right`) it suffices that `Q` is

    * continuous on the CLOSED `[0,1]`            (`hQcont`), AND
    * right-differentiable on the OPEN `(0,1)`    (`hQderiv`, on `Ioi x`), AND
    * boundary-vanishing `Q 0 = Q 1 = 0`          (landed `..._endpoint_zero/one`),

  because then the IBP boundary term `[Q·cos]₀¹ = Q(1)cos(kπ) − Q(0) = 0`
  vanishes WITHOUT touching the endpoint derivative.  All three are satisfiable:
  the within-`(0,1)` derivative is exactly what `ContDiffOn ℝ 2` (the C²
  bootstrap output) gives via `ContDiffOn.differentiableOn ⟶
  DifferentiableWithinAt.hasDerivWithinAt`, and the endpoint vanishing is landed.

  We rebuild the raw IBP, the normalized `cosineCoeffs(∂Q)=√λ·sineCoeffs Q`, the
  `divMode` read-off, and the full per-slice bridge on these SATISFIABLE
  hypotheses, and show the bridge produces the SAME
  `unitIntervalCosineHeatValue (bFormSourceCoeffs ..)` identity.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file, new names only.
-/
import ShenWork.Paper2.IntervalChiNegFinalClose

noncomputable section

namespace ShenWork.Paper2.IntervalSourceBridgeOpen

open MeasureTheory intervalIntegral
open scoped Real
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.IntervalConjugateCosineSeries (intervalSineInner)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs coupledChemDivSourceLift
   chemFluxLifted_endpoint_zero chemFluxLifted_endpoint_one)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs)
open ShenWork.Paper2.HSigmaScale (lam)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_pos_eq_integral cosineCoeffs_zero_eq_integral)
open ShenWork.Paper2.IntervalDivergenceModeIdentity
  (sineCoeffs sineCoeffs_zero sineCoeffs_pos hasDerivAt_cos_kpi sqrt_lam_eq_kpi)

/-! ## Task 1 — the within-interval (open) raw IBP divergence-mode identity -/

/-- **The raw IBP divergence-mode identity, OPEN / within-interval form.**

`∫₀¹ Q'(x)·cos(kπx) = kπ·∫₀¹ Q(x)·sin(kπx)` for `Q` that is

* continuous on the CLOSED `[0,1]`  (`hQcont`),
* right-differentiable on the OPEN `(0,1)` with right-derivative `Q'`
  (`hQderiv` : `HasDerivWithinAt Q (Q' x) (Ioi x) x` for `x ∈ Ioo 0 1`),
* boundary-vanishing `Q 0 = Q 1 = 0`.

This replaces the FALSE ambient closed `HasDerivAt`-on-`uIcc 0 1` hypothesis of
`rawCosCoeff_deriv_eq_kpi_rawSinCoeff` with the SATISFIABLE within-`(0,1)` one,
using the right-derivative integration-by-parts FTC-2. -/
theorem rawCosCoeff_deriv_eq_kpi_rawSinCoeff_open
    {Q Q' : ℝ → ℝ} (k : ℕ)
    (hQcont : ContinuousOn Q (Set.Icc (0 : ℝ) 1))
    (hQderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivWithinAt Q (Q' x) (Set.Ioi x) x)
    (hQ'int : IntervalIntegrable Q' volume 0 1)
    (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0) :
    (∫ x in (0 : ℝ)..1, Q' x * Real.cos ((k : ℝ) * Real.pi * x))
      = (k : ℝ) * Real.pi *
          ∫ x in (0 : ℝ)..1, Q x * Real.sin ((k : ℝ) * Real.pi * x) := by
  -- `u = cos(kπ·)` (smooth), `u' = −kπ sin(kπ·)`; `v = Q`, `v' = Q'`.
  set u : ℝ → ℝ := fun y => Real.cos ((k : ℝ) * Real.pi * y) with hu_def
  set u' : ℝ → ℝ := fun y => -((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * y)
    with hu'_def
  have hzo : (0 : ℝ) ≤ 1 := by norm_num
  -- continuity of `u` on `[0,1]` and right-derivative of `u` on `(0,1)`.
  have hucont : ContinuousOn u (Set.Icc (0 : ℝ) 1) := by
    apply Continuous.continuousOn; fun_prop
  have huderiv : ∀ x ∈ Set.Ioo (min (0:ℝ) 1) (max (0:ℝ) 1),
      HasDerivWithinAt u (u' x) (Set.Ioi x) x := by
    intro x _; exact (hasDerivAt_cos_kpi k x).hasDerivWithinAt
  have hu'_int : IntervalIntegrable u' volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  -- recast hypotheses onto `[[0,1]]` / `Ioo (min 0 1) (max 0 1)`.
  have hucont' : ContinuousOn u (Set.uIcc (0 : ℝ) 1) := by
    rwa [Set.uIcc_of_le hzo]
  have hQcont' : ContinuousOn Q (Set.uIcc (0 : ℝ) 1) := by
    rwa [Set.uIcc_of_le hzo]
  have hQderiv' : ∀ x ∈ Set.Ioo (min (0:ℝ) 1) (max (0:ℝ) 1),
      HasDerivWithinAt Q (Q' x) (Set.Ioi x) x := by
    intro x hx
    rw [min_eq_left hzo, max_eq_right hzo] at hx
    exact hQderiv x hx
  -- IBP (right-derivative FTC-2): `∫ u·Q' = u 1·Q 1 − u 0·Q 0 − ∫ u'·Q`.
  have hibp := integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hucont' hQcont' huderiv hQderiv' hu'_int hQ'int
  rw [hQ0, hQ1] at hibp
  simp only [mul_zero, sub_zero, zero_sub] at hibp
  -- commute and read off, exactly as in the closed-version proof.
  have hcomm : (∫ x in (0 : ℝ)..1, Q' x * u x)
      = ∫ x in (0 : ℝ)..1, u x * Q' x := by
    refine intervalIntegral.integral_congr (fun x _ => ?_); ring
  rw [hcomm, hibp]
  rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [hu'_def]; ring

/-- **The normalized divergence-mode identity, OPEN / within-interval form.**

`cosineCoeffs Q' k = √(lam k)·sineCoeffs Q k`, with the SATISFIABLE within-`(0,1)`
right-derivative hypothesis (`hQderiv`) in place of the FALSE ambient closed
`HasDerivAt`-on-`uIcc 0 1` one. -/
theorem cosineCoeffs_deriv_eq_sqrtLambda_sineCoeff_open
    {Q Q' : ℝ → ℝ} (k : ℕ)
    (hQcont : ContinuousOn Q (Set.Icc (0 : ℝ) 1))
    (hQderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivWithinAt Q (Q' x) (Set.Ioi x) x)
    (hQ'cont : Continuous Q')
    (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0) :
    cosineCoeffs Q' k = Real.sqrt (lam k) * sineCoeffs Q k := by
  have hQ'int : IntervalIntegrable Q' volume 0 1 := hQ'cont.intervalIntegrable 0 1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`: LHS `= ∫₀¹ Q' = Q 1 − Q 0 = 0` via the right-derivative FTC-2.
    rw [cosineCoeffs_zero_eq_integral, sineCoeffs_zero, mul_zero]
    have hzo : (0 : ℝ) ≤ 1 := by norm_num
    have hint : (∫ x in (0 : ℝ)..1, Q' x) = Q 1 - Q 0 := by
      apply integral_eq_sub_of_hasDeriv_right_of_le hzo hQcont
      · intro x hx; exact hQderiv x hx
      · exact hQ'int
    rw [hint, hQ0, hQ1, sub_zero]
  · -- `k ≥ 1`: `cosineCoeffs Q' k = 2∫cos·Q' = 2·kπ·∫Q·sin = kπ·sineCoeffs Q k`.
    have hkne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
    rw [cosineCoeffs_pos_eq_integral hkne, sineCoeffs_pos hkne, sqrt_lam_eq_kpi]
    have hraw := rawCosCoeff_deriv_eq_kpi_rawSinCoeff_open k hQcont hQderiv hQ'int hQ0 hQ1
    have hcomm : (∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * Q' x)
        = ∫ x in (0 : ℝ)..1, Q' x * Real.cos ((k : ℝ) * Real.pi * x) := by
      refine intervalIntegral.integral_congr (fun x _ => ?_); ring
    have hsincomm : (∫ x in (0 : ℝ)..1, Q x * Real.sin ((k : ℝ) * Real.pi * x))
        = ∫ x in (0 : ℝ)..1, Real.sin ((k : ℝ) * Real.pi * x) * Q x := by
      refine intervalIntegral.integral_congr (fun x _ => ?_); ring
    rw [hcomm, hraw, hsincomm]; ring

/-! ## Bridge between `intervalSineInner` and `sineCoeffs` (definitional) -/

private theorem sineInner_eq_sineCoeffs (g : ℝ → ℝ) (n : ℕ) :
    intervalSineInner g n
      = ShenWork.Paper2.IntervalDivergenceModeIdentity.sineCoeffs g n := by
  unfold intervalSineInner ShenWork.Paper2.IntervalDivergenceModeIdentity.sineCoeffs
  rfl

/-! ## Task 1/2 — the divergence-mode identity from the OPEN flux data -/

/-- **The divergence-mode identity, discharged from the OPEN / within-interval
flux data (no FALSE ambient closed derivative).**

`nπ · intervalSineInner (chemFluxLifted p (u s)) n = coupledChemDivSourceCoeffs p u s n`

from:
* `hQcont` — continuity of the flux on the CLOSED `[0,1]`,
* `hQderiv` — the SATISFIABLE within-`(0,1)` right-derivative of the flux equal
  to `coupledChemDivSourceLift` (this is what `ContDiffOn ℝ 2` + the landed
  `deriv_chemFluxLifted_eq_chemDiv`-on-`Ioo` provide), and
* `hdivcont` — continuity of that divergence,
combined with the landed endpoint-vanishing `chemFluxLifted_endpoint_zero/one`.
NO carried ambient `HasDerivAt`-on-`uIcc 0 1` hypothesis. -/
theorem divMode_of_sliceC1_open
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s : ℝ}
    (hQcont : ContinuousOn (chemFluxLifted p (u s)) (Set.Icc (0 : ℝ) 1))
    (hQderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (chemFluxLifted p (u s))
        (coupledChemDivSourceLift p u s x) (Set.Ioi x) x)
    (hdivcont : Continuous (coupledChemDivSourceLift p u s))
    (n : ℕ) :
    ((n : ℝ) * Real.pi) * intervalSineInner (chemFluxLifted p (u s)) n
      = coupledChemDivSourceCoeffs p u s n := by
  have hQ0 : chemFluxLifted p (u s) 0 = 0 := chemFluxLifted_endpoint_zero p (u s)
  have hQ1 : chemFluxLifted p (u s) 1 = 0 := chemFluxLifted_endpoint_one p (u s)
  have hibp := cosineCoeffs_deriv_eq_sqrtLambda_sineCoeff_open
    (Q := chemFluxLifted p (u s)) (Q' := coupledChemDivSourceLift p u s) n
    hQcont hQderiv hdivcont hQ0 hQ1
  rw [coupledChemDivSourceCoeffs, hibp, sqrt_lam_eq_kpi, sineInner_eq_sineCoeffs]

/-! ## Task 2 — the SATISFIABLE per-slice source bridge -/

/-- **The per-slice source bridge from the OPEN / within-interval flux data.**

Identical conclusion to the closed-endpoint
`source_bridge_slice_of_sliceC1` —

  `(-χ₀)·conjKernel(chemFlux) + fullSemigroup(logistic)
     = unitIntervalCosineHeatValue r (bFormSourceCoeffs p u s) x` —

but the chemotaxis flux derivative hypothesis is the SATISFIABLE within-`(0,1)`
right-derivative `hQderiv` (what `ContDiffOn ℝ 2` gives), NOT the proven-FALSE
ambient `HasDerivAt`-on-`uIcc 0 1`.  We reuse the landed
`source_bridge_slice_of_divMode` after discharging its `hDivMode` via
`divMode_of_sliceC1_open`. -/
theorem source_bridge_slice_open
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {s : ℝ}
    (hchem_cont : Continuous (chemFluxLifted p (u s)))
    (hlog_cont : Continuous (logisticLifted p (u s)))
    {Mlog : ℝ}
    (hlog_bound : ∀ n, |cosineCoeffs (logisticLifted p (u s)) n| ≤ Mlog)
    {Mchem : ℝ}
    (hchem_bound : ∀ n, |coupledChemDivSourceCoeffs p u s n| ≤ Mchem)
    (hQderiv : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (chemFluxLifted p (u s))
        (coupledChemDivSourceLift p u s y) (Set.Ioi y) y)
    (hdivcont : Continuous (coupledChemDivSourceLift p u s)) :
    (-p.χ₀) * intervalConjugateKernelOperator r (chemFluxLifted p (u s)) x
        + intervalFullSemigroupOperator r (logisticLifted p (u s)) x
      = unitIntervalCosineHeatValue r (bFormSourceCoeffs p u s) x :=
  ShenWork.Paper2.IntervalChiNegFinalClose.source_bridge_slice_of_divMode
    hr hx hchem_cont hlog_cont hlog_bound hchem_bound
    (divMode_of_sliceC1_open hchem_cont.continuousOn hQderiv hdivcont)

/-! ## Task 3 — `ContDiffOn ℝ 2` discharges the within-interval derivative

The within-interval derivative hypothesis `hQderiv` of `source_bridge_slice_open`
is dischargeable from `ContDiffOn ℝ 2 Q (Icc 0 1)` (the C² bootstrap output): the
generic lemma below produces, at every interior point, a
`HasDerivWithinAt Q (derivWithin Q (Icc 0 1) x) (Ioi x) x`.  In the chemotaxis
application this `derivWithin` agrees with `coupledChemDivSourceLift` on `Ioo 0 1`
by the landed `deriv_chemFluxLifted_eq_chemDiv` (interior `deriv`-equality; on the
open interior the lift is genuinely differentiable so `derivWithin = deriv`).
Thus the source-bridge's derivative hypothesis is SATISFIABLE — the FALSE ambient
closed `HasDerivAt` is gone. -/
theorem hasDerivWithinAt_Ioi_of_contDiffOn
    {Q : ℝ → ℝ} (hQ : ContDiffOn ℝ 2 Q (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivWithinAt Q (derivWithin Q (Set.Icc (0 : ℝ) 1) x) (Set.Ioi x) x := by
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hdiff : DifferentiableWithinAt ℝ Q (Set.Icc (0 : ℝ) 1) x :=
    (hQ.differentiableOn (by norm_num)) x hxIcc
  have hbig : HasDerivWithinAt Q (derivWithin Q (Set.Icc (0 : ℝ) 1) x)
      (Set.Icc (0 : ℝ) 1) x := hdiff.hasDerivWithinAt
  -- `Icc 0 1 ∈ 𝓝[Ioi x] x`: the open `Ioo 0 1 ∋ x` sits inside `Icc 0 1`.
  refine hbig.mono_of_mem_nhdsWithin ?_
  have hIoo : Set.Ioo (0 : ℝ) 1 ∈ nhds x := IsOpen.mem_nhds isOpen_Ioo hx
  have hIooW : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin x (Set.Ioi x) :=
    nhdsWithin_le_nhds hIoo
  exact Filter.mem_of_superset hIooW Set.Ioo_subset_Icc_self

end ShenWork.Paper2.IntervalSourceBridgeOpen
