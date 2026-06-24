/-
  ShenWork/Wiener/EWA/SourceFluxSpatialReg.lean

  **χ₀<0 — closing the MECHANICAL secondary spatial-regularity atom
  `h_flux_diff` of the per-slice realized-source frontier.**

  `realSlice_reducedCore` / `realizes_clean` carry, per interior time `τ` and per
  interior point `x ∈ Ioo 0 1`, the real differentiability of the chemotaxis flux

      h_flux_diff : DifferentiableAt ℝ (chemFluxLifted p (realSlice u_star τ.1)) x,

  where (`IntervalGradientDuhamelMap.lean:47`)

      chemFluxLifted p w y
        = lift w y · resolverGradReal p w y / (1 + lift (R w) y)^β,   R w = resolver.

  This is MECHANICAL from the smooth composition on the OPEN interior `(0,1)` plus
  the banked `C²` data, by the SAME spine as `flux_contDiffOn_Ioo`
  (`IntervalDomainL2UEnergyCombine.lean:939`):

  * `lift w` is `C²` on the interior (`intervalDomainCosineSlice_contDiffOn_Ioo`,
    fed by the slab `hsumE`/`hrealizes`), hence `DifferentiableAt`;
  * `resolverGradReal p w` is differentiable EVERYWHERE
    (`resolverGradReal_hasDerivAt_of_sourceDecay`, fed the `SourceCoeffQuadraticDecay`
    from `realSlice_resolverDecay`);
  * `lift (R w)` is `C²` on the interior (`vSpatialInterior`-style, from
    `resolverR_summability` + `lift_resolver_eqOn_Icc`), so it is `DifferentiableAt`,
    and `1 + lift (R w) > 0` (`realSlice_resolverPos`), so `(1 + lift (R w))^β`
    is `DifferentiableAt` (`Real.rpow_natCast`-free `HasDerivAt.rpow_const` on the
    positive branch);
  * the quotient `DifferentiableAt.div` then closes it.

  The core lemma `chemFluxLifted_differentiableAt_of_decay` takes the BANKED
  per-slice `SourceCoeffQuadraticDecay` and positivity as inputs; the wired form
  `realSlice_h_flux_diff` discharges those from the standing heat-floor / slab atoms
  exactly as `realSlice_resolverDecay` / `realSlice_resolverPos` do, yielding the
  carried-hyp shape directly.

  The companion atom `h_src_cont_chem` (`Continuous (wChem …)` on the CLOSED
  subtype) is NOT mechanical: `wChem ⟨x,_⟩ = deriv F (x.1)` with `F` built from the
  zero-extended lift, so at the endpoints `deriv F` sees the zero-extension jump and
  the closed-subtype continuity requires genuine boundary-matching of the physical
  second derivative (the substantive "Gap 1" frontier).  It is left to the deep
  layer; only the mechanical `h_flux_diff` is closed here.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceResolverSpectralDischarge
import ShenWork.Wiener.EWA.SourceRealizesRecords
import ShenWork.Paper2.IntervalDomainL2UEnergyCombine

noncomputable section

namespace ShenWork.EWA

open Set Filter Topology
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.PDE (intervalNeumannResolverR intervalNeumannResolverCoeff)
open ShenWork.Paper2
  (resolverGradReal resolverGradReal_hasDerivAt_of_sourceDecay SourceCoeffQuadraticDecay)
open ShenWork.IntervalResolverSpatialC2 (resolverR_summability)
open ShenWork.IntervalCosineSliceRegularity (intervalDomainCosineSlice_contDiffOn_Ioo)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)

variable {T : ℝ}

/-! ### Interior `C²` of the resolver lift, from the banked source decay. -/

/-- On the OPEN interior the resolver lift agrees with its cosine-coefficient series.
A local copy of the `Icc` agreement, used to transport the cosine-slice engine. -/
private theorem liftResolver_eqOn_Icc (p : CM2Params) (u : intervalDomainPoint → ℝ) :
    Set.EqOn (intervalDomainLift (intervalNeumannResolverR p u))
      (fun x : ℝ => ∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re * cosineMode k x)
      (Set.Icc (0 : ℝ) 1) := by
  intro x hxIcc
  simp only [intervalDomainLift, dif_pos hxIcc,
    ShenWork.IntervalResolverGradientBridge.resolverR_apply_eq, cosineMode]

/-- The resolver lift `lift (R w)` is `C²` on the open interior `(0,1)`, from the
`SourceCoeffQuadraticDecay` of `w` (cosine-slice engine fed by `resolverR_summability`
and the interior-blind agreement). -/
private theorem liftResolver_contDiffOn_Ioo {p : CM2Params} {w : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p w) :
    ContDiffOn ℝ 2 (intervalDomainLift (intervalNeumannResolverR p w)) (Set.Ioo (0 : ℝ) 1) :=
  intervalDomainCosineSlice_contDiffOn_Ioo (resolverR_summability hdecay)
    (liftResolver_eqOn_Icc p w)

/-! ### The mechanical flux differentiability, from banked source decay + positivity. -/

/-- **Core: `chemFluxLifted p w` is `DifferentiableAt` every interior point**, from the
banked per-slice `SourceCoeffQuadraticDecay` of `w` and the strict positivity of the
resolver value `R w` on the interval.  All three factors are smooth on `(0,1)`:
`lift w` (slab `C²`), `resolverGradReal p w` (globally `C¹`), and `(1 + lift (R w))^β`
(`rpow` on the positive base). -/
theorem chemFluxLifted_differentiableAt_of_decay
    {p : CM2Params} {w : intervalDomainPoint → ℝ} {b : ℕ → ℝ}
    (hsumE : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|))
    (hwagree : Set.EqOn (intervalDomainLift w)
      (fun x => ∑' n, b n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1))
    (hdecay : SourceCoeffQuadraticDecay p w)
    (hvpos : ∀ x : intervalDomainPoint, 0 < intervalNeumannResolverR p w x)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (chemFluxLifted p w) x := by
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  have hnhds : Set.Ioo (0 : ℝ) 1 ∈ nhds x := isOpen_Ioo.mem_nhds hx
  -- `lift w` is `C²` on the interior, hence `DifferentiableAt`.
  have hCu : ContDiffOn ℝ 2 (intervalDomainLift w) (Set.Ioo (0 : ℝ) 1) :=
    intervalDomainCosineSlice_contDiffOn_Ioo hsumE hwagree
  have hdu : DifferentiableAt ℝ (intervalDomainLift w) x :=
    (hCu.differentiableOn (by norm_num)).differentiableAt hnhds
  -- `resolverGradReal p w` is differentiable everywhere.
  have hdg : DifferentiableAt ℝ (fun y : ℝ => resolverGradReal p w y) x :=
    (resolverGradReal_hasDerivAt_of_sourceDecay hdecay x).differentiableAt
  -- `lift (R w)` is `C²` on the interior, hence `DifferentiableAt`.
  have hCv : ContDiffOn ℝ 2 (intervalDomainLift (intervalNeumannResolverR p w))
      (Set.Ioo (0 : ℝ) 1) := liftResolver_contDiffOn_Ioo hdecay
  have hdv : DifferentiableAt ℝ (intervalDomainLift (intervalNeumannResolverR p w)) x :=
    (hCv.differentiableOn (by norm_num)).differentiableAt hnhds
  -- the base `1 + lift (R w) x` is positive at `x`.
  have hbase_pos : (0 : ℝ) < 1 + intervalDomainLift (intervalNeumannResolverR p w) x := by
    have hvx : (0 : ℝ) < intervalNeumannResolverR p w ⟨x, hxIcc⟩ := hvpos ⟨x, hxIcc⟩
    have hlift_eq : intervalDomainLift (intervalNeumannResolverR p w) x
        = intervalNeumannResolverR p w ⟨x, hxIcc⟩ := by
      simp only [intervalDomainLift, dif_pos hxIcc]
    rw [hlift_eq]; linarith
  -- the base function `1 + lift (R w)` is `DifferentiableAt`.
  have hdbase : DifferentiableAt ℝ
      (fun y : ℝ => 1 + intervalDomainLift (intervalNeumannResolverR p w) y) x :=
    (differentiableAt_const _).add hdv
  -- `(1 + lift (R w))^β` is `DifferentiableAt` (rpow on the positive base).
  have hdpow : DifferentiableAt ℝ
      (fun y : ℝ => (1 + intervalDomainLift (intervalNeumannResolverR p w) y) ^ p.β) x :=
    hdbase.rpow_const (Or.inl (ne_of_gt hbase_pos))
  -- the numerator `lift w · resolverGradReal p w` is `DifferentiableAt`.
  have hnum : DifferentiableAt ℝ
      (fun y : ℝ => intervalDomainLift w y * resolverGradReal p w y) x := hdu.mul hdg
  -- denominator nonzero.
  have hden_ne : ((1 + intervalDomainLift (intervalNeumannResolverR p w) x) ^ p.β) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hbase_pos _)
  -- assemble the quotient.
  have hquot : DifferentiableAt ℝ
      (fun y : ℝ => intervalDomainLift w y * resolverGradReal p w y /
        (1 + intervalDomainLift (intervalNeumannResolverR p w) y) ^ p.β) x :=
    hnum.div hdpow hden_ne
  -- `chemFluxLifted p w` is definitionally that quotient.
  exact hquot

/-! ### Wired form: `h_flux_diff` from the standing heat-floor / slab atoms. -/

/-- **`h_flux_diff` DISCHARGED (per interior time and point).**  For every interior
`t ∈ Ioo 0 T` and every interior `x ∈ Ioo 0 1`, the chemotaxis flux
`chemFluxLifted p (realSlice u_star t)` is real-differentiable at `x`.  The
`SourceCoeffQuadraticDecay` is supplied by `realSlice_resolverDecay`, the slab `C²`
data by `hsumE`/`hrealizes`, and the resolver positivity by `realSlice_resolverPos`;
all inputs are the standing heat-floor / slab atoms the reduced core already carries. -/
theorem realSlice_h_flux_diff
    (p : CM2Params) (u_star : EWA T 1) (u₀cos : ℕ → ℝ)
    {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    (hsumE : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|))
    (hrealizes : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
    (huNE0 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (realSlice u_star t) 0 ≠ 0)
    (huNE1 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (realSlice u_star t) 1 ≠ 0)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (chemFluxLifted p (realSlice u_star t)) x := by
  -- banked per-slice source decay and resolver positivity.
  have hdecay : SourceCoeffQuadraticDecay p (realSlice u_star t) :=
    realSlice_resolverDecay p u_star u₀cos hδρ hheat hu_ball hsumE hrealizes huNE0 huNE1 t ht
  have hvpos : ∀ y : intervalDomainPoint,
      0 < intervalNeumannResolverR p (realSlice u_star t) y := by
    intro y
    have := realSlice_resolverPos p u_star u₀cos hδρ hheat hu_ball hsumE hrealizes t ht y
    -- `mildChemicalConcentration p (realSlice u_star) t = intervalNeumannResolverR …` (defeq).
    exact this
  -- the slab `C²` data, with the χ₀<0 value-field coefficients as the `b` sequence.
  have hagree : Set.EqOn (intervalDomainLift (realSlice u_star t))
      (fun y => ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n y)
      (Set.Icc (0 : ℝ) 1) := fun y hy => hrealizes t ht y hy
  exact chemFluxLifted_differentiableAt_of_decay (b := fun n =>
    fullSourceCoeff p (realSlice u_star) u₀cos t n) (hsumE t ht) hagree hdecay hvpos hx

end ShenWork.EWA

#print axioms ShenWork.EWA.chemFluxLifted_differentiableAt_of_decay
#print axioms ShenWork.EWA.realSlice_h_flux_diff
