/-
  # `ShenWork.Paper2.ChemMildC1etaUncond`

  **P2-T11 step (ii) — the UNCONDITIONAL `[0,1]` slice + Wiener feed.**

  The committed assembly `ChemMildC1etaAssembly` chains the mild slice through the
  GLOBAL-`ℝ` `holderCosineCoeff_summable`, which forces a global `Differentiable ℝ w`
  representation and a Neumann boundary package.  Here we run the *unconditional*
  `DifferentiableOn (Set.Icc 0 1)` route instead:

    * the chemotaxis leg `chemLitLeg t₀ Q` is differentiable on `[0,1]` with
      `derivWithin = chemLitLeg₂` (committed step 1, `chemLeg_differentiableOn_Icc` /
      `chemLeg_derivWithin_eq_Icc`), and globally continuous (`chemLitLeg_continuousAt`);
    * the value legs `initLeg`, `reactLeg` are globally smooth (committed gradient route
      `gradLeg_holder_global`), so `DifferentiableOn ℝ · (Icc 0 1)` and their
      `derivWithin = deriv` come for free, with global `η`-Hölder derivatives;
    * the differentiated `[0,1]` representative `w = initLeg − χ₀·chemLitLeg + reactLeg`
      is therefore `DifferentiableOn ℝ · (Icc 0 1)`, its `derivWithin` on `[0,1]` is the
      three-leg sum, and is `η`-Hölder on `[0,1]` by the triangle inequality;
    * feeding this plus the endpoint no-flux package into the committed
      `holderCosineCoeff_summable_diffOn` yields `Summable |cosineCoeffs w n|`.

  **NO global-`ℝ` differentiability** of `w`; the Wiener feed still carries the honest
  closed-interval endpoint no-flux package for `derivWithin w` on `[0,1]`.
  **NO off-interior residual** (the interchange is the committed interior one extended to
  the endpoints, step 1), **NO global-`ℝ` differentiability** of `w` (only on `[0,1]`).

  The only carried datum is the differentiated mild REPRESENTATION on `[0,1]`
  (`w = initLeg − χ₀·chemLitLeg + reactLeg`, the `∂ₓ ∫ = ∫ ∂ₓ` identity) and the per-leg
  `η`-Hölder moduli — exactly the bridge data of the committed `DifferentiatedMildSlice`,
  NOT a regularity conclusion.

  No proof placeholders, native-decision shortcuts, or custom axiomatic declarations.
-/
import ShenWork.Paper2.ChemMildDifferentiableOn
import ShenWork.Paper2.ChemMildC1etaAssembly
import ShenWork.Paper2.IntervalChemFluxHolderSourceDecay
import ShenWork.Paper2.IntervalMildToLocalExistence
import ShenWork.Wiener.EWA.HolderCosineDecayDiffOn

open MeasureTheory Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalDomainRegularityBootstrap (unitIntervalCosineHeatSecondValue)

namespace ShenWork.Paper2

noncomputable section

/-! ## The literal=spectral chemotaxis bridge on `[0,1]`

The literal second-order leg `chemLitLeg₂ t₀ Q` (a time integral of the LITERAL second
spatial derivative `∂ₓₓS(t₀−s)Q(s)`) equals the spectral clamped Duhamel leg
`chemDuhamelLeg t₀ Q` (a time integral of `unitIntervalCosineHeatSecondValue (t₀−s) ⟨Q s⟩
(clamp01 ·)`) at every `x ∈ [0,1]`.  Pointwise (for `s ∈ (0,t₀)`) this is the committed Icc
pinning `intervalFullSemigroupOperator_secondDeriv_eq_secondValue_Icc`; we integrate it over
`s` a.e. on `(0,t₀)` and absorb `clamp01 x = x`.  This is what discharges `chem_holder` from
the committed spectral `chemLeg_holder_of_brick4`. -/
theorem chemLitLeg₂_eq_chemDuhamelLeg_Icc {t₀ θ CQ HQ M : ℝ} {Q : ℝ → ℝ → ℝ}
    (hd : ChemLegData t₀ θ CQ HQ M Q) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    chemLitLeg₂ t₀ Q x = chemDuhamelLeg t₀ Q x := by
  have ht₀ : 0 < t₀ := hd.ht₀
  -- `clamp01 x = x` on `[0,1]`, then the two integrands agree a.e. on `(0,t₀)`.
  have hclamp : clamp01 x = x := clamp01_eq_self hx
  unfold chemLitLeg₂ chemDuhamelLeg
  simp only [hclamp]
  refine intervalIntegral.integral_congr_ae ?_
  -- goal: a.e.-`volume` `s`, `s ∈ uIoc 0 t₀ → integrands agree`.  On `uIoc = Ioc` we have
  -- `0 < s`; a.e.-`volume` `s ≠ t₀` gives `s < t₀`, so `s ∈ Ioo 0 t₀`.
  have huIoc_eq : Set.uIoc (0:ℝ) t₀ = Set.Ioc (0:ℝ) t₀ := Set.uIoc_of_le ht₀.le
  have hae_ne_t : ∀ᵐ s ∂volume, s ≠ t₀ := by
    have heq : {s : ℝ | ¬ s ≠ t₀} = {t₀} := by ext s; simp [eq_comm]
    rw [MeasureTheory.ae_iff, heq]; exact Real.volume_singleton
  filter_upwards [hae_ne_t] with s hsne hs_mem
  rw [huIoc_eq] at hs_mem
  have hsIoo : s ∈ Set.Ioo (0:ℝ) t₀ := ⟨hs_mem.1, lt_of_le_of_ne hs_mem.2 hsne⟩
  have hσ : (0:ℝ) < t₀ - s := sub_pos.mpr hsIoo.2
  -- the committed Icc pinning at the fixed `x`, with `σ = t₀−s`, `h = Q s`.
  exact intervalFullSemigroupOperator_secondDeriv_eq_secondValue_Icc hσ
    (hd.hQcont s hsIoo) (hd.hQcoeff s hsIoo) hx

/-- The literal second-derivative chemotaxis-leg time integrand is interval-integrable
at every closed-interval point. -/
theorem chemLegData_literal_secondDeriv_intervalIntegrable
    {t₀ θ CQ HQ M : ℝ} {Q : ℝ → ℝ → ℝ}
    (hd : ChemLegData t₀ θ CQ HQ M Q) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable
      (fun s : ℝ => deriv (fun z : ℝ => deriv
        (fun w : ℝ =>
          ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
            (t₀ - s) (Q s) w) z) x)
      volume 0 t₀ := by
  have hQ_ae : AEStronglyMeasurable (Function.uncurry Q)
      ((volume.restrict (Set.uIoc (0:ℝ) t₀)).prod
        (ShenWork.IntervalDomain.intervalMeasure 1)) :=
    hd.hQmeas.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => deriv (fun z : ℝ => deriv
        (fun w : ℝ =>
          ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
            (t₀ - s) (Q s) w) z) x)
      (volume.restrict (Set.uIoc (0:ℝ) t₀)) :=
    intervalFullSemigroupOperator_s_dependent_secondDeriv_aestronglyMeasurable_x₀
      hd.ht₀ hQ_ae hd.hQint hd.hQbdd x
  set bound : ℝ → ℝ := fun s =>
    ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst θ
      * (t₀ - s) ^ (-1 + θ / 2 : ℝ) * HQ with hbound_def
  have hbound_int : IntervalIntegrable bound volume 0 t₀ := by
    have h0 :=
      ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := t₀) hd.hθ0
    have h1 := (h0.const_mul
      (ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst θ)).mul_const HQ
    exact h1.congr (fun s _ => by rw [hbound_def])
  have huIoc_eq : Set.uIoc (0:ℝ) t₀ = Set.Ioc (0:ℝ) t₀ :=
    Set.uIoc_of_le hd.ht₀.le
  have hae_ne_t : ∀ᵐ s ∂volume, s ≠ t₀ := by
    have heq : {s : ℝ | ¬ s ≠ t₀} = {t₀} := by ext s; simp [eq_comm]
    rw [ae_iff, heq]
    exact Real.volume_singleton
  refine IntervalIntegrable.mono_fun'
    (f := fun s : ℝ => deriv (fun z : ℝ => deriv
      (fun w : ℝ =>
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
          (t₀ - s) (Q s) w) z) x)
    (g := bound) hbound_int hmeas ?_
  refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
  filter_upwards [hae_ne_t] with s hsne hs
  rw [huIoc_eq] at hs
  have hsIoo : s ∈ Set.Ioo (0:ℝ) t₀ := ⟨hs.1, lt_of_le_of_ne hs.2 hsne⟩
  have hts : 0 < t₀ - s := sub_pos.mpr hsIoo.2
  have hQ_ae_meas : AEStronglyMeasurable (Q s)
      (ShenWork.IntervalDomain.intervalMeasure 1) :=
    (hd.hQint s).aestronglyMeasurable
  have hbrick := ShenWork.IntervalNeumannFullKernel.neumannHeatSecondDeriv_Ctheta_to_Linfty
    hts hd.hθ0 hd.hθ1 hQ_ae_meas (hd.hQbdd s) hd.hHQ_nn
    (hd.hQholder s hsIoo) hx
  rw [Real.norm_eq_abs, hbound_def]
  exact hbrick

/-- The spectral second-value chemotaxis-leg time integrand is interval-integrable.
This discharges the former `hleg_int` input used by the C1/η chemotaxis-leg bridge. -/
theorem chemLegData_unitIntervalCosineHeatSecondValue_intervalIntegrable
    {t₀ θ CQ HQ M : ℝ} {Q : ℝ → ℝ → ℝ}
    (hd : ChemLegData t₀ θ CQ HQ M Q) (x : ℝ) :
    IntervalIntegrable
      (fun s : ℝ => unitIntervalCosineHeatSecondValue (t₀ - s)
        (cosineCoeffs (Q s)) (clamp01 x))
      volume 0 t₀ := by
  have hLit :=
    chemLegData_literal_secondDeriv_intervalIntegrable (hd := hd) (x := clamp01 x)
      (clamp01_mem x)
  have huIoc_eq : Set.uIoc (0:ℝ) t₀ = Set.Ioc (0:ℝ) t₀ :=
    Set.uIoc_of_le hd.ht₀.le
  have hae_ne_t : ∀ᵐ s ∂volume, s ≠ t₀ := by
    have heq : {s : ℝ | ¬ s ≠ t₀} = {t₀} := by ext s; simp [eq_comm]
    rw [ae_iff, heq]
    exact Real.volume_singleton
  refine hLit.congr_ae ?_
  refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
  filter_upwards [hae_ne_t] with s hsne hs
  rw [huIoc_eq] at hs
  have hsIoo : s ∈ Set.Ioo (0:ℝ) t₀ := ⟨hs.1, lt_of_le_of_ne hs.2 hsne⟩
  have hσ : (0:ℝ) < t₀ - s := sub_pos.mpr hsIoo.2
  exact intervalFullSemigroupOperator_secondDeriv_eq_secondValue_Icc hσ
    (hd.hQcont s hsIoo) (hd.hQcoeff s hsIoo) (clamp01_mem x)

/-- **`DifferentiatedMildSliceDiffOn` — the unconditional `[0,1]` bridge package.**

The differentiated mild slice `w = u(t₀,·)` over `[0,1]`, recorded as the honest
representation data plus the per-leg `η`-Hölder moduli, in the `DifferentiableOn`/
`derivWithin` route (NO global differentiability; endpoint no-flux is not built into
this bridge package):

* `w_split` — the `[0,1]` representative `w x = initLeg x − χ₀·chemLitLeg t₀ Q x + reactLeg x`
  (the differentiated mild representation; legs defined on all of `ℝ`);
* `chemData` — the committed step-1 bundle giving `chemLitLeg` differentiable on `[0,1]`
  with `derivWithin = chemLitLeg₂`;
* `init_diff` / `react_diff` — the value legs are globally differentiable (committed
  gradient route), hence `DifferentiableOn ℝ · (Icc 0 1)` and `derivWithin = deriv`;
* `init_holder` / `chem_holder` / `react_holder` — the per-leg `η`-Hölder of the
  `[0,1]` derivatives, `[0,1]`-local (the value legs are even global).
This bridge package does not carry endpoint no-flux; the Wiener feed takes that separately. -/
structure DifferentiatedMildSliceDiffOn (χ₀ t₀ θ η CQ HQ M : ℝ) (Q : ℝ → ℝ → ℝ)
    (w initLeg reactLeg : ℝ → ℝ) (Ainit Achem Areact : ℝ) : Prop where
  /-- The `[0,1]` differentiated representative (legs on all of `ℝ`). -/
  w_split : ∀ x : ℝ, w x = initLeg x - χ₀ * chemLitLeg t₀ Q x + reactLeg x
  /-- The committed step-1 chemotaxis-leg `[0,1]` differentiability bundle. -/
  chemData : ChemLegData t₀ θ CQ HQ M Q
  /-- Initial value leg: globally differentiable (committed gradient smoothing). -/
  init_diff : Differentiable ℝ initLeg
  /-- Reaction value leg: globally differentiable (committed gradient smoothing). -/
  react_diff : Differentiable ℝ reactLeg
  /-- Nonneg leg constants (non-vacuity). -/
  Ainit_nn : 0 ≤ Ainit
  Achem_nn : 0 ≤ Achem
  Areact_nn : 0 ≤ Areact
  /-- Initial-leg derivative `η`-Hölder on `[0,1]` (`deriv initLeg`, global value leg). -/
  init_holder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
    |deriv initLeg x - deriv initLeg y| ≤ Ainit * |x - y| ^ η
  /-- Chemotaxis-leg derivative `η`-Hölder on `[0,1]` (`chemLitLeg₂ = derivWithin chemLitLeg`).
  This field is NO LONGER carried as a free hypothesis: the canonical constructor
  `differentiatedMildSliceDiffOn_of_brick4_chem` DISCHARGES it via the literal=spectral
  bridge `chemLitLeg₂_eq_chemDuhamelLeg_Icc` + the committed spectral
  `chemLeg_holder_of_brick4`.  It stays a structure field only so the downstream
  consumers (`differentiatedMildSliceDiffOn_derivWithin`, the slice theorem) read it
  uniformly — every inhabitant produced by the constructor has it PROVED, not assumed. -/
  chem_holder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
    |chemLitLeg₂ t₀ Q x - chemLitLeg₂ t₀ Q y| ≤ Achem * |x - y| ^ η
  /-- Reaction-leg derivative `η`-Hölder on `[0,1]` (`deriv reactLeg`, global value leg). -/
  react_holder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
    |deriv reactLeg x - deriv reactLeg y| ≤ Areact * |x - y| ^ η

/-- **`differentiatedMildSliceDiffOn_of_brick4_chem` — the constructor that PROVES
`chem_holder`.**

Where the bare `DifferentiatedMildSliceDiffOn` would CARRY `chem_holder` as a free field
(the assume-the-conclusion anti-pattern), this constructor DISCHARGES it.  The chemotaxis
derivative `chemLitLeg₂ t₀ Q` equals the spectral clamped Duhamel leg `chemDuhamelLeg t₀ Q`
on `[0,1]` (the literal=spectral bridge `chemLitLeg₂_eq_chemDuhamelLeg_Icc`), and the
spectral `η`-Hölder with constant `chemDuhamelConst t₀ θ η HQ` is PROVED by the committed
`chemLeg_holder_of_brick4` (bricks 1–4 + integral-Minkowski over `[0,t₀]`).

The remaining inputs are exactly the honest bridge data, NO regularity conclusion:
* `w_split` — the differentiated mild REPRESENTATION on `[0,1]`;
* `chemData` — the committed step-1 chemotaxis differentiability bundle;
* `init_diff`/`react_diff` + `init_holder`/`react_holder` — the GROUNDED value legs
  (realizable from the committed global gradient route `gradLeg_holder_global`).
`chem_holder` is NO LONGER assumed. -/
theorem differentiatedMildSliceDiffOn_of_brick4_chem
    {χ₀ t₀ θ η CQ HQ M Ainit Areact : ℝ} {Q : ℝ → ℝ → ℝ}
    {w initLeg reactLeg : ℝ → ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hθη : η < θ)
    (chemData : ChemLegData t₀ θ CQ HQ M Q)
    (init_diff : Differentiable ℝ initLeg) (react_diff : Differentiable ℝ reactLeg)
    (hAinit_nn : 0 ≤ Ainit) (hAreact_nn : 0 ≤ Areact)
    (w_split : ∀ x : ℝ, w x = initLeg x - χ₀ * chemLitLeg t₀ Q x + reactLeg x)
    (init_holder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv initLeg x - deriv initLeg y| ≤ Ainit * |x - y| ^ η)
    (react_holder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv reactLeg x - deriv reactLeg y| ≤ Areact * |x - y| ^ η) :
    DifferentiatedMildSliceDiffOn χ₀ t₀ θ η CQ HQ M Q w initLeg reactLeg
      Ainit (chemDuhamelConst t₀ θ η HQ) Areact := by
  have ht₀ := chemData.ht₀; have hθ0 := chemData.hθ0; have hθ1 := chemData.hθ1
  have hHQ_nn := chemData.hHQ_nn
  have hleg_int : ∀ x : ℝ, IntervalIntegrable
      (fun s => unitIntervalCosineHeatSecondValue (t₀ - s) (cosineCoeffs (Q s)) (clamp01 x))
      volume 0 t₀ :=
    fun x => chemLegData_unitIntervalCosineHeatSecondValue_intervalIntegrable chemData x
  -- the chemotaxis Hölder constant is nonneg (integral of a nonneg integrand on `[0,t₀]`).
  have hAchem_nn : 0 ≤ chemDuhamelConst t₀ θ η HQ := by
    unfold chemDuhamelConst
    refine intervalIntegral.integral_nonneg ht₀.le (fun s hs => ?_)
    have hts : (0:ℝ) ≤ t₀ - s := by have := hs.2; linarith
    have hb := brick4Const_nonneg θ η
    have hr : (0:ℝ) ≤ (t₀ - s) ^ (-1 + (θ - η) / 2 : ℝ) := Real.rpow_nonneg hts _
    positivity
  -- DISCHARGE `chem_holder`: bridge `chemLitLeg₂ = chemDuhamelLeg` on `[0,1]`, then brick 4.
  have hChem : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |chemLitLeg₂ t₀ Q x - chemLitLeg₂ t₀ Q y|
        ≤ chemDuhamelConst t₀ θ η HQ * |x - y| ^ η := by
    intro x hx y hy
    rw [chemLitLeg₂_eq_chemDuhamelLeg_Icc chemData hx,
      chemLitLeg₂_eq_chemDuhamelLeg_Icc chemData hy]
    have h := chemLeg_holder_of_brick4 ht₀ hθ0 hθ1 hη0 hη1 hθη hHQ_nn
      chemData.hQcont chemData.hQcoeff
      (fun s hs y => chemData.hQbdd s y) chemData.hQholder x y (hleg_int x) (hleg_int y)
    simpa only [chemDuhamelLeg, chemDuhamelConst] using h
  exact
    { w_split := w_split
      chemData := chemData
      init_diff := init_diff
      react_diff := react_diff
      Ainit_nn := hAinit_nn
      Achem_nn := hAchem_nn
      Areact_nn := hAreact_nn
      init_holder := init_holder
      chem_holder := hChem
      react_holder := react_holder }

/-- The differentiated `[0,1]` representative is continuous on all of `ℝ` (each leg is:
the value legs are differentiable, the chemotaxis leg is globally continuous). -/
theorem differentiatedMildSliceDiffOn_continuous {χ₀ t₀ θ η CQ HQ M : ℝ} {Q : ℝ → ℝ → ℝ}
    {w initLeg reactLeg : ℝ → ℝ} {Ainit Achem Areact : ℝ}
    (D : DifferentiatedMildSliceDiffOn χ₀ t₀ θ η CQ HQ M Q w initLeg reactLeg
      Ainit Achem Areact) :
    Continuous w := by
  have hchem : Continuous (chemLitLeg t₀ Q) :=
    continuous_iff_continuousAt.mpr (fun z =>
      chemLitLeg_continuousAt D.chemData.ht₀ D.chemData.hQmeas D.chemData.hQint
        D.chemData.hQbdd D.chemData.hQcont D.chemData.hQcoeff z)
  have hsum : Continuous
      (fun x => initLeg x - χ₀ * chemLitLeg t₀ Q x + reactLeg x) :=
    ((D.init_diff.continuous.sub (continuous_const.mul hchem)).add D.react_diff.continuous)
  exact hsum.congr (fun x => (D.w_split x).symm)

/-- The differentiated `[0,1]` representative is differentiable on `[0,1]`: the value legs
are globally differentiable, the chemotaxis leg by committed step 1. -/
theorem differentiatedMildSliceDiffOn_differentiableOn {χ₀ t₀ θ η CQ HQ M : ℝ}
    {Q : ℝ → ℝ → ℝ} {w initLeg reactLeg : ℝ → ℝ} {Ainit Achem Areact : ℝ}
    (D : DifferentiatedMildSliceDiffOn χ₀ t₀ θ η CQ HQ M Q w initLeg reactLeg
      Ainit Achem Areact) :
    DifferentiableOn ℝ w (Set.Icc (0:ℝ) 1) := by
  have hchem : DifferentiableOn ℝ (chemLitLeg t₀ Q) (Set.Icc (0:ℝ) 1) :=
    chemLeg_differentiableOn_Icc D.chemData
  have hinit : DifferentiableOn ℝ initLeg (Set.Icc (0:ℝ) 1) := D.init_diff.differentiableOn
  have hreact : DifferentiableOn ℝ reactLeg (Set.Icc (0:ℝ) 1) := D.react_diff.differentiableOn
  have hsum : DifferentiableOn ℝ
      (fun x => initLeg x - χ₀ * chemLitLeg t₀ Q x + reactLeg x) (Set.Icc (0:ℝ) 1) :=
    ((hinit.sub ((differentiableOn_const χ₀).mul hchem)).add hreact)
  exact hsum.congr (fun x _ => D.w_split x)

/-- On `[0,1]`, `derivWithin w (Icc 0 1)` is the three-leg sum
`deriv initLeg − χ₀·chemLitLeg₂ + deriv reactLeg`. -/
theorem differentiatedMildSliceDiffOn_derivWithin {χ₀ t₀ θ η CQ HQ M : ℝ}
    {Q : ℝ → ℝ → ℝ} {w initLeg reactLeg : ℝ → ℝ} {Ainit Achem Areact : ℝ}
    (D : DifferentiatedMildSliceDiffOn χ₀ t₀ θ η CQ HQ M Q w initLeg reactLeg
      Ainit Achem Areact)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    derivWithin w (Set.Icc (0:ℝ) 1) x =
      deriv initLeg x - χ₀ * chemLitLeg₂ t₀ Q x + deriv reactLeg x := by
  have huniq : UniqueDiffWithinAt ℝ (Set.Icc (0:ℝ) 1) x :=
    (uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1)) x hx
  -- `HasDerivWithinAt` of each leg at `x` within `[0,1]`.
  have hinit : HasDerivWithinAt initLeg (deriv initLeg x) (Set.Icc (0:ℝ) 1) x :=
    (D.init_diff x).hasDerivAt.hasDerivWithinAt
  have hreact : HasDerivWithinAt reactLeg (deriv reactLeg x) (Set.Icc (0:ℝ) 1) x :=
    (D.react_diff x).hasDerivAt.hasDerivWithinAt
  have hchem : HasDerivWithinAt (chemLitLeg t₀ Q) (chemLitLeg₂ t₀ Q x) (Set.Icc (0:ℝ) 1) x :=
    chemLeg_hasDerivWithinAt_Icc D.chemData hx
  -- the sum has the stated derivative.
  have hsum : HasDerivWithinAt
      (fun z => initLeg z - χ₀ * chemLitLeg t₀ Q z + reactLeg z)
      (deriv initLeg x - χ₀ * chemLitLeg₂ t₀ Q x + deriv reactLeg x)
      (Set.Icc (0:ℝ) 1) x :=
    ((hinit.sub (hchem.const_mul χ₀)).add hreact)
  -- transport to `w` via `w_split`, then read off `derivWithin`.
  have hw : HasDerivWithinAt w
      (deriv initLeg x - χ₀ * chemLitLeg₂ t₀ Q x + deriv reactLeg x)
      (Set.Icc (0:ℝ) 1) x :=
    hsum.congr (fun z _ => D.w_split z) (D.w_split x)
  exact hw.derivWithin huniq

/-- The `η`-Hölder control of `derivWithin w (Icc 0 1)` supplied by the
three-leg bridge package. -/
theorem differentiatedMildSliceDiffOn_derivWithin_holder {χ₀ t₀ θ η CQ HQ M : ℝ}
    {Q : ℝ → ℝ → ℝ} {w initLeg reactLeg : ℝ → ℝ} {Ainit Achem Areact : ℝ}
    (D : DifferentiatedMildSliceDiffOn χ₀ t₀ θ η CQ HQ M Q w initLeg reactLeg
      Ainit Achem Areact) :
    ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |derivWithin w (Set.Icc (0:ℝ) 1) x - derivWithin w (Set.Icc (0:ℝ) 1) y|
        ≤ (Ainit + |χ₀| * Achem + Areact) * |x - y| ^ η := by
  intro x hx y hy
  rw [differentiatedMildSliceDiffOn_derivWithin D hx,
    differentiatedMildSliceDiffOn_derivWithin D hy]
  set dxy : ℝ := |x - y| ^ η with hdxy
  have hI := D.init_holder x hx y hy
  have hC := D.chem_holder x hx y hy
  have hR := D.react_holder x hx y hy
  have hsplit :
      (deriv initLeg x - χ₀ * chemLitLeg₂ t₀ Q x + deriv reactLeg x)
        - (deriv initLeg y - χ₀ * chemLitLeg₂ t₀ Q y + deriv reactLeg y)
      = (deriv initLeg x - deriv initLeg y)
        + (-χ₀) * (chemLitLeg₂ t₀ Q x - chemLitLeg₂ t₀ Q y)
        + (deriv reactLeg x - deriv reactLeg y) := by ring
  rw [hsplit]
  have htri :
      |(deriv initLeg x - deriv initLeg y)
          + (-χ₀) * (chemLitLeg₂ t₀ Q x - chemLitLeg₂ t₀ Q y)
          + (deriv reactLeg x - deriv reactLeg y)|
        ≤ |deriv initLeg x - deriv initLeg y|
          + |(-χ₀) * (chemLitLeg₂ t₀ Q x - chemLitLeg₂ t₀ Q y)|
          + |deriv reactLeg x - deriv reactLeg y| := by
    refine (abs_add_le _ _).trans ?_
    gcongr
    exact abs_add_le _ _
  refine htri.trans ?_
  have hχC : |(-χ₀) * (chemLitLeg₂ t₀ Q x - chemLitLeg₂ t₀ Q y)|
      ≤ |χ₀| * (Achem * dxy) := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left hC (abs_nonneg _)
  calc |deriv initLeg x - deriv initLeg y|
          + |(-χ₀) * (chemLitLeg₂ t₀ Q x - chemLitLeg₂ t₀ Q y)|
          + |deriv reactLeg x - deriv reactLeg y|
      ≤ Ainit * dxy + |χ₀| * (Achem * dxy) + Areact * dxy :=
        add_le_add (add_le_add hI hχC) hR
    _ = (Ainit + |χ₀| * Achem + Areact) * dxy := by ring

/-- The clamped closed-interval derivative representative required by the
`DifferentiableOn` Wiener feed is continuous. -/
theorem differentiatedMildSliceDiffOn_derivWithin_clamp_continuous
    {χ₀ t₀ θ η CQ HQ M : ℝ} {Q : ℝ → ℝ → ℝ}
    {w initLeg reactLeg : ℝ → ℝ} {Ainit Achem Areact : ℝ}
    (hη0 : 0 < η)
    (D : DifferentiatedMildSliceDiffOn χ₀ t₀ θ η CQ HQ M Q w initLeg reactLeg
      Ainit Achem Areact) :
    Continuous (fun x => derivWithin w (Set.Icc (0:ℝ) 1) (clamp01 x)) := by
  have hK_nn : 0 ≤ Ainit + |χ₀| * Achem + Areact := by
    have h2 : 0 ≤ |χ₀| * Achem := mul_nonneg (abs_nonneg _) D.Achem_nn
    have := D.Ainit_nn
    have := D.Areact_nn
    linarith
  have hcontOn : ContinuousOn (derivWithin w (Set.Icc (0:ℝ) 1)) (Set.Icc (0:ℝ) 1) :=
    holderBound_continuousOn_Icc hη0 hK_nn
      (fun a b ha hb => differentiatedMildSliceDiffOn_derivWithin_holder D a ha b hb)
  have hmaps : Set.MapsTo clamp01 Set.univ (Set.Icc (0:ℝ) 1) :=
    fun x _ => clamp01_mem x
  have hcomp : ContinuousOn
      (fun x => derivWithin w (Set.Icc (0:ℝ) 1) (clamp01 x)) Set.univ :=
    hcontOn.comp clamp01_continuous.continuousOn hmaps
  exact continuousOn_univ.mp hcomp

/-- **`chemMild_C1eta_slice_diffOn` — the `[0,1]` slice + Wiener feed from the bridge.**

From the differentiated mild bridge `DifferentiatedMildSliceDiffOn` (`0 < η ≤ 1`):

* `w` is differentiable on `[0,1]`;
* `derivWithin w (Icc 0 1)` is `η`-Hölder on `[0,1]` with constant
  `Ainit + |χ₀|·Achem + Areact`;
* `Summable |cosineCoeffs w n|` (the Wiener feed).

NO off-interior residual, NO global-`ℝ` differentiability, and — after the `chem_holder`
discharge (`differentiatedMildSliceDiffOn_of_brick4_chem`) — NO regularity conclusion is
carried: `init_holder`/`react_holder` come from `gradLeg_holder_global`, `chem_holder` from
the literal=spectral bridge + the committed spectral `chemLeg_holder_of_brick4`.  The
clamped `derivWithin` continuity is produced from this same Hölder package; the Wiener feed
still requires the honest endpoint no-flux package for `derivWithin w`.

**This is a slice-FROM-bridge, NOT concretely unconditional** (hence the honest relabel,
parallel to the committed `chemMild_positiveTime_C1eta_slice`).  What the bridge
`DifferentiatedMildSliceDiffOn` still CARRIES is exactly TWO non-regularity facts, both
realizable but not yet instantiated from `GradientMildSolutionData`:

* (a) the differentiated mild REPRESENTATION on `[0,1]` (`w_split`: `w = initLeg
  − χ₀·chemLitLeg + reactLeg` with `chemLitLeg` differentiable on `[0,1]`, `derivWithin =
  chemLitLeg₂`) — a REPRESENTATION fact, the interior version of which is the committed
  `chemLeg_interior_hasDerivAt`, NOT a regularity conclusion;
* (b) the concrete-`u` `Q`-data (`chemData`: continuity / sup-bound / `θ`-Hölder of
  `Q = chemFluxLifted u(s)`), realizable from the committed `chemFlux_Ctheta` +
  `mild_orderBox_positiveTime_holder`.

NO Hölder / regularity conclusion (`chem_holder`/`init_holder`/`react_holder`) remains a
free assumption. -/
theorem chemMild_C1eta_slice_diffOn {χ₀ t₀ θ η CQ HQ M : ℝ} {Q : ℝ → ℝ → ℝ}
    {w initLeg reactLeg : ℝ → ℝ} {Ainit Achem Areact : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (D : DifferentiatedMildSliceDiffOn χ₀ t₀ θ η CQ HQ M Q w initLeg reactLeg
      Ainit Achem Areact)
    (hNeumann : derivWithin w (Set.Icc (0 : ℝ) 1) 0 = 0 ∧
      derivWithin w (Set.Icc (0 : ℝ) 1) 1 = 0) :
    DifferentiableOn ℝ w (Set.Icc (0:ℝ) 1) ∧
      (∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
        |derivWithin w (Set.Icc (0:ℝ) 1) x - derivWithin w (Set.Icc (0:ℝ) 1) y|
          ≤ (Ainit + |χ₀| * Achem + Areact) * |x - y| ^ η) ∧
      Summable (fun n : ℕ => |cosineCoeffs w n|) := by
  have hwc : Continuous w := differentiatedMildSliceDiffOn_continuous D
  have hdiffOn : DifferentiableOn ℝ w (Set.Icc (0:ℝ) 1) :=
    differentiatedMildSliceDiffOn_differentiableOn D
  -- assembled Hölder constant is nonneg.
  have hK_nn : 0 ≤ Ainit + |χ₀| * Achem + Areact := by
    have h2 : 0 ≤ |χ₀| * Achem := mul_nonneg (abs_nonneg _) D.Achem_nn
    have := D.Ainit_nn; have := D.Areact_nn; linarith
  have hHolder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |derivWithin w (Set.Icc (0:ℝ) 1) x - derivWithin w (Set.Icc (0:ℝ) 1) y|
        ≤ (Ainit + |χ₀| * Achem + Areact) * |x - y| ^ η :=
    differentiatedMildSliceDiffOn_derivWithin_holder D
  have hD_cont : Continuous (fun x => derivWithin w (Set.Icc (0:ℝ) 1) (clamp01 x)) :=
    differentiatedMildSliceDiffOn_derivWithin_clamp_continuous hη0 D
  refine ⟨hdiffOn, hHolder, ?_⟩
  exact ShenWork.Wiener.EWA.holderCosineCoeff_summable_diffOn
    w hwc hdiffOn hD_cont hNeumann hη0 hη1 hK_nn
    (fun x y hx hy => hHolder x hx y hy)

/-! ## Small-`θ` chem-flux source consumer

The next two wrappers consume the Task188 small-exponent initial-holder
`ChemLegData` producer for the cutoff chem-flux source.  They discharge the
`chemData` slot and the spectral second-value leg integrability of the C1/eta
bridge; the differentiated mild representation and value-leg differentiability/Hölder
inputs remain explicit. -/

/-- The explicit `η`-Holder constant for the derivative of the homogeneous initial
value leg `S(t)u₀`. -/
noncomputable def initialValueLegDerivHolderConst (t η Cu₀ : ℝ) : ℝ :=
  (2 : ℝ) ^ (1 - η) *
    (secondDerivSmoothingConst ^ η * gradSmoothingConst ^ (1 - η)) *
      t ^ (-((1 + η) / 2) : ℝ) * Cu₀

/-- The explicit `η`-Holder constant for the derivative of the reaction Duhamel leg. -/
noncomputable def reactionDerivLegHolderConst (t η CL : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t,
    (2 : ℝ) ^ (1 - η) *
      (secondDerivSmoothingConst ^ η * gradSmoothingConst ^ (1 - η)) *
        (t - s) ^ (-((1 + η) / 2) : ℝ) * CL

/-- Time-cutoff logistic source, matching `logisticLifted p (u s)` on `0 < s ≤ T`.
This is the reaction-source analogue of `chemFluxCthetaCutoffSource`. -/
noncomputable def logisticCutoffSource
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) :
    ℝ → ℝ → ℝ :=
  fun s y => if 0 < s ∧ s ≤ T then logisticLifted p (u s) y else 0

/-- The global smooth representative carried by the phase-1 C1/η route.  It agrees
with the true lifted mild slice on `[0,1]`, but unlike the zero extension it is not
forced to vanish off the interval. -/
noncomputable def gradientMildPhase1ValueLegsCutoffRep
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (T t : ℝ) : ℝ → ℝ :=
  fun x => initialValueLeg t (intervalDomainLift u₀) x
    - p.χ₀ * chemLitLeg t (chemFluxCthetaCutoffSource p u T) x
    + reactionValueLeg t (logisticCutoffSource p u T) x

/-- The concrete mild slice agrees on `[0,1]` with the canonical global representative
used by the phase-1 C1/η value-leg bridge.  This is deliberately an `EqOn`, not a
global equality: outside `[0,1]`, `intervalDomainLift` is the zero extension while the
heat/Duhamel representative is generally nonzero. -/
theorem gradientMild_phase1ValueLegs_cutoffRep_eqOn_Icc
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (Dsol : GradientMildSolutionData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ Dsol.T) :
    Set.EqOn (intervalDomainLift (Dsol.u t))
      (gradientMildPhase1ValueLegsCutoffRep p u₀ Dsol.u Dsol.T t)
      (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  have hmap :=
    ShenWork.IntervalMildToLocalExistence.gradientMildSolution_lift_eq_gradientMildMapTermSum_on_Icc
      p Dsol ht htT
  have hchem :
      chemLitLeg t (chemFluxCthetaCutoffSource p Dsol.u Dsol.T) x =
        ∫ s in (0 : ℝ)..t,
          deriv (fun z =>
            intervalFullSemigroupOperator (t - s) (chemFluxLifted p (Dsol.u s)) z) x := by
    unfold chemLitLeg
    refine intervalIntegral.integral_congr_ae ?_
    have huIoc_eq : Set.uIoc (0 : ℝ) t = Set.Ioc (0 : ℝ) t :=
      Set.uIoc_of_le ht.le
    filter_upwards with s hs_mem
    rw [huIoc_eq] at hs_mem
    have hsT : s ≤ Dsol.T := le_trans hs_mem.2 htT
    have hwin : 0 < s ∧ s ≤ Dsol.T := ⟨hs_mem.1, hsT⟩
    have heq :
        chemFluxCthetaCutoffSource p Dsol.u Dsol.T s =
          chemFluxLifted p (Dsol.u s) := by
      funext y
      simp [chemFluxCthetaCutoffSource, hwin]
    simp [heq]
  have hreact :
      reactionValueLeg t (logisticCutoffSource p Dsol.u Dsol.T) x =
        ∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (Dsol.u s)) x := by
    unfold reactionValueLeg
    refine intervalIntegral.integral_congr_ae ?_
    have huIoc_eq : Set.uIoc (0 : ℝ) t = Set.Ioc (0 : ℝ) t :=
      Set.uIoc_of_le ht.le
    filter_upwards with s hs_mem
    rw [huIoc_eq] at hs_mem
    have hsT : s ≤ Dsol.T := le_trans hs_mem.2 htT
    have hwin : 0 < s ∧ s ≤ Dsol.T := ⟨hs_mem.1, hsT⟩
    have heq :
        logisticCutoffSource p Dsol.u Dsol.T s = logisticLifted p (Dsol.u s) := by
      funext y
      simp [logisticCutoffSource, hwin]
    simp [heq]
  calc
    intervalDomainLift (Dsol.u t) x
        = ShenWork.IntervalMildToLocalExistence.gradientMildMapTermSum p u₀ Dsol.u t x :=
          hmap hx
    _ = gradientMildPhase1ValueLegsCutoffRep p u₀ Dsol.u Dsol.T t x := by
          unfold ShenWork.IntervalMildToLocalExistence.gradientMildMapTermSum
            ShenWork.IntervalMildToLocalExistence.gradientMildSemigroupTerm
            ShenWork.IntervalMildToLocalExistence.gradientMildChemotaxisDuhamelTerm
            ShenWork.IntervalMildToLocalExistence.gradientMildLogisticDuhamelTerm
            gradientMildPhase1ValueLegsCutoffRep initialValueLeg
          rw [hchem, hreact]
          ring

/-- Cosine-coefficient summability transfers across `[0,1]` equality.  This is the
bridge from the smooth global representative back to the true lifted interval slice. -/
theorem summable_abs_cosineCoeffs_of_eqOn_Icc {f g : ℝ → ℝ}
    (hfg : Set.EqOn f g (Set.Icc (0 : ℝ) 1))
    (hg : Summable (fun n : ℕ => |cosineCoeffs g n|)) :
    Summable (fun n : ℕ => |cosineCoeffs f n|) := by
  refine hg.congr ?_
  intro n
  rw [cosineCoeffs_congr_on_Icc hfg n]

/-- The homogeneous initial value leg is globally differentiable at positive time. -/
theorem initialValueLeg_differentiable
    {t : ℝ} (ht : 0 < t) {u₀ : ℝ → ℝ}
    (hu₀_meas : AEStronglyMeasurable u₀
      (ShenWork.IntervalDomain.intervalMeasure 1))
    {Cu₀ : ℝ} (hu₀_bdd : ∀ y, |u₀ y| ≤ Cu₀) :
    Differentiable ℝ (initialValueLeg t u₀) := by
  intro x
  exact (initialValueLeg_hasDerivAt ht hu₀_meas hu₀_bdd x).differentiableAt

/-- Nonnegativity of the homogeneous initial derivative Holder constant. -/
theorem initialValueLegDerivHolderConst_nonneg
    {t η Cu₀ : ℝ} (ht : 0 < t) (hCu₀_nn : 0 ≤ Cu₀) :
    0 ≤ initialValueLegDerivHolderConst t η Cu₀ := by
  unfold initialValueLegDerivHolderConst
  have htwo : 0 ≤ (2 : ℝ) ^ (1 - η) := Real.rpow_nonneg (by norm_num) _
  have hsecond : 0 ≤ secondDerivSmoothingConst ^ η :=
    Real.rpow_nonneg secondDerivSmoothingConst_nonneg _
  have hgrad : 0 ≤ gradSmoothingConst ^ (1 - η) :=
    Real.rpow_nonneg gradSmoothingConst_nonneg _
  have ht_rpow : 0 ≤ t ^ (-((1 + η) / 2) : ℝ) :=
    Real.rpow_nonneg ht.le _
  exact mul_nonneg (mul_nonneg (mul_nonneg htwo (mul_nonneg hsecond hgrad)) ht_rpow)
    hCu₀_nn

/-- The derivative of the homogeneous initial value leg is `η`-Holder on `[0,1]`. -/
theorem initialValueLeg_deriv_holder_Icc
    {t η : ℝ} (ht : 0 < t) (hη0 : 0 < η) (hη1 : η < 1)
    {u₀ : ℝ → ℝ}
    (hu₀_meas : AEStronglyMeasurable u₀
      (ShenWork.IntervalDomain.intervalMeasure 1))
    {Cu₀ : ℝ} (hu₀_bdd : ∀ y, |u₀ y| ≤ Cu₀) :
    ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv (initialValueLeg t u₀) x - deriv (initialValueLeg t u₀) y|
        ≤ initialValueLegDerivHolderConst t η Cu₀ * |x - y| ^ η := by
  intro x _ y _
  simpa [initialValueLeg, initialValueLegDerivHolderConst] using
    (gradLeg_holder_global ht hη0 hη1 hu₀_meas hu₀_bdd x y)

/-- Nonnegativity of the reaction Duhamel derivative Holder constant. -/
theorem reactionDerivLegHolderConst_nonneg
    {t η CL : ℝ} (ht : 0 < t) (hCL_nn : 0 ≤ CL) :
    0 ≤ reactionDerivLegHolderConst t η CL := by
  unfold reactionDerivLegHolderConst
  refine intervalIntegral.integral_nonneg ht.le (fun s hs => ?_)
  have hts : 0 ≤ t - s := by linarith [hs.2]
  have htwo : 0 ≤ (2 : ℝ) ^ (1 - η) := Real.rpow_nonneg (by norm_num) _
  have hsecond : 0 ≤ secondDerivSmoothingConst ^ η :=
    Real.rpow_nonneg secondDerivSmoothingConst_nonneg _
  have hgrad : 0 ≤ gradSmoothingConst ^ (1 - η) :=
    Real.rpow_nonneg gradSmoothingConst_nonneg _
  have htime : 0 ≤ (t - s) ^ (-((1 + η) / 2) : ℝ) :=
    Real.rpow_nonneg hts _
  positivity

/-- The derivative of the reaction Duhamel leg is `η`-Holder on `[0,1]` for a bounded
measurable source. -/
theorem reactionDerivLeg_holder_Icc
    {t η : ℝ} (ht : 0 < t) (hη0 : 0 < η) (hη1 : η < 1)
    {L : ℝ → ℝ → ℝ}
    (hL_meas : Measurable (Function.uncurry L))
    {CL : ℝ} (hCL_nn : 0 ≤ CL) (hL_bdd : ∀ s y, |L s y| ≤ CL) :
    ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |reactionDerivLeg t L x - reactionDerivLeg t L y|
        ≤ reactionDerivLegHolderConst t η CL * |x - y| ^ η := by
  intro x _ y _
  unfold reactionDerivLeg reactionDerivLegHolderConst
  have hφ_int : IntervalIntegrable
      (fun s : ℝ => (2 : ℝ) ^ (1 - η) *
        (secondDerivSmoothingConst ^ η * gradSmoothingConst ^ (1 - η)) *
        (t - s) ^ (-((1 + η) / 2) : ℝ) * CL) volume 0 t := by
    have h0 := duhamel_holder_gradTime_integrand_integrable ht hη0 hη1
    have h1 := h0.const_mul ((2 : ℝ) ^ (1 - η) *
      (secondDerivSmoothingConst ^ η * gradSmoothingConst ^ (1 - η)))
    have h2 := h1.mul_const CL
    exact h2.congr (fun s _ => by ring)
  refine holder_of_duhamel_integral ht.le
    (ShenWork.IntervalDuhamelIntegrability.gradDuhamel_intervalIntegrable_of_joint_measurable
      ht hL_meas hCL_nn hL_bdd x)
    (ShenWork.IntervalDuhamelIntegrability.gradDuhamel_intervalIntegrable_of_joint_measurable
      ht hL_meas hCL_nn hL_bdd y)
    hφ_int ?_
  have hne : ∀ᵐ s ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
  filter_upwards [hne] with s hs_ne hs_mem
  have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs_mem.2 hs_ne)
  have hLs_meas : AEStronglyMeasurable (L s)
      (ShenWork.IntervalDomain.intervalMeasure 1) := by
    exact (hL_meas.comp measurable_prodMk_left).aestronglyMeasurable
  exact neumannHeatGradient_Linf_to_Ctheta hts hη0 hη1 hLs_meas
    (hL_bdd s) x y

/-- Small-exponent initial-data Holder route from the concrete chem-flux data to
the differentiated `[0,1]` C1/eta bridge package. -/
theorem differentiatedMildSliceDiffOn_of_gradientMild_initialHolder_smallTheta_cutoff_components
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (Dsol : GradientMildSolutionData p u₀)
    {χ₀ t θ η H₀ Ainit Areact : ℝ}
    {w initLeg reactLeg : ℝ → ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hθη : η < θ)
    (hθ0 : 0 < θ) (hθlt : θ < (1 / 2 : ℝ))
    (hH₀_nonneg : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (hplan : ∀ r, 0 < r → r ≤ Dsol.T → ∀ x y : intervalDomainPoint,
      NeumannHeatContractiveCouplingFor r x y (intervalDomainLift u₀))
    (ht : 0 < t) (htT : t ≤ Dsol.T)
    (init_diff : Differentiable ℝ initLeg) (react_diff : Differentiable ℝ reactLeg)
    (hAinit_nn : 0 ≤ Ainit) (hAreact_nn : 0 ≤ Areact)
    (w_split : ∀ x : ℝ,
      w x = initLeg x - χ₀ * chemLitLeg t
        (chemFluxCthetaCutoffSource p Dsol.u Dsol.T) x + reactLeg x)
    (init_holder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv initLeg x - deriv initLeg y| ≤ Ainit * |x - y| ^ η)
    (react_holder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv reactLeg x - deriv reactLeg y| ≤ Areact * |x - y| ^ η) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      DifferentiatedMildSliceDiffOn χ₀ t θ η
        (Dsol.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * Dsol.M ^ p.γ)))) HQ
        (2 * (Dsol.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * Dsol.M ^ p.γ)))))
        (chemFluxCthetaCutoffSource p Dsol.u Dsol.T)
        w initLeg reactLeg Ainit (chemDuhamelConst t θ η HQ) Areact := by
  rcases ChemLegData_of_gradientMild_initialHolder_smallTheta_cutoff_components
      Dsol hθ0 hθlt hH₀_nonneg hholder hplan ht htT with
    ⟨HQ, hHQ_nonneg, chemData⟩
  refine ⟨HQ, hHQ_nonneg, ?_⟩
  exact differentiatedMildSliceDiffOn_of_brick4_chem hη0 hη1 hθη chemData
    init_diff react_diff hAinit_nn hAreact_nn w_split init_holder react_holder

/-- Small-exponent concrete chem-flux route with the canonical homogeneous initial
value leg `S(t)u₀`.  This discharges the initial-leg differentiability and Holder
inputs from heat-gradient smoothing; the reaction-leg data and representation remain
honest inputs. -/
theorem differentiatedMildSliceDiffOn_of_gradientMild_initialValueLeg_smallTheta_cutoff_components
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (Dsol : GradientMildSolutionData p u₀)
    {χ₀ t θ η H₀ Cu₀ Areact : ℝ}
    {w reactLeg : ℝ → ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hθη : η < θ)
    (hθ0 : 0 < θ) (hθlt : θ < (1 / 2 : ℝ))
    (hH₀_nonneg : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (hplan : ∀ r, 0 < r → r ≤ Dsol.T → ∀ x y : intervalDomainPoint,
      NeumannHeatContractiveCouplingFor r x y (intervalDomainLift u₀))
    (ht : 0 < t) (htT : t ≤ Dsol.T)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀)
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hu₀_bdd : ∀ y, |intervalDomainLift u₀ y| ≤ Cu₀)
    (hCu₀_nn : 0 ≤ Cu₀)
    (react_diff : Differentiable ℝ reactLeg)
    (hAreact_nn : 0 ≤ Areact)
    (w_split : ∀ x : ℝ,
      w x = initialValueLeg t (intervalDomainLift u₀) x - χ₀ * chemLitLeg t
        (chemFluxCthetaCutoffSource p Dsol.u Dsol.T) x + reactLeg x)
    (react_holder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv reactLeg x - deriv reactLeg y| ≤ Areact * |x - y| ^ η) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      DifferentiatedMildSliceDiffOn χ₀ t θ η
        (Dsol.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * Dsol.M ^ p.γ)))) HQ
        (2 * (Dsol.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * Dsol.M ^ p.γ)))))
        (chemFluxCthetaCutoffSource p Dsol.u Dsol.T)
        w (initialValueLeg t (intervalDomainLift u₀)) reactLeg
        (initialValueLegDerivHolderConst t η Cu₀) (chemDuhamelConst t θ η HQ)
        Areact := by
  have init_diff : Differentiable ℝ (initialValueLeg t (intervalDomainLift u₀)) :=
    initialValueLeg_differentiable ht hu₀_meas hu₀_bdd
  have hAinit_nn : 0 ≤ initialValueLegDerivHolderConst t η Cu₀ :=
    initialValueLegDerivHolderConst_nonneg ht hCu₀_nn
  have init_holder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv (initialValueLeg t (intervalDomainLift u₀)) x -
          deriv (initialValueLeg t (intervalDomainLift u₀)) y|
        ≤ initialValueLegDerivHolderConst t η Cu₀ * |x - y| ^ η :=
    initialValueLeg_deriv_holder_Icc ht hη0 hη1 hu₀_meas hu₀_bdd
  exact differentiatedMildSliceDiffOn_of_gradientMild_initialHolder_smallTheta_cutoff_components
    Dsol hη0 hη1 hθη hθ0 hθlt hH₀_nonneg hholder hplan ht htT
    init_diff react_diff hAinit_nn hAreact_nn w_split init_holder react_holder

/-- Small-exponent concrete chem-flux route with the canonical phase-1 value legs
`S(t)u₀` and `∫₀ᵗ S(t-s)L(s) ds`.  This discharges the value-leg differentiability
inputs and the initial-leg Holder input from existing phase-1 APIs; the reaction-leg
Holder field, representation, and endpoint no-flux remain honest data. -/
theorem differentiatedMildSliceDiffOn_of_gradientMild_phase1ValueLegs_smallTheta_cutoff_components
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (Dsol : GradientMildSolutionData p u₀)
    {χ₀ t θ η H₀ Cu₀ CL : ℝ}
    {L : ℝ → ℝ → ℝ} {w : ℝ → ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hθη : η < θ)
    (hθ0 : 0 < θ) (hθlt : θ < (1 / 2 : ℝ))
    (hH₀_nonneg : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (hplan : ∀ r, 0 < r → r ≤ Dsol.T → ∀ x y : intervalDomainPoint,
      NeumannHeatContractiveCouplingFor r x y (intervalDomainLift u₀))
    (ht : 0 < t) (htT : t ≤ Dsol.T)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀)
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hu₀_bdd : ∀ y, |intervalDomainLift u₀ y| ≤ Cu₀)
    (hCu₀_nn : 0 ≤ Cu₀)
    (hL_meas : Measurable (Function.uncurry L))
    (hCL_nn : 0 ≤ CL)
    (hL_bdd : ∀ s y, |L s y| ≤ CL)
    (w_split : ∀ x : ℝ,
      w x = initialValueLeg t (intervalDomainLift u₀) x - χ₀ * chemLitLeg t
        (chemFluxCthetaCutoffSource p Dsol.u Dsol.T) x + reactionValueLeg t L x) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      DifferentiatedMildSliceDiffOn χ₀ t θ η
        (Dsol.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * Dsol.M ^ p.γ)))) HQ
        (2 * (Dsol.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * Dsol.M ^ p.γ)))))
        (chemFluxCthetaCutoffSource p Dsol.u Dsol.T)
        w (initialValueLeg t (intervalDomainLift u₀)) (reactionValueLeg t L)
        (initialValueLegDerivHolderConst t η Cu₀) (chemDuhamelConst t θ η HQ)
        (reactionDerivLegHolderConst t η CL) := by
  have react_diff : Differentiable ℝ (reactionValueLeg t L) := by
    intro x
    exact (reactionValueLeg_hasDerivAt ht hL_meas hCL_nn hL_bdd x).differentiableAt
  have hAreact_nn : 0 ≤ reactionDerivLegHolderConst t η CL :=
    reactionDerivLegHolderConst_nonneg ht hCL_nn
  have react_holder_deriv : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv (reactionValueLeg t L) x - deriv (reactionValueLeg t L) y|
        ≤ reactionDerivLegHolderConst t η CL * |x - y| ^ η := by
    intro x hx y hy
    rw [reactionValueLeg_deriv_eq ht hL_meas hCL_nn hL_bdd x,
      reactionValueLeg_deriv_eq ht hL_meas hCL_nn hL_bdd y]
    exact reactionDerivLeg_holder_Icc ht hη0 hη1 hL_meas hCL_nn hL_bdd x hx y hy
  exact
    differentiatedMildSliceDiffOn_of_gradientMild_initialValueLeg_smallTheta_cutoff_components
      Dsol hη0 hη1 hθη hθ0 hθlt hH₀_nonneg hholder hplan ht htT
      hu₀_meas hu₀_bdd hCu₀_nn react_diff hAreact_nn w_split react_holder_deriv

/-- Small-exponent initial-data Holder route from the concrete chem-flux data to
the `[0,1]` C1/eta slice conclusion and Wiener coefficient summability. -/
theorem chemMild_C1eta_slice_diffOn_of_gradientMild_initialHolder_smallTheta_cutoff_components
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (Dsol : GradientMildSolutionData p u₀)
    {χ₀ t θ η H₀ Ainit Areact : ℝ}
    {w initLeg reactLeg : ℝ → ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hθη : η < θ)
    (hθ0 : 0 < θ) (hθlt : θ < (1 / 2 : ℝ))
    (hH₀_nonneg : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (hplan : ∀ r, 0 < r → r ≤ Dsol.T → ∀ x y : intervalDomainPoint,
      NeumannHeatContractiveCouplingFor r x y (intervalDomainLift u₀))
    (ht : 0 < t) (htT : t ≤ Dsol.T)
    (init_diff : Differentiable ℝ initLeg) (react_diff : Differentiable ℝ reactLeg)
    (hAinit_nn : 0 ≤ Ainit) (hAreact_nn : 0 ≤ Areact)
    (w_split : ∀ x : ℝ,
      w x = initLeg x - χ₀ * chemLitLeg t
        (chemFluxCthetaCutoffSource p Dsol.u Dsol.T) x + reactLeg x)
    (init_holder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv initLeg x - deriv initLeg y| ≤ Ainit * |x - y| ^ η)
    (react_holder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv reactLeg x - deriv reactLeg y| ≤ Areact * |x - y| ^ η)
    (hNeumann : derivWithin w (Set.Icc (0 : ℝ) 1) 0 = 0 ∧
      derivWithin w (Set.Icc (0 : ℝ) 1) 1 = 0) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      DifferentiableOn ℝ w (Set.Icc (0:ℝ) 1) ∧
        (∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
          |derivWithin w (Set.Icc (0:ℝ) 1) x -
              derivWithin w (Set.Icc (0:ℝ) 1) y|
            ≤ (Ainit + |χ₀| * chemDuhamelConst t θ η HQ + Areact) *
              |x - y| ^ η) ∧
        Summable (fun n : ℕ => |cosineCoeffs w n|) := by
  rcases
      differentiatedMildSliceDiffOn_of_gradientMild_initialHolder_smallTheta_cutoff_components
        Dsol hη0 hη1 hθη hθ0 hθlt hH₀_nonneg hholder hplan ht htT
        init_diff react_diff hAinit_nn hAreact_nn w_split init_holder react_holder with
    ⟨HQ, hHQ_nonneg, Dslice⟩
  refine ⟨HQ, hHQ_nonneg, ?_⟩
  exact chemMild_C1eta_slice_diffOn hη0 hη1.le Dslice hNeumann

/-- Small-exponent concrete chem-flux route to the `[0,1]` C1/eta slice conclusion
with the canonical phase-1 value legs `S(t)u₀` and `∫₀ᵗ S(t-s)L(s) ds`. -/
theorem chemMild_C1eta_slice_diffOn_of_gradientMild_phase1ValueLegs_smallTheta_cutoff_components
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (Dsol : GradientMildSolutionData p u₀)
    {χ₀ t θ η H₀ Cu₀ CL : ℝ}
    {L : ℝ → ℝ → ℝ} {w : ℝ → ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hθη : η < θ)
    (hθ0 : 0 < θ) (hθlt : θ < (1 / 2 : ℝ))
    (hH₀_nonneg : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (hplan : ∀ r, 0 < r → r ≤ Dsol.T → ∀ x y : intervalDomainPoint,
      NeumannHeatContractiveCouplingFor r x y (intervalDomainLift u₀))
    (ht : 0 < t) (htT : t ≤ Dsol.T)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀)
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hu₀_bdd : ∀ y, |intervalDomainLift u₀ y| ≤ Cu₀)
    (hCu₀_nn : 0 ≤ Cu₀)
    (hL_meas : Measurable (Function.uncurry L))
    (hCL_nn : 0 ≤ CL)
    (hL_bdd : ∀ s y, |L s y| ≤ CL)
    (w_split : ∀ x : ℝ,
      w x = initialValueLeg t (intervalDomainLift u₀) x - χ₀ * chemLitLeg t
        (chemFluxCthetaCutoffSource p Dsol.u Dsol.T) x + reactionValueLeg t L x)
    (hNeumann : derivWithin w (Set.Icc (0 : ℝ) 1) 0 = 0 ∧
      derivWithin w (Set.Icc (0 : ℝ) 1) 1 = 0) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      DifferentiableOn ℝ w (Set.Icc (0:ℝ) 1) ∧
        (∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
          |derivWithin w (Set.Icc (0:ℝ) 1) x -
              derivWithin w (Set.Icc (0:ℝ) 1) y|
            ≤ (initialValueLegDerivHolderConst t η Cu₀ +
                |χ₀| * chemDuhamelConst t θ η HQ +
                  reactionDerivLegHolderConst t η CL) *
              |x - y| ^ η) ∧
        Summable (fun n : ℕ => |cosineCoeffs w n|) := by
  rcases
      differentiatedMildSliceDiffOn_of_gradientMild_phase1ValueLegs_smallTheta_cutoff_components
        Dsol hη0 hη1 hθη hθ0 hθlt hH₀_nonneg hholder hplan ht htT
        hu₀_meas hu₀_bdd hCu₀_nn hL_meas hCL_nn hL_bdd w_split with
    ⟨HQ, hHQ_nonneg, Dslice⟩
  refine ⟨HQ, hHQ_nonneg, ?_⟩
  exact chemMild_C1eta_slice_diffOn hη0 hη1.le Dslice hNeumann

/-- Small-exponent concrete chem-flux route to the `[0,1]` C1/eta slice conclusion
with the canonical homogeneous initial value leg `S(t)u₀`. -/
theorem chemMild_C1eta_slice_diffOn_of_gradientMild_initialValueLeg_smallTheta_cutoff_components
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (Dsol : GradientMildSolutionData p u₀)
    {χ₀ t θ η H₀ Cu₀ Areact : ℝ}
    {w reactLeg : ℝ → ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hθη : η < θ)
    (hθ0 : 0 < θ) (hθlt : θ < (1 / 2 : ℝ))
    (hH₀_nonneg : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (hplan : ∀ r, 0 < r → r ≤ Dsol.T → ∀ x y : intervalDomainPoint,
      NeumannHeatContractiveCouplingFor r x y (intervalDomainLift u₀))
    (ht : 0 < t) (htT : t ≤ Dsol.T)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀)
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hu₀_bdd : ∀ y, |intervalDomainLift u₀ y| ≤ Cu₀)
    (hCu₀_nn : 0 ≤ Cu₀)
    (react_diff : Differentiable ℝ reactLeg)
    (hAreact_nn : 0 ≤ Areact)
    (w_split : ∀ x : ℝ,
      w x = initialValueLeg t (intervalDomainLift u₀) x - χ₀ * chemLitLeg t
        (chemFluxCthetaCutoffSource p Dsol.u Dsol.T) x + reactLeg x)
    (react_holder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv reactLeg x - deriv reactLeg y| ≤ Areact * |x - y| ^ η)
    (hNeumann : derivWithin w (Set.Icc (0 : ℝ) 1) 0 = 0 ∧
      derivWithin w (Set.Icc (0 : ℝ) 1) 1 = 0) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      DifferentiableOn ℝ w (Set.Icc (0:ℝ) 1) ∧
        (∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
          |derivWithin w (Set.Icc (0:ℝ) 1) x -
              derivWithin w (Set.Icc (0:ℝ) 1) y|
            ≤ (initialValueLegDerivHolderConst t η Cu₀ +
                |χ₀| * chemDuhamelConst t θ η HQ + Areact) *
              |x - y| ^ η) ∧
        Summable (fun n : ℕ => |cosineCoeffs w n|) := by
  rcases
      differentiatedMildSliceDiffOn_of_gradientMild_initialValueLeg_smallTheta_cutoff_components
        Dsol hη0 hη1 hθη hθ0 hθlt hH₀_nonneg hholder hplan ht htT
        hu₀_meas hu₀_bdd hCu₀_nn react_diff hAreact_nn w_split react_holder with
    ⟨HQ, hHQ_nonneg, Dslice⟩
  refine ⟨HQ, hHQ_nonneg, ?_⟩
  exact chemMild_C1eta_slice_diffOn hη0 hη1.le Dslice hNeumann

end

end ShenWork.Paper2
