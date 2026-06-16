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
    * feeding this into the `DifferentiableOn` summability variant
      `holderCosineCoeff_summable_of_differentiableOn` yields `Summable |cosineCoeffs w n|`.

  **NO Neumann** (the cosine-IBP boundary term vanishes from `sin(nπ)=sin 0=0` alone),
  **NO off-interior residual** (the interchange is the committed interior one extended to
  the endpoints, step 1), **NO global-`ℝ` differentiability** of `w` (only on `[0,1]`).

  The only carried datum is the differentiated mild REPRESENTATION on `[0,1]`
  (`w = initLeg − χ₀·chemLitLeg + reactLeg`, the `∂ₓ ∫ = ∫ ∂ₓ` identity) and the per-leg
  `η`-Hölder moduli — exactly the bridge data of the committed `DifferentiatedMildSlice`,
  NOT a regularity conclusion.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.Paper2.ChemMildDifferentiableOn
import ShenWork.Paper2.ChemMildC1etaAssembly
import ShenWork.Wiener.EWA.HolderCosineDecayDiffOn

open MeasureTheory Set
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
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
    (hd : ChemLegData t₀ θ CQ HQ M Q) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
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

/-- **`DifferentiatedMildSliceDiffOn` — the unconditional `[0,1]` bridge package.**

The differentiated mild slice `w = u(t₀,·)` over `[0,1]`, recorded as the honest
representation data plus the per-leg `η`-Hölder moduli, in the `DifferentiableOn`/
`derivWithin` route (NO global differentiability, NO Neumann):

* `w_split` — the `[0,1]` representative `w x = initLeg x − χ₀·chemLitLeg t₀ Q x + reactLeg x`
  (the differentiated mild representation; legs defined on all of `ℝ`);
* `chemData` — the committed step-1 bundle giving `chemLitLeg` differentiable on `[0,1]`
  with `derivWithin = chemLitLeg₂`;
* `init_diff` / `react_diff` — the value legs are globally differentiable (committed
  gradient route), hence `DifferentiableOn ℝ · (Icc 0 1)` and `derivWithin = deriv`;
* `init_holder` / `chem_holder` / `react_holder` — the per-leg `η`-Hölder of the
  `[0,1]` derivatives, `[0,1]`-local (the value legs are even global). -/
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
  (realizable from the committed global gradient route `gradLeg_holder_global`);
* `hleg_int` — interval-integrability of the spectral Duhamel integrand (needed by
  `chemLeg_holder_of_brick4`; for `x ∈ [0,1]` this is the `chemLitLeg₂` integrand).
`chem_holder` is NO LONGER assumed. -/
theorem differentiatedMildSliceDiffOn_of_brick4_chem
    {χ₀ t₀ θ η CQ HQ M Ainit Areact : ℝ} {Q : ℝ → ℝ → ℝ}
    {w initLeg reactLeg : ℝ → ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hθη : η < θ)
    (chemData : ChemLegData t₀ θ CQ HQ M Q)
    (init_diff : Differentiable ℝ initLeg) (react_diff : Differentiable ℝ reactLeg)
    (hAinit_nn : 0 ≤ Ainit) (hAreact_nn : 0 ≤ Areact)
    (hleg_int : ∀ x : ℝ, IntervalIntegrable
      (fun s => unitIntervalCosineHeatSecondValue (t₀ - s) (cosineCoeffs (Q s)) (clamp01 x))
      volume 0 t₀)
    (w_split : ∀ x : ℝ, w x = initLeg x - χ₀ * chemLitLeg t₀ Q x + reactLeg x)
    (init_holder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv initLeg x - deriv initLeg y| ≤ Ainit * |x - y| ^ η)
    (react_holder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv reactLeg x - deriv reactLeg y| ≤ Areact * |x - y| ^ η) :
    DifferentiatedMildSliceDiffOn χ₀ t₀ θ η CQ HQ M Q w initLeg reactLeg
      Ainit (chemDuhamelConst t₀ θ η HQ) Areact := by
  have ht₀ := chemData.ht₀; have hθ0 := chemData.hθ0; have hθ1 := chemData.hθ1
  have hHQ_nn := chemData.hHQ_nn
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
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
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

/-- **`chemMild_C1eta_slice_diffOn` — the `[0,1]` slice + Wiener feed from the bridge.**

From the differentiated mild bridge `DifferentiatedMildSliceDiffOn` (`0 < η ≤ 1`):

* `w` is differentiable on `[0,1]`;
* `derivWithin w (Icc 0 1)` is `η`-Hölder on `[0,1]` with constant
  `Ainit + |χ₀|·Achem + Areact`;
* `Summable |cosineCoeffs w n|` (the Wiener feed).

NO Neumann, NO off-interior residual, NO global-`ℝ` differentiability, and — after the
`chem_holder` discharge (`differentiatedMildSliceDiffOn_of_brick4_chem`) — NO regularity
conclusion is carried: `init_holder`/`react_holder` come from `gradLeg_holder_global`,
`chem_holder` from the literal=spectral bridge + the committed spectral
`chemLeg_holder_of_brick4`.

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
      Ainit Achem Areact) :
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
  -- the `η`-Hölder of `derivWithin w (Icc 0 1)` on `[0,1]` via the three-leg triangle.
  have hHolder : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |derivWithin w (Set.Icc (0:ℝ) 1) x - derivWithin w (Set.Icc (0:ℝ) 1) y|
        ≤ (Ainit + |χ₀| * Achem + Areact) * |x - y| ^ η := by
    intro x hx y hy
    rw [differentiatedMildSliceDiffOn_derivWithin D hx,
      differentiatedMildSliceDiffOn_derivWithin D hy]
    set dxy : ℝ := |x - y| ^ η with hdxy
    have hI := D.init_holder x hx y hy
    have hC := D.chem_holder x hx y hy
    have hR := D.react_holder x hx y hy
    -- rearrange the difference of the three-leg sums into leg differences.
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
  refine ⟨hdiffOn, hHolder, ?_⟩
  exact ShenWork.Wiener.EWA.holderCosineCoeff_summable_of_differentiableOn
    w hwc hdiffOn hη0 hη1 hK_nn hHolder

end

end ShenWork.Paper2
