import ShenWork.Wiener.EWA.ChemDivUncond
import ShenWork.Wiener.EWA.SourceFixedPointAbs
import ShenWork.Paper2.IntervalMildRegularityBootstrap

/-!
# EWA capstone (χ₀<0 Route A′) — BRICKS 5–6: source fixed point → CLASSICAL solution

This file is the FINAL assembly of the χ₀<0 Route-A′ construction.  It connects the
committed source-form EWA fixed point `u* = Φ(u*)` (`picardEWA_abs_fixedPoint`,
`SourceFixedPointAbs.lean:145`) to a CLASSICAL solution of the source-form PDE, via:

* the **source-ℓ¹ capstone** `chemDiv_eigenvalueSummableOn_uncond`
  (`ChemDivUncond.lean:187`), which gives the eigenvalue-ℓ¹ summability of the
  chemotaxis-divergence Duhamel summand; and
* the **cosine C² route** `cosineCoeffSeries_contDiff_two`
  (`IntervalDuhamelClosedC2.lean:1386`), which turns `Σₙ λₙ|b̂ₙ(t)| < ∞` into a
  `ContDiff ℝ 2` spatial slice with Neumann endpoint derivatives.

## The solution coefficient and its three-way decomposition

The source-form mild solution's `n`-th Neumann cosine coefficient at time `t` is the
sum of three spectral pieces — exactly the eval of the Picard map
`Φ(u) = heatEWA u₀E + (−χ₀)•𝒟(Q(u)) + 𝒱(G(u))` (`SourceFixedPoint.lean:53`):

```
  fullSourceCoeff p u u₀cos t n
    =       heatHomCoeff u₀cos t n                              -- heat datum S_N(t)u₀
      + (−χ₀) · duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n   -- −χ₀ ∂ₓQ
      +        duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n    -- logistic G
```

Each summand is eigenvalue-ℓ¹ from a SEPARATE committed engine:

* **heat**: `heatCoeff_eigenvalue_summable` (`IntervalSemigroupNeumann.lean:31`) —
  positive-time heat smoothing, needs only a uniform bound on `u₀cos`;
* **chemDiv-Duhamel**: THE CAPSTONE `chemDiv_eigenvalueSummableOn_uncond` — note
  `duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n` is DEFINITIONALLY the
  capstone's integral `∫₀ᵗ e^{−(t−s)λₙ} (coupledChemDivSourceCoeffs p u s n) ds`
  (`duhamelSpectralCoeff`, `IntervalDuhamelClosedC2.lean:1494`);
* **logistic-Duhamel**: `duhamelSpectralCoeff_eigenvalue_summable`
  (`IntervalDuhamelClosedC2.lean:1551`) from a `DuhamelSourceTimeC1` for the
  logistic source — carried as a named field (genuine source time-regularity).

The three-way summability then feeds `cosineCoeffSeries_contDiff_two` for the spatial
`C²`, with Neumann endpoints from `cosineCoeffSeries_deriv_at_zero/one`.

## Honest accounting — what closes vs. what is carried

What is PROVED here (unconditionally on the carried record data):

1. `fullSourceCoeff_eigenvalue_summable` — the three-way `Σₙ λₙ|b̂ₙ| < ∞` assembly,
   with the chemDiv leg discharged by the capstone and the heat/logistic legs by the
   committed engines;
2. `fullSourceCoeff_contDiff_two` — the spatial `ContDiff ℝ 2` of the synthesised
   slice `x ↦ Σₙ b̂ₙ(t) cos(nπx)`;
3. `fullSourceCoeff_neumann_left/right` — the Neumann endpoint derivatives vanish.

What is CARRIED as named hypotheses in `SourceStrongSolutionData` (genuinely open,
NOT dischargeable from the fixed point in the current tree):

* the **realization** `realizes`: the real-space slice equals its cosine synthesis
  `u t x = Σₙ b̂ₙ(t) cos(nπx)` on `[0,1]`.  This is the eval of `Φ(u*)`; its heat leg
  needs the UNCOMMITTED heat eval bridge `heatEWA_evalST_eq`
  (`SourceFixedPointAbs.lean:42`, flagged MODERATE/gated in `ROUTE.md`).
* the capstone's discharge inputs (chemDiv early/window/continuity inputs — the
  `hcap*` fields, exactly the hypotheses of `chemDiv_eigenvalueSummableOn_uncond`);
* the **logistic source** time-`C¹` package `logSrc : DuhamelSourceTimeC1 …`;
* the **heat coefficient bound** `hu0bd`;
* the **time-regularity** `u_t` and the PDE-from-mild step are NOT part of the
  spatial-`C²` record (mirrors the grade-1 architecture of
  `GradientMildClassicalRegularityFrontierData`, where the time-derivative legs are
  separate named frontier fields — `IntervalMildToClassical.lean:680`).

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDuhamelClosedC2
  (duhamelSpectralCoeff duhamelSpectralCoeff_eigenvalue_summable DuhamelSourceTimeC1
    cosineCoeffSeries_contDiff_two cosineCoeffSeries_deriv_at_zero
    cosineCoeffSeries_deriv_at_one)
open ShenWork.IntervalSemigroupNeumann (heatCoeff_eigenvalue_summable)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledChemDivSourceLift coupledLogisticSourceCoeffs)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.PDE (intervalNeumannResolverCoeff)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Part 1 — the source-form full solution coefficient. -/

/-- **The source-form full solution coefficient.**  The `n`-th Neumann cosine
coefficient at time `t` of the source-form mild solution, as the eval of the Picard
map `Φ(u) = heatEWA u₀E + (−χ₀)•𝒟(Q(u)) + 𝒱(G(u))`:

heat datum `+` `(−χ₀)·` chemotaxis-divergence Duhamel `+` logistic Duhamel.

`u₀cos n` is the `n`-th cosine coefficient of the initial datum (so the heat leg is
`e^{−tλₙ}·u₀cos n`); `duhamelSpectralCoeff` is the committed spectral Duhamel
coefficient `∫₀ᵗ e^{−(t−s)λₙ} ĝₙ(s) ds`. -/
noncomputable def fullSourceCoeff (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n
    + (-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n
    + duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n

/-! ### Part 2 — the three-way eigenvalue-ℓ¹ summability (capstone + heat + logistic). -/

/-- **The chemDiv-Duhamel coefficient IS the capstone's integral.**  `rfl`: the
committed `duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n` unfolds to
`∫₀ᵗ e^{−(t−s)λₙ}·(coupledChemDivSourceCoeffs p u s n) ds`, exactly the summand of
`chemDiv_eigenvalueSummableOn_uncond`. -/
theorem duhamelSpectralCoeff_chemDiv_eq (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) (n : ℕ) :
    duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n
      = ∫ s in (0 : ℝ)..t,
          Real.exp (-(t - s) * unitIntervalCosineEigenvalue n)
            * coupledChemDivSourceCoeffs p u s n := rfl

/-- **The chemDiv-Duhamel leg is eigenvalue-ℓ¹** — a thin re-statement of the
capstone `chemDiv_eigenvalueSummableOn_uncond` in `duhamelSpectralCoeff` form. -/
theorem chemDivDuhamel_eigenvalue_summable
    {μ ν γ : ℝ} (hμ : 0 < μ) (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ)
    {t τ₀ : ℝ} (htlo : 0 < t) (hthi : t ≤ T)
    (hτ0 : 0 < τ₀) (hτt : τ₀ < t)
    (hGcont : ∀ n, Continuous (fun s => coupledChemDivSourceCoeffs p u s n))
    {M : ℝ} (hM : 0 ≤ M)
    (hLiftCont : ∀ s ∈ Set.Icc (0 : ℝ) τ₀,
      ContinuousOn (coupledChemDivSourceLift p u s) (Set.Icc (0 : ℝ) 1))
    (hLiftBd : ∀ s ∈ Set.Icc (0 : ℝ) τ₀, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |coupledChemDivSourceLift p u s x| ≤ M)
    (Bv : ℕ → ℝ)
    (hBv : ∀ s k,
      |cosineCoeffs (intervalDomainLift ((fun s => u (s + τ₀)) s)) k| ≤ Bv k)
    (hBvnn : ∀ k, 0 ≤ Bv k)
    (hBvsum : Summable (fun k : ℕ => (1 + (k : ℝ)) * Bv k))
    (hcont : ∀ n : ℤ, Continuous (embedModeFun (fun s => u (s + τ₀)) n))
    (hgrad : ∀ τ : TimeDom T, Summable fun k : ℕ =>
      |(intervalNeumannResolverCoeff p ((fun s => u (s + τ₀)) τ.1) k).re|
        * ((k : ℝ) * Real.pi))
    (h_flux_nbhd : ∀ (τ : TimeDom T), ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (y : WA.Circ) (GWA.incl (by omega : (0:ℕ) ≤ 1)
        (chemFluxEWA μ ν p.β γ hμ
          (embedEWA (fun s => u (s + τ₀)) hBv hBvnn hBvsum hcont)))
        = ((chemFluxLifted p ((fun s => u (s + τ₀)) τ.1) y : ℝ) : ℂ))
    (h_flux_diff : ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (chemFluxLifted p ((fun s => u (s + τ₀)) τ.1)) x) :
    Summable (fun n => unitIntervalCosineEigenvalue n *
      |duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n|) := by
  simpa only [duhamelSpectralCoeff_chemDiv_eq] using
    chemDiv_eigenvalueSummableOn_uncond hμ p u htlo hthi hτ0 hτt hGcont hM
      hLiftCont hLiftBd Bv hBv hBvnn hBvsum hcont hgrad h_flux_nbhd h_flux_diff

/-- **The three-way eigenvalue-ℓ¹ assembly.**  Given the chemDiv-Duhamel leg
eigenvalue-ℓ¹ (`hchem`, from the capstone), a uniform bound on the heat datum
(`hu0bd`) and a `DuhamelSourceTimeC1` package for the logistic source (`logSrc`),
the full source coefficient is eigenvalue-ℓ¹:
`Σₙ λₙ |fullSourceCoeff p u u₀cos t n| < ∞`. -/
theorem fullSourceCoeff_eigenvalue_summable (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {t : ℝ} (ht : 0 < t)
    {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : Summable (fun n => unitIntervalCosineEigenvalue n *
      |duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n|))
    (logSrc : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u)) :
    Summable (fun n => unitIntervalCosineEigenvalue n *
      |fullSourceCoeff p u u₀cos t n|) := by
  -- the three summable legs
  have hheat : Summable (fun n => unitIntervalCosineEigenvalue n *
      |Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n|) :=
    heatCoeff_eigenvalue_summable ht hu0bd
  have hlog : Summable (fun n => unitIntervalCosineEigenvalue n *
      |duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n|) :=
    duhamelSpectralCoeff_eigenvalue_summable logSrc ht
  -- the chemDiv leg scaled by |−χ₀|
  have hchemS : Summable (fun n => unitIntervalCosineEigenvalue n *
      ((|(-p.χ₀)|) * |duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n|)) := by
    have := hchem.mul_left (|(-p.χ₀)|)
    refine this.congr (fun n => by ring)
  -- dominate the full coefficient by the sum of the three legs
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((hheat.add hchemS).add hlog)
  · exact mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity) (abs_nonneg _)
  · have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    unfold fullSourceCoeff
    calc unitIntervalCosineEigenvalue n
            * |Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n
                + (-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n
                + duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n|
        ≤ unitIntervalCosineEigenvalue n
            * (|Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n|
                + |(-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n|
                + |duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n|) := by
          refine mul_le_mul_of_nonneg_left ?_ hlam
          exact le_trans (abs_add_le _ _) (by gcongr; exact abs_add_le _ _)
      _ = unitIntervalCosineEigenvalue n
              * |Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n|
            + unitIntervalCosineEigenvalue n
              * (|(-p.χ₀)| * |duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n|)
            + unitIntervalCosineEigenvalue n
              * |duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n| := by
          have hchemabs :
              |(-p.χ₀) * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n|
                = |(-p.χ₀)| * |duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n| :=
            abs_mul _ _
          rw [hchemabs]; ring

/-! ### Part 3 — the spatial `C²` and Neumann endpoints of the synthesised slice. -/

/-- **The source-form slice is spatially `C²`.**  From the three-way eigenvalue-ℓ¹
summability, the synthesised cosine slice `x ↦ Σₙ b̂ₙ(t) cos(nπx)` is `ContDiff ℝ 2`
(the committed cosine-series `C²` engine). -/
theorem fullSourceCoeff_contDiff_two (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {t : ℝ}
    (hsum : Summable (fun n => unitIntervalCosineEigenvalue n *
      |fullSourceCoeff p u u₀cos t n|)) :
    ContDiff ℝ 2 (fun x => ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x) :=
  cosineCoeffSeries_contDiff_two hsum

/-- **Left Neumann endpoint.**  `∂ₓ` of the synthesised slice vanishes at `x = 0`. -/
theorem fullSourceCoeff_neumann_left (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {t : ℝ}
    (hsum : Summable (fun n => unitIntervalCosineEigenvalue n *
      |fullSourceCoeff p u u₀cos t n|)) :
    deriv (fun x => ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x) 0 = 0 :=
  cosineCoeffSeries_deriv_at_zero hsum

/-- **Right Neumann endpoint.**  `∂ₓ` of the synthesised slice vanishes at `x = 1`. -/
theorem fullSourceCoeff_neumann_right (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {t : ℝ}
    (hsum : Summable (fun n => unitIntervalCosineEigenvalue n *
      |fullSourceCoeff p u u₀cos t n|)) :
    deriv (fun x => ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x) 1 = 0 :=
  cosineCoeffSeries_deriv_at_one hsum

/-! ### Part 4 — the SourceStrongSolutionData record + the strong-solution theorem. -/

/-- **Source-form strong-solution data (χ₀<0).**

The record bundles the realized real-space solution `u` of the source-form mild
equation, the initial cosine datum `u₀cos`, and the genuinely-open inputs needed to
turn the EWA fixed point into the cosine-synthesis classical slice:

* `htlo`/`hthi`/`hτ0`/`hτt` — the positive-time window `0 < τ₀ < t ≤ T`;
* `realizes` — the realization: on `[0,1]` the physical slice `u t` equals its
  cosine synthesis from `fullSourceCoeff` (the eval of `Φ(u*)`; its heat leg needs
  the gated `heatEWA_evalST_eq`, so this is carried, NOT proved here);
* `hu0bd` — uniform bound on the heat datum's cosine coefficients;
* the `cap*` fields — exactly the discharge inputs of
  `chemDiv_eigenvalueSummableOn_uncond` for the chemDiv leg;
* `logSrc` — the logistic source's time-`C¹` package (`DuhamelSourceTimeC1`).

From these the spatial `C²` + Neumann endpoints of the slice are PROVED
(`isClassicalSpatialSlice`). -/
structure SourceStrongSolutionData (T : ℝ) {μ ν γ : ℝ} (hμ : 0 < μ) (p : CM2Params) where
  /-- The realized real-space solution. -/
  u : ℝ → intervalDomainPoint → ℝ
  /-- The initial datum's Neumann cosine coefficients. -/
  u₀cos : ℕ → ℝ
  /-- The interior evaluation time. -/
  t : ℝ
  /-- The early-window split point. -/
  τ₀ : ℝ
  htlo : 0 < t
  hthi : t ≤ T
  hτ0 : 0 < τ₀
  hτt : τ₀ < t
  /-- Uniform bound on the heat datum coefficients. -/
  Mu0 : ℝ
  hu0bd : ∀ n, |u₀cos n| ≤ Mu0
  /-- **Realization** (carried — needs the gated heat eval bridge): on `[0,1]` the
  physical slice equals its cosine synthesis from `fullSourceCoeff`. -/
  realizes : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    intervalDomainLift (u t) x
      = ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x
  -- capstone discharge inputs (chemDiv leg):
  hGcont : ∀ n, Continuous (fun s => coupledChemDivSourceCoeffs p u s n)
  Mlift : ℝ
  hMlift : 0 ≤ Mlift
  hLiftCont : ∀ s ∈ Set.Icc (0 : ℝ) τ₀,
    ContinuousOn (coupledChemDivSourceLift p u s) (Set.Icc (0 : ℝ) 1)
  hLiftBd : ∀ s ∈ Set.Icc (0 : ℝ) τ₀, ∀ x ∈ Set.Icc (0 : ℝ) 1,
    |coupledChemDivSourceLift p u s x| ≤ Mlift
  Bv : ℕ → ℝ
  hBv : ∀ s k,
    |cosineCoeffs (intervalDomainLift ((fun s => u (s + τ₀)) s)) k| ≤ Bv k
  hBvnn : ∀ k, 0 ≤ Bv k
  hBvsum : Summable (fun k : ℕ => (1 + (k : ℝ)) * Bv k)
  hcont : ∀ n : ℤ, Continuous (embedModeFun (fun s => u (s + τ₀)) n)
  hgrad : ∀ τ : TimeDom T, Summable fun k : ℕ =>
    |(intervalNeumannResolverCoeff p ((fun s => u (s + τ₀)) τ.1) k).re|
      * ((k : ℝ) * Real.pi)
  h_flux_nbhd : ∀ (τ : TimeDom T), ∀ y ∈ Set.Ioo (0 : ℝ) 1,
    evalST τ (y : WA.Circ) (GWA.incl (by omega : (0:ℕ) ≤ 1)
      (chemFluxEWA μ ν p.β γ hμ
        (embedEWA (fun s => u (s + τ₀)) hBv hBvnn hBvsum hcont)))
      = ((chemFluxLifted p ((fun s => u (s + τ₀)) τ.1) y : ℝ) : ℂ)
  h_flux_diff : ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
    DifferentiableAt ℝ (chemFluxLifted p ((fun s => u (s + τ₀)) τ.1)) x
  /-- The logistic source's time-`C¹` package. -/
  logSrc : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u)

/-- **The full source coefficient's eigenvalue-ℓ¹ summability** for the record's
solution — the capstone leg discharged from the `cap*` fields, the heat/logistic
legs from the committed engines. -/
theorem SourceStrongSolutionData.eigenvalue_summable
    {T μ ν γ : ℝ} {hμ : 0 < μ} {p : CM2Params}
    (D : SourceStrongSolutionData T (μ := μ) (ν := ν) (γ := γ) hμ p) :
    Summable (fun n => unitIntervalCosineEigenvalue n *
      |fullSourceCoeff p D.u D.u₀cos D.t n|) := by
  have hchem := chemDivDuhamel_eigenvalue_summable (T := T) hμ p D.u D.htlo D.hthi
    D.hτ0 D.hτt D.hGcont D.hMlift D.hLiftCont D.hLiftBd D.Bv D.hBv D.hBvnn D.hBvsum
    D.hcont D.hgrad D.h_flux_nbhd D.h_flux_diff
  exact fullSourceCoeff_eigenvalue_summable p D.u D.u₀cos D.htlo D.hu0bd hchem D.logSrc

/-- **THE χ₀<0 STRONG-SOLUTION SPATIAL CLASSICAL SLICE.**

For the record's interior time `D.t`, the realized physical slice `u(t,·)` is, on
`[0,1]`, the cosine synthesis `Σₙ b̂ₙ(t) cos(nπx)` of the source-form full
coefficient, which is `ContDiff ℝ 2` with vanishing Neumann endpoint derivatives.

This is the spatial-regularity half of the source-form classical solution (the
time-regularity `u_t` and the PDE-from-mild step are separate, per the grade-1
architecture).  The chemotaxis-divergence summand's eigenvalue-ℓ¹ is supplied by the
capstone `chemDiv_eigenvalueSummableOn_uncond`; the realization is the one carried
field needing the gated heat eval bridge. -/
theorem SourceStrongSolutionData.isClassicalSpatialSlice
    {T μ ν γ : ℝ} {hμ : 0 < μ} {p : CM2Params}
    (D : SourceStrongSolutionData T (μ := μ) (ν := ν) (γ := γ) hμ p) :
    -- (i) `u(t,·)` synthesis is `C²` on the line (hence on `[0,1]`):
    ContDiff ℝ 2 (fun x => ∑' n, fullSourceCoeff p D.u D.u₀cos D.t n * cosineMode n x)
      -- (ii) Neumann at the left endpoint:
      ∧ deriv (fun x => ∑' n, fullSourceCoeff p D.u D.u₀cos D.t n * cosineMode n x) 0 = 0
      -- (iii) Neumann at the right endpoint:
      ∧ deriv (fun x => ∑' n, fullSourceCoeff p D.u D.u₀cos D.t n * cosineMode n x) 1 = 0
      -- (iv) the physical slice agrees with the synthesis on `[0,1]`:
      ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1,
          intervalDomainLift (D.u D.t) x
            = ∑' n, fullSourceCoeff p D.u D.u₀cos D.t n * cosineMode n x := by
  have hsum := D.eigenvalue_summable
  refine ⟨fullSourceCoeff_contDiff_two p D.u D.u₀cos hsum,
    fullSourceCoeff_neumann_left p D.u D.u₀cos hsum,
    fullSourceCoeff_neumann_right p D.u D.u₀cos hsum,
    D.realizes⟩

end ShenWork.EWA

#print axioms ShenWork.EWA.fullSourceCoeff_eigenvalue_summable
#print axioms ShenWork.EWA.chemDivDuhamel_eigenvalue_summable
#print axioms ShenWork.EWA.SourceStrongSolutionData.isClassicalSpatialSlice
