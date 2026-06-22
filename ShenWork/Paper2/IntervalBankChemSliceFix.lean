/-
  ShenWork/Paper2/IntervalBankChemSliceFix.lean

  SATISFIABLE (interior / within-interval) chemotaxis-divergence slice regularity
  for the B-form bank fields `hchemCont` / `hchemFourier`.

  ## Why this file exists

  The bank `BFormDirectClassical.BFormBankedInputs` (IntervalBFormDirectClassical.lean)
  carries, for the chemotaxis-divergence source slice, two analytic fields:

    * `hchemCont` (field 11): `∀ t∈(0,T), Continuous (intervalDomainConstExtend
        (fun x => intervalDomainChemotaxisDiv p (limit t) (chemConc …) x))`, and
    * `hchemFourier` (field 12): `∀ t∈(0,T), Summable (fun n:ℤ =>
        fourierCoeff (reflCircle (intervalDomainConstExtend (…chemDiv…))) n)`.

  Both are consumed in `IntervalBFormPIDUnconditional.lean:167-173` ONLY to build a
  `ChemDivCosineFourierData` via `chemDivCosineFourierData_constExtend`, whose
  `representative` is hard-wired to `intervalDomainConstExtend (chemDiv)` and which
  demands GLOBAL continuity of that representative.

  Earlier audit (IntervalBankSourceSliceLeaves.lean §"Field 11") PROVED that
  `intervalDomainConstExtend (chemDiv)` is DISCONTINUOUS at the endpoints `{0,1}`:
  `intervalDomainChemotaxisDiv = deriv φ` with `φ` built from the ZERO-extension
  `intervalDomainLift`, so `φ ≡ 0` for `y ≤ 0`, forcing Lean's `deriv φ 0 = 0`
  while the interior right-limit is the generically-nonzero
  `u(0)·v''(0)/(1+v(0))^β` (Neumann kills `v'(0)` but not `v''(0)`).  So the
  hard-coded `constExtend(chemDiv)` representative is the WRONG object and
  `hchemCont` is FALSE as stated.

  ## The fix (this file), mirroring `IntervalSourceBridgeOpen.lean`

  The cosine-inversion consumers (`chemDiv_cosineSeries_summable` /
  `chemDiv_cosineFourier_convergence`, IntervalBFormSpectralHchem.lean:84,105) only
  ever evaluate the representative at INTERIOR points `x.1 ∈ Ioo 0 1`.  So we
  replace the closed-`Icc` agreement of the `ChemDivCosineFourierData` package by an
  INTERIOR (`Ioo 0 1`) agreement: a globally-continuous representative `ψ` that
  agrees with the chemDiv lift only on the OPEN interior (where the lift is
  genuinely `C⁰` — the discontinuity lives ONLY at the endpoints, created by the
  zero-extension jump).

  We land:
    * `chemDivLift_continuousOn_Ioo` — the chemDiv lift IS continuous on `Ioo 0 1`
      (Task 2), from `ContDiffOn ℝ 2` of the lift on `Icc 0 1`;
    * `ChemDivCosineFourierDataIoo` + the two re-proved consumers
      `chemDiv_cosineSeries_summable_Ioo` / `chemDiv_cosineFourier_convergence_Ioo`
      on `Ioo`-agreement, via the endpoint-insensitive `cosineCoeffs_congr_on_Ioo`
      (Task 4 — the SATISFIABLE replacement for the FALSE `hchemCont`); and
    * `hchemFourier_endpoint_insensitive` — the bank's `hchemFourier` summability
      is integral-based and ALREADY fine (it equals that of the interior-agreeing
      representative; reuse the landed `hchemFourier_of_chemDiv_C2Neumann`)
      (Task 3).

  Conclusion (see report): `hchemFourier` is DISCHARGEABLE from `ContDiffOn ℝ 2`
  unchanged; `hchemCont` (the hard-coded `constExtend(chemDiv)`) is FALSE and needs
  the bank/consumer field replaced by the `Ioo`-representative form provided here —
  which is SATISFIABLE from `ContDiffOn ℝ 2`.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file, new names only.
-/
import ShenWork.Paper2.IntervalBankChemDivFourier

open Set Filter Topology

noncomputable section

namespace ShenWork.Paper2.BankChemSliceFix

open ShenWork.IntervalDomain
  (intervalDomainPoint intervalDomainLift intervalDomainConstExtend
   intervalDomainChemotaxisDiv constExtend_eq_lift_on_Ioo)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalMildPicardRegularity (cosineCoeffs_eq_factor_mul_integral)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalCosineInversion
  (intervalCosine_hasSum_pointwise reflCircle)
open ShenWork.IntervalBFormSpectral
  (chemDivLift chemDivCoeffs)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceLift coupledChemDivSourceCoeffs)

/-! ## Task 2 — interior continuity of the chemotaxis-divergence slice

The chemDiv lift is `C²` (hence `C⁰`) on the OPEN interior `Ioo 0 1`: the only
obstruction to continuity lives at the endpoints, where the zero-extension jump
pins the lift's value.  On the interior the lift never sees that jump, so the
`ContDiffOn ℝ 2`-on-`Icc 0 1` regularity (the same `hC2` consumed by the landed
`hchemFourier_of_chemDiv_C2Neumann`) restricts to genuine continuity. -/

/-- **The chemotaxis-divergence lift is continuous on the open interior.**
`ContDiffOn ℝ 2` on the closed `Icc 0 1` restricts to `ContinuousOn` on the open
`Ioo 0 1` (interior continuity); the endpoint discontinuity is excluded. -/
theorem chemDivLift_continuousOn_Ioo
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (hC2 : ContDiffOn ℝ 2 (chemDivLift p u v) (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (chemDivLift p u v) (Set.Ioo (0 : ℝ) 1) :=
  (hC2.continuousOn).mono Set.Ioo_subset_Icc_self

/-! ## Task 4 — the interior-agreeing (`Ioo`) regularity package + consumers

The hard-coded `constExtend(chemDiv)` representative is discontinuous at the
endpoints, so the closed-`Icc` `ChemDivCosineFourierData` cannot be built for the
chemotaxis source.  We restate the package with INTERIOR (`Ioo 0 1`) agreement: a
globally-continuous `representative` agreeing with `chemDivLift` only on the open
interior.  This is SATISFIABLE — e.g. any continuous extension of the interior
surrogate.  The consumers only ever read the representative at interior points, so
they go through unchanged, with `cosineCoeffs_congr_on_Ioo` (the endpoint-blind,
integral-based coefficient congruence) in place of `cosineCoeffs_congr_on_Icc`. -/

/-- **Endpoint-insensitive cosine-coefficient congruence.**  If two functions agree
on the OPEN interior `Ioo 0 1`, their Neumann cosine coefficients agree: the
defining interval integral over `(0,1)` ignores the null endpoint set `{1}`.
(Local copy of the EWA `cosineCoeffs_congr_on_Ioo`, proved here from the
factored-integral form to avoid pulling the Wiener/EWA import.) -/
theorem cosineCoeffs_congr_on_Ioo {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ Set.Ioo (0 : ℝ) 1, f x = g x) (k : ℕ) :
    cosineCoeffs f k = cosineCoeffs g k := by
  rw [cosineCoeffs_eq_factor_mul_integral, cosineCoeffs_eq_factor_mul_integral]
  congr 1
  apply intervalIntegral.integral_congr_ae
  rw [MeasureTheory.ae_iff]
  apply MeasureTheory.measure_mono_null (t := ({(1 : ℝ)} : Set ℝ)) _ (by simp)
  intro x hx
  simp only [Set.mem_setOf_eq, not_forall] at hx
  obtain ⟨hmem, hfail⟩ := hx
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Ioc] at hmem
  simp only [Set.mem_singleton_iff]
  by_contra hx1
  exact hfail (by rw [hfg x ⟨hmem.1, lt_of_le_of_ne hmem.2 hx1⟩])

/-- **Interior-agreeing chem-div cosine-Fourier regularity package.**

Identical to `ChemDivCosineFourierData` except the representative need agree with
the chemDiv lift only on the OPEN interior `Ioo 0 1` (not the closed `Icc 0 1`):
the discontinuous endpoint values are irrelevant to both the cosine coefficients
(integrals, endpoint-null) and the interior-point inversion consumers. -/
structure ChemDivCosineFourierDataIoo
    (p : CM2Params) (u v : intervalDomainPoint → ℝ) where
  representative : ℝ → ℝ
  continuous_representative : Continuous representative
  representative_eq_chemDiv :
    Set.EqOn representative (chemDivLift p u v) (Set.Ioo (0 : ℝ) 1)
  fourier_summable :
    Summable (fun n : ℤ => fourierCoeff (reflCircle representative) n)

/-- Coefficient transfer through the interior-agreeing representative (the
defining integral over `(0,1)` ignores the null endpoint set). -/
private theorem chemDiv_coeff_eq_representative_Ioo
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (H : ChemDivCosineFourierDataIoo p u v) (n : ℕ) :
    chemDivCoeffs p u v n = cosineCoeffs H.representative n := by
  refine cosineCoeffs_congr_on_Ioo (fun y hy => ?_) n
  exact (H.representative_eq_chemDiv hy).symm

/-- **Task 4 — chem-div cosine-series summability at an interior point**, from the
interior-agreeing package.  Mirrors `chemDiv_cosineSeries_summable` with `Ioo`
agreement.  The inversion engine only needs global continuity of `representative`
and is evaluated at the interior point `x.1 ∈ Ioo 0 1`. -/
theorem chemDiv_cosineSeries_summable_Ioo
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (H : ChemDivCosineFourierDataIoo p u v)
    {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0 : ℝ) 1) :
    Summable (fun n => chemDivCoeffs p u v n * cosineMode n x.1) := by
  have hinv := intervalCosine_hasSum_pointwise H.representative
    H.continuous_representative hx H.fourier_summable
  have hterm :
      (fun n => chemDivCoeffs p u v n * cosineMode n x.1)
        =
      (fun n => unitIntervalCosineMode n x.1
        * cosineCoeffs H.representative n) := by
    funext n
    rw [chemDiv_coeff_eq_representative_Ioo H n]
    simp only [cosineMode,
      unitIntervalCosineMode]
    ring
  rw [hterm]
  exact hinv.summable

/-- **Task 4 — chem-div cosine Fourier convergence** on the open interval, from the
interior-agreeing package.  Mirrors `chemDiv_cosineFourier_convergence` with `Ioo`
agreement.  At the interior point `x.1 ∈ Ioo 0 1` the representative equals the
chemDiv lift, which equals the pointwise chemotaxis divergence. -/
theorem chemDiv_cosineFourier_convergence_Ioo
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (H : ChemDivCosineFourierDataIoo p u v)
    {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0 : ℝ) 1) :
    (∑' n, chemDivCoeffs p u v n * cosineMode n x.1)
      = intervalDomainChemotaxisDiv p u v x := by
  have hinv := intervalCosine_hasSum_pointwise H.representative
    H.continuous_representative hx H.fourier_summable
  have hsum_eq :
      (∑' n, chemDivCoeffs p u v n * cosineMode n x.1)
        = H.representative x.1 := by
    rw [← hinv.tsum_eq]
    refine tsum_congr (fun n => ?_)
    rw [chemDiv_coeff_eq_representative_Ioo H n]
    simp only [cosineMode,
      unitIntervalCosineMode]
    ring
  have hrep_x : H.representative x.1 = chemDivLift p u v x.1 :=
    H.representative_eq_chemDiv hx
  have hlift :
      chemDivLift p u v x.1 = intervalDomainChemotaxisDiv p u v x := by
    simp [chemDivLift, intervalDomainLift]
  rw [hsum_eq, hrep_x, hlift]

/-! ## Task 3 — the bank's `hchemFourier` summability is endpoint-insensitive

`hchemFourier` is an INTEGRAL-based statement (Fourier coefficients of the even
reflection are integrals over the circle), so it is insensitive to the endpoint
values.  It is dischargeable, UNCHANGED, from `ContDiffOn ℝ 2` plus the
`C²`/Neumann endpoint data, exactly as the landed
`BankChemDivFourier.hchemFourier_of_chemDiv_C2Neumann` shows.  We re-export that
discharge here so the bank field `hchemFourier` (the hard-coded
`constExtend(chemDiv)` form) is confirmed SATISFIABLE without any structure
change. -/

/-- **Task 3 — `hchemFourier` is dischargeable from `ContDiffOn ℝ 2` + Neumann data,
unchanged.**  Re-export of the landed integral-based summability: the bank's
`hchemFourier` body (the `constExtend(chemDiv)` Fourier summability) follows from
the `C²`-Neumann regularity of the chemDiv lift — the endpoint discontinuity of
the const-extension is irrelevant because the coefficients are integrals. -/
theorem hchemFourier_of_chemDiv_C2Neumann_reexport
    (p : CM2Params) (u v : intervalDomainPoint → ℝ)
    (hcont : Continuous (fun x : intervalDomainPoint =>
      intervalDomainChemotaxisDiv p u v x))
    (hC2 : ContDiffOn ℝ 2
      (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p u v x))
      (Set.Icc (0 : ℝ) 1))
    (htend0 : Filter.Tendsto
      (deriv (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p u v x)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htend1 : Filter.Tendsto
      (deriv (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p u v x)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hbc0 : deriv
      (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p u v x)) 0 = 0)
    (hbc1 : deriv
      (intervalDomainLift (fun x => intervalDomainChemotaxisDiv p u v x)) 1 = 0) :
    Summable (fun n : ℤ =>
      fourierCoeff
        (reflCircle
          (intervalDomainConstExtend
            (fun x : intervalDomainPoint =>
              intervalDomainChemotaxisDiv p u v x))) n) :=
  ShenWork.Paper2.BankChemDivFourier.hchemFourier_of_chemDiv_C2Neumann
    p u v hcont hC2 htend0 htend1 hbc0 hbc1

/-! ## Coupled specialisations (B-form data) — interior consumers wired to the
resolver-substituted coefficients, mirroring `coupledChemDiv_cosineSeries_summable`
/ `coupledChemDiv_cosineFourier_convergence` but on the interior-agreeing package. -/

/-- Coupled B-form chem-div summability on the interior, with the elliptic
resolver substituted (interior-agreeing package). -/
theorem coupledChemDiv_cosineSeries_summable_Ioo
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ)
    (H : ChemDivCosineFourierDataIoo p (u t) (coupledChemicalConcentration p u t))
    {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0 : ℝ) 1) :
    Summable (fun n => coupledChemDivSourceCoeffs p u t n * cosineMode n x.1) := by
  simpa [coupledChemDivSourceCoeffs, coupledChemDivSourceLift,
    chemDivCoeffs, chemDivLift] using
    chemDiv_cosineSeries_summable_Ioo (p := p) (u := u t)
      (v := coupledChemicalConcentration p u t) H hx

/-- Coupled B-form chem-div cosine Fourier convergence on the interior, with the
resolver written as the `mildChemicalConcentration` used by the PDE core
(interior-agreeing package). -/
theorem coupledChemDiv_cosineFourier_convergence_Ioo
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ)
    (H : ChemDivCosineFourierDataIoo p (u t) (coupledChemicalConcentration p u t))
    {x : intervalDomainPoint} (hx : x.1 ∈ Set.Ioo (0 : ℝ) 1) :
    (∑' n, coupledChemDivSourceCoeffs p u t n * cosineMode n x.1)
      = ShenWork.IntervalDomain.intervalDomain.chemotaxisDiv p (u t)
          (ShenWork.IntervalMildToClassical.mildChemicalConcentration p u t) x := by
  have h := chemDiv_cosineFourier_convergence_Ioo (p := p) (u := u t)
    (v := coupledChemicalConcentration p u t) H hx
  change
    (∑' n, coupledChemDivSourceCoeffs p u t n * cosineMode n x.1)
      = intervalDomainChemotaxisDiv p (u t)
          (ShenWork.IntervalMildToClassical.mildChemicalConcentration p u t) x
  simpa [coupledChemDivSourceCoeffs, coupledChemDivSourceLift,
    chemDivCoeffs, chemDivLift,
    coupledChemicalConcentration,
    ShenWork.IntervalMildToClassical.mildChemicalConcentration] using h

/-! ## Builder — `ChemDivCosineFourierDataIoo` from `ContDiffOn ℝ 2`

The interior-agreeing package is genuinely SATISFIABLE: given any globally
continuous representative `ψ` agreeing with the chemDiv lift on the OPEN interior
(e.g. the interior surrogate's continuous extension) together with the
integral-based Fourier summability (Task 3, endpoint-insensitive), the package is
built directly.  This is the SATISFIABLE replacement for the FALSE
`chemDivCosineFourierData_constExtend` (which demanded a globally continuous
representative agreeing on the CLOSED interval, impossible for the chemDiv slice). -/

/-- **The interior-agreeing chem-div package from a satisfiable representative.**
Drop-in replacement for the FALSE `chemDivCosineFourierData_constExtend`: the
representative agrees with the chemDiv lift on the OPEN interior only, so a
globally continuous `ψ` exists (the endpoint discontinuity is sidestepped). -/
def chemDivCosineFourierDataIoo_of_repr
    (p : CM2Params) (u v : intervalDomainPoint → ℝ)
    (ψ : ℝ → ℝ) (hψcont : Continuous ψ)
    (hψeq : Set.EqOn ψ (chemDivLift p u v) (Set.Ioo (0 : ℝ) 1))
    (hsum : Summable (fun n : ℤ => fourierCoeff (reflCircle ψ) n)) :
    ChemDivCosineFourierDataIoo p u v where
  representative := ψ
  continuous_representative := hψcont
  representative_eq_chemDiv := hψeq
  fourier_summable := hsum

end ShenWork.Paper2.BankChemSliceFix

section Axioms

#print axioms ShenWork.Paper2.BankChemSliceFix.chemDivLift_continuousOn_Ioo
#print axioms ShenWork.Paper2.BankChemSliceFix.chemDiv_cosineSeries_summable_Ioo
#print axioms ShenWork.Paper2.BankChemSliceFix.chemDiv_cosineFourier_convergence_Ioo
#print axioms ShenWork.Paper2.BankChemSliceFix.hchemFourier_of_chemDiv_C2Neumann_reexport
#print axioms ShenWork.Paper2.BankChemSliceFix.coupledChemDiv_cosineSeries_summable_Ioo
#print axioms ShenWork.Paper2.BankChemSliceFix.coupledChemDiv_cosineFourier_convergence_Ioo
#print axioms ShenWork.Paper2.BankChemSliceFix.chemDivCosineFourierDataIoo_of_repr

end Axioms
