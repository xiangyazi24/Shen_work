/-
  ShenWork/Wiener/EWA/SourceHchemInvDirect.lean

  **χ₀<0 — DIRECT discharge of the `hchemInv` member carried by
  `realSlice_reducedCore` (SourceReducedCore.lean:101), with NO `C³`/`C⁴`
  bootstrap.**

  The reduced core carries, per interior point, the chemotaxis-divergence
  cosine-inversion identity

    `hchemInv` : `∑ₙ coupledChemDivSourceCoeffs p u t n · cos = chemotaxis div`,

  for `u = realSlice u_star`.  The committed analytic primitive that produces it,
  `chemDiv_source_inversion` (SourceInversion.lean), consumes:

  * a CONTINUOUS surrogate `g` agreeing on `[0,1]` with the chem source lift, and
  * the `ℓ¹` `ℤ`-Fourier summability of `reflCircle g`.

  The prior discharge (`realSlice_hchemInv_of_C2Neumann`,
  SourceInversionDischarge.lean) routed the Fourier `ℓ¹` through the `C²`-Neumann
  embedding `hchemFourier_of_chemDiv_C2Neumann`, which forces a `C³`/`C⁴`
  source-regularity residual the banked `C²` atoms cannot produce
  (`realSlice_hchemInv_C2Neumann_residual`, SourceSliceC2Neumann.lean:312).

  That residual is ARTIFACTUAL.  The inversion engine needs ONLY the `reflCircle`
  Fourier `ℓ¹` of a continuous surrogate, and that follows DIRECTLY from the
  banked Wiener-algebra `sourceEnvelope` of `chemDivEWA`:

  * surrogate `g := intervalDomainConstExtend (chem-div slice)` — continuous via
    `constExtend_continuous`, agreeing with `coupledChemDivSourceLift` on `[0,1]`
    via `constExtend_eq_lift_on_Icc`;
  * `cosineCoeffs g n = coupledChemDivSourceCoeffs p u t n` via
    `cosineCoeffs_constExtend_eq_lift` (constExtend ↔ lift) and the `def` of the
    coupled coefficients;
  * the cosine `ℓ¹` `Summable (fun n => |cosineCoeffs g n|)` from the BANKED
    `sourceEnvelope_summable (chemDivEWA …)` dominating
    `|coupledChemDivSourceCoeffs p u t n|` through the carried envelope hypothesis
    `h_coeff` — the SAME envelope-domination feeder
    `chemDiv_eigenvalueSummableOn_of_EWA` carries at the realSlice call site;
  * the `reflCircle` Fourier `ℓ¹` from the cosine `ℓ¹` via
    `fourierCoeff_reflCircle_summable_of_cosineCoeff_abs` (full-circle variant,
    fed the global continuity of `g`).

  So the `C³`/`C⁴` is eliminated: `hchemInv` closes FULLY from banked data.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceInversion
import ShenWork.Wiener.EWA.ChemDivSourceAssembly
import ShenWork.Wiener.EWA.SourceClassicalExistence
import ShenWork.Paper2.IntervalDomainPdeUWiring
import ShenWork.PDE.IntervalDomainContinuousExtension

noncomputable section

namespace ShenWork.EWA

open Set Filter Topology
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain
  (intervalDomainPoint intervalDomainLift intervalDomainConstExtend
   intervalDomainChemotaxisDiv constExtend_eq_lift_on_Icc constExtend_continuous
   cosineCoeffs_constExtend_eq_lift)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalCosineInversion (reflCircle)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceLift coupledChemDivSourceCoeffs coupledChemicalConcentration)

variable {T : ℝ}

/-! ### The chem-source cosine `ℓ¹`, from the banked Wiener-algebra envelope. -/

/-- **Chem-source cosine-`ℓ¹` from the banked `sourceEnvelope`.**

The cosine coefficients of the continuous constant-extension surrogate of the
chem-div slice at time `t` are absolutely summable.  Proof: the surrogate's cosine
coefficients equal `coupledChemDivSourceCoeffs p u t n` (constExtend ↔ lift), which
are dominated in absolute value by the banked, summable Wiener-algebra
`sourceEnvelope (chemDivEWA μ ν γ hμ p U)` (carried hypothesis `h_coeff`), so the
comparison `Summable.of_nonneg_of_le` against `sourceEnvelope_summable` closes it. -/
theorem realSlice_chemSource_cosineCoeff_abs_summable
    {μ ν γ : ℝ} (hμ : 0 < μ)
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (U : EWA T 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (h_coeff : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
        |coupledChemDivSourceCoeffs p u s n|
          ≤ sourceEnvelope (chemDivEWA μ ν γ hμ p U) n) :
    Summable (fun n : ℕ =>
      |cosineCoeffs (intervalDomainConstExtend
        (fun x => intervalDomainChemotaxisDiv p (u t)
          (coupledChemicalConcentration p u t) x)) n|) := by
  -- the surrogate's cosine coefficients are `coupledChemDivSourceCoeffs p u t n`
  have hcoeff_eq : ∀ n : ℕ,
      cosineCoeffs (intervalDomainConstExtend
        (fun x => intervalDomainChemotaxisDiv p (u t)
          (coupledChemicalConcentration p u t) x)) n
        = coupledChemDivSourceCoeffs p u t n := by
    intro n
    rw [coupledChemDivSourceCoeffs, coupledChemDivSourceLift,
      cosineCoeffs_constExtend_eq_lift]
  -- dominate by the banked summable envelope and compare
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
    (sourceEnvelope_summable (chemDivEWA μ ν γ hμ p U))
  rw [hcoeff_eq n]
  exact h_coeff t ht n

/-! ### `hchemInv` — chemotaxis-divergence inversion, DIRECTLY from banked data. -/

/-- **`hchemInv` of the `pde_u` family, discharged DIRECTLY from banked data.**

For each interior time `t ∈ Ioo 0 T` the chem-div source cosine series inverts to
the physical chemotaxis divergence.  Inputs are EXACTLY the banked feeders the
realSlice call site already carries:

* `hcont` — continuity of the chem-div slice per interior `t` (the surrogate's
  continuity hypothesis, already banked for the eval/realization bricks);
* `h_coeff` — the Wiener-algebra `sourceEnvelope` domination of the chem
  coefficients (the SAME feeder `chemDiv_eigenvalueSummableOn_of_EWA` carries).

The continuous surrogate is `g := intervalDomainConstExtend (chem-div slice)`; it
agrees with `coupledChemDivSourceLift p u t` on `[0,1]`
(`constExtend_eq_lift_on_Icc`), and its `reflCircle` Fourier `ℓ¹` follows from the
cosine `ℓ¹` (`realSlice_chemSource_cosineCoeff_abs_summable`) through
`fourierCoeff_reflCircle_summable_of_cosineCoeff_abs`.  Feeding these to
`chemDiv_source_inversion` yields the inversion identity at every interior point —
with NO `C³`/`C⁴` regularity. -/
theorem realSlice_hchemInv_direct
    {μ ν γ : ℝ} (hμ : 0 < μ)
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (U : EWA T 1)
    (hcont : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Continuous (fun x : intervalDomainPoint =>
        intervalDomainChemotaxisDiv p (u t) (coupledChemicalConcentration p u t) x))
    (h_coeff : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
        |coupledChemDivSourceCoeffs p u s n|
          ≤ sourceEnvelope (chemDivEWA μ ν γ hμ p U) n) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      (∑' n, coupledChemDivSourceCoeffs p u t n * cosineMode n x.1)
        = intervalDomainChemotaxisDiv p (u t)
            (coupledChemicalConcentration p u t) x := by
  intro t ht x hx
  have htIcc : t ∈ Set.Icc (0 : ℝ) T := Set.Ioo_subset_Icc_self ht
  -- the continuous constant-extension surrogate of the chem-div slice
  refine chemDiv_source_inversion p u t
    (intervalDomainConstExtend (fun y => intervalDomainChemotaxisDiv p (u t)
      (coupledChemicalConcentration p u t) y))
    (constExtend_continuous (hcont t ht)) ?_ ?_ hx
  · -- surrogate agrees with the lift on `[0,1]` (lift defeq `coupledChemDivSourceLift`)
    intro y hy
    show intervalDomainConstExtend
        (fun z => intervalDomainChemotaxisDiv p (u t)
          (coupledChemicalConcentration p u t) z) y
      = coupledChemDivSourceLift p u t y
    exact constExtend_eq_lift_on_Icc hy
  · -- `reflCircle` Fourier `ℓ¹`, from the banked-envelope cosine `ℓ¹`
    exact ShenWork.Paper2.PdeUWiring.fourierCoeff_reflCircle_summable_of_cosineCoeff_abs
      (constExtend_continuous (hcont t ht))
      (realSlice_chemSource_cosineCoeff_abs_summable hμ p u U htIcc h_coeff)

/-! ### The exact `realSlice u_star` specialization carried by the reduced core. -/

/-- **`hchemInv` for `u = realSlice u_star`, DIRECTLY from banked data.**

The precise `hchemInv` shape carried by `realSlice_reducedCore`
(SourceReducedCore.lean:101), discharged with NO `C³`/`C⁴` bootstrap — only the
banked continuity (`hcont`) and Wiener-algebra `sourceEnvelope` domination
(`h_coeff`) of the chem coefficients of the realized slice. -/
theorem realSlice_hchemInv_direct_realSlice
    {μ ν γ : ℝ} (hμ : 0 < μ)
    (p : CM2Params) (u_star : EWA T 1) (U : EWA T 1)
    (hcont : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Continuous (fun x : intervalDomainPoint =>
        intervalDomainChemotaxisDiv p (realSlice u_star t)
          (coupledChemicalConcentration p (realSlice u_star) t) x))
    (h_coeff : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
        |coupledChemDivSourceCoeffs p (realSlice u_star) s n|
          ≤ sourceEnvelope (chemDivEWA μ ν γ hμ p U) n) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : intervalDomainPoint,
      x.1 ∈ Set.Ioo (0 : ℝ) 1 →
      (∑' n, coupledChemDivSourceCoeffs p (realSlice u_star) t n * cosineMode n x.1)
        = intervalDomainChemotaxisDiv p (realSlice u_star t)
            (coupledChemicalConcentration p (realSlice u_star) t) x :=
  realSlice_hchemInv_direct hμ p (realSlice u_star) U hcont h_coeff

end ShenWork.EWA

namespace ShenWork.EWA
section AxiomAudit
#print axioms realSlice_chemSource_cosineCoeff_abs_summable
#print axioms realSlice_hchemInv_direct
#print axioms realSlice_hchemInv_direct_realSlice
end AxiomAudit
end ShenWork.EWA
