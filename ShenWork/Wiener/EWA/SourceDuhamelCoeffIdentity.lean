import ShenWork.Wiener.EWA.SourceDuhamelSynthesis
import ShenWork.Wiener.EWA.ChemDivEval
import ShenWork.Wiener.EWA.GrowthEvalBridge
import ShenWork.Wiener.EWA.SourceClassicalExistence
import ShenWork.PDE.IntervalDuhamelClosedC2
import ShenWork.PDE.IntervalCoupledSourceTimeC1

/-!
# EWA brick (χ₀<0 Route A′) — the DUHAMEL COEFFICIENT IDENTITY

The `realizes` field of the χ₀<0 source-form solution consumes, per mode `n`, the
identity that the EWA per-mode Duhamel coefficient extractor `ewaCosCoeffAt` of the
grade-dropped Duhamel element EQUALS the committed real-space spectral Duhamel
coefficient `duhamelSpectralCoeff`.

The whole content factors through ONE generic **interchange** lemma `R0`
(`ewaCosCoeffAt_duhamelEWA_eq_spectral`): the `±`-mode `Re`-extractor of the Duhamel
slice equals the spectral Duhamel integral whose integrand is the per-time
`±`-mode source extractor `srcCoeffAt`.  Mechanism: the slice of the Duhamel element is
the per-mode `duhFun` integral (`coeff_sliceWA_*DuhamelEWA`), its REAL kernel
`e^{−(τ−s)(nπ)²}` is identical for modes `±n` (`modeSq_neg`), so pulling the finite
`Re`-of-`±`-combination INSIDE the interval integral (`Re(∫)=∫Re` via
`Complex.reCLM`, `Re(real·z)=real·Re z`) lands the real per-mode integrand
`srcCoeffAt`.  Since `unitIntervalCosineEigenvalue n = (nπ)²` definitionally, the
result IS `duhamelSpectralCoeff srcCoeffAt τ n`.

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemDivSourceLift
  coupledChemDivSourceCoeffs coupledLogisticSourceLift coupledLogisticSourceCoeffs)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Part 1 — the per-time source extractor and the `duhFun.re` reduction. -/

/-- The per-time `±`-mode REAL source extractor of the per-mode integrand
`coef n · ext hT (B.toFun n) s`.  For `n = 0` it is the real part of the
`0`-mode product; for `n ≠ 0` it is the sum of the real parts of the `±n`
products — exactly the structure of `ewaCosCoeffAt` carried to the integrand. -/
noncomputable def srcCoeffAt (hT : 0 ≤ T) (B : EWA T 1) (coef : ℤ → ℂ)
    (s : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then (coef 0 * ext hT (B.toFun 0) s).re
  else (coef (n : ℤ) * ext hT (B.toFun (n : ℤ)) s).re
    + (coef (-(n : ℤ)) * ext hT (B.toFun (-(n : ℤ))) s).re

/-- **`Re`-through-interval-integral.**  For a continuous (hence interval-integrable)
ℂ-integrand, the real part commutes with the interval integral. -/
theorem re_intervalIntegral {f : ℝ → ℂ} {a b : ℝ} (hf : Continuous f) :
    (∫ s in a..b, f s).re = ∫ s in a..b, (f s).re := by
  have hi : IntervalIntegrable f MeasureTheory.volume a b :=
    hf.intervalIntegrable a b
  have := (ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hi).symm
  simpa using this

/-- **`duhFun.re` as a real spectral integral.**  The real part of the per-mode
Duhamel integral is the real interval integral of the real kernel times the real
part of the per-mode product.  Uses the realness of the kernel
(`duhKernel_ofReal`) and `Re(real·z)=real·Re z`, then `re_intervalIntegral`. -/
theorem duhFun_re_eq (y2 τ : ℝ) (coef : ℂ) {g : ℝ → ℂ} (hg : Continuous g) :
    (duhFun y2 coef g τ).re
      = ∫ s in (0:ℝ)..τ, Real.exp (-((τ - s) * y2)) * (coef * g s).re := by
  have hcont : Continuous fun s : ℝ =>
      Complex.exp (-((↑(τ - s)) * (↑y2))) * (coef * g s) := by fun_prop
  rw [duhFun, re_intervalIntegral hcont]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  rw [duhKernel_ofReal]
  rw [show (((Real.exp (-((τ - s) * y2)) : ℝ) : ℂ) * (coef * g s)).re
        = Real.exp (-((τ - s) * y2)) * (coef * g s).re from ?_]
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]

/-! ### Part 2 — R0, THE INTERCHANGE. -/

/-- **R0 (the interchange).**  For a Duhamel EWA element `DuhamelEWA hT B` with
per-mode spatial coefficient family `coef`, the `±`-mode `Re`-extractor of the
grade-dropped slice equals the committed spectral Duhamel coefficient of the
per-time source extractor `srcCoeffAt`.

`sliceFun` is the per-mode slice abbreviation supplied by
`coeff_sliceWA_*DuhamelEWA` (it is `duhFun ((nπ)²) (coef n) (ext hT (B.toFun n)) τ`),
passed as a hypothesis so that BOTH the value and divergence legs instantiate the
same interchange.  Continuity of every per-mode integrand `ext hT (B.toFun n)` is
the only analytic input, supplied by `ext_continuous`. -/
theorem ewaCosCoeffAt_duhamelEWA_eq_spectral (hT : 0 ≤ T) (B : EWA T 1)
    (coef : ℤ → ℂ) (D : EWA T 1) (τ : TimeDom T)
    (hslice : ∀ n : ℤ, (sliceWA τ D).toFun n
      = duhFun (((n : ℝ) * Real.pi) ^ 2) (coef n) (ext hT (B.toFun n)) (τ : ℝ))
    (n : ℕ) :
    ewaCosCoeffAt (GWA.incl (by omega : (0:ℕ) ≤ 1) D) τ n
      = duhamelSpectralCoeff (srcCoeffAt hT B coef) (τ : ℝ) n := by
  -- reduce `ewaCosCoeffAt (incl D)` to the slice of `D` (grade drop is identity)
  have hincl : ∀ m : ℤ,
      (sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1) D)).toFun m = (sliceWA τ D).toFun m :=
    fun m => coeff_sliceWA_incl (by omega) D τ m
  -- the spectral eigenvalue is `(nπ)²`
  have hlam : unitIntervalCosineEigenvalue n = ((n : ℝ) * Real.pi) ^ 2 := rfl
  unfold ewaCosCoeffAt duhamelSpectralCoeff srcCoeffAt
  by_cases hn : n = 0
  · subst hn
    simp only [↓reduceIte]
    rw [hincl 0, hslice 0, duhFun_re_eq _ _ _ (ext_continuous hT (B.toFun 0))]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    rw [hlam, neg_mul]; push_cast; ring
  · simp only [if_neg hn]
    rw [hincl (n : ℤ), hincl (-(n : ℤ)), hslice (n : ℤ),
      hslice (-(n : ℤ)), Complex.add_re]
    rw [show (((-n : ℤ) : ℝ) * Real.pi) ^ 2 = ((n : ℝ) * Real.pi) ^ 2 from modeSq_neg n]
    rw [duhFun_re_eq _ _ _ (ext_continuous hT (B.toFun (n : ℤ))),
      duhFun_re_eq _ _ _ (ext_continuous hT (B.toFun (-(n : ℤ))))]
    rw [← intervalIntegral.integral_add]
    · refine intervalIntegral.integral_congr (fun s _ => ?_)
      rw [hlam, neg_mul]; push_cast; ring
    · exact (Continuous.intervalIntegrable (by
        have := ext_continuous hT (B.toFun (n : ℤ)); fun_prop) _ _)
    · exact (Continuous.intervalIntegrable (by
        have := ext_continuous hT (B.toFun (-(n : ℤ))); fun_prop) _ _)

/-! ### Part 3 — G1/G2, the two leg instantiations of R0. -/

/-- **G1 (chemDiv leg).**  The EWA per-mode coefficient of the divergence-Duhamel
element of the chemotactic flux equals the committed real-space spectral Duhamel
coefficient of the realized chemDiv source.

DISCHARGED from R0: the per-mode slice (`coeff_sliceWA_divDuhamelEWA`, `coef = inπ`),
the interchange `R0`, the spectral-`∂ₓ` algebra `coef·chemFlux̂ₙ = chemDiv̂ₙ`
(`coeff_sliceWA_gDeriv`), and the coefficient bridge `ewaCosCoeffAt_eq_cosineCoeffs_of_eval`.
CARRIED as named atoms (genuinely uncommitted by the pointwise eval bridge): the
full-circle realization record `H` for `chemDivEWA`, and the lift-match `hw`
identifying its realized `w` with `coupledChemDivSourceLift p (realSlice U)`. -/
theorem ewaCosCoeffAt_divDuhamel_eq_duhamelSpectral
    {μ ν γ : ℝ} (hμ : 0 < μ) (p : CM2Params) (U : EWA T 1) (hT : 0 ≤ T)
    (τ : TimeDom T) (w : ℝ → intervalDomainPoint → ℝ)
    (H : EWARealizesOn T 0 (chemDivEWA μ ν γ hμ p U) w)
    (hw : ∀ s, intervalDomainLift (w s) = coupledChemDivSourceLift p (realSlice U) s)
    (n : ℕ) :
    ewaCosCoeffAt (GWA.incl (by omega : (0:ℕ) ≤ 1)
        (divDuhamelEWA hT (chemFluxEWA μ ν p.β γ hμ U))) τ n
      = duhamelSpectralCoeff (coupledChemDivSourceCoeffs p (realSlice U)) (τ : ℝ) n := by
  rw [ewaCosCoeffAt_duhamelEWA_eq_spectral hT (chemFluxEWA μ ν p.β γ hμ U)
      (fun m => Complex.I * ((m : ℝ) * Real.pi))
      (divDuhamelEWA hT (chemFluxEWA μ ν p.β γ hμ U)) τ
      (fun m => coeff_sliceWA_divDuhamelEWA hT (chemFluxEWA μ ν p.β γ hμ U) τ m) n]
  unfold duhamelSpectralCoeff
  refine intervalIntegral.integral_congr (fun s hs => ?_)
  have hsT : s ∈ Set.Icc (0:ℝ) T := by
    rw [Set.uIcc_of_le τ.2.1] at hs; exact ⟨hs.1, le_trans hs.2 τ.2.2⟩
  have hid : srcCoeffAt hT (chemFluxEWA μ ν p.β γ hμ U)
        (fun m => Complex.I * ((m : ℝ) * Real.pi)) s n
      = coupledChemDivSourceCoeffs p (realSlice U) s n := by
    have halg : srcCoeffAt hT (chemFluxEWA μ ν p.β γ hμ U)
          (fun m => Complex.I * ((m : ℝ) * Real.pi)) s n
        = ewaCosCoeffAt (chemDivEWA μ ν γ hμ p U) (Set.projIcc 0 T hT s) n := by
      unfold srcCoeffAt ewaCosCoeffAt
      have key : ∀ m : ℤ,
          Complex.I * ((m : ℝ) * Real.pi) * ext hT ((chemFluxEWA μ ν p.β γ hμ U).toFun m) s
            = (sliceWA (Set.projIcc 0 T hT s) (chemDivEWA μ ν γ hμ p U)).toFun m := by
        intro m; rw [chemDivEWA, coeff_sliceWA_gDeriv, ext_toFun_eq_slice, smul_eq_mul]
        push_cast; ring
      by_cases hn : n = 0
      · subst hn; rw [key 0]; norm_num
      · simp only [if_neg hn]; rw [key (n : ℤ), key (-(n : ℤ)), Complex.add_re]
    rw [halg, ewaCosCoeffAt_eq_cosineCoeffs_of_eval H]
    have hproj : (Set.projIcc 0 T hT s).1 = s := by rw [Set.projIcc_of_mem hT hsT]
    unfold coupledChemDivSourceCoeffs; rw [hproj, hw s]
  rw [hid]

/-- **G2 (logistic leg).**  The EWA per-mode coefficient of the value-Duhamel
element of the logistic growth term equals the committed real-space spectral
Duhamel coefficient of the realized logistic source.

DISCHARGED from R0: the per-mode slice (`coeff_sliceWA_valDuhamelEWA`, `coef = 1`),
the interchange `R0`, the trivial value algebra `1·growtĥₙ = growtĥₙ`, and the
coefficient bridge.  CARRIED as named atoms: the realization record `H` for
`incl growthEWA`, and the lift-match `hw` to `coupledLogisticSourceLift p (realSlice U)`. -/
theorem ewaCosCoeffAt_valDuhamel_eq_duhamelSpectral
    (p : CM2Params) (U : EWA T 1) (hT : 0 ≤ T)
    (τ : TimeDom T) (w : ℝ → intervalDomainPoint → ℝ)
    (H : EWARealizesOn T 0 (GWA.incl (by omega : (0 : ℕ) ≤ 1) (growthEWA p.α p.a p.b U)) w)
    (hw : ∀ s, intervalDomainLift (w s) = coupledLogisticSourceLift p (realSlice U) s)
    (n : ℕ) :
    ewaCosCoeffAt (GWA.incl (by omega : (0:ℕ) ≤ 1)
        (valDuhamelEWA hT (growthEWA p.α p.a p.b U))) τ n
      = duhamelSpectralCoeff (coupledLogisticSourceCoeffs p (realSlice U)) (τ : ℝ) n := by
  rw [ewaCosCoeffAt_duhamelEWA_eq_spectral hT (growthEWA p.α p.a p.b U)
      (fun _ => 1) (valDuhamelEWA hT (growthEWA p.α p.a p.b U)) τ
      (fun m => coeff_sliceWA_valDuhamelEWA hT (growthEWA p.α p.a p.b U) τ m) n]
  unfold duhamelSpectralCoeff
  refine intervalIntegral.integral_congr (fun s hs => ?_)
  have hsT : s ∈ Set.Icc (0:ℝ) T := by
    rw [Set.uIcc_of_le τ.2.1] at hs; exact ⟨hs.1, le_trans hs.2 τ.2.2⟩
  have hid : srcCoeffAt hT (growthEWA p.α p.a p.b U) (fun _ => 1) s n
      = coupledLogisticSourceCoeffs p (realSlice U) s n := by
    have halg : srcCoeffAt hT (growthEWA p.α p.a p.b U) (fun _ => 1) s n
        = ewaCosCoeffAt (GWA.incl (by omega : (0:ℕ) ≤ 1) (growthEWA p.α p.a p.b U))
            (Set.projIcc 0 T hT s) n := by
      unfold srcCoeffAt ewaCosCoeffAt
      have key : ∀ m : ℤ,
          (1 : ℂ) * ext hT ((growthEWA p.α p.a p.b U).toFun m) s
            = (sliceWA (Set.projIcc 0 T hT s)
                (GWA.incl (by omega : (0:ℕ) ≤ 1) (growthEWA p.α p.a p.b U))).toFun m := by
        intro m; rw [coeff_sliceWA_incl (by omega), ext_toFun_eq_slice, one_mul]
      by_cases hn : n = 0
      · subst hn; simp only [↓reduceIte]; rw [key 0]
      · simp only [if_neg hn]; rw [key (n : ℤ), key (-(n : ℤ)), Complex.add_re]
    rw [halg, ewaCosCoeffAt_eq_cosineCoeffs_of_eval H]
    have hproj : (Set.projIcc 0 T hT s).1 = s := by rw [Set.projIcc_of_mem hT hsT]
    unfold coupledLogisticSourceCoeffs; rw [hproj, hw s]
  rw [hid]

end ShenWork.EWA
