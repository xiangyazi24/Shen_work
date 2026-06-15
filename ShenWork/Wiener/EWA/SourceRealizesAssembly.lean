import ShenWork.Wiener.EWA.SourceDuhamelCoeffIdentity
import ShenWork.Wiener.EWA.SourceClassicalExistence
import ShenWork.Wiener.EWA.SourceCenterFloorHeat
import ShenWork.Wiener.EWA.GrowthEvenReal
import ShenWork.Wiener.EWA.WLEvenReal

/-!
# EWA capstone (χ₀<0 Route A′) — ASSEMBLING `realizes` for a Picard fixed point

This file ASSEMBLES the `realizes` field of `SourceStrongSolutionData`
(`SourceClassicalExistence.lean:252`) for an actual source-form Picard fixed point
`u* = Φ(u*)` (`picardEWA`, `SourceFixedPoint.lean:53`), out of the committed pieces:

* the **heat bridge** `heatEWA_evalST_eq_cosineHeatValue` + the synthesis
  `cosineHeatSynthesis_eq_cosineHeatValue` (`HeatFloor.lean`);
* **Bridge B** `divDuhamelEWA_evalST_eq_cosineSynthesis` /
  `valDuhamelEWA_evalST_eq_cosineSynthesis` (`SourceDuhamelSynthesis.lean`);
* the **coefficient identities** `ewaCosCoeffAt_divDuhamel_eq_duhamelSpectral` /
  `ewaCosCoeffAt_valDuhamel_eq_duhamelSpectral` (`SourceDuhamelCoeffIdentity.lean`, G1/G2);
* the **parity closures** `chemFluxEWA_oddImag` / `growthEWA_evenReal` fed by the
  committed `FnegEWA_evenReal_Hyp_proved` (`WLEvenReal.lean`).

## What is DISCHARGED vs. CARRIED

DISCHARGED here (from the fixed-point equation): the LHS→`evalST` reduction, the
`incl`+`evalST` additive/scalar split into three legs, each leg's identification with its
cosine series, and the three-tsum merge into `∑ₙ fullSourceCoeff … n · cosineMode n x`.

CARRIED as named hypotheses (genuinely open in the current tree):
* `hER_star : EvenRealEWA u_star` — the fixed point's parity (Φ preserves even-real on a
  closed subspace, but proving it for the fixed point is a separate brick — circular here);
* `hsum`/`hmem` — the heat-datum coefficient summability + membership;
* `hfix` — the fixed-point equation;
* the **G1/G2 realization atoms** `w_chem`/`H_chem`/`hw_chem`,
  `w_log`/`H_log`/`hw_log` (the exact hypotheses of the committed coefficient identities).

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledChemDivSourceLift coupledLogisticSourceCoeffs
    coupledLogisticSourceLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Part 1 — per-leg summability of the cosine series. -/

/-- The heat series `n ↦ exp(−t·(nπ)²)·u₀cos n · cosineMode n x` is summable for
`t ≥ 0` and `|u₀cos|` summable: majorised by `|u₀cos|` (heat factor and cosine both
bounded by `1`). -/
theorem heatSeries_summable {u₀cos : ℕ → ℝ} (hsum : Summable (fun k => |u₀cos k|))
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    Summable (fun n : ℕ =>
      Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n x) := by
  refine Summable.of_norm_bounded hsum (fun n => ?_)
  have : (Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n) * cosineMode n x
      = (Real.exp (-t * ((n : ℝ) * Real.pi) ^ 2) * u₀cos n) * cosineMode n x := rfl
  rw [this]
  exact heatSynthesisTerm_norm_le u₀cos ht n x

/-- A cosine series `n ↦ c n · cosineMode n x` is summable whenever `|c|` is: cosine is
bounded by `1`. -/
theorem cosineSeries_summable {c : ℕ → ℝ} (hc : Summable (fun k => |c k|)) (x : ℝ) :
    Summable (fun n : ℕ => c n * cosineMode n x) := by
  refine Summable.of_norm_bounded hc (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hcos : |cosineMode n x| ≤ 1 := by
    unfold ShenWork.CosineSpectrum.cosineMode; exact Real.abs_cos_le_one _
  calc |c n| * |cosineMode n x| ≤ |c n| * 1 :=
        mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
    _ = |c n| := mul_one _

/-- **Intrinsic summability of an even-real EWA element's cosine coefficients.**  An
even-real grade-`0` EWA element has slice `ofCosineCoeffs (ewaCosCoeffAt F τ)`, so
`Summable |ewaCosCoeffAt F τ|` is free from `F.mem` (no analytic atom). -/
theorem ewaCosCoeffAt_abs_summable {F : EWA T 0} {τ : TimeDom T}
    (heven : ∀ n : ℤ, (sliceWA τ F).toFun (-n) = (sliceWA τ F).toFun n)
    (hreal : ∀ n : ℤ, ((sliceWA τ F).toFun n).im = 0) :
    Summable (fun k : ℕ => |ewaCosCoeffAt F τ k|) :=
  summable_abs_of_slice_eq (slice_eq_ofCosineCoeffs_of_even_real heven hreal)

/-! ### Part 2 — the three legs of `evalST (incl (Φ u*)) x`. -/

/-- The heat leg: `Re (evalST τ x (incl (heatEWA u₀E)))` is the heat cosine series. -/
theorem heat_leg {u₀cos : ℕ → ℝ} (hsum : Summable (fun k => |u₀cos k|))
    (hmem : MemW 1 (ofCosineCoeffs u₀cos)) (τ : TimeDom T) (x : ℝ) :
    (evalST τ ((x : ℝ) : WA.Circ)
        (GWA.incl (by omega : (0:ℕ) ≤ 1)
          (heatEWA (T := T) (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)))).re
      = ∑' n : ℕ,
          Real.exp (-(τ : ℝ) * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n x := by
  rw [heatEWA_evalST_eq_cosineHeatValue u₀cos hsum hmem τ x, Complex.ofReal_re,
    ← cosineHeatSynthesis_eq_cosineHeatValue u₀cos (τ : ℝ) x]
  rfl

/-! ### Part 3 — THE ASSEMBLY: `realizes` from a Picard fixed point. -/

/-- **THE `realizes` ASSEMBLY.**  For a source-form Picard fixed point
`u* = picardEWA p p.μ p.ν p.γ p.hμ hT u₀E u*` with `u₀E = ⟨ofCosineCoeffs u₀cos, hmem⟩`,
the realized real-space slice equals its full cosine synthesis on `[0,1]`:
`intervalDomainLift (realSlice u* t) x = Σₙ fullSourceCoeff p (realSlice u*) u₀cos t n · cos`.

The heat leg closes via `heatEWA_evalST_eq_cosineHeatValue`; the chemDiv/logistic Duhamel
legs via Bridge B + the committed coefficient identities (G1/G2); the three cosine series
merge by `tsum_add` + `tsum_const_mul`. -/
theorem realizes_of_picardFixedPoint (p : CM2Params) (u₀cos : ℕ → ℝ)
    (hsum : Summable (fun k => |u₀cos k|)) (hmem : MemW 1 (ofCosineCoeffs u₀cos))
    (hT : (0 : ℝ) ≤ T) (u_star : EWA T 1)
    (hfix : u_star = picardEWA p p.μ p.ν p.γ p.hμ hT
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1) u_star)
    (hER_star : EvenRealEWA u_star)
    (w_chem : ℝ → intervalDomainPoint → ℝ)
    (H_chem : EWARealizesOn T 0 (chemDivEWA p.μ p.ν p.γ p.hμ p u_star) w_chem)
    (hw_chem : ∀ s, intervalDomainLift (w_chem s)
      = coupledChemDivSourceLift p (realSlice u_star) s)
    (w_log : ℝ → intervalDomainPoint → ℝ)
    (H_log : EWARealizesOn T 0
      (GWA.incl (by omega : (0 : ℕ) ≤ 1) (growthEWA p.α p.a p.b u_star)) w_log)
    (hw_log : ∀ s, intervalDomainLift (w_log s)
      = coupledLogisticSourceLift p (realSlice u_star) s)
    (t : ℝ) (htlo : 0 < t) (hthi : t ≤ T) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x := by
  intro x hx
  have ht : t ∈ Set.Icc (0 : ℝ) T := ⟨htlo.le, hthi⟩
  set τ : TimeDom T := ⟨t, ht⟩ with hτ
  -- abbreviations for the three flux/heat building blocks
  set Heat : EWA T 1 := heatEWA (T := T) (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1) with hHeat
  set Chem : EWA T 1 := chemFluxEWA p.μ p.ν p.β p.γ p.hμ u_star with hChem
  set Grow : EWA T 1 := growthEWA p.α p.a p.b u_star with hGrow
  -- STEP 1 — LHS → evalST.re
  have hlift : intervalDomainLift (realSlice u_star t) x
      = (evalST τ ((x : ℝ) : WA.Circ)
          (GWA.incl (by omega : (0:ℕ) ≤ 1) u_star)).re := by
    rw [intervalDomainLift, dif_pos hx]
    show realSlice u_star t ⟨x, hx⟩ = _
    rw [realSlice, dif_pos ht]
  -- STEP 2 — substitute hfix and split via incl + evalST additivity / scalar.
  have hsplit : (evalST τ ((x : ℝ) : WA.Circ)
        (GWA.incl (by omega : (0:ℕ) ≤ 1) u_star)).re
      = (evalST τ ((x : ℝ) : WA.Circ)
            (GWA.incl (by omega : (0:ℕ) ≤ 1) Heat)).re
        + (-p.χ₀) * (evalST τ ((x : ℝ) : WA.Circ)
            (GWA.incl (by omega : (0:ℕ) ≤ 1) (divDuhamelEWA hT Chem))).re
        + (evalST τ ((x : ℝ) : WA.Circ)
            (GWA.incl (by omega : (0:ℕ) ≤ 1) (valDuhamelEWA hT Grow))).re := by
    conv_lhs => rw [hfix]
    rw [picardEWA]
    -- incl of the sum splits
    have hadd1 : GWA.incl (by omega : (0:ℕ) ≤ 1)
          (Heat + ((-p.χ₀ : ℝ) : ℂ) • divDuhamelEWA hT Chem + valDuhamelEWA hT Grow)
        = GWA.incl (by omega : (0:ℕ) ≤ 1)
            (Heat + ((-p.χ₀ : ℝ) : ℂ) • divDuhamelEWA hT Chem)
          + GWA.incl (by omega : (0:ℕ) ≤ 1) (valDuhamelEWA hT Grow) := by
      rw [← GWA.gIncl_apply, map_add, GWA.gIncl_apply, GWA.gIncl_apply]
    have hadd2 : GWA.incl (by omega : (0:ℕ) ≤ 1)
          (Heat + ((-p.χ₀ : ℝ) : ℂ) • divDuhamelEWA hT Chem)
        = GWA.incl (by omega : (0:ℕ) ≤ 1) Heat
          + GWA.incl (by omega : (0:ℕ) ≤ 1) (((-p.χ₀ : ℝ) : ℂ) • divDuhamelEWA hT Chem) := by
      rw [← GWA.gIncl_apply, map_add, GWA.gIncl_apply, GWA.gIncl_apply]
    have hsmul : GWA.incl (by omega : (0:ℕ) ≤ 1) (((-p.χ₀ : ℝ) : ℂ) • divDuhamelEWA hT Chem)
        = ((-p.χ₀ : ℝ) : ℂ) • GWA.incl (by omega : (0:ℕ) ≤ 1) (divDuhamelEWA hT Chem) := by
      rw [← GWA.gIncl_apply, map_smul, GWA.gIncl_apply]
    rw [hadd1, (evalST τ ((x : ℝ) : WA.Circ)).map_add, Complex.add_re, hadd2,
      (evalST τ ((x : ℝ) : WA.Circ)).map_add, Complex.add_re, hsmul,
      evalST_smul, Complex.re_ofReal_mul]
  have hτt : ((τ : ℝ)) = t := rfl
  -- STEP 3 — the three legs as cosine series.
  -- HEAT
  have hheat := heat_leg (T := T) hsum hmem τ x
  rw [hτt] at hheat
  -- CHEMDIV (Bridge B + G1)
  have hBchem : OddImagEWA Chem :=
    chemFluxEWA_oddImag FnegEWA_evenReal_Hyp_proved p.hμ hER_star
  have hchem : (evalST τ ((x : ℝ) : WA.Circ)
        (GWA.incl (by omega : (0:ℕ) ≤ 1) (divDuhamelEWA hT Chem))).re
      = ∑' n : ℕ,
          duhamelSpectralCoeff (coupledChemDivSourceCoeffs p (realSlice u_star)) t n
            * cosineMode n x := by
    rw [divDuhamelEWA_evalST_eq_cosineSynthesis hT hBchem τ x, Complex.ofReal_re]
    refine tsum_congr (fun n => ?_)
    rw [ewaCosCoeffAt_divDuhamel_eq_duhamelSpectral p.hμ p u_star hT τ w_chem
      H_chem hw_chem n]
  -- LOGISTIC (Bridge B + G2)
  have hElog : EvenRealEWA Grow :=
    growthEWA_evenReal FnegEWA_evenReal_Hyp_proved hER_star
  have hlog : (evalST τ ((x : ℝ) : WA.Circ)
        (GWA.incl (by omega : (0:ℕ) ≤ 1) (valDuhamelEWA hT Grow))).re
      = ∑' n : ℕ,
          duhamelSpectralCoeff (coupledLogisticSourceCoeffs p (realSlice u_star)) t n
            * cosineMode n x := by
    rw [valDuhamelEWA_evalST_eq_cosineSynthesis hT hElog τ x, Complex.ofReal_re]
    refine tsum_congr (fun n => ?_)
    rw [ewaCosCoeffAt_valDuhamel_eq_duhamelSpectral p u_star hT τ w_log H_log hw_log n]
  -- STEP 4 — merge the three tsums.
  -- per-leg summabilities
  have hsumH : Summable (fun n : ℕ =>
      Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n x) :=
    heatSeries_summable hsum htlo.le x
  -- chemDiv leg: |duhamelSpectralCoeff| summable, intrinsic via Bridge B parity + G1.
  have hERchem : EvenRealEWA (GWA.incl (by omega : (0:ℕ) ≤ 1) (divDuhamelEWA hT Chem)) :=
    (hBchem.divDuhamelEWA hT).incl (by omega)
  have habsC : Summable (fun n : ℕ =>
      |duhamelSpectralCoeff (coupledChemDivSourceCoeffs p (realSlice u_star)) t n|) := by
    refine (ewaCosCoeffAt_abs_summable (fun n => hERchem.even τ n)
      (fun n => hERchem.real τ n)).congr (fun n => ?_)
    rw [ewaCosCoeffAt_divDuhamel_eq_duhamelSpectral p.hμ p u_star hT τ w_chem
      H_chem hw_chem n]
  have hsumC : Summable (fun n : ℕ =>
      duhamelSpectralCoeff (coupledChemDivSourceCoeffs p (realSlice u_star)) t n
        * cosineMode n x) := cosineSeries_summable habsC x
  -- logistic leg: same, via Bridge B parity + G2.
  have hERlog : EvenRealEWA (GWA.incl (by omega : (0:ℕ) ≤ 1) (valDuhamelEWA hT Grow)) :=
    (hElog.valDuhamelEWA hT).incl (by omega)
  have habsL : Summable (fun n : ℕ =>
      |duhamelSpectralCoeff (coupledLogisticSourceCoeffs p (realSlice u_star)) t n|) := by
    refine (ewaCosCoeffAt_abs_summable (fun n => hERlog.even τ n)
      (fun n => hERlog.real τ n)).congr (fun n => ?_)
    rw [ewaCosCoeffAt_valDuhamel_eq_duhamelSpectral p u_star hT τ w_log H_log hw_log n]
  have hsumL : Summable (fun n : ℕ =>
      duhamelSpectralCoeff (coupledLogisticSourceCoeffs p (realSlice u_star)) t n
        * cosineMode n x) := cosineSeries_summable habsL x
  -- the χ₀-scaled chemDiv series is summable too
  have hsumCχ : Summable (fun n : ℕ =>
      (-p.χ₀) * (duhamelSpectralCoeff (coupledChemDivSourceCoeffs p (realSlice u_star)) t n
        * cosineMode n x)) := hsumC.mul_left _
  rw [hlift, hsplit, hheat, hchem, hlog]
  -- RHS: expand fullSourceCoeff and split tsum
  have hrhs : (∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x)
      = (∑' n : ℕ,
          Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n x)
        + (∑' n : ℕ, (-p.χ₀) *
            (duhamelSpectralCoeff (coupledChemDivSourceCoeffs p (realSlice u_star)) t n
              * cosineMode n x))
        + (∑' n : ℕ,
            duhamelSpectralCoeff (coupledLogisticSourceCoeffs p (realSlice u_star)) t n
              * cosineMode n x) := by
    rw [← hsumH.tsum_add hsumCχ, ← (hsumH.add hsumCχ).tsum_add hsumL]
    refine tsum_congr (fun n => ?_)
    unfold fullSourceCoeff; ring
  rw [hrhs, tsum_mul_left]

end ShenWork.EWA

#print axioms ShenWork.EWA.realizes_of_picardFixedPoint
