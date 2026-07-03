/-
  ShenWork/Wiener/EWA/SourceVdFloorGeneric.lean

  **Uniform floor `1` for `1 + vdEWA U` for ANY EvenReal element U with
  positive floor — not just the heat center.**

  The existing `vdEWA_center_floor_heat_discharged` proves
  `UniformFloor (1 + vdEWA (heatEWA u₀E)) 1` specifically for the heat
  center. That theorem's proof passes through a PER-τ realization chain
  specialized to the heat track `unitIntervalCosineHeatValue τ c₀`.

  This theorem GENERALIZES: for ANY `U : EWA T 1` that is `EvenRealEWA`
  and has `UniformFloor U δ` with `δ > 0`, we get `UniformFloor (1 + vdEWA U) 1`.

  The proof is exactly the same chain: `realPowEWA_eval` gives the
  evaluation bridge, `slice_smul_realPow_eq_source` gives the slice
  coefficient identity, `evalST_gResolver_eq_resolverSynthesis_all` gives
  the resolver eval bridge, and `resolverSynthesis_nonneg_all` gives the
  nonnegativity from the nonneg source. The key inputs (`sourceFn_continuous`,
  `sourceFn_nonneg`, `sourceFn_coeff`) already work for generic `U`.

  **Impact:** This eliminates the ball-reduction approach to `hVdFloor`
  entirely. Instead of bounding `‖vdEWA u − vdEWA center‖ ≤ Lv·ρ`
  (which fails for large Wiener norms), we get floor `1` directly for
  any EvenReal ball element. The `hsmall` condition (Lv·ρ ≤ 1 − δv)
  is no longer needed.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceResolverSummabilityDischarge
import ShenWork.Wiener.EWA.SourceResolverFloor

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

theorem vdEWA_floor_of_evenReal (p : CM2Params) (U : EWA T 1)
    (hER_U : EvenRealEWA U) {δ : ℝ} (hδpos : 0 < δ)
    (hfloor : UniformFloor U δ) (hνpos : 0 ≤ p.ν) :
    UniformFloor (1 + vdEWA p.μ p.ν p.γ p.hμ U) 1 := by
  -- Step 1: the source term ν·U^γ is EvenReal.
  have hER : EvenRealEWA
      (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        ((p.ν : ℂ) • realPowEWA U p.γ)) :=
    ((realPowEWA_evenReal FnegEWA_evenReal_Hyp_proved
        hER_U p.γ).smul_real p.ν).incl (by omega)
  -- Step 2: U has real evaluations (from EvenReal).
  have hUReal :=
    evalST_incl_im_zero_of_evenReal hER_U
  -- Step 3: hRealize — evalST of the source equals ν·(realSlice U τ x)^γ.
  have hRealize : ∀ (τ : TimeDom T),
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        evalST τ (x : WA.Circ)
          (GWA.incl (by omega : (0 : ℕ) ≤ 1)
            ((p.ν : ℂ) • realPowEWA U p.γ))
        = ((p.ν *
            intervalDomainLift (realSlice U τ.1) x
              ^ p.γ : ℝ) : ℂ) := by
    intro τ x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hx.1.le, hx.2.le⟩
    have hincl_smul :
        GWA.incl (by omega : (0 : ℕ) ≤ 1)
          ((p.ν : ℂ) • realPowEWA U p.γ)
        = (p.ν : ℂ) •
            GWA.incl (by omega : (0 : ℕ) ≤ 1)
              (realPowEWA U p.γ) := by
      rw [← GWA.gIncl_apply, map_smul,
        GWA.gIncl_apply]
    rw [hincl_smul, evalST_smul]
    rw [realPowEWA_eval p.hγ.le hδpos hfloor
      hUReal τ (x : WA.Circ)]
    have hbase :=
      realSlice_evalST_realizes U τ x hxIcc
        (hUReal τ (x : WA.Circ))
    rw [hbase, Complex.ofReal_re]
    push_cast
    ring
  -- Step 4: hWslice — slice coefficient identity.
  have hWslice : ∀ τ : TimeDom T,
      (sliceWA τ (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        ((p.ν : ℂ) • realPowEWA U p.γ))).toFun
      = ofCosineCoeffs
          (resolverSourceReCoeff p (realSlice U τ.1)) :=
    fun τ => slice_smul_realPow_eq_source p
      (realSlice U) U τ hER (hRealize τ)
  -- Step 5: hsource — absolute summability of source coefficients.
  have hsource : ∀ τ : TimeDom T,
      ResolverSourceSummable p (realSlice U τ.1) :=
    fun τ => summable_abs_of_slice_eq (hWslice τ)
  -- Step 6: source function data (from existing generic lemmas).
  have hf_cont : ∀ τ : TimeDom T,
      Continuous (fun y : ℝ =>
        p.ν * (WA.evalAt (y : WA.Circ)
          (sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1) U))).re
            ^ p.γ) :=
    fun τ => sourceFn_continuous p U hδpos hfloor τ
  have hf_nonneg : ∀ (τ : TimeDom T) (y : ℝ),
      0 ≤ p.ν * (WA.evalAt (y : WA.Circ)
        (sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1) U))).re
          ^ p.γ :=
    fun τ y => sourceFn_nonneg p U hνpos hδpos hfloor τ y
  have hf_coeff : ∀ (τ : TimeDom T) (k : ℕ),
      cosineCoeffs (fun y : ℝ =>
        p.ν * (WA.evalAt (y : WA.Circ)
          (sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1) U))).re
            ^ p.γ) k
      = (intervalNeumannResolverSourceCoeff p
          (realSlice U τ.1) k).re :=
    fun τ k => sourceFn_coeff p U τ k
  have hf2 : ∀ τ : TimeDom T,
      Summable (fun k => (cosineCoeffs (fun y : ℝ =>
        p.ν * (WA.evalAt (y : WA.Circ)
          (sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1) U))).re
            ^ p.γ) k) ^ 2) := by
    intro τ
    have hcoeff : ∀ k, cosineCoeffs (fun y : ℝ =>
        p.ν * (WA.evalAt (y : WA.Circ)
          (sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1) U))).re
            ^ p.γ) k
      = resolverSourceReCoeff p (realSlice U τ.1) k := by
      intro k; simp only [hf_coeff τ k, resolverSourceReCoeff]
    simp_rw [hcoeff]
    exact summable_sq_of_summable_abs (hsource τ)
  -- Step 7: the resolver eval bridge + nonnegativity.
  intro τ x
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
    have hincl_one :
        GWA.incl (by omega : (0:ℕ) ≤ 1) (1 : EWA T 1) = 1 := by
      rw [← GWA.gIncl_apply, map_one]
    have hincl_add :
        GWA.incl (by omega : (0:ℕ) ≤ 1)
            (1 + vdEWA p.μ p.ν p.γ p.hμ U)
        = GWA.incl (by omega : (0:ℕ) ≤ 1) (1 : EWA T 1)
          + GWA.incl (by omega : (0:ℕ) ≤ 1)
              (vdEWA p.μ p.ν p.γ p.hμ U) := by
      rw [← GWA.gIncl_apply, map_add,
        GWA.gIncl_apply, GWA.gIncl_apply]
    have hvd :
        evalST τ (x : WA.Circ)
          (GWA.incl (by omega : (0:ℕ) ≤ 1)
            (vdEWA p.μ p.ν p.γ p.hμ U))
        = ((∑' k : ℕ,
              (intervalNeumannResolverCoeff p
                (realSlice U τ.1) k).re
              * cosineMode k x : ℝ) : ℂ) := by
      rw [vdEWA, vFieldEWA]
      exact evalST_gResolver_eq_resolverSynthesis_all
        p (realSlice U τ.1)
        ((p.ν : ℂ) • realPowEWA U p.γ)
        τ x (hsource τ) (hWslice τ)
    rw [hincl_add,
      (evalST τ (x : WA.Circ)).map_add,
      hincl_one,
      (evalST τ (x : WA.Circ)).map_one,
      hvd]
    rw [Complex.add_re, Complex.one_re,
      Complex.ofReal_re]
    have hR : 0 ≤ ∑' k : ℕ,
        (intervalNeumannResolverCoeff p
          (realSlice U τ.1) k).re
        * cosineMode k x :=
      resolverSynthesis_nonneg_all p (realSlice U τ.1)
        (hf_cont τ) (hf_nonneg τ) (hf_coeff τ)
        (hf2 τ) x
    linarith

end ShenWork.EWA

#print axioms ShenWork.EWA.vdEWA_floor_of_evenReal
