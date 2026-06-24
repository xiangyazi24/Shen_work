import ShenWork.Wiener.EWA.SourceChiNegUncond
import ShenWork.Wiener.EWA.SourceRealizesClean

/-!
# χ₀<0 EWA track — WIRING the 3 banked evalST atoms into the `realizes` slab

`SourceChiNegUncond.lean` PRODUCES, for the abstract Picard fixed point
`u_star : EWA T 1`, the three `evalST`-realization atoms that the prior closeout
carried as an "open frontier":

* `realSlice_evalST_realizes`  (`h_u`,         per `τ x`, on `Icc 0 1`),
* `realSlice_realPow_realizes` (`h_uα`,        per `τ x`, on `Icc 0 1`),
* `realSlice_flux_realizes`    (`h_flux_nbhd`, per `τ x`, on `Ioo 0 1`).

`SourceRealizesClean.lean`'s capstone `realizes_clean` consumes those three atoms
(in their `∀τ`/`∀x∈Icc`/`∀x∈Ioo` slab shapes) — alongside the parity-deriving
contraction data and the secondary regularity side-atoms — to deliver the slab
realization
`intervalDomainLift (realSlice u_star t) x = Σ fullSourceCoeff … cosineMode`.

This file is the WIRING step.  It packages the three banked per-point producers
into the exact slab shapes `realizes_clean` wants, with `EvenRealEWA u_star`
derived once from the carried contraction data (`picardEWA_evenReal_fixedPoint`),
so the resulting capstone `realizes_evalST_discharged` carries the three hard-core
`evalST` atoms **NO LONGER as hypotheses** — they are discharged internally from
the banked theorems.  What it still carries are:

* the contraction / fixed-point data (`hfix`/`hρ`/`hself`/`hLipQ`/`hLipG`/
  `hKnn`/`hK`/`hmem_star`) — the parity + fixed-point inputs;
* the uniform floor `UniformFloor u_star δ` and the resolver-source analytic data
  (`hsum`/`hgrad`/`hμle1` + the nonneg-continuous source family `f`) that the
  banked `realSlice_flux_realizes` requires (the framework-wide O1 positivity
  input, NOT an `hfp` and NOT an embed form);
* the two secondary regularity side-atoms `h_flux_diff` / `h_src_cont_chem` /
  `h_src_cont_log` still carried by `realizes_clean` (these are the named
  secondary residuals, untouched here).

The three hard-core `evalST` realization atoms — the genuine χ₀<0 frontier the
prior session wrongly called irreducible — are now fully INTERNAL.

No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/

open scoped BigOperators
open Set Metric
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.PDE
  (intervalNeumannResolverCoeff intervalNeumannResolverSourceCoeff)
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Slab packaging of the three banked per-point evalST producers. -/

/-- **`h_u` slab — DISCHARGED.**  The base realization atom for every `τ` and every
`x ∈ Icc 0 1`, from the banked per-point producer `realSlice_evalST_realizes` with
reality supplied by `EvenRealEWA u_star`. -/
theorem realSlice_h_u_slab {u_star : EWA T 1} (hER : EvenRealEWA u_star) :
    ∀ (τ : TimeDom T), ∀ x ∈ Set.Icc (0 : ℝ) 1,
      evalST τ x (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)
        = (intervalDomainLift (realSlice u_star τ.1) x : ℂ) := by
  intro τ x hx
  exact realSlice_evalST_realizes u_star τ x hx
    (evalST_incl_im_zero_of_evenReal hER τ (x : WA.Circ))

/-- **`h_uα` slab — DISCHARGED.**  The power-factor realization atom for every `τ`
and every `x ∈ Icc 0 1`, from the banked per-point producer
`realSlice_realPow_realizes`. -/
theorem realSlice_h_uα_slab (p : CM2Params) {u_star : EWA T 1} {δ : ℝ}
    (hδpos : 0 < δ) (hER : EvenRealEWA u_star) (hfloor : UniformFloor u_star δ)
    (hα : 0 ≤ p.α) :
    ∀ (τ : TimeDom T), ∀ x ∈ Set.Icc (0 : ℝ) 1,
      evalST τ x (GWA.incl (by omega : (0 : ℕ) ≤ 1) (realPowEWA u_star p.α))
        = ((intervalDomainLift (realSlice u_star τ.1) x ^ p.α : ℝ) : ℂ) := by
  intro τ x hx
  exact realSlice_realPow_realizes p u_star hδpos hER hfloor hα τ x hx

/-- **`h_flux_nbhd` slab — DISCHARGED.**  The chemotaxis-flux realization atom for
every `τ` and every `y ∈ Ioo 0 1`, from the banked per-point producer
`realSlice_flux_realizes`.  Carries exactly the no-embed resolver-source datum the
banked producer needs. -/
theorem realSlice_h_flux_slab (p : CM2Params) {u_star : EWA T 1} {δ : ℝ}
    (hδpos : 0 < δ) (hβpos : 0 < p.β) (hER : EvenRealEWA u_star)
    (hfloor : UniformFloor u_star δ)
    (hsum : ∀ σ : TimeDom T, ResolverSourceSummable p (realSlice u_star σ.1))
    (hgrad : ∀ (τ : TimeDom T),
      Summable fun k : ℕ =>
        |(intervalNeumannResolverCoeff p (realSlice u_star τ.1) k).re| * ((k : ℝ) * Real.pi))
    (hμle1 : p.μ ≤ 1)
    (f : ℝ → ℝ → ℝ) (hf_cont : ∀ σ : TimeDom T, Continuous (f σ.1))
    (hf_nonneg : ∀ (σ : TimeDom T) (y : ℝ), 0 ≤ f σ.1 y)
    (hf_coeff : ∀ (σ : TimeDom T) (k : ℕ),
      cosineCoeffs (f σ.1) k = (intervalNeumannResolverSourceCoeff p (realSlice u_star σ.1) k).re)
    (hâ : ∀ σ : TimeDom T, Summable (fun k => (cosineCoeffs (f σ.1) k) ^ 2)) :
    ∀ (τ : TimeDom T), ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (y : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (chemFluxEWA p.μ p.ν p.β p.γ p.hμ u_star))
        = ((chemFluxLifted p (realSlice u_star τ.1) y : ℝ) : ℂ) := by
  intro τ y hy
  exact realSlice_flux_realizes p u_star hδpos hβpos hER hfloor τ y hy
    hsum (hgrad τ) hμle1 f hf_cont hf_nonneg hf_coeff hâ

/-! ### The slab realization with the three evalST atoms discharged internally. -/

/-- **The χ₀<0 `realizes` slab — three hard-core evalST atoms DISCHARGED.**

`realizes_clean` delivers the slab realization but carries `h_flux_nbhd`/`h_u`/
`h_uα` as hypotheses.  Here those three are supplied INTERNALLY from the banked
producers (`realSlice_evalST_realizes`/`realSlice_realPow_realizes`/
`realSlice_flux_realizes`, via the slab packagers above), with `EvenRealEWA u_star`
derived once from the carried contraction data.

The result carries the contraction/fixed-point data, the uniform floor + the
no-embed resolver-source datum, the spectral floor `p.μ ≤ 1`, and ONLY the two
remaining secondary regularity side-atoms (`h_flux_diff`/`h_src_cont_chem`/
`h_src_cont_log`).  The hard-core `evalST` frontier is gone. -/
theorem realizes_evalST_discharged (p : CM2Params) (u₀cos : ℕ → ℝ)
    (hsumc : Summable (fun k => |u₀cos k|)) (hmem : MemW 1 (ofCosineCoeffs u₀cos))
    (hT : (0 : ℝ) ≤ T)
    {ρ L_Q L_G δ : ℝ} (hδpos : 0 < δ) (u_star : EWA T 1)
    (hfix : u_star = picardEWA p p.μ p.ν p.γ p.hμ hT
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1) u_star)
    (hρ : 0 ≤ ρ)
    (hself : MapsTo
      (picardEWA p p.μ p.ν p.γ p.hμ hT (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1))
      (Metric.closedBall (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ)
      (Metric.closedBall (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ))
    (hLipQ : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ‖chemFluxEWA p.μ p.ν p.β p.γ p.hμ a - chemFluxEWA p.μ p.ν p.β p.γ p.hμ b‖
        ≤ L_Q * ‖a - b‖)
    (hLipG : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ,
      ‖growthEWA p.α p.a p.b a - growthEWA p.α p.a p.b b‖ ≤ L_G * ‖a - b‖)
    (hKnn : (0 : ℝ) ≤ |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T)
    (hK : |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T < 1)
    (hmem_star : u_star ∈ Metric.closedBall (heatEWA (T := T)
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ)
    -- floor + no-embed resolver-source datum the banked flux/power producers need:
    (hβpos : 0 < p.β) (hαnn : 0 ≤ p.α) (hμle1 : p.μ ≤ 1)
    (hfloorδ : δ = T) (hfloor : UniformFloor u_star δ)
    (hsumR : ∀ σ : TimeDom T, ResolverSourceSummable p (realSlice u_star σ.1))
    (hgrad : ∀ (τ : TimeDom T),
      Summable fun k : ℕ =>
        |(intervalNeumannResolverCoeff p (realSlice u_star τ.1) k).re| * ((k : ℝ) * Real.pi))
    (f : ℝ → ℝ → ℝ) (hf_cont : ∀ σ : TimeDom T, Continuous (f σ.1))
    (hf_nonneg : ∀ (σ : TimeDom T) (y : ℝ), 0 ≤ f σ.1 y)
    (hf_coeff : ∀ (σ : TimeDom T) (k : ℕ),
      cosineCoeffs (f σ.1) k = (intervalNeumannResolverSourceCoeff p (realSlice u_star σ.1) k).re)
    (hf2 : ∀ σ : TimeDom T, Summable (fun k => (cosineCoeffs (f σ.1) k) ^ 2))
    -- the two remaining SECONDARY regularity side-atoms (named residuals, untouched):
    (h_flux_diff : ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (chemFluxLifted p (realSlice u_star τ.1)) x)
    (h_src_cont_chem : ∀ (τ : TimeDom T), Continuous (wChem p u_star τ.1))
    (h_src_cont_log : ∀ (τ : TimeDom T), Continuous (wLog p u_star τ.1))
    (t : ℝ) (htlo : 0 < t) (hthi : t ≤ T) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x := by
  -- parity of the fixed point, from the carried contraction data.
  have hER : EvenRealEWA u_star :=
    picardEWA_evenReal_fixedPoint p p.hμ hT u₀cos hmem hρ hself hLipQ hLipG hKnn hK
      u_star hmem_star hfix
  -- the three banked evalST atoms in slab shape, discharged internally.
  subst hfloorδ
  have h_u := realSlice_h_u_slab hER
  have h_uα := realSlice_h_uα_slab p hδpos hER hfloor hαnn
  have h_flux := realSlice_h_flux_slab p hδpos hβpos hER hfloor hsumR hgrad hμle1
    f hf_cont hf_nonneg hf_coeff hf2
  exact realizes_clean p u₀cos hsumc hmem hT u_star hfix hρ hself hLipQ hLipG hKnn hK
    hmem_star hgrad h_flux h_flux_diff h_src_cont_chem h_u h_uα h_src_cont_log t htlo hthi

end ShenWork.EWA

#print axioms ShenWork.EWA.realSlice_h_u_slab
#print axioms ShenWork.EWA.realSlice_h_uα_slab
#print axioms ShenWork.EWA.realSlice_h_flux_slab
#print axioms ShenWork.EWA.realizes_evalST_discharged
