import ShenWork.Wiener.EWA.SourceRealizesClean

/-!
# EWA capstone (χ₀<0 Route A′) — DISCHARGING the carried `hrealizes`

The χ₀<0 classical-regularity assembly `realSlice_classicalRegularity`
(`SourceClassicalRegularity.lean:120`) carries, among its atoms, the slab
`realizes` hypothesis

```
hrealizes : ∀ t ∈ Set.Ioo (0:ℝ) T, ∀ x ∈ Set.Icc (0:ℝ) 1,
  intervalDomainLift (realSlice u_star t) x
    = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x
```

i.e. "the realized slice lift equals its `fullSourceCoeff` cosine synthesis on
`[0,1]`, at every interior time".

This file shows `hrealizes` is **already produced** by the committed capstone
`realizes_clean` (`SourceRealizesClean.lean:40`), which delivers exactly that
identity for a single time `t` with `0 < t` and `t ≤ T`.  The only gap between
`realizes_clean`'s per-time conclusion and the slab `hrealizes` is the outer
`t`-quantifier: `realizes_clean` takes `htlo : 0 < t` and `hthi : t ≤ T`
separately, while `hrealizes` quantifies over `t ∈ Set.Ioo (0:ℝ) T`.  Membership
in `Ioo 0 T` is definitionally the pair `(0 < t, t < T)`, and `t < T → t ≤ T`,
so the wiring is a one-step `Ioo`-destructure feeding `realizes_clean`.

Hence the discharge is **pure wiring**: there is NO independent residual.  The
only analytic side-conditions threaded here are precisely `realizes_clean`'s own
hypotheses — the heat-datum data (`hsum`/`hmem`/`hT`), the Picard fixed-point +
contraction data (`hfix`/`hρ`/`hself`/`hLipQ`/`hLipG`/`hKnn`/`hK`/`hmem_star`),
and the two committed eval-bridge realized-source atoms.  In particular the
heat-datum summability `hsum : Summable (fun k => |u₀cos k|)` here is the SAME
`u₀`-summability already required elsewhere in the carried set (it is what makes
`hu0cos`/`hsumE`-type bounds available), so the residual coincides with an
already-carried summability hypothesis and is **not** independent.

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open scoped BigOperators
open Set Metric
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.PDE (intervalNeumannResolverCoeff)
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- **Discharge of the carried `hrealizes`.**  The slab `realizes` hypothesis of
`realSlice_classicalRegularity` — the realized slice lift equals its
`fullSourceCoeff` cosine synthesis on `[0,1]` at every interior time
`t ∈ Set.Ioo (0:ℝ) T` — is produced directly by the committed capstone
`realizes_clean`, applied once per interior time `t` after destructuring
`t ∈ Set.Ioo 0 T` into `0 < t` and `t < T` (hence `t ≤ T`).

This carries exactly `realizes_clean`'s own hypotheses (heat-datum, Picard
fixed-point + contraction data, and the two committed realized-source eval
atoms); it introduces no new analytic side-condition.  The `u₀`-summability
`hsum` here is the same summability already present in the carried atom set, so
the discharge is not an independent residual but a one-line quantifier rewiring. -/
theorem realSlice_realizes_of_atoms (p : CM2Params) (u₀cos : ℕ → ℝ)
    (hsum : Summable (fun k => |u₀cos k|)) (hmem : MemW 1 (ofCosineCoeffs u₀cos))
    (hT : (0 : ℝ) ≤ T)
    {ρ L_Q L_G : ℝ} (u_star : EWA T 1)
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
    (hgrad : ∀ (τ : TimeDom T),
      Summable fun k : ℕ =>
        |(intervalNeumannResolverCoeff p (realSlice u_star τ.1) k).re| * ((k : ℝ) * Real.pi))
    (h_flux_nbhd : ∀ (τ : TimeDom T), ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (y : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (chemFluxEWA p.μ p.ν p.β p.γ p.hμ u_star))
        = ((chemFluxLifted p (realSlice u_star τ.1) y : ℝ) : ℂ))
    (h_flux_diff : ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (chemFluxLifted p (realSlice u_star τ.1)) x)
    (h_u : ∀ (τ : TimeDom T), ∀ x ∈ Set.Icc (0 : ℝ) 1,
      evalST τ x (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)
        = (intervalDomainLift (realSlice u_star τ.1) x : ℂ))
    (h_uα : ∀ (τ : TimeDom T), ∀ x ∈ Set.Icc (0 : ℝ) 1,
      evalST τ x (GWA.incl (by omega : (0 : ℕ) ≤ 1) (realPowEWA u_star p.α))
        = ((intervalDomainLift (realSlice u_star τ.1) x ^ p.α : ℝ) : ℂ))
    (h_src_cont_log : ∀ (τ : TimeDom T), Continuous (wLog p u_star τ.1)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x := by
  intro t ht
  exact realizes_clean p u₀cos hsum hmem hT u_star hfix hρ hself hLipQ hLipG hKnn hK
    hmem_star hgrad h_flux_nbhd h_flux_diff h_u h_uα h_src_cont_log
    t ht.1 ht.2.le

end ShenWork.EWA

#print axioms ShenWork.EWA.realSlice_realizes_of_atoms
