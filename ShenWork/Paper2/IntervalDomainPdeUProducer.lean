/-
  ShenWork/Paper2/IntervalDomainPdeUProducer.lean

  **Honest spectral producer for the `hpde_u` field (χ₀ = 0 regime).**

  Target (the `hpde_u` field of `ReducedLimitRegularityInputs`,
  ShenWork/Paper2/IntervalDomainLedgerSweep.lean):

      ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
        intervalDomain.timeDeriv D.u t x =
          intervalDomain.laplacian (D.u t) x
            - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
                (mildChemicalConcentration p D.u t) x
            + D.u t x * (p.a - p.b * (D.u t x) ^ p.α)

  With `p.χ₀ = 0` the chemotaxis term vanishes, so the genuine content is the
  spectral parabolic identity `∂ₜu = Δu + reaction`.

  The CORE algebraic combination of the three spectral identities
  (time-derivative series, laplacian inversion, source cosine inversion) is
  already proved as `ShenWork.IntervalDomainPdeUChiZero.hpde_u_of_representation`.
  That producer consumes, FOR A FIXED interior time `t₀`, the restart cosine
  representation of `u` in a time-neighborhood of `t₀` together with the
  per-slice source-coefficient identity and the relevant summability /
  Fourier-summability / continuity facts.

  This file packages exactly that per-`t₀` data into a single predicate
  `HasSpectralPdeAgreement` and turns it into the universally-quantified
  `hpde_u` field via a clean unpack + apply.  All of the bundled data is
  precisely what the ledger's `Hu_of_restart`
  (ShenWork/Paper2/IntervalPicardLimitTimeNhd.lean) constructs from the reduced
  ledger families: the restart base `offset = t₀/2`, the restart coefficients
  `a₀ = cosineCoeffs (lift (u (t₀/2)))`, the source family
  `a = σ ↦ cosineCoeffs (logisticLifted p (u (t₀/2+σ)))` (whose value at
  `t₀ − offset` is `cosineCoeffs (logisticLifted p (u t₀))`, i.e. the logistic
  cosine coefficients — discharging `hsrc_coeff`), and the eigenvalue-weighted
  summability supplied by the `DuhamelSourceTimeC1` envelope plus the
  quadratic-decay machinery.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.Paper2.IntervalDomainPdeUChiZero
import ShenWork.Paper2.IntervalMildPicard

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift intervalDomain)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalSourceCoefficientTimeC1
  (localRestartCoeff)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalCosineInversion (reflCircle)

noncomputable section

namespace ShenWork.IntervalDomainPdeUProducer

/-- **Per-time spectral PDE agreement** for a trajectory `u` on `(0,T)`.

For each interior time `t₀ ∈ (0,T)` this bundles exactly the inputs consumed by
`ShenWork.IntervalDomainPdeUChiZero.hpde_u_of_representation`:

* a restart base `offset` with `0 < t₀ − offset`, restart coefficients `a₀`
  bounded by `M`, and a `DuhamelSourceTimeC1` source family `a`;
* the restart cosine representation `hrep`: `u` equals `∑ localRestartCoeff cos`
  in a time-neighborhood of `t₀`, pointwise in space;
* the source-coefficient identity `hsrc_coeff`: the source coefficients at the
  slice value `t₀ − offset` are the cosine coefficients of the logistic source
  of `u t₀` (this is exactly how the ledger's restart family is instantiated:
  `a σ = cosineCoeffs (logisticLifted p (u (offset+σ)))`, whose value at
  `σ = t₀ − offset` is `cosineCoeffs (logisticLifted p (u t₀))`);
* the continuity / Fourier-summability of the logistic source (`hcont`,
  `hsum_fourier`) needed for the cosine inversion, and the eigenvalue-weighted
  summability facts (`hsum_b`, `hsum_src`, `hsum_lb`) of the spectral series.

This is the honest upstream hypothesis: the ledger's `Hu_of_restart` builds the
restart half of this data, and the source half (`hsrc_coeff` and the three
summability facts) are produced by the `DuhamelSourceTimeC1` envelope together
with the quadratic-decay coefficient bounds the ledger carries. -/
structure HasSpectralPdeAgreement
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_data : ∀ t₀, 0 < t₀ → t₀ < T →
    ∀ {x : intervalDomainPoint}, x.1 ∈ Set.Ioo (0 : ℝ) 1 →
    ∃ (a₀ : ℕ → ℝ) (M : ℝ) (_ : 0 ≤ M) (_ : ∀ n, |a₀ n| ≤ M)
      (a : ℝ → ℕ → ℝ) (src : DuhamelSourceTimeC1 a)
      (offset : ℝ) (_ : 0 < t₀ - offset),
      -- restart cosine representation in a time-neighbourhood of t₀
      (∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
        u s y = ∑' n, localRestartCoeff a₀ a (s - offset) n * cosineMode n y.1) ∧
      -- the source coefficients ARE the logistic cosine coefficients of `u t₀`
      (∀ n, a (t₀ - offset) n
        = cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (u t₀))) n) ∧
      -- continuity + Fourier-summability of the logistic source (for inversion)
      Continuous (logisticSourceFun p.a p.b p.α (intervalDomainLift (u t₀))) ∧
      Summable (fun n : ℤ => fourierCoeff
        (reflCircle (logisticSourceFun p.a p.b p.α (intervalDomainLift (u t₀)))) n) ∧
      -- eigenvalue-weighted summability of the restart coefficients (laplacian)
      Summable (fun n => unitIntervalCosineEigenvalue n
        * |localRestartCoeff a₀ a (t₀ - offset) n|) ∧
      -- summability of the source spectral series (time-derivative split)
      Summable (fun n => a (t₀ - offset) n * cosineMode n x.1) ∧
      -- summability of the eigenvalue·coeff·cos series (time-derivative split)
      Summable (fun n => unitIntervalCosineEigenvalue n
        * localRestartCoeff a₀ a (t₀ - offset) n * cosineMode n x.1)

/-- **Honest spectral producer of `hpde_u` (χ₀ = 0).**

From the per-time spectral PDE agreement, the pointwise parabolic identity
`∂ₜu = Δu − χ₀·chemotaxis + reaction` holds at every interior point of every
interior time.  With `p.χ₀ = 0` the chemotaxis term drops out; the genuine
content `∂ₜu = Δu + reaction` is discharged by
`ShenWork.IntervalDomainPdeUChiZero.hpde_u_of_representation`.

This is exactly the shape of the `hpde_u` field of `ReducedLimitRegularityInputs`
(ShenWork/Paper2/IntervalDomainLedgerSweep.lean), with `u := D.u` and
`T := D.T`. -/
theorem mildSolution_pde_u_of_spectral
    (p : CM2Params) (hχ0 : p.χ₀ = 0) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (Hpde : HasSpectralPdeAgreement p D.T D.u) :
    ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α) := by
  intro t x ht htT hx
  -- `x ∈ intervalDomain.inside` unfolds to `x.1 ∈ Ioo 0 1`.
  have hx' : x.1 ∈ Set.Ioo (0 : ℝ) 1 := hx
  obtain ⟨a₀, M, hM, ha₀, a, src, offset, hoff,
      hrep, hsrc_coeff, hcont, hsum_fourier, hsum_b, hsum_src, hsum_lb⟩ :=
    Hpde.exists_data t ht htT hx'
  exact ShenWork.IntervalDomainPdeUChiZero.hpde_u_of_representation
    p hχ0 hM ha₀ src hoff hrep hsrc_coeff hcont hsum_fourier hsum_b hx' hsum_src hsum_lb

end ShenWork.IntervalDomainPdeUProducer
