/-
  ShenWork/Paper2/IntervalChiNegMildPackage.lean

  χ₀<0 — the per-slice `MildPackageFamily` for the CONJUGATE mild solution
  `u = conjugatePicardLimit p u₀ DB.T`, wiring the LANDED per-slice mild data into
  the `MildSlicePackage`/`MildPackageFamily` interface of
  `IntervalChiNegFluxSourceClosure`, and threading the `FluxFactorEnvelopes` input.

  ## WHAT THIS FILE DELIVERS — honest accounting (signature-audited below)

  The deliverable `mildPackageFamily_conjugate` PRODUCES a `MildPackageFamily` for
  the CONCRETE conjugate mild solution
    `u  := fun τ => intervalDomainLift ((conjugatePicardLimit p u₀ DB.T) τ)`,
    `Q  := conjQ  p (conjugatePicardLimit p u₀ DB.T)`   (= `chemFluxLifted p (u·)`),
    `Fl := conjFl p (conjugatePicardLimit p u₀ DB.T)`   (= `cos⟨logisticLifted⟩/√λ`),
    `û₀ := cosineCoeffs (intervalDomainLift u₀)`,  `χ₀ := p.χ₀`.

  CLOSED σ-UNIFORMLY from a SINGLE landed instance (NOT re-derived per σ):

  * `hdecomp` — the τ-uniform 3-term Duhamel decomposition.  This field is
    `E`- and `σ`-INDEPENDENT (mentions neither `E` nor `σ`).  So one application of
    the LANDED `conjugateSlice_decomp_tauLift` (IntervalDecompTauLift) discharges
    it for EVERY `(σ, E)`.  The genuine per-τ residuals it itself carries
    (continuities, Fubini swaps, heat diagonalization, the logistic coefficient
    bound, and the GENUINE `k = 0` mean-conservation `hzero`) are threaded as the
    named hypotheses `Dhyp …`; they are the SAME residuals the landed endpoint
    decomposition carries — NOT faked, NOT empty-repackaged.

  CLOSED from carried numerics / definitional shape (σ-uniformly, no per-σ data):

  * `hμ hσ0 hσ1 hβ ht ht1` — numeric side conditions (carried scalars; the σ-band
    `hσ0`/`hσ1` is supplied PER σ since `MildSlicePackage` fixes σ in its type).
  * `hQ`   — `conjQ` is by construction `W·vx`; supplied by the carried `hQ`.
  * `hWdef`— the chemotaxis weight factorisation; supplied by the carried `hWdef`.

  CARRIED PER (σ, E) — the genuinely irreducible per-slice mild content (these
  depend on `E`/`σ` and/or are the per-τ resolver/bridge/continuity seam, none of
  which is a consequence of the coefficient envelope alone):

    `hû₀`        : `MemHSigma (σ+1/4) û₀`                       (heat datum, per σ)
    `hvnn`       : resolver positivity                          (per-τ elliptic max)
    `hbr`        : `CosineMulBridge (u τ) (1+v)^{-β}`           (per-τ Wiener bridge)
    `hbridge`    : `MixedMulBridge (W τ) (vx τ)`                (per-τ mixed bridge)
    `hvrel`      : `Envelopes (resolverCoeff 1 E.env) …`        (per-σ resolver relay)
    `hdiv`       : divergence identity `|sin vx| = √λ·|cos v|`  (per-τ relay)
    `hQ_cont`    : `Continuous (τ ↦ sineCoeffs (Q τ) k)`        (flux continuity)
    `L hFl_cont` : the σ-level logistic envelope + continuity   (per-σ envelope)

  These are EXACTLY the fields the landed assembly STALL REPORT names as the
  per-slice/per-σ seam (`hbr`/`hbridge`/`hvrel`/`hdiv`/`hvnn`, the σ-level `L`, the
  heat datum) — they are carried with explicit signatures, not discharged.

  ## FluxFactorEnvelopes threading + the (C1) base reach

  `fluxFactors_of_carried` packages the carried per-σ factor envelopes
  (`W vx gW gvx` with `hgW/hgvx ∈ H^σ`, `hbridge`, `heW`, `hevx`) into the LANDED
  `FluxFactorEnvelopes σ t Q`, feeding `trajBaseEnvelope_of_fluxFactors` (C1).
  `reach_H1_conjugate` then plugs the (C1) base + the package family into the
  LANDED `trajEnvelope_one_of_baseInputs`, reaching `TrajectoryHSigmaEnvelope 1`
  for the conjugate mild solution — carrying EXACTLY the (C1) factor-envelope base
  data, `hFcont`, `htraj_dom`, and the package family `PF`.

  ## HONEST VERDICT

  `MemHSigma 1` is NOT reached UNCONDITIONALLY for `conjugatePicardLimit`.  No such
  unconditional discharge exists in Paper2: even the landed
  `u_posTime_memHSigma_one_of_mild` (IntervalMildPosTimeHSigma) carries a per-slice
  engine step `S`.  This file CLOSES the per-slice ASSEMBLY (one field, `hdecomp`,
  discharged σ-uniformly from a landed lemma; the numerics/`hQ`/`hWdef` discharged)
  and carries the genuinely-irreducible per-slice mild seam with explicit, audited
  signatures.  NON-CIRCULAR: never imports `localClassicalSolution`/
  `IsPaper2ClassicalSolution`/C²-of-`u`.  No `sorry`/`admit`/`native_decide`/custom
  `axiom`.  New file only.  `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
-/
import ShenWork.Paper2.IntervalChiNegFluxSourceClosure
import ShenWork.Paper2.IntervalDecompTauLift
import ShenWork.Paper2.IntervalMildPosTimeHSigma

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegMildPackage

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugatePicard (conjugatePicardLimit)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma resolverCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalDenomEnvelopeResolver (resolverValue)
open ShenWork.Paper2.IntervalEnvelopeProp (Envelopes)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.IntervalDecompTauLift (conjQ conjFl conjugateSlice_decomp_tauLift)
open ShenWork.Paper2.IntervalTrajectoryEnvelope
  (TrajectoryHSigmaEnvelope FluxFactorEnvelopes)
open ShenWork.Paper2.IntervalChiNegTrajectoryClosure (InputFamily)
open ShenWork.Paper2.IntervalChiNegFluxSourceClosure
  (MildSlicePackage MildPackageFamily inputFamily_of_packageFamily
   trajBaseEnvelope_of_fluxFactors)

/-! ## The per-τ analytic residuals that the landed `conjugateSlice_decomp_tauLift`
itself carries — packaged once, threaded σ-uniformly into `hdecomp`. -/

/-- The bundle of per-`τ` analytic residuals consumed by the landed
`conjugateSlice_decomp_tauLift` (IntervalDecompTauLift): source continuities,
Fubini swaps, heat diagonalization, the logistic coefficient bound, and the
GENUINE `k = 0` (and `τ = 0`) mean-conservation residual `hzero`.  These are the
exact residuals the landed per-endpoint decomposition carries; they are
`σ`- and `E`-INDEPENDENT, so threading them once discharges `hdecomp` for the whole
family. -/
structure DecompHyp (p : CM2Params)
    {T : ℝ} (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    (hmild : ShenWork.IntervalConjugateDuhamelMap.IntervalConjugateMildSolution p T u₀ u)
    (t : ℝ) where
  htT : t ≤ T
  hQcont : ∀ τ, 0 < τ → ∀ s, s < τ → Continuous (chemFluxLifted p (u s))
  hLcont : ∀ τ, 0 < τ → ∀ s, s < τ → Continuous (logisticLifted p (u s))
  hLM : ∀ τ, 0 < τ → ∃ Ml : ℝ, ∀ s, s < τ → ∀ j,
    |cosineCoeffs (logisticLifted p (u s)) j| ≤ Ml
  hheat_cont : ∀ τ, 0 < τ → Continuous
    (fun x => intervalFullSemigroupOperator τ (intervalDomainLift u₀) x)
  hchemI_cont : ∀ τ, 0 < τ → Continuous (fun x => ∫ s in (0:ℝ)..τ,
    ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator
      (τ - s) (chemFluxLifted p (u s)) x)
  hlogI_cont : ∀ τ, 0 < τ → Continuous (fun x => ∫ s in (0:ℝ)..τ,
    intervalFullSemigroupOperator (τ - s) (logisticLifted p (u s)) x)
  hpt_heat : ∀ τ, 0 < τ → ∀ k, cosineCoeffs
    (fun x => intervalFullSemigroupOperator τ (intervalDomainLift u₀) x) k
      = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
  hswap_chem : ∀ τ, 0 < τ → ∀ k, cosineCoeffs (fun x => ∫ s in (0:ℝ)..τ,
      ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator
        (τ - s) (chemFluxLifted p (u s)) x) k
    = ∫ s in (0:ℝ)..τ, cosineCoeffs
      (fun x => ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator
        (τ - s) (chemFluxLifted p (u s)) x) k
  hswap_log : ∀ τ, 0 < τ → ∀ k, cosineCoeffs (fun x => ∫ s in (0:ℝ)..τ,
      intervalFullSemigroupOperator (τ - s) (logisticLifted p (u s)) x) k
    = ∫ s in (0:ℝ)..τ, cosineCoeffs
      (fun x => intervalFullSemigroupOperator (τ - s) (logisticLifted p (u s)) x) k
  hzero : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
    (k = 0 ∨ τ = 0) → cosineCoeffs (intervalDomainLift (u τ)) k
      = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
        + (-p.χ₀) * duhamelEnergyCoeff 1
            (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
        + duhamelEnergyCoeff 1 (conjFl p u) τ k

/-- **The σ- and E-independent `hdecomp` for the conjugate mild solution**, discharged
from a SINGLE landed `conjugateSlice_decomp_tauLift` instance.  This is the EXACT
`MildSlicePackage.hdecomp` shape (with `u := lift∘(picard)`, `û₀ := cos⟨lift u₀⟩`,
`Q := conjQ`, `Fl := conjFl`, `χ₀ := p.χ₀`) — closed UNCONDITIONALLY given the
carried per-τ residual bundle `D`. -/
theorem conjugate_hdecomp (p : CM2Params)
    {T : ℝ} (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    (hmild : ShenWork.IntervalConjugateDuhamelMap.IntervalConjugateMildSolution p T u₀ u)
    {t : ℝ} (D : DecompHyp p u₀ u hmild t) :
    ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
      cosineCoeffs (intervalDomainLift (u τ)) k
        = Real.exp (-(τ * lam k)) * cosineCoeffs (intervalDomainLift u₀) k
          + (-p.χ₀) * duhamelEnergyCoeff 1
              (fun k τ => sineCoeffs (conjQ p u τ) k) τ k
          + duhamelEnergyCoeff 1 (conjFl p u) τ k :=
  conjugateSlice_decomp_tauLift p hmild D.htT D.hQcont D.hLcont D.hLM
    D.hheat_cont D.hchemI_cont D.hlogI_cont D.hpt_heat D.hswap_chem D.hswap_log
    D.hzero

/-! ## The per-(σ, E) carried mild seam — everything `hdecomp` does NOT supply. -/

/-- The genuinely-irreducible per-`(σ, E)` mild seam fields, carried as a record
indexed by σ and the running envelope `E` (these DEPEND on `E`/`σ` or are the per-τ
resolver/bridge/continuity seam; none is a consequence of `E` alone). -/
structure SeamHyp (p : CM2Params) (μ β t : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (v vx W : ℝ → ℝ → ℝ)
    (σ : ℝ)
    (E : TrajectoryHSigmaEnvelope σ t
      (fun τ => cosineCoeffs (intervalDomainLift (u τ)))) where
  hμ : 0 < μ
  hσ0 : 1 / 2 < σ
  hσ1 : σ < 3 / 2
  hβ : 0 ≤ β
  ht : 0 < t
  ht1 : t ≤ 1
  hû₀ : MemHSigma (σ + 1 / 4) (cosineCoeffs (intervalDomainLift (u 0)))
  hvnn : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ x,
    0 ≤ resolverValue μ (cosineCoeffs (intervalDomainLift (u τ))) x
  hQeq : ∀ τ, conjQ p u τ = fun x => W τ x * vx τ x
  hWdef : ∀ τ, W τ = fun x => (intervalDomainLift (u τ)) x
    * (1 + resolverValue μ
        (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β)
  hbr : ∀ τ ∈ Set.Icc (0:ℝ) t,
    ShenWork.Paper2.IntervalWienerAlgebra.CosineMulBridge
      (intervalDomainLift (u τ))
      (fun x => (1 + resolverValue μ
        (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β))
  hbridge : ∀ τ ∈ Set.Icc (0:ℝ) t,
    ShenWork.Paper2.IntervalMixedProduct.MixedMulBridge (W τ) (vx τ)
  hvrel : ∀ τ ∈ Set.Icc (0:ℝ) t,
    Envelopes (resolverCoeff 1 E.env) (cosineCoeffs (v τ))
  hdiv : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
    |sineCoeffs (vx τ) k| = Real.sqrt (lam k) * |cosineCoeffs (v τ) k|
  hQ_cont : ∀ k, Continuous (fun τ => sineCoeffs (conjQ p u τ) k)
  L : TrajectoryHSigmaEnvelope σ t (fun τ k => conjFl p u k τ)
  hFl_cont : ∀ k, Continuous (conjFl p u k)

/-! ## ASSEMBLE the `MildSlicePackage` for the conjugate mild solution. -/

/-- **One `MildSlicePackage` for the conjugate mild solution at level `σ`.**
`hdecomp` is discharged from the landed `conjugate_hdecomp` (σ-uniform); every
other field is threaded from the carried per-`(σ, E)` seam `S`. -/
def mildSlicePackage_conjugate (p : CM2Params)
    {T : ℝ} (u₀ : intervalDomainPoint → ℝ)
    {μ β t : ℝ} {u : ℝ → intervalDomainPoint → ℝ} {v vx W : ℝ → ℝ → ℝ}
    (hmild : ShenWork.IntervalConjugateDuhamelMap.IntervalConjugateMildSolution p T u₀ u)
    (hu0 : u 0 = u₀)
    (D : DecompHyp p u₀ u hmild t)
    {σ : ℝ}
    {E : TrajectoryHSigmaEnvelope σ t
      (fun τ => cosineCoeffs (intervalDomainLift (u τ)))}
    (S : SeamHyp p μ β t u v vx W σ E) :
    MildSlicePackage μ σ β p.χ₀ t
      (fun τ => intervalDomainLift (u τ)) v
      (cosineCoeffs (intervalDomainLift u₀))
      (conjQ p u) W vx (conjFl p u) E where
  hμ := S.hμ
  hσ0 := S.hσ0
  hσ1 := S.hσ1
  hβ := S.hβ
  ht := S.ht
  ht1 := S.ht1
  hû₀ := by simpa [hu0] using S.hû₀
  hvnn := S.hvnn
  hQ := S.hQeq
  hWdef := S.hWdef
  hbr := S.hbr
  hbridge := S.hbridge
  hvrel := S.hvrel
  hdiv := S.hdiv
  hQ_cont := S.hQ_cont
  L := S.L
  hFl_cont := S.hFl_cont
  hdecomp := by
    have h := conjugate_hdecomp p u₀ u hmild D
    simpa [hu0] using h

/-- **The `MildPackageFamily` for the conjugate mild solution.**  A σ-uniform
family of `MildSlicePackage`s, discharging `hdecomp` from the single landed
`conjugate_hdecomp` and threading the carried per-`(σ, E)` seam `SF σ E`. -/
def mildPackageFamily_conjugate (p : CM2Params)
    {T : ℝ} (u₀ : intervalDomainPoint → ℝ)
    {μ β t : ℝ} {u : ℝ → intervalDomainPoint → ℝ} {v vx W : ℝ → ℝ → ℝ}
    (hmild : ShenWork.IntervalConjugateDuhamelMap.IntervalConjugateMildSolution p T u₀ u)
    (hu0 : u 0 = u₀)
    (D : DecompHyp p u₀ u hmild t)
    (SF : ∀ σ : ℝ, ∀ E : TrajectoryHSigmaEnvelope σ t
        (fun τ => cosineCoeffs (intervalDomainLift (u τ))),
        SeamHyp p μ β t u v vx W σ E) :
    MildPackageFamily μ β p.χ₀ t
      (fun τ => intervalDomainLift (u τ)) v
      (cosineCoeffs (intervalDomainLift u₀))
      (conjQ p u) W vx (conjFl p u) :=
  fun σ E => mildSlicePackage_conjugate p u₀ hmild hu0 D (S := SF σ E)

/-- **The `InputFamily` for the conjugate mild solution** — lifts the package
family through the landed `inputFamily_of_packageFamily`. -/
def inputFamily_conjugate (p : CM2Params)
    {T : ℝ} (u₀ : intervalDomainPoint → ℝ)
    {μ β t : ℝ} {u : ℝ → intervalDomainPoint → ℝ} {v vx W : ℝ → ℝ → ℝ}
    (hmild : ShenWork.IntervalConjugateDuhamelMap.IntervalConjugateMildSolution p T u₀ u)
    (hu0 : u 0 = u₀)
    (D : DecompHyp p u₀ u hmild t)
    (SF : ∀ σ : ℝ, ∀ E : TrajectoryHSigmaEnvelope σ t
        (fun τ => cosineCoeffs (intervalDomainLift (u τ))),
        SeamHyp p μ β t u v vx W σ E) :
    InputFamily μ β p.χ₀ t
      (fun τ => intervalDomainLift (u τ)) v
      (cosineCoeffs (intervalDomainLift u₀))
      (conjQ p u) W vx (conjFl p u) :=
  inputFamily_of_packageFamily (mildPackageFamily_conjugate p u₀ hmild hu0 D SF)

/-! ## FluxFactorEnvelopes threading + the (C1) base. -/

/-- Package the carried per-σ factor-envelope seam into the LANDED
`FluxFactorEnvelopes σ t (conjQ p u)`. -/
def fluxFactors_of_carried (p : CM2Params)
    {σ t : ℝ} {u : ℝ → intervalDomainPoint → ℝ} {W vx : ℝ → ℝ → ℝ}
    {gW gvx : ℕ → ℝ}
    (hgW : MemHSigma σ gW) (hgvx : MemHSigma σ gvx)
    (hQeq : ∀ τ, conjQ p u τ = fun x => W τ x * vx τ x)
    (hbridge : ∀ τ ∈ Set.Icc (0:ℝ) t,
      ShenWork.Paper2.IntervalMixedProduct.MixedMulBridge (W τ) (vx τ))
    (heW : ∀ τ ∈ Set.Icc (0:ℝ) t, Envelopes gW (cosineCoeffs (W τ)))
    (hevx : ∀ τ ∈ Set.Icc (0:ℝ) t, Envelopes gvx (sineCoeffs (vx τ))) :
    FluxFactorEnvelopes σ t (conjQ p u) where
  W := W
  vx := vx
  gW := gW
  gvx := gvx
  hQ := hQeq
  hgW := hgW
  hgvx := hgvx
  hbridge := hbridge
  heW := heW
  hevx := hevx

/-- **REACH `H¹` for the conjugate mild solution.**  Plugs the (C1) flux-factor
base + the conjugate `InputFamily` into the landed `trajEnvelope_one_of_baseInputs`.
Carries EXACTLY: the flux factor envelope `F`, `hFcont`, `htraj_dom`, the count `n`,
`hreach`, plus the package-family inputs `hmild`/`hu0`/`D`/`SF`.  This is NOT an
unconditional `MemHSigma 1`: the per-slice mild seam is carried. -/
def reach_H1_conjugate (p : CM2Params)
    {T : ℝ} (u₀ : intervalDomainPoint → ℝ)
    {μ β σ₀ t : ℝ} {u : ℝ → intervalDomainPoint → ℝ} {v vx W : ℝ → ℝ → ℝ}
    (hσ₀ : 1 / 2 < σ₀) (hσ₀hi : σ₀ < 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hmild : ShenWork.IntervalConjugateDuhamelMap.IntervalConjugateMildSolution p T u₀ u)
    (hu0 : u 0 = u₀)
    (D : DecompHyp p u₀ u hmild t)
    (SF : ∀ σ : ℝ, ∀ E : TrajectoryHSigmaEnvelope σ t
        (fun τ => cosineCoeffs (intervalDomainLift (u τ))),
        SeamHyp p μ β t u v vx W σ E)
    (F : FluxFactorEnvelopes σ₀ t (conjQ p u))
    (hFcont : ∀ k, Continuous (fun τ => sineCoeffs (conjQ p u τ) k))
    (htraj_dom : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
      |cosineCoeffs (intervalDomainLift (u τ)) k|
        ≤ |duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (conjQ p u τ) k) τ k|)
    (n : ℕ) (hreach : (1 : ℝ) ≤ (0 + σ₀) + n * (1 / 4)) :
    TrajectoryHSigmaEnvelope 1 t
      (fun τ => cosineCoeffs (intervalDomainLift (u τ))) :=
  ShenWork.Paper2.IntervalChiNegTrajectoryClosure.trajEnvelope_one_of_baseInputs
    n hreach
    (trajBaseEnvelope_of_fluxFactors (by linarith) hσ₀hi hσ₀ ht ht1 F hFcont htraj_dom)
    (inputFamily_conjugate p u₀ hmild hu0 D SF)

end ShenWork.Paper2.IntervalChiNegMildPackage

namespace ShenWork.Paper2.IntervalChiNegMildPackage
#print axioms conjugate_hdecomp
#print axioms mildSlicePackage_conjugate
#print axioms mildPackageFamily_conjugate
#print axioms inputFamily_conjugate
#print axioms fluxFactors_of_carried
#print axioms reach_H1_conjugate
end ShenWork.Paper2.IntervalChiNegMildPackage
