/-
  ShenWork/Wiener/EWA/SourceReducedCoreWire.lean

  **χ₀<0 capstone — the MAXIMALLY-WIRED reduced coupled-Duhamel classical core.**

  `SourceReducedCore.lean`'s `realSlice_reducedCore` produces
  `CoupledDuhamelReducedClassicalCore p T u₀ (realSlice u_star)` but carries ~24
  named hypotheses (the honest χ₀<0 frontier).  Many of those are NOT independent
  residuals: they are produced by banked discharge lemmas elsewhere in the tree
  from a much smaller standing-input set.  This file CONSUMES every banked
  discharge plus the three closed `evalST` atoms and re-emits the reduced core
  carrying only the irreducible base residual.

  The central nexus is the slab `realizes`
  `intervalDomainLift (realSlice u_star t) x = Σ fullSourceCoeff … cosineMode`,
  produced here by `realizes_evalST_discharged` (the slab packaging of the three
  banked `evalST` atoms `realSlice_evalST_realizes`/`realSlice_realPow_realizes`/
  `realSlice_flux_realizes`).  From that single slab the following reduced-core
  fields are discharged with NO further frontier hypothesis:

  * `htime`/`hlap`/`hsum_lap`/`hsum_chem`/`hsum_log`  ← `SourcePdeUFamilyDischarge`
  * `hlogInv`                                          ← `realSlice_hlogInv_of_bankedU`
  * `hchemInv`                                         ← `realSlice_hchemInv_direct_realSlice`
  * `htimeDeriv`/`hdiffU`                              ← `SourceTimeDerivDischarge`
  * `huNE0`/`huNE1`                                    ← `SourceEndpointNonvanish`
  * `hdecay`                                           ← `realSlice_resolverDecay`
  * `Hvpos`                                            ← `realSlice_resolverPos`

  What remains carried is the PRECISE residual, classified in the docstring of
  `realSlice_reducedCore_wired`: (i) satisfiable STANDING inputs — the datum's own
  regularity / positivity / contraction class — versus (ii) genuinely OPEN content
  with no producer (the two source TIME-C¹ packages `hchem`/`hlog`, the resolver
  TIME-C¹ witness `Hv`, and the secondary regularity side-atoms).

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceReducedCore
import ShenWork.Wiener.EWA.SourceChiNegUncondWire
import ShenWork.Wiener.EWA.SourcePdeUFamilyDischarge
import ShenWork.Wiener.EWA.SourceHchemInvDirect
import ShenWork.Wiener.EWA.SourceSliceC2Neumann
import ShenWork.Wiener.EWA.SourceTimeDerivDischarge
import ShenWork.Wiener.EWA.SourceEndpointNonvanish
import ShenWork.Wiener.EWA.SourceResolverSpectralDischarge

noncomputable section

namespace ShenWork.EWA

open scoped BigOperators
open Set Metric
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.PDE
  (intervalNeumannResolverCoeff intervalNeumannResolverSourceCoeff)
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomainChemotaxisDiv)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalResolverDirectTimeRegularity (HasResolverDirectSpectralData)
open ShenWork.Paper2 (SourceCoeffQuadraticDecay)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs
    coupledChemicalConcentration CoupledDuhamelReducedClassicalCore)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)

variable {T : ℝ}

/-! ### The slab `realizes` with the three hard-core `evalST` atoms discharged. -/

/-- **The χ₀<0 `realizes` slab over ALL interior times — evalST atoms discharged.**

`realizes_evalST_discharged` delivers, for one interior time `t`, the slab
realization with the three hard-core `evalST` atoms supplied internally from the
banked producers.  Quantifying it over every `t ∈ Ioo 0 T` gives the exact slab
`hrealizes` shape consumed by `realSlice_reducedCore` and the downstream
discharges.  Carries exactly `realizes_evalST_discharged`'s own inputs: the
contraction/fixed-point data, the floor + no-embed resolver-source datum, and the
two secondary regularity side-atoms — NO `evalST` atom. -/
theorem realSlice_realizes_slab_evalST_discharged
    (p : CM2Params) (u₀cos : ℕ → ℝ)
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
    (h_flux_diff : ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (chemFluxLifted p (realSlice u_star τ.1)) x)
    (h_src_cont_chem : ∀ (τ : TimeDom T), Continuous (wChem p u_star τ.1))
    (h_src_cont_log : ∀ (τ : TimeDom T), Continuous (wLog p u_star τ.1)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x := by
  intro t ht
  exact realizes_evalST_discharged p u₀cos hsumc hmem hT hδpos u_star hfix hρ hself
    hLipQ hLipG hKnn hK hmem_star hβpos hαnn hμle1 hfloorδ hfloor hsumR hgrad
    f hf_cont hf_nonneg hf_coeff hf2 h_flux_diff h_src_cont_chem h_src_cont_log
    t ht.1 ht.2.le

/-! ### The maximally-wired reduced core. -/

/-- **The χ₀<0 MAXIMALLY-WIRED reduced coupled-Duhamel classical core.**

Consumes every banked discharge plus the three closed `evalST` atoms (via the
slab nexus `realSlice_realizes_slab_evalST_discharged`) and re-emits
`CoupledDuhamelReducedClassicalCore p T u₀ (realSlice u_star)` carrying only the
irreducible base residual.  The 24-hyp frontier of `realSlice_reducedCore` is
reduced to the following carried inputs, classified:

**(i) SATISFIABLE STANDING inputs** (the datum's own class — these PASS §3.3 as the
solution-class admissibility of `u₀`/`u_star`, no open math):

  * `hu0bd` — boundedness of the datum cosine coefficients;
  * `hδpos`/`hfloorδ`/`hfloor` — the uniform floor on the fixed point (positivity
    class of the realized slice; `δ = T`);
  * `hδρ`/`hheat`/`hu_ball` — the heat-floor + ball-membership positivity atoms;
  * `hfix`/`hρ`/`hself`/`hLipQ`/`hLipG`/`hKnn`/`hK`/`hmem_star` — the Picard
    fixed-point + contraction data (the existence/uniqueness class — `hK < 1`);
  * `hβpos`/`hαnn`/`hμle1` — sign/scale constraints on the model parameters;
  * `hsumR`/`hgrad`/`f`/`hf_cont`/`hf_nonneg`/`hf_coeff`/`hf2` — the no-embed
    resolver-source datum (the framework-wide O1 positivity/ℓ² input);
  * `hsumE` — eigenvalue-ℓ¹ summability of the source coefficients (the spatial-C²
    regularity budget of the slice; itself bankable from chemReg, kept as the
    leaner carried form);
  * `hcontChem`/`h_coeffChem` — continuity + Wiener-`sourceEnvelope` domination of
    the chem-div coefficients (eval/coeff regularity of the realized slice);
  * `hlogNE0`/`hlogNE1` — logistic-source endpoint nonvanishing (slice positivity
    at `{0,1}`);
  * `hu0cos`/`hrecon`/`hdefect`/`htrace` — datum ℓ¹ + cosine reconstruction +
    source/datum defect summability and its `t→0⁺` vanishing (the initial-trace
    class of the datum).

**(ii) GENUINELY OPEN content** (no producer; NOT a standing datum input — these are
the named χ₀<0 residuals §3.3 must flag):

  * `hchem`/`hlog` — the source TIME-C¹ packages `DuhamelSourceTimeC1`.  The banked
    `coupledChemDivSource_timeC1On_of_EWA` reduces these to an OPEN per-mode
    time-derivative leg (`adot`/`h_deriv`/`h_adotcont`/`Mdot`); no producer closes
    it from the standing inputs, so they are carried.
  * `Hv` — `HasResolverDirectSpectralData`, the resolver-source TIME-C¹ frontier.
    `realSlice_resolverSpectralData_residual` shows it bottoms out at a clamped
    `DuhamelSourceTimeC1` witness for the resolver source — also OPEN time-C¹.
  * `h_flux_diff`/`h_src_cont_chem`/`h_src_cont_log` — the secondary regularity
    side-atoms (flux differentiability, `wChem`/`wLog` continuity); no producer in
    the tree, carried through the realizes nexus.

So the faithful conditional PASSES §3.3 EXCEPT for the four named open packages
`hchem`, `hlog`, `Hv`, and the secondary regularity triple — all of TIME-C¹ /
secondary-regularity character, none a standing datum input. -/
theorem realSlice_reducedCore_wired (p : CM2Params) (u_star : EWA T 1)
    (u₀ : intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ)
    {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    -- positivity (heat-floor) atoms:
    {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    -- the realizes-nexus inputs (contraction + floor + resolver-source datum):
    (hsumc : Summable (fun k => |u₀cos k|)) (hmem : MemW 1 (ofCosineCoeffs u₀cos))
    (hT0 : (0 : ℝ) ≤ T) {L_Q L_G δ' ρ' : ℝ} (hδ'pos : 0 < δ')
    (hρ'ρ : ρ' = ρ)
    (hfix : u_star = picardEWA p p.μ p.ν p.γ p.hμ hT0
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1) u_star)
    (hρ' : 0 ≤ ρ')
    (hself : MapsTo
      (picardEWA p p.μ p.ν p.γ p.hμ hT0 (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1))
      (Metric.closedBall (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ')
      (Metric.closedBall (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ'))
    (hLipQ : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ',
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ',
      ‖chemFluxEWA p.μ p.ν p.β p.γ p.hμ a - chemFluxEWA p.μ p.ν p.β p.γ p.hμ b‖
        ≤ L_Q * ‖a - b‖)
    (hLipG : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ',
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ',
      ‖growthEWA p.α p.a p.b a - growthEWA p.α p.a p.b b‖ ≤ L_G * ‖a - b‖)
    (hKnn : (0 : ℝ) ≤ |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T)
    (hK : |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T < 1)
    (hmem_star : u_star ∈ Metric.closedBall (heatEWA (T := T)
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ')
    (hβpos : 0 < p.β) (hαnn : 0 ≤ p.α) (hμle1 : p.μ ≤ 1)
    (hfloorδ : δ' = T) (hfloor : UniformFloor u_star δ')
    (hsumR : ∀ σ : TimeDom T, ResolverSourceSummable p (realSlice u_star σ.1))
    (hgrad : ∀ (τ : TimeDom T),
      Summable fun k : ℕ =>
        |(intervalNeumannResolverCoeff p (realSlice u_star τ.1) k).re| * ((k : ℝ) * Real.pi))
    (f : ℝ → ℝ → ℝ) (hf_cont : ∀ σ : TimeDom T, Continuous (f σ.1))
    (hf_nonneg : ∀ (σ : TimeDom T) (y : ℝ), 0 ≤ f σ.1 y)
    (hf_coeff : ∀ (σ : TimeDom T) (k : ℕ),
      cosineCoeffs (f σ.1) k = (intervalNeumannResolverSourceCoeff p (realSlice u_star σ.1) k).re)
    (hf2 : ∀ σ : TimeDom T, Summable (fun k => (cosineCoeffs (f σ.1) k) ^ 2))
    -- secondary regularity side-atoms (genuinely open, no producer):
    (h_flux_diff : ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (chemFluxLifted p (realSlice u_star τ.1)) x)
    (h_src_cont_chem : ∀ (τ : TimeDom T), Continuous (wChem p u_star τ.1))
    (h_src_cont_log : ∀ (τ : TimeDom T), Continuous (wLog p u_star τ.1))
    -- source TIME-C¹ packages (genuinely open):
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p (realSlice u_star)))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p (realSlice u_star)))
    -- eigenvalue-ℓ¹ summability (spatial-C² budget):
    (hsumE : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|))
    -- chem-source inversion data (continuity + Wiener-envelope domination):
    {μc νc γc : ℝ} (hμc : 0 < μc) (Uc : EWA T 1)
    (hcontChem : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Continuous (fun x : intervalDomainPoint =>
        intervalDomainChemotaxisDiv p (realSlice u_star t)
          (coupledChemicalConcentration p (realSlice u_star) t) x))
    (h_coeffChem : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
        |coupledChemDivSourceCoeffs p (realSlice u_star) s n|
          ≤ sourceEnvelope (chemDivEWA μc νc γc hμc p Uc) n)
    -- logistic-source endpoint nonvanishing:
    (hlogNE0 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (intervalLogisticSource p (realSlice u_star t)) 0 ≠ 0)
    (hlogNE1 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (intervalLogisticSource p (realSlice u_star t)) 1 ≠ 0)
    -- resolver TIME-C¹ witness (genuinely open):
    (Hv : HasResolverDirectSpectralData T
      (mildChemicalConcentration p (realSlice u_star)) p)
    -- initial-trace atoms (datum class):
    (hT : (0 : ℝ) < T)
    (hu0cos : Summable (fun n => |u₀cos n|))
    (hrecon : ∀ x : intervalDomainPoint,
      u₀ x = ∑' n, u₀cos n * cosineMode n x.1)
    (hdefect : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n =>
        |fullSourceCoeff p (realSlice u_star) u₀cos t n - u₀cos n|))
    (htrace : Filter.Tendsto
      (fun t => ∑' n,
        |fullSourceCoeff p (realSlice u_star) u₀cos t n - u₀cos n|)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    CoupledDuhamelReducedClassicalCore p T u₀ (realSlice u_star) := by
  -- central nexus: the slab `realizes`, three evalST atoms discharged internally.
  have hrealizes : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (realSlice u_star t) x
        = ∑' n, fullSourceCoeff p (realSlice u_star) u₀cos t n * cosineMode n x := by
    refine realSlice_realizes_slab_evalST_discharged p u₀cos hsumc hmem hT0 hδ'pos
      u_star ?_ hρ' ?_ ?_ ?_ hKnn hK ?_ hβpos hαnn hμle1 hfloorδ hfloor hsumR hgrad
      f hf_cont hf_nonneg hf_coeff hf2 h_flux_diff h_src_cont_chem h_src_cont_log
    · exact hfix
    · exact hρ'ρ ▸ hself
    · exact hρ'ρ ▸ hLipQ
    · exact hρ'ρ ▸ hLipG
    · exact hρ'ρ ▸ hmem_star
  -- endpoint nonvanishing of the `u`-side from the heat floor (standing).
  have huNE0 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (realSlice u_star t) 0 ≠ 0 :=
    realSlice_lift_endpoint0_ne_zero hδρ hheat hu_ball
  have huNE1 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift (realSlice u_star t) 1 ≠ 0 :=
    realSlice_lift_endpoint1_ne_zero hδρ hheat hu_ball
  -- the `pde_u` family discharges from the slab + summability + the source packages.
  have htime := realSlice_htime_of_atoms p (realSlice u_star) u₀cos hu0bd hchem hlog
    hrealizes
  have hlap := realSlice_hlap_of_atoms p (realSlice u_star) u₀cos hsumE hrealizes
  have hsum_lap := realSlice_hsum_lap_of_atoms p (realSlice u_star) u₀cos hsumE
  have hsum_chem := realSlice_hsum_chem_of_atoms p (realSlice u_star) hchem (T := T)
  have hsum_log := realSlice_hsum_log_of_atoms p (realSlice u_star) hlog (T := T)
  -- chem inversion DIRECT from banked continuity + Wiener-envelope domination.
  have hchemInv := realSlice_hchemInv_direct_realSlice hμc p u_star Uc hcontChem h_coeffChem
  -- logistic inversion from the banked u-data + logistic endpoint nonvanishing.
  have hlogInv := realSlice_hlogInv_of_bankedU p u_star u₀cos hδρ hheat hu_ball hsumE
    hrealizes hlogNE0 hlogNE1
  -- time-derivative + differentiability from the slab + source packages.
  have htimeDeriv := realSlice_timeDeriv_of_atoms p (realSlice u_star) u₀cos hu0bd hchem
    hlog hrealizes
  have hdiffU := realSlice_diffU_of_atoms p (realSlice u_star) u₀cos hu0bd hchem hlog
    hrealizes
  -- quadratic decay + chemical-concentration positivity from the banked atoms.
  have hdecay := realSlice_resolverDecay p u_star u₀cos hδρ hheat hu_ball hsumE
    hrealizes huNE0 huNE1
  have hvpos := realSlice_resolverPos p u_star u₀cos hδρ hheat hu_ball hsumE hrealizes
  -- assemble the reduced core, feeding every discharged field.
  exact realSlice_reducedCore p u_star u₀ u₀cos hu0bd hδρ hheat hu_ball
    htime hlap hchemInv hlogInv hsum_lap hsum_chem hsum_log
    hchem hlog hsumE hrealizes htimeDeriv hdiffU huNE0 huNE1 hdecay Hv hvpos
    hT hu0cos hrecon hdefect htrace

end ShenWork.EWA

#print axioms ShenWork.EWA.realSlice_realizes_slab_evalST_discharged
#print axioms ShenWork.EWA.realSlice_reducedCore_wired
