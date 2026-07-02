# Codex Spec: v2 Bundled Core Constructor

## Goal

Create ONE new file `ShenWork/Wiener/EWA/SourceBundledCoreV2.lean`
that bundles the full v2 chain into a SINGLE theorem:

Given an EWA fixed point with its standard properties, produce
`CoupledDuhamelReducedClassicalCore` using L1ContOn (not TimeC1).

## Why this matters

The v2 chain has 5+ files, each producing intermediate results:
- SourceL1ContOnBridge → L1ContOn packages
- SourceSynthesisL1 → time derivatives
- SourceSpatialJointRegularityL1 → gradient continuity
- SourcePerSliceCloseL1 → Hv
- SourceReducedCoreWireV2 → classical regularity + reduced core

Threading all their hypotheses individually is a ~40-parameter nightmare.
This file bundles them into ONE theorem that takes the EWA fixed point
data and produces the core directly.

## The theorem to prove

```lean
theorem reducedCore_of_EWA_fixedPoint_v2 (p : CM2Params)
    (u_star : EWA T 1)
    (u₀ : intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ)
    {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    (hu_ball : u_star ∈ Metric.closedBall
      (heatEWA (T := T) u₀E) ρ)
    (hsumc : Summable (fun k => |u₀cos k|))
    (hmem : MemW 1 (ofCosineCoeffs u₀cos))
    (hT0 : (0 : ℝ) ≤ T) {L_Q L_G δ' ρ' : ℝ}
    (hδ'pos : 0 < δ') (hρ'ρ : ρ' = ρ)
    (hfix : u_star = picardEWA p p.μ p.ν p.γ p.hμ hT0
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1) u_star)
    (hρ' : 0 ≤ ρ')
    (hself : MapsTo
      (picardEWA p p.μ p.ν p.γ p.hμ hT0
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1))
      (Metric.closedBall
        (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ')
      (Metric.closedBall
        (heatEWA (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ'))
    (hLipQ : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ',
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ',
      ‖chemFluxEWA p.μ p.ν p.β p.γ p.hμ a
        - chemFluxEWA p.μ p.ν p.β p.γ p.hμ b‖
          ≤ L_Q * ‖a - b‖)
    (hLipG : ∀ a ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ',
      ∀ b ∈ Metric.closedBall (heatEWA (T := T)
        (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ',
      ‖growthEWA p.α p.a p.b a - growthEWA p.α p.a p.b b‖
        ≤ L_G * ‖a - b‖)
    (hKnn : (0 : ℝ) ≤
      |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T)
    (hK : |p.χ₀| * (C₀ * Real.sqrt T) * L_Q + L_G * T < 1)
    (hmem_star : u_star ∈ Metric.closedBall (heatEWA (T := T)
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1)) ρ')
    (hβpos : 0 < p.β) (hαnn : 0 ≤ p.α) (hμle1 : p.μ ≤ 1)
    (hfloorδ : δ' = T) (hfloor : UniformFloor u_star δ')
    (hsumR : ∀ σ : TimeDom T,
      ResolverSourceSummable p (realSlice u_star σ.1))
    (hgrad : ∀ (τ : TimeDom T),
      Summable fun k : ℕ =>
        |(intervalNeumannResolverCoeff p
          (realSlice u_star τ.1) k).re| * ((k : ℝ) * Real.pi))
    (f : ℝ → ℝ → ℝ)
    (hf_cont : ∀ σ : TimeDom T, Continuous (f σ.1))
    (hf_nonneg : ∀ (σ : TimeDom T) (y : ℝ), 0 ≤ f σ.1 y)
    (hf_coeff : ∀ (σ : TimeDom T) (k : ℕ),
      cosineCoeffs (f σ.1) k =
        (intervalNeumannResolverSourceCoeff p
          (realSlice u_star σ.1) k).re)
    (hf2 : ∀ σ : TimeDom T,
      Summable (fun k => (cosineCoeffs (f σ.1) k) ^ 2))
    (h_flux_diff : ∀ (τ : TimeDom T),
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        DifferentiableAt ℝ
          (chemFluxLifted p (realSlice u_star τ.1)) x)
    (h_src_cont_log : ∀ (τ : TimeDom T),
      Continuous (wLog p u_star τ.1))
    -- EIGENVALUE-ℓ¹ summability:
    (hsumE : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun n => unitIntervalCosineEigenvalue n *
        |fullSourceCoeff p (realSlice u_star) u₀cos t n|))
    -- Chem-source inversion data:
    {μc νc γc : ℝ} (hμc : 0 < μc) (Uc : EWA T 1)
    (hcontChem : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Continuous (fun x : intervalDomainPoint =>
        intervalDomainChemotaxisDiv p (realSlice u_star t)
          (coupledChemicalConcentration p (realSlice u_star) t) x))
    (h_coeffChem : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
        |coupledChemDivSourceCoeffs p (realSlice u_star) s n| ≤
          sourceEnvelope (chemDivEWA μc νc γc hμc p Uc) n)
    -- Logistic endpoint nonvanishing:
    (hlogNE0 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift
        (intervalLogisticSource p (realSlice u_star t)) 0 ≠ 0)
    (hlogNE1 : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      intervalDomainLift
        (intervalLogisticSource p (realSlice u_star t)) 1 ≠ 0)
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
    CoupledDuhamelReducedClassicalCore p T u₀ (realSlice u_star)
```

## Proof strategy

The proof MUST call `realSlice_reducedCore_wired_v2` which takes the
SAME parameters as above, PLUS:
- `hchem_l1 : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs ...) T`
- `hlog_l1 : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs ...) T`
- `hclassReg : intervalDomainClassicalRegularity T ...`
- `Hv : HasResolverDirectSpectralData T ...`

These 4 pieces come from the v2 chain:
1. `hchem_l1` from `chemDivSourceL1ContOn_of_EWA` (SourceL1ContOnBridge)
2. `hlog_l1` from `logisticSourceL1ContOn_of_EWA` (SourceL1ContOnBridge)
3. `hclassReg` from `realSlice_classicalRegularity_of_L1ContOn` (SourceReducedCoreWireV2)
4. `Hv` from `realSlice_Hv_closed_of_L1ContOn` (SourcePerSliceCloseL1)

So the proof is:
```
have hchem_l1 := chemDivSourceL1ContOn_of_EWA ...
have hlog_l1 := logisticSourceL1ContOn_of_EWA ...
have hclassReg := realSlice_classicalRegularity_of_L1ContOn ...
have Hv := realSlice_Hv_closed_of_L1ContOn ...
exact realSlice_reducedCore_wired_v2 p u_star u₀ u₀cos hu0bd hδρ hheat
  hu_ball hsumc hmem hT0 hδ'pos hρ'ρ hfix hρ' hself hLipQ hLipG hKnn hK
  hmem_star hβpos hαnn hμle1 hfloorδ hfloor hsumR hgrad f hf_cont hf_nonneg
  hf_coeff hf2 h_flux_diff h_src_cont_log hchem_l1 hlog_l1 hclassReg
  hsumE hμc Uc hcontChem h_coeffChem hlogNE0 hlogNE1 Hv hT hu0cos hrecon
  hdefect htrace
```

## KEY: What are the EXACT signatures of the v2 producers?

Read these files to get the exact types:

1. `SourceL1ContOnBridge.lean` — find `chemDivSourceL1ContOn_of_EWA`
   and `logisticSourceL1ContOn_of_EWA`. Understand what they need.

2. `SourceReducedCoreWireV2.lean` — find `realSlice_classicalRegularity_of_L1ContOn`.
   This takes hchem_l1, hlog_l1, and many other hypotheses.

3. `SourcePerSliceCloseL1.lean` — find `realSlice_Hv_closed_of_L1ContOn`.
   This takes hchem_l1, hlog_l1, and other hypotheses.

4. `SourceReducedCoreWireV2.lean` — find `realSlice_reducedCore_wired_v2`.
   This is the FINAL consumer.

The theorem's hypothesis list MUST match what these consumers need.
Study v1 `realSlice_reducedCore_wired` (SourceReducedCoreWire.lean:459-573)
as the pattern — the v2 bundled core takes the SAME parameters but with
L1ContOn replacing TimeC1On, and with Hv and classicalRegularity
produced internally (not taken as hypotheses).

## CRITICAL: namespace opens

Copy the opens block EXACTLY from SourceReducedCoreWireV2.lean (the
`open` block at the top). This was fixed through 3 iterations and is
the ONLY correct opens block. Do NOT guess opens — use the exact block.

## Verification

```bash
cd ~/repos/Shen_work
lake build ShenWork.Wiener.EWA.SourceBundledCoreV2 2>&1 | tail -10
```

Must compile with `#print axioms` showing ONLY [propext, Classical.choice, Quot.sound].

## Constraints

- NO sorry, NO axiom, NO native_decide, NO admit
- Line length ≤ 100 characters
- Do NOT modify any existing files
- The theorem signature should be IDENTICAL to `realSlice_reducedCore_wired_v2`
  except it drops the TimeC1-related hypotheses (hchem_on, hlog_on) and
  adds nothing (since L1ContOn packages are built internally from the EWA data)
- Actually, WAIT: the bundled theorem should take STRICTLY FEWER hypotheses
  than `realSlice_reducedCore_wired_v2`. The hypotheses it can DROP are:
  - hchem_l1, hlog_l1 (built from EWA data by SourceL1ContOnBridge)
  - hclassReg (built from L1ContOn by SourceReducedCoreWireV2)
  - Hv (built from L1ContOn by SourcePerSliceCloseL1)
  Confirm by reading the exact inputs of each v2 producer before writing.
