# Paper 2 χ₀<0 — Status (2026-07-08 night)

## Files
- `ShenWork/Paper2/IntervalChiNegV5SelfContained.lean` — 4 sorry
- `ShenWork/Paper2/IntervalTruncatedTestedSpectral.lean` — 1 sorry

## Sorry 1: energy_continuous (V5 ~L570)
ContinuousOn (negativePartEnergy u) [0,T]
- Interior (0,T]: joint continuity (PROVED in IntervalTruncatedPicardLimitJointContinuity)
- At t=0: u(0)=0 by definition, energy(0)=0. Need energy(t)→0 as t→0+.
  From InitialTrace: u(t)→u₀ uniformly, u₀≥0 → u_minus→0 → integral→0.
- ChatGPT proof: negativePart_le_abs_sub_of_nonneg + sq bound + integral_mono

## Sorry 2: energy_has_deriv (V5 ~L581)
HasDerivWithinAt for negativePartEnergy
- IntervalNegativePartEnergyTimeLeibniz.lean has the Leibniz rule (0 sorry)
- Need to instantiate with window data: pointwise time derivative from coeff ODE
- The window `HasDerivWithinAt` needs joint continuity + coeff ODE → time derivative
- ChatGPT: instantiate negativePartEnergy_hasDerivWithinAt_Ici_of_window_data

## Sorry 3: jensenStrictPosData (V5 ~L657)
JensenBypassStrictPosDataFor
- Need: restart seed f, Jensen (S(t)f)²≤S(t)(f²), S(t)f>0, mild lower bound
- ChatGPT route: mass Gronwall → positive mass → ∃ x₀ u(s,x₀)>0 → seed=const*√(u(s))
  → heat kernel positivity (DELIVERED) → Jensen from Green nonneg + integral=1/μ
  → reaction-discounted lower: u(s+σ) ≥ e^{-Dσ}·S(σ)u(s) from mild identity + bound

## Sorry 4: fullAgreement (V5 ~L669)
truncatedPicardLimit = conjugatePicardLimit
- After nonneg: posPart(u_n) = u_n for each iterate
- So truncated Duhamel map = full Duhamel map (truncatedConjugateDuhamelMap_eq_intervalConjugateDuhamelMap_of_nonneg already proved)
- By induction: truncated iterates = full iterates
- Limits agree
- Does NOT need ConjugateMildExistenceData — just induction on iterates

## Sorry 5: spectralData (Spectral ~L667)
TruncatedPositiveTimeSpectralData instantiation
- Need: eigenvalue-weighted summability, time derivative representation, gradient representation
- From ℓ¹ ladder (IntervalCoeffLadderFull) + joint continuity + coeff ODE
- ChatGPT: instantiate WindowCoefficientEnvelope then extract spectral fields

## Priority
fullAgreement (sorry 4) is the EASIEST — pure induction, no analysis.
energy_continuous (sorry 1) is next — ChatGPT gave complete code.
The hardest: sorry 3 (Jensen) and sorry 5 (spectral data).

## V6 Architecture (current best, 0 sorry, axiom-clean)

File: IntervalChiNegV6Assembly.lean (251 lines)
Headline: paper2_chiNeg_v6
Carries: UniformTruncatedV6AssemblyInputs p + HSpectral

### V6 eliminates fullAgreement (Option B refactor)
- truncated limit used directly as ConjugateMildSolutionData.u
- no iterate-level nonneg needed (was likely false)
- no conjugatePicardLimit name-level equality needed

### 2 remaining unconditional producer gaps:

1. **energy (UniformTruncatedEnergyDataV6)**
   - Needs NegativePartStandardHeatSemigroupDuhamelFacts
   - = the weak testing identity for the negative-part test
   - Coefficient route (A): use FTC coefficient ODE + truncated source (C0)
   - Key: truncated source is continuous (1-Lipschitz), so coefficient ODE works

2. **HSpectral (BFormMildSpectralBootstrapData)**
   - Needs hPdeAgreement + hTimeNhd + hResolverData for arbitrary ConjugateMildSolutionData
   - All reduce to: per-t0 DuhamelSourceTimeC1 + eigenvalue-weighted summability
   - From: ℓ¹ ladder (IntervalCoeffLadderFull) + source continuity + spectral infra

ChatGPT Pro analyzing both gaps now (/tmp/gpt_Q3884 pending).
