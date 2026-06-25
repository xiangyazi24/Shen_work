# ChatGPT git-drop (cron1)

## Q327 — `DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p (realSlice u_star)) 0 T`: input audit

### Executive verdict

The assembler

```lean
coupledChemDivSource_timeC1On_of_EWA
```

is exactly a **consumer** of the remaining time-derivative legs. It supplies the value-side `envelope` and `henv_summable` from the EWA `sourceEnvelope`, but it does not prove the chain-rule slab, joint continuity of the time-derivative lift, or the Mdot bound.

Its current signature is:

```lean
noncomputable def coupledChemDivSource_timeC1On_of_EWA
    {μ ν γ : ℝ} (hμ : 0 < μ)
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (U : EWA T 1)
    (h_coeff : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
        |coupledChemDivSourceCoeffs p u s n|
          ≤ sourceEnvelope (chemDivEWA μ ν γ hμ p U) n)
    (adot : ℝ → ℕ → ℝ)
    (h_deriv : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
        HasDerivWithinAt (fun r => coupledChemDivSourceCoeffs p u r n)
          (adot s n) (Set.Icc 0 T) s)
    (h_adotcont : ∀ n, ContinuousOn (fun s => adot s n) (Set.Icc 0 T))
    (Mdot : ℝ) (h_Mdot : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n, |adot s n| ≤ Mdot) :
    DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) 0 T
```

and its fields are assigned by:

```lean
envelope := sourceEnvelope (chemDivEWA μ ν γ hμ p U)
henv_summable := sourceEnvelope_summable _
henv_bound := h_coeff
derivBound := Mdot
hderivBound := h_Mdot
```

So the current assembly split is:

```text
h_coeff            caller-side eval/coeff bridge into the EWA sourceEnvelope
adot               should be coupledChemDivAdot p u
h_deriv            from CoupledChemDivLocalChainRule
h_adotcont         from joint continuity of coupledChemDivTimeDerivativeLift on [0,T]×[0,1]
Mdot/h_Mdot        from chemDivAdot_Mdot_of_spatial_H2 or a stronger envelope
```

---

## (A) What `CoupledChemDivLocalChainRule` needs

The definition is in `IntervalChemDivTimeDerivative.lean`:

```lean
structure CoupledChemDivLocalChainRule
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt
        (fun r => coupledChemDivSourceLift p u r x)
        (coupledChemDivTimeDerivativeLift p u s x) s) ∧
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

So it needs three local-slab facts around every time `τ`:

1. eventual spatial continuity of the source lift,
2. pointwise-in-space time `HasDerivAt` of the chem-div source lift,
3. joint continuity of the explicit time-derivative field on the closed slab.

### Is per-slice `ContDiff 2` of `realSlice u_star` enough?

No. Per-slice spatial `C²` is not enough by itself.

It helps with spatial regularity of the factors, but the chain-rule package also needs **time differentiability** of

```lean
r ↦ coupledChemDivSourceLift p u r x
```

with derivative

```lean
coupledChemDivTimeDerivativeLift p u s x
```

and joint continuity of that derivative field. Those are time/mixed regularity facts, not merely per-slice spatial `C²` facts.

The repo has a clean hierarchy for producing this package:

```lean
CoupledChemDivPointwiseChainAtoms p u
  → coupledChemDivLocalChainRule_of_pointwiseChainAtoms
  → CoupledChemDivLocalChainRule p u
```

where `CoupledChemDivPointwiseChainAtoms` has exactly the same `exists_local_slab` content.

There is also a more structural route:

```lean
CoupledChemDivFluxJointC2Hyp p u
  → coupledChemDivLocalChainRule_of_fluxJointC2
  → CoupledChemDivLocalChainRule p u
```

and an even more factorized route:

```lean
CoupledChemDivFluxFactorJointC2Inputs p u
  → coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
  → coupledChemDivLocalChainRule_of_fluxJointC2
```

The factor-level package explicitly needs local joint `C²` of:

```lean
(t,x) ↦ intervalDomainLift (u t) x
(t,x) ↦ intervalDomainLift (coupledChemicalConcentration p u t) x
(t,x) ↦ deriv (intervalDomainLift (coupledChemicalConcentration p u t)) x
```

plus positivity of `1+v`, the time-partial bridge, and the closed-slab continuity of `coupledChemDivTimeDerivativeLift`.

So the correct statement is:

```text
SourceSliceC2Neumann / per-slice C² is useful but insufficient.
For (A) you need either the explicit pointwise chain atoms or the joint-flux C² / FAC package.
```

---

## (B) Joint continuity of `coupledChemDivTimeDerivativeLift`

### What exists for `∂ₜv` only

`IntervalChemDivTimeDerivative.lean` has:

```lean
theorem coupledChemicalTimeDerivative_jointContinuousOn_closed
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {U : ℝ}
    (H : ResolverHasSpectralAgreement U (coupledChemicalConcentration p u)) :
    ContinuousOn
      (Function.uncurry (coupledChemicalTimeDerivativeLift p u))
      (Ioo (0 : ℝ) U ×ˢ Icc (0 : ℝ) 1)
```

This is only the resolver time-derivative factor `v_t`, not the full chem-div time-derivative lift.

It also has the fixed-space compact-window version:

```lean
theorem coupledChemicalTimeDerivative_continuousOn_Icc_of_lt_horizon
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {U T c x : ℝ}
    (H : ResolverHasSpectralAgreement U (coupledChemicalConcentration p u))
    (hc : 0 < c) (hTU : T < U) (hx : x ∈ Icc (0 : ℝ) 1) :
    ContinuousOn
      (fun s => coupledChemicalTimeDerivativeLift p u s x)
      (Icc c T)
```

Again, this is for `v_t`, not for the full `coupledChemDivTimeDerivativeLift`.

### What exists for full `coupledChemDivTimeDerivativeLift`

`IntervalChemDivTimeDerivClosed.lean` introduces the exact representative-based hypothesis:

```lean
def ChemDivMixedTimeDerivClosedRepr
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) : Prop :=
  ∃ Gmix : ℝ × ℝ → ℝ, Continuous Gmix ∧
    ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
      coupledChemDivTimeDerivativeLift p u t x = Gmix (t, x)
```

and proves:

```lean
theorem chemDivMixedTimeDeriv_jointContinuousOn_closed
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (H : ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

So the repo **does** have a theorem producing the desired closed-slab joint continuity, but only from the explicit closed-slab representative `ChemDivMixedTimeDerivClosedRepr`. It is not unconditional for arbitrary `u`.

I found no `ChemDivGcont` / `chemDivGcont` symbol by grep.

There is also a higher-level producer:

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt)
    (hu_cont : ∀ s : ℝ, Continuous (u s))
    (hu_nonneg : ∀ s : ℝ, ∀ x : intervalDomainPoint, 0 ≤ u s x)
    (other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
      (∀ᶠ s in 𝓝 τ,
        ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
        ContDiffAt ℝ 2 (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)) ∧
      ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    CoupledChemDivFluxFactorJointC2Inputs p u
```

This discharges the `htime_cont` field internally via `chemDivMixedTimeDeriv_jointContinuousOn_closed`, but still requires the `ChemDivMixedTimeDerivClosedRepr` input.

### For `h_adotcont` on `[0,T]`

The EWA brick `ChemDivAdot.lean` has:

```lean
theorem chemDivAdot_continuousOn_of_jointCont
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hjointcont : ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ∀ n, ContinuousOn (fun s => coupledChemDivAdot p u s n) (Set.Icc (0 : ℝ) T)
```

So for your final theorem, the required exact route is:

```text
joint continuity of coupledChemDivTimeDerivativeLift on [0,T]×[0,1]
  → chemDivAdot_continuousOn_of_jointCont
  → h_adotcont.
```

The repo currently gives a local closed-slab continuity theorem from `ChemDivMixedTimeDerivClosedRepr`. To get the **global window** `[0,T]×[0,1]`, you either need a single representative on `[0,T]`, or a compact/gluing lemma from local slabs covering `[0,T]`. The landed theorem itself is local-slab-shaped.

---

## (C) What `chemDivAdot_Mdot_of_spatial_H2` needs

The file `ChemDivAdotEnvelope.lean` has the requested Mdot producer:

```lean
theorem chemDivAdot_Mdot_of_spatial_H2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {B_sup B_H2 : ℝ} (hBs : 0 ≤ B_sup) (hBh : 0 ≤ B_H2)
    (hcont : ∀ s ∈ Icc (0 : ℝ) T, ContinuousOn
      (coupledChemDivTimeDerivativeLift p u s) (Icc (0 : ℝ) 1))
    (hbd : ∀ s ∈ Icc (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      |coupledChemDivTimeDerivativeLift p u s x| ≤ B_sup)
    (hdecay_raw : ∀ s ∈ Icc (0 : ℝ) T, ∀ n : ℕ, 1 ≤ n →
      |coupledChemDivAdot p u s n| ≤ 2 * B_H2 / ((n : ℝ) * Real.pi) ^ 2) :
    ∃ Mdot : ℝ, ∀ s ∈ Icc (0 : ℝ) T, ∀ n,
      |coupledChemDivAdot p u s n| ≤ Mdot
```

So it does **not** directly take `IntervalWeakH2Neumann` as an argument. It takes the already-quantified consequences:

1. nonnegative constants:

```lean
hBs : 0 ≤ B_sup
hBh : 0 ≤ B_H2
```

2. per-slice spatial continuity of the time-derivative field:

```lean
hcont : ∀ s ∈ Icc 0 T,
  ContinuousOn (coupledChemDivTimeDerivativeLift p u s) (Icc 0 1)
```

3. uniform sup bound:

```lean
hbd : ∀ s ∈ Icc 0 T, ∀ x ∈ Icc 0 1,
  |coupledChemDivTimeDerivativeLift p u s x| ≤ B_sup
```

4. uniform quadratic coefficient-decay bound for positive modes:

```lean
hdecay_raw : ∀ s ∈ Icc 0 T, ∀ n, 1 ≤ n →
  |coupledChemDivAdot p u s n| ≤ 2 * B_H2 / ((n : ℝ) * Real.pi) ^ 2
```

Internally it sets:

```lean
Cdot := max (2 * B_sup) (2 * B_H2)
```

uses `cosineCoeffs_abs_le_of_continuous_bounded` for mode `0`, and uses `hdecay_raw` for modes `n ≥ 1`, then delegates to the summable-envelope theorem.

### What still feeds `hdecay_raw`?

The file documentation says the intended source is:

```text
IntervalWeakH2Neumann + quantitative H²_N coefficient decay
```

namely the theorem:

```lean
intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound
```

But `chemDivAdot_Mdot_of_spatial_H2` expects the final coefficient decay inequality already packaged as `hdecay_raw`. If you want a theorem that starts from per-slice `IntervalWeakH2Neumann` of `coupledChemDivTimeDerivativeLift p u s` plus a uniform bound on the relevant second-derivative integral, that is one wrapper above this current theorem.

---

## Current dependency map for your final `DuhamelSourceTimeC1On`

The intended final assembly should look like:

```lean
let adot := coupledChemDivAdot p (realSlice u_star)

have h_deriv : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
    HasDerivWithinAt
      (fun r => coupledChemDivSourceCoeffs p (realSlice u_star) r n)
      (adot s n) (Set.Icc 0 T) s :=
  chemDivAdot_hasDerivWithinAt_of_chainRule hchain

have h_adotcont : ∀ n,
    ContinuousOn (fun s => adot s n) (Set.Icc 0 T) :=
  chemDivAdot_continuousOn_of_jointCont hjointcont

obtain ⟨Mdot, h_Mdot⟩ :=
  chemDivAdot_Mdot_of_spatial_H2 hBs hBh hcont hbd hdecay_raw

exact coupledChemDivSource_timeC1On_of_EWA
  (hμ := hμ) p (realSlice u_star) U
  h_coeff
  adot
  h_deriv
  h_adotcont
  Mdot
  h_Mdot
```

where the currently open producer obligations for `u = realSlice u_star` are:

```text
hchain       : CoupledChemDivLocalChainRule p (realSlice u_star)
hjointcont   : ContinuousOn (Function.uncurry
                 (coupledChemDivTimeDerivativeLift p (realSlice u_star)))
                 (Icc 0 T ×ˢ Icc 0 1)
hcont        : ∀ s∈[0,T], ContinuousOn (coupledChemDivTimeDerivativeLift ... s) [0,1]
hbd          : uniform sup bound of the derivative field
hdecay_raw   : uniform 1/n² coefficient decay of coupledChemDivAdot
h_coeff      : EWA sourceEnvelope domination for the value coefficients
```

`hcont` follows immediately from `hjointcont` by restricting to a fixed time slice, but `hbd` and `hdecay_raw` require quantitative boundedness / H²_N information.

---

## Answer to the three specific questions

### (A)

`CoupledChemDivLocalChainRule` requires a local slab around every `τ`: eventual source continuity, pointwise time `HasDerivAt` of the source lift, and joint continuity of `coupledChemDivTimeDerivativeLift` on the closed slab. It is **not** produced merely from per-slice `ContDiff 2` of `realSlice u_star`; per-slice spatial C² does not provide the needed time derivative or mixed continuity.

The closest producers are:

```lean
coupledChemDivLocalChainRule_of_pointwiseChainAtoms
coupledChemDivLocalChainRule_of_fluxJointC2
```

and the factor-level route through:

```lean
CoupledChemDivFluxFactorJointC2Inputs
```

### (B)

The repo has:

```lean
chemDivMixedTimeDeriv_jointContinuousOn_closed
```

which proves joint continuity of the full `coupledChemDivTimeDerivativeLift`, but only from:

```lean
ChemDivMixedTimeDerivClosedRepr p u τ δ
```

It also has resolver-only joint continuity for `coupledChemicalTimeDerivativeLift` from `ResolverHasSpectralAgreement`, but that is only the `v_t` factor, not the full chem-div derivative field.

I found no `ChemDivGcont` / `chemDivGcont` symbol.

### (C)

`chemDivAdot_Mdot_of_spatial_H2` needs:

```lean
hBs : 0 ≤ B_sup
hBh : 0 ≤ B_H2
hcont : ∀ s∈[0,T], ContinuousOn (coupledChemDivTimeDerivativeLift p u s) [0,1]
hbd : ∀ s∈[0,T], ∀ x∈[0,1], |coupledChemDivTimeDerivativeLift p u s x| ≤ B_sup
hdecay_raw : ∀ s∈[0,T], ∀ n≥1,
  |coupledChemDivAdot p u s n| ≤ 2 * B_H2 / ((n : ℝ) * Real.pi)^2
```

It returns exactly:

```lean
∃ Mdot, ∀ s∈[0,T], ∀ n,
  |coupledChemDivAdot p u s n| ≤ Mdot
```

It does not itself prove `hdecay_raw`; it consumes the quadratic-decay inequality that should come from `IntervalWeakH2Neumann` plus a uniform second-derivative integral bound.

---

## Final classification

For `realSlice u_star`, the three non-produced inputs are accurately identified, but they are not all equally primitive:

```text
(A) hchain:
    not from per-slice C² alone;
    route through pointwise chain atoms or flux joint-C²/FAC inputs.

(B) hjointcont:
    no unconditional theorem for arbitrary u;
    available from ChemDivMixedTimeDerivClosedRepr via chemDivMixedTimeDeriv_jointContinuousOn_closed.

(C) Mdot/H²:
    Mdot producer exists;
    it needs continuity, uniform sup bound, and positive-mode quadratic coefficient decay of coupledChemDivAdot.
```

Thus the remaining hard analytic producer is not the final `DuhamelSourceTimeC1On` assembly. The final assembly is wired. The real work is to produce the **closed-slab mixed time-derivative representative / joint-C² chain data** and the **uniform H²_N quantitative bounds** for `coupledChemDivTimeDerivativeLift p (realSlice u_star)`.
