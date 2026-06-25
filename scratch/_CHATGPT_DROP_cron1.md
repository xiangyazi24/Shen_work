# ChatGPT git-drop (cron1)

## Q329 — circularity check: `hchem_on` vs. source joint-regularity feeders

### Executive verdict

There are **two different issues** that must not be conflated.

1. **Mathematically/conceptually**, the flux-factor joint `C²` data should *not* be produced from the chem-div source coefficient `DuhamelSourceTimeC1`.  It should come from the Picard/K1/EWA solution-side regularity: joint regularity of `u`, `u_t`, `v`, `v_t`, `v_x`, `v_xt`, plus product/quotient/rpow calculus.  This is the non-circular route.

2. **In the current Lean file `SourceJointRegularity.lean`, the theorem `fullSourceCoeff_jointSolutionClosed` is over-typed as taking global `DuhamelSourceTimeC1` packages for chem and log.**  Its value-field majorant is envelope-only, but the proof still uses `src.hderiv` indirectly to prove per-mode time continuity of the Duhamel coefficient.  Therefore, if you literally route the production of `CoupledChemDivLocalChainRule` through the current `fullSourceCoeff_jointSolutionClosed` theorem, you inherit a formal dependency on `hchem/hlog`.  That would be circular for producing `hchem_on`.

The fix is not to use `fullSourceCoeff_jointSolutionClosed` as the source of flux-factor joint regularity.  Use the Picard/K1/EWA regularity route, or split out a weaker value-field continuity theorem that takes only:

```lean
∀ n, Continuous (fun s => sourceCoeffs s n)
Summable envelope
∀ s∈[0,T], ∀ n, |sourceCoeffs s n| ≤ envelope n
```

rather than the full `DuhamelSourceTimeC1` package.

---

## What `fullSourceCoeff_jointSolutionClosed` actually does

The theorem is a thin wrapper:

```lean
theorem fullSourceCoeff_jointSolutionClosed (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u)) {T : ℝ} :
    ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  (fullSourceCoeff_jointContinuousOn p u u₀cos hu0bd hchem hlog).mono (slabClosed_subset T)
```

The real proof is in the private theorem `fullSourceCoeff_jointContinuousOn`, which does exactly the three-leg split:

```lean
have hheat := heatValueSeries_jointContinuousOn u₀cos hu0bd
have hchemJ := duhamelSeries_jointContinuousOn hchem
have hlogJ := duhamelSeries_jointContinuousOn hlog
have hsum := ((hheat.add (hchemJ.const_smul (-p.χ₀))).add hlogJ)
refine hsum.congr (fun q hq => ?_)
have := fullSourceCoeff_tsum_split p u u₀cos hu0bd hchem hlog hq
...
```

So the value-field theorem consumes `DuhamelSourceTimeC1` only through the two Duhamel value-leg lemmas and the pointwise split.

---

## Does the value-field proof use `src.hderiv`?

### Uniform majorant: envelope-only

For the value Duhamel series, the local `continuousOn_tsum` majorant in `duhamelSeries_jointContinuousOn` is:

```lean
T * src.envelope n
```

and the summability proof is:

```lean
have hu : Summable (fun n => T * src.envelope n) :=
  src.henv_summable.mul_left T
```

The norm bound uses:

```lean
src.henv_bound s hs n
```

together with the heat kernel bound and `|cosineMode n x| ≤ 1`.

So the **M-test / uniform majorant** part is indeed envelope-only:

```text
src.envelope
src.henv_summable
src.henv_bound
```

It does **not** use `src.adot`, `src.hadotcont`, `src.derivBound`, or `src.hderivBound`.

### Term continuity: uses `src.hderiv` indirectly

However, each summand must be continuous in `(t,x)`.  In `duhamelSeries_jointContinuousOn`, the proof obtains continuity of

```lean
fun τ => duhamelSpectralCoeff a τ n
```

from:

```lean
have hb_cont : Continuous (fun τ => duhamelSpectralCoeff a τ n) :=
  continuous_iff_continuousAt.2
    (fun τ => (duhamelSpectralCoeff_hasDerivAt src τ n).continuousAt)
```

and `duhamelSpectralCoeff_hasDerivAt src τ n` itself uses `src.hderiv` to prove continuity of the source coefficient `fun s => a s n`:

```lean
have hcont_an : Continuous (fun s => a s n) :=
  continuous_iff_continuousAt.2 (fun s => (src.hderiv s n).continuousAt)
```

So the accurate answer is:

```text
fullSourceCoeff_jointSolutionClosed uses src.hderiv indirectly for per-mode continuity,
but its uniform summable majorant uses only src.envelope / henv_summable / henv_bound.
```

It does not use the full derivative-envelope side of `DuhamelSourceTimeC1` for the value field.  It only needs source coefficient continuity plus the envelope.

---

## What about `fullSourceCoeffDot_jointTimeDerivClosed`?

This one is different and genuinely source-time-C¹ dependent.

The theorem is:

```lean
theorem fullSourceCoeffDot_jointTimeDerivClosed (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u)) {T : ℝ} :
    ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        ∑' n, fullSourceCoeffDot p u u₀cos t n * cosineMode n x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  (fullSourceCoeffDot_jointContinuousOn p u u₀cos hu0bd hchem hlog).mono (slabClosed_subset T)
```

The private proof calls:

```lean
have hchemJ := duhamelDerivSeries_jointContinuousOn hchem
have hlogJ := duhamelDerivSeries_jointContinuousOn hlog
```

`duhamelDerivSeries_jointContinuousOn` uses the derivative-side majorant:

```lean
src.envelope n + src.derivBound * reciprocalSquareTerm n
```

and uses the derivative identity / IBP path through:

```lean
duhamelSpectralCoeff_deriv_summable_uniform_bound
```

which depends on:

```lean
src.hderiv
src.hadotcont
src.hderivBound
src.derivBound
```

So `fullSourceCoeffDot_jointTimeDerivClosed` genuinely requires the source coefficient time-C¹ package.  It is not an envelope-only theorem.

Using this theorem to build the chain-rule data needed for `hchem_on` would be circular.

---

## The actual circularity status

### If the chain is literally this:

```text
hchem_on
  ← CoupledChemDivLocalChainRule
    ← CoupledChemDivFluxFactorJointC2Inputs
      ← joint C² of u/v/∂v
        ← fullSourceCoeff_jointSolutionClosed + fullSourceCoeffDot_jointTimeDerivClosed
          ← DuhamelSourceTimeC1 chem/log
```

then **yes, that Lean dependency chain is circular**.

The value-field theorem is only mildly overstrong, but the time-derivative theorem is genuinely downstream of `DuhamelSourceTimeC1`.

### If the chain is instead this:

```text
Picard fixed point / EWA/K1 solution-side regularity
  → joint continuity/C² of u and slopeSlice u
  → resolver time regularity for v and v_t
  → product/quotient/rpow calculus for flux factors
  → CoupledChemDivFluxFactorJointC2Inputs
  → CoupledChemDivLocalChainRule
  → h_deriv for coupledChemDivAdot
  → hchem_on
```

then it is **not circular**.

This is the intended architecture.  In fact, the definition of the chem-div time derivative already points to this route:

```lean
def coupledChemDivTimeDerivativeLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s x : ℝ) : ℝ :=
  deriv
    (fun y : ℝ =>
      let v : ℝ → ℝ := intervalDomainLift (coupledChemicalConcentration p u s)
      let vt : ℝ → ℝ := coupledChemicalTimeDerivativeLift p u s
      ShenWork.Paper2.PicardLimitK1.slopeSlice u s y * deriv v y /
          (1 + v y) ^ p.β +
        intervalDomainLift (u s) y * deriv vt y / (1 + v y) ^ p.β -
        p.β * intervalDomainLift (u s) y * deriv v y * vt y /
          (1 + v y) ^ (p.β + 1))
    x
```

The `u_t` factor is `PicardLimitK1.slopeSlice`, not `fullSourceCoeffDot`.

---

## What to change / avoid

### Do not use `fullSourceCoeffDot_jointTimeDerivClosed` to prove `hchem_on`

That theorem is downstream of `DuhamelSourceTimeC1`.  It is appropriate after `hchem/hlog` are known, for the classical-regularity capstone, but not for building `hchem_on` itself.

### Split the value theorem if needed

For solution-field joint continuity alone, the current theorem is stronger than necessary.  A non-circular variant should have a source package like:

```lean
structure DuhamelSourceValueJointData (a : ℝ → ℕ → ℝ) : Prop where
  envelope : ℕ → ℝ
  henv_summable : Summable envelope
  henv_bound : ∀ s, 0 ≤ s → ∀ n, |a s n| ≤ envelope n
  hcont : ∀ n, Continuous (fun s => a s n)
```

Then prove:

```lean
duhamelSeries_jointContinuousOn_valueOnly
  (src : DuhamelSourceValueJointData a) :
  ContinuousOn
    (Function.uncurry
      (fun τ x => ∑' n, duhamelSpectralCoeff a τ n * cosineMode n x))
    (Set.Ioi 0 ×ˢ Set.univ)
```

The proof is exactly the existing `duhamelSeries_jointContinuousOn` proof, replacing

```lean
(duhamelSpectralCoeff_hasDerivAt src τ n).continuousAt
```

by a direct continuity proof for the Duhamel integral from `src.hcont n`.

This would let `fullSourceCoeff_jointSolutionClosed` be proved from envelope + source continuity, without requiring source time-C¹.

### For flux factor joint C², use the factor path

The relevant non-circular producers are the ones around:

```lean
CoupledChemDivPointwiseChainAtoms
coupledChemDivLocalChainRule_of_pointwiseChainAtoms
CoupledChemDivFluxJointC2Hyp
coupledChemDivLocalChainRule_of_fluxJointC2
CoupledChemDivFluxFactorJointC2Inputs
coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
```

and the closed-slab representative route:

```lean
ChemDivMixedTimeDerivClosedRepr
chemDivMixedTimeDeriv_jointContinuousOn_closed
```

These are the right upstream targets for `hchem_on`.

---

## Final answer

`fullSourceCoeff_jointSolutionClosed` currently takes `DuhamelSourceTimeC1` and therefore formally depends on `hchem/hlog`.  In its value proof, the **summable majorant** uses only `src.envelope`, `src.henv_summable`, and `src.henv_bound`; however, the proof still uses `src.hderiv` indirectly to obtain per-mode continuity of the Duhamel coefficient.  So it is not purely envelope-only as written.

`fullSourceCoeffDot_jointTimeDerivClosed` genuinely uses the derivative side of `DuhamelSourceTimeC1` and is definitely downstream of `hchem/hlog`.

Therefore:

```text
Using SourceJointRegularity's current fullSourceCoeffDot path to prove hchem_on is circular.
Using the Picard/K1/EWA factor-regularity path to prove hchem_on is not circular.
```

The practical route is to keep `hchem_on` upstream of `SourceJointRegularity`'s time-derivative capstone, and, if necessary, introduce a weaker value-only source package for solution-field joint continuity so the value-field regularity does not artificially require source time-C¹.
