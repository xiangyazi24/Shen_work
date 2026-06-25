# Q572 / cron1: `Continuous (intervalDomainLift u₀)` and the spectral bridge

## Verdict

Your diagnosis is correct: for a general continuous

```lean
u₀ : intervalDomainPoint → ℝ
```

`Continuous (intervalDomainLift u₀)` is **not** true.  The lift is a zero extension to all of `ℝ`, so unless the boundary traces match the outside value `0` — in particular `u₀(0)=0` and `u₀(1)=0` with the right compatibility — it has jumps at the endpoints.  For positive data it is definitely false.

The repo already has this exact diagnosis and a replacement route.  The key file is:

```text
ShenWork/PDE/IntervalDomainContinuousExtension.lean
```

Its header says the paper works on `C(Ω̄)`, the spectral chain sees only values on `[0,1]`, and the bridge is to extend a subtype function by constants instead of by zero.  The comments explicitly say the constant extension is globally continuous and agrees with `intervalDomainLift` on `(0,1)` / `[0,1]` where needed.

## What exists for `intervalDomainLift`

The zero-extension behavior is visible in `IntervalDomainExistence.lean` for constants:

```lean
-- ShenWork/PDE/IntervalDomainExistence.lean:54-60
/-- The lift of a constant function on intervalDomainPoint equals
`c` on `[0,1]` and `0` outside. -/
lemma intervalDomainLift_const (c : ℝ) :
    intervalDomainLift (fun _ : intervalDomainPoint => c) =
      fun x => if x ∈ Set.Icc (0 : ℝ) 1 then c else 0 := by
  ext x
  simp [intervalDomainLift]
```

This is the concrete obstruction: if `c ≠ 0`, that function jumps at `0` and `1`.

I did not find a useful general theorem of the form

```lean
Continuous (intervalDomainLift u₀)
```

from `Continuous u₀`; that theorem would be false.  Search hits for `Continuous (intervalDomainLift ...)` are mostly old call sites, handoff notes, or adapters documenting that the old requirement was bad.

## The replacement: constant extension

`ShenWork/PDE/IntervalDomainContinuousExtension.lean` defines:

```lean
-- lines 27-34
def intervalDomainConstExtend (f : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun x =>
    if h0 : x ≤ 0 then f ⟨0, ⟨le_refl _, zero_le_one⟩⟩
    else if h1 : 1 ≤ x then f ⟨1, ⟨zero_le_one, le_refl _⟩⟩
    else f ⟨x, ⟨(not_le.mp h0).le, (not_le.mp h1).le⟩⟩
```

It proves agreement with the zero lift:

```lean
-- lines 37-49
theorem constExtend_eq_lift_on_Ioo {f : intervalDomainPoint → ℝ}
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    intervalDomainConstExtend f x = intervalDomainLift f x

theorem constExtend_eq_lift_on_Icc {f : intervalDomainPoint → ℝ}
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    intervalDomainConstExtend f x = intervalDomainLift f x
```

and the crucial continuity theorem:

```lean
-- lines 60-66
/-- The constant extension is globally continuous when f is continuous
on the subtype. This is the paper-faithful replacement for the false
`Continuous (intervalDomainLift f)`. -/
theorem constExtend_continuous {f : intervalDomainPoint → ℝ}
    (hf : Continuous f) : Continuous (intervalDomainConstExtend f)
```

It also proves the two congruence facts needed to transfer spectral statements back to the zero lift:

```lean
-- lines 78-82
theorem cosineCoeffs_constExtend_eq_lift (f : intervalDomainPoint → ℝ) (n : ℕ) :
    cosineCoeffs (intervalDomainConstExtend f) n =
    cosineCoeffs (intervalDomainLift f) n

-- lines 96-103
theorem semigroupOperator_constExtend_eq_lift
    {f : intervalDomainPoint → ℝ} {t x : ℝ} :
    intervalFullSemigroupOperator t (intervalDomainConstExtend f) x =
    intervalFullSemigroupOperator t (intervalDomainLift f) x
```

## Spectral bridge with subtype continuity

There is an exact adapter for your use case:

```text
ShenWork/PDE/IntervalSpectralSubtypeAdapter.lean
```

The file header states the problem directly: the closed-interval spectral identity takes `Continuous f` globally on `ℝ`, but Picard calls were using `f = intervalDomainLift g`, whose global continuity is false for positive boundary data.  It says the solution is to use `intervalDomainConstExtend g`, which is globally continuous and indistinguishable from the lift for both the semigroup operator and cosine coefficients.

The main theorem is:

```lean
-- ShenWork/PDE/IntervalSpectralSubtypeAdapter.lean:49-54
theorem intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
    {t : ℝ} (ht : 0 < t) {f : intervalDomainPoint → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs (intervalDomainLift f) n| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator t (intervalDomainLift f) x =
      unitIntervalCosineHeatValue t (cosineCoeffs (intervalDomainLift f)) x
```

The proof is exactly the constant-extension transfer:

```lean
-- lines 62-69
calc intervalFullSemigroupOperator t (intervalDomainLift f) x
    = intervalFullSemigroupOperator t (intervalDomainConstExtend f) x :=
      semigroupOperator_constExtend_eq_lift.symm
  _ = unitIntervalCosineHeatValue t (cosineCoeffs (intervalDomainConstExtend f)) x :=
      ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
        ht (constExtend_continuous hf) hM' hx
  _ = unitIntervalCosineHeatValue t (cosineCoeffs (intervalDomainLift f)) x := by
      rw [hcoef]
```

So: **use this theorem instead of trying to prove `Continuous (intervalDomainLift u₀)`**.

## Does the original spectral bridge take `ContinuousOn`?

The original cleaned bridge does **not** take `ContinuousOn`; it takes global `Continuous f`:

```lean
-- ShenWork/PDE/IntervalFullKernelSpectralClean.lean:28-33
theorem intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator t f x =
      unitIntervalCosineHeatValue t (cosineCoeffs f) x
```

Search for a `ContinuousOn` variant of `intervalFullSemigroupOperator_eq_cosineHeatValue...` did not reveal a clean theorem replacing `hf : Continuous f` by `ContinuousOn f (Icc 0 1)`.  The repo’s solution is the stronger and cleaner subtype-continuity adapter above.

## Practical replacement snippet

Use:

```lean
have hspec :
    intervalFullSemigroupOperator t (intervalDomainLift u₀) x =
      unitIntervalCosineHeatValue t (cosineCoeffs (intervalDomainLift u₀)) x :=
  ShenWork.IntervalSpectralSubtypeAdapter
    .intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
      ht hu₀_cont hM hx
```

where

```lean
hu₀_cont : Continuous u₀
hM : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M
hx : x ∈ Set.Icc (0 : ℝ) 1
```

This is the paper-faithful bridge: `u₀` is continuous on the closed interval subtype, the constant extension supplies the global continuity demanded by the old spectral theorem, and the final statement is still about `intervalDomainLift u₀`.
