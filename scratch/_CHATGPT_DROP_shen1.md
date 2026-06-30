# Q2451 shen1 — proof-tail patch for integrated Moser time-integral lemmas

Repo: `xiangyazi24/Shen_work`

Context: local patch in `ShenWork/PDE/P3MoserIntegratedClosure.lean` adds

```lean
intervalIntegral_le_const_mul_integral_add_length_mul_const_of_le_on
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
```

The remote `main` copy I can see still only has the Stage 1 closure file, so the code below is written as replacement proof tails for the theorem shapes described in the prompt.  It avoids statement changes and uses the current imported interval-integral APIs already used elsewhere in the repo.

## 1. Robust proof for the generic affine interval-integral helper

The failure mode you describe comes from rewriting `integral_add`/`integral_const_mul` directly in a target where Lean can rewrite inside the intended right-hand side too.  The robust pattern is:

1. define the affine RHS integrand as a local function `H`;
2. prove `∫ F ≤ ∫ H` by `intervalIntegral.integral_mono_on`;
3. prove `∫ H = A * ∫ G + (b - a) * B` as a separate `hH_eval` using small local equalities;
4. finish by `calc`.

Use this body for the helper, adapting only hypothesis names if your local theorem uses different names:

```lean
/-- Integrate a pointwise affine upper bound over an oriented interval with
`a ≤ b`.  Keeping the affine integrand as `H` avoids over-eager `rw` into the
right-hand side. -/
theorem intervalIntegral_le_const_mul_integral_add_length_mul_const_of_le_on
    {F G : ℝ → ℝ} {a b A B : ℝ}
    (hab : a ≤ b)
    (hF_int : IntervalIntegrable F MeasureTheory.volume a b)
    (hG_int : IntervalIntegrable G MeasureTheory.volume a b)
    (hpoint : ∀ s ∈ Set.Icc a b, F s ≤ A * G s + B) :
    (∫ s in a..b, F s) ≤
      A * (∫ s in a..b, G s) + (b - a) * B := by
  let H : ℝ → ℝ := fun s => A * G s + B
  have hconst_int :
      IntervalIntegrable (fun _s : ℝ => B) MeasureTheory.volume a b :=
    intervalIntegrable_const
  have hH_int : IntervalIntegrable H MeasureTheory.volume a b := by
    simpa [H] using (hG_int.const_mul A).add hconst_int
  have hmono :
      (∫ s in a..b, F s) ≤ ∫ s in a..b, H s :=
    intervalIntegral.integral_mono_on hab hF_int hH_int (by
      intro s hs
      simpa [H] using hpoint s hs)
  have hadd :
      (∫ s in a..b, H s) =
        (∫ s in a..b, A * G s) + (∫ _s in a..b, B) := by
    simpa [H] using
      (intervalIntegral.integral_add (hG_int.const_mul A) hconst_int)
  have hmul :
      (∫ s in a..b, A * G s) = A * (∫ s in a..b, G s) := by
    rw [intervalIntegral.integral_const_mul]
  have hconst :
      (∫ _s in a..b, B) = (b - a) * B := by
    rw [intervalIntegral.integral_const]
    ring
  calc
    (∫ s in a..b, F s) ≤ ∫ s in a..b, H s := hmono
    _ = A * (∫ s in a..b, G s) + (b - a) * B := by
      rw [hadd, hmul, hconst]
```

If your theorem statement already has the constant integrability hypothesis implicitly or imports enough to infer it, keep the explicit `hconst_int`; it makes both `hH_int` and `integral_add` inference stable.

### If your statement does not have `hab : a ≤ b`

For this lemma as stated over `Set.Icc a b`, you really want `hab : a ≤ b`.  `intervalIntegral.integral_mono_on` is the right API for this proof and it requires the nonnegative orientation.  If the local theorem currently lacks `hab`, adding it is the one statement change I would consider necessary.  Without `a ≤ b`, the oriented integral inequality has the wrong sign in the reversed interval case.

## 2. Tail for `relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound`

The internal use should call the helper above rather than manually rewriting the integral.  The proof tail should look like this after you obtain the relative-Moser constant `Ceps` and have the current `Lp` bound on `Y_p` over the window.

Use the same local abbreviations consistently:

```lean
let F : ℝ → ℝ := fun s =>
  D.integral (fun x => (u s x) ^ (p + rho))
let G : ℝ → ℝ := fun s =>
  D.integral (fun x =>
    (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)
```

Then build the pointwise affine bound:

```lean
have hpoint :
    ∀ s ∈ Set.Icc a b, F s ≤ eps * G s + Ceps * Cp := by
  intro s hs
  have hs0 : 0 < s := lt_of_lt_of_le ha_pos hs.1
  have hsT : s < T := lt_of_le_of_lt hs.2 hb_lt
  have hrel_s := hCeps s hs0 hsT
  have hYp_s :
      D.integral (fun x => (u s x) ^ p) ≤ Cp :=
    hCp s hs0 hsT
  have hscaled :
      Ceps * D.integral (fun x => (u s x) ^ p) ≤ Ceps * Cp :=
    mul_le_mul_of_nonneg_left hYp_s hCeps_nonneg
  dsimp [F, G]
  linarith
```

and finish with the affine helper:

```lean
exact
  intervalIntegral_le_const_mul_integral_add_length_mul_const_of_le_on
    (F := F) (G := G) (a := a) (b := b)
    (A := eps) (B := Ceps * Cp)
    hab hF_int hG_int hpoint
```

Here:

- `hab : a ≤ b`
- `ha_pos : 0 < a`
- `hb_lt : b < T`
- `hF_int` is integrability of the higher-power time profile on `a..b`
- `hG_int` is integrability of the Moser-gradient time profile on `a..b`
- `hCp` is the current `Lp` bound, typically from unpacking `LpPowerBoundedBefore D p T u`
- `hCeps` and `hCeps_nonneg` come from `hrel p hp eps heps`

This avoids any direct `rw` of the final affine integral expression.

## 3. Tail for `relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound`

The issue here is only additive order.  Do not try to force `add_le_add_right` or `add_le_add_left` to match.  Let `linarith` close the final additive comparison from the scaled gradient inequality.

Suppose the previous lemma gives:

```lean
have htime :
    (∫ s in a..b,
      D.integral (fun x => (u s x) ^ (p + rho))) ≤
      eps * (∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) +
        (b - a) * (Ceps * Cp) :=
  relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound
    ...
```

and you have:

```lean
hgradBound :
  (∫ s in a..b,
    D.integral (fun x =>
      (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) ≤ Gbound
```

then replace the failing tail with:

```lean
have hscaled :
    eps * (∫ s in a..b,
      D.integral (fun x =>
        (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) ≤
      eps * Gbound :=
  mul_le_mul_of_nonneg_left hgradBound (le_of_lt heps)
exact htime.trans (by linarith)
```

This is robust to whether the target has the rest term elaborated as

```lean
eps * Gbound + (b - a) * (Ceps * Cp)
```

or a definitional equivalent expression.  `linarith` treats the integral and product subterms as atoms and uses `hscaled` to close the additive comparison.

If your local theorem uses `heps_nonneg : 0 ≤ eps` instead of `heps : 0 < eps`, use:

```lean
have hscaled :
    eps * (∫ s in a..b,
      D.integral (fun x =>
        (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) ≤
      eps * Gbound :=
  mul_le_mul_of_nonneg_left hgradBound heps_nonneg
exact htime.trans (by linarith)
```

## 4. Minimal patch summary

The only source-level changes needed should be:

1. Replace the body of `intervalIntegral_le_const_mul_integral_add_length_mul_const_of_le_on` with the `H`-based proof above.
2. In `relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound`, call the helper instead of rewriting affine integrals manually.
3. In `relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound`, replace the failing `add_le_add_right hscaled _` tail with:

```lean
exact htime.trans (by linarith)
```

after defining `hscaled` with `mul_le_mul_of_nonneg_left`.

## 5. Import/naming caveats

No new imports should be needed if `P3MoserIntegratedClosure.lean` still imports:

```lean
import ShenWork.PDE.P3MoserDissipationShape
```

and has:

```lean
open MeasureTheory
open scoped Interval
```

The proof uses:

```lean
IntervalIntegrable
intervalIntegrable_const
intervalIntegral.integral_mono_on
intervalIntegral.integral_add
intervalIntegral.integral_const_mul
intervalIntegral.integral_const
```

which are already available through the existing import stack used by the file.

If Lean cannot infer the constant integrability type, keep the explicit annotation:

```lean
have hconst_int :
    IntervalIntegrable (fun _s : ℝ => B) MeasureTheory.volume a b :=
  intervalIntegrable_const
```

That is the most important stability trick for the helper.
