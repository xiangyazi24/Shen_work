# Q840 / cron1: is `3A-sub` still reachable after `level0_chemDiv_envelope_summable` restructuring?

Repo inspected: `xiangyazi24/Shen_work`

Source ref inspected: `main`

Branch written: `chatgpt-scratch`

## Grep result

Command requested:

```bash
grep -n "hcont_slices\|3A-sub" ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
```

Result on current `main` content:

```text
# hcont_slices: no matches
960-ish: sorry -- [SUB-SORRY 3A-sub: requires upstream weakening of ContinuousOn to IntervalIntegrable ...]
1038-ish: sorry -- [SUB-SORRY 3A-sub: per-slab continuity, τ ≤ 0 case ...]
```

So: **`hcont_slices` is gone**, but **`3A-sub` is still present and reachable**.

## Precise verdict

The restructuring eliminated the old envelope-path need for per-slice

```lean
ContinuousOn (coupledChemDivSourceLift ...) (Icc 0 1)
```

inside `level0_chemDiv_envelope_summable`.

`hSup` now asks for:

```lean
IntervalIntegrable (coupledChemDivSourceLift ...) volume 0 1
```

plus a pointwise `Icc` sup bound, not `ContinuousOn`.  The theorem then obtains

```lean
hint_slices, hsup_slices
```

from `hSup`, and the zero-mode coefficient estimate uses:

```lean
cosineCoeffs_abs_le_of_integrable_bounded
  (hint_slices s hs) hMsupnn (hsup_slices s hs) 0
```

This confirms that the **envelope** no longer needs `hcont_slices` or per-slice `ContinuousOn` of the actual zero-extension source.

## Why `3A-sub` is still reachable

`3A-sub` survived in the **time-derivative data** theorem, not in the envelope theorem.

Specifically, in `level0_chemDiv_timeDerivData`, the proof builds

```lean
hfluxC2 : CoupledChemDivFluxJointC2Hyp p (conjugatePicardIter p u₀ 0)
```

by applying

```lean
coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
```

The first field `F1` is still the per-slab source-continuity field:

```lean
∀ᶠ s in 𝓝 τ,
  ContinuousOn (coupledChemDivSourceLift p (...) s) (Icc 0 1)
```

and that field is exactly where the positive-time `3A-sub` sorry remains.

The comments in the file explicitly say this is still a boundary obstruction, and the proposed fix is to weaken the upstream structures from closed-interval `ContinuousOn` to `IntervalIntegrable` / dominated-convergence-style hypotheses.

## Dependency path

The remaining reachable path is:

```text
level0_chemDiv_timeDerivData
  → hfluxC2 : CoupledChemDivFluxJointC2Hyp
    → F1 per-slab source continuity
      → SUB-SORRY 3A-sub
  → coupledChemDivLocalChainRule_of_fluxJointC2 hfluxC2
  → hchain.exists_local_slab
  → hjointcont / hderiv / DuhamelSourceTimeC1On time-derivative data
```

So `3A-sub` is not dead code.  It is no longer needed for the **coefficient envelope**, but it is still needed for the **chain-rule / coefficient time-derivative route**.

## Practical conclusion

The architectural restructuring solved the envelope-side boundary obstruction, but not the time-derivative-side one.

The next fix should target the structures feeding `CoupledChemDivLocalChainRule`: weaken the F1/source-continuity requirement from

```lean
ContinuousOn (coupledChemDivSourceLift p u s) (Icc 0 1)
```

to an integrability/a.e. or smooth-representative formulation sufficient for the time-Leibniz integral step.  Until that upstream weakening happens, `3A-sub` remains reachable from `level0_chemDiv_timeDerivData`.
