# Q1143 cron2

Static GitHub connector inspection only. I did not run Lean locally.

Yes. Add these helpers in `IntervalConjugateLevel0BFormSourceOn.lean` inside `namespace ShenWork.Paper2.ConjugateLevel0BFormSourceOn`.

```lean
theorem intervalNeumannResolverR_nonneg_of_continuous_nonneg
    (p : CM2Params) {w : intervalDomainPoint → ℝ}
    (hw_cont : Continuous w)
    (hw_nonneg : ∀ x : intervalDomainPoint, 0 ≤ w x) :
    ∀ y : intervalDomainPoint, 0 ≤ intervalNeumannResolverR p w y := by
  intro yp
  -- paste the existing lines 590-691 chain here, replacing the local proofs of
  -- `hw_cont` and `hw_nonneg` by the two hypotheses above.
  -- The internal structure is unchanged:
  --   hcont_on, clip, hf_cont, hf_nonneg, hf_coeff, hsrc_l2,
  --   intervalNeumannResolverR_nonneg_of_nonneg_source ... yp
```

Then add wrappers:

```lean
theorem intervalNeumannResolverR_nonneg_on_Icc_of_continuous_nonneg
    (p : CM2Params) {w : intervalDomainPoint → ℝ}
    (hw_cont : Continuous w)
    (hw_nonneg : ∀ x : intervalDomainPoint, 0 ≤ w x) :
    ∀ x : ℝ, ∀ hx : x ∈ Icc (0 : ℝ) 1,
      0 ≤ intervalNeumannResolverR p w ⟨x, hx⟩ := by
  intro x hx
  exact intervalNeumannResolverR_nonneg_of_continuous_nonneg
    p hw_cont hw_nonneg ⟨x, hx⟩
```
