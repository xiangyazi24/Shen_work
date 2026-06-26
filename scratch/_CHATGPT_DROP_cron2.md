# Q822 (cron2) — `intervalDomainLift` eventual equality near an interior point

Static repo inspection only; I did not run a local Lean build.

## Short answer

Yes. The repo already has the exact product-neighborhood pattern you want.

Best reference:

```text
ShenWork/PDE/IntervalIteratePicardJointC2.lean
```

The theorem is:

```lean
theorem iterate_lift_jointContDiffAt_two
    {u : ℝ → intervalDomainPoint → ℝ} {c : ℕ → ℝ → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : IteratePicardJointC2Data u c Bt) {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x) := by
  have hseries : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' k : ℕ, boundedWeightJointTerm c k q) :=
    boundedWeightJointSeries_contDiff_two H.coeff_contDiff
      (fun i k t hi => H.coeff_bound i k t hi) H.value_summable
  refine (hseries.contDiffAt).congr_of_eventuallyEq ?_
  have hmem : {q : ℝ × ℝ | q.2 ∈ Ioo (0 : ℝ) 1} ∈ 𝓝 (s, x) :=
    (isOpen_Ioo.preimage continuous_snd).mem_nhds hx
  filter_upwards [hmem] with q hq
  have he := H.lift_eq_series (t := q.1) (x := q.2) (Ioo_subset_Icc_self hq)
  simpa [boundedWeightJointTerm] using he
```

This is the clean template for sub-sorry 3B.  It does **not** separately prove

```lean
intervalDomainLift (u q.1) q.2 = (u q.1) ⟨q.2, _⟩
```

as an intermediate target.  Instead it keeps the proof nondependent by using the already-packaged slice agreement

```lean
H.lift_eq_series : ∀ {t x : ℝ}, x ∈ Icc (0 : ℝ) 1 →
  intervalDomainLift (u t) x = ∑' k : ℕ, c k t * cosineMode k x
```

and then makes that agreement eventual near `(s,x)` by restricting only the second coordinate to `Ioo 0 1`.

## Why this is the right pattern for 3B

Your target has the same left-hand side:

```lean
fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2
```

The existing proof turns a global or per-time `EqOn ... (Icc 0 1)` statement into an eventual equality at `(s,x)` by:

```lean
have hmem : {q : ℝ × ℝ | q.2 ∈ Ioo (0 : ℝ) 1} ∈ 𝓝 (s, x) :=
  (isOpen_Ioo.preimage continuous_snd).mem_nhds hx
filter_upwards [hmem] with q hq
have hxIcc : q.2 ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hq
-- apply the slice EqOn at time q.1 and space q.2
```

Then it applies `ContDiffAt.congr_of_eventuallyEq` in the orientation from Q816:

```lean
refine (hseries.contDiffAt).congr_of_eventuallyEq ?_
```

where the proof obligation is:

```lean
(fun q => intervalDomainLift (u q.1) q.2)
  =ᶠ[𝓝 (s,x)]
(fun q => cosine-series q.1 q.2)
```

## Adapting it to `hagree_zero`

For level 0, `hagree_zero` in

```text
ShenWork/Paper2/IntervalPicardIterateRepresentation.lean
```

has the fixed-time shape:

```lean
theorem hagree_zero ... {σ M₀ : ℝ} (hσ : 0 < σ) ... :
  Set.EqOn (intervalDomainLift (picardIter p u₀ 0 σ))
    (fun x => ∑' k, iterateReprCoeff p u₀ 0 σ k * cosineMode k x)
    (Set.Icc (0 : ℝ) 1)
```

So if your 3B point has `hs : 0 < s`, add a time-neighborhood restriction as well:

```lean
have htime : {q : ℝ × ℝ | 0 < q.1} ∈ 𝓝 (s, x) :=
  (isOpen_Ioi.preimage continuous_fst).mem_nhds hs
have hspace : {q : ℝ × ℝ | q.2 ∈ Ioo (0 : ℝ) 1} ∈ 𝓝 (s, x) :=
  (isOpen_Ioo.preimage continuous_snd).mem_nhds hx
filter_upwards [htime, hspace] with q hq_time hq_space
have hxIcc : q.2 ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hq_space
have heqon :=
  ShenWork.IntervalPicardIterateRepresentation.hagree_zero
    p u₀ (σ := q.1) (M₀ := M₀) hq_time hu₀_cont hu₀_bound
have he := heqon q.2 hxIcc
-- `he` is the pointwise equality needed for the eventual equality.
```

Depending on whether your `u` is definitionally `picardIter p u₀ 0` or a local alias/wrapper such as `conjugatePicardIter p u₀ 0`, the final line will be some `simpa [...] using he`, possibly unfolding the level-0 wrapper and the series term definition.

## Supporting examples in the repo

There are two other useful patterns:

1. `IntervalLiftEndpointDeriv.lean` has exterior-neighborhood eventual equalities for the lift:

```lean
theorem lift_eventuallyEq_zero_Iio
    (f : intervalDomainPoint → ℝ) {x : ℝ} (hx : x < 0) :
    intervalDomainLift f =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
  have hmem : Set.Iio (0 : ℝ) ∈ nhds x := isOpen_Iio.mem_nhds hx
  filter_upwards [hmem] with z hz
  have hzn : z ∉ Set.Icc (0 : ℝ) 1 := by
    intro hcon; exact absurd hcon.1 (not_le.2 hz)
  exact lift_eq_zero_of_not_mem f hzn
```

and similarly for `Ioi 1`.  This is the same `open set ∈ nhds` + `filter_upwards` style, but for the outside branch of `intervalDomainLift`.

2. `IntervalPicardLimitTimeNhd.lean` has a time-neighborhood spectral-agreement proof that uses an open time neighborhood, then unfolds the lift at a subtype point with `dif_pos`:

```lean
filter_upwards [hopen.mem_nhds hmem] with s hs
...
have hx1 : x.1 ∈ Set.Icc (0:ℝ) 1 := x.2
have hlift : u s x = intervalDomainLift (u s) x.1 := by
  simp only [intervalDomainLift, hx1, dif_pos, Subtype.eta]
rw [hlift, heqon hx1]
```

This is not the full product-neighborhood proof, but it is a useful example of the `dif_pos`/`EqOn` bridge around `intervalDomainLift`.

## Recommendation for sub-sorry 3B

Use `IntervalIteratePicardJointC2.iterate_lift_jointContDiffAt_two` as the direct model.  For level 0, the main difference is that `hagree_zero` needs a positive time hypothesis, so include the extra eventual restriction

```lean
{q : ℝ × ℝ | 0 < q.1} ∈ 𝓝 (s,x)
```

via `continuous_fst`.  Avoid proving a separate dependent-subtype equality unless you absolutely need it; the existing successful pattern goes directly from `intervalDomainLift` to the cosine representative by applying the `EqOn` theorem on `Icc` after shrinking spatially to `Ioo`.
