# Q1603 (cron1) -- `BddAbove` for `‖iteratedFDeriv‖` of a non-compactly-supported cutoff resolver term

Repository: `xiangyazi24/Shen_work`  
Branch committed: `chatgpt-scratch`  
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Method / caveat

Connector-only inspection.  I did not run Lean locally and did not use Python/sandbox.

I checked the relevant Mathlib lemma names through the GitHub connector and wrote the answer as Lean skeletons that should be inserted into the local Shen_work file and adjusted to existing namespace/import context.

## Short answer

There is **no useful general** theorem of the form

```lean
Continuous.bddAbove_range
```

for arbitrary continuous functions on `ℝ × ℝ`, because it would be false: continuous functions on noncompact domains can be unbounded.

For a **compact set** `K`, the exact Mathlib lemma you want is:

```lean
IsCompact.bddAbove_image
```

Shape:

```lean
theorem IsCompact.bddAbove_image
    (hK : IsCompact K) (hf : ContinuousOn f K) :
    BddAbove (f '' K)
```

For norm bounds, the cleaner lemma is usually:

```lean
IsCompact.exists_bound_of_continuousOn
```

For an additive normed target, it gives:

```lean
∃ C, ∀ x ∈ K, ‖F x‖ ≤ C
```

The source file also has a primed multiplicative original

```lean
IsCompact.exists_bound_of_continuousOn'
```

with a `to_additive` alias named `IsCompact.exists_bound_of_continuousOn`.

There is also

```lean
Continuous.bddAbove_range_of_hasCompactSupport
```

but that is only for compactly supported scalar/order-valued functions.  It is not applicable to your full resolver term because the cutoff is right-constant `1` for `t ≥ c`, not compactly supported.

## Compact-image / compact-bound snippets

Let

```lean
F q = iteratedFDeriv ℝ j f q
D q = ‖F q‖
```

and suppose

```lean
hf : ContDiff ℝ (2 : ℕ∞) f
hj : (j : ℕ∞) ≤ (2 : ℕ∞)
```

Then continuity of the iterated derivative is:

```lean
have hFcont : Continuous (fun q : ℝ × ℝ => iteratedFDeriv ℝ j f q) :=
  hf.continuous_iteratedFDeriv (by exact_mod_cast hj)

have hDcont : Continuous (fun q : ℝ × ℝ => ‖iteratedFDeriv ℝ j f q‖) :=
  hFcont.norm
```

For a compact rectangle:

```lean
open Set

have hK : IsCompact (Icc (c / 2) c ×ˢ Icc (-R) R) :=
  isCompact_Icc.prod isCompact_Icc
```

If you literally want `BddAbove` of the image over that compact rectangle:

```lean
have hbddK : BddAbove
    ((fun q : ℝ × ℝ => ‖iteratedFDeriv ℝ j f q‖) ''
      (Icc (c / 2) c ×ˢ Icc (-R) R)) :=
  hK.bddAbove_image hDcont.continuousOn
```

If you want a pointwise numerical bound, this is usually easier:

```lean
rcases hK.exists_bound_of_continuousOn hFcont.continuousOn with ⟨C, hC⟩
-- hC : ∀ q ∈ Icc (c / 2) c ×ˢ Icc (-R) R,
--        ‖iteratedFDeriv ℝ j f q‖ ≤ C
```

That avoids unpacking `BddAbove` of an image.

## Big warning: `[c/2,c] × [-R,R]` does not cover the middle strip

Your domain is all `ℝ × ℝ`.  The compact rectangle

```lean
Icc (c / 2) c ×ˢ Icc (-R) R
```

only bounds the part with `|x| ≤ R`.  It does **not** bound the whole middle strip

```lean
{q : ℝ × ℝ | c / 2 ≤ q.1 ∧ q.1 ≤ c}
```

because `q.2` is still unbounded.

So, from just

```lean
ContDiff ℝ 2 f
f q = 0 for q.1 < c / 2
```

you cannot prove the desired global `BddAbove`.  Counterexample shape:

```lean
f(t,x) = smoothRightCutoff (c / 2) c t * x^2
```

This is `ContDiff`, zero on the left, but unbounded on the middle strip in `x`.

For the resolver term, the missing input is the special product/trigonometric structure:

```lean
f(t,x) = A(t) * cos(k * π * x)
```

and all `x`-derivatives of `cos(kπx)` are globally bounded.  Therefore the right proof should compactify only the **time** variable, and use global cosine derivative bounds for the space variable.

## Recommended global `BddAbove` lemma: split by time

Use a purely order/topology wrapper that assumes explicit bounds on the three time regions.

```lean
private theorem bddAbove_range_norm_of_left_mid_tail
    {E : Type*} [SeminormedAddCommGroup E]
    {F : ℝ × ℝ → E} {a b Cmid Ctail : ℝ}
    (hleft : ∀ q : ℝ × ℝ, q.1 < a → ‖F q‖ = 0)
    (hmid : ∀ q : ℝ × ℝ, a ≤ q.1 → q.1 ≤ b → ‖F q‖ ≤ Cmid)
    (htail : ∀ q : ℝ × ℝ, b < q.1 → ‖F q‖ ≤ Ctail) :
    BddAbove (Set.range fun q : ℝ × ℝ => ‖F q‖) := by
  refine ⟨max 0 (max Cmid Ctail), ?_⟩
  rintro _ ⟨q, rfl⟩
  by_cases hqa : q.1 < a
  · rw [hleft q hqa]
    exact le_max_left 0 (max Cmid Ctail)
  · have hqa' : a ≤ q.1 := le_of_not_gt hqa
    by_cases hqb : q.1 ≤ b
    · exact (hmid q hqa' hqb).trans
        ((le_max_left Cmid Ctail).trans (le_max_right 0 (max Cmid Ctail)))
    · have hqb' : b < q.1 := lt_of_not_ge hqb
      exact (htail q hqb').trans
        ((le_max_right Cmid Ctail).trans (le_max_right 0 (max Cmid Ctail)))
```

Then instantiate with:

```lean
F := fun q : ℝ × ℝ => iteratedFDeriv ℝ j f q
```

This is the clean replacement for trying to get a global bound from compactness alone.

## How to prove the middle bound correctly

For the actual cutoff resolver term, do not use `[c/2,c] × [-R,R]` unless you have a periodic reduction lemma.  Instead use product Leibniz.

Set

```lean
A t := smoothRightCutoff (c / 2) c t * resolverTimeCoeff p u k t
B x := cosineMode k x
f q := A q.1 * B q.2
```

On the time interval `[c/2,c]`, compactness gives a bound for each time derivative of `A`:

```lean
private theorem compact_time_deriv_bound
    {A : ℝ → E} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {i : ℕ}
    (hA : ContDiff ℝ (2 : ℕ∞) A)
    (hi : (i : ℕ∞) ≤ (2 : ℕ∞)) :
    ∃ C, ∀ t ∈ Set.Icc a b, ‖iteratedFDeriv ℝ i A t‖ ≤ C := by
  have hcont : Continuous (fun t : ℝ => iteratedFDeriv ℝ i A t) :=
    hA.continuous_iteratedFDeriv (by exact_mod_cast hi)
  exact isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
```

Then combine:

1. `norm_iteratedFDeriv_mul_le` for the product;
2. `norm_iteratedFDeriv_comp_fst_le` for `A ∘ Prod.fst`;
3. `norm_iteratedFDeriv_comp_snd_le` for `B ∘ Prod.snd`;
4. a global cosine derivative bound, e.g. the existing cosine-mode bound in the project;
5. the finite Leibniz sum.

The middle-bound target should be:

```lean
∃ Cmid : ℝ, ∀ q : ℝ × ℝ,
  c / 2 ≤ q.1 → q.1 ≤ c →
  ‖iteratedFDeriv ℝ j f q‖ ≤ Cmid
```

not a bound merely on `q.2 ∈ [-R,R]`.

## Left side: cutoff-local-zero

For strict left side, use eventual equality to zero and transfer through `iteratedFDeriv`.

```lean
private theorem iteratedFDeriv_left_zero_of_eventually_zero
    {f : ℝ × ℝ → ℝ} {a : ℝ} (j : ℕ) (q : ℝ × ℝ)
    (hev : f =ᶠ[𝓝 q] fun _ : ℝ × ℝ => (0 : ℝ)) :
    ‖iteratedFDeriv ℝ j f q‖ = 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · rw [norm_iteratedFDeriv_zero, hev.eq_of_nhds, norm_zero]
  · have hev' := Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev j
    have hz := hev'.eq_of_nhds
    rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hjpos), Pi.zero_apply] at hz
    rw [hz, norm_zero]
```

For your cutoff term, build `hev` from

```lean
Iio_mem_nhds hq
smoothRightCutoff_eq_zero_of_le
```

exactly as in the existing heat/cutoff proofs.

## Right tail: use an explicit tail bound, not compactness

For `q.1 > c`, the cutoff is locally `1`, and positive-order derivatives of the cutoff are locally zero.  The tail should be bounded directly from the resolver coefficient bounds and global cosine derivative bounds.

Target shape:

```lean
∃ Ctail : ℝ, ∀ q : ℝ × ℝ, c < q.1 →
  ‖iteratedFDeriv ℝ j f q‖ ≤ Ctail
```

For nonzero modes, exponential heat damping can give decay.  For the zeroth mode, do **not** require decay to zero; boundedness or finite limit is enough.

## Final answer to the lemma-name question

Use these names:

```lean
-- scalar BddAbove of compact image:
hK.bddAbove_image hDcont.continuousOn

-- direct norm bound on compact set:
hK.exists_bound_of_continuousOn hFcont.continuousOn

-- compact-support global range only if truly compactly supported:
hf.bddAbove_range_of_hasCompactSupport hsupport
-- or for norm-valued compact support:
hf.bounded_above_of_compact_support hsupport
```

But for the resolver cutoff term, the final global proof should be:

```lean
left zero
+ middle strip bound using compact time interval and global cosine bounds
+ right tail bound using resolver/heat estimates
⇒ BddAbove (Set.range fun q => ‖iteratedFDeriv ℝ j f q‖)
```

not a direct application of any single compactness lemma to the whole range.
