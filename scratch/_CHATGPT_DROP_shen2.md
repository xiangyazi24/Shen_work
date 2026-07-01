# Q2867 shen2: coefficient-gap lemma for integrated Moser surplus

Repo target: `xiangyazi24/Shen_work`, Lean 4.

The current local theorem has a surplus input of the form

```lean
hsurplus :
  ∀ p hp A K, 0 < A → 0 < K →
    ∃ eps > 0, (p * K) * eps ≤ p * A - theta
```

Yes: this is naturally derivable from a coefficient gap assumption

```lean
theta < p * A
```

The cleanest lemma depends on whether the caller already knows `0 < p`.

## Robust lemma matching the current `hsurplus` shape

Because the displayed `hsurplus` does not include `0 < p`, the most robust epsilon choice is

```lean
eps := (p * A - theta) / (2 * (|p * K| + 1))
```

rather than `(p*A-theta)/(2*(p*K+1))`. This avoids needing to prove `0 < p*K + 1`. It only needs the gap `theta < p*A`; the hypotheses `0<A` and `0<K` can be accepted for API compatibility but are not needed by the scalar proof.

Place this near the scalar absorption/window-coefficient lemmas in

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
```

It is independent of PDE definitions except for the file’s existing imports of real arithmetic/tactics.

```lean
/-- A positive coefficient gap gives an epsilon small enough for the integrated
Moser absorption surplus.

This version does not require `0 < p`.  The absolute value in the denominator
makes the denominator positive for all real `p*K`; if `p*K < 0`, the target
inequality is immediate because the left side is nonpositive. -/
theorem exists_pos_eps_mul_le_sub_of_coeff_gap
    {p A K theta : ℝ}
    (hgap : theta < p * A) :
    ∃ eps : ℝ, 0 < eps ∧ (p * K) * eps ≤ p * A - theta := by
  let N : ℝ := p * A - theta
  let den : ℝ := 2 * (|p * K| + 1)
  have hN : 0 < N := by
    dsimp [N]
    linarith
  have hden : 0 < den := by
    dsimp [den]
    have habs : 0 ≤ |p * K| := abs_nonneg _
    nlinarith
  refine ⟨N / den, div_pos hN hden, ?_⟩
  by_cases hx : 0 ≤ p * K
  · have hratio : (p * K) / den ≤ 1 := by
      rw [div_le_one hden]
      dsimp [den]
      have hle_abs : p * K ≤ |p * K| := le_abs_self _
      have hle_den : |p * K| ≤ 2 * (|p * K| + 1) := by
        nlinarith [abs_nonneg (p * K)]
      exact le_trans hle_abs hle_den
    calc
      (p * K) * (N / den)
          = N * ((p * K) / den) := by
            ring_nf
      _ ≤ N * 1 := mul_le_mul_of_nonneg_left hratio hN.le
      _ = N := by ring
  · have hxneg : p * K < 0 := lt_of_not_ge hx
    have hprod_nonpos : (p * K) * (N / den) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hxneg.le (div_nonneg hN.le hden.le)
    exact le_trans hprod_nonpos hN.le
```

Then wrap it in the exact API shape:

```lean
/-- Package the coefficient-gap hypothesis in the shape expected by
`integratedHigherPowerEnergyWindowCoeffFrontier_of_LpBootstrapEnergyInequality`. -/
theorem surplus_of_coeff_gap
    {theta p0 : ℝ}
    (hgap : ∀ p, p0 ≤ p → ∀ A K, 0 < A → 0 < K → theta < p * A) :
    ∀ p, p0 ≤ p → ∀ A K, 0 < A → 0 < K →
      ∃ eps : ℝ, 0 < eps ∧ (p * K) * eps ≤ p * A - theta := by
  intro p hp A K hA hK
  exact exists_pos_eps_mul_le_sub_of_coeff_gap
    (p := p) (A := A) (K := K) (theta := theta)
    (hgap p hp A K hA hK)
```

This is the safest theorem for the current `hsurplus` signature.

## Simpler lemma if `0 < p` is available

If the integrated route already has `hp_pos : ∀ p, p0 ≤ p → 0 < p`, then the more intuitive choice from the prompt also works:

```lean
eps := (p * A - theta) / (2 * (p * K + 1))
```

The theorem can be:

```lean
/-- Positive-`p` version using the simpler denominator `2*(p*K+1)`. -/
theorem exists_pos_eps_mul_le_sub_of_coeff_gap_pos_p
    {p A K theta : ℝ}
    (hp : 0 < p) (hK : 0 < K) (hgap : theta < p * A) :
    ∃ eps : ℝ, 0 < eps ∧ (p * K) * eps ≤ p * A - theta := by
  let N : ℝ := p * A - theta
  let den : ℝ := 2 * (p * K + 1)
  have hN : 0 < N := by
    dsimp [N]
    linarith
  have hpK_nonneg : 0 ≤ p * K := mul_nonneg hp.le hK.le
  have hden : 0 < den := by
    dsimp [den]
    nlinarith
  refine ⟨N / den, div_pos hN hden, ?_⟩
  have hratio : (p * K) / den ≤ 1 := by
    rw [div_le_one hden]
    dsimp [den]
    nlinarith
  calc
    (p * K) * (N / den)
        = N * ((p * K) / den) := by
          ring_nf
    _ ≤ N * 1 := mul_le_mul_of_nonneg_left hratio hN.le
    _ = N := by ring
```

And a packaged version:

```lean
theorem surplus_of_coeff_gap_pos_p
    {theta p0 : ℝ}
    (hp_pos : ∀ p, p0 ≤ p → 0 < p)
    (hgap : ∀ p, p0 ≤ p → ∀ A K, 0 < A → 0 < K → theta < p * A) :
    ∀ p, p0 ≤ p → ∀ A K, 0 < A → 0 < K →
      ∃ eps : ℝ, 0 < eps ∧ (p * K) * eps ≤ p * A - theta := by
  intro p hp A K hA hK
  exact exists_pos_eps_mul_le_sub_of_coeff_gap_pos_p
    (p := p) (A := A) (K := K) (theta := theta)
    (hp_pos p hp) hK (hgap p hp A K hA hK)
```

## Which version should be added?

Add the robust `abs` denominator version first. It matches the current `hsurplus` shape exactly and avoids threading `0 < p` through the surplus lemma. It is also harmless if later you do have `0 < p`.

If you want the displayed epsilon to be the cleaner `(p*A-theta)/(2*(p*K+1))`, use the positive-`p` version and pass `hp_pos`. In the integrated Moser route, such an `hp_pos` is usually available from the bootstrap threshold, but the robust lemma keeps this proof independent of those PDE/bootstrap facts.

## Expected use

At the call site:

```lean
have hsurplus :
    ∀ p, p0 ≤ p → ∀ A K, 0 < A → 0 < K →
      ∃ eps : ℝ, 0 < eps ∧ (p * K) * eps ≤ p * A - theta :=
  surplus_of_coeff_gap hgap
```

where the new simpler gap hypothesis is:

```lean
hgap : ∀ p, p0 ≤ p → ∀ A K, 0 < A → 0 < K → theta < p * A
```

This is a purely scalar layer and should compile independently of the PDE route.
