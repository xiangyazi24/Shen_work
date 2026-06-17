## Bottom line

`α ≤ m + γ - 1` is a **faithful paper hypothesis** for the χ≤0 traveling-wave existence theorem. Keep it in the formal theorem that is meant to mirror Theorem 1.1(1).

However, your diagnosis about the **logistic loss alone** is also correct: the bound

```text
(U⁻)^{α+1} ≤ e^{-(α+1)κx} ≤ e^{-κ̃x}
```

uses only

```text
κ̃ ≤ (α+1)κ,
```

not `α ≤ m+γ-1`. The place where `α ≤ m+γ-1` matters is the **chemotaxis exponent comparison**, especially the `γκ < 1` branch, where losses of order `e^{-(m+γ)κx}` must be absorbed by the scalar margin `e^{-κ̃x}`. The paper gets

```text
κ̃ ≤ (α+1)κ ≤ (m+γ)κ
```

from `α ≤ m+γ-1`.

So: **do not use `α ≤ m+γ-1` for the logistic estimate; do keep it for the faithful negative-χ theorem and for the chemotaxis exponent comparison under the paper’s stated κ̃-window.**

---

## (1) Does the paper assume `α ≤ m+γ−1`?

Yes. The paper’s Theorem 1.1(1), the χ≤0 existence theorem, explicitly assumes

```text
α ≤ m + γ − 1  and  χ ≤ 0.
```

Then it states existence of a monotone traveling wave for speeds `c > c*_{χ,m,γ}`. citeturn101802view0

This is not just a stability/uniqueness condition. The stability and uniqueness theorems also assume it in the χ<0 branch, but the existence theorem itself already has it. citeturn902247view1

It also appears explicitly in Lemma 4.1, the super-solution lemma: the negative-sensitivity case assumes `α ≤ m+γ−1`, `χ≤0`, and the corresponding speed/`M` conditions. citeturn866674view0 In its proof, the paper states “Case 1” under `χ≤0, α≤m+γ−1`, then uses `α≤m+γ−1` in the exponential comparison for the upper barrier `e^{-κx}`. citeturn866674view1

For Lemma 4.2 specifically, the printed statement of the lower-solution lemma lists

```text
0 < κ < κ̃ ≤ min{(1+α)κ, mκ + 1/2, 1},  M ≥ 1,
```

and then states the subsolution result for `D > D_{M,κ,κ̃,χ,m,γ}`. It does **not** visibly repeat `α≤m+γ−1` in the lemma statement. citeturn902247view4 But the χ≤0 existence route in which it is used is already under `α≤m+γ−1`, and the exponent comparison needed to package all loss terms into the same `e^{-κ̃x}` margin is supplied by that theorem-level hypothesis.

In Lean, I would not try to prove the paper’s Theorem 1.1(1) without:

```lean
(hα_le : p.α ≤ p.m + p.γ - 1)
```

or equivalently:

```lean
(hα1_le : p.α + 1 ≤ p.m + p.γ)
```

depending on how your exponents are normalized.

---

## (2) Logistic loss: your proposed bound is correct

For the raw lower tail

```lean
lowerBarrierRaw κ κtilde D x = exp (-κ*x) - D * exp (-κtilde*x),
```

the repo already has the exact definition. fileciteturn116file0L3-L4 On the positive tail `x ≥ x⁻`, one has

```text
0 ≤ U⁻(x) ≤ e^{-κx}.
```

Then

```text
(U⁻(x))^{α+1}
≤ (e^{-κx})^{α+1}
= e^{-(α+1)κx}.
```

If

```text
κ̃ ≤ (α+1)κ
```

and `x ≥ 0`, then

```text
e^{-(α+1)κx} ≤ e^{-κ̃x}.
```

So the logistic loss satisfies

```text
-(U⁻)^{α+1} ≥ -e^{-κ̃x}.
```

This is the `-1` in the paper’s final lower bound

```text
A(U_{κ,κ̃,D};u)
≥ ( D(cκ̃ − κ̃² − 1) − 1 − |χ|K_{M,κ,κ̃,m,γ} ) e^{-κ̃x}.
```

The paper’s proof of Lemma 4.2 reaches exactly that form. citeturn807354view2

So if your Lean proof used `α≤m+γ−1` **only** to prove

```lean
(Uminus x)^(p.α + 1) ≤ Real.exp (-κtilde * x)
```

then that is an unnecessary detour. Replace it by a lemma using only `κtilde ≤ (p.α + 1) * κ`.

Suggested Lean lemma:

```lean
lemma lowerRaw_logistic_loss_le_margin
    {κ κtilde D α x : ℝ}
    (hx0 : 0 ≤ x)
    (hU_nonneg : 0 ≤ lowerBarrierRaw κ κtilde D x)
    (hU_le : lowerBarrierRaw κ κtilde D x ≤ Real.exp (-κ * x))
    (hα0 : 0 ≤ α)
    (hκtilde_le : κtilde ≤ (α + 1) * κ) :
    (lowerBarrierRaw κ κtilde D x) ^ (α + 1)
      ≤ Real.exp (-κtilde * x) := by
  calc
    (lowerBarrierRaw κ κtilde D x) ^ (α + 1)
        ≤ (Real.exp (-κ * x)) ^ (α + 1) :=
          Real.rpow_le_rpow hU_nonneg hU_le (by linarith)
    _ = Real.exp (-(α + 1) * κ * x) := by
          -- `exp(a) ^ b = exp(b*a)`, then ring
          ...
    _ ≤ Real.exp (-κtilde * x) := by
          apply Real.exp_le_exp.mpr
          -- since `κtilde ≤ (α+1)κ` and `0 ≤ x`
          nlinarith
```

This removes `α≤m+γ−1` from the logistic sublemma.

---

## Where `α≤m+γ−1` actually enters

The lower-solution proof has other loss terms. In the χ≤0 case, the paper writes

```text
A(W;u)
= Wxx + cWx + mW^{m-1}|χ| Vx Wx
  + W(1 + |χ|W^{m-1}V − (W^α + |χ|W^{m+γ−1})).
```

citeturn807354view0

For `W = U_{κ,κ̃,D}`, after dropping good positive terms, the paper estimates:

```text
A(U;u)
≥ D(cκ̃ − κ̃² − 1)e^{-κ̃x}
  + derivative-chemotaxis-loss
  − U(U^α + |χ|U^{m+γ−1}).
```

citeturn807354view0

The derivative chemotaxis loss is then bounded by cases using the `Vx` estimates:

```text
γκ = 1  : loss ≤ C e^{-(mκ+1/2)x}
γκ < 1  : loss ≤ C e^{-(m+γ)κx}
γκ > 1  : loss ≤ C e^{-(mκ+1)x}
```

citeturn807354view2

To absorb all of these into the scalar margin `e^{-κ̃x}`, you need exponent inequalities of the form:

```text
κ̃ ≤ mκ + 1/2          for γκ = 1,
κ̃ ≤ (m+γ)κ            for γκ < 1,
κ̃ ≤ mκ + 1            for γκ > 1.
```

The paper’s stated κ̃ condition gives

```text
κ̃ ≤ min{(1+α)κ, mκ + 1/2, 1}.
```

citeturn902247view4

For the `γκ < 1` branch, `κ̃ ≤ mκ + 1/2` does **not** imply `κ̃ ≤ (m+γ)κ` when `γκ < 1/2`. The theorem-level assumption

```text
α ≤ m + γ − 1
```

does imply

```text
(1+α)κ ≤ (m+γ)κ,
```

hence

```text
κ̃ ≤ (1+α)κ ≤ (m+γ)κ.
```

That is the clean way the paper’s hypotheses make the exponent packaging work.

So the right Lean split is:

```lean
-- Logistic loss: no α≤m+γ−1 needed
have hlogistic :
  (U x)^(p.α + 1) ≤ exp (-κtilde*x) :=
  lowerRaw_logistic_loss_le_margin ... hκtilde_le_alpha

-- Chemotaxis algebraic loss `U^(m+γ)`:
have hmgamma_exp :
  (U x)^(p.m + p.γ) ≤ exp (-κtilde*x) := by
  -- needs κtilde ≤ (p.m+p.γ)*κ
  ...

-- Under paper assumptions, derive this from α≤m+γ−1:
have hκtilde_le_mgamma :
    κtilde ≤ (p.m + p.γ) * κ := by
  have hα1_le : p.α + 1 ≤ p.m + p.γ := by linarith [hα_le]
  exact le_trans hκtilde_le_alpha
    (mul_le_mul_of_nonneg_right hα1_le hκ_nonneg)
```

This matches the paper’s theorem assumptions and makes the proof modular.

---

## (3) Should the condition be kept?

For a theorem faithful to the paper’s χ≤0 existence theorem: **keep it.**

The exact hypothesis appears in Theorem 1.1(1):

```text
Assume that α ≤ m + γ − 1 and χ ≤ 0.
```

citeturn101802view0

It also appears in the negative branch of the super-solution lemma used in the construction. citeturn866674view0 The proof of that super-solution lemma explicitly says it is working under `χ≤0, α≤m+γ−1` and then uses `α≤m+γ−1` to transform the estimate for `A(e^{-κx};u)` into a sign condition. citeturn866674view1 citeturn316425view3

For the **raw lower-solution Lemma 4.2 tail estimate alone**, the logistic part does not need `α≤m+γ−1`. You may be able to state a slightly more general lower-tail lemma with a direct exponent assumption:

```lean
(hκtilde_le_alpha : κtilde ≤ (p.α + 1) * κ)
(hκtilde_le_mgamma : κtilde ≤ (p.m + p.γ) * κ)
(hκtilde_le_derivCase : ... )
```

Then derive these assumptions from the paper package when proving the faithful theorem. This is the cleanest formal structure.

Concretely:

```lean
structure NegativeBranchExponentPackage
    (p : CMParams) (κ κtilde : ℝ) : Prop where
  hα_le : p.α ≤ p.m + p.γ - 1
  hκtilde_le_alpha : κtilde ≤ (p.α + 1) * κ
  hκtilde_le_mhalf : κtilde ≤ p.m * κ + 1/2
  hκtilde_le_one : κtilde ≤ 1

lemma exponentPackage_to_mgamma
    (hκ0 : 0 ≤ κ)
    (h : NegativeBranchExponentPackage p κ κtilde) :
    κtilde ≤ (p.m + p.γ) * κ := by
  have hα1 : p.α + 1 ≤ p.m + p.γ := by
    linarith [h.hα_le]
  exact le_trans h.hκtilde_le_alpha
    (mul_le_mul_of_nonneg_right hα1 hκ0)
```

Then your lower-solution proof can use only the precise exponent inequalities it needs; the final paper theorem supplies them from `α≤m+γ−1`.

---

## Practical recommendation

Refactor the Lean proof as follows:

1. **Remove `α≤m+γ−1` from the logistic sublemma.** Use only `κ̃≤(1+α)κ`.

2. **Keep `α≤m+γ−1` in the theorem-level negative branch package.** It is explicitly in Theorem 1.1(1) and Lemma 4.1.

3. **For Lemma 4.2, either:**
   - formalize the paper-faithful version under the global negative-branch package, or
   - prove a more general lower-tail theorem with direct assumptions `κ̃≤(1+α)κ` and `κ̃≤(m+γ)κ`.

4. **Do not claim the paper proves χ≤0 existence for all `α,m,γ≥1`.** The abstract says the model has general `m,α,γ≥1`, but the formal theorem statement restricts the χ≤0 existence branch by `α≤m+γ−1`. The theorem statement is what the Lean formalization should mirror.
