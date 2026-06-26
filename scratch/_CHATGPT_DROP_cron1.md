# Q696 / cron1: parity-chain lemmas for depth-2 Neumann BC of `ν * U^γ`

Repo inspected: `xiangyazi24/Shen_work`.  Scratch write target: branch `chatgpt-scratch`.

## Verdict

Yes, the repo has useful parity-chain infrastructure, but the best reusable material is **not** the local `deriv_even_odd` / `deriv_odd_even` helpers in `IntervalChemDivSpatialC2.lean`.  The strongest reusable file is:

```text
ShenWork/Paper2/IntervalSourceRepresentative.lean
```

It defines endpoint parity abstractions:

```lean
def EvenAboutZero (f : ℝ → ℝ) : Prop := ∀ x : ℝ, f (-x) = f x

def EvenAboutOne (f : ℝ → ℝ) : Prop := ∀ x : ℝ, f (2 - x) = f x

structure DoublyEven (f : ℝ → ℝ) : Prop where
  about0 : EvenAboutZero f
  about1 : EvenAboutOne f
```

and proves odd iterated-derivative vanishing at both endpoints:

```lean
theorem iteratedDeriv_odd_evenAboutZero_eq_zero
    {f : ℝ → ℝ} (hf : EvenAboutZero f) {n : ℕ} (hn : Odd n) :
    iteratedDeriv n f 0 = 0
```

```lean
theorem iteratedDeriv_odd_evenAboutOne_eq_zero
    {f : ℝ → ℝ} (hf : EvenAboutOne f) {n : ℕ} (hn : Odd n) :
    iteratedDeriv n f 1 = 0
```

For a third derivative target, instantiate with `n = 3`.

## Recommended route for `ν * U^γ`

If you have cosine-series parity hypotheses:

```lean
hU0 : ∀ x, U (-x) = U x
hU1 : ∀ x, U (2 - x) = U x
```

then make the source doubly even by closure under composition/product:

```lean
open ShenWork.Paper2.SourceRepresentative

have hUde : DoublyEven U where
  about0 := hU0
  about1 := hU1

-- Positivity is needed for differentiability/C⁴ of `U^γ`, but not for parity.
have hpow_de : DoublyEven (fun x => U x ^ γ) :=
  DoublyEven.comp (fun y : ℝ => y ^ γ) hUde

have hconst_de : DoublyEven (fun _ : ℝ => ν) where
  about0 := by intro x; rfl
  about1 := by intro x; rfl

have hsrc_de : DoublyEven (fun x => ν * U x ^ γ) :=
  hconst_de.mul hpow_de
```

Then endpoint vanishing of the third iterated derivative is:

```lean
have hthird0_iter : iteratedDeriv 3 (fun x => ν * U x ^ γ) 0 = 0 :=
  iteratedDeriv_odd_evenAboutZero_eq_zero hsrc_de.about0 ⟨1, by norm_num⟩

have hthird1_iter : iteratedDeriv 3 (fun x => ν * U x ^ γ) 1 = 0 :=
  iteratedDeriv_odd_evenAboutOne_eq_zero hsrc_de.about1 ⟨1, by norm_num⟩
```

If the goal is literally:

```lean
deriv (deriv (deriv (fun x => ν * U x ^ γ))) 0 = 0
```

then convert from `iteratedDeriv 3` using the standard unfolding:

```lean
simpa [iteratedDeriv_eq_iterate, Function.iterate_succ, Function.iterate_zero]
  using hthird0_iter
```

and similarly at `1`.

For the Neumann-tower/depth-index shape, use the already-packaged theorem instead:

```lean
have hN0 : deriv (ShenWork.Paper2.NeumannTowerOfC6.gTower
    (fun x => ν * U x ^ γ) 1) 0 = 0 :=
  gTower_deriv_zero_of_doublyEven hsrc_de 1

have hN1 : deriv (ShenWork.Paper2.NeumannTowerOfC6.gTower
    (fun x => ν * U x ^ γ) 1) 1 = 0 :=
  gTower_deriv_one_of_doublyEven hsrc_de 1
```

Here `i = 1` corresponds to `2*i+1 = 3`, i.e. the third derivative in the `gTower` formulation.

## 1. `deriv_even_odd`, `deriv_odd_even`

Search hits:

```text
ShenWork/Paper2/IntervalChemDivSpatialC2.lean
ShenWork/Paper2/IntervalSourceRepresentative.lean   -- for `deriv_odd_even` search only, via comments/related derivative parity
```

In `IntervalChemDivSpatialC2.lean`, the exact requested helpers occur inside:

```lean
noncomputable def chemDivSource_weakH2_of_cosineRep ... :
    IntervalWeakH2Neumann (chemDivLift p u v) := by
```

They are **local `have`s**, not exported theorem names:

```lean
-- Parity helper: derivative of even C¹ function is odd
have deriv_even_odd : ∀ {g : ℝ → ℝ}, ContDiff ℝ 1 g → (∀ x, g (-x) = g x) →
    ∀ x, deriv g (-x) = -(deriv g x) := by
  intro g _hg heven x
  have h1 := deriv_comp_neg (f := g) (x := x)
  rw [show (fun x => g (-x)) = g from funext heven] at h1; linarith
```

```lean
-- Parity helper: derivative of odd C¹ function is even
have deriv_odd_even : ∀ {g : ℝ → ℝ}, ContDiff ℝ 1 g → (∀ x, g (-x) = -(g x)) →
    ∀ x, deriv g (-x) = deriv g x := by
  intro g _hg hodd x
  have h1 := deriv_comp_neg (f := g) (x := x)
  rw [show (fun x => g (-x)) = fun x => -(g x) from funext hodd] at h1
  simp [deriv_neg] at h1; linarith
```

These are useful proof patterns, but because they are local, they cannot be referenced elsewhere without refactoring.

## 2. `odd_zero`

Also in `IntervalChemDivSpatialC2.lean`, again only local inside `chemDivSource_weakH2_of_cosineRep`:

```lean
-- Odd function vanishes at 0
have odd_zero : ∀ {g : ℝ → ℝ}, (∀ x, g (-x) = -(g x)) → g 0 = 0 := by
  intro g hodd; have h := hodd 0; rw [neg_zero] at h; linarith
```

The reusable replacement is stronger:

```lean
iteratedDeriv_odd_evenAboutZero_eq_zero
```

from `IntervalSourceRepresentative.lean`, which handles all odd orders, not just a function that is already odd.

## 3. Existing x=1 Neumann BC from shift symmetry

There are two relevant patterns.

### Local first-derivative pattern in `IntervalChemDivSpatialC2.lean`

Inside `chemDivSource_weakH2_of_cosineRep`, the file proves endpoint `1` Neumann BC for a function `F` satisfying `F (2-x) = F x` by using `deriv_comp_const_sub`:

```lean
have hbc1 : deriv F 1 = 0 := by
  have h1 := deriv_comp_const_sub (f := F) (a := 2) (x := 1)
  rw [show (fun x => F (2 - x)) = F from funext hF_symm1] at h1
  have : (2 : ℝ) - 1 = 1 := by norm_num
  rw [this] at h1; linarith
```

The same proof also uses `deriv_comp_const_sub` to show antisymmetry of `V_cos'` about `1` and symmetry of `F` about `1`:

```lean
have hdv_antisymm1 : ∀ x, deriv V_cos (2 - x) = -(deriv V_cos x) := by
  intro x
  have h1 := deriv_comp_const_sub (f := V_cos) (a := 2) (x := x)
  rw [show (fun x => V_cos (2 - x)) = V_cos from funext hv_symm1] at h1; linarith
```

### Reusable all-odd-orders pattern in `IntervalSourceRepresentative.lean`

This is the better theorem for third derivatives:

```lean
theorem iteratedDeriv_odd_evenAboutOne_eq_zero
    {f : ℝ → ℝ} (hf : EvenAboutOne f) {n : ℕ} (hn : Odd n) :
    iteratedDeriv n f 1 = 0 := by
  have hfun : (fun x : ℝ => f (2 - x)) = f := funext hf
  have hkey := congrFun (iteratedDeriv_comp_const_sub n f (2 : ℝ)) (1 : ℝ)
  simp only [hfun, hn.neg_one_pow] at hkey
  norm_num at hkey
  linarith [hkey]
```

So for `x = 1`, do **not** redo the one-derivative `deriv_comp_const_sub` proof if your goal can be expressed with `iteratedDeriv` or `gTower`; use this theorem.

## 4. Is there a theorem showing `deriv (deriv (deriv f)) 0 = 0` from `f` even?

I did **not** find a theorem with that exact literal conclusion.

But the repo has a stronger reusable theorem:

```lean
iteratedDeriv_odd_evenAboutZero_eq_zero
```

For `n = 3`, it gives:

```lean
iteratedDeriv 3 f 0 = 0
```

from:

```lean
hf : EvenAboutZero f
```

This is mathematically the same third-derivative vanishing, and it should convert to the literal `deriv (deriv (deriv f)) 0 = 0` form by unfolding `iteratedDeriv_eq_iterate`.

The repo also has `gTower` packaging, which is likely closer to the depth-2 Neumann BC target:

```lean
theorem deriv_gTower_eq_iteratedDeriv (f : ℝ → ℝ) (i : ℕ) :
    deriv (gTower f i) = iteratedDeriv (2 * i + 1) f
```

```lean
theorem gTower_deriv_zero_of_doublyEven
    {f : ℝ → ℝ} (hf : DoublyEven f) (i : ℕ) :
    deriv (gTower f i) 0 = 0
```

```lean
theorem gTower_deriv_one_of_doublyEven
    {f : ℝ → ℝ} (hf : DoublyEven f) (i : ℕ) :
    deriv (gTower f i) 1 = 0
```

```lean
theorem higherNeumannCompatibility_of_doublyEven
    {f : ℝ → ℝ} (hf : DoublyEven f) :
    (∀ i, i < 3 → deriv (gTower f i) 0 = 0) ∧
      (∀ i, i < 3 → deriv (gTower f i) 1 = 0)
```

For the third derivative, use `i = 1`.

## Other useful closure lemmas

`IntervalSourceRepresentative.lean` also has:

```lean
theorem DoublyEven.add {f g : ℝ → ℝ} (hf : DoublyEven f) (hg : DoublyEven g) :
    DoublyEven (fun x => f x + g x)
```

```lean
theorem DoublyEven.mul {f g : ℝ → ℝ} (hf : DoublyEven f) (hg : DoublyEven g) :
    DoublyEven (fun x => f x * g x)
```

```lean
theorem DoublyEven.comp {f : ℝ → ℝ} (g : ℝ → ℝ) (hf : DoublyEven f) :
    DoublyEven (fun x => g (f x))
```

```lean
theorem DoublyEven.deriv_deriv {f : ℝ → ℝ} (hf : DoublyEven f) :
    DoublyEven (deriv (deriv f))
```

For `ν * U^γ`, the important one is `DoublyEven.comp` with `g := fun y => y ^ γ`; positivity is not required for the parity equality itself.

## Search summary

Searched terms:

```text
deriv_even_odd
deriv_odd_even
odd_zero
deriv_comp_const_sub
iteratedDeriv_odd_evenAboutZero_eq_zero
higherNeumannCompatibility_of_doublyEven
EvenAboutZero
iteratedDeriv_comp_const_sub
third derivative vanishes
```

Main files found:

```text
ShenWork/Paper2/IntervalChemDivSpatialC2.lean
ShenWork/Paper2/IntervalSourceRepresentative.lean
ShenWork/Paper2/IntervalSourceC6Representative.lean
```

`IntervalSourceC6Representative.lean` consumes the reusable parity package for cosine-series source representatives: it proves `doublyEven_cosineSeries` and then uses `higherNeumannCompatibility_of_doublyEven` to discharge the source `hSrcN0`/`hSrcN1` fields.
