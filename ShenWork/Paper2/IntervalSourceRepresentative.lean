/-
# The source's higher Neumann compatibility — DOES it hold?  (YES, by parity)

This file answers the make-or-break question behind the smooth-representative
hypotheses of `ShenWork.Paper2.ChiNegUnconditionalClose.chiNeg_resolverC2Coeff_unconditional`:

  > do the source's odd spatial derivatives `∂ₓ`, `∂ₓ³`, `∂ₓ⁵` vanish at the
  > endpoints `0` and `1` (the higher Neumann compatibility `hSrcN0`/`hSrcN1`)?

**Answer: YES — to ALL odd orders — by the double-even (cosine-series) parity.**

REASONING (the mathematics, recorded for the survey).  In the concrete model the
iterate `u` and the elliptic signal `v = R u` are Neumann cosine-series objects
(`LocalRestart.hrep`: `u(x) = ∑ₙ aₙ cos(nπx)`; the resolver
`intervalNeumannResolverR` is literally `∑ₖ v̂ₖ cos(kπx)`, solving the coefficient
elliptic equation `(μ+λₖ) v̂ₖ = âₖ`, i.e. `-vₓₓ + μ v = ν uᵞ`, Neumann).  A Neumann
cosine series is the restriction to `[0,1]` of a function that is **even about `0`**
(`f(-x)=f(x)`, since `cos` is even) and **even about `1`** (`f(2-x)=f(x)`, since
`cos(nπ(2-x))=cos(nπx)`).  Call such functions *doubly even* (DE).

The chemotaxis–logistic source `S = -χ₀ ∂ₓF + L`, with flux `F = u·∂ₓv·(1+v)^{-β}`
and logistic `L = u(a-b uᵅ)`, inherits the DE parity:
  * `u, v` DE, `∂ₓv` odd-about-each-endpoint, `(1+v)^{-β}` DE  ⟹  `F` is odd  ⟹
    `∂ₓF` is DE; `L` is DE (products/compositions of DE are DE)  ⟹  `S` is DE.
Every odd derivative of a DE function is odd-about-each-endpoint, hence vanishes at
`0` and `1` — **automatically, to every odd order**.  So `∂ₓ³`/`∂ₓ⁵` vanishing is no
extra "higher compatibility": it is the same parity that gives `∂ₓ` vanishing, and
there is **no obstruction**.  (The `O(1/n⁶)` eigen-cube decay is therefore NOT
over-asked: the cosine spectrum sees only the parity, which holds at order `6`.)

This file proves the load-bearing fact abstractly and packages it in exactly the
`hSrcN0`/`hSrcN1` shape (`deriv (gTower f i) 0 = 0`, `… 1 = 0`, for `i < 3`), so the
Neumann hypotheses of the unconditional close are dischargeable from a doubly-even
representative.  The regularity input (`ContDiff ℝ 6`) is the source's honest `C⁶`,
supplied separately (the iterate's `C⁷` via `chemDivLosesOne` + elliptic smoothing);
the odd-derivative vanishing proved here is the PARITY half and is independent of it.

No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalNeumannTowerOfC6
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open Set Filter Topology
open ShenWork.Paper2.NeumannTowerOfC6 (gTower gTower_zero deriv_gTower)

namespace ShenWork.Paper2.SourceRepresentative

noncomputable section

/-- A function is **even about `0`** if `f (-x) = f x` for all `x`
(the parity of a Neumann cosine series at the left endpoint). -/
def EvenAboutZero (f : ℝ → ℝ) : Prop := ∀ x : ℝ, f (-x) = f x

/-- A function is **even about `1`** if `f (2 - x) = f x` for all `x`
(the parity of a Neumann cosine series at the right endpoint:
`cos (n π (2 - x)) = cos (n π x)`). -/
def EvenAboutOne (f : ℝ → ℝ) : Prop := ∀ x : ℝ, f (2 - x) = f x

/-- A **doubly-even** function: even about both endpoints `0` and `1`.
Every Neumann cosine series is doubly even, and the chemotaxis–logistic source is
doubly even because it is built from the doubly-even iterate `u` and signal `v`. -/
structure DoublyEven (f : ℝ → ℝ) : Prop where
  about0 : EvenAboutZero f
  about1 : EvenAboutOne f

/-- **Odd iterated derivatives of an even-about-`0` function vanish at `0`.**
From `iteratedDeriv_comp_neg`: `iteratedDeriv n (f ∘ neg) 0 = (-1)^n iteratedDeriv n f 0`;
when `f ∘ neg = f` and `n` is odd this forces `iteratedDeriv n f 0 = 0`. -/
theorem iteratedDeriv_odd_evenAboutZero_eq_zero
    {f : ℝ → ℝ} (hf : EvenAboutZero f) {n : ℕ} (hn : Odd n) :
    iteratedDeriv n f 0 = 0 := by
  have hfun : (fun x : ℝ => f (-x)) = f := funext hf
  have hkey := iteratedDeriv_comp_neg n f (0 : ℝ)
  rw [hfun, neg_zero] at hkey
  rw [hn.neg_one_pow, neg_one_smul] at hkey
  linarith [hkey]

/-- **Odd iterated derivatives of an even-about-`1` function vanish at `1`.**
From `iteratedDeriv_comp_const_sub` (with `s = 2`):
`iteratedDeriv n (fun x => f (2 - x)) 1 = (-1)^n iteratedDeriv n f (2 - 1)`;
when `f (2 - ·) = f` and `n` is odd this forces `iteratedDeriv n f 1 = 0`. -/
theorem iteratedDeriv_odd_evenAboutOne_eq_zero
    {f : ℝ → ℝ} (hf : EvenAboutOne f) {n : ℕ} (hn : Odd n) :
    iteratedDeriv n f 1 = 0 := by
  have hfun : (fun x : ℝ => f (2 - x)) = f := funext hf
  have hkey := congrFun (iteratedDeriv_comp_const_sub n f (2 : ℝ)) (1 : ℝ)
  simp only [hfun, hn.neg_one_pow] at hkey
  norm_num at hkey
  linarith [hkey]

/-- `deriv (gTower f i)` is the odd iterated derivative `∂ₓ^{2i+1} f`. -/
theorem deriv_gTower_eq_iteratedDeriv (f : ℝ → ℝ) (i : ℕ) :
    deriv (gTower f i) = iteratedDeriv (2 * i + 1) f := by
  rw [deriv_gTower, iteratedDeriv_eq_iterate]

/-- `2 * i + 1` is odd. -/
theorem odd_two_mul_add_one (i : ℕ) : Odd (2 * i + 1) := ⟨i, by ring⟩

/-- **The `hSrcN0` half from double-even parity.**  For a doubly-even `f`, the
Neumann tower's left-endpoint odd-derivative vanishing holds at every level:
`deriv (gTower f i) 0 = 0`. -/
theorem gTower_deriv_zero_of_doublyEven
    {f : ℝ → ℝ} (hf : DoublyEven f) (i : ℕ) :
    deriv (gTower f i) 0 = 0 := by
  rw [deriv_gTower_eq_iteratedDeriv]
  exact iteratedDeriv_odd_evenAboutZero_eq_zero hf.about0 (odd_two_mul_add_one i)

/-- **The `hSrcN1` half from double-even parity.**  For a doubly-even `f`, the
Neumann tower's right-endpoint odd-derivative vanishing holds at every level:
`deriv (gTower f i) 1 = 0`. -/
theorem gTower_deriv_one_of_doublyEven
    {f : ℝ → ℝ} (hf : DoublyEven f) (i : ℕ) :
    deriv (gTower f i) 1 = 0 := by
  rw [deriv_gTower_eq_iteratedDeriv]
  exact iteratedDeriv_odd_evenAboutOne_eq_zero hf.about1 (odd_two_mul_add_one i)

/-- **The full higher-Neumann compatibility, packaged for the unconditional close.**

A doubly-even (Neumann cosine-series parity) representative `f` supplies BOTH the
left- and right-endpoint odd-derivative vanishing for all tower levels `i < 3`
(i.e. `∂ₓ`, `∂ₓ³`, `∂ₓ⁵` vanishing) — exactly the `hSrcN0`/`hSrcN1` shape consumed
by `neumannTower_gTower_three_of_contDiff_six` and hence by
`chiNeg_resolverC2Coeff_unconditional`.  **No obstruction.** -/
theorem higherNeumannCompatibility_of_doublyEven
    {f : ℝ → ℝ} (hf : DoublyEven f) :
    (∀ i, i < 3 → deriv (gTower f i) 0 = 0) ∧
      (∀ i, i < 3 → deriv (gTower f i) 1 = 0) :=
  ⟨fun i _ => gTower_deriv_zero_of_doublyEven hf i,
   fun i _ => gTower_deriv_one_of_doublyEven hf i⟩

/-- **A genuine doubly-even function exists at every regularity** — the cosine mode
`cos (n π x)` is the prototypical Neumann-cosine basis function and is doubly even,
witnessing that the parity hypothesis is non-vacuous (the source is a series of
exactly these). -/
theorem doublyEven_cos (n : ℕ) :
    DoublyEven (fun x : ℝ => Real.cos (n * Real.pi * x)) where
  about0 := by
    intro x
    simp only
    rw [show (n : ℝ) * Real.pi * (-x) = -((n : ℝ) * Real.pi * x) by ring, Real.cos_neg]
  about1 := by
    intro x
    simp only
    rw [show (n : ℝ) * Real.pi * (2 - x)
        = (n : ℝ) * (2 * Real.pi) - (n : ℝ) * Real.pi * x by ring]
    exact Real.cos_nat_mul_two_pi_sub _ n

/-- `DoublyEven` is closed under sums (the source is a sum of doubly-even pieces). -/
theorem DoublyEven.add {f g : ℝ → ℝ} (hf : DoublyEven f) (hg : DoublyEven g) :
    DoublyEven (fun x => f x + g x) where
  about0 := fun x => by simp only [hf.about0 x, hg.about0 x]
  about1 := fun x => by simp only [hf.about1 x, hg.about1 x]

/-- `DoublyEven` is closed under products (flux = `u · ∂ₓv · (1+v)^{-β}` etc.). -/
theorem DoublyEven.mul {f g : ℝ → ℝ} (hf : DoublyEven f) (hg : DoublyEven g) :
    DoublyEven (fun x => f x * g x) where
  about0 := fun x => by simp only [hf.about0 x, hg.about0 x]
  about1 := fun x => by simp only [hf.about1 x, hg.about1 x]

/-- `DoublyEven` is closed under post-composition with any `g : ℝ → ℝ`
(`g (u x)` is doubly even when `u` is — covers `u^α`, `(1+v)^{-β}`, logistic). -/
theorem DoublyEven.comp {f : ℝ → ℝ} (g : ℝ → ℝ) (hf : DoublyEven f) :
    DoublyEven (fun x => g (f x)) where
  about0 := fun x => by simp only [hf.about0 x]
  about1 := fun x => by simp only [hf.about1 x]

/-- **Derivative flips parity: the derivative of a doubly-even function is
odd-about-each-endpoint, hence its `deriv` is again doubly even after one more
derivative — formally, `deriv (deriv f)` of a `DoublyEven f` is `DoublyEven`.**
This is the chemotaxis-divergence step `∂ₓ(odd) = even`: `∂ₓF` with `F` odd is DE.
(Stated at the second-derivative level, which is what the tower `gTower` uses.) -/
theorem DoublyEven.deriv_deriv {f : ℝ → ℝ} (hf : DoublyEven f) :
    DoublyEven (deriv (deriv f)) where
  about0 := by
    intro x
    have h2 : deriv (deriv (fun y : ℝ => f (-y))) = deriv (deriv f) := by
      rw [funext hf.about0]
    have hcn := iteratedDeriv_comp_neg 2 f
    simp only [iteratedDeriv_eq_iterate, Function.iterate_succ, Function.iterate_zero,
      Function.comp_apply, id_eq] at hcn
    have hcn' : deriv (deriv (fun y : ℝ => f (-y)))
        = fun a => deriv (deriv f) (-a) := by
      funext a; have := hcn a; simpa using this
    rw [h2] at hcn'
    have := congrFun hcn' (-x)
    simpa using this
  about1 := by
    intro x
    have h2 : deriv (deriv (fun y : ℝ => f (2 - y))) = deriv (deriv f) := by
      rw [funext hf.about1]
    have hcs := iteratedDeriv_comp_const_sub 2 f (2 : ℝ)
    simp only [iteratedDeriv_eq_iterate, Function.iterate_succ, Function.iterate_zero,
      Function.comp_apply, id_eq] at hcs
    have hcs' : deriv (deriv (fun y : ℝ => f (2 - y)))
        = fun a => deriv (deriv f) (2 - a) := by
      funext a; have := congrFun hcs a; simpa using this
    rw [h2] at hcs'
    have := congrFun hcs' (2 - x)
    simpa using this

end

end ShenWork.Paper2.SourceRepresentative
