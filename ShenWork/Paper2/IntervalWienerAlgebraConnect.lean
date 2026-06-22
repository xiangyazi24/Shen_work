import ShenWork.Paper2.IntervalWienerAlgebraFlux
import ShenWork.PDE.IntervalCosineInversion

/-!
  # WALL-A function bridge: connecting the `H^σ` coefficient algebra to real
  function products (Paper 2).

  The landed files build the full `H^σ` (σ > 1/2) coefficient-sequence algebra
  (`addConv`, `diffConv`, `cosProd`, `cosPow`, `chemotaxisFlux_memHSigma`) on the
  abstract `MemHSigma σ` predicate.  This file connects that algebra to *actual
  functions* via the repository's `cosineCoeffs` map and the even-reflection /
  `AddCircle 2` Fourier bridge (`reflCircle`, `fourierCoeff`,
  `intervalCosine_hasSum_pointwise`).

  ## What is proved here (rigorous, no `sorry`, axiom-clean)

  * `reflCircle_mul` / `reflC_mul` — the even reflection is **multiplicative**:
    `reflCircle (f·g) = reflCircle f · reflCircle g` (pointwise on `AddCircle 2`),
    the structural heart of the product→convolution correspondence.
  * `memHSigma_of_update` / `memHSigma_congr_except` — `H^σ` membership is
    insensitive to changing a sequence at a single mode (used to repair the
    `k = 0` diagonal over-count of the landed `diffConv`).
  * `trueCosProd` — the **exact** normalized cosine-product coefficient operator
    (the landed `cosProd` is correct for all `k ≥ 1` but over-counts the `k = 0`
    diagonal; `trueCosProd` fixes precisely that one mode).
  * `memHSigma_trueCosProd_of_gt_half` — the exact product operator inherits the
    landed `H^σ` Banach-algebra closure (`σ > 1/2`), since it differs from the
    landed `cosProd` only at `k = 0`.
  * `chemotaxisFlux_memHSigma_function` — the **function-level** chemotaxis flux
    `u^m (1+v)^{−β} v_x ∈ H^σ` (σ > 1/2), assembled through the exact product
    operator from `H^σ` membership of the three flux-factor coefficient sequences.
  * `chemotaxisFlux_memHSigma_intPow_function` — the integer-power specialization,
    discharging the `u^m` factor (integer `m ≥ 1`) purely through `cosPow`.

  ## The function bridge `cosineCoeffs_mul_eq_cosProd`

  The literal sequence identity `cosineCoeffs (f·g) = cosProd (cosineCoeffs f)
  (cosineCoeffs g)` is **false at `k = 0`** with the landed `cosProd`
  (the landed `diffConv` double-counts the diagonal there: e.g. `f = g = 1` gives
  landed `cosProd … 0 = 3/2 ≠ 1 = (f·g)^0`).  It is exact for every `k ≥ 1`, and
  becomes exact for *all* `k` with `trueCosProd` (proved here to be the correct
  operator and `H^σ`-closed).  The remaining analytic content — the per-mode
  identity `cosineCoeffs (f·g) k = trueCosProd (cosineCoeffs f) (cosineCoeffs g) k`
  — is the triple-cosine integral / double-series interchange; it is isolated as
  `CosineMulBridge` (a `Prop` predicate) and `chemotaxisFlux_memHSigma_function`
  shows that once that predicate holds (for the three flux factors), the
  function-level flux lands in `H^σ`.  See the report for the precise residual.
-/

noncomputable section

open MeasureTheory
open ShenWork.Paper2.HSigmaScale
open ShenWork.IntervalCosineInversion
open ShenWork.IntervalNeumannFullKernel
open ShenWork.CosineParsevalBridge

namespace ShenWork.Paper2.IntervalWienerAlgebra

/-! ## 1. Multiplicativity of the even reflection. -/

/-- The even reflection (complex form) is **multiplicative**:
`reflC (fun x => f x * g x) y = reflC f y * reflC g y`.  Immediate from
`unitIntervalEvenReflection h y = h |y|`. -/
theorem reflC_mul (f g : ℝ → ℝ) (y : ℝ) :
    reflC (fun x => f x * g x) y = reflC f y * reflC g y := by
  simp only [reflC, unitIntervalEvenReflection]
  push_cast
  ring

/-- The lifted even reflection on `AddCircle 2` is multiplicative pointwise.
`AddCircle.liftIoc` precomposes with the canonical representative map, so the
factorwise product passes straight through. -/
theorem reflCircle_mul (f g : ℝ → ℝ) (z : AddCircle (2 : ℝ)) :
    reflCircle (fun x => f x * g x) z = reflCircle f z * reflCircle g z := by
  simp only [reflCircle, AddCircle.liftIoc, Function.comp_apply, Set.restrict_apply]
  exact reflC_mul f g _

/-! ## 2. `H^σ` membership is insensitive to a single mode. -/

/-- Changing a sequence at a single index keeps `H^σ` membership: if `a` and `b`
agree off `{k₀}`, then `MemHSigma σ a ↔ MemHSigma σ b`.  (A single mode contributes
a finitely-supported, hence summable, correction to the `H^σ` energy.) -/
theorem memHSigma_congr_except {σ : ℝ} {a b : ℕ → ℝ} (k₀ : ℕ)
    (h : ∀ k, k ≠ k₀ → a k = b k) (ha : MemHSigma σ a) : MemHSigma σ b := by
  unfold MemHSigma at *
  refine ha.congr_cofinite ?_
  have hsub : {k : ℕ | ¬ (1 + lam k) ^ σ * (a k) ^ 2
      = (1 + lam k) ^ σ * (b k) ^ 2} ⊆ {k₀} := by
    intro k hk
    simp only [Set.mem_setOf_eq] at hk
    simp only [Set.mem_singleton_iff]
    by_contra hkne
    exact hk (by rw [h k hkne])
  have hfin : {k : ℕ | ¬ (1 + lam k) ^ σ * (a k) ^ 2
      = (1 + lam k) ^ σ * (b k) ^ 2}.Finite :=
    (Set.finite_singleton k₀).subset hsub
  exact Filter.eventually_cofinite.mpr hfin

/-! ## 3. The exact normalized cosine-product coefficient `trueCosProd`. -/

/-- The diagonal correlation `Σ' n, a n * b n` (the value the landed `diffConv`
double-counts at the output mode `k = 0`). -/
def diagCorr (a b : ℕ → ℝ) : ℝ := ∑' n : ℕ, a n * b n

/-- **The exact normalized cosine-product coefficient.**  Equal to the landed
`cosProd` for every `k ≥ 1`; at `k = 0` it subtracts the `½`-weighted diagonal
over-count of the landed `diffConv` (which counts the `m = n` term twice through
its two correlation leaves `corr1 a b + corr1 b a`).  By the product-to-sum
identity `cos(mπx)cos(nπx) = ½(cos((m+n)πx)+cos(|m−n|πx))`, `trueCosProd a b k` is
exactly the `k`-th normalized cosine coefficient of the function product. -/
def trueCosProd (a b : ℕ → ℝ) (k : ℕ) : ℝ :=
  cosProd a b k - (if k = 0 then (1 / 2 : ℝ) * diagCorr a b else 0)

/-- `trueCosProd a b k = cosProd a b k` for every positive mode. -/
theorem trueCosProd_pos {a b : ℕ → ℝ} {k : ℕ} (hk : k ≠ 0) :
    trueCosProd a b k = cosProd a b k := by
  simp [trueCosProd, hk]

/-- `trueCosProd` differs from the landed `cosProd` only at the single mode `0`. -/
theorem trueCosProd_eq_cosProd_except (a b : ℕ → ℝ) :
    ∀ k, k ≠ 0 → cosProd a b k = trueCosProd a b k :=
  fun _ hk => (trueCosProd_pos hk).symm

/-- **The exact product operator inherits the `H^σ` Banach-algebra closure**
(σ > 1/2).  Since `trueCosProd a b` agrees with the landed `cosProd a b` off the
single mode `0`, and the landed `memHSigma_cosProd_of_gt_half` puts `cosProd a b`
in `H^σ`, the single-mode-insensitivity lemma transports membership. -/
theorem memHSigma_trueCosProd_of_gt_half {σ : ℝ} (hσ : 1 / 2 < σ) {a b : ℕ → ℝ}
    (ha : MemHSigma σ a) (hb : MemHSigma σ b) :
    MemHSigma σ (trueCosProd a b) :=
  memHSigma_congr_except 0 (trueCosProd_eq_cosProd_except a b)
    (memHSigma_cosProd_of_gt_half hσ ha hb)

/-! ## 4. The function bridge predicate and the function-level flux. -/

/-- **The cosine-multiplication bridge predicate.**  `CosineMulBridge f g` asserts
the exact per-mode identity connecting the cosine coefficients of the function
product `f·g` to the exact product operator on their coefficient sequences:
`cosineCoeffs (f·g) k = trueCosProd (cosineCoeffs f) (cosineCoeffs g) k` for all `k`.

This is the genuinely analytic content of the function bridge — the triple-cosine
integral / absolutely-convergent double-series interchange on `[0,1]`.  It holds for
`f, g` with summable cosine coefficients (e.g. `f, g ∈ H^σ`, `σ > 1/2`, via the
landed `hSigma_subset_l1_of_gt_half`).  It is isolated as a hypothesis so the
`H^σ`-algebra consequence (the chemotaxis flux landing in `H^σ`) is available the
moment the bridge is supplied for the flux factors. -/
def CosineMulBridge (f g : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, cosineCoeffs (fun x => f x * g x) k
    = trueCosProd (cosineCoeffs f) (cosineCoeffs g) k

/-- Under the bridge, the product's coefficient map is literally `trueCosProd` of
the factors' coefficient maps. -/
theorem cosineCoeffs_mul_eq_trueCosProd {f g : ℝ → ℝ} (h : CosineMulBridge f g) :
    cosineCoeffs (fun x => f x * g x) = trueCosProd (cosineCoeffs f) (cosineCoeffs g) :=
  funext h

/-- **Function-product `H^σ` closure (σ > 1/2).**  Given the bridge for `f, g` and
`H^σ` membership of their cosine coefficients, the cosine coefficients of the
function product `f·g` lie in `H^σ`.  This is the function-level Banach-algebra
statement: `H^σ` (σ > 1/2) is closed under *actual* pointwise multiplication of the
underlying interval functions, not merely under the abstract coefficient product. -/
theorem memHSigma_cosineCoeffs_mul_of_gt_half {σ : ℝ} (hσ : 1 / 2 < σ) {f g : ℝ → ℝ}
    (hbridge : CosineMulBridge f g)
    (hf : MemHSigma σ (cosineCoeffs f)) (hg : MemHSigma σ (cosineCoeffs g)) :
    MemHSigma σ (cosineCoeffs (fun x => f x * g x)) := by
  rw [cosineCoeffs_mul_eq_trueCosProd hbridge]
  exact memHSigma_trueCosProd_of_gt_half hσ hf hg

/-- **Triple function product `H^σ` closure (σ > 1/2).**  For the chemotaxis flux
`u^m · (1+v)^{−β} · v_x`, written as the iterated function product `f·(g·h)`. -/
theorem memHSigma_cosineCoeffs_mul3_of_gt_half {σ : ℝ} (hσ : 1 / 2 < σ)
    {f g h : ℝ → ℝ}
    (hgh : CosineMulBridge g h)
    (hf_gh : CosineMulBridge f (fun x => g x * h x))
    (hf : MemHSigma σ (cosineCoeffs f)) (hg : MemHSigma σ (cosineCoeffs g))
    (hh : MemHSigma σ (cosineCoeffs h)) :
    MemHSigma σ (cosineCoeffs (fun x => f x * (g x * h x))) :=
  memHSigma_cosineCoeffs_mul_of_gt_half hσ hf_gh hf
    (memHSigma_cosineCoeffs_mul_of_gt_half hσ hgh hg hh)

/-- **THE FUNCTION-LEVEL TARGET — chemotaxis flux `u^m (1+v)^{−β} v_x ∈ H^σ**
(σ > 1/2).  Let `uPow = u^m`, `invDen = (1+v)^{−β}`, `vx = v_x` be the three flux
factor *functions*, each with cosine coefficients in `H^σ` (the `u^m` factor via the
integer-power / composition lemma, `(1+v)^{−β}` via the smooth-composition lemma,
`v_x` via the `H^{σ+1} ⊂ H^σ` embedding).  Given the cosine-multiplication bridge for
the two function products assembling the flux, the coefficients of the *function*
flux `uPow · (invDen · vx)` lie in `H^σ`.

This is the function-level companion of the landed sequence-level
`chemotaxisFlux_memHSigma`: it routes the landed `H^σ` coefficient algebra back onto
genuine pointwise products of the chemotaxis flux factors. -/
theorem chemotaxisFlux_memHSigma_function {σ : ℝ} (hσ : 1 / 2 < σ)
    {uPow invDen vx : ℝ → ℝ}
    (hden_vx : CosineMulBridge invDen vx)
    (hu_rest : CosineMulBridge uPow (fun x => invDen x * vx x))
    (hu : MemHSigma σ (cosineCoeffs uPow))
    (hv : MemHSigma σ (cosineCoeffs invDen))
    (hvx : MemHSigma σ (cosineCoeffs vx)) :
    MemHSigma σ (cosineCoeffs (fun x => uPow x * (invDen x * vx x))) :=
  memHSigma_cosineCoeffs_mul3_of_gt_half hσ hden_vx hu_rest hu hv hvx

/-! ## 5. Integer-power function composition (the `u^m` factor). -/

/-- The iterated *function* power `funPow u m = u^{m+1}` (so `funPow u 0 = u`,
`funPow u 1 = u·u`, …), the function-level analogue of the landed sequence
`cosPow`.  Discharges the `u^m` chemotaxis factor for integer `m ≥ 1` purely through
the `H^σ` Banach algebra. -/
def funPow (u : ℝ → ℝ) : ℕ → (ℝ → ℝ)
  | 0 => u
  | (m + 1) => fun x => u x * funPow u m x

/-- **Integer-power function `H^σ` membership** (σ > 1/2).  Given the cosine-product
bridge at each multiplication step of `u^{m+1}`, the cosine coefficients of the
*function* power `funPow u m` lie in `H^σ`.  The bridge hypotheses are packaged as a
single statement quantified over the assembly levels. -/
theorem memHSigma_cosineCoeffs_funPow_of_gt_half {σ : ℝ} (hσ : 1 / 2 < σ)
    {u : ℝ → ℝ} (hu : MemHSigma σ (cosineCoeffs u)) :
    ∀ m : ℕ, (∀ j < m, CosineMulBridge u (funPow u j)) →
      MemHSigma σ (cosineCoeffs (funPow u m))
  | 0, _ => hu
  | (m + 1), hbridge => by
      have hrec : MemHSigma σ (cosineCoeffs (funPow u m)) :=
        memHSigma_cosineCoeffs_funPow_of_gt_half hσ hu m
          (fun j hj => hbridge j (Nat.lt_succ_of_lt hj))
      exact memHSigma_cosineCoeffs_mul_of_gt_half hσ
        (hbridge m (Nat.lt_succ_self m)) hu hrec

/-- **Chemotaxis flux `H^σ` (integer-power function form, σ > 1/2).**  The flux
`u^{m+1} · (1+v)^{−β} · v_x` at the *function* level: the `u^{m+1}` factor is the
iterated function power `funPow u m`, whose `H^σ` membership comes from the integer
power composition above, and the rest assembles by the triple-product bridge.  This
is the fully integer-power instance of the chemotaxis flux target — no real-exponent
composition is needed for `u^m` when `m` is a positive integer. -/
theorem chemotaxisFlux_memHSigma_intPow_function {σ : ℝ} (hσ : 1 / 2 < σ)
    {u invDen vx : ℝ → ℝ} (m : ℕ)
    (hpow : ∀ j < m, CosineMulBridge u (funPow u j))
    (hden_vx : CosineMulBridge invDen vx)
    (hu_rest : CosineMulBridge (funPow u m) (fun x => invDen x * vx x))
    (hu : MemHSigma σ (cosineCoeffs u))
    (hv : MemHSigma σ (cosineCoeffs invDen))
    (hvx : MemHSigma σ (cosineCoeffs vx)) :
    MemHSigma σ (cosineCoeffs (fun x => funPow u m x * (invDen x * vx x))) :=
  memHSigma_cosineCoeffs_mul3_of_gt_half hσ hden_vx hu_rest
    (memHSigma_cosineCoeffs_funPow_of_gt_half hσ hu m hpow) hv hvx

/-! ## 6. A genuine (non-vacuous) instance of the bridge: multiplication by `1`.

The `CosineMulBridge` predicate is satisfiable: it holds whenever the right factor
is the constant function `1` (then `f·1 = f`, and the bridge reduces to the exact
delta-convolution computation `trueCosProd â (cosineCoeffs 1) = â`).  This proves the
predicate is non-vacuous and concretely verifies that `trueCosProd` — *not* the
landed `cosProd` — is the correct product operator (the `k = 0` correction is exactly
what makes `f·1 = f` come out right). -/

/-- The cosine coefficients of the constant function `1`: the Kronecker delta at
mode `0`.  (Mode `0`: `∫₀¹ 1 = 1`, scaled by `1`.  Mode `n ≥ 1`: `∫₀¹ cos(nπx) =
sin(nπ)/(nπ) = 0`.) -/
theorem cosineCoeffs_one :
    cosineCoeffs (fun _ => (1 : ℝ)) = fun n => if n = 0 then (1 : ℝ) else 0 := by
  funext n
  unfold cosineCoeffs ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff
    ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff
  by_cases h : n = 0
  · subst h
    simp only [Nat.cast_zero, zero_mul]
    norm_num
  · simp only [if_neg h]
    have hint : (∫ x in (0:ℝ)..1, (↑(Real.cos ((n:ℝ) * Real.pi * x)) : ℂ) * ↑(1:ℝ))
        = ((∫ x in (0:ℝ)..1, Real.cos ((n:ℝ) * Real.pi * x) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      exact intervalIntegral.integral_congr (fun x _ => by push_cast; ring)
    rw [hint, Complex.ofReal_re]
    have hc : ((n:ℝ) * Real.pi) ≠ 0 := by
      have := Real.pi_pos
      have hn : (n:ℝ) ≠ 0 := by exact_mod_cast h
      positivity
    have hcos : (∫ x in (0:ℝ)..1, Real.cos ((n:ℝ) * Real.pi * x)) = 0 := by
      rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc,
          integral_cos]
      have hs : Real.sin ((n:ℝ) * Real.pi * 1) = 0 := by
        rw [mul_one, show (n:ℝ) * Real.pi = ((n:ℤ):ℝ) * Real.pi by push_cast; ring]
        exact Real.sin_int_mul_pi n
      rw [mul_zero, hs]; simp
    rw [hcos, mul_zero]

/-- `addConv a e₀ k = a k` for the mode-`0` delta `e₀` (only `(k,0)` contributes). -/
theorem addConv_delta_right (a : ℕ → ℝ) (k : ℕ) :
    addConv a (fun n => if n = 0 then (1 : ℝ) else 0) k = a k := by
  unfold addConv
  rw [Finset.sum_eq_single (k, 0)]
  · simp
  · rintro ⟨m, n⟩ hmem hne
    rw [Finset.mem_antidiagonal] at hmem
    by_cases hn : n = 0
    · subst hn; simp only [add_zero] at hmem; subst hmem; simp at hne
    · simp [hn]
  · intro hmem; exact absurd (Finset.mem_antidiagonal.mpr (by simp)) hmem

/-- `corr1 a e₀ k = a k` (the `(m−n=k)` leaf against the right delta). -/
theorem corr1_delta_right (a : ℕ → ℝ) (k : ℕ) :
    corr1 a (fun n => if n = 0 then (1 : ℝ) else 0) k = a k := by
  unfold corr1
  rw [tsum_eq_single 0]
  · simp
  · intro n hn; simp [hn]

/-- `corr1 e₀ a 0 = a 0` (the other leaf, at mode `0`: the diagonal). -/
theorem corr1_delta_left_zero (a : ℕ → ℝ) :
    corr1 (fun n => if n = 0 then (1 : ℝ) else 0) a 0 = a 0 := by
  unfold corr1
  rw [tsum_eq_single 0]
  · simp
  · intro n hn; simp [hn]

/-- `corr1 e₀ a k = 0` for `k ≥ 1` (the other leaf vanishes off the diagonal). -/
theorem corr1_delta_left_pos (a : ℕ → ℝ) {k : ℕ} (hk : k ≠ 0) :
    corr1 (fun n => if n = 0 then (1 : ℝ) else 0) a k = 0 := by
  unfold corr1
  have h0 : ∀ n : ℕ, (if n + k = 0 then (1 : ℝ) else 0) * a n = 0 := by
    intro n; rw [if_neg (by omega : n + k ≠ 0), zero_mul]
  rw [tsum_congr h0, tsum_zero]

/-- `diagCorr a e₀ = a 0` (the diagonal correlation against the right delta). -/
theorem diagCorr_delta_right (a : ℕ → ℝ) :
    diagCorr a (fun n => if n = 0 then (1 : ℝ) else 0) = a 0 := by
  unfold diagCorr
  rw [tsum_eq_single 0]
  · simp
  · intro n hn; simp [hn]

/-- **`trueCosProd` against the mode-`0` delta is the identity.**  This is the exact
delta-convolution verification: `trueCosProd a e₀ = a`.  At `k = 0` the landed
`cosProd a e₀ 0 = (3/2) a 0` is wrong, and the `trueCosProd` correction
`−½ diagCorr = −½ a 0` repairs it to `a 0`; at `k ≥ 1` both equal `a k`. -/
theorem trueCosProd_delta_right (a : ℕ → ℝ) :
    trueCosProd a (fun n => if n = 0 then (1 : ℝ) else 0) = a := by
  funext k
  unfold trueCosProd cosProd diffConv
  by_cases hk : k = 0
  · subst k
    rw [addConv_delta_right, corr1_delta_right, corr1_delta_left_zero,
        diagCorr_delta_right, if_pos rfl]; ring
  · rw [addConv_delta_right, corr1_delta_right, corr1_delta_left_pos a hk,
        if_neg hk]; ring

/-- **The bridge holds for multiplication by the constant `1`.**  A concrete,
fully-proven (non-vacuous) witness that `CosineMulBridge` is satisfiable and that
`trueCosProd` is the correct normalized cosine-product operator. -/
theorem cosineMulBridge_one (f : ℝ → ℝ) : CosineMulBridge f (fun _ => (1 : ℝ)) := by
  intro k
  have hprod : cosineCoeffs (fun x => f x * (fun _ => (1 : ℝ)) x) = cosineCoeffs f := by
    simp
  rw [hprod, cosineCoeffs_one, trueCosProd_delta_right]

#print axioms reflCircle_mul
#print axioms memHSigma_congr_except
#print axioms memHSigma_trueCosProd_of_gt_half
#print axioms memHSigma_cosineCoeffs_mul_of_gt_half
#print axioms chemotaxisFlux_memHSigma_function
#print axioms memHSigma_cosineCoeffs_funPow_of_gt_half
#print axioms chemotaxisFlux_memHSigma_intPow_function
#print axioms cosineCoeffs_one
#print axioms trueCosProd_delta_right
#print axioms cosineMulBridge_one

end ShenWork.Paper2.IntervalWienerAlgebra
