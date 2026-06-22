# Paper 1: C2 limits from uniformly C3-bounded translates

## Executive verdict

The clean Lean route is:

1. Extract a common subsequence for the three families

       U_n,
       deriv U_n,
       deriv (deriv U_n)

   using nested Arzela-Ascoli / diagonal selection on compact intervals.

2. Use Mathlib's uniform-limit-of-derivatives theorem

       hasDerivAt_of_tendstoLocallyUniformlyOn

   twice:

       U_n -> W,      U_n' -> G1   => HasDerivAt W (G1 x) x,
       U_n' -> G1,    U_n'' -> G2  => HasDerivAt G1 (G2 x) x.

3. Then identify

       deriv W = G1,
       deriv (deriv W) = G2,

   pointwise via `HasDerivAt.deriv`.

4. Pass uniform pointwise bounds to the limits by pointwise convergence.

The derivative-limit theorem exists and is already used in the repo.  The Arzela-Ascoli extraction on the whole line is the part I would keep as project-local infrastructure rather than trying to find a fragile one-line Mathlib theorem.

## 1. Exact derivative-limit theorem

Import:

    import Mathlib.Analysis.Calculus.UniformLimitsDeriv

The theorem used in the repo is:

    hasDerivAt_of_tendstoLocallyUniformlyOn

The instantiated shape for functions `R -> R` is:

    hasDerivAt_of_tendstoLocallyUniformlyOn
      (𝕜 := R) (l := atTop) (s := Set.univ)
      (f := f_n)
      (f' := f_n')
      (g := f)
      (g' := g')
      isOpen_univ
      hderiv_loc
      hfinite_hasDeriv
      hvalue_pointwise
      (Set.mem_univ x)

The repo contains an exact working instance in `ShenWork/PaperOne/WholeLineImageDifferentiable.lean`:

    hasDerivAt_of_tendstoLocallyUniformlyOn
      (𝕜 := R) (l := atTop) (s := Set.univ)
      (f := fun n => w U (time n))
      (f' := fun n y => deriv (w U (time n)) y)
      (g := longTimeMap w U) (g' := dlim)
      isOpen_univ hderiv_loc ... ... (Set.mem_univ x)

Its hypotheses are:

1. `IsOpen s`;
2. derivative convergence:

       TendstoLocallyUniformlyOn f' g' l s;

3. eventual differentiability of the approximants:

       forallᶠ n in l, forall x, x in s -> HasDerivAt (f n) (f' n x) x;

4. pointwise convergence of values:

       forall x, x in s -> Tendsto (fun n => f n x) l (nhds (g x));

5. the point `x in s`.

It returns:

    HasDerivAt g (g' x) x.

Important: it does **not** require local-uniform convergence of the values, only pointwise convergence of values.  Local-uniform value convergence is more than enough, because

    hval_loc.tendsto_at (Set.mem_univ x)

gives the pointwise convergence hypothesis.

## 2. Apply the theorem twice

Suppose after extraction you have:

    hU  : TendstoLocallyUniformlyOn (fun j x => U (phi j) x) W atTop Set.univ
    hU1 : TendstoLocallyUniformlyOn (fun j x => deriv (U (phi j)) x) G1 atTop Set.univ
    hU2 : TendstoLocallyUniformlyOn (fun j x => deriv (deriv (U (phi j))) x) G2 atTop Set.univ

and finite-level differentiability:

    hD0 : forall j x,
      HasDerivAt (U (phi j)) (deriv (U (phi j)) x) x

    hD1 : forall j x,
      HasDerivAt (fun y => deriv (U (phi j)) y)
        (deriv (deriv (U (phi j))) x) x.

Then:

    have hW_has : forall x, HasDerivAt W (G1 x) x := by
      intro x
      refine hasDerivAt_of_tendstoLocallyUniformlyOn
        (k := R) (l := atTop) (s := Set.univ)
        (f := fun j => U (phi j))
        (f' := fun j y => deriv (U (phi j)) y)
        (g := W) (g' := G1)
        isOpen_univ hU1 ?_ ?_ (Set.mem_univ x)
      · exact Eventually.of_forall (fun j y hy => hD0 j y)
      · intro y hy
        exact hU.tendsto_at hy

    have hG1_has : forall x, HasDerivAt G1 (G2 x) x := by
      intro x
      refine hasDerivAt_of_tendstoLocallyUniformlyOn
        (k := R) (l := atTop) (s := Set.univ)
        (f := fun j => fun y => deriv (U (phi j)) y)
        (f' := fun j y => deriv (deriv (U (phi j))) y)
        (g := G1) (g' := G2)
        isOpen_univ hU2 ?_ ?_ (Set.mem_univ x)
      · exact Eventually.of_forall (fun j y hy => hD1 j y)
      · intro y hy
        exact hU1.tendsto_at hy

Then define pointwise derivative identities:

    have hderivW : deriv W = G1 := by
      funext x
      exact (hW_has x).deriv

    have hderivG1 : deriv G1 = G2 := by
      funext x
      exact (hG1_has x).deriv

From `hderivW`, if needed:

    Differentiable R W := fun x => (hW_has x).differentiableAt

and from `hderivG1`:

    Differentiable R (deriv W)

by rewriting `deriv W = G1` and using `hG1_has`.

So the limit is C2 in the sense needed for ODE/PDE work:

    Differentiable R W,
    Differentiable R (deriv W),
    deriv W = G1,
    deriv (deriv W) = G2.

If you need `ContDiff R 2 W`, you must also prove continuity of `G2`.  Local-uniform limits of continuous functions are continuous, so if each `U_n''` is continuous and `U_n'' -> G2` locally uniformly, then `G2` is continuous.  Then combine differentiability and continuity to build the `ContDiff` statement.  For most stationary ODE arguments, the two differentiability fields plus continuity of G2 are enough.

## 3. Common subsequence extraction

You start with only values converging along some subsequence.  To identify derivatives, you need convergence of derivative families along a compatible subsequence.

The robust extraction is nested:

1. Start with the value subsequence `phi0` such that

       U_{phi0 n} -> W

   locally uniformly.

2. Apply Arzela-Ascoli to the derivative family

       V1_n = deriv (U_{phi0 n})

   to obtain a further subsequence `psi1` and a limit `G1`:

       V1_{psi1 n} -> G1

   locally uniformly.

   The values still converge to W along the further subsequence, because subsequences preserve convergence.

3. Apply Arzela-Ascoli to the second derivative family

       V2_n = deriv (deriv (U_{phi0 (psi1 n)}))

   to obtain a further subsequence `psi2` and a limit `G2`.

4. Compose subsequences:

       phi n = phi0 (psi1 (psi2 n)).

Then along `phi`, all three families converge locally uniformly:

       U_phi -> W,
       U_phi' -> G1,
       U_phi'' -> G2.

This nested selection is simpler than trying to extract a single subsequence in a product space, though the product-space route is also valid.

## 4. Arzela-Ascoli infrastructure

I would not rely on a general Mathlib Arzela-Ascoli theorem for this proof unless you have already located and tested it in the repo.  The derivative-limit theorem is available and stable; a convenient whole-line AA theorem is usually project-local.

The minimal helper you need is:

    theorem locallyUniform_subseq_of_uniform_bound_lipschitz
      (F : Nat -> R -> R)
      (hbound : forall R, exists C_R, forall n x,
         x in Set.Icc (-R) R -> abs (F n x) <= C_R)
      (hlip : forall R, exists L_R, forall n x y,
         x in Set.Icc (-R) R -> y in Set.Icc (-R) R ->
           abs (F n x - F n y) <= L_R * abs (x - y)) :
      exists phi : Nat -> Nat, StrictMono phi and
      exists Flim : R -> R,
        TendstoLocallyUniformlyOn (fun j x => F (phi j) x)
          Flim atTop Set.univ

Proof by hand:

1. For each integer R >= 1, restrict to `Icc (-R) R`.
2. Uniform boundedness plus uniform Lipschitz gives equicontinuity.
3. Prove compact-interval AA using a finite mesh:
   - choose mesh size delta from the Lipschitz modulus;
   - values at finitely many mesh points lie in compact intervals `Icc (-C_R) C_R`;
   - use Bolzano-Weierstrass on the finite product;
   - extend convergence from mesh points to uniform convergence by Lipschitz control.
4. Diagonalize over R = 1,2,3,...

If the repo already has `RotheAACompactnessData`, use it as the provider.  But for derivatives you need it reusable for arbitrary families, not just the original profiles.

A product-family version is also convenient:

    Fpair_n x = ![U_n x, U_n' x, U_n'' x] : Fin 3 -> R.

Uniform C3 bounds imply this vector-valued family is uniformly bounded and Lipschitz on compacts.  Apply AA once to `Fpair_n`; then project coordinates to get W, G1, G2.  This may be cleaner than nested extraction if the repo has finite-dimensional vector-valued local-uniform compactness.

## 5. Equicontinuity from derivative bounds

For the family `U_n`, the bound `|deriv U_n| <= C` gives Lipschitz:

    abs (U_n x - U_n y) <= C * abs (x - y).

For `deriv U_n`, use `|deriv (deriv U_n)| <= C`.

For `deriv (deriv U_n)`, use `|thirdDeriv U_n| <= C`.

Mathlib routes:

1. Mean-value theorem route.

   The relevant theorem family is in `Mathlib.Analysis.Calculus.MeanValue`.  Names can vary by exact statement, but the typical theorem to use is one of:

       Convex.norm_image_sub_le_of_norm_deriv_le
       Convex.norm_image_sub_le_of_norm_hasDerivWithinAt_le

   on the convex set `Set.Icc a b` or `Set.univ`.

   For functions R -> R, the statement gives:

       norm (f x - f y) <= C * norm (x - y)

   assuming differentiability on the interval and a derivative norm bound.

2. If a direct Lipschitz theorem is available under imports, try:

       lipschitzWith_of_nnnorm_deriv_le
       lipschitzOnWith_of_nnnorm_deriv_le

   or the corresponding `fderiv` versions.  These names are less stable than the convex mean-value theorem route.

3. If API friction is high, prove a small helper once:

       theorem abs_sub_le_of_deriv_bound
         (hf : forall x, HasDerivAt f (f' x) x)
         (hbound : forall x, abs (f' x) <= C)
         (hC : 0 <= C) :
         forall x y, abs (f x - f y) <= C * abs (x - y)

   using the mean value theorem on `Icc (min x y) (max x y)`.

Once you have Lipschitz, equicontinuity is immediate.  In Mathlib, `LipschitzWith` has standard continuity/equicontinuity consequences, but for AA it is often simpler to use the Lipschitz inequality directly in the finite-mesh proof.

## 6. Passing bounds to the limits

The repo already has the exact useful lemma:

    abs_le_of_tendstoLocallyUniformlyOn_of_uniform_abs_le

from `WholeLineImageDifferentiable.lean`.

Shape:

    theorem abs_le_of_tendstoLocallyUniformlyOn_of_uniform_abs_le
        {fs : Nat -> R -> R} {f : R -> R} {B : R}
        (hlim : TendstoLocallyUniformlyOn fs f atTop Set.univ)
        (hbound : forall n x, abs (fs n x) <= B) :
        forall x, abs (f x) <= B

It uses pointwise convergence from `hlim.tendsto_at` and `le_of_tendsto'`.

Apply it to:

    fs n x = deriv (U (phi n)) x,       limit G1,
    fs n x = deriv (deriv (U (phi n))) x, limit G2.

Then rewrite with derivative identities:

    abs (deriv W x) <= C,
    abs (deriv (deriv W) x) <= C.

If you also extract the third derivatives and identify the derivative of G2, you can prove the bound for `deriv^[3] W`; but for C2 you do not need this.

## 7. Overall Lean theorem skeleton

A good theorem statement is:

    structure UniformC3Family (U : Nat -> R -> R) (C : R) : Prop where
      C_nonneg : 0 <= C
      has0 : forall n x, abs (U n x) <= C
      has1 : forall n x, HasDerivAt (U n) (deriv (U n) x) x
      bd1  : forall n x, abs (deriv (U n) x) <= C
      has2 : forall n x,
        HasDerivAt (fun y => deriv (U n) y)
          (deriv (deriv (U n)) x) x
      bd2  : forall n x, abs (deriv (deriv (U n)) x) <= C
      has3 : forall n x,
        HasDerivAt (fun y => deriv (deriv (U n)) y)
          (thirdDeriv U n x) x
      bd3  : forall n x, abs (thirdDeriv U n x) <= C

Then the compactness theorem:

    theorem subseq_C2_limit_of_uniformC3
      (H : UniformC3Family U C)
      (hval : exists phi0 W,
        StrictMono phi0 and
        TendstoLocallyUniformlyOn (fun j x => U (phi0 j) x) W atTop Set.univ) :
      exists phi W G1 G2,
        StrictMono phi and
        TendstoLocallyUniformlyOn (fun j x => U (phi j) x) W atTop Set.univ and
        TendstoLocallyUniformlyOn (fun j x => deriv (U (phi j)) x) G1 atTop Set.univ and
        TendstoLocallyUniformlyOn (fun j x => deriv (deriv (U (phi j))) x) G2 atTop Set.univ and
        (forall x, HasDerivAt W (G1 x) x) and
        (forall x, HasDerivAt G1 (G2 x) x) and
        deriv W = G1 and
        deriv (deriv W) = G2 and
        (forall x, abs (W x) <= C) and
        (forall x, abs (deriv W x) <= C) and
        (forall x, abs (deriv (deriv W) x) <= C)

Proof outline:

1. Use `hval` for values.
2. Apply the project AA helper to `deriv (U (phi0 n))`, using `bd1` for boundedness and `bd2` for Lipschitz.
3. Apply the project AA helper to `deriv (deriv (U (phi0 (psi1 n))))`, using `bd2` for boundedness and `bd3` for Lipschitz.
4. Compose subsequences.
5. Use `hasDerivAt_of_tendstoLocallyUniformlyOn` twice.
6. Use `(hhas x).deriv` to identify `deriv W` and `deriv G1`.
7. Use the bound-passing lemma to pass `C` bounds to W, G1, G2.

## 8. If Mathlib AA is unavailable or awkward

The minimal helper to add is the local compact Lipschitz AA theorem above.  It is only a metric-space diagonal argument over compact intervals and finite meshes.  It is much smaller and more stable than trying to force a general compact-open Arzela-Ascoli theorem into the proof.

A very practical version specialized to this project is:

    theorem real_locallyUniform_subseq_of_uniform_bound_lipschitz
      (F : Nat -> R -> R)
      (C L : R) (hC : 0 <= C) (hL : 0 <= L)
      (hbound : forall n x, abs (F n x) <= C)
      (hlip : forall n x y, abs (F n x - F n y) <= L * abs (x-y)) :
      exists phi G,
        StrictMono phi and
        TendstoLocallyUniformlyOn (fun j x => F (phi j) x) G atTop Set.univ

This global-bound/global-Lipschitz version is exactly enough for uniformly C3-bounded translates.

If you only have local bounds on each `Icc (-R) R`, use the local version and diagonalize over natural R.

## 9. Final recommendation

For the P1 left-translate theorem, formalize this as two reusable pieces:

1. `real_locallyUniform_subseq_of_uniform_bound_lipschitz`, specialized and project-local.
2. `C2_limit_of_locallyUniform_values_and_derivatives`, using Mathlib's exact theorem

       hasDerivAt_of_tendstoLocallyUniformlyOn.

This avoids depending on a possibly hard-to-use general Arzela-Ascoli theorem and uses the Mathlib derivative-limit theorem in the way already proven to work in the repository.
