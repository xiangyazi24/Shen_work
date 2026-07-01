# Q2844 (shen1) — coefficient dissipation absorption wrapper

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Source edit requested: none; answer file only.

Off-limits producer files, not touched:

- `ShenWork/PDE/P3MoserHighExcursionProducer.lean`
- `ShenWork/PDE/P3MoserThresholdPlanProducer.lean`

## Visibility note

I tried to verify the new names with the GitHub connector, but the connector-visible default branch does **not** yet show:

```lean
IntegratedMoserDissipationDropBeforeCoeff
integratedMoserDissipationDropBefore_of_coeff_two
integratedMoserDissipationDropBefore_of_coeff_ge_two
scalar_absorb_higherPower_window
```

The visible source still has only the fixed-coefficient `IntegratedMoserDissipationDropBefore` and the old integrated relative-Moser helper. So the exact proof term below is necessarily a patch sketch against the API you described. The surrounding existing names and risks are verified from the visible files.

## Verdict

The next smallest non-Zinan wrapper should live in:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
```

not in `P3MoserDissipationShape.lean`, because `P3MoserIntegratedClosure.lean` already imports `P3MoserDissipationShape.lean`; putting the absorption wrapper back in `P3MoserDissipationShape.lean` would likely create an import cycle if it calls `scalar_absorb_higherPower_window` from `P3MoserIntegratedClosure.lean`.

The honest wrapper should **not** claim that arbitrary positive gradient coefficient `A > 0` is enough. It should require an explicit surplus over the target coefficient:

```lean
theta < A
```

or, even more explicitly,

```lean
K * eps ≤ A - theta
```

for the chosen relative-Moser epsilon. Since `eps` can be chosen after `A` and `K`, `theta < A` plus `0 ≤ K` is a convenient practical form: choose

```lean
eps := (A - theta) / (K + 1)
```

then `0 < eps` and `K * eps ≤ A - theta`.

## Recommended wrapper statement

This wrapper assumes a full-window integrated higher-power bound and a full-window integrated relative-Moser estimate. That is deliberate: it avoids silently using a pointwise relative estimate at `t = 0` or `t = T`, where the current relative-Moser predicate only talks about `0 < t < T`.

```lean
import ShenWork.PDE.P3MoserIntegratedClosure

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Absorb an integrated higher-power term using a full-window integrated
relative-Moser estimate, producing the coefficient-form integrated Moser
dissipation predicate.

The surplus condition is `theta < A`, not merely `0 < A`.  The proof chooses
`eps = (A - theta) / (K + 1)`, so `K * eps ≤ A - theta`.

The `hrelWin` hypothesis is intentionally already integrated over the closed
window.  Deriving it from pointwise `RelativeMoserInterpolationBefore` at
endpoints is a separate endpoint/a.e. lemma. -/
theorem integratedMoserDissipationDropBeforeCoeff_of_higherPower_and_relative
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 theta : ℝ}
    (hp0_one : 1 ≤ p0)
    (hG_nonneg :
      ∀ p, p0 ≤ p →
      ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        0 ≤ ∫ s in t1..t2,
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2))
    (hraw :
      ∀ p, p0 ≤ p →
        ∃ A C K, theta < A ∧ 0 ≤ C ∧ 0 ≤ K ∧
          ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
            D.integral (fun x => (u t2 x) ^ p) -
                D.integral (fun x => (u t1 x) ^ p) +
              A * (∫ s in t1..t2,
                D.integral (fun x =>
                  (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) ≤
            C * p * (∫ s in t1..t2,
              max 1 (D.integral (fun x => (u s x) ^ p))) +
            K * (∫ s in t1..t2,
              D.integral (fun x => (u s x) ^ (p + rho))))
    (hrelWin :
      ∀ p, p0 ≤ p → ∀ eps, 0 < eps →
        ∃ Ceps, 0 ≤ Ceps ∧
          ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
            (∫ s in t1..t2,
              D.integral (fun x => (u s x) ^ (p + rho))) ≤
            eps * (∫ s in t1..t2,
              D.integral (fun x =>
                (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) +
            Ceps * (∫ s in t1..t2,
              max 1 (D.integral (fun x => (u s x) ^ p)))) :
    IntegratedMoserDissipationDropBeforeCoeff theta D u T rho p0 := by
  intro p hp
  rcases hraw p hp with ⟨A, C, K, htheta_lt_A, hC_nonneg, hK_nonneg, hraw_p⟩
  let eps : ℝ := (A - theta) / (K + 1)
  have hA_sub_pos : 0 < A - theta := sub_pos.mpr htheta_lt_A
  have hKp1_pos : 0 < K + 1 := by linarith
  have heps_pos : 0 < eps := by
    dsimp [eps]
    exact div_pos hA_sub_pos hKp1_pos
  have hsurplus : K * eps ≤ A - theta := by
    dsimp [eps]
    have hfrac : K / (K + 1) ≤ 1 := by
      field_simp [ne_of_gt hKp1_pos]
      linarith
    have hrewrite : K * ((A - theta) / (K + 1)) =
        (K / (K + 1)) * (A - theta) := by ring
    rw [hrewrite]
    exact mul_le_of_le_one_left hA_sub_pos.le hfrac
  rcases hrelWin p hp eps heps_pos with ⟨Ceps, hCeps_nonneg, hrel_p⟩
  refine ⟨C + K * Ceps, add_nonneg hC_nonneg (mul_nonneg hK_nonneg hCeps_nonneg), ?_⟩
  intro t1 ht1 t2 ht2
  have hp_one : 1 ≤ p := le_trans hp0_one hp
  have hH_nonneg :
      0 ≤ ∫ s in t1..t2,
        max 1 (D.integral (fun x => (u s x) ^ p)) := by
    exact intervalIntegral.integral_nonneg_of_forall ht2.1
      (fun _ => le_trans zero_le_one (le_max_left _ _))
  have hG_nonneg_win := hG_nonneg p hp t1 ht1 t2 ht2
  have hraw_win := hraw_p t1 ht1 t2 ht2
  have hrel_win := hrel_p t1 ht1 t2 ht2
  -- Expected one-line call if `scalar_absorb_higherPower_window` has the intended API:
  exact scalar_absorb_higherPower_window
    (theta := theta) (A := A) (C := C) (K := K) (Ceps := Ceps)
    (p := p)
    (Ydiff :=
      D.integral (fun x => (u t2 x) ^ p) -
        D.integral (fun x => (u t1 x) ^ p))
    (G := ∫ s in t1..t2,
      D.integral (fun x =>
        (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2))
    (Z := ∫ s in t1..t2,
      D.integral (fun x => (u s x) ^ (p + rho)))
    (H := ∫ s in t1..t2,
      max 1 (D.integral (fun x => (u s x) ^ p)))
    hp_one hG_nonneg_win hH_nonneg hK_nonneg hCeps_nonneg hsurplus
    hraw_win hrel_win

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

If `scalar_absorb_higherPower_window` does not include the `p`/`H` scaling, the final line can be replaced by the same scalar algebra inline. The required scalar facts are exactly:

```lean
0 ≤ G
0 ≤ H
0 ≤ K
0 ≤ Ceps
1 ≤ p
K * eps ≤ A - theta
Ydiff + A * G ≤ C * p * H + K * Z
Z ≤ eps * G + Ceps * H
```

and the target is:

```lean
Ydiff + theta * G ≤ (C + K * Ceps) * p * H
```

The `1 ≤ p` assumption is why the wrapper should assume `hp0_one : 1 ≤ p0`; otherwise `K*Ceps*H ≤ K*Ceps*p*H` is not available.

## Should the integrated relative-Moser lemma with `∫Y` be proved now?

There is an easy **interior-window** lemma from current APIs, but it is not quite enough for `IntegratedMoserDissipationDropBeforeCoeff`, whose windows may include `0` and `T`.

A likely compileable interior lemma is:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure

open MeasureTheory
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Integrated relative-Moser on a strict interior window, with the lower-order
term kept as `∫Y_p` rather than replaced by a pointwise bound. -/
theorem relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_integral
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b eps : ℝ}
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hp : p0 ≤ p)
    (heps : 0 < eps)
    (hab : a ≤ b)
    (ha : 0 < a)
    (hb : b < T)
    (hZ_int :
      IntervalIntegrable
        (fun s => D.integral (fun x => (u s x) ^ (p + rho)))
        volume a b)
    (hG_int :
      IntervalIntegrable
        (fun s =>
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2))
        volume a b)
    (hY_int :
      IntervalIntegrable
        (fun s => D.integral (fun x => (u s x) ^ p))
        volume a b) :
    ∃ Ceps, 0 ≤ Ceps ∧
      ∫ s in a..b,
          D.integral (fun x => (u s x) ^ (p + rho)) ≤
        eps * (∫ s in a..b,
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) +
        Ceps * (∫ s in a..b,
          D.integral (fun x => (u s x) ^ p)) := by
  rcases hrel p hp eps heps with ⟨Ceps, hCeps_nonneg, hpoint⟩
  refine ⟨Ceps, hCeps_nonneg, ?_⟩
  have hR_int :
      IntervalIntegrable
        (fun s =>
          eps * D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) +
          Ceps * D.integral (fun x => (u s x) ^ p))
        volume a b :=
    (hG_int.const_mul eps).add (hY_int.const_mul Ceps)
  have hmono := intervalIntegral.integral_mono_on hab hZ_int hR_int (by
    intro s hs
    exact hpoint s (lt_of_lt_of_le ha hs.1) (lt_of_le_of_lt hs.2 hb))
  have hsplit :
      (∫ s in a..b,
        eps * D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) +
        Ceps * D.integral (fun x => (u s x) ^ p)) =
      eps * (∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) +
      Ceps * (∫ s in a..b,
        D.integral (fun x => (u s x) ^ p)) := by
    rw [intervalIntegral.integral_add (hG_int.const_mul eps) (hY_int.const_mul Ceps)]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simpa [hsplit] using hmono

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

This is useful, but I would **not** use it directly in the coefficient wrapper unless you also prove an endpoint/a.e. version. The coefficient predicate quantifies:

```lean
t1 ∈ Set.Icc (0 : ℝ) T
 t2 ∈ Set.Icc t1 T
```

so `t1 = 0` and `t2 = T` are allowed. Pointwise `RelativeMoserInterpolationBefore` only supplies estimates for:

```lean
0 < t → t < T
```

Bridging the endpoints is likely true by endpoint-null/a.e. arguments plus integrability, but that is an extra lemma. Until it is proved, keep `hrelWin` as a full-window integrated hypothesis in the coefficient wrapper.

## Hidden assumptions / unsoundness checks

1. **Arbitrary `A > 0` is not enough.**  To get target coefficient `theta`, require either `theta < A` and choose `eps`, or explicitly require `K * eps ≤ A - theta`. For the fixed coefficient 2 route, this becomes surplus over 2.

2. **Need `0 ≤ G` to drop the leftover gradient term.**  If `K*eps - (A-theta) ≤ 0`, then dropping `(K*eps - (A-theta))*G` needs `0 ≤ G`. For `intervalDomain`, this comes from squared gradients; for generic `D`, assume it.

3. **Need `1 ≤ p0` or equivalent.**  The final target has `C * p * H`. To absorb a relative lower-order term `K*Ceps*H` into `K*Ceps*p*H`, you need `1 ≤ p`. Since only `p0 ≤ p` is available, assume `1 ≤ p0`.

4. **Endpoint windows are not automatic from pointwise relative Moser.**  Interior integrated relative-Moser is easy. Full closed-window integrated relative-Moser needs an endpoint-null/a.e. lemma and integrability; otherwise it should remain a separate hypothesis.

5. **Do not put this wrapper in `P3MoserDissipationShape.lean` if it calls `scalar_absorb_higherPower_window`.**  That would likely introduce an import cycle because `P3MoserIntegratedClosure.lean` already imports `P3MoserDissipationShape.lean`.

## Minimal next edit

Add the coefficient absorption wrapper in `P3MoserIntegratedClosure.lean`, with `hrelWin` as a full-window integrated hypothesis. Then separately add the strict-interior integrated relative-Moser `∫Y` lemma. Only after an endpoint/a.e. version is proved should `hrelWin` be replaced by `RelativeMoserInterpolationBefore` plus regularity integrability fields.
