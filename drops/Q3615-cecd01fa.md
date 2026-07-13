ANSWER Q3615 cecd01fa

# Task151 audit: endpoint-layer operator vanish from endpoint smallness

Repository/head audited:

```text
xiangyazi24/Shen_work main HEAD 870035d3
```

Current `ShenWork/PDE/IntervalSemigroupC1ApproxIdentity.lean` already contains:

```lean
theorem conjugateKernel_abs_moment_le
    {t : ℝ} (ht : 0 < t) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ y in (0 : ℝ)..1,
        |y - x| * |intervalNeumannConjugateKernel t x y|)
      ≤ 4 * t / Real.sqrt (4 * Real.pi * t)
```

and:

```lean
theorem initialLegConjugateOscillationControl_of_continuousOn
    {df : ℝ → ℝ}
    (hdf_cont : ContinuousOn df (Set.Icc (0 : ℝ) 1)) :
    InitialLegConjugateOscillationControl df
```

## Verdict

The proposed theorem is non-circular and is the right next theorem in the same file:

```lean
theorem initialLegConjugateEndpointOperatorVanish_of_endpointSmall_bound
    {df : ℝ → ℝ} {M : ℝ}
    (hdf_cont : ContinuousOn df (Set.Icc (0 : ℝ) 1))
    (hM : 0 ≤ M)
    (hdf_bound : ∀ y ∈ Set.Icc (0 : ℝ) 1, |df y| ≤ M)
    (hsmall : InitialLegDerivativeEndpointSmall df) :
    InitialLegConjugateEndpointOperatorVanish df
```

It uses only endpoint smallness, the global bound, `conjugateKernel_L1_bound`, and `conjugateKernel_abs_moment_le`.  It does not need positivity of `-intervalNeumannConjugateKernel`, mass-defect control, reflected-kernel definitions, or endpoint cancellation at exact `x = 0,1`.

The constants work as follows:

* Ask `hsmall` for `ε / 2`; get `ηs > 0`, `ηs < 1/2`.
* Set endpoint operator layer `η := ηs / 2`.
* Set `C := 2 * M / ηs + 1`.

The `+ 1` is useful: it guarantees `0 < C` even in the degenerate case `M = 0`, so the square-root time horizon

```lean
δ := (ε / (4 * C)) ^ 2
```

is positive without a case split.

The key pointwise bound for `x` in the endpoint layer is:

```lean
|df y| ≤ ε / 2 + C * |y - x|
```

for all `y ∈ [0,1]`.  Near an endpoint, this is from `hsmall`; away from both endpoints, `|y-x| ≥ ηs/2`, and the global bound `|df y| ≤ M` is absorbed by `C * |y-x|`.

Then:

```lean
|∫ df y * K̃(t,x,y)|
  ≤ ∫ |df y| * |K̃(t,x,y)|
  ≤ (ε/2) ∫ |K̃| + C ∫ |y-x| |K̃|
  ≤ ε/2 + C * (4*t/sqrt(4*pi*t))
  < ε.
```

## Lean skeleton

Add this immediately after `initialLegConjugateOscillationControl_of_continuousOn` or near the endpoint reducer declarations in:

```text
ShenWork/PDE/IntervalSemigroupC1ApproxIdentity.lean
```

No new imports should be needed.

```lean
import ShenWork.PDE.IntervalSemigroupC1ApproxIdentity

open MeasureTheory Filter Topology
open scoped Topology

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel

namespace ShenWork.IntervalSemigroupC1ApproxIdentity

noncomputable section

/-- Bounded profiles that are small near the endpoints have vanishing
conjugate-kernel operator on endpoint x-layers. -/
theorem initialLegConjugateEndpointOperatorVanish_of_endpointSmall_bound
    {df : ℝ → ℝ} {M : ℝ}
    (hdf_cont : ContinuousOn df (Set.Icc (0 : ℝ) 1))
    (hM : 0 ≤ M)
    (hdf_bound : ∀ y ∈ Set.Icc (0 : ℝ) 1, |df y| ≤ M)
    (hsmall : InitialLegDerivativeEndpointSmall df) :
    InitialLegConjugateEndpointOperatorVanish df := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases hsmall (ε / 2) hε2 with ⟨ηs, hηs_pos, hηs_lt, hsη⟩

  -- endpoint operator layer, half the endpoint-smallness layer
  set η : ℝ := ηs / 2 with hη_def
  have hη_pos : 0 < η := by
    rw [hη_def]
    positivity
  have hη_lt : η < (1 / 2 : ℝ) := by
    rw [hη_def]
    linarith

  -- linear absorption coefficient; `+ 1` avoids a zero coefficient when `M = 0`.
  set C : ℝ := 2 * M / ηs + 1 with hC_def
  have hC_pos : 0 < C := by
    rw [hC_def]
    have hnonneg : 0 ≤ 2 * M / ηs := by
      exact div_nonneg (mul_nonneg (by norm_num) hM) hηs_pos.le
    linarith

  -- `M` is absorbed once `|y-x| ≥ ηs/2`.
  have hM_absorb_half : M ≤ C * (ηs / 2) := by
    have hbase : (2 * M / ηs) * (ηs / 2) = M := by
      field_simp [ne_of_gt hηs_pos]
      ring
    calc
      M = (2 * M / ηs) * (ηs / 2) := hbase.symm
      _ ≤ (2 * M / ηs + 1) * (ηs / 2) := by
        exact mul_le_mul_of_nonneg_right (by linarith : 2 * M / ηs ≤ 2 * M / ηs + 1)
          (by positivity)
      _ = C * (ηs / 2) := by
        rw [hC_def]

  -- Pointwise endpoint-layer modulus.  This is the main finite-dimensional step.
  have hpoint :
      ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≤ η ∨ 1 - η ≤ x →
        ∀ y ∈ Set.Icc (0 : ℝ) 1,
          |df y| ≤ ε / 2 + C * |y - x| := by
    intro x hx hxend y hy
    by_cases hynear : y ≤ ηs ∨ 1 - ηs ≤ y
    · have hy_small : |df y| < ε / 2 := hsη y hy hynear
      exact le_trans (le_of_lt hy_small)
        (le_add_of_nonneg_right (mul_nonneg hC_pos.le (abs_nonneg _)))
    · have hy_gt_left : ηs < y := by
        have hnot : ¬ y ≤ ηs := by
          intro hy_le
          exact hynear (Or.inl hy_le)
        exact lt_of_not_ge hnot
      have hy_lt_right : y < 1 - ηs := by
        have hnot : ¬ 1 - ηs ≤ y := by
          intro hy_ge
          exact hynear (Or.inr hy_ge)
        exact lt_of_not_ge hnot
      have hdist_half : ηs / 2 ≤ |y - x| := by
        rcases hxend with hxleft | hxright
        · have hxleft' : x ≤ ηs / 2 := by
            simpa [hη_def] using hxleft
          have hyx_nonneg : 0 ≤ y - x := by linarith
          rw [abs_of_nonneg hyx_nonneg]
          linarith
        · have hxright' : 1 - ηs / 2 ≤ x := by
            simpa [hη_def] using hxright
          have hyx_nonpos : y - x ≤ 0 := by linarith
          rw [abs_of_nonpos hyx_nonpos]
          linarith
      have hMdist : M ≤ C * |y - x| := by
        exact le_trans hM_absorb_half
          (mul_le_mul_of_nonneg_left hdist_half hC_pos.le)
      calc
        |df y| ≤ M := hdf_bound y hy
        _ ≤ C * |y - x| := hMdist
        _ ≤ ε / 2 + C * |y - x| := by linarith

  -- Time horizon for making the first-moment contribution `< ε/2`.
  set δ : ℝ := (ε / (4 * C)) ^ 2 with hδ_def
  have hδ_pos : 0 < δ := by
    rw [hδ_def]
    positivity

  refine ⟨η, hη_pos, hη_lt, δ, hδ_pos, ?_⟩
  intro t ht htδ x hx hxend

  let K : ℝ → ℝ := fun y => intervalNeumannConjugateKernel t x y
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hdf_u : ContinuousOn df (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le h01] using hdf_cont
  have hK_u : ContinuousOn K (Set.uIcc (0 : ℝ) 1) := by
    simpa [K, Set.uIcc_of_le h01] using continuousOn_conjugateKernel_snd ht x
  have hdist_u : ContinuousOn (fun y : ℝ => |y - x|) (Set.uIcc (0 : ℝ) 1) :=
    (continuous_abs.comp (continuous_id.sub continuous_const)).continuousOn
  have hcoef_u : ContinuousOn (fun y : ℝ => ε / 2 + C * |y - x|)
      (Set.uIcc (0 : ℝ) 1) :=
    continuousOn_const.add (continuousOn_const.mul hdist_u)

  -- Interval-integrability obligations for the triangle/mass/moment estimates.
  have hprod_ii : IntervalIntegrable
      (fun y : ℝ => df y * K y) MeasureTheory.volume 0 1 :=
    (hdf_u.mul hK_u).intervalIntegrable
  have hKabs_ii : IntervalIntegrable
      (fun y : ℝ => |K y|) MeasureTheory.volume 0 1 :=
    hK_u.abs.intervalIntegrable
  have hmoment_ii : IntervalIntegrable
      (fun y : ℝ => |y - x| * |K y|) MeasureTheory.volume 0 1 :=
    (hdist_u.mul hK_u.abs).intervalIntegrable
  have hmod_ii : IntervalIntegrable
      (fun y : ℝ => (ε / 2 + C * |y - x|) * |K y|)
      MeasureTheory.volume 0 1 :=
    (hcoef_u.mul hK_u.abs).intervalIntegrable

  have hsplit :
      (∫ y in (0 : ℝ)..1, (ε / 2 + C * |y - x|) * |K y|)
        = (ε / 2) * (∫ y in (0 : ℝ)..1, |K y|)
          + C * (∫ y in (0 : ℝ)..1, |y - x| * |K y|) := by
    rw [show (fun y : ℝ => (ε / 2 + C * |y - x|) * |K y|) =
        fun y : ℝ => (ε / 2) * |K y| + C * (|y - x| * |K y|) from by
      funext y
      ring]
    rw [intervalIntegral.integral_add (hKabs_ii.const_mul (ε / 2))
      (hmoment_ii.const_mul C), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]

  have htail_bound : C * (4 * t / Real.sqrt (4 * Real.pi * t)) < ε / 2 := by
    have h4pit_pos : 0 < 4 * Real.pi * t := by positivity
    have hpi_ge : 4 * t ≤ 4 * Real.pi * t := by nlinarith [Real.pi_gt_three]
    have hsqrt4t : Real.sqrt (4 * t) = 2 * Real.sqrt t := by
      have h4t_eq : (4 : ℝ) * t = (2 * Real.sqrt t) * (2 * Real.sqrt t) := by
        have := Real.mul_self_sqrt ht.le
        nlinarith
      rw [show (4 : ℝ) * t = (2 * Real.sqrt t) * (2 * Real.sqrt t) from h4t_eq,
        Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt t)]
    have hmoment_le : 4 * t / Real.sqrt (4 * Real.pi * t) ≤ 2 * Real.sqrt t := by
      rw [div_le_iff₀ (Real.sqrt_pos_of_pos h4pit_pos)]
      calc
        4 * t = 2 * Real.sqrt t * Real.sqrt (4 * t) := by
          rw [hsqrt4t]
          nlinarith [Real.mul_self_sqrt ht.le]
        _ ≤ 2 * Real.sqrt t * Real.sqrt (4 * Real.pi * t) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hpi_ge) (by positivity)
    have hsqrt_bound : Real.sqrt t < ε / (4 * C) := by
      rw [← Real.sqrt_sq (show (0 : ℝ) ≤ ε / (4 * C) by positivity)]
      rw [hδ_def] at htδ
      exact Real.sqrt_lt_sqrt ht.le htδ
    calc
      C * (4 * t / Real.sqrt (4 * Real.pi * t))
          ≤ C * (2 * Real.sqrt t) :=
        mul_le_mul_of_nonneg_left hmoment_le hC_pos.le
      _ < C * (2 * (ε / (4 * C))) :=
        mul_lt_mul_of_pos_left (by linarith) hC_pos
      _ = ε / 2 := by field_simp; ring

  calc
    |-(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y)|
        = |∫ y in (0 : ℝ)..1, df y * K y| := by
      simp [K]
    _ ≤ ∫ y in (0 : ℝ)..1, |df y * K y| :=
      intervalIntegral.abs_integral_le_integral_abs h01
    _ ≤ ∫ y in (0 : ℝ)..1, (ε / 2 + C * |y - x|) * |K y| := by
      apply intervalIntegral.integral_mono_on h01 hprod_ii.abs hmod_ii
      intro y hy
      have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le h01] using hy
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hpoint x hx hxend y hyIcc) (abs_nonneg _)
    _ = (ε / 2) * (∫ y in (0 : ℝ)..1, |K y|)
          + C * (∫ y in (0 : ℝ)..1, |y - x| * |K y|) := hsplit
    _ ≤ (ε / 2) * 1 + C * (4 * t / Real.sqrt (4 * Real.pi * t)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (by simpa [K] using conjugateKernel_L1_bound ht x)
          (by linarith))
        (mul_le_mul_of_nonneg_left
          (by simpa [K] using conjugateKernel_abs_moment_le ht hx) hC_pos.le)
    _ < ε := by
      linarith

end

end ShenWork.IntervalSemigroupC1ApproxIdentity
```

## Compile pitfalls and adjustments

### 1. The `simpa [hη_def] using hxright` line

If Lean does not simplify `1 - η ≤ x` to `1 - ηs / 2 ≤ x`, replace it with:

```lean
have hxright' : 1 - ηs / 2 ≤ x := by
  rw [hη_def] at hxright
  exact hxright
```

and similarly for the left case:

```lean
have hxleft' : x ≤ ηs / 2 := by
  rw [hη_def] at hxleft
  exact hxleft
```

### 2. `hC_def` orientation

With

```lean
set C : ℝ := 2 * M / ηs + 1 with hC_def
```

Lean usually gives `hC_def : C = 2 * M / ηs + 1`.  The proof above uses `rw [hC_def]`.  If your local version has the reverse orientation, use `rw [← hC_def]` in the few affected places.

### 3. Endpoint far-distance cases

Do not split far cases only as `ηs < y` for both endpoints.  For the right endpoint, the useful far fact is `y < 1 - ηs`.  The robust pattern is exactly:

```lean
by_cases hynear : y ≤ ηs ∨ 1 - ηs ≤ y
```

If `hynear` holds, use `hsmall`.  If not, derive both:

```lean
ηs < y
 y < 1 - ηs
```

Then use the left or right endpoint layer of `x` to prove `ηs / 2 ≤ |y - x|`.

### 4. No positivity of `-K̃`

The proof never needs `0 ≤ -intervalNeumannConjugateKernel`.  It uses:

```lean
intervalIntegral.abs_integral_le_integral_abs
conjugateKernel_L1_bound
conjugateKernel_abs_moment_le
```

so it is strictly before, and independent of, any full Dirichlet positivity development.

### 5. `hdf_cont` is still needed

Although the pointwise estimate uses only `hdf_bound` and `hsmall`, `hdf_cont` supplies `IntervalIntegrable (fun y => df y * K y)` in the current interval-integral style.  Keep it in the theorem statement.
