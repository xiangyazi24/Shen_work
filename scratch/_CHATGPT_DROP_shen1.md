# Q2861 (shen1) — tactic pattern for closed-window integrated energy inequality

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Source edit requested: none; answer file only.

Do not edit `ShenWork/PDE/P3MoserHighExcursionProducer.lean`.

## Goal pattern

You have a pointwise strict-time energy inequality from `LpBootstrapEnergyInequality`:

```lean
(1 / p) * deriv (fun τ => integratedMoserEnergy D u p τ) t
  + A * integratedMoserGradientEnergy D u p t
  + B * integratedMoserEnergy D u p t
≤ K * integratedMoserEnergy D u (p + rho) t + L
```

for `0 < t`, `t < T`, with `0 < p`, `0 < B`, etc.  On a closed window

```lean
t1 ∈ Set.Icc (0 : ℝ) T,
t2 ∈ Set.Icc t1 T
```

you want:

```lean
integratedMoserEnergy D u p t2 - integratedMoserEnergy D u p t1
  + (p * A) * ∫ s in t1..t2, integratedMoserGradientEnergy D u p s
≤ (p * K) * ∫ s in t1..t2, integratedMoserEnergy D u (p + rho) s
  + max 0 (p * L) * ∫ s in t1..t2,
      max 1 (integratedMoserEnergy D u p s)
```

or the same expression with the right side parenthesized to match your coefficient-frontier record.

The robust route is:

1. integrate the scaled pointwise inequality a.e. on the interval-integral domain `Set.Ioc t1 t2`;
2. expand integrals of sums and constant multiples;
3. rewrite `∫ deriv Y` using `IntegratedMoserEnergyWindowFTC.window_ftc`;
4. drop the nonnegative term `(p * B) * ∫Y`;
5. bound the constant term `(t2 - t1) * (p * L)` by `max 0 (p * L) * ∫max(1,Y)`.

## Mathlib / repo lemmas to use

Likely names to grep/check:

```lean
-- interval-integral representation / integrability
intervalIntegral.integral_of_le
intervalIntegrable_iff_integrableOn_Ioc_of_le
IntervalIntegrable.add
IntervalIntegrable.const_mul
intervalIntegrable_const

-- a.e. monotonicity / nonnegativity
MeasureTheory.integral_mono_ae
MeasureTheory.integral_nonneg_of_ae
MeasureTheory.ae_restrict_iff'
measurableSet_Ioc
measure_mono_null

-- interval integral algebra
intervalIntegral.integral_add
intervalIntegral.integral_const_mul
intervalIntegral.integral_const

-- repo helpers
IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
Icc_subset_uIcc_zero_T_of_endpoint_memberships
intervalIntegral_length_le_integral_max_one
IntegratedMoserEnergyWindowFTC.window_ftc
IntegratedMoserEnergyWindowFTC.deriv_intervalIntegrable
```

If your current helper is named `ae_restrict_Icc_strictInterior_of_Icc_endpoints`, prefer adding/using an `Ioc` version too, because `intervalIntegral.integral_of_le` rewrites `∫ in a..b` to integration over `Set.Ioc a b`.

## General helper 1: interval-integral monotonicity from a.e. inequality on `Ioc`

This is the main helper I would add near the a.e. endpoint bridge lemmas.

```lean
import ShenWork.PDE.P3MoserIntegratedClosure

open MeasureTheory
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Monotonicity of interval integrals from an a.e. inequality on the actual
interval-integral domain `Ioc a b`.  This is often more robust than trying to
use pointwise `intervalIntegral.integral_mono_on`, because the pointwise PDE
inequality only holds at strict interior times. -/
theorem intervalIntegral_integral_mono_ae_Ioc
    {a b : ℝ} {f g : ℝ → ℝ}
    (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hfg : ∀ᵐ s ∂(volume.restrict (Set.Ioc a b)), f s ≤ g s) :
    ∫ s in a..b, f s ≤ ∫ s in a..b, g s := by
  rw [intervalIntegral.integral_of_le hab]
  rw [intervalIntegral.integral_of_le hab]
  have hf_on : IntegrableOn f (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hf
  have hg_on : IntegrableOn g (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hg
  -- In this Mathlib version, one of these two usually works:
  exact MeasureTheory.integral_mono_ae hf_on hg_on hfg
  -- If the line above fails, replace it by one of:
  --   exact MeasureTheory.integral_mono_ae hf_on.integrable hg_on.integrable hfg
  -- or:
  --   change ∫ s, f s ∂(volume.restrict (Set.Ioc a b)) ≤
  --     ∫ s, g s ∂(volume.restrict (Set.Ioc a b))
  --   exact MeasureTheory.integral_mono_ae hf_on hg_on hfg

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

If `MeasureTheory.integral_mono_ae` expects `Integrable` rather than `IntegrableOn`, unfold/convert:

```lean
change Integrable f (volume.restrict (Set.Ioc a b)) at hf_on
change Integrable g (volume.restrict (Set.Ioc a b)) at hg_on
exact MeasureTheory.integral_mono_ae hf_on hg_on hfg
```

## General helper 2: interval-integral nonnegativity from a.e. nonnegativity on `Ioc`

This makes dropping `(p*B)*∫Y` clean when energy nonnegativity is only strict-interior.

```lean
/-- Nonnegativity of an interval integral from a.e. nonnegativity on the `Ioc`
interval-integral domain. -/
theorem intervalIntegral_integral_nonneg_ae_Ioc
    {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hf_nonneg : ∀ᵐ s ∂(volume.restrict (Set.Ioc a b)), 0 ≤ f s) :
    0 ≤ ∫ s in a..b, f s := by
  rw [intervalIntegral.integral_of_le hab]
  have hf_on : IntegrableOn f (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hf
  -- Try this first:
  exact MeasureTheory.integral_nonneg_of_ae hf_nonneg
  -- If Mathlib asks for integrability explicitly, use/check:
  --   exact MeasureTheory.integral_nonneg_of_ae hf_on hf_nonneg
  -- or `change` the measure to `volume.restrict (Set.Ioc a b)` as in the previous helper.
```

## General helper 3: strict-interior a.e. on the interval domain

If you only have the `Icc` version, add this `Ioc` version. It avoids measure-transfer clutter.

```lean
/-- On a closed time window `[a,b] ⊆ [0,T]`, the interval-integral domain
`Ioc a b` consists of strict interior times a.e.  The left endpoint is excluded
by `Ioc`; the only possible right-endpoint failure is the singleton `{T}`. -/
theorem ae_restrict_Ioc_strictInterior_of_Icc_endpoints
    {T a b : ℝ}
    (haT : a ∈ Set.Icc (0 : ℝ) T)
    (hbT : b ∈ Set.Icc a T) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioc a b)), 0 < s ∧ s < T := by
  refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
  refine (MeasureTheory.ae_iff).2 ?_
  have hbad_subset :
      {s : ℝ | s ∈ Set.Ioc a b ∧ ¬ (0 < s ∧ s < T)} ⊆ ({T} : Set ℝ) := by
    intro s hs
    rcases hs with ⟨hsIoc, hbad⟩
    have hs_pos : 0 < s := lt_of_le_of_lt haT.1 hsIoc.1
    have hs_le_T : s ≤ T := le_trans hsIoc.2 hbT.2
    push_neg at hbad
    rcases hbad with hs_nonpos | hT_le_s
    · exact False.elim ((not_le_of_gt hs_pos) hs_nonpos)
    · exact le_antisymm hs_le_T hT_le_s
  exact measure_mono_null hbad_subset (by simp)
```

## Main tactic skeleton

This skeleton is the pattern I would use inside the theorem proving the closed-window higher-power energy inequality from pointwise `LpBootstrapEnergyInequality`.

```lean
-- Assumed local context, schematically:
-- D u T rho p0 p t1 t2 A B K L : ℝ
-- hp : p0 ≤ p
-- hp_pos : 0 < p
-- hA : 0 < A, hB : 0 < B, hK : 0 < K
-- ht1 : t1 ∈ Set.Icc (0 : ℝ) T
-- ht2 : t2 ∈ Set.Icc t1 T
-- hpoint : ∀ t, 0 < t → t < T →
--   (1 / p) * deriv (fun τ => integratedMoserEnergy D u p τ) t
--     + A * integratedMoserGradientEnergy D u p t
--     + B * integratedMoserEnergy D u p t
--   ≤ K * integratedMoserEnergy D u (p + rho) t + L
-- hftc : IntegratedMoserEnergyWindowFTC D u T p0
-- hreg : IntegratedMoserFirstCrossingRegularity D u T p0
-- hnonneg : IntegratedMoserEnergyNonnegativity D u T p0
-- hrho_nonneg : 0 ≤ rho

have hab : t1 ≤ t2 := ht2.1
have hp_nonneg : 0 ≤ p := hp_pos.le
have hp_ne : p ≠ 0 := ne_of_gt hp_pos
have hp_rho : p0 ≤ p + rho := le_trans hp (le_add_of_nonneg_right hrho_nonneg)
have hsub : Set.Icc t1 t2 ⊆ Set.uIcc (0 : ℝ) T :=
  Icc_subset_uIcc_zero_T_of_endpoint_memberships ht1 ht2

let Y : ℝ → ℝ := fun s => integratedMoserEnergy D u p s
let Z : ℝ → ℝ := fun s => integratedMoserEnergy D u (p + rho) s
let G : ℝ → ℝ := fun s => integratedMoserGradientEnergy D u p s
let H : ℝ → ℝ := fun s => max (1 : ℝ) (Y s)
let dY : ℝ → ℝ := fun s => deriv (fun τ => integratedMoserEnergy D u p τ) s

have hdY_int : IntervalIntegrable dY volume t1 t2 := by
  simpa [dY] using hftc.deriv_intervalIntegrable p hp t1 ht1 t2 ht2
have hY_int : IntervalIntegrable Y volume t1 t2 := by
  simpa [Y] using hreg.power_intervalIntegrable_of_Icc hp hab hsub
have hZ_int : IntervalIntegrable Z volume t1 t2 := by
  simpa [Z] using hreg.power_intervalIntegrable_of_Icc hp_rho hab hsub
have hG_int : IntervalIntegrable G volume t1 t2 := by
  simpa [G] using hreg.gradient_intervalIntegrable_of_Icc hp hab hsub
have hH_int : IntervalIntegrable H volume t1 t2 := by
  simpa [Y, H] using hreg.maxOneEnergy_intervalIntegrable_of_Icc hp hab hsub

let F : ℝ → ℝ := fun s => dY s + (p * A) * G s + (p * B) * Y s
let R : ℝ → ℝ := fun s => (p * K) * Z s + p * L

have hF_int : IntervalIntegrable F volume t1 t2 := by
  dsimp [F]
  exact (hdY_int.add (hG_int.const_mul (p * A))).add
    (hY_int.const_mul (p * B))
have hR_int : IntervalIntegrable R volume t1 t2 := by
  dsimp [R]
  exact (hZ_int.const_mul (p * K)).add intervalIntegrable_const

have hstrict_ae := ae_restrict_Ioc_strictInterior_of_Icc_endpoints ht1 ht2

have hFR_ae : ∀ᵐ s ∂(volume.restrict (Set.Ioc t1 t2)), F s ≤ R s := by
  filter_upwards [hstrict_ae] with s hs
  rcases hs with ⟨hs0, hsT⟩
  have hpt := hpoint s hs0 hsT
  have hmul := mul_le_mul_of_nonneg_left hpt hp_nonneg
  -- Scale away `(1 / p)` robustly by rewriting both sides of `hmul`.
  have hleft_scale :
      p * ((1 / p) * dY s + A * G s + B * Y s) =
        dY s + (p * A) * G s + (p * B) * Y s := by
    field_simp [hp_ne]
    ring
  have hright_scale :
      p * (K * Z s + L) = (p * K) * Z s + p * L := by
    ring
  dsimp [F, R]
  calc
    dY s + (p * A) * G s + (p * B) * Y s
        = p * ((1 / p) * dY s + A * G s + B * Y s) := hleft_scale.symm
    _ ≤ p * (K * Z s + L) := hmul
    _ = (p * K) * Z s + p * L := hright_scale

have hmono : ∫ s in t1..t2, F s ≤ ∫ s in t1..t2, R s :=
  intervalIntegral_integral_mono_ae_Ioc hab hF_int hR_int hFR_ae
```

### Expand the integrals

```lean
have hF_eq :
    (∫ s in t1..t2, F s) =
      (∫ s in t1..t2, dY s) +
      (p * A) * (∫ s in t1..t2, G s) +
      (p * B) * (∫ s in t1..t2, Y s) := by
  dsimp [F]
  rw [intervalIntegral.integral_add
    (hdY_int.add (hG_int.const_mul (p * A)))
    (hY_int.const_mul (p * B))]
  rw [intervalIntegral.integral_add hdY_int (hG_int.const_mul (p * A))]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_const_mul]
  ring

have hR_eq :
    (∫ s in t1..t2, R s) =
      (p * K) * (∫ s in t1..t2, Z s) +
      (t2 - t1) * (p * L) := by
  dsimp [R]
  rw [intervalIntegral.integral_add (hZ_int.const_mul (p * K)) intervalIntegrable_const]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_const]
  ring

have hFTC :
    (∫ s in t1..t2, dY s) = Y t2 - Y t1 := by
  simpa [dY, Y] using hftc.window_ftc p hp t1 ht1 t2 ht2

have hmono_expanded :
    (Y t2 - Y t1) +
      (p * A) * (∫ s in t1..t2, G s) +
      (p * B) * (∫ s in t1..t2, Y s) ≤
    (p * K) * (∫ s in t1..t2, Z s) +
      (t2 - t1) * (p * L) := by
  rw [hF_eq, hR_eq] at hmono
  rwa [hFTC] at hmono
```

### Prove `∫Y ≥ 0` a.e. and drop the nonnegative term

```lean
have hY_nonneg_ae :
    ∀ᵐ s ∂(volume.restrict (Set.Ioc t1 t2)), 0 ≤ Y s := by
  filter_upwards [hstrict_ae] with s hs
  rcases hs with ⟨hs0, hsT⟩
  simpa [Y] using hnonneg p hp hp_nonneg s hs0 hsT

have hYint_nonneg : 0 ≤ ∫ s in t1..t2, Y s :=
  intervalIntegral_integral_nonneg_ae_Ioc hab hY_int hY_nonneg_ae

have hBYint_nonneg : 0 ≤ (p * B) * (∫ s in t1..t2, Y s) := by
  exact mul_nonneg (mul_nonneg hp_nonneg hB.le) hYint_nonneg

have hdropY :
    (Y t2 - Y t1) +
      (p * A) * (∫ s in t1..t2, G s) ≤
    (p * K) * (∫ s in t1..t2, Z s) +
      (t2 - t1) * (p * L) := by
  nlinarith [hmono_expanded, hBYint_nonneg]
```

If `nlinarith` struggles, rearrange with an explicit `have`:

```lean
have hadd :
    (Y t2 - Y t1) + (p * A) * (∫ s in t1..t2, G s) +
      (p * B) * (∫ s in t1..t2, Y s) =
    ((Y t2 - Y t1) + (p * A) * (∫ s in t1..t2, G s)) +
      (p * B) * (∫ s in t1..t2, Y s) := by ring
rw [hadd] at hmono_expanded
linarith
```

### Bound the constant by `max 0 (p*L) * ∫max(1,Y)`

```lean
have hlen_le_H :
    t2 - t1 ≤ ∫ s in t1..t2, H s := by
  simpa [H] using intervalIntegral_length_le_integral_max_one
    (Y := Y) hab hH_int

have hH_nonneg : 0 ≤ ∫ s in t1..t2, H s := by
  have hlen_nonneg : 0 ≤ t2 - t1 := sub_nonneg.mpr hab
  exact le_trans hlen_nonneg hlen_le_H

have hconst_bound :
    (t2 - t1) * (p * L) ≤
      max 0 (p * L) * (∫ s in t1..t2, H s) := by
  by_cases hpL_nonneg : 0 ≤ p * L
  · have hmax : max 0 (p * L) = p * L := max_eq_right hpL_nonneg
    have hmul := mul_le_mul_of_nonneg_right hlen_le_H hpL_nonneg
    -- `hmul` has `(t2-t1)*(p*L) ≤ H*(p*L)` or similar depending on orientation.
    simpa [hmax, mul_comm, mul_left_comm, mul_assoc] using hmul
  · have hpL_nonpos : p * L ≤ 0 := le_of_not_ge hpL_nonneg
    have hlen_nonneg : 0 ≤ t2 - t1 := sub_nonneg.mpr hab
    have hleft_nonpos : (t2 - t1) * (p * L) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos hlen_nonneg hpL_nonpos
    have hright_nonneg : 0 ≤ max 0 (p * L) * (∫ s in t1..t2, H s) := by
      exact mul_nonneg (le_max_left _ _) hH_nonneg
    exact le_trans hleft_nonpos hright_nonneg
```

If the first branch orientation does not match, switch to:

```lean
have hmul := mul_le_mul_of_nonneg_left hlen_le_H hpL_nonneg
```

and `simpa [hmax, mul_comm, mul_left_comm, mul_assoc] using hmul`.

### Final assembly

```lean
calc
  (Y t2 - Y t1) +
      (p * A) * (∫ s in t1..t2, G s)
      ≤ (p * K) * (∫ s in t1..t2, Z s) +
          (t2 - t1) * (p * L) := hdropY
  _ ≤ (p * K) * (∫ s in t1..t2, Z s) +
        max 0 (p * L) * (∫ s in t1..t2, H s) := by
      linarith [hconst_bound]
```

Then unfold `Y`, `G`, `Z`, `H` or `simpa [Y, G, Z, H]` to match the target statement.

## Common failure modes and fixes

### 1. `field_simp` does not rewrite the scaled pointwise inequality

Use a `calc` with explicit local variables, not `ring_nf at hmul` globally:

```lean
let d := dY s
let y := Y s
let g := G s
let z := Z s
have hpt' : (1 / p) * d + A * g + B * y ≤ K * z + L := by
  simpa [d, y, g, z, dY, Y, G, Z] using hpoint s hs0 hsT
have hmul := mul_le_mul_of_nonneg_left hpt' hp_nonneg
have hscale_left : p * ((1 / p) * d + A * g + B * y) =
    d + (p * A) * g + (p * B) * y := by
  field_simp [hp_ne]
  ring
have hscale_right : p * (K * z + L) = (p * K) * z + p * L := by ring
calc
  d + (p * A) * g + (p * B) * y
      = p * ((1 / p) * d + A * g + B * y) := hscale_left.symm
  _ ≤ p * (K * z + L) := hmul
  _ = (p * K) * z + p * L := hscale_right
```

### 2. `MeasureTheory.integral_mono_ae` type mismatch

After rewriting with `intervalIntegral.integral_of_le`, the goal is over the restricted measure. Use `change`:

```lean
change ∫ s, f s ∂(volume.restrict (Set.Ioc a b)) ≤
  ∫ s, g s ∂(volume.restrict (Set.Ioc a b))
```

Then convert integrability:

```lean
have hf_on : Integrable f (volume.restrict (Set.Ioc a b)) := by
  simpa [IntegrableOn] using
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hf
```

### 3. The strict-interior a.e. helper is over `Icc`, not `Ioc`

Prefer an `Ioc` helper. If you must use an `Icc` helper, prove the `Ioc` version separately rather than transferring measures; it is only a few lines and avoids absolute-continuity API friction.

### 4. Endpoint nonnegativity of `Y`

Do not require endpoint nonnegativity unless you already have it. For interval integrals, a.e. nonnegativity on `Ioc` is enough. Use `hstrict_ae` plus `IntegratedMoserEnergyNonnegativity`, which is strict-interior.

## Bottom line

Add two general helpers:

```lean
intervalIntegral_integral_mono_ae_Ioc
intervalIntegral_integral_nonneg_ae_Ioc
```

Then use the tactic pattern:

1. define `Y`, `G`, `Z`, `H`, `dY`, `F`, `R`;
2. prove interval-integrability of `F` and `R` from `hftc` and `hreg`;
3. build `hFR_ae` by `filter_upwards [ae_restrict_Ioc_strictInterior_of_Icc_endpoints ht1 ht2]`;
4. scale the pointwise inequality with `mul_le_mul_of_nonneg_left`, using a local `calc` to eliminate `(1/p)`;
5. apply `intervalIntegral_integral_mono_ae_Ioc`;
6. expand integrals with `intervalIntegral.integral_add` and `intervalIntegral.integral_const_mul`;
7. rewrite `∫ dY` by `hftc.window_ftc`;
8. prove `0 ≤ ∫Y` a.e. and drop `(p*B)*∫Y`;
9. bound the constant using `intervalIntegral_length_le_integral_max_one` and `max 0 (p*L)`.
