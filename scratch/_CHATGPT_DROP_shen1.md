# Q2864 (shen1) — per-window pointwise-to-integrated energy skeleton

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Source edit requested: none; answer file only.

## Target

You want a compiling per-window theorem that takes a pointwise strict-time witness

```lean
(1 / p) * derivY t + A * G t + B * Y t ≤ K * Z t + L_const
```

and proves the raw closed-window inequality used by `IntegratedHigherPowerEnergyWindowCoeffFrontier`, with constants

```lean
A_window = p * A
K_window = p * K
C0 = 0
L_window = max 0 (p * L_const)
```

The key is to use your existing helper exactly as:

```lean
intervalIntegral.integral_mono_ae_restrict hab hF_int hR_int hFR_ae
```

and to keep the endpoint/strict-time issue inside `hFR_ae` via:

```lean
ae_restrict_Icc_strictInterior_of_Icc_endpoints ht1 ht2
```

## Suggested theorem statement

Put this in `ShenWork/PDE/P3MoserIntegratedClosure.lean`, near the window-energy frontier code.

```lean
import ShenWork.PDE.P3MoserIntegratedClosure

open MeasureTheory
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Per-window integration of a strict-time pointwise Lp-bootstrap energy
inequality.  This is the local algebraic step used to build
`IntegratedHigherPowerEnergyWindowCoeffFrontier`.

The endpoint issue is handled by `ae_restrict_Icc_strictInterior_of_Icc_endpoints`
and `intervalIntegral.integral_mono_ae_restrict`; the nonnegative `B∫Y` term is
kept as an input `hYint_nonneg` and then dropped. -/
theorem integratedHigherPowerEnergyWindowCoeff_of_pointwise_witness
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p t1 t2 A B K L_const : ℝ}
    (hp_pos : 0 < p)
    (hB_nonneg : 0 ≤ B)
    (ht1 : t1 ∈ Set.Icc (0 : ℝ) T)
    (ht2 : t2 ∈ Set.Icc t1 T)
    (hdY_int :
      IntervalIntegrable
        (fun s => deriv (fun τ => integratedMoserEnergy D u p τ) s)
        volume t1 t2)
    (hY_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u p s)
        volume t1 t2)
    (hG_int :
      IntervalIntegrable
        (fun s => integratedMoserGradientEnergy D u p s)
        volume t1 t2)
    (hZ_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u (p + rho) s)
        volume t1 t2)
    (hH_int :
      IntervalIntegrable
        (fun s => max (1 : ℝ) (integratedMoserEnergy D u p s))
        volume t1 t2)
    (hYint_nonneg :
      0 ≤ ∫ s in t1..t2, integratedMoserEnergy D u p s)
    (hftc :
      (∫ s in t1..t2,
        deriv (fun τ => integratedMoserEnergy D u p τ) s) =
        integratedMoserEnergy D u p t2 -
          integratedMoserEnergy D u p t1)
    (hpoint :
      ∀ t, 0 < t → t < T →
        (1 / p) * deriv (fun τ => integratedMoserEnergy D u p τ) t +
            A * integratedMoserGradientEnergy D u p t +
            B * integratedMoserEnergy D u p t ≤
          K * integratedMoserEnergy D u (p + rho) t + L_const) :
    integratedMoserEnergy D u p t2 -
        integratedMoserEnergy D u p t1 +
      (p * A) * (∫ s in t1..t2,
        integratedMoserGradientEnergy D u p s) ≤
      (0 * p * (∫ s in t1..t2,
          max (1 : ℝ) (integratedMoserEnergy D u p s)) +
        (p * K) * (∫ s in t1..t2,
          integratedMoserEnergy D u (p + rho) s)) +
        max 0 (p * L_const) * (∫ s in t1..t2,
          max (1 : ℝ) (integratedMoserEnergy D u p s)) := by
  classical
  have hab : t1 ≤ t2 := ht2.1
  have hp_nonneg : 0 ≤ p := hp_pos.le
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos

  let Y : ℝ → ℝ := fun s => integratedMoserEnergy D u p s
  let G : ℝ → ℝ := fun s => integratedMoserGradientEnergy D u p s
  let Z : ℝ → ℝ := fun s => integratedMoserEnergy D u (p + rho) s
  let H : ℝ → ℝ := fun s => max (1 : ℝ) (Y s)
  let dY : ℝ → ℝ := fun s => deriv (fun τ => integratedMoserEnergy D u p τ) s

  have hdY_int' : IntervalIntegrable dY volume t1 t2 := by
    simpa [dY] using hdY_int
  have hY_int' : IntervalIntegrable Y volume t1 t2 := by
    simpa [Y] using hY_int
  have hG_int' : IntervalIntegrable G volume t1 t2 := by
    simpa [G] using hG_int
  have hZ_int' : IntervalIntegrable Z volume t1 t2 := by
    simpa [Z] using hZ_int
  have hH_int' : IntervalIntegrable H volume t1 t2 := by
    simpa [H, Y] using hH_int

  let F : ℝ → ℝ := fun s => dY s + (p * A) * G s + (p * B) * Y s
  let R : ℝ → ℝ := fun s => (p * K) * Z s + p * L_const

  have hF_int : IntervalIntegrable F volume t1 t2 := by
    dsimp [F]
    exact (hdY_int'.add (hG_int'.const_mul (p * A))).add
      (hY_int'.const_mul (p * B))

  have hR_int : IntervalIntegrable R volume t1 t2 := by
    dsimp [R]
    exact (hZ_int'.const_mul (p * K)).add intervalIntegrable_const

  have hstrict_ae := ae_restrict_Icc_strictInterior_of_Icc_endpoints ht1 ht2

  have hFR_ae :
      ∀ᵐ s ∂(volume.restrict (Set.Icc t1 t2)), F s ≤ R s := by
    filter_upwards [hstrict_ae] with s hs
    rcases hs with ⟨hs0, hsT⟩
    have hpt := hpoint s hs0 hsT
    have hmul := mul_le_mul_of_nonneg_left hpt hp_nonneg
    have hleft_scale :
        p * ((1 / p) * dY s + A * G s + B * Y s) =
          dY s + (p * A) * G s + (p * B) * Y s := by
      field_simp [hp_ne]
      ring
    have hright_scale :
        p * (K * Z s + L_const) = (p * K) * Z s + p * L_const := by
      ring
    dsimp [F, R, dY, Y, G, Z] at hleft_scale hright_scale ⊢
    calc
      deriv (fun τ => integratedMoserEnergy D u p τ) s +
          (p * A) * integratedMoserGradientEnergy D u p s +
          (p * B) * integratedMoserEnergy D u p s
          = p *
            ((1 / p) * deriv (fun τ => integratedMoserEnergy D u p τ) s +
              A * integratedMoserGradientEnergy D u p s +
              B * integratedMoserEnergy D u p s) := hleft_scale.symm
      _ ≤ p *
            (K * integratedMoserEnergy D u (p + rho) s + L_const) := hmul
      _ = (p * K) * integratedMoserEnergy D u (p + rho) s +
            p * L_const := hright_scale

  have hmono :
      ∫ s in t1..t2, F s ≤ ∫ s in t1..t2, R s :=
    intervalIntegral.integral_mono_ae_restrict hab hF_int hR_int hFR_ae

  have hF_eq :
      (∫ s in t1..t2, F s) =
        (∫ s in t1..t2, dY s) +
          (p * A) * (∫ s in t1..t2, G s) +
          (p * B) * (∫ s in t1..t2, Y s) := by
    dsimp [F]
    rw [intervalIntegral.integral_add
      (hdY_int'.add (hG_int'.const_mul (p * A)))
      (hY_int'.const_mul (p * B))]
    rw [intervalIntegral.integral_add hdY_int' (hG_int'.const_mul (p * A))]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_const_mul]
    ring

  have hR_eq :
      (∫ s in t1..t2, R s) =
        (p * K) * (∫ s in t1..t2, Z s) +
          (t2 - t1) * (p * L_const) := by
    dsimp [R]
    rw [intervalIntegral.integral_add
      (hZ_int'.const_mul (p * K)) intervalIntegrable_const]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_const]
    ring

  have hftc' : (∫ s in t1..t2, dY s) = Y t2 - Y t1 := by
    simpa [dY, Y] using hftc

  have hmono_expanded :
      (Y t2 - Y t1) +
          (p * A) * (∫ s in t1..t2, G s) +
          (p * B) * (∫ s in t1..t2, Y s) ≤
        (p * K) * (∫ s in t1..t2, Z s) +
          (t2 - t1) * (p * L_const) := by
    have hmono' := hmono
    rw [hF_eq, hR_eq] at hmono'
    rw [hftc'] at hmono'
    exact hmono'

  have hBYint_nonneg :
      0 ≤ (p * B) * (∫ s in t1..t2, Y s) := by
    exact mul_nonneg (mul_nonneg hp_nonneg hB_nonneg)
      (by simpa [Y] using hYint_nonneg)

  have hdropY :
      (Y t2 - Y t1) +
          (p * A) * (∫ s in t1..t2, G s) ≤
        (p * K) * (∫ s in t1..t2, Z s) +
          (t2 - t1) * (p * L_const) := by
    nlinarith [hmono_expanded, hBYint_nonneg]

  have hlen_le_H :
      t2 - t1 ≤ ∫ s in t1..t2, H s := by
    simpa [H, Y] using
      intervalIntegral_length_le_integral_max_one
        (Y := fun s => integratedMoserEnergy D u p s) hab hH_int

  have hH_nonneg : 0 ≤ ∫ s in t1..t2, H s := by
    have hlen_nonneg : 0 ≤ t2 - t1 := sub_nonneg.mpr hab
    exact le_trans hlen_nonneg hlen_le_H

  have hconst_bound :
      (t2 - t1) * (p * L_const) ≤
        max 0 (p * L_const) * (∫ s in t1..t2, H s) := by
    by_cases hPL_nonneg : 0 ≤ p * L_const
    · have hmax : max 0 (p * L_const) = p * L_const :=
        max_eq_right hPL_nonneg
      have hmul := mul_le_mul_of_nonneg_right hlen_le_H hPL_nonneg
      simpa [hmax, mul_comm, mul_left_comm, mul_assoc] using hmul
    · have hPL_nonpos : p * L_const ≤ 0 := le_of_not_ge hPL_nonneg
      have hlen_nonneg : 0 ≤ t2 - t1 := sub_nonneg.mpr hab
      have hleft_nonpos : (t2 - t1) * (p * L_const) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos hlen_nonneg hPL_nonpos
      have hright_nonneg :
          0 ≤ max 0 (p * L_const) * (∫ s in t1..t2, H s) := by
        exact mul_nonneg (le_max_left _ _) hH_nonneg
      exact le_trans hleft_nonpos hright_nonneg

  have hfinal :
      (Y t2 - Y t1) +
          (p * A) * (∫ s in t1..t2, G s) ≤
        (p * K) * (∫ s in t1..t2, Z s) +
          max 0 (p * L_const) * (∫ s in t1..t2, H s) := by
    linarith [hdropY, hconst_bound]

  simpa [Y, G, Z, H, add_assoc, add_comm, add_left_comm] using hfinal

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

## If the final `simpa` misses the target shape

The target has an extra `0 * p * ∫H` term. If `simpa` does not remove it automatically, replace the final line by:

```lean
  have htarget :
      (Y t2 - Y t1) +
          (p * A) * (∫ s in t1..t2, G s) ≤
        (0 * p * (∫ s in t1..t2, H s) +
          (p * K) * (∫ s in t1..t2, Z s)) +
          max 0 (p * L_const) * (∫ s in t1..t2, H s) := by
    nlinarith [hfinal]
  simpa [Y, G, Z, H, add_assoc, add_comm, add_left_comm] using htarget
```

## If `field_simp` in `hleft_scale` is brittle

Replace the `hleft_scale` proof with a local scalar version:

```lean
    have hleft_scale :
        p * ((1 / p) * dY s + A * G s + B * Y s) =
          dY s + (p * A) * G s + (p * B) * Y s := by
      calc
        p * ((1 / p) * dY s + A * G s + B * Y s)
            = p * ((1 / p) * dY s) + p * (A * G s) + p * (B * Y s) := by ring
        _ = dY s + (p * A) * G s + (p * B) * Y s := by
            field_simp [hp_ne]
            ring
```

This usually gives `field_simp` a simpler denominator context.

## Notes on constants for the frontier witness

When assembling `IntegratedHigherPowerEnergyWindowCoeffFrontier`, use this per-window theorem with witnesses:

```lean
Awin := p * A
Kwin := p * K
C0 := 0
Lwin := max 0 (p * L_const)
```

You will need:

```lean
0 ≤ Kwin := mul_nonneg hp_pos.le hK.le
0 ≤ (0 : ℝ) := le_rfl
0 ≤ Lwin := le_max_left _ _
```

The surplus side in the frontier is then:

```lean
Kwin * eps ≤ Awin - theta
```

that is:

```lean
(p * K) * eps ≤ p * A - theta
```

Do not try to reuse an unscaled `K * eps ≤ A - theta` after multiplying the pointwise inequality by `p`; the constants have changed.

## Checklist of likely compile-sensitive names

If any line fails, check these exact names:

```lean
#check intervalIntegral.integral_mono_ae_restrict
#check ae_restrict_Icc_strictInterior_of_Icc_endpoints
#check intervalIntegral_length_le_integral_max_one
#check intervalIntegral.integral_add
#check intervalIntegral.integral_const_mul
#check intervalIntegral.integral_const
#check IntervalIntegrable.add
#check IntervalIntegrable.const_mul
```

If `intervalIntegral.integral_mono_ae_restrict` expects `Ioc` instead of `Icc`, change only these two lines:

```lean
have hstrict_ae := ae_restrict_Ioc_strictInterior_of_Icc_endpoints ht1 ht2
...
∀ᵐ s ∂(volume.restrict (Set.Ioc t1 t2)), F s ≤ R s
```

Everything else is unchanged.
