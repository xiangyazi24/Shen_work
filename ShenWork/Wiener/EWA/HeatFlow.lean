import ShenWork.Wiener.EWA.Basic

/-!
# The time-parameterized heat flow as an `EWA T r` element (brick `heatEWA`)

This brick realizes the Neumann heat flow `S(t)u₀` — whose `n`-th Fourier
coefficient is `exp(−t·(nπ)²)·(u₀)_n` — as a single element of the time-lifted
weighted Wiener algebra `EWA T r := GWA (CT T) r`, where `CT T := C(Icc 0 T, ℂ)`.
It is the **base term** of the Phase-C EWA Picard map (the eval-bridge/contraction
later builds on it).  This is a *pure construction*: we define the element and
prove its norm bound, nothing about the semigroup property, the heat kernel, or
the eval bridge.

For a static input `u₀E : WA r` (the committed concrete `ℂ`-Wiener algebra), the
heat-flow coefficient is the **time-dependent** scalar `exp(−t(nπ)²)` (a function
of `t∈[0,T]`, in contrast to the fixed-`τ` multiplier `GWA.gHeat`).  Each mode
becomes a `CT T` element:

* `heatModeCT n c : CT T` — the continuous map `t ↦ exp(−t(nπ)²)·c` on `[0,T]`,
  built `⟨fun x => …, continuity⟩` in the `Duhamel.lean` `duhCM` idiom; its
  sup-norm is `≤ ‖c‖` because `0 ≤ t` on the window ⟹ `exp(−t(nπ)²) ≤ 1`.
* `heatEWA u₀E : EWA T r` — the `GWA (CT T) r` element with
  `toFun n = heatModeCT n (u₀E.toFun n)`; membership `GMemW r` is dominated
  termwise by `gWeight r n · ‖u₀E.toFun n‖`, summable since `u₀E ∈ MemW r`.
* `heatEWA_norm_le : ‖heatEWA u₀E‖ ≤ ‖u₀E‖` — the per-mode sup `≤ |coeff|`,
  summed.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener

namespace ShenWork.EWA

section HeatMode

variable {T : ℝ}

/-- The per-mode heat-flow time-coefficient `t ↦ exp(−t·(nπ)²)·c` as an underlying
function `ℝ → ℂ`. -/
noncomputable def heatModeFun (n : ℤ) (c : ℂ) (t : ℝ) : ℂ :=
  (Real.exp (-(t) * ((n : ℝ) * Real.pi) ^ 2) : ℂ) * c

theorem heatModeFun_continuous (n : ℤ) (c : ℂ) : Continuous (heatModeFun n c) := by
  unfold heatModeFun; fun_prop

/-- **The per-mode `CT T` heat coefficient** `heatModeCT n c : CT T`, the continuous
map `t ↦ exp(−t·(nπ)²)·c` on `[0,T]` (restricting the `ℝ`-continuous `heatModeFun`
to the compact window via `continuous_subtype_val`, the `duhCM` idiom). -/
noncomputable def heatModeCT (n : ℤ) (c : ℂ) : CT T :=
  ⟨fun x => heatModeFun n c x,
    (heatModeFun_continuous n c).comp continuous_subtype_val⟩

@[simp] theorem heatModeCT_apply (n : ℤ) (c : ℂ) (x : Set.Icc (0 : ℝ) T) :
    (heatModeCT (T := T) n c) x = heatModeFun n c x := rfl

/-- **The per-mode sup bound** `‖heatModeCT n c‖ ≤ ‖c‖`.  On the window `0 ≤ t`,
the heat factor `exp(−t(nπ)²) ≤ 1`, so `|exp(−t(nπ)²)·c| ≤ ‖c‖` pointwise. -/
theorem heatModeCT_norm_le (n : ℤ) (c : ℂ) :
    ‖heatModeCT (T := T) n c‖ ≤ ‖c‖ := by
  rw [ContinuousMap.norm_le _ (norm_nonneg c)]
  intro x
  change ‖heatModeFun n c x‖ ≤ ‖c‖
  unfold heatModeFun
  have ht0 : (0 : ℝ) ≤ (x : ℝ) := x.2.1
  have hsq : (0 : ℝ) ≤ ((n : ℝ) * Real.pi) ^ 2 := sq_nonneg _
  have hfac : ‖(Real.exp (-((x : ℝ)) * ((n : ℝ) * Real.pi) ^ 2) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), Real.exp_le_one_iff]
    nlinarith [ht0, hsq]
  calc ‖(Real.exp (-((x : ℝ)) * ((n : ℝ) * Real.pi) ^ 2) : ℂ) * c‖
      = ‖(Real.exp (-((x : ℝ)) * ((n : ℝ) * Real.pi) ^ 2) : ℂ)‖ * ‖c‖ := norm_mul _ _
    _ ≤ 1 * ‖c‖ := mul_le_mul_of_nonneg_right hfac (norm_nonneg c)
    _ = ‖c‖ := one_mul _

end HeatMode

section HeatEWA

variable {T : ℝ} {r : ℕ}

/-- **Heat-flow membership.** The mode sequence `n ↦ heatModeCT n (u₀E.toFun n)`
is in `GMemW r`: each weighted sup `gWeight r n · ‖heatModeCT n (u₀E.toFun n)‖` is
dominated by `gWeight r n · ‖u₀E.toFun n‖` (via `heatModeCT_norm_le`), summable
since `u₀E ∈ MemW r`. -/
theorem heatEWA_mem (u₀E : WA r) :
    GMemW (K := CT T) r (fun n => heatModeCT n (u₀E.toFun n)) := by
  -- `∑ gWeight r n · ‖u₀E.toFun n‖` is summable: this is `MemW r u₀E.toFun`.
  have hdom : Summable (fun n => GWA.gWeight r n * ‖u₀E.toFun n‖) :=
    u₀E.mem.congr (fun n => by rw [← gWeight_eq_wWeight])
  refine Summable.of_nonneg_of_le
    (fun n => GWA.gWeightedNorm_nonneg r (fun n => heatModeCT n (u₀E.toFun n)) n) ?_ hdom
  intro n
  have hle : ‖heatModeCT (T := T) n (u₀E.toFun n)‖ ≤ ‖u₀E.toFun n‖ :=
    heatModeCT_norm_le n (u₀E.toFun n)
  exact mul_le_mul_of_nonneg_left hle (GWA.gWeight_nonneg r n)

/-- **The heat flow as an `EWA T r` element.**  `heatEWA u₀E : EWA T r` has
`n`-th time-coefficient `t ↦ exp(−t(nπ)²)·(u₀E)_n`. -/
noncomputable def heatEWA (u₀E : WA r) : EWA T r :=
  ⟨fun n => heatModeCT n (u₀E.toFun n), heatEWA_mem u₀E⟩

@[simp] theorem heatEWA_toFun (u₀E : WA r) (n : ℤ) :
    (heatEWA (T := T) u₀E).toFun n = heatModeCT n (u₀E.toFun n) := rfl

/-- **The heat-flow norm bound** `‖heatEWA u₀E‖ ≤ ‖u₀E‖`.  Termwise the weighted
sup `gWeight r n · ‖heatModeCT n (u₀E)_n‖ ≤ gWeight r n · ‖(u₀E)_n‖`, summed over
all `n` (both sides summable). -/
theorem heatEWA_norm_le (u₀E : WA r) :
    ‖heatEWA (T := T) u₀E‖ ≤ ‖u₀E‖ := by
  change GWA.gNorm r (heatEWA (T := T) u₀E).toFun ≤ wNorm r u₀E.toFun
  rw [GWA.gNorm, wNorm]
  have hu : Summable (fun n => wWeight r n * ‖u₀E.toFun n‖) := u₀E.mem
  refine Summable.tsum_le_tsum (fun n => ?_) (heatEWA_mem u₀E) ?_
  · have hle : ‖heatModeCT (T := T) n (u₀E.toFun n)‖ ≤ ‖u₀E.toFun n‖ :=
      heatModeCT_norm_le n (u₀E.toFun n)
    have hw : (0 : ℝ) ≤ GWA.gWeight r n := GWA.gWeight_nonneg r n
    calc GWA.gWeight r n * ‖(heatEWA (T := T) u₀E).toFun n‖
        = GWA.gWeight r n * ‖heatModeCT (T := T) n (u₀E.toFun n)‖ := by rw [heatEWA_toFun]
      _ ≤ GWA.gWeight r n * ‖u₀E.toFun n‖ := mul_le_mul_of_nonneg_left hle hw
      _ = wWeight r n * ‖u₀E.toFun n‖ := by rw [gWeight_eq_wWeight]
  · exact hu.congr (fun n => by rw [← gWeight_eq_wWeight])

end HeatEWA

end ShenWork.EWA

#print axioms ShenWork.EWA.heatEWA_norm_le
