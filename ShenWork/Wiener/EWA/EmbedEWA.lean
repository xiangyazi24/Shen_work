import Mathlib
import ShenWork.Wiener.EWA.CoeffBridge
import ShenWork.Wiener.EWA.EvenRealClosure
import ShenWork.Wiener.WeightedL1CosineAdapter
import ShenWork.PDE.IntervalNeumannFullKernel
import ShenWork.PDE.IntervalDomain
import ShenWork.PDE.CosineSpectrum

/-!
# EWA brick Q2 — the EMBED construction (real solution `u` ↦ even-real `EWA T 1`)

This is the bridge from the committed Neumann solution to the EWA layer.  Given a
real solution `u : ℝ → intervalDomainPoint → ℝ`, its slice at time `t` lifts to
`intervalDomainLift (u t) : ℝ → ℝ`, whose Neumann cosine coefficients are
`cosineCoeffs (intervalDomainLift (u t)) k`.  We **build** the even ℤ-bilateral
embedding of that coefficient family, as a single element of the time-lifted
weighted Wiener algebra `EWA T 1 := GWA (CT T) 1` whose `n`-th time-coefficient is
the `CT T` map `t ↦ ofCosineCoeffs (cosineCoeffs (lift (u t))) n`.

The construction MIRRORS `heatEWA` (`HeatFlow.lean`): a per-mode continuous-in-`t`
coefficient + a `GMemW 1` membership proof dominated by an A¹ envelope.

## Analytic input taken as HYPOTHESES (the documented Wiener reduction)
* `hcont n` — each per-mode coefficient is continuous in `t` (regularity of `u`);
* an A¹ envelope `Bv : ℕ → ℝ` with `hBv : ∀ t k, |cosineCoeffs (lift (u t)) k| ≤ Bv k`
  and `hBvsum : Summable (fun k => (1 + (k:ℝ)) * Bv k)` (the `A¹`/weighted-ℓ¹
  regularity, uniform in `t`);
* `hcos_series` — the committed Neumann fact that `lift (u t)` IS its cosine series
  on `[0,1]`.

## What is built
1. `embedEWA u … : EWA T 1` — the even-embedding element (membership from the A¹
   envelope, mirroring `heatEWA_mem`).
2. `embedEWA_evenReal : EvenRealEWA (embedEWA u …)` — even + real, direct from the
   `ofCosineCoeffs` parity facts (`ParityFoundations`).
3. `embedEWA_realizes` — the slice synthesis reproduces `lift (u τ.1)` on `[0,1]`,
   via `evalC_ofCosineCoeffs_all` + `hcos_series`.

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalNeumannFullKernel ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### 1. The per-mode `CT T` coefficient. -/

/-- The underlying `ℝ → ℂ` per-mode coefficient
`t ↦ ofCosineCoeffs (cosineCoeffs (intervalDomainLift (u t))) n`. -/
def embedModeFun (u : ℝ → intervalDomainPoint → ℝ) (n : ℤ) (t : ℝ) : ℂ :=
  ofCosineCoeffs (fun k => cosineCoeffs (intervalDomainLift (u t)) k) n

/-- The per-mode `CT T` coefficient (restricting the `ℝ`-continuous `embedModeFun`
to the compact window via `continuous_subtype_val`, the `heatModeCT`/`duhCM` idiom). -/
def embedModeCT (u : ℝ → intervalDomainPoint → ℝ) (n : ℤ)
    (hcont : Continuous (embedModeFun u n)) : CT T :=
  ⟨fun x => embedModeFun u n x, hcont.comp continuous_subtype_val⟩

@[simp] theorem embedModeCT_apply (u : ℝ → intervalDomainPoint → ℝ) (n : ℤ)
    (hcont : Continuous (embedModeFun u n)) (x : TimeDom T) :
    (embedModeCT (T := T) u n hcont) x = embedModeFun u n x := rfl

/-- The per-mode sup bound `‖embedModeCT u _ n‖ ≤ Bv n.natAbs`, from the A¹
envelope `|cosineCoeffs (lift (u t)) k| ≤ Bv k` (uniform in `t`).  At `n = 0` the
mode norm is `|c_t 0| ≤ Bv 0`; off `0` it is `|c_t |n||/2 ≤ Bv |n|`. -/
theorem embedModeCT_norm_le (u : ℝ → intervalDomainPoint → ℝ)
    {Bv : ℕ → ℝ} (hBv : ∀ t k, |cosineCoeffs (intervalDomainLift (u t)) k| ≤ Bv k)
    (hBvnn : ∀ k, 0 ≤ Bv k) (n : ℤ)
    (hcont : Continuous (embedModeFun u n)) :
    ‖embedModeCT (T := T) u n hcont‖ ≤ Bv n.natAbs := by
  rw [ContinuousMap.norm_le _ (hBvnn _)]
  intro x
  rw [embedModeCT_apply]
  change ‖embedModeFun u n (x : ℝ)‖ ≤ Bv n.natAbs
  unfold embedModeFun
  rw [norm_ofCosineCoeffs]
  by_cases h : n = 0
  · subst h; simpa using hBv (x : ℝ) 0
  · rw [if_neg h]
    have hle : |cosineCoeffs (intervalDomainLift (u (x : ℝ))) n.natAbs| ≤ Bv n.natAbs :=
      hBv (x : ℝ) n.natAbs
    have h2 : |cosineCoeffs (intervalDomainLift (u (x : ℝ))) n.natAbs| / 2
        ≤ |cosineCoeffs (intervalDomainLift (u (x : ℝ))) n.natAbs| := by
      have := abs_nonneg (cosineCoeffs (intervalDomainLift (u (x : ℝ))) n.natAbs)
      linarith
    linarith

/-! ### 2. The membership `GMemW 1` from the A¹ envelope. -/

/-- The weighted envelope summand `n ↦ gWeight 1 n · Bv n.natAbs` is summable: it is
the ℤ-split of `2·∑_{k≥1}(1+k)Bv k + Bv 0` (the `memW_ofCosineCoeffs` envelope). -/
theorem summable_gWeight_Bv {Bv : ℕ → ℝ}
    (hBvsum : Summable (fun k : ℕ => (1 + (k : ℝ)) * Bv k)) :
    Summable (fun n : ℤ => GWA.gWeight 1 n * Bv n.natAbs) := by
  -- the ℤ-summand at `±(m+1)` is `(1+(m+1))·Bv (m+1)`, at `0` is `Bv 0`.
  have hcs : Summable (fun m : ℕ => (1 + ((m : ℝ) + 1)) * Bv (m + 1)) := by
    have := (summable_nat_add_iff 1).2 hBvsum
    refine this.congr (fun m => ?_)
    push_cast; ring
  have hweight : ∀ n : ℤ, GWA.gWeight 1 n * Bv n.natAbs
      = (1 + |(n : ℝ)|) * Bv n.natAbs := by
    intro n; rw [GWA.gWeight]; ring_nf
  have hpos : Summable
      (fun m : ℕ => GWA.gWeight 1 ((m : ℤ) + 1) * Bv ((m : ℤ) + 1).natAbs) := by
    refine hcs.congr (fun m => ?_)
    rw [hweight]
    have hnat : ((m : ℤ) + 1).natAbs = m + 1 := by omega
    have hcast : |(((m : ℤ) + 1 : ℤ) : ℝ)| = 1 + (m : ℝ) := by
      push_cast; rw [abs_of_nonneg (by positivity)]; ring
    rw [hnat, hcast]; ring
  have hneg : Summable
      (fun m : ℕ => GWA.gWeight 1 (-((m : ℤ) + 1)) * Bv (-((m : ℤ) + 1)).natAbs) := by
    refine hcs.congr (fun m => ?_)
    rw [hweight]
    have hnat : (-((m : ℤ) + 1)).natAbs = m + 1 := by omega
    have hcast : |((-((m : ℤ) + 1) : ℤ) : ℝ)| = 1 + (m : ℝ) := by
      push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]; ring
    rw [hnat, hcast]; ring
  exact hpos.of_add_one_of_neg_add_one hneg

/-- **Embed membership.**  The mode sequence is in `GMemW 1`: each weighted sup
`gWeight 1 n · ‖embedModeCT n‖` is dominated by `gWeight 1 n · Bv n.natAbs` (via
`embedModeCT_norm_le`), summable by `summable_gWeight_Bv`. -/
theorem embedEWA_mem (u : ℝ → intervalDomainPoint → ℝ)
    {Bv : ℕ → ℝ} (hBv : ∀ t k, |cosineCoeffs (intervalDomainLift (u t)) k| ≤ Bv k)
    (hBvnn : ∀ k, 0 ≤ Bv k)
    (hBvsum : Summable (fun k : ℕ => (1 + (k : ℝ)) * Bv k))
    (hcont : ∀ n : ℤ, Continuous (embedModeFun u n)) :
    GMemW (K := CT T) 1 (fun n => embedModeCT u n (hcont n)) := by
  refine Summable.of_nonneg_of_le
    (fun n => GWA.gWeightedNorm_nonneg 1 (fun n => embedModeCT u n (hcont n)) n) ?_
    (summable_gWeight_Bv hBvsum)
  intro n
  exact mul_le_mul_of_nonneg_left
    (embedModeCT_norm_le u hBv hBvnn n (hcont n)) (GWA.gWeight_nonneg 1 n)

/-- **The embed construction** `embedEWA u … : EWA T 1`, with `n`-th
time-coefficient `t ↦ ofCosineCoeffs (cosineCoeffs (lift (u t))) n`. -/
def embedEWA (u : ℝ → intervalDomainPoint → ℝ)
    {Bv : ℕ → ℝ} (hBv : ∀ t k, |cosineCoeffs (intervalDomainLift (u t)) k| ≤ Bv k)
    (hBvnn : ∀ k, 0 ≤ Bv k)
    (hBvsum : Summable (fun k : ℕ => (1 + (k : ℝ)) * Bv k))
    (hcont : ∀ n : ℤ, Continuous (embedModeFun u n)) : EWA T 1 :=
  ⟨fun n => embedModeCT u n (hcont n), embedEWA_mem u hBv hBvnn hBvsum hcont⟩

@[simp] theorem embedEWA_toFun (u : ℝ → intervalDomainPoint → ℝ)
    {Bv : ℕ → ℝ} (hBv : ∀ t k, |cosineCoeffs (intervalDomainLift (u t)) k| ≤ Bv k)
    (hBvnn : ∀ k, 0 ≤ Bv k)
    (hBvsum : Summable (fun k : ℕ => (1 + (k : ℝ)) * Bv k))
    (hcont : ∀ n : ℤ, Continuous (embedModeFun u n)) (n : ℤ) :
    (embedEWA (T := T) u hBv hBvnn hBvsum hcont).toFun n
      = embedModeCT u n (hcont n) := rfl

/-- The slice of `embedEWA` at time `τ` is exactly the even embedding
`ofCosineCoeffs (cosineCoeffs (lift (u τ.1)))`. -/
theorem coeff_embedEWA_slice (u : ℝ → intervalDomainPoint → ℝ)
    {Bv : ℕ → ℝ} (hBv : ∀ t k, |cosineCoeffs (intervalDomainLift (u t)) k| ≤ Bv k)
    (hBvnn : ∀ k, 0 ≤ Bv k)
    (hBvsum : Summable (fun k : ℕ => (1 + (k : ℝ)) * Bv k))
    (hcont : ∀ n : ℤ, Continuous (embedModeFun u n)) (τ : TimeDom T) (n : ℤ) :
    (sliceWA τ (embedEWA u hBv hBvnn hBvsum hcont)).toFun n
      = ofCosineCoeffs (fun k => cosineCoeffs (intervalDomainLift (u τ.1)) k) n := by
  rw [coeff_sliceWA, embedEWA_toFun, embedModeCT_apply, embedModeFun]

/-! ### 3. Even + real (`EvenRealEWA`). -/

/-- **`embedEWA` is even-real.**  Each slice is `ofCosineCoeffs c` (an even, real
embedding): even from `ofCosineCoeffs_neg`, real from `ofCosineCoeffs_im`. -/
theorem embedEWA_evenReal (u : ℝ → intervalDomainPoint → ℝ)
    {Bv : ℕ → ℝ} (hBv : ∀ t k, |cosineCoeffs (intervalDomainLift (u t)) k| ≤ Bv k)
    (hBvnn : ∀ k, 0 ≤ Bv k)
    (hBvsum : Summable (fun k : ℕ => (1 + (k : ℝ)) * Bv k))
    (hcont : ∀ n : ℤ, Continuous (embedModeFun u n)) :
    EvenRealEWA (embedEWA (T := T) u hBv hBvnn hBvsum hcont) where
  even τ n := by
    rw [coeff_embedEWA_slice, coeff_embedEWA_slice]
    exact ofCosineCoeffs_neg _ n
  real τ n := by
    rw [coeff_embedEWA_slice]
    exact ofCosineCoeffs_im _ n

/-! ### 4. The realization (slice synthesis reproduces `lift (u τ.1)` on `[0,1]`). -/

/-- **`embedEWA` realizes `u`.**  Given the committed Neumann cosine-series property
of the solution slice (`hcos_series`: `lift (u t)` IS its cosine series on `[0,1]`),
the space-time synthesis of `embedEWA u …` reproduces `lift (u τ.1) x` for every
`τ` and `x ∈ [0,1]`.  Via `evalC_ofCosineCoeffs_all` (the full-circle synthesis of
the even embedding) composed with `hcos_series`. -/
theorem embedEWA_realizes (u : ℝ → intervalDomainPoint → ℝ)
    {Bv : ℕ → ℝ} (hBv : ∀ t k, |cosineCoeffs (intervalDomainLift (u t)) k| ≤ Bv k)
    (hBvnn : ∀ k, 0 ≤ Bv k)
    (hBvsum : Summable (fun k : ℕ => (1 + (k : ℝ)) * Bv k))
    (hcont : ∀ n : ℤ, Continuous (embedModeFun u n))
    (hsummable : ∀ t, Summable (fun k => |cosineCoeffs (intervalDomainLift (u t)) k|))
    (hcos_series : ∀ t x, x ∈ Set.Icc (0:ℝ) 1 →
      intervalDomainLift (u t) x
        = ∑' k : ℕ, cosineCoeffs (intervalDomainLift (u t)) k * cosineMode k x)
    (τ : TimeDom T) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    evalST τ (x : WA.Circ)
        (GWA.incl (by omega : (0:ℕ) ≤ 1) (embedEWA u hBv hBvnn hBvsum hcont))
      = (intervalDomainLift (u τ.1) x : ℂ) := by
  set c : ℕ → ℝ := fun k => cosineCoeffs (intervalDomainLift (u τ.1)) k with hc_def
  have hcsum : Summable (fun k : ℕ => |c k|) := hsummable τ.1
  -- the slice of the included element equals the even embedding `a'`.
  set a' : WA 0 := ⟨ofCosineCoeffs c, memW_ofCosineCoeffs (r := 0) (by simpa using hcsum)⟩
    with ha'
  have hslice : sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 1)
      (embedEWA u hBv hBvnn hBvsum hcont)) = a' := by
    apply WA.ext; funext n
    rw [ha', coeff_sliceWA, GWA.incl_toFun, embedEWA_toFun, embedModeCT_apply, embedModeFun]
  -- full-circle synthesis of the even embedding, then the committed cosine series.
  rw [evalST_apply, WA.evalAt_apply, ← WA.evalC_apply, hslice, ha',
    evalC_ofCosineCoeffs_all c hcsum x]
  rw [← hcos_series τ.1 x hx]

end ShenWork.EWA

#print axioms ShenWork.EWA.embedEWA_evenReal
#print axioms ShenWork.EWA.embedEWA_realizes
