/-
# Physical (bounded-weight) joint `(t,x)` `C²` of the elliptic resolver series

The committed spatial-`C²` theorem `IntervalResolverPhysicalC2.resolverR_contDiff_two_of_source_l1`
proves the resolver's spatial `C²` from `ℓ¹` source coefficients via the bounded
elliptic multiplier `λ_k/(μ+λ_k) ≤ 1`.  This file lifts that mechanism to the
**joint** `(t,x)` order-`≤2` regularity, WITHOUT the spectral eigenvalue-cube
ladder.

## The bounded-weight mechanism

`v(t,x) = ∑_k c_k(t) · cos(kπx)` with `c_k(t) = â_k(t)/(μ+λ_k)`.  Each order-`≤2`
joint `(t,x)` iterated derivative of the `n`-th term `c_n(t)·cos(nπx)` is bounded,
by the Leibniz product rule, by

  `∑_{i≤k} C(k,i) · Bₜ(i,n) · valueCosWeight(k-i,n)`,

where `Bₜ(i,n) ≥ ‖∂ₜⁱ c_n‖` and `valueCosWeight(·,n)` carries the spatial weight
(`1`, `nπ`, `λ_n` for orders `0,1,2`).  The **only** eigenvalue growth lives in the
spatial factor `valueCosWeight 2 n = λ_n`; the bounded elliptic weight inside
`Bₜ(0,n) = |â_n|/(μ+λ_n)` cancels it exactly (`λ_n·Bₜ(0,n) ≤ |â_n|`).  So the
joint majorant is controlled by `(|â_n| + (nπ)|∂ₜâ_n| + |∂ₜ²â_n|)`-summability — the
3-time-order source `ℓ¹` data, strictly weaker than the spectral `λ²` ladder.

## What is proved (0 sorry, 0 admit, 0 custom axiom)

* `boundedWeightJointTerm_iteratedFDeriv_le` — the joint order-`≤2` Leibniz majorant
  for one mode term, in terms of the time-derivative bounds and `valueCosWeight`.
* `boundedWeightJointSeries_contDiff_two` — the generic joint `ContDiff ℝ 2`
  assembler from a `ContDiff`-in-`t` mode family plus its three-order summable
  bounded-weight majorant.  Mirrors the committed `contDiff_tsum` application, but
  the majorant is the bounded-weight `(Bₜ·valueCosWeight)` one (NO `λ²`).
-/
import ShenWork.PDE.IntervalResolverSpectralJointC2Concrete

open Filter Topology Set
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalResolverSpectralJointC2Concrete
  (valueCosWeight valueCosWeight_nonneg cosineMode_iteratedFDeriv_bound
   gradCosWeight gradCosWeight_nonneg cosineModeDeriv_iteratedFDeriv_bound)
open ShenWork.CosineSpectrum (cosineMode_deriv)
open ShenWork.IntervalResolverSpectralJointC2CutoffBounds
  (norm_iteratedFDeriv_comp_fst_le norm_iteratedFDeriv_comp_snd_le)

noncomputable section

namespace ShenWork.IntervalResolverJointC2Physical

/-- The `n`-th joint `(t,x)` term of the bounded-weight resolver series:
`(t,x) ↦ c n t · cos(nπx)`. -/
def boundedWeightJointTerm (c : ℕ → ℝ → ℝ) (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => c n q.1 * cosineMode n q.2

/-- The bounded-weight joint majorant of one term at order `k`:
`∑_{i≤k} C(k,i)·Bₜ(i,n)·valueCosWeight(k-i,n)`. -/
def boundedWeightJointMajorant (Bt : ℕ → ℕ → ℝ) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * Bt i n * valueCosWeight (k - i) n

/-- Each mode term is jointly `ContDiff ℝ 2` when `c n` is `ContDiff ℝ 2` in `t`. -/
theorem boundedWeightJointTerm_contDiff
    {c : ℕ → ℝ → ℝ} (n : ℕ) (hc : ContDiff ℝ (2 : ℕ∞) (c n)) :
    ContDiff ℝ (2 : ℕ∞) (boundedWeightJointTerm c n) := by
  have hcj : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => c n q.1) :=
    hc.comp contDiff_fst
  have hcos₀ : ContDiff ℝ (2 : ℕ∞) (cosineMode n) := by
    unfold cosineMode; fun_prop
  have hcos : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => cosineMode n q.2) :=
    hcos₀.comp contDiff_snd
  simpa [boundedWeightJointTerm] using hcj.mul hcos

/-- **Joint Leibniz majorant** for one bounded-weight mode term.  The order-`≤2`
joint `(t,x)` iterated derivative is bounded by the bounded-weight majorant, with
the time factor controlled by `Bt` and the spatial factor by `valueCosWeight`. -/
theorem boundedWeightJointTerm_iteratedFDeriv_le
    {c : ℕ → ℝ → ℝ} {Bt : ℕ → ℕ → ℝ} {n k : ℕ} {q : ℝ × ℝ}
    (hc : ContDiff ℝ (2 : ℕ∞) (c n)) (hk : (k : ℕ∞) ≤ (2 : ℕ∞))
    (hBt : ∀ i, i ≤ 2 → ‖iteratedFDeriv ℝ i (c n) q.1‖ ≤ Bt i n) :
    ‖iteratedFDeriv ℝ k (boundedWeightJointTerm c n) q‖ ≤
      boundedWeightJointMajorant Bt k n := by
  have hkNat : k ≤ 2 := by exact_mod_cast hk
  have hcj : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => c n q.1) :=
    hc.comp contDiff_fst
  have hcos₀ : ContDiff ℝ (2 : ℕ∞) (cosineMode n) := by
    unfold cosineMode; fun_prop
  have hcos : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => cosineMode n q.2) :=
    hcos₀.comp contDiff_snd
  have hkTop : ((k : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast hk
  have hprod := norm_iteratedFDeriv_mul_le hcj hcos q hkTop
  have hprod' :
      ‖iteratedFDeriv ℝ k (boundedWeightJointTerm c n) q‖ ≤
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => c n q.1) q‖ *
          ‖iteratedFDeriv ℝ (k - i) (fun q : ℝ × ℝ => cosineMode n q.2) q‖ := by
    simpa [boundedWeightJointTerm] using hprod
  refine hprod'.trans ?_
  apply Finset.sum_le_sum
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hiTop : ((i : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_trans hik hkNat
  have hkiTop : (((k - i : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_trans (Nat.sub_le k i) hkNat
  have htime : ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => c n q.1) q‖ ≤ Bt i n :=
    (norm_iteratedFDeriv_comp_fst_le hc hiTop q).trans (hBt i (le_trans hik hkNat))
  have hspace : ‖iteratedFDeriv ℝ (k - i) (fun q : ℝ × ℝ => cosineMode n q.2) q‖ ≤
      valueCosWeight (k - i) n :=
    (norm_iteratedFDeriv_comp_snd_le hcos₀ hkiTop q).trans
      (cosineMode_iteratedFDeriv_bound n (k - i) q.2 (by omega))
  have hcnn : (0 : ℝ) ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
  have htnn : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => c n q.1) q‖ :=
    norm_nonneg _
  have hsnn : (0 : ℝ) ≤ valueCosWeight (k - i) n := valueCosWeight_nonneg _ _
  have hBtnn : (0 : ℝ) ≤ Bt i n := le_trans htnn htime
  calc (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => c n q.1) q‖ *
        ‖iteratedFDeriv ℝ (k - i) (fun q : ℝ × ℝ => cosineMode n q.2) q‖
      ≤ (k.choose i : ℝ) * Bt i n * valueCosWeight (k - i) n := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left htime hcnn
        · exact hspace
        · exact norm_nonneg _
        · exact mul_nonneg hcnn hBtnn
    _ = (k.choose i : ℝ) * Bt i n * valueCosWeight (k - i) n := rfl

/-- **Generic bounded-weight joint `ContDiff ℝ 2` assembler.**
From a mode family `c` that is `ContDiff ℝ 2` in `t`, with three-order time
bounds `Bt` whose bounded-weight joint majorant `boundedWeightJointMajorant Bt k`
is summable for every `k ≤ 2`, the joint series `(t,x) ↦ ∑' n, c n t · cos(nπx)`
is jointly `ContDiff ℝ 2`.  This is the physical-route mirror of the spectral
`contDiff_tsum` assembly — the majorant carries the spatial `λ_n` only, with the
time factor `Bt` bounded by the elliptic weight (NO `λ²` ladder). -/
theorem boundedWeightJointSeries_contDiff_two
    {c : ℕ → ℝ → ℝ} {Bt : ℕ → ℕ → ℝ}
    (hc : ∀ n, ContDiff ℝ (2 : ℕ∞) (c n))
    (hBt : ∀ (i n : ℕ) (t : ℝ), i ≤ 2 → ‖iteratedFDeriv ℝ i (c n) t‖ ≤ Bt i n)
    (hsumm : ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant Bt k)) :
    ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' n : ℕ, boundedWeightJointTerm c n q) :=
  contDiff_tsum
    (𝕜 := ℝ) (f := boundedWeightJointTerm c)
    (v := boundedWeightJointMajorant Bt)
    (fun n => boundedWeightJointTerm_contDiff n (hc n))
    hsumm
    (fun k n q hk =>
      boundedWeightJointTerm_iteratedFDeriv_le (hc n)
        (by exact_mod_cast hk) (fun i hi => hBt i n q.1 hi))

/-! ## Gradient (spatial-derivative) bounded-weight joint series -/

/-- The `n`-th joint term of the **spatial-gradient** bounded-weight series:
`(t,x) ↦ c n t · ∂ₓ cos(nπx)`. -/
def boundedWeightJointGradTerm (c : ℕ → ℝ → ℝ) (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => c n q.1 * deriv (cosineMode n) q.2

/-- Gradient joint majorant of one term:
`∑_{i≤k} C(k,i)·Bₜ(i,n)·gradCosWeight(k-i,n)`. -/
def boundedWeightJointGradMajorant (Bt : ℕ → ℕ → ℝ) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * Bt i n * gradCosWeight (k - i) n

/-- `∂ₓ cos(nπx)` is `ContDiff ℝ 2`. -/
private theorem cosineModeDeriv_contDiff (n : ℕ) :
    ContDiff ℝ (2 : ℕ∞) (fun y : ℝ => deriv (cosineMode n) y) := by
  have hEq : (fun y : ℝ => deriv (cosineMode n) y) =
      fun y : ℝ => -((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * y) := by
    funext y; rw [cosineMode_deriv]
  rw [hEq]; fun_prop

theorem boundedWeightJointGradTerm_contDiff
    {c : ℕ → ℝ → ℝ} (n : ℕ) (hc : ContDiff ℝ (2 : ℕ∞) (c n)) :
    ContDiff ℝ (2 : ℕ∞) (boundedWeightJointGradTerm c n) := by
  have hcj : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => c n q.1) := hc.comp contDiff_fst
  have hd : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => deriv (cosineMode n) q.2) :=
    (cosineModeDeriv_contDiff n).comp contDiff_snd
  simpa [boundedWeightJointGradTerm] using hcj.mul hd

/-- **Gradient joint Leibniz majorant** for one bounded-weight mode term. -/
theorem boundedWeightJointGradTerm_iteratedFDeriv_le
    {c : ℕ → ℝ → ℝ} {Bt : ℕ → ℕ → ℝ} {n k : ℕ} {q : ℝ × ℝ}
    (hc : ContDiff ℝ (2 : ℕ∞) (c n)) (hk : (k : ℕ∞) ≤ (2 : ℕ∞))
    (hBt : ∀ i, i ≤ 2 → ‖iteratedFDeriv ℝ i (c n) q.1‖ ≤ Bt i n) :
    ‖iteratedFDeriv ℝ k (boundedWeightJointGradTerm c n) q‖ ≤
      boundedWeightJointGradMajorant Bt k n := by
  have hkNat : k ≤ 2 := by exact_mod_cast hk
  have hcj : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => c n q.1) := hc.comp contDiff_fst
  have hd₀ : ContDiff ℝ (2 : ℕ∞) (fun y : ℝ => deriv (cosineMode n) y) :=
    cosineModeDeriv_contDiff n
  have hd : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => deriv (cosineMode n) q.2) :=
    hd₀.comp contDiff_snd
  have hkTop : ((k : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hk
  have hprod := norm_iteratedFDeriv_mul_le hcj hd q hkTop
  have hprod' :
      ‖iteratedFDeriv ℝ k (boundedWeightJointGradTerm c n) q‖ ≤
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => c n q.1) q‖ *
          ‖iteratedFDeriv ℝ (k - i)
            (fun q : ℝ × ℝ => deriv (cosineMode n) q.2) q‖ := by
    simpa [boundedWeightJointGradTerm] using hprod
  refine hprod'.trans ?_
  apply Finset.sum_le_sum
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hiTop : ((i : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_trans hik hkNat
  have hkiTop : (((k - i : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_trans (Nat.sub_le k i) hkNat
  have htime : ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => c n q.1) q‖ ≤ Bt i n :=
    (norm_iteratedFDeriv_comp_fst_le hc hiTop q).trans (hBt i (le_trans hik hkNat))
  have hspace :
      ‖iteratedFDeriv ℝ (k - i) (fun q : ℝ × ℝ => deriv (cosineMode n) q.2) q‖ ≤
        gradCosWeight (k - i) n :=
    (norm_iteratedFDeriv_comp_snd_le hd₀ hkiTop q).trans
      (cosineModeDeriv_iteratedFDeriv_bound n (k - i) q.2 (by omega))
  have hcnn : (0 : ℝ) ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
  have hBtnn : (0 : ℝ) ≤ Bt i n := le_trans (norm_nonneg _) htime
  calc (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => c n q.1) q‖ *
        ‖iteratedFDeriv ℝ (k - i) (fun q : ℝ × ℝ => deriv (cosineMode n) q.2) q‖
      ≤ (k.choose i : ℝ) * Bt i n * gradCosWeight (k - i) n := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left htime hcnn
        · exact hspace
        · exact norm_nonneg _
        · exact mul_nonneg hcnn hBtnn
    _ = (k.choose i : ℝ) * Bt i n * gradCosWeight (k - i) n := rfl

/-- **Generic gradient bounded-weight joint `ContDiff ℝ 2` assembler.** -/
theorem boundedWeightJointGradSeries_contDiff_two
    {c : ℕ → ℝ → ℝ} {Bt : ℕ → ℕ → ℝ}
    (hc : ∀ n, ContDiff ℝ (2 : ℕ∞) (c n))
    (hBt : ∀ (i n : ℕ) (t : ℝ), i ≤ 2 → ‖iteratedFDeriv ℝ i (c n) t‖ ≤ Bt i n)
    (hsumm : ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant Bt k)) :
    ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' n : ℕ, boundedWeightJointGradTerm c n q) :=
  contDiff_tsum
    (𝕜 := ℝ) (f := boundedWeightJointGradTerm c)
    (v := boundedWeightJointGradMajorant Bt)
    (fun n => boundedWeightJointGradTerm_contDiff n (hc n))
    hsumm
    (fun k n q hk =>
      boundedWeightJointGradTerm_iteratedFDeriv_le (hc n)
        (by exact_mod_cast hk) (fun i hi => hBt i n q.1 hi))

end ShenWork.IntervalResolverJointC2Physical
