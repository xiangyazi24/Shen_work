import ShenWork.Wiener.EWA.Flux
import ShenWork.Wiener.EWA.FnegLipschitz

/-!
# EWA brick — `RealPowLipschitz`: norm + Lipschitz of the WL1/WL2 power maps (Phase C)

Quantitative companion of `Flux`'s `realPowEWA`/`qFactor`.  Builds, on top of the
just-built `FnegEWA_norm_le`/`FnegEWA_lipschitz`:

* `pow_nat_lipschitz_on_ball` — generic `NormedCommRing` power-Lipschitz on a ball:
  `‖f^m − g^m‖ ≤ m·R^{m−1}·‖f−g‖` (induction via `f^{n+1}−g^{n+1} = (f^n−g^n)f + g^n(f−g)`);
* `realPowEWA_norm_le` — `‖realPowEWA f γ‖ ≤ R^m·negNormConst (m−γ) δ Md` with `m = ⌊γ⌋+1`;
* `realPowEWA_lipschitz` — Lipschitz of `f ↦ realPowEWA f γ` on a ball, splitting
  `f^m·N(f) − g^m·N(g) = (f^m−g^m)·N(f) + g^m·(N(f)−N(g))`;
* `qFactor_lipschitz` / `qFactor_norm_le` — `FnegEWA_lipschitz`/`FnegEWA_norm_le` on `1+f`,
  using `gDeriv (1+f) = gDeriv f` (`GWA.gD_one` + CLM `map_add`).
-/

open scoped BigOperators
open MeasureTheory Set Real
open ShenWork.GWA ShenWork.Wiener

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Part 1 — generic power-Lipschitz on a ball. -/

/-- **`pow_nat_lipschitz_on_ball`.** In any `NormedCommRing`, on the ball of radius `R`,
the `m`-th power is Lipschitz with constant `m·R^{m−1}`. -/
theorem pow_nat_lipschitz_on_ball {A : Type*} [NormedCommRing A] {f g : A} {R : ℝ} {m : ℕ}
    (hR : 0 ≤ R) (hfR : ‖f‖ ≤ R) (hgR : ‖g‖ ≤ R) :
    ‖f ^ m - g ^ m‖ ≤ (m : ℝ) * R ^ (m - 1) * ‖f - g‖ := by
  induction m with
  | zero => simp
  | succ n ih =>
    -- `g ^ n`-norm bound, available without `NormOneClass` only for `n ≥ 1`;
    -- the `n = 0` step is handled separately (where the LHS reduces to `‖f − g‖`).
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0; simp
    · have hsplit : f ^ (n + 1) - g ^ (n + 1) = (f ^ n - g ^ n) * f + g ^ n * (f - g) := by
        ring
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      have hgn : ‖g ^ n‖ ≤ R ^ n :=
        le_trans (norm_pow_le' g hnpos) (pow_le_pow_left₀ (norm_nonneg g) hgR n)
      -- bound the two summands.
      have hA : ‖(f ^ n - g ^ n) * f‖ ≤ ((n : ℝ) * R ^ (n - 1) * ‖f - g‖) * R := by
        refine le_trans (norm_mul_le _ _) ?_
        exact mul_le_mul ih hfR (norm_nonneg f) (by positivity)
      have hB : ‖g ^ n * (f - g)‖ ≤ R ^ n * ‖f - g‖ := by
        refine le_trans (norm_mul_le _ _) ?_
        exact mul_le_mul_of_nonneg_right hgn (norm_nonneg _)
      refine le_trans (add_le_add hA hB) ?_
      -- collect: ((n)·R^{n−1}·‖f−g‖)·R + R^n·‖f−g‖ ≤ (n+1)·R^n·‖f−g‖.
      have hRn1 : R ^ (n - 1) * R = R ^ n := by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
        rw [Nat.succ_sub_one, ← pow_succ]
      have hdfg : (0 : ℝ) ≤ ‖f - g‖ := norm_nonneg _
      have hRn : (0 : ℝ) ≤ R ^ n := by positivity
      rw [Nat.add_sub_cancel]
      push_cast
      have key : ((n : ℝ) * R ^ (n - 1) * ‖f - g‖) * R + R ^ n * ‖f - g‖
          = ((n : ℝ) + 1) * R ^ n * ‖f - g‖ := by
        rw [show ((n : ℝ) * R ^ (n - 1) * ‖f - g‖) * R
              = (n : ℝ) * (R ^ (n - 1) * R) * ‖f - g‖ by ring, hRn1]; ring
      rw [key]

/-! ### Part 2 — `realPowEWA` norm bound. -/

/-- **`realPowEWA_norm_le`.** With `m = ⌊γ⌋+1` and `s = m−γ > 0`,
`‖realPowEWA f γ‖ ≤ R^m · negNormConst s δ Md`, on the ball `‖f‖ ≤ R`. -/
theorem realPowEWA_norm_le {f : EWA T 1} {γ δ Md R : ℝ} (hγ : 0 ≤ γ) (hδpos : 0 < δ)
    (hMd : 0 ≤ Md) (hf_floor : UniformFloor f δ) (hfD : ‖GWA.gDeriv f‖ ≤ Md)
    (hfR : ‖f‖ ≤ R) (hR : 0 ≤ R) :
    ‖realPowEWA f γ‖
      ≤ R ^ (Nat.floor γ + 1) * negNormConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md := by
  set m : ℕ := Nat.floor γ + 1 with hm_def
  have hs : 0 < (Nat.floor γ + 1 : ℝ) - γ := by
    have := Nat.lt_floor_add_one γ; linarith
  have hNf : ‖FnegEWA f ((Nat.floor γ + 1 : ℝ) - γ)‖
      ≤ negNormConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md :=
    FnegEWA_norm_le hs hδpos hMd hf_floor hfD
  have hmpos : 0 < m := by rw [hm_def]; exact Nat.succ_pos _
  have hpow : ‖f ^ m‖ ≤ R ^ m :=
    le_trans (norm_pow_le' f hmpos) (pow_le_pow_left₀ (norm_nonneg f) hfR m)
  rw [realPowEWA]
  refine le_trans (norm_mul_le _ _) ?_
  have hNnn : (0 : ℝ) ≤ negNormConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md :=
    le_trans (norm_nonneg _) hNf
  exact mul_le_mul hpow hNf (norm_nonneg _) (by positivity)

/-! ### Part 3 — `realPowEWA` Lipschitz on a ball. -/

/-- **`realPowEWA_lipschitz`.** `f ↦ realPowEWA f γ` is Lipschitz on the ball `‖·‖ ≤ R`
with constant `m·R^{m−1}·negNormConst s + R^m·negLipConst s` (`m = ⌊γ⌋+1`, `s = m−γ`). -/
theorem realPowEWA_lipschitz {f g : EWA T 1} {γ δ Md R : ℝ} (hγ : 0 ≤ γ) (hδpos : 0 < δ)
    (hMd : 0 ≤ Md) (hf_floor : UniformFloor f δ) (hg_floor : UniformFloor g δ)
    (hfD : ‖GWA.gDeriv f‖ ≤ Md) (hgD : ‖GWA.gDeriv g‖ ≤ Md)
    (hfR : ‖f‖ ≤ R) (hgR : ‖g‖ ≤ R) (hR : 0 ≤ R) :
    ‖realPowEWA f γ - realPowEWA g γ‖
      ≤ ((Nat.floor γ + 1 : ℝ) * R ^ ((Nat.floor γ + 1) - 1)
            * negNormConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md
          + R ^ (Nat.floor γ + 1) * negLipConst ((Nat.floor γ + 1 : ℝ) - γ) δ Md)
        * ‖f - g‖ := by
  set m : ℕ := Nat.floor γ + 1 with hm_def
  set s : ℝ := (Nat.floor γ + 1 : ℝ) - γ with hs_def
  have hs : 0 < s := by
    have := Nat.lt_floor_add_one γ; rw [hs_def]; linarith
  -- abbreviations N f, N g for the negative-power factors.
  set Nf : EWA T 1 := FnegEWA f s with hNf_def
  set Ng : EWA T 1 := FnegEWA g s with hNg_def
  -- the algebraic split.
  have hsplit : f ^ m * Nf - g ^ m * Ng = (f ^ m - g ^ m) * Nf + g ^ m * (Nf - Ng) := by
    ring
  -- the three ingredient bounds.
  have hpowL : ‖f ^ m - g ^ m‖ ≤ (m : ℝ) * R ^ (m - 1) * ‖f - g‖ :=
    pow_nat_lipschitz_on_ball hR hfR hgR
  have hNfnorm : ‖Nf‖ ≤ negNormConst s δ Md :=
    FnegEWA_norm_le hs hδpos hMd hf_floor hfD
  have hNlip : ‖Nf - Ng‖ ≤ negLipConst s δ Md * ‖f - g‖ :=
    FnegEWA_lipschitz hs hδpos hMd hf_floor hg_floor hfD hgD
  have hmpos : 0 < m := by rw [hm_def]; exact Nat.succ_pos _
  have hgpow : ‖g ^ m‖ ≤ R ^ m :=
    le_trans (norm_pow_le' g hmpos) (pow_le_pow_left₀ (norm_nonneg g) hgR m)
  -- nonnegativity bookkeeping.
  have hRm : (0 : ℝ) ≤ R ^ m := by positivity
  -- bound the two summands.
  have hT1 : ‖(f ^ m - g ^ m) * Nf‖
      ≤ ((m : ℝ) * R ^ (m - 1) * ‖f - g‖) * negNormConst s δ Md := by
    refine le_trans (norm_mul_le _ _) ?_
    exact mul_le_mul hpowL hNfnorm (norm_nonneg _) (by positivity)
  have hT2 : ‖g ^ m * (Nf - Ng)‖ ≤ R ^ m * (negLipConst s δ Md * ‖f - g‖) := by
    refine le_trans (norm_mul_le _ _) ?_
    exact mul_le_mul hgpow hNlip (norm_nonneg _) hRm
  -- assemble.
  -- the constant's `m−1` exponent and `↑m` cast, normalised against `⌊γ⌋₊`.
  have hm1 : m - 1 = Nat.floor γ := by rw [hm_def, Nat.add_sub_cancel]
  have hmcast : (m : ℝ) = (Nat.floor γ : ℝ) + 1 := by rw [hm_def]; push_cast; ring
  rw [realPowEWA, realPowEWA, ← hs_def, ← hm_def, ← hNf_def, ← hNg_def, hsplit]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add hT1 hT2) ?_
  rw [hm1, hmcast]
  apply le_of_eq; ring

/-! ### Part 4 — `qFactor` norm + Lipschitz (via `1+·` and `gD_one`). -/

/-- `gDeriv (1 + f) = gDeriv f` for `f : EWA T 1`: `gDeriv` is `ℂ`-linear (a CLM),
`gDeriv 1 = 0` (`GWA.gD_one`). -/
theorem gDeriv_one_add (f : EWA T 1) :
    GWA.gDeriv (1 + f) = GWA.gDeriv f := by
  rw [map_add, GWA.gD_one, zero_add]

/-- **`qFactor_norm_le`.** `‖qFactor β f‖ ≤ negNormConst β δ Md`, via `FnegEWA_norm_le` on `1+f`. -/
theorem qFactor_norm_le {β δ Md : ℝ} {f : EWA T 1} (hβ : 0 < β) (hδpos : 0 < δ)
    (hMd : 0 ≤ Md) (hf_floor : UniformFloor (1 + f) δ) (hfD : ‖GWA.gDeriv f‖ ≤ Md) :
    ‖qFactor β f‖ ≤ negNormConst β δ Md := by
  rw [qFactor]
  have hfD' : ‖GWA.gDeriv (1 + f)‖ ≤ Md := by rw [gDeriv_one_add]; exact hfD
  exact FnegEWA_norm_le hβ hδpos hMd hf_floor hfD'

/-- **`qFactor_lipschitz`.** `‖qFactor β f − qFactor β g‖ ≤ negLipConst β δ Md · ‖f−g‖`,
via `FnegEWA_lipschitz` on `1+f`, `1+g`, using `(1+f)−(1+g)=f−g` and `gDeriv (1+·)=gDeriv ·`. -/
theorem qFactor_lipschitz {β δ Md : ℝ} {f g : EWA T 1} (hβ : 0 < β) (hδpos : 0 < δ)
    (hMd : 0 ≤ Md) (hf_floor : UniformFloor (1 + f) δ) (hg_floor : UniformFloor (1 + g) δ)
    (hfD : ‖GWA.gDeriv f‖ ≤ Md) (hgD : ‖GWA.gDeriv g‖ ≤ Md) :
    ‖qFactor β f - qFactor β g‖ ≤ negLipConst β δ Md * ‖f - g‖ := by
  rw [qFactor, qFactor]
  have hfD' : ‖GWA.gDeriv (1 + f)‖ ≤ Md := by rw [gDeriv_one_add]; exact hfD
  have hgD' : ‖GWA.gDeriv (1 + g)‖ ≤ Md := by rw [gDeriv_one_add]; exact hgD
  have hsub : (1 + f) - (1 + g) = f - g := by ring
  have h := FnegEWA_lipschitz hβ hδpos hMd hf_floor hg_floor hfD' hgD'
  rw [hsub] at h
  exact h

end ShenWork.EWA

#print axioms ShenWork.EWA.pow_nat_lipschitz_on_ball
#print axioms ShenWork.EWA.realPowEWA_lipschitz
#print axioms ShenWork.EWA.qFactor_lipschitz
