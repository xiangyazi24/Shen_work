# Q2581 (cron1) — Lean 4 last-exit lemma for a continuous real function

Repository: `xiangyazi24/Shen_work`  
Branch: `chatgpt-scratch`  
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Core construction

Let

```lean
S := Set.Icc (0 : ℝ) t ∩ {s : ℝ | Z s ≤ K}
```

This set is nonempty because `0 ∈ S`, compact because it is a closed subset of the compact interval `[0,t]`, and bounded above by `t`.  Define

```lean
a := sSup S
```

By compactness, `a ∈ S`, hence `0 ≤ a`, `a ≤ t`, and `Z a ≤ K`.  If `Z a < K`, the intermediate value theorem on `[a,t]` gives some `c ∈ [a,t]` with `Z c = K`; since `Z a < K`, `c ≠ a`, so `a < c`.  But `c ∈ S`, contradicting `c ≤ sSup S = a`.  Thus `Z a = K`.  Finally, if some `s ∈ [a,t]` had `Z s < K`, then `s ∈ S`, so `s ≤ a`; with `a ≤ s`, this gives `s = a`, contradicting `Z a = K`.

## Complete Lean code

```lean
import Mathlib

open Set
open scoped Classical

noncomputable section

/-- Last exit from the sublevel set `{s | Z s ≤ K}` before a high excursion.

Given `Z` continuous on `[0,T]`, `Z 0 < K`, and a later time `t` with
`2*K < Z t`, there is a last time `a ∈ (0,t)` where `Z a = K`, and after
that time `Z` stays above `K` on `[a,t]`.
-/
theorem exists_last_exit_eq_level_and_stays_above
    {Z : ℝ → ℝ} {T K t : ℝ}
    (hcont : ContinuousOn Z (Set.Icc (0 : ℝ) T))
    (hZ0 : Z 0 < K)
    (hK : 0 < K)
    (ht0 : 0 < t)
    (htT : t < T)
    (hZt : 2 * K < Z t) :
    ∃ a : ℝ,
      a ∈ Set.Ioo (0 : ℝ) t ∧
        Z a = K ∧
          ∀ s ∈ Set.Icc a t, K ≤ Z s := by
  classical

  let S : Set ℝ := Set.Icc (0 : ℝ) t ∩ {s : ℝ | Z s ≤ K}

  have hsub_tT : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := by
    intro x hx
    exact ⟨hx.1, le_trans hx.2 htT.le⟩

  have hcont_t : ContinuousOn Z (Set.Icc (0 : ℝ) t) :=
    hcont.mono hsub_tT

  have hS_nonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    simp [S, ht0.le, hZ0.le]

  have hS_closed : IsClosed S := by
    simpa [S, Set.preimage, Set.mem_Iic] using
      (hcont_t.preimage_closed_of_closed
        (isClosed_Icc : IsClosed (Set.Icc (0 : ℝ) t))
        (isClosed_Iic : IsClosed (Set.Iic K)))

  have hS_subset_Icc : S ⊆ Set.Icc (0 : ℝ) t := by
    intro x hx
    exact hx.1

  have hS_compact : IsCompact S := by
    exact isCompact_Icc.of_isClosed_subset hS_closed hS_subset_Icc

  have hS_bddAbove : BddAbove S := by
    refine ⟨t, ?_⟩
    intro x hx
    exact hx.1.2

  let a : ℝ := sSup S

  have haS : a ∈ S := by
    dsimp [a]
    exact hS_compact.sSup_mem hS_nonempty

  have ha0 : 0 ≤ a := haS.1.1
  have hat : a ≤ t := haS.1.2
  have hZa_le : Z a ≤ K := haS.2

  have hK_lt_Zt : K < Z t := by
    nlinarith [hK, hZt]
  have hK_le_Zt : K ≤ Z t := hK_lt_Zt.le

  have hZa_eq : Z a = K := by
    by_contra hZa_ne
    have hZa_lt : Z a < K := lt_of_le_of_ne hZa_le hZa_ne

    have hsub_atT : Set.Icc a t ⊆ Set.Icc (0 : ℝ) T := by
      intro x hx
      exact ⟨le_trans ha0 hx.1, le_trans hx.2 htT.le⟩

    have hcont_at : ContinuousOn Z (Set.Icc a t) :=
      hcont.mono hsub_atT

    obtain ⟨c, hcIcc, hc_eq⟩ :=
      intermediate_value_Icc hat hcont_at hZa_le hK_le_Zt

    have hc_ne_a : c ≠ a := by
      intro hca
      have : Z a = K := by
        simpa [hca] using hc_eq
      exact hZa_ne this

    have ha_lt_c : a < c :=
      lt_of_le_of_ne hcIcc.1 (Ne.symm hc_ne_a)

    have hcS : c ∈ S := by
      refine ⟨?_, ?_⟩
      · exact ⟨le_trans ha0 hcIcc.1, hcIcc.2⟩
      · exact le_of_eq hc_eq

    have hc_le_a : c ≤ a := by
      dsimp [a]
      exact le_csSup hS_bddAbove hcS

    exact (not_lt_of_ge hc_le_a) ha_lt_c

  have ha_pos : 0 < a := by
    have h0_ne_a : (0 : ℝ) ≠ a := by
      intro h0a
      have hZ0_eq : Z 0 = K := by
        rw [h0a]
        exact hZa_eq
      exact (ne_of_lt hZ0) hZ0_eq
    exact lt_of_le_of_ne ha0 h0_ne_a

  have ha_lt_t : a < t := by
    have ha_ne_t : a ≠ t := by
      intro hat_eq
      have hZt_eq : Z t = K := by
        rw [← hat_eq]
        exact hZa_eq
      exact (ne_of_lt hK_lt_Zt) hZt_eq.symm
    exact lt_of_le_of_ne hat ha_ne_t

  refine ⟨a, ⟨ha_pos, ha_lt_t⟩, hZa_eq, ?_⟩

  intro s hs
  by_contra hnot
  have hZs_lt : Z s < K := lt_of_not_ge hnot

  have hsS : s ∈ S := by
    refine ⟨?_, ?_⟩
    · exact ⟨le_trans ha0 hs.1, hs.2⟩
    · exact hZs_lt.le

  have hs_le_a : s ≤ a := by
    dsimp [a]
    exact le_csSup hS_bddAbove hsS

  have hs_eq_a : s = a := le_antisymm hs_le_a hs.1

  have hZs_eq : Z s = K := by
    rw [hs_eq_a]
    exact hZa_eq

  exact (ne_of_lt hZs_lt) hZs_eq

end
```

## Notes for local integration

* The proof deliberately uses `S := [0,t] ∩ {s | Z s ≤ K}` and `a := sSup S`, not an arbitrary maximum witness.
* The compactness step is the intended one: restrict continuity to `[0,t]`, use `ContinuousOn.preimage_closed_of_closed` for the closed sublevel set, then use `isCompact_Icc.of_isClosed_subset`.
* The equality `Z a = K` is forced by `intermediate_value_Icc`; otherwise an equality point strictly after `a` would still lie in `S`, contradicting the supremum property.
* The assumption `K > 0` is used only to derive `K < Z t` from `2*K < Z t`.
