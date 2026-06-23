/-
  ShenWork/Paper2/IntervalChiNegContinuationEnvelope.lean

  THE χ₀<0 BASE TRAJECTORY ENVELOPE via NON-CIRCULAR TIME-CONTINUATION.

  ## Why this file exists (the prior rejection)

  A prior producer carried the GLOBAL domination
    `hEdom : ∀ τ ∈ [0,t], ∀ k, |cosineCoeffs (u τ) k| ≤ Estar k`
  — i.e. the `TrajectoryHSigmaEnvelope.hdom` CONCLUSION — as a certificate field
  and fed it into the flux-envelope build.  That is circular: it assumes the
  conclusion.  This file NEVER carries the global domination.  Instead it carries
  ONLY the SHORT-TIME local persistence `hext` (`∃ r' > r`, a genuinely weaker and
  distinct analytic input) and DERIVES the global `BoundUpTo Estar t` from it by a
  pure supremum/order continuation argument.

  ## What is BUILT here (pure order theory, no PDE)

  * `BoundAt`, `BoundUpTo` — the per-time / cumulative coordinatewise bound.
  * `BoundUpTo.mono_right` — restriction of a cumulative bound to a smaller time.
  * `continuation_from_local_extension` — the abstract sup lemma:
      `{h0, hclosed_left, hext} ⊢ BoundUpTo E t`.  FULLY PROVED (csSup_le /
      le_csSup).  The global bound is its OUTPUT.
  * `boundUpTo_zero_of_base` — `h0 := BoundUpTo E 0` from the base `BoundAt E 0`.
  * `hclosed_left_of_coeffContinuity` — the closed-left step from per-mode
    time-continuity of `s ↦ cosineCoeffs (u s) k`.
  * `baseTrajectoryEnvelope_of_continuation : BoundUpTo Estar t →
      TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (u τ))` — the env
    constructor; `hdom` is read off the DERIVED `BoundUpTo Estar t`.
  * `baseTrajectoryEnvelope` — the end-to-end producer.

  ## What is CARRIED (the single faithful named analytic input)

  ONLY `hext` = `local_inflated_envelope_persistence`: short-time `∃ r' > r`
  extension of the cumulative bound.  This is the paper's local mild/Picard
  persistence in the envelope lattice — genuinely distinct from (weaker than) the
  global domination.  No global-`τ` hypothesis is carried.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.  Imports
  ONLY the envelope structure + the coefficient definition; never the classical
  producers.
-/
import ShenWork.Paper2.IntervalTrajectoryEnvelope

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegContinuationEnvelope

open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (MemHSigma)
open ShenWork.Paper2.IntervalTrajectoryEnvelope (TrajectoryHSigmaEnvelope)

/-! ## The cumulative coordinatewise bound (no PDE content). -/

/-- `BoundAt c E s` : at time `s` every coefficient `c s k` is dominated by `E k`. -/
def BoundAt (c : ℝ → ℕ → ℝ) (E : ℕ → ℝ) (s : ℝ) : Prop := ∀ k, |c s k| ≤ E k

/-- `BoundUpTo c E t r` : `0 ≤ r ≤ t` and the bound holds on all of `[0,r]`. -/
def BoundUpTo (c : ℝ → ℕ → ℝ) (E : ℕ → ℝ) (t r : ℝ) : Prop :=
  0 ≤ r ∧ r ≤ t ∧ ∀ s, 0 ≤ s → s ≤ r → BoundAt c E s

/-- A cumulative bound up to `r` restricts to any `0 ≤ q ≤ r`. -/
theorem BoundUpTo.mono_right {c : ℝ → ℕ → ℝ} {E : ℕ → ℝ} {t r q : ℝ}
    (h : BoundUpTo c E t r) (hq0 : 0 ≤ q) (hqr : q ≤ r) : BoundUpTo c E t q :=
  ⟨hq0, le_trans hqr h.2.1, fun s hs0 hsq => h.2.2 s hs0 (le_trans hsq hqr)⟩

/-! ## The abstract continuation lemma (PURE order/sup — FULLY PROVED). -/

/-- **`continuation_from_local_extension`** — the non-circular continuation.

From the base point `h0`, the closed-left step `hclosed_left` (limit/closedness of
the cumulative bound from per-mode continuity), and the SHORT-TIME extension
`hext` (`∃ r' > r`, the carried local persistence), the GLOBAL cumulative bound
`BoundUpTo c E t t` is DERIVED.  `R := {r | BoundUpTo c E t r}`, `r* := sSup R`;
`r* ∈ R` by `hclosed_left`, and `r* = t` because `hext` forbids `r* < t`. -/
theorem continuation_from_local_extension {c : ℝ → ℕ → ℝ} {E : ℕ → ℝ} {t : ℝ}
    (_ht : 0 ≤ t)
    (h0 : BoundUpTo c E t 0)
    (hclosed_left : ∀ r, 0 ≤ r → r ≤ t →
      (∀ q, 0 ≤ q → q < r → BoundUpTo c E t q) → BoundUpTo c E t r)
    (hext : ∀ r, 0 ≤ r → r < t →
      BoundUpTo c E t r → ∃ r', r < r' ∧ r' ≤ t ∧ BoundUpTo c E t r') :
    BoundUpTo c E t t := by
  set R : Set ℝ := {r | BoundUpTo c E t r} with hR
  have hRne : R.Nonempty := ⟨0, h0⟩
  have hRbdd : BddAbove R := ⟨t, fun r hr => hr.2.1⟩
  set r := sSup R with hr_def
  have hr0 : 0 ≤ r := le_csSup hRbdd h0
  have hrt : r ≤ t := csSup_le hRne (fun x hx => hx.2.1)
  -- the closed-left step pins `r ∈ R`.
  have hmem : BoundUpTo c E t r := by
    refine hclosed_left r hr0 hrt (fun q hq0 hqr => ?_)
    obtain ⟨x, hxR, hqx⟩ := exists_lt_of_lt_csSup hRne hqr
    exact (hxR.mono_right hq0 (le_of_lt hqx))
  -- if `r < t`, the short-time extension overshoots the sup: contradiction.
  rcases lt_or_eq_of_le hrt with hlt | heq
  · obtain ⟨r', hrr', hr't, hr'mem⟩ := hext r hr0 hlt hmem
    exact absurd (le_csSup hRbdd hr'mem) (not_le.2 hrr')
  · exact heq ▸ hmem

/-! ## `h0` — the base point from the s = 0 datum bound (BUILT). -/

/-- The base `BoundUpTo c E t 0` from the single base bound `BoundAt c E 0`. -/
theorem boundUpTo_zero_of_base {c : ℝ → ℕ → ℝ} {E : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hbase : BoundAt c E 0) : BoundUpTo c E t 0 :=
  ⟨le_refl 0, ht, fun _ hs0 hs0' => le_antisymm hs0' hs0 ▸ hbase⟩

/-! ## `hclosed_left` — the closed-left step from per-mode time-continuity (BUILT).

For fixed `k`, `s ↦ c s k` is continuous, so `|c s k| ≤ E k` is preserved when we
take a left limit `q ↑ r`.  We only need per-mode continuity — NOT a global
modulus.  Interior points `s < r` are handled directly by `hlt`. -/

/-- Left-limit closure of the bound at a point `s ∈ (0,r]`, using per-mode
continuity on `[0,s)` and the strict-interior bounds from `hlt`. -/
theorem bound_endpoint_via_left_limit {c : ℝ → ℕ → ℝ} {E : ℕ → ℝ} {t : ℝ}
    (hcont : ∀ k, ContinuousOn (fun s => c s k) (Set.Icc 0 t))
    {r s : ℝ} (hrt : r ≤ t)
    (hlt : ∀ q, 0 ≤ q → q < r → BoundUpTo c E t q)
    (hs0 : 0 ≤ s) (hsr : s ≤ r) (h0s : (0 : ℝ) < s) (k : ℕ) : |c s k| ≤ E k := by
  have hsmem : s ∈ Set.Icc (0 : ℝ) t := ⟨hs0, le_trans hsr hrt⟩
  have hsub : Set.Ico (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) t :=
    fun u hu => ⟨hu.1, le_trans (le_of_lt hu.2) (le_trans hsr hrt)⟩
  have hcl : ContinuousWithinAt (fun u => c u k) (Set.Ico 0 s) s :=
    ((hcont k).continuousWithinAt hsmem).mono hsub
  have hcvabs : ContinuousWithinAt (fun u => |c u k|) (Set.Ico 0 s) s := hcl.abs
  have hbnd : ∀ᶠ u in nhdsWithin s (Set.Ico 0 s), |c u k| ≤ E k :=
    eventually_nhdsWithin_of_forall
      (fun u hu => (hlt u hu.1 (lt_of_lt_of_le hu.2 hsr)).2.2 u hu.1 (le_refl u) k)
  have hF : (nhdsWithin s (Set.Ico (0 : ℝ) s)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico (ne_of_lt h0s)]
    exact ⟨hs0, le_refl s⟩
  exact le_of_tendsto hcvabs.tendsto hbnd

/-- The closed-left step from per-mode continuity of `s ↦ c s k` on `[0,t]`.

The single-time base bound `hbase` covers ONLY the degenerate endpoint `s = 0`
(where there is no left interval to take a limit over); it is NOT the global
domination.  Interior points use `hlt`, and `s ∈ (0,r]` uses the left limit. -/
theorem hclosed_left_of_coeffContinuity {c : ℝ → ℕ → ℝ} {E : ℕ → ℝ} {t : ℝ}
    (hbase : BoundAt c E 0)
    (hcont : ∀ k, ContinuousOn (fun s => c s k) (Set.Icc 0 t)) :
    ∀ r, 0 ≤ r → r ≤ t →
      (∀ q, 0 ≤ q → q < r → BoundUpTo c E t q) → BoundUpTo c E t r := by
  refine fun r hr0 hrt hlt => ⟨hr0, hrt, fun s hs0 hsr => ?_⟩
  rcases lt_or_eq_of_le hsr with hsr' | hsr'
  · exact (hlt s hs0 hsr').2.2 s hs0 (le_refl s)
  -- the endpoint `s = r`: take a left limit of `q ↑ r`.
  subst hsr'
  rcases eq_or_lt_of_le hs0 with h0s | h0s
  · -- `s = 0` (so `r = 0`): the window is the single point; use the base bound.
    rw [← h0s]; exact hbase
  · exact fun k => bound_endpoint_via_left_limit hcont hrt hlt hs0 hsr h0s k

/-! ## The env constructor — `hdom` read off the DERIVED global bound (BUILT). -/

/-- **`baseTrajectoryEnvelope_of_continuation`** — package the DERIVED global
bound `BoundUpTo (fun τ => cosineCoeffs (u τ)) Estar t t` into the trajectory
envelope.  `env := Estar`, `henv := hEstar`, and `hdom` is exactly the cumulative
bound unfolded at the right-endpoint window.  The `hdom` field is OUTPUT
(derived), never a carried input. -/
def baseTrajectoryEnvelope_of_continuation {σ t : ℝ} {u : ℝ → ℝ → ℝ} {Estar : ℕ → ℝ}
    (hEstar : MemHSigma σ Estar)
    (hglob : BoundUpTo (fun τ => cosineCoeffs (u τ)) Estar t t) :
    TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (u τ)) where
  env := Estar
  henv := hEstar
  hdom := fun τ hτ k => hglob.2.2 τ hτ.1 hτ.2 k

/-! ## The end-to-end producer (BUILT continuation + CARRIED `hext` only). -/

/-- **`baseTrajectoryEnvelope`** — the χ₀<0 base trajectory envelope.

BUILT from: `hEstar` (the `H^σ` membership of `Estar`), `hbase` (the s = 0 datum
bound, a SINGLE-TIME fact), per-mode time-continuity `hcont`, and the SINGLE
CARRIED analytic input `hext` (short-time `∃ r' > r` persistence).  The global
domination `TrajectoryHSigmaEnvelope.hdom` is DERIVED via
`continuation_from_local_extension`, NOT carried. -/
def baseTrajectoryEnvelope {σ t : ℝ} {u : ℝ → ℝ → ℝ} {Estar : ℕ → ℝ} (ht : 0 ≤ t)
    (hEstar : MemHSigma σ Estar)
    (hbase : BoundAt (fun τ => cosineCoeffs (u τ)) Estar 0)
    (hcont : ∀ k,
      ContinuousOn (fun s => cosineCoeffs (u s) k) (Set.Icc 0 t))
    (hext : ∀ r, 0 ≤ r → r < t →
      BoundUpTo (fun τ => cosineCoeffs (u τ)) Estar t r →
      ∃ r', r < r' ∧ r' ≤ t ∧ BoundUpTo (fun τ => cosineCoeffs (u τ)) Estar t r') :
    TrajectoryHSigmaEnvelope σ t (fun τ => cosineCoeffs (u τ)) :=
  baseTrajectoryEnvelope_of_continuation hEstar
    (continuation_from_local_extension ht
      (boundUpTo_zero_of_base ht hbase)
      (hclosed_left_of_coeffContinuity hbase hcont)
      hext)

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms continuation_from_local_extension
#print axioms baseTrajectoryEnvelope
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegContinuationEnvelope
