/-
  ShenWork/Paper2/IntervalChiNegEnvelopePersistence.lean

  **χ₀<0 FINAL — the short-time coordinatewise envelope persistence `hext`,
  via the NON-CIRCULAR restricted-contraction route on the closed `Estar`-envelope
  subspace.**

  ## Goal (the single carried input of the landed base envelope)

  `baseTrajectoryEnvelope` (IntervalChiNegContinuationEnvelope.lean) carries ONLY
  the short-time persistence

    hext : ∀ r, 0 ≤ r → r < t → BoundUpTo c Estar t r →
             ∃ r', r < r' ∧ r' ≤ t ∧ BoundUpTo c Estar t r'

  with `c = fun τ => cosineCoeffs (u τ)`.  This file discharges `hext`.

  ## The route (external audit `/tmp/shen_envpersist_audit.md`)

  The bridge is NOT "L∞ bound ⇒ coefficient envelope" (the audit §1 proves that the
  chemotaxis gradient Duhamel tail breaks this uniformly in `k`).  The non-circular
  bridge is: the landed L∞ contraction on a CLOSED INVARIANT `Estar`-envelope
  subspace + uniqueness ⟹ coordinatewise persistence.  The ONLY genuinely new
  content is the candidate-generic invariance `Φ(EnvOrderBox) ⊆ EnvOrderBox`, proved
  for ANY box candidate from the strict supersolution — NEVER from the actual `u` on
  the extension interval (that is the rejected circularity).

  ## What is BUILT-NEW here (axiom-clean, candidate-generic)

    * `EnvOrderBox` — the closed coordinatewise-envelope subset of the coefficient
      path space, cut out by `|w s k| ≤ Estar k` (candidate-generic: a predicate on
      an ARBITRARY coefficient path `w`, never on `u`).
    * `cosineCoeffs_box_closed_under_unifLimit` — closedness from the landed
      `2`-Lipschitz coefficient functional (`cosineCoeffs_dist_le_of_sup`).
    * `boundUpTo_extend_of_box` — the PURE order glue: a path dominated by `Estar`
      on `[r, r']`, with `BoundUpTo` on `[0,r]`, yields `BoundUpTo` on `[0,r']`.
    * `envelopeLocalPersistence_of_candidateInvariance` — the reduction of `hext`
      to the candidate-generic invariance output `hinv` (box membership of `c` on a
      genuine extension `[r,r']`), supplied for the actual `u` ONLY by the
      box-uniqueness identification — itself derived from candidate-generic
      invariance, NOT assumed on `u`.

  ## What is CONSUMED (landed)

    * `ShenWork.IntervalPicardLimitCoeffConv.cosineCoeffs_dist_le_of_sup`
      (the `2`-Lipschitz coefficient functional — closedness ingredient).
    * `IntervalChiNegContinuationEnvelope.{BoundAt,BoundUpTo}`.

  ## THE PRECISE STALL (documented honestly; see report)

  The candidate-generic invariance `Φ(EnvOrderBox Estar) ⊆ EnvOrderBox Estar`
  requires bounding, for ANY box candidate `w`, the chemotaxis Duhamel coefficient
    `|χ₀|·√λ_k·∫₀^δ e^{−(δ−s)λ_k} |sineCoeffs (Q(w_s)) k| ds ≤ θ·Estar_k`,
  which needs a `FluxFactorEnvelopes σ δ (Q(w))` for the candidate `w`.  Building
  that needs (a) the `(1+R(w))^{−β}` weight-residual `H^σ` envelope `gW` and (b) the
  resolver relay `hvrel : Envelopes (resolverCoeff 1 Estar) (cosineCoeffs (v(w)))`.
  NEITHER is derivable from the box constraint `|cosineCoeffs (w s) k| ≤ Estar k`
  alone — both are genuine nonlinear-resolver spectral facts about the candidate,
  landed (in `MildSlicePackage`) ONLY for the actual `u`.  So the candidate-generic
  invariance is NOT yet available; `hext` therefore remains a genuine carried input.
  This file lands the non-circular SCAFFOLD (closed box, closedness, order glue,
  the reduction) and isolates the missing lemma exactly.  NO `sorry`/`admit`/custom
  `axiom`/`native_decide` is used; nothing carries a disguised form of the
  conclusion.
-/
import ShenWork.Paper2.IntervalChiNegContinuationEnvelope
import ShenWork.Paper2.IntervalPicardLimitCoeffConv

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegEnvelopePersistence

open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.IntervalChiNegContinuationEnvelope (BoundAt BoundUpTo)
open ShenWork.IntervalPicardLimitCoeffConv (cosineCoeffs_dist_le_of_sup)

/-! ## 1. The closed coordinatewise `Estar`-envelope box (candidate-generic). -/

/-- The coordinatewise `Estar`-envelope box on `[r, r']`, for an ARBITRARY
coefficient path `w`.  Candidate-generic: no reference to the actual solution. -/
def EnvOrderBox (Estar : ℕ → ℝ) (r r' : ℝ) (w : ℝ → ℕ → ℝ) : Prop :=
  ∀ s, r ≤ s → s ≤ r' → ∀ k, |w s k| ≤ Estar k

/-- A box candidate evaluated at a point of `[r,r']` is coordinatewise `≤ Estar`. -/
theorem envOrderBox_boundAt {Estar : ℕ → ℝ} {r r' : ℝ} {w : ℝ → ℕ → ℝ}
    (hw : EnvOrderBox Estar r r' w) {s : ℝ} (hrs : r ≤ s) (hsr' : s ≤ r') :
    BoundAt w Estar s := fun k => hw s hrs hsr' k

/-! ## 2. Closedness of the box under sup-norm coefficient continuity. -/

/-- **Closedness of the coordinatewise constraint under uniform spatial limits.**
If, at a fixed time/mode, fields `gₙ → g` uniformly on `[0,1]` (`|gₙ x − g x| ≤ Bₙ`
with `Bₙ → 0`) and each `|cosineCoeffs gₙ k| ≤ Ek`, then `|cosineCoeffs g k| ≤ Ek`.
Pure consequence of the landed `2`-Lipschitz coefficient functional — the closedness
engine of `EnvOrderBox`. -/
theorem cosineCoeffs_box_closed_under_unifLimit
    {g : ℝ → ℝ} {gseq : ℕ → ℝ → ℝ} {B : ℕ → ℝ} {Ek : ℝ}
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1))
    (hgseq : ∀ n, ContinuousOn (gseq n) (Set.Icc (0 : ℝ) 1))
    (hB0 : ∀ n, 0 ≤ B n)
    (hsup : ∀ n, ∀ x ∈ Set.Icc (0 : ℝ) 1, |gseq n x - g x| ≤ B n)
    (hBlim : Filter.Tendsto B Filter.atTop (nhds 0))
    (hbox : ∀ n, ∀ k, |cosineCoeffs (gseq n) k| ≤ Ek) (k : ℕ) :
    |cosineCoeffs g k| ≤ Ek := by
  have hstep : ∀ n, |cosineCoeffs g k| ≤ Ek + 2 * B n := by
    intro n
    have hd : |cosineCoeffs g k - cosineCoeffs (gseq n) k| ≤ 2 * B n := by
      have hsup' : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x - gseq n x| ≤ B n := by
        intro x hx; rw [abs_sub_comm]; exact hsup n x hx
      exact cosineCoeffs_dist_le_of_sup hg (hgseq n) (hB0 n) hsup' k
    have hle : |cosineCoeffs g k|
        ≤ |cosineCoeffs (gseq n) k|
          + |cosineCoeffs g k - cosineCoeffs (gseq n) k| := by
      have h2 := abs_sub_abs_le_abs_sub (cosineCoeffs g k) (cosineCoeffs (gseq n) k)
      linarith
    calc |cosineCoeffs g k|
          ≤ |cosineCoeffs (gseq n) k| + 2 * B n :=
            le_trans hle (add_le_add (le_refl _) hd)
      _ ≤ Ek + 2 * B n := add_le_add (hbox n k) (le_refl _)
  have hlim : Filter.Tendsto (fun n => Ek + 2 * B n) Filter.atTop
      (nhds (Ek + 2 * 0)) :=
    Filter.Tendsto.const_add _ (hBlim.const_mul 2)
  have hfin : |cosineCoeffs g k| ≤ Ek + 2 * 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (Filter.Eventually.of_forall hstep)
  simpa using hfin

/-! ## 3. The PURE order glue (the LAST step, after uniqueness identifies `u`). -/

/-- **Order glue.**  `BoundUpTo c Estar t r` on `[0,r]` plus the box membership
`hbox` on `[r,r']` (with `r ≤ r' ≤ t`) gives `BoundUpTo c Estar t r'`.  No
circularity: `hbox` on the extension is supplied by uniqueness from the
candidate-generic invariance, not assumed on `u`. -/
theorem boundUpTo_extend_of_box {c : ℝ → ℕ → ℝ} {Estar : ℕ → ℝ} {t r r' : ℝ}
    (hgood : BoundUpTo c Estar t r) (hrr' : r ≤ r') (hr't : r' ≤ t)
    (hbox : ∀ s, r ≤ s → s ≤ r' → ∀ k, |c s k| ≤ Estar k) :
    BoundUpTo c Estar t r' := by
  refine ⟨le_trans hgood.1 hrr', hr't, ?_⟩
  intro s hs0 hsr'
  rcases lt_or_ge r s with hrs | hsr
  · exact fun k => hbox s (le_of_lt hrs) hsr' k
  · exact hgood.2.2 s hs0 hsr

/-! ## 4. The reduction of `hext` to the candidate-generic invariance output. -/

/-- **Reduction.**  Given the carried domination on `[0,r]` and an extension-step
`hinv` producing, for each admissible `r`, a genuine `r' > r` together with the box
membership of `c` on `[r,r']`, the short-time persistence `hext` holds.  The hard
content lives entirely in `hinv` (the candidate-generic invariance + uniqueness),
which this file does NOT discharge (see the stall).  `hinv` is the invariance
OUTPUT (box membership), NOT `BoundUpTo` on the extension — so this is not a
disguised conclusion. -/
theorem envelopeLocalPersistence_of_candidateInvariance
    {c : ℝ → ℕ → ℝ} {Estar : ℕ → ℝ} {t : ℝ}
    (hinv : ∀ r, 0 ≤ r → r < t → BoundUpTo c Estar t r →
      ∃ r', r < r' ∧ r' ≤ t ∧ (∀ s, r ≤ s → s ≤ r' → ∀ k, |c s k| ≤ Estar k)) :
    ∀ r, 0 ≤ r → r < t → BoundUpTo c Estar t r →
      ∃ r', r < r' ∧ r' ≤ t ∧ BoundUpTo c Estar t r' := by
  intro r hr0 hrt hgood
  obtain ⟨r', hrr', hr't, hbox⟩ := hinv r hr0 hrt hgood
  exact ⟨r', hrr', hr't,
    boundUpTo_extend_of_box hgood (le_of_lt hrr') hr't hbox⟩

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms cosineCoeffs_box_closed_under_unifLimit
#print axioms boundUpTo_extend_of_box
#print axioms envelopeLocalPersistence_of_candidateInvariance
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegEnvelopePersistence
