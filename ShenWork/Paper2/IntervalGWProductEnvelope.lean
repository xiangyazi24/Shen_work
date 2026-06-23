/-
  ShenWork/Paper2/IntervalGWProductEnvelope.lean

  Atom #1E — the chemotaxis WEIGHT product envelope `gW` of `W = u·(1+v)^{−β}`,
  the LAST piece of `FluxFactorEnvelopes` (the carried `gW`/`hgW`/`heW` fields of
  `IntervalFluxFactorEnvelope`).  Closing it removes the only carried hypothesis
  from `genv_of_trajectoryEnvelope`, closing the χ₀<0 flux factor-envelope (#1)
  down to the trajectory envelope `Uσ` + ONE precisely-named denominator residual.

  ## What this file delivers

  * `gW := trueCosProd Uσ Gdenσ` — the cosine envelope of `W = u·(1+v)^{−β}`.

  * **`MemHSigma σ gW` UNCONDITIONALLY** (`gW_memHSigma`): from `MemHSigma σ Uσ`
    (the trajectory envelope) and `MemHSigma σ Gdenσ` (the denominator envelope's
    membership), via the H^σ Banach-algebra closure
    `memHSigma_trueCosProd_of_gt_half` (σ > 1/2).  No new estimate.

  * **τ-uniform domination** (`gW_envelopes`): given the per-τ cosine bridge
    `CosineMulBridge (u τ) ((1+v τ)^{−β})` and the τ-uniform factor envelopes
    `Envelopes Uσ (cosineCoeffs (u τ))`, `Envelopes Gdenσ (cosineCoeffs ((1+v τ)^{−β}))`,
    the SINGLE sequence `trueCosProd Uσ Gdenσ` envelopes `cosineCoeffs (W τ)` for
    EVERY `τ ∈ [0,t]` — by the envelope-monotone product `envelopes_trueCosProd`
    composed with the function-product bridge.  No Gronwall, no per-τ estimate.

  * **ASSEMBLY** (`fluxFactorEnvelopes_of_traj_denom`, `genv_of_traj_denom`):
    feeds `gW` + the landed resolver-relay sine envelope `gvx := sineEnv Uσ` into
    the landed `fluxFactorEnvelopes_of_trajectoryEnvelope` / `fluxEnvelope_of_*`,
    producing the FULL `FluxFactorEnvelopes σ t Q` and chaining the flux H^σ
    envelope `genv := trueCosProd gW (sineEnv Uσ)` — with NO carried `gW`.

  ## THE PRECISE RESIDUAL (τ-uniformity of `Gdenσ`)

  The landed `denom_envelope_memHSigma` gives, for each FIXED `g = cosineCoeffs (u τ)`,
  `MemHSigma σ (cosineCoeffs ((1+v τ)^{−β}))` — per-τ MEMBERSHIP only, NOT a
  domination of `cosineCoeffs ((1+v τ)^{−β})` by a single τ-free sequence.  The
  τ-uniform denominator envelope `Gdenσ` (a single `H^σ` sequence dominating
  `cosineCoeffs ((1+v τ)^{−β})` over ALL `τ ∈ [0,t]`) is the genuine residual: it
  needs a τ-UNIFORM second-derivative integral bound
  `∫₀¹ |((1+v τ)^{−β})''| ≤ B` (feeding the `n^{−2}`-decay route
  `cosineCoeffs_decay_two`), a quantitative NONLINEAR-composition C² estimate (Faà
  di Bruno on the bounded-base `(1+·)^{−β}` composed with `v τ`, controlled by the
  τ-uniform `H^{σ+2}` resolver envelope `resolverCoeff 1 Uσ`).  That composition
  estimate is NOT landed.  It is isolated below as the abstract structure
  `DenomUniformEnvelope`, and the `n^{−2}`-decay constructor
  `denomUniformEnvelope_of_secondDerivBound` reduces it to exactly that single
  scalar bound `B` plus a uniform mode-0 bound `A`.  This is a REAL analytic gap,
  NOT a circularity, and STRICTLY upstream of any classical-existence object.

  ## NON-CIRCULARITY

  Imports ONLY `IntervalFluxFactorEnvelope` (→ `IntervalTrajectoryEnvelope` → mild
  engine) and `IntervalDenomEnvelopeResolver` (the C²-via-resolver denom env, itself
  non-circular).  NEVER references `localClassicalSolution`,
  `IsPaper2ClassicalSolution`, the C²-Neumann producers, or the PID-classical
  bridge.  `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.
-/
import ShenWork.Paper2.IntervalFluxFactorEnvelope
import ShenWork.Paper2.IntervalDenomEnvelopeResolver

noncomputable section

namespace ShenWork.Paper2.IntervalGWProductEnvelope

open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma resolverCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.Paper2.IntervalEnvelopeProp (Envelopes envelopes_trueCosProd)
open ShenWork.Paper2.IntervalMixedProduct (MixedMulBridge)
open ShenWork.Paper2.IntervalWienerAlgebra
  (trueCosProd memHSigma_trueCosProd_of_gt_half CosineMulBridge
   cosineCoeffs_mul_eq_trueCosProd memHSigma_of_coeff_decay)
open ShenWork.Paper2.IntervalTrajectoryEnvelope
  (TrajectoryHSigmaEnvelope FluxFactorEnvelopes)
open ShenWork.Paper2.IntervalFluxFactorEnvelope (sineEnv)

/-! ## The τ-uniform denominator envelope (the precise residual structure). -/

/-- **`DenomUniformEnvelope σ t W₂`** — a SINGLE `H^σ` sequence `Gden` dominating
the cosine coefficients of the τ-snapshot denominator `W₂ τ = (1+v τ)^{−β}`
UNIFORMLY over `τ ∈ [0,t]`.

This is exactly the τ-uniform analogue of the landed per-τ
`denom_envelope_memHSigma` (which gives only `MemHSigma σ (cosineCoeffs (W₂ τ))`
for each fixed `τ`).  Producing it requires a τ-uniform second-derivative
integral bound on the composition `(1+v τ)^{−β}` (see header / the constructor
below); it is isolated here as the precise #1E residual. -/
structure DenomUniformEnvelope (σ t : ℝ) (W₂ : ℝ → ℝ → ℝ) where
  Gden : ℕ → ℝ
  hGden : MemHSigma σ Gden
  hdom : ∀ τ ∈ Set.Icc (0:ℝ) t, Envelopes Gden (cosineCoeffs (W₂ τ))

/-! ## The `n^{−2}`-decay constructor — reducing the residual to one scalar bound.

The `DenomUniformEnvelope` is producible from the landed `n^{−2}`-decay route the
moment a τ-uniform `∫₀¹|f''|` bound `B` (and a uniform mode-0 bound `A`) is
supplied: take `Gden 0 := A`, `Gden n := (2/π²·B)/n²` for `n ≥ 1`. -/

/-- The explicit `n^{−2}`-decay denominator envelope sequence: `A` at mode `0`,
`(2/π²·B)/n²` for `n ≥ 1`.  A single τ-free sequence. -/
def denomDecaySeq (A B : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then A else (2 / Real.pi ^ 2 * B) / (n : ℝ) ^ 2

theorem denomDecaySeq_memHSigma {σ A B : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 3 / 2)
    (hB0 : 0 ≤ B) :
    MemHSigma σ (denomDecaySeq A B) := by
  refine memHSigma_of_coeff_decay
    (q := 2) (C := 2 / Real.pi ^ 2 * B) hσ0 (by linarith) (fun n hn => ?_)
  have hn0 : n ≠ 0 := by omega
  have hnp : (0:ℝ) < (n:ℝ) := by positivity
  rw [show (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ (2 : ℕ) from Real.rpow_natCast (n : ℝ) 2,
    denomDecaySeq, if_neg hn0]
  have hpos : (0:ℝ) ≤ 2 / Real.pi ^ 2 * B / (n : ℝ) ^ 2 := by positivity
  rw [abs_of_nonneg hpos]

/-- **Decay-route constructor of the τ-uniform denominator envelope.**  Given a
τ-uniform second-derivative integral bound `B` (`∀τ, ∀n≥1,
|cosineCoeffs (W₂ τ) n| ≤ (2/π²·B)/n²` — the output of `cosineCoeffs_decay_two`
under a τ-uniform `∫|f''| ≤ B`) and a uniform mode-0 bound `A`
(`∀τ, |cosineCoeffs (W₂ τ) 0| ≤ A`), the `denomDecaySeq A B` IS a
`DenomUniformEnvelope`.  Reduces #1E's residual to exactly `(A, B)`. -/
def denomUniformEnvelope_of_secondDerivBound {σ t : ℝ} (hσ0 : 0 ≤ σ)
    (hσ1 : σ < 3 / 2) {W₂ : ℝ → ℝ → ℝ} {A B : ℝ} (hB0 : 0 ≤ B)
    (hA : ∀ τ ∈ Set.Icc (0:ℝ) t, |cosineCoeffs (W₂ τ) 0| ≤ A)
    (hB : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ n : ℕ, 1 ≤ n →
      |cosineCoeffs (W₂ τ) n| ≤ (2 / Real.pi ^ 2 * B) / (n : ℝ) ^ 2) :
    DenomUniformEnvelope σ t W₂ where
  Gden := denomDecaySeq A B
  hGden := denomDecaySeq_memHSigma hσ0 hσ1 hB0
  hdom := by
    intro τ hτ k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [denomDecaySeq, if_pos rfl]; exact hA τ hτ
    · have hkne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
      rw [denomDecaySeq, if_neg hkne]
      exact hB τ hτ k hk

/-! ## The weight product envelope `gW = trueCosProd Uσ Gden`. -/

/-- **`gW`** — the cosine envelope of the chemotaxis weight `W = u·(1+v)^{−β}`,
the exact product operator on the trajectory envelope `Uσ` and the denominator
envelope `Gden`. -/
def gW (Uσ Gden : ℕ → ℝ) : ℕ → ℝ := trueCosProd Uσ Gden

/-- **`gW ∈ H^σ` UNCONDITIONALLY** (σ > 1/2).  From the trajectory envelope
membership and the denominator envelope membership, by the H^σ Banach-algebra
closure of `trueCosProd`. -/
theorem gW_memHSigma {σ : ℝ} (hσ : 1 / 2 < σ) {Uσ Gden : ℕ → ℝ}
    (hU : MemHSigma σ Uσ) (hG : MemHSigma σ Gden) :
    MemHSigma σ (gW Uσ Gden) :=
  memHSigma_trueCosProd_of_gt_half hσ hU hG

/-- **`gW` τ-uniform domination.**  For a fixed `τ` with the cosine bridge
`CosineMulBridge (u τ) ((1+v τ)^{−β})` and the factor envelopes `Uσ ⊵ cosineCoeffs (u τ)`,
`Gden ⊵ cosineCoeffs ((1+v τ)^{−β})`, the single sequence `gW Uσ Gden` envelopes
`cosineCoeffs (W τ)` where `W τ = (u τ)·((1+v τ)^{−β})`.  Pure envelope-monotone
product. -/
theorem gW_envelopes_of_bridge {σ : ℝ} (hσ : 1 / 2 < σ) {Uσ Gden : ℕ → ℝ}
    (hU : MemHSigma σ Uσ) (hG : MemHSigma σ Gden)
    {uf w₂f : ℝ → ℝ}
    (hbr : CosineMulBridge uf w₂f)
    (heU : Envelopes Uσ (cosineCoeffs uf))
    (heG : Envelopes Gden (cosineCoeffs w₂f)) :
    Envelopes (gW Uσ Gden) (cosineCoeffs (fun x => uf x * w₂f x)) := by
  rw [gW, cosineCoeffs_mul_eq_trueCosProd hbr]
  exact envelopes_trueCosProd hσ hU hG heU heG

/-! ## ASSEMBLY — the full `FluxFactorEnvelopes` from `Uσ` + `DenomUniformEnvelope`.

The chemotaxis flux `Q τ = W τ · vx τ`, with the COSINE weight envelope
`gW := trueCosProd Uσ Gden` (built here, no carried hypothesis) and the SINE
resolver-relay envelope `gvx := sineEnv Uσ` (the landed unconditional piece),
yields the full factor package and the flux H^σ envelope `genv`. -/

/-- **The full `FluxFactorEnvelopes`, `gW` NO LONGER carried.**  From the
trajectory envelope `Uσ`, the τ-uniform denominator envelope `D`, the per-τ cosine
bridge + factor matching, the mixed bridge, and the resolver/divergence sine data,
assemble `FluxFactorEnvelopes σ t Q` with cosine weight `gW = trueCosProd Uσ D.Gden`
built — not assumed. -/
@[reducible] def fluxFactorEnvelopes_of_traj_denom {σ t : ℝ} (hσ : 1 / 2 < σ)
    {Uσ : ℕ → ℝ} (hU : MemHSigma σ Uσ)
    {Q W vx : ℝ → ℝ → ℝ} {u v w₂ : ℝ → ℝ → ℝ}
    (D : DenomUniformEnvelope σ t w₂)
    (hQ : ∀ τ, Q τ = fun x => W τ x * vx τ x)
    (hWdef : ∀ τ, W τ = fun x => u τ x * w₂ τ x)
    (hbr : ∀ τ ∈ Set.Icc (0:ℝ) t, CosineMulBridge (u τ) (w₂ τ))
    (heU : ∀ τ ∈ Set.Icc (0:ℝ) t, Envelopes Uσ (cosineCoeffs (u τ)))
    (hbridge : ∀ τ ∈ Set.Icc (0:ℝ) t, MixedMulBridge (W τ) (vx τ))
    (hvrel : ∀ τ ∈ Set.Icc (0:ℝ) t,
      Envelopes (resolverCoeff 1 Uσ) (cosineCoeffs (v τ)))
    (hdiv : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
      |sineCoeffs (vx τ) k| = Real.sqrt (lam k) * |cosineCoeffs (v τ) k|) :
    FluxFactorEnvelopes σ t Q where
  W := W
  vx := vx
  gW := gW Uσ D.Gden
  gvx := sineEnv Uσ
  hQ := hQ
  hgW := gW_memHSigma hσ hU D.hGden
  hgvx := ShenWork.Paper2.IntervalFluxFactorEnvelope.sineEnv_memHSigma hU
  hbridge := hbridge
  heW := by
    intro τ hτ
    have hWeq : cosineCoeffs (W τ) = cosineCoeffs (fun x => u τ x * w₂ τ x) := by
      rw [hWdef τ]
    rw [hWeq]
    exact gW_envelopes_of_bridge hσ hU D.hGden (hbr τ hτ) (heU τ hτ) (D.hdom τ hτ)
  hevx := fun τ hτ =>
    ShenWork.Paper2.IntervalFluxFactorEnvelope.sineEnv_envelopes (hvrel τ hτ) (hdiv τ hτ)

/-- **The flux H^σ envelope `genv`, chained — `gW` BUILT (not carried).**  For
σ > 1/2, the assembled package yields `genv := trueCosProd (gW Uσ D.Gden) (sineEnv Uσ)`:
it lies in `H^σ` and dominates `|sineCoeffs (Q τ) k|` τ-uniformly over `[0,t]`.
This closes the `(genv σ, hg, hg_dom σ)` triple of `SliceMildStepData` from the
trajectory envelope + the τ-uniform denominator envelope — NO carried `gW`. -/
theorem genv_of_traj_denom {σ t : ℝ} (hσ : 1 / 2 < σ)
    {Uσ : ℕ → ℝ} (hU : MemHSigma σ Uσ)
    {Q W vx : ℝ → ℝ → ℝ} {u v w₂ : ℝ → ℝ → ℝ}
    (D : DenomUniformEnvelope σ t w₂)
    (hQ : ∀ τ, Q τ = fun x => W τ x * vx τ x)
    (hWdef : ∀ τ, W τ = fun x => u τ x * w₂ τ x)
    (hbr : ∀ τ ∈ Set.Icc (0:ℝ) t, CosineMulBridge (u τ) (w₂ τ))
    (heU : ∀ τ ∈ Set.Icc (0:ℝ) t, Envelopes Uσ (cosineCoeffs (u τ)))
    (hbridge : ∀ τ ∈ Set.Icc (0:ℝ) t, MixedMulBridge (W τ) (vx τ))
    (hvrel : ∀ τ ∈ Set.Icc (0:ℝ) t,
      Envelopes (resolverCoeff 1 Uσ) (cosineCoeffs (v τ)))
    (hdiv : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
      |sineCoeffs (vx τ) k| = Real.sqrt (lam k) * |cosineCoeffs (v τ) k|) :
    MemHSigma σ (trueCosProd (gW Uσ D.Gden) (sineEnv Uσ)) ∧
      ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
        |sineCoeffs (Q τ) k| ≤ trueCosProd (gW Uσ D.Gden) (sineEnv Uσ) k := by
  -- Build the package literal so its `.gW`/`.gvx` ARE `gW Uσ D.Gden`/`sineEnv Uσ`.
  let F : FluxFactorEnvelopes σ t Q :=
    { W := W, vx := vx, gW := gW Uσ D.Gden, gvx := sineEnv Uσ, hQ := hQ,
      hgW := gW_memHSigma hσ hU D.hGden,
      hgvx := ShenWork.Paper2.IntervalFluxFactorEnvelope.sineEnv_memHSigma hU,
      hbridge := hbridge,
      heW := by
        intro τ hτ
        have hWeq : cosineCoeffs (W τ) = cosineCoeffs (fun x => u τ x * w₂ τ x) := by
          rw [hWdef τ]
        rw [hWeq]
        exact gW_envelopes_of_bridge hσ hU D.hGden (hbr τ hτ) (heU τ hτ) (D.hdom τ hτ),
      hevx := fun τ hτ =>
        ShenWork.Paper2.IntervalFluxFactorEnvelope.sineEnv_envelopes
          (hvrel τ hτ) (hdiv τ hτ) }
  exact ShenWork.Paper2.IntervalTrajectoryEnvelope.fluxEnvelope_of_factorEnvelopes hσ F

end ShenWork.Paper2.IntervalGWProductEnvelope

namespace ShenWork.Paper2.IntervalGWProductEnvelope
#print axioms denomDecaySeq_memHSigma
#print axioms denomUniformEnvelope_of_secondDerivBound
#print axioms gW_memHSigma
#print axioms gW_envelopes_of_bridge
#print axioms fluxFactorEnvelopes_of_traj_denom
#print axioms genv_of_traj_denom
end ShenWork.Paper2.IntervalGWProductEnvelope
