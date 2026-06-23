/-
  ShenWork/Paper2/IntervalFluxFactorEnvelope.lean

  CONSTRUCTING `FluxFactorEnvelopes σ t Q` from a `TrajectoryHSigmaEnvelope σ t u`
  — the envelope-algebra "wiring given Uσ" step of the χ₀<0 regularity ladder
  (route file `ANALYSIS_traj_envelope.md`).

  ## What this file delivers

  * UNCONDITIONAL (the resolver-relay sub-piece `gvx`).  From a τ-uniform cosine
    envelope `Uσ` of the solution trajectory `u` (a `TrajectoryHSigmaEnvelope σ t u`),
    the SINE envelope of `v_x` is the SINGLE sequence
        `sineEnv Uσ k := √(lam k) · (Uσ k / (1 + lam k))`
    (`= √λ · resolverCoeff 1 Uσ`, since `v` solves the Neumann resolver
    `(-∂ₓₓ+1)v = u`, so `cosineCoeffs (v τ) = Uσ / (1+λ)`, and the divergence-mode
    identity gives `sineCoeffs (v_x τ) = ±√λ · cosineCoeffs (v τ)`).  This sequence
    lies in `H^σ` (`sineEnv_memHSigma`) PURELY from `MemHSigma σ Uσ` via the
    multiplier bound `λ/(1+λ)² ≤ 1` — NO classical regularity.  It envelopes the
    sine coeffs of any `v_x` whose modes match the resolver relay
    (`sineEnv_envelopes`).

  * CONDITIONAL on one explicit residual.  The chemotaxis weight `W = u·(1+v)^{−β}`
    needs a COSINE `H^σ` envelope `gW` of `(1+v)^{−β}`-composed `W`.  The ONLY
    landed `(1+v)^{−β}` `H^σ` envelope in the repo (`IntervalCkComposition.
    memHSigma_one_add_rpow_neg_of_contDiff_two`) requires `ContDiff ℝ 2 v` —
    classical C² regularity, which is FORBIDDEN here (circular w.r.t. the very
    regularity being bootstrapped).  No bounded-range Nemytskii / Wiener `H^σ`
    composition envelope for `(1+v)^{−β}` from `v`'s `H^σ` envelope alone is landed.
    So `gW` (+ its τ-uniform cosine envelope + mixed bridge) is carried as an
    EXPLICIT hypothesis.  This is a REAL analytic gap (denominator composition),
    NOT a circularity introduced by this file.

  * ASSEMBLY.  `fluxFactorEnvelopes_of_trajectoryEnvelope` assembles a full
    `FluxFactorEnvelopes σ t Q` from `Uσ` + the carried `gW` data + the per-τ
    resolver/divergence matching, and `genv_of_trajectoryEnvelope` chains it to the
    flux `H^σ` envelope `genv := trueCosProd gW (sineEnv Uσ)` via the landed
    `fluxEnvelope_of_factorEnvelopes`.

  ## NON-CIRCULARITY

  Imports ONLY `IntervalTrajectoryEnvelope` (which imports the mild engine inputs).
  NEVER references `localClassicalSolution`, `IsPaper2ClassicalSolution`, the
  C²-Neumann producers, or the PID-classical bridge.  `#print axioms` ⊆
  `{propext, Classical.choice, Quot.sound}`.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.
-/
import ShenWork.Paper2.IntervalTrajectoryEnvelope

noncomputable section

namespace ShenWork.Paper2.IntervalFluxFactorEnvelope

open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale
  (lam MemHSigma one_add_lam_pos lam_nonneg resolverCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs sqrt_lam_eq_kpi)
open ShenWork.Paper2.IntervalEnvelopeProp (Envelopes envelopes_resolver)
open ShenWork.Paper2.IntervalMixedProduct (MixedMulBridge)
open ShenWork.Paper2.IntervalWienerAlgebra (trueCosProd)
open ShenWork.Paper2.IntervalTrajectoryEnvelope
  (TrajectoryHSigmaEnvelope FluxFactorEnvelopes fluxEnvelope_of_factorEnvelopes)

/-! ## The resolver-relay SINE envelope `sineEnv` of `v_x` (UNCONDITIONAL). -/

/-- The sine envelope of `v_x` induced by the cosine envelope `Uσ` of `u`:
`sineEnv Uσ k = √(lam k) · resolverCoeff 1 Uσ k = √(lam k) · Uσ k / (1 + lam k)`.

`v` solves the Neumann resolver `(-∂ₓₓ+1)v = u`, so `cosineCoeffs (v) k = u_k/(1+λ_k)`
(`= resolverCoeff 1 Uσ` at the envelope level); the divergence-mode identity gives
`sineCoeffs (v_x) k = ±√(lam k) · cosineCoeffs (v) k`. -/
def sineEnv (Uσ : ℕ → ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (lam k) * resolverCoeff 1 Uσ k

theorem sineEnv_nonneg {Uσ : ℕ → ℝ} (hU0 : ∀ k, 0 ≤ Uσ k) (k : ℕ) :
    0 ≤ sineEnv Uσ k := by
  unfold sineEnv resolverCoeff
  have hden : (0 : ℝ) < 1 + lam k := one_add_lam_pos k
  have hsqrt : 0 ≤ Real.sqrt (lam k) := Real.sqrt_nonneg _
  have := hU0 k
  positivity

/-- The per-mode multiplier bound `λ_k / (1 + λ_k)² ≤ 1`: since `λ ≥ 0`,
`λ ≤ 1 + 2λ + λ² = (1 + λ)²`. -/
theorem lam_div_one_add_sq_le_one (k : ℕ) :
    lam k / (1 + lam k) ^ 2 ≤ 1 := by
  have hlam := lam_nonneg k
  have hpos : (0 : ℝ) < (1 + lam k) ^ 2 := by positivity
  rw [div_le_one hpos]; nlinarith [hlam]

/-- The `H^σ` weighted square of `sineEnv` is dominated by that of `Uσ`:
`(1+λ_k)^σ (sineEnv Uσ k)² ≤ (1+λ_k)^σ (Uσ k)²`, using `λ/(1+λ)² ≤ 1`. -/
theorem sineEnv_weighted_sq_le (σ : ℝ) (Uσ : ℕ → ℝ) (k : ℕ) :
    (1 + lam k) ^ σ * (sineEnv Uσ k) ^ 2 ≤ (1 + lam k) ^ σ * (Uσ k) ^ 2 := by
  have hpos : (0 : ℝ) < 1 + lam k := one_add_lam_pos k
  have hw : (0 : ℝ) ≤ (1 + lam k) ^ σ := (Real.rpow_nonneg hpos.le σ)
  have hlam := lam_nonneg k
  have hsqrt_sq : (Real.sqrt (lam k)) ^ 2 = lam k := Real.sq_sqrt hlam
  -- (sineEnv)² = lam · (Uσ)² / (1+λ)²
  have hden : (0 : ℝ) < (1 + lam k) ^ 2 := by positivity
  have hsq : (sineEnv Uσ k) ^ 2 = lam k * (Uσ k) ^ 2 / (1 + lam k) ^ 2 := by
    unfold sineEnv resolverCoeff
    rw [mul_pow, hsqrt_sq, div_pow, mul_div_assoc]
  rw [hsq]
  -- reduce to lam/(1+λ)² ≤ 1 scaled by (1+λ)^σ (Uσ)² ≥ 0
  have hmul := lam_div_one_add_sq_le_one k
  have heq : (1 + lam k) ^ σ * (lam k * (Uσ k) ^ 2 / (1 + lam k) ^ 2)
      = ((1 + lam k) ^ σ * (Uσ k) ^ 2) * (lam k / (1 + lam k) ^ 2) := by
    field_simp
  rw [heq]
  calc
    ((1 + lam k) ^ σ * (Uσ k) ^ 2) * (lam k / (1 + lam k) ^ 2)
        ≤ ((1 + lam k) ^ σ * (Uσ k) ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = (1 + lam k) ^ σ * (Uσ k) ^ 2 := by ring

/-- **UNCONDITIONAL — the resolver-relay membership.**  If the trajectory cosine
envelope `Uσ ∈ H^σ`, then the induced `v_x` sine envelope `sineEnv Uσ ∈ H^σ`.
Pure comparison via the multiplier bound `λ/(1+λ)² ≤ 1`; NO classical regularity. -/
theorem sineEnv_memHSigma {σ : ℝ} {Uσ : ℕ → ℝ} (hU : MemHSigma σ Uσ) :
    MemHSigma σ (sineEnv Uσ) := by
  have hnonneg : ∀ k, 0 ≤ (1 + lam k) ^ σ * (sineEnv Uσ k) ^ 2 := by
    intro k
    have := Real.rpow_nonneg (one_add_lam_pos k).le σ
    positivity
  exact Summable.of_nonneg_of_le hnonneg (fun k => sineEnv_weighted_sq_le σ Uσ k) hU

/-- **UNCONDITIONAL — the resolver-relay membership, directly from `E`.**  The
`v_x` sine envelope `sineEnv E.env` lies in `H^σ`, built from the trajectory
envelope's own sequence `E.env` — no extra hypothesis, no classical regularity. -/
theorem sineEnv_memHSigma_of_traj {σ t : ℝ} {u : ℝ → ℕ → ℝ}
    (E : TrajectoryHSigmaEnvelope σ t u) : MemHSigma σ (sineEnv E.env) :=
  sineEnv_memHSigma E.henv

/-- **UNCONDITIONAL — the resolver-relay envelope.**  Suppose the trajectory
envelope `Uσ` dominates the cosine coeffs of the resolver `v τ` (i.e. of `u τ`
through the relay), and `v_x τ` satisfies the divergence-mode identity
`sineCoeffs (vx τ) k = ±√(lam k) · cosineCoeffs (v τ) k`.  Then `sineEnv Uσ`
envelopes `sineCoeffs (vx τ)` pointwise.

Concretely: with `hvrel : Envelopes (resolverCoeff 1 Uσ) (cosineCoeffs (v τ))`
(the resolver relay applied to `Uσ` dominating `v`'s cosine coeffs) and the
identity `|sineCoeffs (vx τ) k| = √(lam k) · |cosineCoeffs (v τ) k|`. -/
theorem sineEnv_envelopes {Uσ : ℕ → ℝ} {v vx : ℝ → ℝ}
    (hvrel : Envelopes (resolverCoeff 1 Uσ) (cosineCoeffs v))
    (hdiv : ∀ k, |sineCoeffs vx k| = Real.sqrt (lam k) * |cosineCoeffs v k|) :
    Envelopes (sineEnv Uσ) (sineCoeffs vx) := by
  intro k
  rw [hdiv k]
  unfold sineEnv
  have hsqrt : 0 ≤ Real.sqrt (lam k) := Real.sqrt_nonneg _
  exact mul_le_mul_of_nonneg_left (hvrel k) hsqrt

/-! ## ASSEMBLY — `FluxFactorEnvelopes` from `Uσ` + the carried `gW` residual.

The cosine weight envelope `gW` of `W = u·(1+v)^{−β}` is the genuine residual:
the only landed `(1+v)^{−β}` `H^σ` envelope needs `ContDiff ℝ 2 v` (forbidden), so
`gW`, its `H^σ` membership, its τ-uniform cosine envelope, and the per-τ mixed
bridge are carried as explicit hypotheses.  `gvx := sineEnv Uσ` is produced
unconditionally from `Uσ`. -/

/-- **ASSEMBLY (conditional on the denominator residual `gW`).**  From:
* a τ-uniform cosine trajectory envelope `Uσ` of `u` (a `TrajectoryHSigmaEnvelope`);
* the carried weight data `W`, `gW` with `MemHSigma σ gW` and the τ-uniform cosine
  envelope `heW` of `cosineCoeffs (W τ)` (the `(1+v)^{−β}` denominator residual);
* the chemotaxis factorisation `Q τ = W τ · vx τ` and the per-τ mixed bridge;
* the resolver/divergence matching giving `gvx := sineEnv Uσ` as a τ-uniform sine
  envelope of `v_x`,
produce a full `FluxFactorEnvelopes σ t Q` with `gvx = sineEnv Uσ` built from `Uσ`. -/
@[reducible] def fluxFactorEnvelopes_of_trajectoryEnvelope {σ t : ℝ}
    {u : ℝ → ℕ → ℝ} (_E : TrajectoryHSigmaEnvelope σ t u)
    {Uσ : ℕ → ℝ} (hU : MemHSigma σ Uσ)
    {Q W vx : ℝ → ℝ → ℝ} {v : ℝ → ℝ → ℝ}
    (hQ : ∀ τ, Q τ = fun x => W τ x * vx τ x)
    {gW : ℕ → ℝ} (hgW : MemHSigma σ gW)
    (hbridge : ∀ τ ∈ Set.Icc (0:ℝ) t, MixedMulBridge (W τ) (vx τ))
    (heW : ∀ τ ∈ Set.Icc (0:ℝ) t, Envelopes gW (cosineCoeffs (W τ)))
    (hvrel : ∀ τ ∈ Set.Icc (0:ℝ) t,
      Envelopes (resolverCoeff 1 Uσ) (cosineCoeffs (v τ)))
    (hdiv : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
      |sineCoeffs (vx τ) k| = Real.sqrt (lam k) * |cosineCoeffs (v τ) k|) :
    FluxFactorEnvelopes σ t Q where
  W := W
  vx := vx
  gW := gW
  gvx := sineEnv Uσ
  hQ := hQ
  hgW := hgW
  hgvx := sineEnv_memHSigma hU
  hbridge := hbridge
  heW := heW
  hevx := fun τ hτ => sineEnv_envelopes (hvrel τ hτ) (hdiv τ hτ)

/-- **The flux `H^σ` envelope `genv`, chained.**  For `σ > 1/2`, the assembled
`FluxFactorEnvelopes` yields the `genv := trueCosProd gW (sineEnv Uσ)` flux
envelope: it lies in `H^σ` and dominates `|sineCoeffs (Q τ) k|` τ-uniformly. -/
theorem genv_of_trajectoryEnvelope {σ t : ℝ} (hσ : 1 / 2 < σ)
    {u : ℝ → ℕ → ℝ} (_E : TrajectoryHSigmaEnvelope σ t u)
    {Uσ : ℕ → ℝ} (hU : MemHSigma σ Uσ)
    {Q W vx : ℝ → ℝ → ℝ} {v : ℝ → ℝ → ℝ}
    (hQ : ∀ τ, Q τ = fun x => W τ x * vx τ x)
    {gW : ℕ → ℝ} (hgW : MemHSigma σ gW)
    (hbridge : ∀ τ ∈ Set.Icc (0:ℝ) t, MixedMulBridge (W τ) (vx τ))
    (heW : ∀ τ ∈ Set.Icc (0:ℝ) t, Envelopes gW (cosineCoeffs (W τ)))
    (hvrel : ∀ τ ∈ Set.Icc (0:ℝ) t,
      Envelopes (resolverCoeff 1 Uσ) (cosineCoeffs (v τ)))
    (hdiv : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
      |sineCoeffs (vx τ) k| = Real.sqrt (lam k) * |cosineCoeffs (v τ) k|) :
    MemHSigma σ (trueCosProd gW (sineEnv Uσ)) ∧
      ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ k,
        |sineCoeffs (Q τ) k| ≤ trueCosProd gW (sineEnv Uσ) k := by
  -- Build the factor package literal so its `.gW`/`.gvx` ARE `gW`/`sineEnv Uσ`.
  let F : FluxFactorEnvelopes σ t Q :=
    { W := W, vx := vx, gW := gW, gvx := sineEnv Uσ, hQ := hQ, hgW := hgW,
      hgvx := sineEnv_memHSigma hU, hbridge := hbridge, heW := heW,
      hevx := fun τ hτ => sineEnv_envelopes (hvrel τ hτ) (hdiv τ hτ) }
  exact fluxEnvelope_of_factorEnvelopes hσ F

end ShenWork.Paper2.IntervalFluxFactorEnvelope

namespace ShenWork.Paper2.IntervalFluxFactorEnvelope
#print axioms sineEnv_memHSigma
#print axioms sineEnv_memHSigma_of_traj
#print axioms sineEnv_envelopes
#print axioms lam_div_one_add_sq_le_one
#print axioms fluxFactorEnvelopes_of_trajectoryEnvelope
#print axioms genv_of_trajectoryEnvelope
end ShenWork.Paper2.IntervalFluxFactorEnvelope
