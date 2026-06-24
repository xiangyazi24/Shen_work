/-
  ShenWork/Wiener/EWA/SourcePowerCoeffDeriv.lean

  **χ₀<0 — K1(i): the power-source `ν·u^γ` cosine-coefficient time-derivative,
  past the `whnf`/`isDefEq` structural wall.**

  Target (the sole obligation of this file):

      K1(i):  ∀ σ ∈ Ioo 0 T, ∀ k,
        HasDerivAt
          (fun r => cosineCoeffs
            (fun x => p.ν * (intervalDomainLift (realSlice u_star r) x) ^ p.γ) k)
          (adotPow p (realSlice u_star) vdotL σ k) σ

  with the explicit derivative coefficient

      adotPow p v vdotL σ k :=
        cosineCoeffs
          (fun x => p.ν * p.γ * (intervalDomainLift (v σ) x) ^ (p.γ - 1) * vdotL σ x) k.

  ## The structural defeq wall and how this file blocks it

  Two prior producers timed out at `(deterministic) timeout at whnf` / `isDefEq`
  on the IDENTICAL line, even at `maxHeartbeats 1000000`: when the integral-swap
  engine `cosineCoeffs_hasDerivAt_of_smooth_param` is applied with
  `f := fun r x => p.ν · (intervalDomainLift (realSlice u_star r) x) ^ p.γ`, Lean
  tries to `whnf`-reduce `realSlice u_star`, whose `evalST`/Wiener point-evaluation
  unfolding never terminates.  `maxHeartbeats` does NOT fix this — the reduction is
  non-terminating, not merely slow.

  The fix (the whole point) is to BLOCK the unfolding, not to raise heartbeats:

  1. **Opaque integrand.**  `realSlice u_star` is consumed only through an
     ABSTRACT variable `v : ℝ → intervalDomainPoint → ℝ`.  Every analytic input
     (pointwise time-derivative, positivity, per-slice/joint continuity) is taken
     as an explicit hypothesis ABOUT `v` — never extracted by unfolding the EWA
     structure inside this file.  The K1(i) statement then instantiates `v` to
     `realSlice u_star` at the very end, *after* the engine has already run on the
     opaque `v`, so the engine never `whnf`s the EWA term.
  2. **`attribute [local irreducible] realSlice`** at the top of the section
     forbids any residual unfolding even at the instantiation boundary.
  3. **`show <pinned goal type>`** before the final `exact` so elaboration matches
     syntactically, not via a defeq search into the EWA structure.
  4. The pointwise chain rule uses `HasDerivAt.rpow_const` with the POSITIVITY
     branch `Or.inl (ne_of_gt …)` and the exponent `p.γ` passed EXPLICITLY
     (`(p := p.γ)`) so unification is forced — the prior implicit-synthesis failure.
  5. `maxHeartbeats` raise is a backstop ONLY, on its own line, after the barriers.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceClassicalExistence
import ShenWork.Paper2.IntervalMildPicardRegularity

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

noncomputable section

namespace ShenWork.EWA

-- BLOCK the whnf/isDefEq wall: `realSlice` must never unfold inside this section.
attribute [local irreducible] realSlice

/-! ### The explicit power-source derivative coefficient `adotPow`.

`adotPow p v vdotL σ k` is the `k`-th cosine coefficient of the chain-rule
integrand `x ↦ ν·γ·(lift (v σ) x)^{γ−1} · vdotL σ x`, where `vdotL σ x` is the
pointwise time-derivative of the *lifted* slice `r ↦ intervalDomainLift (v r) x`.
It is the value the K1(i) `HasDerivAt` carries. -/
def adotPow (p : CM2Params) (v : ℝ → intervalDomainPoint → ℝ)
    (vdotL : ℝ → ℝ → ℝ) (σ : ℝ) (k : ℕ) : ℝ :=
  cosineCoeffs
    (fun x => p.ν * p.γ * (intervalDomainLift (v σ) x) ^ (p.γ - 1) * vdotL σ x) k

/-! ### Pointwise chain rule for the power source (opaque `v`).

`d/dr [ν·(lift (v r) x)^γ] = ν·γ·(lift (v r) x)^{γ−1}·vdotL r x`, from the banked
pointwise time-derivative of the lifted slice and the slice positivity, via
`HasDerivAt.rpow_const` (positivity branch, exponent explicit). -/
theorem hasDerivAt_powerLiftSlice {p : CM2Params}
    {v : ℝ → intervalDomainPoint → ℝ} {vdotL : ℝ → ℝ → ℝ} {x : ℝ} {r : ℝ}
    (hslice : HasDerivAt (fun s => intervalDomainLift (v s) x) (vdotL r x) r)
    (hpos : 0 < intervalDomainLift (v r) x) :
    HasDerivAt (fun s => p.ν * (intervalDomainLift (v s) x) ^ p.γ)
      (p.ν * p.γ * (intervalDomainLift (v r) x) ^ (p.γ - 1) * vdotL r x) r := by
  -- d/dr (lift v r x)^γ = vdotL · γ · (lift v r x)^{γ−1}  (exponent EXPLICIT).
  have hpow : HasDerivAt (fun s => (intervalDomainLift (v s) x) ^ p.γ)
      (vdotL r x * p.γ * (intervalDomainLift (v r) x) ^ (p.γ - 1)) r :=
    hslice.rpow_const (p := p.γ) (Or.inl (ne_of_gt hpos))
  have hmul := hpow.const_mul p.ν
  refine hmul.congr_deriv ?_
  ring

/-! ### K1(i) over the OPAQUE `v`.

The integral-swap engine `cosineCoeffs_hasDerivAt_of_smooth_param` is applied with
the integrand built from the abstract `v`; it never sees the EWA structure.  All
four engine hypotheses are supplied as explicit inputs about `v`. -/
set_option maxHeartbeats 800000 in
-- Backstop only: the opaque-`v` + `[local irreducible] realSlice` barriers already
-- defuse the `whnf`/`isDefEq` non-termination; this raise is defensive headroom.
theorem hasDerivAt_powerCoeff_of_inputs {p : CM2Params}
    {v : ℝ → intervalDomainPoint → ℝ} {vdotL : ℝ → ℝ → ℝ} {σ δ : ℝ} (k : ℕ)
    (hδ : 0 < δ)
    (hf_cont : ∀ᶠ s in 𝓝 σ,
      ContinuousOn (fun x => p.ν * (intervalDomainLift (v s) x) ^ p.γ)
        (Set.Icc (0 : ℝ) 1))
    (hslice : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball σ δ,
      HasDerivAt (fun r => intervalDomainLift (v r) x) (vdotL s x) s)
    (hpos : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball σ δ,
      0 < intervalDomainLift (v s) x)
    (hderivcont : ContinuousOn
      (Function.uncurry
        (fun s x => p.ν * p.γ * (intervalDomainLift (v s) x) ^ (p.γ - 1) * vdotL s x))
      (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasDerivAt
      (fun r => cosineCoeffs
        (fun x => p.ν * (intervalDomainLift (v r) x) ^ p.γ) k)
      (adotPow p v vdotL σ k) σ := by
  -- pointwise HasDerivAt of the integrand from the chain rule on the ball.
  have h_diff : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball σ δ,
      HasDerivAt (fun r => p.ν * (intervalDomainLift (v r) x) ^ p.γ)
        (p.ν * p.γ * (intervalDomainLift (v s) x) ^ (p.γ - 1) * vdotL s x) s :=
    fun x hx s hs => hasDerivAt_powerLiftSlice (hslice x hx s hs) (hpos x hx s hs)
  -- the engine's derivative target is `cosineCoeffs (f' σ) k = adotPow … σ k`.
  change HasDerivAt
      (fun r => cosineCoeffs
        (fun x => p.ν * (intervalDomainLift (v r) x) ^ p.γ) k)
      (cosineCoeffs
        (fun x => p.ν * p.γ * (intervalDomainLift (v σ) x) ^ (p.γ - 1) * vdotL σ x) k) σ
  exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param
    (f := fun r x => p.ν * (intervalDomainLift (v r) x) ^ p.γ)
    (f' := fun s x => p.ν * p.γ * (intervalDomainLift (v s) x) ^ (p.γ - 1) * vdotL s x)
    (τ := σ) (n := k) hδ hf_cont h_diff hderivcont

/-! ### K1(i) instantiated at `realSlice u_star`.

`v := realSlice u_star`, fixed via `set` so it stays an opaque local; `realSlice`
is `[local irreducible]` so no unfolding occurs.  All the engine inputs are the
caller's banked data (`realSlice_hasDerivAt_time` for the slice derivative,
`realSlice_pos` for positivity, joint-continuity for the chain-rule field). -/
set_option maxHeartbeats 800000 in
-- Backstop only: barriers (opaque `v` via `set`, `[local irreducible] realSlice`)
-- already prevent the EWA `whnf` blow-up; this raise is defensive headroom.
theorem realSlice_powerCoeff_hasDerivAt {p : CM2Params} {T : ℝ}
    (u_star : EWA T 1) {vdotL : ℝ → ℝ → ℝ}
    (hδ : ∀ σ ∈ Set.Ioo (0 : ℝ) T, ∃ δ > 0,
      (∀ᶠ s in 𝓝 σ,
          ContinuousOn
            (fun x => p.ν * (intervalDomainLift (realSlice u_star s) x) ^ p.γ)
            (Set.Icc (0 : ℝ) 1))
        ∧ (∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball σ δ,
            HasDerivAt (fun r => intervalDomainLift (realSlice u_star r) x)
              (vdotL s x) s)
        ∧ (∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball σ δ,
            0 < intervalDomainLift (realSlice u_star s) x)
        ∧ ContinuousOn
            (Function.uncurry
              (fun s x => p.ν * p.γ
                * (intervalDomainLift (realSlice u_star s) x) ^ (p.γ - 1)
                * vdotL s x))
            (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    ∀ σ ∈ Set.Ioo (0 : ℝ) T, ∀ k : ℕ,
      HasDerivAt
        (fun r => cosineCoeffs
          (fun x => p.ν * (intervalDomainLift (realSlice u_star r) x) ^ p.γ) k)
        (adotPow p (realSlice u_star) vdotL σ k) σ := by
  -- keep the EWA solution OPAQUE: `v` is a local variable, never the EWA def.
  set v : ℝ → intervalDomainPoint → ℝ := realSlice u_star with hv
  intro σ hσ k
  obtain ⟨δ, hδpos, hf_cont, hslice, hpos, hderivcont⟩ := hδ σ hσ
  exact hasDerivAt_powerCoeff_of_inputs (p := p) (v := v) (vdotL := vdotL)
    (σ := σ) (δ := δ) k hδpos hf_cont hslice hpos hderivcont

end ShenWork.EWA
