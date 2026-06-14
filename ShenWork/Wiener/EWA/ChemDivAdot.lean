import ShenWork.PDE.IntervalChemDivTimeDerivative
import ShenWork.Paper2.IntervalDomainPositiveWindowK1OnEndpoint

/-!
# EWA brick — the `adot`/`h_deriv`/`h_adotcont` reduction for the chemDiv FINAL theorem

The Phase C `chemDiv_eigenvalueSummableOn_of_solution` (`ChemDivFinal.lean`) carries
the chemotaxis-divergence **time-derivative data** as four explicit hypotheses:

* `adot : ℝ → ℕ → ℝ` — the time-derivative of the source cosine coefficients;
* `h_deriv` — `HasDerivWithinAt (fun r => coupledChemDivSourceCoeffs p u r n)`
  `(adot s n) (Icc 0 T) s`;
* `h_adotcont` — `ContinuousOn (fun s => adot s n) (Icc 0 T)`;
* `Mdot`, `h_Mdot` — a single uniform constant `|adot s n| ≤ Mdot` for ALL `n, s`.

This file discharges the FIRST THREE (`adot`, `h_deriv`, `h_adotcont`) from the
solution's TIME-SMOOTHNESS, which is the documented analytic input.  The canonical
`adot` is the committed `coupledChemDivAdot p u`, i.e. the cosine coefficients of the
pointwise chain-rule field `coupledChemDivTimeDerivativeLift p u`
(`IntervalChemDivTimeDerivative.lean`).

The two time-smoothness facts are taken as named hypotheses, exactly the content the
committed `CoupledChemDivLocalChainRule` / `CoupledChemDivTimeC1Fields` packages
already carry (no new analysis):

1. `hchain : CoupledChemDivLocalChainRule p u` — the pointwise chain-rule + local
   dominated-convergence slab.  Via the committed time-Leibniz
   `cosineCoeffs_hasDerivAt_of_smooth_param` (consumed by
   `coupledChemDivCoeff_hasDerivAt_of_fields`) it yields, for every `s, n`, the
   GLOBAL `HasDerivAt` of `fun r => cosineCoeffs (coupledChemDivSourceLift p u r) n`
   with derivative `coupledChemDivAdot p u s n`.  `HasDerivAt.hasDerivWithinAt` then
   gives `h_deriv`.
2. `hjointcont : ContinuousOn (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
   (Icc 0 T ×ˢ Icc 0 1)` — the joint continuity of the chain-rule field (supplied by
   the resolver time-regularity route, cf.
   `coupledChemicalTimeDerivative_jointContinuousOn_closed`).  Via the committed
   `cosineCoeffs_continuousOn_of_jointContinuousOn_Icc` it yields `h_adotcont`.

**What this file does NOT supply: the uniform bound `Mdot`.**  `Mdot` is a SINGLE
constant dominating `|coupledChemDivAdot p u s n|` for ALL `n`.  `coupledChemDivAdot`
is the cosine coefficient of `∂ₜ(∂ₓB) = ∂ₓ(B_t)`; a uniform-in-`n` bound on these
coefficients is precisely the EWA-T-3 time-chain residual (`B_t ∈ A⁰`, the `gDeriv`
operator-norm route — DOCTRINE §6/§(d), RUN_LOG "B8 time-chain@EWA3").  It is NOT
dischargeable from per-mode smoothness alone (smoothness gives continuity of each
`s ↦ adot s n`, hence a per-`n` bound on `[0,T]`, but NOT a uniform-in-`n` one).  See
the residual theorem `chemDivAdot_Mdot_residual` below, which isolates exactly the
missing hypothesis.

NO `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open scoped BigOperators
open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
  (cosineCoeffs_continuousOn_of_jointContinuousOn_Icc)

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

variable {T : ℝ}

/-! ### 1. `h_deriv` from the committed local chain-rule package. -/

/-- **The global coefficient `HasDerivAt`, from the local chain-rule package.**

Given the committed `CoupledChemDivLocalChainRule p u` (the documented time-smoothness
input: a pointwise chain rule + local dominated-convergence slab for the chemDiv
source field), the cosine coefficient `s ↦ cosineCoeffs (coupledChemDivSourceLift p u s) n`
is differentiable in time at every `s`, with derivative the committed
`coupledChemDivAdot p u s n`.

This re-exposes `coupledChemDivCoeff_hasDerivAt_of_fields` but consuming ONLY the
`hchain` field (no `Cchem`/`hH2`/`hdecay`/`hzero`/bound data), since the time-Leibniz
`cosineCoeffs_hasDerivAt_of_smooth_param` uses only the chain-rule slab. -/
theorem coupledChemDivCoeff_hasDerivAt_of_chainRule
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) (s : ℝ) (n : ℕ) :
    HasDerivAt
      (fun r => cosineCoeffs (coupledChemDivSourceLift p u r) n)
      (coupledChemDivAdot p u s n) s := by
  rcases hchain.exists_local_slab s with
    ⟨δ, hδ, hf_cont, hdiff, hcont_deriv⟩
  exact
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param
      (f := coupledChemDivSourceLift p u)
      (f' := coupledChemDivTimeDerivativeLift p u)
      (τ := s) (δ := δ) (n := n) hδ hf_cont hdiff hcont_deriv

/-- **`h_deriv` reduction.**  The FINAL theorem's `HasDerivWithinAt` form of the
coefficient time-derivative on `[0,T]`, with `adot := coupledChemDivAdot p u`, follows
directly from the global `HasDerivAt` (which holds at every `s`), restricted to the
within-set form via `HasDerivAt.hasDerivWithinAt`.

Note `coupledChemDivSourceCoeffs p u r n = cosineCoeffs (coupledChemDivSourceLift p u r) n`
DEFINITIONALLY. -/
theorem chemDivAdot_hasDerivWithinAt_of_chainRule
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
      HasDerivWithinAt (fun r => coupledChemDivSourceCoeffs p u r n)
        (coupledChemDivAdot p u s n) (Set.Icc 0 T) s := by
  intro s _ n
  -- unfold the definitional equality of the coefficient family
  have h : HasDerivAt
      (fun r => coupledChemDivSourceCoeffs p u r n)
      (coupledChemDivAdot p u s n) s := by
    simpa only [coupledChemDivSourceCoeffs] using
      coupledChemDivCoeff_hasDerivAt_of_chainRule hchain s n
  exact h.hasDerivWithinAt

/-! ### 2. `h_adotcont` from joint continuity of the chain-rule field. -/

/-- **`h_adotcont` reduction.**  The continuity-on-`[0,T]` of `s ↦ coupledChemDivAdot p u s n`
follows from the joint continuity of the chain-rule field
`coupledChemDivTimeDerivativeLift p u` on the closed slab `[0,T] × [0,1]`, via the
committed compact dominated-convergence lemma
`cosineCoeffs_continuousOn_of_jointContinuousOn_Icc`.

`coupledChemDivAdot p u s n = cosineCoeffs (coupledChemDivTimeDerivativeLift p u s) n`
DEFINITIONALLY. -/
theorem chemDivAdot_continuousOn_of_jointCont
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hjointcont : ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ∀ n, ContinuousOn (fun s => coupledChemDivAdot p u s n) (Set.Icc (0 : ℝ) T) := by
  intro n
  -- coupledChemDivAdot p u s n = cosineCoeffs (coupledChemDivTimeDerivativeLift p u s) n
  simpa only [coupledChemDivAdot] using
    cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
      (f := coupledChemDivTimeDerivativeLift p u) (c := (0 : ℝ)) (T := T) n hjointcont

/-! ### 3. The combined `adot`/`h_deriv`/`h_adotcont` package. -/

/-- **Combined reduction of the three smoothness-discharged FINAL hypotheses.**

From the documented time-smoothness inputs — `hchain` (the local chain rule) and
`hjointcont` (joint continuity of the chain-rule field on `[0,T] × [0,1]`) — produces
the canonical `adot := coupledChemDivAdot p u` together with the `h_deriv` and
`h_adotcont` legs in EXACTLY the shape the FINAL theorem
`chemDiv_eigenvalueSummableOn_of_solution` consumes.

`Mdot`/`h_Mdot` are deliberately NOT produced here: the uniform-in-`n` coefficient bound
is the EWA-T-3 time-chain residual (see `chemDivAdot_Mdot_residual`). -/
theorem chemDivAdot_deriv_legs_of_smoothness
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u)
    (hjointcont : ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
        HasDerivWithinAt (fun r => coupledChemDivSourceCoeffs p u r n)
          (coupledChemDivAdot p u s n) (Set.Icc 0 T) s)
      ∧ (∀ n, ContinuousOn (fun s => coupledChemDivAdot p u s n)
          (Set.Icc (0 : ℝ) T)) :=
  ⟨chemDivAdot_hasDerivWithinAt_of_chainRule hchain,
    chemDivAdot_continuousOn_of_jointCont hjointcont⟩

/-! ### 4. The `Mdot` residual — isolated precisely.

The uniform bound `Mdot` is a SINGLE real with `|coupledChemDivAdot p u s n| ≤ Mdot`
for ALL `n` and all `s ∈ [0,T]`.  Per-mode smoothness gives continuity of each
`s ↦ coupledChemDivAdot p u s n` on the compact `[0,T]`, hence a per-`n` bound — but the
constant depends on `n` and there is no uniform control as `n → ∞` from smoothness alone.

The honest residual: the uniform bound holds the MOMENT the time-derivative field has a
summable (hence sup-bounded) cosine-coefficient envelope, which is what an EWA element
realizing `∂ₜ(∂ₓB) = ∂ₓ(B_t)` would supply (mirroring how `sourceEnvelope` supplied the
VALUE bound for `coupledChemDivSourceCoeffs`).  Constructing that element is the EWA-T-3
time-chain (`B_t ∈ A⁰`, the high-weight Wiener–Lévy / `gDeriv` operator-norm brick). -/

/-- **`Mdot` residual, isolated.**  Given ANY uniform envelope `env : ℕ → ℝ` that is
summable and dominates the time-derivative coefficients `|coupledChemDivAdot p u s n|`
uniformly in `s ∈ [0,T]` (the EWA-T-3 / `B_t ∈ A⁰` deliverable, analogous to
`sourceEnvelope` for the value side), a single uniform constant `Mdot` exists, with
`|coupledChemDivAdot p u s n| ≤ Mdot` for all `s ∈ [0,T]` and all `n`.

The constant is `Mdot := ∑' n, env n` (finite by summability), and `|adot s n| ≤ env n ≤
∑' env` since `env ≥ 0`.  This shows the `Mdot` leg reduces EXACTLY to the missing
summable-envelope-on-the-time-derivative datum; it does NOT manufacture that datum. -/
theorem chemDivAdot_Mdot_residual
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (env : ℕ → ℝ) (henvnn : ∀ n, 0 ≤ env n) (henvsum : Summable env)
    (henv : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n, |coupledChemDivAdot p u s n| ≤ env n) :
    ∃ Mdot : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
      |coupledChemDivAdot p u s n| ≤ Mdot := by
  refine ⟨∑' n, env n, fun s hs n => ?_⟩
  exact (henv s hs n).trans (henvsum.le_tsum n (fun m _ => henvnn m))

end ShenWork.IntervalCoupledRegularityBootstrap
