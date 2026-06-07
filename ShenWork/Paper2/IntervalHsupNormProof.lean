/-
  HsupNorm: integrity finding + reusable constructor for
  `IntervalDomainSupNormDerivativeNonposOn`.

  ## INTEGRITY FINDING (faithfulness audit, automode)

  The ledger field
    `HsupNorm : IntervalDomainSupNormDerivativeNonposOn D.u (Set.Ioo 0 D.T)`
  asserts that `t ↦ ‖u(t)‖_∞` is differentiable with **non-positive**
  derivative on ALL of `(0, D.T)`, UNCONDITIONALLY.

  **This statement is FALSE for the cone-constructed `D` in general.**
  Counterexample: take a flat positive datum `u₀ ≡ ε` with
  `0 < ε < (a/b)^{1/α}` (a valid `PositiveInitialDatum`; the constant is
  `> 0` on the interior, bounded, continuous, and satisfies the Neumann
  condition trivially).  Under the (CM) system with `χ₀ = 0` the spatial
  Laplacian and chemotaxis terms vanish identically, so `u` stays
  spatially constant and solves the logistic ODE
    `u'(t) = u(t)·(a − b·u(t)^α)`,
  whose right-hand side is **strictly positive** for `0 < u < (a/b)^{1/α}`.
  Hence `‖u(t)‖_∞ = u(t)` is strictly **increasing** on `(0, δ)`, i.e.
  `deriv ‖u(·)‖_∞ > 0` there — directly contradicting `deriv_nonpos`.

  **The genuine parabolic maximum-principle content is CONDITIONAL.**  The
  Hamilton/Grönwall bound for `M(t) := ‖u(t)‖_∞` is
    `M'(t) ≤ M(t)·(a − b·M(t)^α)`,
  which is `≤ 0` only when `M(t) ≥ (a/b)^{1/α}` (above carrying
  capacity).  The unconditional `≤ 0` is a strictly-too-strong predicate.

  **The frontier only ever needs the weaker, true pieces.**  In
  `RegularityFrontierWiring.gradientMildClassicalRegularityFrontierData_of_spectral`
  the field `HsupNorm` is consumed in exactly two places:
    * `supnormLogistic` — the conjunct already carries the hypothesis
      `_hsup : (a/b)^{1/α} < ‖u(t₀)‖_∞` (currently discarded); only the
      ABOVE-CAPACITY decay is needed there;
    * `supnormZero` — only the `a = 0 ∧ b = 0` (pure-heat, sub-Markov)
      case, where the sup-norm is genuinely non-increasing.
  So the correct refactor replaces the single too-strong `HsupNorm` field
  with (i) the conditional above-capacity decay and (ii) the pure-heat
  case — both true.

  ## What this file provides

  Since the unconditional field cannot (and should not) be proved, this
  file does NOT discharge `hsupNorm_chiZero`.  Instead it gives the
  reusable, axiom-clean constructor `nonposOn_of_locally_eq`, which
  reduces `IntervalDomainSupNormDerivativeNonposOn` to a local-equality
  with a differentiable majorant of non-positive derivative — exactly the
  interface the eventual CONDITIONAL proof (above capacity, via the
  Hamilton machinery in `IntervalDomainMinPersistenceAtoms`) will use.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalDomain

open Filter Topology

noncomputable section

namespace ShenWork.Paper2.HsupNormProof

open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainSupNorm
  IntervalDomainSupNormDerivativeNonposOn)

/-- **Reusable constructor.**  If the sup-norm trajectory is continuous on
`I`, and near every interior point it agrees (`=ᶠ`) with a function `g`
that is differentiable there with `deriv g ≤ 0`, then the
`IntervalDomainSupNormDerivativeNonposOn` structure holds.

This is the honest interface for the genuine (conditional) parabolic
maximum principle: the eventual proof supplies, on the above-capacity
region, a local smooth majorant `g` solving the logistic ODE comparison
whose derivative is `≤ 0`. -/
theorem nonposOn_of_locally_eq
    {u : ℝ → intervalDomainPoint → ℝ} {I : Set ℝ} {g : ℝ → ℝ}
    (hcont : ContinuousOn (fun t => intervalDomainSupNorm (u t)) I)
    (hloc : ∀ t ∈ interior I,
      (fun s => intervalDomainSupNorm (u s)) =ᶠ[nhds t] g)
    (hdiff : ∀ t ∈ interior I, DifferentiableAt ℝ g t)
    (hnonpos : ∀ t ∈ interior I, deriv g t ≤ 0) :
    IntervalDomainSupNormDerivativeNonposOn u I where
  continuousOn := hcont
  differentiableOn := by
    intro t ht
    exact ((hloc t ht).differentiableAt_iff.mpr (hdiff t ht)).differentiableWithinAt
  deriv_nonpos := by
    intro t ht
    rw [(hloc t ht).deriv_eq]
    exact hnonpos t ht

/-- Specialisation: a single global differentiable majorant equal to the
sup-norm on all of `I`, with non-positive derivative on the interior. -/
theorem nonposOn_of_eq
    {u : ℝ → intervalDomainPoint → ℝ} {I : Set ℝ} {g : ℝ → ℝ}
    (hU : IsOpen I)
    (hcont : ContinuousOn (fun t => intervalDomainSupNorm (u t)) I)
    (heq : ∀ t ∈ I, intervalDomainSupNorm (u t) = g t)
    (hdiff : ∀ t ∈ I, DifferentiableAt ℝ g t)
    (hnonpos : ∀ t ∈ I, deriv g t ≤ 0) :
    IntervalDomainSupNormDerivativeNonposOn u I := by
  have hloc : ∀ t ∈ interior I,
      (fun s => intervalDomainSupNorm (u s)) =ᶠ[nhds t] g := by
    intro t ht
    rw [hU.interior_eq] at ht
    exact Filter.eventuallyEq_of_mem (hU.mem_nhds ht) (fun s hs => heq s hs)
  refine nonposOn_of_locally_eq hcont hloc (fun t ht => ?_) (fun t ht => ?_)
  · rw [hU.interior_eq] at ht; exact hdiff t ht
  · rw [hU.interior_eq] at ht; exact hnonpos t ht

end ShenWork.Paper2.HsupNormProof
