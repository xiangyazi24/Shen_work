/-
  Lemma 3.1, the `a = b = 0` branch: reusable max-side Grönwall reduction
  + the chemotaxis obstruction finding.

  ## What the branch asks

  `Lemma_3_1`'s second alternative (Statements.lean) is, with `χ₀ ≤ 0`:
    `a = 0 → b = 0 → ∀ T>0, ∀ classical (u,v), SupNormNonincreasingOn u (Ioo 0 T)`.

  ## FINDING: `a = b = 0` is NOT pure heat unless `χ₀ = 0`

  The (CM) momentum equation of a classical solution is
    `u_t = Δu − χ₀·chemotaxisDiv p u v + u·(a − b·u^α)`.
  Setting `a = b = 0` kills only the LOGISTIC reaction `u(a−bu^α)`; the
  chemotaxis transport term `−χ₀·chemotaxisDiv` SURVIVES whenever
  `χ₀ ≠ 0`.  Expanding it (divergence form):
    `−χ₀·∂ₓ(u·φ(v)·∂ₓv) = −χ₀·φ·∂ₓv·∂ₓu − χ₀·∂ₓ(φ·∂ₓv)·u`,
  i.e. `u_t = Δu + B·∂ₓu + C·u` with `C := −χ₀·∂ₓ(φ(v)∂ₓv)`.  At an
  interior max `x*` of `u` (`∂ₓu(x*)=0`, `Δu(x*)≤0`):
    `u_t(x*) = Δu(x*) + C(x*)·u(x*)`,
  and `C(x*) = −χ₀·(φ·v_xx + φ'·v_x²)` is SIGN-INDEFINITE for `χ₀ < 0`
  (`v_xx = μv − ν u^γ` from the elliptic equation, `φ' < 0`).  So the
  spatial maximum can INCREASE: `SupNormNonincreasingOn` is FALSE for the
  full `χ₀ ≤ 0` branch — it holds only in the genuine pure-heat sub-case
  `χ₀ = 0` (where `B = C = 0`).  The "pure-heat / sub-Markov" comment on
  the branch is correct only for `χ₀ = 0`.

  ## What IS clean and reusable

  Even the true `χ₀ = 0` sub-case needs a maximum principle for an
  ARBITRARY classical solution (the sub-Markov semigroup bound applies to
  `u = S(t)u₀`, which requires uniqueness, not in scope here).  The
  parabolic-max-principle conclusion reduces, via Grönwall with rate `0`,
  to a one-sided Dini condition on the sup-norm trajectory.  This file
  provides that reduction — `supNorm_nonincreasing_of_dini` — the honest
  interface for closing the branch once the Dini input is supplied (at an
  interior/boundary argmax, `u_t ≤ 0` for the pure-heat operator).  It is
  the max-side mirror of `MinPersistenceAtoms.hamilton_lower_bound`.

  ## Consumer audit (for the `χ₀ = 0` narrowing)

  Who consumes `(Lemma_3_1_intervalDomain p hχ).2` (the a=b=0 branch)?
    * `IntervalDomainStabilityChain.lean:143` — with only `hχ : χ₀ ≤ 0`.
    * `IntervalDomainChain.lean` (minimal branch) — likewise `χ₀ ≤ 0`.
  NEITHER restricts to `χ₀ = 0`.  Their `a=b=0` paths ARE dead in the real
  theorems (`0 < a`, `0 < b`), so narrowing the branch to `χ₀ = 0` is
  SOUND — but it is not a local edit: a `χ₀ = 0` hypothesis must cascade
  through both consumer files (their `a=b=0` paths discharge via the
  `a>0`-contradiction in the real theorems, or thread `χ₀ = 0`).

  ## Conclusion

  The `a = b = 0` sorry is NOT closed here.  Three compounding reasons:
    1. TOO STRONG as stated (`χ₀ ≤ 0`): chemotaxis survives for `χ₀ < 0`,
       sup-norm can grow (finding above).
    2. The true `χ₀ = 0` narrowing still needs the max-principle DINI
       input for an ARBITRARY classical solution (`supNorm_nonincreasing_
       of_dini` reduces to it).  The sub-Markov semigroup bound applies
       only to `u = S(t)u₀` (heat uniqueness, not wired); the direct max
       principle is the deferred Hamilton-max machinery
       (`MinPersistenceAtoms` B2).  `ParabolicMaxPrinciple.
       parabolic_maximum_principle` is whole-line, needs even-reflection.
    3. The narrowing cascade touches `IntervalDomainChain` /
       `IntervalDomainStabilityChain`, currently under active concurrent
       refactor — editing them now would collide.

  RECOMMENDATION: once the refactor converges, narrow the branch to
  `χ₀ = 0`, thread it through the two consumers, and discharge the Dini
  via the Hamilton-max lane; `supNorm_nonincreasing_of_dini` is the
  drop-in final step.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.Statements
import Mathlib.Analysis.ODE.Gronwall

open Filter Topology
open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint intervalDomainSupNorm)

noncomputable section

namespace ShenWork.Paper2.Lemma31Heat

/-- **Max-side Grönwall reduction (reusable, TRUE).**  If the sup-norm
trajectory `M(t) := ‖u(t)‖_∞` is continuous on `Ioo 0 T` and satisfies
the one-sided Dini condition "M does not increase to the right" — for
every interior `x` and every `r > 0` the forward difference quotient
`(M z − M x)/(z − x)` is `< r` arbitrarily close to the right of `x` —
then `M` is non-increasing on `Ioo 0 T`.

This is exactly the parabolic-maximum-principle conclusion stripped of
all PDE content: the PDE enters only through the Dini hypothesis (at an
argmax, `u_t ≤ 0` for the pure-heat operator forces it). -/
theorem supNorm_nonincreasing_of_dini
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hcont : ContinuousOn (fun t => intervalDomainSupNorm (u t))
      (Set.Ioo (0 : ℝ) T))
    (hDini : ∀ x ∈ Set.Ioo (0 : ℝ) T, ∀ r : ℝ, 0 < r →
      ∃ᶠ z in nhdsWithin x (Set.Ioi x),
        (z - x)⁻¹ * (intervalDomainSupNorm (u z)
          - intervalDomainSupNorm (u x)) < r) :
    SupNormNonincreasingOn intervalDomain u (Set.Ioo (0 : ℝ) T) := by
  intro t₁ ht₁ t₂ ht₂ hle
  -- `M` on the closed window `[t₁, t₂] ⊆ Ioo 0 T`.
  set M : ℝ → ℝ := fun t => intervalDomainSupNorm (u t) with hM_def
  have hsub : Set.Icc t₁ t₂ ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨lt_of_lt_of_le ht₁.1 hs.1, lt_of_le_of_lt hs.2 ht₂.2⟩
  have hcont' : ContinuousOn M (Set.Icc t₁ t₂) := hcont.mono hsub
  -- Apply the Grönwall inequality with `f := M`, `f' := 0`, `K = ε = 0`,
  -- `δ := M t₁`.
  have hgron := le_gronwallBound_of_liminf_deriv_right_le
    (f := M) (f' := fun _ => 0) (δ := M t₁) (K := 0) (ε := 0)
    (a := t₁) (b := t₂)
    hcont'
    (by
      intro x hx r hr
      have hxmem : x ∈ Set.Ioo (0 : ℝ) T :=
        hsub (Set.Ico_subset_Icc_self hx)
      exact hDini x hxmem r hr)
    (le_refl _)
    (by intro x _; simp)
  have hbx := hgron t₂ (Set.right_mem_Icc.mpr hle)
  rwa [gronwallBound_ε0, mul_zero, Real.exp_zero, mul_one] at hbx

end ShenWork.Paper2.Lemma31Heat
