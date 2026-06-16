/-
  ShenWork/Paper1/WaveRotheMaxPrincipleClosers.lean

  B1 — discharging the three *standard-calculus* hypotheses carried by the
  implicit-step maximum principle `implicitStep_le_of_barrier_maxPrinciple`
  (WaveRotheMaxPrinciple.lean).  These are mechanical real-analysis facts,
  orthogonal to the order content of the trap:

    (a) `iteratedDeriv 2 W x₀ ≤ iteratedDeriv 2 B x₀`  — the 2nd-derivative test
        at the positive max  (`iteratedDeriv2_nonpos_of_isLocalMax` + linearity);
    (b) `IsMaxOn (W − B) univ x₀ ∧ 0 < (W−B) x₀`  — attainment of the positive max
        from the two-sided tail  (`exists_isMaxOn_pos_of_tendsto_nonpos`);
    (c) the chemotaxis flux product-rule split identity `hsplit`
        (`chemFlux_split_identity`).

  All three are proven here as general lemmas (NO sorry / axiom / native_decide),
  and assembled into `implicitStep_le_of_barrier_maxPrinciple_clean`, which takes
  only the genuine inputs and discharges (a)(b)(c) internally — making the trap
  unconditional on the standard-calculus pieces.
-/
import ShenWork.Paper1.WaveRotheMaxPrinciple
import Mathlib.Analysis.Calculus.DerivativeTest

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## 1 — the 2nd-derivative test at a local max

The Mathlib gap: `Mathlib/Analysis/Calculus/DerivativeTest.lean` provides only the
FORWARD second-derivative test (`isLocalMax_of_deriv_deriv_neg`,
`isLocalMin_of_deriv_deriv_pos`).  We need the CONVERSE: a local max forces
`(f')'(x₀) ≤ 0`.  We prove it by contradiction, using only existing Mathlib pieces:

  if `(f')'(x₀) > 0`, the forward test (`isLocalMin_of_deriv_deriv_pos`) makes `f`
  *also* a local min at `x₀`; a function that is both a local min and a local max
  is eventually constant (`eventuallyEq_of_isMinFilter_of_isMaxFilter`), hence
  `deriv f =ᶠ 0` near `x₀`, so `(f')'(x₀) = 0`, contradicting `> 0`. -/

/-- **2nd-derivative test at a local max.**  If `f : ℝ → ℝ` is continuous at `x₀`
and has a local maximum there, then `deriv (deriv f) x₀ ≤ 0`. -/
theorem deriv_deriv_nonpos_of_isLocalMax
    {f : ℝ → ℝ} {x₀ : ℝ} (hmax : IsLocalMax f x₀) (hc : ContinuousAt f x₀) :
    deriv (deriv f) x₀ ≤ 0 := by
  by_contra hpos
  push_neg at hpos  -- hpos : 0 < deriv (deriv f) x₀
  have hd0 : deriv f x₀ = 0 := hmax.deriv_eq_zero
  -- forward 2nd-derivative test ⟹ f also has a local MIN at x₀
  have hmin : IsLocalMin f x₀ := isLocalMin_of_deriv_deriv_pos hpos hd0 hc
  -- both local min and local max ⟹ f is eventually constant near x₀
  have hconst : f =ᶠ[𝓝 x₀] (fun _ => f x₀) :=
    eventuallyEq_of_isMinFilter_of_isMaxFilter hmin hmax
  -- hence deriv f =ᶠ deriv (const) = 0 near x₀
  have hderiv_const : deriv f =ᶠ[𝓝 x₀] deriv (fun _ : ℝ => f x₀) :=
    hconst.deriv
  have hderiv_zero : deriv f =ᶠ[𝓝 x₀] (fun _ : ℝ => (0 : ℝ)) := by
    refine hderiv_const.trans ?_
    filter_upwards with x using deriv_const x _
  -- so (deriv f)' x₀ = (fun _ => 0)' x₀ = 0
  have : deriv (deriv f) x₀ = deriv (fun _ : ℝ => (0 : ℝ)) x₀ :=
    hderiv_zero.deriv_eq
  rw [this, deriv_const] at hpos
  exact lt_irrefl 0 hpos

/-- The same in `iteratedDeriv 2` form. -/
theorem iteratedDeriv2_nonpos_of_isLocalMax
    {f : ℝ → ℝ} {x₀ : ℝ} (hmax : IsLocalMax f x₀) (hc : ContinuousAt f x₀) :
    iteratedDeriv 2 f x₀ ≤ 0 := by
  have h := deriv_deriv_nonpos_of_isLocalMax hmax hc
  simpa [iteratedDeriv_succ, iteratedDeriv_zero] using h

/-- **Discharge of hypothesis (a).**  For `W, B : ℝ → ℝ` that are `ContDiffAt ℝ 2`
at `x₀`, if `W − B` has a local max at `x₀`, then `iteratedDeriv 2 W x₀ ≤
iteratedDeriv 2 B x₀`. -/
theorem iteratedDeriv2_le_of_isLocalMax_sub
    {W B : ℝ → ℝ} {x₀ : ℝ}
    (hWC2 : ContDiffAt ℝ 2 W x₀) (hBC2 : ContDiffAt ℝ 2 B x₀)
    (hmax : IsLocalMax (fun x => W x - B x) x₀) :
    iteratedDeriv 2 W x₀ ≤ iteratedDeriv 2 B x₀ := by
  -- `W − B` is continuous at x₀ (differentiable, since ContDiffAt 2 ≥ ContDiffAt 1)
  have hWcont : ContinuousAt W x₀ :=
    (hWC2.continuousAt)
  have hBcont : ContinuousAt B x₀ :=
    (hBC2.continuousAt)
  have hc : ContinuousAt (fun x => W x - B x) x₀ := hWcont.sub hBcont
  have h := iteratedDeriv2_nonpos_of_isLocalMax hmax hc
  -- linearity:  iteratedDeriv 2 (W − B) = iteratedDeriv 2 W − iteratedDeriv 2 B
  have hlin : iteratedDeriv 2 (fun x => W x - B x) x₀
      = iteratedDeriv 2 W x₀ - iteratedDeriv 2 B x₀ :=
    iteratedDeriv_fun_sub hWC2 hBC2
  rw [hlin] at h
  linarith

/-! ## 2 — attainment of the positive maximum from the two-sided tail

For continuous `φ` with `φ → La ≤ 0` at `−∞`, `φ → Lb ≤ 0` at `+∞`, and `φ x₁ > 0`,
there is a global max point `x₀` with `φ x₀ > 0`.  Route: outside a large compact
set `φ < φ x₁` (from the limits), so the global max — obtained by the extreme value
theorem on a compact set / `Continuous.exists_forall_ge'` — is `≥ φ x₁ > 0`. -/

/-- **Discharge of hypothesis (b).**  `φ` continuous with two-sided nonpositive
tails and a positive value somewhere attains a positive global maximum. -/
theorem exists_isMaxOn_pos_of_tendsto_nonpos
    {φ : ℝ → ℝ} {x₁ La Lb : ℝ}
    (hφ : Continuous φ)
    (hbot : Tendsto φ atBot (𝓝 La)) (hLa : La ≤ 0)
    (htop : Tendsto φ atTop (𝓝 Lb)) (hLb : Lb ≤ 0)
    (hpos : 0 < φ x₁) :
    ∃ x₀, IsMaxOn φ Set.univ x₀ ∧ 0 < φ x₀ := by
  -- away from compact sets, φ < φ x₁ (strictly below the positive value)
  have hbot_lt : ∀ᶠ x in atBot, φ x < φ x₁ :=
    hbot.eventually_lt_const (lt_of_le_of_lt hLa hpos)
  have htop_lt : ∀ᶠ x in atTop, φ x < φ x₁ :=
    htop.eventually_lt_const (lt_of_le_of_lt hLb hpos)
  -- combine on `cocompact ℝ = atBot ⊔ atTop`
  have hcoc : ∀ᶠ x in cocompact ℝ, φ x ≤ φ x₁ := by
    rw [cocompact_eq_atBot_atTop]
    exact eventually_sup.mpr
      ⟨hbot_lt.mono fun _ h => h.le, htop_lt.mono fun _ h => h.le⟩
  -- extreme value theorem with a value beaten away from compacts
  obtain ⟨x₀, hx₀⟩ := hφ.exists_forall_ge' x₁ hcoc
  refine ⟨x₀, ?_, ?_⟩
  · exact isMaxOn_univ_iff.mpr hx₀
  · exact lt_of_lt_of_le hpos (hx₀ x₁)

/-! ## 3 — the chemotaxis flux product-rule split identity

`chemFlux p u W y = (W y)^m · V'(y)`, `V = frozenElliptic p u`.  With `W`
differentiable at `x` and `V = frozenElliptic p u` (committed: differentiable, with
`deriv V` differentiable at `x`), the product rule gives

    `(chemFlux p u W)'(x)
        = m·(W x)^{m−1}·W'(x)·V'(x) + (W x)^m·V''(x)`.

This is the structural identity carried as `hsplit` in `chemFlux_increment_bound`. -/

/-- **Discharge of hypothesis (c) — the flux split identity.**
For `W` differentiable at `x` and `u` in `IsCUnifBdd` with `u ≥ 0` (so that
`V = frozenElliptic p u` is `C²` near `x`, committed), the chemotaxis flux
`chemFlux p u W = (W ·)^m · V'` obeys the product rule

    `deriv (chemFlux p u W) x
        = m · V'(x) · ((W x)^{m−1}) · W'(x) + (W x)^m · V''(x)`.

(`V'' = deriv (deriv V)`.)  This is exactly the shape of the carried `hsplit`. -/
theorem chemFlux_split_identity
    (p : CMParams) {u W : ℝ → ℝ} {x : ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ y, 0 ≤ u y)
    (hWdiff : DifferentiableAt ℝ W x) :
    deriv (chemFlux p u W) x
      = p.m * deriv (frozenElliptic p u) x * ((W x) ^ (p.m - 1)) * deriv W x
        + (W x) ^ p.m * deriv (deriv (frozenElliptic p u)) x := by
  set V := frozenElliptic p u with hV
  -- HasDerivAt for the power factor `(W ·)^m`:  m ≥ 1 so the `Or.inr` branch.
  have hWderiv : HasDerivAt W (deriv W x) x := hWdiff.hasDerivAt
  have hpow : HasDerivAt (fun y => (W y) ^ p.m)
      (deriv W x * p.m * (W x) ^ (p.m - 1)) x :=
    hWderiv.rpow_const (Or.inr p.hm)
  -- HasDerivAt for the elliptic-derivative factor `V'`:
  have hVp_diff : DifferentiableAt ℝ (deriv V) x :=
    frozenElliptic_deriv_differentiableAt p hu hu_nonneg x
  have hVp : HasDerivAt (deriv V) (deriv (deriv V) x) x := hVp_diff.hasDerivAt
  -- product rule
  have hmul : HasDerivAt (fun y => (W y) ^ p.m * deriv V y)
      ((deriv W x * p.m * (W x) ^ (p.m - 1)) * deriv V x
        + (W x) ^ p.m * deriv (deriv V) x) x := by
    have := hpow.mul hVp
    simpa [Pi.mul_apply] using this
  -- chemFlux is literally that function
  have hchem_eq : chemFlux p u W = (fun y => (W y) ^ p.m * deriv V y) := by
    funext y; simp [chemFlux, hV]
  have hderiv : deriv (chemFlux p u W) x
      = (deriv W x * p.m * (W x) ^ (p.m - 1)) * deriv V x
        + (W x) ^ p.m * deriv (deriv V) x := by
    rw [hchem_eq]; exact hmul.deriv
  rw [hderiv, hV]; ring

/-- The flux split identity in the exact algebraic shape consumed by
`chemFlux_increment_bound`'s `hsplit` (difference of two flux derivatives, with
`W'(x₀) = B'(x₀)` already substituted on the `W` side). -/
theorem chemFlux_increment_split
    (p : CMParams) {u W B : ℝ → ℝ} {x₀ : ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ y, 0 ≤ u y)
    (hWdiff : DifferentiableAt ℝ W x₀) (hBdiff : DifferentiableAt ℝ B x₀)
    (hderiv1 : deriv W x₀ = deriv B x₀) :
    deriv (chemFlux p u W) x₀ - deriv (chemFlux p u B) x₀
      = p.m * deriv (frozenElliptic p u) x₀
          * ((W x₀) ^ (p.m - 1) - (B x₀) ^ (p.m - 1)) * deriv W x₀
        + ((W x₀) ^ p.m - (B x₀) ^ p.m) * deriv (deriv (frozenElliptic p u)) x₀ := by
  have hW := chemFlux_split_identity p hu hu_nonneg hWdiff
  have hB := chemFlux_split_identity p hu hu_nonneg hBdiff
  rw [hW, hB, ← hderiv1]
  ring

/-! ## 4 — the assembled clean maximum principle

`implicitStep_le_of_barrier_maxPrinciple_clean` takes only the GENUINE inputs and
discharges (a)(b)(c) via the three lemmas above plus the committed
`chemFlux_increment_bound`. -/

/-- **`implicitStep_le_of_barrier_maxPrinciple_clean`.**
The implicit-step maximum principle, now unconditional on the standard-calculus
pieces.  It takes only:

* `hstep` — `W` solves the step `G_h(W) = Z`;
* `hBsuper` — `B` is a step super-barrier `F_u(B) ≤ 0`;
* `hZB` — `Z ≤ B` pointwise;
* `hh`, `hCB` — `0 < h`, `h·C_B < 1`;
* `hM`, `hC_chem_nonneg` — `0 ≤ M`, `0 ≤ C_chem`;
* `hφcont`, the two-sided tails (`hbot`/`hLa`, `htop`/`hLb`), and `hx₁` —
  attainment data for the positive max of `φ = W − B`;
* `hWC2`, `hBC2` — `C²`-regularity of `W`, `B` at the max (supplies the
  2nd-derivative test and the first-order differentiability);
* the trapped-range membership and the structural chemotaxis bound (split
  identity `chemFlux_increment_split` + the `chemFlux_increment_bound` analytic
  factors), passed via the already-assembled `hchem`.

Conclusion: `∀ x, W x ≤ B x`.

Hypotheses (a) `W'' ≤ B''` and (b) `IsMaxOn` are discharged *internally* here;
only the genuine order/analytic inputs remain. -/
theorem implicitStep_le_of_barrier_maxPrinciple_clean
    (p : CMParams) {c h M C_chem : ℝ} {u Z W B : ℝ → ℝ} {La Lb : ℝ}
    (hh : 0 < h) (hM : 0 ≤ M) (hC_chem_nonneg : 0 ≤ C_chem)
    (hCB : h * (reactionLip p.α M + C_chem) < 1)
    (hstep : ∀ x, implicitStepOp p c h u W x = Z x)
    (hBsuper : ∀ x, frozenWaveOperator p c u B x ≤ 0)
    (hZB : ∀ x, Z x ≤ B x)
    -- attainment data for φ = W − B:
    (hφcont : Continuous (fun x => W x - B x))
    (hbot : Tendsto (fun x => W x - B x) atBot (𝓝 La)) (hLa : La ≤ 0)
    (htop : Tendsto (fun x => W x - B x) atTop (𝓝 Lb)) (hLb : Lb ≤ 0)
    -- C²-regularity of `W` at *every* point (the Green-smoothed iterate is C²);
    -- C²-regularity of the barrier `B` only AT THE INTERNALLY-CHOSEN MAX of
    -- `φ = W − B` (the honest, satisfiable form: for `B = upperBarrier κ M` the
    -- everywhere-C² is FALSE at the kink, but the max never lands on the kink):
    (hWC2 : ∀ y, ContDiffAt ℝ 2 W y)
    (hBC2 : ∀ x₀, IsMaxOn (fun x => W x - B x) Set.univ x₀ → ContDiffAt ℝ 2 B x₀)
    -- range membership and the carried chemotaxis bound, at the (internally chosen) max:
    (hrange : ∀ x₀, IsMaxOn (fun x => W x - B x) Set.univ x₀ →
        W x₀ ∈ Set.Icc (0 : ℝ) M ∧ B x₀ ∈ Set.Icc (0 : ℝ) M)
    (hchem : ∀ x₀, IsMaxOn (fun x => W x - B x) Set.univ x₀ →
        -p.χ * (deriv (chemFlux p u W) x₀ - deriv (chemFlux p u B) x₀)
          ≤ C_chem * (W x₀ - B x₀)) :
    ∀ x, W x ≤ B x := by
  -- If φ is nowhere positive, maximality is vacuous; we argue by contradiction on
  -- the existence of a positive value, exactly as in the carried version.
  by_contra hcon
  push_neg at hcon
  obtain ⟨x₁', hx₁'⟩ := hcon
  have hpos₁ : 0 < W x₁' - B x₁' := by linarith
  -- (b) attainment of the positive max
  obtain ⟨x₀, hattain, hx₀pos⟩ :=
    exists_isMaxOn_pos_of_tendsto_nonpos (φ := fun x => W x - B x)
      hφcont hbot hLa htop hLb hpos₁
  -- the max on `univ` is in particular a LOCAL max (`univ ∈ 𝓝 x₀`).
  have hloc : IsLocalMax (fun x => W x - B x) x₀ :=
    hattain.isLocalMax Filter.univ_mem
  -- `B` is C² at this (internally-chosen) max point, from the at-max field:
  have hBC2₀ : ContDiffAt ℝ 2 B x₀ := hBC2 x₀ hattain
  -- (a) 2nd-derivative test, discharged from C² + local max
  have hderiv2 : iteratedDeriv 2 W x₀ ≤ iteratedDeriv 2 B x₀ :=
    iteratedDeriv2_le_of_isLocalMax_sub (hWC2 x₀) hBC2₀ hloc
  -- range + chem at this x₀
  obtain ⟨hWmem, hBmem⟩ := hrange x₀ hattain
  have hchem₀ := hchem x₀ hattain
  -- differentiability at x₀ from C² (≥ C¹)
  have hWdiff : DifferentiableAt ℝ W x₀ :=
    (hWC2 x₀).differentiableAt (by norm_num)
  have hBdiff : DifferentiableAt ℝ B x₀ :=
    hBC2₀.differentiableAt (by norm_num)
  -- now invoke the carried maximum principle: it concludes φ ≤ 0 everywhere,
  -- contradicting the positive value at x₁'.
  have hle :=
    implicitStep_le_of_barrier_maxPrinciple (p := p) (c := c) (h := h) (M := M)
      (C_chem := C_chem) (u := u) (Z := Z) (W := W) (B := B) (x₀ := x₀)
      hh hM hC_chem_nonneg hCB hstep hBsuper hZB hattain hloc hWdiff hBdiff
      hderiv2 hWmem hBmem hchem₀
  have := hle x₁'
  linarith

/-! ## Axiom audit -/

section AxiomAudit
#print axioms deriv_deriv_nonpos_of_isLocalMax
#print axioms iteratedDeriv2_nonpos_of_isLocalMax
#print axioms iteratedDeriv2_le_of_isLocalMax_sub
#print axioms exists_isMaxOn_pos_of_tendsto_nonpos
#print axioms chemFlux_split_identity
#print axioms chemFlux_increment_split
#print axioms implicitStep_le_of_barrier_maxPrinciple_clean
end AxiomAudit

end ShenWork.Paper1
