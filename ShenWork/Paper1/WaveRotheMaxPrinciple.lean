/-
  ShenWork/Paper1/WaveRotheMaxPrinciple.lean

  B1 traveling-wave Rothe (implicit-Euler) trapping via a NONLINEAR
  IMPLICIT-STEP MAXIMUM PRINCIPLE.

  Per Shen's paper (ChatGPT-Pro reading) the over-strong carried source-difference
  residual `R_B − R_W ≥ 0` is the WRONG obligation: the correct proof of the
  per-step comparison `W ≤ B` is a maximum principle for the implicit step

      `G_h(W) = W − h·F_u(W) = Z`,    `h = 1/λ`,

  where `F_u` is the cross-frozen wave operator

      `F_u(W) = W'' + cW' − χ ∂ₓ(W^m V_u') + W(1 − W^a)`,
      `V_u = frozenElliptic p u`,  `χ ≤ 0`.

  Here `F_u = frozenWaveOperator p c u` (Statements.lean:2704) and `B = Ū` is the
  committed cross-frozen super-barrier `frozenWaveOperator p c u Ū ≤ 0`
  (Statements:3643 etc.).

  ──────────────────────────────────────────────────────────────────────────
  THE ARGUMENT (fully discharged here, modulo the explicitly carried analytic
  inputs noted below).

  Set `φ = W − B`.  Suppose `φ` is positive somewhere.  By the two-sided tail
  `limsup_{|x|→∞} φ ≤ 0` + continuity, `φ` attains a positive maximum at a finite
  `x₀`.  We carry "φ attains a positive max at `x₀`" as an explicit hypothesis
  (`IsMaxOn φ univ x₀ ∧ 0 < φ x₀`) — the attainment-from-limsup is standard but
  orthogonal to the order content and is supplied upstream.

  At `x₀`:
    * first-order:  `φ'(x₀) = 0`  ⟹  `W'(x₀) = B'(x₀)`   (`IsLocalMax.deriv_eq_zero`);
    * second-order: `W''(x₀) ≤ B''(x₀)`  (carried — the standard `φ''(x₀) ≤ 0`
      second-derivative test, no clean Mathlib lemma in v4.29.1).

  The ONE-SIDED MAX ESTIMATE then bounds the operator increment:

      `F_u(W) x₀ − F_u(B) x₀ ≤ C_B · (W x₀ − B x₀)`,    `h·C_B < 1`,

  assembled from (i) `W''−B'' ≤ 0`, (ii) `c(W'−B') = 0`, (iii) the reaction
  increment `reaction(W) − reaction(B) ≤ reactionLip·(W−B)` (committed
  `reaction_lipschitz_on_Icc`), and (iv) the chemotaxis increment
  `−χ[∂ₓ(W^m V')−∂ₓ(B^m V')] ≤ C_chem·(W−B)` (carried as `hchem`, derivable from the
  product-rule split `mV'(W^{m−1}−B^{m−1})W' + (W^m−B^m)V''` with `V''=V−u^γ`,
  `|V'|≤V≤1`, and the committed `rpow_m_lipschitz_on_Icc`).

  Then the step gives the contradiction:

      `G_h(W) x₀ = Z x₀ ≤ B x₀ ≤ B x₀ − h F_u(B) x₀ = G_h(B) x₀`   (uses F_u(B)≤0),

  while `G_h(W) − G_h(B) = (W−B) − h(F_u(W)−F_u(B)) ≥ (1 − h C_B)(W−B) > 0`
  at the positive max.  Contradiction.  Hence `φ ≤ 0`, i.e. `W ≤ B` everywhere.

  ──────────────────────────────────────────────────────────────────────────
  WHAT IS UNCONDITIONAL HERE (vs. the old `WaveRotheTrap` residual):
  the comparison is UNCONDITIONAL on any source-difference sign / resolvent
  positivity.  It carries only (a) the satisfiable two-sided tail packaged as an
  attained positive max, (b) the C²-regularity facts at the max (W'=B' is proven
  from φ'(x₀)=0; W''≤B'' is carried), and (c) the one-sided estimate, whose
  reaction half is proven from the committed Lipschitz fact and whose chemotaxis
  half is carried as the explicit `hchem`.
-/
import ShenWork.Paper1.WaveRotheStep
import ShenWork.Paper1.WaveRotheOrder

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

variable {c lam : ℝ}

/-! ## 0 — the implicit step `G_h` and pointwise pieces of `F_u` -/

/-- The implicit-Euler step operator `G_h(W) = W − h·F_u(W)`, `h = 1/λ`,
`F_u = frozenWaveOperator p c u`.  The step equation is `G_h(W) = Z`. -/
def implicitStepOp (p : CMParams) (c h : ℝ) (u W : ℝ → ℝ) : ℝ → ℝ :=
  fun x => W x - h * frozenWaveOperator p c u W x

@[simp] theorem implicitStepOp_apply (p : CMParams) (c h : ℝ) (u W : ℝ → ℝ) (x : ℝ) :
    implicitStepOp p c h u W x = W x - h * frozenWaveOperator p c u W x := rfl

/-- The chemotaxis flux `Q_u(W) y = (W y)^m · V'(y)`, `V = frozenElliptic p u`, so
that the chemotaxis term of `F_u` is `−χ · (Q_u W)'`. -/
def chemFlux (p : CMParams) (u W : ℝ → ℝ) : ℝ → ℝ :=
  fun y => (W y) ^ p.m * deriv (frozenElliptic p u) y

/-- `frozenWaveOperator` split into its four named pieces at a point. -/
theorem frozenWaveOperator_eq_pieces (p : CMParams) (c : ℝ) (u W : ℝ → ℝ) (x : ℝ) :
    frozenWaveOperator p c u W x =
      iteratedDeriv 2 W x + c * deriv W x
        - p.χ * deriv (chemFlux p u W) x
        + reactionFun p.α (W x) := by
  unfold frozenWaveOperator chemFlux reactionFun
  ring

/-! ## 1 — the one-sided max estimate

At a positive max `x₀` of `φ = W − B` we have `W'(x₀) = B'(x₀)`,
`W''(x₀) ≤ B''(x₀)`, `W(x₀) ≥ B(x₀)`, both in `[0,M]`.  The reaction increment is
`reactionLip`-Lipschitz; the chemotaxis increment is carried as `hchem`.  Assemble

    `F_u(W) x₀ − F_u(B) x₀ ≤ C_B · (W x₀ − B x₀)`,
    `C_B = reactionLip α M + C_chem`. -/

/-- **The one-sided max estimate.**  At `x₀` with the C²-regularity facts of a
positive max (`W' = B'`, `W'' ≤ B''`, range bounds `W,B ∈ [0,M]` and `B ≤ W`),
and the carried chemotaxis-increment bound `hchem`, the operator increment obeys

    `F_u(W) x₀ − F_u(B) x₀ ≤ (reactionLip α M + C_chem) · (W x₀ − B x₀)`.

The reaction half is the committed `reaction_lipschitz_on_Icc`; the second-order
and first-order terms vanish/are nonpositive; the chemotaxis half is `hchem`. -/
theorem implicitStep_oneSided_max_estimate
    (p : CMParams) {c M C_chem : ℝ} {u W B : ℝ → ℝ} {x₀ : ℝ}
    (hM : 0 ≤ M)
    (hWmem : W x₀ ∈ Set.Icc (0 : ℝ) M)
    (hBmem : B x₀ ∈ Set.Icc (0 : ℝ) M)
    (hBW : B x₀ ≤ W x₀)
    (hderiv1 : deriv W x₀ = deriv B x₀)
    (hderiv2 : iteratedDeriv 2 W x₀ ≤ iteratedDeriv 2 B x₀)
    (hchem : -p.χ * (deriv (chemFlux p u W) x₀ - deriv (chemFlux p u B) x₀)
        ≤ C_chem * (W x₀ - B x₀)) :
    frozenWaveOperator p c u W x₀ - frozenWaveOperator p c u B x₀
      ≤ (reactionLip p.α M + C_chem) * (W x₀ - B x₀) := by
  rw [frozenWaveOperator_eq_pieces, frozenWaveOperator_eq_pieces]
  -- reaction increment bound
  have hrxn : reactionFun p.α (W x₀) - reactionFun p.α (B x₀)
      ≤ reactionLip p.α M * (W x₀ - B x₀) := by
    have habs := reaction_increment_abs_le (a := p.α) (M := M) p.hα hM hBmem hWmem
    have hge : reactionFun p.α (W x₀) - reactionFun p.α (B x₀) ≤
        |reactionFun p.α (W x₀) - reactionFun p.α (B x₀)| := le_abs_self _
    have habs_eq : |W x₀ - B x₀| = W x₀ - B x₀ := abs_of_nonneg (by linarith)
    rw [habs_eq] at habs
    linarith
  -- second-order term ≤ 0, first-order term = 0
  have hd1 : c * deriv W x₀ - c * deriv B x₀ = 0 := by rw [hderiv1]; ring
  -- assemble
  nlinarith [hrxn, hchem, hderiv2, hd1]

/-! ## 2 — the maximum principle (unconditional on the chemotaxis residual)

The comparison `W ≤ B` carrying only the attained positive max + the one-sided
estimate.  No source-difference sign is assumed. -/

/-- **`implicitStep_le_of_barrier_maxPrinciple` — the nonlinear implicit-step
maximum principle.**

Assumes:
* `hstep` — `W` solves the step:  `∀ x, G_h(W) x = Z x`.
* `hBsuper` — `B` is a step super-barrier:  `∀ x, F_u(B) x ≤ 0`.
* `hZB` — `Z ≤ B` pointwise.
* `hh` — `0 < h`.
* `hCB` — `h · C_B < 1`  (the contraction smallness, `h = 1/λ`, `C_B = reactionLip α M + C_chem`).
* `hC_chem_nonneg`, `hM` — `0 ≤ C_chem`, `0 ≤ M`.
* `hattain` — `φ = W − B` attains a max at `x₀` (`IsMaxOn (W−B) univ x₀`).
* `hloc` — that max is a `local` max (`IsLocalMax (W−B) x₀`), so `φ'(x₀)=0`.
* `hWdiff`, `hBdiff` — `W`,`B` differentiable at `x₀` (for the first-order test).
* `hderiv2` — second-derivative test `W''(x₀) ≤ B''(x₀)`.
* range/`hchem` — the trapped-range membership and the carried chemotaxis bound at `x₀`.

Conclusion: `∀ x, W x ≤ B x`.

The proof: if `φ x₀ ≤ 0` we are done by maximality.  Otherwise `φ x₀ > 0`; the
one-sided estimate + `F_u(B) ≤ 0` + the step give a strict contradiction. -/
theorem implicitStep_le_of_barrier_maxPrinciple
    (p : CMParams) {c h M C_chem : ℝ} {u Z W B : ℝ → ℝ} {x₀ : ℝ}
    (hh : 0 < h) (hM : 0 ≤ M) (hC_chem_nonneg : 0 ≤ C_chem)
    (hCB : h * (reactionLip p.α M + C_chem) < 1)
    (hstep : ∀ x, implicitStepOp p c h u W x = Z x)
    (hBsuper : ∀ x, frozenWaveOperator p c u B x ≤ 0)
    (hZB : ∀ x, Z x ≤ B x)
    (hattain : IsMaxOn (fun x => W x - B x) Set.univ x₀)
    (hloc : IsLocalMax (fun x => W x - B x) x₀)
    (hWdiff : DifferentiableAt ℝ W x₀) (hBdiff : DifferentiableAt ℝ B x₀)
    (hderiv2 : iteratedDeriv 2 W x₀ ≤ iteratedDeriv 2 B x₀)
    (hWmem : W x₀ ∈ Set.Icc (0 : ℝ) M)
    (hBmem : B x₀ ∈ Set.Icc (0 : ℝ) M)
    (hchem : -p.χ * (deriv (chemFlux p u W) x₀ - deriv (chemFlux p u B) x₀)
        ≤ C_chem * (W x₀ - B x₀)) :
    ∀ x, W x ≤ B x := by
  -- Reduce to:  φ x₀ ≤ 0,  where x₀ is the max.
  have hmax : ∀ x, W x - B x ≤ W x₀ - B x₀ := by
    intro x
    have := hattain (Set.mem_univ x)
    simpa using this
  suffices hx0 : W x₀ - B x₀ ≤ 0 by
    intro x; have := hmax x; linarith
  by_contra hpos
  push_neg at hpos  -- hpos : 0 < W x₀ - B x₀
  have hBW : B x₀ ≤ W x₀ := by linarith
  -- first-order: φ'(x₀) = 0  ⟹  W'(x₀) = B'(x₀)
  have hφderiv : deriv (fun x => W x - B x) x₀ = 0 :=
    hloc.deriv_eq_zero
  have hderiv1 : deriv W x₀ = deriv B x₀ := by
    have hsub : deriv (fun x => W x - B x) x₀ = deriv W x₀ - deriv B x₀ :=
      deriv_sub hWdiff hBdiff
    rw [hsub] at hφderiv
    linarith
  -- one-sided estimate
  have hOneSided :=
    implicitStep_oneSided_max_estimate (p := p) (c := c) (M := M) (C_chem := C_chem)
      (u := u) (W := W) (B := B) (x₀ := x₀)
      hM hWmem hBmem hBW hderiv1 hderiv2 hchem
  -- the step ⟹ G_h(W) x₀ = Z x₀ ≤ B x₀;  and B x₀ ≤ G_h(B) x₀ since F_u(B) ≤ 0.
  have hGW : W x₀ - h * frozenWaveOperator p c u W x₀ = Z x₀ := by
    have := hstep x₀; simpa [implicitStepOp_apply] using this
  have hGB_ge : B x₀ ≤ B x₀ - h * frozenWaveOperator p c u B x₀ := by
    have : 0 ≤ -(h * frozenWaveOperator p c u B x₀) :=
      neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hh.le (hBsuper x₀))
    linarith
  -- chain:  G_h(W) x₀ = Z x₀ ≤ B x₀ ≤ G_h(B) x₀
  have hChain : W x₀ - h * frozenWaveOperator p c u W x₀
      ≤ B x₀ - h * frozenWaveOperator p c u B x₀ := by
    rw [hGW]; exact le_trans (hZB x₀) hGB_ge
  -- so  (W−B) − h(F_u W − F_u B) ≤ 0  at x₀
  have hGdiff : (W x₀ - B x₀) - h * (frozenWaveOperator p c u W x₀
      - frozenWaveOperator p c u B x₀) ≤ 0 := by linarith
  -- but the one-sided estimate gives  F_u W − F_u B ≤ C_B (W−B),
  -- and  h·C_B < 1,  so  (W−B) − h(F_u W − F_u B) ≥ (1 − h C_B)(W−B) > 0.
  set Δ := W x₀ - B x₀ with hΔ
  set CB := reactionLip p.α M + C_chem with hCBdef
  have hΔpos : 0 < Δ := hpos
  -- h ≥ 0, so h·(F_u W − F_u B) ≤ h·(CB·Δ)
  have hstep_le : h * (frozenWaveOperator p c u W x₀ - frozenWaveOperator p c u B x₀)
      ≤ h * (CB * Δ) :=
    mul_le_mul_of_nonneg_left hOneSided hh.le
  -- (1 − h·CB)·Δ > 0
  have hcoef_pos : 0 < 1 - h * CB := by linarith [hCB]
  have hbig_pos : 0 < (1 - h * CB) * Δ := mul_pos hcoef_pos hΔpos
  -- Δ − h(F_u W − F_u B) ≥ Δ − h(CB Δ) = (1 − h CB)Δ > 0, contradiction with hGdiff
  nlinarith [hGdiff, hstep_le, hbig_pos]

/-- Dual lower-barrier comparison for one implicit step, proved by the same
maximum-principle calculation as `implicitStep_le_of_barrier_maxPrinciple`.

This is local at the positive maximum of `A - W`; no Green-kernel
representation is used. -/
theorem implicitStep_ge_of_barrier_maxPrinciple
    (p : CMParams) {c h M C_chem : ℝ} {u Z W A : ℝ → ℝ} {x₀ : ℝ}
    (hh : 0 < h) (hM : 0 ≤ M) (hC_chem_nonneg : 0 ≤ C_chem)
    (hCB : h * (reactionLip p.α M + C_chem) < 1)
    (hstep : ∀ x, implicitStepOp p c h u W x = Z x)
    (hAsub : ∀ x, 0 ≤ frozenWaveOperator p c u A x)
    (hAZ : ∀ x, A x ≤ Z x)
    (hattain : IsMaxOn (fun x => A x - W x) Set.univ x₀)
    (hloc : IsLocalMax (fun x => A x - W x) x₀)
    (hWdiff : DifferentiableAt ℝ W x₀)
    (hAdiff : DifferentiableAt ℝ A x₀)
    (hderiv2 : iteratedDeriv 2 A x₀ ≤ iteratedDeriv 2 W x₀)
    (hAmem : A x₀ ∈ Set.Icc 0 M)
    (hWmem : W x₀ ∈ Set.Icc 0 M)
    (hchem :
      -p.χ * (deriv (chemFlux p u A) x₀ - deriv (chemFlux p u W) x₀)
        ≤ C_chem * (A x₀ - W x₀)) :
    ∀ x, A x ≤ W x := by
  have hmax : ∀ x, A x - W x ≤ A x₀ - W x₀ := by
    intro x
    have := hattain (Set.mem_univ x)
    simpa using this
  suffices hx₀_nonpos : A x₀ - W x₀ ≤ 0 by
    intro x
    have := hmax x
    linarith
  by_contra hpos_not
  push_neg at hpos_not
  have hWA : W x₀ ≤ A x₀ := by linarith
  have hφderiv : deriv (fun x => A x - W x) x₀ = 0 :=
    hloc.deriv_eq_zero
  have hderiv_sub :
      deriv (fun x => A x - W x) x₀ = deriv A x₀ - deriv W x₀ :=
    deriv_sub hAdiff hWdiff
  have hderiv_eq : deriv A x₀ = deriv W x₀ := by
    rw [hderiv_sub] at hφderiv
    linarith
  have hFdiff :
      frozenWaveOperator p c u A x₀ - frozenWaveOperator p c u W x₀
        ≤ (reactionLip p.α M + C_chem) * (A x₀ - W x₀) :=
    implicitStep_oneSided_max_estimate (p := p) (c := c) (M := M)
      (C_chem := C_chem) (u := u) (W := A) (B := W) (x₀ := x₀)
      hM hAmem hWmem hWA hderiv_eq hderiv2 hchem
  have hGW :
      W x₀ - h * frozenWaveOperator p c u W x₀ = Z x₀ := by
    have := hstep x₀
    simpa [implicitStepOp_apply] using this
  have hGA_le_A :
      A x₀ - h * frozenWaveOperator p c u A x₀ ≤ A x₀ := by
    have hmul : 0 ≤ h * frozenWaveOperator p c u A x₀ :=
      mul_nonneg hh.le (hAsub x₀)
    linarith
  have hGA_le_GW :
      A x₀ - h * frozenWaveOperator p c u A x₀
        ≤ W x₀ - h * frozenWaveOperator p c u W x₀ := by
    calc
      A x₀ - h * frozenWaveOperator p c u A x₀
          ≤ A x₀ := hGA_le_A
      _ ≤ Z x₀ := hAZ x₀
      _ = W x₀ - h * frozenWaveOperator p c u W x₀ := hGW.symm
  have hGdiff :
      (A x₀ - W x₀) - h *
          (frozenWaveOperator p c u A x₀ - frozenWaveOperator p c u W x₀) ≤ 0 := by
    linarith
  set Δ := A x₀ - W x₀ with hΔ
  set CB := reactionLip p.α M + C_chem with hCBdef
  have hΔpos : 0 < Δ := hpos_not
  have hstep_le :
      h * (frozenWaveOperator p c u A x₀ - frozenWaveOperator p c u W x₀)
        ≤ h * (CB * Δ) :=
    mul_le_mul_of_nonneg_left hFdiff hh.le
  have hcoef_pos : 0 < 1 - h * CB := by linarith [hCB]
  have hbig_pos : 0 < (1 - h * CB) * Δ := mul_pos hcoef_pos hΔpos
  nlinarith [hGdiff, hstep_le, hbig_pos]

/-- Paper-operator lower-barrier comparison for one implicit step.

The barrier side uses `paperWaveOperator` (the expanded paper operator), while
the unknown step still uses the actual `frozenWaveOperator` from
`implicitStepOp`.  The only analytic input is the one-sided difference estimate
between these two operators at the positive maximum of `A - W`. -/
theorem implicitStep_ge_of_paperBarrier_maxPrinciple
    (p : CMParams) {c h M C_chem : ℝ} {u Z W A : ℝ → ℝ} {x₀ : ℝ}
    (hh : 0 < h)
    (hCB : h * (reactionLip p.α M + C_chem) < 1)
    (hstep : ∀ x, implicitStepOp p c h u W x = Z x)
    (hAsub : 0 ≤ paperWaveOperator p c u A x₀)
    (hAZ : ∀ x, A x ≤ Z x)
    (hattain : IsMaxOn (fun x => A x - W x) Set.univ x₀)
    (hFdiff :
      paperWaveOperator p c u A x₀ - frozenWaveOperator p c u W x₀
        ≤ (reactionLip p.α M + C_chem) * (A x₀ - W x₀)) :
    ∀ x, A x ≤ W x := by
  have hmax : ∀ x, A x - W x ≤ A x₀ - W x₀ := by
    intro x
    have := hattain (Set.mem_univ x)
    simpa using this
  suffices hx₀_nonpos : A x₀ - W x₀ ≤ 0 by
    intro x
    have := hmax x
    linarith
  by_contra hpos_not
  push_neg at hpos_not
  have hGW :
      W x₀ - h * frozenWaveOperator p c u W x₀ = Z x₀ := by
    have := hstep x₀
    simpa [implicitStepOp_apply] using this
  have hGA_le_A :
      A x₀ - h * paperWaveOperator p c u A x₀ ≤ A x₀ := by
    have hmul : 0 ≤ h * paperWaveOperator p c u A x₀ :=
      mul_nonneg hh.le hAsub
    linarith
  have hGA_le_GW :
      A x₀ - h * paperWaveOperator p c u A x₀
        ≤ W x₀ - h * frozenWaveOperator p c u W x₀ := by
    calc
      A x₀ - h * paperWaveOperator p c u A x₀
          ≤ A x₀ := hGA_le_A
      _ ≤ Z x₀ := hAZ x₀
      _ = W x₀ - h * frozenWaveOperator p c u W x₀ := hGW.symm
  have hGdiff :
      (A x₀ - W x₀) - h *
          (paperWaveOperator p c u A x₀ - frozenWaveOperator p c u W x₀) ≤ 0 := by
    linarith
  set Δ := A x₀ - W x₀ with hΔ
  set CB := reactionLip p.α M + C_chem with hCBdef
  have hΔpos : 0 < Δ := hpos_not
  have hstep_le :
      h * (paperWaveOperator p c u A x₀ - frozenWaveOperator p c u W x₀)
        ≤ h * (CB * Δ) :=
    mul_le_mul_of_nonneg_left hFdiff hh.le
  have hcoef_pos : 0 < 1 - h * CB := by linarith [hCB]
  have hbig_pos : 0 < (1 - h * CB) * Δ := mul_pos hcoef_pos hΔpos
  nlinarith [hGdiff, hstep_le, hbig_pos]

/-! ## 3 — the chemotaxis-increment supplier (the carried `hchem`, derived)

At `x₀` the chemotaxis-flux increment splits, using `W'(x₀)=B'(x₀)`, as

    `(Q_u W)'(x₀) − (Q_u B)'(x₀)
        = m V'(x₀)(W^{m−1}−B^{m−1})·W'(x₀) + (W^m−B^m)·V''(x₀)`,

with `V''=V−u^γ` (committed `frozenElliptic_deriv_deriv_eq`), `|V'|≤V≤1`, and
`s↦s^{m−1}`, `s↦s^m` Lipschitz on `[0,M]` (committed `rpow_m_lipschitz_on_Icc`).
Bounding each factor yields the explicit `C_chem`.  We expose the structural
SPLIT identity as the carried hypothesis and discharge the bound from it, so the
heavy product/chain-rule expansion (differentiability of `W^m`, `V'`) is the one
explicitly named analytic input rather than re-derived from scratch. -/

/-- **Chemotaxis increment bound from the split identity.**
Given the product-rule split of the flux increment at `x₀` (with `W'(x₀)=B'(x₀)`
already substituted), and the committed analytic bounds
`|V'(x₀)| ≤ 1`, `|V''(x₀)| ≤ Cvpp`, the Lipschitz/MVT facts
`|W^{m−1}−B^{m−1}| ≤ L1·(W−B)`, `|W^m−B^m| ≤ Lm·(W−B)` on `[0,M]`, and `|W'(x₀)| ≤ Cwp`,
derive

    `−χ·[(Q_u W)'−(Q_u B)'](x₀) ≤ C_chem·(W−B)(x₀)`,
    `C_chem = (−χ)·(p.m·L1·Cwp + Lm·Cvpp)`.

This supplies the `hchem` hypothesis of the maximum principle. -/
theorem chemFlux_increment_bound
    (p : CMParams) {u W B : ℝ → ℝ} {x₀ : ℝ}
    {Cvpp Cwp L1 Lm C_chem : ℝ}
    (hχ : p.χ ≤ 0)
    (hBW : B x₀ ≤ W x₀)
    -- the product-rule split identity at x₀ (W'=B' substituted):
    (hsplit : deriv (chemFlux p u W) x₀ - deriv (chemFlux p u B) x₀
        = p.m * deriv (frozenElliptic p u) x₀
            * ((W x₀) ^ (p.m - 1) - (B x₀) ^ (p.m - 1)) * deriv W x₀
          + ((W x₀) ^ p.m - (B x₀) ^ p.m) * deriv (deriv (frozenElliptic p u)) x₀)
    -- analytic bounds:
    (hVp : |deriv (frozenElliptic p u) x₀| ≤ 1)
    (hVpp : |deriv (deriv (frozenElliptic p u)) x₀| ≤ Cvpp) (hCvpp : 0 ≤ Cvpp)
    (hWp : |deriv W x₀| ≤ Cwp) (hCwp : 0 ≤ Cwp)
    (hL1 : |(W x₀) ^ (p.m - 1) - (B x₀) ^ (p.m - 1)| ≤ L1 * (W x₀ - B x₀)) (hL1' : 0 ≤ L1)
    (hLm : |(W x₀) ^ p.m - (B x₀) ^ p.m| ≤ Lm * (W x₀ - B x₀)) (hLm' : 0 ≤ Lm)
    (hCchem : C_chem = (-p.χ) * (p.m * L1 * Cwp + Lm * Cvpp)) :
    -p.χ * (deriv (chemFlux p u W) x₀ - deriv (chemFlux p u B) x₀)
      ≤ C_chem * (W x₀ - B x₀) := by
  have hΔ : 0 ≤ W x₀ - B x₀ := by linarith
  have hmpos : 0 ≤ p.m := le_trans zero_le_one p.hm
  -- bound the two summands of the split in absolute value
  -- term 1: |m V' (W^{m-1}-B^{m-1}) W'| ≤ m·1·(L1 Δ)·Cwp
  have hterm1 :
      |p.m * deriv (frozenElliptic p u) x₀
          * ((W x₀) ^ (p.m - 1) - (B x₀) ^ (p.m - 1)) * deriv W x₀|
        ≤ p.m * L1 * Cwp * (W x₀ - B x₀) := by
    have e1 : |p.m * deriv (frozenElliptic p u) x₀
          * ((W x₀) ^ (p.m - 1) - (B x₀) ^ (p.m - 1)) * deriv W x₀|
        = p.m * |deriv (frozenElliptic p u) x₀|
            * |(W x₀) ^ (p.m - 1) - (B x₀) ^ (p.m - 1)| * |deriv W x₀| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hmpos]
    rw [e1]
    -- p.m * |V'| * |Δrpow| * |W'|  ≤  p.m * 1 * (L1 Δ) * Cwp
    set A := |deriv (frozenElliptic p u) x₀| with hA
    set D := |(W x₀) ^ (p.m - 1) - (B x₀) ^ (p.m - 1)| with hD
    set E := |deriv W x₀| with hE
    have hA0 : 0 ≤ A := abs_nonneg _
    have hD0 : 0 ≤ D := abs_nonneg _
    have hE0 : 0 ≤ E := abs_nonneg _
    -- step 1: p.m * A * D * E ≤ p.m * 1 * D * E   (A ≤ 1)
    have s1 : p.m * A * D * E ≤ p.m * 1 * D * E := by
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hVp hmpos) (mul_nonneg hD0 hE0)
      nlinarith [this]
    -- step 2: p.m * 1 * D * E ≤ p.m * (L1*(W-B)) * Cwp
    have s2 : p.m * 1 * D * E ≤ p.m * (L1 * (W x₀ - B x₀)) * Cwp := by
      have hDle : D ≤ L1 * (W x₀ - B x₀) := hL1
      have hEle : E ≤ Cwp := hWp
      have hpm1 : (0:ℝ) ≤ p.m * 1 := by positivity
      have hL1Δ0 : 0 ≤ L1 * (W x₀ - B x₀) := mul_nonneg hL1' hΔ
      nlinarith [mul_le_mul hDle hEle hE0 hL1Δ0, hpm1, hmpos]
    have hfinal : p.m * (L1 * (W x₀ - B x₀)) * Cwp = p.m * L1 * Cwp * (W x₀ - B x₀) := by
      ring
    calc p.m * A * D * E ≤ p.m * 1 * D * E := s1
      _ ≤ p.m * (L1 * (W x₀ - B x₀)) * Cwp := s2
      _ = p.m * L1 * Cwp * (W x₀ - B x₀) := hfinal
  -- term 2: |(W^m-B^m) V''| ≤ (Lm Δ)·Cvpp
  have hterm2 :
      |((W x₀) ^ p.m - (B x₀) ^ p.m) * deriv (deriv (frozenElliptic p u)) x₀|
        ≤ Lm * Cvpp * (W x₀ - B x₀) := by
    rw [abs_mul]
    set P := |(W x₀) ^ p.m - (B x₀) ^ p.m| with hP
    set Q := |deriv (deriv (frozenElliptic p u)) x₀| with hQ
    have hP0 : 0 ≤ P := abs_nonneg _
    have hQ0 : 0 ≤ Q := abs_nonneg _
    have hPle : P ≤ Lm * (W x₀ - B x₀) := hLm
    have hQle : Q ≤ Cvpp := hVpp
    have hLmΔ0 : 0 ≤ Lm * (W x₀ - B x₀) := mul_nonneg hLm' hΔ
    calc P * Q ≤ (Lm * (W x₀ - B x₀)) * Cvpp :=
          mul_le_mul hPle hQle hQ0 hLmΔ0
      _ = Lm * Cvpp * (W x₀ - B x₀) := by ring
  -- combine: |split| ≤ (p.m L1 Cwp + Lm Cvpp) Δ
  have hsplit_abs : |deriv (chemFlux p u W) x₀ - deriv (chemFlux p u B) x₀|
      ≤ (p.m * L1 * Cwp + Lm * Cvpp) * (W x₀ - B x₀) := by
    rw [hsplit]
    calc |p.m * deriv (frozenElliptic p u) x₀
            * ((W x₀) ^ (p.m - 1) - (B x₀) ^ (p.m - 1)) * deriv W x₀
          + ((W x₀) ^ p.m - (B x₀) ^ p.m) * deriv (deriv (frozenElliptic p u)) x₀|
        ≤ |p.m * deriv (frozenElliptic p u) x₀
            * ((W x₀) ^ (p.m - 1) - (B x₀) ^ (p.m - 1)) * deriv W x₀|
          + |((W x₀) ^ p.m - (B x₀) ^ p.m) * deriv (deriv (frozenElliptic p u)) x₀| :=
          abs_add_le _ _
      _ ≤ p.m * L1 * Cwp * (W x₀ - B x₀) + Lm * Cvpp * (W x₀ - B x₀) := by
          linarith [hterm1, hterm2]
      _ = (p.m * L1 * Cwp + Lm * Cvpp) * (W x₀ - B x₀) := by ring
  -- finally multiply by (−χ) ≥ 0
  have hnegχ : 0 ≤ -p.χ := neg_nonneg.mpr hχ
  have hle_signed : -p.χ * (deriv (chemFlux p u W) x₀ - deriv (chemFlux p u B) x₀)
      ≤ -p.χ * |deriv (chemFlux p u W) x₀ - deriv (chemFlux p u B) x₀| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hnegχ
  have hle2 : -p.χ * |deriv (chemFlux p u W) x₀ - deriv (chemFlux p u B) x₀|
      ≤ -p.χ * ((p.m * L1 * Cwp + Lm * Cvpp) * (W x₀ - B x₀)) :=
    mul_le_mul_of_nonneg_left hsplit_abs hnegχ
  calc -p.χ * (deriv (chemFlux p u W) x₀ - deriv (chemFlux p u B) x₀)
      ≤ -p.χ * |deriv (chemFlux p u W) x₀ - deriv (chemFlux p u B) x₀| := hle_signed
    _ ≤ -p.χ * ((p.m * L1 * Cwp + Lm * Cvpp) * (W x₀ - B x₀)) := hle2
    _ = C_chem * (W x₀ - B x₀) := by rw [hCchem]; ring

/-! ## Axiom audit -/

section AxiomAudit
#print axioms frozenWaveOperator_eq_pieces
#print axioms implicitStep_oneSided_max_estimate
#print axioms implicitStep_le_of_barrier_maxPrinciple
#print axioms implicitStep_ge_of_barrier_maxPrinciple
#print axioms implicitStep_ge_of_paperBarrier_maxPrinciple
#print axioms chemFlux_increment_bound
end AxiomAudit

end ShenWork.Paper1
