# F2-core design round: route to classical local existence (Paper2 Thm 1.1)

## Your task (DESIGN ONLY — no Lean code, output a design document)

Repo: ~/repos/shen_work (Lean4 + Mathlib v4.29.1). Paper 2 Theorem 1.1 is reduced
(all wiring proved, 0 sorry) to three residual frontiers:
- ThresholdQuantitativeLocalExistence (Picard δ(M,c) classical existence on
  {|u₀|≤M, u₀≥c}) — see ShenWork/Paper2/IntervalDomainQuantFromThreshold.lean
- ClassicalMinPersistence (quantitative strong minimum principle) — same file
- hlocal / hMildLocal: per-datum classical local existence, currently routed
  through the Picard mild solution + a regularity bootstrap that needs
  GradientMildHalfStepRestartData (abstract source family a t : ℝ → ℕ → ℝ with
  DuhamelSourceTimeC1 envelope + restart cosine agreement hagree) — see
  ShenWork/Paper2/IntervalMildRegularityBootstrap.lean (RestartCosineRepresentation),
  ShenWork/Paper2/IntervalDomainRestartLocalWiring.lean (faithful interface),
  INTEGRITY_GAPS.md (2026-06-06 entry), TASK_QUEUE.md (S1-S6/Q1-Q4 roadmap).

The mild map is the DIVERGENCE-form gradient Duhamel map (ShenWork/Paper2/
IntervalGradientDuhamelMap.lean):
  Φ(u₀,u)(t,x) = S(t)u₀(x) − χ₀ ∫₀ᵗ ∂ₓ[S(t−s) Q(u s)](x) ds + ∫₀ᵗ S(t−s) L(u s)(x) ds
S = intervalFullSemigroupOperator (Neumann heat propagator, full periodised kernel),
Q = chemotaxis flux (C⁰ on the ball), L = logistic source.

## Discovered obstructions (verify, then design around)

1. **Logistic-only hagree unsatisfiable for χ₀ ≠ 0** (INTEGRITY_GAPS.md): the
   half-step restart source must contain the flux contribution; z↦z(a−bz^α) is
   bounded above for α ≥ 1, the flux part is not. Already fixed at interface
   level (abstract GradientMildHalfStepRestartData).
2. **Two-semigroup obstruction**: ∂ₓ[S^N(r)g] = S^D(r)[g'] (Neumann derivative
   = Dirichlet evolution of the derivative; kernel identity ∂ₓK_N(x,y) = −∂_yK_D(x,y)).
   Hence S^N(τ)[flux-part of u(t/2)] ≠ flux-part propagated to time t: the naive
   restart/cocycle identity FAILS termwise in the gradient form. The genuine-source
   restart u(t) = S^N(τ)u(t/2) + ∫₀^τ S^N(τ−σ)[−χ₀(Q)_x + L]dσ holds for CLASSICAL
   solutions (variation of constants), but classical regularity of the Picard limit
   is exactly what we are trying to prove (circularity).
3. **Wiener envelope**: DuhamelSourceTimeC1 requires ∑ₙ supₛ|aₙ(s)| < ∞. For the
   flux part aₙ ⊇ cosine coeffs of (Q)_x; with u only C², Q'' is only C⁰ and the
   coefficients are o(1/n), NOT summable. Needs u ∈ C^{2,γ}-ish (or coefficient-space
   control giving u'' in the Wiener algebra). One bootstrap round from C⁰ does not
   reach this.
4. **S(0) ≠ id**: heatKernel 0 ≡ 0 definitional degeneracy
   (ShenWork/PDE/IntervalSemigroupAtZero.lean): any FTC/variation-of-constants
   argument must use ε-restart + one-sided limits, never the value at 0.
   The existing intervalDuhamelRepresentation_of (IntervalDuhamelRepresentation.lean)
   consumes the unsatisfiable S(0)=id predicate — it is vacuous as stated and needs
   restatement in ε-restart form.

## Candidate routes — compare and rank

R1 **Spectral-space Picard**: run the fixed point directly on coefficient families
   (û_n(t)); flux enters via the explicit mode-mixing c_k((Q)_x) (sine↔cosine);
   choose a weighted sequence space (e.g. sup_t ∑_k (1+λ_k)|û_k(t)| or ℓ¹ with
   parabolic weights) where the Duhamel integral regains one power of λ and the
   contraction closes; regularity and hagree hold by construction.
R2 **Iterate induction with two-semigroup split**: represent each Picard iterate as
   cosine part + Dirichlet-evolved flux part; carry C² with uniform constants
   through the induction (PicardIterateHasC2Slices exists, qualitative); pass to
   the limit by G2.5 (duhamelSourceTimeC1_of_uniform_limit, proved).
   Requires building the Dirichlet kernel/semigroup machinery (currently absent).
R3 **Classical-first Schauder-lite**: a fixed point in a C^{2,γ}-type ball using the
   proved Lᵖ/L∞ smoothing (H0.1/H0.2: intervalHeatSemigroup_Lp_Lq_bound,
   heatGradientLinftyLinfty) + interval Hölder bootstrap, bypassing restart
   representations entirely; afterwards hagree for classical solutions follows from
   an ε-restart representation theorem (fixing obstruction 4).
R4 **χ₀ = 0 first**: close the logistic-only architecture for the flux-free
   sub-regime (cocycle clean, single semigroup; S2-S6 in TASK_QUEUE.md), defer χ₀<0.

## Deliverables (write to ~/repos/shen_work/HANDOFF/outbox/f2-design-reply.md)

1. Verify or refute each obstruction (cite exact repo lemmas; if you think an
   obstruction is wrong, give the precise identity that fixes it).
2. Ranked comparison of R1–R4 (+ any better R5) by: total new-code estimate,
   number of genuinely-new analytic atoms, risk of hidden unsatisfiable
   hypotheses, reuse of existing 8k-job infrastructure.
3. For the winner: full dependency DAG, precise Lean statements (signatures) of
   the first 3 modules, and a satisfiability audit of every new hypothesis/
   predicate you introduce (cite the S(0)=id and logistic-hagree precedents —
   no plausible-but-unsatisfiable interfaces).
4. Honest risk register: what could kill the route after 2 weeks of work.

Read the actual repo files before opining. Do not write Lean code. Do not touch
any file outside HANDOFF/outbox/.
