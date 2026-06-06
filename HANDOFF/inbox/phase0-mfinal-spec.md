# Phase-0 / M-final spec: the n-uniform joint induction (χ₀=0 gate theorem)

Target file (NEW, sole writer): ShenWork/Paper2/IntervalPicardIterateUniform.lean

## ARCHITECTURE (corrected 2026-06-06 ~03:10 — supersedes the earlier
"G2* := 2M₁Ē₂ + M2-uniform-G1" note in COORDINATION.md)

Power-counting audit: routing G1 through the coefficient sums feeds G1² back
into B_log and the recursion does NOT close at t→0 for any power profile.
The fix that closes:

* **G1-line (n-free, kernel route — NO recursion):**
  ∂ₓ lift(u_{n+1}(t)) = ∂ₓS(t)(lift u₀) + ∂ₓ∫₀ᵗS(t−s)L_n(s)ds (χ₀=0), so
    |∂ₓ lift(u_{n+1}(t))| ≤ heatGradientLinftyLinftyConstant/√t · M
                            + heatGradientLinftyLinftyConstant·2√t · CL
  with CL := M·(p.a + p.b·M^p.α) ≥ sup|L_n| (logistic sup on the M-ball,
  n-free via the ball bound). Atoms: the L∞→L∞ semigroup gradient bound
  (HeatKernelGradientEstimates.lean ~:2536, READ the wrapping theorem) +
  gradDuhamel_sup_bound (IntervalGradDuhamelBound.lean:72). Define
    G1profile t := Cg/√t·M + Cg·2√t·CL          (all explicit).
  NOTE: you must bridge |∂ₓ(value of intervalGradientDuhamelMap at χ₀=0)| to
  these two atoms — i.e. deriv distributes over the three-term sum and the
  flux term vanishes (0·∫ = 0; its deriv contribution is deriv of the
  constant-0 function — make the χ₀=0 reduction at the LIFT level first;
  M1's file has intervalGradientDuhamelMap_eq_of_chi0_zero-style lemmas —
  REUSE M1's reduction lemma if exported, else re-derive).
  CAVEAT: deriv-under-integral for the Duhamel term — gradDuhamel_sup_bound's
  statement form may already be about deriv of the integral (READ IT; it was
  built for exactly the contraction's needs). Match shapes; if it bounds
  a different arrangement (integral of deriv), use the repo's existing
  Leibniz bridges (IntervalDuhamelIntegrability / IntervalFullKernelLeibniz)
  — they exist because the contraction needed them.

* **G2-line (coefficient route with profile recursion):**
  G2profile t := A₂ / t²  with A₂ explicit, chosen so that both:
   (a) base case: |∂ₓ²S(t)u₀-series| ≤ 2M·eigExpWeight(t/2)·(use M1-rep at
       n=0? simpler: the n=0 slice is the pure homogeneous series; bound via
       M2-uniform's abstract lemma + homogeneous_eigenvalue_tsum_le +
       eigExpWeight_le: ≤ 2M·C₂/(t/2)² — so A₂ ≥ 8M·C₂·(safety));
   (b) step: via M2-uniform's iterate_abs_deriv2_le:
       |∂ₓ²u_{n+1}(t)| ≤ M₁·eigExpWeight(t/2) + Cgain·(t/2)^{1/4}·Benv(t)
       where M₁ ≤ 2M (half-step coefficient bound from the ball) and
       Benv(t) = max(2·B_log(p.a,p.b,p.α,M,G1profile(t/2),G2profile(t/2)),
                     M·(p.a+p.b·M^p.α))   (M3's envelope at window [t/2,t],
       using monotone-decreasing profiles: sup over the window = value at t/2).
       The gate condition (hypothesis of the final theorem, explicit):
         (GATE) ∀ t ∈ (0,T]: 2M·C₂/(t/2)² + Cgain·(t/2)^{1/4}·Benv(t) ≤ A₂/t²
       — derive a SUFFICIENT closed-form smallness condition on T of the shape
         Cgain·(T/2)^{1/4}·(p.a + p.b·(1+p.α)·M^p.α)·(4·safety) ≤ 1/2-ish
       (the G1²-part of B_log scales like 1/t — strictly subordinate to 1/t²
       for t ≤ T ≤ 1, absorb it with an explicit T ≤ 1 assumption and a
       constant; SHOW THE ARITHMETIC in comments). If deriving the cleanest
       sufficient condition gets heavy, you may state the gate condition
       itself as the (GATE) hypothesis ∀-quantified as above — it is explicit
       and checkable; report which form landed.
* **M-line**: ball bound n-free — take as hypothesis the ball facts in the
  shape the existing IntervalMildPicard machinery provides (READ
  picardIter_ball's signature and take ITS hypotheses), do not re-prove.
* **floor-line**: positivity floor m ≤ u_n: take as carried hypothesis
  (threshold class provides it; M3's K2 needs it).
* **time-line**: K1 fields from M3b (READ ShenWork/Paper2/
  IntervalPicardIterateTimeC1.lean — LANDED, match its exact output shapes)
  with Mdot profile; src from M3 (IntervalPicardIterateSourceC1.lean).
* **rep-line**: M1 (IntervalPicardIterateRestart.lean).

## Deliverable
A structure `PicardIterateUniformData (p) (u₀) (T) (n) : Prop`-or-structure
carrying exactly the fields above (explicit profiles), plus:
  theorem picardIterateUniformData_zero : ...base case...
  theorem picardIterateUniformData_succ : Data n → Data (n+1)   (under GATE)
  theorem picardIterateUniformData_all : (GATE) → ∀ n, Data n
The hypotheses of _zero/_succ must each be satisfiable-by-design (header
notes); the carried global hypotheses (datum regularity, ball facts, floor,
GATE smallness, T ≤ 1) are fine.
If full closure of one line walls, land the others + the walled line as a
named field-level hypothesis with justification (honest-partial). PRIORITIZE:
G2-line recursion (the genuinely new gate content) > rep/src/time wiring >
base case polish.

## Constraints
Standard: new file only; scp + lake env lean loop on uisai1 (NEVER lake
build; oleans via lake env lean -o); 0 sorry/admit/axiom/native_decide;
explicit constants; #print axioms = 3 standard; commit ONLY your file:
"Phase-0 M-final: n-uniform joint induction (chi0=0 gate)", push with the
untracked-copy dance. Pitfalls: set/beta; HO-unification (g:=)(f:=);
positivity doesn't unfold defs; renames lt_or_le→lt_or_ge, le_or_lt→le_or_gt,
tsum_le_tsum→Summable.tsum_le_tsum; rw [defName] fails → simp only.
