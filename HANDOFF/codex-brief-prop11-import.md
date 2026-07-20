# Codex Brief — Prop 1.1 residual window: the imported-input interface + capstone

Repo ~/Shen_work (HEAD 812b7d1a). Rules: 0 sorry, 0 axiom, NEW files only, build
green per file, append imports to ShenWork.lean. Do NOT commit, do NOT edit
existing files. Design source: HANDOFF/gpt-Q135-import-interface.md (verified).

## The design (Q135, verified against the repo)

The residual window 1 ≤ χ (critical exponent, paper1PositiveCriticalThreshold)
is closed the way the SOURCE closes it: local BUC theory + a-priori L^∞ bound +
blow-up alternative — the first and third being an imported citation
(Salako–Shen JDE 262 (2017), verified at paper1.pdf p.6). Formalize the import as
ONE explicit hypothesis in the style of `hcore` in Theorem12Corrected.lean, NOT
a typeclass, NOT a record of unrelated estimates.

Two files.

### I1. `WholeLineMaximalBUCImport.lean`
Define the imported input as a Prop bundling exactly what the continuation proof
consumes (Q135 §"Repository vocabulary" — note IsCUnifBdd is only cont+bdd, use
the BUC submodule `WholeLineBUC` as the carrier):
- a maximal existence horizon `Tmax ∈ (0, ∞]` and an orbit `u, v` on `[0, Tmax)`;
- `IsGlobalNonnegativeCauchySolutionFrom`-style finite-subhorizon classical/mild
  identities + nonnegativity + initial trace (mirror the fields of the committed
  `IsGlobalNonnegativeCauchySolutionFrom`, restricted to `t < Tmax`);
- the WEAK projection of the blow-up alternative that the proof actually uses:
    `(u uniformly bounded in BUC on [0,Tmax))  →  Tmax = ⊤`.
  (Weaker than limsup‖u‖∞=∞; that is fine — a future proof of the cited theorem
  instantiates this.)

### I2. `Proposition11PositiveLargeImport.lean`
The capstone, conditional ONLY on I1's hypothesis `hmax`:
```
theorem Proposition_1_1_positive_critical_large_of_maximalBUC
  (p : CMParams) (hcritical : p.α = p.m + p.γ - 1)
  (hχ1 : 1 ≤ p.χ) (hthreshold : paper1PositiveCriticalThreshold p)
  (hmax : WholeLineMaximalBUCImport p)   -- the single imported input
  (hStage3 : <the L^{P/m}→L^∞ gradient semigroup bound, as an explicit hyp>)
  (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀) :
  ∃ u v, IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧ UniformEventuallyBounded u
```
Proof chain (all pieces committed except hStage3, which is carried):
1. extract P from `paper1PositiveCriticalThreshold_iff_exists_admissible_exponent`
   (Proposition11PositiveErrata.lean);
2. `UniformlyLocalLpBounded` from the committed local-moment producers
   (WholeLineLocalMomentGlobalProducer.lean) — a-priori translation-uniform L^P;
3. `‖v_x‖_∞` from WholeLineChiLargeGradientBound.lean;
4. hStage3 (carried): the gradient semigroup step `L^{P/m}→L^∞`, Q135's
   `‖∂x e^{(Δ−I)τ}f‖∞ ≤ Cq e^{−τ} τ^{−(1/2+1/2q)} ‖f‖_q` at q=P/m>1 — this is the
   ONE genuinely missing analytic estimate; carry it as an explicit hypothesis
   with the exact constant, do NOT stub it with an axiom;
5. combine 2+3+4 into a uniform `‖u‖_∞` bound on `[0,Tmax)`;
6. feed hmax's blow-up projection ⟹ Tmax = ⊤ ⟹ global; `UniformEventuallyBounded`
   from the same bound.

DELIVERABLE: both files green, hStage3 and hmax the ONLY carried hypotheses,
clean-3. Report which downstream steps needed adaptation. Then a combined
theorem over the full faithful threshold (critical χ<1 from the committed
branch ∪ this 1≤χ branch). If a step can't be done, STOP with the exact goal.
