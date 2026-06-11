# FIDELITY AUDIT — Paper 2 Theorem 1.1 (independent adversarial, 2026-06-11)

Per formalization-playbook §3.3 + Group C.  Independent read-only auditor +
orchestrator source re-verification.  Verdict labels: FAITHFUL / CONDITIONAL /
FRAGMENT / IMPOSTOR.

## The paper (Chen–Ruau–Shen, paper2.pdf)
Theorem 1.1 assumes **χ₀ ≤ 0**, general domain **Ω ⊂ ℝᴺ**, parameters α,γ > 0.
Part (1) a,b>0: ‖u(t)‖∞ ≤ max{‖u₀‖∞,(a/b)^{1/α}} on (0,Tmax), m≥1 ⟹ Tmax=∞.
Part (2) a=b=0: limsup‖u‖∞ ≤ ‖u₀‖∞, m≥1 ⟹ Tmax=∞.

## What Lean has (HEAD f93cbda)

| Axis | Verdict | Evidence |
|---|---|---|
| Q1 parameter coverage | **FRAGMENT (→IMPOSTOR)** | every route to `Theorem_1_1 intervalDomain p` requires `hχ0 : p.χ₀ = 0` + `0<a` + `0<b`; χ₀=0 decouples the model to scalar reaction-diffusion (`Statements.lean:93-96`, term `−p.χ₀·chemotaxisDiv`). χ₀<0 untouched (repo's own INTEGRITY_GAPS:902-918: "likely impossible" this route). |
| Q2 statement layer | **FAITHFUL, not hollow** ✅ — but N=1 | `IsPaper2ClassicalSolution` asserts the real u-PDE + τ=0 v-equation + Neumann BC pointwise (`Statements.lean:70-100`); `intervalDomain` instantiates laplacian/chemotaxisDiv/supNorm for real (`IntervalDomain.lean:2756,2919,2923`); `classicalRegularity` is a genuine 9-conjunct C² predicate (`:2768`). BUT `intervalDomain.Point = Subtype (Icc 0 1)` = **N=1** (`:2746`), dodging the paper's N≥2 elliptic core. |
| Q3 conclusion | a,b>0 genuine; **a=b=0 VACUOUS** | `IntervalDomainMoserClosure.lean:746-800`: a,b>0 branch delivers Tmax>0 + bound + real m≥1 global clause; a=b=0 branch entered only under contradictory 0<a∧a=0. |
| Q4 residual | **CONDITIONAL on plausibly-UNSATISFIABLE certificate** | `TowerConeAnalyticResidual = { hsrc0 }` (`TowerSupply.lean:120-125`); `hsrc0 : ∀n, DuhamelSourceTimeC1(canonical)` demands ℓ¹ envelope at s=0 (`IntervalDuhamelClosedC2.lean:1502-1518`) — for merely-continuous u₀ the t=0 coeffs need not be ℓ¹ (the documented t→0 disease, same class as the FIXED hL_cont vacuity bug). The paper's hard analytic content relocated into a hypothesis (假设偷换 / certificate anti-pattern). |
| Q5 axiom integrity | **RESOLVED — CLEAN-TREE CERTIFIED** | Fresh f93cbda checkout (/dev/shm/shen_verify, mathlib cache reused, ShenWork rebuilt from clean source): capstone closure built 3680 jobs EXIT 0; `#print axioms` on `paper2_theorem_1_1_chiZero_unconditional`, `..._from_coneSupply`, `from_cone_construction` ALL = `[propext, Classical.choice, Quot.sound]` — **no sorryAx, no custom axioms**. The pre-fix docstring claim of inherited sorryAx was STALE (fixed). The earlier full-build "failure" was a transient dependency race (ConeQuantBridge builds standalone, 3610 jobs). So the theorem is a LEGITIMATE conditional theorem (not hollow-via-sorry); the analytic content lives honestly in the `hsrc0` hypothesis (Q4), not in a hidden sorry. |

## BOTTOM LINE
Unconditionally proved of the paper's Theorem 1.1: **essentially none of its
mathematical substance.** Every route is conditional on `hsrc0` = the paper's
hard content carried as a hypothesis, plausibly unsatisfiable as typed. What is
real: a FAITHFUL (non-hollow) statement layer, but only on N=1, χ₀=0 (decoupled,
non-chemotaxis), a,b>0, 1≤α, 1≤γ. Untouched: χ₀<0, a=b=0 (vacuous), N≥2,
Theorems 1.2/1.3. The repo's "unconditional"/"prize"/"done" language (incl. my
own Telegram reports and commit messages) OVERSTATED reality.

## ACTIONS
1. [done] Fidelity banner on the capstone docstring; corrected stale sorryAx/Hiter claims.
2. [DONE] Clean-tree certification: full ShenWork 8547 jobs EXIT 0 on fresh f93cbda + capstone axioms all [propext, Classical.choice, Quot.sound], no sorryAx. Mechanically sound end-to-end.
3. [next] hsrc0 go/no-go: prove satisfiable OR finish the BddOn replacement (W7-W9). Until then NO unconditional claim, even for the χ₀=0 fragment.
4. [standing] Independent adversarial audit before ANY headline claim. Verification env must be a clean checkout, not a rsync-patched cache.
