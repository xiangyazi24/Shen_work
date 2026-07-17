# DOCTRINE — Shen_work 5-frontier grind (2026-07-17)

## Main goal
Close all 5 remaining open frontiers (1D) sequentially.

## Avenues (in order)

### (a) Paper 1 Theorem 1.2 — tail asymptotics
Terminal: sorry count in ShenWork/Paper1/ reduced; capstone wired or carried only on Henry-class imported infra.
Attack: audit sorry in Paper1/, identify leaf sorry, grind each.

### (b) Paper 3 Theorem 2.3 — χ₀≤0 global stability, general-m
Terminal: unconditional on intervalDomainM (no hm : p.m = 1).
Attack: port m=1 proof using Thm 2.4 general-m infrastructure from 07-16.
**STATUS: DONE (0 sorry). Commit 1897737a.**
- Both branches (nonminimal + minimal) fully proved and axiom-clean.
- IntervalDomainMMinimalChiNonposConvergence.lean (1045 lines): full convergence chain.
- IntervalDomainMTheorem23Eventual.lean: capstone wiring, all 5 theorems clean.

### (c) Paper 3 Theorem 2.5 — minimal a=b=0 stability
**STATUS: ALREADY DONE (0 sorry, faithful to paper — m=1 is the paper's own statement).**

### (d) Paper 2 supporting — Prop 2.2/2.4/2.5, Lem 2.6, Cor 2.1
Terminal: each stated + proved or carried on headline-level hypotheses.
Attack: audit each statement, find producers, wire.

### (e) General-N infrastructure
Terminal: architectural plan + partial infrastructure beyond 1D.
Attack: abstract intervalDomain to general bounded domain.

## Constraints
- mini DOWN — uisai1 only
- Build: /dev/shm/lean/Shen_work-active (lake build in progress)
- Working copy: /home/xhuan5/Shen_work (synced, no warm build)
