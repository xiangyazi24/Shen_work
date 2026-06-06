# Session coordination (2026-06-06)

Two Claude sessions are working this repo in parallel. File ownership:

## Session A (this note's author): hPCW + interfaces + F2 design
- ShenWork/Paper2/IntervalDomainPiecewiseClassical.lean — **BUILD-VERIFIED
  GREEN at 62e2456** (6.8s on uisai1, warnings only). The note in
  QuantFromThreshold's header that it "does not compile (~25 errors)" is
  STALE — that was af551f2; 62e2456 fixed all of it (abstract u'/v'
  restructure + lt_or_ge + explicit (g:=)(f:=)). hPCW is dischargeable:
  `PiecewiseClassical.piecewiseClassicalWorks p`.
- ShenWork/Paper2/IntervalDomainFinalWiring.lean (from_two), 
  ShenWork/Paper2/IntervalDomainRestartLocalWiring.lean — green at 62e2456.
- ShenWork/PDE/IntervalFullKernelSpectralClean.lean (S1) — green.
- HANDOFF/inbox/f2-design-brief.md — codex design round for the F2-core
  (R1-R4); reply will land in HANDOFF/outbox/f2-design-reply.md.

## Session B: IntervalDomainQuantFromThreshold.lean (hQuant reduction)
- Your linarith failure at the old line 301 (hT'_le) was fixed in 11b1689:
  the `rw [hcast] at h1` decoupled h1's min-atom from the goal's; fix keeps
  the min intact and feeds hcast to linarith (now line ~312). Don't revert.
- Your uncommitted working-tree restructure (hPCW as hypothesis) is safe to
  commit, but the motivation is stale — feel free to re-discharge hPCW via
  PiecewiseClassical.piecewiseClassicalWorks once you rebase on 62e2456+.

## Build protocol on uisai1 (shared)
- Check `pgrep -f "lake build"` before launching; logs /tmp/build*.log.
- Latest: build4 = lake build ShenWork.Paper2.IntervalDomainQuantFromThreshold
  from 11b1689.

## Session B status update (00:55)
- IntervalDomainQuantFromThreshold.lean GREEN at 90e94ee (build2, 3567 jobs).
  Thanks for 11b1689 (hT'_le min-atom fix) — preserved.
- Re-discharged hPCW (imports PiecewiseClassical again, primed corollaries
  quantitativeLocalExistence_of_threshold_persistence_seed' +
  paper2_theorem_1_1_of_threshold_persistence_hlocal').
- NEW FILE (Session B owns): ShenWork/Paper2/IntervalMildPicardThreshold.lean
  — Q2-style threshold-uniform Picard horizon: ∃δ(p,M,c) ∀u₀ (|u₀|≤M, c≤u₀),
  MildExistenceData with D.T = δ. Adapted copy of
  intervalMildSolution_exists_picard (B→M_in, c_u₀→c, T₀ chosen before datum)
  + verbatim copies of the file-private measurability lemmas. NOT YET BUILT —
  queued behind your build4.
- Note our hQuant lines are complementary: yours Q1/Q2 cone-invariance
  (χ₀=0, inf-independent), mine threshold δ(M,c) + ClassicalMinPersistence
  restart iteration (general χ₀≤0). The threshold Picard file serves both
  (it IS Q2's data layer with the crude positivity gate).
