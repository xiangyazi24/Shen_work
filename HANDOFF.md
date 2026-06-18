# HANDOFF — Shen trilogy formalization (Opus → Codex)

Date: 2026-06-18. Written at HEAD `d774b63`. Read `docs/CHECKLIST.md` FIRST — it is the authoritative
live map. This file is the operating manual + deep context the checklist can't hold.

## GOAL (Stop-hook, non-negotiable)
Complete the formalization of all THREE Chen–Ruau–Shen chemotaxis papers (`~/repos/Shen_work`, GitHub
`xiangyazi24/Shen_work`), **judged by passing the playbook audit** (`~/.openclaw/workspace/formalization-playbook.md`
§3.3). Playbook audit = FAITHFUL + no faking: no `sorry`/`admit`/`native_decide`/custom `axiom`; no VACUOUS
conditional theorems (unsatisfiable hypotheses); no carrying the paper's hard content as a hypothesis and
calling it done. Every banked result is **full-build verified + `#print axioms` = `[propext, Classical.choice,
Quot.sound]`**.

## THE THREE NON-NEGOTIABLE DISCIPLINES (these caught real regressions)
1. **FULL-BUILD before banking, never single-file.** `lake env lean <file>` (single-file) MASKED a ripple
   that broke the headline (the PaperIterateBase change → WaveRotheFloor). ALWAYS verify with
   `~/.elan/bin/lake build ShenWork.Paper1.WaveLemma42G1Discharge` (full headline module) on the codex dir,
   then pull to local + commit. Confirm "Build completed successfully (8308 jobs)" + headline axiom-clean.
2. **No faking, no re-carrying.** Codex (gpt-5.5) has been EXCELLENT at honest stalls — it refuted a FALSE
   "absolute ω" lemma I proposed, caught two circularities, and flagged unsatisfiable interfaces. TRUST those
   stalls; they locate the real next atom. Do NOT pressure it to close something false. The only field
   permitted to stay CARRIED is `hboxCubeData` (the finite-net Schauder witness — the SAME floor the outer G1
   carries; see below). Everything else must be PROVEN.
3. **Verify before claim.** Count real sorries with proof-position regex `(:=|by|=>)\s*sorry`, not bare word.
   Use `git diff` as the authoritative deletion check. Read the actual source before asserting structure.

## CURRENT STATE (Paper 1 headline)
Live headline: `b1_chiNeg_existence_paper_clean_of_cubeApproxData` (WaveLemma42G1Discharge.lean). It assembles
cleanly; the ONLY substantive open floor is `hprodAll` (the per-step Rothe producer). Everything else is
discharged (outer G1 Schauder, hflat, hsmp, hstationary + cx_r3 uniform-bounds, hlim_neg, antitone).

### The per-step (`hprodAll`) — route and status
Construction = **truncated fixed-source box Schauder** (ChatGPT-validated, the only faithful route; raw-mapsTo
is FALSE because chemotaxis transport breaks it). Solve `R = paperStepSource_truncated(u, Z, greenConv R)` on a
**weighted-Hölder source box**, set `W = greenConv R`, then a-priori bounds show the truncation inactive.
PROVEN + committed (see `docs/CHECKLIST.md` for the box-by-box ledger and commit hashes):
- truncated-operator max-principle (non-circular) + `truncation_inactive` (direct, paperDiff-free)
- weighted-Hölder box, β case-split (0<β≤1), greenConv left-tail limits, iterate-regularity threading
- Lemma 1 `paperFixedSourceMap_holder_kernel` (β-Hölder modulus), Lemma 2 `…leftTailCauchy_kernel`
- `continuousOn` (internal), map_bound
- **A+ (1/2)**: `ExpLeftRate` predicate + kernel moments `m_σ`/`m_σ¹` + greenConv/greenConvDeriv rate
  preservation + inner-orbit `left_rate` threading + exponential-ω box bridge (d774b63)

### IMMEDIATE NEXT (in flight RIGHT NOW on the codex dir, not yet banked)
**A+ (2/2)** — spec at `/tmp/shen_pde_urate.md` on uisai2, log `/tmp/cx_pde_urate.log`. The gap codex pinned:
the per-step's frozen `u` only carries `InMonotoneWaveTrapSet` (left LIMIT, no exponential RATE), so
`V = frozenElliptic(u)` lacks the rate the source-map contraction needs. The fix (two-layer threading):
1. Thread `u`'s exponential left-rate through the OUTER orbit (`u` is itself a per-step output `W` carrying the
   rate; outer seed `upperBarrier` has rate 0). May force a +rate field on the OUTER iterate predicate /
   WaveLemma42* — codex must REPORT before touching those.
2. `frozenElliptic_expLeftRate`: V inherits u's rate ((D²−1) resolvent, kernel ½e^{−|·|}, moment 1/(1−σ²)).
3. Materialize the explicit `paperFixedSourceMap_expLeftRate` contraction `Cλσ·C_R + A_Z·C_Z + D0`, all O(λ⁻¹).
4. Two-radius: `C_Z = m_σ·C_R`, condition `Cλσ + A_Z·m_σ < 1`, box `ω = K_R·exp(σ(·−aL))` → close
   `map_leftTail`/`map_leftTailCauchy`/`ascoliCompactRange`, carry ONLY `hboxCubeData`.
KEY fact (verified): source is `paperStepNonlinearity(u, greenConv R) + lam·Z` — the `λ` is on the FIXED `Z`,
NOT `greenConv R`, so the W-dependence is λ-free and `Cλσ = O(λ⁻¹)` → contraction is REAL. If you ever see
`lam * greenConv R`, STOP — that would break it.

### After the box closes (still inside hprodAll)
- `boxCubeData` (B.4): the finite-net `ProjectedCubeApproxData` for the source box. This MAY legitimately stay
  CARRIED — it is the SAME approximation-theory floor the OUTER G1 Schauder already carries (`b1_…_clean` is
  the unconditional outer version; the cube data is its parameter). If the outer one is genuinely closed,
  mirror it; otherwise both are the same recognized shared floor. Do NOT fake a finite-net witness.
- Wire `of_truncated_sourceBox → … → paperRotheStepProducer_of_routeA_greenCore` ⟹ `hprodAll` unconditional.
- Also secondary headline floors `hstep`/`htail` (PaperRotheSeqStepDependence / TailUniform) — WARMAP marks
  them vestigial under the direct route; revisit after the box.

## DISPATCH RECIPE (how to drive the build agent)
Builds + grinds run on **uisai2** (Mac mini local builds are OFF; ~/repos is git source + commit point only).
- Codex working dir: `/var/tmp/shen_cx_pde` (synced from HEAD). Lean toolchain = **v4.29.1** (Shen_work pins
  it; do NOT "upgrade to 4.30" — that breaks the build; several repos still on 4.29.x/4.27).
- Write a contract-grade spec to `/tmp/shen_pde_*.md`, `scp` it, then (two SEPARATE ssh calls — the combined
  pkill+launch races on the ssh ControlSocket and silently drops the launch):
  ```
  ssh uisai2 'pkill -f "shen_cx_pde.*codex exec"'
  ssh uisai2 'cd /var/tmp/shen_cx_pde && nohup ~/bin/codex exec --dangerously-bypass-approvals-and-sandbox \
    --skip-git-repo-check -m gpt-5.5 -c model_reasoning_effort=xhigh "Read /tmp/shen_pde_X.md and execute it
    exactly. … ACCEPTANCE = FULL lake build … green + axiom-clean, verify before reporting. No faking." \
    > /tmp/cx_pde_X.log 2>&1 & echo PID $!'
  ```
  Use `~/bin/codex` (full path; bare `codex` not on the non-interactive PATH). Keep the inline prompt free of
  shell-glob chars (`<`, `*`, backticks) — zsh will choke; put detail in the spec file.
- Monitor via file mtime/size + `tail` the log + `ps aux | grep "[s]hen_cx_pde"`. Do NOT char-poll tmux.
- On a deliverable: pull the changed files, `git diff` deletion-check (additive?), copy to local,
  **full-build-verify yourself**, then commit (+ push), then tick `docs/CHECKLIST.md`.
- Spec files for the current campaign are on uisai2 `/tmp/shen_pde_*.md` (reuse as templates).

## ChatGPT Pro (design consults) — when codex hits a genuine analytic fork
`python3 ~/.openclaw/workspace/scripts/ask-gpt.py cron < q.txt` (run_in_background; long-thinks 10–20 min,
notifies on return). It validated the truncbox route, the weighted-Hölder box, the left-end lemma, and the A+
exponential-rate majorant. Use it for "which route is faithful/cheapest", not code gen. VERIFY its claims
against source (it once proposed a false absolute-ω that codex correctly refuted).

## ROADMAP after Paper 1
- **Paper 2**: DONE (Schauder, 0 real sorry, axiom-clean).
- **Paper 3** (`ShenWork/Paper3/`): statement-complete + build-clean (0 sorry/admit/axiom), but the headline
  `Paper3MainlineTargets` is CONDITIONAL on ~6 unproven PDE floors (P3.1 global existence, P3.2 uniform
  persistence Thm 2.1, P3.3 stability dichotomy Thm 2.2, P3.4 sectorial decay, P3.5 compactness, P3.6 global
  stability Thm 2.3–2.5; P3.7 small threshold tails). Only the unit-point ODE case + χ* formula are
  unconditional. These floors are the same depth as Paper 1's per-step. See `docs/CHECKLIST.md` Paper 3 section.

## INFRA NOTES
- Disk: Mac mini was 99% full; cleaned (uv cache + 9 local `.lake` dirs, all regenerable since builds are
  remote). 92G free now. Local `.lake` for any repo regenerates on first local build.
- Telegram: report to Xiang at chat_id `-5278910619`, plain text (NO markdown/##/tables), address him 你.
- `docs/WARMAP.md` is an older floor-map; `docs/CHECKLIST.md` supersedes it as the live tracker.
