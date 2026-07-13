# DOCTRINE — FULL formalization of the 3 Shen papers + pass the Lean playbook audit

Goal set by Xiang 2026-07-12 (automode): complete formalization of all three Shen chemotaxis papers, every headline
UNCONDITIONAL + NON-VACUOUS + faithful, passing the formalization-playbook audit.

## The three papers (repo dir → published)
- Paper1 (repo) — traveling-wave / Rothe existence (Theorem 1.1 negative+positive branches, tail asymptotics).
  Executor: Codex#3. Fable Rothe construction (source-box + finite-cube discharged via Schauder-Tychonoff + modulus L).
- Paper2 (repo) = arXiv:2512.14858 Part I "Boundedness and global existence". Theorems 1.1/1.2/1.3.
  Executor: Codex#1. Thm 1.2 positive-critical UNCONDITIONAL geOne VERIFIED; generalizing to all α,γ>0 (positive-strip
  local existence, Q4618 = paper-faithful). ERRATUM found+proven (a>0,b=0 guard).
- Paper3 (repo) = arXiv:2604.02599 Part II "Persistence and stabilization". Theorems 2.1–2.5.
  Executor: Codex#2. Stability keystone = eventual full-mode orbit bound (Fable restarted-Duhamel core built; concrete
  Nemytskii verified). ERRATUM found (Thm 2.2 (2.12) over-statement).

## Playbook audit gates (terminal quality bar — every headline must pass ALL)
1. 0 sorry / 0 admit.
2. Axiom-clean: #print axioms = [propext, Classical.choice, Quot.sound] only (verify via OWN remote-build.sh, NOT
   Codex self-report).
3. NON-VACUOUS: hypotheses satisfiable (concrete witness), conclusion genuinely inhabited/constructed. (Q4614 lesson:
   axiom-clean ≠ non-vacuous. The hglobalExtension vacuity was caught only by adversarial audit + trace.)
4. FAITHFUL statement: matches the arXiv source (not a repo paraphrase, not weakened). No `of_assumed_*` tautological
   escapes left in the discharge chain. Maximal-continuation / genuine existential where the paper says so.
5. No free/impossible hypotheses (the vacuity trap). Every carried hypothesis either discharged or a genuine
   satisfiable input with provenance.
6. Errata: where the paper's statement is wrong/over-broad, refute formally + amend faithfully + note (2 found so far:
   Paper2/Part I Thm 1.2 a>0,b=0; Paper3/Part II Thm 2.2 (2.12)).

## Driving method
- Three Codex, one per paper. Each headline: drive to unconditional, then I VERIFY two ways (own remote build axioms +
  non-vacuity trace/audit) BEFORE declaring closed.
- Map open targets from repo status files: PAPER_INVENTORY.md, THEOREM_STATUS.md, CLOSURE_MAP.md, UNPROVED_TARGETS.md,
  INTEGRITY_GAPS.md, TRILOGY_AUDIT.md. Cross-check against the playbook gates.
- ChatGPT (shen tabs, sees live code via autosync) = design + adversarial audits (vacuity/faithfulness). Fable =
  hardest analytic cores. Keep tabs full.
- Terminal audit: run the formalization-playbook audit (/code-review ultra or the playbook's own gates) over each
  paper's headline chain once individually closed.

## Immediate front (in progress)
- Thm 1.2 (Paper2): finish general α,γ>0 (Codex#1, positive-strip local existence Q4618) → full unconditional.
- Orbit bound (Paper3): Codex#2 wiring the eventual mass-free orbit bound to Thm 2.2/2.3/2.4/2.5.
- Rothe (Paper1): Codex#3 discharging source-box + finite-cube (Fable construction).

## Terminal condition
All headline theorems of all 3 papers: unconditional, non-vacuous, faithful, axiom-clean, passing the playbook audit;
errata documented. Then: run the playbook audit end-to-end; report the closure map.
