# RUN_LOG — shen_work autonomous run

## Run 2026-06-11 ~05:35
- doctrine: HANDOFF/DOCTRINE.md (+ ROADMAP.md)
- approval: Xiang "提交 skill 然后按照路线图清单逐个推, 自主执行" + /automode + /fable
- starting avenue: (a) A-line endpoint stack — codex W8d in flight; (b) D2/D3 — opus in flight; route 2nd-opinion — ChatGPT Pro in flight
- 06-11 05:40 avenue (b) CLOSED: D2 IMPOSTOR banners landed (abcb884); D3 + semigroup-wiring reclassified as Lᵖ mountain (avenue C), not quick wins. Only genuine quick win was D2 banners.
- 06-11 05:40 route validated: ChatGPT Pro (cron) rejected the hi↑T density shortcut ("hides the same endpoint derivative proof behind limits, more painful in Lean") — STAY Route A. codex W8d actively grinding the one-sided endpoint stack.
- 06-11 06:1x endpoint sub-lemma foundation COMPLETE + audited: W7/W7b/W8-D1/W8e(crux)/W8g(cosineCoeffs bridge)/W8h(joint-cont _On) all independent-adversarial-audit PASS, committed (8ce81dd). Crux (per-mode endpoint left-deriv, W8e) Fable-broken + codex-executed.
- 06-11 06:2x BIG SWING (codex reset window, xhigh): W9 (A-line total: adot assembly→endpoint legs→wire→DELETE hsrc0 @shen_codex), D2 (vacuous semigroup→real heat-kernel @shen_codex4), C1 (L²energy sorries @shen_codex3) — 3 parallel xhigh codex. Fable holds the high-care W9 step-3 (delete hsrc0 + Σ' fix).
- 06-11 11:2x C1 = NULL (FALSE ALARM caught by adversarial audit + self-recheck): my `\bsorry\b` grep counted DOCSTRING mentions ("no sorry"/"NOT a sorry"), NOT proof terms. The 3 L²energy files had ZERO real sorries in HEAD — the open content is a NAMED RESIDUAL OBLIGATION (packaged as a hypothesis, like hsrc0), not a sorry. codex C1 only edited docstrings (reverted). No "10 sorries closed" — that headline was a grep artifact; the playbook discipline caught it before any false claim. ROADMAP correction: avenue C's L²energy foundation is CONDITIONAL on a named frontier residual, not complete.
- LESSON: count sorries as PROOF TERMS (`:= sorry` / `by sorry` / standalone), never `\bsorry\b` (matches docstrings). Re-audit any prior sorry-count claims.
- end: <open>
- final result: <open>

## Run 2026-07-12 (resumed automode, session = shen window)
- doctrine: HANDOFF/DOCTRINE-P31.md (Paper 3 P3.1)
- approval: handoff /tmp/zinan_handoff_shen.md automode:yes + "不要等指示,立即继续推进"
- starting avenue: (a) Gap A eventualSupBound [independent of Codex χ<0]
- parallel: Codex owns χ<0 (tmux win 6, 3h43m in, HSpectral wiring); I do NOT re-drive it.
- end: <fill on close>
- final result: <fill on close>

### P3.1 results (2026-07-12, session = shen window) — COMMITTED
- Gap A eventualSupBound DISCHARGED for the paper regime, axiom-clean:
  eventualSupBound_of_global_posAB (0<a,0<b), _zeroAB (a=b=0). Proof = Lemma_3_1_intervalDomain
  invariant region + INTERIOR reference time t=1 (no initial-trace approach dep). commit 3f4fce99.
- proposition_1_2_of_theorem_1_1_posAB : Theorem_1_1 intervalDomain p → Proposition_1_2 intervalDomain p
  (0<a,0<b). The clean P3.1 reduction to Paper 2's main theorem, PPID-typed (no PID datum-class detour). commit 0fe943de.
- proposition_1_2_intervalDomain_chiZero : P3.1 UNCONDITIONAL for χ₀=0, 0<a,0<b,1≤α,1≤γ (axiom-clean).
  FIRST Paper 3 headline closed. commit 6314f552.
- χ<0 / full χ₀≤0 closure recorded as ready one-liner (proposition_1_2_of_theorem_1_1_posAB ∘
  paper2_theorem_1_1_intervalDomain_chiNonpos_..._of_reducedCoreData) — deferred to cold build
  (EWA import not single-file-compilable). commit 4cd21cda. Auto-closes when Codex lands Theorem_1_1(χ<0).
- OPEN (low priority): a=0,b>0 corner of eventualSupBound (degenerate no-growth; helpers max_point_slope_bound/
  supNorm_nonincr_core are non-private so ~30-line follow-up); a>0,b=0 genuinely FALSE (pure growth) — field
  over-stated there, honestly scope to {0<a,0<b}∪{a=b=0}. Cold uisai2 gate on new file still pending.
- All verified single-file (lake env lean) + #print axioms = propext/Classical.choice/Quot.sound.

## Run 2026-07-20 (resumed automode, session = cron window)
- doctrine: HANDOFF/session-2026-07-20.md + FARLEFT_BRIEF.md (on branch codex/farleft-energy)
- approval: "cont shen work proof! /automode"
- starting avenue: (a) far-left equilibrium convergence beyond chi<1/2 — resume branch codex/farleft-energy in worktree ../Shen_work_farleft

### Avenue (a) — TERMINAL: SUCCESS, merged to main at befbd13d (build 9970 jobs green)
- Inherited claim "the 4 branch commits are build-verified" was FALSE.
  WholeLineChiPosHalfLineSharpRectangle.lean had 2 real errors compiling to
  sorryAx (positivity could not see 0<=chi / 0<1-chi; a stray `ring` after
  field_simp). Fixed (def34a37).
- m>1 sharp rectangle: threshold chi<1/2  ->  chi*gamma < alpha*(1-chi),
  i.e. chi < alpha/(alpha+gamma).
- NEW: chiStar_le_sharpThreshold_of_cubic — exact condition for that threshold
  to cover the paper's whole window is P = m^3+m^2(g-2)+m(1-3g)-2g^2 >= 0.
  Streamlined headline stableRegime_chi_pos_..._of_cubic (regime already
  carries chi<chiStar and the critical exponent).
- SELF-CORRECTION: the first commit quoted "gamma+2 <= m", which MISSES the
  band where the result has new content (gamma>=2). Exact cubic is the right
  hypothesis; documented in the module docstring.

### Avenue (b) — OPEN: refined ceiling coefficient (widen toward alpha/(2gamma))
- Found independently and CONFIRMED by ChatGPT (Q155): the ceiling absorption
  M'^(m-1)(M'^g - l'^g) <= M'^a - l'^a is crude. By homogeneity it is an
  IDENTITY with coefficient c(t) = (1-t^g)/(1-t^a), t = l'/M', and c is
  non-increasing with c(0+)=1, c(1-)=g/a.
- t is bounded below by the SEED aspect ratio (ell increases, M decreases), so
  no circularity: t0 comes from the chi<1 equilibrium-height trap.
- Landed: chiPos_squeeze_gap_step_refined_ceiling (coefficient c0 carried),
  chiPos_refined_contraction_iff (chi < alpha/(gamma + alpha*c0)),
  chiStar_le_limitThreshold_of_poly (Q = m^3+g*m^2-(g+1)m-2g^2-2g >= 0 is the
  exact condition for alpha/(2gamma) >= chiStar; root 1.6590 at g=1 vs 2.2695
  for the c0=1 cubic P), chiStar_le_limitThreshold_of_gamma_add_one_le.
- Codex DELIVERED the c(t) monotonicity lemma (WholeLineChiPosCeilingRatio.lean),
  routed through Mathlib's convexOn_rpow / secant_mono_aux1. Verified by me
  independently in main (single-file, clean-3) rather than on its own report;
  note it did NOT commit, so the file had to be picked up by hand.
- Avenue (b) is now CLOSED end-to-end and the coefficient is DISCHARGED, not
  carried: uniformCoMoving..._seedRatio takes no absorption hypothesis at all,
  only the contraction condition at c0 = (1-t0^g)/(1-t0^a), t0 = seed.ell/seed.M.
  The chain's containment in the seed box is proved by induction from
  ell_le / M_le.
- WALL (ChatGPT Q155, matches my own derivation): 2*chi*gamma < alpha is the
  INTRINSIC limit of any two-endpoint rectangle — the endpoint model permits
  worst-case anti-correlation between u and v. Beyond it a different mechanism
  is required.

### Avenue (c) — the real residual: near-equilibrium / Liouville
- ChatGPT Q155: the PDE's exact linearized spectral margin at u=1 is positive
  throughout chi<1, so the whole paper window is LOCALLY stable; the missing
  ingredient is ENTRY into a two-sided trap 1-eps <= u <= 1+eps. A merely
  positive floor d<=u is NOT enough.
- Also flagged: a genuine gap in the PAPER — Prop 1.2(2) is stated/proved only
  for chi<1/2, but Thm 1.2 Step 4 invokes it for chi<chi*. Verification
  question dispatched; do NOT record as fact until it returns.
- end: <open>
- final result: <open>
