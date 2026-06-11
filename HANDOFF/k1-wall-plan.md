# K1 wall battle plan (2026-06-10 19:4x, Zinan hand-written)

## The wall, precisely
`TowerConeAnalyticResidual` is down to 7 fields, all one root:
- `hsrc0 : ∀ n, DuhamelSourceTimeC1 (fun s k => coeff(logistic(picardIter n s)))`
- `hL_cont`, `adot`, `hadot_deriv`, `hadot_cont`, `adotBound`, `hadot_bound`

`DuhamelSourceTimeC1` (IntervalDuhamelClosedC2:1502) demands GLOBAL data:
`hderiv` at every `s : ℝ`, `hadotcont` on ℝ, ℓ¹ `envelope` for ALL `s ≥ 0`
(including `s = 0` — the t→0 disease: no summable envelope at 0 for merely
continuous u₀), `derivBound` on `[0,∞)`.  As typed for the CANONICAL family
this is plausibly unsatisfiable-in-spirit; the honest content lives on
interior windows `[a',b'] ⊂ (0,T]`.

## The key identity (why the wall should fall)
Per-mode FTC on the restart representation: at level `n+1`,

    d/ds bc_{n+1}(s,k) = -λ_k·bc_{n+1}(s,k) + src_n(s,k)        (*)

— the iterate-coefficient time derivative needs only level-`n` source VALUES,
no derivatives.  Then

    ∂_s u_{n+1}(s,x) = Σ' (-λ_k bc + src_n)·cos(kπx)

(differentiate the cosine series term-by-term; domination on windows:
`Σλ|bc| < ∞` is the tower's hrepr_sum, `src_n` has the stage-F windowEnv).
Finally

    adot_{n+1}(s,k) = ∫₀¹ logistic'(u_{n+1})·∂_s u_{n+1}·cos(kπx) dx

(differentiation under the spatial integral, dominated).  Level 0 explicit:
bc_0 = e^{-sλ}û₀, all derivatives in closed form.

So the K1 data should be producible BY INDUCTION over levels — the same
induction shape the tower already runs for hrepr/hG1/hG2/srcWin.

## Attack steps
1. READ `IntervalPicardIterateTimeC1Full.lean` in full: what exactly do
   `picardIterate_K1_full_from_restart_of_representation` (line ~100) and
   `clampedIterateSource_duhamelSourceTimeC1` (line ~241) consume — same-level
   adot (upgrade lemma) or previous-level (induction step)?  Also grep the
   per-mode FTC lemma ("weak restart identity + per-mode FTC" from the
   campaign ledger — likely in IntervalPicardIterateTimeC1.lean /
   IntervalSourceCoefficientTimeC1.lean).
2. If the step lemma is same-level: build the missing inductive step from (*)
   — new file, window-local: `WindowK1 n → WindowK1 (n+1)` where
   `WindowK1 n` = adot data on every compact `[a',b'] ⊂ (0,T]` + window
   envelopes.  Reuse: hasDerivAt_tsum_of_isPreconnected (DuhamelClosedC2),
   stage-F slice decay, tower hrepr/hG1/hG2, logistic chain rule
   (logisticSourceDot machinery in TimeC1Full §D.1 — already there!).
3. Consumers audit: who eats hsrc0's GLOBAL fields?  srcWin_of_levelData,
   shift_nonneg (witness src), hiter_cont_of_tower, hbsum_succ chains.
   Each likely reads only (0,T] windows → retype consumers windowed OR patch
   via the C¹ soft clamp (IntervalTimeSoftClamp) to produce the literal
   global package from window data — clampedIterateSource_duhamelSourceTimeC1
   may BE that upgrade lemma already.
4. Surgery: TowerLevel gains a srcK1 field (window K1 data); tower_zero
   explicit; tower_succ via the new step; residual fields
   hsrc0/adot/hadot_* DELETED (hL_cont may fall too — logistic slice
   continuity from representation + Weierstrass).
5. Verify: remote single-file → full build → #print axioms both theorems
   = [propext, Classical.choice, Quot.sound]; md5; commit+push; TG report.

## Rules
No axiom, no local lake build, no fake satisfaction; remote = rsync (never
--delete) → uisai2:/dev/shm/shen_work; acceptance = #print axioms only.
