# Wiener-algebra build — route & doctrine (χ₀<0 unconditional regularity)

## ===== 合龙 VERDICT (ChatGPT cron RUN#278, 2026-06-13) — the join CLOSES in strategy but needs E_T^r =====
STATUS of the WA bottom layer: COMPLETE + hostile-audited (bricks 1..5: convolution alg, ring axioms,
∂ₓ, multipliers, resolver +2 gain, t^{-1/2} smoothing, √t self-map, eval+map_exp+recovery, D_exp,
DECISIVE estimate, Gamma Wiener–Lévy realPow_eval). 136 commits.
NOT a gap: (1) eval-vs-coefficient (realPow_eval returns a genuine WA 1 element, not an AddCircle function
— product/resolver act on the real element). (2) cos/sin↔ℤ adapter = plumbing (cos_k=a_k+a_{−k},
sin_k=i(a_k−a_{−k}), match ½-factor + zero mode). [brick 6a builds this]
THE REAL REMAINING THEOREM (yellow): the E_T^r COEFFICIENT-ENVELOPE layer. Committed PDE bricks consume
Σ_k sup_t|·| (sup INSIDE); static WA gives sup_t Σ_k (sup OUTSIDE) — implication FALSE (disjoint-bumps).
So build E_T^r = {a:ℤ→C([0,T],ℂ) : Σ_n(1+|n|)^r·sup_t‖a_n(t)‖<∞}, a Banach algebra under convolution
(product/resolver/∂ₓ are EASY lifts — rerun the coeff majorant with sup-norm coeffs), and RE-PROVE in it:
the decisive estimate (sup_t|coeff(e^{−su(t)})_n|≤e^{−δs}, mode-split identical) + Gamma WL (realPow_EWA)
+ the √t Duhamel + the flux time-chain (B_t = u_t·v_x·q + u·(v_t)_x·q + u·v_x·q_t). Finite weight ladder:
∂ₓB∈A⁰⟸B∈A¹; gradient leg⟸B∈A²; chemDiv time-chain safe at u∈E_T³ (u_t=u_xx−χ₀∂ₓB+G(u)∈A¹).
1+v FLOOR — RESOLVED, NOT A GAP (Explore a3df669): committed TWO ways. (1) intervalNeumannResolverR_nonneg_of_nonneg_source
(IntervalResolverPositivity.lean:489) PROVES 0≤R_μ(νu^γ)=v via heat-Laplace rep + positive Neumann kernel + closed
cone Ici 0. (2) 0≤v is a faithful STANDING hypothesis in IsPaper2ClassicalSolution (Paper2/Statements.lean:91,
the Chen–Ruau–Shen positive classical solution). ⇒ 1+v≥1>0. So the 合龙 has NO residual analytic gap; what
remains (E_T^r layer + flux time-chain) is PURE CONSTRUCTION (a mirror of the WA bricks + the flux assembly).
brick-6 map: 6a cos↔ℤ adapter [building] · 6b EWA Banach algebra · 6c EWA operators (∂ₓ,R_μ,√t Duhamel)
· 6d EWA realPow/WL [biggest] · 6e flux + time-chain · 6f feed duhamelSpectral_eigenvalueSummable_of_sourceL1.
Honest closure: WA(done)+E_T^r lift+E_T³ WL+floor(u,1+v)+flux time-chain+cos adapter ⇒ committed bricks close.
TWO INPUT/STRUCTURE conditions (from re-reading the A¹-closure audit,钉死): (i) u₀∈A¹ — the fixed point in
C([0,T];A¹) needs the initial data in A¹ at t=0 (committed S_N(t)u₀∈C²_x for t>0 does NOT give it); carry as
honest input. (ii) PARITY — ofCosineCoeffs (6a) is the EVEN/cosine embedding; but B=u·v_x·q is SINE/ODD
(even·odd·even), ∂ₓB back to cosine. So the adapter ALSO needs an ODD embedding ofSineCoeffs
(a_k=ĉ_k^sin/(2i), a_{−k}=−ĉ_k^sin/(2i)) to extract v_x/B coefficients — a 6a-sibling brick.
## ====================================================================================================

Goal: build, from scratch (Mathlib has NONE of this), the weighted Wiener algebra needed to
prove the chemotaxis divergence source `∂ₓB ∈ A` (B = u·v_x/(1+v)^β) for the actual nonlinear
Picard iterate — discharging the source-ℓ¹ hypotheses my committed duhamelSpectral bricks consume.
User decision (2026-06-13): build the unconditional Wiener–Lévy path, 稳打稳扎, one audited brick
at a time. Lean on ChatGPT (cron + cron2) for route design + adversarial check each brick.

## ===== CONSOLIDATED E_T^r PLAN (cron EWA-strategy + cron2 soundness, 2026-06-13) — awaiting sign-off =====
SOUNDNESS (cron2): architecture CAN close, NO circularity (fixed point uses source VALUES only; the adot/
time-chain is a POST-fixed-point regularity theorem, NOT an input to the contraction), NO hidden regress.
CONSTRUCTION (cron): build GENERIC `GWA K r` over [NormedCommRing K][NormedAlgebra ℂ K][CompleteSpace K];
WA r stays committed; EWA T r := GWA (C([0,T],ℂ)) r; bridge `sliceWA τ : EWA T r →A[ℂ] WA r` reuses committed
WA eval/decisive/recovery pointwise-in-t via NormedSpace.map_exp. Algebra layer transfers VERBATIM-generic.
r=3 for the chemDiv time-chain; use the committed WINDOWED interface DuhamelSourceTimeC1On + ..._on (shortest).
THE 12-BRICK SEQUENCE (3 phases):
  A (mechanical/generic): E1 GWA Basic (weighted-ℓ¹+lp completeness) · E2 GWA convolution Banach algebra ·
    E3 GWA coeffwiseCLM (∂ₓ/multipliers/R_μ/∂ₓR_μ/heat as one-liners + D_mul/D_exp) · E4 EWA + sliceWA bridge.
  B (genuinely-new analytic): E5 EWA Duhamel value+√T divergence (sup_t INSIDE the sum, short) ·
    E6 EWA decisive estimate (only new step: EWA_coeff_decay = sup_τ static-WA-coeff-decay ≤ e^{−δs}) ·
    E7 EWA Gamma/Laplace WL realPow (BIGGEST) · E9 coefficient-ODE time-regularity (c_n'=−λc+F, c_n''=λ²c−λF+F').
  C (the join — mandatory bridges): E7' EWA flux B + G maps & Lipschitz in EWA³ · E8 EWA fixed point
    (contraction + agreement eval(Φ_EWA)=intervalGradientDuhamelMap) · E10 chemDiv time-chain B_t (HIGHEST RISK)
    · E11 package as DuhamelSourceTimeC1On · E12 PICARD BRIDGE (eval(u_n^EWA)=picardIter + cosine-coeff
    agreement c_k = cosineCoeffs(lift(picardIter)); MANDATORY, "most likely to be forgotten").
TWO HIGHEST-RISK BRICKS: (1) E10 chemDiv time-chain — hardest sublemma realPow_timeDerivative
  ∂_t(u^γ)=γu^{γ−1}u_t with envelope bounds (≠ realPow_eval membership). (2) E12/E7' the Picard eval-agreement
  bridge — EWA fixed point must be proven = committed picardIter/IteratePicardJointC2Data object.
FALLBACK ladder if E10 fails: (a) window-local coefficient-derivative package (scalar chain rules + uniform EWA
  envelopes) → DuhamelSourceTimeC1On; (b) weakest: mild local existence in EWA³ + source VALUE envelopes — a
  valid PARTIAL theorem (does NOT discharge the committed joint-C²/adot, but real). CAVEAT: needs u₀∈WA³ (if the
  paper assumes it, sound; else add a positive-time restart/smoothing on [τ,T]).
## ============================================================================================================

## The algebra
Bilateral coefficients ℤ→ℂ (exponential basis e^{inπx} → products are plain convolution, NO |j−k|
folding). Weighted norms:
  A  = W⁰ = { a : Σ_n |a_n| < ∞ },     A¹ = W¹ = { a : Σ_n (1+|n|)|a_n| < ∞ }.
Real PDE data sits as conjugate-symmetric (a_{−n} = conj a_n); cosine = even, sine = odd. Cos/sin
ℕ-coeffs embed as even/odd bilateral via a_0=ĉ_0, a_k=a_{−k}=½ĉ_k (cos) / a_k=ĉ_k^sin/2i (sin).

## Bricks
1. [DONE, building/auditing] ShenWork/Wiener/WeightedL1Convolution.lean — wWeight, MemW, wNorm,
   wConv; wWeight_submul (1+|m+n| ≤ (1+|m|)(1+|n|)); wNorm_conv_le (‖a*b‖_{Wʳ}≤‖a‖‖b‖, the
   Banach-algebra core, via ℤ×ℤ Tonelli + Equiv shear (m,n)↦(m,n−m)); memW_conv.
2. [NEXT] ∂ₓ multiplier: (Da)_n = iπn a_n; ‖Da‖_{A} ≤ π‖a‖_{A¹}  (i.e. ∂ₓ:A¹→A). Bounded
   multipliers: ‖m·a‖_{Wʳ} ≤ ‖m‖_∞‖a‖_{Wʳ} (carries the elliptic resolver R_μ, ∂ₓR_μ — multipliers
   1/(μ+λ_k), kπ/(μ+λ_k)≤1/(2√μ), λ_k/(μ+λ_k)≤1 all bounded).
3. Algebra exponential exp_{A¹}(a) = Σ aⁿ/n! (global, ‖aⁿ‖≤‖a‖ⁿ); evaluation eval_x(exp a)=exp(eval_x a);
   D(exp(−tf)) = −t(Df)exp(−tf) (derivation).
4. THE DECISIVE ESTIMATE (ChatGPT cron RUN#263, validated route C):
     ‖exp(−tf)‖_{A¹} ≤ C·(1 + t‖Df‖_A)²·e^{−δt}   for real f, floor f(x) ≥ δ > 0.
   Proof (elementary, floor used POINTWISE not in abstract norm):
     |a_n| ≤ ‖Σ a_m e^{imπx}‖_∞ ≤ e^{−δt}  (coeff ≤ sup; eval is e^{−tf(x)}, |·|≤e^{−δt});
     Σ_{|n|>N}|a_n| ≤ ‖Da‖_A/(π(N+1)), Da_t=−t(Df)a_t ⇒ ‖Da_t‖_A ≤ t‖Df‖_A·‖a_t‖_A;
     mode split X_t ≤ (2N+1)e^{−δt} + (tM/π(N+1))X_t, pick N~2tM/π ⇒ X_t ≤ C(1+tM)e^{−δt};
     ‖a_t‖_{A¹} ≤ (1+tM/π)X_t ⇒ the (1+tM)²e^{−δt} bound.
5. Wiener–Lévy via Gamma/Laplace (route C — avoids partition-of-unity, contour, inverse-closedness):
     f^{−s} = (1/Γ(s))∫₀^∞ t^{s−1} exp(−tf) dt   converges in A¹ (∫ t^{s−1}(1+tM)²e^{−δt}dt
     = finite combo of Γ(s+j)δ^{−(s+j)}, j=0,1,2; Mathlib Real.integral_rpow_mul_exp_neg_mul_Ioi).
     Eval commutes with Bochner integral (ContinuousLinearMap.integral_comp_comm) ⇒ F_s(x)=f(x)^{−s}.
     Then f^γ = f^m·f^{−(m−γ)} ∈ A¹ (m>γ). Gives WL1 (u^γ∈A¹, u≥δ>0) and WL2 ((1+v)^{−β}∈A¹).
6. Adapters: cos/sin ℕ-coeff ↔ even/odd bilateral; connect to the committed duhamelSpectral source-ℓ¹.

## CLOSURE VERDICT (ChatGPT cron2 RUN, 2026-06-13) — ROUTE IS SOUND, with two corrections
GREEN: the divergence-Duhamel self-map CLOSES — ‖∫S_N(t−s)∂ₓB ds‖_{A^r} ≤ C√T·sup‖B‖_{A^r} at
EVERY finite r (sup_{y>0} y·e^{−τy²} = 1/√(2eτ) ⇒ t^{−1/2} kernel, integrable). Contraction for
small T. NO fatal derivative-loss regress. Logistic term: ≤ T·sup‖G(u)‖_{A^r}.

CORRECTION 1 — finite weight ladder (build A^r ONCE, parameterized; pick r per leg):
  ∂ₓB∈A^q ⟺ B∈A^{q+1}.  U_xx leg: ∂ₓB∈A⁰ ⟸ B∈A¹.  gradient leg: ∂ₓB∈A¹ ⟸ B∈A².
  chemDiv mixed time-chain (coupledChemDivTimeDerivativeLift differentiates a flux with u_t):
  safe at u∈A³ (u_t=u_xx−χ₀∂ₓB+G(u) ⇒ u∈A³ ⇒ u_t∈A¹ ⇒ time-flux∈A¹ ⇒ ∂ₓ∈A⁰), unless refactored.
  Also: need u₀∈A^r (committed S_N(t)u₀∈C²_x for t>0 does NOT put the path in C_tA¹ at t=0).

CORRECTION 2 — THE REAL CATCH (coefficient-envelope mismatch): C_t A^r does NOT imply
  Σ_k w_k^r·sup_t|F̂_k(t)| < ∞  (sup INSIDE the sum). C_t A^r only gives sup_t Σ_k w_k^r|F̂_k| (sup
  OUTSIDE). Counterexample: f̂_n(t)=(1/(n w_n^r))φ_n(t), disjoint bumps near t=2^{−n} — continuous
  into A^r but Σ w_n^r sup_t|f̂_n| = Σ1/n = ∞. MY COMMITTED duhamelSpectral bricks consume the
  sup-INSIDE version. FIX (chosen): build the fixed point in the COEFFICIENT-ENVELOPE time space
    E_T^r = { f(t,x)=Σ_k a_k(t)e_k(x) : Σ_k w_k^r·sup_{t∈[0,T]}|a_k(t)| < ∞ } + continuity into A^r.
  Product/WL/resolver/divergence-Duhamel all still close in E_T^r. (Alt: re-prove the source lemmas
  for sup-outside hyps — more disruptive; prefer E_T^r.)

Parity-split (refinement on top of the ℤ-bilateral algebra): A_c^r (cosine, even), A_s^r (sine, odd);
∂ₓ:A_c^{r+1}→A_s^r, A_s^{r+1}→A_c^r; B=u·v_x·(1+v)^{−β} ∈ A_s^1 ⇒ ∂ₓB∈A_c^0. v=R_μ(νu^γ)∈A_c, v_x∈A_s.

## brick-4 sub-plan — the algebra exponential + decisive estimate (ChatGPT cron RUN, 2026-06-13)
DECISION: do NOT hand-roll coefficient-wise exp. Package A^r as a proper NormedCommRing + CompleteSpace
(via LinearIsometryEquiv to Mathlib `lp (fun _:ℤ => ℂ) 1`, storing the WEIGHTED sequence n↦(1+|n|)^r·a_n
so the weighted norm = lp-1 norm), then REUSE `NormedSpace.exp` + `NormedSpace.map_exp` + the `AddCircle 2`
Fourier API. Function-level bricks 1–3c are the ingredients (submult ← wNorm_conv_le; completeness ← lp).
Sub-bricks:
  4a [NEXT] convolution ring laws on functions: wConv_comm, wConv_assoc, wConv_wOne (unit) — prereq for CommRing.
  4b  bundle type A r (subtype/structure) + NormedAddCommGroup + CompleteSpace (lp isometry) + NormedCommRing
      (mul=wConv, one=wOne, submult from wNorm_conv_le). incl10:A¹→A⁰ ring hom (continuous).
  4c  evalC : A⁰ →A[ℂ] C(AddCircle 2,ℂ) (Fourier synthesis, ‖evalC a‖≤‖a‖, mult via finite-support density);
      evalAt x : A⁰ →+* ℂ; evalAt_exp via NormedSpace.map_exp; fourierCoeff recovery
      norm_coeff_le_of_eval_bound (|a_n|≤‖evalC a‖, via AddCircle.fourierCoeff — NO raw interval integral).
  4d  D : A¹ →L[ℂ] A⁰ (coeff_D = iπn·a_n); D_mul (Leibniz cross-space); D_exp via series; D_exp_neg_t.
  4e  THE DECISIVE ESTIMATE: coeff_decay_exp_neg_t (|coeff e^{−tf}_n|≤e^{−δt} from eval≤e^{−δt}); the mode
      split (A0_split + absorb_half, N=⌈2tM/π⌉ isolated as a standalone Archimedean lemma); A1_split ⇒
      ‖e^{−tf}‖_{A¹} ≤ C(1+t‖Df‖)²e^{−δt}. Loose/existential C (do NOT chase sharp constants).
Mathlib reuse: lp, lp.completeSpace, NormedSpace.exp/exp_eq_tsum/map_exp, Complex.exp_eq_exp_ℂ,
  AddCircle.fourier/fourierCoeff/fourierCoeff_fourier. Hand-roll: the A^r wrapper/isometry, evalC, D_exp, mode split.

## brick-4c–4e exp-drill (ChatGPT cron RUN, 2026-06-13) — full code-level skeleton at /tmp/exp_drill_ref.md
KEY DECISION: coefficient recovery + eval multiplicativity via FINITE-SUPPORT DENSITY, NOT MeasureTheory.
integral_tsum (the fragile path — avoid). FS := AddMonoidAlgebra ℂ ℤ (its mul IS convolution = wConv).
4c: coeff0CLM (a↦a.toFun n, ‖·‖≤‖a‖); evalLin : WA 0 →L C(AddCircle 2,ℂ) (a↦∑'n a_n•fourier n x,
  ‖evalLin a‖≤‖a‖ via fourier_norm=1 + norm_tsum_le_tsum_norm); ofFS:FS→ₐWA 0 + dense_ofFS (truncations
  dense in weighted ℓ¹) + coeff_ofFS; evalLin_mul via DenseRange.induction_on₂; evalC (AlgHom); evalAt x
  via ContinuousMap.evalAlgHom; evalAt_exp via NormedSpace.map_exp + Complex.exp_eq_exp_ℂ; coefficient
  recovery fourierCoeff_evalC_eq_coeff via DenseRange.equalizer + (fourierCoeff_norm_le via
  norm_integral_le_of_norm_le_const on normalized Haar) ⇒ norm_coeff_le_of_eval_bound (|a_n|≤sup|evalC a|).
4d: D:A¹→L A⁰, coeff_D=iπn·a_n; D_mul Leibniz; D_pow_succ induction; D_exp via D.map_tsum(expSeries_summable')
  + Summable.tsum_eq_zero_add (factorial shift) + Summable.tsum_mul_right. (map_tsum is NOT the risky part.)
4e: exists_nat_good (Int.ceil), absorb_le_half (nlinarith), mode_absorb_skeleton ⇒ ‖e^{−tf}‖_{A¹}≤C(1+t‖Df‖)²e^{−δt}.
MOST LIKELY TO BREAK: the integral_tsum route (avoided); next: the fourierCoeff finite-support simp
  [fourierCoeff.sum, fourierCoeff.const_smul, fourierCoeff_fourier] + dense_ofFS.
THEN brick 5 = Gamma/Laplace Wiener–Lévy (f^{−s}=∫t^{s−1}e^{−tf}/Γ(s); Real.integral_rpow_mul_exp_neg_mul_Ioi
  + ContinuousLinearMap.integral_comp_comm); brick 6 = E_T^r envelope + A^r heat semigroup + divergence-Duhamel
  smoothing + flux bounds + cos/sin↔ℤ adapters + the C_tE^r fixed point connecting to the committed PDE bricks.

## Honest status discipline (user feedback 2026-06-13)
Report only proved-unconditional commits, never "reduced to N residuals" / "快收口". A conditional
theorem is conditional; name its hypotheses. See feedback_no_residual_framing.

## ============================================================================================================
## PHASE C KICKOFF (2026-06-14) — B complete @09da750, the join begins
B-phase closed: B1 Duhamel √T (24c660f), E3d D_exp (e018f39), B2 decisive (1912e08), B3 Wiener-Lévy (09da750),
all hostile-audited FAITHFUL, clean-tree 8266 jobs EXIT 0. 149 commits.
Clean verify/codex tree: /dev/shm/shen_C (git clone @09da750 + mathlib symlink + warm oleans). shen_work is the
LIVE-SIMS dir at OLD commit 6d2f95a — NEVER verify there (the dirty-tree trap).
C-phase brick order + current dispatch:
  C1 [codex, in flight] E7'a flux/source MAP skeleton ShenWork/Wiener/EWA/Flux.lean — realPowEWA (explicit
     f^m·FnegEWA), qFactor=(1+v)^{-β}, chemFluxEWA=u·incl(gDeriv vField)·qFactor, growthEWA, vField=gResolver(ν•u^γ);
     + eval-agreement factoring (defs+eval ONLY, no norm/Lipschitz). spec /dev/shm/shen_specs/shen_C1.md.
  C2 [ChatGPT cron, long-thinking] E7'b Lipschitz of u↦u^γ, v↦(1+v)^{-β} in EWA norm (contraction constant).
     Route candidates: (A) segment integral f^γ-g^γ=γ∫(g+θ(f-g))^{γ-1}(f-g)dθ; (B) Laplace-difference
     f^{-s}-g^{-s}=(1/Γs)∫t^{s-1}(e^{-tf}-e^{-tg})dt with ‖e^{-tf}-e^{-tg}‖≤t‖f-g‖·majorant. Awaiting verdict.
  C1b [pending] norm bounds ‖FnegEWA‖≤Γ-combo, ‖realPowEWA‖, ‖chemFluxEWA‖, ‖growthEWA‖ (self-map into ball).
  E8 EWA fixed point (contraction via C1+C1b+C2, ×C√T Duhamel) + agreement eval(Φ_EWA)=intervalGradientDuhamelMap.
  E10 [HIGHEST RISK] chemDiv time-chain B_t; sublemma realPow_timeDerivative ∂_t(u^γ)=γu^{γ-1}u_t + envelopes.
  E11 package DuhamelSourceTimeC1On.  E12 [MANDATORY] Picard bridge eval(u_n^EWA)=picardIter + cosine-coeff align.
## ============================================================================================================

## JOIN-TARGET RECON (2026-06-14) — exact committed焊接点 signatures (细审 prep)
Read the two structures E10/E11/E12 must witness:
* DuhamelSourceTimeC1On (a:ℝ→ℕ→ℝ)(lo hi) [PDE/IntervalDuhamelSourceTimeC1On.lean:20] — the WINDOWED path
  (ROUTE's "shortest"). Fields: adot (time-deriv of coeffs); hderiv (HasDerivWithinAt a·n = adot on [lo,hi]);
  hadotcont; envelope:ℕ→ℝ + henv_summable (Σ envelope<∞) + henv_bound (|a s n|≤envelope n); derivBound:ℝ (a
  SINGLE uniform const) + hderivBound (|adot s n|≤derivBound ∀ s n). KEY: envelope is weighted-summable (=
  E_T⁰ VALUE source-ℓ¹, have machinery), but derivBound is just UNIFORM-in-(n,t), NOT summable. ⟹ E10 only needs
  B_t to have uniformly-bounded coeffs (follows from B_t∈A⁰), MUCH weaker than the C² joint majorant. De-risks E10/E11.
* IteratePicardJointC2Data (u)(c)(Bt) [PDE/IntervalIteratePicardJointC2.lean:41] — the HEAVIER alt (NOT taking):
  lift_eq_series (u-lift=Σ c_k(t)cos kπx); coeff_contDiff (each c_k C² in t); coeff_bound (‖iteratedFDeriv i c_k‖≤Bt
  i k, i≤2); value_summable (boundedWeightJointMajorant Bt m, m≤2). Full C² joint — only needed if windowed path fails.
* intervalGradientDuhamelMap (p:CM2Params)(u₀) [Paper2/IntervalGradientDuhamelMap.lean:58] — E8 agreement target.
* picardIter (p:CM2Params)(u₀) [Paper2/IntervalMildPicard.lean:863] — E12 equality target.
* duhamelSpectral_eigenvalueSummable_of_sourceL1 [PDE/IntervalDuhamelSpectralC2FromSourceL1.lean:67] — consumer.
DECISION: E11 targets DuhamelSourceTimeC1On (windowed, uniform-derivBound) — confirmed the shortest sound path.
## NOTE: codex usage-limited until 2026-06-18; Lean grind re-routed to opus subagents (C1 in flight via Agent),
## ChatGPT (cron) for design/audit only. Resume codex dispatch after 06-18.

## ============================================================================================================
## PHASE C-2 JOIN BLUEPRINT (ChatGPT cron2, 2026-06-14) — captured gpt_e8_join_strategy.txt. STRATEGY = B′.
Lipschitz layer COMPLETE (bricks 1-4 committed @a135e0d): Flux skeleton, ExpLipschitz, FnegLipschitz,
RealPowLipschitz — the full contraction machinery in E_T^1.
B′ = "EWA shadow Picard": lift each committed picardIter iterate to an EWA shadow, prove the shadow is CAUCHY
(geometric ‖U_{n+1}-U_n‖≤K^n C0, K<1 — uniform bounds ALONE insufficient, the trap in pure B), pass to EWA
limit, fixed-point identity as a CONSEQUENCE. NOT pure-A (no separate fixed point + uniqueness/agreement).
picardIter (IntervalMildPicard.lean:863) is recursively intervalGradientDuhamelMap — join is stepwise/definitional.

REMAINING BRICKS (precise):
  B5 [eval bridge — HARD] PhiEWA := heatEWA u₀ + divDuhamelEWA(-χ₀ chemFluxEWA u) + valDuhamelEWA(growthEWA u)
     (committed B1 Duhamel ops); EWARealizesOn structure (eval_eq: evalST U = intervalDomainLift w);
     PhiEWA_eval_eq_intervalGradientDuhamelMap. NEEDS resolving the currently-OPAQUE eval(gDeriv v):
     eval_vFieldEWA_eq_intervalNeumannResolverR + eval_gDeriv_vFieldEWA_eq_resolverGradReal. Hardest brick.
  B6 [coeff bridge] ewaCosCoeffAt F τ k := ((sliceWA τ F).toFun k + .toFun(-k)).re (sum-of-±-modes, avoids
     evenness); ewaCosCoeffAt_eq_cosineCoeffs_of_eval (given EWARealizesOn) via committed fourierCoeff_evalC_eq_coeff
     + ofCosineCoeffs/evalC_ofCosineCoeffs (CosineAdapter). Load-bearing for DuhamelSourceTimeC1On.
  B7 [B′ contraction] FlooredBall struct (‖U-center‖≤R + UniformFloor U δ + RealValued, complete: norm-closed +
     floor-closed via continuous evalST); invariant by SMALL-TIME (S(t)u₀≥2δ + Duhamel perturb ≤δ ⟹ Φ(U)≥δ;
     1+v≥1 via committed intervalNeumannResolverR_nonneg_of_nonneg_source); picardEWA shadow def;
     picardEWA_realizes_picardIter (induction via B5); picardEWA_geometric→cauchy→tendsto→limit_fixed.
  B8 [time-chain @ EWA T 3 — HIGHEST RISK] U_t=U_xx-χ₀∂ₓB+G ⟹ v_t,q_t,B_t,F_t=-χ₀∂ₓB_t+G_t ∈ EWA⁰;
     adot_k=ewaCosCoeffAt F_t, |adot|≤C‖F_t‖_{EWA⁰} (single uniform derivBound). CAVEAT: needs EWA T 3 (not T 1)
     — either re-run WL/Lipschitz at r=3 (high-weight WL, new), or positive-time restart on [τ,T]. DECIDE AT B8.
  B9 [package] DuhamelSourceTimeC1On (fun s k => ewaCosCoeffAt (sourceEWA U∞) ⟨s,hs⟩ k) 0 T, rewrite via coeff
     equality to committed cosineCoeffs shape → feed duhamelSpectral_eigenvalueSummable_of_sourceL1.
Circularity-safe order: value maps → contraction (value Lipschitz only) → lift Picard → EWA limit → fixed-point
identity → time-chain (post-fixed-point readout) → package. Source derivative NOT a contraction input.
## ============================================================================================================

## JOIN INTERFACE MAP (recon a8c7e1a, 2026-06-14) — exact committed file:line for B5-B9
COEFF (B6): cosineCoeffs (PDE/IntervalNeumannFullKernel.lean:83, =unitIntervalNeumannCosineCoeff, 0th unscaled,
  k≥1 ×2); fourierCoeff_evalC_eq_coeff (Wiener/WeightedL1Eval.lean:478: fourierCoeff(evalC a) n = a.toFun n, T=2);
  ofCosineCoeffs (Wiener/WeightedL1CosineAdapter.lean:24: n=0↦c₀, else c_{|n|}/2); evalC_ofCosineCoeffs
  (Wiener/WeightedL1CosineEval.lean:58: synth of even embed = ∑c_k cos(kπx) on [0,1]); cosineMode
  (PDE/CosineSpectrum.lean:21 = cos(nπx)); intervalDomainLift (PDE/IntervalDomain.lean:2750, extend-by-0).
  ⟹ fourierCoeff(cosine-series w) = ofCosineCoeffs(cosineCoeffs w) ⟹ (a_k+a_{-k}).re = cosineCoeffs_k.
DUHAMEL/HEAT (B5/PhiEWA): valDuhamelEWA (EWA/Duhamel.lean:472, bound T), divDuhamelEWA (:478, bound C₀√T),
  duhValMode/duhDivMode (:217/:260). gHeat (GWA/Operators.lean:324, scalar exp(-τ(nπ)²)), gHeatDeriv (:344).
  NO heatEWA — B5 must build the time-dependent heat flow as an EWA element (coeff_n(t)=exp(-t(nπ)²)û₀_n).
EVAL TARGET (B5): intervalGradientDuhamelMap (Paper2/IntervalGradientDuhamelMap.lean:58) = S(t)u₀ -χ₀∫∂ₓS(t-s)Q
  +∫S(t-s)L; Q=chemFluxLifted (:47 = lift w·resolverGradReal/(1+lift(R w))^β), L=logisticLifted (:52). picardIter
  (Paper2/IntervalMildPicard.lean:863, base S(t)u₀ / step Φ). intervalFullSemigroupOperator (PDE/...FullKernel:78).
EVAL(gDeriv v) (B5 HARD): resolverGradReal (Paper2/IntervalDomainL2StaticVDifference.lean:748) =
  intervalNeumannResolverRGrad (PDE/IntervalNeumannEllipticResolverR.lean:463 = ∑(v̂_k).re·(-kπ sin(kπx))) — a
  SINE series ⟹ B5 needs ofSineCoeffs (odd embedding, the held parity sibling). intervalNeumannResolverR (:102).
  Floor: intervalNeumannResolverR_nonneg_of_nonneg_source (PDE/IntervalResolverPositivity.lean:489).
NEXT: B6 coeff bridge first (self-contained); then B5 eval bridge (needs ofSineCoeffs for the gradient leg).
## ============================================================================================================

## B5 FULL-CIRCLE OBLIGATION (discovered by B6 audit a2b761a, 2026-06-14)
B6's EWARealizesOn.eval_eq is FULL-CIRCLE (eval = cosine synthesis ∑ c_k cos(kπx) for all x). To discharge it,
B5 cannot just cite iterate_lift_eq_cosineSeries (that's [0,1]-only, = the is_cosine_series field). B5 must prove
the coefficient-embedding identity (sliceWA τ (picardEWA-shadow)).toFun = ofCosineCoeffs(cosineCoeffs(lift picardIter))
and route the realized slice through evalC_ofCosineCoeffs_all for the full-circle synthesis. Track B5 against this.

## B5 EVAL-BRIDGE DECOMPOSITION (recon a5e50de, 2026-06-14) — coefficient-level route
Q1 RESOLVER: intervalNeumannResolverCoeff (IntervalNeumannEllipticResolverR.lean:89) = (μ+λ_k)⁻¹·source;
  intervalNeumannResolverCoeff_elliptic (:141): (μ+λ_k)·v̂_k=â_k; source = cosine coeff of ν·u^γ (:76). Matches
  EWA gResolver 1/(μ+(nπ)²). PREREQ: confirm unitIntervalNeumannSpectrum.eigenvalue k = (kπ)².
Q2 EVAL-OF-MULTIPLIER: NO committed lemma (eval(scalarMultiplier)=symbol action). Template = eval_gConv
  (EWA/Basic.lean:112, evalCLM.map_tsum). BUT coeff-level route avoids pointwise: scalarMultiplier_toFun
  (Operators.lean:122, (mult m a).toFun n = m n•a.toFun n) gives the COEFFICIENT action FREE. New work = per-op
  termwise-symbol↔real-operator match (gDeriv→∂ₓ via SINE adapter; gResolver→resolver; gHeat→semigroup).
Q3 HEAT: intervalFullSemigroupOperator_eq_cosineHeatValue (IntervalNeumannFullKernel.lean:604) EXISTS, gated on
  hkernel (=intervalNeumannFullKernel_eq_cosineKernel) + hinterchange (FullKernelIntegralInterchange:593, a Prop
  obligation). heatEWA eval = MODERATE. Related: IntervalSemigroupSpectralForm.lean:44.
Q4 [KEY] COEFF-LEVEL DUHAMEL: iterateCoeff (IntervalPicardIterateRestart.lean:212) = e^{-tλ_k}û₀_k +
  duhamelSpectralCoeff(logistic source) — committed but χ₀=0 ONLY. cosineCoeffs_halfstep_eq_iterateCoeff (:434):
  cosineCoeffs(lift(picardIter(n+1))) = iterateCoeff (χ₀=0). The χ₀≠0 CHEMOTAXIS coeff is NOT committed → THE EWA
  divDuhamelEWA LAYER PROVIDES IT (the raison d'être of the Wiener algebra). B5 EXTENDS the χ₀=0 coeff identity to
  χ₀≠0 by adding the EWA chemotaxis Duhamel coefficient. (variants: ..._of_sourceTimeC1On
  IntervalPicardWindowAdotOn.lean:182; restartIterateCoeff IntervalPicardIterateC2Bound.lean:415.)
B5 SUB-BRICKS: B5a heatEWA + eval (Q3 gated); B5b eval(gResolver)=resolverR (Q1); B5c eval(gDeriv vField)=
  resolverGradReal (SINE adapter); B5d eval(divDuhamelEWA)=chemotaxis Duhamel term + eval(valDuhamelEWA)=logistic;
  B5e PhiEWA + coeff identity extending iterateCoeff to χ₀≠0 (discharge EWARealizesOn.eval_eq full-circle obligation).
NOTE: do coeff-level (match EWA coeffs to cosineCoeffs via B6), NOT pointwise eval — Q4 + B6 make this the short path.
## ============================================================================================================

## B5 DE-RISK FINDINGS (2026-06-14)
* λ_k=(kπ)² is `rfl`: unitIntervalNeumannSpectrum.eigenvalue k = (k:ℝ)^2*Real.pi^2 (committed everywhere, e.g.
  IntervalNeumannEllipticResolverR.lean:493). ⟹ EWA symbols 1/(μ+(nπ)²), exp(-τ(nπ)²), iπn match committed λ_k FREE.
* COMMITTED IntervalResolverGradientBridge.lean (lines 231/352/368: (μ+λ_m)·(mπ)² resolver-grad algebra) — likely
  supplies much of B5c eval(gDeriv vField)=resolverGradReal. RECON this file before building B5c.
* B5 core-formulation consult fired to ChatGPT cron2 (/tmp/gpt_b5.out): per-op coeff bridges, the χ₀≠0 extension
  of iterateCoeff (option A fresh cosineCoeffs_of_intervalGradientDuhamelMap vs B), spectral↔kernel need, induction.

## B5c DE-RISK (recon of IntervalResolverGradientBridge.lean, 2026-06-14)
COMMITTED real-space termwise-diff: resolverR_apply_eq (:132 R=∑v̂_k.re cos), resolverRGrad_apply_eq (:141 =
∑v̂_k.re(-kπ)sin), resolverR_hasDerivAt_grad (:159: ∂ₓ(intervalNeumannResolverR) = resolverGradReal via
hasDerivAt_tsum + gradient ℓ¹ majorant resolverGrad_majorant_summable_of_sourceDecay:207). Template
cosineSeries_hasDerivAt_of_gradSummable (:74). Also 2nd-deriv: sineSeries_hasDerivAt (:288), resolverGrad2 (:330,387).
⟹ B5c = [NEW EWA: eval(gDeriv F)=∂ₓ(evalC F), mirror :74's hasDerivAt_tsum for the e^{inπx} series] ∘
  [COMMITTED: ∂ₓ resolverR=resolverGrad, :159]. The hard real-space gradient is DONE; new piece is the EWA
  termwise-derivative-commutes-with-eval, a clean mirror of committed technique.
## ============================================================================================================

## ⚠️ CRITICAL JOIN RISK (B5 consult cron2 + independent check, 2026-06-14) — MAP-FORM MISMATCH
ChatGPT cron2 (gpt_e8/gpt_b5) flags + my independent derivation CONFIRMS: the committed intervalGradientDuhamelMap
chemotaxis term is ∂ₓS_N(t-s)B (gradient-OF-semigroup: deriv(intervalFullSemigroupOperator (t-s) (chemFluxLifted)),
verified in earlier recon), whereas the EWA divDuhamelEWA computes S_N(t-s)∂ₓB (semigroup-OF-divergence, symbol
inπ INSIDE the Volterra integral). On [0,1] with the method-of-images Neumann kernel, ∂ₓ does NOT commute with S_N
(it intertwines Neumann↔Dirichlet ∂ₓe^{tΔ_N}=e^{tΔ_D}∂ₓ); the two forms differ by the image-term contribution
∑∫G'(x+y-2m)B(y)dy (IBP boundary vanishes since B is a sine/Dirichlet series, but the +y image term survives).
Diagnostic (ChatGPT): B=sin(πy) ⟹ S_N∂B=πe^{-π²t}cos vs ∂S_N B is sine-valued — different parity.
⟹ B5 CANNOT naively prove "committed ∂ₓS_N B map = EWA divDuhamelEWA". RESOLUTION PENDING recon: does the committed
dev prove intervalGradientDuhamelMap = a SOURCE-form operator (intervalFullKernelCoupledDuhamelOperator, S(t-s)·
source)? If YES (gradient=source proven for the actual flux) the issue dissolves; if NO, B5 must target the
source-form map + a separate equivalence (the bigger architectural path). DO NOT BUILD B5 UNTIL RESOLVED.
ChatGPT recommended target: intervalFullKernelCoupledDuhamelOperator (source-form) + connect to paper separately.
NOTE: the per-op coeff bridges (OpCoeffBridge), adapters, heatEWA, Lipschitz layer are ALL still valid — they're
operator-level, independent of this map-form question. Only the B5 ASSEMBLY target is affected.
## ============================================================================================================

## ✅ MAP-FORM RISK RESOLVED — RETARGET TO SOURCE-FORM (recon a506cb18, 2026-06-14)
DECISIVE: the committed chain runs ENTIRELY in χ₀=0 (a:=cosineCoeffs(logisticLifted), the gradient↔source bridges
:972/:1019 only fire via hchem=0/χ₀=0). The χ₀≠0 chemotaxis is the gap the EWA work FILLS. My divDuhamelEWA
(source-form S_N∂ₓB) matches the committed SOURCE-form operator intervalFullKernelCoupledDuhamelOperator
(IntervalFullKernelDuhamelGradEq.lean:39 = S_N(t-s)·intervalCoupledSource), NOT the gradient-form
intervalGradientDuhamelMap. The source-ℓ¹ consumer (duhamelSpectral_..._of_sourceL1) is GENERIC (any source-ℓ¹
family); committed dev only fed it χ₀=0 logistic; EWA feeds the χ₀≠0 source -χ₀∂ₓB+G.
IBP bridge deriv_intervalFullSemigroupOperator...source_integral (IntervalFullKernelSourceIBP.lean:69) proves
∂ₓS_N Q = S_D Q' (Dirichlet kernel, ORPHAN/unimported) — confirms ∂ₓS_N≠S_N∂ₓ, so do NOT chase gradient-form.
RETARGETED B5/B-phase (source-form): the EWA layer provides the SOURCE cosine-coeff family for DuhamelSourceTimeC1On:
  source S(U) := -χ₀•gDeriv(chemFluxEWA U) + growthEWA U : EWA T 0 (∂ₓB even/cosine via OpCoeffBridge gDeriv of the
  sine flux); ewaCosCoeffAt(S(U)) = cosineCoeffs(-χ₀∂ₓB+G) via B6; source-ℓ¹ envelope from EWA⁰ membership; time-C1
  (B8) → DuhamelSourceTimeC1On → feed the generic spectral machinery. NO gradient-form picardIter realization.
  Key committed targets: intervalCoupledSource (IntervalDomainExistence.lean:1481 = -χ₀·intervalDomainChemotaxisDiv
  + logistic), intervalDomainChemotaxisDiv (IntervalDomain.lean:2923 = ∂ₓB the divergence).
SALVAGED: OpCoeffBridge, adapters, B6, heatEWA, Lipschitz layer ALL valid. Still needed: flux eval bridges
(eval chemFluxEWA = chemFluxLifted via resolver/gradient eval) + eval(gDeriv F)=∂ₓ(evalC F) + the source pkg + B8.
OPEN (for Xiang): does the EWA layer also owe the SOLUTION existence (fixed point B7), or only source-control given
the committed iterate? The source-ℓ¹ target is clear regardless; the existence-structure connection to the paper
theorem is the architectural question. Proceeding with the source-control eval bridges (valid either way).
## ============================================================================================================

## 🎯 ARCHITECTURAL DECISION (Xiang delegated the call, 2026-06-14) — TARGET = SOURCE-ℓ¹, DEFER EXISTENCE
The EWA layer's theorem: for u in the floored EWA ball, the χ₀≠0 chemotaxis source -χ₀∂ₓB(u)+G(u) has the
DuhamelSourceTimeC1On structure — ℓ¹ value envelope (Σ_k sup_t|coeff| ≤ ‖S(U)‖_{EWA⁰}, intrinsic to the EWA
element's norm) + uniform time-derivative bound (B8) — REALIZING the real chemotaxis source (B5e: ewaCosCoeffAt
= cosineCoeffs of the real source). This discharges the GENERIC committed duhamelSpectral_eigenvalueSummable_
of_sourceL1 hypothesis for χ₀≠0 (the gap the committed χ₀=0 chain leaves). = the Wiener-algebra content (∂ₓB∈A).
EXISTENCE / fixed-point (B7) DEFERRED — committed local-existence chain or future piece; not conflated here.
Remaining bricks to the milestone: flux eval (auditing) → growth eval → source assembly (S(U) + eval=-χ₀∂ₓB+G)
→ source coeff (B6) + ℓ¹ envelope → B8 time-chain (adot uniform bound, hardest) → B5e realization discharge
(EWARealizesOn full-circle) → B9 package DuhamelSourceTimeC1On → feed the generic spectral machinery.
## ============================================================================================================

## ✅✅ DECISIVE: GAP CONFIRMED, EWA IS THE GAP-FILLER (recon a1e94177, 2026-06-14)
The chemDiv ℓ¹ bound Summable(cosineCoeffs(intervalDomainChemotaxisDiv)) = ∂ₓB∈A is NOT proven in committed dev —
it's the `hdecay` field of CoupledChemDivTimeC1Fields (IntervalChemDivTimeDerivative.lean:96-104), a struct that is
NEVER CONSTRUCTED (grep: no .mk/⟨⟩). The χ₀-general node duhamelProfile_closedC2_neumann_of_coupledChemicalSource
(IntervalCoupledClassicalCorePAR.lean:179, sorry-free) TAKES it as hypothesis hchem. = the real undischarged gap
("zero sorry ≠ complete"). Only the final paper2_theorem_1_1_chiZero_final (IntervalDomainThm11ChiZeroFinal.lean:204)
is χ₀=0-restricted; the machinery below it is χ₀-GENERAL.
THE LIVE CONSUMER needs a PURE summable ℓ¹ envelope: DuhamelSourceTimeC1 (IntervalDuhamelClosedC2.lean:1502) fields
envelope/henv_summable/henv_bound — NOT quadratic decay (that's the H²-elliptic constructor's artifact,
IntervalSemigroupNeumann.lean:828). EWA SourceEnvelope (sourceEnvelope/_summable/_abs_le) maps FIELD-FOR-FIELD onto
it, from the Wiener norm — bypassing H²/elliptic. ⟹ THE 15 EWA BRICKS PLUG INTO THE REAL χ₀≠0 PATH. Not orthogonal.

ENDGAME (fill CoupledChemDivTimeC1Fields / build DuhamelSourceTimeC1 for the chemDiv source via the EWA):
  E1 [B5e parity, non-circular] ewaCosCoeffAt(sourceEWA) = cosineCoeffs(intervalCoupledSource): needs the source
     even-embedded (parity propagation: realPowEWA/gResolver/gHeat preserve even, gDeriv even↔odd, products) +
     the realization; CRUCIAL fix: supply EWARealizesOn.summable_cos from the EWA intrinsic summable_coeff_norm
     (NOT assume it — recon caught the circularity). Caveat: U must realize the SOLUTION u; regularity/weight
     ladder (u∈A^r) + the gradient-vs-source map-form both bear here.
  E2 [B8 adot] the time-derivative data (adot/hderiv/derivBound) for DuhamelSourceTimeC1 — mirror
     coupledChemDivSource_duhamelSourceTimeC1 (IntervalCoupledSourceTimeC1.lean:52) / the logistic uniform-limit
     constructor (IntervalPicardLimitLogisticSource.lean:187). The head risk all along.
  E3 [assembly] build DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs) from SourceEnvelope (henv triple) + E2 adot
     → discharge hchem → duhamelProfile_closedC2_neumann_of_coupledChemicalSource (χ₀≠0) → generalize Thm 1.1.
  Discharge the carried B5e factor hyps (hgrad, h_flux_nbhd, h_growth) of evalST_sourceEWA_eq_intervalCoupledSource.
NOTE: E1's "U realizes the solution" + the regularity/weight + the map-form are entangled — the genuinely hard 合龙.
## ============================================================================================================

## 🎯 ENDGAME DESIGN (ChatGPT cron2 endgame consult, 2026-06-14, captured gpt_endgame.out) — REROUTE: ℓ¹ not hdecay
DECISIVE: do NOT fill CoupledChemDivTimeC1Fields.hdecay — it demands QUADRATIC decay |chemDiv_k|≤C/(kπ)² (STRONGER
than ℓ¹; a sparse summable seq can have k²E_k→∞). My SourceEnvelope is pure ℓ¹, NOT quadratic. So target instead:
  build DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u) via a NEW ℓ¹-field constructor (duhamelSourceTimeC1_
  of_data takes an ARBITRARY summable envelope) + a PAR SIBLING duhamelProfile_closedC2_neumann_of_coupled
  ChemicalSource_l1 consuming the chemDiv DuhamelSourceTimeC1 directly (body = current thm after line 43).
ENDGAME STEPS (cleanest Lean target):
  S1 struct CoupledChemDivTimeC1L1Fields (ℓ¹ envelope+summable+bound + hchain + adotcont + Mdot) +
     coupledChemDivSource_timeC1_of_l1Fields (wrapper over duhamelSourceTimeC1_of_data). [windowed ...On / [0,T]]
  S2 PAR sibling ..._l1 (hlog + hchemSrc:DuhamelSourceTimeC1(chemDiv) + hcoeffSplit). thin surgical join.
  S3 chemDivEWA := gDeriv(chemFluxEWA U) : EWA T 0; chemDiv_coeff_bound_of_EWA : |cosineCoeffs(coupledChemDiv
     SourceLift u) k| ≤ sourceEnvelope(chemDivEWA U) k — via evalST_gDeriv_chemFlux_eq_deriv + deriv_chemFluxLifted
     _eq_chemDiv + the NON-CIRCULAR coeff bridge + ewaCosCoeffAt_abs_le_envelope. (factor sublemma evalST_chemDivEWA
     _eq_coupledChemDivSourceLift from SourceEvalBridge.)
  S4 envelope fields := sourceEnvelope(chemDivEWA U), henv_summable/henv_bound from SourceEnvelope.
  S5 adot fields — STILL the hard B8: reuse committed coupledChemDivAdot (cosineCoeff of coupledChemDivTime
     DerivativeLift) + local chain for hderiv, OR a post-fixed-point EWA time-chain. SourceEnvelope does NOT give adot.
NON-CIRCULAR COEFF BRIDGE (Q1, drop EWARealizesOn): ewaCosCoeffAt_eq_cosineCoeffs_of_even_real_eval_ae {F}{f}(τ)
  (heven : slice toFun even)(hreal : slice toFun im=0)(heval : evalST=f on Ioo 0 1) : ewaCosCoeffAt F τ k =
  cosineCoeffs f k. Summability from SourceEnvelope (INTRINSIC, not assumed). Interior-only eval → a.e./endpoint-null
  congruence. PARITY IS NEEDED (real-valued alone insufficient): EvenRealEWA struct (even+real slice) + closure
  realPowEWA/gResolver/qFactor/growthEWA preserve; gDeriv even↔odd; chemFluxEWA odd; chemDivEWA even. USES my
  committed ConvParity + ParityFoundations atoms.
Q2 SLICE-EMBEDDING SHORTCUT CONFIRMED: construct U slice-wise = even-embed of the committed solution's cosineCoeffs
  — sidesteps the gradient-vs-source map-form ENTIRELY (source bound is pointwise-in-time, evolution irrelevant).
  Condition: must be an honest EWA T 1 element (CT-continuous in t), not just WA 1 slices.
⚠️ Q3 REMAINING OBSTRUCTION (the real analytic gap): the Wiener product route NEEDS u∈A¹ (Σ(1+k)|cosineCoeffs(u)|<∞;
  the bare u factor in B=u·v_x·q is the bottleneck, resolver smoothing does NOT help). The committed solution is only
  C² ⟹ |û_k|~k^{-2} ⟹ Σk|û_k|~Σ1/k DIVERGES, NOT A¹. Need a NEW positive-time-restart/smoothing brick exposing E_T^1
  on [τ₀,T] (positiveTime_EWA1_of_classicalSolution), OR leave u∈A¹ as a hypothesis. The EWA reduces the χ₀≠0
  chemotaxis source-ℓ¹ to the solution's A¹ regularity (a cleaner/standard parabolic fact than the full estimate).
## ============================================================================================================

## ★★ CAMPAIGN CLOSE (2026-06-14, commit c027ff2) — Wiener-algebra value content COMPLETE; 2 gaps scoped
DELIVERED (29 bricks, 0 sorry/0 axiom, all hostile-audited): chemDiv_eigenvalueSummableOn_of_solution (the
assembled theorem — χ₀≠0 chemotaxis-divergence eigenvalue-ℓ¹ via ∂ₓB∈A) + the full machinery (WA→EWA→WL→eval
bridges→parity→SourceEnvelope→realization chain h_u/h_v/h_vx→assembly node→top-level) + adot/h_deriv/h_adotcont.
The Wiener algebra SOLVED the hard nonlinear χ₀≠0 source VALUE-ℓ¹ the committed χ₀=0 dev couldn't pass.
TWO REMAINING GAPS to fully unconditional (precisely scoped, substantial NEW constructions — NOT mechanical):
  (1) A¹ regularity (Q3): committed solution is C²=A⁰; A¹ needs Σ(1+k)/k²<∞ (diverges). Needs a NEW positive-time
      parabolic-smoothing brick (committed dev exposes only C²). Separate standard analysis.
  (2) Mdot/B8 time-chain: Mdot reduces EXACTLY (chemDivAdot_Mdot_residual) to a summable cosine-coeff envelope on
      the TIME-DERIVATIVE field ∂_t(∂ₓB)=∂ₓ(B_t). No time-derivative EWA element exists (gDeriv is spatial only).
      Needs the EWA-T-3 time-chain: mirror the WL/Lipschitz/eval-bridge layer at weight 3 for B_t, build a B_t
      EWA element realizing ∂ₓ(B_t)∈A⁰, then SourceEnvelope supplies Mdot (exactly as it supplied the value bound).
RECOMMENDED NEXT CAMPAIGN: the EWA-T-3 time-chain for Mdot (clearest path — the value layer is the template).
Then the A¹ positive-time smoothing. Both reduce the FINAL theorem to fully unconditional.
## ============================================================================================================

## A¹ RESOLVED (2026-06-14, commit 83839f4) — not a wall; precise remaining brick identified
THREE independent confirmations A¹ is sound (not a wall):
  - Committed (kπ)²-weighted ℓ¹ SOLUTION bound (eigenvalue_mul_abs_limitCoeff_le_uniform_bdd,
    IntervalPicardLimitBddAdapter.lean:84) σ-uniform on windows [a',τ]⊂(0,T], dominates A¹ via (1+k)≤(kπ)².
  - ChatGPT Pro: F∈A⁰ + heat smoothing ⟹ Duhamel∈A¹ on [τ₀,T] (per-coeff |U_k^D|≤B_k/(kπ)², Σ(1+k)|U_k^D|≤
    (T+1/π²)ΣB_k). Flags: (3) t→0 unbounded for A⁰ initial data; (4) circularity — F∈A⁰ proof must not use u∈A¹.
  - Built+verified brick solution_A1_on_pos (SolutionA1.lean, clean-tree 3579 jobs, clean axioms, hostile-audited
    FAITHFUL): A¹ on positive-time window [a',b'].
AUDIT KILL (why not yet wired): FINAL theorem's hBv is ALL-s (embedEWA time domain TimeDom T=Icc 0 T INCLUDES 0);
  A¹ is FALSE at s=0 for A⁰ initial data (Σ(1+k)/k² diverges). Committed window bound's windowEigEnv → Σλ_k
  (divergent) as a'→0, so NO uniform-to-0 envelope from the generic A⁰-smoothing route.
RESOLUTION (the math, worked through): assume u₀∈A¹ (smooth initial data — natural regularity class). Then
  S(t)u₀∈A¹ UNIFORMLY on [0,T] (heat semigroup contracts A¹, e^{-tλ_k}≤1, NO t^{-1/2} blow-up) + Duhamel A¹-norm
  ≤2√T·sup‖F‖_{A⁰} uniformly ⟹ u∈A¹ uniformly on ALL [0,T] incl 0 ⟹ all-s hBv SATISFIABLE.
PRECISE REMAINING BRICK (A¹): solution_A1_uniform — extend solution_A1_on_pos to include t=0 under an u₀∈A¹
  hypothesis, giving a SINGLE Bv valid on all [0,T]. t>0 via the committed window bound (shrink a''→t/2 for any t);
  t=0 via u(0)=u₀∈A¹ directly; uniform glue via the mild formula (S(t)u₀ A¹-contraction + Duhamel 2√T bound).
  Breaks ChatGPT's circularity flag (4) because u∈A¹ for t>0 comes from the committed Picard (kπ)²-bound, NOT from
  F∈A⁰. Committed shift/restrict lemmas (IntervalDuhamelSourceTimeC1On.lean:38-101) available for window algebra.
NOTE: chemDiv_eigenvalueSummableOn_of_solution is HONEST as a conditional on (all-s hBv); making it unconditional =
  build solution_A1_uniform as the satisfiability witness under u₀∈A¹. Mdot/B8 recon died on server rate-limit —
  re-dispatch (does committed dev bound the time-derivative coeffs uniformly, like windowEigEnv for u?).
## ============================================================================================================

## Mdot/B8 VERDICT (2026-06-14, recon aeeaff0): (B) DEEP — needs a parabolic regularity BOOTSTRAP, not assembly
The committed dev ISOLATES this gap: every chemDiv producer (CoupledChemDivTimeC1Fields.MchemDot/hMdot @
IntervalChemDivTimeDerivative.lean:109-110; ChemDivSourceAssembly.lean:63; etc.) carries Mdot/hMdot as an UNFILLED
hypothesis. ChemDivAdot.lean discharges adot/h_deriv/h_adotcont but explicitly leaves Mdot = EWA-T-3 residual.
NO committed lemma bounds |coupledChemDivAdot s n| uniformly in n (neither [0,T] nor window [τ₀,T]).
WHY the window doesn't auto-unlock it (my analysis): committed (kπ)²-bound gives λ_k|û_k|≤windowEigEnv_k, but
  windowEigEnv_k ~ 1/k² (the source env(a'/2) term DOMINATES the super-poly heads λ_k·e^{-a'λ_k}). So on the window
  u∈A² but NOT A³ ⟹ Δu∈A⁰ not A¹ ⟹ ∂ₜu=Δu+F∈A⁰ not A¹ ⟹ B_t=∂ₜu·∂ₓv·q+…∈A⁰ ⟹ ∂ₓB_t∈A^{-1} (envelope diverges).
  Mdot needs ∂ₜu∈A¹ needs u∈A³ — one PARABOLIC BOOTSTRAP level above the committed env (which did ONE level).
TWO construction routes (both NEW work, recon-confirmed): (1) EWA-T-3: build B_t as a weight-3 EWA element (needs
  embedEWA(∂ₜu)∈EWA T 1 i.e. ∂ₜu∈A¹), gDeriv, sourceEnvelope → Mdot via chemDivAdot_Mdot_residual. (2) Compactness:
  prove ChemDivMixedTimeDerivClosedRepr (Gmix, needs weighted-ℓ¹ on ∂ₜu/∂ₓ∂ₜv) then mirror
  exists_Mdot_adottOf_bound_Icc_of_lt_horizon (IntervalDomainPositiveWindowK1OnEndpoint.lean:228 — the LOGISTIC
  source's window-Mdot via joint-continuity+compactness+cosineCoeffs_abs_le). Both hinge on the bootstrap input.
ASYMMETRY (vs A¹): A¹ value gap = TRACTABLE (R2 window+heat-tail, r=1 directly from committed bound). Mdot time gap
  = DEEP (the parabolic bootstrap u∈A³, the highest-risk brick from day 1). The honest hard core of the campaign.
## ============================================================================================================

## ★★★ R2 BREAKTHROUGH (2026-06-14, cron2 verified SOUND) — direct route BYPASSES Mdot/B8 entirely
ChatGPT Pro cron2 (1fe23ad5, 344s) verified R2 SOUND: the FINAL conclusion Summable(λ_n·|∫₀ᵗ e^{-(t-s)λ_n}·G_n ds|)
at FIXED t∈(0,T] is proven DIRECTLY by the split estimate, NOT via the committed DuhamelSourceTimeC1On consumer.
  (I) [τ₀,t]: λ_n∫_{τ₀}^t e^{-(t-s)λ_n}ds = 1−e^{-(t−τ₀)λ_n} ≤ 1, so Σλ_n|∫_{τ₀}^t …| ≤ Σ E_n < ∞ (window A⁰
      source envelope E_n, ΣE_n<∞). VERIFIED exact.
  (II) [0,τ₀]: |G_n|≤C(1+n) (poly, from u,v bounded — NOT A¹), heat gap t−τ₀>0 ⟹ Σλ_n·Cn·τ₀·e^{-(t−τ₀)λ_n}
      = Cτ₀Σ n³π²e^{-(t−τ₀)(nπ)²} < ∞ (super-poly beats poly). VERIFIED.
KEY CONSEQUENCE: the DuhamelSourceTimeC1On package is the ONLY thing that demanded Mdot/adot. R2 proves the
  conclusion WITHOUT it ⟹ Mdot/B8 (the deep parabolic-bootstrap gap) is BYPASSED, NOT needed. Also bypasses all-s
  A¹ (only window A¹ + poly early bound). The two "deep" gaps are both routed around by the direct fixed-time proof.
R2 inputs to build: (I) window source ℓ¹ envelope on [τ₀,t] (from solution_A1_on_pos window Bv — slice-wise A¹
  Banach-algebra estimate OR windowed embedEWA; decide which avoids the t=0 embedEWA wall); (II) poly bound
  |coupledChemDivSourceCoeffs s n|≤C(1+n) on [0,τ₀] (|B_n| bounded ⟹ |∂ₓB coeff|=nπ|B_n^sin|≤Cn, from u,v∈L∞
  committed); + the heat-tail summable lemma Σ n³e^{-cn²}<∞ (near-committed: unitIntervalCosineEigenvalue_mul_exp).
NEW TARGET THEOREM: chemDiv_eigenvalueSummableOn_viaR2 — proves the FINAL conclusion from (I)+(II)+elementary, NO
  Mdot, NO all-s A¹. This is the route to UNCONDITIONAL. 合龙处慢审: verify the split integrability + the slice-wise
  envelope at the join.
## ============================================================================================================

## ★★★★ CAPSTONE (2026-06-14, commit 6f4771a) — both DEEP gaps ELIMINATED; eigenvalue-ℓ¹ on standard open-window regularity
chemDiv_eigenvalueSummableOn_uncond (ChemDivUncond.lean): the chemDiv eigenvalue-ℓ¹ spectral summability (conclusion
char-for-char = of_solution, about the ORIGINAL u), proven by discharging the three R2 hypotheses. Clean-tree EXIT 0
(8400 jobs), #print axioms clean, HOSTILE-AUDITED FAITHFUL+SOUND (conclusion exact; rfl time-shift genuine — source
slice-local verified layer-by-layer; (I)+(II) transport correct; hyps standard+satisfiable+non-smuggling).
ELIMINATED (vs of_solution): Mdot/adot/h_deriv/h_adotcont/h_Mdot (B8 parabolic-bootstrap time-chain, the day-1
highest-risk brick) + all-s A¹ over closed [0,T] (the t=0 wall). Route: R2 direct fixed-time split (ChatGPT-Pro
cron/cron2 verified) bypasses the DuhamelSourceTimeC1On consumer (sole Mdot demander).
REMAINING CONDITIONALITY = standard solution regularity, ALL on the OPEN window (off the wall):
  (I) shifted-window A¹/eval-bridge for ũ=u(·+τ₀): Bv/hBv/hBvnn/hBvsum (A¹ via solution_A1_on_pos) +
      hgrad/h_flux_nbhd/h_flux_diff (the eval-bridge realizations — SAME shape of_solution carried; FurtherReduce:
      wire FluxRealizeEmbed.flux_nbhd_of_embed under floor/positivity to discharge h_flux_nbhd).
  (II) early-slice L∞: M/hLiftCont/hLiftBd (C⁰ sup-bound of source lift on [0,τ₀]×[0,1]).
  (III) hGcont: per-mode C⁰ time-continuity of coupledChemDivSourceCoeffs.
These have NO committed general-solution lemma (the dev provides them for Picard iterates, not abstractly) — genuine
"strong solution" inputs. NEXT: (a) wire FluxRealizeEmbed → discharge eval-bridge (I); (b) assess what higher paper
theorem consumes the eigenvalue-ℓ¹ summability (is this lemma the paper's target, or feeds a global-existence thm?).
## ============================================================================================================

## WIRING VERDICT (2026-06-14, recon ae7349d): ROUTE (A) — R2 summability wires into Thm 1.1, Mdot stays bypassed
The χ₀=0 FrontierCore provider (IntervalDomainThm11ChiZeroCoreProvider.lean:332-440) consumes hsrc0F :
DuhamelSourceBddOn (NOT TimeC1On) — only .henv_summable/.henv_bound/.hcont (envelope + eigenvalue-ℓ¹ summability),
NO adot/derivBound. Consumed fields hbsumF (:382-393 bare Summable), hG1tF/hG2tF (gradient/C² via
deriv_lift_bound_on_compact, IntervalCompactSliceGradientBounds.lean:411,482 — consume only hbsum), hagreeF, K1
quadruple. Mdot/adot demand is ONLY on the logistic-iterate TimeC1On leg (K1WeakEndpoint restartCosineSeries_
hasDerivWithinAt + IntervalPicardSourceTower) — ORTHOGONAL to the chemDiv source.
χ₀=0 hard-coding: intervalGradientDuhamelMap (IntervalGradientDuhamelMap.lean:58-64) = heat(u₀) +
(-χ₀)·∫∂ₓS(t-s)chemFlux + ∫S(t-s)logistic. At χ₀=0 the chemotaxis term vanishes ⟹ source = pure logistic
patchedSource. χ₀≠0 lift: source coeff = logistic + (-χ₀)·chemDiv (LINEAR, additive — the Duhamel map is literally
that sum). ADDITIVE SPLIT FEASIBLE (Summable.add; consumers bound via of_nonneg_of_le against envelope).
VERDICT ROUTE (A): chemDiv_eigenvalueSummableOn_uncond (R2, NO Mdot) is a DROP-IN additive summand to the committed
logistic eigenvalue-summability. NO provider field changes type; the χ₀≠0 version supplies the augmented summand.
Mdot genuinely bypassed at the wiring. Remaining wiring cost (NOT Mdot): (1) additive-coeff-split lemma
(Duhamel-integrated combined coeff = logistic + (-χ₀)·chemDiv); (2) instantiate R2's 3 open-window hyps
(shifted-window A¹/eval-bridge + early-slice L∞ + hGcont) at the CONE datum D.u — genuine strong-solution inputs
(dev has them for Picard iterates, not abstractly; F1-class, shared with the mild→classical bridge gap).
NEXT: build the Mdot-free combined-source summability scaffold (ChemDivWiring.lean), then the open-window-hyp
instantiation at D.u (the genuine remaining PDE-regularity content for χ₀≠0 Thm 1.1).
## ============================================================================================================

## WIRING SCAFFOLD AUDIT (2026-06-14, audit a57014c): SOUND-BUT-MISTARGETED — trashed; real wiring is deeper
The additive scaffold (combinedDuhamel_eigenvalueSummable) was mathematically sound + Mdot-free, BUT the audit
caught it MIS-TARGETED + dead code: its conclusion |∫₀ᵗ exp·(Glog+c·Gchem)| puts everything INSIDE one integral,
whereas the provider's actual hbsumF (ChiZeroCoreProvider.lean:382-393) is Summable(λ_n·|limitCoeff p u₀ D.u σ n|)
with limitCoeff = exp(-σλ_n)·û₀_n + duhamelSpectralCoeff(logistic) (IntervalPicardLimitRestart.lean:102-106) — a
HEAT TERM OUTSIDE the integral + the Duhamel source. The integral-form abstract lemma is the WRONG SHAPE to produce
that; hlog was mis-advertised as "committed hbsumF" (it's heat-free). Trashed (untracked, not committed).
THE REAL WIRING (corrected understanding): right shape = BARE-coefficient additive lemma
  Summable(λ|a|) + Summable(λ|b|) ⟹ Summable(λ|a + c·b|), instantiated a := limitCoeff_logistic (=hbsumF, heat+
  Duhamel), b := chemDiv Duhamel coeff (=capstone). BUT a+(-χ₀)·b must = the χ₀≠0 solution's spectral coeff — which
  requires a χ₀≠0 MILD SOLUTION whose coeff splits as heat + Duhamel(logistic+(-χ₀)chemDiv) = limitCoeff_logistic +
  (-χ₀)·chemDiv-Duhamel. That χ₀≠0 solution does NOT exist in the committed χ₀=0-restricted dev. So the wiring needs
  the χ₀≠0 PICARD/mild-solution construction (+ its per-coeff Duhamel split) — NOT a trivial add. Route A (Mdot-free)
  still holds, but the wiring is the χ₀≠0 solution sub-campaign (F1-class), not plumbing.
HONEST STATE: capstone chemDiv_eigenvalueSummableOn_uncond (χ₀≠0 source-ℓ¹, the campaign's STATED goal) DONE +
  audited. It is the KEY INGREDIENT the χ₀≠0 Picard source-regularity step needs. Full wiring to Thm 1.1 = build the
  χ₀≠0 solution (generalize the χ₀=0 Picard machinery, the capstone supplies its source-ℓ¹) + open-window hyps at
  D.u. Large continued effort (shares F1-class strong-solution content).
## ============================================================================================================

## ★★★ χ₀≠0 Thm 1.1 REACHABLE (2026-06-14, recon af9c54f) — solution EXISTS committed; blocker is ONE B5 brick, NOT F1
MAJOR CORRECTION: the χ₀≠0 mild solution ALREADY EXISTS, committed + 0-sorry. intervalMildSolution_exists_picard
(IntervalMildPicard.lean:1486) builds the FULL χ₀≠0 fixed point — intervalGradientDuhamelMap (IntervalGradient
DuhamelMap.lean:58-64) literally contains (-χ₀)·∫∂ₓS(t-s)chemFlux; contraction closes with |χ₀| in the constant
(glue1 chemFlux_div_lipschitz IntervalChemFluxLipschitz.lean:111 + Atom D gradDuhamel_sup_bound + gradientDuhamel_
contraction_pointwise :152, invoked IntervalMildPicard.lean:2602/2733). NO F1 wall for existence (gradient-Duhamel
form consumes only C⁰ flux Q; capstone source-ℓ¹ not even needed for existence).
THE SINGLE HARD BLOCKER (NOT F1, it's B5 EWA coefficient-bridge): the χ₀≠0 PER-COEFF DUHAMEL SPLIT
  cosineCoeffs(solution σ)_n = exp(-σλ_n)û₀_n + duhamelSpectralCoeff(logistic)_n + (-χ₀)·chemDiv-Duhamel-coeff_n.
  Committed ONLY under hχ0=0: limitCoeff (IntervalPicardLimitRestart.lean:102-106) is logistic-only; the bridge
  cosineCoeffs_halfstep_eq_limitCoeff_weak (IntervalPicardLimitRestartWeak.lean:372) gated on hχ0 (:373), routes
  through intervalGradientDuhamelMap_eq_of_chi0_zero (IntervalPicardIterateRestart.lean:85) killing chemotaxis.
SUBTLETY (the map-form distinction): the Picard map uses GRADIENT-form (-χ₀)∂ₓS·chemFlux (∂ₓ-of-semigroup, sine
  coeffs / Dirichlet kernel via IBP); the capstone is SOURCE-form coupledChemDivSourceCoeffs = cosine coeff of
  ∂ₓB (S·∂ₓB). These DIFFER on Neumann [0,1] (boundary/IBP terms). The B5 brick must reconcile them (gradient-Duhamel
  chemotaxis coeff ↔ source-form summability).
ONCE B5 split exists: A¹ window de-gates (solution_A1_on_pos hbridge SolutionA1.lean:190 = the SAME χ₀=0 split,
  collapses to one blocker); capstone supplies chemDiv ℓ¹; additive summability assembles (Route A). Residue: hGcont
  (per-mode time-cont of chemDiv coeff, genuinely carried) + L∞/continuity (committed-suppliable, picardLimit_
  hasContinuousSlices). VERDICT: χ₀≠0 Thm 1.1 REACHABLE — reduces to the B5 per-coeff split + small residue.
NEXT: build the B5 χ₀≠0 per-coeff Duhamel split (first reconcile gradient-form vs source-form for the chemotaxis
  term), then de-gate the A¹ window, assemble the additive summability into the χ₀≠0 hbsumF, lift the χ₀=0 provider.
## ============================================================================================================

## ★★★ B5 RECONCILIATION FAILS (2026-06-14, recon a6dbf74) — capstone (source-form) does NOT wire to Thm 1.1
HONEST SETBACK: the source-form capstone does NOT transfer to the gradient-form (Picard map / Thm 1.1) coefficient.
TWO independent obstructions, both verified (explicit IBP + numerical to 1e-6):
(A) MAP-FORM DIFFERENCE. Picard map chemotaxis term = gradient-form (-χ₀)∂ₓ[S(t-s)chemFlux] (IntervalGradient
    DuhamelMap.lean:61-62, ∂ₓ OUTSIDE S). Capstone = source-form S·∂ₓchemFlux (∂ₓ inside). On Neumann [0,1] IBP:
    gradient cosine coeff_n = bulk_n (off-diagonal Hilbert-transform mixing ~1/(k-n)) + bdy_n where
    bdy_n = 2((-1)ⁿ S(τ)g(1) - S(τ)g(0)). bdy_n is O(1) NON-DECAYING in n (chemFlux g violates Neumann BC, so
    S(τ)g(0/1)≠0). Duhamel eigenvalue kernel λ_n∫e^{-(t-s)λ_n}ds=1-e^{-tλ_n}→1 (no decay) ⟹ Σλ_n|gradDuhamel_n|
    terms→O(1) ⟹ DIVERGES. Source-form summability CANNOT bound gradient-form. No honest equality/≤ lemma exists.
(B) STRUCTURAL χ₀=0-ONLY. limitCoeff (IntervalPicardLimitRestart.lean:102-106) = e^{-tλ_k}û₀_k +
    duhamelSpectralCoeff(LOGISTIC) — NO chemotaxis term. The fixed-point→spectral bridge cosineCoeffs_halfstep_eq_
    limitCoeff_weak gated on hχ0, applies intervalGradientDuhamelMap_eq_of_chi0_zero (IntervalPicardIterateRestart.
    lean:85: rw[hχ0];ring) DELETING the chemotaxis term. capstone has NO consumer outside ChemDiv*; limitCoeff/
    hbsumF NEVER reference coupledChemDivSourceCoeffs/chemDivEWA/chemFluxLifted (grep empty intersection).
CORRECTION TO PRIOR ROUTE.md: the "route A / capstone is the key ingredient / drop-in additive summand" framing was
WRONG. The capstone is a CORRECT source-form theorem but targets the WRONG map-form for Thm 1.1. The map-form
distinction (flagged campaign-early) is a GENUINE mathematical obstruction, not bookkeeping.
WHAT THM 1.1 χ₀≠0 ACTUALLY NEEDS: gradient-form chemotaxis coefficient eigenvalue-ℓ¹ summability — control the
boundary term 2((-1)ⁿSg(1)-Sg(0)) + the off-diagonal bulk mixing, requiring EXTRA solution regularity (flux endpoint
decay), NOT available from the source-form bound. A NEW, harder target. DECISION POINT (surfaced to Xiang): pursue
the gradient-form (hard, boundary-term obstruction) or consolidate capstone as a standalone correct source-form
result. The capstone stands as correct mathematics (χ₀≠0 source-form chemotaxis spectral ℓ¹, 0 sorry/0 axiom,
hostile-audited) but is NOT the Thm 1.1 wiring ingredient.
## ============================================================================================================
