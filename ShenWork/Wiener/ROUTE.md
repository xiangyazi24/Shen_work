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
