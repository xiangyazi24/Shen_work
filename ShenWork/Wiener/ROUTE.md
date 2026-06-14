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
## ====================================================================================================

Goal: build, from scratch (Mathlib has NONE of this), the weighted Wiener algebra needed to
prove the chemotaxis divergence source `∂ₓB ∈ A` (B = u·v_x/(1+v)^β) for the actual nonlinear
Picard iterate — discharging the source-ℓ¹ hypotheses my committed duhamelSpectral bricks consume.
User decision (2026-06-13): build the unconditional Wiener–Lévy path, 稳打稳扎, one audited brick
at a time. Lean on ChatGPT (cron + cron2) for route design + adversarial check each brick.

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
