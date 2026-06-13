# Wiener-algebra build — route & doctrine (χ₀<0 unconditional regularity)

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

NEXT (green-lit): brick 3 = Banach-algebra structure of W^r (‖aⁿ‖≤‖a‖ⁿ, completeness) + the algebra
exponential exp(a)=Σaⁿ/n!, eval_x(exp a)=exp(eval_x a), D(exp(−tf))=−(Df)exp(−tf). brick 4 = the
decisive estimate. brick 5 = Gamma/Laplace Wiener–Lévy. Then E_T^r envelope + the A^r heat semigroup
+ divergence-Duhamel smoothing + resolver multipliers + flux bounds + the C_tE^r fixed point.

## Honest status discipline (user feedback 2026-06-13)
Report only proved-unconditional commits, never "reduced to N residuals" / "快收口". A conditional
theorem is conditional; name its hypotheses. See feedback_no_residual_framing.
