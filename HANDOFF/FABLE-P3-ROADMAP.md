# FABLE ROADMAP — Paper 3 dynamical engine (Thm 2.2 / 2.3-2.5), avoid Henry sectorial theory
# (Fable answer 2026-07-12 — the roadmap's LONGEST POLE, cracked. Verify-don't-transcribe each step.)

## The one reduction: eliminate v = R[u] = (−Δ+μ)^{-1}(νu^γ); whole system = ONE nonlocal scalar
## parabolic eq for u, done in the cosine basis e_k=cos(kπx), −Δe_k=λ_k e_k, λ_k=(kπ)². This escapes Henry.

## A. Linearized decay, mode-wise (u=u*+φ, v=v*+ψ, ∇v*=0):
## reaction → −aα·φ (since a−bu*^α=0, −bαu*^α=−aα); ψ=γνu*^{γ-1}(−Δ+μ)^{-1}φ;
## chemotaxis → −χ₀u*(1+v*)^{-β}Δψ. Single constant κ := χ₀·γν·u*^γ·(1+v*)^{-β}.
## ⇒ φ_k' = σ_k φ_k, σ_k = −λ_k(λ_k+μ−κ)/(λ_k+μ) − aα. k=0: σ_0=−aα<0. k≥1: σ_k<0 ⟺ κλ_k<(λ_k+μ)(λ_k+aα).
## SHARP THRESHOLD: f(λ)=(λ+μ)(λ+aα)/λ, min at λ*=√(μaα), value (√μ+√(aα))². So
##   STABILITY ⟺ κ < κ_crit = (√μ+√(aα))² = μ+aα+2√(μaα).   (covers χ₀≤0 automatically since κ≤0.)
## χ_β = (√μ+√(aα))² / [γν u*^γ (1+v*)^{-β}],  u*=(a/b)^{1/α}, v*=(ν/μ)u*^γ.  Rate δ=min(aα, min_{k≥1}(−σ_k)).
## PHASE SPACE X^s = {φ : Σ_k(1+λ_k)^s|φ_k|²<∞}, s>1/2 (↪C⁰). Semigroup DIAGONAL:
##   (L1 decay) ‖e^{tL}φ‖_s ≤ e^{−δt}‖φ‖_s  (each mode e^{σ_k t}).
##   (L2 smoothing) ‖e^{tL}φ‖_{s+θ} ≤ C_θ t^{−θ/2}e^{−δ't}‖φ‖_s, 0≤θ<2, from sup_λ λ^{θ/2}e^{−λt}=(θ/2e)^{θ/2}t^{−θ/2}.
## ⇒ L2 IS the exact one-line replacement for Henry's fractional smoothing. Only mild=classical uniqueness (Gronwall) needed.

## B. Nonlinear closing: route (b) mode-wise Duhamel/stable-manifold WINS over (a) LaSalle (LaSalle needs
## semiflow+ω-limit+compact embedding+invariance principle = 4-5 libraries not in Mathlib). (b) = L1+L2+one
## nonlinearity est + Banach fixed point (Mathlib ContractingWith). (b) alone = LOCAL = Thm 2.2. For global
## (2.3-2.5): two-stage (Tello-Winkler): entropy dissipation drives orbit into basin (L8), then (b) closes exp.

## C. Asymptotic compactness = elementary 1D Arzelà-Ascoli (Mathlib has it): |φ(x)−φ(y)|≤‖φ'‖_{L²}|x−y|^{1/2}.
## Need: sup_{t≥T}‖u(t)‖_{H¹}≤M (from eventual L∞ ⇒ uniform L² ⇒ L2-smoothing θ=1 pushes X^0→X^1 for t≥T+1).

## D. Entropy: H(u)=∫[u ln(u/u*)−(u−u*)]≥0 (=0 iff u≡u*, convex pointwise). Dissipation identity (IBP, Neumann):
##   dH/dt = −∫|∇u|²/u + χ₀∫(1+v)^{-β}∇u·∇v − b∫u ln(u/u*)(u^α−u*^α). 1st,3rd ≤0; middle indefinite.
## Young(weight 1/u): |χ₀∫(1+v)^{-β}∇u·∇v| ≤ ½∫|∇u|²/u + (χ₀²/2)∫u(1+v)^{-2β}|∇v|². Bound (1+v)^{-2β}≤1, u≤M∞.
## Modal Poincaré: ∫|∇v|²=Σ_{k≥1}λ_k v_k²=ν²Σ_{k≥1}λ_k(u^γ)_k²/(λ_k+μ)² (only k≥1 = Poincaré gain λ_1=π²>0)
##   ≤ (ν²γ²u*^{2(γ-1)}/(π²+μ)²)∫|∇u|². Domination ⟺ χ₀² < (π²+μ)²(1+v*)^{2β}/(M∞²ν²γ²u*^{2(γ-1)}) [entropy-side threshold].
## RECONCILE the two thresholds in chiBeta (state under binding one, prove other implies it) — the one hidden-gap risk.

## E. Lemma DAG (reuse black boxes: existence/nonneg/L∞, cosine diag, resolver R+grad bounds, equilibrium):
## L1 diagonal decay [easy] · L2 diagonal smoothing [easy] · L3 threshold κ<κ_crit⇒δ>0, unwind χ_β [easy-med]
## L4 nonlinearity ‖N(φ)‖_{X^{s-1}}≤C(‖φ‖_s)‖φ‖_s² (1D Sobolev algebra s>1/2; chemo loses 1 deriv→X^{s-1}, matched by L2 θ=1) [med]
## L5 LOCAL exp stability (Thm 2.2): Duhamel φ=e^{tL}φ_0+∫e^{(t-τ)L}N(φ), contraction in sup_t e^{δ''t}‖·‖_s [HARD CORE]
## L6 entropy dissipation identity (∂ₜ/∫ interchange from uniform H²) [med] · L7 coercivity dH/dt≤−c₀D [med, sharp const]
## L8 basin entry: ∫₀^∞D<∞ ⇒ D(u(t_n))→0 ⇒ ‖u(t_n)−u*‖_{H¹}→0 + uniform continuity ⇒ eventually in basin [REPLACES LaSalle]
## L9 GLOBAL convergence (Thm 2.3): enter basin (L8)→apply L5→exp sup convergence; v→v* via resolver [easy glue]
## HARD CORE ranked: L5 Duhamel contraction (elementary once L1/L2/L4) > L7 sharp absorption > L4 deriv-loss > L8 bridge.
## Sectorial theory needed NOWHERE — only L2 (one line of modal calculus). Toolbox: Young(1/u), 1D Neumann-Poincaré
## ‖w−w̄‖≤(1/π)‖∇w‖, sup_λ λ^{θ/2}e^{−λt}, Arzelà-Ascoli via Hölder-½, Sobolev H^s↪C⁰ s>1/2.
