# Fable: complete Paper 1 Rothe branch construction (discharges BOTH carried hypotheses)

## VERDICT: closes, with 2 non-negotiable structural inputs (these ARE the content)
1. The uniform modulus L (C^{2,β} bound) MUST be part of the trap 𝒯. Whole-line trap "antitone, φ≤q≤B" is genuinely
   NON-COMPACT in C⁰_loc (Helly gives only POINTWISE limits ⇒ discontinuous limit / mass escaping to +∞ — the real
   obstruction). Fix: intersect with fixed modulus L. Admissible because parabolic smoothing + §3-bounded frozen
   coefficients give T(𝒯) a UNIFORM C^{2,β} bound. This ONE fact closes both compactness (L9) AND continuity (L10).
2. Both carried hypotheses are THEOREMS not hypotheses (see §2, §3).

## The trap 𝒯 = { q | φ ≤ q ≤ B, q antitone, ‖q‖_{C^{2,β}} ≤ L }
B (upper barrier) = min(1, e^{-κ(x-x₀)}) smoothed; φ (lower pin) = KPP subsolution; L = uniform Schauder modulus.
LEMMA (compactness): 𝒯 is COMPACT CONVEX in Fréchet space C⁰_loc (seminorms ‖·‖_{C⁰[-n,n]}). Convex: obvious. Compact:
uniform C^{2,β} ⇒ equi-Lipschitz on [-n,n] ⇒ Arzelà–Ascoli + diagonalize. (Helly NOT needed once L present.)

## The map T(q): freeze V_q, run cross-frozen parabolic w_t=w_xx+cw_x−χ∂ₓ(w^m∂ₓV_q)+w(1−w^α), w(0)=B.
Drift c−χmw^{m−1}∂ₓV_q bounded (|∂ₓV_q|≤1, §3) ⇒ uniformly parabolic, comparison applies.
LEMMA (long-time limit exists, TIME-MONOTONE): B supersol + φ subsol ⇒ φ≤w(·,t)≤B and t↦w(·,t) NONINCREASING ⇒
w(·,t)↓w_∞ pointwise; parabolic interior est ⇒ C²_loc; w_∞ stationary. T(q):=w_∞. NO Lyapunov needed.
T(q)∈𝒯 (antitone preserved by χ≤0 comparison vs translates; φ≤T(q)≤B; uniform C^{2,β} = §3 Schauder).

## §3 DISCHARGE (a) source-box: V_q=(½e^{-|·|})∗q^γ ∈ B_src AUTOMATICALLY for q∈𝒯 (Young + explicit kernel):
0≤V_q≤1 (Young, ∫G=1); |∂ₓV_q|≤1 (∫|G'|=1); |∂ₓ²V_q|≤2 (V''=V−q^γ, both∈[0,1]); ∂ₓV_q≤0 antitone image (= property
iii, symmetric kernel * antitone); tail V_q(x)≤C_γ e^{-sx}, s=min(γκ,1). = a LEMMA, not a hypothesis.

## §2 DISCHARGE (b) finite-cube: Schauder–Tychonoff on compact convex 𝒯⋐C⁰_loc (Fréchet locally convex) ⇒ T has
fixed point U∈𝒯 = stationary profile. NO finite-cube data needed. Constructive fallback: Schauder on [-R,R] Neumann
caps → U_R → (§1 compactness) subseq → U in C⁰_loc, equation passes locally (cap error → 0 as R→∞). Convergence of the
finite-cube approx fixed points is a THEOREM driven by 𝒯 compactness (the modulus L).

## §4 Adaptive-diagonal closed graph (Rothe moving-index). Implicit Euler (I−kL_q)W^{(j+1)}=W^{(j)}, resolvent Green
kernel R_k integrable + exp off-diagonal decay. Moving-index compactness ALONE fails (counterexample a(n,k)=1_{k≤n}).
FIX: choose kₙ s.t. ‖W^{(kₙ+1)}−S_k(W^{(kₙ)})‖_{C⁰[-n,n]}<1/n. Then W^{(kₙ)}→W_∞ (compactness) + residual→0 on every
compact (n→∞ sweeps ℝ). Green closed graph (dominated convergence via R_k decay + §3 box) ⇒ W_∞=S_k(W_∞) ⇒ L_q W_∞=0
= profile equation. NO k→0 limit, NO global uniform tail (profile eq is LOCAL).

## §5 Right tail: linearize at U=0: κ²−cκ+1=0 ⇒ κ±=(c±√(c²−4))/2, κ₋κ₊=1. cStarLower=2, κ(c)=(c−√(c²−4))/2∈(0,1)
for c>2. Three correction exponents: (1+α)κ [nonlinear reaction], mκ+s s=min(γκ,1) [chemotaxis-elliptic], 1 [Green
kernel]. Window (κ(c), min((1+α)κ, mκ+min(γκ,1), 1)) NONEMPTY ⟺ c>2 (binding gate = kernel exponent 1).
⚠ CAVEAT: paper's literal mκ+1/2 = specialization s=min(γκ,1) at s=1/2 (holds iff γκ(c)=1/2; generically s=γκ(c)).
Doesn't affect closure. General statement should read mκ+min(γκ(c),1) unless paper pinned γκ=1/2. VERIFY vs source.
Barrier: B supersol of paperWaveOperator (favorable −|χ|W^{m+γ}) under RELAXED budget |χ|(1+mγκ²)/(1−γ²κ²)≤1+|χ|
(RHS 1+|χ| from the −|χ|W^{m+γ} term). At fixed pt paperWaveOperator=frozenWaveOperator ⇒ transfers.

## LEAN DAG
L1 green_kernel_bounds → L2 source_box(disch a) → L3 frozen_coeff_uniform → L4 comparison_principle;
L5 barrier_supersolution[relaxed budget], L6 subsolution_pin → L7 longtime_limit_exists[time-monotone] →
L8 T_maps_trap → L9 trap_compact_convex[Arzelà+modulus] → L10 ★T_continuous_Cloc★[double-limit, Dini] →
L11 schauder_tychonoff_fp(disch b) → L12 profile_solution+tail.
Rothe alt: L7' adaptive_diagonal_select → L8' green_closed_graph → L9' self_implicit_step.
HARDEST = L10 (only double limit t→∞ ∘ q_j→q; interchange needs monotone-in-t loc-uniform UNIFORMLY in j — Dini +
uniform C^{2,β} from L3/L8).
HIDDEN-GAP candidates (ranked): 1) L10 interchange (needs explicit equicontinuity from modulus — make L8 C^{2,β} an
explicit hyp of L10); 2) L9 compact (needs modulus L, not just boundedness — cite L8/L3); 3) L8'/L9' closed graph
(needs adaptive diagonal L7' — else a(n,k) counterexample). L7 existence is SAFE (time-monotonicity, no Lyapunov).
