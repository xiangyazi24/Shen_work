# Fable design: ACYCLIC boundedness route for Thm 1.2 (breaks the resolver circularity)

## The circularity break (the one fact)
Resolver SUP bound Fg(M)≲‖u‖_∞^γ is a NEEDLESS overestimate. T:=∂ₓ(−∂ₓₓ+μ)^{-1} is order-(−1) smoothing:
  ‖v‖_{W^{2,q}} ≤ C_E‖νu^γ‖_{L^q} = C_E ν‖u‖_{L^{γq}}^γ  (any q∈(1,∞))
  ‖v_x‖_{L^s} ≤ C_E‖u‖_{L^{γs}}^γ    (load-bearing line)
  ‖v_x‖_∞ ≤ C_E'‖u‖_{L^{γq}}^γ  (any q>1, via 1D W^{2,q}↪C¹)
The v-gradient needs only an L^{γq} bound — a STRICTLY LOWER exponent than the current rung. Substituting
‖u‖_∞^γ → ‖u‖_{L^{γq}}^γ converts the cyclic graph into a DAG. Everything else is bookkeeping.

## Per-level DI (test u-eq with p u^{p-1}, w:=u^{p/2})
d/dt∫uᵖ + (4(p−1)/p)∫|∂ₓw|² = 2χ₀(p−1)∫w(∂ₓw)(1+v)^{−β}v_x + ap∫uᵖ − bp∫u^{p+α}.
Young ε=1/(pχ₀) absorbs EXACTLY half the diffusion (no χ₀-smallness here); leftover κ_p:=χ₀²p(p−1)/2:
  (★) d/dt yₚ + (2(p−1)/p)∫|∂ₓw|² ≤ κ_p∫uᵖv_x² + ap yₚ − bp∫u^{p+α},  yₚ:=∫uᵖ.
Close κ_p∫uᵖv_x² two ways:
 (A) sup route (1D-cheap): ∫uᵖv_x² ≤ ‖v_x‖_∞² yₚ ≤ C_E'²‖u‖_{L^{γq}}^{2γ} yₚ — LINEAR in yₚ if lower-rung K:=‖u‖_{L^{γq}} exists.
 (B) L²-gradient route: ‖v_x‖_{L²}≤C_E‖u‖_{L^{2γ}}^γ, then GNS-interpolate (used when (A)'s lower rung unavailable, γ≥1).

## Base L¹ — FREE, no L∞, no chemotaxis (DAG root)
Integrate u-eq: diffusion + ENTIRE chemotaxis divergence integrate to 0 (Neumann). Only reaction survives:
  d/dt‖u‖₁ = a‖u‖₁ − b∫u^{1+α} ≤ a‖u‖₁ − b‖u‖₁^{1+α} (Jensen) ⟹ limsup‖u‖₁ ≤ (a/b)^{1/α}. Absorbing, horizon-uniform.

## DAG acyclicity
Rank each node by produced Lebesgue exponent ρ∈[1,∞]. Rung p consumes rank γq, produces rank p. Edge downhill iff γq<p.
Every edge strictly increases rank; strict-increase on set bounded below = well-founded = no cycle. Geometric ladder
p_{k+1}=θp_k reaches ∞ in countably many rungs. Only failure: a rung with γq≥p i.e. γ≥p (the γ-threshold).

## γ-threshold VERDICT
- γ<1: route (A) grounds directly (γq≤1 ⊂ L¹). Seed p₀=2. NO χ₀-smallness anywhere.
- γ≥1: route (A) descends forever; MUST use route (B) GNS climb (diffusion-grounded at L¹). χ₀<chiBeta genuinely required.
- "L²=p₀=2 clears only γ<2" = the CHEAP BYPASS (§3), NOT the theorem. Bypass consumes L^{γq}(q>1) covered by seed L²:
  need γq≤2 with q>1 ⟺ γ<2. For γ≥2: minimal seed p₀=γ⁺, produced by route-(B) GNS sub-ladder L¹→L^{γ⁺}.
- NET: in 1D NO γ-threshold for boundedness itself; γ<2 only bounds where the infra-cheap route works.

## χ₀ absorption / chiBeta origin
When diffusion must absorb (route B): χ₀²<chiBeta_p² := (2(p−1)/p)/(p(p−1)·C_E²·C_GNS(p)·K_{2γ}^{2γ}),
chiBeta=inf_p chiBeta_p. Exactly the Keller–Segel-with-logistic coercivity condition, thresholded by the bottom rung.
GUARD: verify chiBeta_p bounded below (else hypothesis vacuous at high rungs). In 1D it is (GNS exponents stay admissible).

## 3-step 1D bypass (γ<2, smallest Lean surface, PREFERRED)
1. Seed L^{2γ} (=‖u^γ‖_{L²}): γ<1 ⊂L¹ free; 1≤γ<2 one route-(B) rung from L¹.
2. H¹-energy bound: test −u_xx; cross-term Young vs ∫u_xx²; leftover ≲χ₀²∫u_x²v_x²; bound v_x in L² via seed, u_x via GNS. NO ‖u‖_∞.
3. 1D Sobolev H¹↪L∞: ‖u‖_∞≤C_S‖u‖_{H¹}. Done.

## atTop upgrade
Every rung's comparison ODE dy≤Ay−By^{1+δ} (A,B horizon-indep) has entry time T*(A,B,δ) indep of y(0):
y(t)≤2y* ∀t≥T*, y*=(A/B)^{1/δ}. The superlinear sink −By^{1+δ} is what upgrades boundedBefore→∃M∀ᶠt.
M=sup_p(2y*_p)^{1/p} horizon-independent. This is the exact absorbing-set argument the atTop half needs.

## Lean lemma DAG (dependency-ordered)
L0 mass_L1_absorbing   : divergence + Jensen ⟹ limsup‖u‖₁≤(a/b)^{1/α}. [root, no input]
L1 elliptic_grad_estimate: ‖v_x‖_{L^s}≤C_E‖u‖_{L^{γs}}^γ; ‖v_x‖_∞≤C_E'‖u‖_{L^{γq}}^γ,q>1. [stateless]
L2 Lp_diff_ineq        : (★) with Young ε=1/(pχ₀). [needs L1] ⚠ MUST take lower-rung bound as explicit hyp, NEVER ‖u‖_∞.
L3 absorbing_ode       : dy≤Ay−By^{1+δ} ⟹ limsup y≤(A/B)^{1/δ}, entry time indep of y(0). [pure ODE]
L4 seed                : uniform L^{p₀},p₀>γ. γ<2⟹p₀=2 from L0+L2+L3; γ≥2⟹p₀=γ⁺ via one L5 rung. [needs L2,L3;L5 if γ≥2]
L5 gns_climb_step      : rung p→θp via diffusion dissipation+GNS+χ₀<chiBeta absorption. [needs L1,L2,L3] ← HARDEST
L6 Linfty              : γ<2→bypass(H¹+H¹↪L∞); general→Moser limit sup_p C_p^{1/p}<∞. [needs L4,L5]
L7 atTop_assembly      : boundedBefore+L3 absorbing constants ⟹ ∃M∀ᶠt‖u‖_∞≤M. [needs L6,L3]

## Single hardest lemma: L5 — the uniform-in-p tracking keeping sup_p C_p^{1/p}<∞ in L6.
If C_p^{1/p}→∞ you get every L^p but NOT L∞ (silent failure). γ<2 sidesteps via bypass (no p-family) — PREFER IT.

## Hidden-circularity / γ-gap guards
1. L1 sup-variant at a rung where consumed L^{γq} not yet uniform → reintroduces upward edge. Guard: assert γq<p + L^{γq}
   from strictly-lower node. This is exactly where Fg(M) circularity lived; L2 Lean statement takes lower-rung bound as
   explicit hyp, NEVER ‖u‖_∞.
2. Seed L4 for γ≥1: route (A) descends forever. Guard: force L4 through L5 (diffusion-grounded), never a chemotaxis rung.
3. L7 using per-horizon boundedBefore constant instead of absorbing L3 constant → finite-on-[0,T] not atTop. Guard: L7
   consumes A,B from L3 (provably horizon-indep, descend from (a/b)^{1/α}).
4. chiBeta must be inf_p chiBeta_p>0 (else vacuous at high rungs). Verify chiBeta_p bounded below (1D: yes).
