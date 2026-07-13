# Fable: concrete P3 Nemytskii verification — the abstract quadratic bound DOES apply to the true nonlinearity

## VERDICT: ‖N(w)‖_{L²} ≤ C‖w‖_{X^α}² TRUE on α∈[1/2,1) ⊇ (3/4,1). So the built L1-L4 core applies to reality.
Correction: α>3/4 NOT forced by Nemytskii — genuine threshold is α≥1/2 (3/4 = H^{2α}↪C¹ comfort margin only).

## Two load-bearing facts (adversarial flags CONFIRMED real):
1. POSITIVITY RADIUS ρ₀ INDISPENSABLE. For α<1, γ<2 the 2nd Taylor derivs (u*+w)^{α-1},(u*+w)^{γ-2} BLOW UP as
   u*+w→0 — quadratic bound FALSE without positivity. TRUE on {‖w‖_∞≤u*/2}. ρ₀:=u*/(2C_∞) (‖w‖_∞≤C_∞‖w‖_{X^α}).
   On B_{ρ₀}: u*+sw≥u*/2, 1+V(w)≥(1+v*)/2 ∀s∈[0,1]. Thread into EVERY power-function lemma (rpow needs positive base).
2. DERIVATIVE IN DIVERGENCE. N=−χ₀∂ₓG(w), measured in L². ROUTE (a) keep ∂ₓ, need G(w)∈H¹ ⇒ α≥1/2. ROUTE (b) absorb
   ∂ₓ into semigroup needs t^{-(α+1/2)} integrable ⇔ α<1/2 ⇒ (b) does NOT close on (3/4,1). Route (a) mandatory+sufficient.

## Key simplification: v*=νu*^γ/μ CONSTANT ⇒ ∂ₓv*=0. So DΦ(0)[w]=Φ_lin ⇒ G(w)=Φ(w)−DΦ(0)[w] genuine 1st-order
Taylor remainder = quadratic. Leading bilinears: w·q*·∂ₓZ₁(w), u*(q(w)−q*)∂ₓZ₁(w) with q(w)−q*=O(w).

## The three pieces:
(B) logistic: B(w)=−bα(1+α)[∫(1−s)(u*+sw)^{α-1}ds]w², ‖B‖_{L²}≤C_B C_∞‖w‖_{X^α}² (α>1/4, needs ρ₀).
(3) elliptic: P(w)=νγ(γ−1)[∫(1−s)(u*+sw)^{γ-2}ds]w², Z₂=R[P], ‖Z₂‖_{H²},‖∂ₓZ₂‖_{H¹}≤C‖w‖²_{X^α}. NO γ-threshold beyond
    γ>0+positivity (γ=1⇒Z₂≡0). Z₁=R[νγu*^{γ-1}w], ‖Z₁‖_{H^{2α+2}}, ∂ₓZ₁∈H^{2α+1} (smoother than w — makes route(a) work).
(A) chemA route(a): G(w)∈H¹ via H^{2α} algebra + ∂ₓZ₁∈H^{2α+1}; the w·∂ₓZ₁∈H¹ step USES 2α≥1 (∂ₓ(w∂ₓZ₁)=∂ₓw·∂ₓZ₁+
    w·∂ₓₓZ₁∈L²·L∞+L∞·L²⊂L²). ‖A‖_{L²}≤|χ₀|C_A‖w‖²_{X^α}, α≥1/2.

## THEOREM: α∈[1/2,1), ‖w‖_{X^α}≤ρ₀ ⇒ ‖N(w)‖_{L²}≤C‖w‖²_{X^α}, C=|χ₀|C_A+C_B C_∞. Constant ∝u*^{α-1},u*^{γ-2}
(→∞ as u*→0, why ρ₀ needed). ALSO NEED polarized LOCAL-LIPSCHITZ ‖N(w₁)−N(w₂)‖≤C(‖w₁‖+‖w₂‖)‖w₁−w₂‖ for the fixed pt.

## SEPARATE caveat (OUTSIDE Nemytskii): decay δ>0 needs L's spectrum in {Re≤−δ}. Chemotaxis κ=χ₀γνu*^γ(1+v*)^{-β}
can destabilize high modes (Turing). δ>0 = smallness/sign on χ₀ = the LinearlyStable/κ<χ* condition (repo has it).
Nemytskii holds for ALL χ₀ (∝|χ₀|); stability is the DISTINCT linear hypothesis.

## Lean DAG L1-L10: L1 Embeddings1D; L2 EllipticGain ‖Rφ‖_{H^{s+2}}≤C_R‖φ‖_{H^s} Neumann ★HARD(BC/half-int);
L3 PositivityRadius ★★HARDEST-HIDDEN-GAP (thread u*+w≥u*/2 into every power lemma); L4 TaylorRem2 (needs L3); L5 LogisticB;
L6 ellipticP+Z2; L7 linZ1; L8 weight ‖q(w)−q*‖_{H^{2α+2}}≤C‖w‖ (Moser comp, needs 1+V>0 from L3); L9 chemA ★HARD
(route a, 2α≥1 bookkeeping = hidden gap #2); L10 Assemble (+L10' polarized Lipschitz).
GAP GUARDS: L3 positivity threaded everywhere; L9 the 2α≥1 (if proven under only 2α>1/2 algebra → ∂ₓ lands in
H^{2α-1}⊄L², fails α<1/2); keep α≥1/2 (divergence) and α>1/4 (logistic/L∞) as DISTINCT hyps.
