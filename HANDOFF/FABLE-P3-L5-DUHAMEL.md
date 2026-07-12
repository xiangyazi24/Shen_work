# FABLE L5 build plan — nonlinear Duhamel orbit bound (IntervalDomainSpectralSemigroupOrbitBoundRaw)
# The single deep open core of Paper 3 Thm 2.2. Fable 2026-07-12. Verify-don't-transcribe each step.

## Decomposition (CORRECTED): φ=u−u*, ψ=v−v*=R[u]−R[u*]. ∂ₜφ=Aφ+N(φ), N=N_chem+N_log.
## N_chem = ∂ₓQ_chem (chemotactic flux − its linearization), QUADRATIC in φ, and ∫N_chem=0 EXACTLY
##   (Neumann ∂ₓψ|_{0,1}=0) → (I−P₀) + π²-decay available on N_chem.
## N_log = g(u*+φ)+aαφ = ½g''(u*)φ²+O(φ³), g''(u*)=−bα(α+1)u*^{α-1}. ∫N_log = O(‖φ‖²) ≠ 0.
## ⇒ SPLIT φ=φ̄·1+φ̃ (φ̄=P₀φ mean, φ̃=(I−P₀)φ):
##   φ̃(t)=e^{tA}(I−P₀)φ_0+∫₀ᵗe^{(t−s)A}(I−P₀)N ds  [‖S(t)‖≤e^{−π²t} applies]
##   φ̄'=−aα φ̄+P₀N_log  [scalar logistic ODE; mass NOT conserved; mean relaxes at rate aα]
##   DO NOT apply (I−P₀)-decay to all of N (logistic mean is real).

## L²→C¹ smoothing: H^s↪C¹ ⟺ s>3/2 ⟹ X^{1+θ}↪C¹ ⟺ θ>1/2; X^σ↪C⁰ ⟺ σ>1/2. Work θ∈(1/2,1).
##   ‖e^{tA}(I−P₀)w‖_{X^{1+θ}} ≤ C_θ·t^{−(1+θ)/2}·e^{−δt}·‖w‖_{L²}  (p=(1+θ)/2, my scalar x^p e^{−xt}≤(p/et)^p).
##   Rate via interpolation σₖ≤−βπ²−(1−β)λₖ+(1−β)M, M=κ−aα: β→1 ⟹ rate→π² if M≤0 (aα≥κ), else δ<π².

## Duhamel convolution (L6, HARDEST): quadratic source e^{−2δs}, kernel (t−s)^{−p}e^{−δ(t−s)}, split at t/2:
##   [0,t/2]: (t/2)^{−p}e^{−δt}∫e^{−δs} ≤ (t/2)^{−p}e^{−δt}/δ
##   [t/2,t]: e^{−δt}∫₀^∞ r^{−p}e^{−δr}dr = e^{−δt}Γ(1−p)δ^{p−1}
##   ⇒ C¹ norm of Duhamel integral decays at SAME rate e^{−δt} (quadratic source beats kernel). π²-decay REPRODUCED.
##   FLAG: keep e^{−δ(t−s)}=e^{−δt}e^{δs} on [0,t/2] (don't mis-bound to e^{−δt/2}).

## Nonlinearity (CORRECTED): ‖N(φ)‖_{L²} ≤ K(‖φ‖_{C¹})·‖φ‖_{C¹}·‖φ‖_{X^σ} (one factor MUST be C¹:
##   worst term ‖∂ₓφ·∂ₓψ‖_{L²}≤‖∂ₓφ‖_{L∞}‖∂ₓψ‖_{L²}≤‖φ‖_{C¹}·C_R‖φ‖_{X^σ}). +local-Lipschitz version.
##   Elliptic: ‖∂ₓψ‖_{L²}≤C_R‖φ‖_{L²}, ‖ψ−ψ_lin‖_{H²}≤C(‖φ‖_{C⁰})‖φ‖_{C⁰}‖φ‖_{L²}.

## Contraction (L8): weighted two-norm |||φ|||=sup e^{δt}‖φ‖_{X^σ}+sup t^{p₀}e^{δt}‖φ‖_{C¹}, p₀=(1+θ−σ)/2∈(¼,¾).
##   Φ self-maps B_R (R=2C₀ε), contraction q=4C₁K(2C₀ε)C₀ε<1 for ε small. Mathlib ContractingWith.fixedPoint.
##   Continuation: mild sol on [0,∞) (decay in Y); identify w/ given global sol via IsClopen bootstrap on
##   T*=sup{T: ‖φ‖_{C¹}≤2C₀εe^{−δt} on [0,T]} (a-priori improves 2C₀→<2C₀ ⇒ open+closed ⇒ T*=∞).

## ★★ EXACT δ = min( π²−(κ−aα)⁺ , aα ).  The frontier RHS C·‖e^{tA}(I−P₀)‖=C·e^{−π²t} SILENTLY ASSUMES
##   aα≥κ (spatial) AND aα≥π² (mean mode). HIGHEST-PRIORITY: verify against Theorem_2_2's regime hypotheses
##   BEFORE stating L9 as e^{−π²t}. If not guaranteed, frontier as stated is unprovable at full π² rate.

## DAG: L0 infra/blackboxes · L1 N-decomp+meanzero · L2 elliptic quad remainder · L3 nonlinearity(bilinear C¹×X^σ)
##   · L4 semigroup smoothing+rate · L5 linear-in-Y · L6★ Duhamel convolution(split t/2) · L7 mean-mode ODE
##   · L8 ContractingWith fixed point · L9 identify mild=classical + assemble frontier.  HARDEST=L6.
## Gaps: (1) δ vs π² [aα≥κ, aα≥π²] · (2) t↓0 C¹ from X^σ data (short-time reg, t^{p₀} weight) · (3) bilinear not X^σ²
##   · (4) partial mean-zero (logistic mean via scalar ODE) · (5) A self-adjoint (symmetric multiplier R'[u*]).

## ★★★ CONFIRMED FINDING 2026-07-12 (verify-frontier-satisfiability, Fable+repo): FRONTIER OVER-STATED
IntervalDomainSpectralSemigroupOrbitBoundRaw demands c1Distance(u,uStar) ≤ C·‖(I−P₀) heat semigroup‖ = C·e^{−π²t}.
But c1Distance (IntervalDomainSectorial:55) = supNorm(f−g)+supNorm(∂ₓ(f−g)) — FULL C¹, mean included (no P₀).
u's MEAN mode relaxes at rate aα only (logistic ODE φ̄'=−aα φ̄+…; mass NOT conserved). For small u₀ with nonzero
mean deviation m₀: c1Dist ≳ |m₀|e^{−aα t}; frontier needs ≤ C e^{−π²t} ⟹ |m₀| ≤ C e^{−(π²−aα)t}→0 — FALSE for
m₀≠0 when aα<π². Regime is only 0<a,0<b,χ₀<chiCritical — NO hypothesis forces aα≥π² (a=α=1 ⟹ aα=1<π²≈9.87).
⇒ Frontier UNPROVABLE for aα<π². True rate δ=min(π²−(κ−aα)⁺, aα). STATEMENT-LEVEL FIX (Xiang's call):
  (1) restrict Thm 2.2 + frontier to aα≥π² AND aα≥κ (⟹ δ=π², frontier provable as written); OR
  (2) weaken frontier RHS to mean-inclusive C·e^{−δt}, fix downstream intervalDomain_sectorialLocalExponentialRaw_
      of_spectralSemigroupOrbitBound (currently hardcodes Real.pi^2 at line 183) to carry δ.
Once corrected, Fable's 10-lemma DAG (above) builds toward the true target. DO NOT build L5 toward e^{−π²t} until fixed.
