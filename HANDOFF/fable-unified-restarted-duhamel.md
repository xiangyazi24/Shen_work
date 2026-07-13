# Fable: UNIFIED restarted nonlinear Duhamel framework (master key for P2 Prop_2_5 + P3 orbit bound)

## VERDICT (adversarial): shared SUBSTRATE, TWO EXIT DOORS (not one fixed-point lemma)
P2 & P3 share a restarted mild-smoothing convolution calculus (integrable singular kernel θ<1, Bochner-Duhamel
convolution, restart converting local→global). They do NOT share a single fixed-point lemma:
- P2 (AFFINE exit): once uniform finite-L^P bound in hand AND P>γ, the divergence flux → CONSTANT forcing → affine
  Duhamel estimate, NO smallness, NO fixed point.
- P3 (SUPERLINEAR exit): genuine quadratic Nemytskii, NEEDS data smallness (Banach FP).
Divergence-form vs Nemytskii differ only in θ value + closure mode, NOT the substrate. One substrate, two closures.
A single fixed-point lemma for both would be WRONG (P2 needs no smallness); "they share nothing" also wrong.

## SHARED CORE (L1-L4, PROVE)
Setup: Y (rough, where N lands) ↪ Z (strong). Semigroup S(τ): ‖S(τ)‖_{Y→Z}≤k(τ):=C(1+τ^{-θ})e^{-ντ}, 0<θ<1, ν≥0;
‖S(τ)‖_{Z→Z}≤Me^{-ντ}. Mild: w(t)=S(t)w₀+∫₀^t S(t−s)f(s)ds, ‖f(s)‖_Y≤Φ(‖w(s)‖_Z).
L1 KernelCalculus: θ<1 ⇒ K₀(T):=∫₀^T k(σ)dσ<∞. ν=0 ⇒ K₀(T)≤C(T+T^{1-θ}/(1-θ)) GROWS in T (needs restart).
  ν>0 ⇒ K₀(∞)≤C(1/ν+Γ(1-θ)ν^{θ-1})=:C_ν<∞ UNIFORM FOR FREE (P3 all-time).
L2 WeightedConvolution: ∫₀^t k(t−s)e^{-ν(1+ε)s}ds ≤ K(θ,ν,ε)e^{-νt} (L¹ kernel rate ν * input rate ν(1+ε) → rate ν).
L3 RestartedMildClosure ★HARDEST:
  (3a) AFFINE: Φ≡Λ₀ const ⇒ sup_{[0,T]}‖w‖_Z ≤ M‖w₀‖_Z+Λ₀K₀(T). NO smallness. [P2]
  (3b) SUPERLINEAR: Φ(r)=Λr^{1+ε}, ‖w₀‖_Z≤ρ:=(1/2M)(1/(2ΛC_*))^{1/ε} (C_*=K₀(T)[ν=0] or C_ν[ν>0]) ⇒ unique mild
       sol, sup‖w‖_Z≤2M‖w₀‖_Z; ν>0 ⇒ ∀t≥0 ‖w(t)‖_Z≤2M‖w₀‖_Z e^{-νt}. [P3]
  Proof(3b): ball R=2M‖w₀‖_Z, map-in M‖w₀‖+ΛC_*R^{1+ε}≤R + contraction 2ΛC_*R^ε≤1 both ⇔ ΛC_*R^ε≤1/2 ⇔‖w₀‖≤ρ.
L4 RestartGlue: window-bound B(K)+uniform data≤K ⇒ sup_{t≥1}≤B(K).
θ<1 = integrability of Duhamel singularity (θ≥1 ⇒ ∫(w−s)^{-θ}ds diverges — HIDDEN DIVERGENCE #1). restart = device
making ν=0 finite (cap T=1, re-init). ν>0 = no restart needed (decay uniformizes).

## P2 LAYER (Prop_2_5, thin): finite-L^P ⟹ uniform L∞
θ = 1/2+1/(2P); θ<1 ⇔ P>1. Neumann heat: ‖e^{τΔ_N}∂ₓg‖_∞≤C(1+τ^{-1/2-1/(2P)})e^{-λ₁τ}‖g‖_{L^P}, λ₁=π².
γ-CEILING: put elliptic factor in L∞: ‖∂ₓv‖_∞≤C‖u‖_{L^{γs}}^γ, s=P/γ. s>1 ⇔ P>γ (=paper P>max{1,γ}), γs=P ⇒
  ‖F‖_{L^P}=‖u(1+v)^{-β}∂ₓv‖_{L^P}≤‖u‖_{L^P}‖∂ₓv‖_∞≤CK_P^{1+γ} = CONSTANT ⇒ P2 is AFFINE exit (3a), no smallness.
  If γ≥P: elliptic factor needs L∞(u) → CIRCULAR, no uniform bound. EXACT γ-CEILING: γ<P. For γ≥1 MUST use L∞-elliptic
  route (naive L^P-elliptic → flux ~‖u‖_∞^γ superlinear → restart FAILS).
RESTART (t≥1 from t−1): data term ‖e^{Δ·1}u(t−1)‖_∞≤C′K_P (fixed τ=1, no accumulation); flux ≤Cχ₀K_P^{1+γ}(1+1/(1-θ));
  LOGISTIC CAP g(u)=au−bu^{1+α}≤g_max=C(a,b,α)<∞ (needs α>0!), heat preserves ⇒ ∫_{t−1}^t e^{τΔ}g≤g_max·1.
  ⇒ sup_{t≥1}‖u‖_∞≤C′K_P+Cχ₀K_P^{1+γ}(1+1/(1-θ))+g_max=C(K_P) indep of t. = hcriticalGlobalBound.
  RESTART ESSENTIAL: logistic ν=0, Duhamel-from-0 ∫₀^t e^{τΔ}g_max=g_max·t→∞; restart caps at g_max·1. α=0 ⇒ g_max=∞ fails.

## P3 LAYER (orbit bound, thin): LinearlyStable ⟹ nonlinear stability
Diagonal e^{-d_n τ}, d_n=aα+λ_n−κλ_n/(λ_n+μ)≥c_*(1+λ_n) (κ<χ*). X=L², X^α=D((I−L)^α)≈H^{2α}.
‖e^{Lt}‖_{X→X^α}≤Ct^{-α}e^{-δt} (θ=α,ν=δ). Nemytskii ‖N(w)‖_X≤C‖w‖_{X^α}² needs X^α↪C¹ ⇔ 2α>3/2 ⇔ α>3/4. Window
(3/4,1) NONEMPTY ONLY IN 1D. Zero mode σ_0=−aα<0 (logistic stabilizes) — NO special treatment.
Stage A (X^α-small): core(3b) ν=δ,ε=1 ⇒ ∀t≥0 ‖w‖_{X^α}≤2M‖w₀‖_{X^α}e^{-δt} (Henry).
Stage B (L∞-small): L∞↪L², ‖e^{Lt}w₀‖_{X^α}≤Ct^{-α}e^{-δt}‖w₀‖_{L∞}; local Duhamel (0,T₀] closes (α<1); at T₀
  ‖w(T₀)‖_{X^α}≤CT₀^{-α}e^{-δT₀}‖w₀‖_∞≤ρ ⇒ restart Stage A ⇒ ∀t≥T₀ decay. Same restart principle.

## LEAN DAG
SHARED (prove): L1 KernelCalculus[calc], L2 WeightedConvolution[calc], L3 RestartedMildClosure ★HARDEST
  [Banach FP + Bochner Duhamel singular kernel + L1,L2], L4 RestartGlue.
P2 (thin): L5 HeatDivSmoothing θ=½+1/2P[assume kernel], L6 EllipticGradL∞[assume elliptic], L7 FluxIsConstant P>γ
  ←γ-ceiling, L8 LogisticCap α>0, L9 P2=L3(3a)+L4+L5+L7+L8.
P3 (thin): L10 SpectrumGap, L11 DiagSmoothing θ=α,ν=δ[L10], L12 Nemytskii α>3/4[assume Sobolev], L13 StageA=L3(3b)+L11+L12,
  L14 StageB=local L∞→X^α bridge ∘ L13.
HARDEST = L3 (Bochner Duhamel singular convolution + Banach FP + weighted bootstrap; Mathlib has pieces, not glued).
GUARDS: θ≥1(P=1/α≥1) non-integrable; γ-ceiling P>γ (else circular; γ≥1 must L∞-elliptic); restart needs α>0
  (g_max<∞); X^α↪C¹ needs α∈(3/4,1) nonempty only 1D.
ASSUME: heat L^p→L^q Gaussian(L5), 1D elliptic W^{2,s}+Sobolev H^{2α}↪C¹(L6,L12), analytic-semigroup fractional
  power(L11), Banach FP+Bochner(Mathlib). PROVE: L1-L4, L7(P>γ), L8(α>0), L10, assembly L9/L13/L14.
