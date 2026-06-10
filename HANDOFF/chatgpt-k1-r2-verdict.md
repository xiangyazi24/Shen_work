Verdict
R2 is the route I would formalize. It is sound, non-circular, and it should require no new analytic estimates beyond the weak restart identity, source-coefficient continuity, and the compact-uniform weighted coefficient envelopes you already have.
The one adversarial correction: do not rely only on the formula with base time σ and h ≥ 0 to prove HasDerivAt, because that gives a right-derivative-shaped proof. For Lean’s two-sided HasDerivAt, prove the scalar coefficient ODE by restarting from an earlier time τ < σ, say τ = σ / 2. Then the restart formula is valid for all t in a genuine neighborhood of σ, because t > τ there. This removes the one-sided issue completely.
The dependency is:


$$\text{weak source continuity + weak restart}
\Rightarrow c_k'=-\lambda_k c_k+A_k
\Rightarrow u_t=\sum_k(-\lambda_k c_k+A_k)\Phi_k
\Rightarrow A_k'=\int f'(u)u_t\cos_k.$$


Here $A_k(\sigma)=\langle f(u(\sigma)),\cos_k\rangle$, $c_k(\sigma)$ is the solution coefficient, and $\Phi_k$ denotes whatever normalized reconstruction mode your project uses. No derivative of $A_k$ is used until the last arrow, so this is not circular.
Mathlib has exactly the kind of plumbing you want: hasDerivAt_tsum_of_isPreconnected / hasDerivAt_tsum for differentiating series under a summable uniform derivative bound on an open preconnected set, continuousOn_tsum for continuity of a uniformly summable series, FTC lemmas such as intervalIntegral.integral_hasDerivAt_right, and the parametric interval-integral lemma intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le. Lean Community+3Lean Community+3Lean Community+3

The concrete R2 implementation plan
Use the following notation, adjusted to your normalization:


$$\lambda_k=(k\pi)^2,\qquad
c(\sigma,k)=\widehat u_k(\sigma),\qquad
A(\sigma,k)=\widehat{f(u(\sigma))}_k.$$


Define


$$d(\sigma,k):=-\lambda_k c(\sigma,k)+A(\sigma,k),$$


and define the reconstructed time derivative


$$v(\sigma,x):=\sum_{j=0}^{\infty} d(\sigma,j)\,\Phi_j(x).$$


Finally define the desired producer by


$$\boxed{
\operatorname{adott}(\sigma,k)
=
\int_0^1 f'(u(\sigma,x))\,v(\sigma,x)\,\cos(k\pi x)\,dx
}$$


with any coefficient-normalization constant included if your innerProduct convention has one.

Lemma 1: weak source coefficients are continuous
Statement shape:
leanlemma sourceCoeff_continuousOn_limit  (k : ℕ) :  ContinuousOn (fun σ => A σ k) (Set.Ioo 0 T)
Hypotheses used:
lean-- schematichu_cont :  ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2)    (Set.Ioo 0 T ×ˢ Set.Icc 0 1)hu_bound :  ∀ σ ∈ Set.Ioo 0 T, ∀ x ∈ Set.Icc (0:ℝ) 1, ‖u σ x‖ ≤ Mhf_cont :  ContinuousOn f relevantRangehcos_bound :  ∀ x ∈ Set.Icc (0:ℝ) 1, ‖Real.cos (k * Real.pi * x)‖ ≤ 1
Proof idea: dominated convergence for


$$\sigma\mapsto \int_0^1 f(u(\sigma,x))\cos(k\pi x)\,dx.$$


The dominating function is constant on [0,1], for example sup_{|y|≤M} |f y|. In Lean, intervalIntegral.continuousAt_of_dominated_interval / intervalIntegral.continuous_of_dominated_interval are the intended tools. Lean Community
You likely already have this from slice continuity plus dominated convergence. This lemma is the only source regularity needed for the next step.

Lemma 2: solution coefficients are time differentiable from weak restart
First prove the scalar coefficient restart formula from picardLimitRestart_general:
leanlemma limitCoeff_restart_from  {τ t : ℝ} (hτ : 0 < τ) (hτt : τ ≤ t) (ht : t < T) (k : ℕ) :  c t k =      Real.exp (-(λ k) * (t - τ)) * c τ k    + ∫ s in τ..t,        Real.exp (-(λ k) * (t - s)) * A s k
This is just applying the k-th coefficient functional to the weak restart identity, using the semigroup coefficient formula.
Then prove:
leanlemma limitCoeff_hasDerivAt  {σ : ℝ} (hσ : σ ∈ Set.Ioo 0 T) (k : ℕ) :  HasDerivAt    (fun t => c t k)    (-(λ k) * c σ k + A σ k)    σ
Proof: choose τ = σ / 2. For all t in a small neighborhood of σ, τ < t < T, so the restart formula gives


$$c_k(t)
=
e^{-\lambda_k(t-\tau)}c_k(\tau)
+
\int_\tau^t e^{-\lambda_k(t-s)}A_k(s)\,ds.$$


Rewrite the integral term as


$$\int_\tau^t e^{-\lambda_k(t-s)}A_k(s)\,ds
=
e^{-\lambda_k t}\int_\tau^t e^{\lambda_k s}A_k(s)\,ds.$$


Now FTC gives


$$\frac{d}{dt}\int_\tau^t e^{\lambda_k s}A_k(s)\,ds
=
e^{\lambda_k t}A_k(t),$$


because A · k is continuous. Differentiating the rewritten expression gives


$$c_k'(\sigma)
=
-\lambda_k c_k(\sigma)+A_k(\sigma).$$


This is the clean two-sided HasDerivAt proof. Use HasDerivAt.congr_of_eventuallyEq to replace c by the restarted expression near σ.
Also record:
leanlemma limitCoeff_derivExpr_continuousOn  (k : ℕ) :  ContinuousOn (fun σ => -(λ k) * c σ k + A σ k) (Set.Ioo 0 T)
This follows from continuity of c · k and A · k.

Lemma 3: reconstruct $u_t$ by differentiating the cosine series
Define:
leannoncomputable def timeDerivSeries (σ x : ℝ) : ℝ :=  ∑' j : ℕ, d σ j * Φ j x
where
leand σ j := -(λ j) * c σ j + A σ j
The key compact-uniform summability hypothesis you need is exactly:
leanlemma derivCoeff_l1_bound_on_compact  {a b : ℝ} (hab : Set.Icc a b ⊆ Set.Ioo 0 T) :  ∃ B : ℕ → ℝ,    Summable B ∧    ∀ σ ∈ Set.Icc a b, ∀ j : ℕ,      ‖d σ j‖ * modeBound j ≤ B j
In practice, take


$$B_j=C_\Phi\bigl(B^{\lambda c}_j+B^A_j\bigr),$$


where


$$\lambda_j |c(\sigma,j)|\le B^{\lambda c}_j,\qquad
|A(\sigma,j)|\le B^A_j$$


uniformly on [a,b], and both envelopes are summable. This is exactly where your already-formalized eigenvalue-weighted summability and source envelope enter.
Then prove:
leanlemma timeDerivSeries_hasDerivAt_eval  {σ x : ℝ}  (hσ : σ ∈ Set.Ioo 0 T)  (hx : x ∈ Set.Icc (0:ℝ) 1) :  HasDerivAt    (fun t => u t x)    (timeDerivSeries σ x)    σ
Proof structure:


Choose an open interval J = Set.Ioo l r with l < σ < r and Set.Icc l r ⊆ Set.Ioo 0 T.


For each j, apply Lemma 2:


$$\frac{d}{dt}\bigl(c_j(t)\Phi_j(x)\bigr)=d_j(t)\Phi_j(x).$$




Use the compact envelope above to bound the derivative terms by a summable sequence uniformly on J.


Apply hasDerivAt_tsum_of_isPreconnected to
leanfun t => ∑' j, c t j * Φ j x


Transfer from the series to u t x using your already-formalized representation equality.


This is the exact place to use Mathlib’s hasDerivAt_tsum_of_isPreconnected: the docs state the theorem for an open preconnected set with a summable uniform derivative bound and summability at one base point. Lean Community
Also prove continuity of the reconstructed derivative:
leanlemma timeDerivSeries_continuousOn :  ContinuousOn    (fun p : ℝ × ℝ => timeDerivSeries p.1 p.2)    (Set.Ioo 0 T ×ˢ Set.Icc (0:ℝ) 1)
On each compact time window, this follows from continuousOn_tsum: every term
leanfun p => d p.1 j * Φ j p.2
is continuous, and the same summable envelope gives uniform convergence. Mathlib’s continuousOn_tsum is designed for exactly this situation. Lean Community

Lemma 4: differentiate the limit source coefficient under the spatial integral
Define:
leannoncomputable def sourceCoeffDerivLimit (σ : ℝ) (k : ℕ) : ℝ :=  ∫ x in (0:ℝ)..1,    fDeriv (u σ x) * timeDerivSeries σ x * Real.cos (k * Real.pi * x)
Then prove:
leanlemma sourceCoeff_hasDerivAt_limit  {σ : ℝ} (hσ : σ ∈ Set.Ioo 0 T) (k : ℕ) :  HasDerivAt    (fun r => A r k)    (sourceCoeffDerivLimit σ k)    σ
Proof:
For fixed spatial x, Lemma 3 gives


$$\frac{d}{d\sigma}u(\sigma,x)=v(\sigma,x).$$


The scalar chain rule gives


$$\frac{d}{d\sigma}
\left[f(u(\sigma,x))\cos(k\pi x)\right]
=
f'(u(\sigma,x))v(\sigma,x)\cos(k\pi x).$$


Then use intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le.
The local dominating bound on a compact window K ⊂ (0,T) is


$$|f'(u(r,x))\,v(r,x)\cos(k\pi x)|
\le
L_K\,V_K,$$


where


$$L_K:=\sup_{(r,x)\in K\times[0,1]} |f'(u(r,x))|,
\qquad
V_K:=\sup_{(r,x)\in K\times[0,1]} |v(r,x)|.$$


V_K is finite by the summable derivative-coefficient envelope. L_K is finite because u is bounded and continuous; for real-power logistic formalization, use local strict positivity on K × [0,1] if your rpow differentiability lemmas require positivity. The parametric interval-integral theorem in Mathlib assumes differentiability in a neighborhood and an integrable bound independent of the parameter, which is exactly this setup. Lean Community
This proves K1(i).

Lemma 5: continuity and compact bounds for adott
Continuity:
leanlemma sourceCoeffDerivLimit_continuousOn  (k : ℕ) :  ContinuousOn    (fun σ => sourceCoeffDerivLimit σ k)    (Set.Ioo 0 T)
Proof: the integrand


$$(\sigma,x)\mapsto f'(u(\sigma,x))v(\sigma,x)\cos(k\pi x)$$


is continuous on compact subwindows of (0,T) × [0,1], and is locally dominated by a constant. Use intervalIntegral.continuousAt_of_dominated_interval, then convert pointwise ContinuousAt to ContinuousOn. The dominated-continuity interval-integral lemmas are in Mathlib.MeasureTheory.Integral.DominatedConvergence. Lean Community
Compact bound:
leanlemma sourceCoeffDerivLimit_bound_on_compact  {a b : ℝ} (hab : Set.Icc a b ⊆ Set.Ioo 0 T) :  ∃ Mdot : ℝ,    ∀ σ ∈ Set.Icc a b, ∀ k : ℕ,      ‖sourceCoeffDerivLimit σ k‖ ≤ Mdot
Take the summable derivative-coefficient envelope on [a,b]:


$$|d(\sigma,j)|\,|\Phi_j(x)|\le B_j,\qquad \sum_jB_j<\infty.$$


Then


$$|v(\sigma,x)|
\le
\sum_j B_j
=:V_{[a,b]}.$$


Let


$$L_{[a,b]}
:=
\sup_{\sigma\in[a,b],\,x\in[0,1]}
|f'(u(\sigma,x))|.$$


Since $|\cos(k\pi x)|\le 1$,


$$|\operatorname{adott}(\sigma,k)|
\le
\int_0^1 L_{[a,b]}V_{[a,b]}\,dx
=
L_{[a,b]}V_{[a,b]}.$$


If your coefficient functional has a normalization constant, multiply the right side by that fixed constant. This gives K1(iii), uniformly in k.
K1(ii) is Lemma 5’s continuity statement.

Why this is not circular
The only restart input is the weak restart identity plus continuity/envelope of the source coefficients. Lemma 2 derives differentiability of the solution coefficients from that weak package. Lemma 3 reconstructs $u_t$ from the already-known weighted coefficient envelopes. Lemma 4 then differentiates the source coefficient for the first time.
So the dependency graph is acyclic:
weak source continuity/envelope        ↓weak restart for u        ↓c_k' = -λ_k c_k + A_k        ↓u_t series reconstruction        ↓A_k' = ∫ f'(u) u_t cos_k        ↓K1 package
The only audit point is this: make sure the compact-uniform eigenvalue-weighted bound


$$\sum_k \sup_{\sigma\in K} \lambda_k |c(\sigma,k)|<\infty$$


was not itself proved using the missing K1 package. You said it comes from heat smoothing/restart representation machinery already formalized independently, so under that premise R2 is clean.

R1 assessment
R1 is mathematically standard, but it is a much worse formal route.
At the sup-norm level, the naive estimate


$$\left\|\Delta\int_0^t e^{(t-s)\Delta}g(s)\,ds\right\|
\le
\int_0^t (t-s)^{-1}\|g(s)\|\,ds$$


does not close. The integration-by-parts repair is the right textbook move. For


$$\delta_n=u_n-u_{n-1},\qquad
g_n=f(u_n)-f(u_{n-1}),$$


restart at some $\theta<a$. For $t\in[a,T]$,


$$\delta'_{n+1}(t)
=
\Delta e^{(t-\theta)\Delta}\delta_{n+1}(\theta)
+
e^{(t-\theta)\Delta}g_n(\theta)
+
\int_\theta^t e^{(t-s)\Delta}g_n'(s)\,ds.$$


Using $|f'|\le L$, $|f''|\le K$ on the ball,


$$\|g_n'(s)\|
\le
L\|\delta_n'(s)\|
+
K\|u_{n-1}'(s)\|\|\delta_n(s)\|.$$


Thus, schematically,


$$D_{n+1}^{[a,T]}
\le
C_{a,\theta}E_{n+1}
+
L E_n
+
\int_\theta^T
\left(
L D_n(s)+K U_{n-1}(s)E_n
\right)\,ds.$$


If you already have a uniform bound $U_{n-1}\le U_\theta$ on $[\theta,T]$ and $E_n\le C r^n$, this becomes a Volterra recurrence


$$D_{n+1}(t)\le B_\theta r^n+L\int_\theta^tD_n(s)\,ds.$$


A weighted/exponential induction gives $D_n\le C_\rho\rho^n$ for any $r<\rho<1$. A cruder discrete estimate gives an $n r^n$-type loss. Constants depend on the distance from zero and blow as $a\downarrow0$.
The catch is formal: a fixed-window statement on [a,T] is not quite self-contained, because the integration-by-parts formula started at θ<a asks for derivative control on [θ,T]. You either need a weighted-in-time derivative norm or a simultaneous family of compact-window estimates. This is all doable, but it is exactly the kind of analytic bookkeeping R2 avoids.

R1b coefficient-level version
Coefficient-level R1 can be made precise, but only if you work in a weighted ℓ¹/Wiener algebra, not per-mode alone.
The induction statement would be something like:


$$\|q\|_{\lambda,K}
:=
\sum_j (1+\lambda_j)\sup_{\sigma\in K}|q_j(\sigma)|.$$


Assume the nonlinear coefficient map


$$c\mapsto \operatorname{Coeff}(f(\sum_j c_j\Phi_j))$$


is locally Lipschitz in this weighted algebra on the compact window K. Then prove:
leanC_n := ‖c_n - c_{n-1}‖_{λ,K} ≤ C ρ^nA_n := ‖A_n - A_{n-1}‖_{λ,K} ≤ C ρ^nD_n := ‖d_n - d_{n-1}‖_{0,K} ≤ C ρ^n
where


$$d_n=-\lambda c_n+A_{n-1}.$$


The parabolic gain gives


$$\lambda_k
\left|
\int e^{-\lambda_k(t-s)}\delta A_{n,k}(s)\,ds
\right|
\le
\sup_s|\delta A_{n,k}(s)|,$$


so


$$\|d_{n+1}-d_n\|_{0,K}
\le
2\|A_n-A_{n-1}\|_{0,K}.$$


For the source derivatives,


$$\operatorname{adot}_n
=
\operatorname{Coeff}\bigl(f'(u_n)v_n\bigr),$$


and the Banach-algebra product estimate gives


$$\|\operatorname{adot}_n-\operatorname{adot}_m\|_1
\le
C\|u_n-u_m\|_{\lambda,1}
+
C\|v_n-v_m\|_1.$$


That works, but it requires the weighted ℓ¹ algebra, product, and composition Lipschitz infrastructure. Since R2 gets the same endpoint from already-available limit envelopes and standard tsum/integral plumbing, R2 is the better formalization route.
