I’ll audit the current repo and handoff designs, focusing on the iterate C² constants, logistic source envelopes, and whether the weighted recursion truly gains a small horizon factor.

I’ve confirmed the crucial asymmetry: G1 has no time-small Duhamel prefactor, while G2 only gains (t/2)^(1/4). I’m now checking whether B_log supplies any compensating smallness.

Verdict
The weighted bootstrap is sound only in the hybrid form, not in the literal “use iterate_abs_deriv_le for R₁ and iterate_abs_deriv2_le for R₂” form.
Your back-of-envelope diagnosis is right, and the actual repo constants make it sharper:
G1 spectral Duhamel term:  C₁ · Benv       -- no τ-small factorG2 spectral Duhamel term:  C₂ · τ^(1/4) · Benv
IntervalDuhamelQuantGain explicitly says the √λ/G1 Duhamel estimate is τ-free, while the λ/G2 estimate has the τ^(1/4) gain. IntervalDuhamelQuantGain The iterate C2 bound confirms the same split: first derivative has + C₁·Benv, second derivative has + C₂·(t/2)^(1/4)·Benv. IntervalPicardIterateC2Bound IntervalPicardIterateC2Bound
So the corrected route is:
G1: package-free kernel route, no recursion.G2: coefficient/spectral route, weighted by t², with the τ^(1/4) Duhamel gain.
This is not just a preference; the repo already encodes this hybrid verdict in IntervalPicardIterateUniform: G1 is the kernel route with profile
leanG1profile p M t =  Cg / sqrt t * M + Cg * (2 * sqrt t) * CL p M
and G2 is the coefficient route with profile
leanG2profile A₂ t = A₂ / t^2.
IntervalPicardIterateUniform IntervalPicardIterateUniform

1. The crux: does the Duhamel side carry smallness?
For G1: no, not in the spectral bound
The repo’s iterate_abs_deriv_le gives


$$G_1^{n+1}(t)
\le
M_1\,\mathrm{sqrtEigExpWeight}(t/2)
+
C_1\,B_{\rm env}(t),$$


with no power of t multiplying Benv. IntervalPicardIterateC2Bound This matches IntervalDuhamelQuantGain, where the √λ Duhamel sum is explicitly called τ-free. IntervalDuhamelQuantGain
If you try to close


$$R_1(n)=\sup_{0<t\le T} t^{1/2}G_1^n(t)$$


using this spectral G1 bound and the quadratic source constant


$$B_{\log}
=
\beta G_1^2 + \Lambda G_2,$$


then the quadratic piece is at least


$$t^{1/2}\cdot B_{\log}
\supset
t^{1/2}\cdot \beta\,R_1^2\,t^{-1}
=
\beta R_1^2 t^{-1/2},$$


which blows up as t → 0. If you insert the hoped-for informal √t factor, you get the undamped O(R₁²) term you computed; but the actual repo theorem does not even give that factor.
So: do not use iterate_abs_deriv_le to close R₁.
For G1: use the kernel route
The kernel G1 route is already the intended one. IntervalPicardIterateUniform describes it as n-free:


$$|\partial_x u_n(t)|
\le
C_g\,t^{-1/2}M
+
C_g\,2\sqrt t\,CL,$$


where


$$CL = M\,(p.a+p.b\,M^{p.\alpha}).$$


IntervalPicardIterateUniform
Thus


$$R_1
:=
\sup_{0<t\le T} t^{1/2}G_1(t)
\le
C_g M + 2C_g\,CL\,T.$$


This is uniform in n and requires no bootstrap recursion. The repo’s g1_kernel_bound theorem is exactly the two-atom assembly: T1 for the homogeneous gradient and Atom D for the Duhamel gradient. IntervalPicardIterateUniform IntervalPicardIterateUniform
For G2: yes, the Duhamel side has the needed smallness
The second derivative bound is:


$$G_2^{n+1}(t)
\le
M_1\,E_2(t/2)
+
C_2\,(t/2)^{1/4}B_{\rm env}(t).$$


IntervalPicardIterateC2Bound
The repo has the homogeneous power bound


$$E_2(\tau)=\mathrm{eigExpWeight}(\tau)
\le
\frac{4}{e\pi^2}\,\tau^{-2}.$$


IntervalWeightPowerBound IntervalWeightPowerBound
So the correct formal weight is:


$$R_2(n):=\sup_{0<t\le T} t^2G_2^n(t).$$


With $s\ge t/2$,


$$G_1(s)\le R_1s^{-1/2}\le \sqrt{2}R_1t^{-1/2},$$


and


$$G_2(s)\le R_2s^{-2}\le 4R_2t^{-2}.$$


Write


$$\beta:=p.b\,p.\alpha(1+p.\alpha)M^{p.\alpha-1},
\qquad
\Lambda:=p.a+p.b(1+p.\alpha)M^{p.\alpha}.$$


The repo’s logistic source constant is


$$B_{\log}
=
\beta G_1^2+\Lambda G_2.$$


IntervalLogisticSourceQuantBound IntervalLogisticSourceQuantBound
The actual iterate envelope constant is


$$B_{\rm env}
=
\max(2B_{\log},\,CL),$$


where the max also handles the zeroth coefficient. IntervalPicardIterateSourceC1 IntervalPicardIterateSourceC1
Thus, using max X Y ≤ X + Y,


$$B_{\rm env}(t)
\le
CL
+
4\beta R_1^2t^{-1}
+
8\Lambda R_2t^{-2}.$$


Multiplying the G2 step by $t^2$,


$$t^2G_2^{n+1}(t)
\le
t^2M_1E_2(t/2)
+
C_2t^2(t/2)^{1/4}B_{\rm env}(t).$$


Using $M_1\le 2M$ and $E_2(t/2)\le \frac{4}{e\pi^2}(t/2)^{-2}$,


$$t^2M_1E_2(t/2)
\le
\frac{32M}{e\pi^2}.$$


For the Duhamel part,


$$t^2(t/2)^{1/4}B_{\rm env}(t)
\le
2^{-1/4}
\left(
CL\,T^{9/4}
+
4\beta R_1^2T^{5/4}
+
8\Lambda R_2T^{1/4}
\right).$$


Therefore the closure inequality is:


$$R_2(n+1)
\le
A_0(T)
+
\eta(T)R_2(n),$$


where


$$A_0(T)
=
\frac{32M}{e\pi^2}
+
C_2\,2^{-1/4}
\left(
CL\,T^{9/4}
+
4\beta R_1^2T^{5/4}
\right),$$


and


$$\eta(T)
=
8C_2\,2^{-1/4}\Lambda T^{1/4}.$$


So choose the Picard/cone horizon so that


$$\eta(T)<1,$$


and then take


$$A_2
\ge
\frac{A_0(T)}{1-\eta(T)}.$$


Equivalently, use the repo’s packaged GateCondition, which states exactly that the homogeneous-plus-Duhamel budget is absorbed by A₂ / t². IntervalPicardIterateUniform The theorem g2_step_closes is already the formal arithmetic that turns the M2-shaped estimate into the A₂/t² profile under that gate. IntervalPicardIterateUniform
So the answer to the crux is:

The literal spectral G1 recursion does not close. The hybrid route does close on the small Picard/cone horizon: G1 by kernel, G2 by $t^2$-weighted spectral recursion with the τ^(1/4) Duhamel gain.


2. Window-shift bookkeeping
Using full weighted norms over (0,T] eliminates the window regression.
For the n+1 iterate at time t, the restart source is the previous iterate evaluated at absolute times
leant/2 + σ
inside the shifted source family used by restartIterateCoeff. IntervalPicardIterateC2Bound
The interval relevant to the Duhamel half-step lies in [t/2,t], and any global/clamped package may over-read up to a window inside (0,T]. Since the weighted profiles are global on (0,T],


$$G_1^n(s)\le G1profile(s),\qquad
G_2^n(s)\le A_2/s^2$$


for every s ∈ (0,T], so evaluating on [t/2,T] or [t/2,t] is harmless. There is no iterative shrinkage of windows.
This is exactly how IntervalPicardIterateUniform sets up the carrier: hG1 and hG2 are stated for every t ∈ (0,T], uniformly at each iterate level. IntervalPicardIterateUniform

3. Base case
The base is n = 0, the pure homogeneous heat slice. For G1, the kernel bound is enough. For G2, the repo survey is right: do not look for a second-kernel bound; use the spectral route.
The handoff notes already say no second derivative kernel bound exists in the repo and that C² currently flows through coefficient/source-decay machinery. r2-weighted-bootstrap-design
For the base G2 proof, use:


cosineCoeffs_semigroup to identify the heat-propagated coefficients:


$$\widehat{S(t)u_0}_n=e^{-t\lambda_n}\widehat{u_0}_n.$$


The theorem is in IntervalSemigroupComposition. IntervalSemigroupComposition


unitIntervalCosineEigenvalue_mul_exp_summable for


$$\sum_n \lambda_n e^{-t\lambda_n}<\infty.$$


IntervalMildRegularityBootstrap


cosineCoeffSeries_contDiff_two, or more directly the semigroup heat-value C² theorem used in the restart bridge:
leanunitIntervalCosineHeatValue_contDiff_two
which is invoked in restartDuhamelFormula_closedC2_of_timeC1_source. IntervalMildRegularityBootstrap IntervalMildRegularityBootstrap


For the weighted base bound, use
leanIntervalWeightPowerBound.eigExpWeight_le
to get


$$t^2\cdot M_0\,E_2(t)\le M_0\frac{4}{e\pi^2}.$$


IntervalWeightPowerBound


The current UniformWiring carrier phrases hG2base as a carried wiring field: the n=0 slice is the homogeneous heat value, and the GATE absorbs it into A₂/t². IntervalPicardIterateUniform That is fine structurally, but the direct proof should be the four-lemma spectral route above.
restartDuhamelCoeffSeries_contDiff_two is not the first-choice base lemma; it is the homogeneous-plus-Duhamel restart-series C² theorem. It can be used with a zero source if convenient, but the cleaner base route is cosineCoeffs_semigroup + heat-value C² + eigExpWeight_le.

4. One-step “slicker” alternative
I would not switch to the one-step limit route.
Your obstruction analysis is right: with only a C¹ spatial source giving roughly


$$|\hat f_k|\lesssim 1/k,$$


the Duhamel tail gives


$$\lambda_k\int e^{-(\sigma-s)\lambda_k}\hat f_k(s)\,ds
\lesssim
1/k,$$


and


$$\sum_k 1/k$$


diverges. A fixed positive time gap only fixes the head. The last short tail still has no exponential gap and still needs better-than-$1/k$ spatial coefficient decay.
The handoff survey’s verdict is exactly this: the C¹-only bootstrap gives 1/k source decay and misses summability by one power. r2-weighted-bootstrap-design
Could Hölder regularity of the spatial derivative save it? Mathematically, yes: a C^{1,θ} source should give coefficient decay better than 1/k, enough for summability. But formally this is not slicker in this repo. It would require new infrastructure:
spatial Hölder seminorms on [0,1]→ parabolic C^{1,θ} estimates for the mild solution→ logistic composition in C^{1,θ}→ cosine/sine coefficient decay from Hölder derivative→ Duhamel tail summability
None of that is part of the existing coefficient-decay spine. The repo already has the explicit B_log/quadratic-decay machinery from C² bounds, and the hybrid weighted C² bootstrap is aligned with the existing M2/M3/M-gate files. IntervalLogisticSourceQuantBound
So the one-step route is mathematically plausible but formally longer and riskier. The hybrid weighted bootstrap is the executable route.

Engineer-executable plan
File to add or complete
Use:
ShenWork/Paper2/IntervalPicardWeightedC2Bootstrap.lean
or, if keeping the current split, extend:
IntervalPicardIterateUniform.leanIntervalPicardIterateSourceC1.leanIntervalDomainThm11ChiZeroCoreProvider.lean
The proof should be organized as follows.
Lemma A: kernel G1 profile, n-uniform
Already present as the intended carrier field and proved core theorem:
leanIntervalPicardIterateUniform.G1profileIntervalPicardIterateUniform.g1_kernel_bound
G1profile is:
leanheatGradientLinftyLinftyConstant / Real.sqrt t * M  + heatGradientLinftyLinftyConstant * (2 * Real.sqrt t) * CL p M
IntervalPicardIterateUniform
Use this to define the scalar window constant
leanG1win a' := G1profile p M a'
or a monotone upper bound on [a',T].
Lemma B: homogeneous G2 weighted base
Prove:
leantheorem picardIter_zero_G2profile  ... :  ∀ t, 0 < t → t ≤ T → ∀ x,    |deriv (deriv (intervalDomainLift (picardIter p u₀ 0 t))) x|      ≤ A₂ / t^2
Inputs:
leancosineCoeffs_semigroupunitIntervalCosineEigenvalue_mul_exp_summableeigExpWeight_lecosineCoeffSeries_contDiff_two
Take A₂ ≥ M₀ * 4/(e*pi^2) or the repo’s 2M-based base budget if using M as the universal coefficient bound.
Lemma C: source envelope from profiles
Use the existing constant:
leaniterateSourceEnvelopeConst p.a p.b p.α M G1 G2
defined as:
leanmax (2 * B_log p.a p.b p.α M G1 G2)    (M * (p.a + p.b * M ^ p.α))
IntervalPicardIterateSourceC1
For the half-step source of level n, use:
leanG1 := G1profile p M (t/2)G2 := G2profile A₂ (t/2)
This is exactly Benv p M A₂ t in IntervalPicardIterateUniform. IntervalPicardIterateUniform
Lemma D: G2 step closure
Use the existing theorem:
leanIntervalPicardIterateUniform.g2_step_closes
It consumes a bound of the shape
leanval ≤ M₁ * eigExpWeight (t/2)  + duhamelGainConst * (t/2)^(1/4) * Benv p M A₂ t
and the GateCondition, then concludes
leanval ≤ G2profile A₂ t
IntervalPicardIterateUniform
The M2 input is exactly iterate_abs_deriv2_le. IntervalPicardIterateC2Bound
Lemma E: full uniform induction
Use or mirror:
leanPicardIterateUniformDatapicardIterateUniformData_zeropicardIterateUniformData_succpicardIterateUniformData_all
These already express the intended induction: G1 is n-free, G2 closes through g2_step_closes. IntervalPicardIterateUniform
Lemma F: window source envelope for all iterates
For every a' with 0 < a' and a' ≤ T, define:
leanG1a := G1profile p M a'G2a := A₂ / a'^2Cwin := windowSourceConst p M G1a G2a
where windowSourceConst is the same max(2*B_log, zeroth) constant. The current default branch already has the standalone form:
leanwindowSourceConstslice_source_coeff_decayslice_source_coeff_zero
with the intended coefficient bound
lean|cosineCoeffs ... k| ≤ windowSourceConst / ((k:ℝ)*π)^2
for k ≥ 1. IntervalPicardWeightedC2Bootstr…
If that file is not present at de9c7d6, add the same declarations. The proof is just the additive-adapter spine:
leancosineCoeffSeries_contDiff_twologisticSourceFun_cosineCoeff_quadratic_decay_explicitcosineCoeffs_congr_on_IcccosineCoeffs_zero_abs_le_of_boundlogisticSourceFun_abs_le_of_bound
Lemma G: pass to the limit
Use the already-threaded hDu design: consumers need D.u = picardLimit p u₀ D.T, and the handoff says the convergence theorem already exists:
leanIntervalPicardLimitCoeffConv.picardIter_logisticCoeff_tendsto_limit
hdu-threading-design
Then pass the uniform iterate envelope to the limit with le_of_tendsto.
This closes R-src0F-2.

Trap list


Do not close G1 with iterate_abs_deriv_le. Its Duhamel term is τ-free; the weighted recursion either blows up or is undamped. Use the kernel G1 profile.


Use R₂ = sup t²G₂(t), not sup tG₂(t). The repo’s available homogeneous bound is eigExpWeight τ ≤ C/τ², so the executable profile is A₂/t². IntervalWeightPowerBound


Keep Benv = max(2B_log, CL) straight. The positive-mode decay numerator is 2B_log; the zeroth mode is controlled by CL. IntervalPicardIterateSourceC1


Do not rely on a non-existent second-kernel bound. The base and G2 line are spectral/coefficient-level.


Do not introduce shrinking windows. The full (0,T] profiles control every shifted half-step window.


Do not pursue the Hölder shortcut unless you want a new campaign. It would require new spatial Hölder and Fourier-decay infrastructure and still has to solve the endpoint/Neumann bookkeeping. The existing C² coefficient-decay route is much closer to completion.