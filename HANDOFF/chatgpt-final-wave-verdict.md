I’ll read the current files at 1a2721e and focus only on the residual interfaces: iterate source C1, limit-side representation cure, Duhamel gradient wiring, and picardLimit’s definition.

For Front B, one important distinction is visible already: IntervalGradDuhamelBound proves the bound for the gradient-Duhamel integral with deriv already inside the s-integral; it still takes hg_int as a prerequisite and does not itself prove the split identity.

Executive verdict
Both fronts are real, but they are different kinds of residuals.
Front A should be fixed by cloning the limit-side representation cure for iterates. The current iterate producer still asks for global ContDiff ℝ 2 (intervalDomainLift …), which is exactly the zero-extension disease. The correct new producer should take a per-slice cosine proxy bc σ plus eigenvalue summability and [0,1] agreement, then feed the proxy into the existing logistic weak-H² / coefficient-decay machinery.
Front B is not yet discharged by the current Atom-D files. The repo has the gradient-Duhamel estimate once the Leibniz identity is provided, but the spatial derivative/time-integral interchange is still a separate lemma to build.
Structural question: picardIter itself is horizon-free, but picardLimit p u₀ T is horizon-indexed. I would not rely on definitional equality after restriction. Either add a theorem proving horizon-independence on overlap by uniqueness of limits, or re-run the cone construction at the smaller gate horizon.

FRONT A — iterate-side representation cure
A1. Current bad interface
picardIterate_source_duhamelSourceTimeC1 currently has this relevant hypothesis block:
lean(hC2 : ∀ σ, ContDiff ℝ 2 (intervalDomainLift (picardIter p u₀ n σ)))(hpos : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,  0 < intervalDomainLift (picardIter p u₀ n σ) x)(hub : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,  intervalDomainLift (picardIter p u₀ n σ) x ≤ M)(hG1 : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,  |deriv (intervalDomainLift (picardIter p u₀ n σ)) x| ≤ G1)(hG2 : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,  |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x| ≤ G2)(hN0 : ∀ σ, deriv (intervalDomainLift (picardIter p u₀ n σ)) 0 = 0)(hN1 : ∀ σ, deriv (intervalDomainLift (picardIter p u₀ n σ)) 1 = 0)
This is in IntervalPicardIterateSourceC1.lean; the header also explicitly says this M3 producer is intended to assemble DuhamelSourceTimeC1 for the source family consumed by picardIterateRestart_cosineIdentity. IntervalPicardIterateSourceC1
The poisoned fields are:


Definitely poisoned: hC2.
Global C² of intervalDomainLift is false for a positive profile at the boundary, because intervalDomainLift is the zero extension.


Also poisoned / should be removed: hN0, hN1.
These are endpoint derivative facts about the zero extension. The cosine proxy has Neumann endpoint derivatives for free, so the iterate producer should not ask for endpoint derivatives of the lift.


Semantically poisoned at endpoints: hG1, hG2 as stated over Icc.
The bounds are meaningful on the interior; at endpoints they refer to deriv / deriv (deriv …) of the zero extension. Retype them to Ioo 0 1, or state them directly for the cosine proxy. The limit-side cure already shows the better pattern: prove the bound on Ioo, then extend to Icc using continuity of the proxy derivative.


Not poisoned: hpos, hub.
These are value statements on [0,1], so they are legitimate. For a cleaner source producer, they can be restricted to 0 ≤ σ if the target only needs the DuhamelSourceTimeC1 envelope on nonnegative time.


The limit-side representation cure already does exactly this replacement: it takes bc, hbsum, and hagree, builds a genuinely global C² cosine series, transfers positivity/sup/derivative bounds to the series, and uses the series’ free Neumann endpoints. IntervalDomainLimitSourceRepres…
A2. Satisfiable iterate-side retype
Add a new producer, do not patch the old one in place first:
leannoncomputable def picardIterate_source_duhamelSourceTimeC1_of_representation    (p : CM2Params)    (u₀ : intervalDomainPoint → ℝ) (n : ℕ)    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)    {M G1 G2 : ℝ}    -- representation proxy    (bc : ℝ → ℕ → ℝ)    (hbsum : ∀ σ,      Summable (fun k => unitIntervalCosineEigenvalue k * |bc σ k|))    (hagree : ∀ σ,      Set.EqOn        (intervalDomainLift (picardIter p u₀ n σ))        (fun x => ∑' k, bc σ k * cosineMode k x)        (Set.Icc (0 : ℝ) 1))    -- value bounds on the lift    (hpos : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,      0 < intervalDomainLift (picardIter p u₀ n σ) x)    (hub : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,      intervalDomainLift (picardIter p u₀ n σ) x ≤ M)    -- preferably interior-only derivative bounds on the lift    (hG1 : ∀ σ, ∀ x ∈ Set.Ioo (0 : ℝ) 1,      |deriv (intervalDomainLift (picardIter p u₀ n σ)) x| ≤ G1)    (hG2 : ∀ σ, ∀ x ∈ Set.Ioo (0 : ℝ) 1,      |deriv (deriv (intervalDomainLift (picardIter p u₀ n σ))) x| ≤ G2)    -- K1 time-C¹ source coefficient data    (adot : ℝ → ℕ → ℝ)    (hderiv : ∀ σ k, HasDerivAt      (fun r => cosineCoeffs        (logisticSourceFun p.a p.b p.α          (intervalDomainLift (picardIter p u₀ n r))) k)      (adot σ k) σ)    (hadotcont : ∀ k, Continuous (fun σ => adot σ k))    {Mdot : ℝ}    (hMdot : ∀ σ, 0 ≤ σ → ∀ k, |adot σ k| ≤ Mdot) :    DuhamelSourceTimeC1      (fun s k => cosineCoeffs        (logisticLifted p (picardIter p u₀ n s)) k)
Internally, copy the limit-side proof pattern:
leanlet cs σ x := ∑' k, bc σ k * cosineMode k xhave hcsC2 : ∀ σ, ContDiff ℝ 2 (cs σ) :=  fun σ => cosineCoeffSeries_contDiff_two (hbsum σ)
Then:
leanhpos_cs, hub_cs       -- by hagreehG1_cs, hG2_cs        -- by EqOn on Ioo + continuity extension to IcchN0_cs, hN1_cs        -- cosineCoeffSeries_deriv_at_zero / _at_one
Finally call the existing logistic source quantitative decay on cs σ, then transport coefficients back by cosineCoeffs_congr_on_Icc.
The existing limit adapter has the exact ingredients: cosineCoeffSeries_contDiff_two, derivative continuity, transfer from Ioo to Icc, and free Neumann endpoint fields. IntervalDomainLimitSourceRepres…
A3. K1: already exists iterate-side
The K1 front is mostly already present in IntervalPicardIterateTimeC1.lean. Its header says it is the “K1 discharge” from the restart representation of the iterate slice; it builds
leanadot σ k := cosineCoeffs (∂_σ L(w σ)) k
with HasDerivAt, time-continuity, and a uniform bound Mdot. It uses:
leanrestartCosineSeries_hasDerivAt_timerestartFieldTimeDerivrestartDerivField_continuousOn_jointlogisticSourceFun_hasDerivAt_timecosineCoeffs_hasDerivAt_of_smooth_param
and it explicitly notes the remaining named hypothesis hprofile_joint for joint continuity of the value field. IntervalPicardIterateTimeC1
So: do not clone the whole K1 chain-rule proof unless necessary. Reuse IntervalPicardIterateTimeC1. The only likely additional lemma is the value-field joint-continuity package for the concrete restart iterate representation, because the file currently treats that as hprofile_joint.
A4. Eigenvalue summability of restart coefficients
Use restartSeries_eigenvalue_summable from IntervalPicardIterateC2Bound.lean. That file’s header describes the exact setting: for restart coefficients
leanrestartDuhamelCoeff a₀ a τ n
with τ > 0, half-step coefficient bound, and DuhamelSourceTimeC1 source package, the restart series has the λ-weighted summability needed for C². IntervalPicardIterateC2Bound
For an actual iterate slice, use the existing restartIterateCoeff definition in the same file, whose source is
leanfun σ k =>  cosineCoeffs (logisticLifted p (picardIter p u₀ n (t / 2 + σ))) k
and whose homogeneous datum is the half-step coefficient family. IntervalPicardIterateC2Bound
One trap: the n = 0 iterate is not a restart-from-previous-source slice in the same way. Treat it separately as the homogeneous heat slice of u₀, or define bc by cases.
A5. Front A trap list
The traps I would explicitly guard against:


Do not use ContDiff ℝ 2 (intervalDomainLift …) anywhere. That reintroduces the old contradiction.


Do not ask for Neumann endpoint derivatives of the lift. Get them from the cosine proxy.


Do not transfer derivative bounds from EqOn Icc directly at endpoints. Use local equality on Ioo plus continuity of the proxy derivative to extend to Icc.


Do not forget shifted-source bookkeeping. picardIterateRestart_cosineIdentity uses the half-step shifted source internally; its header says the σ ↦ t/2+σ shift is handled by the half-step split, so no separate shifted global source hypothesis should be invented. IntervalPicardIterateRestart


Do not try to use the old M3 producer as a black box. The old producer’s shape is exactly the residual disease.



FRONT B — G1 derivative-split identity
B1. Existing repo status
The mild map is exactly
leanS(t)u₀+ (-χ₀) * ∫₀ᵗ ∂ₓ S(t-s) Q(u s) ds+ ∫₀ᵗ S(t-s) L(u s) ds
as defined in IntervalGradientDuhamelMap.lean. IntervalGradientDuhamelMap
For χ₀ = 0, the iterate restart file has
leanintervalGradientDuhamelMap_eq_of_chi0_zero
which rewrites the map to
leanS(t)u₀ + ∫₀ᵗ S(t-s)Lₙ(s) ds
and this is the algebraic starting point for hsplit. IntervalPicardIterateRestart
The repo also has the per-slice full-kernel gradient estimate:
leanintervalFullCoupledDuhamel_grad_integrand_pointwise_bound
giving the pointwise bound
lean|deriv (fun z =>  intervalFullSemigroupOperator (t - s) F z) x|≤ Cgrad * (t - s)^(-1/2) * C_source
for s < t. IntervalFullKernelGradEstimate
But the important point is this: the existing full-kernel Duhamel gradient estimate takes the Leibniz identity as an input, named hLeibniz. It does not prove the derivative/time-integral interchange itself. IntervalFullKernelGradEstimate
So you still need to build the full Duhamel spatial-Leibniz lemma.
B2. Lemma to add
Add something like:
leantheorem intervalFullDuhamel_hasDerivAt_fst    {t : ℝ} (ht : 0 < t)    {F : ℝ → ℝ → ℝ}    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))    {C_source : ℝ} (hC_source_nn : 0 ≤ C_source)    (hF_sup : ∀ s y, |F s y| ≤ C_source)    (x₀ : ℝ) :    HasDerivAt      (fun x => ∫ s in (0 : ℝ)..t,        intervalFullSemigroupOperator (t - s) (F s) x)      (∫ s in (0 : ℝ)..t,        deriv (fun z =>          intervalFullSemigroupOperator (t - s) (F s) z) x₀)      x₀
Then get the derivative equality:
leantheorem intervalFullDuhamel_deriv_eq_integral_deriv ... :  deriv    (fun x => ∫ s in (0 : ℝ)..t,      intervalFullSemigroupOperator (t - s) (F s) x) x₀  =    ∫ s in (0 : ℝ)..t,      deriv (fun z =>        intervalFullSemigroupOperator (t - s) (F s) z) x₀
B3. Correct Mathlib tool and dominating function
Use the same general theorem already used in the repo for differentiating the kernel integral:
leanhasDerivAt_integral_of_dominated_loc_of_deriv_le
IntervalMildPicard.lean uses this theorem for intervalFullSemigroupOperator_hasDerivAt_fst_of_integrable; that confirms the right Mathlib tool family. IntervalMildPicard
For the time integral, do it over a fixed restricted measure, not directly as a variable interval problem:
leanμ := volume.restrict (Set.Ico (0 : ℝ) t)
Use Ico rather than Icc to avoid the singular endpoint s = t. The interval integral over [0,t] is unchanged by deleting the singleton {t}.
The dominating function is:
leanfun s =>  heatGradientLinftyLinftyConstant    * C_source    * (t - s) ^ (-(1 / 2 : ℝ))
on s ∈ Ico 0 t.
Integrability is already packaged in IntervalGradDuhamelBound:
leanintervalIntegrable_sub_rpow_neg_halfintegral_sub_rpow_neg_half
The header of IntervalGradDuhamelBound explicitly says this is the singular factor absorbed by


$$\int_0^t (t-s)^{-1/2}\,ds = 2\sqrt t.$$


IntervalGradDuhamelBound
B4. hsplit
Once the Duhamel Leibniz lemma exists, hsplit should be a small calculus lemma:
leanhave hhom :  HasDerivAt    (fun x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x)    Hhom    x₀ := ...have hduh :  HasDerivAt    (fun x => ∫ s in (0 : ℝ)..t,      intervalFullSemigroupOperator (t - s) Ls x)    Hduh    x₀ := intervalFullDuhamel_hasDerivAt_fst ...have hsum := hhom.add hduhexact hsum.deriv
Do the χ₀ rewrite before differentiating, using intervalGradientDuhamelMap_eq_of_chi0_zero, so that the chemotaxis term never enters the split.
B5. hq_int, hL, hg_int
The needed source-integrability shape is already visible in the existing gradient estimate interface:
leanhF_int : ∀ s, Integrable (F s) (intervalMeasure 1)hF_sup : ∀ s y, |F s y| ≤ C_source
For the logistic source
leanF s = logisticLifted p (picardIter p u₀ n s)
prove:
lean∀ s, Integrable (F s) (intervalMeasure 1)
from continuity of the slice on [0,1] plus finite interval measure. The source bound is
lean|L(u)| ≤ M * (p.a + p.b * M^p.α)
under 0 < u ≤ M, which is the same bound already used in IntervalPicardIterateSourceC1 for the zeroth coefficient package. IntervalPicardIterateSourceC1
For the chemotaxis source
leanQ s = chemFluxLifted p (picardIter p u₀ n s)
the map definition shows its exact formula:
leanlift u * resolverGradReal p u / (1 + R u)^β
IntervalGradientDuhamelMap
But for the χ₀=0 derivative split, avoid using Q analytically if possible. Rewrite the map first so Q is killed algebraically.
hg_int should be produced by the new Duhamel-Leibniz lemma, or separately from the same domination argument. Existing gradDuhamel_sup_bound takes hg_int as an input; it does not create it. IntervalGradDuhamelBound
B6. Front B trap list


Endpoint s = t: never require the per-slice derivative lemma at t-s=0. Work on Ico 0 t or prove the endpoint is null.


Interval orientation: all these lemmas should assume 0 < t. Do not make the interval-integral proof polymorphic over reversed intervals.


uIcc vs Icc: when using intervalIntegral.integral_of_le, normalize to Ioc/Icc early.


Do not differentiate the chemotaxis term in χ₀=0. Rewrite with intervalGradientDuhamelMap_eq_of_chi0_zero first.


Measurability: the dominated differentiation theorem needs measurability/integrability of the integrand family. Use the existing joint measurability infrastructure from IntervalMildPicard if needed. IntervalMildPicard



STRUCTURAL QUESTION — horizon dependence of picardLimit
Verdict
picardIter is horizon-free, but picardLimit p u₀ T is horizon-indexed. So:
leanpicardLimit p u₀ T'
and
leanpicardLimit p u₀ T
should be expected to be propositionally equal on the overlap, not definitionally equal.
The reason is visible from the architecture: picardIter is the raw iteration u_{n+1}=Φ(u₀,u_n) on functions of time, while the limit is obtained from the contraction/Cauchy proof on a chosen horizon. IntervalMildPicard The mild-solution predicate itself is explicitly horizon-indexed on (0,T]. IntervalGradientDuhamelMap
Add this lemma
leantheorem picardLimit_eq_on_restrict    {T' T : ℝ} (hT'T : T' ≤ T) :    ∀ t, 0 < t → t ≤ T' →    ∀ x,      picardLimit p u₀ T' t x = picardLimit p u₀ T t x := by  intro t ht htT' x  -- both sides are limits of the same sequence:  -- n ↦ picardIter p u₀ n t x  -- use picardLimit_tendsto for T' and T, then uniqueness of tendsto
The proof should use the existing convergence theorem for picardLimit; if it is not exposed, expose it first:
leantheorem picardIter_tendsto_picardLimit    {T : ℝ} :    Tendsto (fun n => picardIter p u₀ n t x) atTop      (nhds (picardLimit p u₀ T t x))
Then the overlap lemma is immediate by uniqueness of limIntervalDomainThm11ChiZeroCoreP…