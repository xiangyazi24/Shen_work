I’ll re-read the current fa2adee versions of the residual, patched slice file, G5 semigroup file, iterate-time file, and restart/initial-approach files, then give a route choice with exact implementation shape.

Verdict
Pick route (ii), the one-step mild/restart route. It is formally cheaper in this repo.
Route (i) is viable mathematically, but it routes through IntervalPicardIterateTimeC1, whose job is K1/source-coefficient time-C¹ data, not direct sup-norm slice continuity. Its header says the value-field joint continuity needed for that K1 route is still a separate hypothesis hprofile_joint, even if you are discharging it elsewhere. So using route (i) would turn hsliceTC into a second continuity campaign.
Route (ii) uses the PDE infrastructure already built for exactly this: G5 semigroup strong continuity, Chapman–Kolmogorov, the χ₀=0 mild/restart identity, and bounded logistic source estimates. It proves the target directly in the norm the target wants: ∀ y after one δ.

What the residual wants
PicardIterateResidualData.hsliceTC is exactly:
lean∀ s₀ ∈ Set.Icc (0 : ℝ) D.T, ∀ ε > 0, ∃ δ > 0,  ∀ s ∈ Set.Icc (0 : ℝ) D.T, |s - s₀| < δ →    ∀ y,      |patchedSlice u₀ D.u s y        - patchedSlice u₀ D.u s₀ y| < ε
The file marks this as the single genuinely-open analytic residual and says it is consumed by IntervalPicardLimitBddHcontP.patchedSource_continuousOn_Icc. IntervalDomainThm11ChiZeroResid…
patchedSlice is:
leannoncomputable def patchedSlice (u₀ : intervalDomainPoint → ℝ)    (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) : intervalDomainPoint → ℝ :=  if s ≤ 0 then u₀ else u s
with branch lemmas patchedSlice_of_nonpos and patchedSlice_of_pos in IntervalPicardLimitBddHcontP.lean. The same file explains that coefficient continuity has already been reduced to sup-norm time continuity of this patched slice, so the direction is not reversible. IntervalPicardLimitBddHcontP

Audit of route (i): iterate route
IntervalPicardIterateTimeC1.lean does not give the target continuity. It builds K1 data:
leanadot σ k := cosineCoeffs (∂_σ L(w σ)) k
from a restart representation, proves HasDerivAt, time-continuity, and uniform bounds for those source coefficients, and explicitly keeps a value-field joint-continuity hypothesis hprofile_joint because that piece is not packaged there. IntervalPicardIterateTimeC1
The convergence side is closer: IntervalPicardLimitCoeffConv.lean has PicardConvFacts, with hgeom, hlim_ball, and nonnegativity/boundedness data; its header says the coefficient convergence is derived from the geometric Picard machinery and picardIter_pointwise_tail_bound. IntervalPicardLimitCoeffConv But for hsliceTC you need a sup-norm tail lemma, not coefficient convergence:
lean∀ n t, 0 < t → t ≤ T →  ∀ y,    |picardIter p u₀ n t y - picardLimit p u₀ T t y|      ≤ C₀ * K^n / (1 - K)
That is probably easy from PicardConvFacts.hgeom, but it is still another lemma. Then you still need per-iterate sup-norm time continuity. The iterate file’s hprofile_joint means this route does not actually avoid the hard continuity work.
So route (i) is more indirect and risks circularity with the K1/hprofile-joint spine.

Audit of route (ii): one-step mild/restart route
This route is the right one.
The repo has the right ingredients:


G5 strong continuity. IntervalSemigroupUniform.lean is exactly the uniform approximate-identity file: “S(t)f → f on [0,1] for continuous f.” It proves the heat-kernel first-moment bound intervalNeumannFullKernel_abs_moment_le, which is the core estimate behind the final uniform strong-continuity theorem. IntervalSemigroupUniform
I could verify the file and its core theorem family, but the connector truncates before the final theorem name. In implementation, grep in that file after intervalNeumannFullKernel_abs_moment_le; the final theorem is the G5 one referenced in UNDERSTANDING.md.


G5 is recorded as done. UNDERSTANDING.md lists “G5 — Uniform S(t)u₀→u₀ for continuous u₀ — DONE.” UNDERSTANDING


Semigroup composition. UNDERSTANDING.md also says Chapman–Kolmogorov / IntervalSemigroupComposition is landed. UNDERSTANDING


Restart identity for the Picard limit. IntervalPicardLimitRestart.lean proves the χ₀=0 half-step restart cosine identity for the Picard limit, reducing the limit slice through the mild fixed-point equation and spectral pipeline. Its header says this is the limit’s own half-step restart identity. IntervalPicardLimitRestart
The weak version IntervalPicardLimitRestartWeak.lean introduces DuhamelSourceL1ContOn and the horizon-bounded split lemmas needed to avoid derivative-field circularity. It provides weak Duhamel source packages and weak spectral Duhamel lemmas. IntervalPicardLimitRestartWeak


Initial approach is part of the landed cone infrastructure. UNDERSTANDING.md states that gradientMildSolutionData_initialApproach is generic and no longer a per-datum frontier for continuous data. UNDERSTANDING
You still need to inspect whether its statement is sup-norm or pointwise. If it is only pointwise, do not use it directly; prove the sup-norm wrapper from G5 + Duhamel bound.



Implementation plan
Create a small file, e.g.
leanShenWork/Paper2/IntervalPicardLimitSliceTimeContinuity.lean
importing:
leanimport ShenWork.Paper2.IntervalDomainThm11ChiZeroResidualimport ShenWork.PDE.IntervalSemigroupUniformimport ShenWork.PDE.IntervalSemigroupCompositionimport ShenWork.Paper2.IntervalPicardLimitRestartWeakimport ShenWork.Paper2.IntervalMildPicardConeData
The proof should be three lemmas plus a final assembly.

Lemma A: source sup bound on the mild ball
You need a uniform Lmax such that
lean∀ s, 0 < s → s ≤ D.T →  ∀ y, |logisticLifted p (D.u s) y| ≤ Lmax
Use the same bounded/nonnegative logistic estimate already used in IntervalPicardLimitBddHcontP:
leanlogisticSourceFun_abs_le_of_nonneg_bound
It is proved for nonnegative profiles bounded by B on [0,1]. IntervalPicardLimitBddHcontP
Expected shape:
leantheorem logisticLifted_mildSlice_abs_le    (D : GradientMildSolutionData p u₀)    {M : ℝ} (hM : 0 ≤ M)    (hbound : ∀ s, 0 < s → s ≤ D.T → ∀ y, |D.u s y| ≤ M)    (hnn : ∀ s, 0 < s → s ≤ D.T → ∀ y, 0 ≤ D.u s y) :    ∃ Lmax, 0 ≤ Lmax ∧      ∀ s, 0 < s → s ≤ D.T →        ∀ y, |logisticLifted p (D.u s) y| ≤ Lmax
A convenient witness is:
leanLmax := M * (p.a + p.b * M ^ p.α)
or a slightly inflated nonnegative version if Lean arithmetic is easier.

Lemma B: initial sup-norm approach at 0
Target:
leantheorem patchedSlice_timeContinuousAt_zero    (p : CM2Params) (hχ0 : p.χ₀ = 0)    (u₀ : intervalDomainPoint → ℝ)    (D : GradientMildSolutionData p u₀)    (hLmax : ...)    (hG5 : ... strong continuity for u₀ ...)    :    ∀ ε > 0, ∃ δ > 0,      ∀ s ∈ Set.Icc (0 : ℝ) D.T, |s - 0| < δ →        ∀ y,          |patchedSlice u₀ D.u s y - patchedSlice u₀ D.u 0 y| < ε
Proof:
leanpatchedSlice u₀ D.u 0 = u₀
by patchedSlice_of_nonpos.
For s = 0, the difference is zero. For 0 < s, use the χ₀=0 mild identity:


$$D.u(s)=S(s)u₀+\int_0^s S(s-r)L(D.u(r))\,dr.$$


Then:


$$\|D.u(s)-u₀\|_\infty
\le
\|S(s)u₀-u₀\|_\infty
+
sL_{\max}.$$


Choose:
leanε/2  for G5δ₂ := ε / (2 * (Lmax + 1))δ := min δ₁ δ₂
If gradientMildSolutionData_initialApproach already gives this exact sup-norm statement, use it as a wrapper. If it gives only pointwise convergence, ignore it for this residual.

Lemma C: positive-time sup-norm continuity
Target:
leantheorem patchedSlice_timeContinuousAt_pos    (p : CM2Params) (hχ0 : p.χ₀ = 0)    (u₀ : intervalDomainPoint → ℝ)    (D : GradientMildSolutionData p u₀)    (hDu : D.u = picardLimit p u₀ D.T)    {s₀ : ℝ} (hs₀ : 0 < s₀) (hs₀T : s₀ ≤ D.T)    :    ∀ ε > 0, ∃ δ > 0,      ∀ s ∈ Set.Icc (0 : ℝ) D.T, |s - s₀| < δ →        ∀ y,          |patchedSlice u₀ D.u s y - patchedSlice u₀ D.u s₀ y| < ε
First shrink:
leanδ ≤ s₀ / 2
so any admissible s near s₀ is positive, and both patched slices unfold using patchedSlice_of_pos.
Use a fixed base
leanτ := s₀ / 2
not the moving base min s s₀. This avoids needing a uniform G5 modulus for the family D.u s.
For every r near s₀, use the restart identity from base τ:


$$D.u(r)
=
S(r-\tau)D.u(\tau)
+
\int_\tau^r S(r-a)L(D.u(a))\,da.$$


For r = s and r = s₀, subtract:


$$D.u(s)-D.u(s₀)
=
\big(S(s-\tau)-S(s₀-\tau)\big)D.u(\tau)
+
\big(\mathrm{Duh}_{\tau,s}-\mathrm{Duh}_{\tau,s₀}\big).$$


Homogeneous part
Assume s ≥ s₀; the other side is symmetric. By semigroup composition:


$$S(s-\tau)
=
S(s-s₀)S(s₀-\tau).$$


So


$$S(s-\tau)D.u(\tau)-S(s₀-\tau)D.u(\tau)
=
(S(s-s₀)-I)\big(S(s₀-\tau)D.u(\tau)\big).$$


Now apply G5 to the continuous datum
leanf := fun x => intervalFullSemigroupOperator (s₀ - τ)      (intervalDomainLift (D.u τ)) x
or, if the semigroup theorem accepts subtype data directly, to that semigroup slice.
This datum is continuous because:


D.u τ is continuous by HasContinuousSlices for positive τ;


the semigroup regularity gives continuous output for positive time.


The repo’s HasContinuousSlices definition says each positive time slice is continuous. IntervalMildPicard
Duhamel part
Bound by the length of the interval times Lmax:


$$\|\mathrm{Duh}_{\tau,s}-\mathrm{Duh}_{\tau,s₀}\|_\infty
\le
C\,|s-s₀|\,L_{\max}
+
\text{possibly one common-interval semigroup-shift term}.$$


There are two implementation options:


Cheaper but slightly stronger lemma: prove the whole restart map is continuous using the same G5 + bounded-source estimate. This avoids manipulating the common interval.


Direct split: split the Duhamel integrals into common part plus short tail. The short tail is ≤ |s-s₀| Lmax; the common part is again controlled by G5 on the bounded family. This may require more Fubini/integral bookkeeping.


If the available picardLimitRestart_general_of_subtypeCont gives a cosine restart series rather than a semigroup integral restart formula, an alternative is to prove continuity of the restart series in sup norm from the restart derivative field and a uniform λ-weighted bound. But that is more spectral work. Prefer the semigroup/Duhamel restart formula if available.

Final assembly theorem
leantheorem hsliceTC_of_mild_restart    (p : CM2Params) (hχ0 : p.χ₀ = 0)    (u₀ : intervalDomainPoint → ℝ)    (D : GradientMildSolutionData p u₀)    (hDu : D.u = picardLimit p u₀ D.T)    -- source bound / G5 / restart inputs, if not derivable directly from D    :    ∀ s₀ ∈ Set.Icc (0 : ℝ) D.T, ∀ ε > 0, ∃ δ > 0,      ∀ s ∈ Set.Icc (0 : ℝ) D.T, |s - s₀| < δ →        ∀ y,          |patchedSlice u₀ D.u s y            - patchedSlice u₀ D.u s₀ y| < ε := by  intro s₀ hs₀ ε hε  by_cases h0 : s₀ = 0  · subst s₀    exact patchedSlice_timeContinuousAt_zero ...  · have hs₀pos : 0 < s₀ := lt_of_le_of_ne hs₀.1 (Ne.symm h0)    exact patchedSlice_timeContinuousAt_pos ... hs₀pos hs₀.2 ε hε
This is exactly the field to insert into PicardIterateResidualData.

Trap list
1. Patched branch at zero
At exactly s = 0:
leanpatchedSlice u₀ D.u 0 = u₀
not D.u 0. Never rewrite D.u 0 = u₀; prove the branch by patchedSlice_of_nonpos.
For positive s₀, shrink δ ≤ s₀/2 before unfolding the patch, so s > 0.
2. Sup-norm vs pointwise
The target is:
lean∃ δ > 0, ∀ s, ... → ∀ y, ...
A pointwise statement:
lean∀ y, ∃ δ > 0, ...
does not suffice. This is why route (ii) is better: G5 and the Duhamel L∞ bound naturally give one δ for all y.
3. Subtype/lift plumbing
patchedSlice is a function on:
leanintervalDomainPoint → ℝ
but most semigroup estimates are on raw ℝ → ℝ via intervalDomainLift.
Use:
leanintervalDomainLift (D.u s) y = D.u s ⟨y, hy⟩
when hy : y ∈ Set.Icc 0 1.
In the final goal, y is already an intervalDomainPoint, so you can use y.1 and y.2.
4. Fixed s₀, not uniform in s₀
hsliceTC fixes s₀ before choosing δ. You do not need a modulus uniform in s₀. This is why choosing τ = s₀/2 is legitimate.
5. Do not use coefficient continuity backward
IntervalPicardLimitBddHcontP uses hsliceTC to prove patchedSource_continuousOn_Icc, via coefficient Lipschitz and logistic source Lipschitz. IntervalPicardLimitBddHcontP
So coefficient continuity cannot be used to prove hsliceTC without circularity.
6. Restart identity shape
Check whether picardLimitRestart_general_of_subtypeCont gives a semigroup/Duhamel restart formula or only cosine-series agreement. If it is only cosine-series agreement, route (ii) is still right, but the homogeneous/Duhamel difference proof should use the underlying split lemmas in IntervalPicardLimitRestartWeak, especially the horizon-bounded duhamelSpectralCoeff_general_split_on. IntervalPicardLimitRestartWeak

Short answer
Use route (ii).
Route (i) is overkill and reopens hprofile_joint. Route (ii) closes hsliceTC in the target norm using existing PDE infrastructure:
leanpatchedSlice branches+ G5: uniform S(t)f → f+ χ₀=0 mild/restart identity+ Chapman–Kolmogorov+ source L∞ bound from D.hbound/nonneg⇒ sup-norm time continuity on Icc 0 D.T
This is the smallest non-circular proof path for the current repo.