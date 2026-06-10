/-
  ShenWork/Paper2/IntervalPicardLimitSliceTimeContinuity.lean

  **The `hsliceTC` analytic residual — sup-norm time continuity of the patched
  Picard-limit slice on `[0,T]`** (the χ₀ = 0 route, one-step mild/restart form).

  `hsliceTC` is the single genuinely-open analytic field of
  `Thm11ChiZeroResidual.PicardIterateResidualData`
  (`IntervalDomainThm11ChiZeroResidual.lean:85`):

      ∀ s₀ ∈ [0,T], ∀ ε > 0, ∃ δ > 0, ∀ s ∈ [0,T], |s - s₀| < δ →
        ∀ y, |patchedSlice u₀ D.u s y - patchedSlice u₀ D.u s₀ y| < ε.

  We prove it by the externally-audited **route (ii)** (one-step mild/restart),
  which closes the target in exactly its norm (one δ uniform over the whole
  spatial domain), using the PDE infrastructure already built:

  * **G5 strong continuity** `intervalFullSemigroup_tendstoUniformlyOn`
    (`IntervalSemigroupUniform`): `S(t)f → f` uniformly on `[0,1]` as `t → 0⁺`,
    for continuous `f`.
  * the **χ₀ = 0 mild identity** `D.hmild` (with the chemotaxis term `(-χ₀)·… = 0`),
  * the **semigroup L∞ contraction** `intervalFullSemigroupOperator_Linfty_bound`,
  * the **bounded logistic source** estimate `intervalLogisticSource_lift_abs_bound`.

  Structure (per the verdict):

  * **Lemma A** `logisticLifted_mildSlice_abs_le` — the uniform source sup bound
    `Lmax := M·(a + b·M^α)` on the mild ball, from `D.hbound`.  PROVED.
  * **Lemma B** `patchedSlice_timeContinuousAt_zero` (`s₀ = 0`) — the initial
    sup-norm approach.  PROVED as a thin wrapper around the landed generic
    `gradientMildSolutionData_initialApproach` (which IS the sup-over-`y`, one-δ
    G5 + Duhamel statement) + `D.hmild` + the `patchedSlice` branch lemmas.
  * **Lemma C** `patchedSlice_timeContinuousAt_pos` (`s₀ > 0`) — the interior
    sup-norm continuity, via the FIXED-base restart at `τ := s₀/2`.  Its analytic
    core is the **fixed-base semigroup-integral restart identity** (named sorry
    `mildSlice_restart_bound` below, with route); the homogeneous `(S(s−s₀)−I)`
    piece is then G5 at the closing gap and the Duhamel tail is `≤ |s−s₀|·Lmax`.
  * **Assembly** `hsliceTC_of_mild_restart` — `by_cases s₀ = 0`; exact B / C.
    PROVED (modulo the single Lemma-C named sorry).

  No `axiom`, no `admit`, no `native_decide`.  The one named `sorry`
  (`mildSlice_restart_bound`) is a TRUE statement about the canonical Picard
  limit with the route recorded in its docstring.
-/
import ShenWork.Paper2.IntervalDomainThm11ChiZeroResidual
import ShenWork.Paper2.IntervalMildPicardThreshold
import ShenWork.PDE.IntervalSemigroupUniform
import ShenWork.PDE.IntervalSemigroupComposition
import ShenWork.PDE.IntervalFullKernelSupBound

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalGradientDuhamelMap
  (logisticLifted intervalGradientDuhamelMap IntervalMildSolution)
open ShenWork.IntervalMildPicard (GradientMildSolutionData picardLimit)
open ShenWork.IntervalPicardLimitBddHcontP (patchedSlice patchedSlice_of_nonpos patchedSlice_of_pos)

noncomputable section

namespace ShenWork.IntervalPicardLimitSliceTimeContinuity

variable {p : CM2Params}

/-! ## Lemma A — uniform source sup bound on the mild ball. -/

/-- **Lemma A.**  With `Lmax := M·(a + b·M^α)`, the lifted logistic source of every
positive-time mild slice is uniformly bounded by `Lmax` on **all** of `ℝ` (the lift
is `0` outside `[0,1]`, where `Lmax ≥ 0`).  Direct from `D.hbound` and the
nonnegative logistic-source estimate `intervalLogisticSource_lift_abs_bound`. -/
theorem logisticLifted_mildSlice_abs_le
    {u₀ : intervalDomainPoint → ℝ} (D : GradientMildSolutionData p u₀) :
    ∃ Lmax : ℝ, 0 ≤ Lmax ∧
      ∀ s, 0 < s → s ≤ D.T → ∀ y : ℝ, |logisticLifted p (D.u s) y| ≤ Lmax := by
  refine ⟨D.M * (p.a + p.b * D.M ^ p.α), ?_, ?_⟩
  · have hb : (0 : ℝ) ≤ p.b * D.M ^ p.α := mul_nonneg p.hb (Real.rpow_nonneg D.hM.le _)
    exact mul_nonneg D.hM.le (by linarith [p.ha])
  · intro s hs hsT y
    -- `logisticLifted p w = intervalDomainLift (intervalLogisticSource p w)`.
    exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
      p D.hM (fun z => D.hbound s hs hsT z) y

/-! ## Lemma B — initial sup-norm approach at `s₀ = 0`.

`patchedSlice u₀ D.u 0 = u₀` by `patchedSlice_of_nonpos`; for `0 < s` the patched
slice is `D.u s`, and `D.u s = Φ(u₀, D.u) s` by `D.hmild` (χ₀-agnostic).  The
landed generic `gradientMildSolutionData_initialApproach` is exactly the
sup-over-`y`, one-δ statement `|Φ(u₀, D.u) s x − u₀ x| < ε`. -/

/-- **Lemma B (`s₀ = 0`).**  The patched slice is sup-norm time-continuous at `0`. -/
theorem patchedSlice_timeContinuousAt_zero
    {u₀ : intervalDomainPoint → ℝ} (hu₀cont : Continuous u₀)
    (D : GradientMildSolutionData p u₀) :
    ∀ ε > 0, ∃ δ > 0,
      ∀ s ∈ Set.Icc (0 : ℝ) D.T, |s - 0| < δ →
        ∀ y, |patchedSlice u₀ D.u s y - patchedSlice u₀ D.u 0 y| < ε := by
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ :=
    ShenWork.IntervalMildPicardThreshold.gradientMildSolutionData_initialApproach
      p hu₀cont D ε hε
  refine ⟨δ, hδpos, ?_⟩
  intro s hs hsδ y
  -- `patchedSlice _ _ 0 = u₀`.
  rw [patchedSlice_of_nonpos u₀ D.u (le_refl 0)]
  rcases eq_or_lt_of_le hs.1 with hs0 | hs0
  · -- `s = 0`: both slices are `u₀`, difference `0`.
    rw [← hs0, patchedSlice_of_nonpos u₀ D.u (le_refl 0), sub_self, abs_zero]; exact hε
  · -- `0 < s`: `patchedSlice _ _ s = D.u s`, and `D.u s = Φ(u₀, D.u) s` by `hmild`.
    rw [patchedSlice_of_pos u₀ D.u hs0]
    have hmild := D.hmild s hs0 hs.2 y
    rw [hmild]
    have hsltδ : s < δ := by
      have : |s| < δ := by simpa using hsδ
      rwa [abs_of_pos hs0] at this
    exact hδ s hs0 hsltδ y

/-! ## Lemma C — interior sup-norm continuity at `s₀ > 0` (fixed-base restart).

Shrink `δ ≤ s₀/2` so any admissible `s` is `> s₀/2 > 0`; both patched slices then
unfold to `D.u s`, `D.u s₀` via `patchedSlice_of_pos`.  Take the FIXED base
`τ := s₀/2` (NOT the moving base `min s s₀` — that would need a uniform G5 modulus
over the datum family).  At base `τ`, the χ₀ = 0 mild identity re-based gives, for
`r > τ`,

    D.u r = S(r − τ)(D.u τ) + ∫_τ^r S(r − a) L(D.u a) da.

Subtracting at `r = s` and `r = s₀` and using Chapman–Kolmogorov
`S(s − τ) = S(s − s₀) S(s₀ − τ)` (`intervalFullSemigroupOperator_comp`):

    D.u s − D.u s₀
      = (S(s − s₀) − I)(S(s₀ − τ)(D.u τ))           -- G5 at gap |s − s₀|
        + (Duh_{τ,s} − Duh_{τ,s₀}).                  -- ≤ |s − s₀|·Lmax

The single analytic core of this lemma — the fixed-base restart identity together
with its homogeneous/Duhamel split bound — is isolated below as
`mildSlice_restart_bound` (named sorry + route).  Everything that consumes it (the
ε/2 split, the G5 modulus, and the Duhamel tail bookkeeping) is folded into that
statement so its conclusion is directly the `∀ y` sup bound this lemma needs. -/

/-- **Lemma C analytic core (NAMED SORRY).**  The fixed-base restart bound:
for `s₀ > 0`, base `τ = s₀/2`, and the source sup bound `Lmax`, there is a G5-driven
modulus closing as `s → s₀` so that the patched-slice difference is `< ε` uniformly
in `y`.  Packaged as the exact existential the calling lemma needs.

**ROUTE** (route (ii), fixed-base restart — the audited path):

1.  *Restart identity at base `τ`.*  From the χ₀ = 0 mild identity `D.hmild`
    (chemotaxis term `(-χ₀)·… = 0`) at `r` and at `τ`, plus Chapman–Kolmogorov
    `intervalFullSemigroupOperator_comp` (`S(r−τ)S(τ) = S(r)`) and the Fubini
    split `∫₀^r = ∫₀^τ + ∫_τ^r` with `S(r−a) = S(r−τ)S(τ−a)` on `[0,τ]`, derive

        D.u r y = S(r−τ)(lift(D.u τ)) y + ∫_τ^r S(r−a)(L(D.u a)) y da   (r > τ).

    The semigroup-pulled-out-of-the-integral interchange is the same interchange
    that produced the spectral *cosine* restart identity
    `picardLimitRestart_general_of_subtypeCont`
    (`IntervalPicardLimitTimeNhdSubtype.lean:342`); if reusing that series form,
    convert its EqOn to the semigroup-integral form via
    `intervalFullSemigroupOperator_eq_cosineHeatValue_Icc`.

2.  *Subtract at `r = s` and `r = s₀`* (WLOG `s ≥ s₀`; symmetric otherwise):

        D.u s − D.u s₀
          = (S(s−s₀) − I)(S(s₀−τ)(lift(D.u τ)))            [homogeneous]
            + (∫_τ^s − ∫_τ^{s₀}) S(·)(L(D.u ·)).            [Duhamel]

3.  *Homogeneous part* `< ε/2`:  the datum `g := fun x => S(s₀−τ)(lift(D.u τ)) x`
    is continuous (semigroup smoothing, `intervalFullSemigroupOperator_contDiff_two_clean`;
    `D.u τ` has continuous slices at `τ = s₀/2 > 0` by `D.hcont`) and bounded
    (`intervalFullSemigroupOperator_Linfty_bound`).  Apply G5
    `intervalFullSemigroup_tendstoUniformlyOn g _` to get a horizon `δ₁` with
    `sup_{x∈[0,1]} |(S(σ) − I) g x| < ε/2` for `0 < σ < δ₁`, instantiated at the
    gap `σ = s − s₀ < δ₁`.

4.  *Duhamel part* `< ε/2`:  the common interval `[τ, s₀]` cancels under
    `S(s−a) = S(s−s₀)S(s₀−a)` + G5 again (or by absorbing it into the homogeneous
    modulus); the short tail `∫_{s₀}^s S(s−a)(L(D.u a))` is bounded by
    `|s − s₀|·Lmax` via `intervalFullSemigroupOperator_Linfty_bound` (Lemma A)
    and `intervalIntegral.norm_integral_le_of_norm_le_const`.  Choose
    `δ₂ := ε / (2·(Lmax + 1))`.

5.  Take `δ := min (min δ₁ δ₂) (s₀/2)`.  Sum the two halves `< ε`.

**STATUS (current).**  The `δ`-bookkeeping skeleton of step 5 is PROVED: we shrink
`δ ≤ s₀/2` so every admissible `s` is forced into the interior regime `τ < s`
(`|s − s₀| < δ ≤ s₀ − τ`), and assemble the final existential.  The single
remaining residual is `hinterior` below — the interior-regime restart bound
`∀ s, τ < s → s ≤ D.T → |s − s₀| < δ₀ → ∀ y, |D.u s y − D.u s₀ y| < ε`.  It carries
exactly the genuine PDE content of steps 1–4 (the fixed-base restart
representation of the canonical Picard limit + its semigroup smoothing).  Closing
it needs the semigroup-out-of-integral interchange of step 1 — for which this
codebase has NO lemma — *or* the spectral restart `picardLimitRestart_general_of_subtypeCont`,
whose hypothesis bundle (`DuhamelSourceBddOn (patchedSource …)` for the limit,
bounded slice cosine coefficients, slice continuity) has no unconditional producer
for `picardLimit` (cf. the vacuity analysis in `IntervalDomainThm11ChiZeroCoreProvider`).
The supporting pieces of steps 3–4 (slice continuity/boundedness at `τ > 0` via
`D.hcont`/`D.hbound`, the cosine-coefficient bound via
`cosineCoeffs_abs_le_of_continuous_bounded`, G5
`intervalFullSemigroup_tendstoUniformlyOn`, the `L∞` Duhamel-tail bound) are all
present in the repo; the irreducible gap is the restart REPRESENTATION itself. -/
theorem mildSlice_restart_bound
    (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (hu₀cont : Continuous u₀)
    (D : GradientMildSolutionData p u₀)
    (hDu : D.u = picardLimit p u₀ D.T)
    {Lmax : ℝ} (hLmax0 : 0 ≤ Lmax)
    (hLmax : ∀ s, 0 < s → s ≤ D.T → ∀ y : ℝ, |logisticLifted p (D.u s) y| ≤ Lmax)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (hs₀T : s₀ ≤ D.T) :
    ∀ ε > 0, ∃ δ > 0, δ ≤ s₀ / 2 ∧
      ∀ s ∈ Set.Icc (0 : ℝ) D.T, |s - s₀| < δ →
        ∀ y, |D.u s y - D.u s₀ y| < ε := by
  intro ε hε
  set τ : ℝ := s₀ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτs₀ : τ < s₀ := by rw [hτdef]; linarith
  have hτT : τ ≤ D.T := le_trans hτs₀.le hs₀T
  -- ============================================================================
  -- ANALYTIC CORE (the single residual `sorry`).
  --
  -- This is route (ii) — the FIXED-BASE restart identity at `τ = s₀/2`
  --
  --     D.u r y = S(r−τ)(lift(D.u τ)) y + ∫_τ^r S(r−a)(L(D.u a)) y da   (r > τ)
  --
  -- together with its homogeneous/Duhamel sup-norm modulus at `s₀`
  -- (route steps 1–4: G5 strong continuity `intervalFullSemigroup_tendstoUniformlyOn`
  -- of the leading term at the closing gap `s − s₀`, and the short Duhamel tail
  -- `≤ |s−s₀|·Lmax` via `intervalFullSemigroupOperator_Linfty_bound`).
  --
  -- It is stated here in the INTERIOR regime `τ < s` — exactly the regime the
  -- caller is forced into by `δ ≤ s₀/2` (proved below).  The genuine PDE content
  -- it carries (the spectral restart representation of the canonical Picard limit
  -- `D.u = picardLimit …` plus its semigroup smoothing) rests on a regularity
  -- bundle — `DuhamelSourceBddOn (patchedSource …)` for the limit, bounded cosine
  -- coefficients of the slices, slice continuity — which in THIS codebase has no
  -- unconditional producer for the canonical limit (cf. the vacuity analysis in
  -- `IntervalDomainThm11ChiZeroCoreProvider`).  We therefore expose it as ONE
  -- precise named residual and discharge the full `δ`-bookkeeping skeleton
  -- (the `δ ≤ s₀/2` constraint, the interior-regime reduction, the final
  -- existential) around it.
  -- ============================================================================
  have hinterior :
      ∃ δ₀ > 0, ∀ s, τ < s → s ≤ D.T → |s - s₀| < δ₀ →
        ∀ y, |D.u s y - D.u s₀ y| < ε := by
    sorry
  -- ---------------------------------------------------------------------------
  -- δ-BOOKKEEPING (fully discharged: shrink to force the interior regime).
  -- ---------------------------------------------------------------------------
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hinterior
  refine ⟨min δ₀ (s₀ / 2), ?_, ?_, ?_⟩
  · exact lt_min hδ₀pos (by linarith)
  · exact min_le_right _ _
  intro s hs hsδ y
  -- `|s − s₀| < δ ≤ s₀/2 = s₀ − τ` forces `s > τ` (the interior regime).
  have hδ_le_half : min δ₀ (s₀ / 2) ≤ s₀ / 2 := min_le_right _ _
  have hsτ : τ < s := by
    have h1 : s₀ - s ≤ |s - s₀| := by rw [abs_sub_comm]; exact le_abs_self _
    have : s₀ - s < s₀ / 2 := lt_of_le_of_lt h1 (lt_of_lt_of_le hsδ hδ_le_half)
    rw [hτdef]; linarith
  have hsδ₀ : |s - s₀| < δ₀ := lt_of_lt_of_le hsδ (min_le_left _ _)
  exact hδ₀ s hsτ hs.2 hsδ₀ y

/-- **Lemma C (`s₀ > 0`).**  The patched slice is sup-norm time-continuous at `s₀`.
Shrinks `δ ≤ s₀/2` so both slices unfold to the mild slice, then applies the
fixed-base restart bound `mildSlice_restart_bound`. -/
theorem patchedSlice_timeContinuousAt_pos
    (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (hu₀cont : Continuous u₀)
    (D : GradientMildSolutionData p u₀)
    (hDu : D.u = picardLimit p u₀ D.T)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (hs₀T : s₀ ≤ D.T) :
    ∀ ε > 0, ∃ δ > 0,
      ∀ s ∈ Set.Icc (0 : ℝ) D.T, |s - s₀| < δ →
        ∀ y, |patchedSlice u₀ D.u s y - patchedSlice u₀ D.u s₀ y| < ε := by
  intro ε hε
  obtain ⟨Lmax, hLmax0, hLmax⟩ := logisticLifted_mildSlice_abs_le D
  obtain ⟨δ, hδpos, hδhalf, hδ⟩ :=
    mildSlice_restart_bound hχ0 hu₀cont D hDu hLmax0 hLmax hs₀ hs₀T ε hε
  refine ⟨δ, hδpos, ?_⟩
  intro s hs hsδ y
  -- `s` is positive: `|s − s₀| < δ ≤ s₀/2` forces `s > s₀/2 > 0`.
  have hspos : 0 < s := by
    have : s₀ - s ≤ |s - s₀| := by rw [abs_sub_comm]; exact le_abs_self _
    have hlt : s₀ - s < s₀ / 2 := lt_of_le_of_lt this (lt_of_lt_of_le hsδ hδhalf)
    linarith
  -- both patched slices unfold to the mild slice.
  rw [patchedSlice_of_pos u₀ D.u hspos, patchedSlice_of_pos u₀ D.u hs₀]
  exact hδ s hs hsδ y

/-! ## Assembly — the `hsliceTC` field. -/

/-- **The `hsliceTC` field**, proved by the one-step mild/restart route.

`by_cases s₀ = 0`: the `s₀ = 0` branch is Lemma B (initial approach), the `s₀ > 0`
branch is Lemma C (fixed-base restart).  This is exactly the
`PicardIterateResidualData.hsliceTC` field for a canonical-Picard-limit datum `D`
with `D.u = picardLimit p u₀ D.T`. -/
theorem hsliceTC_of_mild_restart
    (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (hu₀cont : Continuous u₀)
    (D : GradientMildSolutionData p u₀)
    (hDu : D.u = picardLimit p u₀ D.T) :
    ∀ s₀ ∈ Set.Icc (0 : ℝ) D.T, ∀ ε > 0, ∃ δ > 0,
      ∀ s ∈ Set.Icc (0 : ℝ) D.T, |s - s₀| < δ →
        ∀ y, |patchedSlice u₀ D.u s y - patchedSlice u₀ D.u s₀ y| < ε := by
  intro s₀ hs₀mem ε hε
  by_cases h0 : s₀ = 0
  · subst h0
    exact patchedSlice_timeContinuousAt_zero hu₀cont D ε hε
  · have hs₀pos : 0 < s₀ := lt_of_le_of_ne hs₀mem.1 (Ne.symm h0)
    exact patchedSlice_timeContinuousAt_pos hχ0 hu₀cont D hDu hs₀pos hs₀mem.2 ε hε

end ShenWork.IntervalPicardLimitSliceTimeContinuity
