/-
  ShenWork/Paper2/IntervalPicardLimitCoeffTimeCont.lean

  **Stage A — the NON-CIRCULAR `hcontP` producer.**

  The deliverable consumed by `IntervalPicardLimitBddProducer.duhamelSourceBddOn_of_mildData`
  is

      `hcontP : ∀ k, ContinuousOn (fun s => patchedSource p u₀ D.u s k) (Set.Icc 0 τ)`,

  i.e. time-continuity of the patched limit-source coefficient family on the closed
  window `[0, τ]`.

  ## The circularity we break

  The existing route to `hcontP`
  (`IntervalPicardLimitBddHcontP.patchedSource_continuousOn_Icc`) reduces it to the
  sup-norm *slice* time-continuity `hsliceTC`.  But the only producer of `hsliceTC`
  for the canonical Picard limit
  (`IntervalPicardLimitSliceTimeContinuity.mildSlice_restart_bound`) rests on the
  spectral *restart representation* of the limit, whose hypothesis bundle
  (`DuhamelSourceBddOn (patchedSource …)`, bounded slice cosine coefficients, slice
  continuity) has no unconditional producer — it is exactly the package `hcontP`
  feeds.  Circular; and `mildSlice_restart_bound` still carries a `sorry`.

  ## The non-circular route (coefficient side, uniform convergence)

  We go through the COEFFICIENT functional directly, never through the slice sup
  norm restart:

  * **Interior windows `[a', τ] ⊆ (0, T]` (A2+A3).**  The geometric Picard data of
    `PicardConvFacts` gives an `s`-UNIFORM majorant on the coefficient distance
    `|coeff_k(L(uₙ s)) − coeff_k(L(lim s))| ≤ 2·Lc·(Kⁿ·C₀/(1−K))` (the exact squeeze
    of `IntervalPicardLimitCoeffConv.picardIter_logisticCoeff_tendsto_limit_of_facts`,
    noted to be uniform in `s`).  This is `TendstoUniformlyOn` of the iterate
    coefficient functions to the limit coefficient on `[a', τ]`; with per-iterate
    time-continuity of the coefficient on the window (the WEAKEST iterate-side input
    — see `hiter_cont`, a later projection from the tower), `TendstoUniformlyOn.continuousOn`
    gives `ContinuousOn` of the limit coefficient on `[a', τ]`.

  * **Boundary at `0` (A4).**  `IntervalPicardLimitSliceTimeContinuity.patchedSlice_timeContinuousAt_zero`
    (PROVED, unconditional, READ-only) gives sup-norm patched-slice continuity at `0`;
    we transfer it to coefficient continuity at `0` via the slice Lipschitz bound
    `logisticLifted_slice_dist_le` + the coefficient `2`-Lipschitz bound
    `cosineCoeffs_dist_le_of_sup`, exactly as `patchedSource_continuousOn_Icc` does —
    but ONLY at the single point `0`, where no restart representation is needed.

  * **Glue (A5).**  `ContinuousOn (Icc 0 τ)` pointwise: at `0` the boundary leg, at
    `s₀ ∈ (0, τ]` the window `[s₀/2, τ]` interior leg pushed to `𝓝[Icc 0 τ] s₀`.

  ## What landed vs. stayed hypothetical

  * **A2+A3+A4+A5 (CORE):** fully proved.
  * **A1 (per-iterate coefficient time-continuity producer):** NOT attempted
    unconditionally.  Producing it needs the iterate time-`C¹` coefficient data
    (`adot`/`hderiv`, see `IntervalPicardIterateTimeC1Full.clampedIterateSource_duhamelSourceTimeC1`),
    which only the in-flight tower files carry; importing them would re-introduce
    the cross-file coupling this Stage-A producer is meant to avoid.  It is therefore
    exposed as the WEAKEST named hypothesis `hiter_cont` (window-local
    `ContinuousOn` of the iterate coefficient), to be discharged by a later tower
    projection.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.Paper2.IntervalPicardLimitCoeffConv
import ShenWork.Paper2.IntervalPicardLimitBddProducer
import ShenWork.Paper2.IntervalPicardLimitBddHcontP
import ShenWork.Paper2.IntervalPicardLimitSliceTimeContinuity

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (GradientMildSolutionData picardIter picardLimit)
open ShenWork.IntervalPicardLimitCoeffConv
  (PicardConvFacts cosineCoeffs_dist_le_of_sup logisticLifted_slice_dist_le)
open ShenWork.IntervalPicardLimitBddProducer (patchedSource patchedSource_eq_of_pos)
open ShenWork.IntervalPicardLimitBddHcontP
  (patchedSlice patchedSlice_of_nonpos patchedSlice_of_pos
   patchedSource_eq_coeff_slice logisticLifted_patchedSlice_continuousOn)

noncomputable section

namespace ShenWork.IntervalPicardLimitCoeffTimeCont

variable {p : CM2Params}

/-! ## A2+A3 — the `s`-uniform coefficient majorant on an interior window. -/

/-- **The `s`-uniform coefficient distance majorant.**  On the whole interior range
`(0, T]` the level-`n` iterate logistic coefficient differs from the limit logistic
coefficient by at most `2·Lc·(Kⁿ·C₀/(1−K))`, UNIFORMLY in `s`.  This is the per-`n`
bound underlying `picardIter_logisticCoeff_tendsto_limit_of_facts`, with the
majorant explicitly independent of `s`. -/
theorem coeff_dist_uniform_bound
    {u₀ : intervalDomainPoint → ℝ}
    (F : PicardConvFacts p u₀)
    (hLcont_iter : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ F.T →
      ContinuousOn (logisticLifted p (picardIter p u₀ n σ)) (Set.Icc (0 : ℝ) 1))
    (hLcont_lim : ∀ (σ : ℝ), 0 < σ → σ ≤ F.T →
      ContinuousOn (logisticLifted p (picardLimit p u₀ F.T σ)) (Set.Icc (0 : ℝ) 1)) :
    ∃ Lc : ℝ, 0 ≤ Lc ∧ ∀ (n : ℕ) (s : ℝ), 0 < s → s ≤ F.T → ∀ k,
      |cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k
        - cosineCoeffs (logisticLifted p (picardLimit p u₀ F.T s)) k|
        ≤ 2 * (Lc * (F.K ^ n * F.C₀ / (1 - F.K))) := by
  obtain ⟨Lc, hLc_pos, hLip⟩ := logisticLifted_slice_dist_le p F.hM
  have h1K : (0 : ℝ) < 1 - F.K := by linarith [F.hK]
  refine ⟨Lc, hLc_pos.le, ?_⟩
  intro n s hs hsT k
  -- slice sup bound on `[0,1]`: `|L(uₙ s) x − L(lim s) x| ≤ Lc·(Kⁿ·C₀/(1−K))`.
  have hB_nn : (0 : ℝ) ≤ Lc * (F.K ^ n * F.C₀ / (1 - F.K)) :=
    mul_nonneg hLc_pos.le
      (div_nonneg (mul_nonneg (pow_nonneg F.hK_nn n) F.hC₀) h1K.le)
  have hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |logisticLifted p (picardIter p u₀ n s) x
        - logisticLifted p (picardLimit p u₀ F.T s) x|
        ≤ Lc * (F.K ^ n * F.C₀ / (1 - F.K)) := by
    intro x hx
    have htail : |picardIter p u₀ n s ⟨x, hx⟩
        - picardLimit p u₀ F.T s ⟨x, hx⟩| ≤ F.K ^ n * F.C₀ / (1 - F.K) :=
      ShenWork.IntervalMildPicard.picardIter_pointwise_tail_bound
        p u₀ F.hK F.hK_nn F.hC₀ F.hgeom s hs hsT ⟨x, hx⟩ n
    calc |logisticLifted p (picardIter p u₀ n s) x
            - logisticLifted p (picardLimit p u₀ F.T s) x|
        ≤ Lc * |picardIter p u₀ n s ⟨x, hx⟩
                - picardLimit p u₀ F.T s ⟨x, hx⟩| :=
          hLip (picardIter p u₀ n s) (picardLimit p u₀ F.T s)
            (fun y => F.hball n s hs hsT y) (fun y => F.hball_nn n s hs hsT y)
            (fun y => F.hlim_ball s hs hsT y) (fun y => F.hlim_nn s hs hsT y) hx
      _ ≤ Lc * (F.K ^ n * F.C₀ / (1 - F.K)) :=
          mul_le_mul_of_nonneg_left htail hLc_pos.le
  exact cosineCoeffs_dist_le_of_sup (hLcont_iter n s hs hsT)
    (hLcont_lim s hs hsT) hB_nn hsup k

/-- **Uniform convergence of the iterate coefficient on an interior window.**
On `[a', τ] ⊆ (0, T]`, the iterate logistic-coefficient functions converge
UNIFORMLY (`TendstoUniformlyOn`) to the limit logistic coefficient. -/
theorem coeff_tendstoUniformlyOn_window
    {u₀ : intervalDomainPoint → ℝ}
    (F : PicardConvFacts p u₀)
    (hLcont_iter : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ F.T →
      ContinuousOn (logisticLifted p (picardIter p u₀ n σ)) (Set.Icc (0 : ℝ) 1))
    (hLcont_lim : ∀ (σ : ℝ), 0 < σ → σ ≤ F.T →
      ContinuousOn (logisticLifted p (picardLimit p u₀ F.T σ)) (Set.Icc (0 : ℝ) 1))
    {a' τ : ℝ} (ha' : 0 < a') (hτT : τ ≤ F.T) (k : ℕ) :
    TendstoUniformlyOn
      (fun n s => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
      (fun s => cosineCoeffs (logisticLifted p (picardLimit p u₀ F.T s)) k)
      atTop (Set.Icc a' τ) := by
  obtain ⟨Lc, hLc_nn, hbound⟩ :=
    coeff_dist_uniform_bound F hLcont_iter hLcont_lim
  -- the `s`-free majorant sequence `c n := 2·Lc·(Kⁿ·C₀/(1−K)) → 0`.
  set c : ℕ → ℝ := fun n => 2 * (Lc * (F.K ^ n * F.C₀ / (1 - F.K))) with hc
  have hc_tendsto : Tendsto c atTop (nhds 0) := by
    have hpow : Tendsto (fun n => F.K ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one F.hK_nn F.hK
    have : Tendsto (fun n => 2 * (Lc * (F.K ^ n * F.C₀ / (1 - F.K))))
        atTop (nhds (2 * (Lc * (0 * F.C₀ / (1 - F.K))))) := by
      apply Tendsto.const_mul
      apply Tendsto.const_mul
      apply Tendsto.div_const
      exact (hpow.mul_const F.C₀)
    simpa [hc] using (by simpa using this)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- eventually `c n < ε`.
  filter_upwards [hc_tendsto.eventually_lt_const hε] with n hcn
  intro s hs
  have hspos : 0 < s := lt_of_lt_of_le ha' hs.1
  have hsT : s ≤ F.T := le_trans hs.2 hτT
  rw [Real.dist_eq]
  have hb := hbound n s hspos hsT k
  rw [abs_sub_comm] at hb
  exact lt_of_le_of_lt hb hcn

/-- **Limit coefficient time-continuity on an interior window (A3).**  Given
per-iterate time-continuity of the coefficient on the window `[a', τ] ⊆ (0, T]`,
the LIMIT coefficient is continuous there — as the uniform limit of continuous
functions. -/
theorem limitCoeff_continuousOn_window
    {u₀ : intervalDomainPoint → ℝ}
    (F : PicardConvFacts p u₀)
    (hLcont_iter : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ F.T →
      ContinuousOn (logisticLifted p (picardIter p u₀ n σ)) (Set.Icc (0 : ℝ) 1))
    (hLcont_lim : ∀ (σ : ℝ), 0 < σ → σ ≤ F.T →
      ContinuousOn (logisticLifted p (picardLimit p u₀ F.T σ)) (Set.Icc (0 : ℝ) 1))
    {a' τ : ℝ} (ha' : 0 < a') (hτT : τ ≤ F.T) (k : ℕ)
    (hiter_cont : ∀ (n : ℕ),
      ContinuousOn
        (fun s => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
        (Set.Icc a' τ)) :
    ContinuousOn
      (fun s => cosineCoeffs (logisticLifted p (picardLimit p u₀ F.T s)) k)
      (Set.Icc a' τ) := by
  refine (coeff_tendstoUniformlyOn_window F hLcont_iter hLcont_lim ha' hτT k).continuousOn ?_
  exact Filter.Eventually.frequently (Filter.Eventually.of_forall hiter_cont)

/-! ## A4 — boundary continuity of the patched coefficient at `0`. -/

/-- **Boundary leg (A4).**  Given the uniform nonnegative `M`-ball on the patched
profile and the (PROVED, unconditional) sup-norm patched-slice continuity at `0`
(`patchedSlice_timeContinuousAt_zero`), the patched coefficient is continuous at `0`
within `[0, τ]`.  Transfer: coefficient `2`-Lipschitz in the slice sup norm
(`cosineCoeffs_dist_le_of_sup`) ∘ slice Lipschitz (`logisticLifted_slice_dist_le`). -/
theorem patchedSource_continuousWithinAt_zero
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hu₀cont : Continuous u₀)
    {M : ℝ} (hMpos : 0 < M)
    (hball : ∀ s ∈ Set.Icc (0 : ℝ) D.T, ∀ y, |patchedSlice u₀ D.u s y| ≤ M)
    (hnn : ∀ s ∈ Set.Icc (0 : ℝ) D.T, ∀ y, 0 ≤ patchedSlice u₀ D.u s y)
    {τ : ℝ} (hτT : τ ≤ D.T) (k : ℕ) :
    ContinuousWithinAt
      (fun s => patchedSource p u₀ D.u s k) (Set.Icc 0 τ) 0 := by
  obtain ⟨Lc, hLc_pos, hLip⟩ := logisticLifted_slice_dist_le (p := p) hMpos
  -- sup-norm patched-slice continuity at `0` (on `[0,T]`).
  have hsliceTC0 :=
    ShenWork.IntervalPicardLimitSliceTimeContinuity.patchedSlice_timeContinuousAt_zero
      hu₀cont D
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set η : ℝ := ε / (4 * Lc) with hηdef
  have hη_pos : 0 < η := by rw [hηdef]; positivity
  obtain ⟨δ, hδ_pos, hδ⟩ := hsliceTC0 η hη_pos
  refine ⟨δ, hδ_pos, ?_⟩
  intro s hsmem hsdist
  -- `s ∈ Icc 0 τ ⊆ Icc 0 D.T`.
  have hsT : s ∈ Set.Icc (0 : ℝ) D.T := ⟨hsmem.1, le_trans hsmem.2 hτT⟩
  have h0T : (0 : ℝ) ∈ Set.Icc (0 : ℝ) D.T := ⟨le_refl 0, D.hT.le⟩
  rw [Real.dist_eq] at hsdist
  rw [Real.dist_eq, patchedSource_eq_coeff_slice, patchedSource_eq_coeff_slice]
  -- continuity of both lifted profiles on `[0,1]`.
  have hcont_s := logisticLifted_patchedSlice_continuousOn p D hu₀cont hsT
  have hcont_0 := logisticLifted_patchedSlice_continuousOn p D hu₀cont h0T
  -- pointwise slice distance bound on `[0,1]`.
  have hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |logisticLifted p (patchedSlice u₀ D.u s) x
        - logisticLifted p (patchedSlice u₀ D.u 0) x| ≤ Lc * η := by
    intro x hx
    have hxlt : |patchedSlice u₀ D.u s ⟨x, hx⟩ - patchedSlice u₀ D.u 0 ⟨x, hx⟩| ≤ η := by
      have := hδ s hsT (by simpa using hsdist) ⟨x, hx⟩
      exact this.le
    calc |logisticLifted p (patchedSlice u₀ D.u s) x
            - logisticLifted p (patchedSlice u₀ D.u 0) x|
        ≤ Lc * |patchedSlice u₀ D.u s ⟨x, hx⟩ - patchedSlice u₀ D.u 0 ⟨x, hx⟩| :=
          hLip (patchedSlice u₀ D.u s) (patchedSlice u₀ D.u 0)
            (hball s hsT) (hnn s hsT) (hball 0 h0T) (hnn 0 h0T) hx
      _ ≤ Lc * η := mul_le_mul_of_nonneg_left hxlt hLc_pos.le
  have hLcη_nn : (0 : ℝ) ≤ Lc * η := mul_nonneg hLc_pos.le hη_pos.le
  have hbound := cosineCoeffs_dist_le_of_sup hcont_s hcont_0 hLcη_nn hsup k
  have hlt : 2 * (Lc * η) < ε := by
    rw [hηdef]
    have hsimp : 2 * (Lc * (ε / (4 * Lc))) = ε / 2 := by
      field_simp; ring
    rw [hsimp]; linarith
  exact lt_of_le_of_lt hbound hlt

/-! ## A5 — the glue: `hcontP` on `[0, τ]` from iterate window continuity. -/

/-- **Stage-A `hcontP` producer (conditional glue).**  For a packaged mild solution
`D` whose trajectory is the canonical Picard limit (`hDu`), the patched limit-source
coefficient family is time-continuous on `[0, τ]`, `0 < τ ≤ D.T`, given:

* `F` — the `s`-uniform geometric facts (`PicardConvFacts`, `F.T = D.T`);
* `hLcont_iter`/`hLcont_lim` — `[0,1]`-spatial continuity of the iterate/limit
  logistic sources (genuinely `C²` slices);
* the patched profile's uniform nonnegative `M`-ball;
* `hiter_cont` — the WEAKEST iterate-side input: per-iterate, per-window
  time-`ContinuousOn` of the iterate coefficient on every interior window
  `[a', τ]`, `0 < a'` (a later tower projection discharges this);
* `hu₀cont` — datum continuity (for the boundary leg at `0`).

NON-CIRCULAR: it consumes NO `hsliceTC` at positive times and NO restart
representation; the interior is closed by uniform convergence, the boundary at `0`
by the unconditional initial approach. -/
theorem patchedSource_coeff_continuousOn_of_iterate_data
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hDu : D.u = picardLimit p u₀ D.T)
    (hu₀cont : Continuous u₀)
    (F : PicardConvFacts p u₀) (hF_T : F.T = D.T)
    (hLcont_iter : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T →
      ContinuousOn (logisticLifted p (picardIter p u₀ n σ)) (Set.Icc (0 : ℝ) 1))
    (hLcont_lim : ∀ (σ : ℝ), 0 < σ → σ ≤ D.T →
      ContinuousOn (logisticLifted p (picardLimit p u₀ D.T σ)) (Set.Icc (0 : ℝ) 1))
    {M : ℝ} (hMpos : 0 < M)
    (hball : ∀ s ∈ Set.Icc (0 : ℝ) D.T, ∀ y, |patchedSlice u₀ D.u s y| ≤ M)
    (hnn : ∀ s ∈ Set.Icc (0 : ℝ) D.T, ∀ y, 0 ≤ patchedSlice u₀ D.u s y)
    {τ : ℝ} (_hτ : 0 < τ) (hτT : τ ≤ D.T)
    (hiter_cont : ∀ (a' : ℝ), 0 < a' → a' ≤ τ → ∀ (n : ℕ) (k : ℕ),
      ContinuousOn
        (fun s => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
        (Set.Icc a' τ)) :
    ∀ k, ContinuousOn (fun s => patchedSource p u₀ D.u s k) (Set.Icc 0 τ) := by
  -- transport `F`'s horizon to `D.T`.
  have hLcont_iter' : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ F.T →
      ContinuousOn (logisticLifted p (picardIter p u₀ n σ)) (Set.Icc (0 : ℝ) 1) := by
    rw [hF_T]; exact hLcont_iter
  have hLcont_lim' : ∀ (σ : ℝ), 0 < σ → σ ≤ F.T →
      ContinuousOn (logisticLifted p (picardLimit p u₀ F.T σ)) (Set.Icc (0 : ℝ) 1) := by
    rw [hF_T]; exact hLcont_lim
  have hτF : τ ≤ F.T := by rw [hF_T]; exact hτT
  intro k
  -- pointwise `ContinuousWithinAt` on `[0, τ]`.
  intro s₀ hs₀
  rcases eq_or_lt_of_le hs₀.1 with hs₀0 | hs₀pos
  · -- boundary: `s₀ = 0`.
    subst hs₀0
    exact patchedSource_continuousWithinAt_zero D hu₀cont hMpos hball hnn hτT k
  · -- interior: `s₀ ∈ (0, τ]`; window `[s₀/2, τ]`.
    set a' : ℝ := s₀ / 2 with ha'def
    have ha'pos : 0 < a' := by rw [ha'def]; linarith
    have ha's₀ : a' < s₀ := by rw [ha'def]; linarith
    have ha'τ : a' ≤ τ := le_trans ha's₀.le hs₀.2
    have hs₀τ : s₀ ≤ τ := hs₀.2
    -- the LIMIT coefficient is continuous on the window `[a', τ]`.
    have hwin : ContinuousOn
        (fun s => cosineCoeffs (logisticLifted p (picardLimit p u₀ F.T s)) k)
        (Set.Icc a' τ) :=
      limitCoeff_continuousOn_window F hLcont_iter' hLcont_lim' ha'pos hτF k
        (fun n => hiter_cont a' ha'pos ha'τ n k)
    -- rewrite through `hDu` and `patchedSource_eq_of_pos`: on `(0,τ]` the patched
    -- family equals `coeff (logistic (limit s)) k`.
    have hcongr : Set.EqOn
        (fun s => patchedSource p u₀ D.u s k)
        (fun s => cosineCoeffs (logisticLifted p (picardLimit p u₀ F.T s)) k)
        (Set.Icc a' τ) := by
      intro s hsmem
      have hspos : 0 < s := lt_of_lt_of_le ha'pos hsmem.1
      show patchedSource p u₀ D.u s k
        = cosineCoeffs (logisticLifted p (picardLimit p u₀ F.T s)) k
      rw [patchedSource_eq_of_pos p u₀ D.u hspos k, hDu, ← hF_T]
    have hwin' : ContinuousOn
        (fun s => patchedSource p u₀ D.u s k) (Set.Icc a' τ) :=
      hwin.congr hcongr
    -- push the window `ContinuousWithinAt` to `𝓝[Icc 0 τ] s₀`.
    have hcwa : ContinuousWithinAt
        (fun s => patchedSource p u₀ D.u s k) (Set.Icc a' τ) s₀ :=
      hwin'.continuousWithinAt ⟨ha's₀.le, hs₀τ⟩
    refine hcwa.mono_of_mem_nhdsWithin ?_
    -- `Icc a' τ ∈ 𝓝[Icc 0 τ] s₀`: take the open `Ioi a'`.
    rw [mem_nhdsWithin]
    refine ⟨Set.Ioi a', isOpen_Ioi, ha's₀, ?_⟩
    intro x hx
    exact ⟨le_of_lt hx.1, hx.2.2⟩

end ShenWork.IntervalPicardLimitCoeffTimeCont
