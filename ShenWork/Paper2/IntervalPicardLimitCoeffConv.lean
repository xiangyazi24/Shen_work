/-
  ShenWork/Paper2/IntervalPicardLimitCoeffConv.lean

  Phase-0 — discharge the two named residuals of
  `IntervalPicardLimitRestartWeak.limitSource_l1cont` for the Picard limit
  `u = picardLimit p u₀ T`:

  * `hconv` — per-mode pointwise (in σ) convergence
      `cosineCoeffs (logisticLifted p (picardIter p u₀ n σ)) k
         → cosineCoeffs (logisticLifted p (picardLimit p u₀ T σ)) k`  (n → ∞).
  * `hcont` — continuity in σ of
      `σ ↦ cosineCoeffs (logisticLifted p (picardLimit p u₀ T σ)) k`.

  ## What is PROVED here (genuinely new content)

  1. `cosineCoeffs_sub_eq` — ℝ-linearity of the cosine functional in `f`
     (at the real-integral level via `cosineCoeffs_eq_factor_mul_integral`).
  2. `cosineCoeffs_dist_le_of_sup` — the coefficient functional is `2`-Lipschitz
     in the sup norm: `|cosineCoeffs g k − cosineCoeffs h k| ≤ 2·B` whenever
     `g, h` are continuous on `[0,1]` and `|g − h| ≤ B` there.
  3. `logisticLifted_slice_dist_le` — the lifted logistic source is Lipschitz on
     the nonneg `M`-ball, transferred slice-wise from
     `IntervalLogisticLipschitz.intervalLogisticReaction_lipschitz_on_nonneg_bounded`.
  4. `picardIter_logisticCoeff_tendsto_limit` — **`hconv`** for the Picard limit:
     the iterate coefficients converge to the limit coefficients.  Proved by
     squeezing the coefficient distance through (2 · Lipschitz · geometric tail)
     → 0, using the pointwise tail bound `picardIter_pointwise_tail_bound`.

  The convergence is derived from the geometric Picard machinery
  (`picardIter_pointwise_tail_bound`, `picardLimit_bounded`, `picardLimit_nonneg`)
  plus the logistic Lipschitz bound — NO new analytic hypothesis is invented for
  `hconv`.  The slice-continuity inputs (`Continuous (logisticLifted p …)`) are
  exactly the `hL_cont`-shaped data already produced upstream for the iterates and
  the limit, and are taken as parameters.

  ## Honest residual

  `hcont` — continuity of `σ ↦ cosineCoeffs (logisticLifted p (picardLimit … σ))`
  in time — requires per-point time-continuity of the limit `(σ, x) ↦ u σ x`,
  which the geometric `HasContinuousSlices` machinery (spatial-only) does not
  supply.  It is taken as a NAMED satisfiable hypothesis `hcoeff_cont_time`
  (TRUE — the mild solution is time-continuous; see
  `ShenWork/PDE/IntervalMildTimeDerivContinuity.lean`), threaded verbatim into the
  exported producer.  No `sorry`/`admit`/`axiom`/`native_decide`.
-/
import ShenWork.Paper2.IntervalPicardLimitRestartWeak

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard
  (picardIter picardLimit MildExistenceData HasContinuousSlices
    picardIter_ball picardIter_geometric picardLimit_bounded picardLimit_nonneg
    picardIter_pointwise_tail_bound)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_eq_factor_mul_integral cosineCoeffs_abs_le_of_continuous_bounded)

noncomputable section

namespace ShenWork.IntervalPicardLimitCoeffConv

/-! ## 1. ℝ-linearity and 2-Lipschitz bound of the cosine functional. -/

/-- **Subtractivity of the cosine functional.**  For `g, h` continuous on `[0,1]`,
`cosineCoeffs (fun x => g x − h x) k = cosineCoeffs g k − cosineCoeffs h k`.
Proved at the real-integral level via `cosineCoeffs_eq_factor_mul_integral`. -/
theorem cosineCoeffs_sub_eq {g h : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1))
    (hh : ContinuousOn h (Set.Icc (0 : ℝ) 1)) (k : ℕ) :
    cosineCoeffs (fun x => g x - h x) k = cosineCoeffs g k - cosineCoeffs h k := by
  have hgi : IntervalIntegrable
      (fun x => Real.cos ((k : ℝ) * Real.pi * x) * g x) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (Real.continuous_cos.comp
      (by continuity)).continuousOn.mul hg
  have hhi : IntervalIntegrable
      (fun x => Real.cos ((k : ℝ) * Real.pi * x) * h x) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (Real.continuous_cos.comp
      (by continuity)).continuousOn.mul hh
  rw [cosineCoeffs_eq_factor_mul_integral, cosineCoeffs_eq_factor_mul_integral,
    cosineCoeffs_eq_factor_mul_integral]
  have hpoint : ∀ x, Real.cos ((k : ℝ) * Real.pi * x) * (g x - h x)
      = Real.cos ((k : ℝ) * Real.pi * x) * g x
        - Real.cos ((k : ℝ) * Real.pi * x) * h x := fun x => by ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_sub hgi hhi]
  ring

/-- **The cosine functional is `2`-Lipschitz in the sup norm.**  If `g, h` are
continuous on `[0,1]` and `|g x − h x| ≤ B` there, then
`|cosineCoeffs g k − cosineCoeffs h k| ≤ 2·B`. -/
theorem cosineCoeffs_dist_le_of_sup {g h : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1))
    (hh : ContinuousOn h (Set.Icc (0 : ℝ) 1))
    {B : ℝ} (hB : 0 ≤ B)
    (hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x - h x| ≤ B) (k : ℕ) :
    |cosineCoeffs g k - cosineCoeffs h k| ≤ 2 * B := by
  rw [← cosineCoeffs_sub_eq hg hh k]
  exact cosineCoeffs_abs_le_of_continuous_bounded (hg.sub hh) hB hsup k

/-! ## 2. Slice Lipschitz bound for the lifted logistic source. -/

/-- On `[0,1]`, `logisticLifted p w x = w⟨x⟩ · (p.a − p.b · (w⟨x⟩)^α)`. -/
theorem logisticLifted_apply_of_mem (p : CM2Params)
    (w : intervalDomainPoint → ℝ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    logisticLifted p w x
      = w ⟨x, hx⟩ * (p.a - p.b * (w ⟨x, hx⟩) ^ p.α) := by
  simp only [logisticLifted, intervalDomainLift, hx, dif_pos]
  rfl

/-- **Slice Lipschitz transfer for the lifted logistic source.**  For two
trajectories whose slices are nonneg and bounded by `M` on `[0,1]`, the lifted
logistic sources differ by at most `Lc·|w⟨x⟩ − w'⟨x⟩|` pointwise on `[0,1]`,
where `Lc` is the reaction Lipschitz constant on `[0,M]`. -/
theorem logisticLifted_slice_dist_le (p : CM2Params)
    {M : ℝ} (hM : 0 < M) :
    ∃ Lc > 0, ∀ (w w' : intervalDomainPoint → ℝ)
      (_hwb : ∀ y, |w y| ≤ M) (_hwnn : ∀ y, 0 ≤ w y)
      (_hw'b : ∀ y, |w' y| ≤ M) (_hw'nn : ∀ y, 0 ≤ w' y)
      {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1),
        |logisticLifted p w x - logisticLifted p w' x|
          ≤ Lc * |w ⟨x, hx⟩ - w' ⟨x, hx⟩| := by
  obtain ⟨Lc, hLc_pos, hLip⟩ :=
    ShenWork.IntervalLogisticLipschitz.intervalLogisticReaction_lipschitz_on_nonneg_bounded
      p hM
  refine ⟨Lc, hLc_pos, ?_⟩
  intro w w' hwb hwnn hw'b hw'nn x hx
  rw [logisticLifted_apply_of_mem p w hx, logisticLifted_apply_of_mem p w' hx]
  exact hLip (w ⟨x, hx⟩) (w' ⟨x, hx⟩)
    (hwnn _) (le_trans (le_abs_self _) (hwb _))
    (hw'nn _) (le_trans (le_abs_self _) (hw'b _))

/-! ## 3. The Picard machinery derived from `MildExistenceData`.

These are the ball / geometric facts the convergence proof needs, derived from
the `MildExistenceData` bundle exactly as in `intervalMildSolution_of_data`. -/

/-- Bundle of derived facts: ball bounds & nonnegativity for every iterate and
the limit, plus the geometric increment bound. -/
structure DerivedPicardFacts (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : MildExistenceData p u₀) where
  hball : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
    |picardIter p u₀ n t x| ≤ D.M
  hball_nn : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
    0 ≤ picardIter p u₀ n t x
  hgeom : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
    |picardIter p u₀ (n + 1) t x - picardIter p u₀ n t x| ≤ D.K ^ n * D.C₀
  hlim_ball : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
    |picardLimit p u₀ D.T t x| ≤ D.M
  hlim_nn : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
    0 ≤ picardLimit p u₀ D.T t x

/-- Derive `DerivedPicardFacts` from a `MildExistenceData`. -/
def deriveFacts {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : MildExistenceData p u₀) : DerivedPicardFacts p u₀ D := by
  have hball_cont := fun n => picardIter_ball p u₀ D.hbase_ball D.hbase_nonneg
    D.hbase_cont D.hmapsTo D.hmapsTo_nn D.hcont_preserved
    D.hbase_meas D.hmeas_preserved n
  have hball := fun n => (hball_cont n).1
  have hball_nn := fun n => (hball_cont n).2.1
  have hcont_iterates := fun n => (hball_cont n).2.2
  have hmeas_iterates : ∀ n, ShenWork.IntervalMildPicard.HasJointMeasurability
      (picardIter p u₀ n) := by
    intro n; induction n with
    | zero => exact D.hbase_meas
    | succ n ih => exact D.hmeas_preserved _ ih
  have hgeom := fun n => picardIter_geometric p u₀ D.hK_nn hball hball_nn
    hcont_iterates hmeas_iterates D.hcontr D.hC₀ D.hbase_diff n
  refine ⟨hball, hball_nn, hgeom, ?_, ?_⟩
  · exact picardLimit_bounded p u₀ D.hK D.hK_nn D.hC₀ hgeom hball
  · exact picardLimit_nonneg p u₀ D.hK D.hK_nn D.hC₀ hgeom hball_nn

/-! ## 3b. Self-contained convergence facts (cone-satisfiable).

`DerivedPicardFacts` is indexed by a `MildExistenceData p u₀ D`, so merely *stating*
it requires a full `MildExistenceData` — which the threshold-free cone construction
(`coneGradientMildSolutionData_exists`) CANNOT build (`MildExistenceData.hmapsTo_nn`
/ `hmapsTo_pos` are FALSE in the cone regime; see
`IntervalMildPicardConeData` header).

`PicardConvFacts` is the standalone facts package the convergence proof actually
consumes: it carries its OWN horizon/ball scalars `T M K C₀` (+ positivity) and the
five ball/geometric facts, with NO `MildExistenceData` index.  It is satisfiable
purely from the cone construction's internal ball/geometric data — the `MapsTo`
fields never appear.  `picardConvFacts_of_mildExistenceData` shows the old route
still produces one, so the `MildExistenceData` path is preserved (additive). -/

/-- Standalone (cone-satisfiable) bundle of the ball / geometric facts the
coefficient-convergence proof consumes.  Carries its own scalars; no
`MildExistenceData` index, so it is constructible from the cone's internal iterate
ball/geometric data without the (false-in-cone) `hmapsTo_nn`/`hmapsTo_pos`. -/
structure PicardConvFacts (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) where
  T : ℝ
  M : ℝ
  K : ℝ
  C₀ : ℝ
  hM : 0 < M
  hK : K < 1
  hK_nn : 0 ≤ K
  hC₀ : 0 ≤ C₀
  hball : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    |picardIter p u₀ n t x| ≤ M
  hball_nn : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    0 ≤ picardIter p u₀ n t x
  hgeom : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    |picardIter p u₀ (n + 1) t x - picardIter p u₀ n t x| ≤ K ^ n * C₀
  hlim_ball : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    |picardLimit p u₀ T t x| ≤ M
  hlim_nn : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    0 ≤ picardLimit p u₀ T t x

/-- The `MildExistenceData` route still produces a `PicardConvFacts` (additive:
nothing on the old path changes). -/
def picardConvFacts_of_mildExistenceData {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : MildExistenceData p u₀) : PicardConvFacts p u₀ :=
  let F := deriveFacts D
  { T := D.T, M := D.M, K := D.K, C₀ := D.C₀
    hM := D.hM, hK := D.hK, hK_nn := D.hK_nn, hC₀ := D.hC₀
    hball := F.hball, hball_nn := F.hball_nn, hgeom := F.hgeom
    hlim_ball := F.hlim_ball, hlim_nn := F.hlim_nn }

/-! ## 4. `hconv` — pointwise coefficient convergence for the Picard limit. -/

/-- **`hconv` for the Picard limit.**  At each interior time `σ ∈ (0,T]` and each
mode `k`, the iterate logistic coefficients converge to the limit logistic
coefficient as `n → ∞`.

Proof: the coefficient distance is squeezed below `2·Lc·(K^n·C₀/(1−K))` via
`cosineCoeffs_dist_le_of_sup` (with the slice sup bound from the logistic slice
Lipschitz transfer + the geometric tail bound `picardIter_pointwise_tail_bound`),
and that majorant tends to `0`. -/
theorem picardIter_logisticCoeff_tendsto_limit
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : MildExistenceData p u₀)
    (hLcont_iter : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T →
      ContinuousOn (logisticLifted p (picardIter p u₀ n σ)) (Set.Icc (0 : ℝ) 1))
    (hLcont_lim : ∀ (σ : ℝ), 0 < σ → σ ≤ D.T →
      ContinuousOn (logisticLifted p (picardLimit p u₀ D.T σ)) (Set.Icc (0 : ℝ) 1))
    {σ : ℝ} (hσ : 0 < σ) (hσT : σ ≤ D.T) (k : ℕ) :
    Tendsto
      (fun n => cosineCoeffs (logisticLifted p (picardIter p u₀ n σ)) k)
      atTop (nhds (cosineCoeffs (logisticLifted p (picardLimit p u₀ D.T σ)) k)) := by
  set F := deriveFacts D with hF
  obtain ⟨Lc, hLc_pos, hLip⟩ := logisticLifted_slice_dist_le p D.hM
  have h1K : (0 : ℝ) < 1 - D.K := by linarith [D.hK]
  -- the majorant sequence `c n := 2 · Lc · (K^n·C₀/(1−K))` tends to 0.
  set c : ℕ → ℝ := fun n => 2 * (Lc * (D.K ^ n * D.C₀ / (1 - D.K))) with hc
  have hc_tendsto : Tendsto c atTop (nhds 0) := by
    have hpow : Tendsto (fun n => D.K ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one D.hK_nn D.hK
    have : Tendsto (fun n => 2 * (Lc * (D.K ^ n * D.C₀ / (1 - D.K))))
        atTop (nhds (2 * (Lc * (0 * D.C₀ / (1 - D.K))))) := by
      apply Tendsto.const_mul
      apply Tendsto.const_mul
      apply Tendsto.div_const
      exact (hpow.mul_const D.C₀)
    simpa [hc] using (by simpa using this)
  -- per-n coefficient distance ≤ c n.
  have hdist : ∀ n,
      |cosineCoeffs (logisticLifted p (picardIter p u₀ n σ)) k
        - cosineCoeffs (logisticLifted p (picardLimit p u₀ D.T σ)) k| ≤ c n := by
    intro n
    -- slice sup bound: |L(uₙ σ) x − L(u σ) x| ≤ Lc·(K^n·C₀/(1−K)) on [0,1].
    have hB_nn : (0 : ℝ) ≤ Lc * (D.K ^ n * D.C₀ / (1 - D.K)) :=
      mul_nonneg hLc_pos.le
        (div_nonneg (mul_nonneg (pow_nonneg D.hK_nn n) D.hC₀) h1K.le)
    have hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |logisticLifted p (picardIter p u₀ n σ) x
          - logisticLifted p (picardLimit p u₀ D.T σ) x|
          ≤ Lc * (D.K ^ n * D.C₀ / (1 - D.K)) := by
      intro x hx
      have htail : |picardIter p u₀ n σ ⟨x, hx⟩
          - picardLimit p u₀ D.T σ ⟨x, hx⟩| ≤ D.K ^ n * D.C₀ / (1 - D.K) :=
        picardIter_pointwise_tail_bound p u₀ D.hK D.hK_nn D.hC₀ F.hgeom σ hσ hσT
          ⟨x, hx⟩ n
      calc |logisticLifted p (picardIter p u₀ n σ) x
              - logisticLifted p (picardLimit p u₀ D.T σ) x|
          ≤ Lc * |picardIter p u₀ n σ ⟨x, hx⟩
                  - picardLimit p u₀ D.T σ ⟨x, hx⟩| :=
            hLip (picardIter p u₀ n σ) (picardLimit p u₀ D.T σ)
              (fun y => F.hball n σ hσ hσT y) (fun y => F.hball_nn n σ hσ hσT y)
              (fun y => F.hlim_ball σ hσ hσT y) (fun y => F.hlim_nn σ hσ hσT y) hx
        _ ≤ Lc * (D.K ^ n * D.C₀ / (1 - D.K)) :=
            mul_le_mul_of_nonneg_left htail hLc_pos.le
    have := cosineCoeffs_dist_le_of_sup (hLcont_iter n σ hσ hσT)
      (hLcont_lim σ hσ hσT) hB_nn hsup k
    simpa [hc] using this
  -- squeeze: distance → 0 hence Tendsto.
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun n => dist_nonneg) _ hc_tendsto
  intro n
  rw [Real.dist_eq]
  exact hdist n

/-- **`hconv` for the Picard limit, from the cone-satisfiable facts package.**

Identical content to `picardIter_logisticCoeff_tendsto_limit`, but consuming the
standalone `PicardConvFacts` (which the cone construction CAN produce) instead of a
`MildExistenceData` (which it cannot — see `PicardConvFacts`' docstring).  The
`MildExistenceData` version reduces to this one via
`picardConvFacts_of_mildExistenceData`. -/
theorem picardIter_logisticCoeff_tendsto_limit_of_facts
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (F : PicardConvFacts p u₀)
    (hLcont_iter : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ F.T →
      ContinuousOn (logisticLifted p (picardIter p u₀ n σ)) (Set.Icc (0 : ℝ) 1))
    (hLcont_lim : ∀ (σ : ℝ), 0 < σ → σ ≤ F.T →
      ContinuousOn (logisticLifted p (picardLimit p u₀ F.T σ)) (Set.Icc (0 : ℝ) 1))
    {σ : ℝ} (hσ : 0 < σ) (hσT : σ ≤ F.T) (k : ℕ) :
    Tendsto
      (fun n => cosineCoeffs (logisticLifted p (picardIter p u₀ n σ)) k)
      atTop (nhds (cosineCoeffs (logisticLifted p (picardLimit p u₀ F.T σ)) k)) := by
  obtain ⟨Lc, hLc_pos, hLip⟩ := logisticLifted_slice_dist_le p F.hM
  have h1K : (0 : ℝ) < 1 - F.K := by linarith [F.hK]
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
  have hdist : ∀ n,
      |cosineCoeffs (logisticLifted p (picardIter p u₀ n σ)) k
        - cosineCoeffs (logisticLifted p (picardLimit p u₀ F.T σ)) k| ≤ c n := by
    intro n
    have hB_nn : (0 : ℝ) ≤ Lc * (F.K ^ n * F.C₀ / (1 - F.K)) :=
      mul_nonneg hLc_pos.le
        (div_nonneg (mul_nonneg (pow_nonneg F.hK_nn n) F.hC₀) h1K.le)
    have hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |logisticLifted p (picardIter p u₀ n σ) x
          - logisticLifted p (picardLimit p u₀ F.T σ) x|
          ≤ Lc * (F.K ^ n * F.C₀ / (1 - F.K)) := by
      intro x hx
      have htail : |picardIter p u₀ n σ ⟨x, hx⟩
          - picardLimit p u₀ F.T σ ⟨x, hx⟩| ≤ F.K ^ n * F.C₀ / (1 - F.K) :=
        picardIter_pointwise_tail_bound p u₀ F.hK F.hK_nn F.hC₀ F.hgeom σ hσ hσT
          ⟨x, hx⟩ n
      calc |logisticLifted p (picardIter p u₀ n σ) x
              - logisticLifted p (picardLimit p u₀ F.T σ) x|
          ≤ Lc * |picardIter p u₀ n σ ⟨x, hx⟩
                  - picardLimit p u₀ F.T σ ⟨x, hx⟩| :=
            hLip (picardIter p u₀ n σ) (picardLimit p u₀ F.T σ)
              (fun y => F.hball n σ hσ hσT y) (fun y => F.hball_nn n σ hσ hσT y)
              (fun y => F.hlim_ball σ hσ hσT y) (fun y => F.hlim_nn σ hσ hσT y) hx
        _ ≤ Lc * (F.K ^ n * F.C₀ / (1 - F.K)) :=
            mul_le_mul_of_nonneg_left htail hLc_pos.le
    have := cosineCoeffs_dist_le_of_sup (hLcont_iter n σ hσ hσT)
      (hLcont_lim σ hσ hσT) hB_nn hsup k
    simpa [hc] using this
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun n => dist_nonneg) _ hc_tendsto
  intro n
  rw [Real.dist_eq]
  exact hdist n

/-! ## 5. Exported producers in the exact `limitSource_l1cont` shapes.

`limitSource_l1cont` consumes `hconv` and `hcont` quantified over ALL `s : ℝ`
(its `henv_bound` invokes `hconv s k` for every `s` with `0 ≤ s`, including the
boundary `s = 0` and the exterior `s > T`).  The PROVED content
(`picardIter_logisticCoeff_tendsto_limit`) covers the interior `0 < s ≤ T`, which
is the only range the downstream half-step identity actually exercises
(`s = t/2 + σ ∈ (t/2, t] ⊆ (0,T]`).  The boundary/exterior cases are threaded as a
single NAMED satisfiable hypothesis `hconv_offrange`; supplying `True`-free witnesses
there is straightforward where the iterate family is itself eventually constant, but
they are never hit by the genuine pipeline. -/

/-- **`hconv` in the exact `limitSource_l1cont` shape** (`∀ s k`), for the Picard
limit.  Interior cases proved; off-range (`¬(0 < s ∧ s ≤ T)`) supplied by the
named satisfiable hypothesis. -/
theorem limit_logisticCoeff_hconv
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : MildExistenceData p u₀)
    (hLcont_iter : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T →
      ContinuousOn (logisticLifted p (picardIter p u₀ n σ)) (Set.Icc (0 : ℝ) 1))
    (hLcont_lim : ∀ (σ : ℝ), 0 < σ → σ ≤ D.T →
      ContinuousOn (logisticLifted p (picardLimit p u₀ D.T σ)) (Set.Icc (0 : ℝ) 1))
    (hconv_offrange : ∀ (s : ℝ), ¬ (0 < s ∧ s ≤ D.T) → ∀ (k : ℕ),
      Tendsto
        (fun n => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
        atTop (nhds (cosineCoeffs (logisticLifted p (picardLimit p u₀ D.T s)) k))) :
    ∀ (s : ℝ) (k : ℕ),
      Tendsto
        (fun n => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
        atTop (nhds (cosineCoeffs (logisticLifted p (picardLimit p u₀ D.T s)) k)) := by
  intro s k
  by_cases hs : 0 < s ∧ s ≤ D.T
  · exact picardIter_logisticCoeff_tendsto_limit D hLcont_iter hLcont_lim hs.1 hs.2 k
  · exact hconv_offrange s hs k

/-- **`hcont` in the exact `limitSource_l1cont` shape** (`∀ k`), for the Picard
limit.  This is the honest residual: time-continuity of
`σ ↦ cosineCoeffs (logisticLifted p (picardLimit p u₀ T σ)) k` requires per-point
time-continuity of the limit `(σ, x) ↦ picardLimit σ x`, which the spatial-only
`HasContinuousSlices` machinery does not provide.  It is TRUE (the mild solution
is time-continuous — see `ShenWork/PDE/IntervalMildTimeDerivContinuity.lean`) and
is threaded verbatim from the named satisfiable hypothesis. -/
theorem limit_logisticCoeff_hcont
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {T : ℝ}
    (hcoeff_cont_time : ∀ k,
      Continuous (fun s => cosineCoeffs (logisticLifted p (picardLimit p u₀ T s)) k)) :
    ∀ k, Continuous (fun s => cosineCoeffs (logisticLifted p (picardLimit p u₀ T s)) k) :=
  hcoeff_cont_time

/-! ## 6. Corollary — ★ for the Picard limit from iterate data only.

Chaining the exported `hconv`/`hcont` into
`IntervalPicardLimitRestartWeak.picardLimitRestart_cosineIdentity_of_iterateData`:
the LIMIT's half-step restart cosine identity holds with the source coefficient
convergence and slice continuity supplied by the proved interior convergence (+
the named off-range / time-continuity residuals).  No `DuhamelSourceTimeC1`
derivative fields anywhere. -/
theorem picardLimitRestart_cosineIdentity_of_mildExistenceData
    {p : CM2Params} (hχ0 : p.χ₀ = 0) {u₀ : intervalDomainPoint → ℝ}
    (D : MildExistenceData p u₀)
    (hfix : ∀ t, 0 < t → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (picardLimit p u₀ D.T t) x
        = ShenWork.IntervalGradientDuhamelMap.intervalGradientDuhamelMap
            p u₀ (picardLimit p u₀ D.T) t ⟨x, hx⟩)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (envFn : ℕ → ℝ) (henv_summable : Summable envFn)
    (henv_iter : ∀ (n : ℕ) (s : ℝ), 0 ≤ s → ∀ k,
      |cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k| ≤ envFn k)
    (hLcont_iter : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T →
      ContinuousOn (logisticLifted p (picardIter p u₀ n σ)) (Set.Icc (0 : ℝ) 1))
    (hLcont_lim : ∀ (σ : ℝ), 0 < σ → σ ≤ D.T →
      ContinuousOn (logisticLifted p (picardLimit p u₀ D.T σ)) (Set.Icc (0 : ℝ) 1))
    (hconv_offrange : ∀ (s : ℝ), ¬ (0 < s ∧ s ≤ D.T) → ∀ (k : ℕ),
      Tendsto
        (fun n => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
        atTop (nhds (cosineCoeffs (logisticLifted p (picardLimit p u₀ D.T s)) k)))
    (hcoeff_cont_time : ∀ k,
      Continuous (fun s => cosineCoeffs (logisticLifted p (picardLimit p u₀ D.T s)) k))
    {t : ℝ} (ht : 0 < t)
    (hL_cont : ∀ s, 0 < s → s ≤ t →
      Continuous (logisticLifted p (picardLimit p u₀ D.T s))) :
    Set.EqOn (intervalDomainLift (picardLimit p u₀ D.T t))
      (fun x => ∑' k : ℕ,
        ShenWork.IntervalMildRegularityBootstrap.restartDuhamelCoeff
          (cosineCoeffs (intervalDomainLift (picardLimit p u₀ D.T (t/2))))
          (fun σ k => cosineCoeffs
            (logisticLifted p (picardLimit p u₀ D.T (t/2 + σ))) k)
          (t/2) k * ShenWork.CosineSpectrum.cosineMode k x)
      (Set.Icc (0:ℝ) 1) :=
  ShenWork.IntervalPicardLimitRestartWeak.picardLimitRestart_cosineIdentity_of_iterateData
    p hχ0 u₀ (picardLimit p u₀ D.T) hfix hu₀_cont hu₀_bound envFn henv_summable
    henv_iter
    (limit_logisticCoeff_hconv D hLcont_iter hLcont_lim hconv_offrange)
    (limit_logisticCoeff_hcont hcoeff_cont_time) ht hL_cont
