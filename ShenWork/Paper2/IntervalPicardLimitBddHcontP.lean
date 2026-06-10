/-
  ShenWork/Paper2/IntervalPicardLimitBddHcontP.lean

  **Datum-side source bound and time-continuity of the patched coefficient
  family.**  These are the named satisfiable residuals consumed by the F2
  iterate-side bootstrap (`IntervalPicardLimitBddBootstrap.duhamelSourceBddOn_of_iterates`)
  in `IntervalDomainThm11ChiZeroCoreProvider`:

  * `datum_source_coeff_bound` (R-src0F-1a/1b) — the `s ≤ 0` branch coefficient
    bound `|cosineCoeffs (logisticLifted p u₀) k| ≤ M₀'`, with the concrete witness
    `M₀' := 2 * (B * (p.a + p.b * B ^ p.α))`, `B := sSup (range |u₀|)`.  Route:
    `u₀` is continuous (subtype) and bounded (PID admissibility), hence
    `intervalDomainLift u₀` is continuous and bounded on `[0,1]`; positivity on the
    interior `Ioo 0 1` closes to `0 ≤ u₀` on `[0,1]` by continuity, so the logistic
    source `g·(a − b·gᵅ)` is sup-bounded by `B·(a + b·Bᵅ)`, and
    `cosineCoeffs_abs_le_of_continuous_bounded` doubles it.

  * `patchedSource_continuousOn_Icc` (R-src0F-4) — the time continuity
    `∀ k, ContinuousOn (fun s => patchedSource p u₀ D.u s k) (Set.Icc 0 D.T)`.  The
    coefficient functional is `2`-Lipschitz in the slice sup norm
    (`cosineCoeffs_dist_le_of_sup`) and the lifted logistic source is locally
    Lipschitz in the slice on bounded nonnegative profiles
    (`logisticLifted_slice_dist_le`); so continuity of the coefficient family
    reduces to sup-norm time continuity of the patched slice family
    `s ↦ patchedSlice` on `[0, T]` — the genuine analytic input (interior slice
    time continuity of the mild trajectory + the `s = 0⁺` initial approach
    `gradientMildSolutionData_initialApproach`).  That sup-norm time continuity is
    isolated as the single named hypothesis `hsliceTC`.
-/
import ShenWork.Paper2.IntervalPicardLimitBddProducer
import ShenWork.Paper2.IntervalPicardLimitCoeffConv
import ShenWork.Paper2.IntervalMildPicardThreshold

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildPicardRegularity

namespace ShenWork.IntervalPicardLimitBddHcontP

variable {p : CM2Params}

/-! ## 1. The nonnegative-profile logistic source bound.

The library `logisticSourceFun_abs_le_of_bound` demands *strict* positivity of the
profile on `[0,1]`; for the initial datum the profile is only nonnegative at the
endpoints (positivity holds on the open interior, closing to `≥ 0` by continuity).
The proof of the bound only ever uses `0 ≤ g x`, so we re-derive the nonnegative
variant. -/

theorem logisticSourceFun_abs_le_of_nonneg_bound
    {a b α : ℝ} {g : ℝ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hα : 0 < α) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hnn : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g x)
    (hbd : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ B) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |logisticSourceFun a b α g x| ≤ B * (a + b * B ^ α) := by
  intro x hx
  simp only [logisticSourceFun]
  have hgx_nn : 0 ≤ g x := hnn x hx
  have hgx_le : g x ≤ B := by
    have := hbd x hx
    rw [abs_of_nonneg hgx_nn] at this
    exact this
  rw [abs_mul, abs_of_nonneg hgx_nn]
  have hgα_nn : 0 ≤ g x ^ α := Real.rpow_nonneg hgx_nn α
  have hgα_le : g x ^ α ≤ B ^ α := Real.rpow_le_rpow hgx_nn hgx_le hα.le
  have hbgα_nn : 0 ≤ b * g x ^ α := mul_nonneg hb hgα_nn
  have hbBα_nn : 0 ≤ b * B ^ α := mul_nonneg hb (Real.rpow_nonneg hB α)
  have hab_sum_nn : 0 ≤ a + b * g x ^ α := by linarith
  have hbgα_le_bBα : b * g x ^ α ≤ b * B ^ α :=
    mul_le_mul_of_nonneg_left hgα_le hb
  have habs_le : |a - b * g x ^ α| ≤ a + b * g x ^ α := by
    rw [abs_le]; constructor <;> linarith
  calc g x * |a - b * g x ^ α|
      ≤ g x * (a + b * g x ^ α) := mul_le_mul_of_nonneg_left habs_le hgx_nn
    _ ≤ B * (a + b * B ^ α) := mul_le_mul hgx_le (by linarith) hab_sum_nn hB

/-! ## 2. The datum-side coefficient bound (R-src0F-1a/1b). -/

/-- `0 ≤ B := sSup (range |u₀|)` for an admissible datum (the range is nonempty
and bounded above). -/
theorem datum_sSup_nonneg {u₀ : intervalDomainPoint → ℝ}
    (hbdd : BddAbove (Set.range fun x => |u₀ x|)) :
    (0 : ℝ) ≤ sSup (Set.range fun x => |u₀ x|) :=
  le_trans (abs_nonneg _)
    (le_csSup hbdd ⟨⟨1 / 2, ⟨by norm_num, by norm_num⟩⟩, rfl⟩)

/-- The concrete datum-side witness constant. -/
noncomputable def datumBound (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) : ℝ :=
  2 * (sSup (Set.range fun x => |u₀ x|)
        * (p.a + p.b * (sSup (Set.range fun x => |u₀ x|)) ^ p.α))

theorem datumBound_nonneg (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hbdd : BddAbove (Set.range fun x => |u₀ x|)) :
    (0 : ℝ) ≤ datumBound p u₀ := by
  unfold datumBound
  have hB := datum_sSup_nonneg hbdd
  have hrpow : (0 : ℝ) ≤ (sSup (Set.range fun x => |u₀ x|)) ^ p.α := Real.rpow_nonneg hB _
  have hfac : (0 : ℝ) ≤ p.a + p.b * (sSup (Set.range fun x => |u₀ x|)) ^ p.α :=
    add_nonneg p.ha (mul_nonneg p.hb hrpow)
  have : (0 : ℝ) ≤ sSup (Set.range fun x => |u₀ x|)
      * (p.a + p.b * (sSup (Set.range fun x => |u₀ x|)) ^ p.α) := mul_nonneg hB hfac
  linarith

/-- Continuity of the lift on `[0,1]` from subtype continuity of `u₀`. -/
theorem lift_continuousOn_Icc {w : intervalDomainPoint → ℝ}
    (hw : Continuous w) :
    ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift w) = w := by
    funext ⟨y, hy⟩
    simp only [Set.restrict_apply, intervalDomainLift]
    rw [dif_pos hy]
    exact congr_arg w (Subtype.ext rfl)
  rw [heq]; exact hw

/-- Nonnegativity of the lifted datum on the **closed** `[0,1]`: positivity holds on
the open interior `Ioo 0 1` (PID), and continuity closes it to `≥ 0` at the
endpoints (`Icc 0 1 = closure (Ioo 0 1)`). -/
theorem lift_nonneg_of_pos_interior {u₀ : intervalDomainPoint → ℝ}
    (hcont : Continuous u₀)
    (hpos : ∀ x, x ∈ intervalDomain.inside → 0 < u₀ x) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u₀ x := by
  -- `0 ≤ lift u₀` on the interior `Ioo 0 1`
  have hnn_int : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ intervalDomainLift u₀ x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
    simp only [intervalDomainLift, dif_pos hxIcc]
    exact (hpos ⟨x, hxIcc⟩ hx).le
  -- continuity of the lift on `[0,1]`
  have hcontLift : ContinuousOn (intervalDomainLift u₀) (Set.Icc (0 : ℝ) 1) :=
    lift_continuousOn_Icc hcont
  -- close to `[0,1] = closure (Ioo 0 1)` via a sequence in the interior
  intro x hx
  have hclos : x ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]; exact hx
  rw [mem_closure_iff_seq_limit] at hclos
  obtain ⟨xseq, hxseq_mem, hxseq_lim⟩ := hclos
  have hcontAt : ContinuousWithinAt (intervalDomainLift u₀) (Set.Icc (0 : ℝ) 1) x :=
    hcontLift x hx
  have hlim : Filter.Tendsto (fun n => intervalDomainLift u₀ (xseq n))
      Filter.atTop (nhds (intervalDomainLift u₀ x)) := by
    apply hcontAt.tendsto.comp
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hxseq_lim, Filter.Eventually.of_forall
      (fun n => Set.Ioo_subset_Icc_self (hxseq_mem n))⟩
  have hb : ∀ n, (0 : ℝ) ≤ intervalDomainLift u₀ (xseq n) :=
    fun n => hnn_int (xseq n) (hxseq_mem n)
  exact ge_of_tendsto' hlim hb

/-- **R-src0F-1a/1b.**  The datum-side coefficient bound with the concrete witness
`datumBound p u₀ = 2·(B·(a + b·Bᵅ))`, `B = sSup (range |u₀|)`. -/
theorem datum_source_coeff_bound (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hcont : Continuous u₀)
    (hbdd : BddAbove (Set.range fun x => |u₀ x|))
    (hpos : ∀ x, x ∈ intervalDomain.inside → 0 < u₀ x) :
    ∀ k, |cosineCoeffs (logisticLifted p u₀) k| ≤ datumBound p u₀ := by
  set B := sSup (Set.range fun x => |u₀ x|) with hBdef
  have hB0 : 0 ≤ B := datum_sSup_nonneg hbdd
  -- continuity of the lifted logistic source on [0,1]
  have hcontLift : ContinuousOn (intervalDomainLift u₀) (Set.Icc (0 : ℝ) 1) :=
    lift_continuousOn_Icc hcont
  have hnn : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u₀ x :=
    lift_nonneg_of_pos_interior hcont hpos
  have hbd : ∀ x ∈ Set.Icc (0 : ℝ) 1, |intervalDomainLift u₀ x| ≤ B := by
    intro x hx
    simp only [intervalDomainLift, dif_pos hx]
    exact le_csSup hbdd ⟨⟨x, hx⟩, rfl⟩
  -- the source-fun pointwise bound
  have hsrcbd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |logisticSourceFun p.a p.b p.α (intervalDomainLift u₀) x| ≤ B * (p.a + p.b * B ^ p.α) :=
    logisticSourceFun_abs_le_of_nonneg_bound hB0 p.hα p.ha p.hb hnn hbd
  -- continuity of the logistic source on [0,1]
  have hcontSrc : ContinuousOn
      (logisticSourceFun p.a p.b p.α (intervalDomainLift u₀)) (Set.Icc (0 : ℝ) 1) := by
    unfold logisticSourceFun
    apply ContinuousOn.mul hcontLift
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    exact ContinuousOn.rpow_const hcontLift (fun x _ => Or.inr p.hα.le)
  -- bridge logisticLifted = logisticSourceFun on [0,1] at the coefficient level
  intro k
  have hcoeff_eq : cosineCoeffs (logisticLifted p u₀) k
      = cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift u₀)) k :=
    ShenWork.Paper2.cosineCoeffs_congr_on_Icc
      (logisticLifted_eq_logisticSourceFun_on_Icc p u₀) k
  rw [hcoeff_eq]
  have hMa_nn : 0 ≤ B * (p.a + p.b * B ^ p.α) :=
    mul_nonneg hB0 (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg hB0 _)))
  have := cosineCoeffs_abs_le_of_continuous_bounded hcontSrc hMa_nn hsrcbd k
  unfold datumBound
  rw [← hBdef]
  linarith

/-! ## 3. Time-continuity of the patched coefficient family (R-src0F-4).

The patched slice profile is
`patchedSlice s := if s ≤ 0 then u₀ else D.u s`.
On `(0,T]` the patched coefficient is `cosineCoeffs (logisticLifted p (D.u s)) k`
and at `s ≤ 0` it is `cosineCoeffs (logisticLifted p u₀) k`.

The coefficient functional is `2`-Lipschitz in the slice sup norm
(`cosineCoeffs_dist_le_of_sup`) and the lifted logistic source is locally Lipschitz
in the slice on bounded nonnegative profiles (`logisticLifted_slice_dist_le`).  So
continuity in `s` reduces to the sup-norm time continuity of the patched slice
profile — the genuine analytic input (interior slice time continuity of the mild
trajectory + the `s = 0⁺` initial approach), isolated as the named hypothesis
`hsliceTC` below. -/

/-- The patched slice profile: the initial datum for `s ≤ 0`, the mild slice for
`s > 0`. -/
noncomputable def patchedSlice (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) : intervalDomainPoint → ℝ :=
  if s ≤ 0 then u₀ else u s

theorem patchedSlice_of_nonpos (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) {s : ℝ} (hs : s ≤ 0) :
    patchedSlice u₀ u s = u₀ := by simp [patchedSlice, hs]

theorem patchedSlice_of_pos (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) {s : ℝ} (hs : 0 < s) :
    patchedSlice u₀ u s = u s := by simp [patchedSlice, not_le.mpr hs]

/-- `patchedSource = cosineCoeffs (logisticLifted (patchedSlice ·)) ·`. -/
theorem patchedSource_eq_coeff_slice (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) (k : ℕ) :
    ShenWork.IntervalPicardLimitBddProducer.patchedSource p u₀ u s k
      = cosineCoeffs (logisticLifted p (patchedSlice u₀ u s)) k := by
  unfold ShenWork.IntervalPicardLimitBddProducer.patchedSource patchedSlice
  split_ifs <;> rfl

/-- Continuity on `[0,1]` of the lifted logistic source of the patched slice. -/
theorem logisticLifted_patchedSlice_continuousOn (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ} (D : GradientMildSolutionData p u₀)
    (hu₀cont : Continuous u₀) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) D.T) :
    ContinuousOn (logisticLifted p (patchedSlice u₀ D.u t)) (Set.Icc (0 : ℝ) 1) := by
  have hcont_profile : Continuous (patchedSlice u₀ D.u t) := by
    rcases eq_or_lt_of_le ht.1 with ht0 | ht0
    · rw [patchedSlice_of_nonpos u₀ D.u (le_of_eq ht0.symm)]; exact hu₀cont
    · rw [patchedSlice_of_pos u₀ D.u ht0]; exact D.hcont t ht0 ht.2
  -- logisticLifted = logisticSourceFun (lift); continuity on [0,1]
  have hcontLift : ContinuousOn (intervalDomainLift (patchedSlice u₀ D.u t))
      (Set.Icc (0 : ℝ) 1) := lift_continuousOn_Icc hcont_profile
  have hcontSrc : ContinuousOn
      (logisticSourceFun p.a p.b p.α (intervalDomainLift (patchedSlice u₀ D.u t)))
      (Set.Icc (0 : ℝ) 1) := by
    unfold logisticSourceFun
    apply ContinuousOn.mul hcontLift
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    exact ContinuousOn.rpow_const hcontLift (fun x _ => Or.inr p.hα.le)
  exact hcontSrc.congr
    (fun x hx => logisticLifted_eq_logisticSourceFun_on_Icc p (patchedSlice u₀ D.u t) hx)

/-- **R-src0F-4 (reduced).**  Given the sup-norm time-continuity of the patched
slice profile on `[0,T]` (the isolated analytic input `hsliceTC`) together with the
uniform nonnegative ball bound on the patched profile, every patched coefficient
map is continuous on `[0,T]`.

`hsliceTC` is `Metric`-style: for every `s₀ ∈ [0,T]` and `ε > 0` there is a
`δ > 0` so that any `s ∈ [0,T]` within `δ` of `s₀` has the patched slices uniformly
(over the whole subtype domain `[0,1]`) within `ε`. -/
theorem patchedSource_continuousOn_Icc (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ} (D : GradientMildSolutionData p u₀)
    (hu₀cont : Continuous u₀)
    -- the patched profile is nonnegative and `M`-bounded on the whole domain, ∀ s
    {M : ℝ} (hMpos : 0 < M)
    (hball : ∀ s ∈ Set.Icc (0 : ℝ) D.T, ∀ y, |patchedSlice u₀ D.u s y| ≤ M)
    (hnn : ∀ s ∈ Set.Icc (0 : ℝ) D.T, ∀ y, 0 ≤ patchedSlice u₀ D.u s y)
    -- the isolated sup-norm time-continuity (genuine analytic input)
    (hsliceTC : ∀ s₀ ∈ Set.Icc (0 : ℝ) D.T, ∀ ε > 0, ∃ δ > 0,
      ∀ s ∈ Set.Icc (0 : ℝ) D.T, |s - s₀| < δ →
        ∀ y, |patchedSlice u₀ D.u s y - patchedSlice u₀ D.u s₀ y| < ε) :
    ∀ k, ContinuousOn
      (fun s => ShenWork.IntervalPicardLimitBddProducer.patchedSource p u₀ D.u s k)
      (Set.Icc 0 D.T) := by
  -- the logistic slice Lipschitz constant
  obtain ⟨Lc, hLc_pos, hLip⟩ :=
    ShenWork.IntervalPicardLimitCoeffConv.logisticLifted_slice_dist_le (p := p) hMpos
  intro k
  rw [Metric.continuousOn_iff]
  intro s₀ hs₀ ε hε
  -- target tolerance for the slice sup norm: η so that 2·Lc·η < ε
  set η : ℝ := ε / (4 * Lc) with hηdef
  have hη_pos : 0 < η := by rw [hηdef]; positivity
  obtain ⟨δ, hδ_pos, hδ⟩ := hsliceTC s₀ hs₀ η hη_pos
  refine ⟨δ, hδ_pos, ?_⟩
  intro s hs hsdist
  rw [Real.dist_eq] at hsdist
  rw [Real.dist_eq, patchedSource_eq_coeff_slice, patchedSource_eq_coeff_slice]
  -- continuity of both lifted profiles on [0,1]
  have hcont_s := logisticLifted_patchedSlice_continuousOn p D hu₀cont hs
  have hcont_s₀ := logisticLifted_patchedSlice_continuousOn p D hu₀cont hs₀
  -- pointwise logistic-lifted slice distance bound on [0,1]
  have hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |logisticLifted p (patchedSlice u₀ D.u s) x
        - logisticLifted p (patchedSlice u₀ D.u s₀) x| ≤ Lc * η := by
    intro x hx
    have hxlt : |patchedSlice u₀ D.u s ⟨x, hx⟩ - patchedSlice u₀ D.u s₀ ⟨x, hx⟩| ≤ η :=
      (hδ s hs hsdist ⟨x, hx⟩).le
    calc |logisticLifted p (patchedSlice u₀ D.u s) x
              - logisticLifted p (patchedSlice u₀ D.u s₀) x|
        ≤ Lc * |patchedSlice u₀ D.u s ⟨x, hx⟩ - patchedSlice u₀ D.u s₀ ⟨x, hx⟩| :=
          hLip (patchedSlice u₀ D.u s) (patchedSlice u₀ D.u s₀)
            (hball s hs) (hnn s hs) (hball s₀ hs₀) (hnn s₀ hs₀) hx
      _ ≤ Lc * η := mul_le_mul_of_nonneg_left hxlt hLc_pos.le
  -- coefficient 2-Lipschitz: |coeff s − coeff s₀| ≤ 2·(Lc·η)
  have hLcη_nn : (0 : ℝ) ≤ Lc * η := mul_nonneg hLc_pos.le hη_pos.le
  have hbound := ShenWork.IntervalPicardLimitCoeffConv.cosineCoeffs_dist_le_of_sup
    hcont_s hcont_s₀ hLcη_nn hsup k
  -- 2·Lc·η < ε  since η = ε/(4Lc)
  have hlt : 2 * (Lc * η) < ε := by
    rw [hηdef]
    have : 2 * (Lc * (ε / (4 * Lc))) = ε / 2 := by
      field_simp
      ring
    rw [this]; linarith
  exact lt_of_le_of_lt hbound hlt

end ShenWork.IntervalPicardLimitBddHcontP
