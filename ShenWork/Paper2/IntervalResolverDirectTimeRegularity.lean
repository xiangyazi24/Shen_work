/-
  ShenWork/Paper2/IntervalResolverDirectTimeRegularity.lean

  **V-side time regularity DIRECTLY from the resolver spectral structure.**

  The chemical concentration `v(t,x) = R(u(t))(x) = ∑ v̂_k(t) cos(kπx)` where
  `v̂_k(t) = â_k(t) · w_k` with `w_k = 1/(μ + λ_k)` the resolver weight and
  `â_k` the cosine coefficients of the source `ν · u(t)^γ`.

  Given `DuhamelSourceTimeC1` of the source coefficients `â_k(t)`, we derive:

  1. **HasDerivAt** of the resolver series in time — from
     `hasDerivAt_tsum_of_isPreconnected` with the summable per-mode derivative
     bound `|v̂'_k · cos| ≤ derivBound · w_k`.

  2. **Joint ContinuousOn** of the time derivative on open and closed slabs —
     from `continuousOn_tsum` with the same summable bound.

  3. **Joint ContinuousOn** of the resolver value on the closed slab —
     from `continuousOn_tsum` with the summable value bound `envelope_k · w_k`.

  **Why this bypasses the restart form**: the existing `ResolverHasSpectralAgreement`
  requires `localRestartCoeff` (homogeneous + Duhamel decomposition with offset).
  The elliptic resolver has no such decomposition — it is a pure series
  `∑ c_k(t) cos(kπx)` with time-varying coefficients, no exponential decay piece.
  This file proves the v-side fields directly from that simpler structure.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.PDE.IntervalSourceCoefficientTimeC1
import ShenWork.PDE.IntervalResolverSpatialC2
import ShenWork.PDE.IntervalNeumannEllipticResolverR

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.PDE (intervalNeumannResolverWeight intervalNeumannResolver_denom_pos
  intervalNeumannResolverWeight_nonneg)
open ShenWork.PDE.ResolventEstimate (unitIntervalNeumannSpectrum_eigenvalue_nonneg)
open ShenWork.IntervalResolverSpatialC2 (resolverWeight_summable)
open ShenWork.Paper3 (unitIntervalNeumannSpectrum)
open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalResolverDirectTimeRegularity

/-! ## Hypothesis: direct resolver spectral agreement -/

/-- **Hypothesis**: the resolver `v` agrees with a weighted cosine series
`∑ a(t,k) · w_k · cos(kπx)` in a time neighborhood of each interior point,
where `a` has `DuhamelSourceTimeC1` and `w_k = 1/(μ+λ_k)`.

No restart form, no offset, no homogeneous piece.

**Per-`t₀` form** (mirrors `HasTimeNeighborhoodSpectralAgreement`): the spectral
family `a` and its `DuhamelSourceTimeC1` package are chosen PER interior time
`t₀ ∈ (0,T)`, so a soft-clamped witness (agreeing with the canonical resolver
source coefficients only on a window around `t₀`) suffices.  This dissolves the
global-quantifier obstruction: the canonical source `ν·u^γ` jumps at `s = T`, so
no single GLOBAL `DuhamelSourceTimeC1` exists, but a per-`t₀` clamped one does. -/
def HasResolverDirectSpectralData
    (T : ℝ) (v : ℝ → intervalDomainPoint → ℝ) (p : CM2Params) : Prop :=
  ∀ t₀, 0 < t₀ → t₀ < T →
    ∃ (a : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC1 a),
      ∀ᶠ s in 𝓝 t₀, ∀ x : intervalDomainPoint,
        v s x = ∑' k, a s k *
          intervalNeumannResolverWeight p k * cosineMode k x.1

/-! ## Envelope nonnegativity -/

/-- The `DuhamelSourceTimeC1` envelope is nonneg: `0 ≤ envelope n`. -/
private theorem envelope_nonneg {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    (n : ℕ) : 0 ≤ src.envelope n :=
  le_trans (abs_nonneg _) (src.henv_bound 0 le_rfl n)

/-! ## Core summability lemmas -/

/-- Resolver weight upper bound: `w_k ≤ 1/μ`. -/
private theorem resolverWeight_le_inv_mu (p : CM2Params) (k : ℕ) :
    intervalNeumannResolverWeight p k ≤ 1 / p.μ := by
  unfold intervalNeumannResolverWeight
  apply div_le_div_of_nonneg_left one_pos.le p.hμ
  linarith [unitIntervalNeumannSpectrum_eigenvalue_nonneg k]

/-- The per-mode derivative bound `derivBound · w_k` is summable. -/
theorem resolverDerivBound_summable (p : CM2Params) (D : ℝ) :
    Summable (fun k : ℕ => D * intervalNeumannResolverWeight p k) :=
  (resolverWeight_summable p).mul_left D

/-- The product `envelope(k) · w_k` is summable from `Summable envelope`,
via `w_k ≤ 1/μ` and `envelope(k) ≥ 0`. -/
theorem resolverEnvelopeWeight_summable
    (p : CM2Params) {envelope : ℕ → ℝ} (henv : Summable envelope)
    (henv_nn : ∀ n, 0 ≤ envelope n) :
    Summable (fun k : ℕ =>
      envelope k * intervalNeumannResolverWeight p k) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (henv_nn k) (intervalNeumannResolverWeight_nonneg p k))
    (fun k => ?_) (henv.mul_right (1 / p.μ))
  exact mul_le_mul_of_nonneg_left (resolverWeight_le_inv_mu p k) (henv_nn k)

/-- Pointwise summability of the resolver series at `0 ≤ t` and any `x`. -/
private theorem resolverSeries_summable_at
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    (p : CM2Params) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    Summable (fun k : ℕ => a t k *
      intervalNeumannResolverWeight p k * cosineMode k x) := by
  apply Summable.of_norm_bounded
    (g := fun k => src.envelope k * intervalNeumannResolverWeight p k)
    (resolverEnvelopeWeight_summable p src.henv_summable (envelope_nonneg src))
  intro k
  rw [Real.norm_eq_abs]
  have hcos : |cosineMode k x| ≤ 1 := by
    unfold cosineMode; exact Real.abs_cos_le_one _
  calc |a t k * intervalNeumannResolverWeight p k * cosineMode k x|
      ≤ |a t k| * intervalNeumannResolverWeight p k * 1 := by
        rw [abs_mul, abs_mul,
          abs_of_nonneg (intervalNeumannResolverWeight_nonneg p k)]
        apply mul_le_mul_of_nonneg_left hcos
        exact mul_nonneg (abs_nonneg _) (intervalNeumannResolverWeight_nonneg p k)
    _ ≤ src.envelope k * intervalNeumannResolverWeight p k * 1 := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right (src.henv_bound t ht k)
            (intervalNeumannResolverWeight_nonneg p k)
        · exact one_pos.le
    _ = src.envelope k * intervalNeumannResolverWeight p k := mul_one _

/-! ## Part 1: HasDerivAt of the resolver series in time -/

/-- **HasDerivAt** for the resolver series in time.  At each `t₀ > 0`, the
series `∑ a(t,k) · w_k · cos(kπx)` has time derivative
`∑ adot(t₀,k) · w_k · cos(kπx)`.

Uses `hasDerivAt_tsum_of_isPreconnected` on `Ioi 0` with the summable
per-mode bound `|src.derivBound| · w_k`. -/
theorem resolverSeries_hasDerivAt_time
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) (p : CM2Params)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (x : ℝ) :
    HasDerivAt
      (fun t => ∑' k, a t k * intervalNeumannResolverWeight p k *
        cosineMode k x)
      (∑' k, src.adot t₀ k * intervalNeumannResolverWeight p k *
        cosineMode k x) t₀ := by
  set u := fun k : ℕ =>
    |src.derivBound| * intervalNeumannResolverWeight p k
  have hu : Summable u := resolverDerivBound_summable p |src.derivBound|
  -- HasDerivAt of each summand.
  have hg : ∀ k (t : ℝ), t ∈ Ioi (0 : ℝ) →
      HasDerivAt (fun s => a s k * intervalNeumannResolverWeight p k *
        cosineMode k x)
        (src.adot t k * intervalNeumannResolverWeight p k *
          cosineMode k x) t := by
    intro k t _
    have h1 := (src.hderiv t k).mul_const
      (intervalNeumannResolverWeight p k * cosineMode k x)
    have heq : (fun s => a s k * intervalNeumannResolverWeight p k *
        cosineMode k x) =
        (fun s => a s k * (intervalNeumannResolverWeight p k * cosineMode k x)) :=
      funext (fun s => by ring)
    rw [heq, show src.adot t k * intervalNeumannResolverWeight p k *
      cosineMode k x = src.adot t k *
        (intervalNeumannResolverWeight p k * cosineMode k x) from by ring]
    exact h1
  -- Norm bound on derivative: for t ∈ Ioi 0, norm ≤ u k.
  have hg' : ∀ k (t : ℝ), t ∈ Ioi (0 : ℝ) →
      ‖src.adot t k * intervalNeumannResolverWeight p k *
        cosineMode k x‖ ≤ u k := by
    intro k t ht
    rw [Real.norm_eq_abs]
    calc |src.adot t k * intervalNeumannResolverWeight p k * cosineMode k x|
        = |src.adot t k| * intervalNeumannResolverWeight p k * |cosineMode k x| := by
          rw [abs_mul, abs_mul,
            abs_of_nonneg (intervalNeumannResolverWeight_nonneg p k)]
      _ ≤ |src.derivBound| * intervalNeumannResolverWeight p k * 1 := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right
              ((src.hderivBound t (le_of_lt (mem_Ioi.1 ht)) k).trans (le_abs_self _))
              (intervalNeumannResolverWeight_nonneg p k)
          · unfold cosineMode; exact Real.abs_cos_le_one _
          · exact abs_nonneg _
          · exact mul_nonneg (abs_nonneg _)
              (intervalNeumannResolverWeight_nonneg p k)
      _ = u k := mul_one _
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi
    isPreconnected_Ioi hg hg' (mem_Ioi.2 ht₀)
    (resolverSeries_summable_at src p ht₀.le x) (mem_Ioi.2 ht₀)

/-! ## Part 2: transfer HasDerivAt to the function v via eventuallyEq -/

/-- **HasDerivAt for v** at each interior point, given the per-`t₀` spectral data. -/
theorem resolver_direct_hasDerivAt_time
    {v : ℝ → intervalDomainPoint → ℝ} {p : CM2Params}
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hagree : ∀ᶠ s in 𝓝 t₀, ∀ x : intervalDomainPoint,
      v s x = ∑' k, a s k *
        intervalNeumannResolverWeight p k * cosineMode k x.1)
    (x : intervalDomainPoint) :
    HasDerivAt (fun s => v s x)
      (∑' k, src.adot t₀ k *
        intervalNeumannResolverWeight p k * cosineMode k x.1) t₀ :=
  (resolverSeries_hasDerivAt_time src p ht₀ x.1).congr_of_eventuallyEq
    (hagree.mono (fun _ hs => hs x))

/-- **DifferentiableAt** for the resolver in time. -/
theorem resolver_direct_differentiableAt_time
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ} {p : CM2Params}
    (H : HasResolverDirectSpectralData T v p)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (ht₀T : t₀ < T)
    (x : intervalDomainPoint) :
    DifferentiableAt ℝ (fun s => v s x) t₀ := by
  obtain ⟨a, src, hagree⟩ := H t₀ ht₀ ht₀T
  exact (resolver_direct_hasDerivAt_time src ht₀ hagree x).differentiableAt

/-! ## Part 3: ContinuousOn of the time derivative -/

/-- **ContinuousOn of the derivative series** on `Ioi 0`, for fixed `x`. -/
private theorem resolverDerivSeries_continuousOn_time
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) (p : CM2Params) (x : ℝ) :
    ContinuousOn
      (fun t => ∑' k, src.adot t k *
        intervalNeumannResolverWeight p k * cosineMode k x)
      (Ioi (0 : ℝ)) := by
  apply continuousOn_tsum
  · intro k
    have : Continuous (fun t : ℝ => src.adot t k *
        intervalNeumannResolverWeight p k * cosineMode k x) := by
      apply Continuous.mul
      · exact (src.hadotcont k).mul continuous_const
      · exact continuous_const
    exact this.continuousOn
  · exact resolverDerivBound_summable p |src.derivBound|
  · intro k t ht
    rw [Real.norm_eq_abs]
    calc |src.adot t k * intervalNeumannResolverWeight p k * cosineMode k x|
        = |src.adot t k| * intervalNeumannResolverWeight p k * |cosineMode k x| := by
          rw [abs_mul, abs_mul,
            abs_of_nonneg (intervalNeumannResolverWeight_nonneg p k)]
      _ ≤ |src.derivBound| * intervalNeumannResolverWeight p k * 1 := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right
              ((src.hderivBound t (le_of_lt (mem_Ioi.1 ht)) k).trans (le_abs_self _))
              (intervalNeumannResolverWeight_nonneg p k)
          · unfold cosineMode; exact Real.abs_cos_le_one _
          · exact abs_nonneg _
          · exact mul_nonneg (abs_nonneg _)
              (intervalNeumannResolverWeight_nonneg p k)
      _ = |src.derivBound| * intervalNeumannResolverWeight p k := mul_one _

/-- **ContinuousOn of `deriv (v · x)`** on `(0,T)`. -/
theorem resolver_direct_timeDeriv_continuousOn
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ} {p : CM2Params}
    (H : HasResolverDirectSpectralData T v p)
    (x : intervalDomainPoint) :
    ContinuousOn (fun s => deriv (fun r => v r x) s) (Ioo (0 : ℝ) T) := by
  rw [isOpen_Ioo.continuousOn_iff]
  intro t₀ ht₀
  obtain ⟨ht₀_pos, ht₀_lt⟩ := mem_Ioo.1 ht₀
  obtain ⟨a, src, hagrees⟩ := H t₀ ht₀_pos ht₀_lt
  obtain ⟨V, hV_agree, hV_open, hV_mem⟩ :=
    eventually_nhds_iff.1 hagrees
  set W := V ∩ Ioi (0 : ℝ)
  have hW_open : IsOpen W := hV_open.inter isOpen_Ioi
  have hW_mem : t₀ ∈ W := ⟨hV_mem, mem_Ioi.2 ht₀_pos⟩
  -- For every t ∈ W, the agreement holds in a time neighborhood.
  have hagree_at : ∀ t ∈ W, ∀ᶠ s in 𝓝 t, ∀ y : intervalDomainPoint,
      v s y = ∑' k, a s k * intervalNeumannResolverWeight p k *
        cosineMode k y.1 :=
    fun t ht => eventually_of_mem (hW_open.mem_nhds ht)
      (fun s hs => hV_agree s hs.1)
  -- Deriv identity on W.
  have hderiv_eq : ∀ t ∈ W,
      deriv (fun s => v s x) t =
        ∑' k, src.adot t k * intervalNeumannResolverWeight p k *
          cosineMode k x.1 := by
    intro t ht
    have ht_pos : 0 < t := mem_Ioi.1 ht.2
    have hseries := resolverSeries_hasDerivAt_time src p ht_pos x.1
    exact (hseries.congr_of_eventuallyEq
      ((hagree_at t ht).mono (fun _ hs => hs x))).deriv
  -- ContinuousAt of the spectral derivative at t₀.
  have hcont := resolverDerivSeries_continuousOn_time src p x.1
  have hca : ContinuousAt
      (fun t => ∑' k, src.adot t k * intervalNeumannResolverWeight p k *
        cosineMode k x.1) t₀ :=
    hcont.continuousAt (isOpen_Ioi.mem_nhds (mem_Ioi.2 ht₀_pos))
  exact hca.congr (eventually_of_mem (hW_open.mem_nhds hW_mem)
    (fun t ht => (hderiv_eq t ht).symm))

/-! ## Part 4: Joint (t,x) continuity of the derivative series -/

/-- **Joint ContinuousOn of the derivative series** on `Ioi 0 ×ˢ univ`. -/
private theorem resolverDerivSeries_jointContinuousOn
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) (p : CM2Params) :
    ContinuousOn
      (fun q : ℝ × ℝ => ∑' k, src.adot q.1 k *
        intervalNeumannResolverWeight p k * cosineMode k q.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  apply continuousOn_tsum
  · intro k
    apply ContinuousOn.mul
    · exact ((src.hadotcont k).comp continuous_fst |>.mul
        continuous_const).continuousOn
    · exact (Real.continuous_cos.comp
        (continuous_const.mul continuous_snd)).continuousOn
  · exact resolverDerivBound_summable p |src.derivBound|
  · intro k q hq
    obtain ⟨ht, _⟩ := mem_prod.1 hq
    rw [Real.norm_eq_abs]
    calc |src.adot q.1 k * intervalNeumannResolverWeight p k * cosineMode k q.2|
        = |src.adot q.1 k| * intervalNeumannResolverWeight p k * |cosineMode k q.2| := by
          rw [abs_mul, abs_mul,
            abs_of_nonneg (intervalNeumannResolverWeight_nonneg p k)]
      _ ≤ |src.derivBound| * intervalNeumannResolverWeight p k * 1 := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right
              ((src.hderivBound q.1 (le_of_lt (mem_Ioi.1 ht)) k).trans (le_abs_self _))
              (intervalNeumannResolverWeight_nonneg p k)
          · unfold cosineMode; exact Real.abs_cos_le_one _
          · exact abs_nonneg _
          · exact mul_nonneg (abs_nonneg _)
              (intervalNeumannResolverWeight_nonneg p k)
      _ = |src.derivBound| * intervalNeumannResolverWeight p k := mul_one _

/-- **Joint ContinuousOn of the value series** on `Ioi 0 ×ˢ univ`. -/
private theorem resolverValueSeries_jointContinuousOn
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a) (p : CM2Params) :
    ContinuousOn
      (fun q : ℝ × ℝ => ∑' k, a q.1 k *
        intervalNeumannResolverWeight p k * cosineMode k q.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  apply continuousOn_tsum
  · intro k
    have ha_cont : Continuous (fun t : ℝ => a t k) :=
      continuous_iff_continuousAt.2 (fun t => (src.hderiv t k).continuousAt)
    apply ContinuousOn.mul
    · exact (ha_cont.comp continuous_fst |>.mul continuous_const).continuousOn
    · exact (Real.continuous_cos.comp
        (continuous_const.mul continuous_snd)).continuousOn
  · exact resolverEnvelopeWeight_summable p src.henv_summable (envelope_nonneg src)
  · intro k q hq
    obtain ⟨ht, _⟩ := mem_prod.1 hq
    rw [Real.norm_eq_abs]
    calc |a q.1 k * intervalNeumannResolverWeight p k * cosineMode k q.2|
        = |a q.1 k| * intervalNeumannResolverWeight p k * |cosineMode k q.2| := by
          rw [abs_mul, abs_mul,
            abs_of_nonneg (intervalNeumannResolverWeight_nonneg p k)]
      _ ≤ src.envelope k * intervalNeumannResolverWeight p k * 1 := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right
              (src.henv_bound q.1 (le_of_lt (mem_Ioi.1 ht)) k)
              (intervalNeumannResolverWeight_nonneg p k)
          · unfold cosineMode; exact Real.abs_cos_le_one _
          · exact abs_nonneg _
          · exact mul_nonneg (envelope_nonneg src k)
              (intervalNeumannResolverWeight_nonneg p k)
      _ = src.envelope k * intervalNeumannResolverWeight p k := mul_one _

/-! ## Part 5: v-side frontier fields from HasResolverDirectSpectralData -/

/-- **V-side time differentiability + derivative continuity** from
`HasResolverDirectSpectralData`. -/
theorem resolver_direct_timeSlices
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ} {p : CM2Params}
    (H : HasResolverDirectSpectralData T v p)
    (x : intervalDomainPoint) :
    (∀ t ∈ Ioo (0 : ℝ) T,
      DifferentiableAt ℝ (fun s => v s x) t) ∧
    ContinuousOn (fun s => deriv (fun r => v r x) s) (Ioo (0 : ℝ) T) :=
  ⟨fun _ ht => resolver_direct_differentiableAt_time H ht.1 ht.2 x,
   resolver_direct_timeDeriv_continuousOn H x⟩

/-- **Helper**: the intervalDomainLift agrees with the series for t ∈ Wt, x ∈ Icc. -/
private theorem intervalDomainLift_resolverSeries_agree
    {a : ℝ → ℕ → ℝ} {v : ℝ → intervalDomainPoint → ℝ} {p : CM2Params}
    {V : Set ℝ} (hV_agree : ∀ s ∈ V, ∀ y : intervalDomainPoint,
      v s y = ∑' k, a s k * intervalNeumannResolverWeight p k *
        cosineMode k y.1)
    {t : ℝ} (ht : t ∈ V) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    intervalDomainLift (v t) x =
      ∑' k, a t k * intervalNeumannResolverWeight p k * cosineMode k x := by
  simp only [intervalDomainLift, hx, dif_pos]
  exact hV_agree t ht ⟨x, hx⟩

/-- **V-side joint time-derivative continuity on the open slab**
`Ioo 0 T ×ˢ Ioo 0 1`. -/
theorem resolver_direct_jointTimeDerivInterior
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ} {p : CM2Params}
    (H : HasResolverDirectSpectralData T v p) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s => intervalDomainLift (v s) x) t))
      (Ioo (0 : ℝ) T ×ˢ Ioo (0 : ℝ) 1) := by
  intro ⟨t₀, x₀⟩ hp
  obtain ⟨ht₀, hx₀⟩ := mem_prod.1 hp
  obtain ⟨ht₀_pos, ht₀_lt⟩ := mem_Ioo.1 ht₀
  obtain ⟨a, src, hagrees⟩ := H t₀ ht₀_pos ht₀_lt
  obtain ⟨V, hV_agree, hV_open, hV_mem⟩ :=
    eventually_nhds_iff.1 hagrees
  set Wt := V ∩ Ioi (0 : ℝ)
  have hWt_open : IsOpen Wt := hV_open.inter isOpen_Ioi
  have hWt_mem : t₀ ∈ Wt := ⟨hV_mem, mem_Ioi.2 ht₀_pos⟩
  -- Spectral derivative field G.
  set G : ℝ × ℝ → ℝ := fun q =>
    ∑' k, src.adot q.1 k * intervalNeumannResolverWeight p k *
      cosineMode k q.2
  -- Deriv of lift equals G on Wt × Icc 0 1.
  have hderiv_eq : ∀ t ∈ Wt, ∀ x ∈ Icc (0 : ℝ) 1,
      deriv (fun s => intervalDomainLift (v s) x) t = G (t, x) := by
    intro t ht x hx
    have ht_pos : 0 < t := mem_Ioi.1 ht.2
    have hagree_lift : ∀ᶠ s in 𝓝 t,
        intervalDomainLift (v s) x =
          ∑' k, a s k * intervalNeumannResolverWeight p k * cosineMode k x :=
      eventually_of_mem (hWt_open.mem_nhds ht)
        (fun s hs => intervalDomainLift_resolverSeries_agree
          (fun s' hs' => hV_agree s' hs'.1) hs hx)
    exact ((resolverSeries_hasDerivAt_time src p ht_pos x).congr_of_eventuallyEq
      hagree_lift).deriv
  -- G is ContinuousAt at (t₀, x₀).
  have hG_ca : ContinuousAt G (t₀, x₀) :=
    (resolverDerivSeries_jointContinuousOn src p).continuousAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (mem_prod.2 ⟨mem_Ioi.2 ht₀_pos, mem_univ _⟩))
  -- Transfer via eventuallyEq.
  set S := Ioo (0 : ℝ) T ×ˢ Ioo (0 : ℝ) 1
  have hWt_nhds : Wt ×ˢ (univ : Set ℝ) ∈ 𝓝 (t₀, x₀) :=
    (hWt_open.prod isOpen_univ).mem_nhds (mem_prod.2 ⟨hWt_mem, mem_univ _⟩)
  have heventual :
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        deriv (fun s => intervalDomainLift (v s) x) t)) =ᶠ[𝓝[S] (t₀, x₀)]
        (fun q => G q) :=
    Filter.mem_inf_of_inter hWt_nhds (mem_principal_self S)
      (fun ⟨t, x⟩ ⟨hW, hS'⟩ => by
        obtain ⟨htWt, _⟩ := mem_prod.1 hW
        obtain ⟨_, hxIoo⟩ := mem_prod.1 hS'
        exact hderiv_eq t htWt x (Ioo_subset_Icc_self hxIoo))
  exact (hG_ca.continuousWithinAt).congr_of_eventuallyEq heventual
    (hderiv_eq t₀ hWt_mem x₀ (Ioo_subset_Icc_self hx₀))

/-- **V-side joint time-derivative continuity on the closed slab**
`Ioo 0 T ×ˢ Icc 0 1`. -/
theorem resolver_direct_jointTimeDerivClosed
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ} {p : CM2Params}
    (H : HasResolverDirectSpectralData T v p) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s => intervalDomainLift (v s) x) t))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
  intro ⟨t₀, x₀⟩ hp
  obtain ⟨ht₀, hx₀⟩ := mem_prod.1 hp
  obtain ⟨ht₀_pos, ht₀_lt⟩ := mem_Ioo.1 ht₀
  obtain ⟨a, src, hagrees⟩ := H t₀ ht₀_pos ht₀_lt
  obtain ⟨V, hV_agree, hV_open, hV_mem⟩ :=
    eventually_nhds_iff.1 hagrees
  set Wt := V ∩ Ioi (0 : ℝ)
  have hWt_open : IsOpen Wt := hV_open.inter isOpen_Ioi
  have hWt_mem : t₀ ∈ Wt := ⟨hV_mem, mem_Ioi.2 ht₀_pos⟩
  set G : ℝ × ℝ → ℝ := fun q =>
    ∑' k, src.adot q.1 k * intervalNeumannResolverWeight p k *
      cosineMode k q.2
  have hderiv_eq : ∀ t ∈ Wt, ∀ x ∈ Icc (0 : ℝ) 1,
      deriv (fun s => intervalDomainLift (v s) x) t = G (t, x) := by
    intro t ht x hx
    have ht_pos : 0 < t := mem_Ioi.1 ht.2
    have hagree_lift : ∀ᶠ s in 𝓝 t,
        intervalDomainLift (v s) x =
          ∑' k, a s k * intervalNeumannResolverWeight p k * cosineMode k x :=
      eventually_of_mem (hWt_open.mem_nhds ht)
        (fun s hs => intervalDomainLift_resolverSeries_agree
          (fun s' hs' => hV_agree s' hs'.1) hs hx)
    exact ((resolverSeries_hasDerivAt_time src p ht_pos x).congr_of_eventuallyEq
      hagree_lift).deriv
  have hG_ca : ContinuousAt G (t₀, x₀) :=
    (resolverDerivSeries_jointContinuousOn src p).continuousAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (mem_prod.2 ⟨mem_Ioi.2 ht₀_pos, mem_univ _⟩))
  set S := Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1
  have hWt_nhds : Wt ×ˢ (univ : Set ℝ) ∈ 𝓝 (t₀, x₀) :=
    (hWt_open.prod isOpen_univ).mem_nhds (mem_prod.2 ⟨hWt_mem, mem_univ _⟩)
  have heventual :
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        deriv (fun s => intervalDomainLift (v s) x) t)) =ᶠ[𝓝[S] (t₀, x₀)]
        (fun q => G q) :=
    Filter.mem_inf_of_inter hWt_nhds (mem_principal_self S)
      (fun ⟨t, x⟩ ⟨hW, hS'⟩ => by
        obtain ⟨htWt, _⟩ := mem_prod.1 hW
        obtain ⟨_, hxIcc⟩ := mem_prod.1 hS'
        exact hderiv_eq t htWt x hxIcc)
  exact (hG_ca.continuousWithinAt).congr_of_eventuallyEq heventual
    (hderiv_eq t₀ hWt_mem x₀ hx₀)

/-- **V-side joint solution continuity on the closed slab**
`Ioo 0 T ×ˢ Icc 0 1`. -/
theorem resolver_direct_jointSolutionClosed
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ} {p : CM2Params}
    (H : HasResolverDirectSpectralData T v p) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
  intro ⟨t₀, x₀⟩ hp
  obtain ⟨ht₀, hx₀⟩ := mem_prod.1 hp
  obtain ⟨ht₀_pos, ht₀_lt⟩ := mem_Ioo.1 ht₀
  obtain ⟨a, src, hagrees⟩ := H t₀ ht₀_pos ht₀_lt
  obtain ⟨V, hV_agree, hV_open, hV_mem⟩ :=
    eventually_nhds_iff.1 hagrees
  set Wt := V ∩ Ioi (0 : ℝ)
  have hWt_open : IsOpen Wt := hV_open.inter isOpen_Ioi
  have hWt_mem : t₀ ∈ Wt := ⟨hV_mem, mem_Ioi.2 ht₀_pos⟩
  set F : ℝ × ℝ → ℝ := fun q =>
    ∑' k, a q.1 k * intervalNeumannResolverWeight p k * cosineMode k q.2
  have hvalue_eq : ∀ t ∈ Wt, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (v t) x = F (t, x) := by
    intro t ht x hx
    exact intervalDomainLift_resolverSeries_agree
      (fun s' hs' => hV_agree s' hs'.1) ht hx
  have hF_ca : ContinuousAt F (t₀, x₀) :=
    (resolverValueSeries_jointContinuousOn src p).continuousAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (mem_prod.2 ⟨mem_Ioi.2 ht₀_pos, mem_univ _⟩))
  set S := Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1
  have hWt_nhds : Wt ×ˢ (univ : Set ℝ) ∈ 𝓝 (t₀, x₀) :=
    (hWt_open.prod isOpen_univ).mem_nhds (mem_prod.2 ⟨hWt_mem, mem_univ _⟩)
  have heventual :
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        intervalDomainLift (v t) x)) =ᶠ[𝓝[S] (t₀, x₀)]
        (fun q => F q) :=
    Filter.mem_inf_of_inter hWt_nhds (mem_principal_self S)
      (fun ⟨t, x⟩ ⟨hW, hS'⟩ => by
        obtain ⟨htWt, _⟩ := mem_prod.1 hW
        obtain ⟨_, hxIcc⟩ := mem_prod.1 hS'
        exact hvalue_eq t htWt x hxIcc)
  exact (hF_ca.continuousWithinAt).congr_of_eventuallyEq heventual
    (hvalue_eq t₀ hWt_mem x₀ hx₀)

end ShenWork.IntervalResolverDirectTimeRegularity
