/-
  Windowed Picard iterate regularity pass-to-limit.

  `DuhamelSourceTimeC1On` passes to pointwise limits under uniform
  derivative convergence on a closed interval `[lo, hi]`.
  This is the windowed analogue of `duhamelSourceTimeC1_of_uniform_limit`.

  The key mathematical content is proving `HasDerivWithinAt` for the limit
  from `HasDerivWithinAt` of each iterate + uniform convergence of derivatives
  on the closed interval. This is done via MVT on the convex set `Icc lo hi`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory Set Filter Asymptotics
open scoped Topology
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)

noncomputable section

namespace ShenWork.IntervalMildPicardLimitRegularityOn

/-! ### Helper: `HasDerivWithinAt` from uniform convergence on a convex set

Standard proof: for each ε > 0, pick N with sup|f'ₙ - g'| < ε/4.
MVT on the convex set gives |slope(g - fₙ)| ≤ ε/2 (via iterate-to-iterate
Lipschitz control + pointwise limit). The iterate's own derivative error
is o(|y - x|). The three terms sum to ≤ ε|y - x|. -/

private theorem hasDerivWithinAt_of_tendstoUniformlyOn_convex
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    {f' : ℕ → ℝ → ℝ} {g' : ℝ → ℝ}
    {s : Set ℝ} (hs : Convex ℝ s)
    (hconv : ∀ x ∈ s, Tendsto (fun n => f n x) atTop (nhds (g x)))
    (hderiv : ∀ n, ∀ x ∈ s, HasDerivWithinAt (f n) (f' n x) s x)
    (hunif : TendstoUniformlyOn f' g' atTop s)
    (x₀ : ℝ) (hx₀ : x₀ ∈ s) :
    HasDerivWithinAt g (g' x₀) s x₀ := by
  rw [hasDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  -- Step 1: Pick N so that |f'(n,r) - g'(r)| < c/4 for ALL n ≥ N, r ∈ s.
  have hc4 : (0 : ℝ) < c / 4 := by linarith
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨N, hN⟩ := (hunif (c / 4) hc4).exists_forall_of_atTop
  -- hN : ∀ n ≥ N, ∀ x ∈ s, dist (g' x) (f' n x) < c / 4
  -- Step 2: MVT. For n, m ≥ N, y ∈ s:
  --   ‖(fₙ y - fₘ y) - (fₙ x₀ - fₘ x₀)‖ ≤ (c/2) · ‖y - x₀‖
  have hMVT : ∀ n m, N ≤ n → N ≤ m → ∀ y ∈ s,
      ‖(f n y - f m y) - (f n x₀ - f m x₀)‖ ≤ (c / 2) * ‖y - x₀‖ := by
    intro n m hn hm y hy
    have hd : ∀ z ∈ s, HasDerivWithinAt (fun r => f n r - f m r)
        (f' n z - f' m z) s z :=
      fun z hz => (hderiv n z hz).sub (hderiv m z hz)
    have hb : ∀ z ∈ s, ‖f' n z - f' m z‖ ≤ c / 2 := by
      intro z hz
      have h1 : dist (g' z) (f' n z) < c / 4 := hN n hn z hz
      have h2 : dist (g' z) (f' m z) < c / 4 := hN m hm z hz
      rw [Real.dist_eq] at h1 h2
      rw [Real.norm_eq_abs]
      have : |f' n z - f' m z| ≤ |f' n z - g' z| + |g' z - f' m z| := by
        calc |f' n z - f' m z|
            = |(f' n z - g' z) + (g' z - f' m z)| := by ring_nf
          _ ≤ |f' n z - g' z| + |g' z - f' m z| := abs_add_le _ _
      linarith [abs_sub_comm (g' z) (f' n z)]
    exact hs.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hx₀ hy
  -- Step 3: Passage to limit m → ∞:
  --   ‖(f N y - g y) - (f N x₀ - g x₀)‖ ≤ (c/2) · ‖y - x₀‖
  have hLipLim : ∀ y ∈ s,
      ‖(f N y - g y) - (f N x₀ - g x₀)‖ ≤ (c / 2) * ‖y - x₀‖ := by
    intro y hy
    have ht : Tendsto (fun m => ‖(f N y - f m y) - (f N x₀ - f m x₀)‖)
        atTop (nhds ‖(f N y - g y) - (f N x₀ - g x₀)‖) :=
      ((tendsto_const_nhds.sub (hconv y hy)).sub
        (tendsto_const_nhds.sub (hconv x₀ hx₀))).norm
    exact le_of_tendsto ht (by
      filter_upwards [Filter.Ici_mem_atTop N] with m hm
      exact hMVT N m le_rfl hm y hy)
  -- Step 4: HasDerivWithinAt of f N at x₀ gives isLittleO control.
  have hderivN := (hderiv N x₀ hx₀).isLittleO
  rw [isLittleO_iff] at hderivN
  -- Step 5: Derivative proximity: |f'(N, x₀) - g'(x₀)| ≤ c/4.
  have hfg_x₀ : ‖f' N x₀ - g' x₀‖ ≤ c / 4 := by
    rw [Real.norm_eq_abs, abs_sub_comm, ← Real.dist_eq]
    exact (hN N le_rfl x₀ hx₀).le
  -- Step 6: Combine via triangle inequality.
  filter_upwards [hderivN hc4, self_mem_nhdsWithin] with y hN_y hy_s
  simp only [smul_eq_mul] at hN_y ⊢
  -- Decompose: g y - g x₀ - (y - x₀) * g' x₀ = three terms.
  have key : g y - g x₀ - (y - x₀) * g' x₀ =
      -((f N y - g y) - (f N x₀ - g x₀)) +
      (f N y - f N x₀ - (y - x₀) * f' N x₀) +
      (y - x₀) * (f' N x₀ - g' x₀) := by ring
  rw [key]
  calc ‖-((f N y - g y) - (f N x₀ - g x₀)) +
        (f N y - f N x₀ - (y - x₀) * f' N x₀) +
        (y - x₀) * (f' N x₀ - g' x₀)‖
      ≤ ‖-((f N y - g y) - (f N x₀ - g x₀))‖ +
        ‖f N y - f N x₀ - (y - x₀) * f' N x₀‖ +
        ‖(y - x₀) * (f' N x₀ - g' x₀)‖ := by
          linarith [norm_add_le (-((f N y - g y) - (f N x₀ - g x₀)) +
            (f N y - f N x₀ - (y - x₀) * f' N x₀))
            ((y - x₀) * (f' N x₀ - g' x₀)),
            norm_add_le (-((f N y - g y) - (f N x₀ - g x₀)))
            (f N y - f N x₀ - (y - x₀) * f' N x₀)]
    _ ≤ (c / 2) * ‖y - x₀‖ + (c / 4) * ‖y - x₀‖ + (c / 4) * ‖y - x₀‖ := by
          have h1 : ‖-((f N y - g y) - (f N x₀ - g x₀))‖ ≤ (c / 2) * ‖y - x₀‖ := by
            rw [norm_neg]; exact hLipLim y hy_s
          have h3 : ‖(y - x₀) * (f' N x₀ - g' x₀)‖ ≤ (c / 4) * ‖y - x₀‖ := by
            rw [norm_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right hfg_x₀ (norm_nonneg _)
          linarith
    _ = c * ‖y - x₀‖ := by ring

/-! ### Main theorem -/

/-- `DuhamelSourceTimeC1On` passes to pointwise limits when the derivatives
converge uniformly on `Icc lo hi`, the coefficients share a common summable
envelope, and the derivative sequence is uniformly bounded. -/
def duhamelSourceTimeC1On_of_uniform_limit
    {a : ℝ → ℕ → ℝ} {aSeq : ℕ → ℝ → ℕ → ℝ}
    {lo hi : ℝ}
    (hconv : ∀ s ∈ Icc lo hi, ∀ k, Tendsto (fun n => aSeq n s k) atTop (nhds (a s k)))
    {adotSeq : ℕ → ℝ → ℕ → ℝ}
    (hderiv_each : ∀ n, ∀ s ∈ Icc lo hi, ∀ k,
      HasDerivWithinAt (fun r => aSeq n r k) (adotSeq n s k) (Icc lo hi) s)
    {adot : ℝ → ℕ → ℝ}
    (hadot_unif : ∀ k, TendstoUniformlyOn (fun n s => adotSeq n s k)
      (fun s => adot s k) atTop (Icc lo hi))
    (hadot_cont : ∀ k, ContinuousOn (fun s => adot s k) (Icc lo hi))
    {envelope : ℕ → ℝ}
    (henv_summable : Summable envelope)
    (henv_bound : ∀ n, ∀ s ∈ Icc lo hi, ∀ k, |aSeq n s k| ≤ envelope k)
    {D : ℝ}
    (hderiv_bound : ∀ n, ∀ s ∈ Icc lo hi, ∀ k, |adotSeq n s k| ≤ D) :
    DuhamelSourceTimeC1On a lo hi where
  adot := adot
  hderiv := by
    intro s hs k
    exact hasDerivWithinAt_of_tendstoUniformlyOn_convex
      (convex_Icc lo hi)
      (fun x hx => hconv x hx k)
      (fun n x hx => hderiv_each n x hx k)
      (hadot_unif k)
      s hs
  hadotcont := hadot_cont
  envelope := envelope
  henv_summable := henv_summable
  henv_bound := by
    intro s hs k
    exact le_of_tendsto
      ((continuous_abs.tendsto _).comp (hconv s hs k))
      (Eventually.of_forall (fun n => by
        simp only [Function.comp]; exact henv_bound n s hs k))
  derivBound := D
  hderivBound := by
    intro s hs k
    exact le_of_tendsto
      ((continuous_abs.tendsto _).comp ((hadot_unif k).tendsto_at hs))
      (Eventually.of_forall (fun n => by
        simp only [Function.comp]; exact hderiv_bound n s hs k))

end ShenWork.IntervalMildPicardLimitRegularityOn
