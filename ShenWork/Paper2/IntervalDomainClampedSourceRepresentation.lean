/-
  ShenWork/Paper2/IntervalDomainClampedSourceRepresentation.lean

  Clamped, time-shifted representation-fed `DuhamelSourceTimeC1` producer.

  The producer `IntervalDomainLimitSourceRepresentation.limitSource_duhamelSourceTimeC1_of_representation`
  requires its per-slice cosine representation / `K2` / time-`C¹` data on a GLOBAL
  set of slice indices `σ : ℝ`.  For a trajectory `w` known to be regular only on a
  compact time window `[c', d'] ⊂ (0, T)`, those global quantifiers are
  unsatisfiable.

  This file dissolves them.  Composing the slice index with the C¹ soft clamp
  `Φ σ := φ c' c d d' (τ + σ)` of `ShenWork.PDE.IntervalTimeSoftClamp`, every slice
  index lands in the compact window `[c', d']` (`φ_mem_range`), so the per-slice
  hypotheses on `w` are required ONLY for `σ ∈ Set.Icc c' d'`.  The composed
  trajectory `σ ↦ w (Φ σ)` then satisfies the GLOBAL hypotheses of the limit-source
  producer (its slice index always lies in the window), and the time-`C¹` data
  transfers by the chain rule: `Φ' = ψ(τ + σ)` (`hasDerivAt_φ`), so the composed
  coefficient derivative is `adot (Φ σ) k · ψ(τ + σ)`, with `ψ ∈ [0,1]` giving the
  uniform bound `Mdot`.

  On the active window `τ + σ ∈ [c, d]` the clamp is the identity (`φ_eq_id_on`),
  so the clamped coefficient family agrees there with the genuine
  `w (τ + σ)` family — the downstream agreement lemma.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.Paper2.IntervalDomainLimitSourceRepresentation
import ShenWork.PDE.IntervalTimeSoftClamp

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)

noncomputable section

namespace ShenWork.Paper2.ClampedSourceRepresentation

open ShenWork.IntervalTimeSoftClamp

/-- **Clamped, time-shifted representation-fed `DuhamelSourceTimeC1`.**

For a trajectory `w` whose per-slice cosine representation / `K2` sup-gradient-Hessian
bounds / time-`C¹` coefficient data are known ONLY on the compact window
`[c', d'] ⊂ (0, T)`, this produces the `DuhamelSourceTimeC1` package for the
CLAMPED source family

    `σ ↦ k ↦ cosineCoeffs (logisticSourceFun a b α (lift (w (φ c' c d d' (τ + σ))))) k`,

whose slice index `Φ σ := φ c' c d d' (τ + σ)` always lies in `[c', d']`
(`φ_mem_range`).  The composed trajectory `wc σ := w (Φ σ)` satisfies the GLOBAL
hypotheses of `limitSource_duhamelSourceTimeC1_of_representation`, and the
time-`C¹` data transfers by the chain rule (inner derivative `ψ (τ + σ)`). -/
noncomputable def clampedSource_duhamelSourceTimeC1
    (p : CM2Params) (w : ℝ → intervalDomainPoint → ℝ)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    -- clamp parameters
    {τ c' c d d' : ℝ} (hc' : c' < c) (hcd : c ≤ d) (hd' : d < d')
    {M G1 G2 : ℝ}
    -- per-slice cosine representation, required ONLY on the window
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ ∈ Set.Icc c' d', Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ ∈ Set.Icc c' d', Set.EqOn (intervalDomainLift (w σ))
        (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    -- K2 slice bounds on the window
    (hpos : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (w σ) x)
    (hub : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (w σ) x ≤ M)
    (hG1 : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (w σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (w σ))) x| ≤ G2)
    -- K1 time-C¹ data on the window
    (adot : ℝ → ℕ → ℝ)
    (hderiv : ∀ σ ∈ Set.Icc c' d', ∀ k, HasDerivAt
      (fun r => cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (w r))) k)
      (adot σ k) σ)
    (hadotcont : ∀ k, ContinuousOn (fun σ => adot σ k) (Set.Icc c' d'))
    {Mdot : ℝ} (hMdot : ∀ σ ∈ Set.Icc c' d', ∀ k, |adot σ k| ≤ Mdot) :
    DuhamelSourceTimeC1
      (fun σ k => cosineCoeffs (logisticSourceFun p.a p.b p.α
        (intervalDomainLift (w (ShenWork.IntervalTimeSoftClamp.φ c' c d d' (τ + σ))))) k) := by
  -- The clamped slice index and the composed trajectory.
  set Φ : ℝ → ℝ := fun σ => φ c' c d d' (τ + σ) with hΦ
  have hΦmem : ∀ σ, Φ σ ∈ Set.Icc c' d' := fun σ => φ_mem_range hc' hcd hd' (τ + σ)
  set wc : ℝ → intervalDomainPoint → ℝ := fun σ => w (Φ σ) with hwc
  -- Inner derivative of `Φ`: `Φ' σ = ψ (τ + σ)` (clamp FTC ∘ affine shift).
  have hΦderiv : ∀ σ, HasDerivAt Φ (ψ c' c d d' (τ + σ)) σ := by
    intro σ
    have hshift : HasDerivAt (fun s : ℝ => τ + s) 1 σ := (hasDerivAt_id σ).const_add τ
    have h := (hasDerivAt_φ (c' := c') (c := c) (d := d) (d' := d') (τ + σ)).comp σ hshift
    simpa [Φ, hΦ, Function.comp, mul_one] using h
  -- Composed time derivative of each coefficient: `adot (Φ σ) k · ψ (τ + σ)`.
  set adotc : ℝ → ℕ → ℝ := fun σ k => adot (Φ σ) k * ψ c' c d d' (τ + σ) with hadotc
  -- `Mdot ≥ 0` (window nonempty: `c' ∈ [c', d']`).
  have hc'mem : c' ∈ Set.Icc c' d' := ⟨le_rfl, by linarith [hc'.le, hd'.le]⟩
  have hMdot_nn : 0 ≤ Mdot := le_trans (abs_nonneg _) (hMdot c' hc'mem 0)
  -- Globalized hypotheses for the composed trajectory `wc`.
  have hbsum' : ∀ σ, Summable (fun n => unitIntervalCosineEigenvalue n * |bc (Φ σ) n|) :=
    fun σ => hbsum (Φ σ) (hΦmem σ)
  have hagree' : ∀ σ, Set.EqOn (intervalDomainLift (wc σ))
      (fun x => ∑' n, bc (Φ σ) n * cosineMode n x) (Set.Icc (0 : ℝ) 1) :=
    fun σ => hagree (Φ σ) (hΦmem σ)
  have hpos' : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (wc σ) x :=
    fun σ => hpos (Φ σ) (hΦmem σ)
  have hub' : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (wc σ) x ≤ M :=
    fun σ => hub (Φ σ) (hΦmem σ)
  have hG1' : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (wc σ)) x| ≤ G1 :=
    fun σ => hG1 (Φ σ) (hΦmem σ)
  have hG2' : ∀ σ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (wc σ))) x| ≤ G2 :=
    fun σ => hG2 (Φ σ) (hΦmem σ)
  -- Composed time-`C¹` derivative via the chain rule.
  have hderiv' : ∀ σ k, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (wc r))) k) (adotc σ k) σ := by
    intro σ k
    have houter := hderiv (Φ σ) (hΦmem σ) k
    have h := houter.comp σ (hΦderiv σ)
    -- `h : HasDerivAt ((coeff ∘ w) ∘ Φ) (adot (Φ σ) k * ψ (τ+σ)) σ`
    have hfun : (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (wc r))) k)
        = (fun s => cosineCoeffs
            (logisticSourceFun p.a p.b p.α (intervalDomainLift (w s))) k) ∘ Φ := by
      funext r; simp [wc, Function.comp]
    rw [hfun]
    simpa [adotc, hadotc] using h
  -- Continuity of the composed derivative coefficients.
  have hΦcont : Continuous Φ :=
    φ_continuous.comp (continuous_const.add continuous_id)
  have hadotcont' : ∀ k, Continuous (fun σ => adotc σ k) := by
    intro k
    have h1 : Continuous (fun σ => adot (Φ σ) k) :=
      (hadotcont k).comp_continuous hΦcont (fun σ => hΦmem σ)
    have h2 : Continuous (fun σ => ψ c' c d d' (τ + σ)) :=
      ψ_continuous.comp (continuous_const.add continuous_id)
    simpa [adotc, hadotc] using h1.mul h2
  -- Uniform bound on the composed derivative coefficients (`|adot · ψ| ≤ Mdot · 1`).
  have hMdot' : ∀ σ, 0 ≤ σ → ∀ k, |adotc σ k| ≤ Mdot := by
    intro σ _ k
    rw [hadotc]
    rw [abs_mul, abs_of_nonneg (ψ_nonneg (τ + σ))]
    calc |adot (Φ σ) k| * ψ c' c d d' (τ + σ)
        ≤ Mdot * 1 := by
          apply mul_le_mul (hMdot (Φ σ) (hΦmem σ) k) (ψ_le_one (τ + σ))
            (ψ_nonneg (τ + σ)) hMdot_nn
      _ = Mdot := mul_one _
  -- Assemble through the limit-source producer for the composed trajectory `wc`.
  have hpkg := ShenWork.IntervalDomainLimitSourceRepresentation.limitSource_duhamelSourceTimeC1_of_representation
    p wc hα ha hb (fun σ => bc (Φ σ)) hbsum' hagree' hpos' hub' hG1' hG2'
    adotc hderiv' hadotcont' hMdot'
  -- The producer's output family is `cosineCoeffs (logisticLifted p (wc s))`; rewrite
  -- it to the `logisticSourceFun ∘ lift` shape (equal cosine coeffs, `[0,1]`-agreement).
  have hfam : (fun s k =>
        cosineCoeffs (ShenWork.IntervalGradientDuhamelMap.logisticLifted p (wc s)) k)
      = (fun σ k => cosineCoeffs (logisticSourceFun p.a p.b p.α
          (intervalDomainLift (w (Φ σ)))) k) := by
    funext s k
    exact ShenWork.Paper2.cosineCoeffs_congr_on_Icc
      (ShenWork.IntervalMildPicardRegularity.logisticLifted_eq_logisticSourceFun_on_Icc p (wc s)) k
  rw [hfam] at hpkg
  simpa [Φ, hΦ] using hpkg

/-- **Agreement on the active window.**  Where `τ + σ ∈ [c, d]` the clamp is the
identity (`φ_eq_id_on`), so the clamped source coefficient family agrees pointwise
(in `k`) with the genuine `w (τ + σ)` source coefficient family. -/
theorem clampedFamily_eq_on
    (p : CM2Params) (w : ℝ → intervalDomainPoint → ℝ)
    {τ c' c d d' : ℝ} (hc' : c' < c) (hd' : d < d')
    {σ : ℝ} (hσ : τ + σ ∈ Set.Icc c d) (k : ℕ) :
    cosineCoeffs (logisticSourceFun p.a p.b p.α
        (intervalDomainLift (w (ShenWork.IntervalTimeSoftClamp.φ c' c d d' (τ + σ))))) k
      = cosineCoeffs (logisticSourceFun p.a p.b p.α (intervalDomainLift (w (τ + σ)))) k := by
  rw [ShenWork.IntervalTimeSoftClamp.φ_eq_id_on hc' hd' hσ]

end ShenWork.Paper2.ClampedSourceRepresentation
