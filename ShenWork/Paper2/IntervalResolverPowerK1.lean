/-
  ShenWork/Paper2/IntervalResolverPowerK1.lean

  **R-Hvsrc-2: the power-source `ν·u^γ` K1 time-`C¹` quadruple on the window.**

  The clamped resolver-source witness
  (`ResolverSourceClampedWitness.clampedResolverSource_duhamelSourceTimeC1`)
  consumes the time-`C¹` data of the cosine coefficients of
  `x ↦ ν·(lift (D.u σ) x)^γ`: for each window slice σ a `HasDerivAt` of
  `r ↦ cosineCoeffs (ν·lift(D.u r)^γ) n` at σ, its continuity in σ, and a
  window-uniform bound.

  This file is the `ν·u^γ` analogue of the logistic K1 quadruple
  `IntervalPicardLimitK1Weak.k1_quadruple_weak_of_subtypeCont`.  The restart
  engine `LocalRestartWeak` (built from the SAME satisfiable ledger data) already
  proves the intrinsic time-slope identity `hasDerivAt_slice`
  (`slopeSlice u r x = vSeries L (r−τ) x`), which is INDEPENDENT of the
  nonlinearity.  The power chain rule

      d/dr [ν·(lift(u r) x)^γ] = ν·γ·(lift(u r) x)^{γ−1} · slopeSlice u r x

  (via `HasDerivAt.rpow_const (Or.inl (ne_of_gt hpos))`, the POSITIVITY branch)
  then gives the per-slice derivative `resolverPowerDerivSlice`, whose joint slab
  continuity is the `rpow_const` clone of `sourceDerivSlice_continuousOn_slab`,
  and whose compact bounds give the K1 quadruple exactly as in the logistic spine.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.Paper2.IntervalPicardLimitK1Weak

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint
  intervalDomainConstExtend)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalPicardLimitRestartBdd (DuhamelSourceBddOn)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_eq_factor_mul_integral cosineCoeffs_abs_le_of_continuous_bounded)
open ShenWork.Paper2.PicardLimitK1Weak (LocalRestartWeak)

noncomputable section

namespace ShenWork.Paper2.ResolverPowerK1

open ShenWork.Paper2.PicardLimitK1 (slopeSlice)

/-- The power-source chain-rule integrand:
`ν·γ·u(σ,x)^{γ−1} · ∂_σ u(σ,x)`, the spatial slice whose cosine coefficients are
the power-source K1 derivative coefficients. -/
def resolverPowerDerivSlice (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (σ x : ℝ) : ℝ :=
  p.ν * p.γ * (intervalDomainLift (u σ) x) ^ (p.γ - 1) * slopeSlice u σ x

/-- **The power-source K1 derivative coefficients.** -/
def adotPowOf (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (σ : ℝ) (k : ℕ) : ℝ :=
  cosineCoeffs (resolverPowerDerivSlice p u σ) k

end ShenWork.Paper2.ResolverPowerK1

namespace ShenWork.Paper2.PicardLimitK1Weak.LocalRestartWeak

open ShenWork.Paper2.ResolverPowerK1 (resolverPowerDerivSlice adotPowOf)

variable {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T σ : ℝ}
  (L : LocalRestartWeak p u T σ)

/-- The power-source slice equals `ν·γ·(valueSeries)^{γ−1} · vSeries` on the
window — the `rpow` analogue of `sourceDerivSlice_eq_series`. -/
theorem resolverPowerDerivSlice_eq_series {r : ℝ} (hr : r ∈ Set.Ioo L.τ L.d)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    resolverPowerDerivSlice p u r x
      = p.ν * p.γ * (L.valueSeries (r - L.τ) x) ^ (p.γ - 1)
          * L.vSeries (r - L.τ) x := by
  unfold resolverPowerDerivSlice
  rw [L.slopeSlice_eq hr hx, L.lift_eq_valueSeries hr hx]

/-- Joint slab continuity of the power-source slice — the `rpow_const` clone of
`sourceDerivSlice_continuousOn_slab`. -/
theorem resolverPowerDerivSlice_continuousOn_slab {a' b' : ℝ}
    (hsub : Set.Icc a' b' ⊆ Set.Ioo L.τ L.d) :
    ContinuousOn (Function.uncurry (fun s x => resolverPowerDerivSlice p u s x))
      (Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1) := by
  set Φ : ℝ × ℝ → ℝ × ℝ := fun q => (q.1 - L.τ, q.2) with hΦ
  have hΦcont : Continuous Φ := (continuous_fst.sub continuous_const).prodMk continuous_snd
  have hmaps := L.shift_mapsTo hsub
  have hvS : ContinuousOn (fun q : ℝ × ℝ => L.vSeries (q.1 - L.τ) q.2)
      (Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1) :=
    (L.vSeries_jointContinuousOn.comp hΦcont.continuousOn hmaps)
  have hwS : ContinuousOn (fun q : ℝ × ℝ => L.valueSeries (q.1 - L.τ) q.2)
      (Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1) :=
    (L.valueSeries_jointContinuousOn.comp hΦcont.continuousOn hmaps)
  have hposS : ∀ q ∈ Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1,
      0 < L.valueSeries (q.1 - L.τ) q.2 := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
    rw [← L.lift_eq_valueSeries (hsub hq1) hq2]
    exact L.hpos q.1 (hsub hq1) q.2 hq2
  have hpow : ContinuousOn
      (fun q : ℝ × ℝ => (L.valueSeries (q.1 - L.τ) q.2) ^ (p.γ - 1))
      (Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1) := by
    apply ContinuousOn.rpow_const hwS
    intro q hq; exact Or.inl (ne_of_gt (hposS q hq))
  have hprod : ContinuousOn
      (fun q : ℝ × ℝ => p.ν * p.γ * (L.valueSeries (q.1 - L.τ) q.2) ^ (p.γ - 1)
        * L.vSeries (q.1 - L.τ) q.2)
      (Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1) :=
    ((continuousOn_const.mul hpow).mul hvS)
  apply hprod.congr
  intro q hq
  obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
  simp only [Function.uncurry]
  exact L.resolverPowerDerivSlice_eq_series (hsub hq1) hq2

/-- **Pointwise time derivative of the power source.**  The chain rule
`d/dr [ν·u(r,x)^γ] = resolverPowerDerivSlice` via `HasDerivAt.rpow_const`
(positivity branch). -/
theorem hasDerivAt_powerSlice {r : ℝ} (hr : r ∈ Set.Ioo L.τ L.d)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    HasDerivAt (fun s => p.ν * (intervalDomainLift (u s) x) ^ p.γ)
      (resolverPowerDerivSlice p u r x) r := by
  have hslice := L.hasDerivAt_slice hr hx
  have hpos := L.hpos r hr x hx
  -- d/dr u^γ = γ·u^{γ−1}·(∂_r u)
  have hpow : HasDerivAt (fun s => (intervalDomainLift (u s) x) ^ p.γ)
      (L.vSeries (r - L.τ) x * p.γ * (intervalDomainLift (u r) x) ^ (p.γ - 1)) r :=
    hslice.rpow_const (Or.inl (ne_of_gt hpos))
  have hmul := hpow.const_mul p.ν
  refine hmul.congr_deriv ?_
  unfold resolverPowerDerivSlice
  rw [L.slopeSlice_eq hr hx]
  ring

include L in
/-- **K1(i) for the power source.**  HasDerivAt of the coefficient family. -/
theorem hasDerivAt_powerCoeff (k : ℕ) :
    HasDerivAt
      (fun r => cosineCoeffs
        (fun x => p.ν * (intervalDomainLift (u r) x) ^ p.γ) k)
      (adotPowOf p u σ k) σ := by
  set δ : ℝ := min (σ - L.τ) (L.d - σ) / 2 with hδdef
  have hδ1 : 0 < σ - L.τ := by have := L.hστ; linarith
  have hδ2 : 0 < L.d - σ := by have := L.hσd; linarith
  have hδ : 0 < δ := by rw [hδdef]; have := lt_min hδ1 hδ2; linarith
  have hδle1 : δ ≤ (σ - L.τ) / 2 := by
    rw [hδdef]; have := min_le_left (σ - L.τ) (L.d - σ); linarith
  have hδle2 : δ ≤ (L.d - σ) / 2 := by
    rw [hδdef]; have := min_le_right (σ - L.τ) (L.d - σ); linarith
  have hball : Metric.ball σ δ ⊆ Set.Ioo L.τ L.d := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    exact ⟨by linarith [hs.1, hδle1], by linarith [hs.2, hδle2]⟩
  have hslab : Set.Icc (σ - δ) (σ + δ) ⊆ Set.Ioo L.τ L.d := by
    intro s hs
    exact ⟨by linarith [hs.1, hδle1], by linarith [hs.2, hδle2]⟩
  -- continuity of the power slice (per-slice) on a neighbourhood of σ.
  have hf_cont : ∀ᶠ s in 𝓝 σ,
      ContinuousOn (fun x => p.ν * (intervalDomainLift (u s) x) ^ p.γ)
        (Set.Icc (0:ℝ) 1) := by
    refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds L.hσ_mem) (fun s hs => ?_)
    have hrτ : 0 < s - L.τ := by have := hs.1; linarith
    have hrW : s - L.τ < L.W := by have := hs.2; have := L.hdτW; linarith
    have hval : ContinuousOn (fun x => L.valueSeries (s - L.τ) x) (Set.Icc (0:ℝ) 1) := by
      have hmaps : Set.MapsTo (fun x : ℝ => ((s - L.τ, x) : ℝ × ℝ))
          (Set.Icc (0:ℝ) 1) (Set.Ioo (0:ℝ) L.W ×ˢ Set.univ) :=
        fun x _ => Set.mem_prod.mpr ⟨Set.mem_Ioo.mpr ⟨hrτ, hrW⟩, Set.mem_univ _⟩
      exact L.valueSeries_jointContinuousOn.comp
        (continuousOn_const.prodMk continuousOn_id) hmaps
    have hpos : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < L.valueSeries (s - L.τ) x := by
      intro x hx; rw [← L.lift_eq_valueSeries hs hx]; exact L.hpos s hs x hx
    have hpow : ContinuousOn (fun x => (L.valueSeries (s - L.τ) x) ^ p.γ)
        (Set.Icc (0:ℝ) 1) :=
      hval.rpow_const (fun x hx => Or.inl (ne_of_gt (hpos x hx)))
    have hbody : ContinuousOn (fun x => p.ν * (L.valueSeries (s - L.τ) x) ^ p.γ)
        (Set.Icc (0:ℝ) 1) := continuousOn_const.mul hpow
    refine hbody.congr (fun x hx => ?_)
    rw [L.lift_eq_valueSeries hs hx]
  have hf_int : ∀ᶠ s in 𝓝 σ, IntervalIntegrable
      (fun x => p.ν * (intervalDomainLift (u s) x) ^ p.γ)
      MeasureTheory.volume (0:ℝ) 1 := by
    filter_upwards [hf_cont] with s hs
    rw [← Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    exact hs.intervalIntegrable
  have h_diff : ∀ x ∈ Set.Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball σ δ,
      HasDerivAt (fun r => p.ν * (intervalDomainLift (u r) x) ^ p.γ)
        (resolverPowerDerivSlice p u s x) s := by
    intro x hx s hs
    exact L.hasDerivAt_powerSlice (hball hs) (Set.Ioo_subset_Icc_self hx)
  have h_cont_deriv : ContinuousOn (Function.uncurry (resolverPowerDerivSlice p u))
      (Set.Icc (σ - δ) (σ + δ) ×ˢ Set.Icc (0:ℝ) 1) :=
    L.resolverPowerDerivSlice_continuousOn_slab hslab
  exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param
    (f := fun r x => p.ν * (intervalDomainLift (u r) x) ^ p.γ)
    (f' := resolverPowerDerivSlice p u) (τ := σ) (n := k)
    hδ hf_int h_diff h_cont_deriv

end ShenWork.Paper2.PicardLimitK1Weak.LocalRestartWeak

namespace ShenWork.Paper2.ResolverPowerK1

open ShenWork.Paper2.PicardLimitK1Weak.LocalRestartWeak

set_option maxHeartbeats 1600000 in
set_option linter.style.maxHeartbeats false in
/-- **The power-source K1 producer (subtype-continuity form).**  Same ledger
hypotheses as `k1_quadruple_weak_of_subtypeCont`; conclusion is the power-source
`ν·u^γ` K1 quadruple. -/
theorem powerK1_quadruple_of_subtypeCont
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (u : ℝ → intervalDomainPoint → ℝ)
    {T : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hfix : ∀ s, 0 < s → s < T → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u s) x = intervalGradientDuhamelMap p u₀ u s ⟨x, hx⟩)
    (hsrc0 : DuhamelSourceBddOn
      (ShenWork.IntervalPicardLimitBddProducer.patchedSource p u₀ u) T)
    {Msup : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < T → Set.EqOn (intervalDomainLift (u σ))
      (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x)
    (hubt : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ Msup)
    (hG1t : ∀ a' b', 0 < a' → b' < T → ∃ G1, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (u σ)) x| ≤ G1)
    (hG2t : ∀ a' b', 0 < a' → b' < T → ∃ G2, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2)
    (hLc_ce : ∀ t, 0 < t → t < T →
      ∀ s, 0 < s → s ≤ t →
        Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s)))) :
    (∀ σ, 0 < σ → σ < T → ∀ k, HasDerivAt
        (fun r => cosineCoeffs
          (fun x => p.ν * (intervalDomainLift (u r) x) ^ p.γ) k)
        (adotPowOf p u σ k) σ)
      ∧ (∀ k, ContinuousOn (fun σ => adotPowOf p u σ k) (Set.Ioo 0 T))
      ∧ (∀ a' b', 0 < a' → b' < T → ∃ Mdot, ∀ σ ∈ Set.Icc a' b',
          ∀ k, |adotPowOf p u σ k| ≤ Mdot) := by
  have mkL : ∀ σ, 0 < σ → σ < T → LocalRestartWeak p u T σ := fun σ hσ0 hσT =>
    ShenWork.Paper2.PicardLimitK1Weak.localRestartWeak_of_ledger_of_subtypeCont
      hχ0 u hα ha hb hu₀_cont hu₀_bound hfix hsrc0 bc hbsum hagree hpost hubt
      hG1t hG2t hLc_ce hσ0 hσT
  have hderiv : ∀ σ, 0 < σ → σ < T → ∀ k, HasDerivAt
      (fun r => cosineCoeffs
        (fun x => p.ν * (intervalDomainLift (u r) x) ^ p.γ) k)
      (adotPowOf p u σ k) σ :=
    fun σ hσ0 hσT k => (mkL σ hσ0 hσT).hasDerivAt_powerCoeff k
  -- Global joint continuity of the power slice on Ioo 0 T ×ˢ Icc 0 1.
  have hslice_cont : ContinuousOn (Function.uncurry (resolverPowerDerivSlice p u))
      (Set.Ioo 0 T ×ˢ Set.Icc (0:ℝ) 1) := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
    set σ₀ := q.1 with hσ₀
    have hσ₀0 : 0 < σ₀ := hq1.1
    have hσ₀T : σ₀ < T := hq1.2
    set L := mkL σ₀ hσ₀0 hσ₀T with hLdef
    set δ : ℝ := min (σ₀ - L.τ) (L.d - σ₀) / 2 with hδdef
    have hδ1 : 0 < σ₀ - L.τ := by have := L.hστ; linarith
    have hδ2 : 0 < L.d - σ₀ := by have := L.hσd; linarith
    have hδ : 0 < δ := by rw [hδdef]; have := lt_min hδ1 hδ2; linarith
    have hδle1 : δ ≤ (σ₀ - L.τ) / 2 := by
      rw [hδdef]; have := min_le_left (σ₀ - L.τ) (L.d - σ₀); linarith
    have hδle2 : δ ≤ (L.d - σ₀) / 2 := by
      rw [hδdef]; have := min_le_right (σ₀ - L.τ) (L.d - σ₀); linarith
    have hslab_sub : Set.Icc (σ₀ - δ) (σ₀ + δ) ⊆ Set.Ioo L.τ L.d := fun s hs =>
      ⟨by linarith [hs.1, hδle1], by linarith [hs.2, hδle2]⟩
    have hslabcont := L.resolverPowerDerivSlice_continuousOn_slab hslab_sub
    have hmem : q ∈ Set.Icc (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Icc (0:ℝ) 1 :=
      Set.mem_prod.mpr ⟨⟨by linarith, by linarith⟩, hq2⟩
    have hnhds : Set.Icc (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Icc (0:ℝ) 1
        ∈ 𝓝[Set.Ioo 0 T ×ˢ Set.Icc (0:ℝ) 1] q := by
      have hopen : Set.Ioo (σ₀ - δ) (σ₀ + δ) ×ˢ (Set.univ : Set ℝ) ∈ 𝓝 q := by
        apply (isOpen_Ioo.prod isOpen_univ).mem_nhds
        exact Set.mem_prod.mpr ⟨⟨by linarith, by linarith⟩, Set.mem_univ _⟩
      have hinter := Filter.inter_mem (Filter.mem_inf_of_left hopen)
        (self_mem_nhdsWithin (a := q) (s := Set.Ioo 0 T ×ˢ Set.Icc (0:ℝ) 1))
      refine Filter.mem_of_superset hinter ?_
      intro y hy
      obtain ⟨hy1, hy2⟩ := hy
      exact Set.mem_prod.mpr ⟨⟨(Set.mem_prod.mp hy1).1.1.le,
        (Set.mem_prod.mp hy1).1.2.le⟩, (Set.mem_prod.mp hy2).2⟩
    exact (hslabcont.continuousWithinAt hmem).mono_of_mem_nhdsWithin hnhds
  have hcont : ∀ k, ContinuousOn (fun σ => adotPowOf p u σ k) (Set.Ioo 0 T) := by
    intro k σ₀ hσ₀
    have hσ₀0 : 0 < σ₀ := hσ₀.1
    have hσ₀T : σ₀ < T := hσ₀.2
    set L := mkL σ₀ hσ₀0 hσ₀T with hLdef
    set δ : ℝ := min (σ₀ - L.τ) (L.d - σ₀) / 2 with hδdef
    have hδ1 : 0 < σ₀ - L.τ := by have := L.hστ; linarith
    have hδ2 : 0 < L.d - σ₀ := by have := L.hσd; linarith
    have hδ : 0 < δ := by rw [hδdef]; have := lt_min hδ1 hδ2; linarith
    have hδle1 : δ ≤ (σ₀ - L.τ) / 2 := by
      rw [hδdef]; have := min_le_left (σ₀ - L.τ) (L.d - σ₀); linarith
    have hδle2 : δ ≤ (L.d - σ₀) / 2 := by
      rw [hδdef]; have := min_le_right (σ₀ - L.τ) (L.d - σ₀); linarith
    set I : Set ℝ := Set.Icc (σ₀ - δ) (σ₀ + δ) with hIdef
    have hIsub : I ⊆ Set.Ioo L.τ L.d := fun s hs =>
      ⟨by linarith [hs.1, hδle1], by linarith [hs.2, hδle2]⟩
    have hσ₀mem : σ₀ ∈ I := ⟨by linarith, by linarith⟩
    have hslabcont := L.resolverPowerDerivSlice_continuousOn_slab hIsub
    set F : ℝ → ℝ → ℝ := fun σ x =>
      Real.cos ((k : ℝ) * Real.pi * x) * resolverPowerDerivSlice p u σ x with hFdef
    have hcos_cont : Continuous (fun x : ℝ => Real.cos ((k : ℝ) * Real.pi * x)) :=
      Real.continuous_cos.comp (continuous_const.mul continuous_id')
    have hFcont : ContinuousOn (Function.uncurry F) (I ×ˢ Set.Icc (0:ℝ) 1) :=
      (hcos_cont.comp continuous_snd).continuousOn.mul hslabcont
    have hKcompact : IsCompact (I ×ˢ Set.Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
    obtain ⟨B, hB⟩ := (hKcompact.bddAbove_image hFcont.norm)
    set B' := max B 0 with hB'def
    have hB'nn : 0 ≤ B' := le_max_right _ _
    have hFbd : ∀ σ ∈ I, ∀ x ∈ Set.Icc (0:ℝ) 1, ‖F σ x‖ ≤ B' := by
      intro σ hσ x hx
      have : ‖Function.uncurry F (σ, x)‖ ≤ B :=
        hB (Set.mem_image_of_mem _ (Set.mem_prod.mpr ⟨hσ, hx⟩))
      exact le_trans this (le_max_left _ _)
    have hsec_cont : ∀ σ ∈ I, ContinuousOn (F σ) (Set.Icc (0:ℝ) 1) := by
      intro σ hσ
      have hsslice : ContinuousOn (resolverPowerDerivSlice p u σ) (Set.Icc (0:ℝ) 1) :=
        hslabcont.comp (continuousOn_const.prodMk continuousOn_id)
          (fun x hx => Set.mem_prod.mpr ⟨hσ, hx⟩)
      exact (hcos_cont.continuousOn).mul hsslice
    have hInhds : I ∈ 𝓝 σ₀ := by
      have : Set.Ioo (σ₀ - δ) (σ₀ + δ) ⊆ I := fun y hy => ⟨hy.1.le, hy.2.le⟩
      exact Filter.mem_of_superset
        (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩) this
    have hint_cont : ContinuousAt (fun σ => ∫ x in (0:ℝ)..1, F σ x) σ₀ := by
      refine intervalIntegral.continuousAt_of_dominated_interval
        (bound := fun _ => B') ?_ ?_ intervalIntegrable_const ?_
      · filter_upwards [hInhds] with σ hσ
        have : ContinuousOn (F σ) (Set.uIcc (0:ℝ) 1) := by
          rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hsec_cont σ hσ
        exact (this.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
      · filter_upwards [hInhds] with σ hσ
        refine Filter.Eventually.of_forall (fun x hx => ?_)
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
        exact hFbd σ hσ x ⟨hx.1.le, hx.2⟩
      · refine Filter.Eventually.of_forall (fun x hx => ?_)
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
        have hxIcc : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx.1.le, hx.2⟩
        have hcwa : ContinuousWithinAt (fun σ => F σ x) I σ₀ := by
          have := (hFcont.comp (continuousOn_id.prodMk continuousOn_const)
            (fun σ hσ => Set.mem_prod.mpr ⟨hσ, hxIcc⟩)).continuousWithinAt hσ₀mem
          simpa [Function.uncurry] using this
        exact hcwa.continuousAt hInhds
    have hadeq : ∀ σ, adotPowOf p u σ k =
        (if k = 0 then (1:ℝ) else 2) * ∫ x in (0:ℝ)..1, F σ x := by
      intro σ; unfold adotPowOf; rw [cosineCoeffs_eq_factor_mul_integral]
    have hcont_at : ContinuousAt (fun σ => adotPowOf p u σ k) σ₀ := by
      have hfun : (fun σ => adotPowOf p u σ k)
          = (fun σ => (if k = 0 then (1:ℝ) else 2) * ∫ x in (0:ℝ)..1, F σ x) :=
        funext hadeq
      rw [hfun]
      exact hint_cont.const_mul _
    exact hcont_at.continuousWithinAt
  have hbound : ∀ a' b', 0 < a' → b' < T → ∃ Mdot, ∀ σ ∈ Set.Icc a' b',
      ∀ k, |adotPowOf p u σ k| ≤ Mdot := by
    intro a' b' ha' hb'
    set K := Set.Icc a' b' ×ˢ Set.Icc (0:ℝ) 1 with hKdef
    have hKsub : K ⊆ Set.Ioo 0 T ×ˢ Set.Icc (0:ℝ) 1 := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
      exact Set.mem_prod.mpr ⟨⟨lt_of_lt_of_le ha' hq1.1, lt_of_le_of_lt hq1.2 hb'⟩, hq2⟩
    have hKcompact : IsCompact K := (isCompact_Icc).prod (isCompact_Icc)
    have hcontK : ContinuousOn (Function.uncurry (resolverPowerDerivSlice p u)) K :=
      hslice_cont.mono hKsub
    obtain ⟨B, hB⟩ := (hKcompact.bddAbove_image (hcontK.norm)).imp (fun B hB => hB)
    set B' := max B 0 with hB'def
    have hB'nn : 0 ≤ B' := le_max_right _ _
    have hbd : ∀ σ ∈ Set.Icc a' b', ∀ x ∈ Set.Icc (0:ℝ) 1,
        |resolverPowerDerivSlice p u σ x| ≤ B' := by
      intro σ hσ x hx
      have hmem : (σ, x) ∈ K := Set.mem_prod.mpr ⟨hσ, hx⟩
      have : ‖Function.uncurry (resolverPowerDerivSlice p u) (σ, x)‖ ≤ B :=
        hB (Set.mem_image_of_mem _ hmem)
      simp only [Function.uncurry, Real.norm_eq_abs] at this
      exact le_trans this (le_max_left _ _)
    refine ⟨2 * B', fun σ hσ k => ?_⟩
    have hsec : ContinuousOn (resolverPowerDerivSlice p u σ) (Set.Icc (0:ℝ) 1) := by
      have hmaps : Set.MapsTo (fun x : ℝ => ((σ, x) : ℝ × ℝ))
          (Set.Icc (0:ℝ) 1) K :=
        fun x hx => Set.mem_prod.mpr ⟨hσ, hx⟩
      exact hcontK.comp (continuousOn_const.prodMk continuousOn_id) hmaps
    exact cosineCoeffs_abs_le_of_continuous_bounded hsec hB'nn
      (fun x hx => hbd σ hσ x hx) k
  exact ⟨hderiv, hcont, hbound⟩

set_option maxHeartbeats 800000 in
/-- **Window-uniform positive lower bound on the lift (for R-Hvsrc-1).**

From the SAME satisfiable ledger data (driving the `LocalRestartWeak` engine,
whose `valueSeries` is jointly continuous and agrees with the lift on the window),
the lift `(σ,x) ↦ lift(u σ) x` is jointly continuous on `Ioo 0 T ×ˢ Icc 0 1`;
restricting to the compact window `[c',d'] ×ˢ [0,1] ⊂ (0,T) ×ˢ [0,1]` and taking
its minimum (`IsCompact.exists_isMinOn`) gives a uniform positive lower bound `m`
(the same route as `lift_u_uniformPositive_on_compact`). -/
theorem lift_window_uniformPositive_of_subtypeCont
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (u : ℝ → intervalDomainPoint → ℝ)
    {T : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hfix : ∀ s, 0 < s → s < T → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u s) x = intervalGradientDuhamelMap p u₀ u s ⟨x, hx⟩)
    (hsrc0 : DuhamelSourceBddOn
      (ShenWork.IntervalPicardLimitBddProducer.patchedSource p u₀ u) T)
    {Msup : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < T → Set.EqOn (intervalDomainLift (u σ))
      (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x)
    (hubt : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ Msup)
    (hG1t : ∀ a' b', 0 < a' → b' < T → ∃ G1, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (u σ)) x| ≤ G1)
    (hG2t : ∀ a' b', 0 < a' → b' < T → ∃ G2, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2)
    (hLc_ce : ∀ t, 0 < t → t < T →
      ∀ s, 0 < s → s ≤ t →
        Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s))))
    {c' d' : ℝ} (hc'pos : 0 < c') (hcd' : c' ≤ d') (hd'T : d' < T) :
    ∃ m : ℝ, 0 < m ∧
      ∀ σ ∈ Set.Icc c' d', ∀ x ∈ Set.Icc (0 : ℝ) 1,
        m ≤ intervalDomainLift (u σ) x := by
  classical
  have mkL : ∀ σ, 0 < σ → σ < T → LocalRestartWeak p u T σ := fun σ hσ0 hσT =>
    ShenWork.Paper2.PicardLimitK1Weak.localRestartWeak_of_ledger_of_subtypeCont
      hχ0 u hα ha hb hu₀_cont hu₀_bound hfix hsrc0 bc hbsum hagree hpost hubt
      hG1t hG2t hLc_ce hσ0 hσT
  -- Global joint continuity of the lift on Ioo 0 T ×ˢ Icc 0 1 (engine covering).
  have hlift_cont : ContinuousOn
      (Function.uncurry (fun (σ : ℝ) (x : ℝ) => intervalDomainLift (u σ) x))
      (Set.Ioo 0 T ×ˢ Set.Icc (0:ℝ) 1) := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
    set σ₀ := q.1 with hσ₀
    have hσ₀0 : 0 < σ₀ := hq1.1
    have hσ₀T : σ₀ < T := hq1.2
    set L := mkL σ₀ hσ₀0 hσ₀T with hLdef
    set δ : ℝ := min (σ₀ - L.τ) (L.d - σ₀) / 2 with hδdef
    have hδ1 : 0 < σ₀ - L.τ := by have := L.hστ; linarith
    have hδ2 : 0 < L.d - σ₀ := by have := L.hσd; linarith
    have hδ : 0 < δ := by rw [hδdef]; have := lt_min hδ1 hδ2; linarith
    have hδle1 : δ ≤ (σ₀ - L.τ) / 2 := by
      rw [hδdef]; have := min_le_left (σ₀ - L.τ) (L.d - σ₀); linarith
    have hδle2 : δ ≤ (L.d - σ₀) / 2 := by
      rw [hδdef]; have := min_le_right (σ₀ - L.τ) (L.d - σ₀); linarith
    have hslab_sub : Set.Icc (σ₀ - δ) (σ₀ + δ) ⊆ Set.Ioo L.τ L.d := fun s hs =>
      ⟨by linarith [hs.1, hδle1], by linarith [hs.2, hδle2]⟩
    -- joint continuity of valueSeries on the slab → agree with the lift.
    set Φ : ℝ × ℝ → ℝ × ℝ := fun r => (r.1 - L.τ, r.2) with hΦ
    have hΦcont : Continuous Φ :=
      (continuous_fst.sub continuous_const).prodMk continuous_snd
    have hmaps := L.shift_mapsTo hslab_sub
    have hwS : ContinuousOn (fun r : ℝ × ℝ => L.valueSeries (r.1 - L.τ) r.2)
        (Set.Icc (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Icc (0:ℝ) 1) :=
      (L.valueSeries_jointContinuousOn.comp hΦcont.continuousOn hmaps)
    have hlift_eq : ContinuousOn
        (Function.uncurry (fun (σ : ℝ) (x : ℝ) => intervalDomainLift (u σ) x))
        (Set.Icc (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Icc (0:ℝ) 1) := by
      refine hwS.congr (fun r hr => ?_)
      obtain ⟨hr1, hr2⟩ := Set.mem_prod.mp hr
      simp only [Function.uncurry]
      exact L.lift_eq_valueSeries (hslab_sub hr1) hr2
    have hmem : q ∈ Set.Icc (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Icc (0:ℝ) 1 :=
      Set.mem_prod.mpr ⟨⟨by linarith, by linarith⟩, hq2⟩
    have hnhds : Set.Icc (σ₀ - δ) (σ₀ + δ) ×ˢ Set.Icc (0:ℝ) 1
        ∈ 𝓝[Set.Ioo 0 T ×ˢ Set.Icc (0:ℝ) 1] q := by
      have hopen : Set.Ioo (σ₀ - δ) (σ₀ + δ) ×ˢ (Set.univ : Set ℝ) ∈ 𝓝 q := by
        apply (isOpen_Ioo.prod isOpen_univ).mem_nhds
        exact Set.mem_prod.mpr ⟨⟨by linarith, by linarith⟩, Set.mem_univ _⟩
      have hinter := Filter.inter_mem (Filter.mem_inf_of_left hopen)
        (self_mem_nhdsWithin (a := q) (s := Set.Ioo 0 T ×ˢ Set.Icc (0:ℝ) 1))
      refine Filter.mem_of_superset hinter ?_
      intro y hy
      obtain ⟨hy1, hy2⟩ := hy
      exact Set.mem_prod.mpr ⟨⟨(Set.mem_prod.mp hy1).1.1.le,
        (Set.mem_prod.mp hy1).1.2.le⟩, (Set.mem_prod.mp hy2).2⟩
    exact (hlift_eq.continuousWithinAt hmem).mono_of_mem_nhdsWithin hnhds
  -- restrict to the compact window and take the positive minimum.
  have hKcompact : IsCompact (Set.Icc c' d' ×ˢ Set.Icc (0:ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hKne : (Set.Icc c' d' ×ˢ Set.Icc (0:ℝ) 1).Nonempty :=
    ⟨(c', 0), ⟨Set.left_mem_Icc.mpr hcd', by constructor <;> norm_num⟩⟩
  have hsub : Set.Icc c' d' ×ˢ Set.Icc (0:ℝ) 1 ⊆
      Set.Ioo (0:ℝ) T ×ˢ Set.Icc (0:ℝ) 1 := by
    rintro ⟨σ, x⟩ ⟨hσ, hx⟩
    exact ⟨⟨lt_of_lt_of_le hc'pos hσ.1, lt_of_le_of_lt hσ.2 hd'T⟩, hx⟩
  have hcontK : ContinuousOn
      (Function.uncurry (fun (σ : ℝ) (x : ℝ) => intervalDomainLift (u σ) x))
      (Set.Icc c' d' ×ˢ Set.Icc (0:ℝ) 1) := hlift_cont.mono hsub
  obtain ⟨q₀, hq₀_mem, hq₀_min⟩ := hKcompact.exists_isMinOn hKne hcontK
  obtain ⟨σ₀, x₀⟩ := q₀
  obtain ⟨hσ₀_mem, hx₀_mem⟩ := hq₀_mem
  have hσ₀_open : 0 < σ₀ ∧ σ₀ < T :=
    ⟨lt_of_lt_of_le hc'pos hσ₀_mem.1, lt_of_le_of_lt hσ₀_mem.2 hd'T⟩
  have hmin_pos : 0 < intervalDomainLift (u σ₀) x₀ :=
    hpost σ₀ hσ₀_open.1 hσ₀_open.2 x₀ hx₀_mem
  refine ⟨intervalDomainLift (u σ₀) x₀, hmin_pos, ?_⟩
  intro σ hσ x hx
  exact isMinOn_iff.mp hq₀_min (σ, x) (Set.mem_prod.mpr ⟨hσ, hx⟩)

end ShenWork.Paper2.ResolverPowerK1
