import ShenWork.Paper3.IntervalDomainNegativeSensitivityMassFloor
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Static logistic-reaction coercivity on interval tail slices

The tail of a bounded global interval orbit is uniformly Lipschitz.  This file
uses only that static spatial compactness to prove the coercivity needed by the
mass ODE: a nonnegative uniformly Lipschitz profile whose mass stays a fixed
amount below the positive logistic equilibrium, while its maximum is close to
that equilibrium from above, has a uniformly positive integrated logistic
reaction.

The proof is a one-slice Arzela--Ascoli contradiction.  It does not construct
a time-translate solution and does not use stability, basin entry, or orbit
convergence.
-/

namespace ShenWork.Paper3

open Filter Set Topology MeasureTheory
open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

local instance intervalDomainTailReactionMetricSpace : MetricSpace intervalDomainPoint :=
  inferInstanceAs (MetricSpace (Subtype (Set.Icc (0 : ℝ) 1)))

/-- A continuous function on the closed unit interval has an interval-
integrable zero extension. -/
theorem intervalDomainLift_intervalIntegrable_of_continuous
    (f : C(intervalDomainPoint, ℝ)) :
    IntervalIntegrable (intervalDomainLift f) volume (0 : ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  rw [continuousOn_iff_continuous_restrict]
  have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift f) = f := by
    funext x
    simp [intervalDomainLift]
  rw [heq]
  exact f.continuous

@[simp] theorem intervalDomain_integral_const (z : ℝ) :
    intervalDomain.integral (fun _ : intervalDomainPoint => z) = z := by
  unfold intervalDomain intervalDomainIntegral
  calc
    (∫ x in (0 : ℝ)..1,
        intervalDomainLift (fun _ : intervalDomainPoint => z) x) =
        ∫ _x in (0 : ℝ)..1, z := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      rw [intervalDomainLift, dif_pos hx]
    _ = z := by simp

/-- Uniform convergence of continuous closed-interval profiles passes through
the concrete interval-domain integral. -/
theorem intervalDomain_integral_tendsto_of_tendstoUniformly
    {f : ℕ → C(intervalDomainPoint, ℝ)} {g : C(intervalDomainPoint, ℝ)}
    (hfg : TendstoUniformly (fun n x => f n x) g atTop) :
    Tendsto (fun n => intervalDomain.integral (f n)) atTop
      (𝓝 (intervalDomain.integral g)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hu := (Metric.tendstoUniformly_iff.mp hfg (ε / 2) hhalf)
  rcases eventually_atTop.1 hu with ⟨N, hN⟩
  refine ⟨N, fun n hnN => ?_⟩
  have hn := hN n hnN
  rw [Real.dist_eq]
  change |(∫ y in (0 : ℝ)..1, intervalDomainLift (f n) y) -
      ∫ y in (0 : ℝ)..1, intervalDomainLift g y| < ε
  rw [← intervalIntegral.integral_sub
    (intervalDomainLift_intervalIntegrable_of_continuous (f n))
    (intervalDomainLift_intervalIntegrable_of_continuous g)]
  have hbound : ∀ y ∈ Set.uIoc (0 : ℝ) 1,
      ‖intervalDomainLift (f n) y - intervalDomainLift g y‖ ≤ ε / 2 := by
    intro y hy
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
    have hpoint := hn ⟨y, hyIcc⟩
    simpa [intervalDomainLift, hyIcc, Real.dist_eq, Real.norm_eq_abs, abs_sub_comm]
      using hpoint.le
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have : ‖∫ y in (0 : ℝ)..1,
      (intervalDomainLift (f n) y - intervalDomainLift g y)‖ ≤ ε / 2 := by
    simpa using hint
  simpa [Real.norm_eq_abs] using lt_of_le_of_lt this (by linarith)

/-- A continuous nonnegative interval-domain profile with one positive value
has strictly positive integral, including when the supplied positive point is
an endpoint. -/
theorem intervalDomain_integral_pos_of_continuous_nonneg_of_exists_pos
    (f : C(intervalDomainPoint, ℝ))
    (hnonneg : ∀ x, 0 ≤ f x) (hpos : ∃ x, 0 < f x) :
    0 < intervalDomain.integral f := by
  have hcont : ContinuousOn (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift f) = f := by
      funext x
      simp [intervalDomainLift]
    rw [heq]
    exact f.continuous
  have hnonneg_lift : ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      0 ≤ intervalDomainLift f y := by
    intro y hy
    rw [intervalDomainLift, dif_pos ⟨hy.1.le, hy.2⟩]
    exact hnonneg _
  have hpos_interior : ∃ y ∈ Set.Ioo (0 : ℝ) 1,
      0 < intervalDomainLift f y := by
    let xm : intervalDomainPoint := ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩
    by_cases hm : 0 < f xm
    · have hmem : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
      exact ⟨(1 : ℝ) / 2, ⟨by norm_num, by norm_num⟩,
        by simpa only [intervalDomainLift, dif_pos hmem, xm] using hm⟩
    · obtain ⟨x, hx⟩ := hpos
      by_cases hxi : x.1 ∈ Set.Ioo (0 : ℝ) 1
      · exact ⟨x.1, hxi, by simpa [intervalDomainLift, x.2] using hx⟩
      · have hfm : f xm = 0 := le_antisymm (le_of_not_gt hm) (hnonneg xm)
        have hx_endpoint : x.1 = 0 ∨ x.1 = 1 := by
          simp only [Set.mem_Ioo, not_and_or, not_lt] at hxi
          rcases hxi with hx0 | hx1
          · exact Or.inl (le_antisymm hx0 x.2.1)
          · exact Or.inr (le_antisymm x.2.2 hx1)
        rcases hx_endpoint with hx0 | hx1
        · let xzero : intervalDomainPoint := ⟨0, ⟨by norm_num, by norm_num⟩⟩
          have hx_eq : x = xzero := Subtype.ext hx0
          have hxpos : 0 < f xzero := by simpa only [hx_eq] using hx
          have hzero : intervalDomainLift f 0 = f xzero := by
            have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
            simpa only [intervalDomainLift, dif_pos hmem, xzero]
          have hhalf : intervalDomainLift f ((1 : ℝ) / 2) = 0 := by
            have hmem : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
            simpa only [intervalDomainLift, dif_pos hmem, xm] using hfm
          have htarget : f xzero / 2 ∈
              Set.Icc (intervalDomainLift f ((1 : ℝ) / 2))
                (intervalDomainLift f 0) := by
            rw [hzero, hhalf]
            constructor <;> linarith
          obtain ⟨y, hyIcc, hyval⟩ :=
            intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1 / 2)
              (hcont.mono (Set.Icc_subset_Icc_right (by norm_num))) htarget
          refine ⟨y, ⟨?_, lt_of_le_of_lt hyIcc.2 (by norm_num)⟩, ?_⟩
          · by_contra hy0
            have : y = 0 := le_antisymm (le_of_not_gt hy0) hyIcc.1
            subst y
            rw [hzero] at hyval
            linarith
          · rw [hyval]
            linarith
        · let xone : intervalDomainPoint := ⟨1, ⟨by norm_num, le_rfl⟩⟩
          have hx_eq : x = xone := Subtype.ext hx1
          have hxpos : 0 < f xone := by simpa only [hx_eq] using hx
          have hone : intervalDomainLift f 1 = f xone := by
            have hmem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
            simpa only [intervalDomainLift, dif_pos hmem, xone]
          have hhalf : intervalDomainLift f ((1 : ℝ) / 2) = 0 := by
            have hmem : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
            simpa only [intervalDomainLift, dif_pos hmem, xm] using hfm
          have htarget : f xone / 2 ∈
              Set.Icc (intervalDomainLift f ((1 : ℝ) / 2))
                (intervalDomainLift f 1) := by
            rw [hone, hhalf]
            constructor <;> linarith
          obtain ⟨y, hyIcc, hyval⟩ :=
            intermediate_value_Icc (by norm_num : (1 / 2 : ℝ) ≤ 1)
              (hcont.mono (Set.Icc_subset_Icc_left (by norm_num))) htarget
          refine ⟨y, ⟨lt_of_lt_of_le (by norm_num) hyIcc.1, ?_⟩, ?_⟩
          · by_contra hy1
            have : y = 1 := le_antisymm hyIcc.2 (le_of_not_gt hy1)
            subst y
            rw [hone] at hyval
            linarith
          · rw [hyval]
            linarith
  unfold intervalDomain intervalDomainIntegral
  exact intervalIntegral.integral_pos (by norm_num) hcont hnonneg_lift
    (by
      obtain ⟨y, hy, hfy⟩ := hpos_interior
      exact ⟨y, ⟨hy.1.le, hy.2.le⟩, hfy⟩)

/-- A uniformly bounded, uniformly Lipschitz sequence of continuous profiles
on the closed unit interval has a uniformly convergent subsequence. -/
theorem intervalDomain_exists_uniform_convergent_subseq_of_lipschitz
    (f : ℕ → C(intervalDomainPoint, ℝ)) {K G : ℝ}
    (hK : 0 ≤ K) (hG : 0 ≤ G)
    (hbound : ∀ n x, |f n x| ≤ K)
    (hlip : ∀ n, LipschitzWith ⟨G, hG⟩ (f n)) :
    ∃ g : C(intervalDomainPoint, ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformly (fun n x => f (φ n) x) g atTop := by
  let S : Set C(intervalDomainPoint, ℝ) :=
    Set.range f
  have hcompact : IsCompact (closure S) := by
    have hcover :
        ⋃₀ {A : Set intervalDomainPoint | IsCompact A} = Set.univ := by
      ext x
      constructor
      · exact fun _ => Set.mem_univ x
      · intro _
        exact Set.mem_sUnion_of_mem (Set.mem_singleton x) isCompact_singleton
    letI : T2Space
        (UniformOnFun intervalDomainPoint ℝ
          {A : Set intervalDomainPoint | IsCompact A}) :=
      UniformOnFun.t2Space_of_covering hcover
    refine ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (X := intervalDomainPoint) (α := ℝ)
      (ι := C(intervalDomainPoint, ℝ))
      (F := fun q : C(intervalDomainPoint, ℝ) => (q : intervalDomainPoint → ℝ))
      (𝔖 := {A : Set intervalDomainPoint | IsCompact A})
      (fun A hA => hA) ?_ ?_ ?_
    · simpa [ContinuousMap.toUniformOnFunIsCompact] using
        (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact :
          IsUniformEmbedding
            (ContinuousMap.toUniformOnFunIsCompact :
              C(intervalDomainPoint, ℝ) →
                UniformOnFun intervalDomainPoint ℝ
                  {A : Set intervalDomainPoint | IsCompact A})).isClosedEmbedding
    · intro A hA
      have hequi : UniformEquicontinuous
          (fun n x => f n x) :=
        LipschitzWith.uniformEquicontinuous
          (fun n x => f n x) ⟨G, hG⟩ hlip
      intro x hx U hU
      have heq : Equicontinuous (fun n x => f n x) := hequi.equicontinuous
      filter_upwards [(heq x U hU).filter_mono nhdsWithin_le_nhds] with y hy
      intro q
      rcases q.2 with ⟨n, hn⟩
      change (q.1 x, q.1 y) ∈ U
      rw [← hn]
      exact hy n
    · intro A hA x hx
      refine ⟨Set.Icc (-K) K, isCompact_Icc, ?_⟩
      intro q hq
      rcases hq with ⟨n, rfl⟩
      exact (abs_le.mp (hbound n x))
  obtain ⟨g, _hg, φ, hφ, hlim⟩ :=
    hcompact.tendsto_subseq
      (x := f) (fun n => subset_closure (Set.mem_range_self n))
  refine ⟨g, φ, hφ, ?_⟩
  have hcm : Tendsto (fun n => f (φ n)) atTop (𝓝 g) := by
    simpa [Function.comp_def] using hlim
  have hall :=
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hcm)
      Set.univ isCompact_univ
  simpa [tendstoUniformlyOn_univ] using hall

/-- The scalar logistic reaction used in the interval mass identity. -/
def intervalDomainLogisticReaction (p : CM2Params) (z : ℝ) : ℝ :=
  z * (p.a - p.b * z ^ p.α)

theorem continuous_intervalDomainLogisticReaction (p : CM2Params) :
    Continuous (intervalDomainLogisticReaction p) := by
  unfold intervalDomainLogisticReaction
  exact continuous_id.mul
    (continuous_const.sub
      (continuous_const.mul (Real.continuous_rpow_const p.hα.le)))

/-- Static coercivity of the integrated logistic reaction below the positive
equilibrium mass.  Only nonnegativity, a common Lipschitz constant, and a
one-sided upper bound close to the carrying capacity are used. -/
theorem intervalDomain_logisticReaction_coercive_of_mass_gap
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    {eta d G : ℝ} (heta : 0 < eta) (hd : 0 < d)
    (hdc : d < (positiveEquilibrium p ⟨ha, hb⟩).1) (hG : 0 ≤ G) :
    ∃ eps > 0, ∃ q > 0,
      ∀ f : C(intervalDomainPoint, ℝ),
        (∀ x, 0 ≤ f x) →
        (∀ x, f x ≤ (positiveEquilibrium p ⟨ha, hb⟩).1 + eps) →
        eta ≤ intervalDomain.integral f →
        intervalDomain.integral f ≤ (positiveEquilibrium p ⟨ha, hb⟩).1 - d →
        LipschitzWith ⟨G, hG⟩ f →
        q ≤ intervalDomain.integral
          (fun x => intervalDomainLogisticReaction p (f x)) := by
  let c : ℝ := (positiveEquilibrium p ⟨ha, hb⟩).1
  have hc : 0 < c := positiveEquilibrium_fst_pos p ⟨ha, hb⟩
  by_contra hcoercive
  push_neg at hcoercive
  let eps : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have heps_pos : ∀ n, 0 < eps n := by
    intro n
    positivity
  let f : ℕ → C(intervalDomainPoint, ℝ) := fun n =>
    Classical.choose (hcoercive (eps n) (heps_pos n) (eps n) (heps_pos n))
  have hf_spec (n : ℕ) :
      (∀ x, 0 ≤ f n x) ∧
      (∀ x, f n x ≤ c + eps n) ∧
      eta ≤ intervalDomain.integral (f n) ∧
      intervalDomain.integral (f n) ≤ c - d ∧
      LipschitzWith ⟨G, hG⟩ (f n) ∧
      intervalDomain.integral
          (fun x => intervalDomainLogisticReaction p (f n x)) < eps n := by
    simpa [f, c] using
      Classical.choose_spec
        (hcoercive (eps n) (heps_pos n) (eps n) (heps_pos n))
  have heps_le_one (n : ℕ) : eps n ≤ 1 := by
    dsimp [eps]
    rw [div_le_one (by positivity : (0 : ℝ) < n + 1)]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hf_abs : ∀ n x, |f n x| ≤ c + 1 := by
    intro n x
    rw [abs_of_nonneg ((hf_spec n).1 x)]
    exact le_trans ((hf_spec n).2.1 x)
      (by simpa [add_comm] using add_le_add_left (heps_le_one n) c)
  obtain ⟨g, φ, hφ, hfg⟩ :=
    intervalDomain_exists_uniform_convergent_subseq_of_lipschitz f
      (by linarith : 0 ≤ c + 1) hG hf_abs (fun n => (hf_spec n).2.2.2.2.1)
  have heps_zero : Tendsto eps atTop (𝓝 0) := by
    simpa [eps, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0))
  have heps_subseq_zero : Tendsto (fun n => eps (φ n)) atTop (𝓝 0) :=
    heps_zero.comp hφ.tendsto_atTop
  have hg_nonneg : ∀ x, 0 ≤ g x := by
    intro x
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (hfg.tendsto_at x)
      (Filter.Eventually.of_forall fun n => (hf_spec (φ n)).1 x)
  have hg_le_c : ∀ x, g x ≤ c := by
    intro x
    have hsum : Tendsto (fun n => c + eps (φ n)) atTop (𝓝 c) := by
      simpa using tendsto_const_nhds.add heps_subseq_zero
    exact le_of_tendsto_of_tendsto (hfg.tendsto_at x) hsum
      (Filter.Eventually.of_forall fun n => (hf_spec (φ n)).2.1 x)
  have hint_f : Tendsto (fun n => intervalDomain.integral (f (φ n))) atTop
      (𝓝 (intervalDomain.integral g)) :=
    intervalDomain_integral_tendsto_of_tendstoUniformly hfg
  have hg_mass_lower : eta ≤ intervalDomain.integral g :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hint_f
      (Filter.Eventually.of_forall fun n => (hf_spec (φ n)).2.2.1)
  have hg_mass_upper : intervalDomain.integral g ≤ c - d :=
    le_of_tendsto hint_f
      (Filter.Eventually.of_forall fun n => (hf_spec (φ n)).2.2.2.1)
  have hreaction_uniform : TendstoUniformly
      (fun n x => intervalDomainLogisticReaction p (f (φ n) x))
      (fun x => intervalDomainLogisticReaction p (g x)) atTop := by
    apply UniformContinuousOn.comp_tendstoUniformly
      (s := Set.Icc (0 : ℝ) (c + 1))
    · intro n x
      exact ⟨(hf_spec (φ n)).1 x,
        le_trans ((hf_spec (φ n)).2.1 x)
          (by simpa [add_comm] using add_le_add_left (heps_le_one (φ n)) c)⟩
    · exact fun x => ⟨hg_nonneg x, le_trans (hg_le_c x) (by linarith)⟩
    · exact isCompact_Icc.uniformContinuousOn_of_continuous
        (continuous_intervalDomainLogisticReaction p).continuousOn
    · exact hfg
  have hreaction_int : Tendsto
      (fun n => intervalDomain.integral
        (fun x => intervalDomainLogisticReaction p (f (φ n) x))) atTop
      (𝓝 (intervalDomain.integral
        (fun x => intervalDomainLogisticReaction p (g x)))) := by
    let F : ℕ → C(intervalDomainPoint, ℝ) := fun n =>
      ⟨fun x => intervalDomainLogisticReaction p (f (φ n) x),
        (continuous_intervalDomainLogisticReaction p).comp (f (φ n)).continuous⟩
    let Rg : C(intervalDomainPoint, ℝ) :=
      ⟨fun x => intervalDomainLogisticReaction p (g x),
        (continuous_intervalDomainLogisticReaction p).comp g.continuous⟩
    exact intervalDomain_integral_tendsto_of_tendstoUniformly
      (f := F) (g := Rg) (by simpa [F, Rg] using hreaction_uniform)
  have hreaction_int_nonpos :
      intervalDomain.integral
          (fun x => intervalDomainLogisticReaction p (g x)) ≤ 0 := by
    exact le_of_tendsto_of_tendsto hreaction_int heps_subseq_zero
      (Filter.Eventually.of_forall fun n =>
        (hf_spec (φ n)).2.2.2.2.2.le)
  have hcapacity_zero : p.a - p.b * c ^ p.α = 0 := by
    simpa [c] using positiveEquilibrium_logistic_zero p ⟨ha, hb⟩
  let Rg : C(intervalDomainPoint, ℝ) :=
    ⟨fun x => intervalDomainLogisticReaction p (g x),
      (continuous_intervalDomainLogisticReaction p).comp g.continuous⟩
  have hRg_nonneg : ∀ x, 0 ≤ Rg x := by
    intro x
    have hpow : g x ^ p.α ≤ c ^ p.α :=
      Real.rpow_le_rpow (hg_nonneg x) (hg_le_c x) p.hα.le
    have hfactor : 0 ≤ p.a - p.b * g x ^ p.α := by
      have : p.b * g x ^ p.α ≤ p.b * c ^ p.α :=
        mul_le_mul_of_nonneg_left hpow hb.le
      linarith
    exact mul_nonneg (hg_nonneg x) hfactor
  have hRg_zero : ∀ x, Rg x = 0 := by
    intro x
    apply le_antisymm
    · by_contra hx
      have hxpos : 0 < Rg x := lt_of_not_ge hx
      have hint_pos :=
        intervalDomain_integral_pos_of_continuous_nonneg_of_exists_pos
          Rg hRg_nonneg ⟨x, hxpos⟩
      have : intervalDomain.integral Rg ≤ 0 := by
        simpa [Rg] using hreaction_int_nonpos
      exact (not_lt_of_ge this) hint_pos
    · exact hRg_nonneg x
  have hg_zero_or_capacity : ∀ x, g x = 0 ∨ g x = c := by
    intro x
    have hprod : g x * (p.a - p.b * g x ^ p.α) = 0 := by
      simpa [Rg, intervalDomainLogisticReaction] using hRg_zero x
    rcases mul_eq_zero.mp hprod with hx0 | hfactor
    · exact Or.inl hx0
    · right
      have hpow_eq : g x ^ p.α = c ^ p.α := by
        nlinarith
      exact le_antisymm
        ((Real.rpow_le_rpow_iff (hg_nonneg x) hc.le p.hα).mp hpow_eq.le)
        ((Real.rpow_le_rpow_iff hc.le (hg_nonneg x) p.hα).mp hpow_eq.ge)
  have hex_capacity : ∃ x, g x = c := by
    by_contra hnone
    push_neg at hnone
    have hg_zero : ∀ x, g x = 0 := fun x =>
      (hg_zero_or_capacity x).resolve_right (hnone x)
    have hint_zero : intervalDomain.integral g = 0 := by
      rw [show (g : intervalDomainPoint → ℝ) = fun _ => 0 from funext hg_zero]
      exact intervalDomain_integral_const 0
    linarith
  have hex_zero : ∃ x, g x = 0 := by
    by_contra hnone
    push_neg at hnone
    have hg_capacity : ∀ x, g x = c := fun x =>
      (hg_zero_or_capacity x).resolve_left (hnone x)
    have hint_capacity : intervalDomain.integral g = c := by
      rw [show (g : intervalDomainPoint → ℝ) = fun _ => c from funext hg_capacity]
      exact intervalDomain_integral_const c
    linarith
  obtain ⟨xzero, hxzero⟩ := hex_zero
  obtain ⟨xcapacity, hxcapacity⟩ := hex_capacity
  have hg_lift_cont : ContinuousOn (intervalDomainLift g) (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift g) = g := by
      funext x
      simp [intervalDomainLift]
    rw [heq]
    exact g.continuous
  have hlift_zero : intervalDomainLift g xzero.1 = 0 := by
    simp [intervalDomainLift, xzero.2, hxzero]
  have hlift_capacity : intervalDomainLift g xcapacity.1 = c := by
    simp [intervalDomainLift, xcapacity.2, hxcapacity]
  have hmid_mem : c / 2 ∈
      Set.Icc (intervalDomainLift g xzero.1) (intervalDomainLift g xcapacity.1) := by
    rw [hlift_zero, hlift_capacity]
    constructor <;> linarith
  obtain ⟨ymid, hymid_mem, hymid⟩ :=
    isPreconnected_Icc.intermediate_value xzero.2 xcapacity.2
      hg_lift_cont hmid_mem
  let xmid : intervalDomainPoint := ⟨ymid, hymid_mem⟩
  have hxmid : g xmid = c / 2 := by
    simpa [xmid, intervalDomainLift, hymid_mem] using hymid
  rcases hg_zero_or_capacity xmid with hxmid_zero | hxmid_capacity
  · rw [hxmid_zero] at hxmid
    linarith
  · rw [hxmid_capacity] at hxmid
    linarith

#print axioms intervalDomainLift_intervalIntegrable_of_continuous
#print axioms intervalDomain_integral_const
#print axioms intervalDomain_integral_pos_of_continuous_nonneg_of_exists_pos
#print axioms intervalDomain_integral_tendsto_of_tendstoUniformly
#print axioms intervalDomain_exists_uniform_convergent_subseq_of_lipschitz
#print axioms continuous_intervalDomainLogisticReaction
#print axioms intervalDomain_logisticReaction_coercive_of_mass_gap

end

end ShenWork.Paper3
