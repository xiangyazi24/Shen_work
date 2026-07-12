import ShenWork.Paper2.IntervalDomainMLpEnergy
import ShenWork.Paper2.IntervalDomainMass

/-!
# Uniform mass control for the paper-faithful interval model

The exact general-`m` weighted identity is specialized at exponent one.  The
diffusion and chemotaxis contributions then vanish algebraically, leaving the
logistic mass ODE.  Jensen's inequality and the initial trace give a uniform
mass bound under the corrected parameter guard `a = 0 ∨ 0 < b`.
-/

open ShenWork.IntervalDomain MeasureTheory Set
open scoped Topology

namespace ShenWork.Paper2.IntervalDomainM

noncomputable section

open ShenWork.Paper2.IntervalDomainEnergyStep

theorem solution_lift_continuousOn_Icc
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
  ((hsol.regularity.2.2.2.2.1 t ht).1.1).continuousOn

theorem solution_lift_pos_Icc
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u t) x := by
  intro x hx
  simp only [intervalDomainLift, hx, dif_pos]
  exact u_pos hsol ht.1 ht.2 ⟨x, hx⟩

theorem solution_slice_abs_bddAbove
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|)) := by
  have hcont := solution_lift_continuousOn_Icc hsol ht
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc.image_of_continuousOn hcont.abs).bddAbove
  refine ⟨M, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx := hM ⟨x.1, x.2, rfl⟩
  simpa [intervalDomainLift] using hx

theorem powerEnergy_one_eq_mass
    (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) :
    intervalDomainPowerEnergy 1 u t = intervalDomain.integral (u t) := by
  unfold intervalDomainPowerEnergy intervalDomain intervalDomainIntegral
  apply intervalIntegral.integral_congr
  intro y hy
  simp only [Real.rpow_one]

/-- The mass is genuinely differentiable at every positive interior time. -/
theorem mass_hasDerivAt
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt (fun τ => intervalDomain.integral (u τ))
      (deriv (fun τ => intervalDomain.integral (u τ)) t) t := by
  have hpow := powerEnergy_hasDerivAt (q := (1 : ℝ)) hsol ⟨ht0, htT⟩
  have hfun : (fun τ => intervalDomainPowerEnergy 1 u τ) =
      fun τ => intervalDomain.integral (u τ) := by
    funext τ
    exact powerEnergy_one_eq_mass u τ
  rw [hfun] at hpow
  exact hpow.differentiableAt.hasDerivAt

/-- Exact mass ODE for the faithful `u^m` flux. -/
theorem mass_derivative_eq_logistic
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    deriv (fun τ => intervalDomain.integral (u τ)) t =
      p.a * intervalDomain.integral (u t) -
        p.b * intervalDomain.integral (fun x => (u t x) ^ (1 + p.α)) := by
  have henergy := weightedLpEnergy_identity
    (p := p) (T := T) (t := t) (pExp := (1 : ℝ))
    (u := u) (v := v) (by norm_num) hsol ht0 htT
  have hfun : (fun τ => intervalDomainLpEnergy 1 u τ) =ᶠ[𝓝 t]
      fun τ => intervalDomain.integral (u τ) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨ht0, htT⟩] with τ hτ
    unfold intervalDomainLpEnergy intervalDomain intervalDomainIntegral
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le zero_le_one] at hy
    have hpos : 0 < u τ ⟨y, hy⟩ := u_pos hsol hτ.1 hτ.2 ⟨y, hy⟩
    simp [intervalDomainLift, hy, abs_of_pos hpos]
  rw [hfun.deriv_eq] at henergy
  simp only [one_div, one_mul, sub_self, zero_mul, add_zero,
    Real.rpow_one] at henergy
  linarith

/-- Exact `HasDerivAt` form of the logistic mass balance. -/
theorem mass_logistic_hasDerivAt
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt (fun τ => intervalDomain.integral (u τ))
      (p.a * intervalDomain.integral (u t) -
        p.b * intervalDomain.integral (fun x => (u t x) ^ (1 + p.α))) t := by
  convert mass_hasDerivAt hsol ht0 htT using 1
  exact (mass_derivative_eq_logistic hsol ht0 htT).symm

theorem lift_continuousOn_Icc_of_continuous
    {f : intervalDomainPoint → ℝ} (hf : Continuous f) :
    ContinuousOn (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift f) = f := by
    funext ⟨y, hy⟩
    simp only [Set.restrict_apply, intervalDomainLift]
    split_ifs
    exact congr_arg f (Subtype.ext rfl)
  rw [heq]
  exact hf

theorem bddAbove_range_abs_diff_of_bddAbove
    {f g : intervalDomain.Point → ℝ}
    (hf : BddAbove (Set.range (fun x => |f x|)))
    (hg : BddAbove (Set.range (fun x => |g x|))) :
    BddAbove (Set.range (fun x => |f x - g x|)) := by
  obtain ⟨Mf, hMf⟩ := hf
  obtain ⟨Mg, hMg⟩ := hg
  refine ⟨Mf + Mg, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (abs_sub (f x) (g x)).trans
    (add_le_add (hMf ⟨x, rfl⟩) (hMg ⟨x, rfl⟩))

/-- The initial sup-norm trace implies convergence of the mass to its initial
value. -/
theorem mass_tendsto_initial
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ → t < T →
      |intervalDomain.integral (u t) - intervalDomain.integral u₀| < ε := by
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := htrace ε hε
  refine ⟨δ, hδ_pos, ?_⟩
  intro t ht0 htδ htT
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hu_cont := solution_lift_continuousOn_Icc hsol ht
  have hu₀_adm :
      BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)) ∧
        Continuous u₀ := by
    simpa [intervalDomainM] using hu₀.admissible
  have hu0_cont := lift_continuousOn_Icc_of_continuous hu₀_adm.2
  have hu_int : IntervalIntegrable (intervalDomainLift (u t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hu_cont
  have hu0_int : IntervalIntegrable (intervalDomainLift u₀) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hu0_cont
  have hbdd_diff := bddAbove_range_abs_diff_of_bddAbove
    (solution_slice_abs_bddAbove hsol ht) hu₀_adm.1
  have hle := ShenWork.Paper2.intervalDomain_integral_abs_sub_le_supNorm
    (f := u t) (g := u₀) hu_int hu0_int hbdd_diff
  exact lt_of_le_of_lt hle (by
    simpa [intervalDomainM, intervalDomain] using hδ t ht0 htδ)

/-- Jensen on the unit interval for the positive solution slice. -/
theorem mass_jensen
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    (intervalDomain.integral (u t)) ^ (1 + p.α) ≤
      intervalDomain.integral (fun x => (u t x) ^ (1 + p.α)) := by
  let f : ℝ → ℝ := intervalDomainLift (u t)
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    simpa [f] using solution_lift_continuousOn_Icc hsol ht
  have hfpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < f x := by
    intro x hx
    simpa [f] using solution_lift_pos_Icc hsol ht x hx
  have hpone : (1 : ℝ) ≤ 1 + p.α := by linarith [p.hα]
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ))
      (fun x : ℝ => x ^ (1 + p.α)) := convexOn_rpow hpone
  have hcontpow : ContinuousOn (fun x : ℝ => x ^ (1 + p.α))
      (Set.Ici (0 : ℝ)) :=
    (Real.continuous_rpow_const (by linarith [p.hα] : 0 ≤ 1 + p.α)).continuousOn
  have hfs : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      f x ∈ Set.Ici (0 : ℝ) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun x hx =>
      (hfpos x ⟨le_of_lt hx.1, hx.2⟩).le
  have hfi_on : IntegrableOn f (Set.Ioc (0 : ℝ) 1) volume :=
    hfcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hpowcont_Icc : ContinuousOn (fun x => f x ^ (1 + p.α))
      (Set.Icc (0 : ℝ) 1) :=
    hfcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hfpos x hx)))
  have hgi_on : IntegrableOn ((fun x : ℝ => x ^ (1 + p.α)) ∘ f)
      (Set.Ioc (0 : ℝ) 1) volume := by
    change IntegrableOn (fun x => f x ^ (1 + p.α)) (Set.Ioc (0 : ℝ) 1) volume
    exact hpowcont_Icc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hJ := hconv.map_set_average_le (μ := volume)
    (t := Set.Ioc (0 : ℝ) 1) hcontpow isClosed_Ici
    (by simp [Real.volume_Ioc]) (by simp [Real.volume_Ioc])
    hfs hfi_on hgi_on
  have hμ : volume.real (Set.Ioc (0 : ℝ) 1) = 1 := by
    rw [Measure.real, Real.volume_Ioc]
    norm_num
  have hAvg_f :
      (⨍ x in Set.Ioc (0 : ℝ) 1, f x ∂volume) =
        ∫ x in (0 : ℝ)..1, f x := by
    rw [MeasureTheory.setAverage_eq, hμ]
    simp [intervalIntegral.integral_of_le zero_le_one]
  have hAvg_pow :
      (⨍ x in Set.Ioc (0 : ℝ) 1, f x ^ (1 + p.α) ∂volume) =
        ∫ x in (0 : ℝ)..1, f x ^ (1 + p.α) := by
    rw [MeasureTheory.setAverage_eq, hμ]
    simp [intervalIntegral.integral_of_le zero_le_one]
  rw [hAvg_f, hAvg_pow] at hJ
  have hpow_int_eq :
      (∫ x in (0 : ℝ)..1, f x ^ (1 + p.α)) =
        intervalDomainIntegral (fun x => (u t x) ^ (1 + p.α)) := by
    unfold intervalDomainIntegral
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    simp [f, intervalDomainLift, hx]
  change (∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x) ^ (1 + p.α) ≤
    intervalDomainIntegral (fun x => (u t x) ^ (1 + p.α))
  rwa [hpow_int_eq] at hJ

theorem mass_pos
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    0 < intervalDomain.integral (u t) := by
  unfold intervalDomain intervalDomainIntegral
  exact intervalIntegral.integral_pos (by norm_num)
    (solution_lift_continuousOn_Icc hsol ht)
    (fun y hy => (solution_lift_pos_Icc hsol ht y
      ⟨le_of_lt hy.1, hy.2⟩).le)
    ⟨(1 : ℝ) / 2, ⟨by norm_num, by norm_num⟩,
      solution_lift_pos_Icc hsol ht ((1 : ℝ) / 2)
        ⟨by norm_num, by norm_num⟩⟩

/-- Jensen turns the exact mass ODE into the scalar logistic inequality. -/
theorem mass_derivative_le_logistic
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    deriv (fun τ => intervalDomain.integral (u τ)) t ≤
      intervalDomain.integral (u t) *
        (p.a - p.b * (intervalDomain.integral (u t)) ^ p.α) := by
  let M : ℝ := intervalDomain.integral (u t)
  let P : ℝ := intervalDomain.integral (fun x => (u t x) ^ (1 + p.α))
  have hJ : M ^ (1 + p.α) ≤ P := by
    simpa [M, P] using mass_jensen hsol ⟨ht0, htT⟩
  have hMpos : 0 < M := by simpa [M] using mass_pos hsol ⟨ht0, htT⟩
  have hpow : M ^ (1 + p.α) = M * M ^ p.α := by
    rw [Real.rpow_add hMpos, Real.rpow_one]
  have hder := mass_derivative_eq_logistic hsol ht0 htT
  change deriv (fun τ => intervalDomain.integral (u τ)) t ≤
    M * (p.a - p.b * M ^ p.α)
  rw [hder]
  have hmul := mul_le_mul_of_nonneg_left hJ p.hb
  rw [hpow] at hmul
  nlinarith

/-- The scalar carrying-capacity threshold used by the mass comparison. -/
def massThreshold (p : CM2Params) : ℝ :=
  (p.a / p.b) ^ (1 / p.α)

theorem massThreshold_nonneg (p : CM2Params) : 0 ≤ massThreshold p :=
  Real.rpow_nonneg (div_nonneg p.ha p.hb) _

theorem mass_le_initial_of_a_eq_b_eq_zero
    {p : CM2Params} {T t : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (ha : p.a = 0) (hb : p.b = 0)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomain.integral (u t) ≤ intervalDomain.integral u₀ := by
  let M : ℝ → ℝ := fun s => intervalDomain.integral (u s)
  have hdiff : DifferentiableOn ℝ M (Set.Ioo (0 : ℝ) T) := by
    intro s hs
    exact (mass_hasDerivAt hsol hs.1 hs.2).differentiableAt.differentiableWithinAt
  have hderiv_zero : ∀ s ∈ Set.Ioo (0 : ℝ) T, deriv M s = 0 := by
    intro s hs
    simpa [M, ha, hb] using mass_derivative_eq_logistic hsol hs.1 hs.2
  have hconst : ∀ s₁ ∈ Set.Ioo (0 : ℝ) T, ∀ s₂ ∈ Set.Ioo (0 : ℝ) T,
      M s₁ = M s₂ := fun s₁ hs₁ s₂ hs₂ =>
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      hdiff hderiv_zero hs₁ hs₂
  have hinit := mass_tendsto_initial hu₀ hsol htrace
  have hlt : ∀ ε > 0, M t < intervalDomain.integral u₀ + ε := by
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := hinit ε hε
    let s := min (δ / 2) (T / 2)
    have hs0 : 0 < s := lt_min (by linarith) (by linarith [hsol.T_pos])
    have hsδ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hsT : s < T := lt_of_le_of_lt (min_le_right _ _) (by linarith [hsol.T_pos])
    rw [hconst t ⟨ht0, htT⟩ s ⟨hs0, hsT⟩]
    have habs := hδ s hs0 hsδ hsT
    linarith [(abs_sub_lt_iff.mp habs).1]
  by_contra hnot
  push_neg at hnot
  have hε : 0 < M t - intervalDomain.integral u₀ := by linarith
  linarith [hlt _ hε]

theorem mass_le_max_initial_threshold_of_b_pos
    {p : CM2Params} {T t : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hb : 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomain.integral (u t) ≤
      max (intervalDomain.integral u₀) (massThreshold p) := by
  let M : ℝ → ℝ := fun s => intervalDomain.integral (u s)
  let K : ℝ := massThreshold p
  by_cases hle : M t ≤ K
  · exact hle.trans (le_max_right _ _)
  push_neg at hle
  have hKnonneg : 0 ≤ K := by simpa [K] using massThreshold_nonneg p
  have hMcont : ContinuousOn M (Set.Ioo (0 : ℝ) T) := by
    intro s hs
    exact (mass_hasDerivAt hsol hs.1 hs.2).continuousAt.continuousWithinAt
  have hderiv_nonpos : ∀ s ∈ Set.Ioo (0 : ℝ) T, K < M s →
      ∃ d : ℝ, d ≤ 0 ∧ HasDerivAt M d s := by
    intro s hs hKs
    have hMpos : 0 < M s := lt_of_le_of_lt hKnonneg hKs
    have hαne : p.α ≠ 0 := ne_of_gt p.hα
    have hKpow : K ^ p.α = p.a / p.b := by
      dsimp [K, massThreshold]
      rw [← Real.rpow_mul (div_nonneg p.ha p.hb),
        one_div_mul_cancel hαne, Real.rpow_one]
    have hMpow : p.a / p.b < (M s) ^ p.α := by
      have hraw := Real.rpow_lt_rpow hKnonneg hKs p.hα
      rwa [hKpow] at hraw
    have hab : p.a < p.b * (M s) ^ p.α := by
      have hmul := mul_lt_mul_of_pos_left hMpow hb
      rwa [mul_div_cancel₀ _ (ne_of_gt hb)] at hmul
    have hlogneg : M s * (p.a - p.b * (M s) ^ p.α) < 0 :=
      mul_neg_of_pos_of_neg hMpos (by linarith)
    let d := p.a * M s - p.b *
      intervalDomain.integral (fun x => (u s x) ^ (1 + p.α))
    refine ⟨d, ?_, ?_⟩
    · calc
        d = deriv (fun τ => intervalDomain.integral (u τ)) s := by
          dsimp [d, M]
          exact (mass_derivative_eq_logistic hsol hs.1 hs.2).symm
        _ ≤ M s * (p.a - p.b * (M s) ^ p.α) := by
          simpa [M] using mass_derivative_le_logistic hsol hs.1 hs.2
        _ ≤ 0 := le_of_lt hlogneg
    · simpa [M, d] using mass_logistic_hasDerivAt hsol hs.1 hs.2
  have habove : ∀ s ∈ Set.Ioc (0 : ℝ) t, K < M s :=
    threshold_persists_below_of_hasDerivAt_nonpos
      ht0 htT hMcont hderiv_nonpos hle
  have hantitone : ∀ s ∈ Set.Ioc (0 : ℝ) t, M t ≤ M s := by
    intro s hs
    have hsub : Set.Icc s t ⊆ Set.Ioo (0 : ℝ) T := fun z hz =>
      ⟨lt_of_lt_of_le hs.1 hz.1, lt_of_le_of_lt hz.2 htT⟩
    have hcont : ContinuousOn M (Set.Icc s t) := hMcont.mono hsub
    have hdiff : DifferentiableOn ℝ M (interior (Set.Icc s t)) := by
      intro z hz
      rw [interior_Icc] at hz
      exact (mass_hasDerivAt hsol
        (lt_trans hs.1 hz.1) (lt_trans hz.2 htT)).differentiableAt.differentiableWithinAt
    have hder : ∀ z ∈ interior (Set.Icc s t), deriv M z ≤ 0 := by
      intro z hz
      rw [interior_Icc] at hz
      have hzT : z ∈ Set.Ioo (0 : ℝ) T :=
        ⟨lt_trans hs.1 hz.1, lt_trans hz.2 htT⟩
      have hzIoc : z ∈ Set.Ioc (0 : ℝ) t :=
        ⟨lt_trans hs.1 hz.1, hz.2.le⟩
      obtain ⟨d, hd, hD⟩ := hderiv_nonpos z hzT (habove z hzIoc)
      calc
        deriv M z = d := hD.deriv
        _ ≤ 0 := hd
    have hanti : AntitoneOn M (Set.Icc s t) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont hdiff hder
    exact hanti (Set.left_mem_Icc.mpr hs.2) (Set.right_mem_Icc.mpr hs.2) hs.2
  have hinit := mass_tendsto_initial hu₀ hsol htrace
  have hMle : M t ≤ intervalDomain.integral u₀ := by
    have hlt : ∀ ε > 0, M t < intervalDomain.integral u₀ + ε := by
      intro ε hε
      obtain ⟨δ, hδpos, hδ⟩ := hinit ε hε
      let s := min (δ / 2) (t / 2)
      have hs0 : 0 < s := lt_min (by linarith) (by linarith)
      have hsδ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hst : s < t := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have h1 := hantitone s ⟨hs0, hst.le⟩
      have h2 := hδ s hs0 hsδ (lt_trans hst htT)
      linarith [(abs_sub_lt_iff.mp h2).1]
    by_contra hnot
    push_neg at hnot
    have hε : 0 < M t - intervalDomain.integral u₀ := by linarith
    linarith [hlt _ hε]
  exact hMle.trans (le_max_left _ _)

/-- The horizon-independent carrying-capacity bound used by the faithful
mass comparison. -/
def uniformMassBoundConstant
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) : ℝ :=
  max |intervalDomain.integral u₀| (massThreshold p)

theorem uniformMassBoundConstant_nonneg
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) :
    0 ≤ uniformMassBoundConstant p u₀ := by
  exact (abs_nonneg _).trans (le_max_left _ _)

/-- The same explicit mass constant works on every finite restriction of a
solution.  In particular, the witness does not depend on the horizon `T`. -/
theorem mass_le_uniformMassBoundConstant_of_guard
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u) :
    ∀ t, 0 < t → t < T →
      intervalDomain.integral (u t) ≤ uniformMassBoundConstant p u₀ := by
  intro t ht0 htT
  have htarget : max (intervalDomain.integral u₀) (massThreshold p) ≤
      uniformMassBoundConstant p u₀ :=
    max_le_max (le_abs_self _) le_rfl
  by_cases hbpos : 0 < p.b
  · exact (mass_le_max_initial_threshold_of_b_pos hbpos hu₀ hsol htrace ht0 htT).trans
      htarget
  · have hbzero : p.b = 0 := le_antisymm (le_of_not_gt hbpos) p.hb
    have hazero : p.a = 0 := hguard.resolve_right hbpos
    exact (mass_le_initial_of_a_eq_b_eq_zero hazero hbzero hu₀ hsol htrace ht0 htT).trans
      ((le_abs_self _).trans (le_max_left _ _))

/-- Uniform mass bound under the corrected theorem guard. -/
theorem uniform_mass_bound_of_guard
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u) :
    ∃ C, 0 ≤ C ∧ ∀ t, 0 < t → t < T →
      intervalDomain.integral (u t) ≤ C := by
  exact ⟨uniformMassBoundConstant p u₀,
    uniformMassBoundConstant_nonneg p u₀,
    mass_le_uniformMassBoundConstant_of_guard hguard hu₀ hsol htrace⟩

#print axioms mass_le_uniformMassBoundConstant_of_guard
#print axioms uniform_mass_bound_of_guard

end

end ShenWork.Paper2.IntervalDomainM
