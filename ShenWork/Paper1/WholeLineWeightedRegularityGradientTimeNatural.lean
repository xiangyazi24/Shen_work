import ShenWork.Paper1.WholeLineWeightedRegularityGradientNatural
import ShenWork.Paper1.WholeLineWeightedRegularityBUCTimeHolder

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Exact-weight time continuity of the population gradient

Uniform BUC continuity of the unweighted spatial derivative controls the
weighted gradient on every bounded spatial interval.  At the endpoint
exponential weight, however, that local information and a uniform `L²`
bound do not by themselves prevent mass from escaping to the right.  This
file isolates the precise additional input: local uniform tightness of the
same-weight square densities.  No stronger exponential weight, second
spatial derivative, generator, or weighted time derivative is used.
-/

/-- The square mass of a scalar field outside the symmetric interval
`[-n,n]`. -/
def wholeLineSquareTail (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in (Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ, f x ^ 2

/-- Local same-weight square tightness at a filter.  This is the exact
no-escape condition missing from a merely bounded family in `L²(ℝ)`. -/
def WholeLineSquareTightAt {ι : Type*}
    (F : ι → ℝ → ℝ) (l : Filter ι) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
    ∀ᶠ s in l, wholeLineSquareTail (F s) n < ε

/-- The tails of one square-integrable field vanish along the symmetric
interval exhaustion. -/
theorem wholeLineSquareTail_tendsto_zero
    {f : ℝ → ℝ} (hf : Integrable (fun x => f x ^ 2) volume) :
    Tendsto (wholeLineSquareTail f) atTop (𝓝 0) := by
  let A : ℕ → Set ℝ := fun n => (Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ
  have hAmeas : ∀ n, MeasurableSet (A n) := fun n => by
    dsimp only [A]
    exact measurableSet_Icc.compl
  have hAanti : Antitone A := by
    intro m n hmn
    apply compl_subset_compl.mpr
    intro x hx
    constructor
    · exact le_trans (by
        exact neg_le_neg (Nat.cast_le.mpr hmn)) hx.1
    · exact hx.2.trans (Nat.cast_le.mpr hmn)
  have hInter : (⋂ n : ℕ, A n) = (∅ : Set ℝ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨N, hN⟩ := exists_nat_ge |x|
      have hxA : x ∈ A N := Set.mem_iInter.mp hx N
      have hxIcc : x ∈ Set.Icc (-(N : ℝ)) (N : ℝ) := by
        rw [abs_le] at hN
        exact hN
      exact (hxA hxIcc).elim
    · intro hx
      exact hx.elim
  have ht := MeasureTheory.tendsto_setIntegral_of_antitone
    (μ := volume) (f := fun x : ℝ => f x ^ 2) (s := A)
    hAmeas hAanti ⟨0, hf.integrableOn⟩
  simpa only [wholeLineSquareTail, A, hInter, Measure.restrict_empty,
    integral_zero_measure] using ht

/-- Square integrability is stable under subtraction. -/
theorem integrable_sq_sub_of_integrable_sq
    {f g : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (hf : Integrable (fun x => f x ^ 2) volume)
    (hg : Integrable (fun x => g x ^ 2) volume) :
    Integrable (fun x => (f x - g x) ^ 2) volume := by
  have hfMem : MemLp f 2 volume :=
    (memLp_two_iff_integrable_sq hf_meas).2 hf
  have hgMem : MemLp g 2 volume :=
    (memLp_two_iff_integrable_sq hg_meas).2 hg
  exact (memLp_two_iff_integrable_sq (hf_meas.sub hg_meas)).1
    (hfMem.sub hgMem)

/-- The square tail of a difference is controlled by the two individual
square tails. -/
theorem wholeLineSquareTail_sub_le
    {f g : ℝ → ℝ} {n : ℕ}
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (hf : Integrable (fun x => f x ^ 2) volume)
    (hg : Integrable (fun x => g x ^ 2) volume) :
    wholeLineSquareTail (fun x => f x - g x) n ≤
      2 * wholeLineSquareTail f n + 2 * wholeLineSquareTail g n := by
  let A : Set ℝ := (Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ
  have hfA : IntegrableOn (fun x => f x ^ 2) A volume :=
    hf.mono_measure Measure.restrict_le_self
  have hgA : IntegrableOn (fun x => g x ^ 2) A volume :=
    hg.mono_measure Measure.restrict_le_self
  have hmajor : IntegrableOn (fun x => 2 * f x ^ 2 + 2 * g x ^ 2) A volume :=
    (hfA.const_mul 2).add (hgA.const_mul 2)
  have hdiffMeas : AEStronglyMeasurable
      (fun x => (f x - g x) ^ 2) (volume.restrict A) := by
    exact ((hf_meas.sub hg_meas).pow 2).mono_measure
      Measure.restrict_le_self
  have hdiff : IntegrableOn (fun x => (f x - g x) ^ 2) A volume := by
    refine hmajor.mono' hdiffMeas ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_sq]
    nlinarith [sq_nonneg (f x + g x)]
  dsimp only [wholeLineSquareTail, A]
  calc
    (∫ x in A, (f x - g x) ^ 2) ≤
        ∫ x in A, (2 * f x ^ 2 + 2 * g x ^ 2) := by
      apply setIntegral_mono_on hdiff hmajor measurableSet_Icc.compl
      intro x _hx
      nlinarith [sq_nonneg (f x + g x)]
    _ = 2 * (∫ x in A, f x ^ 2) + 2 * (∫ x in A, g x ^ 2) := by
      rw [integral_add (hfA.const_mul 2) (hgA.const_mul 2),
        integral_const_mul, integral_const_mul]

/-- Local square convergence plus same-weight tail tightness gives global
strong `L²` convergence.  The target tail is produced internally from its
square integrability. -/
theorem tendsto_integral_sub_sq_zero_of_local_and_tight
    {ι : Type*} {l : Filter ι} {F : ι → ℝ → ℝ} {f : ℝ → ℝ}
    (hF_meas : ∀ s, AEStronglyMeasurable (F s) volume)
    (hf_meas : AEStronglyMeasurable f volume)
    (hF_sq : ∀ s, Integrable (fun x => F s x ^ 2) volume)
    (hf_sq : Integrable (fun x => f x ^ 2) volume)
    (hlocal : ∀ n : ℕ,
      Tendsto (fun s => ∫ x in Set.Icc (-(n : ℝ)) (n : ℝ),
        (F s x - f x) ^ 2) l (𝓝 0))
    (htight : WholeLineSquareTightAt F l) :
    Tendsto (fun s => ∫ x : ℝ, (F s x - f x) ^ 2) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨nF, hFtail⟩ := htight (ε / 16) (by positivity)
  have hftailT := wholeLineSquareTail_tendsto_zero hf_sq
  have hftailEventually : ∀ᶠ n : ℕ in atTop,
      wholeLineSquareTail f n < ε / 16 :=
    by
      have he := (Metric.tendsto_nhds.1 hftailT) (ε / 16) (by positivity)
      filter_upwards [he] with n hn
      rw [Real.dist_eq, sub_zero] at hn
      exact (le_abs_self (wholeLineSquareTail f n)).trans_lt hn
  obtain ⟨n0, hn0⟩ := (eventually_atTop.1 hftailEventually)
  let n : ℕ := max nF n0
  have hFtailN : ∀ᶠ s in l,
      wholeLineSquareTail (F s) n < ε / 16 := by
    filter_upwards [hFtail] with s hs
    have hanti : wholeLineSquareTail (F s) n ≤
        wholeLineSquareTail (F s) nF := by
      unfold wholeLineSquareTail
      refine integral_mono_measure ?_ ?_ ?_
      · exact Measure.restrict_mono_set volume (by
          apply compl_subset_compl.mpr
          intro x hx
          constructor
          · exact le_trans
              (neg_le_neg (Nat.cast_le.mpr (Nat.le_max_left _ _))) hx.1
          · exact hx.2.trans (Nat.cast_le.mpr (Nat.le_max_left _ _)))
      · exact Eventually.of_forall fun _ => sq_nonneg _
      · exact (hF_sq s).mono_measure Measure.restrict_le_self
    exact hanti.trans_lt hs
  have hftailN : wholeLineSquareTail f n < ε / 16 := by
    exact hn0 n (Nat.le_max_right _ _)
  have hlocalN : ∀ᶠ s in l,
      dist (∫ x in Set.Icc (-(n : ℝ)) (n : ℝ),
        (F s x - f x) ^ 2) 0 < ε / 2 :=
    (Metric.tendsto_nhds.1 (hlocal n)) (ε / 2) (by positivity)
  filter_upwards [hFtailN, hlocalN] with s hsTail hsLocal
  have hdiff := integrable_sq_sub_of_integrable_sq
    (hF_meas s) hf_meas (hF_sq s) hf_sq
  have hsplit := MeasureTheory.integral_add_compl
    (s := Set.Icc (-(n : ℝ)) (n : ℝ)) measurableSet_Icc hdiff
  have htailDiff := wholeLineSquareTail_sub_le
    (n := n) (hF_meas s) hf_meas (hF_sq s) hf_sq
  have hlocalNonneg : 0 ≤ ∫ x in Set.Icc (-(n : ℝ)) (n : ℝ),
      (F s x - f x) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hlocalLt : (∫ x in Set.Icc (-(n : ℝ)) (n : ℝ),
      (F s x - f x) ^ 2) < ε / 2 := by
    simpa [Real.dist_eq, abs_of_nonneg hlocalNonneg] using hsLocal
  have hfullNonneg : 0 ≤ ∫ x : ℝ, (F s x - f x) ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hfullNonneg]
  rw [← hsplit]
  have htailLt : wholeLineSquareTail (fun x => F s x - f x) n < ε / 4 := by
    calc
      wholeLineSquareTail (fun x => F s x - f x) n ≤
          2 * wholeLineSquareTail (F s) n + 2 * wholeLineSquareTail f n :=
        htailDiff
      _ < 2 * (ε / 16) + 2 * (ε / 16) := by gcongr
      _ = ε / 4 := by ring
  have htailLt' :
      (∫ x in (Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ,
        (F s x - f x) ^ 2) < ε / 4 := by
    simpa only [wholeLineSquareTail] using htailLt
  linarith

/-! ## Specialization to the weighted population gradient -/

/-- On a symmetric compact interval, uniform-in-space moduli for the
population and its unweighted first derivative control the exact weighted
gradient difference.  The wave profile cancels from the difference. -/
theorem paper5WeightedPopulationX_sub_abs_le_on_Icc
    {eta s t D0 D1 : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hval : ∀ x, |u s x - u t x| ≤ D0)
    (hderiv : ∀ x, |deriv (u s) x - deriv (u t) x| ≤ D1)
    (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-(n : ℝ)) (n : ℝ)) :
    |paper5WeightedPopulationX eta u U s x -
        paper5WeightedPopulationX eta u U t x| ≤
      Real.exp (|eta| * (n : ℝ)) * (|eta| * D0 + D1) := by
  have hxabs : |x| ≤ (n : ℝ) := by
    rw [abs_le]
    exact hx
  have hetaX : eta * x ≤ |eta| * (n : ℝ) := by
    calc
      eta * x ≤ |eta * x| := le_abs_self _
      _ = |eta| * |x| := abs_mul _ _
      _ ≤ |eta| * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hxabs (abs_nonneg eta)
  have hexp : Real.exp (eta * x) ≤ Real.exp (|eta| * (n : ℝ)) :=
    Real.exp_le_exp.mpr hetaX
  have hinner :
      |eta * (u s x - u t x) +
          (deriv (u s) x - deriv (u t) x)| ≤
        |eta| * D0 + D1 := by
    calc
      |eta * (u s x - u t x) +
          (deriv (u s) x - deriv (u t) x)| ≤
          |eta * (u s x - u t x)| +
            |deriv (u s) x - deriv (u t) x| := abs_add_le _ _
      _ = |eta| * |u s x - u t x| +
          |deriv (u s) x - deriv (u t) x| := by rw [abs_mul]
      _ ≤ |eta| * D0 + D1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hval x) (abs_nonneg eta))
          (hderiv x)
  rw [show
      paper5WeightedPopulationX eta u U s x -
          paper5WeightedPopulationX eta u U t x =
        Real.exp (eta * x) *
          (eta * (u s x - u t x) +
            (deriv (u s) x - deriv (u t) x)) by
    unfold paper5WeightedPopulationX paper5WeightedPopulation
    ring]
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul hexp hinner
    (by positivity) (Real.exp_nonneg _)

/-- The already-proved BUC time moduli imply strong square convergence of
the exact weighted population gradient on every compact spatial interval.
This is the local half of the endpoint-weight argument and uses no tail
reserve. -/
theorem paper5WeightedPopulationX_local_integral_sub_sq_tendsto_zero_of_BUC_moduli
    {eta t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {D0 D1 : ℝ → ℝ} {l : Filter ℝ}
    (hWx_meas : ∀ s,
      AEStronglyMeasurable (paper5WeightedPopulationX eta u U s) volume)
    (hWx_sq : ∀ s, Integrable (fun x =>
      paper5WeightedPopulationX eta u U s x ^ 2) volume)
    (hD0_nonneg : ∀ᶠ s in l, 0 ≤ D0 s)
    (hD1_nonneg : ∀ᶠ s in l, 0 ≤ D1 s)
    (hD0 : Tendsto D0 l (𝓝 0))
    (hD1 : Tendsto D1 l (𝓝 0))
    (hval : ∀ᶠ s in l, ∀ x, |u s x - u t x| ≤ D0 s)
    (hderiv : ∀ᶠ s in l, ∀ x,
      |deriv (u s) x - deriv (u t) x| ≤ D1 s)
    (n : ℕ) :
    Tendsto (fun s => ∫ x in Set.Icc (-(n : ℝ)) (n : ℝ),
      (paper5WeightedPopulationX eta u U s x -
        paper5WeightedPopulationX eta u U t x) ^ 2) l (𝓝 0) := by
  let B : ℝ → ℝ := fun s =>
    Real.exp (|eta| * (n : ℝ)) * (|eta| * D0 s + D1 s)
  have hB : Tendsto B l (𝓝 0) := by
    have hetaD0 : Tendsto (fun s => |eta| * D0 s) l
        (𝓝 (|eta| * 0)) := tendsto_const_nhds.mul hD0
    have hinner : Tendsto (fun s => |eta| * D0 s + D1 s) l
        (𝓝 (|eta| * 0 + 0)) := hetaD0.add hD1
    have hout : Tendsto
        (fun s => Real.exp (|eta| * (n : ℝ)) *
          (|eta| * D0 s + D1 s)) l
        (𝓝 (Real.exp (|eta| * (n : ℝ)) * (|eta| * 0 + 0))) :=
      tendsto_const_nhds.mul hinner
    simpa only [B, mul_zero, add_zero] using hout
  have hmajor : Tendsto (fun s => (2 * n : ℝ) * B s ^ 2) l (𝓝 0) := by
    simpa only [mul_zero, zero_pow (by norm_num : 2 ≠ 0)] using
      tendsto_const_nhds.mul (hB.pow 2)
  refine squeeze_zero'
    (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _) ?_ hmajor
  filter_upwards [hD0_nonneg, hD1_nonneg, hval, hderiv] with
      s hsD0 hsD1 hsVal hsDeriv
  let A : Set ℝ := Set.Icc (-(n : ℝ)) (n : ℝ)
  let G : ℝ → ℝ := fun x =>
      (paper5WeightedPopulationX eta u U s x -
        paper5WeightedPopulationX eta u U t x) ^ 2
  have hG : Integrable G volume := by
    exact integrable_sq_sub_of_integrable_sq
      (hWx_meas s) (hWx_meas t) (hWx_sq s) (hWx_sq t)
  have hGA : IntegrableOn G A volume :=
    hG.mono_measure Measure.restrict_le_self
  have hconst : IntegrableOn (fun _x : ℝ => B s ^ 2) A volume := by
    exact integrableOn_const (by simp [A, Real.volume_Icc])
  have hpoint : ∀ x ∈ A, G x ≤ B s ^ 2 := by
    intro x hx
    have habs := paper5WeightedPopulationX_sub_abs_le_on_Icc
      (eta := eta) (U := U) hsVal hsDeriv n hx
    dsimp only [G]
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) (by dsimp [B]; positivity)).2 habs
  calc
    (∫ x in Set.Icc (-(n : ℝ)) (n : ℝ),
        (paper5WeightedPopulationX eta u U s x -
          paper5WeightedPopulationX eta u U t x) ^ 2) =
        ∫ x in A, G x := rfl
    _ ≤ ∫ x in A, B s ^ 2 :=
      setIntegral_mono_on hGA hconst measurableSet_Icc hpoint
    _ = (2 * n : ℝ) * B s ^ 2 := by
      rw [setIntegral_const, Measure.real_def, Real.volume_Icc]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [ENNReal.toReal_ofReal (by linarith :
        (0 : ℝ) ≤ (n : ℝ) - -(n : ℝ))]
      simp only [smul_eq_mul]
      ring

/-- Endpoint-weight strong continuity of the population gradient from the
natural BUC time moduli and the one genuinely additional condition: uniform
same-weight square tightness near the target time. -/
theorem paper5WeightedPopulationX_strongL2At_of_BUC_moduli_and_tight
    {eta t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {D0 D1 : ℝ → ℝ} {l : Filter ℝ}
    (hWx_meas : ∀ s,
      AEStronglyMeasurable (paper5WeightedPopulationX eta u U s) volume)
    (hWx_sq : ∀ s, Integrable (fun x =>
      paper5WeightedPopulationX eta u U s x ^ 2) volume)
    (hD0_nonneg : ∀ᶠ s in l, 0 ≤ D0 s)
    (hD1_nonneg : ∀ᶠ s in l, 0 ≤ D1 s)
    (hD0 : Tendsto D0 l (𝓝 0))
    (hD1 : Tendsto D1 l (𝓝 0))
    (hval : ∀ᶠ s in l, ∀ x, |u s x - u t x| ≤ D0 s)
    (hderiv : ∀ᶠ s in l, ∀ x,
      |deriv (u s) x - deriv (u t) x| ≤ D1 s)
    (htight : WholeLineSquareTightAt
      (paper5WeightedPopulationX eta u U) l) :
    Tendsto (fun s => ∫ x : ℝ,
      (paper5WeightedPopulationX eta u U s x -
        paper5WeightedPopulationX eta u U t x) ^ 2) l (𝓝 0) := by
  exact tendsto_integral_sub_sq_zero_of_local_and_tight
    hWx_meas (hWx_meas t) hWx_sq (hWx_sq t)
    (fun n =>
      paper5WeightedPopulationX_local_integral_sub_sq_tendsto_zero_of_BUC_moduli
        hWx_meas hWx_sq hD0_nonneg hD1_nonneg hD0 hD1 hval hderiv n)
    htight

/-- Pair form matching the `hWx_strong` input of the natural forcing
continuity producer.  Difference-square integrability is automatic from
the static exact-weight `H¹` slices. -/
theorem paper5WeightedPopulationX_eventually_integrable_and_strongL2At_of_BUC_moduli_and_tight
    {eta t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {D0 D1 : ℝ → ℝ} {l : Filter ℝ}
    (hWx_meas : ∀ s,
      AEStronglyMeasurable (paper5WeightedPopulationX eta u U s) volume)
    (hWx_sq : ∀ s, Integrable (fun x =>
      paper5WeightedPopulationX eta u U s x ^ 2) volume)
    (hD0_nonneg : ∀ᶠ s in l, 0 ≤ D0 s)
    (hD1_nonneg : ∀ᶠ s in l, 0 ≤ D1 s)
    (hD0 : Tendsto D0 l (𝓝 0))
    (hD1 : Tendsto D1 l (𝓝 0))
    (hval : ∀ᶠ s in l, ∀ x, |u s x - u t x| ≤ D0 s)
    (hderiv : ∀ᶠ s in l, ∀ x,
      |deriv (u s) x - deriv (u t) x| ≤ D1 s)
    (htight : WholeLineSquareTightAt
      (paper5WeightedPopulationX eta u U) l) :
    (∀ᶠ s in l, Integrable (fun x =>
      (paper5WeightedPopulationX eta u U s x -
        paper5WeightedPopulationX eta u U t x) ^ 2) volume) ∧
      Tendsto (fun s => ∫ x : ℝ,
        (paper5WeightedPopulationX eta u U s x -
          paper5WeightedPopulationX eta u U t x) ^ 2) l (𝓝 0) := by
  refine ⟨Eventually.of_forall fun s => ?_, ?_⟩
  · exact integrable_sq_sub_of_integrable_sq
      (hWx_meas s) (hWx_meas t) (hWx_sq s) (hWx_sq t)
  · exact paper5WeightedPopulationX_strongL2At_of_BUC_moduli_and_tight
      hWx_meas hWx_sq hD0_nonneg hD1_nonneg hD0 hD1 hval hderiv htight

/-! ## Why tightness is load-bearing -/

/-- Unit `L²` mass translated to the right. -/
def wholeLineEscapingUnitBump (n : ℕ) (x : ℝ) : ℝ :=
  (Set.Ioc (n : ℝ) (n + 1 : ℝ)).indicator (fun _ => (1 : ℝ)) x

theorem wholeLineEscapingUnitBump_sq_integrable (n : ℕ) :
    Integrable (fun x => wholeLineEscapingUnitBump n x ^ 2) volume := by
  have hbase : IntegrableOn (fun _x : ℝ => (1 : ℝ))
      (Set.Ioc (n : ℝ) (n + 1 : ℝ)) volume :=
    integrableOn_const (by simp [Real.volume_Ioc])
  have hi := hbase.integrable_indicator measurableSet_Ioc
  refine hi.congr (Eventually.of_forall fun x => ?_)
  simp only [wholeLineEscapingUnitBump, Set.indicator_apply]
  split_ifs <;> simp

/-- Every escaping bump has exactly unit square mass. -/
theorem wholeLineEscapingUnitBump_integral_sq_eq_one (n : ℕ) :
    (∫ x : ℝ, wholeLineEscapingUnitBump n x ^ 2) = 1 := by
  rw [show (fun x : ℝ => wholeLineEscapingUnitBump n x ^ 2) =
      (Set.Ioc (n : ℝ) (n + 1 : ℝ)).indicator (fun _ => (1 : ℝ)) by
    funext x
    simp only [wholeLineEscapingUnitBump, Set.indicator_apply]
    split_ifs <;> simp]
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    MeasureTheory.setIntegral_one_eq_measureReal, Measure.real,
    Real.volume_Ioc]
  norm_num

/-- The escaping bumps converge pointwise to zero. -/
theorem wholeLineEscapingUnitBump_tendsto_zero_pointwise (x : ℝ) :
    Tendsto (fun n => wholeLineEscapingUnitBump n x) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := exists_nat_gt x
  have heq : (fun n => wholeLineEscapingUnitBump n x) =ᶠ[atTop]
      fun _ => (0 : ℝ) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [wholeLineEscapingUnitBump, Set.indicator_of_notMem]
    intro hx
    exact (not_lt_of_ge (hN.le.trans
      (show (N : ℝ) ≤ n by exact_mod_cast hn))) hx.1
  exact (tendsto_congr' heq).2 tendsto_const_nhds

/-- Pointwise convergence and a uniform exact `L²` bound do not imply
strong `L²` convergence: the square mass can escape to spatial infinity. -/
theorem wholeLineEscapingUnitBump_not_strongL2_zero :
    ¬ Tendsto (fun n => ∫ x : ℝ, wholeLineEscapingUnitBump n x ^ 2)
        atTop (𝓝 0) := by
  intro hzero
  have hone : Tendsto
      (fun n => ∫ x : ℝ, wholeLineEscapingUnitBump n x ^ 2)
      atTop (𝓝 1) := by
    simpa only [wholeLineEscapingUnitBump_integral_sq_eq_one] using
      (tendsto_const_nhds : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hbad : (1 : ℝ) = 0 := tendsto_nhds_unique hone hzero
  norm_num at hbad

/-- Once the bump has moved past a fixed symmetric cutoff, all of its unit
mass lies in the corresponding tail. -/
theorem wholeLineSquareTail_escapingUnitBump_eq_one
    {k n : ℕ} (hkn : k ≤ n) :
    wholeLineSquareTail (wholeLineEscapingUnitBump n) k = 1 := by
  unfold wholeLineSquareTail
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact wholeLineEscapingUnitBump_integral_sq_eq_one n
  · intro x hx
    have hxIcc : x ∈ Set.Icc (-(k : ℝ)) (k : ℝ) := by
      simpa using hx
    have hxNot : x ∉ Set.Ioc (n : ℝ) (n + 1 : ℝ) := by
      intro hxBump
      have hkcast : (k : ℝ) ≤ n := by exact_mod_cast hkn
      exact (not_lt_of_ge (hxIcc.2.trans hkcast)) hxBump.1
    simp [wholeLineEscapingUnitBump, hxNot]

/-- The escaping family fails exactly the no-escape condition used above. -/
theorem wholeLineEscapingUnitBump_not_squareTightAt :
    ¬ WholeLineSquareTightAt wholeLineEscapingUnitBump atTop := by
  intro htight
  obtain ⟨k, hk⟩ := htight (1 / 2 : ℝ) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hk
  have htail := hN (max N k) (Nat.le_max_left _ _)
  have hkn : k ≤ max N k := Nat.le_max_right _ _
  rw [wholeLineSquareTail_escapingUnitBump_eq_one hkn] at htail
  norm_num at htail

section AxiomAudit

#print axioms wholeLineSquareTail_tendsto_zero
#print axioms tendsto_integral_sub_sq_zero_of_local_and_tight
#print axioms
  paper5WeightedPopulationX_local_integral_sub_sq_tendsto_zero_of_BUC_moduli
#print axioms paper5WeightedPopulationX_strongL2At_of_BUC_moduli_and_tight
#print axioms
  paper5WeightedPopulationX_eventually_integrable_and_strongL2At_of_BUC_moduli_and_tight
#print axioms wholeLineEscapingUnitBump_not_strongL2_zero
#print axioms wholeLineEscapingUnitBump_not_squareTightAt

end AxiomAudit

end ShenWork.Paper1
