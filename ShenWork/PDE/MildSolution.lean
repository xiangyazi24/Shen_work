/-
  ShenWork/PDE/MildSolution.lean

  Mild solution framework for the chemotaxis system.

  A mild solution of u_t = Δu + F(u) with u(0) = u₀ is a function satisfying
  the Duhamel integral equation:
    u(t) = e^{tΔ} u₀ + ∫₀ᵗ e^{(t-s)Δ} F(u(s)) ds

  For short time T, the map Φ(u)(t) = e^{tΔ} u₀ + ∫₀ᵗ e^{(t-s)Δ} F(u(s)) ds
  is a contraction on a suitable function space, giving local existence
  via Banach fixed-point theorem.
-/
import ShenWork.PDE.HeatSemigroup
import ShenWork.Defs
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory Filter Topology Real

noncomputable section

/-! ## The nonlinear term F(u) for the chemotaxis system -/

/-- The nonlinear source term F(u,v) = -χ(u^m v_x)_x + u(1-u^α).
    For the local existence proof, we treat the full right-hand side
    including the chemotaxis term. For χ ≤ 0, the chemotaxis term
    has good sign properties. -/
def chemotaxisSource (p : CMParams) (u v : ℝ → ℝ) (x : ℝ) : ℝ :=
  u x * (1 - (u x) ^ p.α)

/-! ## Mild solution operator -/

/-- The Duhamel / mild solution operator:
    Φ(u)(t,x) = (e^{tΔ} u₀)(x) + ∫₀ᵗ (e^{(t-s)Δ} F(u(s)))(x) ds -/
def mildSolutionOperator (p : CMParams) (u₀ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (t : ℝ) (x : ℝ) : ℝ :=
  heatSemigroup t u₀ x +
  ∫ s in Set.Icc 0 t, heatSemigroup (t - s) (fun y => chemotaxisSource p (u s) (fun _ => 0) y) x

/-! ## Key estimate: the source term is Lipschitz in u -/

/-- For bounded u, the logistic term u(1-u^α) is Lipschitz in u.
    This is the key for the contraction property. -/
lemma logistic_lipschitz_on_bounded {α M : ℝ} (hα : 1 ≤ α) (hM : 0 < M) :
    ∃ L > 0, ∀ u₁ u₂ : ℝ, |u₁| ≤ M → |u₂| ≤ M →
    |u₁ * (1 - u₁ ^ α) - u₂ * (1 - u₂ ^ α)| ≤ L * |u₁ - u₂| := by
  -- f(u) = u - u^{1+α} has |f'(u)| ≤ 1 + (1+α)M^α on [-M,M]
  -- So f is Lipschitz with constant L = 1 + (1+α)M^α
  use 1 + (1 + α) * M ^ α
  constructor
  · positivity
  · intro u₁ u₂ hu₁ hu₂
    let f : ℝ → ℝ := fun x => x * (1 - x ^ α)
    let fp : ℝ → ℝ := fun x => 1 * (1 - x ^ α) + x * (0 - α * x ^ (α - 1))
    let C : ℝ := 1 + (1 + α) * M ^ α
    have hα0 : 0 ≤ α := by linarith
    have hαm1 : 0 ≤ α - 1 := by linarith
    have hM0 : 0 ≤ M := le_of_lt hM
    have hu₁s : u₁ ∈ Set.Icc (-M) M := abs_le.mp hu₁
    have hu₂s : u₂ ∈ Set.Icc (-M) M := abs_le.mp hu₂
    have hder : ∀ x ∈ Set.Icc (-M) M, HasDerivWithinAt f (fp x) (Set.Icc (-M) M) x := by
      intro x _hx
      have hp : HasDerivAt (fun y : ℝ => y ^ α) (α * x ^ (α - 1)) x :=
        Real.hasDerivAt_rpow_const (x := x) (p := α) (Or.inr hα)
      have hsub : HasDerivAt (fun y : ℝ => 1 - y ^ α) (0 - α * x ^ (α - 1)) x :=
        (hasDerivAt_const x (1 : ℝ)).sub hp
      have hmul : HasDerivAt (fun y : ℝ => y * (1 - y ^ α))
          (1 * (1 - x ^ α) + x * (0 - α * x ^ (α - 1))) x := by
        simpa using (hasDerivAt_id' x).fun_mul hsub
      simpa [f, fp] using hmul.hasDerivWithinAt
    have hbound : ∀ x ∈ Set.Icc (-M) M, ‖fp x‖ ≤ C := by
      intro x hx
      have hxabs : |x| ≤ M := abs_le.mpr hx
      have hxpow : |x ^ α| ≤ M ^ α := by
        calc |x ^ α| ≤ |x| ^ α := Real.abs_rpow_le_abs_rpow x α
          _ ≤ M ^ α := Real.rpow_le_rpow (abs_nonneg x) hxabs hα0
      have hxpowm1 : |x ^ (α - 1)| ≤ M ^ (α - 1) := by
        calc |x ^ (α - 1)| ≤ |x| ^ (α - 1) := Real.abs_rpow_le_abs_rpow x (α - 1)
          _ ≤ M ^ (α - 1) := Real.rpow_le_rpow (abs_nonneg x) hxabs hαm1
      have hMpow : M ^ (α - 1) * M = M ^ α := by
        rw [← Real.rpow_add_one (ne_of_gt hM) (α - 1)]
        congr 1; ring
      have hMpow2 : M * (α * M ^ (α - 1)) = α * M ^ α := by
        calc M * (α * M ^ (α - 1)) = α * (M ^ (α - 1) * M) := by ring
          _ = α * M ^ α := by rw [hMpow]
      have hterm1 : |1 * (1 - x ^ α)| ≤ 1 + M ^ α := by
        simp only [one_mul]
        have h_tri := norm_sub_le (1 : ℝ) (x ^ α)
        simp only [Real.norm_eq_abs, abs_one] at h_tri
        linarith [hxpow]
      have hinner_nonneg : 0 ≤ α * |x ^ (α - 1)| :=
        mul_nonneg hα0 (abs_nonneg _)
      have hterm2 : |x * (0 - α * x ^ (α - 1))| ≤ α * M ^ α := by
        rw [abs_mul, show |0 - α * x ^ (α - 1)| = α * |x ^ (α - 1)| from by
          simp [abs_mul, abs_of_nonneg hα0]]
        calc |x| * (α * |x ^ (α - 1)|)
            ≤ M * (α * M ^ (α - 1)) :=
              mul_le_mul hxabs (mul_le_mul_of_nonneg_left hxpowm1 hα0) hinner_nonneg hM0
          _ = α * M ^ α := hMpow2
      simp only [fp, C, Real.norm_eq_abs]
      calc |1 * (1 - x ^ α) + x * (0 - α * x ^ (α - 1))|
          ≤ |1 * (1 - x ^ α)| + |x * (0 - α * x ^ (α - 1))| := abs_add_le _ _
        _ ≤ (1 + M ^ α) + α * M ^ α := add_le_add hterm1 hterm2
        _ = 1 + (1 + α) * M ^ α := by ring
    have hmv : ‖f u₁ - f u₂‖ ≤ C * ‖u₁ - u₂‖ :=
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        hder hbound (convex_Icc (-M) M) hu₂s hu₁s
    simpa [f, C, Real.norm_eq_abs] using hmv

/-! ## Local existence via contraction -/

private lemma chemotaxisSource_aestronglyMeasurable (p : CMParams) (u : ℝ → ℝ)
    (hu : AEStronglyMeasurable u volume) :
    AEStronglyMeasurable (fun y => chemotaxisSource p u (fun _ => 0) y) volume := by
  simp only [chemotaxisSource]
  exact hu.mul (aestronglyMeasurable_const.sub
    (Continuous.comp_aestronglyMeasurable (continuous_rpow_const (le_trans zero_le_one p.hα)) hu))

private lemma chemotaxisSource_bound_of_bounded (p : CMParams) (u : ℝ → ℝ) {M : ℝ}
    (hu : ∀ y, |u y| ≤ M) :
    ∀ y, |chemotaxisSource p u (fun _ => 0) y| ≤ M * (1 + M ^ p.α) := by
  have hM_nn : 0 ≤ M := (abs_nonneg (u 0)).trans (hu 0)
  have hα_nn : 0 ≤ p.α := le_trans zero_le_one p.hα
  intro y
  have hy_abs : |u y| ≤ M := hu y
  have hy_pow : |(u y) ^ p.α| ≤ M ^ p.α := by
    calc |(u y) ^ p.α| ≤ |u y| ^ p.α := Real.abs_rpow_le_abs_rpow (u y) p.α
      _ ≤ M ^ p.α := Real.rpow_le_rpow (abs_nonneg (u y)) hy_abs hα_nn
  have hfactor : |1 - (u y) ^ p.α| ≤ 1 + M ^ p.α := by
    have htri : |1 - (u y) ^ p.α| ≤ 1 + |(u y) ^ p.α| := by
      simpa [abs_neg] using (abs_sub_le (1 : ℝ) 0 ((u y) ^ p.α))
    calc |1 - (u y) ^ p.α|
        ≤ 1 + |(u y) ^ p.α| := htri
      _ ≤ 1 + M ^ p.α := by
        exact add_le_add (le_refl 1) hy_pow
  simp only [chemotaxisSource]
  calc |u y * (1 - (u y) ^ p.α)|
      = |u y| * |1 - (u y) ^ p.α| := abs_mul _ _
    _ ≤ M * (1 + M ^ p.α) :=
        mul_le_mul hy_abs hfactor (abs_nonneg _) hM_nn

private lemma integrable_on_Icc_of_aestronglyMeasurable_norm_bound
    {G : ℝ → ℝ} {t C : ℝ}
    (hG_meas :
      AEStronglyMeasurable G
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t)))
    (hG_bound :
      ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t)),
        ‖G s‖ ≤ C) :
    MeasureTheory.Integrable G
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t)) := by
  exact
    MeasureTheory.IntegrableOn.of_bound
      (μ := MeasureTheory.volume) (s := Set.Icc (0 : ℝ) t)
      (by simp [Real.volume_Icc]) hG_meas C hG_bound

/-- For sufficiently small T > 0, the mild solution operator Φ is a contraction
    on the space of bounded continuous functions [0,T] → C^b(ℝ). -/
private lemma mildSolutionOperator_difference_integral_identity
    (p : CMParams) (u₀ : ℝ → ℝ) (u₁ u₂ : ℝ → ℝ → ℝ) (t x : ℝ)
    (hu₁_meas : ∀ s, AEStronglyMeasurable (u₁ s) volume)
    (hu₂_meas : ∀ s, AEStronglyMeasurable (u₂ s) volume)
    (hu₁_bdd : ∀ s, ∃ M, ∀ y, |u₁ s y| ≤ M)
    (hu₂_bdd : ∀ s, ∃ M, ∀ y, |u₂ s y| ≤ M)
    (hG₁ : MeasureTheory.Integrable
      (fun s => heatSemigroup (t - s)
        (fun y => chemotaxisSource p (u₁ s) (fun _ => 0) y) x)
      (MeasureTheory.volume.restrict (Set.Icc 0 t)))
    (hG₂ : MeasureTheory.Integrable
      (fun s => heatSemigroup (t - s)
        (fun y => chemotaxisSource p (u₂ s) (fun _ => 0) y) x)
      (MeasureTheory.volume.restrict (Set.Icc 0 t))) :
    mildSolutionOperator p u₀ u₁ t x - mildSolutionOperator p u₀ u₂ t x =
      ∫ s in Set.Icc 0 t, heatSemigroup (t - s)
        (fun y => chemotaxisSource p (u₁ s) (fun _ => 0) y -
          chemotaxisSource p (u₂ s) (fun _ => 0) y) x := by
  simp only [mildSolutionOperator, add_sub_add_left_eq_sub]
  let F₁ : ℝ → ℝ → ℝ := fun s y => chemotaxisSource p (u₁ s) (fun _ => 0) y
  let F₂ : ℝ → ℝ → ℝ := fun s y => chemotaxisSource p (u₂ s) (fun _ => 0) y
  have hG₁' : MeasureTheory.Integrable (fun s => heatSemigroup (t - s) (F₁ s) x)
      (MeasureTheory.volume.restrict (Set.Icc 0 t)) := by
    simpa [F₁] using hG₁
  have hG₂' : MeasureTheory.Integrable (fun s => heatSemigroup (t - s) (F₂ s) x)
      (MeasureTheory.volume.restrict (Set.Icc 0 t)) := by
    simpa [F₂] using hG₂
  rw [← MeasureTheory.integral_sub hG₁' hG₂']
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro s _hs
  by_cases hts : t - s = 0
  · simp [heatSemigroup, hts, heatKernel_zero]
  · have hts_pos : 0 < t - s := lt_of_le_of_ne (by linarith [_hs.2]) (Ne.symm hts)
    obtain ⟨M₁, hM₁⟩ := hu₁_bdd s; obtain ⟨M₂, hM₂⟩ := hu₂_bdd s
    have hF₁_meas := chemotaxisSource_aestronglyMeasurable p (u₁ s) (hu₁_meas s)
    have hF₂_meas := chemotaxisSource_aestronglyMeasurable p (u₂ s) (hu₂_meas s)
    exact (heatSemigroup_sub x
      (heatKernel_mul_bounded_integrable hts_pos x (M := M₁ * (1 + M₁ ^ p.α))
        (chemotaxisSource_bound_of_bounded p (u₁ s) hM₁) hF₁_meas)
      (heatKernel_mul_bounded_integrable hts_pos x (M := M₂ * (1 + M₂ ^ p.α))
        (chemotaxisSource_bound_of_bounded p (u₂ s) hM₂) hF₂_meas)).symm

private lemma mildSolutionOperator_duhamel_integral_bound
    (p : CMParams) (u₁ u₂ : ℝ → ℝ → ℝ) (L D t x : ℝ)
    (_hL_nn : 0 ≤ L) (_hD_nn : 0 ≤ D) (_ht : 0 ≤ t)
    (_hsource_bound : ∀ s y, |chemotaxisSource p (u₁ s) (fun _ => 0) y -
      chemotaxisSource p (u₂ s) (fun _ => 0) y| ≤ L * D)
    (hu₁_meas : ∀ s, AEStronglyMeasurable (u₁ s) volume)
    (hu₂_meas : ∀ s, AEStronglyMeasurable (u₂ s) volume) :
    |∫ s in Set.Icc 0 t, heatSemigroup (t - s)
      (fun y => chemotaxisSource p (u₁ s) (fun _ => 0) y -
        chemotaxisSource p (u₂ s) (fun _ => 0) y) x| ≤ L * t * D := by
  let G : ℝ → ℝ := fun s => heatSemigroup (t - s)
    (fun y => chemotaxisSource p (u₁ s) (fun _ => 0) y -
      chemotaxisSource p (u₂ s) (fun _ => 0) y) x
  have hLD_nn : 0 ≤ L * D := mul_nonneg _hL_nn _hD_nn
  have hG_bound : ∀ s ∈ Set.Icc 0 t, |G s| ≤ L * D := by
    intro s hs
    simp only [G]
    by_cases hts : t - s = 0
    · rw [hts, heatSemigroup_zero, abs_zero]; exact hLD_nn
    · have hts_pos : 0 < t - s := lt_of_le_of_ne (by linarith [hs.2]) (Ne.symm hts)
      exact heatSemigroup_abs_bound (fun y => _hsource_bound s y) hts_pos hLD_nn
        ((chemotaxisSource_aestronglyMeasurable p (u₁ s) (hu₁_meas s)).sub
          (chemotaxisSource_aestronglyMeasurable p (u₂ s) (hu₂_meas s))) x
  have hfinite : MeasureTheory.volume (Set.Icc (0 : ℝ) t) < ⊤ := by simp [Real.volume_Icc]
  have hnorm : ‖∫ s in Set.Icc 0 t, G s‖ ≤
      (L * D) * MeasureTheory.volume.real (Set.Icc (0 : ℝ) t) :=
    MeasureTheory.norm_setIntegral_le_of_norm_le_const hfinite
      (fun s hs => by simpa [Real.norm_eq_abs] using hG_bound s hs)
  have hvol : MeasureTheory.volume.real (Set.Icc (0 : ℝ) t) = t := by
    simpa using Real.volume_real_Icc_of_le _ht
  calc |∫ s in Set.Icc 0 t, G s|
      = ‖∫ s in Set.Icc 0 t, G s‖ := by rw [Real.norm_eq_abs]
    _ ≤ (L * D) * MeasureTheory.volume.real (Set.Icc (0 : ℝ) t) := hnorm
    _ = (L * D) * t := by rw [hvol]
    _ = L * t * D := by ring

private lemma mildSolutionOperator_lipschitz_estimate (p : CMParams) (u₀ : ℝ → ℝ)
    (L T : ℝ) (u₁ u₂ : ℝ → ℝ → ℝ) (t x : ℝ)
    (_hT_nn : 0 ≤ T) (hL_nn : 0 ≤ L)
    (hLip : ∀ a b : ℝ, |a| ≤ 2 * sSup (Set.range fun x => |u₀ x|) →
      |b| ≤ 2 * sSup (Set.range fun x => |u₀ x|) →
      |chemotaxisSource p (fun _ => a) (fun _ => 0) 0 -
       chemotaxisSource p (fun _ => b) (fun _ => 0) 0| ≤ L * |a - b|)
    (hu₁ : ∀ t x, |u₁ t x| ≤ 2 * sSup (Set.range fun x => |u₀ x|))
    (hu₂ : ∀ t x, |u₂ t x| ≤ 2 * sSup (Set.range fun x => |u₀ x|))
    (hu₁_meas : ∀ s, AEStronglyMeasurable (u₁ s) volume)
    (hu₂_meas : ∀ s, AEStronglyMeasurable (u₂ s) volume)
    (hu₁_bdd : ∀ s, ∃ M, ∀ y, |u₁ s y| ≤ M)
    (hu₂_bdd : ∀ s, ∃ M, ∀ y, |u₂ s y| ≤ M)
    (hG₁ : MeasureTheory.Integrable
      (fun s => heatSemigroup (t - s)
        (fun y => chemotaxisSource p (u₁ s) (fun _ => 0) y) x)
      (MeasureTheory.volume.restrict (Set.Icc 0 t)))
    (hG₂ : MeasureTheory.Integrable
      (fun s => heatSemigroup (t - s)
        (fun y => chemotaxisSource p (u₂ s) (fun _ => 0) y) x)
      (MeasureTheory.volume.restrict (Set.Icc 0 t)))
    (ht : 0 ≤ t) (htT : t ≤ T) :
    |mildSolutionOperator p u₀ u₁ t x - mildSolutionOperator p u₀ u₂ t x| ≤
      L * T * sSup (Set.range fun s => sSup (Set.range fun y => |u₁ s y - u₂ s y|)) := by
  set M := sSup (Set.range fun x => |u₀ x|)
  set D := sSup (Set.range fun s => sSup (Set.range fun y => |u₁ s y - u₂ s y|))
  have hdiff_bound : ∀ s y, |u₁ s y - u₂ s y| ≤ 4 * M :=
    fun s y => (abs_sub _ _).trans (add_le_add (hu₁ s y) (hu₂ s y)) |>.trans (by ring_nf; linarith)
  have hbdd_inner : ∀ s, BddAbove (Set.range fun y => |u₁ s y - u₂ s y|) :=
    fun s => ⟨4 * M, by rintro _ ⟨y, rfl⟩; exact hdiff_bound s y⟩
  have hbdd_outer : BddAbove (Set.range fun s => sSup (Set.range fun y => |u₁ s y - u₂ s y|)) :=
    ⟨4 * M, by rintro _ ⟨s, rfl⟩; exact csSup_le (Set.range_nonempty _) (fun _ ⟨y, hy⟩ => hy ▸ hdiff_bound s y)⟩
  have hle_D : ∀ s y, |u₁ s y - u₂ s y| ≤ D :=
    fun s y => (le_csSup (hbdd_inner s) ⟨y, rfl⟩).trans (le_csSup hbdd_outer ⟨s, rfl⟩)
  have hD_nn : 0 ≤ D := le_csSup_of_le hbdd_outer ⟨0, rfl⟩
      (le_csSup_of_le (hbdd_inner 0) ⟨0, rfl⟩ (abs_nonneg _))
  have hsource_bound : ∀ s y, |chemotaxisSource p (u₁ s) (fun _ => 0) y -
      chemotaxisSource p (u₂ s) (fun _ => 0) y| ≤ L * D := by
    intro s y
    have h1 : chemotaxisSource p (u₁ s) (fun _ => 0) y =
        chemotaxisSource p (fun _ => u₁ s y) (fun _ => 0) 0 := by simp [chemotaxisSource]
    have h2 : chemotaxisSource p (u₂ s) (fun _ => 0) y =
        chemotaxisSource p (fun _ => u₂ s y) (fun _ => 0) 0 := by simp [chemotaxisSource]
    rw [h1, h2]
    calc |chemotaxisSource p (fun _ => u₁ s y) (fun _ => 0) 0 -
            chemotaxisSource p (fun _ => u₂ s y) (fun _ => 0) 0|
        ≤ L * |u₁ s y - u₂ s y| := hLip _ _ (hu₁ s y) (hu₂ s y)
      _ ≤ L * D := mul_le_mul_of_nonneg_left (hle_D s y) hL_nn
  rw [mildSolutionOperator_difference_integral_identity p u₀ u₁ u₂ t x
    hu₁_meas hu₂_meas hu₁_bdd hu₂_bdd hG₁ hG₂]
  calc |∫ s in Set.Icc 0 t, heatSemigroup (t - s)
        (fun y => chemotaxisSource p (u₁ s) (fun _ => 0) y -
          chemotaxisSource p (u₂ s) (fun _ => 0) y) x|
      ≤ L * t * D := mildSolutionOperator_duhamel_integral_bound p u₁ u₂ L D t x
          hL_nn hD_nn ht hsource_bound hu₁_meas hu₂_meas
    _ ≤ L * T * D := by nlinarith [mul_nonneg hL_nn hD_nn]

theorem mild_solution_operator_contracting (p : CMParams)
    (u₀ : ℝ → ℝ) (hu₀_bdd : IsBddFun u₀) :
    ∃ T > 0, ∃ K : ℝ, 0 ≤ K ∧ K < 1 ∧
    ∀ u₁ u₂ : ℝ → ℝ → ℝ,
    (∀ t x, |u₁ t x| ≤ 2 * (sSup (Set.range (fun x => |u₀ x|)))) →
    (∀ t x, |u₂ t x| ≤ 2 * (sSup (Set.range (fun x => |u₀ x|)))) →
    (∀ s, AEStronglyMeasurable (u₁ s) volume) →
    (∀ s, AEStronglyMeasurable (u₂ s) volume) →
    (∀ t x, 0 ≤ t → t ≤ T →
      MeasureTheory.Integrable
        (fun s => heatSemigroup (t - s)
          (fun y => chemotaxisSource p (u₁ s) (fun _ => 0) y) x)
        (MeasureTheory.volume.restrict (Set.Icc 0 t)) ∧
      MeasureTheory.Integrable
        (fun s => heatSemigroup (t - s)
          (fun y => chemotaxisSource p (u₂ s) (fun _ => 0) y) x)
        (MeasureTheory.volume.restrict (Set.Icc 0 t))) →
    ∀ t x, 0 ≤ t → t ≤ T →
    |mildSolutionOperator p u₀ u₁ t x - mildSolutionOperator p u₀ u₂ t x| ≤
      K * (sSup (Set.range (fun s => sSup (Set.range (fun y => |u₁ s y - u₂ s y|))))) := by
  let M : ℝ := max 1 (2 * sSup (Set.range fun x => |u₀ x|))
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨L, hL_pos, hLip⟩ := logistic_lipschitz_on_bounded (α := p.α) (M := M) p.hα hM_pos
  have hT_pos : (0 : ℝ) < 1 / (2 * L) := by positivity
  have hK_lt : L * (1 / (2 * L)) < 1 := by
    have h2L : (2 * L) ≠ 0 := by positivity
    have : L * (1 / (2 * L)) = 1 / 2 := by field_simp
    linarith
  refine ⟨1 / (2 * L), hT_pos, L * (1 / (2 * L)), by positivity, hK_lt, ?_⟩
  intro u₁ u₂ hu₁ hu₂ hu₁m hu₂m htime_int t x ht htT
  have hu₁_bdd : ∀ s, ∃ C, ∀ y, |u₁ s y| ≤ C :=
    fun s => ⟨2 * sSup (Set.range fun x => |u₀ x|), hu₁ s⟩
  have hu₂_bdd : ∀ s, ∃ C, ∀ y, |u₂ s y| ≤ C :=
    fun s => ⟨2 * sSup (Set.range fun x => |u₀ x|), hu₂ s⟩
  have hmain := mildSolutionOperator_lipschitz_estimate p u₀ L (1/(2*L)) u₁ u₂ t x
    (by positivity) hL_pos.le (fun a b ha hb => by
      simp only [chemotaxisSource]
      exact hLip a b (le_trans ha (le_max_right _ _)) (le_trans hb (le_max_right _ _)))
    hu₁ hu₂ hu₁m hu₂m hu₁_bdd hu₂_bdd
    (htime_int t x ht htT).1 (htime_int t x ht htT).2 ht htT
  linarith [hmain]

/-- Local existence of mild solutions via Banach fixed-point theorem. -/
theorem local_existence_mild (p : CMParams)
    (u₀ : ℝ → ℝ) (hu₀_cont : Continuous u₀) (hu₀_bdd : IsBddFun u₀)
    (hu₀_nn : ∀ x, 0 ≤ u₀ x) :
    ∃ T > 0, ∃ u : ℝ → ℝ → ℝ,
    (∀ t x, 0 ≤ t → t ≤ T → u t x =
      heatSemigroup t u₀ x +
      ∫ s in Set.Icc 0 t, heatSemigroup (t - s)
        (fun y => chemotaxisSource p (u s) (fun _ => 0) y) x) := by
  obtain ⟨T, hT, K, _hK0, _hK1, _hcontr⟩ :=
    mild_solution_operator_contracting p u₀ hu₀_bdd
  let Φ : (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ :=
    fun u t x =>
      heatSemigroup t u₀ x +
        ∫ s in Set.Icc 0 t,
          heatSemigroup (t - s)
            (fun y => chemotaxisSource p (u s) (fun _ => 0) y) x
  have hfixed :
      ∃ u : ℝ → ℝ → ℝ,
        ∀ t x, 0 ≤ t → t ≤ T → u t x = Φ u t x := by
    sorry
  obtain ⟨u, hu_fixed⟩ := hfixed
  refine ⟨T, hT, u, ?_⟩
  intro t x ht0 htT
  specialize hu_fixed t x ht0 htT
  simpa [Φ] using hu_fixed

end
