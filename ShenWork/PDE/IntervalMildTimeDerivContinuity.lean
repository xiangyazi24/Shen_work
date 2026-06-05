/-
  ShenWork/PDE/IntervalMildTimeDerivContinuity.lean

  **Bridge: spectral time-derivative joint continuity to mild solution.**

  Given that the mild solution agrees with a restart cosine series in a time
  neighborhood of each interior point, the time derivative of the mild solution
  inherits continuity from the spectral derivative field.

  Proved:
  1. `mildSolution_timeDeriv_continuousOn_fixed_x` -- for fixed `x`, the map
     `t ↦ deriv (u · x) t` is `ContinuousOn (Ioo 0 T)`.
  2. `mildSolution_timeDeriv_jointContinuousOn` -- joint `ContinuousOn` of
     `(t, x) ↦ deriv (fun s => intervalDomainLift (u s) x) t` on
     `Ioo 0 T ×ˢ Ioo 0 1`.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.PDE.IntervalRestartDerivJointContinuity
import ShenWork.Paper2.IntervalMildTimeRegularity

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff
  restartCosineSeries_hasDerivAt_time)
open ShenWork.IntervalRestartDerivJointContinuity (restartDerivField_continuousOn_joint)
open ShenWork.IntervalMildRegularityBootstrap (RestartCosineRepresentation
  HasRestartCosineRepresentations restartDuhamelCoeff)
open Filter Topology Set

noncomputable section

namespace ShenWork.IntervalMildTimeDerivContinuity

/-! ## Hypothesis: time-neighborhood spectral agreement -/

/-- Time-neighborhood spectral agreement for the mild solution.  For each
interior time `t₀ ∈ (0,T)`, there exist spectral data `(a₀, M, a, src, offset)`
such that the mild solution equals the restart cosine series for all times `s`
in a neighborhood of `t₀` and all spatial points `x ∈ [0,1]`.

This is the honest upstream hypothesis: it encodes the restart Duhamel formula
at a fixed base time (e.g. `offset = t₀/2`), valid for all `s` in a right
half-neighborhood of the restart base. -/
structure HasTimeNeighborhoodSpectralAgreement
    (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_data : ∀ t₀, 0 < t₀ → t₀ < T →
    ∃ (a₀ : ℕ → ℝ) (M : ℝ) (_ : 0 ≤ M) (_ : ∀ n, |a₀ n| ≤ M)
      (a : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC1 a) (offset : ℝ),
      (0 < t₀ - offset) ∧
      (∀ᶠ s in 𝓝 t₀, ∀ x : intervalDomainPoint,
        u s x = ∑' n, localRestartCoeff a₀ a (s - offset) n *
          cosineMode n x.1)

/-! ## Core lemma: HasDerivAt for the mild solution -/

/-- The restart cosine series `HasDerivAt` (G4i) transfers to the mild
solution via eventuallyEq from the neighborhood spectral agreement. -/
theorem mildSolution_hasDerivAt_time
    {u : ℝ → intervalDomainPoint → ℝ}
    {t₀ : ℝ}
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {offset : ℝ} (hτ₀ : 0 < t₀ - offset)
    (hagree_nhd : ∀ᶠ s in 𝓝 t₀, ∀ x : intervalDomainPoint,
      u s x = ∑' n, localRestartCoeff a₀ a (s - offset) n *
        cosineMode n x.1)
    (x : intervalDomainPoint) :
    HasDerivAt (fun s => u s x)
      (∑' n, (a (t₀ - offset) n - unitIntervalCosineEigenvalue n *
        localRestartCoeff a₀ a (t₀ - offset) n) * cosineMode n x.1) t₀ := by
  have hspec := restartCosineSeries_hasDerivAt_time hM ha₀ src hτ₀ x.1
  have hshift : HasDerivAt
      (fun s => ∑' n, localRestartCoeff a₀ a (s - offset) n *
        cosineMode n x.1)
      (∑' n, (a (t₀ - offset) n - unitIntervalCosineEigenvalue n *
        localRestartCoeff a₀ a (t₀ - offset) n) * cosineMode n x.1) t₀ := by
    have hsub : HasDerivAt (· - offset) 1 t₀ :=
      (hasDerivAt_id t₀).add_const (-offset)
    have hcomp := hspec.scomp t₀ hsub
    simp only [smul_eq_mul, one_mul] at hcomp
    exact hcomp
  exact hshift.congr_of_eventuallyEq
    (hagree_nhd.mono (fun s hs => by change u s x = _; exact hs x))

/-- Deriv identity: at each interior point, the time derivative of the mild
solution equals the spectral derivative value. -/
theorem mildSolution_deriv_eq
    {u : ℝ → intervalDomainPoint → ℝ}
    {t₀ : ℝ}
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {offset : ℝ} (hτ₀ : 0 < t₀ - offset)
    (hagree_nhd : ∀ᶠ s in 𝓝 t₀, ∀ x : intervalDomainPoint,
      u s x = ∑' n, localRestartCoeff a₀ a (s - offset) n *
        cosineMode n x.1)
    (x : intervalDomainPoint) :
    deriv (fun s => u s x) t₀ =
      ∑' n, (a (t₀ - offset) n - unitIntervalCosineEigenvalue n *
        localRestartCoeff a₀ a (t₀ - offset) n) * cosineMode n x.1 :=
  (mildSolution_hasDerivAt_time hM ha₀ src hτ₀ hagree_nhd x).deriv

/-! ## Part 1: Fixed-x time-derivative continuity -/

/-- **Theorem 1.**  For fixed `x ∈ intervalDomainPoint`, the map
`t ↦ deriv (u · x) t` is `ContinuousOn (Ioo 0 T)`. -/
theorem mildSolution_timeDeriv_continuousOn_fixed_x
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (H : HasTimeNeighborhoodSpectralAgreement T u)
    (x : intervalDomainPoint) :
    ContinuousOn (fun t => deriv (fun s => u s x) t) (Ioo 0 T) := by
  rw [isOpen_Ioo.continuousOn_iff]
  intro t₀ ht₀
  obtain ⟨ht₀_pos, ht₀_lt⟩ := mem_Ioo.1 ht₀
  obtain ⟨a₀, M, hM, ha₀, a, src, offset, hτ₀, hagree_nhd⟩ :=
    H.exists_data t₀ ht₀_pos ht₀_lt
  -- Extract an open set V ∋ t₀ where the agreement holds.
  obtain ⟨V, hV_agree, hV_open, hV_mem⟩ := eventually_nhds_iff.1 hagree_nhd
  -- On W := V ∩ Ioi offset (open, contains t₀), deriv (u · x) = spectral deriv.
  set W := V ∩ Ioi offset
  have hW_open : IsOpen W := hV_open.inter isOpen_Ioi
  have hW_mem : t₀ ∈ W := ⟨hV_mem, mem_Ioi.2 (by linarith)⟩
  -- For every t ∈ W, the agreement holds in a neighborhood of t.
  have hagree_at : ∀ t ∈ W, ∀ᶠ s in 𝓝 t, ∀ y : intervalDomainPoint,
      u s y = ∑' n, localRestartCoeff a₀ a (s - offset) n *
        cosineMode n y.1 :=
    fun t ht => eventually_of_mem (hW_open.mem_nhds ht) (fun s hs => hV_agree s hs.1)
  -- For every t ∈ W, deriv (u · x) t = spectral deriv at (t - offset, x.1).
  have hderiv_eq : ∀ t ∈ W, deriv (fun s => u s x) t =
      ∑' n, (a (t - offset) n - unitIntervalCosineEigenvalue n *
        localRestartCoeff a₀ a (t - offset) n) * cosineMode n x.1 :=
    fun t ht => mildSolution_deriv_eq hM ha₀ src
      (by linarith [mem_Ioi.1 ht.2]) (hagree_at t ht) x
  -- The spectral derivative field F is ContinuousOn (Ioi 0 ×ˢ univ).
  set F : ℝ × ℝ → ℝ := fun p =>
    ∑' n, (a p.1 n - unitIntervalCosineEigenvalue n *
      localRestartCoeff a₀ a p.1 n) * cosineMode n p.2
  have hF_cont : ContinuousOn F (Ioi 0 ×ˢ univ) :=
    restartDerivField_continuousOn_joint hM ha₀ src
  -- Build ContinuousAt of the spectral derivative at (t₀ - offset, x.1).
  have hF_ca : ContinuousAt F (t₀ - offset, x.1) :=
    hF_cont.continuousAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (mem_prod.2 ⟨mem_Ioi.2 hτ₀, mem_univ _⟩))
  -- The composition t ↦ F(t - offset, x.1) is ContinuousAt.
  have hcomp_cont : ContinuousAt (fun t : ℝ => F (t - offset, x.1)) t₀ := by
    have hg : Continuous (fun t : ℝ => ((t - offset : ℝ), (x.1 : ℝ))) :=
      (continuous_id.sub continuous_const).prodMk continuous_const
    exact ContinuousAt.comp' (f := fun t : ℝ => ((t - offset : ℝ), (x.1 : ℝ)))
      hF_ca hg.continuousAt
  -- On W, the derivative function equals F ∘ shift.
  -- ContinuousAt.congr : ContinuousAt f x → f =ᶠ[𝓝 x] g → ContinuousAt g x
  exact hcomp_cont.congr
    (eventually_of_mem (hW_open.mem_nhds hW_mem)
      (fun t ht => (hderiv_eq t ht).symm))

/-! ## Part 2: intervalDomainLift bridge -/

/-- The point-level agreement extends to `intervalDomainLift` at `x ∈ [0,1]`. -/
theorem intervalDomainLift_agree_of_point_agree
    {u : ℝ → intervalDomainPoint → ℝ} {s : ℝ}
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset : ℝ}
    (hagree : ∀ y : intervalDomainPoint,
      u s y = ∑' n, localRestartCoeff a₀ a (s - offset) n *
        cosineMode n y.1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    intervalDomainLift (u s) x =
      ∑' n, localRestartCoeff a₀ a (s - offset) n *
        cosineMode n x := by
  simp only [intervalDomainLift, hx, dif_pos]
  exact hagree ⟨x, hx⟩

/-- **HasDerivAt for `intervalDomainLift (u ·) x` at an interior point.**
For `x ∈ [0,1]`, the lift agrees with the cosine series in a time
neighborhood, so the `HasDerivAt` transfers. -/
theorem intervalDomainLift_hasDerivAt_time
    {u : ℝ → intervalDomainPoint → ℝ}
    {t₀ : ℝ}
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {offset : ℝ} (hτ₀ : 0 < t₀ - offset)
    (hagree_nhd : ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
      u s y = ∑' n, localRestartCoeff a₀ a (s - offset) n *
        cosineMode n y.1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => intervalDomainLift (u s) x)
      (∑' n, (a (t₀ - offset) n - unitIntervalCosineEigenvalue n *
        localRestartCoeff a₀ a (t₀ - offset) n) * cosineMode n x) t₀ := by
  have hspec := restartCosineSeries_hasDerivAt_time hM ha₀ src hτ₀ x
  have hshift : HasDerivAt
      (fun s => ∑' n, localRestartCoeff a₀ a (s - offset) n *
        cosineMode n x)
      (∑' n, (a (t₀ - offset) n - unitIntervalCosineEigenvalue n *
        localRestartCoeff a₀ a (t₀ - offset) n) * cosineMode n x) t₀ := by
    have hsub : HasDerivAt (· - offset) 1 t₀ :=
      (hasDerivAt_id t₀).add_const (-offset)
    have hcomp := hspec.scomp t₀ hsub
    simp only [smul_eq_mul, one_mul] at hcomp
    exact hcomp
  exact hshift.congr_of_eventuallyEq
    (hagree_nhd.mono (fun s hs => by
      change intervalDomainLift (u s) x = _
      exact intervalDomainLift_agree_of_point_agree hs hx))

/-- Deriv identity for `intervalDomainLift`. -/
theorem intervalDomainLift_deriv_eq
    {u : ℝ → intervalDomainPoint → ℝ}
    {t₀ : ℝ}
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {offset : ℝ} (hτ₀ : 0 < t₀ - offset)
    (hagree_nhd : ∀ᶠ s in 𝓝 t₀, ∀ y : intervalDomainPoint,
      u s y = ∑' n, localRestartCoeff a₀ a (s - offset) n *
        cosineMode n y.1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    deriv (fun s => intervalDomainLift (u s) x) t₀ =
      ∑' n, (a (t₀ - offset) n - unitIntervalCosineEigenvalue n *
        localRestartCoeff a₀ a (t₀ - offset) n) * cosineMode n x :=
  (intervalDomainLift_hasDerivAt_time hM ha₀ src hτ₀ hagree_nhd hx).deriv

/-! ## Part 3: Joint (t,x) continuity -/

/-- **Theorem 2.**  Joint `ContinuousOn` of
`(t, x) ↦ deriv (fun s => intervalDomainLift (u s) x) t`
on `Ioo 0 T ×ˢ Ioo 0 1`. -/
theorem mildSolution_timeDeriv_jointContinuousOn
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (H : HasTimeNeighborhoodSpectralAgreement T u) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s => intervalDomainLift (u s) x) t))
      (Ioo (0 : ℝ) T ×ˢ Ioo (0 : ℝ) 1) := by
  rw [(isOpen_Ioo.prod isOpen_Ioo).continuousOn_iff]
  intro ⟨t₀, x₀⟩ hp
  obtain ⟨ht₀, hx₀⟩ := mem_prod.1 hp
  obtain ⟨ht₀_pos, ht₀_lt⟩ := mem_Ioo.1 ht₀
  obtain ⟨hx₀_pos, hx₀_lt⟩ := mem_Ioo.1 hx₀
  obtain ⟨a₀, M, hM, ha₀, a, src, offset, hτ₀, hagree_nhd⟩ :=
    H.exists_data t₀ ht₀_pos ht₀_lt
  -- Extract an open set V ∋ t₀ where the agreement holds.
  obtain ⟨V, hV_agree, hV_open, hV_mem⟩ := eventually_nhds_iff.1 hagree_nhd
  -- Spectral derivative field.
  set F : ℝ × ℝ → ℝ := fun p =>
    ∑' n, (a p.1 n - unitIntervalCosineEigenvalue n *
      localRestartCoeff a₀ a p.1 n) * cosineMode n p.2
  -- On Wt := V ∩ Ioi offset (open in time, contains t₀).
  set Wt := V ∩ Ioi offset
  have hWt_open : IsOpen Wt := hV_open.inter isOpen_Ioi
  have hWt_mem : t₀ ∈ Wt := ⟨hV_mem, mem_Ioi.2 (by linarith)⟩
  -- For every t ∈ Wt, the agreement holds in a neighborhood of t.
  have hagree_at : ∀ t ∈ Wt, ∀ᶠ s in 𝓝 t, ∀ y : intervalDomainPoint,
      u s y = ∑' n, localRestartCoeff a₀ a (s - offset) n *
        cosineMode n y.1 :=
    fun t ht => eventually_of_mem (hWt_open.mem_nhds ht)
      (fun s hs => hV_agree s hs.1)
  -- For every (t,x) ∈ Wt × Icc 0 1, the derivative equals F ∘ shift.
  have hderiv_eq : ∀ t ∈ Wt, ∀ x ∈ Icc (0 : ℝ) 1,
      deriv (fun s => intervalDomainLift (u s) x) t =
        F (t - offset, x) :=
    fun t ht x hx => intervalDomainLift_deriv_eq hM ha₀ src
      (by linarith [mem_Ioi.1 ht.2]) (hagree_at t ht) hx
  -- F is ContinuousAt at (t₀ - offset, x₀).
  have hF_cont : ContinuousOn F (Ioi 0 ×ˢ univ) :=
    restartDerivField_continuousOn_joint hM ha₀ src
  have hF_ca : ContinuousAt F (t₀ - offset, x₀) :=
    hF_cont.continuousAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (mem_prod.2 ⟨mem_Ioi.2 hτ₀, mem_univ _⟩))
  -- F ∘ ((t,x) ↦ (t - offset, x)) is ContinuousAt at (t₀, x₀).
  have hcomp_ca : ContinuousAt
      (fun p : ℝ × ℝ => F (p.1 - offset, p.2)) (t₀, x₀) := by
    have hg : Continuous (fun p : ℝ × ℝ => (p.1 - offset, p.2)) :=
      (continuous_fst.sub continuous_const).prodMk continuous_snd
    exact ContinuousAt.comp' (f := fun p : ℝ × ℝ => ((p.1 - offset : ℝ), p.2))
      hF_ca hg.continuousAt
  -- The uncurried derivative function agrees with F ∘ shift on
  -- Wt ×ˢ Ioo 0 1 (neighborhood of (t₀, x₀)).
  have hW_prod_open : IsOpen (Wt ×ˢ Ioo (0 : ℝ) 1) :=
    hWt_open.prod isOpen_Ioo
  have hW_prod_mem : (t₀, x₀) ∈ Wt ×ˢ Ioo (0 : ℝ) 1 :=
    mem_prod.2 ⟨hWt_mem, mem_Ioo.2 ⟨hx₀_pos, hx₀_lt⟩⟩
  have hx₀_Icc : x₀ ∈ Icc (0 : ℝ) 1 :=
    Ioo_subset_Icc_self (mem_Ioo.2 ⟨hx₀_pos, hx₀_lt⟩)
  exact hcomp_ca.congr
    (eventually_of_mem (hW_prod_open.mem_nhds hW_prod_mem)
      (fun ⟨t, x⟩ htx => by
        obtain ⟨ht, hx⟩ := mem_prod.1 htx
        exact (hderiv_eq t ht x (Ioo_subset_Icc_self hx)).symm))

end ShenWork.IntervalMildTimeDerivContinuity
