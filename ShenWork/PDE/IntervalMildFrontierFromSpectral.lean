/-
  ShenWork/PDE/IntervalMildFrontierFromSpectral.lean

  **u-component fields of `GradientMildClassicalRegularityFrontierData`
  from spectral theory.**

  Given `HasTimeNeighborhoodSpectralAgreement T u`, this file constructs:

  1. `mildSolution_timeDeriv_jointContinuousOn_closed` — joint ContinuousOn of
     `(t,x) ↦ deriv (fun s => intervalDomainLift (u s) x) t` on
     `Ioo 0 T ×ˢ Icc 0 1`  (u-part of `jointTimeDerivClosed`).

  2. `mildSolution_jointContinuousOn_closed` — joint ContinuousOn of
     `(t,x) ↦ intervalDomainLift (u t) x` on
     `Ioo 0 T ×ˢ Icc 0 1`  (u-part of `jointSolutionClosed`).

  Key idea: the spectral derivative (resp. series) is continuous on the LARGER
  set `Ioi 0 × univ ⊇ Ioo 0 T × Icc 0 1`.  At each interior time `t₀`, the
  mild solution agrees with the spectral function in a time neighborhood and on
  all of `Icc 0 1`.  The `ContinuousAt` of the spectral composition gives
  `ContinuousWithinAt` on the closed slab, and `congr_of_eventuallyEq_of_mem`
  transfers it to the mild solution.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.PDE.IntervalMildTimeDerivContinuity

open ShenWork.IntervalDomain
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement
   intervalDomainLift_agree_of_point_agree
   intervalDomainLift_deriv_eq)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff
  restartSeries_jointContinuousOn
  restartDerivSeries_jointContinuousOn)
open ShenWork.IntervalRestartDerivJointContinuity (restartDerivField_continuousOn_joint)
open ShenWork.CosineSpectrum (cosineMode)
open Filter Topology Set

noncomputable section

namespace ShenWork.IntervalMildFrontierFromSpectral

/-! ## jointTimeDerivClosed (u-part)

The time derivative of the mild solution is jointly continuous on the
closed slab `Ioo 0 T ×ˢ Icc 0 1`.  This extends `mildSolution_timeDeriv_jointContinuousOn`
(which gives continuity on `Ioo 0 T ×ˢ Ioo 0 1`) to the closed spatial domain. -/

/-- **u-part of `jointTimeDerivClosed`.**
Joint `ContinuousOn` of `(t, x) ↦ deriv (fun s => intervalDomainLift (u s) x) t`
on `Ioo 0 T ×ˢ Icc 0 1`. -/
theorem mildSolution_timeDeriv_jointContinuousOn_closed
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (H : HasTimeNeighborhoodSpectralAgreement T u) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s => intervalDomainLift (u s) x) t))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
  intro ⟨t₀, x₀⟩ hp
  obtain ⟨ht₀, hx₀⟩ := mem_prod.1 hp
  obtain ⟨ht₀_pos, ht₀_lt⟩ := mem_Ioo.1 ht₀
  obtain ⟨a₀, M, hM, ha₀, a, src, offset, hτ₀, hagree_nhd⟩ :=
    H.exists_data t₀ ht₀_pos ht₀_lt
  -- Extract an open set V ∋ t₀ where the agreement holds.
  obtain ⟨V, hV_agree, hV_open, hV_mem⟩ := eventually_nhds_iff.1 hagree_nhd
  -- Wt := V ∩ Ioi offset is open and contains t₀.
  set Wt := V ∩ Ioi offset
  have hWt_open : IsOpen Wt := hV_open.inter isOpen_Ioi
  have hWt_mem : t₀ ∈ Wt := ⟨hV_mem, mem_Ioi.2 (by linarith)⟩
  -- For every t ∈ Wt, the agreement holds in a time neighborhood.
  have hagree_at : ∀ t ∈ Wt, ∀ᶠ s in 𝓝 t, ∀ y : intervalDomainPoint,
      u s y = ∑' n, localRestartCoeff a₀ a (s - offset) n *
        cosineMode n y.1 :=
    fun t ht => eventually_of_mem (hWt_open.mem_nhds ht)
      (fun s hs => hV_agree s hs.1)
  -- Spectral derivative field F.
  set F : ℝ × ℝ → ℝ := fun p =>
    ∑' n, (a p.1 n - unitIntervalCosineEigenvalue n *
      localRestartCoeff a₀ a p.1 n) * cosineMode n p.2
  -- F ∘ shift = (t,x) ↦ F(t - offset, x).
  set G : ℝ × ℝ → ℝ := fun p => F (p.1 - offset, p.2)
  -- For every (t,x) ∈ Wt × Icc 0 1, the derivative equals G(t,x).
  have hderiv_eq : ∀ t ∈ Wt, ∀ x ∈ Icc (0 : ℝ) 1,
      deriv (fun s => intervalDomainLift (u s) x) t = G (t, x) :=
    fun t ht x hx => intervalDomainLift_deriv_eq hM ha₀ src
      (by linarith [mem_Ioi.1 ht.2]) (hagree_at t ht) hx
  -- F is ContinuousOn on Ioi 0 ×ˢ univ (from spectral theory).
  have hF_cont : ContinuousOn F (Ioi 0 ×ˢ univ) :=
    restartDerivField_continuousOn_joint hM ha₀ src
  -- F is ContinuousAt at (t₀ - offset, x₀).
  have hF_ca : ContinuousAt F (t₀ - offset, x₀) :=
    hF_cont.continuousAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (mem_prod.2 ⟨mem_Ioi.2 hτ₀, mem_univ _⟩))
  -- G is ContinuousAt at (t₀, x₀).
  have hG_ca : ContinuousAt G (t₀, x₀) := by
    have hg : Continuous (fun p : ℝ × ℝ => (p.1 - offset, p.2)) :=
      (continuous_fst.sub continuous_const).prodMk continuous_snd
    exact ContinuousAt.comp' (f := fun p : ℝ × ℝ => ((p.1 - offset : ℝ), p.2))
      hF_ca hg.continuousAt
  -- ContinuousAt → ContinuousWithinAt on the closed slab.
  have hG_cwa : ContinuousWithinAt G (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) (t₀, x₀) :=
    hG_ca.continuousWithinAt
  -- The mild solution's time derivative agrees with G in 𝓝[S] (t₀, x₀).
  -- The set Wt × univ is in 𝓝 (t₀, x₀), and on (Wt × univ) ∩ S the functions agree.
  set S := Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1
  have hWt_nhds : Wt ×ˢ (univ : Set ℝ) ∈ 𝓝 (t₀, x₀) :=
    (hWt_open.prod isOpen_univ).mem_nhds (mem_prod.2 ⟨hWt_mem, mem_univ _⟩)
  -- Show agreement on (Wt × univ) ∩ S.
  have hagree_on : ∀ p ∈ (Wt ×ˢ (univ : Set ℝ)) ∩ S,
      Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        deriv (fun s => intervalDomainLift (u s) x) t) p = G p := by
    intro ⟨t, x⟩ hp'
    obtain ⟨hWt_univ, hS⟩ := hp'
    obtain ⟨htWt, _⟩ := mem_prod.1 hWt_univ
    obtain ⟨_, hxIcc⟩ := mem_prod.1 hS
    simp only [Function.uncurry_apply_pair]
    exact hderiv_eq t htWt x hxIcc
  -- Build the eventuallyEq filter: mild_deriv =ᶠ[𝓝[S] (t₀,x₀)] G.
  have heventual :
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        deriv (fun s => intervalDomainLift (u s) x) t)) =ᶠ[𝓝[S] (t₀, x₀)]
        (fun p => G p) := by
    apply Filter.mem_inf_of_inter hWt_nhds (mem_principal_self S)
    intro ⟨t, x⟩ ⟨hW, hS'⟩
    exact hagree_on (t, x) ⟨hW, hS'⟩
  -- Transfer continuity from G to the mild solution derivative.
  exact hG_cwa.congr_of_eventuallyEq heventual (by
    simp only [Function.uncurry_apply_pair]
    exact hderiv_eq t₀ hWt_mem x₀ hx₀)

/-! ## jointSolutionClosed (u-part)

The mild solution itself is jointly continuous on the closed slab
`Ioo 0 T ×ˢ Icc 0 1`. -/

/-- **u-part of `jointSolutionClosed`.**
Joint `ContinuousOn` of `(t, x) ↦ intervalDomainLift (u t) x`
on `Ioo 0 T ×ˢ Icc 0 1`. -/
theorem mildSolution_jointContinuousOn_closed
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (H : HasTimeNeighborhoodSpectralAgreement T u) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
  intro ⟨t₀, x₀⟩ hp
  obtain ⟨ht₀, hx₀⟩ := mem_prod.1 hp
  obtain ⟨ht₀_pos, ht₀_lt⟩ := mem_Ioo.1 ht₀
  obtain ⟨a₀, M, hM, ha₀, a, src, offset, hτ₀, hagree_nhd⟩ :=
    H.exists_data t₀ ht₀_pos ht₀_lt
  -- Extract an open set V ∋ t₀ where the agreement holds.
  obtain ⟨V, hV_agree, hV_open, hV_mem⟩ := eventually_nhds_iff.1 hagree_nhd
  -- Wt := V ∩ Ioi offset is open and contains t₀.
  set Wt := V ∩ Ioi offset
  have hWt_open : IsOpen Wt := hV_open.inter isOpen_Ioi
  have hWt_mem : t₀ ∈ Wt := ⟨hV_mem, mem_Ioi.2 (by linarith)⟩
  -- Spectral value field: (τ, x) ↦ ∑' n, cₙ(τ) cos(nπx).
  set F : ℝ × ℝ → ℝ := fun p =>
    ∑' n, localRestartCoeff a₀ a p.1 n * cosineMode n p.2
  -- F ∘ shift = (t,x) ↦ F(t - offset, x).
  set G : ℝ × ℝ → ℝ := fun p => F (p.1 - offset, p.2)
  -- For every (t,x) ∈ Wt × Icc 0 1, the solution equals G(t,x).
  have hvalue_eq : ∀ t ∈ Wt, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) x = G (t, x) := by
    intro t ht x hx
    exact intervalDomainLift_agree_of_point_agree (hV_agree t ht.1) hx
  -- F is ContinuousOn on Ioi 0 ×ˢ univ.
  have hF_cont : ContinuousOn F (Ioi 0 ×ˢ univ) := by
    have := restartSeries_jointContinuousOn hM ha₀ src
    convert this using 1
  -- F is ContinuousAt at (t₀ - offset, x₀).
  have hF_ca : ContinuousAt F (t₀ - offset, x₀) :=
    hF_cont.continuousAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (mem_prod.2 ⟨mem_Ioi.2 hτ₀, mem_univ _⟩))
  -- G is ContinuousAt at (t₀, x₀).
  have hG_ca : ContinuousAt G (t₀, x₀) := by
    have hg : Continuous (fun p : ℝ × ℝ => (p.1 - offset, p.2)) :=
      (continuous_fst.sub continuous_const).prodMk continuous_snd
    exact ContinuousAt.comp' (f := fun p : ℝ × ℝ => ((p.1 - offset : ℝ), p.2))
      hF_ca hg.continuousAt
  -- ContinuousAt → ContinuousWithinAt on the closed slab.
  set S := Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1
  have hG_cwa : ContinuousWithinAt G S (t₀, x₀) :=
    hG_ca.continuousWithinAt
  -- Wt × univ is in 𝓝 (t₀, x₀).
  have hWt_nhds : Wt ×ˢ (univ : Set ℝ) ∈ 𝓝 (t₀, x₀) :=
    (hWt_open.prod isOpen_univ).mem_nhds (mem_prod.2 ⟨hWt_mem, mem_univ _⟩)
  -- Agreement on (Wt × univ) ∩ S.
  have hagree_on : ∀ p ∈ (Wt ×ˢ (univ : Set ℝ)) ∩ S,
      Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        intervalDomainLift (u t) x) p = G p := by
    intro ⟨t, x⟩ hp'
    obtain ⟨hWt_univ, hS⟩ := hp'
    obtain ⟨htWt, _⟩ := mem_prod.1 hWt_univ
    obtain ⟨_, hxIcc⟩ := mem_prod.1 hS
    simp only [Function.uncurry_apply_pair]
    exact hvalue_eq t htWt x hxIcc
  -- Build the eventuallyEq filter: mild_solution =ᶠ[𝓝[S] (t₀,x₀)] G.
  have heventual :
      (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        intervalDomainLift (u t) x)) =ᶠ[𝓝[S] (t₀, x₀)]
        (fun p => G p) := by
    apply Filter.mem_inf_of_inter hWt_nhds (mem_principal_self S)
    intro ⟨t, x⟩ ⟨hW, hS'⟩
    exact hagree_on (t, x) ⟨hW, hS'⟩
  -- Transfer continuity from G to the mild solution.
  exact hG_cwa.congr_of_eventuallyEq heventual (by
    simp only [Function.uncurry_apply_pair]
    exact hvalue_eq t₀ hWt_mem x₀ hx₀)

end ShenWork.IntervalMildFrontierFromSpectral
