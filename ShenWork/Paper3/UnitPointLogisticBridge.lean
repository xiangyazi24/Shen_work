/-
  Bridge: closes Paper3 Proposition_1_3 + Proposition_1_2 unconditionally
  on unit-point-domain via Slot F's Bernoulli-logistic solution.
-/
import ShenWork.Paper3.Statements
import ShenWork.Paper2.UnitPointLogisticBridge
import ShenWork.PDE.UnitPointLogisticODE
import ShenWork.PDE.UnitPointDecayODE

noncomputable section

namespace ShenWork.Paper3

/-- Paper 3 Proposition 1.3 holds unconditionally on the unit-point
domain.  Hypothesis `0 < p.a, 0 < p.b, 1 ≤ p.m, StrongLogisticCondition`
forces the Bernoulli branch; we route through Slot F. -/
theorem unitPointDomain.Proposition_1_3_holds
    (p : CM2Params) (C : ShenWork.Paper2.Paper2Constants p) :
    Proposition_1_3 ShenWork.Paper2.unitPointDomain p C := by
  intro ha hb _hm _hcond u₀ hu₀
  rcases ShenWork.Paper2.unitPointLogistic_globalExistence_with_attractor
      p ha hb u₀ hu₀ with
    ⟨u, v, hglobal, htrace, hbound, _hlim⟩
  refine ⟨u, v, hglobal, htrace, ?_⟩
  refine ⟨max (ShenWork.Paper2.unitPointDomain.supNorm u₀)
    ((p.a / p.b) ^ (1 / p.α)), ?_⟩
  refine Filter.eventually_atTop.mpr ⟨0, fun t ht => ?_⟩
  exact hbound t ht

/-- Paper 3 Proposition 1.2 holds for the unit-point domain in the
`0 < p.a ∧ 0 < p.b` slice. -/
theorem unitPointDomain.Proposition_1_2_when_a_pos_b_pos
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) :
    Proposition_1_2 ShenWork.Paper2.unitPointDomain p := by
  intro _hχ _hm u₀ hu₀
  rcases ShenWork.Paper2.unitPointLogistic_globalExistence_with_attractor
      p ha hb u₀ hu₀ with
    ⟨u, v, hglobal, htrace, hbound, _hlim⟩
  refine ⟨u, v, hglobal, htrace, ?_⟩
  refine ⟨max (ShenWork.Paper2.unitPointDomain.supNorm u₀)
    ((p.a / p.b) ^ (1 / p.α)), ?_⟩
  refine Filter.eventually_atTop.mpr ⟨0, fun t ht => ?_⟩
  exact hbound t ht

/-- Paper 3 Proposition 1.4 for the `0 < p.a ∧ 0 < p.b` slice (a subcase
of the `(0 ≤ a ∧ 0 < b)` disjunctive branch).  Routes through Slot F. -/
theorem unitPointDomain.Proposition_1_4_when_a_pos_b_pos
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) :
    Proposition_1_4 ShenWork.Paper2.unitPointDomain p := by
  intro _hm _hβ _hor _hχ u₀ hu₀
  rcases ShenWork.Paper2.unitPointLogistic_globalExistence_with_attractor
      p ha hb u₀ hu₀ with
    ⟨u, v, hglobal, htrace, hbound, _hlim⟩
  refine ⟨u, v, hglobal, htrace, ?_⟩
  refine ⟨max (ShenWork.Paper2.unitPointDomain.supNorm u₀)
    ((p.a / p.b) ^ (1 / p.α)), ?_⟩
  refine Filter.eventually_atTop.mpr ⟨0, fun t ht => ?_⟩
  exact hbound t ht

/-- Paper 3 Proposition 1.4 for the disjunction `(a=0 ∧ b=0) ∨ (0 < a ∧ 0 < b)`.
Covers two of three cases of the full hypothesis disjunction; the
`(a=0 ∧ 0 < b)` case requires a separate ODE bridge. -/
theorem unitPointDomain.Proposition_1_4_when_a_b_split
    (p : CM2Params)
    (hsplit : (p.a = 0 ∧ p.b = 0) ∨ (0 < p.a ∧ 0 < p.b)) :
    Proposition_1_4 ShenWork.Paper2.unitPointDomain p := by
  rcases hsplit with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact unitPointDomain.Proposition_1_4_minimal_only p ha hb
  · exact unitPointDomain.Proposition_1_4_when_a_pos_b_pos p ha hb

/-- Paper 3 Proposition 1.4 for the (a = 0, 0 < b) slice via Slot R. -/
theorem unitPointDomain.Proposition_1_4_when_a_zero_b_pos
    (p : CM2Params) (ha : p.a = 0) (hb : 0 < p.b) :
    Proposition_1_4 ShenWork.Paper2.unitPointDomain p := by
  intro _hm _hβ _hor _hχ u₀ hu₀
  rcases ShenWork.Paper2.unitPointDecay_globalExistence_with_bound
      p ha hb u₀ hu₀ with
    ⟨u, v, hglobal, htrace, hbound⟩
  refine ⟨u, v, hglobal, htrace, ?_⟩
  refine ⟨ShenWork.Paper2.unitPointDomain.supNorm u₀, ?_⟩
  refine Filter.eventually_atTop.mpr ⟨0, fun t ht => ?_⟩
  exact hbound t ht

/-- Paper 3 Proposition 1.4 holds **unconditionally** on the unit-point
domain.  The hypothesis disjunction `(a = 0 ∧ b = 0) ∨ (0 ≤ a ∧ 0 < b)`
splits into three subcases — minimal `(0, 0)`, decay `(0, b > 0)`, and
logistic `(a > 0, b > 0)` — each closed by the corresponding bridge. -/
theorem unitPointDomain.Proposition_1_4_holds
    (p : CM2Params) :
    Proposition_1_4 ShenWork.Paper2.unitPointDomain p := by
  intro hm hβ hor hχ u₀ hu₀
  rcases hor with ⟨ha_zero, hb_zero⟩ | ⟨ha_nn, hb_pos⟩
  · exact unitPointDomain.Proposition_1_4_minimal_only p ha_zero hb_zero
      hm hβ (Or.inl ⟨ha_zero, hb_zero⟩) hχ u₀ hu₀
  · by_cases ha_pos : 0 < p.a
    · exact unitPointDomain.Proposition_1_4_when_a_pos_b_pos p ha_pos hb_pos
        hm hβ (Or.inr ⟨ha_nn, hb_pos⟩) hχ u₀ hu₀
    · have ha_zero : p.a = 0 := le_antisymm (not_lt.mp ha_pos) ha_nn
      exact unitPointDomain.Proposition_1_4_when_a_zero_b_pos p ha_zero hb_pos
        hm hβ (Or.inr ⟨ha_nn, hb_pos⟩) hχ u₀ hu₀

/-- Paper 3 Proposition 1.2 holds for the (a = 0, 0 < b) slice via Slot R. -/
theorem unitPointDomain.Proposition_1_2_when_a_zero_b_pos
    (p : CM2Params) (ha : p.a = 0) (hb : 0 < p.b) :
    Proposition_1_2 ShenWork.Paper2.unitPointDomain p := by
  intro _hχ _hm u₀ hu₀
  rcases ShenWork.Paper2.unitPointDecay_globalExistence_with_bound
      p ha hb u₀ hu₀ with
    ⟨u, v, hglobal, htrace, hbound⟩
  refine ⟨u, v, hglobal, htrace, ?_⟩
  refine ⟨ShenWork.Paper2.unitPointDomain.supNorm u₀, ?_⟩
  refine Filter.eventually_atTop.mpr ⟨0, fun t ht => ?_⟩
  exact hbound t ht

/-- Paper 3 Proposition 1.2 on the unit-point domain, **excluding** the
slice `a > 0 ∧ b = 0`.  In that slice the unit-point ODE `u' = au` is
unbounded so the proposition's IsPaper2Bounded conclusion genuinely
fails — a real restriction inherent to the unit-point instance.
Covers `(a = 0, b ≥ 0)` and `(0 < a, 0 < b)`. -/
theorem unitPointDomain.Proposition_1_2_when_not_a_pos_b_zero
    (p : CM2Params)
    (hnot : ¬ (0 < p.a ∧ p.b = 0)) :
    Proposition_1_2 ShenWork.Paper2.unitPointDomain p := by
  by_cases ha_pos : 0 < p.a
  · have hb_ne : p.b ≠ 0 := fun hb0 => hnot ⟨ha_pos, hb0⟩
    have hb_pos : 0 < p.b := lt_of_le_of_ne p.hb (Ne.symm hb_ne)
    exact unitPointDomain.Proposition_1_2_when_a_pos_b_pos p ha_pos hb_pos
  · have ha_zero : p.a = 0 := le_antisymm (not_lt.mp ha_pos) p.ha
    by_cases hb_pos : 0 < p.b
    · exact unitPointDomain.Proposition_1_2_when_a_zero_b_pos p ha_zero hb_pos
    · have hb_zero : p.b = 0 := le_antisymm (not_lt.mp hb_pos) p.hb
      exact unitPointDomain.Proposition_1_2_minimal_only p ha_zero hb_zero

/-- On unitPointDomain with a = 0, b = 0, any PGBS has u constant in time
(since u' = u(a - bu^α) = 0) and positive, so eventual lower bounds hold.
This proves Theorem_2_1_part1 in the minimal regime without ODE uniqueness. -/
theorem unitPointDomain.Theorem_2_1_part1_when_a_zero_b_zero
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) :
    Theorem_2_1_part1 ShenWork.Paper2.unitPointDomain p := by
  intro _hm u v hsol
  -- Extract components of PGBS
  have hglobal := hsol.1
  -- Get regularity: Differentiable ℝ (fun t => u t ())
  have hreg : Differentiable ℝ (fun t : ℝ => u t ()) := by
    have h2 := hglobal 2 (by norm_num : (0 : ℝ) < 2)
    exact h2.2.1.1
  -- Get PDE: deriv (fun s => u s ()) t = 0 for all t > 0
  have hderiv_zero : ∀ t : ℝ, 0 < t → deriv (fun s : ℝ => u s ()) t = 0 := by
    intro t ht
    have hT := hglobal (t + 1) (by linarith)
    have hpde := hT.pde_u (t := t) (x := ()) ht (by linarith) (Set.mem_univ _)
    simp only [ShenWork.Paper2.unitPointDomain] at hpde
    rw [ha, hb] at hpde
    linarith
  -- u is constant on (0, ∞): use IsOpen.is_const_of_deriv_eq_zero
  have hconst : ∀ t₁ t₂ : ℝ, 0 < t₁ → 0 < t₂ →
      u t₁ () = u t₂ () := by
    intro t₁ t₂ ht₁ ht₂
    have hIoi_open : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
    have hIoi_preconn : IsPreconnected (Set.Ioi (0 : ℝ)) :=
      convex_Ioi (0 : ℝ) |>.isPreconnected
    have hDiffOn : DifferentiableOn ℝ (fun t : ℝ => u t ()) (Set.Ioi 0) :=
      hreg.differentiableOn
    have hEqOn : Set.EqOn (deriv (fun t : ℝ => u t ())) 0 (Set.Ioi 0) :=
      fun t ht => hderiv_zero t ht
    exact hIoi_open.is_const_of_deriv_eq_zero hIoi_preconn hDiffOn hEqOn ht₁ ht₂
  -- u(t)() = u(1)() for all t > 0
  have hval : ∀ t : ℝ, 0 < t → u t () = u 1 () :=
    fun t ht => hconst t 1 ht one_pos
  -- u(1)() > 0 from PGBS positivity
  have hpos : 0 < u 1 () := hsol.2.2 1 () one_pos (Set.mem_univ _)
  -- Set δu = u(1)()
  refine ⟨u 1 (), hpos, ?_, ?_⟩
  · -- EventuallyLowerBound D u (u 1 ())
    refine ⟨hpos, Filter.eventually_atTop.mpr ⟨1, fun t ht => ?_⟩⟩
    change u 1 () ≤ ShenWork.Paper2.unitPointDomain.infValue (u t)
    change u 1 () ≤ u t ()
    rw [hval t (lt_of_lt_of_le one_pos ht)]
  · -- EventuallyLowerBound D v (ν/μ * (u 1 ())^γ)
    have hv_eq : ∀ t : ℝ, 0 < t →
        v t () = (p.ν / p.μ) * (u t ()) ^ p.γ := by
      intro t ht
      have hT := hglobal (t + 1) (by linarith)
      have hpde_v := hT.pde_v (t := t) (x := ()) ht (by linarith) (Set.mem_univ _)
      simp only [ShenWork.Paper2.unitPointDomain] at hpde_v
      have hμ_ne : p.μ ≠ 0 := ne_of_gt p.hμ
      have h : p.μ * v t () = p.ν * (u t ()) ^ p.γ := by linarith
      field_simp at h ⊢
      linarith
    have hv_const : ∀ t : ℝ, 0 < t →
        v t () = (p.ν / p.μ) * (u 1 ()) ^ p.γ := by
      intro t ht
      rw [hv_eq t ht, hval t ht]
    have hv_pos : 0 < (p.ν / p.μ) * (u 1 ()) ^ p.γ := by
      apply mul_pos (div_pos p.hν p.hμ)
      exact Real.rpow_pos_of_pos hpos _
    refine ⟨hv_pos, Filter.eventually_atTop.mpr ⟨1, fun t ht => ?_⟩⟩
    change p.ν / p.μ * (u 1 ()) ^ p.γ ≤
      ShenWork.Paper2.unitPointDomain.infValue (v t)
    change p.ν / p.μ * (u 1 ()) ^ p.γ ≤ v t ()
    rw [hv_const t (lt_of_lt_of_le one_pos ht)]

end ShenWork.Paper3

end
